/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.ImplicitFunction.Bivariate

/-!
# Debt overhang, the debt Laffer curve, and debt buybacks

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §6.2.3–6.2.5,
pp. 392–401 (eqs. (36)–(40), footnotes 43–48, Table 6.2) and Exercise 6 (pp. 427–428).

A country with inherited debt `D` invests `K` on date 1; date-2 output is `AF(K)` with
productivity `A` distributed on `[A̲, Ā]` (`0 ≤ A̲ < Ā`) with a continuous density `π`,
`∫π = 1`, `E A = ∫Aπ = 1`. Creditors receive `min{ηAF(K), D}`; the risk-neutral country
(`β = 1`, `r = 0`) maximises `U(K) = Y₁ − K + F(K) − V(D, K)` (36), where
`V(D, K) = E min{ηAF(K), D}` is the market value of the debt.

We prove, with genuine derivatives (`HasDerivAt`) and the fundamental theorem of calculus for
the integration limit `a* = D/(ηF(K))`:
* the representation (37) of `V`, and `U = Y₁ − K + E[AF(K) − min{ηAF(K), D}]`;
* `∂V/∂K = ηF′(K)∫_{A̲}^{a*}Aπ` — the boundary terms from differentiating the limits cancel
  (footnote 43) — the first-order condition (38), and the second derivative of footnote 44;
* the second-order condition `U″ ≤ 0` at an interior maximum (the book's strict `U″ < 0` is an
  extra assumption), and the implicit-function formula `K′(D) = DF′π(a*)/(ηF²U″) < 0`, with the
  optimal-investment branch `K(D)` DERIVED to exist and be differentiable (a Berge argument
  and Mathlib's implicit function theorem, `optimalInvestment_hasDerivAt`);
* debt overhang WITHOUT calculus: `V` has increasing differences in `(D, K)`, so the optimal
  investment is non-increasing in `D` whenever it is unique (a Topkis argument);
* the total derivative (39) of the Laffer curve `D ↦ V[D, K(D)]`, and marginal price `≤`
  average price, `dV/dD ≤ V/D`, WITHOUT any concavity (p. 398 uses concavity);
* the book's "the Laffer curve therefore is concave" (p. 395) is REFUTED as stated: a concave
  function that is nonnegative on `[0, ∞)` is nondecreasing, so a concave Laffer curve can
  never have the downward-sloping "wrong side" of Figure 6.7; an explicit example (uniform `A`,
  `F = 2√K`, `η = 1/2`) shows the curve DOES slope down (`V = 21/32` at `D = 7/8`, `1/2` at
  `D = 2`), so it is provably not concave. What is true: for fixed `K`, `V(·, K)` is concave
  and nondecreasing;
* the debtor's envelope `dU/dD = −Prob(full repayment)` and the gain from a write-down on the
  wrong side;
* the buyback formula (40), footnote 48's general-`Q` derivative, the closed form
  `dU₁/dQ|₀ = −(ηF/D)∫_{A̲}^{a*}Aπ < 0`, and the creditors' gain;
* the Bolivia arithmetic of Table 6.2;
* Exercise 6: the debtor's investment under certain default, the Pareto-improving write-down,
  and the creditors' optimal write-down `D*`, which is attained (the certainty Laffer curve
  drops discontinuously above it).
-/

namespace ObstfeldRogoff.CapitalMarketImperfections.DebtOverhangLaffer

open Set Filter Topology intervalIntegral

/-! ## The model, (36)–(37) -/

/-- The market value of the debt (36)–(37), O&R p. 393:
`V(D, K) = E min{ηAF(K), D} = ∫_{A̲}^{Ā} min{ηAF(K), D} π(A) dA`. -/
noncomputable def marketValue (π : ℝ → ℝ) (Al Ah η : ℝ) (F : ℝ → ℝ) (D K : ℝ) : ℝ :=
  ∫ A in Al..Ah, min (η * A * F K) D * π A

/-- The default threshold `a* = D/(ηF(K))`, O&R p. 393: default iff `A < a*`. -/
noncomputable def threshold (η : ℝ) (F : ℝ → ℝ) (D K : ℝ) : ℝ := D / (η * F K)

/-- The partial mean `∫_{A̲}^{x} Aπ(A) dA`, O&R (37). -/
noncomputable def partialMean (π : ℝ → ℝ) (Al x : ℝ) : ℝ := ∫ A in Al..x, A * π A

/-- The partial probability `∫_{A̲}^{x} π(A) dA`, O&R (37). -/
noncomputable def partialProb (π : ℝ → ℝ) (Al x : ℝ) : ℝ := ∫ A in Al..x, π A

/-- The debtor's expected utility (36), O&R p. 393: `U(K) = Y₁ − K + F(K) − V(D, K)`. -/
noncomputable def debtorUtility (π : ℝ → ℝ) (Al Ah η Y₁ : ℝ) (F : ℝ → ℝ) (D K : ℝ) : ℝ :=
  Y₁ - K + F K - marketValue π Al Ah η F D K

/-- (36) from its primitive form, O&R p. 393: with `E A = 1`, the debtor's expected utility
`Y₁ − K + E[AF(K) − min{ηAF(K), D}]` equals `Y₁ − K + F(K) − V(D, K)`. -/
theorem debtorUtility_eq_expectation {π : ℝ → ℝ} (hπ : Continuous π) {Al Ah η Y₁ : ℝ}
    {F : ℝ → ℝ} (hmean : ∫ A in Al..Ah, A * π A = 1) (D K : ℝ) :
    Y₁ - K + ∫ A in Al..Ah, (A * F K - min (η * A * F K) D) * π A =
      debtorUtility π Al Ah η Y₁ F D K := by
  unfold debtorUtility marketValue
  have h1 : IntervalIntegrable (fun A => A * F K * π A) MeasureTheory.volume Al Ah :=
    (by fun_prop : Continuous fun A => A * F K * π A).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun A => min (η * A * F K) D * π A) MeasureTheory.volume Al Ah :=
    (by fun_prop : Continuous fun A => min (η * A * F K) D * π A).intervalIntegrable _ _
  have e : (fun A => (A * F K - min (η * A * F K) D) * π A) =
      fun A => A * F K * π A - min (η * A * F K) D * π A := by
    funext A; ring
  rw [e, integral_sub h1 h2]
  have e2 : (∫ A in Al..Ah, A * F K * π A) = F K * ∫ A in Al..Ah, A * π A := by
    rw [← integral_const_mul]
    congr 1
    funext A
    ring
  rw [e2, hmean]
  ring

/-- The representation (37) of the market value, O&R p. 393: if `ηF(K) > 0` and the threshold
`a* = D/(ηF(K))` lies in `[A̲, Ā]`, then
`V(D, K) = ηF(K)∫_{A̲}^{a*}Aπ(A)dA + D∫_{a*}^{Ā}π(A)dA`
(payments `ηAF(K)` in default states `A < a*`, `D` in repayment states). -/
theorem marketValue_eq {π : ℝ → ℝ} (hπ : Continuous π) {Al Ah η : ℝ} {F : ℝ → ℝ} {D K : ℝ}
    (hηF : 0 < η * F K) (hlo : Al ≤ threshold η F D K) (hhi : threshold η F D K ≤ Ah) :
    marketValue π Al Ah η F D K =
      η * F K * partialMean π Al (threshold η F D K) +
        D * ∫ A in threshold η F D K..Ah, π A := by
  set a := threshold η F D K with ha
  have hint : ∀ x y, IntervalIntegrable (fun A => min (η * A * F K) D * π A)
      MeasureTheory.volume x y := fun x y =>
    (by fun_prop : Continuous fun A => min (η * A * F K) D * π A).intervalIntegrable _ _
  unfold marketValue
  rw [← integral_add_adjacent_intervals (hint Al a) (hint a Ah)]
  have hηFa : η * F K * a = D := by
    rw [ha]; unfold threshold; rw [mul_div_assoc']; exact mul_div_cancel_left₀ D hηF.ne'
  have e1 : (∫ A in Al..a, min (η * A * F K) D * π A) = η * F K * partialMean π Al a := by
    unfold partialMean
    rw [← integral_const_mul]
    apply integral_congr
    intro A hA
    rw [uIcc_of_le hlo] at hA
    have : η * A * F K ≤ D := by
      rw [← hηFa]; nlinarith [hA.2]
    simp only
    rw [min_eq_left this]
    ring
  have e2 : (∫ A in a..Ah, min (η * A * F K) D * π A) = D * ∫ A in a..Ah, π A := by
    rw [← integral_const_mul]
    apply integral_congr
    intro A hA
    rw [uIcc_of_le hhi] at hA
    have : D ≤ η * A * F K := by
      rw [← hηFa]; nlinarith [hA.1]
    simp only
    rw [min_eq_right this]
  rw [e1, e2]

/-! ## Differentiating through the integration limits: footnote 43 and (38) -/

/-- FTC for the partial mean: `d/dx ∫_{A̲}^{x} Aπ = xπ(x)`. (O&R §6.2.3–6.2.4, pp. 393–395.) -/
theorem hasDerivAt_partialMean {π : ℝ → ℝ} (hπ : Continuous π) (Al x : ℝ) :
    HasDerivAt (partialMean π Al) (x * π x) x :=
  ((by fun_prop : Continuous fun A => A * π A).integral_hasStrictDerivAt Al x).hasDerivAt

/-- FTC for the partial probability: `d/dx ∫_{A̲}^{x} π = π(x)`. (O&R §6.2.3–6.2.4, pp. 393–395.) -/
theorem hasDerivAt_partialProb {π : ℝ → ℝ} (hπ : Continuous π) (Al x : ℝ) :
    HasDerivAt (partialProb π Al) (π x) x :=
  (hπ.integral_hasStrictDerivAt Al x).hasDerivAt

/-- The derivative of the threshold in `K`: `∂a*/∂K = −Dηf₁/(ηF(K))²`.
(O&R §6.2.3–6.2.4, pp. 393–395.) -/
theorem hasDerivAt_threshold {η : ℝ} {F : ℝ → ℝ} {D K f₁ : ℝ} (hF : HasDerivAt F f₁ K)
    (hηF : η * F K ≠ 0) :
    HasDerivAt (threshold η F D) (-(D * (η * f₁)) / (η * F K) ^ 2) K := by
  have := (hasDerivAt_const K D).div (hF.const_mul η) hηF
  unfold threshold
  exact this.congr_deriv (by ring)

/-- The formula (37) written with a variable lower-tail integral:
`Φ(K) = ηF(K)·G(a*(K)) + D·[H(Ā) − H(a*(K))]`. (O&R §6.2.3–6.2.4, pp. 393–395.) -/
noncomputable def valueFormula (π : ℝ → ℝ) (Al Ah η : ℝ) (F : ℝ → ℝ) (D K : ℝ) : ℝ :=
  η * F K * partialMean π Al (threshold η F D K) +
    D * (partialProb π Al Ah - partialProb π Al (threshold η F D K))

/-- `Φ = V` whenever `a* ∈ [A̲, Ā]` (from (37)). (O&R §6.2.3–6.2.4, pp. 393–395.) -/
theorem valueFormula_eq_marketValue {π : ℝ → ℝ} (hπ : Continuous π) {Al Ah η : ℝ}
    {F : ℝ → ℝ} {D K : ℝ} (hηF : 0 < η * F K) (hlo : Al ≤ threshold η F D K)
    (hhi : threshold η F D K ≤ Ah) :
    valueFormula π Al Ah η F D K = marketValue π Al Ah η F D K := by
  rw [marketValue_eq hπ hηF hlo hhi, valueFormula, partialProb, partialProb,
    integral_interval_sub_left (hπ.intervalIntegrable _ _) (hπ.intervalIntegrable _ _)]

/-- Footnote 43 for the formula: `∂Φ/∂K = ηF′(K)∫_{A̲}^{a*}Aπ`; the two terms from the moving
limit, `ηF·a*π(a*)·∂a*/∂K` and `−Dπ(a*)·∂a*/∂K`, cancel because `ηF(K)a* = D`. -/
theorem hasDerivAt_valueFormula {π : ℝ → ℝ} (hπ : Continuous π) {Al Ah η : ℝ} {F : ℝ → ℝ}
    {D K f₁ : ℝ} (hF : HasDerivAt F f₁ K) (hηF : η * F K ≠ 0) :
    HasDerivAt (valueFormula π Al Ah η F D)
      (η * f₁ * partialMean π Al (threshold η F D K)) K := by
  set a := threshold η F D K with ha
  have hth := hasDerivAt_threshold (D := D) hF hηF
  have hG := HasDerivAt.comp (h := threshold η F D) K (hasDerivAt_partialMean hπ Al a) hth
  have hH := HasDerivAt.comp (h := threshold η F D) K (hasDerivAt_partialProb hπ Al a) hth
  have hηFa : η * F K * a = D := by
    rw [ha]; unfold threshold; rw [mul_div_assoc']; exact mul_div_cancel_left₀ D hηF
  have h := HasDerivAt.add ((hF.const_mul η).mul hG)
    ((hH.const_sub (partialProb π Al Ah)).const_mul D)
  unfold valueFormula
  refine h.congr_deriv ?_
  have hc : (partialMean π Al ∘ threshold η F D) K = partialMean π Al a := rfl
  rw [hc]
  have e : η * F K * (a * π a * (-(D * (η * f₁)) / (η * F K) ^ 2)) +
      D * -(π a * (-(D * (η * f₁)) / (η * F K) ^ 2)) = 0 := by
    have : η * F K * (a * π a * (-(D * (η * f₁)) / (η * F K) ^ 2)) =
        D * (π a * (-(D * (η * f₁)) / (η * F K) ^ 2)) := by
      rw [← hηFa]; ring
    rw [this]; ring
  linear_combination e

/-- Footnote 43: at any `K` where `F` is differentiable, `ηF(K) > 0` and the default threshold is
interior, `a* ∈ (A̲, Ā)`, the market value has `∂V/∂K = ηF′(K)∫_{A̲}^{a*}Aπ(A)dA`. -/
theorem hasDerivAt_marketValue_K {π : ℝ → ℝ} (hπ : Continuous π) {Al Ah η : ℝ} {F : ℝ → ℝ}
    {D K f₁ : ℝ} (hF : HasDerivAt F f₁ K) (hηF : 0 < η * F K)
    (hint : threshold η F D K ∈ Ioo Al Ah) :
    HasDerivAt (marketValue π Al Ah η F D)
      (η * f₁ * partialMean π Al (threshold η F D K)) K := by
  have hd := hasDerivAt_valueFormula (Al := Al) (Ah := Ah) (D := D) hπ hF hηF.ne'
  have hcont : ContinuousAt (threshold η F D) K :=
    (hasDerivAt_threshold (D := D) hF hηF.ne').continuousAt
  have hcF : ContinuousAt (fun K => η * F K) K := hF.continuousAt.const_mul η
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [hcont.preimage_mem_nhds (Ioo_mem_nhds hint.1 hint.2),
    hcF.eventually (lt_mem_nhds hηF)] with K' h1 h2
  exact (valueFormula_eq_marketValue hπ h2 h1.1.le h1.2.le).symm

/-- The first-order condition (38) in derivative form, O&R p. 393: under the hypotheses of
`hasDerivAt_marketValue_K`,
`U′(K) = −1 + F′(K)[1 − η∫_{A̲}^{a*}Aπ(A)dA]`. -/
theorem hasDerivAt_debtorUtility {π : ℝ → ℝ} (hπ : Continuous π) {Al Ah η Y₁ : ℝ}
    {F : ℝ → ℝ} {D K f₁ : ℝ} (hF : HasDerivAt F f₁ K) (hηF : 0 < η * F K)
    (hint : threshold η F D K ∈ Ioo Al Ah) :
    HasDerivAt (debtorUtility π Al Ah η Y₁ F D)
      (-1 + f₁ * (1 - η * partialMean π Al (threshold η F D K))) K := by
  have hV := hasDerivAt_marketValue_K hπ hF hηF hint
  have h := (((hasDerivAt_id K).const_sub Y₁).add hF).sub hV
  unfold debtorUtility
  exact h.congr_deriv (by ring)

/-- The first-order condition (38), O&R p. 393: at an interior local maximum of `U` with
interior threshold, `F′(K)[1 − η∫_{A̲}^{a*}Aπ(A)dA] = 1`. -/
theorem foc38 {π : ℝ → ℝ} (hπ : Continuous π) {Al Ah η Y₁ : ℝ} {F : ℝ → ℝ} {D K f₁ : ℝ}
    (hF : HasDerivAt F f₁ K) (hηF : 0 < η * F K) (hint : threshold η F D K ∈ Ioo Al Ah)
    (hmax : IsLocalMax (debtorUtility π Al Ah η Y₁ F D) K) :
    f₁ * (1 - η * partialMean π Al (threshold η F D K)) = 1 := by
  have := hmax.hasDerivAt_eq_zero (hasDerivAt_debtorUtility (Y₁ := Y₁) hπ hF hηF hint)
  linarith

/-- The marginal-utility function of footnote 44: `U′(K) = −1 + F′(K)[1 − ηG(a*(K))]`. -/
noncomputable def marginalUtility (π : ℝ → ℝ) (Al η : ℝ) (F F' : ℝ → ℝ) (D K : ℝ) : ℝ :=
  -1 + F' K * (1 - η * partialMean π Al (threshold η F D K))

/-- The second derivative of footnote 44, O&R p. 394: if `F′` has derivative `F″(K)` at `K`,
then `U″(K) = F″(K)[1 − η∫_{A̲}^{a*}Aπ] + D²F′(K)²π(a*)/(ηF(K)³)`. (The second term is the
derivative of the integration limit; it is positive, so `U″ < 0` is not automatic.) -/
theorem hasDerivAt_marginalUtility {π : ℝ → ℝ} (hπ : Continuous π) {Al η : ℝ}
    {F F' : ℝ → ℝ} {D K f₂ : ℝ} (hF : HasDerivAt F (F' K) K) (hF2 : HasDerivAt F' f₂ K)
    (hηF : η * F K ≠ 0) :
    HasDerivAt (marginalUtility π Al η F F' D)
      (f₂ * (1 - η * partialMean π Al (threshold η F D K)) +
        D ^ 2 * F' K ^ 2 * π (threshold η F D K) / (η * F K ^ 3)) K := by
  set a := threshold η F D K with ha
  have hth := hasDerivAt_threshold (D := D) hF hηF
  have hG := HasDerivAt.comp (h := threshold η F D) K (hasDerivAt_partialMean hπ Al a) hth
  have h := (hF2.mul ((hG.const_mul η).const_sub 1)).const_add (-1)
  unfold marginalUtility
  refine h.congr_deriv ?_
  have hη : η ≠ 0 := left_ne_zero_of_mul hηF
  have hFK : F K ≠ 0 := right_ne_zero_of_mul hηF
  have hc : (partialMean π Al ∘ threshold η F D) K = partialMean π Al a := rfl
  rw [hc, ha]
  unfold threshold
  field_simp

/-- The second-order condition, footnote 44, O&R p. 394, in its correct (weak) form: if `U` has
a local maximum at `K*`, `U′ = m` on a neighbourhood of `K*`, `m(K*) = 0` and `m′(K*) = U″`,
then `U″ ≤ 0`. (The book states "`U″(K₂) < 0` … must hold at the optimal (interior)
investment level"; only `≤ 0` is necessary, the strict inequality is an assumption.) -/
theorem soc_nonpos {U m : ℝ → ℝ} {Ks u₂ : ℝ} (hmax : IsLocalMax U Ks)
    (hU : ∀ᶠ x in 𝓝 Ks, HasDerivAt U (m x) x) (hm0 : m Ks = 0) (hm : HasDerivAt m u₂ Ks) :
    u₂ ≤ 0 := by
  by_contra hpos
  push Not at hpos
  have ht : Tendsto (slope m Ks) (𝓝[>] Ks) (𝓝 u₂) :=
    (hasDerivAt_iff_tendsto_slope.mp hm).mono_left
      (nhdsWithin_mono _ fun y (hy : Ks < y) => hy.ne')
  have hmpos : ∀ᶠ x in 𝓝[>] Ks, 0 < m x := by
    filter_upwards [ht.eventually (lt_mem_nhds hpos), self_mem_nhdsWithin] with x hx hx'
    rw [slope_def_field, hm0, sub_zero] at hx
    rw [mem_Ioi] at hx'
    exact (div_pos_iff_of_pos_right (by linarith)).mp hx
  have hall : ∀ᶠ x in 𝓝[>] Ks, HasDerivAt U (m x) x ∧ 0 < m x ∧ U x ≤ U Ks :=
    (hU.filter_mono nhdsWithin_le_nhds).and (hmpos.and (hmax.filter_mono nhdsWithin_le_nhds))
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hall
  rw [mem_Ioi] at hu
  set x := (Ks + u) / 2 with hx
  have hKx : Ks < x := by rw [hx]; linarith
  have hxu : x < u := by rw [hx]; linarith
  have hderiv : ∀ y ∈ Icc Ks x, HasDerivAt U (m y) y := by
    intro y hy
    rcases hy.1.lt_or_eq with h | h
    · exact (hsub ⟨h, lt_of_le_of_lt hy.2 hxu⟩).1
    · rw [← h]; exact hU.self_of_nhds
  have hcont : ContinuousOn U (Icc Ks x) := fun y hy =>
    (hderiv y hy).continuousAt.continuousWithinAt
  obtain ⟨c, hc, hceq⟩ := exists_hasDerivAt_eq_slope U m hKx hcont
    (fun y hy => hderiv y (Ioo_subset_Icc_self hy))
  have hmc : 0 < m c := (hsub ⟨hc.1, hc.2.trans hxu⟩).2.1
  have hUx : U x ≤ U Ks := (hsub ⟨hKx, hxu⟩).2.2
  rw [hceq] at hmc
  have : 0 < U x - U Ks := (div_pos_iff_of_pos_right (by linarith)).mp hmc
  linarith

/-- The debt-overhang derivative, footnote 44, O&R p. 394, by implicit differentiation of (38):
let `K(D)` be differentiable at `D₀` with `K′(D₀) = k′` and satisfy the first-order condition
(38) for all `D` near `D₀`, let `F` be differentiable with derivative `F′`, and `F′` have
derivative `F″(K₀)` at `K₀ = K(D₀)`. Then
`k′ · U″ = D₀F′(K₀)π(a*)/(ηF(K₀)²)`, where `U″ = F″(K₀)[1 − ηG(a*)] + D₀²F′(K₀)²π(a*)/(ηF(K₀)³)`
is the second derivative of footnote 44 and `a* = D₀/(ηF(K₀))`. -/
theorem implicit_investment_derivative {π : ℝ → ℝ} (hπ : Continuous π) {Al η : ℝ}
    {F F' Kf : ℝ → ℝ} {D₀ k' f₂ : ℝ} (hF : ∀ K, HasDerivAt F (F' K) K)
    (hF2 : HasDerivAt F' f₂ (Kf D₀)) (hK : HasDerivAt Kf k' D₀)
    (hηF : η * F (Kf D₀) ≠ 0)
    (hfoc : ∀ᶠ D in 𝓝 D₀, marginalUtility π Al η F F' D (Kf D) = 0) :
    k' * (f₂ * (1 - η * partialMean π Al (threshold η F D₀ (Kf D₀))) +
        D₀ ^ 2 * F' (Kf D₀) ^ 2 * π (threshold η F D₀ (Kf D₀)) / (η * F (Kf D₀) ^ 3)) =
      D₀ * F' (Kf D₀) * π (threshold η F D₀ (Kf D₀)) / (η * F (Kf D₀) ^ 2) := by
  set K₀ := Kf D₀ with hK₀
  set a := threshold η F D₀ K₀ with ha
  have hη : η ≠ 0 := left_ne_zero_of_mul hηF
  have hFK : F K₀ ≠ 0 := right_ne_zero_of_mul hηF
  -- the composite `D ↦ a*(D, K(D))`
  have hFK' : HasDerivAt (fun D => F (Kf D)) (F' K₀ * k') D₀ :=
    HasDerivAt.comp (h := Kf) D₀ (hF K₀) hK
  have hth : HasDerivAt (fun D => D / (η * F (Kf D)))
      ((1 * (η * F K₀) - D₀ * (η * (F' K₀ * k'))) / (η * F K₀) ^ 2) D₀ :=
    (hasDerivAt_id D₀).div (hFK'.const_mul η) hηF
  have hG := HasDerivAt.comp (h := fun D => D / (η * F (Kf D))) D₀
    (hasDerivAt_partialMean hπ Al a) hth
  have hF'K := HasDerivAt.comp (h := Kf) D₀ hF2 hK
  have hΨ := (hF'K.mul ((hG.const_mul η).const_sub 1)).const_add (-1)
  have hΨ0 : HasDerivAt (fun D => marginalUtility π Al η F F' D (Kf D)) 0 D₀ :=
    (hasDerivAt_const D₀ (0 : ℝ)).congr_of_eventuallyEq hfoc
  have hΨ' : HasDerivAt (fun D => marginalUtility π Al η F F' D (Kf D))
      (f₂ * k' * (1 - η * partialMean π Al a) +
        F' K₀ * -(η * (a * π a * ((1 * (η * F K₀) - D₀ * (η * (F' K₀ * k'))) /
          (η * F K₀) ^ 2)))) D₀ := by
    unfold marginalUtility threshold
    exact hΨ
  have e := hΨ'.unique hΨ0
  rw [ha] at e ⊢
  unfold threshold at e ⊢
  field_simp at e ⊢
  linear_combination e

/-- Debt overhang, O&R p. 394 ("`K′(D) < 0` … if `U″(K₂) < 0`"): under the hypotheses of
`implicit_investment_derivative`, if in addition `U″ < 0`, `D₀ > 0`, `F′(K₀) > 0`, `η > 0`,
`F(K₀) > 0` and `π(a*) > 0`, then `K′(D₀) < 0`. -/
theorem investment_derivative_neg {π : ℝ → ℝ} (hπ : Continuous π) {Al η : ℝ}
    {F F' Kf : ℝ → ℝ} {D₀ k' f₂ : ℝ} (hF : ∀ K, HasDerivAt F (F' K) K)
    (hF2 : HasDerivAt F' f₂ (Kf D₀)) (hK : HasDerivAt Kf k' D₀) (hη : 0 < η)
    (hFpos : 0 < F (Kf D₀))
    (hfoc : ∀ᶠ D in 𝓝 D₀, marginalUtility π Al η F F' D (Kf D) = 0)
    (hU2 : f₂ * (1 - η * partialMean π Al (threshold η F D₀ (Kf D₀))) +
        D₀ ^ 2 * F' (Kf D₀) ^ 2 * π (threshold η F D₀ (Kf D₀)) / (η * F (Kf D₀) ^ 3) < 0)
    (hD : 0 < D₀) (hF' : 0 < F' (Kf D₀)) (hπa : 0 < π (threshold η F D₀ (Kf D₀))) :
    k' < 0 := by
  have e := implicit_investment_derivative hπ hF hF2 hK (mul_pos hη hFpos).ne' hfoc
  have hr : 0 < D₀ * F' (Kf D₀) * π (threshold η F D₀ (Kf D₀)) / (η * F (Kf D₀) ^ 2) := by
    positivity
  by_contra h
  push Not at h
  nlinarith

/-! ## The optimal-investment branch `K(D)`: existence and differentiability (footnote 44)

We derive, rather than assume, that the optimal investment is a differentiable function of the
debt near `D₀`: investment ranges over a compact interval `[K̲, K̄]`, the optimum at `D₀` is
unique and interior, `F` is `C²`, the threshold is interior and `U″ ≠ 0`. Then (a) every
selection of optimal investments is continuous at `D₀` (a Berge argument: `V` is 1-Lipschitz
in `D`); (b) near `D₀` it satisfies (38); (c) by Mathlib's implicit function theorem the
solution of (38) near `(D₀, K₀)` is a differentiable function of `D`, and (d) it coincides with
the optimal selection. So the book's `K′(D)` formula holds unconditionally. -/

/-- The market value is 1-Lipschitz in face value (with `∫π = 1`, `π ≥ 0`):
`V(D, K) ≤ V(D′, K) + |D − D′|`. (O&R §6.2.3–6.2.4, pp. 393–395.) -/
theorem marketValue_lipschitz_debt {π : ℝ → ℝ} (hπ : Continuous π) {Al Ah η : ℝ} {F : ℝ → ℝ}
    (hAlh : Al ≤ Ah) (hπ0 : ∀ A ∈ Icc Al Ah, 0 ≤ π A) (hprob : ∫ A in Al..Ah, π A = 1)
    (D D' K : ℝ) :
    marketValue π Al Ah η F D K ≤ marketValue π Al Ah η F D' K + |D - D'| := by
  unfold marketValue
  have hi : ∀ d, IntervalIntegrable (fun A => min (η * A * F K) d * π A)
      MeasureTheory.volume Al Ah := fun d =>
    (by fun_prop : Continuous fun A => min (η * A * F K) d * π A).intervalIntegrable _ _
  have : (∫ A in Al..Ah, min (η * A * F K) D * π A) ≤
      ∫ A in Al..Ah, (min (η * A * F K) D' * π A + |D - D'| * π A) := by
    apply integral_mono_on hAlh (hi D) ((hi D').add ((hπ.intervalIntegrable _ _).const_mul _))
    intro A hA
    have hp := hπ0 A hA
    have hm : min (η * A * F K) D ≤ min (η * A * F K) D' + |D - D'| := by
      have := abs_sub_abs_le_abs_sub D D'
      simp only [min_def]
      split_ifs <;> linarith [le_abs_self (D - D'), neg_abs_le (D - D')]
    nlinarith
  rw [integral_add (hi D') ((hπ.intervalIntegrable _ _).const_mul _), integral_const_mul,
    hprob, mul_one] at this
  exact this

/-- Continuity of the market value in investment (for continuous `F` and `π`).
(O&R §6.2.3–6.2.4, pp. 393–395.) -/
theorem marketValue_continuous_K {π : ℝ → ℝ} (hπ : Continuous π) {Al Ah η : ℝ} {F : ℝ → ℝ}
    (hF : Continuous F) (D : ℝ) : Continuous fun K => marketValue π Al Ah η F D K := by
  unfold marketValue
  exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (by fun_prop) Al Ah

/-- Berge's maximum theorem for the debt-overhang problem: if investment ranges over a compact
interval `S = [K̲, K̄]`, `K₀` is the unique maximiser of `U(D₀, ·)` on `S`, and `Kopt(D)`
maximises `U(D, ·)` on `S` for every `D`, then `Kopt(D) → K₀` as `D → D₀`.
(O&R §6.2.3–6.2.4, pp. 393–395.) -/
theorem optimalInvestment_tendsto {π : ℝ → ℝ} (hπ : Continuous π) {Al Ah η Y₁ : ℝ}
    {F : ℝ → ℝ} (hF : Continuous F) (hAlh : Al ≤ Ah) (hπ0 : ∀ A ∈ Icc Al Ah, 0 ≤ π A)
    (hprob : ∫ A in Al..Ah, π A = 1) {Kl Kh D₀ K₀ : ℝ} (hK₀ : K₀ ∈ Icc Kl Kh)
    (huniq : ∀ K ∈ Icc Kl Kh, K ≠ K₀ →
      debtorUtility π Al Ah η Y₁ F D₀ K < debtorUtility π Al Ah η Y₁ F D₀ K₀)
    {Kopt : ℝ → ℝ} (hKS : ∀ D, Kopt D ∈ Icc Kl Kh)
    (hopt : ∀ D, ∀ K ∈ Icc Kl Kh,
      debtorUtility π Al Ah η Y₁ F D K ≤ debtorUtility π Al Ah η Y₁ F D (Kopt D)) :
    Tendsto Kopt (𝓝 D₀) (𝓝 K₀) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  set T := Icc Kl Kh ∩ {K | ε ≤ |K - K₀|} with hT
  have hTc : IsCompact T := isCompact_Icc.inter_right
    (isClosed_le continuous_const (continuous_abs.comp (continuous_id.sub continuous_const)))
  have hUc : Continuous fun K => debtorUtility π Al Ah η Y₁ F D₀ K := by
    unfold debtorUtility
    have := marketValue_continuous_K (Al := Al) (Ah := Ah) (η := η) hπ hF D₀
    fun_prop
  have hlip : ∀ D K, |debtorUtility π Al Ah η Y₁ F D K - debtorUtility π Al Ah η Y₁ F D₀ K| ≤
      |D - D₀| := by
    intro D K
    unfold debtorUtility
    have h1 := marketValue_lipschitz_debt (η := η) (F := F) hπ hAlh hπ0 hprob D D₀ K
    have h2 := marketValue_lipschitz_debt (η := η) (F := F) hπ hAlh hπ0 hprob D₀ D K
    rw [abs_sub_comm D₀ D] at h2
    rw [abs_le]
    constructor <;> linarith
  rcases T.eq_empty_or_nonempty with hTe | hTne
  · refine Filter.Eventually.of_forall fun D => ?_
    by_contra hcon
    rw [Real.dist_eq, not_lt] at hcon
    have : Kopt D ∈ T := ⟨hKS D, hcon⟩
    rw [hTe] at this
    exact this
  obtain ⟨Kt, hKt, hmax⟩ := hTc.exists_isMaxOn hTne hUc.continuousOn
  have hgap : 0 < debtorUtility π Al Ah η Y₁ F D₀ K₀ - debtorUtility π Al Ah η Y₁ F D₀ Kt := by
    have hne : Kt ≠ K₀ := by
      intro h
      have := hKt.2
      simp only [mem_ofPred_eq, h, sub_self, abs_zero] at this
      linarith
    linarith [huniq Kt hKt.1 hne]
  set g := debtorUtility π Al Ah η Y₁ F D₀ K₀ - debtorUtility π Al Ah η Y₁ F D₀ Kt
  filter_upwards [Metric.ball_mem_nhds D₀ (half_pos hgap)] with D hD
  rw [Metric.mem_ball, Real.dist_eq] at hD
  by_contra hcon
  rw [Real.dist_eq, not_lt] at hcon
  have hmem : Kopt D ∈ T := ⟨hKS D, hcon⟩
  have a1 := isMaxOn_iff.mp hmax _ hmem
  have a2 := hopt D K₀ hK₀
  have a3 := abs_le.mp (hlip D (Kopt D))
  have a4 := abs_le.mp (hlip D K₀)
  linarith [a1, a2, a3.2, a4.1]

/-- The debt derivative of the marginal-utility function (the `D`-partial of (38)):
`∂/∂D {−1 + F′(K)[1 − ηG(a*)]} = −F′(K)a*π(a*)/F(K)`, `a* = D/(ηF(K))`.
(O&R §6.2.3–6.2.4, pp. 393–395.) -/
theorem hasDerivAt_marginalUtility_debt {π : ℝ → ℝ} (hπ : Continuous π) {Al η : ℝ}
    {F F' : ℝ → ℝ} {D K : ℝ} (hηF : η * F K ≠ 0) :
    HasDerivAt (fun D => marginalUtility π Al η F F' D K)
      (-(F' K * threshold η F D K * π (threshold η F D K)) / F K) D := by
  have hth : HasDerivAt (fun D => threshold η F D K) (1 / (η * F K)) D := by
    unfold threshold
    simpa using (hasDerivAt_id D).div_const (η * F K)
  have hG := HasDerivAt.comp (h := fun D => threshold η F D K) D
    (hasDerivAt_partialMean hπ Al (threshold η F D K)) hth
  have h := ((hG.const_mul η).const_sub 1).const_mul (F' K) |>.const_add (-1)
  unfold marginalUtility
  refine h.congr_deriv ?_
  have hη : η ≠ 0 := left_ne_zero_of_mul hηF
  have hFK : F K ≠ 0 := right_ne_zero_of_mul hηF
  field_simp

/-- `toSpanSingleton` on `ℝ` is scalar multiplication of the identity.
(O&R §6.2.3–6.2.4, pp. 393–395.) -/
theorem toSpanSingleton_eq_smul (d : ℝ) :
    ContinuousLinearMap.toSpanSingleton ℝ d = d • (1 : ℝ →L[ℝ] ℝ) := by
  ext; simp

/-- A nonzero scalar multiple of the identity on `ℝ` is invertible.
(O&R §6.2.3–6.2.4, pp. 393–395.) -/
theorem smul_one_isInvertible {c : ℝ} (hc : c ≠ 0) : (c • (1 : ℝ →L[ℝ] ℝ)).IsInvertible :=
  ContinuousLinearMap.IsInvertible.of_inverse (g := c⁻¹ • (1 : ℝ →L[ℝ] ℝ))
    (by ext; simp [hc]) (by ext; simp [hc])

/-- EXISTENCE AND DIFFERENTIABILITY OF THE OPTIMAL-INVESTMENT BRANCH, and the debt-overhang
derivative of footnote 44 without assuming `K(D)` differentiable (O&R p. 394). Hypotheses:
`π` continuous and nonnegative on `[A̲, Ā]` with `∫π = 1`; `F` twice differentiable with `F″`
continuous; investment ranges over `[K̲, K̄]`; `Kopt(D)` is an optimal investment for every `D`;
at `D₀` the optimum `K₀ ∈ (K̲, K̄)` is unique, `ηF(K₀) > 0`, the threshold `a*` is interior and
`U″ ≠ 0` (the second derivative of footnote 44). Then `Kopt` is differentiable at `D₀` and its
derivative `k′` satisfies `k′·U″ = D₀F′(K₀)π(a*)/(ηF(K₀)²)`. -/
theorem optimalInvestment_hasDerivAt {π : ℝ → ℝ} (hπ : Continuous π) {Al Ah η Y₁ : ℝ}
    {F F' F'' : ℝ → ℝ} (hF : ∀ K, HasDerivAt F (F' K) K) (hF2 : ∀ K, HasDerivAt F' (F'' K) K)
    (hF2c : Continuous F'') (hAlh : Al ≤ Ah) (hπ0 : ∀ A ∈ Icc Al Ah, 0 ≤ π A)
    (hprob : ∫ A in Al..Ah, π A = 1) {Kl Kh D₀ K₀ : ℝ} (hK₀ : K₀ ∈ Ioo Kl Kh)
    (huniq : ∀ K ∈ Icc Kl Kh, K ≠ K₀ →
      debtorUtility π Al Ah η Y₁ F D₀ K < debtorUtility π Al Ah η Y₁ F D₀ K₀)
    {Kopt : ℝ → ℝ} (hKS : ∀ D, Kopt D ∈ Icc Kl Kh)
    (hopt : ∀ D, ∀ K ∈ Icc Kl Kh,
      debtorUtility π Al Ah η Y₁ F D K ≤ debtorUtility π Al Ah η Y₁ F D (Kopt D))
    (hηF : 0 < η * F K₀) (hint : threshold η F D₀ K₀ ∈ Ioo Al Ah)
    (hU2 : F'' K₀ * (1 - η * partialMean π Al (threshold η F D₀ K₀)) +
        D₀ ^ 2 * F' K₀ ^ 2 * π (threshold η F D₀ K₀) / (η * F K₀ ^ 3) ≠ 0) :
    ∃ k', HasDerivAt Kopt k' D₀ ∧
      k' * (F'' K₀ * (1 - η * partialMean π Al (threshold η F D₀ K₀)) +
        D₀ ^ 2 * F' K₀ ^ 2 * π (threshold η F D₀ K₀) / (η * F K₀ ^ 3)) =
      D₀ * F' K₀ * π (threshold η F D₀ K₀) / (η * F K₀ ^ 2) := by
  have hFc : Continuous F := continuous_iff_continuousAt.mpr fun K => (hF K).continuousAt
  have hF'c : Continuous F' := continuous_iff_continuousAt.mpr fun K => (hF2 K).continuousAt
  have hGc : Continuous (partialMean π Al) :=
    continuous_iff_continuousAt.mpr fun x => (hasDerivAt_partialMean hπ Al x).continuousAt
  have hη : η ≠ 0 := left_ne_zero_of_mul hηF.ne'
  -- (a) the optimal selection converges to `K₀`
  have hten := optimalInvestment_tendsto hπ hFc hAlh hπ0 hprob (Ioo_subset_Icc_self hK₀)
    huniq hKS hopt
  have hKopt0 : Kopt D₀ = K₀ := by
    by_contra hne
    exact absurd (hopt D₀ K₀ (Ioo_subset_Icc_self hK₀)) (not_le.mpr (huniq _ (hKS D₀) hne))
  -- (b) near `D₀`, `Kopt` satisfies the first-order condition (38)
  have hpath : Tendsto (fun D => (D, Kopt D)) (𝓝 D₀) (𝓝 (D₀, K₀)) :=
    tendsto_id.prodMk_nhds hten
  have hthc : ContinuousAt (fun p : ℝ × ℝ => threshold η F p.1 p.2) (D₀, K₀) := by
    unfold threshold
    exact ContinuousAt.div (by fun_prop) ((continuousAt_const.mul
      (hFc.continuousAt.comp continuousAt_snd))) hηF.ne'
  have hηFc : ContinuousAt (fun p : ℝ × ℝ => η * F p.2) (D₀, K₀) :=
    continuousAt_const.mul (hFc.continuousAt.comp continuousAt_snd)
  have hfoc : ∀ᶠ D in 𝓝 D₀, marginalUtility π Al η F F' D (Kopt D) = 0 := by
    filter_upwards [hten.eventually (Ioo_mem_nhds hK₀.1 hK₀.2),
      hpath.eventually (hthc.eventually (Ioo_mem_nhds hint.1 hint.2)),
      hpath.eventually (hηFc.eventually (lt_mem_nhds hηF))] with D h1 h2 h3
    have hloc : IsLocalMax (debtorUtility π Al Ah η Y₁ F D) (Kopt D) := by
      filter_upwards [Ioo_mem_nhds h1.1 h1.2] with K hK
      exact hopt D K (Ioo_subset_Icc_self hK)
    have := foc38 hπ (Y₁ := Y₁) (hF (Kopt D)) h3 h2 hloc
    unfold marginalUtility
    linarith
  -- (c) the implicit function theorem for (38)
  set f : ℝ → ℝ → ℝ := fun D K => marginalUtility π Al η F F' D K with hf
  set pD : ℝ → ℝ → ℝ := fun D K => -(F' K * threshold η F D K * π (threshold η F D K)) / F K
  set pK : ℝ → ℝ → ℝ := fun D K => F'' K * (1 - η * partialMean π Al (threshold η F D K)) +
    D ^ 2 * F' K ^ 2 * π (threshold η F D K) / (η * F K ^ 3)
  set f₁ : ℝ → ℝ → (ℝ →L[ℝ] ℝ) := fun D K => pD D K • (1 : ℝ →L[ℝ] ℝ) with hf₁
  set f₂ : ℝ → ℝ → (ℝ →L[ℝ] ℝ) := fun D K => pK D K • (1 : ℝ →L[ℝ] ℝ) with hf₂
  have hne : ∀ᶠ v in 𝓝 (D₀, K₀), η * F v.2 ≠ 0 :=
    (hηFc.eventually (lt_mem_nhds hηF)).mono fun v hv => hv.ne'
  have df₁ : ∀ᶠ v in 𝓝 (D₀, K₀), HasFDerivAt (f · v.2) (f₁ v.1 v.2) v.1 := by
    filter_upwards [hne] with v hv
    rw [hf₁]
    simp only
    rw [← toSpanSingleton_eq_smul]
    exact (hasDerivAt_marginalUtility_debt (F' := F') (Al := Al) hπ hv).hasFDerivAt
  have df₂ : ∀ᶠ v in 𝓝 (D₀, K₀), HasFDerivAt (f v.1 ·) (f₂ v.1 v.2) v.2 := by
    filter_upwards [hne] with v hv
    rw [hf₂]
    simp only
    rw [← toSpanSingleton_eq_smul]
    exact (hasDerivAt_marginalUtility hπ (hF v.2) (hF2 v.2) hv).hasFDerivAt
  have hFK0 : F K₀ ≠ 0 := right_ne_zero_of_mul hηF.ne'
  have hFc' : ContinuousAt (fun p : ℝ × ℝ => F p.2) (D₀, K₀) :=
    hFc.continuousAt.comp continuousAt_snd
  have hF'c' : ContinuousAt (fun p : ℝ × ℝ => F' p.2) (D₀, K₀) :=
    hF'c.continuousAt.comp continuousAt_snd
  have hπc : ContinuousAt (fun p : ℝ × ℝ => π (threshold η F p.1 p.2)) (D₀, K₀) :=
    hπ.continuousAt.comp hthc
  have cf₁ : ContinuousAt (Function.uncurry f₁) (D₀, K₀) := by
    have hp : ContinuousAt (fun p : ℝ × ℝ => pD p.1 p.2) (D₀, K₀) :=
      ContinuousAt.div (((hF'c'.mul hthc).mul hπc).neg) hFc' hFK0
    exact hp.smul continuousAt_const
  have cf₂ : ContinuousAt (Function.uncurry f₂) (D₀, K₀) := by
    have h1 : ContinuousAt (fun p : ℝ × ℝ => F'' p.2) (D₀, K₀) :=
      hF2c.continuousAt.comp continuousAt_snd
    have h2 : ContinuousAt (fun p : ℝ × ℝ => partialMean π Al (threshold η F p.1 p.2))
        (D₀, K₀) := hGc.continuousAt.comp hthc
    have hp : ContinuousAt (fun p : ℝ × ℝ => pK p.1 p.2) (D₀, K₀) :=
      (h1.mul (continuousAt_const.sub (continuousAt_const.mul h2))).add
        (ContinuousAt.div (((continuousAt_fst.pow 2).mul (hF'c'.pow 2)).mul hπc)
          (continuousAt_const.mul (hFc'.pow 3)) (mul_ne_zero hη (pow_ne_zero 3 hFK0)))
    exact hp.smul continuousAt_const
  have if₂u : (f₂ (D₀, K₀).1 (D₀, K₀).2).IsInvertible := smul_one_isInvertible hU2
  set ψ := implicitFunctionOfBivariate df₁ df₂ cf₁ cf₂ if₂u with hψ
  have hψd := (hasStrictFDerivAt_implicitFunctionOfBivariate df₁ df₂ cf₁ cf₂ if₂u).hasFDerivAt
  have hiff := eventually_apply_eq_iff_implicitFunctionOfBivariate df₁ df₂ cf₁ cf₂ if₂u
  -- (d) the implicit function coincides with the optimal selection near `D₀`
  have hfu : f D₀ K₀ = 0 := by
    have := hfoc.self_of_nhds
    rw [hKopt0] at this
    exact this
  have heq : ∀ᶠ D in 𝓝 D₀, ψ D = Kopt D := by
    filter_upwards [hpath.eventually hiff, hfoc] with D h1 h2
    exact h1.mp (by simp only [hf] at h2 hfu ⊢; rw [h2, hfu])
  have hKd : HasDerivAt Kopt _ D₀ :=
    (hψd.hasDerivAt).congr_of_eventuallyEq (heq.mono fun D h => h.symm)
  refine ⟨_, hKd, ?_⟩
  have := implicit_investment_derivative hπ hF (hKopt0 ▸ hF2 K₀) hKd
    (by rw [hKopt0]; exact hηF.ne') hfoc
  rw [hKopt0] at this
  exact this

/-- Debt overhang for the derived optimal branch, O&R p. 394: under the hypotheses of
`optimalInvestment_hasDerivAt` with `U″ < 0`, `D₀ > 0`, `F′(K₀) > 0`, `η > 0` and `π(a*) > 0`,
the optimal investment is differentiable at `D₀` with `K′(D₀) < 0`. -/
theorem optimalInvestment_deriv_neg {π : ℝ → ℝ} (hπ : Continuous π) {Al Ah η Y₁ : ℝ}
    {F F' F'' : ℝ → ℝ} (hF : ∀ K, HasDerivAt F (F' K) K) (hF2 : ∀ K, HasDerivAt F' (F'' K) K)
    (hF2c : Continuous F'') (hAlh : Al ≤ Ah) (hπ0 : ∀ A ∈ Icc Al Ah, 0 ≤ π A)
    (hprob : ∫ A in Al..Ah, π A = 1) {Kl Kh D₀ K₀ : ℝ} (hK₀ : K₀ ∈ Ioo Kl Kh)
    (huniq : ∀ K ∈ Icc Kl Kh, K ≠ K₀ →
      debtorUtility π Al Ah η Y₁ F D₀ K < debtorUtility π Al Ah η Y₁ F D₀ K₀)
    {Kopt : ℝ → ℝ} (hKS : ∀ D, Kopt D ∈ Icc Kl Kh)
    (hopt : ∀ D, ∀ K ∈ Icc Kl Kh,
      debtorUtility π Al Ah η Y₁ F D K ≤ debtorUtility π Al Ah η Y₁ F D (Kopt D))
    (hη : 0 < η) (hFpos : 0 < F K₀) (hint : threshold η F D₀ K₀ ∈ Ioo Al Ah)
    (hU2 : F'' K₀ * (1 - η * partialMean π Al (threshold η F D₀ K₀)) +
        D₀ ^ 2 * F' K₀ ^ 2 * π (threshold η F D₀ K₀) / (η * F K₀ ^ 3) < 0)
    (hD : 0 < D₀) (hF' : 0 < F' K₀) (hπa : 0 < π (threshold η F D₀ K₀)) :
    ∃ k', HasDerivAt Kopt k' D₀ ∧ k' < 0 := by
  obtain ⟨k', hk, he⟩ := optimalInvestment_hasDerivAt hπ hF hF2 hF2c hAlh hπ0 hprob hK₀ huniq
    hKS hopt (mul_pos hη hFpos) hint hU2.ne
  refine ⟨k', hk, ?_⟩
  have hr : 0 < D₀ * F' K₀ * π (threshold η F D₀ K₀) / (η * F K₀ ^ 2) := by positivity
  by_contra h
  push Not at h
  nlinarith

/-! ## Debt overhang without calculus: increasing differences (Topkis) -/

/-- The payoff `min(x, D′) − min(x, D)` of an extra `D′ − D` of face value is nondecreasing in
the resources `x` (for `D ≤ D′`). (O&R §6.2.3–6.2.4, pp. 393–395.) -/
theorem min_increment_mono {x y D D' : ℝ} (hD : D ≤ D') (hxy : x ≤ y) :
    min x D' - min x D ≤ min y D' - min y D := by
  simp only [min_def]
  split_ifs <;> linarith

/-- Increasing differences of the market value, O&R p. 394: with `η ≥ 0`, `F(K) ≤ F(K′)`,
`0 ≤ A̲ ≤ Ā`, `π ≥ 0` on `[A̲, Ā]` and `D ≤ D′`,
`V(D′, K) − V(D, K) ≤ V(D′, K′) − V(D, K′)`: more investment raises the value to creditors of
extra face value (it makes full repayment likelier). -/
theorem marketValue_increasing_differences {π : ℝ → ℝ} (hπ : Continuous π) {Al Ah η : ℝ}
    {F : ℝ → ℝ} (hη : 0 ≤ η) (hAl : 0 ≤ Al) (hAlh : Al ≤ Ah)
    (hπ0 : ∀ A ∈ Icc Al Ah, 0 ≤ π A) {D D' K K' : ℝ} (hD : D ≤ D') (hF : F K ≤ F K') :
    marketValue π Al Ah η F D' K - marketValue π Al Ah η F D K ≤
      marketValue π Al Ah η F D' K' - marketValue π Al Ah η F D K' := by
  have hint : ∀ c d, IntervalIntegrable (fun A => min (η * A * F c) d * π A)
      MeasureTheory.volume Al Ah := fun c d =>
    (by fun_prop : Continuous fun A => min (η * A * F c) d * π A).intervalIntegrable _ _
  unfold marketValue
  rw [← integral_sub (hint K D') (hint K D), ← integral_sub (hint K' D') (hint K' D)]
  apply integral_mono_on hAlh ((hint K D').sub (hint K D)) ((hint K' D').sub (hint K' D))
  intro A hA
  have hx : η * A * F K ≤ η * A * F K' :=
    mul_le_mul_of_nonneg_left hF (mul_nonneg hη (hAl.trans hA.1))
  have := min_increment_mono hD hx
  have hp := hπ0 A hA
  nlinarith

/-- Debt overhang, O&R p. 394, WITHOUT differentiability or second-order conditions (a Topkis
argument): let `F` be nondecreasing, `η ≥ 0`, `0 ≤ A̲ ≤ Ā`, `π ≥ 0`. If `K` maximises `U(D, ·)`
and `K′` maximises `U(D′, ·)` over a set `S`, `D ≤ D′`, and the maximiser at `D′` is unique,
then `K′ ≤ K`: higher inherited debt never raises investment. -/
theorem investment_antitone {π : ℝ → ℝ} (hπ : Continuous π) {Al Ah η Y₁ : ℝ} {F : ℝ → ℝ}
    (hFm : Monotone F) (hη : 0 ≤ η) (hAl : 0 ≤ Al) (hAlh : Al ≤ Ah)
    (hπ0 : ∀ A ∈ Icc Al Ah, 0 ≤ π A) {S : Set ℝ} {D D' K K' : ℝ} (hD : D ≤ D')
    (hK : K ∈ S) (hK' : K' ∈ S)
    (hopt : ∀ x ∈ S, debtorUtility π Al Ah η Y₁ F D x ≤ debtorUtility π Al Ah η Y₁ F D K)
    (hopt' : ∀ x ∈ S, debtorUtility π Al Ah η Y₁ F D' x ≤ debtorUtility π Al Ah η Y₁ F D' K')
    (huniq : ∀ x ∈ S, debtorUtility π Al Ah η Y₁ F D' x = debtorUtility π Al Ah η Y₁ F D' K' →
      x = K') :
    K' ≤ K := by
  by_contra hlt
  push Not at hlt
  have hdiff := marketValue_increasing_differences hπ hη hAl hAlh hπ0 hD (hFm hlt.le)
  have h1 := hopt K' hK'
  have h2 := hopt' K hK
  unfold debtorUtility at h1 h2
  have h3 : debtorUtility π Al Ah η Y₁ F D' K = debtorUtility π Al Ah η Y₁ F D' K' := by
    unfold debtorUtility
    linarith
  exact absurd (huniq K hK h3) hlt.ne

/-! ## The market value at fixed investment -/

/-- The market value is nonnegative (O&R p. 393): for `D ≥ 0`, `η ≥ 0`, `F(K) ≥ 0`,
`0 ≤ A̲ ≤ Ā` and `π ≥ 0`. -/
theorem marketValue_nonneg {π : ℝ → ℝ} {Al Ah η : ℝ} {F : ℝ → ℝ} {D K : ℝ} (hη : 0 ≤ η)
    (hAl : 0 ≤ Al) (hAlh : Al ≤ Ah) (hπ0 : ∀ A ∈ Icc Al Ah, 0 ≤ π A) (hD : 0 ≤ D)
    (hF : 0 ≤ F K) : 0 ≤ marketValue π Al Ah η F D K := by
  unfold marketValue
  apply integral_nonneg hAlh
  intro A hA
  have : 0 ≤ η * A * F K := by
    have := hAl.trans hA.1
    positivity
  exact mul_nonneg (le_min this hD) (hπ0 A hA)

/-- The market value never exceeds face value, O&R p. 396 (`p = V/D ≤ 1`): with `∫π = 1`. -/
theorem marketValue_le_debt {π : ℝ → ℝ} (hπ : Continuous π) {Al Ah η : ℝ} {F : ℝ → ℝ}
    {D K : ℝ} (hAlh : Al ≤ Ah) (hπ0 : ∀ A ∈ Icc Al Ah, 0 ≤ π A)
    (hprob : ∫ A in Al..Ah, π A = 1) : marketValue π Al Ah η F D K ≤ D := by
  unfold marketValue
  have : (∫ A in Al..Ah, min (η * A * F K) D * π A) ≤ ∫ A in Al..Ah, D * π A := by
    apply integral_mono_on hAlh
    · exact (by fun_prop : Continuous fun A => min (η * A * F K) D * π A).intervalIntegrable _ _
    · exact (by fun_prop : Continuous fun A => D * π A).intervalIntegrable _ _
    intro A hA
    exact mul_le_mul_of_nonneg_right (min_le_right _ _) (hπ0 A hA)
  rw [integral_const_mul, hprob, mul_one] at this
  exact this

/-- The market value never exceeds the expected sanction, O&R p. 393: `V ≤ ηF(K)E A = ηF(K)`
(with `E A = 1`). -/
theorem marketValue_le_sanction {π : ℝ → ℝ} (hπ : Continuous π) {Al Ah η : ℝ} {F : ℝ → ℝ}
    {D K : ℝ} (hAlh : Al ≤ Ah) (hπ0 : ∀ A ∈ Icc Al Ah, 0 ≤ π A)
    (hmean : ∫ A in Al..Ah, A * π A = 1) : marketValue π Al Ah η F D K ≤ η * F K := by
  unfold marketValue
  have : (∫ A in Al..Ah, min (η * A * F K) D * π A) ≤ ∫ A in Al..Ah, η * F K * (A * π A) := by
    apply integral_mono_on hAlh
    · exact (by fun_prop : Continuous fun A => min (η * A * F K) D * π A).intervalIntegrable _ _
    · exact (by fun_prop : Continuous fun A => η * F K * (A * π A)).intervalIntegrable _ _
    intro A hA
    have := mul_le_mul_of_nonneg_right (min_le_left (η * A * F K) D) (hπ0 A hA)
    linarith
  rw [integral_const_mul, hmean, mul_one] at this
  exact this

/-- At fixed investment the market value is nondecreasing in face value, O&R p. 395
("conditional on the country repaying in full, creditors do better if the face value … is
higher"). -/
theorem marketValue_mono_debt {π : ℝ → ℝ} (hπ : Continuous π) {Al Ah η : ℝ} {F : ℝ → ℝ}
    {K : ℝ} (hAlh : Al ≤ Ah) (hπ0 : ∀ A ∈ Icc Al Ah, 0 ≤ π A) :
    Monotone fun D => marketValue π Al Ah η F D K := by
  intro D D' hD
  unfold marketValue
  apply integral_mono_on hAlh
  · exact (by fun_prop : Continuous fun A => min (η * A * F K) D * π A).intervalIntegrable _ _
  · exact (by fun_prop : Continuous fun A => min (η * A * F K) D' * π A).intervalIntegrable _ _
  intro A hA
  exact mul_le_mul_of_nonneg_right (min_le_min_left _ hD) (hπ0 A hA)

/-- At fixed investment the market value is concave in face value (the correct kernel of the
concavity claim on p. 395): `D ↦ V(D, K)` is concave on `ℝ`. -/
theorem marketValue_concave_debt {π : ℝ → ℝ} (hπ : Continuous π) {Al Ah η : ℝ} {F : ℝ → ℝ}
    {K : ℝ} (hAlh : Al ≤ Ah) (hπ0 : ∀ A ∈ Icc Al Ah, 0 ≤ π A) :
    ConcaveOn ℝ univ fun D => marketValue π Al Ah η F D K := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  simp only [smul_eq_mul]
  unfold marketValue
  have hi : ∀ d, IntervalIntegrable (fun A => min (η * A * F K) d * π A)
      MeasureTheory.volume Al Ah := fun d =>
    (by fun_prop : Continuous fun A => min (η * A * F K) d * π A).intervalIntegrable _ _
  rw [← integral_const_mul, ← integral_const_mul, ← integral_add ((hi x).const_mul a)
    ((hi y).const_mul b)]
  apply integral_mono_on hAlh (((hi x).const_mul a).add ((hi y).const_mul b)) (hi _)
  intro A hA
  have hp := hπ0 A hA
  set z := η * A * F K
  have t1 := mul_le_mul_of_nonneg_left (min_le_left z x) ha
  have t2 := mul_le_mul_of_nonneg_left (min_le_left z y) hb
  have t3 := mul_le_mul_of_nonneg_left (min_le_right z x) ha
  have t4 := mul_le_mul_of_nonneg_left (min_le_right z y) hb
  have hz : a * z + b * z = z := by rw [← add_mul, hab, one_mul]
  have hm : a * min z x + b * min z y ≤ min z (a * x + b * y) :=
    le_min (by linarith) (by linarith)
  nlinarith

/-! ## The debt Laffer curve, (39) -/

/-- The total derivative (39) of the debt Laffer curve, O&R p. 394: let investment `K(D)` be
differentiable at `D₀` with `K′(D₀) = k′`, `F` differentiable at `K₀ = K(D₀)` with `F′(K₀) = f₁`,
`ηF(K₀) > 0`, and the threshold `a* = D₀/(ηF(K₀))` interior. Then
`d V[D, K(D)]/dD = ∫_{a*}^{Ā}π(A)dA + [ηF′(K₀)∫_{A̲}^{a*}Aπ(A)dA]·K′(D₀)`
(the probability of full repayment plus the investment effect; the moving-limit terms cancel). -/
theorem hasDerivAt_laffer {π : ℝ → ℝ} (hπ : Continuous π) {Al Ah η : ℝ} {F Kf : ℝ → ℝ}
    {D₀ k' f₁ : ℝ} (hK : HasDerivAt Kf k' D₀) (hF : HasDerivAt F f₁ (Kf D₀))
    (hηF : 0 < η * F (Kf D₀)) (hint : threshold η F D₀ (Kf D₀) ∈ Ioo Al Ah) :
    HasDerivAt (fun D => marketValue π Al Ah η F D (Kf D))
      ((∫ A in threshold η F D₀ (Kf D₀)..Ah, π A) +
        η * f₁ * partialMean π Al (threshold η F D₀ (Kf D₀)) * k') D₀ := by
  set K₀ := Kf D₀ with hK₀
  set a := threshold η F D₀ K₀ with ha
  have hFK' : HasDerivAt (fun D => F (Kf D)) (f₁ * k') D₀ := HasDerivAt.comp (h := Kf) D₀ hF hK
  have hth : HasDerivAt (fun D => D / (η * F (Kf D)))
      ((1 * (η * F K₀) - D₀ * (η * (f₁ * k'))) / (η * F K₀) ^ 2) D₀ :=
    (hasDerivAt_id D₀).div (hFK'.const_mul η) hηF.ne'
  have hG := HasDerivAt.comp (h := fun D => D / (η * F (Kf D))) D₀
    (hasDerivAt_partialMean hπ Al a) hth
  have hH := HasDerivAt.comp (h := fun D => D / (η * F (Kf D))) D₀
    (hasDerivAt_partialProb hπ Al a) hth
  have hΦ := HasDerivAt.add ((hFK'.const_mul η).mul hG)
    ((hasDerivAt_id D₀).mul (hH.const_sub (partialProb π Al Ah)))
  have hηFa : η * F K₀ * a = D₀ := by
    rw [ha]; unfold threshold; rw [mul_div_assoc']; exact mul_div_cancel_left₀ D₀ hηF.ne'
  have hsub : partialProb π Al Ah - partialProb π Al a = ∫ A in a..Ah, π A := by
    unfold partialProb
    exact integral_interval_sub_left (hπ.intervalIntegrable _ _) (hπ.intervalIntegrable _ _)
  -- `V` equals the formula along the path near `D₀`
  have hcth : ContinuousAt (fun D => D / (η * F (Kf D))) D₀ := hth.continuousAt
  have hcF : ContinuousAt (fun D => η * F (Kf D)) D₀ := (hFK'.const_mul η).continuousAt
  have hev : (fun D => marketValue π Al Ah η F D (Kf D)) =ᶠ[𝓝 D₀]
      fun D => η * F (Kf D) * partialMean π Al (D / (η * F (Kf D))) +
        D * (partialProb π Al Ah - partialProb π Al (D / (η * F (Kf D)))) := by
    filter_upwards [hcth.preimage_mem_nhds (Ioo_mem_nhds hint.1 hint.2),
      hcF.eventually (lt_mem_nhds hηF)] with D h1 h2
    exact (valueFormula_eq_marketValue hπ h2 h1.1.le h1.2.le).symm
  refine (hΦ.congr_of_eventuallyEq hev).congr_deriv ?_
  have hc1 : ((partialMean π Al ∘ fun D => D / (η * F (Kf D))) D₀) = partialMean π Al a := rfl
  have hc2 : ((partialProb π Al ∘ fun D => D / (η * F (Kf D))) D₀) = partialProb π Al a := rfl
  simp only [hc1, hc2, id]
  rw [← hsub]
  have e : η * F K₀ * (a * π a * ((1 * (η * F K₀) - D₀ * (η * (f₁ * k'))) / (η * F K₀) ^ 2)) =
      D₀ * (π a * ((1 * (η * F K₀) - D₀ * (η * (f₁ * k'))) / (η * F K₀) ^ 2)) := by
    rw [← hηFa]; ring
  linear_combination e

/-- A differentiable function that does not rise to the right of `D₀` has a nonpositive
derivative there (used to sign `K′(D)` from `investment_antitone`).
(O&R §6.2.3–6.2.4, pp. 393–395.) -/
theorem deriv_nonpos_of_right_le {f : ℝ → ℝ} {a d : ℝ} (hf : HasDerivAt f d a)
    (h : ∀ᶠ y in 𝓝[>] a, f y ≤ f a) : d ≤ 0 := by
  have ht : Tendsto (slope f a) (𝓝[>] a) (𝓝 d) :=
    (hasDerivAt_iff_tendsto_slope.mp hf).mono_left
      (nhdsWithin_mono _ fun y (hy : a < y) => hy.ne')
  apply le_of_tendsto ht
  filter_upwards [h, self_mem_nhdsWithin] with y hy hy'
  rw [slope_def_field]
  exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hy) (by rw [mem_Ioi] at hy'; linarith)

/-- Marginal price `≤` average price, O&R p. 398, WITHOUT concavity of the Laffer curve: under
the hypotheses of `hasDerivAt_laffer`, if investment does not rise with debt (`K′(D₀) ≤ 0`,
e.g. by `investment_antitone` and `deriv_nonpos_of_right_le`), `F′(K₀) ≥ 0`, `η ≥ 0`, `D₀ > 0`,
`0 ≤ A̲` and `π ≥ 0` on `[A̲, Ā]`, then `dV[D, K(D)]/dD ≤ V[D₀, K(D₀)]/D₀`. (Indeed
`V/D = E min(ηAF/D, 1) ≥ Prob(A ≥ a*)` and the investment term is `≤ 0`.) -/
theorem marginal_le_average {π : ℝ → ℝ} (hπ : Continuous π) {Al Ah η : ℝ} {F Kf : ℝ → ℝ}
    {D₀ k' f₁ : ℝ} (hK : HasDerivAt Kf k' D₀) (hF : HasDerivAt F f₁ (Kf D₀))
    (hηF : 0 < η * F (Kf D₀)) (hint : threshold η F D₀ (Kf D₀) ∈ Ioo Al Ah)
    (hk' : k' ≤ 0) (hf₁ : 0 ≤ f₁) (hη : 0 ≤ η) (hD : 0 < D₀) (hAl : 0 ≤ Al)
    (hπ0 : ∀ A ∈ Icc Al Ah, 0 ≤ π A) {w : ℝ}
    (hw : HasDerivAt (fun D => marketValue π Al Ah η F D (Kf D)) w D₀) :
    w ≤ marketValue π Al Ah η F D₀ (Kf D₀) / D₀ := by
  rw [hw.unique (hasDerivAt_laffer hπ hK hF hηF hint)]
  set a := threshold η F D₀ (Kf D₀)
  have hG : 0 ≤ partialMean π Al a := by
    unfold partialMean
    apply integral_nonneg hint.1.le
    intro A hA
    exact mul_nonneg (hAl.trans hA.1) (hπ0 A ⟨hA.1, hA.2.trans hint.2.le⟩)
  rw [marketValue_eq hπ hηF hint.1.le hint.2.le, le_div_iff₀ hD]
  have hηG : 0 ≤ η * f₁ * partialMean π Al a := by positivity
  have h1 : η * f₁ * partialMean π Al a * k' ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hηG hk'
  have h2 : 0 ≤ η * F (Kf D₀) * partialMean π Al a := mul_nonneg hηF.le hG
  nlinarith

/-- Marginal price `≤` average price with the investment response signed by debt overhang
(O&R p. 398): as `marginal_le_average`, with `K′(D₀) ≤ 0` replaced by the hypothesis that
optimal investment does not rise with debt to the right of `D₀` — which `investment_antitone`
delivers whenever the optimum is unique. -/
theorem marginal_le_average_of_antitone {π : ℝ → ℝ} (hπ : Continuous π) {Al Ah η : ℝ}
    {F Kf : ℝ → ℝ} {D₀ k' f₁ : ℝ} (hK : HasDerivAt Kf k' D₀) (hF : HasDerivAt F f₁ (Kf D₀))
    (hηF : 0 < η * F (Kf D₀)) (hint : threshold η F D₀ (Kf D₀) ∈ Ioo Al Ah)
    (hanti : ∀ᶠ D in 𝓝[>] D₀, Kf D ≤ Kf D₀) (hf₁ : 0 ≤ f₁) (hη : 0 ≤ η) (hD : 0 < D₀)
    (hAl : 0 ≤ Al) (hπ0 : ∀ A ∈ Icc Al Ah, 0 ≤ π A) {w : ℝ}
    (hw : HasDerivAt (fun D => marketValue π Al Ah η F D (Kf D)) w D₀) :
    w ≤ marketValue π Al Ah η F D₀ (Kf D₀) / D₀ :=
  marginal_le_average hπ hK hF hηF hint (deriv_nonpos_of_right_le hK hanti) hf₁ hη hD hAl hπ0 hw

/-- A concave function that is nonnegative on `[0, ∞)` is nondecreasing there.
(O&R §6.2.3–6.2.4, pp. 393–395.) -/
theorem monotoneOn_of_concaveOn_nonneg {W : ℝ → ℝ} (hW : ConcaveOn ℝ (Ici 0) W)
    (hpos : ∀ D ∈ Ici (0 : ℝ), 0 ≤ W D) : MonotoneOn W (Ici 0) := by
  intro x hx y hy hxy
  by_contra hlt
  push Not at hlt
  rcases hxy.lt_or_eq with hxy' | hxy'
  · -- extrapolate the secant from `x` through `y` until it is negative
    set s := (W x - W y) / (y - x) with hs
    have hspos : 0 < s := div_pos (by linarith) (by linarith)
    set z := y + (W y + 1) / s with hz
    have hWy : 0 ≤ W y := hpos y hy
    have hyz : y < z := by
      rw [hz]; have := div_pos (by linarith : (0 : ℝ) < W y + 1) hspos; linarith
    have hzmem : z ∈ Ici (0 : ℝ) := by rw [mem_Ici] at hy ⊢; linarith
    -- concavity: the slope from `y` to `z` is at most the (negative) slope from `x` to `y`
    have hsl := hW.slope_anti_adjacent hx hzmem hxy' hyz
    have hsz : (W y + 1) / s * s = W y + 1 := div_mul_cancel₀ _ hspos.ne'
    have hzy : z - y = (W y + 1) / s := by rw [hz]; ring
    rw [hzy, div_le_iff₀ (div_pos (by linarith) hspos)] at hsl
    have hsx : (W y - W x) / (y - x) = -s := by rw [hs]; ring
    rw [hsx] at hsl
    have hWz : W z < 0 := by nlinarith
    linarith [hpos z hzmem]
  · rw [hxy'] at hlt; exact lt_irrefl _ hlt

/-- The Laffer curve cannot be both concave and downward-sloping, O&R p. 395 and Figure 6.7:
the book asserts that `V[D, K(D)]` "is concave, as drawn" and may decline for large `D`. Since
the market value is nonnegative (`marketValue_nonneg`), a concave Laffer curve on `[0, ∞)` would
be nondecreasing (`monotoneOn_of_concaveOn_nonneg`). So if the curve ever falls,
`W(D₂) < W(D₁)` with `0 ≤ D₁ < D₂` — the "wrong side" on which §6.2.4's debt-forgiveness
argument rests — it is NOT concave on `[0, ∞)`. -/
theorem laffer_not_concave_of_decreasing {W : ℝ → ℝ} (hpos : ∀ D ∈ Ici (0 : ℝ), 0 ≤ W D)
    {D₁ D₂ : ℝ} (hD₁ : 0 ≤ D₁) (h12 : D₁ ≤ D₂) (hfall : W D₂ < W D₁) :
    ¬ ConcaveOn ℝ (Ici 0) W := by
  intro hW
  have := monotoneOn_of_concaveOn_nonneg hW hpos (mem_Ici.mpr hD₁)
    (mem_Ici.mpr (hD₁.trans h12)) h12
  linarith

/-- A write-down on the wrong side of the Laffer curve raises the value of the debt, O&R p. 395:
if `dV[D, K(D)]/dD < 0` at `D₀`, then `V[D, K(D)] > V[D₀, K(D₀)]` for every `D < D₀` close
enough to `D₀`. -/
theorem writedown_raises_value {W : ℝ → ℝ} {D₀ w : ℝ} (hw : HasDerivAt W w D₀) (hneg : w < 0) :
    ∀ᶠ D in 𝓝[<] D₀, W D₀ < W D := by
  have ht : Tendsto (slope W D₀) (𝓝[<] D₀) (𝓝 w) :=
    (hasDerivAt_iff_tendsto_slope.mp hw).mono_left
      (nhdsWithin_mono _ fun y (hy : y < D₀) => hy.ne)
  filter_upwards [ht.eventually (gt_mem_nhds hneg), self_mem_nhdsWithin] with D hD hD'
  rw [slope_def_field] at hD
  rw [mem_Iio] at hD'
  have hden : D - D₀ < 0 := by linarith
  have := (div_neg_iff.mp hD)
  rcases this with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · linarith
  · linarith

/-- Writing down debt never hurts the debtor, O&R p. 395 ("the debtor naturally is better off as
well"): at every investment level, `U(D′, K) ≤ U(D, K)` for `D ≤ D′`. -/
theorem debtorUtility_antitone_debt {π : ℝ → ℝ} (hπ : Continuous π) {Al Ah η Y₁ : ℝ}
    {F : ℝ → ℝ} (hAlh : Al ≤ Ah) (hπ0 : ∀ A ∈ Icc Al Ah, 0 ≤ π A) {D D' : ℝ} (hD : D ≤ D')
    (K : ℝ) : debtorUtility π Al Ah η Y₁ F D' K ≤ debtorUtility π Al Ah η Y₁ F D K := by
  unfold debtorUtility
  have := marketValue_mono_debt (η := η) (F := F) (K := K) hπ hAlh hπ0 hD
  simp only at this
  linarith

/-- The debtor's envelope theorem, O&R p. 395/399: along optimal investment (FOC (38) at
`(D₀, K(D₀))`), `dU[D, K(D)]/dD = −∫_{a*}^{Ā}π(A)dA = −Prob(full repayment)`: the investment
response has only a second-order effect. -/
theorem hasDerivAt_debtor_value {π : ℝ → ℝ} (hπ : Continuous π) {Al Ah η Y₁ : ℝ}
    {F Kf : ℝ → ℝ} {D₀ k' f₁ : ℝ} (hK : HasDerivAt Kf k' D₀) (hF : HasDerivAt F f₁ (Kf D₀))
    (hηF : 0 < η * F (Kf D₀)) (hint : threshold η F D₀ (Kf D₀) ∈ Ioo Al Ah)
    (hfoc : f₁ * (1 - η * partialMean π Al (threshold η F D₀ (Kf D₀))) = 1) :
    HasDerivAt (fun D => debtorUtility π Al Ah η Y₁ F D (Kf D))
      (-∫ A in threshold η F D₀ (Kf D₀)..Ah, π A) D₀ := by
  have hL := hasDerivAt_laffer hπ hK hF hηF hint
  have hFK : HasDerivAt (fun D => F (Kf D)) (f₁ * k') D₀ := HasDerivAt.comp (h := Kf) D₀ hF hK
  have h := ((hK.const_sub Y₁).add hFK).sub hL
  unfold debtorUtility
  refine h.congr_deriv ?_
  linear_combination k' * hfoc

/-! ## Debt buybacks, (40) and footnote 48 -/

/-- The country's utility after buying back `Q` at the post-buyback price, O&R p. 397:
`U₁(Q) = Y₁ − pQ − K(D−Q) + F(K(D−Q)) − W(D−Q)`, `p = W(D−Q)/(D−Q)`, where `W(D) = V[D, K(D)]`
is the Laffer curve and `K(D)` optimal investment. -/
noncomputable def buybackUtility (Y₁ D : ℝ) (F Kf W : ℝ → ℝ) (Q : ℝ) : ℝ :=
  Y₁ - W (D - Q) / (D - Q) * Q - Kf (D - Q) + F (Kf (D - Q)) - W (D - Q)

/-- Footnote 48, O&R p. 398: for a buyback of any size `Q` (with `D − Q ≠ 0` and `W`, `K`
differentiable at `D − Q`, `F` at `K(D−Q)`),
`dU₁/dQ = {[(D−Q)W′ − W]/(D−Q)²}Q − W/(D−Q) + K′ − F′K′ + W′`, where `W′ = V_D + V_K K′`. -/
theorem hasDerivAt_buybackUtility {Y₁ D Q w k' f₁ : ℝ} {F Kf W : ℝ → ℝ}
    (hW : HasDerivAt W w (D - Q)) (hK : HasDerivAt Kf k' (D - Q))
    (hF : HasDerivAt F f₁ (Kf (D - Q))) (hDQ : D - Q ≠ 0) :
    HasDerivAt (buybackUtility Y₁ D F Kf W)
      (((D - Q) * w - W (D - Q)) / (D - Q) ^ 2 * Q - W (D - Q) / (D - Q) + k' - f₁ * k' + w)
      Q := by
  have hs : HasDerivAt (fun Q => D - Q) (-1) Q := by
    simpa using (hasDerivAt_id Q).const_sub D
  have hWs := HasDerivAt.comp (h := fun Q => D - Q) Q hW hs
  have hKs := HasDerivAt.comp (h := fun Q => D - Q) Q hK hs
  have hFs := HasDerivAt.comp (h := fun Q => Kf (D - Q)) Q hF hKs
  have hp := hWs.div hs hDQ
  have h := ((((hp.mul (hasDerivAt_id Q)).const_sub Y₁).sub hKs).add hFs).sub hWs
  unfold buybackUtility
  refine h.congr_deriv ?_
  simp only [Function.comp, id, Pi.div_apply]
  field_simp
  ring

/-- Equation (40), O&R p. 398: at `Q = 0`,
`dU₁/dQ|₀ = −[F′(K(D)) − 1]K′(D) − [V/D − dV/dD]` (the investment gain minus the gap between
average and marginal price). -/
theorem buyback_marginal_eq40 {Y₁ D w k' f₁ : ℝ} {F Kf W : ℝ → ℝ} (hW : HasDerivAt W w D)
    (hK : HasDerivAt Kf k' D) (hF : HasDerivAt F f₁ (Kf D)) (hD : D ≠ 0) :
    HasDerivAt (buybackUtility Y₁ D F Kf W) (-(f₁ - 1) * k' - (W D / D - w)) 0 := by
  have h := hasDerivAt_buybackUtility (Y₁ := Y₁) (Q := 0) (by simpa using hW)
    (by simpa using hK) (by simpa using hF) (by simpa using hD)
  refine h.congr_deriv ?_
  simp only [sub_zero, mul_zero]
  ring

/-- The closed form of p. 399: substituting (38) (`F′[1 − ηG] = 1`), (37)
(`W(D) = ηF G + D·P`) and (39) (`W′ = P + ηF′G·K′`) into (40) gives
`dU₁/dQ|₀ = −(ηF(K)/D)∫_{A̲}^{a*}Aπ(A)dA`, where `G = ∫_{A̲}^{a*}Aπ`, `P = ∫_{a*}^{Ā}π`: the
investment gains go entirely to the creditors. -/
theorem buyback_closed_form {D k' f₁ η FK G P WD w : ℝ} (hD : D ≠ 0)
    (hfoc : f₁ * (1 - η * G) = 1) (h37 : WD = η * FK * G + D * P)
    (h39 : w = P + η * f₁ * G * k') :
    -(f₁ - 1) * k' - (WD / D - w) = -(η * FK / D) * G := by
  rw [h37, h39]
  field_simp
  linear_combination (-(D * k')) * hfoc

/-- A buyback hurts a country that might default, O&R p. 399: with the closed form, if
`η F(K) > 0`, `D > 0` and `∫_{A̲}^{a*}Aπ > 0` (default has positive probability, `A > 0`), then
`dU₁/dQ|₀ < 0`. Combined with `buyback_marginal_eq40`, `hasDerivAt_laffer` and `foc38`. -/
theorem buyback_hurts_debtor {Y₁ D w k' f₁ η G P : ℝ} {F Kf W : ℝ → ℝ}
    (hW : HasDerivAt W w D) (hK : HasDerivAt Kf k' D) (hF : HasDerivAt F f₁ (Kf D))
    (hD : 0 < D) (hηF : 0 < η * F (Kf D)) (hG : 0 < G)
    (hfoc : f₁ * (1 - η * G) = 1) (h37 : W D = η * F (Kf D) * G + D * P)
    (h39 : w = P + η * f₁ * G * k') {u : ℝ}
    (hu : HasDerivAt (buybackUtility Y₁ D F Kf W) u 0) : u < 0 := by
  rw [hu.unique (buyback_marginal_eq40 hW hK hF hD.ne'),
    buyback_closed_form hD.ne' hfoc h37 h39]
  have : 0 < η * F (Kf D) / D * G := by positivity
  linarith

/-- The creditors gain from a buyback, O&R p. 398 ("creditors always gain"): their receipts
`R(Q) = pQ + W(D − Q)` satisfy `R′(0) = W(D)/D − W′(D) ≥ 0` whenever marginal price is at most
average price (`marginal_le_average`). -/
theorem creditors_gain_from_buyback {D w : ℝ} {W : ℝ → ℝ} (hW : HasDerivAt W w D)
    (hD : D ≠ 0) (hmarg : w ≤ W D / D) :
    HasDerivAt (fun Q => W (D - Q) / (D - Q) * Q + W (D - Q)) (W D / D - w) 0 ∧
      0 ≤ W D / D - w := by
  refine ⟨?_, by linarith⟩
  have hs : HasDerivAt (fun Q => D - Q) (-1) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_sub D
  have hW0 : HasDerivAt W w (D - 0) := by simpa using hW
  have hWs := HasDerivAt.comp (h := fun Q => D - Q) 0 hW0 hs
  have hp := hWs.div hs (by simpa using hD)
  have h := (hp.mul (hasDerivAt_id (0 : ℝ))).add hWs
  refine h.congr_deriv ?_
  simp only [Function.comp, id, sub_zero, mul_zero, Pi.div_apply]
  ring

/-! ## Application: Bolivia's 1988 buyback (Table 6.2) -/

/-- Table 6.2 and p. 400: Bolivia spent `308 × 0.11 = 33.88 ≈ $34` million to retire `$308`
million of its `$670` million debt; the remaining face value was `670 − 308 = $362` million;
the market value fell only from `670 × 0.06 = $40.2` million to `362 × 0.11 = $39.82 ≈ $39.8`
million, i.e. by `$0.4` million, less than `1.2` percent of the `$34` million spent; the face
value fell "by just under a half" (`308/670 < 1/2`) while the price nearly doubled. -/
theorem bolivia_arithmetic :
    (308 : ℝ) * 0.11 = 33.88 ∧ (670 : ℝ) - 308 = 362 ∧ (670 : ℝ) * 0.06 = 40.2 ∧
      (362 : ℝ) * 0.11 = 39.82 ∧ (40.2 : ℝ) - 39.8 = 0.4 ∧ (0.4 : ℝ) / 34 < 0.012 ∧
      (308 : ℝ) / 670 < 1 / 2 ∧ (0.11 : ℝ) / 0.06 < 2 := by
  norm_num

/-! ## Exercise 6: debt overhang and debt forgiveness (pp. 427–428)

`U₁ = log C₁ + β log C₂`, `Y₂ = I^α` (`0 < α`), full depreciation; the debt is so large that
creditors collect `ηY₂`. -/

/-- The country's objective when it defaults, Exercise 6(a): `log(Y₁ − I) + β log[(1−η)I^α]`. -/
noncomputable def exDefaultObjective (Y₁ α β η I : ℝ) : ℝ :=
  Real.log (Y₁ - I) + β * Real.log ((1 - η) * I ^ α)

/-- The investment under certain default, Exercise 6(a): `I^D = αβY₁/(1 + αβ)`. -/
noncomputable def exDefaultInvestment (Y₁ α β : ℝ) : ℝ := α * β * Y₁ / (1 + α * β)

/-- Exercise 6(a): with `Y₁, α, β > 0` and `η < 1`, `I^D = αβY₁/(1+αβ)` lies in `(0, Y₁)` and
maximises `log(Y₁ − I) + β log[(1−η)I^α]` over `0 < I < Y₁`. It does not depend on `η`
(a proportional levy does not distort investment when default is certain); creditors receive
`η(I^D)^α`. -/
theorem ex6a_default_investment {Y₁ α β η : ℝ} (hY : 0 < Y₁) (hα : 0 < α) (hβ : 0 < β)
    (hη1 : η < 1) :
    0 < exDefaultInvestment Y₁ α β ∧ exDefaultInvestment Y₁ α β < Y₁ ∧
      ∀ I, 0 < I → I < Y₁ → exDefaultObjective Y₁ α β η I ≤
        exDefaultObjective Y₁ α β η (exDefaultInvestment Y₁ α β) := by
  have hab : 0 < α * β := mul_pos hα hβ
  set ID := exDefaultInvestment Y₁ α β with hID
  have hIDpos : 0 < ID := by rw [hID]; unfold exDefaultInvestment; positivity
  have hYID : Y₁ - ID = Y₁ / (1 + α * β) := by
    rw [hID]; unfold exDefaultInvestment; field_simp; ring
  have hIDlt : ID < Y₁ := by
    have : 0 < Y₁ / (1 + α * β) := by positivity
    linarith
  refine ⟨hIDpos, hIDlt, fun I hI0 hI1 => ?_⟩
  unfold exDefaultObjective
  have h1η : 0 < 1 - η := by linarith
  rw [Real.log_mul h1η.ne' (Real.rpow_pos_of_pos hI0 α).ne', Real.log_rpow hI0,
    Real.log_mul h1η.ne' (Real.rpow_pos_of_pos hIDpos α).ne', Real.log_rpow hIDpos]
  have hYI : 0 < Y₁ - I := by linarith
  have hYIDp : 0 < Y₁ - ID := by linarith
  have t1 : Real.log (Y₁ - I) - Real.log (Y₁ - ID) ≤ (Y₁ - I) / (Y₁ - ID) - 1 := by
    rw [← Real.log_div hYI.ne' hYIDp.ne']
    exact Real.log_le_sub_one_of_pos (div_pos hYI hYIDp)
  have t2 : Real.log I - Real.log ID ≤ I / ID - 1 := by
    rw [← Real.log_div hI0.ne' hIDpos.ne']
    exact Real.log_le_sub_one_of_pos (div_pos hI0 hIDpos)
  have t2' := mul_le_mul_of_nonneg_left t2 hab.le
  have key : (Y₁ - I) / (Y₁ - ID) - 1 + α * β * (I / ID - 1) = 0 := by
    rw [hYID, hID]; unfold exDefaultInvestment; field_simp; ring
  nlinarith

/-- The repay-branch objective after a write-down to face value `Dw`, Exercise 6(b):
`log(Y₁ − I) + β log(I^α − Dw)`. -/
noncomputable def exRepayObjective (Y₁ α β Dw I : ℝ) : ℝ :=
  Real.log (Y₁ - I) + β * Real.log (I ^ α - Dw)

/-- The country's objective under face value `D` (it pays `min{D, ηI^α}`), Exercise 6(b). -/
noncomputable def exObjective (Y₁ α β η D I : ℝ) : ℝ :=
  Real.log (Y₁ - I) + β * Real.log (I ^ α - min D (η * I ^ α))

/-- Exercise 6(b), the Pareto-improving write-down: writing the face value down to `η(I^D)^α`
(the amount creditors expect anyway). With `Y₁, α, β > 0`, `0 < η < 1`:
(i) some `I₁ ∈ (I^D, Y₁)` gives the country strictly more than its pre-write-down optimum
(the marginal return above `I^D` is now fully retained: the right derivative at `I^D` is
`−1/(Y₁ − I^D) + αβ/[(1−η)I^D] > 0`); (ii) every investment `I ≤ I^D` gives at most the
pre-write-down optimum; hence (iii) at any optimum after the write-down the country invests
more than `I^D` and pays exactly `η(I^D)^α` — the write-down costs the creditors nothing. -/
theorem ex6b_writedown {Y₁ α β η : ℝ} (hY : 0 < Y₁) (hα : 0 < α) (hβ : 0 < β)
    (hη0 : 0 < η) (hη1 : η < 1) :
    (∃ I₁, exDefaultInvestment Y₁ α β < I₁ ∧ I₁ < Y₁ ∧
        exObjective Y₁ α β η (η * exDefaultInvestment Y₁ α β ^ α) I₁ >
          exDefaultObjective Y₁ α β η (exDefaultInvestment Y₁ α β)) ∧
      (∀ I, 0 < I → I ≤ exDefaultInvestment Y₁ α β →
        exObjective Y₁ α β η (η * exDefaultInvestment Y₁ α β ^ α) I ≤
          exDefaultObjective Y₁ α β η (exDefaultInvestment Y₁ α β)) ∧
      (∀ I, 0 < I → I < Y₁ → (∀ J, 0 < J → J < Y₁ →
          exObjective Y₁ α β η (η * exDefaultInvestment Y₁ α β ^ α) J ≤
            exObjective Y₁ α β η (η * exDefaultInvestment Y₁ α β ^ α) I) →
        exDefaultInvestment Y₁ α β < I ∧
          min (η * exDefaultInvestment Y₁ α β ^ α) (η * I ^ α) =
            η * exDefaultInvestment Y₁ α β ^ α) := by
  obtain ⟨hIDpos, hIDlt, hopt⟩ := ex6a_default_investment hY hα hβ hη1
  set ID := exDefaultInvestment Y₁ α β with hID
  set Dw := η * ID ^ α with hDw
  have h1η : 0 < 1 - η := by linarith
  have hab : 0 < α * β := mul_pos hα hβ
  have hIDa : 0 < ID ^ α := Real.rpow_pos_of_pos hIDpos α
  -- on `I ≥ I^D` the country repays `Dw`; on `I ≤ I^D` it pays the levy
  have hmin_hi : ∀ I, ID ≤ I → min Dw (η * I ^ α) = Dw := by
    intro I hI
    apply min_eq_left
    rw [hDw]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hIDpos.le hI hα.le) hη0.le
  have hmin_lo : ∀ I, 0 < I → I ≤ ID → min Dw (η * I ^ α) = η * I ^ α := by
    intro I hI0 hI
    apply min_eq_right
    rw [hDw]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hI0.le hI hα.le) hη0.le
  have hlo : ∀ I, 0 < I → I ≤ ID →
      exObjective Y₁ α β η Dw I ≤ exDefaultObjective Y₁ α β η ID := by
    intro I hI0 hI
    have heq : exObjective Y₁ α β η Dw I = exDefaultObjective Y₁ α β η I := by
      unfold exObjective exDefaultObjective
      rw [hmin_lo I hI0 hI]
      ring_nf
    rw [heq]
    exact hopt I hI0 (lt_of_le_of_lt hI hIDlt)
  -- the repay branch at `I^D` equals the old optimum, and has positive derivative there
  have hg0 : exRepayObjective Y₁ α β Dw ID = exDefaultObjective Y₁ α β η ID := by
    unfold exRepayObjective exDefaultObjective
    rw [hDw]
    ring_nf
  have hYID : 0 < Y₁ - ID := by linarith
  have hpow : HasDerivAt (fun I => I ^ α) (α * ID ^ (α - 1)) ID :=
    Real.hasDerivAt_rpow_const (Or.inl hIDpos.ne')
  have hgap : 0 < ID ^ α - Dw := by rw [hDw]; nlinarith
  have hd1 : HasDerivAt (fun I => Real.log (Y₁ - I)) (-1 / (Y₁ - ID)) ID := by
    have := ((hasDerivAt_id ID).const_sub Y₁).log hYID.ne'
    simpa using this
  have hd2 : HasDerivAt (fun I => Real.log (I ^ α - Dw)) (α * ID ^ (α - 1) / (ID ^ α - Dw)) ID :=
    (hpow.sub_const Dw).log hgap.ne'
  have hg : HasDerivAt (exRepayObjective Y₁ α β Dw)
      (-1 / (Y₁ - ID) + β * (α * ID ^ (α - 1) / (ID ^ α - Dw))) ID := by
    unfold exRepayObjective
    exact hd1.add (hd2.const_mul β)
  have hgpos : 0 < -1 / (Y₁ - ID) + β * (α * ID ^ (α - 1) / (ID ^ α - Dw)) := by
    rw [Real.rpow_sub_one hIDpos.ne', hDw]
    have e1 : Y₁ - ID = Y₁ / (1 + α * β) := by
      rw [hID]; unfold exDefaultInvestment; field_simp; ring
    have e2 : β * (α * (ID ^ α / ID) / (ID ^ α - η * ID ^ α)) = (1 + α * β) / ((1 - η) * Y₁) := by
      rw [hID]; unfold exDefaultInvestment
      have : (α * β * Y₁ / (1 + α * β)) ^ α ≠ 0 := (Real.rpow_pos_of_pos (by positivity) α).ne'
      field_simp
    rw [e1, e2]
    have : -1 / (Y₁ / (1 + α * β)) = -(1 + α * β) / Y₁ := by field_simp
    rw [this, div_add_div _ _ hY.ne' (by positivity), div_pos_iff_of_pos_right (by positivity)]
    have e3 : -(1 + α * β) * ((1 - η) * Y₁) + Y₁ * (1 + α * β) = (1 + α * β) * Y₁ * η := by ring
    rw [e3]
    positivity
  -- a slightly larger investment is strictly better
  have ht : Tendsto (slope (exRepayObjective Y₁ α β Dw) ID) (𝓝[>] ID)
      (𝓝 (-1 / (Y₁ - ID) + β * (α * ID ^ (α - 1) / (ID ^ α - Dw)))) :=
    (hasDerivAt_iff_tendsto_slope.mp hg).mono_left
      (nhdsWithin_mono _ fun y (hy : ID < y) => hy.ne')
  have hev : ∀ᶠ I in 𝓝[>] ID, ID < I ∧ I < Y₁ ∧
      exRepayObjective Y₁ α β Dw ID < exRepayObjective Y₁ α β Dw I := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds hIDlt),
      ht.eventually (lt_mem_nhds hgpos)] with I h1 h2 h3
    rw [mem_Ioi] at h1
    rw [slope_def_field] at h3
    exact ⟨h1, h2, by have := (div_pos_iff_of_pos_right (by linarith)).mp h3; linarith⟩
  obtain ⟨I₁, h1, h2, h3⟩ := hev.exists
  have hI₁ : exObjective Y₁ α β η Dw I₁ = exRepayObjective Y₁ α β Dw I₁ := by
    unfold exObjective exRepayObjective
    rw [hmin_hi I₁ h1.le]
  refine ⟨⟨I₁, h1, h2, by rw [hI₁, ← hg0]; exact h3⟩, hlo, fun I hI0 hI1 hIopt => ?_⟩
  have hbetter : exDefaultObjective Y₁ α β η ID < exObjective Y₁ α β η Dw I := by
    have := hIopt I₁ (hIDpos.trans h1) h2
    rw [hI₁] at this
    linarith
  have hgt : ID < I := by
    by_contra hle
    push Not at hle
    linarith [hlo I hI0 hle]
  exact ⟨hgt, hmin_hi I hgt.le⟩

/-- Repayment is (weakly) preferred at face value `D` in Exercise 6(c): some investment with
positive consumption, repaying `D` in full, is at least as good as the default optimum. -/
def ExRepayPreferred (Y₁ α β η D : ℝ) : Prop :=
  ∃ I, 0 < I ∧ I < Y₁ ∧ D < I ^ α ∧
    exDefaultObjective Y₁ α β η (exDefaultInvestment Y₁ α β) ≤ exRepayObjective Y₁ α β D I

/-- Creditors' receipts at face value `D`, Exercise 6(c): `D` if the country repays (ties
repay), otherwise the levy `η(I^D)^α` at the default investment `I^D`. -/
noncomputable def exReceipts (Y₁ α β η D : ℝ) : ℝ := by
  classical
  exact if ExRepayPreferred Y₁ α β η D then D else η * exDefaultInvestment Y₁ α β ^ α

/-- Exercise 6(c), the creditors' optimal write-down and the certainty Laffer curve: with
`Y₁, α, β > 0`, `0 < η < 1`, let `D*` be the supremum of the face values the country is willing
to repay. Then (i) `η(I^D)^α < D* ≤ Y₁^α` — creditors should forgive less than down to
`η(I^D)^α`; (ii) the country repays every `D < D*` (receipts `D`) and defaults on every
`D > D*` (receipts `η(I^D)^α < D*`): receipts jump down above `D*`; (iii) receipts never
exceed `D*` and come arbitrarily close to it, so the creditors should write the debt down to
`D*`. -/
theorem ex6c_optimal_writedown {Y₁ α β η : ℝ} (hY : 0 < Y₁) (hα : 0 < α) (hβ : 0 < β)
    (hη0 : 0 < η) (hη1 : η < 1) :
    let S := {D : ℝ | ExRepayPreferred Y₁ α β η D}
    η * exDefaultInvestment Y₁ α β ^ α < sSup S ∧ sSup S ≤ Y₁ ^ α ∧
      (∀ D, D < sSup S → ExRepayPreferred Y₁ α β η D ∧ exReceipts Y₁ α β η D = D) ∧
      (∀ D, sSup S < D → exReceipts Y₁ α β η D = η * exDefaultInvestment Y₁ α β ^ α) ∧
      (∀ D, exReceipts Y₁ α β η D ≤ sSup S) ∧
      (∀ ε > 0, ∃ D, sSup S - ε < exReceipts Y₁ α β η D) := by
  intro S
  obtain ⟨hIDpos, hIDlt, -⟩ := ex6a_default_investment hY hα hβ hη1
  obtain ⟨⟨I₁, h1, h2, h3⟩, -, -⟩ := ex6b_writedown hY hα hβ hη0 hη1
  set ID := exDefaultInvestment Y₁ α β with hID
  set Dw := η * ID ^ α with hDw
  set V := exDefaultObjective Y₁ α β η ID with hV
  -- lower set
  have hlower : ∀ D D', D ≤ D' → ExRepayPreferred Y₁ α β η D' → ExRepayPreferred Y₁ α β η D := by
    rintro D D' hDD ⟨I, i0, i1, i2, i3⟩
    refine ⟨I, i0, i1, lt_of_le_of_lt hDD i2, i3.trans ?_⟩
    unfold exRepayObjective
    have := Real.log_le_log (by linarith) (by linarith : I ^ α - D' ≤ I ^ α - D)
    nlinarith
  -- bounded above by `Y₁^α`
  have hbdd : ∀ D ∈ S, D ≤ Y₁ ^ α := by
    rintro D ⟨I, i0, i1, i2, -⟩
    exact (i2.trans (Real.rpow_lt_rpow i0.le i1 hα)).le
  -- a face value above `Dw` is repaid
  have hI₁a : Dw < I₁ ^ α := by
    have : ID ^ α < I₁ ^ α := Real.rpow_lt_rpow hIDpos.le h1 hα
    rw [hDw]; nlinarith [Real.rpow_pos_of_pos hIDpos α]
  have hrep : exRepayObjective Y₁ α β Dw I₁ > V := by
    have hmin : min Dw (η * I₁ ^ α) = Dw := by
      apply min_eq_left; rw [hDw]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hIDpos.le h1.le hα.le) hη0.le
    unfold exObjective at h3
    unfold exRepayObjective
    rw [hmin] at h3
    exact h3
  have hcont : ContinuousAt (fun D => exRepayObjective Y₁ α β D I₁) Dw := by
    unfold exRepayObjective
    apply ContinuousAt.add continuousAt_const
    apply ContinuousAt.mul continuousAt_const
    exact (continuousAt_const.sub continuousAt_id).log
      (by change I₁ ^ α - Dw ≠ 0; exact (sub_pos.mpr hI₁a).ne')
  have hev : ∀ᶠ D in 𝓝 Dw, V < exRepayObjective Y₁ α β D I₁ ∧ D < I₁ ^ α :=
    (hcont.eventually (lt_mem_nhds hrep)).and (Iio_mem_nhds hI₁a)
  obtain ⟨D₁, hD₁, hD₁'⟩ : ∃ D₁, Dw < D₁ ∧ V < exRepayObjective Y₁ α β D₁ I₁ ∧ D₁ < I₁ ^ α :=
    ((hev.filter_mono nhdsWithin_le_nhds).and (self_mem_nhdsWithin (s := Ioi Dw))).exists.imp
      fun D h => ⟨h.2, h.1⟩
  have hD₁S : D₁ ∈ S := ⟨I₁, hIDpos.trans h1, h2, hD₁'.2, hD₁'.1.le⟩
  have hne : S.Nonempty := ⟨D₁, hD₁S⟩
  have hbddA : BddAbove S := ⟨Y₁ ^ α, hbdd⟩
  have hsup_ge : D₁ ≤ sSup S := le_csSup hbddA hD₁S
  have hbelow : ∀ D, D < sSup S → ExRepayPreferred Y₁ α β η D := by
    intro D hD
    obtain ⟨D', hD'S, hD'⟩ := exists_lt_of_lt_csSup hne hD
    exact hlower D D' hD'.le hD'S
  have habove : ∀ D, sSup S < D → ¬ ExRepayPreferred Y₁ α β η D := by
    intro D hD hS
    exact absurd (le_csSup hbddA hS) (not_le.mpr hD)
  have hrec_lt : Dw < sSup S := lt_of_lt_of_le hD₁ hsup_ge
  refine ⟨hrec_lt, csSup_le hne hbdd, fun D hD => ⟨hbelow D hD, ?_⟩, fun D hD => ?_, ?_, ?_⟩
  · simp only [exReceipts, hbelow D hD, ↓reduceIte]
  · simp only [exReceipts, habove D hD, ↓reduceIte]
    rfl
  · intro D
    unfold exReceipts
    split_ifs with h
    · exact le_csSup hbddA h
    · exact hrec_lt.le
  · intro ε hε
    refine ⟨sSup S - ε / 2, ?_⟩
    have hlt : sSup S - ε / 2 < sSup S := by linarith
    simp only [exReceipts, hbelow _ hlt, ↓reduceIte]
    linarith

/-- Exercise 6(c), attainment: the supremum `D*` of the face values the country is willing to
repay is itself repaid, so the creditors' optimal write-down (to `D*`, receipts `D*`) is
attained, and `D*` maximises the creditors' receipts. Proof: plans that make repayment
acceptable at `D` near `D*` have investment bounded away from `Y₁` and output bounded away
from `D` (log bounds); on that compact set the repay objective at `D*` attains a maximum, and
the uniform estimate `R(D, I) − R(D*, I) ≤ β(D* − D)/(I^α − D*)` shows it is at least the
default value. (`Y₁, α, β > 0`, `0 < η < 1`.) -/
theorem ex6c_attained {Y₁ α β η : ℝ} (hY : 0 < Y₁) (hα : 0 < α) (hβ : 0 < β)
    (hη0 : 0 < η) (hη1 : η < 1) :
    ExRepayPreferred Y₁ α β η (sSup {D : ℝ | ExRepayPreferred Y₁ α β η D}) ∧
      exReceipts Y₁ α β η (sSup {D : ℝ | ExRepayPreferred Y₁ α β η D}) =
        sSup {D : ℝ | ExRepayPreferred Y₁ α β η D} ∧
      ∀ D, exReceipts Y₁ α β η D ≤
        exReceipts Y₁ α β η (sSup {D : ℝ | ExRepayPreferred Y₁ α β η D}) := by
  have h6 := ex6c_optimal_writedown hY hα hβ hη0 hη1
  dsimp only at h6
  obtain ⟨hlt, -, hbelow, -, hle, -⟩ := h6
  set Ds := sSup {D : ℝ | ExRepayPreferred Y₁ α β η D} with hDs
  obtain ⟨hIDpos, -, -⟩ := ex6a_default_investment (η := η) hY hα hβ hη1
  set V := exDefaultObjective Y₁ α β η (exDefaultInvestment Y₁ α β) with hV
  have hDw : 0 < η * exDefaultInvestment Y₁ α β ^ α :=
    mul_pos hη0 (Real.rpow_pos_of_pos hIDpos α)
  have hDs0 : 0 < Ds := hDw.trans hlt
  set e1 := Real.exp (V - β * Real.log (Y₁ ^ α)) with he1
  set e2 := Real.exp ((V - Real.log Y₁) / β) with he2
  have he1p : 0 < e1 := Real.exp_pos _
  have he2p : 0 < e2 := Real.exp_pos _
  -- bounds on any plan making repayment acceptable at `D ≥ 0`
  have hbounds : ∀ D I, 0 ≤ D → 0 < I → I < Y₁ → D < I ^ α →
      V ≤ exRepayObjective Y₁ α β D I → I ≤ Y₁ - e1 ∧ D + e2 ≤ I ^ α := by
    intro D I hD hI0 hI1 hDI hR
    unfold exRepayObjective at hR
    have hIa : I ^ α < Y₁ ^ α := Real.rpow_lt_rpow hI0.le hI1 hα
    have hl1 : Real.log (I ^ α - D) ≤ Real.log (Y₁ ^ α) :=
      Real.log_le_log (by linarith) (by linarith)
    have hl2 : Real.log (Y₁ - I) ≤ Real.log Y₁ := Real.log_le_log (by linarith) (by linarith)
    constructor
    · have : V - β * Real.log (Y₁ ^ α) ≤ Real.log (Y₁ - I) := by nlinarith
      have := Real.exp_le_exp.mpr this
      rw [Real.exp_log (by linarith)] at this
      linarith
    · have : (V - Real.log Y₁) / β ≤ Real.log (I ^ α - D) := by
        rw [div_le_iff₀ hβ]; nlinarith
      have := Real.exp_le_exp.mpr this
      rw [Real.exp_log (by linarith)] at this
      linarith
  set C := Icc 0 (Y₁ - e1) ∩ {I : ℝ | Ds + e2 / 2 ≤ I ^ α} with hC
  have hCc : IsCompact C := isCompact_Icc.inter_right
    (isClosed_le continuous_const (Real.continuous_rpow_const hα.le))
  have hCpos : ∀ I ∈ C, 0 < Y₁ - I ∧ 0 < I ^ α - Ds := by
    intro I hI
    have h1 : I ≤ Y₁ - e1 := hI.1.2
    have h2 : Ds + e2 / 2 ≤ I ^ α := hI.2
    constructor <;> linarith
  -- plans near `D*` lie in `C`
  have hnear : ∀ D, 0 ≤ D → D < Ds → Ds - D ≤ e2 / 2 →
      ∃ I ∈ C, V ≤ exRepayObjective Y₁ α β D I := by
    intro D hD0 hDlt hDc
    obtain ⟨I, hI0, hI1, hDI, hR⟩ := (hbelow D hDlt).1
    obtain ⟨b1, b2⟩ := hbounds D I hD0 hI0 hI1 hDI hR
    exact ⟨I, ⟨⟨hI0.le, b1⟩, by change Ds + e2 / 2 ≤ I ^ α; linarith⟩, hR⟩
  have hD0 : 0 ≤ max (Ds - e2 / 4) (Ds / 2) := le_max_of_le_right (by linarith)
  obtain ⟨I₀, hI₀C, -⟩ := hnear _ hD0 (max_lt (by linarith) (by linarith))
    (by have := le_max_left (Ds - e2 / 4) (Ds / 2); linarith)
  have hψ : ContinuousOn (exRepayObjective Y₁ α β Ds) C := by
    intro I hI
    obtain ⟨p1, p2⟩ := hCpos I hI
    apply ContinuousAt.continuousWithinAt
    unfold exRepayObjective
    apply ContinuousAt.add
    · exact (continuousAt_const.sub continuousAt_id).log p1.ne'
    · apply ContinuousAt.mul continuousAt_const
      exact ((Real.continuous_rpow_const hα.le).continuousAt.sub continuousAt_const).log p2.ne'
  obtain ⟨Is, hIsC, hmax⟩ := hCc.exists_isMaxOn ⟨I₀, hI₀C⟩ hψ
  -- the maximum is at least the default value
  have hVle : V ≤ exRepayObjective Y₁ α β Ds Is := by
    by_contra hcon
    push Not at hcon
    set g := V - exRepayObjective Y₁ α β Ds Is with hg
    have hgp : 0 < g := by linarith
    set δ := min (e2 / 4) (g * e2 / (4 * β)) with hδ
    have hδp : 0 < δ := lt_min (by positivity) (by positivity)
    set D₁ := max (Ds - δ) (Ds / 2) with hD₁
    have hD₁0 : 0 ≤ D₁ := le_max_of_le_right (by linarith)
    have hD₁lt : D₁ < Ds := max_lt (by linarith) (by linarith)
    have hD₁c : Ds - D₁ ≤ δ := by have := le_max_left (Ds - δ) (Ds / 2); linarith
    have hδ1 : δ ≤ e2 / 4 := min_le_left _ _
    have hδ2 : δ ≤ g * e2 / (4 * β) := min_le_right _ _
    obtain ⟨I, hIC, hR⟩ := hnear D₁ hD₁0 hD₁lt (by linarith)
    obtain ⟨p1, p2⟩ := hCpos I hIC
    have hIa : Ds + e2 / 2 ≤ I ^ α := hIC.2
    have hM := isMaxOn_iff.mp hmax I hIC
    -- `R(D₁, I) − R(D*, I) ≤ β(D* − D₁)/(I^α − D*)`
    have hq : 0 < (I ^ α - D₁) / (I ^ α - Ds) := div_pos (by linarith) p2
    have hlog : Real.log (I ^ α - D₁) - Real.log (I ^ α - Ds) ≤
        (Ds - D₁) / (I ^ α - Ds) := by
      rw [← Real.log_div (by linarith) p2.ne']
      have := Real.log_le_sub_one_of_pos hq
      have e : (I ^ α - D₁) / (I ^ α - Ds) - 1 = (Ds - D₁) / (I ^ α - Ds) := by
        field_simp; ring
      linarith
    have hfrac : (Ds - D₁) / (I ^ α - Ds) ≤ δ / (e2 / 2) := by
      apply div_le_div₀ hδp.le hD₁c (by positivity) (by linarith)
    have hβfrac : β * (δ / (e2 / 2)) ≤ g / 2 := by
      rw [show β * (δ / (e2 / 2)) = 2 * β * δ / e2 by field_simp, div_le_iff₀ he2p]
      have := mul_le_mul_of_nonneg_left hδ2 (by positivity : (0 : ℝ) ≤ 2 * β)
      have e : 2 * β * (g * e2 / (4 * β)) = g / 2 * e2 := by field_simp; ring
      linarith
    unfold exRepayObjective at hR hM hg
    have h1 := mul_le_mul_of_nonneg_left (hlog.trans hfrac) hβ.le
    nlinarith
  obtain ⟨p1, p2⟩ := hCpos Is hIsC
  have hIs0 : 0 < Is := by
    rcases hIsC.1.1.lt_or_eq with h | h
    · exact h
    · exfalso
      have h2 : Ds + e2 / 2 ≤ Is ^ α := hIsC.2
      rw [← h, Real.zero_rpow hα.ne'] at h2
      linarith
  have hrep : ExRepayPreferred Y₁ α β η Ds :=
    ⟨Is, hIs0, by linarith, by linarith, hVle⟩
  have hrec : exReceipts Y₁ α β η Ds = Ds := by simp only [exReceipts, hrep, ↓reduceIte]
  exact ⟨hrep, hrec, fun D => by rw [hrec]; exact hle D⟩

/-! ## An explicit downward-sloping Laffer curve (p. 395, Figure 6.7)

`A` uniform on `[0, 2]` (density `1/2`, `E A = 1`), `η = 1/2`, `F(K) = 2√K`, investment
`K ≥ 0`. Then `V = F/2` when `F ≤ D` (certain default) and `V = D − D²/(2F)` when `F ≥ D`. At
`D = 7/8` the unique optimal investment is `K = 49/64` and `V = 21/32`; at `D = 2` it is
`K = 1/4` and `V = 1/2`. So the Laffer curve falls from `21/32` to `1/2`. -/

/-- The uniform density `1/2` (on `[0, 2]`). (O&R §6.2.3–6.2.4, pp. 393–395.) -/
noncomputable def uniformDensity (_ : ℝ) : ℝ := 1 / 2

/-- The example technology `F(K) = 2√K`. (O&R §6.2.3–6.2.4, pp. 393–395.) -/
noncomputable def sqrtTech (K : ℝ) : ℝ := 2 * Real.sqrt K

/-- The example's market value in closed form, certain-default case: if `F(K) ≤ D` then
`V(D, K) = F(K)/2` (every productivity level defaults and creditors get `E[ηAF] = F/2`).
(O&R §6.2.3–6.2.4, pp. 393–395.) -/
theorem example_value_default {D K : ℝ} (hF : sqrtTech K ≤ D) :
    marketValue uniformDensity 0 2 (1 / 2) sqrtTech D K = sqrtTech K / 2 := by
  unfold marketValue
  have hF0 : 0 ≤ sqrtTech K := by unfold sqrtTech; positivity
  rw [integral_congr (g := fun A => sqrtTech K / 4 * A)]
  · rw [integral_const_mul, integral_id]; ring
  · intro A hA
    rw [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 2)] at hA
    have : 1 / 2 * A * sqrtTech K ≤ D := by nlinarith [hA.1, hA.2]
    simp only [uniformDensity]
    rw [min_eq_left this]
    ring

/-- The example's market value in closed form, interior case: if `0 < D ≤ F(K)` then
`V(D, K) = D − D²/(2F(K))` (default iff `A < 2D/F(K)`). (O&R §6.2.3–6.2.4, pp. 393–395.) -/
theorem example_value_interior {D K : ℝ} (hD : 0 < D) (hF : D ≤ sqrtTech K) :
    marketValue uniformDensity 0 2 (1 / 2) sqrtTech D K = D - D ^ 2 / (2 * sqrtTech K) := by
  set f := sqrtTech K with hf
  have hfpos : 0 < f := lt_of_lt_of_le hD hF
  set a := 2 * D / f with ha
  have ha0 : 0 ≤ a := by positivity
  have ha2 : a ≤ 2 := by rw [ha, div_le_iff₀ hfpos]; linarith
  have hint : ∀ x y, IntervalIntegrable (fun A => min (1 / 2 * A * f) D * uniformDensity A)
      MeasureTheory.volume x y := fun x y =>
    (by unfold uniformDensity; fun_prop :
      Continuous fun A => min (1 / 2 * A * f) D * uniformDensity A).intervalIntegrable _ _
  have hfa : f * a = 2 * D := by rw [ha]; field_simp
  unfold marketValue
  rw [← integral_add_adjacent_intervals (hint 0 a) (hint a 2)]
  rw [integral_congr (g := fun A => f / 4 * A) (a := 0) (b := a),
    integral_congr (g := fun _ => D / 2) (a := a) (b := 2)]
  · rw [integral_const_mul, integral_id, integral_const, smul_eq_mul]
    rw [ha]
    field_simp
    ring
  · intro A hA
    rw [uIcc_of_le ha2] at hA
    have : D ≤ 1 / 2 * A * f := by nlinarith [hA.1]
    simp only [uniformDensity]
    rw [min_eq_right this]
    ring
  · intro A hA
    rw [uIcc_of_le ha0] at hA
    have : 1 / 2 * A * f ≤ D := by nlinarith [hA.2]
    simp only [uniformDensity]
    rw [min_eq_left this]
    ring

/-- The example's debtor utility at `D = 7/8`: for every `K ≥ 0`,
`U(7/8, K) ≤ Y₁ + 21/64`, with equality only at `K = 49/64`. (O&R §6.2.3–6.2.4, pp. 393–395.) -/
theorem example_optimum_seven_eighths (Y₁ : ℝ) {K : ℝ} (hK : 0 ≤ K) :
    debtorUtility uniformDensity 0 2 (1 / 2) Y₁ sqrtTech (7 / 8) K ≤ Y₁ + 21 / 64 ∧
      (debtorUtility uniformDensity 0 2 (1 / 2) Y₁ sqrtTech (7 / 8) K = Y₁ + 21 / 64 →
        K = 49 / 64) := by
  set x := Real.sqrt K with hx
  have hx0 : 0 ≤ x := Real.sqrt_nonneg K
  have hKx : K = x ^ 2 := by rw [hx, Real.sq_sqrt hK]
  have hF : sqrtTech K = 2 * x := rfl
  unfold debtorUtility
  rcases le_or_gt (sqrtTech K) (7 / 8) with h | h
  · rw [example_value_default h, hF, hKx]
    have hx' : x ≤ 7 / 16 := by rw [hF] at h; linarith
    refine ⟨by nlinarith [sq_nonneg (x - 1 / 2)], fun he => ?_⟩
    nlinarith [sq_nonneg (x - 1 / 2)]
  · rw [example_value_interior (by norm_num) h.le, hF, hKx]
    have hxpos : 7 / 16 < x := by rw [hF] at h; linarith
    have hxp : 0 < x := by linarith
    have key : Y₁ - x ^ 2 + 2 * x - (7 / 8 - (7 / 8) ^ 2 / (2 * (2 * x))) - (Y₁ + 21 / 64) =
        -((x - 7 / 8) ^ 2 * (x - 1 / 4)) / x := by
      field_simp
      ring
    have hnn : 0 ≤ (x - 7 / 8) ^ 2 * (x - 1 / 4) :=
      mul_nonneg (sq_nonneg _) (by linarith)
    refine ⟨?_, fun he => ?_⟩
    · have : -((x - 7 / 8) ^ 2 * (x - 1 / 4)) / x ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (by linarith) hxp.le
      linarith
    · have h0 : -((x - 7 / 8) ^ 2 * (x - 1 / 4)) / x = 0 := by linarith
      rw [div_eq_zero_iff] at h0
      rcases h0 with h0 | h0
      · have : (x - 7 / 8) ^ 2 = 0 := by
          rcases mul_eq_zero.mp (neg_eq_zero.mp h0) with h1 | h1
          · exact h1
          · linarith
        have : x = 7 / 8 := by nlinarith [sq_nonneg (x - 7 / 8)]
        rw [this]; norm_num
      · linarith

/-- At `D = 7/8` the investment `K = 49/64` gives `U = Y₁ + 21/64` and `V = 21/32`.
(O&R §6.2.3–6.2.4, pp. 393–395.) -/
theorem example_values_seven_eighths (Y₁ : ℝ) :
    debtorUtility uniformDensity 0 2 (1 / 2) Y₁ sqrtTech (7 / 8) (49 / 64) = Y₁ + 21 / 64 ∧
      marketValue uniformDensity 0 2 (1 / 2) sqrtTech (7 / 8) (49 / 64) = 21 / 32 := by
  have hs : Real.sqrt (49 / 64) = 7 / 8 := by
    rw [Real.sqrt_eq_iff_mul_self_eq_of_pos (by norm_num)]; norm_num
  have hF : sqrtTech (49 / 64) = 7 / 4 := by unfold sqrtTech; rw [hs]; norm_num
  have hV := example_value_interior (K := 49 / 64) (D := 7 / 8) (by norm_num) (by rw [hF]; norm_num)
  rw [hF] at hV
  norm_num at hV
  refine ⟨?_, by rw [hV]⟩
  unfold debtorUtility
  rw [hV, hF]
  ring

/-- The example's debtor utility at `D = 2`: for every `K ≥ 0`, `U(2, K) ≤ Y₁ + 1/4`, with
equality only at `K = 1/4`, where `V = 1/2` (certain default). (O&R §6.2.3–6.2.4, pp. 393–395.) -/
theorem example_optimum_two (Y₁ : ℝ) {K : ℝ} (hK : 0 ≤ K) :
    debtorUtility uniformDensity 0 2 (1 / 2) Y₁ sqrtTech 2 K ≤ Y₁ + 1 / 4 ∧
      (debtorUtility uniformDensity 0 2 (1 / 2) Y₁ sqrtTech 2 K = Y₁ + 1 / 4 → K = 1 / 4) := by
  set x := Real.sqrt K with hx
  have hx0 : 0 ≤ x := Real.sqrt_nonneg K
  have hKx : K = x ^ 2 := by rw [hx, Real.sq_sqrt hK]
  have hF : sqrtTech K = 2 * x := rfl
  unfold debtorUtility
  rcases le_or_gt (sqrtTech K) 2 with h | h
  · rw [example_value_default h, hF, hKx]
    refine ⟨by nlinarith [sq_nonneg (x - 1 / 2)], fun he => ?_⟩
    have : x = 1 / 2 := by nlinarith [sq_nonneg (x - 1 / 2)]
    rw [this]; norm_num
  · rw [example_value_interior (by norm_num) h.le, hF, hKx]
    have hx1 : 1 < x := by rw [hF] at h; linarith
    have hxp : 0 < x := by linarith
    have e : (2 : ℝ) ^ 2 / (2 * (2 * x)) = 1 / x := by field_simp
    have h1x : 1 / x < 1 := by rw [div_lt_one hxp]; exact hx1
    rw [e]
    constructor
    · nlinarith [sq_nonneg (x - 1)]
    · intro he; nlinarith [sq_nonneg (x - 1)]

/-- At `D = 2` the investment `K = 1/4` gives `U = Y₁ + 1/4` and `V = 1/2`.
(O&R §6.2.3–6.2.4, pp. 393–395.) -/
theorem example_values_two (Y₁ : ℝ) :
    debtorUtility uniformDensity 0 2 (1 / 2) Y₁ sqrtTech 2 (1 / 4) = Y₁ + 1 / 4 ∧
      marketValue uniformDensity 0 2 (1 / 2) sqrtTech 2 (1 / 4) = 1 / 2 := by
  have hs : Real.sqrt (1 / 4) = 1 / 2 := by
    rw [Real.sqrt_eq_iff_mul_self_eq_of_pos (by norm_num)]; norm_num
  have hF : sqrtTech (1 / 4) = 1 := by unfold sqrtTech; rw [hs]; norm_num
  have hV := example_value_default (K := 1 / 4) (D := 2) (by rw [hF]; norm_num)
  rw [hF] at hV
  refine ⟨?_, hV⟩
  unfold debtorUtility
  rw [hV, hF]
  ring

/-- The example admits optimal investment at every `D ≥ 0`: `U(D, ·)` attains its maximum on
`K ≥ 0` (compactness of `[0, 4]`, continuity of `V` in `K`, and `U(D, K) ≤ U(D, 0)` for
`K ≥ 4`). (O&R §6.2.3–6.2.4, pp. 393–395.) -/
theorem example_optimum_exists (Y₁ : ℝ) {D : ℝ} (hD : 0 ≤ D) :
    ∃ K ∈ Ici (0 : ℝ), ∀ K' ∈ Ici (0 : ℝ),
      debtorUtility uniformDensity 0 2 (1 / 2) Y₁ sqrtTech D K' ≤
        debtorUtility uniformDensity 0 2 (1 / 2) Y₁ sqrtTech D K := by
  have hcont : Continuous fun K => debtorUtility uniformDensity 0 2 (1 / 2) Y₁ sqrtTech D K := by
    unfold debtorUtility marketValue sqrtTech uniformDensity
    have : Continuous fun K => ∫ A in (0 : ℝ)..2, min (1 / 2 * A * (2 * Real.sqrt K)) D * (1 / 2) :=
      intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
        (by fun_prop) 0 2
    fun_prop
  obtain ⟨K, hK, hmax⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 4)).exists_isMaxOn
    (nonempty_Icc.mpr (by norm_num)) hcont.continuousOn
  have hU0 : debtorUtility uniformDensity 0 2 (1 / 2) Y₁ sqrtTech D 0 = Y₁ := by
    have := example_value_default (D := D) (K := 0) (by unfold sqrtTech; simpa using hD)
    unfold debtorUtility
    rw [this]
    unfold sqrtTech
    simp
  refine ⟨K, hK.1, fun K' hK' => ?_⟩
  rw [mem_Ici] at hK'
  rcases le_or_gt K' 4 with h | h
  · exact isMaxOn_iff.mp hmax K' ⟨hK', h⟩
  · have hV := marketValue_nonneg (π := uniformDensity) (Al := 0) (Ah := 2) (η := 1 / 2)
      (F := sqrtTech) (D := D) (K := K') (by norm_num) le_rfl (by norm_num)
      (fun _ _ => by unfold uniformDensity; norm_num) hD (by unfold sqrtTech; positivity)
    have hs : Real.sqrt K' ≤ K' / 2 := by
      have h2 : (2 : ℝ) ≤ Real.sqrt K' := by
        rw [show (2 : ℝ) = Real.sqrt 4 by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
        exact Real.sqrt_le_sqrt h.le
      have := Real.sq_sqrt hK'
      nlinarith
    have h0 := isMaxOn_iff.mp hmax 0 ⟨le_rfl, by norm_num⟩
    rw [hU0] at h0
    have hF' : sqrtTech K' = 2 * Real.sqrt K' := rfl
    unfold debtorUtility
    unfold debtorUtility at h0
    rw [hF']
    linarith

/-- THE DEBT LAFFER CURVE CAN SLOPE DOWN, O&R p. 395 and Figure 6.7 ("`V` may be declining
with `D` for large `D`"), and so is not concave: in the example, for ANY selection `K(D)` of
optimal investments (`K(D) ≥ 0` maximising `U(D, ·)` over `K ≥ 0` for every `D ≥ 0`, which
exists by `example_optimum_exists`), the Laffer curve `W(D) = V[D, K(D)]` has
`W(7/8) = 21/32 > 1/2 = W(2)` and is not concave on `[0, ∞)`. -/
theorem example_laffer_declines (Y₁ : ℝ) {Kf : ℝ → ℝ} (hK0 : ∀ D, 0 ≤ D → 0 ≤ Kf D)
    (hopt : ∀ D, 0 ≤ D → ∀ K, 0 ≤ K →
      debtorUtility uniformDensity 0 2 (1 / 2) Y₁ sqrtTech D K ≤
        debtorUtility uniformDensity 0 2 (1 / 2) Y₁ sqrtTech D (Kf D)) :
    marketValue uniformDensity 0 2 (1 / 2) sqrtTech (7 / 8) (Kf (7 / 8)) = 21 / 32 ∧
      marketValue uniformDensity 0 2 (1 / 2) sqrtTech 2 (Kf 2) = 1 / 2 ∧
      ¬ ConcaveOn ℝ (Ici 0) fun D => marketValue uniformDensity 0 2 (1 / 2) sqrtTech D (Kf D) := by
  have h78 : Kf (7 / 8) = 49 / 64 := by
    obtain ⟨hle, heq⟩ := example_optimum_seven_eighths Y₁ (hK0 (7 / 8) (by norm_num))
    apply heq
    apply le_antisymm hle
    have := hopt (7 / 8) (by norm_num) (49 / 64) (by norm_num)
    rw [(example_values_seven_eighths Y₁).1] at this
    exact this
  have h2 : Kf 2 = 1 / 4 := by
    obtain ⟨hle, heq⟩ := example_optimum_two Y₁ (hK0 2 (by norm_num))
    apply heq
    apply le_antisymm hle
    have := hopt 2 (by norm_num) (1 / 4) (by norm_num)
    rw [(example_values_two Y₁).1] at this
    exact this
  have hW78 : marketValue uniformDensity 0 2 (1 / 2) sqrtTech (7 / 8) (Kf (7 / 8)) = 21 / 32 := by
    rw [h78]; exact (example_values_seven_eighths Y₁).2
  have hW2 : marketValue uniformDensity 0 2 (1 / 2) sqrtTech 2 (Kf 2) = 1 / 2 := by
    rw [h2]; exact (example_values_two Y₁).2
  refine ⟨hW78, hW2, laffer_not_concave_of_decreasing (D₁ := 7 / 8) (D₂ := 2) ?_ (by norm_num)
    (by norm_num) (by rw [hW78, hW2]; norm_num)⟩
  intro D hD
  rw [mem_Ici] at hD
  exact marketValue_nonneg (by norm_num) le_rfl (by norm_num)
    (fun _ _ => by unfold uniformDensity; norm_num) hD (by unfold sqrtTech; positivity)

end ObstfeldRogoff.CapitalMarketImperfections.DebtOverhangLaffer
