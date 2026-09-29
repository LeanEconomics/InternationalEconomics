/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import CapitalMarketImperfections.SovereignRiskPrimitives
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Sovereign default and direct creditor sanctions: pure insurance

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §6.1.1
(pp. 351–362), eqs. (1)–(10), footnotes 6–11, Figures 6.1–6.2.

A small country with no date-1 consumption contracts with competitive risk-neutral insurers
for payments `P(ε)` out of date-2 output `Y₂ = Ȳ + ε` (finitely many states, all of positive
probability). Insurers break even, (1) `E P = 0`; consumption is (3) `C₂ = Ȳ + ε − P`.

* **Full insurance (§6.1.1.2, fn 7).** Without default risk `P = ε` is the unique optimum
  (strict Jensen), giving `C₂ = Ȳ` in every state; forward sale of output at the
  risk-neutral price `Ȳ` (p. 355). Footnote 8: the country defaults on full insurance
  exactly when `ε > ηȲ/(1 − η)`; footnote 9: the shortfall `ε − η(Ȳ + ε)` rises in `ε`.
* **Optimal incentive-compatible contract (§6.1.1.3, (2)–(9)).** With creditor sanctions
  costing a fraction `η ∈ (0,1)` of output, (2) `P(ε) ≤ η(Ȳ + ε)`. The optimal contract has
  `C₂(ε) = max(c̄, (1 − η)(Ȳ + ε))` where `c̄ = Ȳ − P₀` is the *unique* solution of
  `E max(c̄, (1 − η)Y₂) = Ȳ`; it is optimal for *every* strictly concave utility and is
  the unique optimum. Kuhn–Tucker multipliers satisfying (4)–(6) exist at the optimum, and
  (4)–(5) are sufficient for optimality. The schedule is (9) with threshold `e` defined by
  (7)–(8).
* **Corollaries (pp. 359–360, fn 10–11).** Full insurance is optimal iff
  `(1 − η)(Ȳ + ε_N) ≤ Ȳ`; otherwise `P₀ > 0`, so the country pays insurers in some
  states with `ε < 0`; the put-option form of fn 11; `0 ≤ ΔP ≤ Δε`; the country's
  welfare rises weakly with `η` (strictly when (2) binds); expected consumption is `Ȳ`;
  with `η = 0` only the null contract is feasible.
* **The uniform example (§6.1.1.4, (10)).** For `ε ~ U[−ε̄, ε̄]` the zero-profit
  integral of schedule (9) is computed exactly; it vanishes iff
  `(e + ε̄)² = 4ηε̄Ȳ/(1 − η)`, i.e. iff `e` is the root (10); `e < ε̄` iff
  `ε̄ > η(Ȳ + ε̄)`; `e > −ε̄` iff `η > 0`; `e` rises strictly with `η` and tends to `−ε̄`
  as `η → 0`; `e < 0` iff `η < ε̄/(4Ȳ + ε̄)`.
-/

namespace ObstfeldRogoff.CapitalMarketImperfections.DirectSanctionsInsurance

open Finset Set Filter Topology
open SovereignRiskPrimitives SovereignRiskPrimitives.StateSpaceFacts

variable {S : Type} [Fintype S] (E : Endowment S)

/-- Date-2 consumption under the payment schedule `P`, O&R (3), p. 356:
`C₂(ε) = Ȳ + ε − P(ε)`. -/
def consumption (P : S → ℝ) (s : S) : ℝ := E.Y s - P s

/-- The insurers' zero-profit condition, O&R (1), p. 354: `Σ π(ε_i) P(ε_i) = 0`. -/
def ZeroProfit (P : S → ℝ) : Prop := E.Ω.expect P = 0

/-- The incentive-compatibility constraint with sanctions `ηY₂`, O&R (2), p. 356. -/
def SanctionIC (η : ℝ) (P : S → ℝ) : Prop := ∀ s, P s ≤ η * E.Y s

/-- Expected utility of date-2 consumption, O&R p. 354: `U₁ = E u(C₂)`. -/
def expectedUtility (U : Utility) (P : S → ℝ) : ℝ :=
  E.Ω.expect (fun s => U.u (consumption E P s))

/-- The consumption floor imposed by the sanction constraint, `(1 − η)(Ȳ + ε)`
(O&R Figure 6.2, p. 360). -/
def floorCons (η : ℝ) (s : S) : ℝ := (1 - η) * E.Y s

/-- The candidate optimal schedule, `P(ε) = Ȳ + ε − max(c̄, (1 − η)(Ȳ + ε))`
(O&R (9), p. 358). -/
def optPayment (η cbar : ℝ) (s : S) : ℝ := E.Y s - max cbar (floorCons E η s)

/-- The mean-consumption equation that pins down `c̄ = Ȳ − P₀`, O&R (1) with (9):
`E max(c̄, (1 − η)(Ȳ + ε)) = Ȳ`. -/
def CbarEq (η cbar : ℝ) : Prop :=
  E.Ω.expect (fun s => max cbar (floorCons E η s)) = E.Ybar

/-! ## Full insurance -/

/-- Footnote 7, O&R p. 355: full insurance `P = ε` gives constant consumption `Ȳ`. -/
theorem full_insurance_consumption (s : S) : consumption E E.ε s = E.Ybar := by
  simp [consumption, Endowment.Y]

/-- Full insurance satisfies the zero-profit condition (1) because `E ε = 0` (O&R p. 355). -/
theorem full_insurance_zero_profit : ZeroProfit E E.ε := E.mean_zero

/-- The forward sale of output at the risk-neutral price, O&R p. 355: `Σ π Y₂ = Ȳ`. -/
theorem forward_price : E.Ω.expect E.Y = E.Ybar := E.expect_Y

/-- Full insurance is optimal without default risk, O&R §6.1.1.2 and footnote 7, p. 355:
every zero-profit schedule with positive consumption gives `E u(C₂) ≤ u(Ȳ)`, the value
of full insurance. -/
theorem full_insurance_optimal (U : Utility) {P : S → ℝ} (hP : ZeroProfit E P)
    (hC : ∀ s, 0 < consumption E P s) :
    expectedUtility E U P ≤ expectedUtility E U E.ε := by
  have hm : E.Ω.expect (consumption E P) = E.Ybar := by
    unfold consumption; rw [expect_sub, E.expect_Y, hP, sub_zero]
  have h := jensen E.Ω U hC
  rw [hm] at h
  have e2 : expectedUtility E U E.ε = U.u E.Ybar := by
    unfold expectedUtility
    simp only [full_insurance_consumption]
    exact E.Ω.expect_const _
  rw [e2]; exact h

/-- Full insurance is the unique optimum without default risk (O&R footnote 7, p. 355;
strict concavity): a zero-profit schedule attaining `u(Ȳ)` is `P = ε`. -/
theorem full_insurance_unique (U : Utility) {P : S → ℝ} (hP : ZeroProfit E P)
    (hC : ∀ s, 0 < consumption E P s)
    (heq : expectedUtility E U P = expectedUtility E U E.ε) : P = E.ε := by
  have hm : E.Ω.expect (consumption E P) = E.Ybar := by
    unfold consumption; rw [expect_sub, E.expect_Y, hP, sub_zero]
  have e2 : expectedUtility E U E.ε = U.u E.Ybar := by
    unfold expectedUtility
    simp only [full_insurance_consumption]
    exact E.Ω.expect_const _
  funext s
  by_contra hne
  have hcs : consumption E P s ≠ E.Ω.expect (consumption E P) := by
    rw [hm]; unfold consumption Endowment.Y; intro h; apply hne; linarith
  have := jensen_strict E.Ω U hC (E.prob_pos s) hcs
  rw [hm] at this
  unfold expectedUtility at heq e2
  rw [heq, e2] at this
  exact lt_irrefl _ this

/-- Footnote 8, O&R p. 355: with repayment under indifference, the country defaults on the
full-insurance payment `ε` exactly when `ηY₂ < ε`, i.e. when `ε > ηȲ/(1 − η)`. -/
theorem default_on_full_insurance_iff {η : ℝ} (hη1 : η < 1) (s : S) :
    η * E.Y s < E.ε s ↔ η * E.Ybar / (1 - η) < E.ε s := by
  unfold Endowment.Y
  rw [div_lt_iff₀ (by linarith)]
  constructor <;> intro h <;> nlinarith

/-- Full insurance is incentive compatible iff `ε ≤ ηȲ/(1 − η)` in every state
(O&R footnote 8, p. 355, and p. 359). -/
theorem full_insurance_ic_iff {η : ℝ} (hη1 : η < 1) :
    SanctionIC E η E.ε ↔ ∀ s, E.ε s ≤ η * E.Ybar / (1 - η) := by
  unfold SanctionIC
  refine forall_congr' fun s => ?_
  have := default_on_full_insurance_iff E hη1 s
  constructor
  · intro h; by_contra h'; push Not at h'; exact absurd (this.mpr h') (not_lt.mpr h)
  · intro h; by_contra h'; push Not at h'; exact absurd (this.mp h') (not_lt.mpr h)

/-- Footnote 9, O&R p. 357: the difference between the full-insurance payment and the cost
of default, `ε − η(Ȳ + ε) = (1 − η)ε − ηȲ`, is increasing in `ε`. -/
theorem shortfall_increasing {η x y : ℝ} (hη1 : η < 1) (Ybar : ℝ) (hxy : x < y) :
    x - η * (Ybar + x) < y - η * (Ybar + y) := by nlinarith

/-! ## The optimal incentive-compatible contract -/

/-- The sanction constraint (2) keeps consumption above the floor `(1 − η)(Ȳ + ε)`
(O&R p. 357). -/
theorem floor_le_consumption {η : ℝ} {P : S → ℝ} (hIC : SanctionIC E η P) (s : S) :
    floorCons E η s ≤ consumption E P s := by
  have := hIC s
  unfold floorCons consumption
  linarith

/-- The consumption floor is positive for `η < 1` (O&R p. 360). -/
theorem floorCons_pos {η : ℝ} (hη1 : η < 1) (s : S) : 0 < floorCons E η s :=
  mul_pos (by linarith) (E.Y_pos s)

/-- Expected floor consumption is `(1 − η)Ȳ` (O&R p. 359). -/
theorem expect_floorCons (η : ℝ) : E.Ω.expect (floorCons E η) = (1 - η) * E.Ybar := by
  unfold floorCons; rw [expect_const_mul, E.expect_Y]

/-- Any solution `c̄` of the mean-consumption equation is positive and at most `Ȳ`
(O&R p. 359: `Ȳ − P₀ ≤ Ȳ`). -/
theorem cbar_bounds {η cbar : ℝ} (hη0 : 0 < η) (hη1 : η < 1) (hc : CbarEq E η cbar) :
    0 < cbar ∧ cbar ≤ E.Ybar := by
  have hY := E.Ybar_pos
  constructor
  · by_contra h; push Not at h
    have e : (fun s => max cbar (floorCons E η s)) = floorCons E η := by
      funext s; exact max_eq_right (le_trans h (floorCons_pos E hη1 s).le)
    unfold CbarEq at hc
    rw [e, expect_floorCons] at hc
    nlinarith
  · by_contra h; push Not at h
    have := expect_mono E.Ω (X := fun _ => cbar) (Y := fun s => max cbar (floorCons E η s))
      fun s => le_max_left _ _
    rw [E.Ω.expect_const] at this
    unfold CbarEq at hc
    linarith

/-- Existence of the constant consumption level `c̄ = Ȳ − P₀` of the unconstrained states,
O&R (7), p. 357 (intermediate value theorem). -/
theorem cbar_exists {η : ℝ} (hη0 : 0 < η) (hη1 : η < 1) : ∃ cbar, CbarEq E η cbar := by
  have hY := E.Ybar_pos
  obtain ⟨c, _, hc⟩ := exists_eq_of_continuous (continuous_expect_max E.Ω (floorCons E η))
    hY.le (a := 0) (T := E.Ybar) (by
      have e : (fun s => max 0 (floorCons E η s)) = floorCons E η := by
        funext s; exact max_eq_right (floorCons_pos E hη1 s).le
      rw [e, expect_floorCons]; nlinarith) (by
      have := expect_mono E.Ω (X := fun _ => E.Ybar)
        (Y := fun s => max E.Ybar (floorCons E η s)) fun s => le_max_left _ _
      rw [E.Ω.expect_const] at this; exact this)
  exact ⟨c, hc⟩

/-- Uniqueness of `c̄`, O&R (7), p. 357: the mean-consumption equation has one solution. -/
theorem cbar_unique {η c₁ c₂ : ℝ} (hη0 : 0 < η) (h₁ : CbarEq E η c₁)
    (h₂ : CbarEq E η c₂) : c₁ = c₂ := by
  have key : ∀ a b, CbarEq E η a → CbarEq E η b → a < b → False := by
    intro a b ha hb hab
    -- some state has floor below `b`
    obtain ⟨s, hs⟩ : ∃ s, floorCons E η s < b := by
      by_contra hn; push Not at hn
      have e : (fun s => max b (floorCons E η s)) = floorCons E η := by
        funext s; exact max_eq_right (hn s)
      unfold CbarEq at hb; rw [e, expect_floorCons] at hb
      have := E.Ybar_pos; nlinarith
    have hlt := expect_strictMono E.Ω (X := fun s => max a (floorCons E η s))
      (Y := fun s => max b (floorCons E η s)) (fun s => max_le_max hab.le le_rfl)
      (E.prob_pos s) (max_lt (lt_of_lt_of_le hab (le_max_left _ _))
        (lt_of_lt_of_le hs (le_max_left _ _)))
    unfold CbarEq at ha hb; linarith
  rcases lt_trichotomy c₁ c₂ with h | h | h
  · exact (key _ _ h₁ h₂ h).elim
  · exact h
  · exact (key _ _ h₂ h₁ h).elim

/-- The candidate schedule gives consumption `max(c̄, (1 − η)(Ȳ + ε))` (O&R Figure 6.2). -/
theorem consumption_optPayment (η cbar : ℝ) (s : S) :
    consumption E (optPayment E η cbar) s = max cbar (floorCons E η s) := by
  simp [consumption, optPayment]

/-- The candidate schedule satisfies the zero-profit condition (1) (O&R p. 358). -/
theorem optPayment_zero_profit {η cbar : ℝ} (hc : CbarEq E η cbar) :
    ZeroProfit E (optPayment E η cbar) := by
  unfold ZeroProfit optPayment
  rw [expect_sub, E.expect_Y]
  unfold CbarEq at hc; rw [hc, sub_self]

/-- The candidate schedule satisfies the sanction constraint (2) (O&R p. 358). -/
theorem optPayment_ic (η cbar : ℝ) : SanctionIC E η (optPayment E η cbar) := by
  intro s
  have := le_max_right cbar (floorCons E η s)
  unfold optPayment floorCons at *
  linarith

/-- **The optimal incentive-compatible contract**, O&R §6.1.1.3, eqs. (1)–(9),
pp. 356–358. Let `c̄` solve `E max(c̄, (1 − η)(Ȳ + ε)) = Ȳ`. The schedule
`P(ε) = Ȳ + ε − max(c̄, (1 − η)(Ȳ + ε))` satisfies (1) and (2), and for every strictly
concave utility every schedule satisfying (1) and (2) gives no higher expected utility,
with equality only for this schedule. In particular the optimal contract does not depend
on `u`. -/
theorem optimal_ic_contract (U : Utility) {η cbar : ℝ} (hη0 : 0 < η) (hη1 : η < 1)
    (hc : CbarEq E η cbar) :
    ZeroProfit E (optPayment E η cbar) ∧ SanctionIC E η (optPayment E η cbar) ∧
      ∀ P, ZeroProfit E P → SanctionIC E η P →
        expectedUtility E U P ≤ expectedUtility E U (optPayment E η cbar) ∧
        (expectedUtility E U P = expectedUtility E U (optPayment E η cbar) →
          P = optPayment E η cbar) := by
  refine ⟨optPayment_zero_profit E hc, optPayment_ic E η cbar, fun P hP hIC => ?_⟩
  have hcpos := (cbar_bounds E hη0 hη1 hc).1
  set hi : S → ℝ := fun s => max (consumption E P s) (max cbar (floorCons E η s))
  have hmin : ∀ s, min (hi s) (max cbar (floorCons E η s)) = max cbar (floorCons E η s) :=
    fun s => min_eq_right (le_max_right _ _)
  have hfun : (fun s => min (hi s) (max cbar (floorCons E η s))) =
      fun s => max cbar (floorCons E η s) := funext hmin
  have hfun' : (fun s => U.u (min (hi s) (max cbar (floorCons E η s)))) =
      fun s => U.u (max cbar (floorCons E η s)) := funext fun s => by rw [hmin]
  have hmean : E.Ω.expect (consumption E P) ≤
      E.Ω.expect (fun s => min (hi s) (max cbar (floorCons E η s))) := by
    rw [hfun]
    unfold consumption; rw [expect_sub, E.expect_Y, hP]
    unfold CbarEq at hc; rw [hc]; simp
  obtain ⟨h1, h2⟩ := clamp_optimal E.Ω U hcpos (floorCons_pos E hη1)
    (fun s => le_trans (le_max_right cbar _) (le_max_right _ _))
    (floor_le_consumption E hIC) (fun s => le_max_left _ _) hmean
  rw [hfun'] at h1 h2
  have e : expectedUtility E U (optPayment E η cbar) =
      E.Ω.expect (fun s => U.u (max cbar (floorCons E η s))) := by
    unfold expectedUtility; simp only [consumption_optPayment]
  refine ⟨by rw [e]; exact h1, fun heq => ?_⟩
  rw [e] at heq
  funext s
  have := h2 heq s (E.prob_pos s)
  rw [hmin, ← consumption_optPayment E η cbar s] at this
  unfold consumption at this
  linarith

/-- **Kuhn–Tucker conditions at the optimum**, O&R (4)–(6), pp. 356–357 (necessity): with
`μ = u'(Ȳ − P₀)` and `λ(ε) = π(ε)[u'(Ȳ − P₀) − u'(C₂(ε))]`, the multipliers are
nonnegative, (4) `π u'(C₂) + λ = μπ` holds and complementary slackness (5) holds. -/
theorem kuhn_tucker_at_optimum (U : Utility) {η cbar : ℝ} (hη0 : 0 < η) (hη1 : η < 1)
    (hc : CbarEq E η cbar) :
    let C := consumption E (optPayment E η cbar)
    let μ := U.du cbar
    let lam : S → ℝ := fun s => E.Ω.prob s * (U.du cbar - U.du (C s))
    (∀ s, 0 ≤ lam s) ∧ (∀ s, E.Ω.prob s * U.du (C s) + lam s = μ * E.Ω.prob s) ∧
      (∀ s, lam s * (η * E.Y s - optPayment E η cbar s) = 0) := by
  intro C μ lam
  have hcpos := (cbar_bounds E hη0 hη1 hc).1
  refine ⟨fun s => ?_, fun s => by simp only [lam, μ]; ring, fun s => ?_⟩
  · simp only [lam, C, consumption_optPayment]
    exact mul_nonneg (E.Ω.prob_nonneg s) (by
      linarith [U.du_anti hcpos (le_max_left cbar (floorCons E η s))])
  · simp only [lam, C, consumption_optPayment]
    rcases le_total (floorCons E η s) cbar with h | h
    · rw [max_eq_left h]; ring
    · have : η * E.Y s - optPayment E η cbar s = 0 := by
        unfold optPayment; rw [max_eq_right h]; unfold floorCons; ring
      rw [this, mul_zero]

/-- **Kuhn–Tucker sufficiency**, O&R (4)–(5), p. 356: a schedule satisfying (1), (2) and
the conditions (4)–(5) for some `μ` and multipliers `λ ≥ 0` is optimal. -/
theorem kuhn_tucker_sufficient (U : Utility) {η : ℝ} (hη1 : η < 1) {P : S → ℝ}
    (hP : ZeroProfit E P) (hIC : SanctionIC E η P) (μ : ℝ) (lam : S → ℝ)
    (hlam : ∀ s, 0 ≤ lam s)
    (h4 : ∀ s, E.Ω.prob s * U.du (consumption E P s) + lam s = μ * E.Ω.prob s)
    (h5 : ∀ s, lam s * (η * E.Y s - P s) = 0) :
    ∀ Q, ZeroProfit E Q → SanctionIC E η Q → expectedUtility E U Q ≤ expectedUtility E U P := by
  intro Q hQ hQIC
  have hCP : ∀ s, 0 < consumption E P s := fun s =>
    lt_of_lt_of_le (floorCons_pos E hη1 s) (floor_le_consumption E hIC s)
  have hCQ : ∀ s, 0 < consumption E Q s := fun s =>
    lt_of_lt_of_le (floorCons_pos E hη1 s) (floor_le_consumption E hQIC s)
  have hpt : ∀ s, E.Ω.prob s * U.u (consumption E Q s) ≤
      E.Ω.prob s * U.u (consumption E P s) + (μ * E.Ω.prob s - lam s) * (P s - Q s) := by
    intro s
    have hsl := U.supporting_line (hCQ s) (hCP s)
    have hd : E.Ω.prob s * U.du (consumption E P s) = μ * E.Ω.prob s - lam s := by
      linarith [h4 s]
    have : consumption E Q s - consumption E P s = P s - Q s := by
      unfold consumption; ring
    rw [this] at hsl
    calc E.Ω.prob s * U.u (consumption E Q s)
        ≤ E.Ω.prob s * (U.u (consumption E P s) + U.du (consumption E P s) * (P s - Q s)) :=
          mul_le_mul_of_nonneg_left hsl (E.Ω.prob_nonneg s)
      _ = E.Ω.prob s * U.u (consumption E P s) +
            (E.Ω.prob s * U.du (consumption E P s)) * (P s - Q s) := by ring
      _ = _ := by rw [hd]
  have hsum := Finset.sum_le_sum fun s (_ : s ∈ Finset.univ) => hpt s
  rw [Finset.sum_add_distrib] at hsum
  have hlin : ∑ s, (μ * E.Ω.prob s - lam s) * (P s - Q s) ≤ 0 := by
    have e : ∑ s, (μ * E.Ω.prob s - lam s) * (P s - Q s) =
        μ * (E.Ω.expect P - E.Ω.expect Q) + ∑ s, lam s * (Q s - P s) := by
      unfold StateSpace.expect
      rw [mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
        ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro s _; ring
    have hl : ∑ s, lam s * (Q s - P s) ≤ 0 := by
      apply Finset.sum_nonpos; intro s _
      have h5s := h5 s
      have : lam s * (Q s - P s) = lam s * (Q s - η * E.Y s) := by
        have : lam s * (Q s - P s) = lam s * (Q s - η * E.Y s) + lam s * (η * E.Y s - P s) := by
          ring
        rw [this, h5s, add_zero]
      rw [this]
      exact mul_nonpos_of_nonneg_of_nonpos (hlam s) (by linarith [hQIC s])
    unfold ZeroProfit at hP hQ
    rw [e, hP, hQ]; linarith
  unfold expectedUtility StateSpace.expect
  linarith

/-- The schedule (9), O&R p. 358: `P(ε) = min(P₀ + ε, η(Ȳ + ε))` with `P₀ = Ȳ − c̄`. -/
theorem optPayment_eq_min (η cbar : ℝ) (s : S) :
    optPayment E η cbar s = min (E.Ybar - cbar + E.ε s) (η * E.Y s) := by
  unfold optPayment floorCons Endowment.Y
  rcases le_total cbar ((1 - η) * (E.Ybar + E.ε s)) with h | h
  · rw [max_eq_right h, min_eq_right (by linarith)]; ring
  · rw [max_eq_left h, min_eq_left (by linarith)]; ring

/-- The threshold `e`, O&R (7)–(8), p. 357: defined by `(1 − η)(Ȳ + e) = Ȳ − P₀ = c̄`. -/
noncomputable def threshold (η cbar Ybar : ℝ) : ℝ := cbar / (1 - η) - Ybar

/-- O&R (7) and (8), p. 357: `Ȳ − P₀ = (1 − η)(Ȳ + e)` and `P₀ + e = η(Ȳ + e)`. -/
theorem threshold_eqs {η cbar : ℝ} (hη1 : η < 1) :
    E.Ybar - (E.Ybar - cbar) = (1 - η) * (E.Ybar + threshold η cbar E.Ybar) ∧
      (E.Ybar - cbar) + threshold η cbar E.Ybar =
        η * (E.Ybar + threshold η cbar E.Ybar) := by
  unfold threshold
  have : (1 : ℝ) - η ≠ 0 := by linarith
  constructor <;> field_simp <;> ring

/-- The two-arm schedule (9), O&R p. 358: `P(ε) = ηȲ − (1 − η)e + ε` for `ε < e` and
`P(ε) = η(Ȳ + ε)` for `ε ≥ e`. -/
theorem optPayment_arms {η cbar : ℝ} (hη1 : η < 1) (s : S) :
    (E.ε s < threshold η cbar E.Ybar →
        optPayment E η cbar s = η * E.Ybar - (1 - η) * threshold η cbar E.Ybar + E.ε s) ∧
      (threshold η cbar E.Ybar ≤ E.ε s → optPayment E η cbar s = η * (E.Ybar + E.ε s)) := by
  have h1 : (0 : ℝ) < 1 - η := by linarith
  have hcb : cbar = (1 - η) * (E.Ybar + threshold η cbar E.Ybar) := by
    unfold threshold; field_simp; ring
  generalize threshold η cbar E.Ybar = t at *
  subst hcb
  unfold optPayment floorCons Endowment.Y
  constructor
  · intro h
    rw [max_eq_left (by nlinarith)]
    ring
  · intro h
    rw [max_eq_right (by nlinarith)]; ring

/-! ## Corollaries -/

/-- O&R p. 360: expected consumption under the optimal contract equals `Ȳ`. -/
theorem mean_consumption_opt {η cbar : ℝ} (hc : CbarEq E η cbar) :
    E.Ω.expect (consumption E (optPayment E η cbar)) = E.Ybar := by
  unfold consumption; rw [expect_sub, E.expect_Y, optPayment_zero_profit E hc, sub_zero]

/-- Full insurance is optimal iff `(1 − η)(Ȳ + ε) ≤ Ȳ` in every state, i.e. iff `c̄ = Ȳ`
(O&R footnote 10, p. 357, and p. 359). -/
theorem full_insurance_iff {η cbar : ℝ} (hη0 : 0 < η) (hc : CbarEq E η cbar) :
    cbar = E.Ybar ↔ ∀ s, floorCons E η s ≤ E.Ybar := by
  constructor
  · intro h s
    by_contra hs; push Not at hs
    have hlt := expect_strictMono E.Ω (X := fun _ => E.Ybar)
      (Y := fun s => max cbar (floorCons E η s)) (fun t => by rw [h]; exact le_max_left _ _)
      (E.prob_pos s) (lt_of_lt_of_le hs (le_max_right _ _))
    rw [E.Ω.expect_const] at hlt
    unfold CbarEq at hc; linarith
  · intro h
    have hY : CbarEq E η E.Ybar := by
      unfold CbarEq
      have e : (fun s => max E.Ybar (floorCons E η s)) = fun _ => E.Ybar := by
        funext s; exact max_eq_left (h s)
      rw [e, E.Ω.expect_const]
    exact cbar_unique E hη0 hc hY

/-- When full insurance is optimal the optimal schedule is `P = ε` (O&R p. 359). -/
theorem opt_is_full_insurance {η : ℝ} (h : ∀ s, floorCons E η s ≤ E.Ybar) :
    optPayment E η E.Ybar = E.ε := by
  funext s; unfold optPayment; rw [max_eq_left (h s)]; simp [Endowment.Y]

/-- O&R p. 359: if full insurance is not incentive compatible somewhere then
`(1 − η)(Ȳ + e) < Ȳ`, i.e. `P₀ > 0`. -/
theorem premium_positive {η cbar : ℝ} (hη0 : 0 < η) (hη1 : η < 1) (hc : CbarEq E η cbar)
    (h : ∃ s, E.Ybar < floorCons E η s) : 0 < E.Ybar - cbar := by
  have hb := (cbar_bounds E hη0 hη1 hc).2
  rcases eq_or_lt_of_le hb with he | he
  · exfalso
    obtain ⟨s, hs⟩ := h
    have := (full_insurance_iff E hη0 hc).mp he s
    linarith
  · linarith

/-- O&R p. 359: under the optimal contract the country pays insurers in state `ε` iff
`ε > −P₀`; with `P₀ > 0` it pays even in some states with `ε < 0`. -/
theorem payment_positive_iff {η cbar : ℝ} (hη0 : 0 < η) (s : S) :
    0 < optPayment E η cbar s ↔ -(E.Ybar - cbar) < E.ε s := by
  rw [optPayment_eq_min]
  have hY : 0 < η * E.Y s := mul_pos hη0 (E.Y_pos s)
  constructor
  · intro h; have := min_le_left (E.Ybar - cbar + E.ε s) (η * E.Y s); linarith
  · intro h; exact lt_min (by linarith) hY

/-- Footnote 11, O&R p. 359: the constrained consumption is the payoff of `(1 − η)Y₂` plus a
put option with strike `c̄`, `max(c̄ − (1 − η)Y₂, 0)`. -/
theorem put_option_form (η cbar : ℝ) (s : S) :
    consumption E (optPayment E η cbar) s =
      floorCons E η s + max (cbar - floorCons E η s) 0 := by
  rw [consumption_optPayment]
  rcases le_total cbar (floorCons E η s) with h | h
  · rw [max_eq_right h, max_eq_right (by linarith)]; ring
  · rw [max_eq_left h, max_eq_left (by linarith)]; ring

/-- O&R p. 358 and Figure 6.1: the optimal payment rises with `ε`, never faster than
dollar for dollar: `0 ≤ P(ε') − P(ε) ≤ ε' − ε` for `ε ≤ ε'`. -/
theorem payment_slope {η cbar : ℝ} (hη0 : 0 ≤ η) (hη1 : η ≤ 1) {s t : S}
    (hst : E.ε s ≤ E.ε t) :
    0 ≤ optPayment E η cbar t - optPayment E η cbar s ∧
      optPayment E η cbar t - optPayment E η cbar s ≤ E.ε t - E.ε s := by
  rw [optPayment_eq_min, optPayment_eq_min]
  unfold Endowment.Y
  set d := E.ε t - E.ε s
  have hd : 0 ≤ d := by simp only [d]; linarith
  have ht1 : E.Ybar - cbar + E.ε t = (E.Ybar - cbar + E.ε s) + d := by simp only [d]; ring
  have ht2 : η * (E.Ybar + E.ε t) = η * (E.Ybar + E.ε s) + η * d := by simp only [d]; ring
  rw [ht1, ht2]
  have hηd : η * d ≤ d := by nlinarith
  have hηd0 : 0 ≤ η * d := mul_nonneg hη0 hd
  constructor
  · have := min_le_min (show E.Ybar - cbar + E.ε s ≤ (E.Ybar - cbar + E.ε s) + d by linarith)
      (show η * (E.Ybar + E.ε s) ≤ η * (E.Ybar + E.ε s) + η * d by linarith)
    linarith
  · have := min_le_min (show (E.Ybar - cbar + E.ε s) + d ≤ (E.Ybar - cbar + E.ε s) + d from
      le_rfl) (show η * (E.Ybar + E.ε s) + η * d ≤ η * (E.Ybar + E.ε s) + d by linarith)
    rw [min_add_add_right] at this
    linarith

/-- O&R p. 360: the optimal contract leaves the country strictly worse off than full
insurance whenever full insurance is not incentive compatible somewhere. -/
theorem worse_than_full_insurance (U : Utility) {η cbar : ℝ} (hη1 : η < 1)
    (hc : CbarEq E η cbar) (h : ∃ s, E.Ybar < floorCons E η s) :
    expectedUtility E U (optPayment E η cbar) < U.u E.Ybar := by
  obtain ⟨s, hs⟩ := h
  have hC : ∀ t, 0 < consumption E (optPayment E η cbar) t := fun t => by
    rw [consumption_optPayment]
    exact lt_of_lt_of_le (floorCons_pos E hη1 t) (le_max_right _ _)
  have hm := mean_consumption_opt E hc
  have hne : consumption E (optPayment E η cbar) s ≠
      E.Ω.expect (consumption E (optPayment E η cbar)) := by
    rw [hm, consumption_optPayment]
    exact ne_of_gt (lt_of_lt_of_le hs (le_max_right _ _))
  have := jensen_strict E.Ω U hC (E.prob_pos s) hne
  rw [hm] at this
  exact this

/-- "It is in the country's interest for sanctions to be as dire as possible", O&R p. 360:
the optimal value is weakly increasing in `η`. -/
theorem value_mono_eta (U : Utility) {η₁ η₂ c₁ c₂ : ℝ} (hη0 : 0 < η₁) (h12 : η₁ ≤ η₂)
    (hη1 : η₂ < 1) (hc₁ : CbarEq E η₁ c₁) (hc₂ : CbarEq E η₂ c₂) :
    expectedUtility E U (optPayment E η₁ c₁) ≤ expectedUtility E U (optPayment E η₂ c₂) := by
  have hIC : SanctionIC E η₂ (optPayment E η₁ c₁) := fun s =>
    le_trans (optPayment_ic E η₁ c₁ s) (mul_le_mul_of_nonneg_right h12 (E.Y_pos s).le)
  exact ((optimal_ic_contract E U (lt_of_lt_of_le hη0 h12) hη1 hc₂).2.2 _
    (optPayment_zero_profit E hc₁) hIC).1

/-- Strict version, O&R p. 360: if the sanction constraint binds in some state at `η₁`,
raising sanctions to `η₂ > η₁` strictly raises welfare. -/
theorem value_strictMono_eta (U : Utility) {η₁ η₂ c₁ c₂ : ℝ} (hη0 : 0 < η₁) (h12 : η₁ < η₂)
    (hη1 : η₂ < 1) (hc₁ : CbarEq E η₁ c₁) (hc₂ : CbarEq E η₂ c₂)
    (hbind : ∃ s, c₁ < floorCons E η₁ s) :
    expectedUtility E U (optPayment E η₁ c₁) < expectedUtility E U (optPayment E η₂ c₂) := by
  have hη₁1 : η₁ < 1 := lt_trans h12 hη1
  have hIC : SanctionIC E η₂ (optPayment E η₁ c₁) := fun s =>
    le_trans (optPayment_ic E η₁ c₁ s) (mul_le_mul_of_nonneg_right h12.le (E.Y_pos s).le)
  obtain ⟨hle, heq⟩ := (optimal_ic_contract E U (lt_trans hη0 h12) hη1 hc₂).2.2 _
    (optPayment_zero_profit E hc₁) hIC
  refine lt_of_le_of_ne hle fun he => ?_
  have hP := heq he
  -- a slack state exists at `η₁`
  obtain ⟨s₀, hs₀⟩ : ∃ s, floorCons E η₁ s < c₁ := by
    by_contra hn; push Not at hn
    have e : (fun s => max c₁ (floorCons E η₁ s)) = floorCons E η₁ := by
      funext s; exact max_eq_right (hn s)
    unfold CbarEq at hc₁; rw [e, expect_floorCons] at hc₁
    have := E.Ybar_pos; nlinarith
  obtain ⟨s₁, hs₁⟩ := hbind
  have hcons : ∀ s, max c₁ (floorCons E η₁ s) = max c₂ (floorCons E η₂ s) := fun s => by
    rw [← consumption_optPayment, ← consumption_optPayment, hP]
  have h0 := hcons s₀
  rw [max_eq_left hs₀.le] at h0
  have h1 := hcons s₁
  rw [max_eq_right hs₁.le] at h1
  have hlt : floorCons E η₂ s₁ < floorCons E η₁ s₁ := by
    unfold floorCons; nlinarith [E.Y_pos s₁]
  have hc2 : c₂ = floorCons E η₁ s₁ := by
    rcases le_total c₂ (floorCons E η₂ s₁) with h | h
    · rw [max_eq_right h] at h1; linarith
    · rw [max_eq_left h] at h1; exact h1.symm
  have : c₂ ≤ c₁ := by rw [h0]; exact le_max_left _ _
  linarith

/-- O&R p. 360: "as `η → 0` … contracting becomes altogether infeasible": with no sanctions
(`η = 0`) the only schedule satisfying (1) and (2) is the null contract. -/
theorem no_sanctions_autarky {P : S → ℝ} (hP : ZeroProfit E P) (hIC : SanctionIC E 0 P) :
    P = 0 := by
  funext s
  exact eq_zero_of_nonpos_of_expect_zero E.Ω (fun t => by simpa using hIC t) hP
    (E.prob_pos s)

/-! ## The uniform example, §6.1.1.4 -/

/-- The schedule (9) with threshold `e`, written as a continuous function of the shock:
`P(x) = η(Ȳ + e) + min(x − e, η(x − e))` (O&R (9), p. 358). -/
def uniformSchedule (η Ybar e x : ℝ) : ℝ := η * (Ybar + e) + min (x - e) (η * (x - e))

/-- The uniform schedule has the two arms of (9), O&R p. 358. -/
theorem uniformSchedule_arms {η : ℝ} (Ybar e x : ℝ) (hη1 : η ≤ 1) :
    (x ≤ e → uniformSchedule η Ybar e x = η * Ybar - (1 - η) * e + x) ∧
      (e ≤ x → uniformSchedule η Ybar e x = η * (Ybar + x)) := by
  unfold uniformSchedule
  constructor
  · intro h; rw [min_eq_left (by nlinarith)]; ring
  · intro h; rw [min_eq_right (by nlinarith)]; ring

/-- The integral of an affine function, used for the zero-profit integral of §6.1.1.4:
`∫_a^b (c + d(x − e)) dx = c(b − a) + d((b − e)² − (a − e)²)/2`.
(O&R §6.1.1.4, p. 358) -/
theorem integral_affine (a b c d e : ℝ) :
    ∫ x in a..b, (c + d * (x - e)) = c * (b - a) + d * ((b - e) ^ 2 - (a - e) ^ 2) / 2 := by
  have hderiv : ∀ x ∈ uIcc a b, HasDerivAt (fun x => c * x + d * (x - e) ^ 2 / 2)
      (c + d * (x - e)) x := by
    intro x _
    have h1 : HasDerivAt (fun x : ℝ => c * x) c x := by
      simpa using (hasDerivAt_id x).const_mul c
    have h2 : HasDerivAt (fun x : ℝ => d * (x - e) ^ 2 / 2) (d * (x - e)) x := by
      have := (((hasDerivAt_id' x).sub_const e).pow 2).const_mul d
      have := this.div_const 2
      convert this using 1
      push_cast; ring
    exact h1.add h2
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (by apply Continuous.intervalIntegrable; fun_prop)]
  ring

/-- **The zero-profit integral** of the uniform example, O&R §6.1.1.4, p. 358: for
`ε ~ U[−ε̄, ε̄]` and `e ∈ [−ε̄, ε̄]`,
`∫ P(ε) dε/(2ε̄) = [2ε̄η(Ȳ + e) − (e + ε̄)²/2 + η(ε̄ − e)²/2]/(2ε̄)`. -/
theorem uniform_zero_profit_integral {η : ℝ} (hη1 : η ≤ 1) (Ybar : ℝ) {e ebar : ℝ}
    (he1 : -ebar ≤ e) (he2 : e ≤ ebar) :
    ∫ x in (-ebar)..ebar, uniformSchedule η Ybar e x / (2 * ebar) =
      (2 * ebar * η * (Ybar + e) - (e + ebar) ^ 2 / 2 + η * (ebar - e) ^ 2 / 2) /
        (2 * ebar) := by
  rw [intervalIntegral.integral_div]
  congr 1
  have hint : ∀ a b, IntervalIntegrable (uniformSchedule η Ybar e) MeasureTheory.volume a b :=
    fun a b => by apply Continuous.intervalIntegrable; unfold uniformSchedule; fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (hint (-ebar) e) (hint e ebar)]
  have hA : ∫ x in (-ebar)..e, uniformSchedule η Ybar e x =
      ∫ x in (-ebar)..e, (η * (Ybar + e) + 1 * (x - e)) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le he1] at hx
    unfold uniformSchedule; rw [min_eq_left (by nlinarith [hx.2])]; ring
  have hB : ∫ x in e..ebar, uniformSchedule η Ybar e x =
      ∫ x in e..ebar, (η * (Ybar + e) + η * (x - e)) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le he2] at hx
    unfold uniformSchedule; rw [min_eq_right (by nlinarith [hx.1])]
  rw [hA, hB, integral_affine, integral_affine]
  ring

/-- **The quadratic for the threshold**, O&R p. 359: for `0 < η < 1`, `ε̄ > 0` and
`e ∈ [−ε̄, ε̄]`, the zero-profit condition holds iff
`e² + 2ε̄e + (ε̄² − 4ηε̄Ȳ/(1 − η)) = 0`. -/
theorem uniform_zero_profit_iff_quadratic {η : ℝ} (hη1 : η < 1) (Ybar : ℝ) {e ebar : ℝ}
    (hebar : 0 < ebar) (he1 : -ebar ≤ e) (he2 : e ≤ ebar) :
    (∫ x in (-ebar)..ebar, uniformSchedule η Ybar e x / (2 * ebar)) = 0 ↔
      e ^ 2 + 2 * ebar * e + (ebar ^ 2 - 4 * η * ebar * Ybar / (1 - η)) = 0 := by
  rw [uniform_zero_profit_integral hη1.le Ybar he1 he2]
  have h1 : (1 : ℝ) - η ≠ 0 := by linarith
  have h2 : (2 : ℝ) * ebar ≠ 0 := by positivity
  rw [div_eq_zero_iff, or_iff_left h2]
  constructor
  · intro h
    field_simp
    have : (1 - η) * (e ^ 2 + 2 * ebar * e + ebar ^ 2) - 4 * η * ebar * Ybar = 0 := by
      linarith
    linarith
  · intro h
    field_simp at h
    linarith

/-- The economically relevant root, O&R (10), p. 359:
`e = −ε̄ + 2√(ηε̄Ȳ/(1 − η))`. -/
noncomputable def uniformThreshold (η ebar Ybar : ℝ) : ℝ :=
  -ebar + 2 * Real.sqrt (η * ebar * Ybar / (1 - η))

/-- **O&R (10)**, p. 359: for `0 < η < 1`, `ε̄, Ȳ > 0` and `e ∈ [−ε̄, ε̄]`, the uniform
schedule earns insurers zero expected profit iff `e = −ε̄ + 2√(ηε̄Ȳ/(1 − η))` (the other
root of the quadratic lies below `−ε̄` and is disregarded). -/
theorem uniform_threshold_iff {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η < 1) {Ybar e ebar : ℝ}
    (hY : 0 < Ybar) (hebar : 0 < ebar) (he1 : -ebar ≤ e) (he2 : e ≤ ebar) :
    (∫ x in (-ebar)..ebar, uniformSchedule η Ybar e x / (2 * ebar)) = 0 ↔
      e = uniformThreshold η ebar Ybar := by
  rw [uniform_zero_profit_iff_quadratic hη1 Ybar hebar he1 he2]
  unfold uniformThreshold
  have hk : 0 ≤ η * ebar * Ybar / (1 - η) := by
    apply div_nonneg (by positivity) (by linarith)
  have hsq := Real.sq_sqrt hk
  have hsn := Real.sqrt_nonneg (η * ebar * Ybar / (1 - η))
  have e4 : 4 * η * ebar * Ybar / (1 - η) = 4 * (η * ebar * Ybar / (1 - η)) := by ring
  rw [e4]
  constructor
  · intro h
    have hq : (e + ebar) ^ 2 = (2 * Real.sqrt (η * ebar * Ybar / (1 - η))) ^ 2 := by
      nlinarith
    have := (sq_eq_sq₀ (by linarith) (by positivity)).mp hq
    linarith
  · intro h
    rw [h]; nlinarith

/-- O&R p. 359: the incentive constraint binds over a nonempty range, `e < ε̄`, iff
`ε̄ > η(Ȳ + ε̄)` — sanctions are too weak to support full insurance. -/
theorem uniformThreshold_lt_iff {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η < 1) {Ybar ebar : ℝ}
    (hY : 0 < Ybar) (hebar : 0 < ebar) :
    uniformThreshold η ebar Ybar < ebar ↔ η * (Ybar + ebar) < ebar := by
  unfold uniformThreshold
  have h1 : (0 : ℝ) < 1 - η := by linarith
  have hk : 0 ≤ η * ebar * Ybar / (1 - η) := div_nonneg (by positivity) h1.le
  rw [show -ebar + 2 * Real.sqrt (η * ebar * Ybar / (1 - η)) < ebar ↔
      Real.sqrt (η * ebar * Ybar / (1 - η)) < ebar by constructor <;> intro h <;> linarith]
  rw [Real.sqrt_lt' hebar, div_lt_iff₀ h1]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-- O&R p. 360: `e > −ε̄` iff `η > 0` (with no sanctions, `e = −ε̄` and no insurance). -/
theorem uniformThreshold_gt_iff {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η < 1) {Ybar ebar : ℝ}
    (hY : 0 < Ybar) (hebar : 0 < ebar) :
    -ebar < uniformThreshold η ebar Ybar ↔ 0 < η := by
  unfold uniformThreshold
  have h1 : (0 : ℝ) < 1 - η := by linarith
  constructor
  · intro h
    have : 0 < Real.sqrt (η * ebar * Ybar / (1 - η)) := by linarith
    rw [Real.sqrt_pos] at this
    by_contra hn; push Not at hn
    have : η = 0 := le_antisymm hn hη0
    subst this; simp at *
  · intro h
    have : 0 < Real.sqrt (η * ebar * Ybar / (1 - η)) :=
      Real.sqrt_pos.mpr (div_pos (by positivity) h1)
    linarith

/-- O&R p. 360: higher sanctions raise `e`: the threshold is strictly increasing in
`η ∈ [0, 1)`. -/
theorem uniformThreshold_strictMono {Ybar ebar : ℝ} (hY : 0 < Ybar) (hebar : 0 < ebar) :
    StrictMonoOn (fun η => uniformThreshold η ebar Ybar) (Ico 0 1) := by
  intro a ha b hb hab
  simp only [uniformThreshold]
  have ha1 : (0 : ℝ) < 1 - a := by linarith [ha.2]
  have hb1 : (0 : ℝ) < 1 - b := by linarith [hb.2]
  have hlt : a * ebar * Ybar / (1 - a) < b * ebar * Ybar / (1 - b) := by
    rw [div_lt_div_iff₀ ha1 hb1]
    have : 0 < ebar * Ybar := by positivity
    nlinarith [ha.1]
  have := Real.sqrt_lt_sqrt (div_nonneg (by have := ha.1; positivity) ha1.le) hlt
  linarith

/-- O&R p. 360: "as `η → 0`, `e → ε_ = −ε̄`". -/
theorem uniformThreshold_tendsto {Ybar ebar : ℝ} :
    Tendsto (fun η => uniformThreshold η ebar Ybar) (𝓝[>] 0) (𝓝 (-ebar)) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds
  have hc : ContinuousAt (fun η => uniformThreshold η ebar Ybar) 0 := by
    unfold uniformThreshold
    apply ContinuousAt.add continuousAt_const
    apply ContinuousAt.mul continuousAt_const
    apply Real.continuous_sqrt.continuousAt.comp
    apply ContinuousAt.div (by fun_prop) (by fun_prop) (by norm_num)
  have := hc.tendsto
  simpa [uniformThreshold] using this

/-- O&R p. 360: "`e` could well be negative (just take `η` low enough)": `e < 0` iff
`η < ε̄/(4Ȳ + ε̄)`. -/
theorem uniformThreshold_neg_iff {η : ℝ} (hη1 : η < 1) {Ybar ebar : ℝ}
    (hY : 0 < Ybar) (hebar : 0 < ebar) :
    uniformThreshold η ebar Ybar < 0 ↔ η < ebar / (4 * Ybar + ebar) := by
  unfold uniformThreshold
  have h1 : (0 : ℝ) < 1 - η := by linarith
  rw [show -ebar + 2 * Real.sqrt (η * ebar * Ybar / (1 - η)) < 0 ↔
      Real.sqrt (η * ebar * Ybar / (1 - η)) < ebar / 2 by constructor <;> intro h <;> linarith]
  rw [Real.sqrt_lt' (by positivity), div_lt_iff₀ h1, lt_div_iff₀ (by positivity)]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-- O&R p. 359 and Figure 6.2 in the uniform example: whenever the constraint binds
(`e < ε̄`), constrained consumption in the low states is below mean output,
`(1 − η)(Ȳ + e) < Ȳ` (equivalently `P₀ > 0`). -/
theorem uniform_floor_below_mean {η : ℝ} (hη0 : 0 ≤ η) (hη1 : η < 1) {Ybar ebar : ℝ}
    (hY : 0 < Ybar) (hebar : 0 < ebar) (hbind : uniformThreshold η ebar Ybar < ebar) :
    (1 - η) * (Ybar + uniformThreshold η ebar Ybar) < Ybar := by
  have h1 : (0 : ℝ) < 1 - η := by linarith
  have hb := (uniformThreshold_lt_iff hη0 hη1 hY hebar).mp hbind
  unfold uniformThreshold at *
  set k := η * Ybar / (1 - η) with hkdef
  have hk0 : 0 ≤ k := div_nonneg (by positivity) h1.le
  have hkeq : η * ebar * Ybar / (1 - η) = ebar * k := by rw [hkdef]; ring
  rw [hkeq]
  have hkne : k ≠ ebar := by
    intro h; rw [hkdef, div_eq_iff h1.ne'] at h; nlinarith
  -- AM–GM: 2√(ε̄k) < k + ε̄ when k ≠ ε̄
  have hs := Real.sq_sqrt (show 0 ≤ ebar * k by positivity)
  have hsn := Real.sqrt_nonneg (ebar * k)
  have hamgm : 2 * Real.sqrt (ebar * k) < k + ebar := by
    have hne : Real.sqrt (ebar * k) ≠ (k + ebar) / 2 := by
      intro h
      have : ebar * k = ((k + ebar) / 2) ^ 2 := by rw [← hs, h]
      apply hkne; nlinarith [sq_nonneg (k - ebar)]
    have hle : Real.sqrt (ebar * k) ≤ (k + ebar) / 2 := by
      rw [Real.sqrt_le_left (by positivity)]; nlinarith [sq_nonneg (k - ebar)]
    have := lt_of_le_of_ne hle hne
    linarith
  have hk1 : (1 - η) * k = η * Ybar := by rw [hkdef]; field_simp
  nlinarith


/-! ## The optimal contract for a general continuous density (fn 6, §6.1.1.3) -/

namespace ContinuousDensity

/-- The floor `(1 − η)(Ȳ + x)` imposed by the sanction constraint (2) in state `x`
(O&R Figure 6.2, p. 360). -/
def lo (η Ybar x : ℝ) : ℝ := (1 - η) * (Ybar + x)

/-- The mean of `g` under the density `f` on `[−ε̄, ε̄]`, O&R footnote 6, p. 354:
`∫_{−ε̄}^{ε̄} g(ε) π(ε) dε`. -/
noncomputable def dmean (f : ℝ → ℝ) (ebar : ℝ) (g : ℝ → ℝ) : ℝ := ∫ x in (-ebar)..ebar, g x * f x

/-- Integrability of continuous integrands against a continuous density. (O&R footnote 6, p. 354) -/
theorem integrable_mul {f g : ℝ → ℝ} {ebar : ℝ} (hebar : 0 < ebar)
    (hf : ContinuousOn f (Set.Icc (-ebar) ebar)) (hg : ContinuousOn g (Set.Icc (-ebar) ebar)) :
    IntervalIntegrable (fun x => g x * f x) MeasureTheory.volume (-ebar) ebar := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le (by linarith)]
  exact hg.mul hf

/-- The density mean of a constant is the constant (`∫ π = 1`). (O&R footnote 6, p. 354) -/
theorem dmean_const {f : ℝ → ℝ} {ebar : ℝ} (hf1 : ∫ x in (-ebar)..ebar, f x = 1) (k : ℝ) :
    dmean f ebar (fun _ => k) = k := by
  unfold dmean; rw [intervalIntegral.integral_const_mul, hf1, mul_one]

/-- The density mean is monotone in the integrand (`f ≥ 0`). (O&R footnote 6, p. 354) -/
theorem dmean_mono {f g h : ℝ → ℝ} {ebar : ℝ} (hebar : 0 < ebar)
    (hf : ContinuousOn f (Set.Icc (-ebar) ebar)) (hf0 : ∀ x ∈ Set.Icc (-ebar) ebar, 0 ≤ f x)
    (hg : ContinuousOn g (Set.Icc (-ebar) ebar)) (hh : ContinuousOn h (Set.Icc (-ebar) ebar))
    (hgh : ∀ x ∈ Set.Icc (-ebar) ebar, g x ≤ h x) : dmean f ebar g ≤ dmean f ebar h :=
  intervalIntegral.integral_mono_on (by linarith) (integrable_mul hebar hf hg)
    (integrable_mul hebar hf hh) fun x hx => mul_le_mul_of_nonneg_right (hgh x hx) (hf0 x hx)

/-- Linearity of the density mean: `E[a + b g] = a + b E g` (`∫ f = 1`). (O&R footnote 6, p. 354) -/
theorem dmean_affine {f g : ℝ → ℝ} {ebar : ℝ} (hebar : 0 < ebar)
    (hf : ContinuousOn f (Set.Icc (-ebar) ebar)) (hf1 : ∫ x in (-ebar)..ebar, f x = 1)
    (hg : ContinuousOn g (Set.Icc (-ebar) ebar)) (a b : ℝ) :
    dmean f ebar (fun x => a + b * g x) = a + b * dmean f ebar g := by
  unfold dmean
  have e : (fun x => (a + b * g x) * f x) = fun x => a * f x + b * (g x * f x) := by
    funext x; ring
  have hi1 : IntervalIntegrable (fun x => a * f x) MeasureTheory.volume (-ebar) ebar := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (by linarith)]
    exact continuousOn_const.mul hf
  rw [e, intervalIntegral.integral_add hi1 ((integrable_mul hebar hf hg).const_mul b),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, hf1, mul_one]

/-- The mean of the floor: `∫ (1 − η)(Ȳ + ε)π = (1 − η)Ȳ` for a mean-zero density
(O&R p. 359). -/
theorem dmean_lo {f : ℝ → ℝ} {ebar : ℝ} (hebar : 0 < ebar)
    (hf : ContinuousOn f (Set.Icc (-ebar) ebar)) (hf1 : ∫ x in (-ebar)..ebar, f x = 1)
    (hfm : ∫ x in (-ebar)..ebar, x * f x = 0) (η Ybar : ℝ) :
    dmean f ebar (lo η Ybar) = (1 - η) * Ybar := by
  have e : lo η Ybar = fun x => (1 - η) * Ybar + (1 - η) * x := by
    funext x; unfold lo; ring
  have h := dmean_affine hebar hf hf1 (g := fun x => x) continuousOn_id ((1 - η) * Ybar)
    (1 - η)
  rw [e, h]
  unfold dmean; rw [hfm]; ring

/-- The candidate consumption schedule `C*(ε) = max(c̄, (1 − η)(Ȳ + ε))` is continuous.
(O&R footnote 6, p. 354) -/
theorem continuous_clamp (η Ybar c : ℝ) : Continuous fun x => max c (lo η Ybar x) := by
  unfold lo; fun_prop

/-- **Existence of `c̄` for a general continuous density**, O&R (7), p. 357 and fn 6: for a
continuous density `π ≥ 0` on `[−ε̄, ε̄]` with mean zero and `Ȳ − ε̄ > 0`, there is `c̄ > 0` with
`∫ max(c̄, (1 − η)(Ȳ + ε))π(ε) dε = Ȳ`. -/
theorem density_cbar_exists {f : ℝ → ℝ} {ebar η Ybar : ℝ} (hebar : 0 < ebar)
    (hf : ContinuousOn f (Set.Icc (-ebar) ebar)) (hf0 : ∀ x ∈ Set.Icc (-ebar) ebar, 0 ≤ f x)
    (hf1 : ∫ x in (-ebar)..ebar, f x = 1) (hfm : ∫ x in (-ebar)..ebar, x * f x = 0)
    (hY : 0 < Ybar - ebar) (hη0 : 0 < η) (hη1 : η < 1) :
    ∃ c, 0 < c ∧ dmean f ebar (fun x => max c (lo η Ybar x)) = Ybar := by
  set Φ : ℝ → ℝ := fun c => dmean f ebar (fun x => max c (lo η Ybar x)) with hΦ
  have hlip : ∀ c₁ c₂, |Φ c₁ - Φ c₂| ≤ |c₁ - c₂| := by
    intro c₁ c₂
    have hsub : Φ c₁ - Φ c₂ = dmean f ebar (fun x => max c₁ (lo η Ybar x) -
        max c₂ (lo η Ybar x)) := by
      simp only [hΦ, dmean]
      rw [← intervalIntegral.integral_sub (integrable_mul hebar hf
        (continuous_clamp η Ybar c₁).continuousOn) (integrable_mul hebar hf
        (continuous_clamp η Ybar c₂).continuousOn)]
      apply intervalIntegral.integral_congr; intro x _; simp only; ring
    have hc : ContinuousOn (fun x => max c₁ (lo η Ybar x) - max c₂ (lo η Ybar x))
        (Set.Icc (-ebar) ebar) :=
      ((continuous_clamp η Ybar c₁).sub (continuous_clamp η Ybar c₂)).continuousOn
    have hup := dmean_mono hebar hf hf0 hc continuousOn_const (h := fun _ => |c₁ - c₂|)
      fun x _ => le_trans (le_abs_self _) (abs_max_sub_max_le_abs _ _ _)
    have hlow := dmean_mono hebar hf hf0 continuousOn_const hc (g := fun _ => -|c₁ - c₂|)
      fun x _ => by have := abs_max_sub_max_le_abs c₁ c₂ (lo η Ybar x); rw [abs_le] at this
                    linarith [this.1]
    rw [dmean_const hf1] at hup hlow
    rw [hsub, abs_le]; exact ⟨hlow, hup⟩
  have hcont : Continuous Φ := by
    apply (LipschitzWith.of_dist_le' (K := 1) fun c₁ c₂ => ?_).continuous
    rw [Real.dist_eq, Real.dist_eq, one_mul]; exact hlip c₁ c₂
  have hlo_pos : ∀ x ∈ Set.Icc (-ebar) ebar, 0 < lo η Ybar x := fun x hx => by
    unfold lo; have := hx.1; exact mul_pos (by linarith) (by linarith)
  have h0 : Φ 0 = (1 - η) * Ybar := by
    simp only [hΦ]
    rw [← dmean_lo hebar hf hf1 hfm η Ybar]
    unfold dmean
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le (by linarith)] at hx
    simp only [max_eq_right (hlo_pos x hx).le]
  have hYpos : 0 < Ybar := by linarith
  have hYv : Ybar ≤ Φ Ybar := by
    have := dmean_mono hebar hf hf0 continuousOn_const (continuous_clamp η Ybar Ybar).continuousOn
      (g := fun _ => Ybar) fun x _ => le_max_left _ _
    rw [dmean_const hf1] at this; exact this
  obtain ⟨c, hc, hceq⟩ := SovereignRiskPrimitives.StateSpaceFacts.exists_eq_of_continuous hcont
    hYpos.le (a := 0) (T := Ybar) (by rw [h0]; nlinarith) hYv
  refine ⟨c, lt_of_le_of_ne hc.1 fun h => ?_, hceq⟩
  subst h
  rw [h0] at hceq
  nlinarith

/-- **The optimal incentive-compatible contract for a general continuous density**, O&R
§6.1.1.3 with footnote 6 (the book's own continuous case, p. 357). With `c̄ > 0` solving the
mean equation, the payment `P*(ε) = Ȳ + ε − max(c̄, (1 − η)(Ȳ + ε))` satisfies the zero-profit
condition and (2), and every continuous schedule `P` satisfying `∫ Pπ = 0` and (2) gives
`∫ u(Ȳ + ε − P)π ≤ ∫ u(Ȳ + ε − P*)π`, strictly if `P ≠ P*` at a point where `π > 0`. -/
theorem density_optimal (U : SovereignRiskPrimitives.Utility) {f : ℝ → ℝ} {ebar η Ybar c : ℝ}
    (hebar : 0 < ebar) (hf : ContinuousOn f (Set.Icc (-ebar) ebar))
    (hf0 : ∀ x ∈ Set.Icc (-ebar) ebar, 0 ≤ f x) (hf1 : ∫ x in (-ebar)..ebar, f x = 1)
    (hfm : ∫ x in (-ebar)..ebar, x * f x = 0) (hY : 0 < Ybar - ebar) (hη1 : η < 1)
    (hc : 0 < c) (hceq : dmean f ebar (fun x => max c (lo η Ybar x)) = Ybar)
    {P : ℝ → ℝ} (hP : ContinuousOn P (Set.Icc (-ebar) ebar)) (hzp : dmean f ebar P = 0)
    (hic : ∀ x ∈ Set.Icc (-ebar) ebar, P x ≤ η * (Ybar + x)) :
    dmean f ebar (fun x => Ybar + x - max c (lo η Ybar x)) = 0 ∧
      (∀ x, Ybar + x - max c (lo η Ybar x) ≤ η * (Ybar + x)) ∧
      dmean f ebar (fun x => U.u (Ybar + x - P x)) ≤
        dmean f ebar (fun x => U.u (max c (lo η Ybar x))) ∧
      ((∃ x ∈ Set.Icc (-ebar) ebar, 0 < f x ∧ P x ≠ Ybar + x - max c (lo η Ybar x)) →
        dmean f ebar (fun x => U.u (Ybar + x - P x)) <
          dmean f ebar (fun x => U.u (max c (lo η Ybar x)))) := by
  have hlo_pos : ∀ x ∈ Set.Icc (-ebar) ebar, 0 < lo η Ybar x := fun x hx => by
    unfold lo; have := hx.1; exact mul_pos (by linarith) (by linarith)
  set Cs : ℝ → ℝ := fun x => max c (lo η Ybar x) with hCs
  set C : ℝ → ℝ := fun x => Ybar + x - P x with hC
  have hCcont : ContinuousOn C (Set.Icc (-ebar) ebar) :=
    (continuousOn_const.add continuousOn_id).sub hP
  have hCscont : Continuous Cs := continuous_clamp η Ybar c
  have hClo : ∀ x ∈ Set.Icc (-ebar) ebar, lo η Ybar x ≤ C x := fun x hx => by
    have := hic x hx; simp only [hC]; unfold lo; linarith
  have hCpos : ∀ x ∈ Set.Icc (-ebar) ebar, 0 < C x := fun x hx =>
    lt_of_lt_of_le (hlo_pos x hx) (hClo x hx)
  have hCspos : ∀ x, 0 < Cs x := fun x => lt_of_lt_of_le hc (le_max_left _ _)
  -- means
  have hmeanC : dmean f ebar C = Ybar := by
    have e : C = fun x => Ybar + (1 : ℝ) * (x - P x) := by funext x; simp only [hC]; ring
    have h := dmean_affine hebar hf hf1 (g := fun x => x - P x) (continuousOn_id.sub hP)
      Ybar 1
    rw [e, h]
    unfold dmean
    rw [show (fun x => (x - P x) * f x) = fun x => x * f x - P x * f x from
      funext fun x => by ring, intervalIntegral.integral_sub (integrable_mul hebar hf
        (g := fun x => x) continuousOn_id) (integrable_mul hebar hf hP), hfm]
    unfold dmean at hzp; rw [hzp]; ring
  have hzpS : dmean f ebar (fun x => Ybar + x - Cs x) = 0 := by
    have e : (fun x => Ybar + x - Cs x) = fun x => Ybar + (1 : ℝ) * (x - Cs x) := by
      funext x; ring
    have h := dmean_affine hebar hf hf1 (g := fun x => x - Cs x)
      (continuousOn_id.sub hCscont.continuousOn) Ybar 1
    rw [e, h]
    unfold dmean
    rw [show (fun x => (x - Cs x) * f x) = fun x => x * f x - Cs x * f x from
      funext fun x => by ring, intervalIntegral.integral_sub (integrable_mul hebar hf
        (g := fun x => x) continuousOn_id) (integrable_mul hebar hf hCscont.continuousOn), hfm]
    unfold dmean at hceq; rw [hceq]; ring
  -- pointwise supporting line with multiplier `u′(c̄)`
  have hkey : ∀ x ∈ Set.Icc (-ebar) ebar,
      U.u (C x) ≤ U.u (Cs x) + U.du c * (C x - Cs x) := by
    intro x hx
    have hsl := U.supporting_line (hCpos x hx) (hCspos x)
    have : U.du (Cs x) * (C x - Cs x) ≤ U.du c * (C x - Cs x) := by
      simp only [hCs]
      rcases le_total (lo η Ybar x) c with h | h
      · rw [max_eq_left h]
      · rw [max_eq_right h]
        have hd := U.du_anti hc h
        have : 0 ≤ C x - lo η Ybar x := by linarith [hClo x hx]
        nlinarith
    linarith
  have huC : ContinuousOn (fun x => U.u (C x)) (Set.Icc (-ebar) ebar) :=
    U.continuousOn.comp hCcont fun x hx => Set.mem_Ioi.mpr (hCpos x hx)
  have huCs : ContinuousOn (fun x => U.u (Cs x)) (Set.Icc (-ebar) ebar) :=
    U.continuousOn.comp hCscont.continuousOn fun x _ => Set.mem_Ioi.mpr (hCspos x)
  have hRcont : ContinuousOn (fun x => U.u (Cs x) + U.du c * (C x - Cs x))
      (Set.Icc (-ebar) ebar) :=
    huCs.add (continuousOn_const.mul (hCcont.sub hCscont.continuousOn))
  have hR : dmean f ebar (fun x => U.u (Cs x) + U.du c * (C x - Cs x)) =
      dmean f ebar (fun x => U.u (Cs x)) + U.du c * (dmean f ebar C - dmean f ebar Cs) := by
    unfold dmean
    rw [show (fun x => (U.u (Cs x) + U.du c * (C x - Cs x)) * f x) = fun x =>
      U.u (Cs x) * f x + U.du c * (C x * f x - Cs x * f x) from funext fun x => by ring,
      intervalIntegral.integral_add (integrable_mul hebar hf huCs)
        (((integrable_mul hebar hf hCcont).sub
          (integrable_mul hebar hf hCscont.continuousOn)).const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_sub
        (integrable_mul hebar hf hCcont) (integrable_mul hebar hf hCscont.continuousOn)]
  have hmeanCs : dmean f ebar Cs = Ybar := hceq
  have hle := dmean_mono hebar hf hf0 huC hRcont hkey
  rw [hR, hmeanC, hmeanCs, sub_self, mul_zero, add_zero] at hle
  refine ⟨hzpS, fun x => ?_, hle, fun ⟨x₀, hx₀, hf₀, hne⟩ => ?_⟩
  · have := le_max_right c (lo η Ybar x); unfold lo at this ⊢; linarith
  · have hlt : dmean f ebar (fun x => U.u (C x)) <
        dmean f ebar (fun x => U.u (Cs x) + U.du c * (C x - Cs x)) := by
      unfold dmean
      apply intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt
        (by linarith) (huC.mul hf) (hRcont.mul hf)
      · intro x hx
        exact mul_le_mul_of_nonneg_right (hkey x (Set.Ioc_subset_Icc_self hx))
          (hf0 x (Set.Ioc_subset_Icc_self hx))
      · refine ⟨x₀, hx₀, mul_lt_mul_of_pos_right ?_ hf₀⟩
        have hCne : C x₀ ≠ Cs x₀ := by
          simp only [hC, hCs]; intro h; apply hne; linarith
        have hsl := U.supporting_line_strict (hCpos x₀ hx₀) (hCspos x₀) hCne
        have : U.du (Cs x₀) * (C x₀ - Cs x₀) ≤ U.du c * (C x₀ - Cs x₀) := by
          simp only [hCs]
          rcases le_total (lo η Ybar x₀) c with h | h
          · rw [max_eq_left h]
          · rw [max_eq_right h]
            have hd := U.du_anti hc h
            have : 0 ≤ C x₀ - lo η Ybar x₀ := by linarith [hClo x₀ hx₀]
            nlinarith
        linarith
    rw [hR, hmeanC, hmeanCs, sub_self, mul_zero, add_zero] at hlt
    exact hlt

/-- The uniform schedule of §6.1.1.4 is the clamp contract with `c̄ = (1 − η)(Ȳ + e)`
(O&R (9), p. 358). -/
theorem uniformSchedule_eq_clamp {η Ybar e : ℝ} (hη1 : η < 1) (x : ℝ) :
    uniformSchedule η Ybar e x = Ybar + x - max ((1 - η) * (Ybar + e)) (lo η Ybar x) := by
  unfold uniformSchedule lo
  rcases le_total x e with h | h
  · rw [min_eq_left (by nlinarith), max_eq_left (by nlinarith)]; ring
  · rw [min_eq_right (by nlinarith), max_eq_right (by nlinarith)]; ring

end ContinuousDensity

end ObstfeldRogoff.CapitalMarketImperfections.DirectSanctionsInsurance
