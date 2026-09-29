/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MoneyExchangeRates.NominalAssetPricing
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic
import Mathlib.Probability.Moments.Covariance
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Comp

/-!
# The forward foreign-exchange premium

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §8.7.5 and
Exercises 6–8, pp. 585–592, 601–603.

* Covered interest parity (104): state prices imply CIP; if CIP fails there is an explicit
  zero-cost portfolio with a strictly positive riskless payoff (an arbitrage), which no
  strictly positive state-price vector can price.
* Siegel's paradox (p. 586): `E[ℰ] E[1/ℰ] ≥ 1`, with equality iff `ℰ` is degenerate, so the
  dollar and yen versions of (105) hold together iff the exchange rate is nonrandom.
  (106) for a genuinely Gaussian log exchange rate (Mathlib's Gaussian law): the dollar and
  yen log forward rates are `m ± v/2`. The p. 587 number: `½ (0.1)² = 0.005`.
* Real speculative profits: (107) ⟺ (108) under relative PPP; the exact finite-state
  forward rate `F = E[ℰ/P]/E[1/P] = E[ℰ] + Cov(ℰ, 1/P)/E[1/P]`; (109) given the lognormal
  moment identity for the two relevant linear combinations (fn 75), and (109), (119) under
  genuine joint normality (Mathlib's `HasGaussianLaw` for `(e, p)` and `(e, p, c)`).
* The Fama decomposition (110)–(115) on a two-date finite event tree: the rational-
  expectations orthogonality is DERIVED (tower property); the population OLS slope
  minimises mean squared error; `a₁ < 0 ⇒ Cov(D, rp) < 0`, `a₁ < ½ ⇒ Var rp > Var D`.
* The forward rate in general equilibrium (116)–(119): the real-return differential
  identity, the forward-position Euler equation (necessary and sufficient), CRRA form,
  exact covariance form, and (119) given the lognormal moment identity.
* Exercise 6 (Engel 1992): `∂C/∂C_j = p_j/P` for homogeneous `Ω`; the multi-good
  forward Euler equations; the yen version and risk neutrality (no Siegel paradox in real
  terms); the two-good cash-in-advance spot rate and forward rate with independent money
  and output shocks; the "risk-neutral" forward equation (107) and its yen version.
* Exercises 7 and 8: time-averaged exchange rates are not random walks (autocorrelation
  1/6); point sampling is; overlapping forecast errors have correlation 1/2; every-other-
  observation errors are uncorrelated for ANY exchange-rate process (tower property).
-/

namespace ObstfeldRogoff.MoneyExchangeRates.ForwardPremium

open Finset Filter Topology
open ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing

variable {S : Type} [Fintype S]

/-! ## Covered interest parity (104) -/

/-- The dollar cost at `t` of `a` dollars in dollar bonds and `b` yen in yen bonds (the
forward position costs nothing) (O&R (104), p. 585). -/
def cipCost (E a b : ℝ) : ℝ := a + b * E

/-- The dollar payoff at `t+1` in state `s` of `a` dollars in dollar bonds, `b` yen in yen
bonds and `c` yen bought forward at `F` (O&R (104), p. 585). -/
def cipPayoff (i istar F : ℝ) (E' : S → ℝ) (a b c : ℝ) (s : S) : ℝ :=
  a * (1 + i) + b * (1 + istar) * E' s + c * (E' s - F)

omit [Fintype S] in
/-- **The covered-interest-arbitrage portfolio is riskless** (O&R p. 586): borrow one
dollar, buy `1/ℰ` yen, invest at `i*`, sell the proceeds forward. It costs nothing and pays
`(1+i*)F/ℰ − (1+i)` in EVERY state. -/
theorem cip_portfolio_riskless {i istar E F : ℝ} (hE : E ≠ 0) (E' : S → ℝ) (s : S) :
    cipCost E (-1) (1 / E) = 0 ∧
      cipPayoff i istar F E' (-1) (1 / E) (-((1 + istar) / E)) s
        = (1 + istar) * F / E - (1 + i) := by
  constructor
  · simp only [cipCost]; field_simp; ring
  · simp only [cipPayoff]; field_simp; ring

omit [Fintype S] in
/-- **If CIP fails there is an arbitrage** (O&R (104), p. 585): a zero-cost portfolio whose
payoff is strictly positive in every state. -/
theorem arbitrage_of_not_cip {i istar E F : ℝ} (hE : E ≠ 0) (E' : S → ℝ)
    (hcip : 1 + i ≠ (1 + istar) * F / E) :
    ∃ a b c : ℝ, cipCost E a b = 0 ∧ ∀ s, 0 < cipPayoff i istar F E' a b c s := by
  rcases lt_or_gt_of_ne hcip with h | h
  · refine ⟨-1, 1 / E, -((1 + istar) / E), ?_, fun s => ?_⟩
    · simp only [cipCost]; field_simp; ring
    · rw [(cip_portfolio_riskless hE E' s).2]; linarith
  · refine ⟨1, -(1 / E), (1 + istar) / E, ?_, fun s => ?_⟩
    · simp only [cipCost]; field_simp; ring
    · have := (cip_portfolio_riskless (i := i) (istar := istar) (F := F) hE E' s).2
      simp only [cipPayoff] at this ⊢
      linarith

/-- A strictly positive state-price vector values every portfolio (O&R p. 586, "no
arbitrage"): dollar bonds, yen bonds and forwards are priced by `q`. -/
structure StatePrices (S : Type) [Fintype S] where
  q : S → ℝ
  q_pos : ∀ s, 0 < q s

/-- The pricing conditions for the three instruments (O&R (104), p. 585). -/
def PricesInstruments (qs : StatePrices S) (i istar E F : ℝ) (E' : S → ℝ) : Prop :=
  (∑ s, qs.q s * (1 + i) = 1) ∧ (∑ s, qs.q s * ((1 + istar) * E' s) = E) ∧
    (∑ s, qs.q s * (E' s - F) = 0)

/-- **State prices imply covered interest parity** (O&R (104), p. 585):
`1 + i = (1 + i*) F/ℰ`. -/
theorem cip_of_statePrices [Nonempty S] {qs : StatePrices S} {i istar E F : ℝ}
    {E' : S → ℝ} (hE : 0 < E) (hp : PricesInstruments qs i istar E F E') :
    1 + i = (1 + istar) * F / E := by
  obtain ⟨h1, h2, h3⟩ := hp
  have hQ : 0 < ∑ s, qs.q s := Finset.sum_pos (fun s _ => qs.q_pos s) Finset.univ_nonempty
  have hb : (∑ s, qs.q s) * (1 + i) = 1 := by rw [Finset.sum_mul]; exact h1
  have hf : ∑ s, qs.q s * E' s = F * ∑ s, qs.q s := by
    have : ∑ s, (qs.q s * E' s - F * qs.q s) = 0 := by
      rw [← h3]; exact Finset.sum_congr rfl fun s _ => by ring
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at this
    linarith
  have hy : (1 + istar) * ∑ s, qs.q s * E' s = E := by
    rw [Finset.mul_sum, ← h2]; exact Finset.sum_congr rfl fun s _ => by ring
  rw [hf] at hy
  field_simp
  nlinarith [hb, hy]

/-- **An arbitrage cannot be priced by strictly positive state prices** (O&R p. 586). -/
theorem no_statePrices_of_arbitrage [Nonempty S] (qs : StatePrices S) {i istar E F : ℝ}
    {E' : S → ℝ} (hp : PricesInstruments qs i istar E F E') {a b c : ℝ}
    (hcost : cipCost E a b = 0) (hpay : ∀ s, 0 < cipPayoff i istar F E' a b c s) :
    False := by
  obtain ⟨h1, h2, h3⟩ := hp
  have hval : ∑ s, qs.q s * cipPayoff i istar F E' a b c s = cipCost E a b := by
    have e : ∀ s, qs.q s * cipPayoff i istar F E' a b c s = a * (qs.q s * (1 + i))
        + b * (qs.q s * ((1 + istar) * E' s)) + c * (qs.q s * (E' s - F)) := fun s => by
      simp only [cipPayoff]; ring
    simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum, h1, h2, h3, cipCost]
    ring
  have hpos : 0 < ∑ s, qs.q s * cipPayoff i istar F E' a b c s :=
    Finset.sum_pos (fun s _ => mul_pos (qs.q_pos s) (hpay s)) Finset.univ_nonempty
  linarith

/-! ## Siegel's paradox (105)–(106) -/

/-- The symmetrised Jensen gap: `E[X]E[1/X] − 1 = ½ ΣΣ πᵢπⱼ (Xᵢ − Xⱼ)²/(XᵢXⱼ)`
(O&R p. 586, Jensen's inequality for `1/(·)` made exact on a finite space). -/
theorem expect_mul_expect_inv (Ω : FinProb S) {X : S → ℝ} (hX : ∀ s, 0 < X s) :
    2 * (Ω.expect X * Ω.expect (fun s => 1 / X s) - 1)
      = ∑ i, ∑ j, Ω.prob i * Ω.prob j * (X i - X j) ^ 2 / (X i * X j) := by
  have h1 : Ω.expect X * Ω.expect (fun s => 1 / X s)
      = ∑ i, ∑ j, Ω.prob i * Ω.prob j * (X i / X j) := by
    simp only [FinProb.expect, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have hsym : ∑ i, ∑ j, Ω.prob i * Ω.prob j * (X j / X i)
      = ∑ i, ∑ j, Ω.prob i * Ω.prob j * (X i / X j) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have e : ∀ i j, Ω.prob i * Ω.prob j * (X i - X j) ^ 2 / (X i * X j)
      = Ω.prob i * Ω.prob j * (X i / X j) + Ω.prob i * Ω.prob j * (X j / X i)
        - 2 * (Ω.prob i * Ω.prob j) := fun i j => by
    have := hX i; have := hX j
    field_simp; ring
  simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hsym, h1]
  simp only [Ω.prob_sum, mul_one]
  ring

/-- **Jensen for `1/ℰ`** (O&R p. 586): `E[1/ℰ] ≥ 1/E[ℰ]`, i.e. `E[ℰ]E[1/ℰ] ≥ 1`. -/
theorem one_le_expect_mul_expect_inv (Ω : FinProb S) {X : S → ℝ} (hX : ∀ s, 0 < X s) :
    1 ≤ Ω.expect X * Ω.expect (fun s => 1 / X s) := by
  have h := expect_mul_expect_inv Ω hX
  have : 0 ≤ ∑ i, ∑ j, Ω.prob i * Ω.prob j * (X i - X j) ^ 2 / (X i * X j) :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      div_nonneg (mul_nonneg (mul_nonneg (Ω.prob_nonneg i) (Ω.prob_nonneg j)) (sq_nonneg _))
        (mul_pos (hX i) (hX j)).le
  linarith

/-- A random variable is degenerate if it takes one value on the support (O&R p. 586,
"in general"). -/
def Degenerate (Ω : FinProb S) (X : S → ℝ) : Prop :=
  ∀ i j, 0 < Ω.prob i → 0 < Ω.prob j → X i = X j

/-- **Strict Jensen** (O&R p. 586): a nondegenerate positive exchange rate has
`E[1/ℰ] > 1/E[ℰ]`. -/
theorem one_lt_expect_mul_expect_inv (Ω : FinProb S) {X : S → ℝ} (hX : ∀ s, 0 < X s)
    (hnd : ¬ Degenerate Ω X) : 1 < Ω.expect X * Ω.expect (fun s => 1 / X s) := by
  simp only [Degenerate, not_forall] at hnd
  obtain ⟨i₀, j₀, hi, hj, hne⟩ := hnd
  have h := expect_mul_expect_inv Ω hX
  set g : S → S → ℝ := fun i j => Ω.prob i * Ω.prob j * (X i - X j) ^ 2 / (X i * X j)
  have hg : ∀ i j, 0 ≤ g i j := fun i j =>
    div_nonneg (mul_nonneg (mul_nonneg (Ω.prob_nonneg i) (Ω.prob_nonneg j)) (sq_nonneg _))
      (mul_pos (hX i) (hX j)).le
  have hsq : 0 < (X i₀ - X j₀) ^ 2 := by
    have : X i₀ - X j₀ ≠ 0 := sub_ne_zero.2 hne
    positivity
  have hpos : 0 < g i₀ j₀ := div_pos (mul_pos (mul_pos hi hj) hsq) (mul_pos (hX i₀) (hX j₀))
  have h1 : g i₀ j₀ ≤ ∑ j, g i₀ j :=
    Finset.single_le_sum (f := g i₀) (fun j _ => hg i₀ j) (Finset.mem_univ j₀)
  have h2 : ∑ j, g i₀ j ≤ ∑ i, ∑ j, g i j :=
    Finset.single_le_sum (f := fun i => ∑ j, g i j)
      (fun i _ => Finset.sum_nonneg fun j _ => hg i j) (Finset.mem_univ i₀)
  have : 0 < ∑ i, ∑ j, g i j := by linarith
  simp only [g] at this
  linarith

/-- The expectation of a degenerate variable is its common value (O&R p. 586). -/
theorem expect_of_degenerate (Ω : FinProb S) {X : S → ℝ} (hd : Degenerate Ω X) {s₀ : S}
    (hs₀ : 0 < Ω.prob s₀) : Ω.expect X = X s₀ := by
  have : ∀ s, Ω.prob s * X s = Ω.prob s * X s₀ := fun s => by
    rcases (Ω.prob_nonneg s).lt_or_eq with h | h
    · rw [hd s s₀ h hs₀]
    · rw [← h]; ring
  simp only [FinProb.expect, this, ← Finset.sum_mul, Ω.prob_sum, one_mul]

/-- **Siegel's paradox** (O&R (105), p. 586): the dollar version `F = E[ℰ]` and the yen
version `1/F = E[1/ℰ]` of the unbiasedness hypothesis hold simultaneously IFF the future
spot rate is degenerate. -/
theorem siegel_iff (Ω : FinProb S) {X : S → ℝ} (hX : ∀ s, 0 < X s) :
    (∃ F, F = Ω.expect X ∧ 1 / F = Ω.expect (fun s => 1 / X s)) ↔ Degenerate Ω X := by
  constructor
  · rintro ⟨F, hF1, hF2⟩
    by_contra hnd
    have h := one_lt_expect_mul_expect_inv Ω hX hnd
    have hFpos : 0 < F := hF1 ▸ Ω.expect_pos hX
    rw [← hF1, ← hF2, mul_one_div_cancel hFpos.ne'] at h
    exact lt_irrefl 1 h
  · intro hd
    obtain ⟨s₀, hs₀⟩ := Ω.exists_prob_pos
    refine ⟨X s₀, (expect_of_degenerate Ω hd hs₀).symm, ?_⟩
    have hd' : Degenerate Ω (fun s => 1 / X s) := fun i j hi hj => by
      simp only [hd i j hi hj]
    exact (expect_of_degenerate Ω hd' hs₀).symm

/-- The p. 587 number: a 10 percent standard deviation of the log exchange rate gives a
Jensen term `½ Var = 0.005` (O&R p. 587). -/
theorem jensen_term_number : (1 / 2 : ℝ) * (0.1 : ℝ) ^ 2 = (0.005 : ℝ) := by norm_num

namespace Gaussian

open MeasureTheory ProbabilityTheory

/-- **(106) for a Gaussian log exchange rate** (O&R (106), p. 587): if `e = log ℰ_{t+1}`
has the Gaussian law with mean `m` and variance `v` (Mathlib's `gaussianReal`), then
`E[ℰ] = exp(m + v/2)` and `E[1/ℰ] = exp(−m + v/2)`. -/
theorem expect_exp_gaussian {Ω' : Type*} {mΩ : MeasurableSpace Ω'} {P : Measure Ω'}
    {e : Ω' → ℝ} {m : ℝ} {v : NNReal} (he : HasLaw e (gaussianReal m v) P) :
    (∫ ω, Real.exp (e ω) ∂P) = Real.exp (m + v / 2) ∧
      (∫ ω, Real.exp (-e ω) ∂P) = Real.exp (-m + v / 2) := by
  have h1 := mgf_gaussianReal he 1
  have h2 := mgf_gaussianReal he (-1)
  simp only [mgf, one_mul, neg_one_mul] at h1 h2
  refine ⟨h1.trans (congrArg Real.exp (by ring)), h2.trans (congrArg Real.exp (by ring))⟩

/-- **The dollar and yen log forward rates under lognormality** (O&R (106), p. 587):
`F = E[ℰ]` gives `f = m + v/2`; the yen version `1/F* = E[1/ℰ]` gives `f* = m − v/2`; they
agree iff `v = 0`. -/
theorem log_forward_gaussian {Ω' : Type*} {mΩ : MeasurableSpace Ω'} {P : Measure Ω'}
    {e : Ω' → ℝ} {m : ℝ} {v : NNReal} (he : HasLaw e (gaussianReal m v) P) {F Fy : ℝ}
    (hF : F = ∫ ω, Real.exp (e ω) ∂P) (hFy : 1 / Fy = ∫ ω, Real.exp (-e ω) ∂P) :
    Real.log F = m + v / 2 ∧ Real.log Fy = m - v / 2 ∧ (Real.log F = Real.log Fy ↔ v = 0) := by
  obtain ⟨h1, h2⟩ := expect_exp_gaussian he
  have hlF : Real.log F = m + v / 2 := by rw [hF, h1, Real.log_exp]
  have hFy' : Fy = Real.exp (m - v / 2) := by
    rw [h2] at hFy
    have : Fy = 1 / Real.exp (-m + v / 2) := by
      rw [← hFy]; field_simp
    rw [this, one_div, ← Real.exp_neg]; congr 1; ring
  have hlFy : Real.log Fy = m - v / 2 := by rw [hFy', Real.log_exp]
  refine ⟨hlF, hlFy, ?_⟩
  rw [hlF, hlFy]
  constructor
  · intro h
    have : (v : ℝ) = 0 := by linarith
    exact_mod_cast this
  · intro h; rw [h]; simp

end Gaussian

/-! ## Real speculative profits (107)–(109) -/

/-- **(107) ⟺ (108) under relative PPP** (O&R (107)–(108), p. 587): with
`P_{t+1} = κ ℰ_{t+1} P*_{t+1}`, zero expected real dollar profits from a forward position is
equivalent to zero expected real yen profits. -/
theorem eq107_iff_eq108 (Ω : FinProb S) {F κ : ℝ} {E' P' Ps' : S → ℝ} (hF : 0 < F)
    (hκ : 0 < κ) (hE' : ∀ s, 0 < E' s) (hPs : ∀ s, 0 < Ps' s)
    (hppp : ∀ s, P' s = κ * E' s * Ps' s) :
    Ω.expect (fun s => (F - E' s) / P' s) = 0 ↔
      Ω.expect (fun s => (1 / F - 1 / E' s) / Ps' s) = 0 := by
  have e : (fun s => (F - E' s) / P' s) = fun s => -(F / κ) * ((1 / F - 1 / E' s) / Ps' s) := by
    funext s
    rw [hppp s]
    have := hE' s; have := hPs s
    field_simp; ring
  rw [e, Ω.expect_mul_left]
  have : -(F / κ) ≠ 0 := neg_ne_zero.2 (div_pos hF hκ).ne'
  constructor
  · intro h; exact (mul_eq_zero.1 h).resolve_left this
  · intro h; rw [h, mul_zero]

/-- **The forward rate from (107)** (O&R (107), p. 587; Exercise 6(f), p. 602):
`E[(F − ℰ)/P] = 0 ⟺ F = E[ℰ/P]/E[1/P]`. -/
theorem eq107_iff_ratio (Ω : FinProb S) {F : ℝ} {E' P' : S → ℝ} (hP' : ∀ s, 0 < P' s) :
    Ω.expect (fun s => (F - E' s) / P' s) = 0 ↔
      F = Ω.expect (fun s => E' s / P' s) / Ω.expect (fun s => 1 / P' s) := by
  have hpos : 0 < Ω.expect (fun s => 1 / P' s) := Ω.expect_pos fun s => one_div_pos.2 (hP' s)
  have e : (fun s => (F - E' s) / P' s) = fun s => F * (1 / P' s) - E' s / P' s := by
    funext s; ring
  rw [e, Ω.expect_sub, Ω.expect_mul_left, eq_div_iff hpos.ne']
  constructor <;> intro h <;> linarith

/-- **The exact finite-state analogue of (109)** (O&R (109), p. 588, without
lognormality): under (107), `F = E[ℰ] + Cov(ℰ, 1/P)/E[1/P]`, so the forward rate is
unbiased iff the future spot rate is uncorrelated with the purchasing power of money. -/
theorem forward_exact_decomposition (Ω : FinProb S) {F : ℝ} {E' P' : S → ℝ}
    (hP' : ∀ s, 0 < P' s) (h107 : Ω.expect (fun s => (F - E' s) / P' s) = 0) :
    F = Ω.expect E' + Ω.cov E' (fun s => 1 / P' s) / Ω.expect (fun s => 1 / P' s) := by
  have hpos : 0 < Ω.expect (fun s => 1 / P' s) := Ω.expect_pos fun s => one_div_pos.2 (hP' s)
  rw [(eq107_iff_ratio Ω hP').1 h107]
  have : Ω.expect (fun s => E' s / P' s) = Ω.expect (fun s => E' s * (1 / P' s)) := by
    congr 1; funext s; ring
  rw [this, Ω.expect_mul_eq]
  field_simp

/-- The lognormal moment identity `E[exp Z] = exp(E Z + ½ Var Z)` for a random variable
(O&R fn 41 of Ch. 5, used in fn 75, p. 588), stated as an explicit hypothesis. -/
def LognormalMGF (Ω : FinProb S) (Z : S → ℝ) : Prop :=
  Ω.expect (fun s => Real.exp (Z s)) = Real.exp (Ω.expect Z + Ω.var Z / 2)

/-- `Var(−X) = Var X` (O&R fn 75, p. 588). -/
theorem var_neg (Ω : FinProb S) (X : S → ℝ) : Ω.var (fun s => -X s) = Ω.var X := by
  have : (fun s => -X s) = fun s => (-1) * X s := funext fun s => by ring
  simp only [this, FinProb.var, FinProb.cov_mul_left, FinProb.cov_mul_right]; ring

/-- **(109)** (O&R (109) and fn 75, p. 588): if (107) holds and the lognormal moment
identity holds for `−p` and `e − p` (as under joint normality of the logs `e, p`), then
`f = E e + ½ Var e − Cov(e, p)`. -/
theorem eq109 (Ω : FinProb S) {F : ℝ} (hF : 0 < F) {e p : S → ℝ}
    (h107 : Ω.expect (fun s => (F - Real.exp (e s)) / Real.exp (p s)) = 0)
    (h1 : LognormalMGF Ω (fun s => -p s)) (h2 : LognormalMGF Ω (fun s => e s - p s)) :
    Real.log F = Ω.expect e + Ω.var e / 2 - Ω.cov e p := by
  have ex : (fun s => (F - Real.exp (e s)) / Real.exp (p s))
      = fun s => F * Real.exp (-p s) - Real.exp (e s - p s) := by
    funext s; rw [Real.exp_neg, Real.exp_sub]; field_simp
  rw [ex, Ω.expect_sub, Ω.expect_mul_left, h1, h2, sub_eq_zero] at h107
  have hl := congrArg Real.log h107
  rw [Real.log_mul hF.ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_exp] at hl
  rw [var_neg, Ω.var_sub, Ω.expect_sub] at hl
  have : Ω.expect (fun s => -p s) = -Ω.expect p := by
    rw [show (fun s => -p s) = fun s => (-1) * p s from funext fun s => by ring,
      Ω.expect_mul_left]; ring
  rw [this] at hl
  linarith

/-- **(106) as the nonstochastic-price case of (109)** (O&R fn 75, p. 588): with a constant
price level `p ≡ p̄`, `f = E e + ½ Var e`. -/
theorem eq106_of_constant_price (Ω : FinProb S) {F pbar : ℝ} (hF : 0 < F) {e : S → ℝ}
    (h107 : Ω.expect (fun s => (F - Real.exp (e s)) / Real.exp pbar) = 0)
    (h2 : LognormalMGF Ω (fun s => e s - pbar)) :
    Real.log F = Ω.expect e + Ω.var e / 2 := by
  have h1 : LognormalMGF Ω (fun _ => -pbar) := by
    simp only [LognormalMGF, FinProb.expect_const, FinProb.var, FinProb.cov_const_left]
    ring_nf
  have := eq109 Ω hF (p := fun _ => pbar) h107 h1 h2
  rw [this, Ω.cov_comm, Ω.cov_const_left, sub_zero]

/-! ## The forward rate in general equilibrium (116)–(119) -/

/-- **The real-return differential identity** (O&R p. 591): with CIP (104) and PPP (92),
`(1+i)P_t/P_{t+1} − (1+i*)P*_t/P*_{t+1} = ((1+i)P_t/F_t)(F_t − ℰ_{t+1})/P_{t+1}`. -/
theorem real_return_differential {i istar P Ps F E E' P' Ps' : ℝ} (hF : 0 < F)
    (hE : 0 < E) (hE' : 0 < E') (hPs' : 0 < Ps') (hcip : 1 + i = (1 + istar) * F / E)
    (hppp : P = E * Ps) (hppp' : P' = E' * Ps') :
    (1 + i) * P / P' - (1 + istar) * Ps / Ps' = (1 + i) * P / F * ((F - E') / P') := by
  have hi : 1 + istar = (1 + i) * E / F := by
    rw [hcip]; field_simp
  rw [hi, hppp, hppp']
  field_simp

/-- **(116) from (93)** (O&R (116), p. 591): if both assets satisfy the Euler equation (93),
the return differential has zero marginal-utility-weighted expectation. -/
theorem eq116_of_euler (Ω : FinProb S) {β uC : ℝ} {rn rm m : S → ℝ} (huC : 0 < uC)
    (hn : uC = β * Ω.expect (fun s => (1 + rn s) * m s))
    (hm : uC = β * Ω.expect (fun s => (1 + rm s) * m s)) :
    Ω.expect (fun s => (rn s - rm s) * (m s / uC)) = 0 := by
  have e : (fun s => (rn s - rm s) * (m s / uC))
      = fun s => 1 / uC * ((1 + rn s) * m s - (1 + rm s) * m s) := by
    funext s; field_simp; ring
  rw [e, Ω.expect_mul_left, Ω.expect_sub]
  have : Ω.expect (fun s => (1 + rn s) * m s) = Ω.expect (fun s => (1 + rm s) * m s) := by
    by_cases hβ : β = 0
    · rw [hβ, zero_mul] at hn; linarith
    · exact mul_left_cancel₀ hβ (hn.symm.trans hm)
  rw [this, sub_self, mul_zero]

/-- **(117) from (116)** (O&R (117), p. 591): substituting the real-return differential of
the two nominal bonds and factoring out the date-`t` term `(1+i)P_t/F_t`. -/
theorem eq117_of_eq116 (Ω : FinProb S) {i P F uC : ℝ} {E' P' m d : S → ℝ} (hi : 0 < 1 + i)
    (hP : 0 < P) (hF : 0 < F)
    (hd : ∀ s, d s = (1 + i) * P / F * ((F - E' s) / P' s))
    (h116 : Ω.expect (fun s => d s * (m s / uC)) = 0) :
    Ω.expect (fun s => (F - E' s) / P' s * (m s / uC)) = 0 := by
  have e : (fun s => d s * (m s / uC))
      = fun s => (1 + i) * P / F * ((F - E' s) / P' s * (m s / uC)) := by
    funext s; rw [hd s]; ring
  rw [e, Ω.expect_mul_left] at h116
  exact (mul_eq_zero.1 h116).resolve_left (by positivity)

/-- **The forward-position Euler equation is necessary and sufficient** (O&R (117),
p. 591: "a forward position, which requires no money down in period t, must yield zero
expected utility in equilibrium"): buying `δ` yen forward costs nothing and pays
`δ(ℰ_{t+1} − F)/P_{t+1}` in real terms. -/
theorem forward_euler_iff {u u' : ℝ → ℝ} (hc : ConcaveOn ℝ (Set.Ioi 0) u)
    (hd : ∀ x, 0 < x → HasDerivAt u (u' x) x) {Ω : FinProb S} {β C F : ℝ}
    {C' E' P' : S → ℝ} (hβ : 0 < β) (hC : 0 < C) (huC : 0 < u' C) (hC' : ∀ s, 0 < C' s) :
    IsLocalMax (assetValue u Ω β C 0 C' (fun s => (E' s - F) / P' s)) 0 ↔
      Ω.expect (fun s => (F - E' s) / P' s * (u' (C' s) / u' C)) = 0 := by
  rw [isLocalMax_assetValue_iff hc hd hβ.le hC hC', zero_mul]
  have e : (fun s => (F - E' s) / P' s * (u' (C' s) / u' C))
      = fun s => (-(1 / u' C)) * (u' (C' s) * ((E' s - F) / P' s)) := by
    funext s; field_simp; ring
  rw [e, Ω.expect_mul_left]
  constructor
  · intro h
    have : Ω.expect (fun s => u' (C' s) * ((E' s - F) / P' s)) = 0 := by
      rcases mul_eq_zero.1 h.symm with h1 | h1
      · linarith
      · exact h1
    rw [this, mul_zero]
  · intro h
    have hne : -(1 / u' C) ≠ 0 := neg_ne_zero.2 (one_div_pos.2 huC).ne'
    rw [(mul_eq_zero.1 h).resolve_left hne, mul_zero]

/-- **(118)**: with CRRA utility `u′(C) = C^{−ρ}`, `u′(C_{t+1})/u′(C_t) = (C_t/C_{t+1})^ρ`
(O&R (118), p. 591). -/
theorem crra_mrs {C C' ρ : ℝ} (hC : 0 < C) (hC' : 0 < C') :
    C' ^ (-ρ) / C ^ (-ρ) = (C / C') ^ ρ := by
  rw [Real.rpow_neg hC'.le, Real.rpow_neg hC.le, Real.div_rpow hC.le hC'.le]
  have := Real.rpow_pos_of_pos hC ρ; have := Real.rpow_pos_of_pos hC' ρ
  field_simp

/-- **The exact general-equilibrium forward rate** (O&R (117), p. 591, without
lognormality): with `m = u′(C_{t+1})/P_{t+1} > 0`, (117) holds iff
`F = E[ℰ m]/E[m] = E[ℰ] + Cov(ℰ, m)/E[m]`: the forward premium over the expected spot rate
is exactly the covariance risk premium. -/
theorem forward_rate_ge (Ω : FinProb S) {F uC : ℝ} {E' m : S → ℝ} (huC : 0 < uC)
    (hm : ∀ s, 0 < m s) :
    Ω.expect (fun s => (F - E' s) * (m s / uC)) = 0 ↔
      F = Ω.expect E' + Ω.cov E' m / Ω.expect m := by
  have hpos := Ω.expect_pos hm
  have e : (fun s => (F - E' s) * (m s / uC)) = fun s => 1 / uC * (F * m s - E' s * m s) := by
    funext s; field_simp
  rw [e, Ω.expect_mul_left, Ω.expect_sub, Ω.expect_mul_left, Ω.expect_mul_eq]
  have hu : 1 / uC ≠ 0 := (one_div_pos.2 huC).ne'
  constructor
  · intro h
    have := (mul_eq_zero.1 h).resolve_left hu
    field_simp
    linarith
  · intro h
    rw [h]
    field_simp
    ring

/-- **(119)** (O&R (119), p. 592, with the hint of fn 79): if (118) holds and the lognormal
moment identity holds for `−(p + ρc)` and `e − (p + ρc)` (logs of `ℰ_{t+1}, P_{t+1},
C_{t+1}`; `C_t = exp c₀` known at `t`), then
`f − E e = ½ Var e − Cov(e, p) − ρ Cov(e, c)`. -/
theorem eq119 (Ω : FinProb S) {F ρ c₀ : ℝ} (hF : 0 < F) {e p c : S → ℝ}
    (h118 : Ω.expect (fun s => (F - Real.exp (e s)) / Real.exp (p s)
      * (Real.exp c₀ / Real.exp (c s)) ^ ρ) = 0)
    (h1 : LognormalMGF Ω (fun s => -(p s + ρ * c s)))
    (h2 : LognormalMGF Ω (fun s => e s + -(p s + ρ * c s))) :
    Real.log F - Ω.expect e = Ω.var e / 2 - Ω.cov e p - ρ * Ω.cov e c := by
  set Z : S → ℝ := fun s => -(p s + ρ * c s)
  have ex : (fun s => (F - Real.exp (e s)) / Real.exp (p s)
      * (Real.exp c₀ / Real.exp (c s)) ^ ρ)
      = fun s => Real.exp (ρ * c₀) * (F * Real.exp (Z s) - Real.exp (e s + Z s)) := by
    funext s
    rw [← Real.exp_sub, ← Real.exp_mul]
    simp only [Z, Real.exp_add, Real.exp_neg]
    rw [show (c₀ - c s) * ρ = ρ * c₀ + -(ρ * c s) by ring, Real.exp_add, Real.exp_neg]
    field_simp
  rw [ex, Ω.expect_mul_left, Ω.expect_sub, Ω.expect_mul_left] at h118
  have h3 := (mul_eq_zero.1 h118).resolve_left (Real.exp_pos _).ne'
  rw [h1, h2, sub_eq_zero] at h3
  have hl := congrArg Real.log h3
  rw [Real.log_mul hF.ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_exp, Ω.expect_add,
    Ω.var_add] at hl
  have hcov : Ω.cov e Z = -(Ω.cov e p + ρ * Ω.cov e c) := by
    have : Z = fun s => (-1) * (p s + ρ * c s) := funext fun s => by simp [Z]
    rw [this, Ω.cov_mul_right, Ω.cov_add_right, Ω.cov_mul_right]; ring
  rw [hcov] at hl
  linarith

/-- With `ρ = 0` (risk-neutral investors who care about real returns) (119) reduces to
(109) (O&R p. 592). -/
theorem eq119_rho_zero (Ω : FinProb S) {F c₀ : ℝ} (hF : 0 < F) {e p c : S → ℝ}
    (h118 : Ω.expect (fun s => (F - Real.exp (e s)) / Real.exp (p s)
      * (Real.exp c₀ / Real.exp (c s)) ^ (0 : ℝ)) = 0)
    (h1 : LognormalMGF Ω (fun s => -(p s + 0 * c s)))
    (h2 : LognormalMGF Ω (fun s => e s + -(p s + 0 * c s))) :
    Real.log F = Ω.expect e + Ω.var e / 2 - Ω.cov e p := by
  have := eq119 Ω hF h118 h1 h2
  linarith

/-- **The world-output form of (119)** (O&R p. 592): with `C = xY^W`, `c = log x + y^W`, so
`Cov(e, c) = Cov(e, y^W)`. -/
theorem cov_consumption_eq_output (Ω : FinProb S) {e y : S → ℝ} (logx : ℝ) :
    Ω.cov e (fun s => logx + y s) = Ω.cov e y :=
  Ω.cov_add_const_right logx e y

/-! ## The Fama decomposition (110)–(115) -/

/-- The joint distribution of today's state (law `π`) and tomorrow's state (kernel `K`):
the two-date event tree behind the regression (110) (O&R p. 588). -/
def pairProb (π : FinProb S) (K : Kernel S) : FinProb (S × S) :=
  ⟨fun q => π.prob q.1 * K.trans q.1 q.2,
    fun q => mul_nonneg (π.prob_nonneg _) (K.trans_nonneg _ _), by
      rw [Fintype.sum_prod_type]
      simp only [← Finset.mul_sum, K.trans_sum, mul_one, π.prob_sum]⟩

/-- The rational-expectations forecast `E_t Y_{t+1}` (O&R p. 590). -/
def condE (K : Kernel S) (Y : S → S → ℝ) (s : S) : ℝ := ∑ s', K.trans s s' * Y s s'

/-- **Rational expectations: forecast errors are orthogonal to date-`t` information**
(O&R p. 590, "must be uncorrelated with all variables observable on date t"), derived from
the tower property. -/
theorem forecast_error_orthogonal (π : FinProb S) (K : Kernel S) (g : S → ℝ)
    (Y : S → S → ℝ) :
    (pairProb π K).expect (fun q => g q.1 * (Y q.1 q.2 - condE K Y q.1)) = 0 := by
  simp only [FinProb.expect, pairProb, Fintype.sum_prod_type]
  refine Finset.sum_eq_zero fun s _ => ?_
  have e : ∑ s', π.prob s * K.trans s s' * (g s * (Y s s' - condE K Y s))
      = π.prob s * g s * (∑ s', K.trans s s' * Y s s' - condE K Y s * ∑ s', K.trans s s') := by
    rw [mul_sub, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun s' _ => by ring
  rw [e, K.trans_sum, mul_one]
  simp [condE]

namespace Fama

variable (π : FinProb S) (K : Kernel S) (f e : S → ℝ) (e' : S → S → ℝ)

/-- The forward premium `f_t − e_t` (O&R (110), p. 588). -/
def fwdPrem : S × S → ℝ := fun q => f q.1 - e q.1

/-- Expected depreciation `D_t = E_t e_{t+1} − e_t` (O&R (112), p. 590). -/
def expDep : S × S → ℝ := fun q => condE K e' q.1 - e q.1

/-- The risk premium `rp_t = f_t − E_t e_{t+1}` (O&R p. 590). -/
def riskPrem : S × S → ℝ := fun q => f q.1 - condE K e' q.1

/-- Realised depreciation `e_{t+1} − e_t` (O&R (110), p. 588). -/
def realDep : S × S → ℝ := fun q => e' q.1 q.2 - e q.1

/-- **(112)**: `f_t − e_t = (E_t e_{t+1} − e_t) + rp_t` (O&R (112), p. 590). -/
theorem fwdPrem_eq : fwdPrem f e = fun q => expDep K e e' q + riskPrem K f e' q := by
  funext q; simp only [fwdPrem, expDep, riskPrem]; ring

/-- **(113)**: `Cov(f − e, e_{t+1} − e_t) = Cov(f − e, E_t e_{t+1} − e_t)`, because the
forecast error is orthogonal to the forward premium (O&R (113), p. 590). -/
theorem cov_fwdPrem_realDep :
    (pairProb π K).cov (fwdPrem f e) (realDep e e')
      = (pairProb π K).cov (fwdPrem f e) (expDep K e e') := by
  have hsplit : realDep e e' = fun q => expDep K e e' q + (e' q.1 q.2 - condE K e' q.1) := by
    funext q; simp only [realDep, expDep]; ring
  rw [hsplit, FinProb.cov_add_right]
  have h1 := forecast_error_orthogonal π K (fun s => f s - e s) e'
  have h2 := forecast_error_orthogonal π K (fun _ => 1) e'
  simp only [one_mul] at h2
  have h0 : (pairProb π K).cov (fwdPrem f e) (fun q => e' q.1 q.2 - condE K e' q.1) = 0 := by
    simp only [FinProb.cov, fwdPrem]
    rw [h1, h2, mul_zero, sub_zero]
  rw [h0, add_zero]

/-- **The population slope of (110)** (O&R (111), (113)–(114), p. 590):
`a₁ = [Var D + Cov(D, rp)]/[Var D + 2Cov(D, rp) + Var rp]` (the book's `plim` of the OLS
estimator is this population coefficient). -/
theorem fama_slope :
    (pairProb π K).cov (fwdPrem f e) (realDep e e') / (pairProb π K).var (fwdPrem f e)
      = ((pairProb π K).var (expDep K e e') + (pairProb π K).cov (expDep K e e')
          (riskPrem K f e'))
        / ((pairProb π K).var (expDep K e e') + 2 * (pairProb π K).cov (expDep K e e')
          (riskPrem K f e') + (pairProb π K).var (riskPrem K f e')) := by
  rw [cov_fwdPrem_realDep, fwdPrem_eq, FinProb.var_add, FinProb.cov_add_left,
    (pairProb π K).cov_comm (riskPrem K f e') (expDep K e e')]
  simp only [FinProb.var]
  ring_nf

/-- **Fama's first result** (O&R p. 590): a negative slope `a₁ < 0` forces
`Cov(D, rp) < −Var D ≤ 0`: the risk premium covaries negatively with expected
depreciation. -/
theorem fama_negative_slope (hvar : 0 < (pairProb π K).var (fwdPrem f e))
    (ha : (pairProb π K).cov (fwdPrem f e) (realDep e e')
      / (pairProb π K).var (fwdPrem f e) < 0) :
    (pairProb π K).cov (expDep K e e') (riskPrem K f e') < -(pairProb π K).var (expDep K e e')
      ∧ (pairProb π K).cov (expDep K e e') (riskPrem K f e') < 0 := by
  have hnum : (pairProb π K).cov (fwdPrem f e) (realDep e e') < 0 := by
    by_contra h
    push Not at h
    have := div_nonneg h hvar.le
    linarith
  rw [cov_fwdPrem_realDep, fwdPrem_eq, FinProb.cov_add_left,
    (pairProb π K).cov_comm (riskPrem K f e') (expDep K e e')] at hnum
  have hv := (pairProb π K).var_nonneg (expDep K e e')
  simp only [FinProb.var] at hv ⊢
  constructor <;> linarith

/-- **Fama's second result (115)** (O&R (114)–(115), p. 590): a slope `a₁ < ½` forces
`Var rp > Var D`: the risk premium is more variable than expected depreciation. -/
theorem fama_half_slope (hvar : 0 < (pairProb π K).var (fwdPrem f e))
    (ha : (pairProb π K).cov (fwdPrem f e) (realDep e e')
      / (pairProb π K).var (fwdPrem f e) < 1 / 2) :
    (pairProb π K).var (expDep K e e') < (pairProb π K).var (riskPrem K f e') := by
  rw [div_lt_iff₀ hvar] at ha
  rw [cov_fwdPrem_realDep, fwdPrem_eq, FinProb.cov_add_left,
    (pairProb π K).cov_comm (riskPrem K f e') (expDep K e e'), FinProb.var_add] at ha
  simp only [FinProb.var] at ha ⊢
  linarith

/-- Under the unbiasedness null `f_t = E_t e_{t+1}` (no risk premium) the population slope is
exactly `1` (O&R (110), p. 588: the null `a₁ = 1`). -/
theorem fama_slope_null (hnull : ∀ s, f s = condE K e' s)
    (hvar : 0 < (pairProb π K).var (expDep K e e')) :
    (pairProb π K).cov (fwdPrem f e) (realDep e e') / (pairProb π K).var (fwdPrem f e) = 1 := by
  have hrp : riskPrem K f e' = fun _ => 0 := by
    funext q; simp only [riskPrem, hnull, sub_self]
  rw [fama_slope, hrp]
  have h0 : (pairProb π K).var (fun _ : S × S => (0 : ℝ)) = 0 := by
    simp only [FinProb.var, FinProb.cov_const_left]
  have h1 : (pairProb π K).cov (expDep K e e') (fun _ => (0 : ℝ)) = 0 := by
    rw [FinProb.cov_comm, FinProb.cov_const_left]
  rw [h0, h1]
  field_simp
  ring

end Fama

/-- `E[Z²] = Var Z + (E Z)²` (O&R (111), p. 589). -/
theorem expect_sq_eq {T : Type} [Fintype T] (Ω : FinProb T) (Z : T → ℝ) :
    Ω.expect (fun t => Z t ^ 2) = Ω.var Z + Ω.expect Z ^ 2 := by
  simp only [FinProb.var, FinProb.cov, sq]; ring

/-- **The population OLS coefficients minimise mean squared error** (O&R (111), p. 589:
the probability limit of OLS is the population projection `a₁ = Cov(x, y)/Var(x)`,
`a₀ = E y − a₁ E x`). -/
theorem ols_minimises {T : Type} [Fintype T] (Ω : FinProb T) {X Y : T → ℝ}
    (hX : 0 < Ω.var X) (a₀ a₁ : ℝ) :
    Ω.expect (fun t => (Y t - (Ω.expect Y - Ω.cov X Y / Ω.var X * Ω.expect X)
        - Ω.cov X Y / Ω.var X * X t) ^ 2)
      ≤ Ω.expect (fun t => (Y t - a₀ - a₁ * X t) ^ 2) := by
  have hvar : ∀ b c : ℝ, Ω.var (fun t => Y t - b - c * X t)
      = Ω.var Y - 2 * c * Ω.cov X Y + c ^ 2 * Ω.var X := fun b c => by
    have e : (fun t => Y t - b - c * X t) = fun t => -b + (Y t + (-c) * X t) :=
      funext fun t => by ring
    rw [e, FinProb.var_const_add, FinProb.var_add]
    simp only [FinProb.var, FinProb.cov_mul_left, FinProb.cov_mul_right,
      Ω.cov_comm Y X]
    ring
  have hmean : ∀ b c : ℝ, Ω.expect (fun t => Y t - b - c * X t)
      = Ω.expect Y - b - c * Ω.expect X := fun b c => by
    rw [Ω.expect_sub, Ω.expect_sub, Ω.expect_const, Ω.expect_mul_left]
  rw [expect_sq_eq, expect_sq_eq, hvar, hvar, hmean, hmean]
  set a := Ω.cov X Y / Ω.var X
  have ha : Ω.cov X Y = a * Ω.var X := by simp only [a]; field_simp
  rw [ha]
  have : 0 ≤ Ω.var X * (a₁ - a) ^ 2 := mul_nonneg hX.le (sq_nonneg _)
  nlinarith [sq_nonneg (Ω.expect Y - a₀ - a₁ * Ω.expect X)]

/-! ## Exercise 6 (a): the consumption-based money price level -/

namespace Engel

variable {ι : Type} [Fintype ι]

/-- Money expenditure `Σ p_j C_j` (O&R Exercise 6, p. 601). -/
def expenditure (p c : ι → ℝ) : ℝ := ∑ j, p j * c j

/-- Bundles of positive goods reaching at least one unit of the index `Ω`, valued at
prices `p`; the money price level `P` is the least element (O&R Exercise 6, p. 601:
"the minimal expenditure of domestic money allowing `Ω = 1`"). -/
def costSet (Ω : (ι → ℝ) → ℝ) (p : ι → ℝ) : Set ℝ :=
  {e | ∃ c, (∀ j, 0 < c j) ∧ 1 ≤ Ω c ∧ e = expenditure p c}

/-- Scaling a bundle scales its cost (O&R Exercise 6). -/
theorem expenditure_smul (p c : ι → ℝ) (t : ℝ) :
    expenditure p (t • c) = t * expenditure p c := by
  simp only [expenditure, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- Positive bundles at positive prices cost something (O&R Exercise 6). -/
theorem expenditure_pos [Nonempty ι] {p c : ι → ℝ} (hp : ∀ j, 0 < p j) (hc : ∀ j, 0 < c j) :
    0 < expenditure p c :=
  Finset.sum_pos (fun j _ => mul_pos (hp j) (hc j)) Finset.univ_nonempty

/-- **The budget binds at an optimum** when `Ω` is homogeneous of degree one
(O&R Exercise 6(a), p. 601). -/
theorem budget_binds [Nonempty ι] {Ω : (ι → ℝ) → ℝ} {p c : ι → ℝ} {X : ℝ}
    (hp : ∀ j, 0 < p j) (hc : ∀ j, 0 < c j) (hhom : ∀ t : ℝ, 0 < t → ∀ c, Ω (t • c) = t * Ω c)
    (hΩc : 0 < Ω c) (hfeas : expenditure p c ≤ X)
    (hopt : ∀ c', (∀ j, 0 < c' j) → expenditure p c' ≤ X → Ω c' ≤ Ω c) :
    expenditure p c = X := by
  by_contra hne
  have hlt : expenditure p c < X := lt_of_le_of_ne hfeas hne
  have he := expenditure_pos hp hc
  set t := X / expenditure p c
  have ht : 1 < t := (one_lt_div he).2 hlt
  have hfe : expenditure p (t • c) ≤ X := by
    rw [expenditure_smul]; simp only [t]; field_simp; exact le_rfl
  have := hopt (t • c) (fun j => by simp only [Pi.smul_apply, smul_eq_mul]; nlinarith [hc j])
    hfe
  rw [hhom t (by linarith)] at this
  nlinarith

/-- **The money price level is expenditure per unit of the index**: `P = X/Ω(c*)`
(O&R Exercise 6(a), p. 601). -/
theorem price_level_eq [Nonempty ι] {Ω : (ι → ℝ) → ℝ} {p c : ι → ℝ} {X P : ℝ}
    (hp : ∀ j, 0 < p j) (hc : ∀ j, 0 < c j) (hhom : ∀ t : ℝ, 0 < t → ∀ c, Ω (t • c) = t * Ω c)
    (hΩc : 0 < Ω c) (hfeas : expenditure p c ≤ X)
    (hopt : ∀ c', (∀ j, 0 < c' j) → expenditure p c' ≤ X → Ω c' ≤ Ω c)
    (hP : IsLeast (costSet Ω p) P) : P = X / Ω c := by
  have hb := budget_binds hp hc hhom hΩc hfeas hopt
  apply le_antisymm
  · apply hP.2
    refine ⟨(1 / Ω c) • c, fun j => ?_, ?_, ?_⟩
    · simp only [Pi.smul_apply, smul_eq_mul]; exact mul_pos (one_div_pos.2 hΩc) (hc j)
    · rw [hhom _ (one_div_pos.2 hΩc)]; field_simp; exact le_rfl
    · rw [expenditure_smul, hb]; ring
  · obtain ⟨c', hc', h1, hPe⟩ := hP.1
    have he := expenditure_pos hp hc'
    set t := X / expenditure p c'
    have hX : 0 < X := hb ▸ expenditure_pos hp hc
    have htpos : 0 < t := div_pos hX he
    have hfe : expenditure p (t • c') ≤ X := by
      rw [expenditure_smul]; simp only [t]; field_simp; exact le_rfl
    have hle := hopt (t • c') (fun j => by
      simp only [Pi.smul_apply, smul_eq_mul]; exact mul_pos htpos (hc' j)) hfe
    rw [hhom t htpos] at hle
    have : t ≤ Ω c := by nlinarith
    rw [hPe, div_le_iff₀ hΩc]
    simp only [t] at this
    rwa [div_le_iff₀ he, mul_comm] at this

/-- Homogeneity of the minimal-expenditure price level in prices (O&R Exercise 6(f),
p. 602): if `P` is the least cost at prices `q`, then `t P` is the least cost at `t q`. -/
theorem least_cost_smul {Ω : (ι → ℝ) → ℝ} {q : ι → ℝ} {P t : ℝ} (ht : 0 < t)
    (hP : IsLeast (costSet Ω q) P) : IsLeast (costSet Ω (t • q)) (t * P) := by
  have hexp : ∀ c, expenditure (t • q) c = t * expenditure q c := fun c => by
    simp only [expenditure, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  constructor
  · obtain ⟨c, hc, h1, he⟩ := hP.1
    exact ⟨c, hc, h1, by rw [hexp, he]⟩
  · rintro e ⟨c, hc, h1, he⟩
    rw [he, hexp]
    exact mul_le_mul_of_nonneg_left (hP.2 ⟨c, hc, h1, rfl⟩) ht.le

/-- **The price level scales with money** (O&R Exercise 6(f), p. 602): if goods prices are
`M • q` then the minimal-expenditure price level is `M` times the one at prices `q`. -/
theorem price_level_scales {Ω : (ι → ℝ) → ℝ} {q : ι → ℝ} {M P φ : ℝ} (hM : 0 < M)
    (hP : IsLeast (costSet Ω (M • q)) P) (hφ : IsLeast (costSet Ω q) φ) : P = M * φ :=
  hP.unique (least_cost_smul hM hφ)

variable [DecidableEq ι]

/-- **Euler's theorem for a homogeneous index**: `Ω′(c)·c = Ω(c)` (O&R Exercise 6(a),
p. 601). -/
theorem euler_homogeneous {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] {Ω : V → ℝ}
    {Ω' : V →L[ℝ] ℝ} {c : V} (hhom : ∀ t : ℝ, 0 < t → ∀ c, Ω (t • c) = t * Ω c)
    (hd : HasFDerivAt Ω Ω' c) :
    Ω' c = Ω c := by
  have hf : HasDerivAt (fun t : ℝ => t • c) c 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).smul_const c
  have hd1 : HasFDerivAt Ω Ω' ((fun t : ℝ => t • c) 1) := by simpa using hd
  have h1 : HasDerivAt (fun t : ℝ => Ω (t • c)) (Ω' c) 1 := hd1.comp_hasDerivAt 1 hf
  have h2 : HasDerivAt (fun t : ℝ => t * Ω c) (Ω c) 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).mul_const (Ω c)
  have heq : (fun t : ℝ => Ω (t • c)) =ᶠ[𝓝 1] fun t => t * Ω c := by
    filter_upwards [lt_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with t ht
    exact hhom t ht c
  exact h1.unique (h2.congr_of_eventuallyEq heq)

/-- **Exercise 6(a)** (O&R p. 601): at an interior optimum of a homogeneous-of-degree-one
index `Ω` under a money budget, `∂Ω/∂C_j = p_j/P` for every good, where `P` is the minimal
money expenditure giving `Ω = 1`. -/
theorem marginal_index_eq_relative_price [Nonempty ι] {Ω : (ι → ℝ) → ℝ}
    {Ω' : (ι → ℝ) →L[ℝ] ℝ} {p c : ι → ℝ} {X P : ℝ} (hp : ∀ j, 0 < p j) (hc : ∀ j, 0 < c j)
    (hhom : ∀ t : ℝ, 0 < t → ∀ c, Ω (t • c) = t * Ω c) (hΩc : 0 < Ω c)
    (hfeas : expenditure p c ≤ X)
    (hopt : ∀ c', (∀ j, 0 < c' j) → expenditure p c' ≤ X → Ω c' ≤ Ω c)
    (hd : HasFDerivAt Ω Ω' c) (hP : IsLeast (costSet Ω p) P) (j : ι) :
    Ω' (Pi.single j 1) = p j / P := by
  have hb := budget_binds hp hc hhom hΩc hfeas hopt
  have hPeq := price_level_eq hp hc hhom hΩc hfeas hopt hP
  have hX : 0 < X := hb ▸ expenditure_pos hp hc
  -- Step 1: equal marginal utility per dollar across goods.
  have hratio : ∀ k l, Ω' (Pi.single k 1) / p k = Ω' (Pi.single l 1) / p l := by
    intro k l
    set d : ι → ℝ := (1 / p k) • Pi.single k 1 - (1 / p l) • Pi.single l 1
    have hed : expenditure p d = 0 := by
      simp only [d, expenditure, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply,
        mul_sub, Finset.sum_sub_distrib]
      simp [mul_inv_cancel₀ (hp k).ne', mul_inv_cancel₀ (hp l).ne']
    have hf : HasDerivAt (fun t : ℝ => c + t • d) d 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const d).const_add c
    have hd0 : HasFDerivAt Ω Ω' ((fun t : ℝ => c + t • d) 0) := by simpa using hd
    have hg := hd0.comp_hasDerivAt 0 hf
    have hmax : IsLocalMax (Ω ∘ fun t : ℝ => c + t • d) 0 := by
      have hev : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ i, 0 < c i + t * d i := by
        refine Filter.eventually_all.2 fun i => ?_
        have hcont : Continuous fun t : ℝ => c i + t * d i := by fun_prop
        exact continuousAt_const.eventually_lt hcont.continuousAt (by simpa using hc i)
      filter_upwards [hev] with t ht
      simp only [Function.comp, zero_smul, add_zero]
      apply hopt
      · intro i; simpa using ht i
      · have : expenditure p (c + t • d) = expenditure p c + t * expenditure p d := by
          simp only [expenditure, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add,
            Finset.sum_add_distrib, Finset.mul_sum]
          congr 1
          exact Finset.sum_congr rfl fun i _ => by ring
        rw [this, hed, mul_zero, add_zero]; exact hfeas
    have h0 := hmax.hasDerivAt_eq_zero hg
    simp only [d, map_sub, map_smul, smul_eq_mul] at h0
    have := hp k; have := hp l
    field_simp at h0 ⊢
    linarith
  -- Step 2: Euler's theorem and the budget.
  obtain ⟨j₀⟩ := (inferInstance : Nonempty ι)
  set lam := Ω' (Pi.single j₀ 1) / p j₀
  have hlam : ∀ k, Ω' (Pi.single k 1) = lam * p k := fun k => by
    rw [show lam = Ω' (Pi.single k 1) / p k from (hratio k j₀).symm,
      div_mul_cancel₀ _ (hp k).ne']
  have heul := euler_homogeneous hhom hd
  have hsum : Ω' c = lam * expenditure p c := by
    conv_lhs => rw [← Finset.univ_sum_single c]
    rw [map_sum]
    simp only [expenditure, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show Pi.single k (c k) = c k • Pi.single k (1 : ℝ) by
      ext i; simp [Pi.single_apply], map_smul, smul_eq_mul, hlam k]
    ring
  rw [heul, hb] at hsum
  rw [hlam j, hPeq]
  have : lam = Ω c / X := by field_simp; linarith
  rw [this]
  field_simp

end Engel

/-! ## Exercise 6 (b)–(d): multi-good forward Euler equations -/

/-- **Exercise 6(d) ⟺ 6(b)** (O&R Exercise 6, p. 601): given 6(a) at both dates
(`u_j = u′ ∂C/∂C_j = u′ p_j/P`), the forward-position Euler equation priced in any single
good `j` is equivalent to the one priced in the consumption-based price level. -/
theorem ex6d_iff_ex6b (Ω : FinProb S) {F uC pj P : ℝ} {E' uC' pj' P' : S → ℝ} (huC : 0 < uC)
    (hpj : 0 < pj) (hP : 0 < P) (hpj' : ∀ s, 0 < pj' s) (hP' : ∀ s, 0 < P' s) :
    Ω.expect (fun s => (F - E' s) / pj' s * ((uC' s * (pj' s / P' s)) / (uC * (pj / P)))) = 0
      ↔ Ω.expect (fun s => (F - E' s) / P' s * (uC' s / uC)) = 0 := by
  have e : (fun s => (F - E' s) / pj' s * ((uC' s * (pj' s / P' s)) / (uC * (pj / P))))
      = fun s => P / pj * ((F - E' s) / P' s * (uC' s / uC)) := by
    funext s
    have := hpj' s; have := hP' s
    field_simp
  rw [e, Ω.expect_mul_left]
  have : P / pj ≠ 0 := (div_pos hP hpj).ne'
  constructor
  · intro h; exact (mul_eq_zero.1 h).resolve_left this
  · intro h; rw [h, mul_zero]

/-- **Exercise 6(c)** (O&R p. 601): under PPP `P_{t+1} = ℰ_{t+1} P*_{t+1}`, the dollar
forward Euler equation is equivalent to the yen one,
`E_t[((1/F) − (1/ℰ_{t+1}))/P*_{t+1} · u′(C_{t+1})/u′(C_t)] = 0`. -/
theorem ex6c_iff (Ω : FinProb S) {F : ℝ} {E' P' Ps' w : S → ℝ} (hF : 0 < F)
    (hE' : ∀ s, 0 < E' s) (hPs : ∀ s, 0 < Ps' s) (hppp : ∀ s, P' s = E' s * Ps' s) :
    Ω.expect (fun s => (F - E' s) / P' s * w s) = 0 ↔
      Ω.expect (fun s => (1 / F - 1 / E' s) / Ps' s * w s) = 0 := by
  have e : (fun s => (F - E' s) / P' s * w s)
      = fun s => (-F) * ((1 / F - 1 / E' s) / Ps' s * w s) := by
    funext s
    rw [hppp s]
    have := hE' s; have := hPs s
    field_simp; ring
  rw [e, Ω.expect_mul_left]
  have : -F ≠ 0 := neg_ne_zero.2 hF.ne'
  constructor
  · intro h; exact (mul_eq_zero.1 h).resolve_left this
  · intro h; rw [h, mul_zero]

/-- **No Siegel paradox in real terms** (O&R Exercise 6(c), p. 601; p. 587–588): with
risk-neutral consumers (`u″ = 0`, so `u′(C_{t+1})/u′(C_t) ≡ 1`), the dollar condition (107)
and the yen condition (108) hold TOGETHER, and there is always a forward rate satisfying both,
`F = E[ℰ/P]/E[1/P]`, however random the exchange rate is. -/
theorem no_real_siegel (Ω : FinProb S) {E' P' Ps' : S → ℝ} (hE' : ∀ s, 0 < E' s)
    (hPs : ∀ s, 0 < Ps' s) (hppp : ∀ s, P' s = E' s * Ps' s) :
    ∃ F, 0 < F ∧ Ω.expect (fun s => (F - E' s) / P' s) = 0 ∧
      Ω.expect (fun s => (1 / F - 1 / E' s) / Ps' s) = 0 := by
  have hP' : ∀ s, 0 < P' s := fun s => by rw [hppp s]; exact mul_pos (hE' s) (hPs s)
  set F := Ω.expect (fun s => E' s / P' s) / Ω.expect (fun s => 1 / P' s)
  have hF : 0 < F := div_pos (Ω.expect_pos fun s => div_pos (hE' s) (hP' s))
    (Ω.expect_pos fun s => one_div_pos.2 (hP' s))
  have h107 : Ω.expect (fun s => (F - E' s) / P' s) = 0 := (eq107_iff_ratio Ω hP').2 rfl
  refine ⟨F, hF, h107, ?_⟩
  have := (ex6c_iff Ω (w := fun _ => 1) hF hE' hPs hppp).1 (by simpa using h107)
  simpa using this

/-! ## Exercise 6 (e)–(f): two-good cash-in-advance model -/

/-- **Cobb–Douglas spending shares** (O&R Exercise 6(e), p. 602): maximising
`γ log C_X + (1−γ) log C_Y` (the log of `C_X^γ C_Y^{1−γ}`) subject to
`p_X C_X + p_Y C_Y = Z` gives `p_X C_X = γ Z`, uniquely. -/
theorem cobb_douglas_share {γ pX pY Z cX : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hpX : 0 < pX)
    (hpY : 0 < pY) (hZ : 0 < Z) (hcX : 0 < cX) (hcX' : pX * cX < Z) :
    γ * Real.log cX + (1 - γ) * Real.log ((Z - pX * cX) / pY)
        ≤ γ * Real.log (γ * Z / pX) + (1 - γ) * Real.log ((1 - γ) * Z / pY) ∧
      (γ * Real.log cX + (1 - γ) * Real.log ((Z - pX * cX) / pY)
          = γ * Real.log (γ * Z / pX) + (1 - γ) * Real.log ((1 - γ) * Z / pY)
        ↔ cX = γ * Z / pX) := by
  have hs : 0 < γ * Z / pX := by positivity
  have hr : 0 < Z - pX * cX := by linarith
  have h1γ : 0 < 1 - γ := by linarith
  have hr' : 0 < (1 - γ) * Z := by positivity
  set a := cX / (γ * Z / pX)
  set b := (Z - pX * cX) / ((1 - γ) * Z)
  have ha : 0 < a := div_pos hcX hs
  have hb : 0 < b := div_pos hr hr'
  have hsum : γ * (a - 1) + (1 - γ) * (b - 1) = 0 := by
    simp only [a, b]; field_simp; ring
  have hla : Real.log cX = Real.log a + Real.log (γ * Z / pX) := by
    rw [← Real.log_mul ha.ne' hs.ne']; congr 1; simp only [a]; field_simp
  have hlb : Real.log ((Z - pX * cX) / pY) = Real.log b + Real.log ((1 - γ) * Z / pY) := by
    rw [← Real.log_mul hb.ne' (by positivity)]; congr 1; simp only [b]; field_simp
  rw [hla, hlb]
  have ta := Real.log_le_sub_one_of_pos ha
  have tb := Real.log_le_sub_one_of_pos hb
  constructor
  · nlinarith
  · constructor
    · intro h
      have h0 : γ * (Real.log a - (a - 1)) + (1 - γ) * (Real.log b - (b - 1)) = 0 := by
        linarith
      have hA : Real.log a - (a - 1) = 0 := by nlinarith
      have ha1 : a = 1 := by
        by_contra hne
        have := Real.log_lt_sub_one_of_pos ha hne
        linarith
      simp only [a] at ha1
      field_simp at ha1
      rw [← ha1]; field_simp
    · intro h
      have ha1 : a = 1 := by simp only [a, h]; field_simp
      have hb1 : b = 1 := by
        rw [ha1, sub_self, mul_zero, zero_add] at hsum
        rcases mul_eq_zero.1 hsum with h0 | h0
        · linarith
        · linarith
      rw [ha1, hb1, Real.log_one]
      ring

/-- **The two-good CIA spot rate** (O&R Exercise 6(e), p. 602): with pooled consumption
`(X/2, Y/2)` per country, Cobb–Douglas spending shares, cash-in-advance `p_X X = M`,
`p*_Y Y = M*`, and the law of one price `p_Y = ℰ p*_Y`, `ℰ = ((1−γ)/γ) M/M*`. -/
theorem ex6e_spot_rate {γ pX pY psY X Y Z M Ms E : ℝ} (hγ0 : 0 < γ)
    (hX : 0 < X) (hY : 0 < Y) (hZ : 0 < Z) (hpsY : 0 < psY)
    (hshareX : pX * (X / 2) = γ * Z) (hshareY : pY * (Y / 2) = (1 - γ) * Z)
    (hcia : M = pX * X) (hcias : Ms = psY * Y) (hloop : pY = E * psY) :
    E = (1 - γ) / γ * (M / Ms) := by
  have hpX : pX = 2 * γ * Z / X := by field_simp; linarith
  have hpY : pY = 2 * (1 - γ) * Z / Y := by field_simp; linarith
  have hE : E = pY / psY := by rw [hloop]; field_simp
  rw [hE, hpY, hcia, hcias, hpX]
  field_simp

/-- **The Cobb–Douglas marginal utility of good X** (O&R Exercise 6(e)): for
`C = C_X^γ C_Y^{1−γ}`, `∂C/∂C_X = γ C/C_X`. -/
theorem cobb_douglas_partial {γ cX cY : ℝ} (hcX : 0 < cX) :
    HasDerivAt (fun z => z ^ γ * cY ^ (1 - γ)) (γ * (cX ^ γ * cY ^ (1 - γ)) / cX) cX := by
  have h := (Real.hasDerivAt_rpow_const (p := γ) (Or.inl hcX.ne')).mul_const (cY ^ (1 - γ))
  convert h using 1
  rw [Real.rpow_sub_one hcX.ne']
  field_simp

/-- The product of two independent finite probability spaces (O&R Exercise 6(e), p. 602:
"money and output shocks are independently distributed"). -/
def prodProb {A B : Type} [Fintype A] [Fintype B] (Ωa : FinProb A) (Ωb : FinProb B) :
    FinProb (A × B) :=
  ⟨fun q => Ωa.prob q.1 * Ωb.prob q.2, fun q => mul_nonneg (Ωa.prob_nonneg _)
    (Ωb.prob_nonneg _), by
      rw [Fintype.sum_prod_type, ← Finset.sum_mul_sum, Ωa.prob_sum, Ωb.prob_sum, one_mul]⟩

/-- Under independence, the expectation of a product of a money-state function and an
output-state function factorises (O&R Exercise 6(e), p. 602). -/
theorem expect_prod_mul {A B : Type} [Fintype A] [Fintype B] (Ωa : FinProb A)
    (Ωb : FinProb B) (h : A → ℝ) (g : B → ℝ) :
    (prodProb Ωa Ωb).expect (fun q => h q.1 * g q.2) = Ωa.expect h * Ωb.expect g := by
  simp only [FinProb.expect, prodProb, Fintype.sum_prod_type, Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

/-- **The two-good CIA forward rate** (O&R Exercise 6(e), p. 602): if money states `a` and
output states `b` are independent, `p_{X,t+1} = M_{t+1}/X_{t+1}`, `ℰ_{t+1} = κ M/M*`
(`κ = (1−γ)/γ`), and the good-`X` forward Euler equation 6(d) holds with a positive marginal
utility of good `X` that depends only on outputs (pooled consumption), then
`F = κ E[1/M*_{t+1}]/E[1/M_{t+1}]`, whatever the degree of risk aversion. -/
theorem ex6e_forward_rate {A B : Type} [Fintype A] [Fintype B] (Ωa : FinProb A)
    (Ωb : FinProb B) {F κ : ℝ} {M' Ms' : A → ℝ} {X' mu : B → ℝ} (hM' : ∀ a, 0 < M' a)
    (hX' : ∀ b, 0 < X' b) (hmu : ∀ b, 0 < mu b)
    (h6d : (prodProb Ωa Ωb).expect
      (fun q => (F - κ * M' q.1 / Ms' q.1) / (M' q.1 / X' q.2) * mu q.2) = 0) :
    F = κ * Ωa.expect (fun a => 1 / Ms' a) / Ωa.expect (fun a => 1 / M' a) := by
  have e : (fun q : A × B => (F - κ * M' q.1 / Ms' q.1) / (M' q.1 / X' q.2) * mu q.2)
      = fun q => (F * (1 / M' q.1) - κ * (1 / Ms' q.1)) * (X' q.2 * mu q.2) := by
    funext q
    have := hM' q.1; have := hX' q.2
    field_simp
  have hf := expect_prod_mul Ωa Ωb (fun a => F * (1 / M' a) - κ * (1 / Ms' a))
    (fun b => X' b * mu b)
  rw [e, hf] at h6d
  have hpos : 0 < Ωb.expect (fun b => X' b * mu b) :=
    Ωb.expect_pos fun b => mul_pos (hX' b) (hmu b)
  have h0 := (mul_eq_zero.1 h6d).resolve_right hpos.ne'
  rw [Ωa.expect_sub, Ωa.expect_mul_left, Ωa.expect_mul_left] at h0
  have hm : 0 < Ωa.expect (fun a => 1 / M' a) := Ωa.expect_pos fun a => one_div_pos.2 (hM' a)
  field_simp
  linarith

/-- **Exercise 6(f)**: the "risk-neutral" forward equation (107) holds in the two-good CIA
model (O&R p. 602). If the date-`t+1` price level is money times a positive function of
outputs, `P_{t+1} = M_{t+1} φ(X, Y)` (homogeneity of the price index, `least_cost_smul`;
`φ = 1/X` for `p_X`), then `E[ℰ/P]/E[1/P] = κ E[1/M*]/E[1/M]`, which is the forward rate of
6(e); the yen version `E[(1/ℰ)/P*]/E[1/P*]` equals its reciprocal. -/
theorem ex6f {A B : Type} [Fintype A] [Fintype B] (Ωa : FinProb A) (Ωb : FinProb B) {κ : ℝ}
    (hκ : 0 < κ) {M' Ms' : A → ℝ} {φ : B → ℝ} (hM' : ∀ a, 0 < M' a) (hMs' : ∀ a, 0 < Ms' a)
    (hφ : ∀ b, 0 < φ b) :
    (prodProb Ωa Ωb).expect (fun q => (κ * M' q.1 / Ms' q.1) / (M' q.1 * φ q.2))
        / (prodProb Ωa Ωb).expect (fun q => 1 / (M' q.1 * φ q.2))
      = κ * Ωa.expect (fun a => 1 / Ms' a) / Ωa.expect (fun a => 1 / M' a) ∧
    (prodProb Ωa Ωb).expect (fun q => (1 / (κ * M' q.1 / Ms' q.1))
          / ((M' q.1 * φ q.2) / (κ * M' q.1 / Ms' q.1)))
        / (prodProb Ωa Ωb).expect (fun q => 1 / ((M' q.1 * φ q.2) / (κ * M' q.1 / Ms' q.1)))
      = Ωa.expect (fun a => 1 / M' a) / (κ * Ωa.expect (fun a => 1 / Ms' a)) := by
  have e1 : (fun q : A × B => (κ * M' q.1 / Ms' q.1) / (M' q.1 * φ q.2))
      = fun q => (κ * (1 / Ms' q.1)) * (1 / φ q.2) := by
    funext q; have := hM' q.1; have := hMs' q.1; have := hφ q.2; field_simp
  have e2 : (fun q : A × B => 1 / (M' q.1 * φ q.2)) = fun q => (1 / M' q.1) * (1 / φ q.2) := by
    funext q; have := hM' q.1; have := hφ q.2; field_simp
  have e3 : (fun q : A × B => (1 / (κ * M' q.1 / Ms' q.1))
      / ((M' q.1 * φ q.2) / (κ * M' q.1 / Ms' q.1)))
      = fun q => (1 / M' q.1) * (1 / φ q.2) := by
    funext q; have := hM' q.1; have := hMs' q.1; have := hφ q.2; field_simp
  have e4 : (fun q : A × B => 1 / ((M' q.1 * φ q.2) / (κ * M' q.1 / Ms' q.1)))
      = fun q => (κ * (1 / Ms' q.1)) * (1 / φ q.2) := by
    funext q; have := hM' q.1; have := hMs' q.1; have := hφ q.2; field_simp
  have hb : 0 < Ωb.expect (fun b => 1 / φ b) := Ωb.expect_pos fun b => one_div_pos.2 (hφ b)
  have hm : 0 < Ωa.expect (fun a => 1 / M' a) := Ωa.expect_pos fun a => one_div_pos.2 (hM' a)
  have hms : 0 < Ωa.expect (fun a => 1 / Ms' a) :=
    Ωa.expect_pos fun a => one_div_pos.2 (hMs' a)
  have f1 := expect_prod_mul Ωa Ωb (fun a => κ * (1 / Ms' a)) (fun b => 1 / φ b)
  have f2 := expect_prod_mul Ωa Ωb (fun a => 1 / M' a) (fun b => 1 / φ b)
  rw [e1, e2, e3, e4, f1, f2, Ωa.expect_mul_left]
  constructor <;> field_simp

/-! ## Exercises 7 and 8: sampling, averaging and overlapping forecast errors -/

/-- Homoskedastic white noise `ε₀, …, ε_{n−1}`: mean zero, variance `σ²`, uncorrelated
(O&R Exercise 7, p. 602: "a serially uncorrelated white noise disturbance"). -/
structure WhiteNoise (Ω : FinProb S) (n : ℕ) where
  eps : Fin n → S → ℝ
  sigma2 : ℝ
  mean_zero : ∀ i, Ω.expect (eps i) = 0
  second : ∀ i j, Ω.expect (fun s => eps i s * eps j s) = if i = j then sigma2 else 0

/-- A linear combination `Σ aᵢ εᵢ` of the shocks (O&R Exercises 7–8). -/
def comb {Ω : FinProb S} {n : ℕ} (W : WhiteNoise Ω n) (a : Fin n → ℝ) : S → ℝ :=
  fun s => ∑ i, a i * W.eps i s

/-- Expectation of a finite sum (O&R Exercises 7–8). -/
theorem expect_finsum (Ω : FinProb S) {n : ℕ} (f : Fin n → S → ℝ) :
    Ω.expect (fun s => ∑ i, f i s) = ∑ i, Ω.expect (f i) := by
  simp only [FinProb.expect, Finset.mul_sum]
  exact Finset.sum_comm

/-- Linear combinations of white noise have mean zero (O&R Exercises 7–8). -/
theorem expect_comb {Ω : FinProb S} {n : ℕ} (W : WhiteNoise Ω n) (a : Fin n → ℝ) :
    Ω.expect (comb W a) = 0 := by
  unfold comb
  rw [expect_finsum]
  exact Finset.sum_eq_zero fun i _ => by rw [Ω.expect_mul_left, W.mean_zero, mul_zero]

/-- **Covariances of linear combinations of white noise**: `Cov(Σ aᵢεᵢ, Σ bᵢεᵢ) =
σ² Σ aᵢbᵢ` (O&R Exercises 7–8, "second-moment algebra"). -/
theorem cov_comb {Ω : FinProb S} {n : ℕ} (W : WhiteNoise Ω n) (a b : Fin n → ℝ) :
    Ω.cov (comb W a) (comb W b) = W.sigma2 * ∑ i, a i * b i := by
  have hpt : (fun s => comb W a s * comb W b s)
      = fun s => ∑ i, ∑ j, a i * b j * (W.eps i s * W.eps j s) := by
    funext s
    simp only [comb, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  simp only [FinProb.cov, expect_comb, mul_zero, sub_zero]
  rw [hpt, expect_finsum]
  simp only [expect_finsum, Ω.expect_mul_left, W.second, mul_ite, mul_zero,
    Finset.sum_ite_eq, Finset.mem_univ, ite_true, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The two-week average `ℰ̃_t = ½(ℰ_t + ℰ_{t−1})` of a random walk: sampled every other week,
`ℰ̃_{t+2} − ℰ̃_t = ½(ε_{t+2} + 2ε_{t+1} + ε_t)` (O&R Exercise 7(a), p. 602). -/
theorem timeavg_increment {E₀ ε₀ ε₁ ε₂ Em : ℝ} :
    (1 / 2 * ((E₀ + ε₁ + ε₂) + (E₀ + ε₁))) - 1 / 2 * (E₀ + Em)
      = 1 / 2 * (ε₂ + 2 * ε₁ + ε₀) ↔ Em = E₀ - ε₀ := by
  constructor <;> intro h <;> linarith

/-- **Exercise 7(a): the sampled average series is autocorrelated with coefficient 1/6**
(O&R p. 602): with shocks `ε_t, …, ε_{t+4}`, the consecutive biweekly changes
`½(ε_{t+2}+2ε_{t+1}+ε_t)` and `½(ε_{t+4}+2ε_{t+3}+ε_{t+2})` have equal variance `(3/2)σ²` and
covariance `σ²/4`, so their correlation is `1/6 ≠ 0`: not a random walk. -/
theorem ex7a_autocorrelation {Ω : FinProb S} (W : WhiteNoise Ω 5) (hσ : 0 < W.sigma2) :
    Ω.var (comb W ![1 / 2, 1, 1 / 2, 0, 0]) = 3 / 2 * W.sigma2 ∧
      Ω.var (comb W ![0, 0, 1 / 2, 1, 1 / 2]) = 3 / 2 * W.sigma2 ∧
      Ω.cov (comb W ![1 / 2, 1, 1 / 2, 0, 0]) (comb W ![0, 0, 1 / 2, 1, 1 / 2])
        = W.sigma2 / 4 ∧
      Ω.cov (comb W ![1 / 2, 1, 1 / 2, 0, 0]) (comb W ![0, 0, 1 / 2, 1, 1 / 2])
        / Ω.var (comb W ![1 / 2, 1, 1 / 2, 0, 0]) = 1 / 6 := by
  have h1 : Ω.var (comb W ![1 / 2, 1, 1 / 2, 0, 0]) = 3 / 2 * W.sigma2 := by
    simp only [FinProb.var, cov_comb, Fin.sum_univ_five]; simp; ring
  have h2 : Ω.var (comb W ![0, 0, 1 / 2, 1, 1 / 2]) = 3 / 2 * W.sigma2 := by
    simp only [FinProb.var, cov_comb, Fin.sum_univ_five]; simp; ring
  have h3 : Ω.cov (comb W ![1 / 2, 1, 1 / 2, 0, 0]) (comb W ![0, 0, 1 / 2, 1, 1 / 2])
      = W.sigma2 / 4 := by
    simp only [cov_comb, Fin.sum_univ_five]; simp; ring
  refine ⟨h1, h2, h3, ?_⟩
  rw [h1, h3]
  field_simp
  ring

/-- **Exercise 7(b): point sampling preserves the random walk** (O&R p. 602): the biweekly
changes `ε_{t+1}+ε_{t+2}` and `ε_{t+3}+ε_{t+4}` are uncorrelated. -/
theorem ex7b_point_sampling {Ω : FinProb S} (W : WhiteNoise Ω 5) :
    Ω.cov (comb W ![0, 1, 1, 0, 0]) (comb W ![0, 0, 0, 1, 1]) = 0 := by
  simp only [cov_comb, Fin.sum_univ_five]; simp

/-- **Exercise 7(a), conditional form** (O&R p. 602): on the event tree, if
`ℰ_{t+1} = ℰ_t + ε_{t+1}` with `E_t ε_{t+1} = 0`, then for the average
`ℰ̃_t = ℰ_t − ε_t/2 = ½(ℰ_t + ℰ_{t−1})`, `E_t ℰ̃_{t+2} = ℰ̃_t + ε_t/2 ≠ ℰ̃_t` (unless
`ε_t = 0`). -/
theorem ex7a_conditional (K : Kernel S) {g : S → ℝ} (hmds : ∀ s, ∑ s', K.trans s s' * g s' = 0)
    {Ex : Hist S → ℝ} (hrw : ∀ h s', Ex (next h s') = Ex h + g s') (h : Hist S) :
    iterStep K.trans 2 (fun h' => Ex h' - g h'.1 / 2) h = (Ex h - g h.1 / 2) + g h.1 / 2 := by
  have hn : ∀ (h : Hist S) s', (next h s').1 = s' := fun _ _ => rfl
  have h1 : ∀ h', oneStep K.trans (fun h'' => Ex h'' - g h''.1 / 2) h' = Ex h' := fun h' => by
    simp only [oneStep, hrw, hn]
    have e : ∀ s', K.trans h'.1 s' * (Ex h' + g s' - g s' / 2)
        = Ex h' * K.trans h'.1 s' + 1 / 2 * (K.trans h'.1 s' * g s') := fun s' => by ring
    simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum, K.trans_sum, hmds]
    ring
  have h2 : oneStep K.trans Ex h = Ex h := by
    simp only [oneStep, hrw]
    have e : ∀ s', K.trans h.1 s' * (Ex h + g s') = Ex h * K.trans h.1 s' + K.trans h.1 s' * g s' :=
      fun s' => by ring
    simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum, K.trans_sum, hmds]
    ring
  change oneStep K.trans (oneStep K.trans (fun h' => Ex h' - g h'.1 / 2)) h = _
  rw [show oneStep K.trans (fun h' => Ex h' - g h'.1 / 2) = Ex from funext h1, h2]
  ring

/-- **Exercise 7(b), conditional form** (O&R p. 602): point-sampled random walk,
`E_t ℰ_{t+2} = ℰ_t`. -/
theorem ex7b_conditional (K : Kernel S) {g : S → ℝ} (hmds : ∀ s, ∑ s', K.trans s s' * g s' = 0)
    {Ex : Hist S → ℝ} (hrw : ∀ h s', Ex (next h s') = Ex h + g s') (h : Hist S) :
    iterStep K.trans 2 Ex h = Ex h := by
  have h1 : ∀ h', oneStep K.trans Ex h' = Ex h' := fun h' => by
    simp only [oneStep, hrw]
    have e : ∀ s', K.trans h'.1 s' * (Ex h' + g s')
        = Ex h' * K.trans h'.1 s' + K.trans h'.1 s' * g s' := fun s' => by ring
    simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum, K.trans_sum, hmds]
    ring
  change oneStep K.trans (oneStep K.trans Ex) h = _
  rw [show oneStep K.trans Ex = Ex from funext h1, h1]

/-- **Exercise 8(a): overlapping forecast errors are serially correlated** (O&R p. 603):
with a random walk, the two-week forecast errors `u_t = −(ε_{t+1}+ε_{t+2})` and
`u_{t+1} = −(ε_{t+2}+ε_{t+3})` have variance `2σ²` and covariance `σ²`, correlation `1/2`. -/
theorem ex8a_overlap {Ω : FinProb S} (W : WhiteNoise Ω 4) (hσ : 0 < W.sigma2) :
    Ω.var (comb W ![0, -1, -1, 0]) = 2 * W.sigma2 ∧
      Ω.cov (comb W ![0, -1, -1, 0]) (comb W ![0, 0, -1, -1]) = W.sigma2 ∧
      Ω.cov (comb W ![0, -1, -1, 0]) (comb W ![0, 0, -1, -1])
        / Ω.var (comb W ![0, -1, -1, 0]) = 1 / 2 := by
  have h1 : Ω.var (comb W ![0, -1, -1, 0]) = 2 * W.sigma2 := by
    simp only [FinProb.var, cov_comb, Fin.sum_univ_four]; simp; ring
  have h2 : Ω.cov (comb W ![0, -1, -1, 0]) (comb W ![0, 0, -1, -1]) = W.sigma2 := by
    simp only [cov_comb, Fin.sum_univ_four]; simp
  refine ⟨h1, h2, ?_⟩
  rw [h1, h2]
  field_simp

/-- The two-period forecast error `u = f_{t,2} − e_{t+2} = E_t e_{t+2} − e_{t+2}`, evaluated
at the date-`t+2` node (O&R Exercise 8, p. 603). -/
def forecastErr (K : Kernel S) (e : Hist S → ℝ) : Hist S → ℝ :=
  fun h₂ => iterStep K.trans 2 e (anc^[2] h₂) - e h₂

/-- The forecast error is unpredictable two periods ahead: `E_t u_t = 0` (O&R Exercise 8,
p. 603, "no risk premium"). -/
theorem forecastErr_unbiased (K : Kernel S) (e : Hist S → ℝ) (h : Hist S) :
    iterStep K.trans 2 (forecastErr K e) h = 0 := by
  unfold forecastErr
  rw [iterStep_sub_fun]
  have := iterStep_pull K.trans 2 (iterStep K.trans 2 e) (fun _ => 1) h
  simp only [mul_one, iterStep_const K.trans_sum] at this
  rw [this, sub_self]

/-- **Exercise 8(b): every-other-observation forecast errors are uncorrelated, for ANY
exchange-rate process** (O&R p. 603): `E_t[u_t u_{t+2}] = 0` and `E_t u_{t+2} = 0`,
because `u_t` is known at `t+2` and `u_{t+2}` is unpredictable at `t+2` (tower property). -/
theorem ex8b_nonoverlap (K : Kernel S) (e : Hist S → ℝ) (h : Hist S) :
    iterStep K.trans 4 (fun h₄ => forecastErr K e (anc^[2] h₄) * forecastErr K e h₄) h = 0 ∧
      iterStep K.trans 4 (forecastErr K e) h = 0 := by
  have inner : ∀ h₂, iterStep K.trans 2
      (fun h₄ => forecastErr K e (anc^[2] h₄) * forecastErr K e h₄) h₂ = 0 := fun h₂ => by
    rw [iterStep_pull, forecastErr_unbiased, mul_zero]
  constructor
  · rw [show (4 : ℕ) = 2 + 2 from rfl, iterStep_add, funext inner]
    exact iterStep_const K.trans_sum 2 0 h
  · rw [show (4 : ℕ) = 2 + 2 from rfl, iterStep_add,
      funext (forecastErr_unbiased K e)]
    exact iterStep_const K.trans_sum 2 0 h

/-! ## Sterilised and forward intervention (§8.7.6.1, Appendix 8B) -/

/-- A central-bank balance sheet in domestic currency (O&R Appendix 8B, p. 598): gold (at
price `P^g`), foreign-currency bonds and money (at the exchange rate `ℰ`), domestic bonds;
liabilities are the monetary base (currency plus reserves) and net worth. -/
structure CBBalanceSheet where
  gold : ℝ
  bondsF : ℝ
  bondsH : ℝ
  moneyF : ℝ
  base : ℝ
  netWorth : ℝ

/-- The balance-sheet identity `P^g Gold + ℰB_F + B_H + ℰM_F = M_H + RR + NW`
(O&R Appendix 8B, p. 598). -/
def CBBalanceSheet.Balanced (b : CBBalanceSheet) (Pg E : ℝ) : Prop :=
  Pg * b.gold + E * b.bondsF + b.bondsH + E * b.moneyF = b.base + b.netWorth

/-- A NONSTERILISED purchase of `δ` dollars' worth of foreign-currency bonds, paid for with
newly issued base money (O&R p. 598). -/
noncomputable def CBBalanceSheet.buyForeign (b : CBBalanceSheet) (E δ : ℝ) : CBBalanceSheet :=
  { b with bondsF := b.bondsF + δ / E, base := b.base + δ }

/-- An open-market SALE of `δ` of domestic bonds, withdrawing base money (O&R p. 599). -/
def CBBalanceSheet.sellHome (b : CBBalanceSheet) (δ : ℝ) : CBBalanceSheet :=
  { b with bondsH := b.bondsH - δ, base := b.base - δ }

/-- A nonsterilised foreign-exchange purchase preserves the balance-sheet identity
(O&R Appendix 8B, p. 598). -/
theorem buyForeign_balanced {b : CBBalanceSheet} {Pg E : ℝ} (hE : E ≠ 0) (δ : ℝ)
    (hb : b.Balanced Pg E) : (b.buyForeign E δ).Balanced Pg E := by
  simp only [CBBalanceSheet.Balanced, CBBalanceSheet.buyForeign] at hb ⊢
  have : E * (b.bondsF + δ / E) = E * b.bondsF + δ := by field_simp
  rw [this]
  linarith

/-- An open-market sale preserves the balance-sheet identity (O&R Appendix 8B, p. 599). -/
theorem sellHome_balanced {b : CBBalanceSheet} {Pg E : ℝ} (δ : ℝ) (hb : b.Balanced Pg E) :
    (b.sellHome δ).Balanced Pg E := by
  simp only [CBBalanceSheet.Balanced, CBBalanceSheet.sellHome] at hb ⊢
  linarith

/-- **A sterilised intervention is a swap of home for foreign bonds with no change in the
money supply** (O&R Appendix 8B, p. 599): nonsterilised purchase followed by an
open-market sale of the same amount. -/
theorem sterilised_is_swap (b : CBBalanceSheet) (E δ : ℝ) :
    ((b.buyForeign E δ).sellHome δ).base = b.base ∧
      ((b.buyForeign E δ).sellHome δ).bondsH = b.bondsH - δ ∧
      ((b.buyForeign E δ).sellHome δ).bondsF = b.bondsF + δ / E ∧
      ((b.buyForeign E δ).sellHome δ).gold = b.gold ∧
      ((b.buyForeign E δ).sellHome δ).moneyF = b.moneyF ∧
      ((b.buyForeign E δ).sellHome δ).netWorth = b.netWorth := by
  simp [CBBalanceSheet.buyForeign, CBBalanceSheet.sellHome]

/-- **Forward intervention is equivalent to sterilised intervention** (O&R §8.7.6.1,
p. 593): a forward purchase of `1+i` dollars for `(1+i)/F` yen at `t+1` lowers the present
value of dollar debt held by the market by `$1` and raises that of yen debt by
`(1+i)/((1+i*)F) = 1/ℰ` yen, also worth `$1`, by covered interest parity (104). -/
theorem forward_intervention_equiv {i istar E F : ℝ} (hi : 0 < 1 + i) (histar : 0 < 1 + istar)
    (hE : 0 < E) (hF : 0 < F) (hcip : 1 + i = (1 + istar) * F / E) :
    (1 + i) / (1 + i) = 1 ∧ 1 / (1 + istar) * ((1 + i) / F) = 1 / E ∧
      E * (1 / (1 + istar) * ((1 + i) / F)) = 1 := by
  refine ⟨div_self hi.ne', ?_, ?_⟩
  · rw [hcip]; field_simp
  · rw [hcip]; field_simp


/-! ## (109) and (119) under genuine joint normality -/

namespace JointGaussian

open MeasureTheory ProbabilityTheory

/-- **The lognormal moment identity for a Gaussian variable** (O&R fn 41 of Ch. 5, used in
fn 75, p. 588): if `Z` has a Gaussian law (Mathlib's `HasGaussianLaw`), then `exp Z` is
integrable and `E[exp Z] = exp(E Z + ½ Var Z)`. -/
theorem expect_exp {Ω' : Type*} {mΩ : MeasurableSpace Ω'} {P : Measure Ω'} {Z : Ω' → ℝ}
    (hZ : HasGaussianLaw Z P) :
    Integrable (fun ω => Real.exp (Z ω)) P ∧
      ∫ ω, Real.exp (Z ω) ∂P = Real.exp (P[Z] + Var[Z; P] / 2) := by
  have hL : HasLaw Z (gaussianReal P[Z] Var[Z; P].toNNReal) P :=
    { aemeasurable := hZ.aemeasurable, map_eq := hZ.map_eq_gaussianReal }
  have hv : ((Var[Z; P].toNNReal : NNReal) : ℝ) = Var[Z; P] :=
    Real.coe_toNNReal _ (variance_nonneg Z P)
  constructor
  · have := hL.integrable_comp (integrable_exp_mul_gaussianReal (μ := P[Z])
      (v := Var[Z; P].toNNReal) 1)
    simpa [Function.comp_def] using this
  · have := mgf_gaussianReal hL 1
    simp only [mgf, one_mul, hv, one_pow, mul_one] at this
    exact this

/-- **(109) under joint normality of `(e, p)`** (O&R (109) and fn 75, p. 588): if the log
exchange rate and the log price level `(e_{t+1}, p_{t+1})` are jointly Gaussian (Mathlib's
`HasGaussianLaw` for the pair) and (107) holds, then
`f = E e + ½ Var e − Cov(e, p)`, with Mathlib's expectation, variance and covariance. -/
theorem eq109_gaussian {Ω' : Type*} {mΩ : MeasurableSpace Ω'} {P : Measure Ω'}
    {e p : Ω' → ℝ} (hG : HasGaussianLaw (fun ω => (e ω, p ω)) P) {F : ℝ} (hF : 0 < F)
    (h107 : ∫ ω, (F - Real.exp (e ω)) / Real.exp (p ω) ∂P = 0) :
    Real.log F = P[e] + Var[e; P] / 2 - cov[e, p; P] := by
  have := hG.isProbabilityMeasure
  have he := hG.fst
  have hp := hG.snd
  have h1 := expect_exp hp.fun_neg
  have h2 := expect_exp hG.fun_sub
  have ex : (fun ω => (F - Real.exp (e ω)) / Real.exp (p ω))
      = fun ω => F * Real.exp (-p ω) - Real.exp (e ω - p ω) := by
    funext ω; rw [Real.exp_neg, Real.exp_sub]; field_simp
  rw [ex, integral_sub (h1.1.const_mul F) h2.1, integral_const_mul, h1.2, h2.2,
    sub_eq_zero] at h107
  have hl := congrArg Real.log h107
  rw [Real.log_mul hF.ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_exp] at hl
  have m1 : P[fun ω => -p ω] = -P[p] := integral_neg _
  have m2 : P[fun ω => e ω - p ω] = P[e] - P[p] := integral_sub he.integrable hp.integrable
  rw [m1, m2, variance_fun_neg, variance_fun_sub he.memLp_two hp.memLp_two] at hl
  linarith

/-- **(119) under joint normality of `(e, p, c)`** (O&R (119) and fn 79, p. 592): if the
logs of the exchange rate, the price level and consumption at `t+1` are jointly Gaussian and
(118) holds (`C_t = exp c₀` known at `t`), then
`f − E e = ½ Var e − Cov(e, p) − ρ Cov(e, c)`. -/
theorem eq119_gaussian {Ω' : Type*} {mΩ : MeasurableSpace Ω'} {P : Measure Ω'}
    {e p c : Ω' → ℝ} (hG : HasGaussianLaw (fun ω => (e ω, p ω, c ω)) P) {F ρ c₀ : ℝ}
    (hF : 0 < F)
    (h118 : ∫ ω, (F - Real.exp (e ω)) / Real.exp (p ω)
      * (Real.exp c₀ / Real.exp (c ω)) ^ ρ ∂P = 0) :
    Real.log F - P[e] = Var[e; P] / 2 - cov[e, p; P] - ρ * cov[e, c; P] := by
  have := hG.isProbabilityMeasure
  have he := hG.fst
  have hpc := hG.snd
  have hp := hpc.fst
  have hc := hpc.snd
  set L : ℝ × ℝ →L[ℝ] ℝ := -(ContinuousLinearMap.fst ℝ ℝ ℝ + ρ • ContinuousLinearMap.snd ℝ ℝ ℝ)
  set Z : Ω' → ℝ := fun ω => -(p ω + ρ * c ω)
  have hZ : HasGaussianLaw Z P := by
    have := hpc.map_fun L
    have e1 : (fun ω => L (p ω, c ω)) = Z := by funext ω; simp [L, Z]
    rwa [e1] at this
  have hW : HasGaussianLaw (fun ω => e ω + Z ω) P := by
    have := hG.map_fun (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)
      + L.comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ)))
    have e1 : (fun ω => (ContinuousLinearMap.fst ℝ ℝ (ℝ × ℝ)
        + L.comp (ContinuousLinearMap.snd ℝ ℝ (ℝ × ℝ))) (e ω, p ω, c ω))
        = fun ω => e ω + Z ω := by funext ω; simp [L, Z]
    rwa [e1] at this
  have h1 := expect_exp hZ
  have h2 := expect_exp hW
  have ex : (fun ω => (F - Real.exp (e ω)) / Real.exp (p ω)
      * (Real.exp c₀ / Real.exp (c ω)) ^ ρ)
      = fun ω => Real.exp (ρ * c₀) * (F * Real.exp (Z ω) - Real.exp (e ω + Z ω)) := by
    funext ω
    rw [← Real.exp_sub, ← Real.exp_mul]
    simp only [Z, Real.exp_add, Real.exp_neg]
    rw [show (c₀ - c ω) * ρ = ρ * c₀ + -(ρ * c ω) by ring, Real.exp_add, Real.exp_neg]
    field_simp
  rw [ex, integral_const_mul, integral_sub (h1.1.const_mul F) h2.1, integral_const_mul]
    at h118
  have h3 := (mul_eq_zero.1 h118).resolve_left (Real.exp_pos _).ne'
  rw [h1.2, h2.2, sub_eq_zero] at h3
  have hl := congrArg Real.log h3
  rw [Real.log_mul hF.ne' (Real.exp_pos _).ne', Real.log_exp, Real.log_exp] at hl
  have m1 : P[fun ω => e ω + Z ω] = P[e] + P[Z] := integral_add he.integrable hZ.integrable
  have v1 : Var[fun ω => e ω + Z ω; P] = Var[e; P] + 2 * cov[e, Z; P] + Var[Z; P] :=
    variance_fun_add he.memLp_two hZ.memLp_two
  have c1 : cov[e, Z; P] = -(cov[e, p; P] + ρ * cov[e, c; P]) := by
    have hpc' : (fun ω => p ω + ρ * c ω) = p + fun ω => ρ * c ω := rfl
    simp only [Z]
    rw [covariance_fun_neg_right, hpc', covariance_add_right he.memLp_two hp.memLp_two
      (hc.memLp_two.const_mul ρ), covariance_const_mul_right]
  rw [m1, v1, c1] at hl
  linarith

/-- **The joint-normality hypothesis is satisfiable with correlated components** (O&R
p. 588): under a standard normal law, `(x, x/2)` is jointly Gaussian. -/
theorem jointGaussian_witness :
    HasGaussianLaw (fun x : ℝ => (x, x / 2)) (gaussianReal 0 1) := by
  have h := (IsGaussian.hasGaussianLaw_id (μ := gaussianReal 0 1)).map_fun
    ((ContinuousLinearMap.id ℝ ℝ).prod ((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ ℝ))
  have e : (fun x : ℝ => ((ContinuousLinearMap.id ℝ ℝ).prod
      ((1 / 2 : ℝ) • ContinuousLinearMap.id ℝ ℝ)) (id x)) = fun x : ℝ => (x, x / 2) := by
    funext x; simp; ring
  rwa [e] at h

end JointGaussian


/-! ## Non-vacuity of the white-noise hypotheses -/

/-- The uniform distribution on eight states (three fair coin flips) (O&R Exercise 7). -/
noncomputable def uniform8 : FinProb (Fin 8) :=
  ⟨fun _ => 1 / 8, fun _ => by norm_num, by simp⟩

/-- Five `±1` Walsh functions of three fair coin flips (O&R Exercise 7). -/
def walsh : Fin 5 → Fin 8 → ℝ :=
  ![![1, -1, 1, -1, 1, -1, 1, -1], ![1, 1, -1, -1, 1, 1, -1, -1],
    ![1, 1, 1, 1, -1, -1, -1, -1], ![1, -1, -1, 1, 1, -1, -1, 1],
    ![1, -1, 1, -1, -1, 1, -1, 1]]

/-- **The white-noise hypotheses of Exercises 7–8 are satisfiable**: the Walsh functions
of three fair coin flips are mean-zero, unit-variance and uncorrelated (O&R Exercise 7,
p. 602). -/
noncomputable def walshNoise : WhiteNoise uniform8 5 :=
  ⟨walsh, 1, fun i => by
    fin_cases i <;> simp [FinProb.expect, uniform8, walsh, Fin.sum_univ_eight],
    fun i j => by
      fin_cases i <;> fin_cases j <;>
        simp [FinProb.expect, uniform8, walsh, Fin.sum_univ_eight] <;> norm_num⟩

end ObstfeldRogoff.MoneyExchangeRates.ForwardPremium
