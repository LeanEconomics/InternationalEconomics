import Mathlib.Algebra.BigOperators.Field
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Real
set_option autoImplicit false

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# A finite state space

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*,
§5.1, pp. 270–275. Uncertainty is modelled by finitely many states of nature `s`
with probabilities `π(s) ≥ 0` summing to one, and expectations are finite sums
`E[X] = Σ_s π(s) X(s)`.
-/

namespace ObstfeldRogoff.InternationalFinancialMarkets

open Finset

/-- Probabilities on a finite set of states of nature (O&R §5.1). -/
structure StateSpace (S : Type) [Fintype S] where
  prob : S → ℝ
  prob_nonneg : ∀ s, 0 ≤ prob s
  prob_sum : ∑ s, prob s = 1

namespace StateSpace

variable {S : Type} [Fintype S] (Ω : StateSpace S)

/-- The expectation `E[X] = Σ_s π(s) X(s)`. -/
def expect (X : S → ℝ) : ℝ := ∑ s, Ω.prob s * X s

/-- The expectation of a constant is that constant. -/
theorem expect_const (c : ℝ) : Ω.expect (fun _ => c) = c := by
  simp [expect, ← Finset.sum_mul, Ω.prob_sum]

/-- Expectation is additive. -/
theorem expect_add (X Y : S → ℝ) :
    Ω.expect (fun s => X s + Y s) = Ω.expect X + Ω.expect Y := by
  simp [expect, mul_add, Finset.sum_add_distrib]

end StateSpace

end ObstfeldRogoff.InternationalFinancialMarkets

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Finite-state expectations, covariances and correlations

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*,
Chapter 5. Uncertainty is a finite set of states with probabilities `π(s)`
(`InternationalFinancialMarkets.Model`). This file provides the moments used
throughout the chapter, as finite sums:
* `Cov(X, Y) = E[XY] − E[X]E[Y]`, `Var(X) = Cov(X, X) ≥ 0`, `Std(X) = √Var(X)`;
* the covariance decomposition `E[XY] = E[X]E[Y] + Cov(X, Y)` (used in O&R (5.52)) and
  shift invariance `Cov(a + X, Y) = Cov(X, Y)` (O&R footnote 32);
* Cauchy–Schwarz `|Cov(X, Y)| ≤ Std(X)Std(Y)` (behind the Hansen–Jagannathan bound,
  O&R footnote 38);
* an affine function with positive slope has correlation one (O&R footnote 18).
-/

namespace ObstfeldRogoff.InternationalFinancialMarkets.StateSpace

open Finset

variable {S : Type} [Fintype S] (Ω : StateSpace S)

/-- The covariance `Cov(X, Y) = E[XY] − E[X]E[Y]`. -/
def cov (X Y : S → ℝ) : ℝ := Ω.expect (fun s => X s * Y s) - Ω.expect X * Ω.expect Y

/-- The variance `Var(X) = Cov(X, X)`. -/
def var (X : S → ℝ) : ℝ := Ω.cov X X

/-- The standard deviation `Std(X) = √Var(X)`. -/
noncomputable def std (X : S → ℝ) : ℝ := Real.sqrt (Ω.var X)

/-- The correlation `Corr(X, Y) = Cov(X, Y)/(Std(X)Std(Y))`. -/
noncomputable def corr (X Y : S → ℝ) : ℝ := Ω.cov X Y / (Ω.std X * Ω.std Y)

/-- Expectation is linear under scaling. -/
theorem expect_smul (c : ℝ) (X : S → ℝ) : Ω.expect (fun s => c * X s) = c * Ω.expect X := by
  simp only [expect, Finset.mul_sum]
  exact Finset.sum_congr rfl fun s _ => by ring

/-- Expectation is linear under subtraction. -/
theorem expect_sub (X Y : S → ℝ) :
    Ω.expect (fun s => X s - Y s) = Ω.expect X - Ω.expect Y := by
  simp [expect, mul_sub, Finset.sum_sub_distrib]

/-- Expectation is monotone. -/
theorem expect_mono {X Y : S → ℝ} (h : ∀ s, X s ≤ Y s) : Ω.expect X ≤ Ω.expect Y :=
  Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (h s) (Ω.prob_nonneg s)

/-- The expectation of a nonnegative variable is nonnegative. -/
theorem expect_nonneg {X : S → ℝ} (h : ∀ s, 0 ≤ X s) : 0 ≤ Ω.expect X := by
  simpa [expect_const] using Ω.expect_mono (X := fun _ => 0) h

/-- **The covariance decomposition** (O&R (5.52)): `E[XY] = E[X]E[Y] + Cov(X, Y)`. -/
theorem expect_mul_eq (X Y : S → ℝ) :
    Ω.expect (fun s => X s * Y s) = Ω.expect X * Ω.expect Y + Ω.cov X Y := by
  unfold cov; ring

/-- The covariance is symmetric. -/
theorem cov_comm (X Y : S → ℝ) : Ω.cov X Y = Ω.cov Y X := by
  unfold cov
  simp only [mul_comm (X _), mul_comm (Ω.expect X)]

/-- **Shift invariance**, O&R footnote 32: `Cov(a + X, Y) = Cov(X, Y)`. -/
theorem cov_const_add (a : ℝ) (X Y : S → ℝ) : Ω.cov (fun s => a + X s) Y = Ω.cov X Y := by
  unfold cov
  have h1 : Ω.expect (fun s => (a + X s) * Y s) =
      a * Ω.expect Y + Ω.expect (fun s => X s * Y s) := by
    simp only [add_mul]
    rw [expect_add, expect_smul]
  rw [h1, expect_add, expect_const]
  ring

/-- Covariance scales: `Cov(cX, Y) = c Cov(X, Y)`. -/
theorem cov_smul (c : ℝ) (X Y : S → ℝ) : Ω.cov (fun s => c * X s) Y = c * Ω.cov X Y := by
  unfold cov
  have : (fun s => c * X s * Y s) = fun s => c * (X s * Y s) := by funext s; ring
  simp only [this, expect_smul]
  ring

/-- The covariance of a constant with anything is zero. -/
theorem cov_const (a : ℝ) (Y : S → ℝ) : Ω.cov (fun _ => a) Y = 0 := by
  unfold cov
  rw [expect_smul, expect_const]
  ring

/-- The covariance in centred form: `Cov(X, Y) = E[(X − EX)(Y − EY)]`. -/
theorem cov_eq_expect_centred (X Y : S → ℝ) :
    Ω.cov X Y = Ω.expect (fun s => (X s - Ω.expect X) * (Y s - Ω.expect Y)) := by
  have e : (fun s => (X s - Ω.expect X) * (Y s - Ω.expect Y)) = fun s =>
      X s * Y s + (-(Ω.expect Y) * X s + (-(Ω.expect X) * Y s + Ω.expect X * Ω.expect Y)) := by
    funext s; ring
  rw [e, expect_add, expect_add, expect_add, expect_smul, expect_smul, expect_const]
  unfold cov
  ring

/-- **The variance is nonnegative.** -/
theorem var_nonneg (X : S → ℝ) : 0 ≤ Ω.var X := by
  unfold var
  rw [cov_eq_expect_centred]
  exact Ω.expect_nonneg fun s => mul_self_nonneg _

/-- The variance of `a + bX` is `b² Var(X)`. -/
theorem var_affine (a b : ℝ) (X : S → ℝ) : Ω.var (fun s => a + b * X s) = b ^ 2 * Ω.var X := by
  unfold var
  rw [cov_const_add, Ω.cov_comm, cov_const_add, cov_smul, Ω.cov_comm, cov_smul]
  ring

/-- **Cauchy–Schwarz for covariances**: `Cov(X, Y)² ≤ Var(X)Var(Y)`. -/
theorem cov_sq_le (X Y : S → ℝ) : Ω.cov X Y ^ 2 ≤ Ω.var X * Ω.var Y := by
  -- the quadratic `Var(tX − Y) ≥ 0` in `t` has nonpositive discriminant
  have hq : ∀ t : ℝ, 0 ≤ t ^ 2 * Ω.var X - 2 * t * Ω.cov X Y + Ω.var Y := by
    intro t
    have h := Ω.var_nonneg (fun s => t * X s - Y s)
    have e : Ω.var (fun s => t * X s - Y s) =
        t ^ 2 * Ω.var X - 2 * t * Ω.cov X Y + Ω.var Y := by
      unfold var
      rw [cov_eq_expect_centred, cov_eq_expect_centred, cov_eq_expect_centred,
        cov_eq_expect_centred]
      rw [expect_sub, expect_smul]
      have e2 : (fun s => (t * X s - Y s - (t * Ω.expect X - Ω.expect Y)) *
          (t * X s - Y s - (t * Ω.expect X - Ω.expect Y))) = fun s =>
          t ^ 2 * ((X s - Ω.expect X) * (X s - Ω.expect X)) +
            (-(2 * t) * ((X s - Ω.expect X) * (Y s - Ω.expect Y)) +
              (Y s - Ω.expect Y) * (Y s - Ω.expect Y)) := by
        funext s; ring
      rw [e2, expect_add, expect_add, expect_smul, expect_smul]
      ring
    rw [← e]
    exact h
  have hvX := Ω.var_nonneg X
  rcases hvX.lt_or_eq with hpos | hzero
  · have := hq (Ω.cov X Y / Ω.var X)
    field_simp at this
    nlinarith
  · -- Var X = 0: the quadratic is linear in t, so Cov X Y = 0
    by_contra hc
    push Not at hc
    have hcov : Ω.cov X Y ≠ 0 := by
      intro h0; rw [h0, ← hzero] at hc; simp at hc
    set t := (Ω.var Y + 1) / (2 * Ω.cov X Y) with ht
    have h2t : 2 * t * Ω.cov X Y = Ω.var Y + 1 := by rw [ht]; field_simp
    have := hq t
    rw [← hzero] at this
    linarith

/-- **Cauchy–Schwarz**: `|Cov(X, Y)| ≤ Std(X) Std(Y)`. -/
theorem abs_cov_le (X Y : S → ℝ) : |Ω.cov X Y| ≤ Ω.std X * Ω.std Y := by
  unfold std
  rw [← Real.sqrt_mul (Ω.var_nonneg X), ← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (Ω.cov_sq_le X Y)

/-- **Correlations lie in `[−1, 1]`** when both standard deviations are positive. -/
theorem abs_corr_le_one {X Y : S → ℝ} (hX : 0 < Ω.std X) (hY : 0 < Ω.std Y) :
    |Ω.corr X Y| ≤ 1 := by
  unfold corr
  rw [abs_div, abs_of_pos (mul_pos hX hY), div_le_one (mul_pos hX hY)]
  exact Ω.abs_cov_le X Y

/-- **An affine function with positive slope has correlation one**, O&R footnote 18: if
`Y = a + bX` with `b > 0` and `Var(X) > 0`, then `Corr(X, Y) = 1`. -/
theorem corr_affine {X : S → ℝ} {a b : ℝ} (hb : 0 < b) (hX : 0 < Ω.var X) :
    Ω.corr X (fun s => a + b * X s) = 1 := by
  unfold corr std
  rw [var_affine, Ω.cov_comm, cov_const_add, cov_smul, Ω.cov_comm]
  change b * Ω.var X / (Real.sqrt (Ω.var X) * Real.sqrt (b ^ 2 * Ω.var X)) = 1
  rw [Real.sqrt_mul (sq_nonneg b), Real.sqrt_sq hb.le]
  have hs : 0 < Real.sqrt (Ω.var X) := Real.sqrt_pos.2 hX
  have hss : Real.sqrt (Ω.var X) * Real.sqrt (Ω.var X) = Ω.var X := Real.mul_self_sqrt hX.le
  field_simp
  nlinarith [hss]

end ObstfeldRogoff.InternationalFinancialMarkets.StateSpace

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Trade across random states of nature: the small-country case

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §5.1.1–5.1.6,
pp. 270–280, Appendix 5B, pp. 337–340, and Exercises 1 and 3, pp. 345–346.

A small endowment economy lives for two dates; date-2 output `Y2(s)` depends on the state
`s` (a finite type, probabilities `Ω.prob s = π(s)`). Arrow–Debreu (AD) security `s` pays one
unit in state `s` only and costs `p(s)/(1+r)` on date 1; the riskless bond costs one unit and
pays `1 + r`. We prove:
* no-arbitrage with bonds and AD securities holds iff `Σ p(s) = 1` and `p ≥ 0` (O&R (7));
  bonds are redundant and AD securities span every payoff (§5.1.2);
* the budget constraints (2)+(3) are equivalent to the intertemporal constraint (4)/(18);
* from the first-order conditions (5): the bond Euler equation (8), (6) and (9), and
  sufficiency of (5) for a concave utility;
* full insurance iff prices are actuarially fair, `p = π` (O&R (10));
* the exact CRRA form of (11) and the Arrow–Pratt coefficient (12);
* log-utility closed forms (15)–(17), footnotes 9 and 10;
* Appendix 5B: (78)–(81), the sign of `CA₁` is that of `r − r^CA` (footnote 51) and not
  that of `r − r^A`, footnote 50, gross flows `B₂(1)`, `B₂(2)`, and Exercise 1;
* Exercise 3 (quadratic utility): certainty equivalence, the Kuhn–Tucker solution with the
  date-2 nonnegativity constraint (the book's "`C_t`" in part (b) is a typo for `C₁`), and
  full insurance under complete markets with fair prices.
-/

namespace ObstfeldRogoff.InternationalFinancialMarkets.SmallCountry

open Finset

variable {S : Type} [Fintype S]

/-! ## Arrow–Debreu securities and bonds (§5.1.2, pp. 272–273) -/

/-- Payoff of one state-`s'` Arrow–Debreu security in state `s`, O&R §5.1.2, p. 272:
one unit if `s = s'`, nothing otherwise. -/
def adPayoff [DecidableEq S] (s' s : S) : ℝ := if s = s' then 1 else 0

/-- Date-2 payoff in state `s` of a portfolio of `b` riskless bonds (each paying `1 + r`) and
`B s'` state-`s'` AD securities, O&R §5.1.2, p. 272. -/
def portfolioPayoff [DecidableEq S] (r b : ℝ) (B : S → ℝ) (s : S) : ℝ :=
  (1 + r) * b + ∑ s', B s' * adPayoff s' s

/-- Date-1 cost of the portfolio: bonds cost 1, AD security `s` costs `p(s)/(1+r)`,
O&R §5.1.3, p. 273. -/
noncomputable def portfolioCost (p : S → ℝ) (r b : ℝ) (B : S → ℝ) : ℝ :=
  b + ∑ s, p s / (1 + r) * B s

/-- No arbitrage, O&R §5.1.4, pp. 276–277: every portfolio with a nonnegative payoff in every
state has a nonnegative cost. -/
def NoArbitrage [DecidableEq S] (p : S → ℝ) (r : ℝ) : Prop :=
  ∀ (b : ℝ) (B : S → ℝ), (∀ s, 0 ≤ portfolioPayoff r b B s) → 0 ≤ portfolioCost p r b B

/-- The payoff of an AD portfolio is the vector of its holdings, O&R §5.1.2, p. 272. -/
theorem portfolioPayoff_eq [DecidableEq S] (r b : ℝ) (B : S → ℝ) (s : S) :
    portfolioPayoff r b B s = (1 + r) * b + B s := by
  simp [portfolioPayoff, adPayoff]

/-- AD securities span all payoffs (complete markets), O&R §5.1.2, pp. 272–273: every date-2
payoff `X` is delivered by the pure AD portfolio `B = X`, at cost `Σ p(s)X(s)/(1+r)`. -/
theorem ad_span [DecidableEq S] (p : S → ℝ) (r : ℝ) (X : S → ℝ) :
    (∀ s, portfolioPayoff r 0 X s = X s) ∧
      portfolioCost p r 0 X = (∑ s, p s * X s) / (1 + r) := by
  refine ⟨fun s => by simp [portfolioPayoff_eq], ?_⟩
  simp only [portfolioCost, zero_add, Finset.sum_div]
  exact Finset.sum_congr rfl fun s _ => by ring

/-- No-arbitrage pricing, O&R (7), p. 277: with `1 + r > 0`, there is no arbitrage between the
bond and the AD securities iff the AD prices satisfy `Σ p(s) = 1` and `p(s) ≥ 0`. The book's
argument (`1 + r` units of every AD security replicate the bond) is the `Σ p = 1` half. -/
theorem noArbitrage_iff [DecidableEq S] (p : S → ℝ) {r : ℝ} (hr : 0 < 1 + r) :
    NoArbitrage p r ↔ (∑ s, p s = 1 ∧ ∀ s, 0 ≤ p s) := by
  have hr0 : 1 + r ≠ 0 := hr.ne'
  constructor
  · intro h
    have h1 := h 1 (fun _ => -(1 + r)) (fun s => by simp [portfolioPayoff_eq])
    have h2 := h (-1) (fun _ => 1 + r) (fun s => by simp [portfolioPayoff_eq])
    have e1 : ∀ c : ℝ, ∑ s, p s / (1 + r) * (c * (1 + r)) = c * ∑ s, p s := fun c => by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun s _ => by field_simp
    simp only [portfolioCost] at h1 h2
    have e1' := e1 (-1)
    have e2' := e1 1
    simp only [neg_mul, one_mul] at e1' e2'
    rw [e1'] at h1
    rw [e2'] at h2
    refine ⟨by linarith, fun s => ?_⟩
    have h3 := h 0 (fun t => if t = s then 1 else 0) (fun t => by
      simp only [portfolioPayoff_eq, mul_zero, zero_add]
      split_ifs <;> norm_num)
    simp only [portfolioCost, mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, ↓reduceIte,
      zero_add] at h3
    exact (div_nonneg_iff.mp h3).elim (fun h => h.1) (fun h => absurd h.2 (not_le.mpr hr))
  · rintro ⟨hsum, hpos⟩ b B hB
    have : portfolioCost p r b B = ∑ s, p s / (1 + r) * portfolioPayoff r b B s := by
      simp only [portfolioCost, portfolioPayoff_eq, mul_add, Finset.sum_add_distrib]
      congr 1
      rw [show ∑ s, p s / (1 + r) * ((1 + r) * b) = ∑ s, p s * b from
        Finset.sum_congr rfl fun s _ => by field_simp, ← Finset.sum_mul, hsum, one_mul]
    rw [this]
    exact Finset.sum_nonneg fun s _ => mul_nonneg (div_nonneg (hpos s) hr.le) (hB s)

/-- Bonds are redundant, O&R §5.1.2, p. 272: when `Σ p(s) = 1`, a portfolio of `b` bonds and
AD holdings `B` has the same payoff and the same cost as the pure AD portfolio
`B + (1 + r)b`. -/
theorem bond_redundant [DecidableEq S] (p : S → ℝ) {r : ℝ} (hr : 1 + r ≠ 0) (hsum : ∑ s, p s = 1)
    (b : ℝ) (B : S → ℝ) :
    (∀ s, portfolioPayoff r b B s = portfolioPayoff r 0 (fun s => B s + (1 + r) * b) s) ∧
      portfolioCost p r b B = portfolioCost p r 0 (fun s => B s + (1 + r) * b) := by
  refine ⟨fun s => by simp only [portfolioPayoff_eq]; ring, ?_⟩
  simp only [portfolioCost, mul_add, Finset.sum_add_distrib, zero_add]
  rw [add_comm]
  congr 1
  rw [show ∑ s, p s / (1 + r) * ((1 + r) * b) = ∑ s, p s * b from
    Finset.sum_congr rfl fun s _ => by field_simp, ← Finset.sum_mul, hsum, one_mul]

/-! ## Budget constraints (§5.1.3, pp. 273–276) -/

/-- The budget constraints, O&R (2), (3) and (18), pp. 273–281: consumption `(C₁, C₂)` is
financed by some AD holdings `B₂` satisfying (2) and (3) iff it satisfies the intertemporal
budget constraint (18), `C₁ − Y₁ + Σ p(s)[C₂(s) − Y₂(s)]/(1+r) = 0`. -/
theorem budget_iff (p : S → ℝ) (r Y1 C1 : ℝ) (Y2 C2 : S → ℝ) :
    (∃ B2 : S → ℝ, ∑ s, p s / (1 + r) * B2 s = Y1 - C1 ∧ ∀ s, C2 s = Y2 s + B2 s) ↔
      C1 - Y1 + ∑ s, p s / (1 + r) * (C2 s - Y2 s) = 0 := by
  constructor
  · rintro ⟨B2, h2, h3⟩
    have : ∑ s, p s / (1 + r) * (C2 s - Y2 s) = ∑ s, p s / (1 + r) * B2 s :=
      Finset.sum_congr rfl fun s _ => by rw [h3 s]; ring
    rw [this, h2]; ring
  · intro h
    exact ⟨fun s => C2 s - Y2 s, by linarith, fun s => by ring⟩

/-- The intertemporal budget constraint in present-value form, O&R (4), p. 275:
(18) is equivalent to `C₁ + Σ p(s)C₂(s)/(1+r) = Y₁ + Σ p(s)Y₂(s)/(1+r)`. -/
theorem budget_pv_iff (p : S → ℝ) (r Y1 C1 : ℝ) (Y2 C2 : S → ℝ) :
    C1 - Y1 + ∑ s, p s / (1 + r) * (C2 s - Y2 s) = 0 ↔
      C1 + ∑ s, p s / (1 + r) * C2 s = Y1 + ∑ s, p s / (1 + r) * Y2 s := by
  simp only [mul_sub, Finset.sum_sub_distrib]
  constructor <;> intro h <;> linarith

/-! ## First-order conditions (§5.1.4, pp. 276–278) -/

/-- The bond Euler equation, O&R (8), p. 277: summing the AD first-order conditions (5),
`p(s)u′(C₁)/(1+r) = π(s)βu′(C₂(s))`, over states and using `Σ p(s) = 1` (O&R (7)) gives
`u′(C₁) = (1+r)βE[u′(C₂)]`. -/
theorem bond_euler (Ω : StateSpace S) (p : S → ℝ) {r : ℝ} (hr : 1 + r ≠ 0)
    (hsum : ∑ s, p s = 1) (β : ℝ) (du : ℝ → ℝ) (C1 : ℝ) (C2 : S → ℝ)
    (hfoc : ∀ s, p s / (1 + r) * du C1 = Ω.prob s * β * du (C2 s)) :
    du C1 = (1 + r) * β * Ω.expect (fun s => du (C2 s)) := by
  have h : ∑ s, p s / (1 + r) * du C1 = ∑ s, Ω.prob s * β * du (C2 s) :=
    Finset.sum_congr rfl fun s _ => hfoc s
  rw [← Finset.sum_mul, ← Finset.sum_div, hsum] at h
  have e : β * Ω.expect (fun s => du (C2 s)) = ∑ s, Ω.prob s * β * du (C2 s) := by
    simp only [StateSpace.expect, Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [mul_assoc, e, ← h]
  field_simp

/-- The marginal rate of substitution equals the relative price, O&R (6), p. 276:
`π(s)βu′(C₂(s))/u′(C₁) = p(s)/(1+r)`, from (5) when `u′(C₁) ≠ 0`. -/
theorem mrs_eq_price (Ω : StateSpace S) (p : S → ℝ) (r β : ℝ) (du : ℝ → ℝ) (C1 : ℝ)
    (C2 : S → ℝ) (hd : du C1 ≠ 0)
    (hfoc : ∀ s, p s / (1 + r) * du C1 = Ω.prob s * β * du (C2 s)) (s : S) :
    Ω.prob s * β * du (C2 s) / du C1 = p s / (1 + r) := by
  rw [← hfoc s]
  field_simp

/-- The across-state first-order condition, O&R (9), p. 277:
`π(s)u′(C₂(s))/[π(t)u′(C₂(t))] = p(s)/p(t)`, from (5) for states `s` and `t`. -/
theorem mrs_ratio_eq_price_ratio (Ω : StateSpace S) (p : S → ℝ) {r β : ℝ} (hr : 1 + r ≠ 0)
    (hβ : β ≠ 0) (du : ℝ → ℝ) (C1 : ℝ) (C2 : S → ℝ) (hd : du C1 ≠ 0)
    (hfoc : ∀ s, p s / (1 + r) * du C1 = Ω.prob s * β * du (C2 s)) (s t : S) :
    Ω.prob s * du (C2 s) / (Ω.prob t * du (C2 t)) = p s / p t := by
  have e : ∀ s, p s = (1 + r) * β * (Ω.prob s * du (C2 s)) / du C1 := fun s => by
    rw [eq_div_iff hd, show (1 + r) * β * (Ω.prob s * du (C2 s)) =
      (1 + r) * (Ω.prob s * β * du (C2 s)) by ring, ← hfoc s]
    field_simp
  rw [e s, e t]
  field_simp

/-- A differentiable concave function lies below its tangent lines (used for the sufficiency
of the first-order conditions (5), O&R §5.1.4, p. 276): if `u` is concave on `D` with
derivative `du x` at `x ∈ D`, then `u y ≤ u x + du x (y − x)` for `y ∈ D`. -/
theorem supergradient_of_concaveOn {D : Set ℝ} {u : ℝ → ℝ} (hconc : ConcaveOn ℝ D u)
    {x y d : ℝ} (hx : x ∈ D) (hy : y ∈ D) (hu : HasDerivAt u d x) :
    u y ≤ u x + d * (y - x) := by
  rcases lt_trichotomy x y with hxy | rfl | hxy
  · have h := hconc.slope_le_of_hasDerivAt hx hy hxy hu
    rw [slope_def_field, div_le_iff₀ (sub_pos.mpr hxy)] at h
    linarith
  · simp
  · have h := hconc.le_slope_of_hasDerivAt hy hx hxy hu
    rw [slope_def_field, le_div_iff₀ (sub_pos.mpr hxy)] at h
    linarith

/-- Expected lifetime utility (1) as a function of the AD holdings `B`, O&R p. 276:
`u(Y₁ − Σ p(s)B(s)/(1+r)) + Σ π(s)βu(Y₂(s) + B(s))`. -/
noncomputable def lifetimeUtility (Ω : StateSpace S) (u : ℝ → ℝ) (p : S → ℝ) (r β Y1 : ℝ)
    (Y2 B : S → ℝ) : ℝ :=
  u (Y1 - ∑ s, p s / (1 + r) * B s) + ∑ s, Ω.prob s * β * u (Y2 s + B s)

/-- Sufficiency of the first-order conditions (5), O&R p. 276 (implicit in the book): if `u` is
concave and differentiable on a convex set `D` of consumption levels, `β ≥ 0`, and the holdings
`B` satisfy (5), then `B` maximises expected utility (1) over all holdings `B'` whose
consumption stays in `D`. -/
theorem foc_sufficient (Ω : StateSpace S) {D : Set ℝ} {u du : ℝ → ℝ}
    (hconc : ConcaveOn ℝ D u) (hu : ∀ x ∈ D, HasDerivAt u (du x) x) (p : S → ℝ)
    {r β : ℝ} (hβ : 0 ≤ β) (Y1 : ℝ) (Y2 B B' : S → ℝ)
    (hC1 : Y1 - ∑ s, p s / (1 + r) * B s ∈ D) (hC2 : ∀ s, Y2 s + B s ∈ D)
    (hC1' : Y1 - ∑ s, p s / (1 + r) * B' s ∈ D) (hC2' : ∀ s, Y2 s + B' s ∈ D)
    (hfoc : ∀ s, p s / (1 + r) * du (Y1 - ∑ s, p s / (1 + r) * B s) =
      Ω.prob s * β * du (Y2 s + B s)) :
    lifetimeUtility Ω u p r β Y1 Y2 B' ≤ lifetimeUtility Ω u p r β Y1 Y2 B := by
  set C1 := Y1 - ∑ s, p s / (1 + r) * B s with hC1def
  have h1 := supergradient_of_concaveOn hconc hC1 hC1' (hu C1 hC1)
  have h2 : ∀ s, Ω.prob s * β * u (Y2 s + B' s) ≤
      Ω.prob s * β * (u (Y2 s + B s) + du (Y2 s + B s) * (B' s - B s)) := fun s => by
    have := supergradient_of_concaveOn hconc (hC2 s) (hC2' s) (hu _ (hC2 s))
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (Ω.prob_nonneg s) hβ)
    convert this using 3; ring
  have key : du C1 * ((Y1 - ∑ s, p s / (1 + r) * B' s) - C1) =
      -∑ s, Ω.prob s * β * du (Y2 s + B s) * (B' s - B s) := by
    rw [hC1def, show Y1 - ∑ s, p s / (1 + r) * B' s - (Y1 - ∑ s, p s / (1 + r) * B s) =
      -∑ s, p s / (1 + r) * (B' s - B s) by
        simp only [mul_sub, Finset.sum_sub_distrib]; ring, mul_neg, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun s _ => by rw [← hfoc s]; ring
  have hsum := Finset.sum_le_sum fun s (_ : s ∈ Finset.univ) => h2 s
  have e : ∑ s, Ω.prob s * β * (u (Y2 s + B s) + du (Y2 s + B s) * (B' s - B s)) =
      ∑ s, Ω.prob s * β * u (Y2 s + B s) +
        ∑ s, Ω.prob s * β * du (Y2 s + B s) * (B' s - B s) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun s _ => by ring
  simp only [lifetimeUtility]
  rw [e] at hsum
  linarith

/-! ## Full insurance and actuarially fair prices (§5.1.4, pp. 277–278) -/

/-- Full insurance iff actuarially fair prices, O&R (10), p. 277, for any number of states: if the
FOCs (5) hold with `Σ p(s) = 1`, `u′` strictly decreasing, `u′(C₁) ≠ 0`, `β > 0`, `1 + r > 0` and
every `π(s) > 0`, then date-2 consumption is the same in all states iff `p(s) = π(s)` for all
`s`. -/
theorem full_insurance_iff_fair (Ω : StateSpace S) (p : S → ℝ) {r β : ℝ} (hr : 0 < 1 + r)
    (hβ : 0 < β) (hsum : ∑ s, p s = 1) {du : ℝ → ℝ} (hanti : StrictAnti du) (C1 : ℝ)
    (C2 : S → ℝ) (hd : du C1 ≠ 0) (hπ : ∀ s, 0 < Ω.prob s)
    (hfoc : ∀ s, p s / (1 + r) * du C1 = Ω.prob s * β * du (C2 s)) :
    (∀ s t, C2 s = C2 t) ↔ ∀ s, p s = Ω.prob s := by
  have hk : du C1 / (1 + r) ≠ 0 := div_ne_zero hd hr.ne'
  constructor
  · intro hc s
    have key : ∀ t, p s * Ω.prob t = p t * Ω.prob s := fun t => by
      have hs := hfoc s
      have ht := hfoc t
      rw [← hc s t] at ht
      refine mul_right_cancel₀ hk ?_
      linear_combination Ω.prob t * hs - Ω.prob s * ht
    have := Finset.sum_congr rfl fun t (_ : t ∈ Finset.univ) => key t
    rwa [← Finset.mul_sum, Ω.prob_sum, mul_one, ← Finset.sum_mul, hsum, one_mul] at this
  · intro hp
    have e : ∀ s, du (C2 s) = du C1 / ((1 + r) * β) := fun s => by
      have h := hfoc s
      rw [hp s] at h
      have hπs := (hπ s).ne'
      field_simp at h ⊢
      linear_combination -h
    intro s t
    exact hanti.injective ((e s).trans (e t).symm)

/-- Full insurance iff actuarially fair relative prices for two given states, O&R (9)–(10),
p. 277: under the FOCs (5) with `u′ > 0` at the consumption points, `u′` strictly decreasing,
`β > 0`, `1 + r > 0` and `π > 0`, `C₂(s) = C₂(t)` iff `p(s)/p(t) = π(s)/π(t)`. -/
theorem full_insurance_iff_fair_ratio (Ω : StateSpace S) (p : S → ℝ) {r β : ℝ}
    (hr : 0 < 1 + r) (hβ : 0 < β) {du : ℝ → ℝ} (hanti : StrictAnti du) (C1 : ℝ) (C2 : S → ℝ)
    (hd : 0 < du C1) (hd2 : ∀ s, 0 < du (C2 s)) (hπ : ∀ s, 0 < Ω.prob s)
    (hfoc : ∀ s, p s / (1 + r) * du C1 = Ω.prob s * β * du (C2 s)) (s t : S) :
    C2 s = C2 t ↔ p s / p t = Ω.prob s / Ω.prob t := by
  have e : ∀ s, p s = (1 + r) * β * (Ω.prob s * du (C2 s)) / du C1 := fun s => by
    rw [eq_div_iff hd.ne', show (1 + r) * β * (Ω.prob s * du (C2 s)) =
      (1 + r) * (Ω.prob s * β * du (C2 s)) by ring, ← hfoc s]
    field_simp
  have hπt := (hπ t).ne'
  have hπs := (hπ s).ne'
  have hdt := (hd2 t).ne'
  rw [e s, e t]
  constructor
  · intro h
    rw [h]
    field_simp
  · intro h
    apply hanti.injective
    field_simp at h
    linear_combination h

/-! ## Risk aversion (§5.1.5, pp. 278–279) -/

/-- The CRRA version of (11), O&R pp. 278–279, in exact (not differential) form: if the FOCs (5)
hold with `u′(C) = C^{-ρ}`, `ρ > 0`, and all quantities positive, then
`log(C₂(t)/C₂(s)) = (1/ρ) log(p(s)/p(t)) + (1/ρ) log(π(t)/π(s))`; in particular `1/ρ` is the
elasticity of relative state consumption with respect to relative AD prices. -/
theorem crra_log_ratio (Ω : StateSpace S) (p : S → ℝ) {r β ρ C1 : ℝ} (C2 : S → ℝ)
    (hr : 0 < 1 + r) (hβ : 0 < β) (hρ : 0 < ρ) (hC1 : 0 < C1) (hC2 : ∀ s, 0 < C2 s)
    (hp : ∀ s, 0 < p s) (hπ : ∀ s, 0 < Ω.prob s)
    (hfoc : ∀ s, p s / (1 + r) * C1 ^ (-ρ) = Ω.prob s * β * C2 s ^ (-ρ)) (s t : S) :
    Real.log (C2 t / C2 s) =
      1 / ρ * Real.log (p s / p t) + 1 / ρ * Real.log (Ω.prob t / Ω.prob s) := by
  have L : ∀ s, Real.log (p s) - Real.log (1 + r) - ρ * Real.log C1 =
      Real.log (Ω.prob s) + Real.log β - ρ * Real.log (C2 s) := fun s => by
    have h := congrArg Real.log (hfoc s)
    have h1 := (hp s).ne'
    have h2 := (hπ s).ne'
    have h3 := (hC2 s).ne'
    rw [Real.log_mul (div_ne_zero h1 hr.ne') (Real.rpow_pos_of_pos hC1 _).ne',
      Real.log_div h1 hr.ne', Real.log_rpow hC1,
      Real.log_mul (mul_ne_zero h2 hβ.ne') (Real.rpow_pos_of_pos (hC2 s) _).ne',
      Real.log_mul h2 hβ.ne', Real.log_rpow (hC2 s)] at h
    linarith
  have Ls := L s
  have Lt := L t
  rw [Real.log_div (hC2 t).ne' (hC2 s).ne', Real.log_div (hp s).ne' (hp t).ne',
    Real.log_div (hπ t).ne' (hπ s).ne']
  have : ρ * (Real.log (C2 t) - Real.log (C2 s)) = (Real.log (p s) - Real.log (p t)) +
      (Real.log (Ω.prob t) - Real.log (Ω.prob s)) := by linarith
  field_simp
  linarith

/-- The Arrow–Pratt coefficient of relative risk aversion, O&R (12)–(13), pp. 278–279: for CRRA
utility `u(C) = C^{1−ρ}/(1−ρ)` (`ρ ≠ 1`) and `C > 0`, `u′(C) = C^{−ρ}`,
`u″(C) = −ρC^{−ρ−1}`, and `−Cu″(C)/u′(C) = ρ`. -/
theorem crra_arrow_pratt {ρ c : ℝ} (hρ : ρ ≠ 1) (hc : 0 < c) :
    HasDerivAt (fun x => x ^ (1 - ρ) / (1 - ρ)) (c ^ (-ρ)) c ∧
      HasDerivAt (fun x => x ^ (-ρ)) (-ρ * c ^ (-ρ - 1)) c ∧
      -(c * (-ρ * c ^ (-ρ - 1))) / c ^ (-ρ) = ρ := by
  have h1ρ : 1 - ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm hρ)
  refine ⟨?_, Real.hasDerivAt_rpow_const (Or.inl hc.ne'), ?_⟩
  · have h := (Real.hasDerivAt_rpow_const (p := 1 - ρ) (Or.inl hc.ne')).div_const (1 - ρ)
    refine HasDerivAt.congr_deriv h ?_
    rw [show 1 - ρ - 1 = -ρ by ring]
    field_simp
  · rw [Real.rpow_sub_one hc.ne']
    have : 0 < c ^ (-ρ) := Real.rpow_pos_of_pos hc _
    field_simp

/-! ## Log utility (§5.1.6, pp. 279–280) -/

/-- Log utility, the spending rule behind O&R (16), pp. 279–280: with `u′(C) = 1/C` the FOCs (5)
say `p(s)C₂(s)/(1+r) = π(s)βC₁`. -/
theorem log_state_spending_eq (Ω : StateSpace S) (p : S → ℝ) {r β C1 : ℝ} (C2 : S → ℝ)
    (hC1 : 0 < C1) (hC2 : ∀ s, 0 < C2 s)
    (hfoc : ∀ s, p s / (1 + r) * C1⁻¹ = Ω.prob s * β * (C2 s)⁻¹) (s : S) :
    p s / (1 + r) * C2 s = Ω.prob s * β * C1 := by
  have h := hfoc s
  have := (hC2 s).ne'
  field_simp at h
  linear_combination h

/-- Log-utility consumption demands, O&R (15)–(16) and footnote 9, p. 280: if the FOCs (5) hold
with `u′(C) = 1/C` and the budget (4) holds, then with `W₁ = Y₁ + Σ p(s)Y₂(s)/(1+r)`:
`C₁ = W₁/(1+β)`, `p(s)C₂(s)/(1+r) = π(s)βW₁/(1+β)`, and (if `p(s) > 0`)
`C₂(s) = π(s)(1+r)βW₁/((1+β)p(s))`. -/
theorem log_consumption_demands (Ω : StateSpace S) (p : S → ℝ) {r β C1 Y1 : ℝ}
    (C2 Y2 : S → ℝ) (hr : 0 < 1 + r) (hβ : 0 < β) (hC1 : 0 < C1) (hC2 : ∀ s, 0 < C2 s)
    (hfoc : ∀ s, p s / (1 + r) * C1⁻¹ = Ω.prob s * β * (C2 s)⁻¹)
    (hbud : C1 + ∑ s, p s / (1 + r) * C2 s = Y1 + ∑ s, p s / (1 + r) * Y2 s) :
    C1 = (Y1 + ∑ s, p s / (1 + r) * Y2 s) / (1 + β) ∧
      (∀ s, p s / (1 + r) * C2 s =
        Ω.prob s * β / (1 + β) * (Y1 + ∑ s, p s / (1 + r) * Y2 s)) ∧
      (∀ s, 0 < p s → C2 s =
        Ω.prob s * (1 + r) * β * (Y1 + ∑ s, p s / (1 + r) * Y2 s) / ((1 + β) * p s)) := by
  have hsp := log_state_spending_eq Ω p C2 hC1 hC2 hfoc
  have hsum : ∑ s, p s / (1 + r) * C2 s = β * C1 := by
    rw [Finset.sum_congr rfl fun s _ => hsp s, ← Finset.sum_mul, ← Finset.sum_mul,
      Ω.prob_sum]
    ring
  have hC1eq : C1 = (Y1 + ∑ s, p s / (1 + r) * Y2 s) / (1 + β) := by
    rw [eq_div_iff (by positivity), ← hbud, hsum]; ring
  refine ⟨hC1eq, fun s => by rw [hsp s, hC1eq]; field_simp, fun s hps => ?_⟩
  have h := hsp s
  rw [hC1eq] at h
  generalize Y1 + ∑ s, p s / (1 + r) * Y2 s = W at h ⊢
  rw [eq_div_iff (by positivity)]
  field_simp at h
  linear_combination h

/-- The log-utility current account, O&R (17), p. 280:
`CA₁ = Y₁ − C₁ = βY₁/(1+β) − [Σ p(s)Y₂(s)/(1+r)]/(1+β)`. -/
theorem log_current_account (Ω : StateSpace S) (p : S → ℝ) {r β C1 Y1 : ℝ}
    (C2 Y2 : S → ℝ) (hr : 0 < 1 + r) (hβ : 0 < β) (hC1 : 0 < C1) (hC2 : ∀ s, 0 < C2 s)
    (hfoc : ∀ s, p s / (1 + r) * C1⁻¹ = Ω.prob s * β * (C2 s)⁻¹)
    (hbud : C1 + ∑ s, p s / (1 + r) * C2 s = Y1 + ∑ s, p s / (1 + r) * Y2 s) :
    Y1 - C1 = β / (1 + β) * Y1 - 1 / (1 + β) * ∑ s, p s / (1 + r) * Y2 s := by
  rw [(log_consumption_demands Ω p C2 Y2 hr hβ hC1 hC2 hfoc hbud).1]
  field_simp
  ring

/-- O&R footnote 10, p. 280: the world-market value of date-2 output equals its expected value,
`Σ p(s)Y₂(s) = E[Y₂]`, for every output vector `Y₂` iff prices are actuarially fair, `p = π`. -/
theorem value_eq_expectation_iff (Ω : StateSpace S) (p : S → ℝ) :
    (∀ Y2 : S → ℝ, ∑ s, p s * Y2 s = Ω.expect Y2) ↔ ∀ s, p s = Ω.prob s := by
  classical
  constructor
  · intro h s
    simpa [StateSpace.expect] using h (fun t => if t = s then 1 else 0)
  · intro h Y2
    simp [StateSpace.expect, h]

/-- O&R footnote 10, p. 280, for two states and a given output vector: if `p` and `π` are
probability vectors and `Y₂(1) ≠ Y₂(2)`, then `p(1)Y₂(1) + p(2)Y₂(2) = E[Y₂]` iff
`p = π`. (With `Y₂(1) = Y₂(2)` the equality holds at any prices.) -/
theorem value_eq_expectation_two_iff {p1 p2 π1 π2 Ya Yb : ℝ} (hp : p1 + p2 = 1)
    (hπ : π1 + π2 = 1) (hY : Ya ≠ Yb) :
    p1 * Ya + p2 * Yb = π1 * Ya + π2 * Yb ↔ p1 = π1 ∧ p2 = π2 := by
  constructor
  · intro h
    have h' : (p1 - π1) * (Ya - Yb) = 0 := by linear_combination h + Yb * hπ - Yb * hp
    rcases mul_eq_zero.mp h' with h1 | h1
    · exact ⟨by linarith, by linarith⟩
    · exact absurd (sub_eq_zero.mp h1) hY
  · rintro ⟨rfl, rfl⟩
    rfl

/-! ## Appendix 5B: comparative advantage and gross flows (pp. 337–340) -/

/-- The "current-account autarky" interest rate, O&R (78), p. 338, for any number of states: if
the country consumes `C₁ = Y₁` and `C₂(s) = π(s)V/p(s)` with `V = Σ p(s)Y₂(s)`, and the gross
rate `R = 1 + r^CA` satisfies the log-utility bond Euler equation (8),
`1/Y₁ = RβE[1/C₂]`, then `R = V/(βY₁)`. -/
theorem rCA_formula (Ω : StateSpace S) (p : S → ℝ) {β Y1 R : ℝ} (Y2 : S → ℝ) (hβ : 0 < β)
    (hY1 : 0 < Y1) (hp : ∀ s, 0 < p s) (hπ : ∀ s, 0 < Ω.prob s) (hsum : ∑ s, p s = 1)
    (hV : 0 < ∑ s, p s * Y2 s)
    (hE : Y1⁻¹ = R * β * Ω.expect (fun s => (Ω.prob s * (∑ t, p t * Y2 t) / p s)⁻¹)) :
    R = (∑ s, p s * Y2 s) / (β * Y1) := by
  have hE' : Ω.expect (fun s => (Ω.prob s * (∑ t, p t * Y2 t) / p s)⁻¹) =
      (∑ s, p s * Y2 s)⁻¹ := by
    simp only [StateSpace.expect]
    rw [Finset.sum_congr rfl fun s _ => show Ω.prob s * (Ω.prob s * (∑ t, p t * Y2 t) / p s)⁻¹
      = p s * (∑ t, p t * Y2 t)⁻¹ by
        have := (hπ s).ne'; have := (hp s).ne'; field_simp, ← Finset.sum_mul, hsum, one_mul]
  rw [hE'] at hE
  rw [eq_div_iff (by positivity)]
  field_simp at hE
  linear_combination -hE

/-- The autarky interest rate, O&R (79), p. 338: if `R = 1 + r^A` satisfies the log-utility bond
Euler equation (8) at the endowment, `1/Y₁ = RβE[1/Y₂]`, then `R = [βY₁E(1/Y₂)]⁻¹`
(for two states: `R = (1/(βY₁))[π(1)/Y₂(1) + π(2)/Y₂(2)]⁻¹`). -/
theorem rA_formula (Ω : StateSpace S) {β Y1 R : ℝ} (Y2 : S → ℝ) (hY1 : Y1 ≠ 0)
    (hE : Y1⁻¹ = R * β * Ω.expect (fun s => (Y2 s)⁻¹)) :
    R = (β * Y1 * Ω.expect (fun s => (Y2 s)⁻¹))⁻¹ := by
  have hne : Ω.expect (fun s => (Y2 s)⁻¹) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hE
    exact inv_ne_zero hY1 hE
  have h1 : R * (β * Y1 * Ω.expect (fun s => (Y2 s)⁻¹)) = 1 := by
    rw [show R * (β * Y1 * Ω.expect (fun s => (Y2 s)⁻¹)) =
      (R * β * Ω.expect (fun s => (Y2 s)⁻¹)) * Y1 by ring, ← hE, inv_mul_cancel₀ hY1]
  exact eq_inv_of_mul_eq_one_left h1

/-- The current account has the sign of `r − r^CA`, O&R Appendix 5B and footnote 51, p. 338,
for any `β(1+r)`: with `V = Σ p(s)Y₂(s)` and `1 + r^CA = V/(βY₁)`, the log-utility current
account (17) equals `βY₁(r − r^CA)/((1+β)(1+r))`. -/
theorem current_account_eq_mul_rCA {β Y1 V r rCA : ℝ} (hβ : 0 < β) (hY1 : 0 < Y1)
    (hr : 0 < 1 + r) (hCA : 1 + rCA = V / (β * Y1)) :
    β / (1 + β) * Y1 - 1 / (1 + β) * (V / (1 + r)) =
      β * Y1 / ((1 + β) * (1 + r)) * (r - rCA) := by
  have hV : V = β * Y1 * (1 + rCA) := by rw [hCA]; field_simp
  rw [hV]
  field_simp
  ring

/-- Sign of the current account, O&R footnote 51, p. 338: `CA₁ > 0` iff `r > r^CA` and
`CA₁ < 0` iff `r < r^CA` (log utility, any `β(1+r)`). -/
theorem current_account_sign_iff {β Y1 V r rCA : ℝ} (hβ : 0 < β) (hY1 : 0 < Y1)
    (hr : 0 < 1 + r) (hCA : 1 + rCA = V / (β * Y1)) :
    (0 < β / (1 + β) * Y1 - 1 / (1 + β) * (V / (1 + r)) ↔ rCA < r) ∧
      (β / (1 + β) * Y1 - 1 / (1 + β) * (V / (1 + r)) < 0 ↔ r < rCA) := by
  rw [current_account_eq_mul_rCA hβ hY1 hr hCA]
  have hk : 0 < β * Y1 / ((1 + β) * (1 + r)) := by positivity
  constructor
  · rw [mul_pos_iff_of_pos_left hk, sub_pos]
  · constructor
    · intro h
      by_contra h'
      push Not at h'
      have := mul_nonneg hk.le (sub_nonneg.mpr h')
      linarith
    · intro h
      have := mul_neg_of_pos_of_neg hk (sub_neg.mpr h)
      linarith

/-- The sign of `CA₁` is NOT that of `r − r^A`, O&R p. 338 ("not `r − r^A`"): a
numerical case with `π = (1/2, 1/2)`, `Y₁ = 1`, `Y₂ = (1, 3)`, `β = 1`, `p = (1/10, 9/10)` and
`r = 1`. The autarky rate (79) is `r^A = 1/2 < r`, yet the current account (17) is
`1/2 − 2.8/4 = −1/5 < 0`. -/
theorem current_account_sign_not_autarky_rate :
    (1 : ℝ) / (1 * 1 * ((1 / 2) / 1 + (1 / 2) / 3)) - 1 < 1 ∧
      (1 : ℝ) / (1 + 1) * 1 - 1 / (1 + 1) * (((1 / 10) * 1 + (9 / 10) * 3) / (1 + 1)) < 0 := by
  norm_num

/-- No output uncertainty, O&R footnote 50, p. 338: if `Y₂(1) = Y₂(2) = Y₂`, `p` and `π` are
probability vectors, then `1 + r^A = [βY₁(π(1)/Y₂ + π(2)/Y₂)]⁻¹` equals
`1 + r^CA = (p(1)Y₂ + p(2)Y₂)/(βY₁)`, and the current account (17) is
`CA₁ = (Y₂/(1+β))[1/(1+r^A) − 1/(1+r)]`, where `1/(1+r^A) = βY₁(π(1)/Y₂ + π(2)/Y₂)`. -/
theorem no_output_risk {π1 π2 p1 p2 β Y1 Y2 r : ℝ} (hπ : π1 + π2 = 1) (hp : p1 + p2 = 1)
    (hβ : 0 < β) (hY1 : 0 < Y1) (hY2 : 0 < Y2) (hr : 0 < 1 + r) :
    (β * Y1 * (π1 / Y2 + π2 / Y2))⁻¹ = (p1 * Y2 + p2 * Y2) / (β * Y1) ∧
      β / (1 + β) * Y1 - 1 / (1 + β) * ((p1 * Y2 + p2 * Y2) / (1 + r)) =
        Y2 / (1 + β) * ((β * Y1 * (π1 / Y2 + π2 / Y2)) - (1 + r)⁻¹) := by
  have e1 : π1 / Y2 + π2 / Y2 = 1 / Y2 := by rw [← add_div, hπ]
  have e2 : p1 * Y2 + p2 * Y2 = Y2 := by rw [← add_mul, hp, one_mul]
  rw [e1, e2]
  constructor
  · field_simp
  · field_simp

/-- Log-utility autarky prices, O&R (80), p. 338: if the FOC (5) holds at the endowment
(`C₁ = Y₁`, `C₂ = Y₂`) with `u′(C) = 1/C`, the autarky AD prices are
`p^A(s)/(1+r^A) = π(s)βY₁/Y₂(s)`; hence `p^A(s)/p^A(t) = [π(s)/Y₂(s)]/[π(t)/Y₂(t)]`
(O&R p. 339). -/
theorem autarky_prices_log (Ω : StateSpace S) (pA : S → ℝ) {RA β Y1 : ℝ} (Y2 : S → ℝ)
    (hRA : 0 < RA) (hβ : 0 < β) (hY1 : 0 < Y1) (hY2 : ∀ s, 0 < Y2 s)
    (hπ : ∀ s, 0 < Ω.prob s)
    (hfoc : ∀ s, pA s / RA * Y1⁻¹ = Ω.prob s * β * (Y2 s)⁻¹) :
    (∀ s, pA s / RA = Ω.prob s * β * Y1 / Y2 s) ∧
      ∀ s t, pA s / pA t = (Ω.prob s / Y2 s) / (Ω.prob t / Y2 t) := by
  have e : ∀ s, pA s / RA = Ω.prob s * β * Y1 / Y2 s := fun s => by
    have h := hfoc s
    have := (hY2 s).ne'
    field_simp at h ⊢
    linear_combination h
  refine ⟨e, fun s t => ?_⟩
  have es : pA s = RA * (Ω.prob s * β * Y1 / Y2 s) := by rw [← e s]; field_simp
  have et : pA t = RA * (Ω.prob t * β * Y1 / Y2 t) := by rw [← e t]; field_simp
  have := (hY2 s).ne'
  have := (hY2 t).ne'
  have := (hπ t).ne'
  rw [es, et]
  field_simp

/-- The current account in terms of autarky and world AD prices, O&R (81), p. 339, for any
number of states: if the autarky prices `q^A(s) = p^A(s)/(1+r^A)` satisfy the log FOC at the
endowment (so (80) holds) and `Σ π(s) = 1`, then the log-utility current account (17) equals
`Σ_s (Y₂(s)/(1+β))[q^A(s) − p(s)/(1+r)]`. -/
theorem current_account_autarky_prices (Ω : StateSpace S) (p qA : S → ℝ) {r β Y1 : ℝ}
    (Y2 : S → ℝ) (hβ : 0 < β) (hY2 : ∀ s, 0 < Y2 s)
    (hfoc : ∀ s, qA s * Y1⁻¹ = Ω.prob s * β * (Y2 s)⁻¹) (hY1 : 0 < Y1) :
    β / (1 + β) * Y1 - 1 / (1 + β) * ∑ s, p s / (1 + r) * Y2 s =
      ∑ s, Y2 s / (1 + β) * (qA s - p s / (1 + r)) := by
  have e : ∀ s, Y2 s / (1 + β) * (qA s - p s / (1 + r)) =
      Ω.prob s * (β * Y1 / (1 + β)) - 1 / (1 + β) * (p s / (1 + r) * Y2 s) := fun s => by
    have h := hfoc s
    have := (hY2 s).ne'
    have hq : qA s = Ω.prob s * β * Y1 / Y2 s := by
      field_simp at h ⊢
      linear_combination h
    rw [hq]
    field_simp
  rw [Finset.sum_congr rfl fun s _ => e s, Finset.sum_sub_distrib, ← Finset.sum_mul,
    Ω.prob_sum, ← Finset.mul_sum]
  ring

/-- Gross asset flows with a balanced current account, O&R Appendix 5B.2, pp. 339–340: two
states, log utility, `C₁ = Y₁` and `r = r^CA`, i.e. `βY₁(1+r) = V = p(1)Y₂(1) + p(2)Y₂(2)`. If
the state FOCs (5) hold, then `C₂(s) = π(s)V/p(s)` and, writing `p^A(1)/p^A(2) =
[π(1)/Y₂(1)]/[π(2)/Y₂(2)]` (from (80)),
`B₂(1) = (p(2)/p(1))π(2)Y₂(1)[p^A(1)/p^A(2) − p(1)/p(2)]` and
`B₂(2) = −π(2)Y₂(1)[p^A(1)/p^A(2) − p(1)/p(2)]`. -/
theorem gross_flows_balanced {π1 π2 p1 p2 β Y1 Y21 Y22 r C21 C22 : ℝ} (hπ : π1 + π2 = 1)
    (hπ1 : 0 < π1) (hπ2 : 0 < π2) (hp1 : 0 < p1) (hp2 : 0 < p2) (hY1 : 0 < Y1)
    (hY21 : 0 < Y21) (hr : 0 < 1 + r) (hC21 : 0 < C21) (hC22 : 0 < C22)
    (hCA : β * Y1 * (1 + r) = p1 * Y21 + p2 * Y22)
    (hfoc1 : p1 / (1 + r) * Y1⁻¹ = π1 * β * C21⁻¹)
    (hfoc2 : p2 / (1 + r) * Y1⁻¹ = π2 * β * C22⁻¹) :
    C21 = π1 * (p1 * Y21 + p2 * Y22) / p1 ∧ C22 = π2 * (p1 * Y21 + p2 * Y22) / p2 ∧
      C21 - Y21 = p2 / p1 * π2 * Y21 * ((π1 / Y21) / (π2 / Y22) - p1 / p2) ∧
      C22 - Y22 = -(π2 * Y21 * ((π1 / Y21) / (π2 / Y22) - p1 / p2)) := by
  have e1 : C21 = π1 * (p1 * Y21 + p2 * Y22) / p1 := by
    rw [← hCA]
    field_simp at hfoc1 ⊢
    linear_combination hfoc1
  have e2 : C22 = π2 * (p1 * Y21 + p2 * Y22) / p2 := by
    rw [← hCA]
    field_simp at hfoc2 ⊢
    linear_combination hfoc2
  refine ⟨e1, e2, ?_, ?_⟩
  · obtain rfl : π1 = 1 - π2 := by linarith
    rw [e1]
    field_simp
    ring
  · obtain rfl : π1 = 1 - π2 := by linarith
    rw [e2]
    field_simp
    ring

/-- Gross AD purchases with an unbalanced current account, O&R Exercise 1, p. 345: two states,
log utility, FOCs (5) and budget (4). With `CA₁ = Y₁ − C₁`, `B₂(s) = C₂(s) − Y₂(s)` and
`p^A(1)/p^A(2) = [π(1)/Y₂(1)]/[π(2)/Y₂(2)]` (from (80)),
`p(1)B₂(1)/(1+r) = (p(2)π(2)Y₂(1)/(1+r))[p^A(1)/p^A(2) − p(1)/p(2)] + π(1)CA₁` and
`p(2)B₂(2)/(1+r) = −(p(2)π(2)Y₂(1)/(1+r))[p^A(1)/p^A(2) − p(1)/p(2)] + π(2)CA₁`. -/
theorem exercise1_gross_purchases {π1 π2 p1 p2 β C1 Y1 Y21 Y22 r C21 C22 : ℝ}
    (hπ : π1 + π2 = 1) (hπ2 : 0 < π2) (hp2 : 0 < p2) (hY21 : 0 < Y21) (hY22 : 0 < Y22)
    (hr : 0 < 1 + r) (hC1 : 0 < C1) (hC21 : 0 < C21) (hC22 : 0 < C22)
    (hfoc1 : p1 / (1 + r) * C1⁻¹ = π1 * β * C21⁻¹)
    (hfoc2 : p2 / (1 + r) * C1⁻¹ = π2 * β * C22⁻¹)
    (hbud : C1 + p1 / (1 + r) * C21 + p2 / (1 + r) * C22 =
      Y1 + p1 / (1 + r) * Y21 + p2 / (1 + r) * Y22) :
    p1 / (1 + r) * (C21 - Y21) =
        p2 * π2 * Y21 / (1 + r) * ((π1 / Y21) / (π2 / Y22) - p1 / p2) + π1 * (Y1 - C1) ∧
      p2 / (1 + r) * (C22 - Y22) =
        -(p2 * π2 * Y21 / (1 + r) * ((π1 / Y21) / (π2 / Y22) - p1 / p2)) +
          π2 * (Y1 - C1) := by
  have hr0 := hr.ne'
  have := hC1.ne'
  have s1 : p1 / (1 + r) * C21 = π1 * β * C1 := by
    have := hC21.ne'
    field_simp at hfoc1 ⊢
    linear_combination hfoc1
  have s2 : p2 / (1 + r) * C22 = π2 * β * C1 := by
    have := hC22.ne'
    field_simp at hfoc2 ⊢
    linear_combination hfoc2
  have hC1eq : C1 * (1 + β) = Y1 + p1 / (1 + r) * Y21 + p2 / (1 + r) * Y22 := by
    linear_combination hbud - s1 - s2 - β * C1 * hπ
  have t : p2 * π2 * Y21 / (1 + r) * ((π1 / Y21) / (π2 / Y22) - p1 / p2) =
      (π1 * p2 * Y22 - π2 * p1 * Y21) / (1 + r) := by
    have := hπ2.ne'
    have := hp2.ne'
    have := hY21.ne'
    have := hY22.ne'
    field_simp
  rw [t]
  constructor
  · linear_combination s1 + π1 * hC1eq + (p1 * Y21 / (1 + r)) * hπ
  · linear_combination s2 + π2 * hC1eq + (p2 * Y22 / (1 + r)) * hπ

/-! ## Exercise 3: quadratic utility, incomplete and complete markets (pp. 345–346) -/

/-- Quadratic period utility `u(C) = C − a₀C²/2`, O&R Exercise 3, p. 345. -/
noncomputable def quadU (a0 c : ℝ) : ℝ := c - a0 / 2 * c ^ 2

/-- Lifetime utility in Exercise 3 (bonds only, `β = 1/(1+r)`), O&R p. 345, as a function of
`C₁`, with `A = (1+r)B₁ + Y₁`: date-2 consumption is `C₂(s) = (1+r)(A − C₁) + Y₂(s)`, and
`U = u(C₁) + (1+r)⁻¹E[u(C₂)]`. -/
noncomputable def quadLifetime (Ω : StateSpace S) (a0 r A : ℝ) (Y2 : S → ℝ) (C1 : ℝ) : ℝ :=
  quadU a0 C1 + (1 + r)⁻¹ * Ω.expect (fun s => quadU a0 ((1 + r) * (A - C1) + Y2 s))

/-- The certainty-equivalent consumption level of Exercise 3(a), O&R p. 346:
`C₁* = ((1+r)/(2+r))[A + E(Y₂)/(1+r)]` with `A = (1+r)B₁ + Y₁`. -/
noncomputable def quadCstar (Ω : StateSpace S) (r A : ℝ) (Y2 : S → ℝ) : ℝ :=
  (1 + r) / (2 + r) * (A + Ω.expect Y2 / (1 + r))

/-- Expected quadratic utility of `k + Y₂` in terms of the first two moments of `Y₂`
(used for Exercise 3, O&R p. 345). -/
theorem quad_expect (Ω : StateSpace S) (a0 k : ℝ) (Y2 : S → ℝ) :
    Ω.expect (fun s => quadU a0 (k + Y2 s)) =
      k + Ω.expect Y2 - a0 / 2 * (k ^ 2 + 2 * k * Ω.expect Y2 +
        Ω.expect (fun s => Y2 s ^ 2)) := by
  simp only [StateSpace.expect, quadU]
  rw [Finset.sum_congr rfl fun s _ => show Ω.prob s * (k + Y2 s - a0 / 2 * (k + Y2 s) ^ 2) =
    Ω.prob s * (k - a0 / 2 * k ^ 2) + (1 - a0 * k) * (Ω.prob s * Y2 s) +
      (-(a0 / 2)) * (Ω.prob s * Y2 s ^ 2) by ring, Finset.sum_add_distrib,
    Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, ← Finset.mul_sum, Ω.prob_sum]
  ring

/-- Exercise 3(a), O&R p. 346, certainty equivalence: with `β(1+r) = 1` and bonds only, the
Euler equation `u′(C₁) = E[u′(C₂)]` for quadratic utility (`a₀ ≠ 0`) holds iff
`C₁ = ((1+r)/(2+r))[(1+r)B₁ + Y₁ + E(Y₂)/(1+r)]`, the same as under certainty with `Y₂`
replaced by `E(Y₂)`. -/
theorem quad_euler_iff (Ω : StateSpace S) {a0 r : ℝ} (ha0 : a0 ≠ 0) (hr : 0 < 1 + r)
    (A C1 : ℝ) (Y2 : S → ℝ) :
    1 - a0 * C1 = Ω.expect (fun s => 1 - a0 * ((1 + r) * (A - C1) + Y2 s)) ↔
      C1 = quadCstar Ω r A Y2 := by
  have e : Ω.expect (fun s => 1 - a0 * ((1 + r) * (A - C1) + Y2 s)) =
      1 - a0 * ((1 + r) * (A - C1) + Ω.expect Y2) := by
    simp only [StateSpace.expect]
    rw [Finset.sum_congr rfl fun s _ => show Ω.prob s * (1 - a0 * ((1 + r) * (A - C1) + Y2 s))
      = Ω.prob s * (1 - a0 * ((1 + r) * (A - C1))) + (-a0) * (Ω.prob s * Y2 s) by ring,
      Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, Ω.prob_sum]
    ring
  have h2r : (2 + r) ≠ 0 := by linarith
  rw [e, quadCstar]
  constructor
  · intro h
    have h' : C1 = (1 + r) * (A - C1) + Ω.expect Y2 :=
      mul_left_cancel₀ ha0 (by linarith)
    field_simp
    linarith
  · intro h
    have h' : C1 = (1 + r) * (A - C1) + Ω.expect Y2 := by
      rw [h]; field_simp; ring
    rw [← h']

/-- Exercise 3(a), O&R p. 346: lifetime utility is an exact concave quadratic around `C₁*`,
`U(C₁) = U(C₁*) − a₀(2+r)(C₁ − C₁*)²/2`; so `C₁*` is the unique global maximiser when the
nonnegativity constraints are ignored. -/
theorem quad_lifetime_eq (Ω : StateSpace S) {r : ℝ} (a0 : ℝ) (hr : 0 < 1 + r) (A C1 : ℝ)
    (Y2 : S → ℝ) :
    quadLifetime Ω a0 r A Y2 C1 = quadLifetime Ω a0 r A Y2 (quadCstar Ω r A Y2) -
      a0 * (2 + r) / 2 * (C1 - quadCstar Ω r A Y2) ^ 2 := by
  have h2r : (2 + r) ≠ 0 := by linarith
  have hr0 := hr.ne'
  simp only [quadLifetime, quad_expect, quadCstar]
  simp only [quadU]
  field_simp
  ring

/-- Exercise 3(a), O&R p. 346: the implied date-2 consumption is
`C₂(s) = C₁* + Y₂(s) − E(Y₂)`, so `E[C₂] = C₁*` (consumption is a martingale). -/
theorem quad_C2_at_optimum (Ω : StateSpace S) {r : ℝ} (hr : 0 < 1 + r) (A : ℝ) (Y2 : S → ℝ)
    (s : S) :
    (1 + r) * (A - quadCstar Ω r A Y2) + Y2 s = quadCstar Ω r A Y2 + (Y2 s - Ω.expect Y2) := by
  have h2r : (2 + r) ≠ 0 := by linarith
  simp only [quadCstar]
  field_simp
  ring

/-- Exercise 3(b), O&R p. 346, feasibility: if state `s₀` has the lowest output, the date-2
nonnegativity constraints `C₂(s) ≥ 0` for all `s` are equivalent to the single constraint
`C₁ ≤ (1+r)B₁ + Y₁ + Y₂(s₀)/(1+r)`. -/
theorem quad_feasible_iff {T : Type} {r : ℝ} (hr : 0 < 1 + r) (A C1 : ℝ) (Y2 : T → ℝ)
    (s0 : T) (hmin : ∀ s, Y2 s0 ≤ Y2 s) :
    (∀ s, 0 ≤ (1 + r) * (A - C1) + Y2 s) ↔ C1 ≤ A + Y2 s0 / (1 + r) := by
  have e : (1 + r) * (A - C1) + Y2 s0 = (1 + r) * (A + Y2 s0 / (1 + r) - C1) := by
    field_simp; ring
  have key : 0 ≤ (1 + r) * (A - C1) + Y2 s0 ↔ C1 ≤ A + Y2 s0 / (1 + r) := by
    rw [e]
    constructor
    · intro h
      have := (mul_nonneg_iff_of_pos_left hr).mp h
      linarith
    · intro h
      exact mul_nonneg hr.le (by linarith)
  constructor
  · intro h
    exact key.mp (h s0)
  · intro h s
    linarith [key.mpr h, hmin s]

/-- Exercise 3(b), O&R p. 346, nonbinding case: if `(1+r)B₁ + Y₁ + ((2+r)/(1+r))Y₂(s₀) ≥ E(Y₂)`
(with `s₀` the lowest-output state and `a₀ ≥ 0`), then `C₁*` of part (a) satisfies the
nonnegativity constraints and maximises lifetime utility among all feasible `C₁`. -/
theorem quad_nonbinding (Ω : StateSpace S) {a0 r : ℝ} (ha0 : 0 ≤ a0) (hr : 0 < 1 + r)
    (A : ℝ) (Y2 : S → ℝ) (s0 : S) (hmin : ∀ s, Y2 s0 ≤ Y2 s)
    (hcond : Ω.expect Y2 ≤ A + (2 + r) / (1 + r) * Y2 s0) :
    (∀ s, 0 ≤ (1 + r) * (A - quadCstar Ω r A Y2) + Y2 s) ∧
      ∀ C1, quadLifetime Ω a0 r A Y2 C1 ≤ quadLifetime Ω a0 r A Y2 (quadCstar Ω r A Y2) := by
  have h2r : 0 < 2 + r := by linarith
  refine ⟨(quad_feasible_iff hr A _ Y2 s0 hmin).mpr ?_, fun C1 => ?_⟩
  · have hy : (2 + r) / (1 + r) * Y2 s0 = (2 + r) * (Y2 s0 / (1 + r)) := by ring
    have hm : Ω.expect Y2 = (1 + r) * (Ω.expect Y2 / (1 + r)) := by field_simp
    rw [hy] at hcond
    rw [hm] at hcond
    simp only [quadCstar]
    rw [div_mul_eq_mul_div, div_le_iff₀ h2r]
    linarith
  · rw [quad_lifetime_eq Ω a0 hr A C1 Y2]
    have : 0 ≤ a0 * (2 + r) / 2 * (C1 - quadCstar Ω r A Y2) ^ 2 := by positivity
    linarith

/-- Exercise 3(b), O&R p. 346, binding case (precautionary saving): if
`(1+r)B₁ + Y₁ + ((2+r)/(1+r))Y₂(s₀) < E(Y₂)` (with `s₀` the lowest-output state, `a₀ > 0`),
then the optimum is the corner `C₁ = (1+r)B₁ + Y₁ + Y₂(s₀)/(1+r)` — the book prints "`C_t`",
a typo for `C₁` — which lies strictly below `C₁*`, maximises lifetime utility over the feasible
set, and violates the bond Euler equation: `u′(C₁) > E[u′(C₂)]` (the Kuhn–Tucker multiplier on
the nonnegativity constraint is positive). -/
theorem quad_binding (Ω : StateSpace S) {a0 r : ℝ} (ha0 : 0 < a0) (hr : 0 < 1 + r)
    (A : ℝ) (Y2 : S → ℝ) (s0 : S) (hmin : ∀ s, Y2 s0 ≤ Y2 s)
    (hcond : A + (2 + r) / (1 + r) * Y2 s0 < Ω.expect Y2) :
    A + Y2 s0 / (1 + r) < quadCstar Ω r A Y2 ∧
      (∀ s, 0 ≤ (1 + r) * (A - (A + Y2 s0 / (1 + r))) + Y2 s) ∧
      (∀ C1, (∀ s, 0 ≤ (1 + r) * (A - C1) + Y2 s) →
        quadLifetime Ω a0 r A Y2 C1 ≤ quadLifetime Ω a0 r A Y2 (A + Y2 s0 / (1 + r))) ∧
      Ω.expect (fun s => 1 - a0 * ((1 + r) * (A - (A + Y2 s0 / (1 + r))) + Y2 s)) <
        1 - a0 * (A + Y2 s0 / (1 + r)) := by
  have h2r : 0 < 2 + r := by linarith
  have hr0 := hr.ne'
  set Cb := A + Y2 s0 / (1 + r) with hCb
  set Cs := quadCstar Ω r A Y2 with hCs
  have hlt : Cb < Cs := by
    have hy : (2 + r) / (1 + r) * Y2 s0 = (2 + r) * (Y2 s0 / (1 + r)) := by ring
    have hm : Ω.expect Y2 = (1 + r) * (Ω.expect Y2 / (1 + r)) := by field_simp
    rw [hy] at hcond
    rw [hm] at hcond
    rw [hCb, hCs, quadCstar, div_mul_eq_mul_div, lt_div_iff₀ h2r]
    linarith
  refine ⟨hlt, (quad_feasible_iff hr A Cb Y2 s0 hmin).mpr le_rfl, fun C1 hC1 => ?_, ?_⟩
  · have hle := (quad_feasible_iff hr A C1 Y2 s0 hmin).mp hC1
    rw [quad_lifetime_eq Ω a0 hr A C1 Y2, quad_lifetime_eq Ω a0 hr A Cb Y2, ← hCs]
    have h1 : (Cb - Cs) ^ 2 ≤ (C1 - Cs) ^ 2 := by nlinarith
    have : 0 ≤ a0 * (2 + r) / 2 := by positivity
    nlinarith
  · have e : Ω.expect (fun s => 1 - a0 * ((1 + r) * (A - Cb) + Y2 s)) =
        1 - a0 * ((1 + r) * (A - Cb) + Ω.expect Y2) := by
      simp only [StateSpace.expect]
      rw [Finset.sum_congr rfl fun s _ => show Ω.prob s * (1 - a0 * ((1 + r) * (A - Cb) + Y2 s))
        = Ω.prob s * (1 - a0 * ((1 + r) * (A - Cb))) + (-a0) * (Ω.prob s * Y2 s) by ring,
        Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, Ω.prob_sum]
      ring
    have hstar : Cs = (1 + r) * (A - Cs) + Ω.expect Y2 := by
      rw [hCs, quadCstar]; field_simp; ring
    rw [e]
    have : Cb < (1 + r) * (A - Cb) + Ω.expect Y2 := by nlinarith
    nlinarith

/-- Exercise 3(c), O&R p. 346, complete markets with actuarially fair prices `p = π` and
`β = 1/(1+r)`: the FOCs (5) for quadratic utility (`a₀ ≠ 0`, `π > 0`) and the budget (4)
(with initial assets, `A = (1+r)B₁ + Y₁`) imply full insurance, `C₂(s) = C₁` for all `s`, with
`C₁ = C₁*` of part (a); nonnegativity is then automatic whenever lifetime resources
`A + E(Y₂)/(1+r)` are nonnegative, which is why it can be disregarded. -/
theorem quad_complete_markets (Ω : StateSpace S) {a0 r : ℝ} (ha0 : a0 ≠ 0) (hr : 0 < 1 + r)
    (hπ : ∀ s, 0 < Ω.prob s) (A C1 : ℝ) (C2 Y2 : S → ℝ)
    (hfoc : ∀ s, Ω.prob s / (1 + r) * (1 - a0 * C1) =
      Ω.prob s * (1 + r)⁻¹ * (1 - a0 * C2 s))
    (hbud : C1 + ∑ s, Ω.prob s / (1 + r) * C2 s = A + ∑ s, Ω.prob s / (1 + r) * Y2 s) :
    (∀ s, C2 s = C1) ∧ C1 = quadCstar Ω r A Y2 ∧
      (0 ≤ A + Ω.expect Y2 / (1 + r) → ∀ s, 0 ≤ C2 s) := by
  have h2r : 0 < 2 + r := by linarith
  have hr0 := hr.ne'
  have hC2 : ∀ s, C2 s = C1 := fun s => by
    have h := hfoc s
    have hk : Ω.prob s * (1 + r)⁻¹ * a0 ≠ 0 :=
      mul_ne_zero (mul_ne_zero (hπ s).ne' (inv_ne_zero hr0)) ha0
    refine mul_left_cancel₀ hk ?_
    rw [div_eq_mul_inv] at h
    linear_combination h
  have hsumY : ∑ s, Ω.prob s / (1 + r) * Y2 s = Ω.expect Y2 / (1 + r) := by
    simp only [StateSpace.expect, Finset.sum_div]
    exact Finset.sum_congr rfl fun s _ => by ring
  have hsumC : ∑ s, Ω.prob s / (1 + r) * C2 s = C1 / (1 + r) := by
    rw [Finset.sum_congr rfl fun s _ => by rw [hC2 s], ← Finset.sum_mul, ← Finset.sum_div,
      Ω.prob_sum]
    ring
  rw [hsumY, hsumC] at hbud
  have hC1 : C1 = quadCstar Ω r A Y2 := by
    rw [quadCstar, ← hbud]
    field_simp
    ring
  refine ⟨hC2, hC1, fun hW s => ?_⟩
  rw [hC2 s, hC1, quadCstar]
  exact mul_nonneg (div_nonneg hr.le h2r.le) hW

end ObstfeldRogoff.InternationalFinancialMarkets.SmallCountry

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# A general result on comparative advantage

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §5.1.7,
pp. 280–282 (the theorem of Deardorff (1980) and Dixit and Norman (1980), their footnote 12).

A consumption bundle is `x = (C₁, C₂(·)) ∈ ℝ × (S → ℝ)`, valued at date-1 prices
`q(s)` of state-`s` claims: `x.1 + Σ q(s)x.2(s)`. World prices are `q(s) = p(s)/(1+r)`,
autarky prices `q^A(s) = p^A(s)/(1+r^A)`. The preference relation `pref x y` ("`x` is at least
as good as `y`") is arbitrary except for transitivity and local non-satiation; no expected
utility, concavity, completeness or continuity is assumed. We prove:
* Walras' law: an optimal free-trade bundle exhausts the budget, giving (18);
* the revealed-preference inequality (19): the free-trade bundle is worth at least the
  endowment at autarky prices;
* the comparative-advantage inequality `Σ [p^A(s)/(1+r^A) − p(s)/(1+r)]B₂(s) ≥ 0`;
* the one-state case `S = Unit`, which is Chapter 1's result (`r > r^A` ⇒ `CA₁ ≥ 0`).

The book's parenthetical argument for (19) ("if the preceding inequality failed, the country
would be able to buy its free-trade consumption bundle, and then some, at autarky prices,
contradicting the presence of gains from trade") is garbled: the contradiction is not with
gains from trade as such but with the optimality of the endowment at autarky prices. If (19)
failed, the free-trade bundle *plus a little more* (local non-satiation) would have been
affordable in autarky; the endowment, chosen in autarky, would then be revealed preferred to a
bundle strictly better than the free-trade bundle, which in turn is at least as good as the
endowment — contradicting transitivity. That is the proof formalised below.
-/

namespace ObstfeldRogoff.InternationalFinancialMarkets.ComparativeAdvantage

open Finset

variable {S : Type} [Fintype S]

/-- The date-1 value of a bundle `x = (C₁, C₂)` at date-1 state-claim prices `q`,
`C₁ + Σ q(s)C₂(s)`, O&R (18)–(19), p. 281 (with `q(s) = p(s)/(1+r)` or `p^A(s)/(1+r^A)`). -/
def bundleValue (q : S → ℝ) (x : ℝ × (S → ℝ)) : ℝ := x.1 + ∑ s, q s * x.2 s

/-- Bundle values are continuous (in the sup metric on `ℝ × (S → ℝ)`), O&R §5.1.7. -/
theorem continuous_bundleValue (q : S → ℝ) : Continuous (bundleValue q) := by
  unfold bundleValue
  fun_prop

/-- Local non-satiation, O&R p. 282 ("more consumption is preferred to less", weakened): every
neighbourhood of every bundle `x` contains a bundle `y` with `¬ (x ⪰ y)`. (For complete
preferences `¬ (x ⪰ y)` means `y ≻ x`; for incomplete ones it is weaker than the usual
condition, so the results below are stronger.) -/
def LocallyNonsatiated (pref : ℝ × (S → ℝ) → ℝ × (S → ℝ) → Prop) : Prop :=
  ∀ x : ℝ × (S → ℝ), ∀ ε > 0, ∃ y, dist y x < ε ∧ ¬ pref x y

/-- Walras' law for the free-trade choice, O&R (18), p. 281: if `C` is affordable at world
prices `q` and at least as good as every affordable bundle, and preferences are locally
non-satiated, then `C` exhausts the budget: `value_q(C) = value_q(Y)`. -/
theorem walras_law {pref : ℝ × (S → ℝ) → ℝ × (S → ℝ) → Prop} (hlns : LocallyNonsatiated pref)
    (q : S → ℝ) (Y C : ℝ × (S → ℝ)) (hC : bundleValue q C ≤ bundleValue q Y)
    (hopt : ∀ z, bundleValue q z ≤ bundleValue q Y → pref C z) :
    bundleValue q C = bundleValue q Y := by
  by_contra hne
  have hlt : bundleValue q C < bundleValue q Y := lt_of_le_of_ne hC hne
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp
    (isOpen_lt (continuous_bundleValue q) continuous_const) C hlt
  obtain ⟨y, hy, hnot⟩ := hlns C ε hε
  have hyv : bundleValue q y < bundleValue q Y := hball (Metric.mem_ball.mpr hy)
  exact hnot (hopt y hyv.le)

/-- The revealed-preference inequality, O&R (19), p. 281: if the endowment `Y` was optimal at
autarky prices `q^A` (it is at least as good as every bundle worth no more than it at `q^A`),
the free-trade bundle `C` is at least as good as `Y` (gains from trade), and preferences are
transitive and locally non-satiated, then `value_{q^A}(C) ≥ value_{q^A}(Y)`, i.e.
`C₁ − Y₁ + Σ q^A(s)[C₂(s) − Y₂(s)] ≥ 0`. -/
theorem revealed_preference {pref : ℝ × (S → ℝ) → ℝ × (S → ℝ) → Prop}
    (htrans : ∀ x y z, pref x y → pref y z → pref x z) (hlns : LocallyNonsatiated pref)
    (qA : S → ℝ) (Y C : ℝ × (S → ℝ))
    (hautarky : ∀ z, bundleValue qA z ≤ bundleValue qA Y → pref Y z) (hCY : pref C Y) :
    bundleValue qA Y ≤ bundleValue qA C := by
  by_contra hlt
  push Not at hlt
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp
    (isOpen_lt (continuous_bundleValue qA) continuous_const) C hlt
  obtain ⟨y, hy, hnot⟩ := hlns C ε hε
  have hyv : bundleValue qA y < bundleValue qA Y := hball (Metric.mem_ball.mpr hy)
  exact hnot (htrans C Y y hCY (hautarky y hyv.le))

/-- The principle of comparative advantage, O&R §5.1.7, p. 281, for ANY transitive, locally
non-satiated preference relation and any number of states: suppose the endowment `Y` is
optimal at autarky prices `p^A(s)/(1+r^A)` and the free-trade bundle `C` is affordable and
optimal at world prices `p(s)/(1+r)`. Then, with net AD purchases `B₂(s) = C₂(s) − Y₂(s)`,
`Σ_s [p^A(s)/(1+r^A) − p(s)/(1+r)]B₂(s) ≥ 0`. -/
theorem comparative_advantage {pref : ℝ × (S → ℝ) → ℝ × (S → ℝ) → Prop}
    (htrans : ∀ x y z, pref x y → pref y z → pref x z) (hlns : LocallyNonsatiated pref)
    (p pA : S → ℝ) (r rA : ℝ) (Y C : ℝ × (S → ℝ))
    (hautarky : ∀ z, bundleValue (fun s => pA s / (1 + rA)) z ≤
      bundleValue (fun s => pA s / (1 + rA)) Y → pref Y z)
    (hC : bundleValue (fun s => p s / (1 + r)) C ≤ bundleValue (fun s => p s / (1 + r)) Y)
    (hopt : ∀ z, bundleValue (fun s => p s / (1 + r)) z ≤
      bundleValue (fun s => p s / (1 + r)) Y → pref C z) :
    0 ≤ ∑ s, (pA s / (1 + rA) - p s / (1 + r)) * (C.2 s - Y.2 s) := by
  have h18 := walras_law hlns _ Y C hC hopt
  have h19 := revealed_preference htrans hlns _ Y C hautarky (hopt Y le_rfl)
  simp only [bundleValue] at h18 h19
  have e : ∑ s, (pA s / (1 + rA) - p s / (1 + r)) * (C.2 s - Y.2 s) =
      (∑ s, pA s / (1 + rA) * C.2 s - ∑ s, pA s / (1 + rA) * Y.2 s) -
        (∑ s, p s / (1 + r) * C.2 s - ∑ s, p s / (1 + r) * Y.2 s) := by
    simp only [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [e]
  linarith

/-- The one-state case is Chapter 1's comparative advantage, O&R p. 281: with a single (sure)
date-2 state, `1 + r > 0` and `1 + r^A > 0`, a country whose autarky interest rate is below
the world rate (`r^A < r`) runs a date-1 current-account surplus, `Y₁ − C₁ ≥ 0`, and one with
`r < r^A` runs a deficit, under the hypotheses of `comparative_advantage`. -/
theorem comparative_advantage_one_state {pref : ℝ × (Unit → ℝ) → ℝ × (Unit → ℝ) → Prop}
    (htrans : ∀ x y z, pref x y → pref y z → pref x z) (hlns : LocallyNonsatiated pref)
    {r rA : ℝ} (hr : 0 < 1 + r) (hrA : 0 < 1 + rA) (Y C : ℝ × (Unit → ℝ))
    (hautarky : ∀ z, bundleValue (fun _ => 1 / (1 + rA)) z ≤
      bundleValue (fun _ => 1 / (1 + rA)) Y → pref Y z)
    (hC : bundleValue (fun _ => 1 / (1 + r)) C ≤ bundleValue (fun _ => 1 / (1 + r)) Y)
    (hopt : ∀ z, bundleValue (fun _ => 1 / (1 + r)) z ≤
      bundleValue (fun _ => 1 / (1 + r)) Y → pref C z) :
    (rA < r → 0 ≤ Y.1 - C.1) ∧ (r < rA → Y.1 - C.1 ≤ 0) := by
  have hca := comparative_advantage htrans hlns (fun _ => 1) (fun _ => 1) r rA Y C hautarky hC
    hopt
  have h18 := walras_law hlns _ Y C hC hopt
  simp only [bundleValue, Finset.univ_unique, Finset.sum_singleton] at hca h18
  have hCA : Y.1 - C.1 = 1 / (1 + r) * (C.2 () - Y.2 ()) := by linarith
  rw [hCA]
  constructor
  · intro h
    have hq : 1 / (1 + r) < 1 / (1 + rA) := one_div_lt_one_div_of_lt hrA (by linarith)
    have hB : 0 ≤ C.2 () - Y.2 () := nonneg_of_mul_nonneg_right hca (by linarith)
    exact mul_nonneg (by positivity) hB
  · intro h
    have hq : 1 / (1 + rA) < 1 / (1 + r) := one_div_lt_one_div_of_lt hr (by linarith)
    have hB : C.2 () - Y.2 () ≤ 0 := by nlinarith
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) hB

/-- Comparative advantage for utility-representable preferences, O&R p. 282 ("the result holds
for nonexpected- as well as expected-utility preferences"): for ANY utility function `U` on
bundles that is locally non-satiated (every neighbourhood of `x` contains `y` with
`U y > U x`), the inequality of `comparative_advantage` holds. -/
theorem comparative_advantage_utility (U : ℝ × (S → ℝ) → ℝ)
    (hlns : ∀ x : ℝ × (S → ℝ), ∀ ε > 0, ∃ y, dist y x < ε ∧ U x < U y)
    (p pA : S → ℝ) (r rA : ℝ) (Y C : ℝ × (S → ℝ))
    (hautarky : ∀ z, bundleValue (fun s => pA s / (1 + rA)) z ≤
      bundleValue (fun s => pA s / (1 + rA)) Y → U z ≤ U Y)
    (hC : bundleValue (fun s => p s / (1 + r)) C ≤ bundleValue (fun s => p s / (1 + r)) Y)
    (hopt : ∀ z, bundleValue (fun s => p s / (1 + r)) z ≤
      bundleValue (fun s => p s / (1 + r)) Y → U z ≤ U C) :
    0 ≤ ∑ s, (pA s / (1 + rA) - p s / (1 + r)) * (C.2 s - Y.2 s) :=
  comparative_advantage (pref := fun x y => U y ≤ U x) (fun _ _ _ h1 h2 => h2.trans h1)
    (fun x ε hε => (hlns x ε hε).imp fun _ h => ⟨h.1, not_le.mpr h.2⟩) p pA r rA Y C
    hautarky hC hopt

end ObstfeldRogoff.InternationalFinancialMarkets.ComparativeAdvantage

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Risk aversion, intertemporal substitution and two-stage budgeting

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §5.1.8,
pp. 282–285, including footnote 14.

Lifetime utility is `u(C₁) + βu(Ω(C₂))` (O&R (20)) with the CES certainty equivalent
`Ω(C₂) = [Σ π(s)C₂(s)^{1−ρ}]^{1/(1−ρ)}` (O&R (23)), `0 < ρ ≠ 1`. Date-1 prices of state
claims are `p(s)/(1+r)`, and `Z₂ = Σ p(s)C₂(s)` is date-2 spending in sure date-2 units. We
prove:
* the demands (24) cost exactly `Z₂` and attain `Ω = Z₂/P`, with `P` the price index (25), and
  no bundle costing at most `Z₂` does better (strictly, unless it is the demand bundle): this
  is the second stage of two-stage budgeting, and lifetime utility (20) is bounded by (21);
* `P ≤ 1`, with equality iff `p = π`, for probability vectors `p`, `π > 0` (O&R p. 285);
* the Euler equation (27) and `C₁ = W₁/(1 + ((1+r)/P)^{σ−1}β^σ)` for isoelastic `u`;
* footnote 14: `C₁ = Y₁` iff `1 + r = 1 + r^CA = (1/β)[Σ p(s)Y₂(s)/(P^{1−σ}Y₁)]^{1/σ}`, and
  `CA₁ > 0` iff `r > r^CA`;
* with `P < 1`, `C₁` lies below its certainty benchmark (`P = 1`) if `σ > 1` and above it if
  `σ < 1`; `σ = 1` and `p = π` are the special cases in which the benchmark is exact; with
  `β(1+r) = 1` and `Y₁ = Σ p(s)Y₂(s)`, `CA₁ > 0` when `σ > 1` and `CA₁ < 0` when `σ < 1`.
-/

namespace ObstfeldRogoff.InternationalFinancialMarkets.TwoStageBudgeting

open Finset

variable {S : Type} [Fintype S]

/-! ## Tangent-line inequalities for powers -/

/-- Bernoulli's inequality for a negative exponent (used for the CES optimality in O&R §5.1.8):
for `a < 0` and `t > 0`, `1 + a(t − 1) ≤ t^a`, strictly if `t ≠ 1`. -/
theorem one_add_mul_le_rpow_of_neg {a t : ℝ} (ha : a < 0) (ht : 0 < t) :
    1 + a * (t - 1) ≤ t ^ a ∧ (t ≠ 1 → 1 + a * (t - 1) < t ^ a) := by
  have e : t ^ a = t * (1 + (t⁻¹ - 1)) ^ (1 - a) := by
    rw [add_sub_cancel, Real.inv_rpow ht.le, ← Real.rpow_neg ht.le, neg_sub,
      Real.rpow_sub_one ht.ne']
    field_simp
  have hs : -1 ≤ t⁻¹ - 1 := by have := inv_pos.mpr ht; linarith
  have key : t * (1 + (1 - a) * (t⁻¹ - 1)) = 1 + a * (t - 1) := by field_simp; ring
  rw [e, ← key]
  refine ⟨mul_le_mul_of_nonneg_left
    (one_add_mul_self_le_rpow_one_add hs (by linarith)) ht.le, fun h1 => ?_⟩
  have hs' : t⁻¹ - 1 ≠ 0 := by
    intro h0
    exact h1 (inv_eq_one.mp (sub_eq_zero.mp h0))
  exact mul_lt_mul_of_pos_left (one_add_mul_self_lt_rpow_one_add hs hs' (by linarith)) ht

/-- Tangent-line inequality for `x ↦ x^a`, `0 < a < 1` (concave), O&R §5.1.8:
`x^a ≤ y^a + a y^{a−1}(x − y)` for `x, y > 0`, strictly if `x ≠ y`. -/
theorem rpow_le_tangent {a x y : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hx : 0 < x) (hy : 0 < y) :
    x ^ a ≤ y ^ a + a * y ^ (a - 1) * (x - y) ∧
      (x ≠ y → x ^ a < y ^ a + a * y ^ (a - 1) * (x - y)) := by
  have hya : 0 < y ^ a := Real.rpow_pos_of_pos hy a
  have ex : x ^ a = y ^ a * (1 + (x / y - 1)) ^ a := by
    rw [add_sub_cancel, Real.div_rpow hx.le hy.le]
    field_simp
  have et : y ^ a + a * y ^ (a - 1) * (x - y) = y ^ a * (1 + a * (x / y - 1)) := by
    rw [Real.rpow_sub_one hy.ne']
    field_simp
  have hs : -1 ≤ x / y - 1 := by have := div_pos hx hy; linarith
  rw [ex, et]
  refine ⟨mul_le_mul_of_nonneg_left
    (rpow_one_add_le_one_add_mul_self hs ha0.le ha1.le) hya.le, fun hxy => ?_⟩
  have hs' : x / y - 1 ≠ 0 := by
    intro h0
    exact hxy ((div_eq_one_iff_eq hy.ne').mp (sub_eq_zero.mp h0))
  exact mul_lt_mul_of_pos_left (rpow_one_add_lt_one_add_mul_self hs hs' ha0 ha1) hya

/-- Tangent-line inequality for `x ↦ x^a`, `a < 0` (convex), O&R §5.1.8:
`y^a + a y^{a−1}(x − y) ≤ x^a` for `x, y > 0`, strictly if `x ≠ y`. -/
theorem tangent_le_rpow_of_neg {a x y : ℝ} (ha : a < 0) (hx : 0 < x) (hy : 0 < y) :
    y ^ a + a * y ^ (a - 1) * (x - y) ≤ x ^ a ∧
      (x ≠ y → y ^ a + a * y ^ (a - 1) * (x - y) < x ^ a) := by
  have hya : 0 < y ^ a := Real.rpow_pos_of_pos hy a
  have ex : x ^ a = y ^ a * (x / y) ^ a := by
    rw [Real.div_rpow hx.le hy.le]
    field_simp
  have et : y ^ a + a * y ^ (a - 1) * (x - y) = y ^ a * (1 + a * (x / y - 1)) := by
    rw [Real.rpow_sub_one hy.ne']
    field_simp
  have h := one_add_mul_le_rpow_of_neg ha (div_pos hx hy)
  rw [ex, et]
  refine ⟨mul_le_mul_of_nonneg_left h.1 hya.le, fun hxy => ?_⟩
  exact mul_lt_mul_of_pos_left (h.2 fun h1 => hxy ((div_eq_one_iff_eq hy.ne').mp h1)) hya

/-! ## The CES certainty equivalent, its price index and demands (O&R (23)–(25)) -/

/-- The CES certainty-equivalent consumption index, O&R (23), p. 283:
`Ω(C₂) = [Σ π(s)C₂(s)^{1−ρ}]^{1/(1−ρ)}`. -/
noncomputable def cesIndex (Ω : StateSpace S) (ρ : ℝ) (C : S → ℝ) : ℝ :=
  (∑ s, Ω.prob s * C s ^ (1 - ρ)) ^ (1 / (1 - ρ))

/-- The date-2 consumption-based price index, O&R (25), p. 283:
`P = [Σ π(s)^{1/ρ} p(s)^{(ρ−1)/ρ}]^{ρ/(ρ−1)}`. -/
noncomputable def priceIndex (Ω : StateSpace S) (ρ : ℝ) (p : S → ℝ) : ℝ :=
  (∑ s, Ω.prob s ^ (1 / ρ) * p s ^ ((ρ - 1) / ρ)) ^ (ρ / (ρ - 1))

/-- The state-contingent consumption demands, O&R (24), p. 283:
`C₂(s) = [(p(s)/π(s))/P]^{−1/ρ} Z₂/P`. -/
noncomputable def cesDemand (Ω : StateSpace S) (ρ : ℝ) (p : S → ℝ) (Z : ℝ) (s : S) : ℝ :=
  (p s / Ω.prob s / priceIndex Ω ρ p) ^ (-1 / ρ) * (Z / priceIndex Ω ρ p)

/-- A finite state space with probabilities summing to one is nonempty (used throughout
O&R §5.1.8). -/
theorem univ_nonempty_of_stateSpace (Ω : StateSpace S) : (Finset.univ : Finset S).Nonempty := by
  by_contra h
  rw [Finset.not_nonempty_iff_eq_empty] at h
  have h1 := Ω.prob_sum
  rw [h, Finset.sum_empty] at h1
  exact zero_ne_one h1

/-- The sum inside the price index (25) is positive, O&R p. 283 (for `π, p > 0`). -/
theorem priceSum_pos (Ω : StateSpace S) (hπ : ∀ s, 0 < Ω.prob s) (p : S → ℝ)
    (hp : ∀ s, 0 < p s) (ρ : ℝ) :
    0 < ∑ s, Ω.prob s ^ (1 / ρ) * p s ^ ((ρ - 1) / ρ) :=
  Finset.sum_pos (fun s _ => by have := hπ s; have := hp s; positivity)
    (univ_nonempty_of_stateSpace Ω)

/-- The price index (25) is positive, O&R p. 283 (for `π, p > 0`). -/
theorem priceIndex_pos (Ω : StateSpace S) (hπ : ∀ s, 0 < Ω.prob s) (p : S → ℝ)
    (hp : ∀ s, 0 < p s) (ρ : ℝ) : 0 < priceIndex Ω ρ p :=
  Real.rpow_pos_of_pos (priceSum_pos Ω hπ p hp ρ) _

/-- Cost of the demands (24), O&R p. 283: `Σ p(s)C₂(s) = Z₂` (for `π, p, Z₂ > 0`,
`0 < ρ ≠ 1`). -/
theorem demand_cost (Ω : StateSpace S) (hπ : ∀ s, 0 < Ω.prob s) (p : S → ℝ)
    (hp : ∀ s, 0 < p s) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≠ 1) {Z : ℝ} (hZ : 0 < Z) :
    ∑ s, p s * cesDemand Ω ρ p Z s = Z := by
  have hD0 := priceSum_pos Ω hπ p hp ρ
  have hP := priceIndex_pos Ω hπ p hp ρ
  set D0 := ∑ s, Ω.prob s ^ (1 / ρ) * p s ^ ((ρ - 1) / ρ) with hD0def
  set P := priceIndex Ω ρ p with hPdef
  have hρ1' : ρ - 1 ≠ 0 := sub_ne_zero.mpr hρ1
  have hPpow : P ^ ((1 - ρ) / ρ) = D0⁻¹ := by
    rw [hPdef, priceIndex, ← hD0def, ← Real.rpow_mul hD0.le,
      show ρ / (ρ - 1) * ((1 - ρ) / ρ) = -1 by field_simp; ring, Real.rpow_neg_one]
  have term : ∀ s, p s * cesDemand Ω ρ p Z s =
      Z * P ^ ((1 - ρ) / ρ) * (Ω.prob s ^ (1 / ρ) * p s ^ ((ρ - 1) / ρ)) := fun s => by
    have := hπ s
    have := hp s
    refine Real.log_injOn_pos (Set.mem_Ioi.2 (by unfold cesDemand; positivity))
      (Set.mem_Ioi.2 (by positivity)) ?_
    simp only [cesDemand, ← hPdef]
    simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_rpow]
    field_simp
    ring
  rw [Finset.sum_congr rfl fun s _ => term s, ← Finset.mul_sum, ← hD0def, hPpow]
  field_simp

/-- The first-order condition behind the demands (24), O&R pp. 283–284:
`π(s)C₂(s)^{−ρ} = λ p(s)` with the same `λ = (Z₂/P)^{−ρ}/P` in every state. -/
theorem demand_foc (Ω : StateSpace S) (hπ : ∀ s, 0 < Ω.prob s) (p : S → ℝ)
    (hp : ∀ s, 0 < p s) {ρ : ℝ} (hρ0 : 0 < ρ) {Z : ℝ} (hZ : 0 < Z) (s : S) :
    Ω.prob s * cesDemand Ω ρ p Z s ^ (-ρ) =
      p s * ((Z / priceIndex Ω ρ p) ^ (-ρ) / priceIndex Ω ρ p) := by
  have hP := priceIndex_pos Ω hπ p hp ρ
  set P := priceIndex Ω ρ p with hPdef
  have := hπ s
  have := hp s
  refine Real.log_injOn_pos (Set.mem_Ioi.2 (by unfold cesDemand; positivity))
    (Set.mem_Ioi.2 (by positivity)) ?_
  simp only [cesDemand, ← hPdef]
  simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_rpow]
  field_simp
  ring

/-- The demands (24) attain the consumption index `Ω = Z₂/P`, O&R (24)–(25), p. 283 (for
`π, p, Z₂ > 0`, `0 < ρ ≠ 1`). -/
theorem cesIndex_demand (Ω : StateSpace S) (hπ : ∀ s, 0 < Ω.prob s) (p : S → ℝ)
    (hp : ∀ s, 0 < p s) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≠ 1) {Z : ℝ} (hZ : 0 < Z) :
    ∑ s, Ω.prob s * cesDemand Ω ρ p Z s ^ (1 - ρ) = (Z / priceIndex Ω ρ p) ^ (1 - ρ) ∧
      cesIndex Ω ρ (cesDemand Ω ρ p Z) = Z / priceIndex Ω ρ p := by
  have hD0 := priceSum_pos Ω hπ p hp ρ
  have hP := priceIndex_pos Ω hπ p hp ρ
  set D0 := ∑ s, Ω.prob s ^ (1 / ρ) * p s ^ ((ρ - 1) / ρ) with hD0def
  set P := priceIndex Ω ρ p with hPdef
  have hρ1' : ρ - 1 ≠ 0 := sub_ne_zero.mpr hρ1
  have h1ρ : 1 - ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm hρ1)
  have hPpow : P ^ ((1 - ρ) / ρ) = D0⁻¹ := by
    rw [hPdef, priceIndex, ← hD0def, ← Real.rpow_mul hD0.le,
      show ρ / (ρ - 1) * ((1 - ρ) / ρ) = -1 by field_simp; ring, Real.rpow_neg_one]
  have term : ∀ s, Ω.prob s * cesDemand Ω ρ p Z s ^ (1 - ρ) =
      (Z / P) ^ (1 - ρ) * P ^ ((1 - ρ) / ρ) *
        (Ω.prob s ^ (1 / ρ) * p s ^ ((ρ - 1) / ρ)) := fun s => by
    have := hπ s
    have := hp s
    refine Real.log_injOn_pos (Set.mem_Ioi.2 (by unfold cesDemand; positivity))
      (Set.mem_Ioi.2 (by positivity)) ?_
    simp only [cesDemand, ← hPdef]
    simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_rpow]
    field_simp
    ring
  have hsum : ∑ s, Ω.prob s * cesDemand Ω ρ p Z s ^ (1 - ρ) = (Z / P) ^ (1 - ρ) := by
    rw [Finset.sum_congr rfl fun s _ => term s, ← Finset.mul_sum, ← hD0def, hPpow]
    field_simp
  refine ⟨hsum, ?_⟩
  rw [cesIndex, hsum, one_div, Real.rpow_rpow_inv (by positivity) h1ρ]

/-- Second-stage optimality of the demands (24), O&R §5.1.8, p. 283 (two-stage budgeting, step
2): for `π, p, Z₂ > 0` and `0 < ρ ≠ 1`, every positive bundle `C₂` with `Σ p(s)C₂(s) ≤ Z₂` has
`Ω(C₂) ≤ Z₂/P`, strictly unless `C₂` is the demand bundle (24). Proof: the tangent-line
inequality for `x^{1−ρ}` at the demands, whose marginal utilities are proportional to `p`. -/
theorem cesIndex_le (Ω : StateSpace S) (hπ : ∀ s, 0 < Ω.prob s) (p : S → ℝ)
    (hp : ∀ s, 0 < p s) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≠ 1) {Z : ℝ} (hZ : 0 < Z)
    (C : S → ℝ) (hC : ∀ s, 0 < C s) (hbud : ∑ s, p s * C s ≤ Z) :
    cesIndex Ω ρ C ≤ Z / priceIndex Ω ρ p ∧
      ((∃ s, C s ≠ cesDemand Ω ρ p Z s) → cesIndex Ω ρ C < Z / priceIndex Ω ρ p) := by
  have hP := priceIndex_pos Ω hπ p hp ρ
  set P := priceIndex Ω ρ p with hPdef
  set D := cesDemand Ω ρ p Z with hDdef
  have hD : ∀ s, 0 < D s := fun s => by
    have := hπ s; have := hp s
    simp only [hDdef, cesDemand, ← hPdef]
    positivity
  set lam := (Z / P) ^ (-ρ) / P with hlam
  have hlampos : 0 < lam := by positivity
  have hfoc : ∀ s, Ω.prob s * D s ^ (-ρ) = p s * lam := demand_foc Ω hπ p hp hρ0 hZ
  have hcost : ∑ s, p s * D s = Z := demand_cost Ω hπ p hp hρ0 hρ1 hZ
  obtain ⟨hval, hind⟩ := cesIndex_demand Ω hπ p hp hρ0 hρ1 hZ
  rw [← hDdef, ← hPdef] at hval hind
  rw [← hind]
  set a := 1 - ρ with ha
  have ha1 : a - 1 = -ρ := by rw [ha]; ring
  have lin : ∑ s, Ω.prob s * (D s ^ a + a * D s ^ (a - 1) * (C s - D s)) =
      ∑ s, Ω.prob s * D s ^ a + a * lam * (∑ s, p s * C s - Z) := by
    rw [← hcost, ← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [ha1, show Ω.prob s * (D s ^ a + a * D s ^ (-ρ) * (C s - D s)) =
      Ω.prob s * D s ^ a + a * (Ω.prob s * D s ^ (-ρ)) * (C s - D s) by ring, hfoc s]
    ring
  have hDsum : 0 < ∑ s, Ω.prob s * D s ^ a :=
    Finset.sum_pos (fun s _ => by have := hπ s; have := hD s; positivity)
      (univ_nonempty_of_stateSpace Ω)
  have hCsum : 0 ≤ ∑ s, Ω.prob s * C s ^ a :=
    Finset.sum_nonneg fun s _ => by have := hπ s; have := hC s; positivity
  rcases lt_or_gt_of_ne hρ1 with hlt | hgt
  · -- ρ < 1: `x^a` concave, the sum is maximised at the demands.
    have ha0 : 0 < a := by rw [ha]; linarith
    have ha1' : a < 1 := by rw [ha]; linarith
    have hexp : 0 < 1 / a := by positivity
    have hterm : ∀ s, Ω.prob s * C s ^ a ≤
        Ω.prob s * (D s ^ a + a * D s ^ (a - 1) * (C s - D s)) := fun s =>
      mul_le_mul_of_nonneg_left (rpow_le_tangent ha0 ha1' (hC s) (hD s)).1 (hπ s).le
    have hneg : a * lam * (∑ s, p s * C s - Z) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
    have hle : ∑ s, Ω.prob s * C s ^ a ≤ ∑ s, Ω.prob s * D s ^ a := by
      have := Finset.sum_le_sum fun s (_ : s ∈ Finset.univ) => hterm s
      linarith
    refine ⟨Real.rpow_le_rpow hCsum hle hexp.le, fun ⟨s0, hs0⟩ => ?_⟩
    have hlt' : ∑ s, Ω.prob s * C s ^ a < ∑ s, Ω.prob s * D s ^ a := by
      have := Finset.sum_lt_sum (fun s (_ : s ∈ Finset.univ) => hterm s)
        ⟨s0, Finset.mem_univ _, mul_lt_mul_of_pos_left
          ((rpow_le_tangent ha0 ha1' (hC s0) (hD s0)).2 hs0) (hπ s0)⟩
      linarith
    exact Real.rpow_lt_rpow hCsum hlt' hexp
  · -- ρ > 1: `x^a` convex with `a < 0`, the sum is minimised at the demands.
    have ha0 : a < 0 := by rw [ha]; linarith
    have hexp : 1 / a < 0 := by rw [one_div]; exact inv_lt_zero.mpr ha0
    have hterm : ∀ s, Ω.prob s * (D s ^ a + a * D s ^ (a - 1) * (C s - D s)) ≤
        Ω.prob s * C s ^ a := fun s =>
      mul_le_mul_of_nonneg_left (tangent_le_rpow_of_neg ha0 (hC s) (hD s)).1 (hπ s).le
    have hpos : 0 ≤ a * lam * (∑ s, p s * C s - Z) :=
      mul_nonneg_of_nonpos_of_nonpos (mul_nonpos_of_nonpos_of_nonneg ha0.le hlampos.le)
        (by linarith)
    have hle : ∑ s, Ω.prob s * D s ^ a ≤ ∑ s, Ω.prob s * C s ^ a := by
      have := Finset.sum_le_sum fun s (_ : s ∈ Finset.univ) => hterm s
      linarith
    refine ⟨Real.rpow_le_rpow_of_nonpos hDsum hle hexp.le, fun ⟨s0, hs0⟩ => ?_⟩
    have hlt' : ∑ s, Ω.prob s * D s ^ a < ∑ s, Ω.prob s * C s ^ a := by
      have := Finset.sum_lt_sum (fun s (_ : s ∈ Finset.univ) => hterm s)
        ⟨s0, Finset.mem_univ _, mul_lt_mul_of_pos_left
          ((tangent_le_rpow_of_neg ha0 (hC s0) (hD s0)).2 hs0) (hπ s0)⟩
      linarith
    exact Real.rpow_lt_rpow_of_neg hDsum hlt' hexp

/-- Two-stage budgeting reduces (20) to (21), O&R pp. 282–283: for any increasing `u` and
`β ≥ 0`, lifetime utility (20) of any positive plan `(C₁, C₂)` is at most
`u(C₁) + βu(Z₂/P)` with `Z₂ = Σ p(s)C₂(s)` its date-2 spending, with equality at the demands
(24). -/
theorem lifetime_le_two_stage (Ω : StateSpace S) (hπ : ∀ s, 0 < Ω.prob s) (p : S → ℝ)
    (hp : ∀ s, 0 < p s) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≠ 1) {u : ℝ → ℝ} (hu : Monotone u)
    {β : ℝ} (hβ : 0 ≤ β) (C1 : ℝ) (C2 : S → ℝ) (hC2 : ∀ s, 0 < C2 s) :
    u C1 + β * u (cesIndex Ω ρ C2) ≤
        u C1 + β * u ((∑ s, p s * C2 s) / priceIndex Ω ρ p) ∧
      (0 < (∑ s, p s * C2 s) → u C1 + β * u (cesIndex Ω ρ (cesDemand Ω ρ p (∑ s, p s * C2 s)))
        = u C1 + β * u ((∑ s, p s * C2 s) / priceIndex Ω ρ p)) := by
  have hZ : 0 < ∑ s, p s * C2 s :=
    Finset.sum_pos (fun s _ => mul_pos (hp s) (hC2 s)) (univ_nonempty_of_stateSpace Ω)
  refine ⟨?_, fun hZ' => by rw [(cesIndex_demand Ω hπ p hp hρ0 hρ1 hZ').2]⟩
  have := (cesIndex_le Ω hπ p hp hρ0 hρ1 hZ C2 hC2 le_rfl).1
  have := hu this
  nlinarith

/-- The price index is at most one, with equality iff prices are actuarially fair,
O&R p. 285: for probability vectors `π > 0`, `p > 0` (`Σ p(s) = 1`) and `0 < ρ ≠ 1`,
`P ≤ 1`, and `P = 1` iff `p(s) = π(s)` for all `s`. (The book's argument: the sure bundle
`C₂ ≡ 1` costs `Σ p(s) = 1` and has `Ω = 1`, and it is the demand bundle only at fair
prices.) -/
theorem priceIndex_le_one (Ω : StateSpace S) (hπ : ∀ s, 0 < Ω.prob s) (p : S → ℝ)
    (hp : ∀ s, 0 < p s) (hpsum : ∑ s, p s = 1) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≠ 1) :
    priceIndex Ω ρ p ≤ 1 ∧ (priceIndex Ω ρ p = 1 ↔ ∀ s, p s = Ω.prob s) := by
  have hP := priceIndex_pos Ω hπ p hp ρ
  have hone : cesIndex Ω ρ (fun _ => 1) = 1 := by
    simp only [cesIndex, Real.one_rpow, mul_one, Ω.prob_sum]
  have hbud : ∑ s, p s * (fun _ => (1 : ℝ)) s ≤ 1 := by simp [hpsum]
  have h := cesIndex_le Ω hπ p hp hρ0 hρ1 one_pos (fun _ => 1) (fun _ => one_pos) hbud
  rw [hone] at h
  have hle : priceIndex Ω ρ p ≤ 1 := by
    have := h.1
    rw [le_div_iff₀ hP, one_mul] at this
    exact this
  refine ⟨hle, ⟨fun hP1 => ?_, fun hfair => ?_⟩⟩
  · by_contra hne
    push Not at hne
    obtain ⟨s, hs⟩ := hne
    have hdem : (fun _ => (1 : ℝ)) s ≠ cesDemand Ω ρ p 1 s := by
      intro h1
      simp only [cesDemand, hP1, div_one, mul_one] at h1
      have hps := hp s
      have hπs := hπ s
      have hlog := congrArg Real.log h1.symm
      rw [Real.log_one, Real.log_rpow (by positivity)] at hlog
      have hl : Real.log (p s / Ω.prob s) = 0 := by
        rcases mul_eq_zero.mp hlog with h0 | h0
        · exact absurd h0 (div_ne_zero (by norm_num) hρ0.ne')
        · exact h0
      have := Real.eq_one_of_pos_of_log_eq_zero (by positivity) hl
      exact hs ((div_eq_one_iff_eq hπs.ne').mp this)
    have := h.2 ⟨s, hdem⟩
    rw [hP1] at this
    norm_num at this
  · have e : ∑ s, Ω.prob s ^ (1 / ρ) * p s ^ ((ρ - 1) / ρ) = 1 := by
      refine (Finset.sum_congr rfl fun s _ => ?_).trans Ω.prob_sum
      rw [hfair s, ← Real.rpow_add (hπ s), show 1 / ρ + (ρ - 1) / ρ = 1 by field_simp; ring,
        Real.rpow_one]
    rw [priceIndex, e, Real.one_rpow]

/-! ## The first stage: saving and the current account (O&R (21)–(22), (27), footnote 14) -/

/-- The intertemporal Euler equation (27), O&R p. 284: with isoelastic `u′(C) = C^{−1/σ}`
(`σ > 0`), the first-stage Euler equation `u′(C₁) = (1+r)β(1/P)u′(Z₂/P)` is equivalent to
`Z₂ = (1+r)^σ β^σ (1/P)^{σ−1} C₁` (all quantities positive). -/
theorem euler_27 {σ r β C1 Z2 P : ℝ} (hσ : 0 < σ) (hr : 0 < 1 + r) (hβ : 0 < β)
    (hC1 : 0 < C1) (hZ2 : 0 < Z2) (hP : 0 < P) :
    C1 ^ (-1 / σ) = (1 + r) * β * P⁻¹ * (Z2 / P) ^ (-1 / σ) ↔
      Z2 = (1 + r) ^ σ * β ^ σ * (1 / P) ^ (σ - 1) * C1 := by
  constructor
  · intro h
    have hL := congrArg Real.log h
    simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_rpow,
      Real.log_inv] at hL
    refine Real.log_injOn_pos (Set.mem_Ioi.2 hZ2) (Set.mem_Ioi.2 (by positivity)) ?_
    simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_rpow, Real.log_one]
    field_simp at hL ⊢
    linarith
  · intro h
    refine Real.log_injOn_pos (Set.mem_Ioi.2 (by positivity))
      (Set.mem_Ioi.2 (by positivity)) ?_
    have hL := congrArg Real.log h
    simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_rpow,
      Real.log_one] at hL
    simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_rpow, Real.log_inv]
    field_simp at hL ⊢
    linarith

/-- Date-1 consumption, O&R p. 284: the Euler equation (27) and the lifetime budget (22),
`C₁ + Z₂/(1+r) = W₁`, give `C₁ = W₁/(1 + ((1+r)/P)^{σ−1}β^σ)`. -/
theorem consumption_27 {σ r β C1 Z2 P W1 : ℝ} (hr : 0 < 1 + r) (hβ : 0 < β) (hP : 0 < P)
    (h27 : Z2 = (1 + r) ^ σ * β ^ σ * (1 / P) ^ (σ - 1) * C1)
    (hbud : C1 + Z2 / (1 + r) = W1) :
    C1 = W1 / (1 + ((1 + r) / P) ^ (σ - 1) * β ^ σ) := by
  have e : Z2 / (1 + r) = ((1 + r) / P) ^ (σ - 1) * β ^ σ * C1 := by
    rw [h27, Real.div_rpow hr.le hP.le, Real.div_rpow zero_le_one hP.le, Real.one_rpow,
      Real.rpow_sub_one hr.ne']
    have : 0 < P ^ (σ - 1) := Real.rpow_pos_of_pos hP _
    field_simp
  rw [eq_div_iff (by positivity)]
  linarith

/-- The current-account-autarky interest rate and the sign of the current account, O&R
footnote 14, p. 285: with `W₁ = Y₁ + V/(1+r)`, `V = Σ p(s)Y₂(s) > 0` and
`C₁ = W₁/(1 + ((1+r)/P)^{σ−1}β^σ)`, define
`1 + r^CA = (1/β)[V/(P^{1−σ}Y₁)]^{1/σ}`. Then `CA₁ = Y₁ − C₁` is positive iff `r > r^CA`,
negative iff `r < r^CA`, and zero (`C₁ = Y₁`) iff `r = r^CA`. -/
theorem current_account_sign_rCA {σ r β P Y1 V : ℝ} (hσ : 0 < σ) (hr : 0 < 1 + r)
    (hβ : 0 < β) (hP : 0 < P) (hY1 : 0 < Y1) (hV : 0 < V) :
    let CA := Y1 - (Y1 + V / (1 + r)) / (1 + ((1 + r) / P) ^ (σ - 1) * β ^ σ)
    let RCA := 1 / β * (V / (P ^ (1 - σ) * Y1)) ^ (1 / σ)
    (0 < CA ↔ RCA < 1 + r) ∧ (CA < 0 ↔ 1 + r < RCA) ∧ (CA = 0 ↔ 1 + r = RCA) := by
  intro CA RCA
  set R := 1 + r with hR
  set K := (R / P) ^ (σ - 1) * β ^ σ with hK
  have hKpos : 0 < K := by positivity
  set g : ℝ → ℝ := fun x => Y1 * P ^ (1 - σ) * (β * x) ^ σ with hg
  have hgmono : ∀ x y, 0 < x → 0 < y → (g x < g y ↔ x < y) := fun x y hx hy => by
    simp only [hg]
    rw [mul_lt_mul_iff_right₀ (by positivity), Real.rpow_lt_rpow_iff (by positivity)
      (by positivity) hσ, mul_lt_mul_iff_right₀ hβ]
  have hRCA : 0 < RCA := by positivity
  have hgRCA : g RCA = V := by
    simp only [hg, RCA]
    rw [show β * (1 / β * (V / (P ^ (1 - σ) * Y1)) ^ (1 / σ)) =
      (V / (P ^ (1 - σ) * Y1)) ^ (1 / σ) by field_simp, one_div,
      Real.rpow_inv_rpow (by positivity) hσ.ne']
    have : 0 < P ^ (1 - σ) := Real.rpow_pos_of_pos hP _
    field_simp
  have hgR : Y1 * K * R = g R := by
    simp only [hK, hg]
    refine Real.log_injOn_pos (Set.mem_Ioi.2 (by positivity))
      (Set.mem_Ioi.2 (by positivity)) ?_
    simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_rpow]
    ring
  have hCA : CA = (g R - V) / (R * (1 + K)) := by
    simp only [CA, ← hR, ← hK, ← hgR]
    field_simp
    ring
  have hden : 0 < R * (1 + K) := by positivity
  have hpos : 0 < CA ↔ RCA < R := by
    rw [hCA, div_pos_iff_of_pos_right hden, sub_pos, ← hgRCA]
    exact hgmono _ _ hRCA hr
  have hneg : CA < 0 ↔ R < RCA := by
    rw [hCA, div_neg_iff, sub_neg, ← hgRCA]
    constructor
    · rintro (⟨h1, _⟩ | ⟨h1, _⟩)
      · exact absurd h1 (not_lt.mpr (le_of_lt (by linarith [hgRCA ▸ h1])))
      · exact (hgmono _ _ hr hRCA).mp h1
    · intro h
      exact Or.inr ⟨(hgmono _ _ hr hRCA).mpr h, hden⟩
  refine ⟨hpos, hneg, ?_⟩
  constructor
  · intro h0
    rcases lt_trichotomy R RCA with h | h | h
    · exact absurd (hneg.mpr h) (by rw [h0]; exact lt_irrefl 0)
    · exact h
    · exact absurd (hpos.mpr h) (by rw [h0]; exact lt_irrefl 0)
  · intro h
    rw [hCA, h, hgRCA, sub_self, zero_div]

/-- Date-1 consumption versus its certainty benchmark, O&R p. 285: when `P < 1` (prices not
actuarially fair) the consumption-based real interest rate `(1+r)/P` exceeds `1 + r`, so
`C₁ = W₁/(1 + ((1+r)/P)^{σ−1}β^σ)` is strictly below the certainty benchmark
`W₁/(1 + (1+r)^{σ−1}β^σ)` (the value at `P = 1`) if `σ > 1`, and strictly above it if
`σ < 1` (`W₁ > 0`). -/
theorem consumption_vs_certainty {σ r β P W1 : ℝ} (hr : 0 < 1 + r) (hβ : 0 < β)
    (hP0 : 0 < P) (hP1 : P < 1) (hW : 0 < W1) :
    (1 < σ → W1 / (1 + ((1 + r) / P) ^ (σ - 1) * β ^ σ) <
      W1 / (1 + (1 + r) ^ (σ - 1) * β ^ σ)) ∧
    (σ < 1 → W1 / (1 + (1 + r) ^ (σ - 1) * β ^ σ) <
      W1 / (1 + ((1 + r) / P) ^ (σ - 1) * β ^ σ)) := by
  have hlt : 1 + r < (1 + r) / P := by
    rw [lt_div_iff₀ hP0]
    nlinarith
  have hbσ : 0 < β ^ σ := Real.rpow_pos_of_pos hβ σ
  constructor
  · intro hσ
    have h := Real.rpow_lt_rpow hr.le hlt (by linarith : 0 < σ - 1)
    apply div_lt_div_of_pos_left hW (by positivity)
    nlinarith
  · intro hσ
    have h := Real.rpow_lt_rpow_of_neg hr hlt (by linarith : σ - 1 < 0)
    apply div_lt_div_of_pos_left hW (by positivity)
    nlinarith

/-- Special case 1, O&R p. 284: with `σ = 1` the income and substitution effects of `P ≠ 1`
offset exactly, and `C₁ = W₁/(1+β)` whatever `P` (as in the log example of §5.1.6). -/
theorem consumption_sigma_one {r β P W1 : ℝ} :
    W1 / (1 + ((1 + r) / P) ^ ((1 : ℝ) - 1) * β ^ (1 : ℝ)) = W1 / (1 + β) := by
  rw [sub_self, Real.rpow_zero, Real.rpow_one, one_mul]

/-- Special case 2, O&R pp. 284–285: at actuarially fair prices `p = π` the price index is
`P = 1`, so `C₁ = W₁/(1 + (1+r)^{σ−1}β^σ)`, the certainty formula with date-2 output
`Σ p(s)Y₂(s)`. -/
theorem consumption_fair_prices (Ω : StateSpace S) (hπ : ∀ s, 0 < Ω.prob s) (p : S → ℝ)
    (hfair : ∀ s, p s = Ω.prob s) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≠ 1) (σ r β W1 : ℝ) :
    W1 / (1 + ((1 + r) / priceIndex Ω ρ p) ^ (σ - 1) * β ^ σ) =
      W1 / (1 + (1 + r) ^ (σ - 1) * β ^ σ) := by
  have hp : ∀ s, 0 < p s := fun s => (hfair s).symm ▸ hπ s
  have hpsum : ∑ s, p s = 1 := by rw [Finset.sum_congr rfl fun s _ => hfair s, Ω.prob_sum]
  rw [((priceIndex_le_one Ω hπ p hp hpsum hρ0 hρ1).2.mpr hfair), div_one]

/-- A current-account surplus from risk alone, O&R p. 285: even with `β(1+r) = 1` and
`Y₁ = V = Σ p(s)Y₂(s)` (which would give `CA₁ = 0` under certainty), `P < 1` implies
`CA₁ = Y₁ − C₁ > 0` when `σ > 1` and `CA₁ < 0` when `σ < 1`, where
`C₁ = (Y₁ + V/(1+r))/(1 + ((1+r)/P)^{σ−1}β^σ)`. -/
theorem current_account_fair_rate {σ r β P Y1 : ℝ} (hr : 0 < 1 + r) (hβR : β * (1 + r) = 1)
    (hP0 : 0 < P) (hP1 : P < 1) (hY1 : 0 < Y1) :
    (1 < σ → 0 < Y1 - (Y1 + Y1 / (1 + r)) / (1 + ((1 + r) / P) ^ (σ - 1) * β ^ σ)) ∧
      (σ < 1 → Y1 - (Y1 + Y1 / (1 + r)) / (1 + ((1 + r) / P) ^ (σ - 1) * β ^ σ) < 0) := by
  have hβ' : β = (1 + r)⁻¹ := eq_inv_of_mul_eq_one_left hβR
  have hβ : 0 < β := by rw [hβ']; positivity
  have hb : (1 + r) ^ (σ - 1) * β ^ σ = β := by
    rw [hβ', Real.inv_rpow hr.le, ← Real.rpow_neg hr.le, ← Real.rpow_add hr,
      show σ - 1 + -σ = -1 by ring, Real.rpow_neg_one]
  have hbench : (Y1 + Y1 / (1 + r)) / (1 + (1 + r) ^ (σ - 1) * β ^ σ) = Y1 := by
    rw [hb, hβ']
    field_simp
  have h := consumption_vs_certainty (σ := σ) hr hβ hP0 hP1
    (by positivity : 0 < Y1 + Y1 / (1 + r))
  rw [hbench] at h
  exact ⟨fun hσ => by linarith [h.1 hσ], fun hσ => by linarith [h.2 hσ]⟩

end ObstfeldRogoff.InternationalFinancialMarkets.TwoStageBudgeting

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# A global complete-markets equilibrium

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §5.2,
pp. 285–299, and Exercise 2, p. 345.

Two countries, Home and Foreign, trade a complete set of Arrow–Debreu securities on date 1
for the `S` states of date 2. Both have CRRA period utility with the same coefficient `ρ`
and discount factor `β`. We write `q(s) = p(s)/(1 + r)` for the date-1 price of the state-`s`
security, so the Euler equation (5) is `q(s) C₁^{-ρ} = π(s) β C₂(s)^{-ρ}`.

Main results:
* equilibrium prices (30), (31), (32) and the world interest rate (33);
* prices are actuarially fair iff world date-2 output is state-independent (p. 287);
* constant consumption shares (35)–(36), equal consumption growth across countries, and the
  closed form for Home's share `μ` (footnote 16);
* the planner weights `κ = μ^ρ/(μ^ρ + (1 − μ)^ρ)` of footnote 17: the first-order conditions
  and global optimality (via the tangent-line inequality for CRRA utility);
* different `ρ`, `β` across countries: equation (37) and perfect correlation of consumption
  growth (footnote 18);
* efficient investment (40)–(41) and the log/linear example `K₂ + K₂* = βY₁ᵂ/(1 + β)`
  (§5.2.4.1);
* Exercise 2 (log date-1, linear date-2 utility).
-/

namespace ObstfeldRogoff.InternationalFinancialMarkets.GlobalEquilibrium

open Finset StateSpace

variable {S : Type} [Fintype S]

/-! ## Two CRRA facts -/

/-- CRRA Euler equation in ratio form, O&R (5) with `u′(C) = C^{-ρ}`, p. 286:
`q C₁^{-ρ} = π β C₂^{-ρ}` iff `q = π β (C₂/C₁)^{-ρ}`. -/
theorem crra_euler_iff {q π β ρ C1 C2 : ℝ} (h1 : 0 < C1) (h2 : 0 < C2) :
    q * C1 ^ (-ρ) = π * β * C2 ^ (-ρ) ↔ q = π * β * (C2 / C1) ^ (-ρ) := by
  have hp : 0 < C1 ^ (-ρ) := Real.rpow_pos_of_pos h1 _
  rw [Real.div_rpow h2.le h1.le]
  constructor
  · intro h; field_simp; linarith
  · intro h; rw [h]; field_simp

/-- The map `x ↦ x^{-ρ}` is injective on positive reals when `ρ ≠ 0` (used for p. 287). -/
theorem rpow_neg_inj {x y ρ : ℝ} (hx : 0 < x) (hy : 0 < y) (hρ : ρ ≠ 0)
    (h : x ^ (-ρ) = y ^ (-ρ)) : x = y := by
  have hn : -ρ ≠ 0 := neg_ne_zero.2 hρ
  rw [← Real.rpow_rpow_inv hx.le hn, ← Real.rpow_rpow_inv hy.le hn, h]

/-! ## The two-country CRRA equilibrium (§5.2.1) -/

/-- A two-country complete-markets equilibrium with common CRRA utility, O&R §5.2.1,
pp. 286–289: Euler equations (5) for Home and Foreign at common Arrow–Debreu prices
`p(s)/(1 + r)`, market clearing (28)–(29), the no-arbitrage condition `Σ p(s) = 1` (7) and
Home's intertemporal budget constraint (18). States have positive probability and all
consumption levels are positive (interiority, implicit in the book). -/
structure GlobalEqm (S : Type) [Fintype S] where
  Ω : StateSpace S
  β : ℝ
  ρ : ℝ
  r : ℝ
  p : S → ℝ
  Y1 : ℝ
  Y1f : ℝ
  Y2 : S → ℝ
  Y2f : S → ℝ
  C1 : ℝ
  C1f : ℝ
  C2 : S → ℝ
  C2f : S → ℝ
  prob_pos : ∀ s, 0 < Ω.prob s
  beta_pos : 0 < β
  rho_pos : 0 < ρ
  gross_pos : 0 < 1 + r
  C1_pos : 0 < C1
  C1f_pos : 0 < C1f
  C2_pos : ∀ s, 0 < C2 s
  C2f_pos : ∀ s, 0 < C2f s
  euler : ∀ s, p s / (1 + r) * C1 ^ (-ρ) = Ω.prob s * β * C2 s ^ (-ρ)
  euler_f : ∀ s, p s / (1 + r) * C1f ^ (-ρ) = Ω.prob s * β * C2f s ^ (-ρ)
  clear1 : C1 + C1f = Y1 + Y1f
  clear2 : ∀ s, C2 s + C2f s = Y2 s + Y2f s
  price_sum : ∑ s, p s = 1
  budget : C1 + ∑ s, p s / (1 + r) * C2 s = Y1 + ∑ s, p s / (1 + r) * Y2 s

namespace GlobalEqm

variable (E : GlobalEqm S)

/-- World date-1 output `Y₁ᵂ = Y₁ + Y₁*`, O&R p. 286. -/
def worldY1 : ℝ := E.Y1 + E.Y1f

/-- World date-2 output `Y₂ᵂ(s) = Y₂(s) + Y₂*(s)`, O&R p. 286. -/
def worldY2 (s : S) : ℝ := E.Y2 s + E.Y2f s

/-- World date-1 output is positive (it equals total positive consumption). -/
theorem worldY1_pos : 0 < E.worldY1 := by
  unfold worldY1; rw [← E.clear1]; linarith [E.C1_pos, E.C1f_pos]

/-- World date-2 output is positive in every state. -/
theorem worldY2_pos (s : S) : 0 < E.worldY2 s := by
  unfold worldY2; rw [← E.clear2 s]; linarith [E.C2_pos s, E.C2f_pos s]

/-- Home and Foreign consumption growth are equal state by state, O&R (36), p. 288:
`C₂(s)/C₁ = C₂*(s)/C₁*`. -/
theorem growth_eq (s : S) : E.C2 s / E.C1 = E.C2f s / E.C1f := by
  have h1 := (crra_euler_iff E.C1_pos (E.C2_pos s)).1 (E.euler s)
  have h2 := (crra_euler_iff E.C1f_pos (E.C2f_pos s)).1 (E.euler_f s)
  have hπβ : 0 < E.Ω.prob s * E.β := mul_pos (E.prob_pos s) E.beta_pos
  have h : (E.C2 s / E.C1) ^ (-E.ρ) = (E.C2f s / E.C1f) ^ (-E.ρ) := by
    have := h1.symm.trans h2
    exact mul_left_cancel₀ hπβ.ne' this
  exact rpow_neg_inj (div_pos (E.C2_pos s) E.C1_pos) (div_pos (E.C2f_pos s) E.C1f_pos)
    E.rho_pos.ne' h

/-- Consumption growth equals world output growth, O&R (36), p. 288:
`C₂(s)/C₁ = Y₂ᵂ(s)/Y₁ᵂ`. -/
theorem growth_eq_world (s : S) : E.C2 s / E.C1 = E.worldY2 s / E.worldY1 := by
  have h := E.growth_eq s
  have h1 := E.C1_pos; have h1f := E.C1f_pos
  unfold worldY1 worldY2
  rw [← E.clear1, ← E.clear2 s]
  rw [div_eq_div_iff h1.ne' h1f.ne'] at h
  rw [div_eq_div_iff h1.ne' (by linarith)]
  linarith

/-- **Equilibrium Arrow–Debreu prices**, O&R (30), p. 286:
`p(s)/(1 + r) = π(s) β [Y₂ᵂ(s)/Y₁ᵂ]^{-ρ}`. -/
theorem ad_price (s : S) :
    E.p s / (1 + E.r) = E.Ω.prob s * E.β * (E.worldY2 s / E.worldY1) ^ (-E.ρ) := by
  rw [← E.growth_eq_world s]
  exact (crra_euler_iff E.C1_pos (E.C2_pos s)).1 (E.euler s)

/-- The price in the form `p(s) = (1 + r) β (Y₁ᵂ)^ρ π(s) Y₂ᵂ(s)^{-ρ}` (step towards (32)). -/
theorem price_expand (s : S) :
    E.p s = (1 + E.r) * E.β * E.worldY1 ^ E.ρ *
      (E.Ω.prob s * E.worldY2 s ^ (-E.ρ)) := by
  have h := E.ad_price s
  rw [Real.div_rpow (E.worldY2_pos s).le E.worldY1_pos.le, Real.rpow_neg E.worldY1_pos.le]
    at h
  have hg := E.gross_pos
  have hY : 0 < E.worldY1 ^ E.ρ := Real.rpow_pos_of_pos E.worldY1_pos _
  field_simp at h
  rw [h]; ring

/-- Relative prices of two contingent claims, O&R (31), p. 287:
`p(s)/p(s′) = [Y₂ᵂ(s)/Y₂ᵂ(s′)]^{-ρ} · π(s)/π(s′)`. -/
theorem price_ratio (s s' : S) :
    E.p s / E.p s' = (E.worldY2 s / E.worldY2 s') ^ (-E.ρ) * (E.Ω.prob s / E.Ω.prob s') := by
  rw [E.price_expand s, E.price_expand s',
    Real.div_rpow (E.worldY2_pos s).le (E.worldY2_pos s').le]
  have := E.gross_pos; have := E.beta_pos; have := E.prob_pos s'
  have : 0 < E.worldY1 ^ E.ρ := Real.rpow_pos_of_pos E.worldY1_pos _
  have : 0 < E.worldY2 s' ^ (-E.ρ) := Real.rpow_pos_of_pos (E.worldY2_pos s') _
  field_simp

/-- The normalising sum `Σ π(s) Y₂ᵂ(s)^{-ρ}` of (32)–(33) is positive. -/
theorem kernel_sum_pos : 0 < ∑ s, E.Ω.prob s * E.worldY2 s ^ (-E.ρ) := by
  have hne : (Finset.univ : Finset S).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have := E.price_sum; rw [h, Finset.sum_empty] at this; exact zero_ne_one this
  exact Finset.sum_pos (fun s _ => mul_pos (E.prob_pos s)
    (Real.rpow_pos_of_pos (E.worldY2_pos s) _)) hne

/-- The normalisation from `Σ p(s) = 1`: `(1 + r) β (Y₁ᵂ)^ρ Σ π Y₂ᵂ^{-ρ} = 1`. -/
theorem normalisation :
    (1 + E.r) * E.β * E.worldY1 ^ E.ρ *
      ∑ s, E.Ω.prob s * E.worldY2 s ^ (-E.ρ) = 1 := by
  calc _ = ∑ s, E.p s := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun s _ => (E.price_expand s).symm
    _ = 1 := E.price_sum

/-- **Date-2 prices**, O&R (32), p. 287:
`p(s) = π(s) Y₂ᵂ(s)^{-ρ} / Σ_{s′} π(s′) Y₂ᵂ(s′)^{-ρ}`. -/
theorem price_formula (s : S) :
    E.p s = E.Ω.prob s * E.worldY2 s ^ (-E.ρ) /
      ∑ s', E.Ω.prob s' * E.worldY2 s' ^ (-E.ρ) := by
  have hK := E.kernel_sum_pos
  have hn := E.normalisation
  rw [eq_div_iff hK.ne', E.price_expand s]
  calc (1 + E.r) * E.β * E.worldY1 ^ E.ρ * (E.Ω.prob s * E.worldY2 s ^ (-E.ρ)) *
        ∑ s', E.Ω.prob s' * E.worldY2 s' ^ (-E.ρ)
      = ((1 + E.r) * E.β * E.worldY1 ^ E.ρ * ∑ s', E.Ω.prob s' * E.worldY2 s' ^ (-E.ρ)) *
        (E.Ω.prob s * E.worldY2 s ^ (-E.ρ)) := by ring
    _ = _ := by rw [hn, one_mul]

/-- **The world interest rate**, O&R (33), p. 287:
`1 + r = (Y₁ᵂ)^{-ρ} / (β Σ π(s) Y₂ᵂ(s)^{-ρ})`. -/
theorem interest_formula :
    1 + E.r = E.worldY1 ^ (-E.ρ) / (E.β * ∑ s, E.Ω.prob s * E.worldY2 s ^ (-E.ρ)) := by
  have hK := E.kernel_sum_pos
  have hn := E.normalisation
  have hb := E.beta_pos
  have hY : 0 < E.worldY1 ^ E.ρ := Real.rpow_pos_of_pos E.worldY1_pos _
  rw [Real.rpow_neg E.worldY1_pos.le, eq_div_iff (by positivity)]
  field_simp
  linarith

/-- **Actuarially fair prices iff no aggregate risk**, O&R p. 287: for `ρ > 0` and positive
state probabilities, `p(s) = π(s)` for every state iff world date-2 output is the same in
all states. -/
theorem fair_iff_no_aggregate_risk :
    (∀ s, E.p s = E.Ω.prob s) ↔ ∀ s s', E.worldY2 s = E.worldY2 s' := by
  have hK := E.kernel_sum_pos
  constructor
  · intro h
    -- every `Y₂ᵂ(s)^{-ρ}` equals the normalising sum
    have key : ∀ s, E.worldY2 s ^ (-E.ρ) = ∑ s', E.Ω.prob s' * E.worldY2 s' ^ (-E.ρ) := by
      intro s
      have h1 := E.price_formula s
      rw [h s, eq_div_iff hK.ne'] at h1
      have hp := E.prob_pos s
      nlinarith [mul_left_cancel₀ hp.ne' (show E.Ω.prob s *
        (∑ s', E.Ω.prob s' * E.worldY2 s' ^ (-E.ρ)) =
          E.Ω.prob s * E.worldY2 s ^ (-E.ρ) by linarith)]
    intro s s'
    exact rpow_neg_inj (E.worldY2_pos s) (E.worldY2_pos s') E.rho_pos.ne'
      ((key s).trans (key s').symm)
  · intro h s
    rw [E.price_formula s]
    obtain ⟨s0⟩ : Nonempty S := ⟨s⟩
    have hc : ∀ s', E.worldY2 s' ^ (-E.ρ) = E.worldY2 s0 ^ (-E.ρ) := fun s' => by rw [h s' s0]
    simp only [hc]
    rw [← Finset.sum_mul, E.Ω.prob_sum, one_mul]
    have : 0 < E.worldY2 s0 ^ (-E.ρ) := Real.rpow_pos_of_pos (E.worldY2_pos s0) _
    field_simp

/-- Home's consumption share `μ = C₁/Y₁ᵂ`, O&R p. 288. -/
noncomputable def share : ℝ := E.C1 / E.worldY1

/-- The share lies strictly between zero and one. -/
theorem share_mem : 0 < E.share ∧ E.share < 1 := by
  have h1 := E.C1_pos; have h2 := E.C1f_pos; have hY := E.worldY1_pos
  unfold share
  refine ⟨div_pos h1 hY, (div_lt_one hY).2 ?_⟩
  unfold worldY1; rw [← E.clear1]; linarith

/-- Home date-1 consumption is the share `μ` of world output, O&R p. 289. -/
theorem C1_eq : E.C1 = E.share * E.worldY1 := by
  unfold share; field_simp [E.worldY1_pos.ne']

/-- Foreign date-1 consumption is the share `1 − μ` of world output, O&R p. 289. -/
theorem C1f_eq : E.C1f = (1 - E.share) * E.worldY1 := by
  have h := E.C1_eq
  have hc : E.C1 + E.C1f = E.worldY1 := E.clear1
  linarith [show (1 - E.share) * E.worldY1 = E.worldY1 - E.share * E.worldY1 by ring]

/-- **Constant consumption shares**, O&R (35)–(36), p. 288–289: Home consumes the same
fraction `μ` of world output in every state of date 2 as on date 1. -/
theorem C2_eq (s : S) : E.C2 s = E.share * E.worldY2 s := by
  have h := E.growth_eq_world s
  have h1 := E.C1_pos; have hY := E.worldY1_pos
  unfold share
  rw [div_eq_div_iff h1.ne' hY.ne'] at h
  field_simp
  linarith

/-- Foreign consumes the constant fraction `1 − μ` of world date-2 output, O&R p. 289. -/
theorem C2f_eq (s : S) : E.C2f s = (1 - E.share) * E.worldY2 s := by
  have h := E.C2_eq s
  have hc : E.C2 s + E.C2f s = E.worldY2 s := E.clear2 s
  linarith [show (1 - E.share) * E.worldY2 s = E.worldY2 s - E.share * E.worldY2 s by ring]

/-- Equation (35), p. 288, in the book's form: `C₂(s)/C₂(s′) = C₂*(s)/C₂*(s′) =
Y₂ᵂ(s)/Y₂ᵂ(s′)`. -/
theorem consumption_ratio_across_states (s s' : S) :
    E.C2 s / E.C2 s' = E.worldY2 s / E.worldY2 s' ∧
      E.C2f s / E.C2f s' = E.worldY2 s / E.worldY2 s' := by
  obtain ⟨h0, h1⟩ := E.share_mem
  have : 0 < 1 - E.share := by linarith
  rw [E.C2_eq, E.C2_eq, E.C2f_eq, E.C2f_eq]
  constructor
  · rw [mul_div_mul_left _ _ h0.ne']
  · rw [mul_div_mul_left _ _ this.ne']

/-- The date-1 Arrow–Debreu price in the form `q(s) = β (Y₁ᵂ)^ρ π(s) Y₂ᵂ(s)^{-ρ}`. -/
theorem ad_price_expand (s : S) :
    E.p s / (1 + E.r) = E.β * E.worldY1 ^ E.ρ * (E.Ω.prob s * E.worldY2 s ^ (-E.ρ)) := by
  rw [E.price_expand s]; field_simp [E.gross_pos.ne']

/-- **Home's share is its share of world wealth at Arrow–Debreu prices**, O&R p. 289 and
footnote 16: `μ = (Y₁ + Σ q(s) Y₂(s)) / (Y₁ᵂ + Σ q(s) Y₂ᵂ(s))`, `q(s) = p(s)/(1 + r)`. -/
theorem share_eq_wealth_share :
    E.share = (E.Y1 + ∑ s, E.p s / (1 + E.r) * E.Y2 s) /
      (E.worldY1 + ∑ s, E.p s / (1 + E.r) * E.worldY2 s) := by
  have hq : ∀ s, 0 < E.p s / (1 + E.r) := fun s => by
    rw [E.ad_price_expand s]
    have := Real.rpow_pos_of_pos E.worldY1_pos E.ρ
    have := Real.rpow_pos_of_pos (E.worldY2_pos s) (-E.ρ)
    have := E.prob_pos s; have := E.beta_pos
    positivity
  have hD : 0 < E.worldY1 + ∑ s, E.p s / (1 + E.r) * E.worldY2 s := by
    have := E.worldY1_pos
    have := Finset.sum_nonneg (fun s (_ : s ∈ Finset.univ) =>
      (mul_pos (hq s) (E.worldY2_pos s)).le)
    linarith
  rw [eq_div_iff hD.ne', ← E.budget, E.C1_eq]
  simp only [E.C2_eq]
  have e : ∀ s, E.p s / (1 + E.r) * (E.share * E.worldY2 s) =
      E.share * (E.p s / (1 + E.r) * E.worldY2 s) := fun s => by ring
  simp only [e, ← Finset.mul_sum]
  ring

/-- **Closed form for the consumption share**, O&R footnote 16, p. 289:
`μ = [Y₁(Y₁ᵂ)^{-ρ} + β Σ π(s) Y₂(s) Y₂ᵂ(s)^{-ρ}] / [(Y₁ᵂ)^{1-ρ} + β Σ π(s) Y₂ᵂ(s)^{1-ρ}]`. -/
theorem share_closed_form :
    E.share = (E.Y1 * E.worldY1 ^ (-E.ρ) +
        E.β * ∑ s, E.Ω.prob s * E.Y2 s * E.worldY2 s ^ (-E.ρ)) /
      (E.worldY1 ^ (1 - E.ρ) + E.β * ∑ s, E.Ω.prob s * E.worldY2 s ^ (1 - E.ρ)) := by
  rw [E.share_eq_wealth_share]
  simp only [E.ad_price_expand]
  have hY := E.worldY1_pos
  have hA : 0 < E.worldY1 ^ E.ρ := Real.rpow_pos_of_pos hY _
  have hAi : E.worldY1 ^ (-E.ρ) = (E.worldY1 ^ E.ρ)⁻¹ := Real.rpow_neg hY.le _
  have h1 : E.worldY1 ^ (1 - E.ρ) = E.worldY1 * (E.worldY1 ^ E.ρ)⁻¹ := by
    rw [sub_eq_add_neg, Real.rpow_add hY, Real.rpow_one, hAi]
  have h2 : ∀ s, E.worldY2 s ^ (1 - E.ρ) = E.worldY2 s * E.worldY2 s ^ (-E.ρ) := fun s => by
    rw [sub_eq_add_neg, Real.rpow_add (E.worldY2_pos s), Real.rpow_one]
  simp only [h2]
  rw [hAi, h1]
  have eN : E.Y1 + ∑ s, E.β * E.worldY1 ^ E.ρ *
      (E.Ω.prob s * E.worldY2 s ^ (-E.ρ)) * E.Y2 s =
      E.worldY1 ^ E.ρ * (E.Y1 * (E.worldY1 ^ E.ρ)⁻¹ +
        E.β * ∑ s, E.Ω.prob s * E.Y2 s * E.worldY2 s ^ (-E.ρ)) := by
    rw [mul_add, Finset.mul_sum, Finset.mul_sum]
    congr 1
    · field_simp
    · exact Finset.sum_congr rfl fun s _ => by ring
  have eD : E.worldY1 + ∑ s, E.β * E.worldY1 ^ E.ρ *
      (E.Ω.prob s * E.worldY2 s ^ (-E.ρ)) * E.worldY2 s =
      E.worldY1 ^ E.ρ * (E.worldY1 * (E.worldY1 ^ E.ρ)⁻¹ +
        E.β * ∑ s, E.Ω.prob s * (E.worldY2 s * E.worldY2 s ^ (-E.ρ))) := by
    rw [mul_add, Finset.mul_sum, Finset.mul_sum]
    congr 1
    · field_simp
    · exact Finset.sum_congr rfl fun s _ => by ring
  rw [eN, eD, mul_div_mul_left _ _ hA.ne']

end GlobalEqm

/-! ## The social planner (footnote 17) -/

/-- CRRA period utility `u(C) = C^{1-ρ}/(1 − ρ)`, O&R (13), p. 277 (for `ρ ≠ 1`). -/
noncomputable def crraU (ρ c : ℝ) : ℝ := c ^ (1 - ρ) / (1 - ρ)

/-- Normalised tangent-line inequality for powers: for `y > 0`, `t < 1`, `t ≠ 0`,
`(y^t − 1)/t ≤ y − 1` (Bernoulli for `0 < t < 1`, weighted AM–GM for `t < 0`). Used for
the concavity argument behind O&R footnote 17. -/
theorem pow_tangent {t y : ℝ} (ht1 : t < 1) (ht0 : t ≠ 0) (hy : 0 < y) :
    (y ^ t - 1) / t ≤ y - 1 := by
  rcases lt_or_gt_of_ne ht0 with ht | ht
  · rw [div_le_iff_of_neg ht]
    have hw1 : 0 ≤ 1 / (1 - t) := by apply div_nonneg <;> linarith
    have hw2 : 0 ≤ -t / (1 - t) := by apply div_nonneg <;> linarith
    have hne : 1 - t ≠ 0 := by linarith
    have hw : 1 / (1 - t) + -t / (1 - t) = 1 := by field_simp; ring
    have h := Real.geom_mean_le_arith_mean2_weighted hw1 hw2
      (Real.rpow_nonneg hy.le t) hy.le hw
    rw [← Real.rpow_mul hy.le, ← Real.rpow_add hy,
      show t * (1 / (1 - t)) + -t / (1 - t) = 0 by field_simp; ring, Real.rpow_zero] at h
    have h' : 1 - t ≤ y ^ t - t * y := by
      have hpos : 0 < 1 - t := by linarith
      have := mul_le_mul_of_nonneg_left h hpos.le
      have e : (1 - t) * (1 / (1 - t) * y ^ t + -t / (1 - t) * y) = y ^ t - t * y := by
        field_simp; ring
      linarith
    linarith
  · rw [div_le_iff₀ ht]
    have h := rpow_one_add_le_one_add_mul_self (s := y - 1) (by linarith) ht.le ht1.le
    rw [show 1 + (y - 1) = y by ring] at h
    linarith

/-- **CRRA utility lies below its tangent**: for `ρ > 0`, `ρ ≠ 1`, `a, x > 0`,
`u(x) ≤ u(a) + a^{-ρ}(x − a)` (concavity of CRRA utility, used for footnote 17). -/
theorem crraU_le_tangent {ρ a x : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≠ 1) (ha : 0 < a) (hx : 0 < x) :
    crraU ρ x ≤ crraU ρ a + a ^ (-ρ) * (x - a) := by
  have ht1 : 1 - ρ < 1 := by linarith
  have ht0 : 1 - ρ ≠ 0 := sub_ne_zero.2 (Ne.symm hρ1)
  have hy : 0 < x / a := div_pos hx ha
  have key := pow_tangent ht1 ht0 hy
  have hA : 0 < a ^ (1 - ρ) := Real.rpow_pos_of_pos ha _
  have hxa : x ^ (1 - ρ) = a ^ (1 - ρ) * (x / a) ^ (1 - ρ) := by
    rw [← Real.mul_rpow ha.le hy.le, mul_div_cancel₀ _ ha.ne']
  have hat : a ^ (-ρ) = a ^ (1 - ρ) / a := by
    rw [show -ρ = (1 - ρ) - 1 by ring]; exact Real.rpow_sub_one ha.ne' _
  unfold crraU
  rw [hxa, hat]
  have e1 : a ^ (1 - ρ) * (x / a) ^ (1 - ρ) / (1 - ρ) =
      a ^ (1 - ρ) / (1 - ρ) + a ^ (1 - ρ) * (((x / a) ^ (1 - ρ) - 1) / (1 - ρ)) := by
    field_simp; ring
  have e2 : a ^ (1 - ρ) / a * (x - a) = a ^ (1 - ρ) * (x / a - 1) := by
    field_simp
  rw [e1, e2]
  have := mul_le_mul_of_nonneg_left key hA.le
  linarith

/-- One pooling step of the planner problem: if `κ a^{-ρ} = (1 − κ) a*^{-ρ}` (equal weighted
marginal utilities) and `d + d* = a + a*`, then `κu(d) + (1−κ)u(d*) ≤ κu(a) + (1−κ)u(a*)`. -/
theorem planner_pair_le {ρ κ a af d df : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≠ 1) (hκ0 : 0 ≤ κ)
    (hκ1 : κ ≤ 1) (ha : 0 < a) (haf : 0 < af) (hd : 0 < d) (hdf : 0 < df)
    (hfoc : κ * a ^ (-ρ) = (1 - κ) * af ^ (-ρ)) (hfeas : d + df = a + af) :
    κ * crraU ρ d + (1 - κ) * crraU ρ df ≤ κ * crraU ρ a + (1 - κ) * crraU ρ af := by
  have h1 := mul_le_mul_of_nonneg_left (crraU_le_tangent hρ0 hρ1 ha hd) hκ0
  have h2 := mul_le_mul_of_nonneg_left (crraU_le_tangent hρ0 hρ1 haf hdf)
    (by linarith : (0 : ℝ) ≤ 1 - κ)
  have e : κ * (a ^ (-ρ) * (d - a)) + (1 - κ) * (af ^ (-ρ) * (df - af)) = 0 := by
    have : df - af = -(d - a) := by linarith
    rw [this]
    linear_combination (d - a) * hfoc
  nlinarith

/-- The planner's weight on Home, O&R footnote 17, p. 289: `κ = μ^ρ/(μ^ρ + (1 − μ)^ρ)`. -/
noncomputable def plannerWeight (ρ μ : ℝ) : ℝ := μ ^ ρ / (μ ^ ρ + (1 - μ) ^ ρ)

/-- The planner weight lies in `(0, 1)` for `0 < μ < 1`. -/
theorem plannerWeight_mem {ρ μ : ℝ} (h0 : 0 < μ) (h1 : μ < 1) :
    0 < plannerWeight ρ μ ∧ plannerWeight ρ μ < 1 := by
  have a : 0 < μ ^ ρ := Real.rpow_pos_of_pos h0 _
  have b : 0 < (1 - μ) ^ ρ := Real.rpow_pos_of_pos (by linarith) _
  unfold plannerWeight
  exact ⟨div_pos a (by linarith), (div_lt_one (by linarith)).2 (by linarith)⟩

/-- **Planner first-order condition**, O&R footnote 17: with `κ = μ^ρ/(μ^ρ + (1−μ)^ρ)`,
constant shares `μ`, `1 − μ` of any positive output `Y` equate weighted marginal utilities:
`κ(μY)^{-ρ} = (1 − κ)((1 − μ)Y)^{-ρ}`. -/
theorem planner_foc {ρ μ Y : ℝ} (h0 : 0 < μ) (h1 : μ < 1) (hY : 0 < Y) :
    plannerWeight ρ μ * (μ * Y) ^ (-ρ) = (1 - plannerWeight ρ μ) * ((1 - μ) * Y) ^ (-ρ) := by
  have h1' : 0 < 1 - μ := by linarith
  have a : 0 < μ ^ ρ := Real.rpow_pos_of_pos h0 _
  have b : 0 < (1 - μ) ^ ρ := Real.rpow_pos_of_pos h1' _
  rw [Real.mul_rpow h0.le hY.le, Real.mul_rpow h1'.le hY.le, Real.rpow_neg h0.le,
    Real.rpow_neg h1'.le]
  unfold plannerWeight
  field_simp
  ring

/-- The utilitarian objective `κU + (1 − κ)U*`, O&R footnote 17, with
`U = u(C₁) + β E u(C₂)` and CRRA `u`. -/
noncomputable def socialWelfare (Ω : StateSpace S) (β ρ κ D1 D1f : ℝ) (D2 D2f : S → ℝ) : ℝ :=
  κ * (crraU ρ D1 + β * Ω.expect (fun s => crraU ρ (D2 s))) +
    (1 - κ) * (crraU ρ D1f + β * Ω.expect (fun s => crraU ρ (D2f s)))

/-- Social welfare regrouped date by date and state by state. -/
theorem socialWelfare_eq (Ω : StateSpace S) (β ρ κ D1 D1f : ℝ) (D2 D2f : S → ℝ) :
    socialWelfare Ω β ρ κ D1 D1f D2 D2f =
      (κ * crraU ρ D1 + (1 - κ) * crraU ρ D1f) +
        β * ∑ s, Ω.prob s * (κ * crraU ρ (D2 s) + (1 - κ) * crraU ρ (D2f s)) := by
  unfold socialWelfare StateSpace.expect
  simp only [mul_add, Finset.mul_sum, Finset.sum_add_distrib]
  have e1 : ∀ s, β * (Ω.prob s * (κ * crraU ρ (D2 s))) = κ * (β * (Ω.prob s * crraU ρ (D2 s))) :=
    fun s => by ring
  have e2 : ∀ s, β * (Ω.prob s * ((1 - κ) * crraU ρ (D2f s))) =
      (1 - κ) * (β * (Ω.prob s * crraU ρ (D2f s))) := fun s => by ring
  simp only [e1, e2]
  ring

namespace GlobalEqm

variable (E : GlobalEqm S)

/-- **The equilibrium is the planner's optimum**, O&R footnote 17, p. 289: with CRRA utility
(`ρ ≠ 1`) and `κ = μ^ρ/(μ^ρ + (1 − μ)^ρ)`, the equilibrium allocation maximises
`κU + (1 − κ)U*` over all positive allocations that exhaust world output on both dates. -/
theorem planner_optimal (hρ1 : E.ρ ≠ 1) (D1 D1f : ℝ) (D2 D2f : S → ℝ) (h1 : 0 < D1)
    (h1f : 0 < D1f) (h2 : ∀ s, 0 < D2 s) (h2f : ∀ s, 0 < D2f s)
    (hf1 : D1 + D1f = E.worldY1) (hf2 : ∀ s, D2 s + D2f s = E.worldY2 s) :
    socialWelfare E.Ω E.β E.ρ (plannerWeight E.ρ E.share) D1 D1f D2 D2f ≤
      socialWelfare E.Ω E.β E.ρ (plannerWeight E.ρ E.share) E.C1 E.C1f E.C2 E.C2f := by
  obtain ⟨hμ0, hμ1⟩ := E.share_mem
  obtain ⟨hκ0, hκ1⟩ := plannerWeight_mem (ρ := E.ρ) hμ0 hμ1
  rw [socialWelfare_eq, socialWelfare_eq]
  have d1 := planner_pair_le E.rho_pos hρ1 hκ0.le hκ1.le E.C1_pos E.C1f_pos h1 h1f
    (by rw [E.C1_eq, E.C1f_eq]; exact planner_foc hμ0 hμ1 E.worldY1_pos)
    (by rw [hf1]; exact E.clear1.symm)
  have d2 : ∀ s, E.Ω.prob s * (plannerWeight E.ρ E.share * crraU E.ρ (D2 s) +
      (1 - plannerWeight E.ρ E.share) * crraU E.ρ (D2f s)) ≤
      E.Ω.prob s * (plannerWeight E.ρ E.share * crraU E.ρ (E.C2 s) +
      (1 - plannerWeight E.ρ E.share) * crraU E.ρ (E.C2f s)) := fun s =>
    mul_le_mul_of_nonneg_left (planner_pair_le E.rho_pos hρ1 hκ0.le hκ1.le (E.C2_pos s)
      (E.C2f_pos s) (h2 s) (h2f s)
      (by rw [E.C2_eq, E.C2f_eq]; exact planner_foc hμ0 hμ1 (E.worldY2_pos s))
      (by rw [hf2 s]; exact (E.clear2 s).symm)) (E.Ω.prob_nonneg s)
  have := mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun s (_ : s ∈ Finset.univ) => d2 s)
    E.beta_pos.le
  linarith

end GlobalEqm

/-! ## Different risk aversion and discount factors: equation (37) -/

/-- **Consumption growth across countries with different `ρ`, `β`**, O&R (37), p. 290: if
countries `n` and `m` face the same Arrow–Debreu price `q` for a state of probability `π > 0`
and their CRRA Euler equations (34) hold, then
`log(c₂ⁿ/c₁ⁿ) = (ρₘ/ρₙ) log(c₂ᵐ/c₁ᵐ) + (1/ρₙ) log(βₙ/βₘ)`. -/
theorem log_growth_relation {q π βn βm ρn ρm c1n c2n c1m c2m : ℝ} (hπ : 0 < π)
    (hβn : 0 < βn) (hβm : 0 < βm) (hρn : 0 < ρn) (h1n : 0 < c1n) (h2n : 0 < c2n)
    (h1m : 0 < c1m) (h2m : 0 < c2m)
    (hn : q * c1n ^ (-ρn) = π * βn * c2n ^ (-ρn))
    (hm : q * c1m ^ (-ρm) = π * βm * c2m ^ (-ρm)) :
    Real.log (c2n / c1n) =
      ρm / ρn * Real.log (c2m / c1m) + 1 / ρn * Real.log (βn / βm) := by
  have en := (crra_euler_iff h1n h2n).1 hn
  have em := (crra_euler_iff h1m h2m).1 hm
  have gn : 0 < c2n / c1n := div_pos h2n h1n
  have gm : 0 < c2m / c1m := div_pos h2m h1m
  have h : π * βn * (c2n / c1n) ^ (-ρn) = π * βm * (c2m / c1m) ^ (-ρm) := en.symm.trans em
  have hl := congrArg Real.log h
  have pn : 0 < (c2n / c1n) ^ (-ρn) := Real.rpow_pos_of_pos gn _
  have pm : 0 < (c2m / c1m) ^ (-ρm) := Real.rpow_pos_of_pos gm _
  rw [Real.log_mul (by positivity) pn.ne', Real.log_mul hπ.ne' hβn.ne',
    Real.log_mul (by positivity) pm.ne', Real.log_mul hπ.ne' hβm.ne',
    Real.log_rpow gn, Real.log_rpow gm] at hl
  rw [Real.log_div hβn.ne' hβm.ne']
  field_simp
  linarith

/-- Correlation is symmetric. -/
theorem corr_symm (Ω : StateSpace S) (X Y : S → ℝ) : Ω.corr X Y = Ω.corr Y X := by
  unfold StateSpace.corr
  rw [Ω.cov_comm, mul_comm]

/-- **Perfectly correlated consumption growth**, O&R (37) and footnote 18, p. 290: with
state-contingent prices common to countries `n` and `m`, CRRA Euler equations, possibly
different `ρₙ, ρₘ > 0` and `βₙ, βₘ > 0`, and non-degenerate consumption growth in `m`, the
log consumption growth rates have correlation one. -/
theorem corr_growth_eq_one (Ω : StateSpace S) {q : S → ℝ} {βn βm ρn ρm c1n c1m : ℝ}
    {c2n c2m : S → ℝ} (hπ : ∀ s, 0 < Ω.prob s) (hβn : 0 < βn) (hβm : 0 < βm)
    (hρn : 0 < ρn) (hρm : 0 < ρm) (h1n : 0 < c1n) (h2n : ∀ s, 0 < c2n s)
    (h1m : 0 < c1m) (h2m : ∀ s, 0 < c2m s)
    (hn : ∀ s, q s * c1n ^ (-ρn) = Ω.prob s * βn * c2n s ^ (-ρn))
    (hm : ∀ s, q s * c1m ^ (-ρm) = Ω.prob s * βm * c2m s ^ (-ρm))
    (hvar : 0 < Ω.var (fun s => Real.log (c2m s / c1m))) :
    Ω.corr (fun s => Real.log (c2n s / c1n)) (fun s => Real.log (c2m s / c1m)) = 1 := by
  have hfun : (fun s => Real.log (c2n s / c1n)) = fun s =>
      1 / ρn * Real.log (βn / βm) + ρm / ρn * Real.log (c2m s / c1m) := by
    funext s
    rw [log_growth_relation (hπ s) hβn hβm hρn h1n (h2n s) h1m (h2m s) (hn s) (hm s)]
    ring
  rw [hfun, corr_symm]
  exact Ω.corr_affine (div_pos hρm hρn) hvar

/-! ## Efficient investment under uncertainty (§5.2.4) -/

/-- The firm's present value, O&R p. 298: `Σ_s q(s)[A(s)F(K) + K] − K` with
`q(s) = p(s)/(1 + r)`, zero depreciation and `K₁ = 0`. -/
def firmValue (q A : S → ℝ) (F : ℝ → ℝ) (K : ℝ) : ℝ := ∑ s, q s * (A s * F K + K) - K

/-- The derivative of the firm's present value in `K`, O&R p. 298. -/
theorem firmValue_hasDerivAt (q A : S → ℝ) {F : ℝ → ℝ} {F' K : ℝ} (hF : HasDerivAt F F' K) :
    HasDerivAt (firmValue q A F) (∑ s, q s * (A s * F' + 1) - 1) K := by
  unfold firmValue
  have hs : ∀ s ∈ (Finset.univ : Finset S), HasDerivAt (fun k => q s * (A s * F k + k))
      (q s * (A s * F' + 1)) K := fun s _ =>
    HasDerivAt.const_mul (q s) (HasDerivAt.add (HasDerivAt.const_mul (A s) hF) (hasDerivAt_id K))
  exact HasDerivAt.sub (HasDerivAt.fun_sum hs) (hasDerivAt_id K)

/-- **Investment first-order condition**, O&R (40), p. 298: at an (interior, local) maximum
of the firm's present value, `Σ_s q(s)[A(s)F′(K₂) + 1] = 1`. -/
theorem investment_foc (q A : S → ℝ) {F : ℝ → ℝ} {F' K : ℝ} (hF : HasDerivAt F F' K)
    (hmax : IsLocalMax (firmValue q A F) K) : ∑ s, q s * (A s * F' + 1) = 1 := by
  have := hmax.hasDerivAt_eq_zero (firmValue_hasDerivAt q A hF)
  linarith

/-- **The marginal value product of capital equals the world interest rate**, O&R p. 298:
with `q = p/(1 + r)` and `Σ p(s) = 1`, (40) is `Σ_s p(s) A(s) F′(K₂) = r`; the same `r` for
Home and Foreign firms. -/
theorem investment_rate {p A : S → ℝ} {r F' : ℝ} (hr : 1 + r ≠ 0) (hp : ∑ s, p s = 1)
    (hfoc : ∑ s, p s / (1 + r) * (A s * F' + 1) = 1) : ∑ s, p s * A s * F' = r := by
  have e : ∑ s, p s / (1 + r) * (A s * F' + 1) =
      (∑ s, p s * A s * F' + ∑ s, p s) / (1 + r) := by
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    exact Finset.sum_congr rfl fun s _ => by field_simp
  rw [e, hp, div_eq_one_iff_eq hr] at hfoc
  linarith

/-- **Investment Euler equation**, O&R (41), p. 298: if the Euler equations (5)
`q(s) u′(C₁) = π(s) β u′(C₂(s))` hold and the firm satisfies (40), then
`u′(C₁) = Σ_s π(s) β u′(C₂(s)) [A(s)F′(K₂) + 1]`. Here `mu1 = u′(C₁)`, `mu2 s = u′(C₂(s))`;
the same holds for Foreign consumption with Home's investment, since prices are common. -/
theorem investment_euler {q π A mu2 : S → ℝ} {β mu1 F' : ℝ}
    (heuler : ∀ s, q s * mu1 = π s * β * mu2 s) (hfoc : ∑ s, q s * (A s * F' + 1) = 1) :
    mu1 = ∑ s, π s * β * mu2 s * (A s * F' + 1) := by
  calc mu1 = (∑ s, q s * (A s * F' + 1)) * mu1 := by rw [hfoc, one_mul]
    _ = ∑ s, q s * mu1 * (A s * F' + 1) := by
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun s _ => by ring
    _ = _ := Finset.sum_congr rfl fun s _ => by rw [heuler s]

/-- **Prices with investment under log utility**, O&R §5.2.4.1, p. 298: with Euler equations
`q(s)/C₁ = π(s)β/C₂(s)` in both countries and market clearing
`C₁ + C₁* = Y₁ᵂ − K₂ − K₂*`, `C₂(s) + C₂*(s) = Y₂ᵂ(s) + K₂ + K₂*`,
`q(s) = π(s)β(Y₁ᵂ − K₂ − K₂*)/(Y₂ᵂ(s) + K₂ + K₂*)`. -/
theorem log_investment_price {q π β C1 C1f C2 C2f Y1W Y2W K Kf : ℝ} (h1 : 0 < C1)
    (h1f : 0 < C1f) (h2 : 0 < C2) (h2f : 0 < C2f)
    (he : q / C1 = π * β / C2) (hef : q / C1f = π * β / C2f)
    (hc1 : C1 + C1f = Y1W - K - Kf) (hc2 : C2 + C2f = Y2W + K + Kf) :
    q = π * β * (Y1W - K - Kf) / (Y2W + K + Kf) := by
  rw [div_eq_div_iff h1.ne' h2.ne'] at he
  rw [div_eq_div_iff h1f.ne' h2f.ne'] at hef
  rw [← hc1, ← hc2, eq_div_iff (by linarith)]
  linarith

/-- **World investment in the log/linear example**, O&R §5.2.4.1, p. 299: with `F(K) = K`,
if both firms' first-order conditions hold at the log-utility prices,
`Σ_s π(s)β(Y₁ᵂ − K₂ − K₂*)/(A(s)K₂ + A*(s)K₂* + K₂ + K₂*) · [A(s) + 1] = 1` and the same with
`A*`, then `K₂ + K₂* = βY₁ᵂ/(1 + β)`. (Nonnegativity of investment is not imposed.) -/
theorem log_linear_world_investment (Ω : StateSpace S) {A Af : S → ℝ} {β Y1W K Kf : ℝ}
    (hβ : 0 < β) (hD : ∀ s, 0 < A s * K + Af s * Kf + K + Kf)
    (hfoc : ∑ s, Ω.prob s * β * (Y1W - K - Kf) / (A s * K + Af s * Kf + K + Kf) *
      (A s + 1) = 1)
    (hfocf : ∑ s, Ω.prob s * β * (Y1W - K - Kf) / (A s * K + Af s * Kf + K + Kf) *
      (Af s + 1) = 1) :
    K + Kf = β * Y1W / (1 + β) := by
  have e : K * (∑ s, Ω.prob s * β * (Y1W - K - Kf) / (A s * K + Af s * Kf + K + Kf) *
      (A s + 1)) + Kf * (∑ s, Ω.prob s * β * (Y1W - K - Kf) /
        (A s * K + Af s * Kf + K + Kf) * (Af s + 1)) = ∑ s, Ω.prob s * β * (Y1W - K - Kf) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    set X := Ω.prob s * β * (Y1W - K - Kf)
    set D := A s * K + Af s * Kf + K + Kf with hDdef
    calc K * (X / D * (A s + 1)) + Kf * (X / D * (Af s + 1))
        = X / D * ((A s + 1) * K + (Af s + 1) * Kf) := by ring
      _ = X / D * D := by rw [hDdef]; ring
      _ = X := div_mul_cancel₀ X (hD s).ne'
  rw [hfoc, hfocf, ← Finset.sum_mul, ← Finset.sum_mul, Ω.prob_sum, one_mul] at e
  have hsum : K + Kf = β * (Y1W - K - Kf) := by linarith
  rw [eq_div_iff (by linarith)]
  linarith

/-! ## Exercise 2: risk neutrality at date 2 -/

/-- **Exercise 2**, O&R p. 345: with `U = log C₁ + β Σ π(s) C₂(s)` in both countries, the
Euler equations `q(s)/C₁ = π(s)β` and `q(s)/C₁* = π(s)β` with `q = p/(1 + r)`, clearing
`C₁ + C₁* = Y₁ᵂ` and `Σ p(s) = 1` imply `C₁ = C₁* = Y₁ᵂ/2`, actuarially fair prices
`p(s) = π(s)`, and `1 + r = 2/(βY₁ᵂ)`. -/
theorem exercise2 (Ω : StateSpace S) {p : S → ℝ} {β r C1 C1f Y1W : ℝ} (hβ : 0 < β)
    (hr : 0 < 1 + r) (h1 : 0 < C1) (h1f : 0 < C1f)
    (he : ∀ s, p s / (1 + r) / C1 = Ω.prob s * β)
    (hef : ∀ s, p s / (1 + r) / C1f = Ω.prob s * β)
    (hc : C1 + C1f = Y1W) (hp : ∑ s, p s = 1) :
    C1 = Y1W / 2 ∧ C1f = Y1W / 2 ∧ (∀ s, p s = Ω.prob s) ∧ 1 + r = 2 / (β * Y1W) := by
  -- sum each Euler equation over states
  have hs : ∀ C : ℝ, 0 < C → (∀ s, p s / (1 + r) / C = Ω.prob s * β) →
      1 = (1 + r) * β * C := by
    intro C hC h
    have : ∑ s, p s / (1 + r) / C = ∑ s, Ω.prob s * β := Finset.sum_congr rfl fun s _ => h s
    rw [← Finset.sum_div, ← Finset.sum_div, hp, ← Finset.sum_mul, Ω.prob_sum, one_mul] at this
    field_simp at this
    linarith
  have a := hs C1 h1 he
  have b := hs C1f h1f hef
  have hrb : 0 < (1 + r) * β := mul_pos hr hβ
  have heq : C1 = C1f := by
    have : (1 + r) * β * C1 = (1 + r) * β * C1f := by linarith
    exact mul_left_cancel₀ hrb.ne' this
  have hC1 : C1 = Y1W / 2 := by linarith
  refine ⟨hC1, by linarith, fun s => ?_, ?_⟩
  · have h := he s
    rw [div_div, div_eq_iff (by positivity)] at h
    calc p s = Ω.prob s * ((1 + r) * β * C1) := by rw [h]; ring
      _ = Ω.prob s := by rw [← a, mul_one]
  · have hY : 0 < Y1W := by linarith
    rw [eq_div_iff (by positivity)]
    rw [hC1] at a
    linarith

/-- **Exercise 2: the date-2 allocation is indeterminate**, O&R p. 345. With fair prices
`p = π`, any reallocation `C₂ ↦ C₂ + D`, `C₂* ↦ C₂* − D` of zero expected value leaves both
countries' intertemporal budgets and date-2 market clearing unchanged; the Euler equations
of Exercise 2 do not involve date-2 consumption at all, so only the value of date-2
consumption is pinned down. -/
theorem exercise2_indeterminate (Ω : StateSpace S) {r : ℝ} {C2 C2f Y2 Y2f D : S → ℝ}
    (hD : Ω.expect D = 0) :
    (∑ s, Ω.prob s / (1 + r) * (C2 s + D s) = ∑ s, Ω.prob s / (1 + r) * C2 s) ∧
      (∑ s, Ω.prob s / (1 + r) * (C2f s - D s) = ∑ s, Ω.prob s / (1 + r) * C2f s) ∧
      ((∀ s, C2 s + C2f s = Y2 s + Y2f s) →
        ∀ s, (C2 s + D s) + (C2f s - D s) = Y2 s + Y2f s) := by
  have key : ∑ s, Ω.prob s / (1 + r) * D s = 0 := by
    have : ∑ s, Ω.prob s / (1 + r) * D s = Ω.expect D / (1 + r) := by
      unfold StateSpace.expect; rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun s _ => by ring
    rw [this, hD, zero_div]
  refine ⟨?_, ?_, fun h s => by linarith [h s]⟩
  · simp only [mul_add, Finset.sum_add_distrib, key, add_zero]
  · simp only [mul_sub, Finset.sum_sub_distrib, key, sub_zero]

end ObstfeldRogoff.InternationalFinancialMarkets.GlobalEquilibrium

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Aggregation under complete markets

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §5.2.2,
pp. 292–294, footnotes 20–21.

* With complete markets and HARA period utility `u(c) = (a₀ + a₁c)^{1-ρ}/(1 − ρ)` common to
  all agents (common `a₀, a₁, ρ, β`), per-capita consumption satisfies the representative
  agent's Euler equation (39), and per-capita consumption satisfies the per-capita budget
  constraint.
* With distinct CRRA coefficients `ρᵢ`, the geometric means `c̃` of consumption satisfy a
  CRRA Euler equation whose coefficient `ρ̃` is the harmonic mean of the `ρᵢ` (p. 294).
* Footnote 21: with a riskless bond as the only asset, aggregation fails; we give an explicit
  two-agent, two-state log-utility counterexample.
-/

namespace ObstfeldRogoff.InternationalFinancialMarkets.Aggregation

open Finset

variable {ι : Type} [Fintype ι]

/-- The HARA/CRRA Euler equation solved for levels, O&R p. 292: for positive `x₁, x₂, m` and
`ρ ≠ 0`, `x₁^{-ρ} = m x₂^{-ρ}` iff `x₁ = m^{(-ρ)⁻¹} x₂` (raise both sides to `−1/ρ`). -/
theorem euler_level_iff {x1 x2 m ρ : ℝ} (h1 : 0 < x1) (h2 : 0 < x2) (hm : 0 < m)
    (hρ : ρ ≠ 0) : x1 ^ (-ρ) = m * x2 ^ (-ρ) ↔ x1 = m ^ (-ρ)⁻¹ * x2 := by
  have hn : -ρ ≠ 0 := neg_ne_zero.2 hρ
  constructor
  · intro h
    rw [← Real.rpow_rpow_inv h1.le hn, h,
      Real.mul_rpow hm.le (Real.rpow_nonneg h2.le _), Real.rpow_rpow_inv h2.le hn]
  · intro h
    rw [h, Real.mul_rpow (Real.rpow_nonneg hm.le _) h2.le, ← Real.rpow_mul hm.le,
      inv_mul_cancel₀ hn, Real.rpow_one]

/-- The per-capita (arithmetic mean) value `Σᵢ xᵢ / I`, O&R p. 293. -/
noncomputable def perCapita (x : ι → ℝ) : ℝ := (∑ i, x i) / Fintype.card ι

/-- The per-capita value of `a₀ + a₁xᵢ` is `a₀ + a₁` times the per-capita value of `x`. -/
theorem perCapita_affine [Nonempty ι] (a0 a1 : ℝ) (x : ι → ℝ) :
    perCapita (fun i => a0 + a1 * x i) = a0 + a1 * perCapita x := by
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  unfold perCapita
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  field_simp

/-- **HARA aggregation**, O&R (39), p. 293: if every agent `i` has HARA utility with common
`a₀, a₁, ρ ≠ 0, β` and satisfies the state-`s` Euler equation
`(a₀ + a₁c₁ⁱ)^{-ρ} = [β(1 + r)π(s)/p(s)] (a₀ + a₁c₂ⁱ(s))^{-ρ}` (with positive marginal-utility
arguments), then per-capita consumption `c = Σᵢcⁱ/I` satisfies the same Euler equation. -/
theorem hara_aggregation [Nonempty ι] {a0 a1 ρ β r π p : ℝ} {c1 c2 : ι → ℝ} (hρ : ρ ≠ 0)
    (hβ : 0 < β) (hr : 0 < 1 + r) (hπ : 0 < π) (hp : 0 < p)
    (h1 : ∀ i, 0 < a0 + a1 * c1 i) (h2 : ∀ i, 0 < a0 + a1 * c2 i)
    (heuler : ∀ i, (a0 + a1 * c1 i) ^ (-ρ) = β * (1 + r) * π / p * (a0 + a1 * c2 i) ^ (-ρ)) :
    (a0 + a1 * perCapita c1) ^ (-ρ) =
      β * (1 + r) * π / p * (a0 + a1 * perCapita c2) ^ (-ρ) := by
  set m := β * (1 + r) * π / p with hmdef
  have hm : 0 < m := by positivity
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hlev : ∀ i, a0 + a1 * c1 i = m ^ (-ρ)⁻¹ * (a0 + a1 * c2 i) := fun i =>
    (euler_level_iff (h1 i) (h2 i) hm hρ).1 (heuler i)
  have hpos2 : 0 < a0 + a1 * perCapita c2 := by
    rw [← perCapita_affine]
    unfold perCapita
    exact div_pos (Finset.sum_pos (fun i _ => h2 i) Finset.univ_nonempty) hn
  have hpos1 : 0 < a0 + a1 * perCapita c1 := by
    rw [← perCapita_affine]
    unfold perCapita
    exact div_pos (Finset.sum_pos (fun i _ => h1 i) Finset.univ_nonempty) hn
  refine (euler_level_iff hpos1 hpos2 hm hρ).2 ?_
  rw [← perCapita_affine, ← perCapita_affine]
  unfold perCapita
  simp only [hlev]
  rw [← Finset.mul_sum, mul_div_assoc]

/-- **Per-capita budget constraint**, O&R p. 293: budget constraints are linear, so if every
agent satisfies `c₁ⁱ + Σ_s q(s) c₂ⁱ(s) = wⁱ`, per-capita consumption satisfies the budget
constraint with per-capita wealth. -/
theorem perCapita_budget {S : Type} [Fintype S] {q : S → ℝ} {c1 w : ι → ℝ}
    {c2 : ι → S → ℝ} (hb : ∀ i, c1 i + ∑ s, q s * c2 i s = w i) :
    perCapita c1 + ∑ s, q s * perCapita (fun i => c2 i s) = perCapita w := by
  unfold perCapita
  simp only [mul_div_assoc', ← Finset.sum_div, Finset.mul_sum]
  rw [Finset.sum_comm, ← add_div, ← Finset.sum_add_distrib]
  simp only [hb]

/-- The unweighted geometric mean `c̃ = Πᵢ (cⁱ)^{1/I}`, O&R p. 293. -/
noncomputable def geoMean (c : ι → ℝ) : ℝ := ∏ i, c i ^ (1 / (Fintype.card ι : ℝ))

/-- The harmonic mean `ρ̃ = 1/((1/I) Σᵢ 1/ρᵢ)` of risk-aversion coefficients, O&R p. 294. -/
noncomputable def harmonicMean (ρ : ι → ℝ) : ℝ :=
  1 / (1 / (Fintype.card ι : ℝ) * ∑ i, 1 / ρ i)

/-- **Geometric-mean aggregation**, O&R p. 294: if agents have CRRA utility with possibly
distinct `ρᵢ > 0` (common `β`) and all satisfy the state-`s` Euler equation
`q c₁ⁱ^{-ρᵢ} = π β c₂ⁱ^{-ρᵢ}` at the common Arrow–Debreu price `q = p(s)/(1 + r) > 0`, then the
geometric means satisfy `q = π β (c̃₂/c̃₁)^{-ρ̃}` with `ρ̃` the harmonic mean of the `ρᵢ`.
(Verified: the book's formula is correct.) -/
theorem geometric_aggregation [Nonempty ι] {q π β : ℝ} {ρ c1 c2 : ι → ℝ} (hq : 0 < q)
    (hπ : 0 < π) (hβ : 0 < β) (hρ : ∀ i, 0 < ρ i) (h1 : ∀ i, 0 < c1 i) (h2 : ∀ i, 0 < c2 i)
    (heuler : ∀ i, q * c1 i ^ (-ρ i) = π * β * c2 i ^ (-ρ i)) :
    q = π * β * (geoMean c2 / geoMean c1) ^ (-harmonicMean ρ) := by
  set m := π * β / q with hmdef
  have hm : 0 < m := by positivity
  set n : ℝ := (Fintype.card ι : ℝ) with hndef
  have hn : 0 < n := by rw [hndef]; exact_mod_cast Fintype.card_pos
  -- each agent: c₂ⁱ = m^{1/ρᵢ} c₁ⁱ
  have hlev : ∀ i, c2 i = m ^ (1 / ρ i) * c1 i := by
    intro i
    have e : c1 i ^ (-ρ i) = m * c2 i ^ (-ρ i) := by
      rw [hmdef]; field_simp; linarith [heuler i]
    have := (euler_level_iff (h1 i) (h2 i) hm (hρ i).ne').1 e
    rw [this, ← mul_assoc, ← Real.rpow_add hm]
    rw [show 1 / ρ i + (-ρ i)⁻¹ = 0 by field_simp; ring, Real.rpow_zero, one_mul]
  set e : ℝ := 1 / n * ∑ i, 1 / ρ i with hedef
  have he : 0 < e := by
    rw [hedef]
    exact mul_pos (by positivity) (Finset.sum_pos (fun i _ => by have := hρ i; positivity)
      Finset.univ_nonempty)
  have hG1 : 0 < geoMean c1 := by
    unfold geoMean
    exact Finset.prod_pos fun i _ => Real.rpow_pos_of_pos (h1 i) _
  have hG2 : geoMean c2 = m ^ e * geoMean c1 := by
    unfold geoMean
    simp only [hlev]
    simp only [Real.mul_rpow (Real.rpow_nonneg hm.le _) (h1 _).le, Finset.prod_mul_distrib,
      ← Real.rpow_mul hm.le]
    congr 1
    rw [← Real.rpow_sum_of_pos hm, hedef, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  have hH : harmonicMean ρ = 1 / e := by unfold harmonicMean; rw [hedef]
  rw [hG2, mul_div_assoc, div_self hG1.ne', mul_one, hH, ← Real.rpow_mul hm.le,
    show e * -(1 / e) = -1 by field_simp, Real.rpow_neg_one, hmdef]
  field_simp

/-! ## Footnote 21: aggregation fails with bonds only -/

/-- The bond Euler equation with log utility (`a₀ = 0`, `a₁ = 1`, `ρ = 1` in (38)) and two
states, O&R footnote 21: `c₁^{-1} = β(1 + r) Σ_s π(s) c₂(s)^{-1}`. -/
def logBondEuler (π : Fin 2 → ℝ) (βR c1 : ℝ) (c2 : Fin 2 → ℝ) : Prop :=
  c1 ^ (-1 : ℝ) = βR * ∑ s, π s * c2 s ^ (-1 : ℝ)

/-- **Aggregation fails with a riskless bond only**, O&R footnote 21, p. 293. Two equally
likely states, `β(1 + r) = 1`, log utility. Agent A consumes `c₁ = 3/2`, `c₂ = (1, 3)`; agent B
consumes `c₁ = 3/2`, `c₂ = (3, 1)`. Both satisfy their bond Euler equations (this is a
bonds-only equilibrium with zero bond trade when endowments equal these consumptions), but
per-capita consumption `c₁ = 3/2`, `c₂ = (2, 2)` violates the bond Euler equation: agents'
marginal rates of substitution between the two states differ. -/
theorem bonds_only_aggregation_fails :
    logBondEuler ![1 / 2, 1 / 2] 1 (3 / 2) ![1, 3] ∧
      logBondEuler ![1 / 2, 1 / 2] 1 (3 / 2) ![3, 1] ∧
      ¬ logBondEuler ![1 / 2, 1 / 2] 1 ((3 / 2 + 3 / 2) / 2)
        (fun s => (![1, 3] s + ![3, 1] s) / 2) := by
  unfold logBondEuler
  simp only [Real.rpow_neg_one, Fin.sum_univ_two]
  norm_num

end ObstfeldRogoff.InternationalFinancialMarkets.Aggregation

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# International portfolio diversification

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §5.3,
pp. 300–304, and Exercises 4 and 5, pp. 346–347.

`N` countries (a finite type `ι`) trade only a riskless bond and claims to each country's
date-2 output (share prices `V₁ᵐ`). Budget constraints (42)–(43), bond Euler equation (8) and
share Euler equations (44).

* §5.3.2: with identical CRRA utility, the guess `xᵐₙ = μⁿ`, `Bⁿ = 0`, `C = μⁿYᵂ`, the rate
  (49) and share prices (50) satisfy every first-order condition, budget constraint and
  market-clearing condition.
* §5.3.3: `V₁ᵐ` equals the Arrow–Debreu value of country `m`'s output at prices (30); the
  allocation satisfies every complete-markets equilibrium condition, even though `S` may
  exceed `N + 1` by any amount.
* Exercise 4: the log-utility guesses (89)–(90).
* Exercise 5: CARA utility — (a) complete markets, (b) bonds and shares with equal fund
  shares plus a riskless loan, (c) different absolute risk aversions.
-/

namespace ObstfeldRogoff.InternationalFinancialMarkets.PortfolioDiversification

open Finset

variable {ι S : Type} [Fintype ι] [Fintype S]

/-! ## The CRRA equilibrium (§5.3.2) -/

/-- World date-1 output `Y₁ᵂ = Σₘ Y₁ᵐ`, O&R (46), p. 302. -/
def worldOut1 (Y1 : ι → ℝ) : ℝ := ∑ m, Y1 m

/-- World date-2 output `Y₂ᵂ(s) = Σₘ Y₂ᵐ(s)`, O&R (47), p. 302. -/
def worldOut2 (Y2 : ι → S → ℝ) (s : S) : ℝ := ∑ m, Y2 m s

/-- The equilibrium gross interest rate, O&R (49), p. 302:
`1 + r = (Y₁ᵂ)^{-ρ} / (β Σ_s π(s) Y₂ᵂ(s)^{-ρ})`. -/
noncomputable def grossRate (Ω : StateSpace S) (β ρ : ℝ) (Y1 : ι → ℝ) (Y2 : ι → S → ℝ) : ℝ :=
  worldOut1 Y1 ^ (-ρ) / (β * ∑ s, Ω.prob s * worldOut2 Y2 s ^ (-ρ))

/-- The Arrow–Debreu price `π(s) β [Y₂ᵂ(s)/Y₁ᵂ]^{-ρ}` of O&R (30), p. 286, in the
`N`-country economy. -/
noncomputable def adPrice (Ω : StateSpace S) (β ρ : ℝ) (Y1 : ι → ℝ) (Y2 : ι → S → ℝ)
    (s : S) : ℝ :=
  Ω.prob s * β * (worldOut2 Y2 s / worldOut1 Y1) ^ (-ρ)

/-- Equilibrium share prices, O&R (50), p. 303:
`V₁ᵐ = Σ_s π(s) β [Y₂ᵂ(s)/Y₁ᵂ]^{-ρ} Y₂ᵐ(s)`. -/
noncomputable def sharePrice (Ω : StateSpace S) (β ρ : ℝ) (Y1 : ι → ℝ) (Y2 : ι → S → ℝ)
    (m : ι) : ℝ :=
  ∑ s, Ω.prob s * β * (worldOut2 Y2 s / worldOut1 Y1) ^ (-ρ) * Y2 m s

/-- Country `n`'s share of initial world wealth, O&R (45), p. 302:
`μⁿ = (Y₁ⁿ + V₁ⁿ)/Σₘ(Y₁ᵐ + V₁ᵐ)`. -/
noncomputable def wealthShare (Ω : StateSpace S) (β ρ : ℝ) (Y1 : ι → ℝ) (Y2 : ι → S → ℝ)
    (n : ι) : ℝ :=
  (Y1 n + sharePrice Ω β ρ Y1 Y2 n) / ∑ m, (Y1 m + sharePrice Ω β ρ Y1 Y2 m)

/-- Positive endowments for the §5.3.2 economy: at least one country, positive outputs,
`β > 0`. -/
structure PortfolioEconomy (ι S : Type) [Fintype ι] [Fintype S] where
  Ω : StateSpace S
  β : ℝ
  ρ : ℝ
  Y1 : ι → ℝ
  Y2 : ι → S → ℝ
  nonempty : Nonempty ι
  beta_pos : 0 < β
  Y1_pos : ∀ m, 0 < Y1 m
  Y2_pos : ∀ m s, 0 < Y2 m s

namespace PortfolioEconomy

variable (P : PortfolioEconomy ι S)

/-- Shorthand for the rate (49). -/
noncomputable def R : ℝ := grossRate P.Ω P.β P.ρ P.Y1 P.Y2

/-- Shorthand for share prices (50). -/
noncomputable def V (m : ι) : ℝ := sharePrice P.Ω P.β P.ρ P.Y1 P.Y2 m

/-- Shorthand for wealth shares (45). -/
noncomputable def μ (n : ι) : ℝ := wealthShare P.Ω P.β P.ρ P.Y1 P.Y2 n

/-- The conjectured consumption `C₁ⁿ = μⁿY₁ᵂ`, O&R (46), p. 302. -/
noncomputable def C1 (n : ι) : ℝ := P.μ n * worldOut1 P.Y1

/-- The conjectured consumption `C₂ⁿ(s) = μⁿY₂ᵂ(s)`, O&R (47), p. 302. -/
noncomputable def C2 (n : ι) (s : S) : ℝ := P.μ n * worldOut2 P.Y2 s

/-- The conjectured portfolio `xᵐₙ = μⁿ`, O&R (48), p. 302 (bond holdings are zero). -/
noncomputable def x (n _m : ι) : ℝ := P.μ n

/-- World date-1 output is positive. -/
theorem worldOut1_pos : 0 < worldOut1 P.Y1 := by
  have := P.nonempty
  exact Finset.sum_pos (fun m _ => P.Y1_pos m) Finset.univ_nonempty

/-- World date-2 output is positive in every state. -/
theorem worldOut2_pos (s : S) : 0 < worldOut2 P.Y2 s := by
  have := P.nonempty
  exact Finset.sum_pos (fun m _ => P.Y2_pos m s) Finset.univ_nonempty

/-- Share prices (50) are nonnegative. -/
theorem V_nonneg (m : ι) : 0 ≤ P.V m := by
  unfold V sharePrice
  refine Finset.sum_nonneg fun s _ => ?_
  have := P.Ω.prob_nonneg s; have := P.beta_pos; have := P.Y2_pos m s
  have := Real.rpow_nonneg (div_pos (P.worldOut2_pos s) P.worldOut1_pos).le (-P.ρ)
  positivity

/-- World wealth `Σₘ (Y₁ᵐ + V₁ᵐ)` is positive. -/
theorem wealth_pos : 0 < ∑ m, (P.Y1 m + P.V m) := by
  have := P.nonempty
  exact Finset.sum_pos (fun m _ => by linarith [P.Y1_pos m, P.V_nonneg m])
    Finset.univ_nonempty

/-- Wealth shares (45) are positive. -/
theorem μ_pos (n : ι) : 0 < P.μ n := by
  have hV := P.V_nonneg n
  unfold V at hV
  unfold μ wealthShare
  exact div_pos (by linarith [P.Y1_pos n]) P.wealth_pos

/-- Wealth shares sum to one. -/
theorem sum_μ : ∑ n, P.μ n = 1 := by
  unfold μ wealthShare
  rw [← Finset.sum_div]
  exact div_self P.wealth_pos.ne'

/-- The share price (50) in expanded form: `V₁ᵐ (Y₁ᵂ)^{-ρ} = β Σ_s π(s) Y₂ᵂ(s)^{-ρ} Y₂ᵐ(s)`. -/
theorem V_mul (m : ι) :
    P.V m * worldOut1 P.Y1 ^ (-P.ρ) =
      P.β * ∑ s, P.Ω.prob s * worldOut2 P.Y2 s ^ (-P.ρ) * P.Y2 m s := by
  unfold V sharePrice
  have hY : 0 < worldOut1 P.Y1 ^ (-P.ρ) := Real.rpow_pos_of_pos P.worldOut1_pos _
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Real.div_rpow (P.worldOut2_pos s).le P.worldOut1_pos.le]
  field_simp

/-- **Date-1 budget constraint** (42), O&R p. 303: with `Bⁿ = 0` and `xᵐₙ = μⁿ`,
`Y₁ⁿ + V₁ⁿ = C₁ⁿ + B₂ⁿ + Σₘ xᵐₙ V₁ᵐ`. -/
theorem budget_date1 (n : ι) :
    P.Y1 n + P.V n = P.C1 n + 0 + ∑ m, P.x n m * P.V m := by
  unfold C1 x
  rw [add_zero, ← Finset.mul_sum, ← mul_add, worldOut1, ← Finset.sum_add_distrib]
  unfold μ wealthShare
  exact (div_mul_cancel₀ _ P.wealth_pos.ne').symm

/-- **Date-2 budget constraint** (43), O&R p. 302: `C₂ⁿ(s) = (1 + r)B₂ⁿ + Σₘ xᵐₙ Y₂ᵐ(s)` with
`B₂ⁿ = 0`. -/
theorem budget_date2 (n : ι) (s : S) :
    P.C2 n s = P.R * 0 + ∑ m, P.x n m * P.Y2 m s := by
  unfold C2 x worldOut2
  rw [mul_zero, zero_add, Finset.mul_sum]

/-- **Bond Euler equation** (8) at the rate (49), O&R p. 302:
`C₁ⁿ^{-ρ} = (1 + r) β Σ_s π(s) C₂ⁿ(s)^{-ρ}`. -/
theorem bond_euler (n : ι) :
    P.C1 n ^ (-P.ρ) = P.R * P.β * ∑ s, P.Ω.prob s * P.C2 n s ^ (-P.ρ) := by
  have hμ := P.μ_pos n
  have hK : 0 < ∑ s, P.Ω.prob s * worldOut2 P.Y2 s ^ (-P.ρ) := by
    obtain ⟨s0, hs0⟩ : ∃ s, 0 < P.Ω.prob s := by
      by_contra h
      push Not at h
      have : ∑ s, P.Ω.prob s ≤ 0 := Finset.sum_nonpos fun s _ => h s
      rw [P.Ω.prob_sum] at this; linarith
    exact Finset.sum_pos' (fun s _ => mul_nonneg (P.Ω.prob_nonneg s)
      (Real.rpow_nonneg (P.worldOut2_pos s).le _))
      ⟨s0, Finset.mem_univ _, mul_pos hs0 (Real.rpow_pos_of_pos (P.worldOut2_pos s0) _)⟩
  unfold C1 C2 R grossRate
  simp only [Real.mul_rpow hμ.le (P.worldOut2_pos _).le, Real.mul_rpow hμ.le P.worldOut1_pos.le]
  have e : ∑ s, P.Ω.prob s * (P.μ n ^ (-P.ρ) * worldOut2 P.Y2 s ^ (-P.ρ)) =
      P.μ n ^ (-P.ρ) * ∑ s, P.Ω.prob s * worldOut2 P.Y2 s ^ (-P.ρ) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun s _ => by ring
  rw [e]
  have := P.beta_pos
  field_simp

/-- **Share Euler equations** (44) at share prices (50), O&R p. 303:
`V₁ᵐ C₁ⁿ^{-ρ} = β Σ_s π(s) C₂ⁿ(s)^{-ρ} Y₂ᵐ(s)` for every country `n` and claim `m`. -/
theorem share_euler (n m : ι) :
    P.V m * P.C1 n ^ (-P.ρ) = P.β * ∑ s, P.Ω.prob s * P.C2 n s ^ (-P.ρ) * P.Y2 m s := by
  have hμ := P.μ_pos n
  unfold C1 C2
  simp only [Real.mul_rpow hμ.le (P.worldOut2_pos _).le, Real.mul_rpow hμ.le P.worldOut1_pos.le]
  have e : ∑ s, P.Ω.prob s * (P.μ n ^ (-P.ρ) * worldOut2 P.Y2 s ^ (-P.ρ)) * P.Y2 m s =
      P.μ n ^ (-P.ρ) * ∑ s, P.Ω.prob s * worldOut2 P.Y2 s ^ (-P.ρ) * P.Y2 m s := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun s _ => by ring
  rw [e]
  have h := P.V_mul m
  calc P.V m * (P.μ n ^ (-P.ρ) * worldOut1 P.Y1 ^ (-P.ρ))
      = P.μ n ^ (-P.ρ) * (P.V m * worldOut1 P.Y1 ^ (-P.ρ)) := by ring
    _ = _ := by rw [h]; ring

/-- **Market clearing**, O&R p. 302: every country's shares are fully held
(`Σₙ xᵐₙ = 1`), bonds are in zero net supply, and consumption exhausts world output on both
dates. -/
theorem market_clearing :
    (∀ m, ∑ n, P.x n m = 1) ∧ (∑ _n : ι, (0 : ℝ)) = 0 ∧
      ∑ n, P.C1 n = worldOut1 P.Y1 ∧ ∀ s, ∑ n, P.C2 n s = worldOut2 P.Y2 s := by
  refine ⟨fun m => P.sum_μ, by simp, ?_, fun s => ?_⟩
  · unfold C1; rw [← Finset.sum_mul, P.sum_μ, one_mul]
  · unfold C2; rw [← Finset.sum_mul, P.sum_μ, one_mul]

/-! ## Efficiency of the allocation (§5.3.3) -/

/-- **Share prices are Arrow–Debreu values**, O&R p. 303 comparing (50) with (30):
`V₁ᵐ = Σ_s [p(s)/(1 + r)] Y₂ᵐ(s)` at the complete-markets prices (30). -/
theorem V_eq_ad_value (m : ι) :
    P.V m = ∑ s, adPrice P.Ω P.β P.ρ P.Y1 P.Y2 s * P.Y2 m s := rfl

/-- The complete-markets interest rate: the `p(s) = (1 + r) · adPrice(s)` implied by (49) sum
to one, O&R (7) and p. 303 comparing (49) with (33). -/
theorem ad_prices_normalised :
    ∑ s, P.R * adPrice P.Ω P.β P.ρ P.Y1 P.Y2 s = 1 := by
  have hY : 0 < worldOut1 P.Y1 ^ (-P.ρ) := Real.rpow_pos_of_pos P.worldOut1_pos _
  have hK : ∑ s, adPrice P.Ω P.β P.ρ P.Y1 P.Y2 s * worldOut1 P.Y1 ^ (-P.ρ) =
      P.β * ∑ s, P.Ω.prob s * worldOut2 P.Y2 s ^ (-P.ρ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    unfold adPrice
    rw [Real.div_rpow (P.worldOut2_pos s).le P.worldOut1_pos.le]
    field_simp
  obtain ⟨s0, hs0⟩ : ∃ s, 0 < P.Ω.prob s := by
    by_contra h'
    push Not at h'
    have : ∑ s, P.Ω.prob s ≤ 0 := Finset.sum_nonpos fun s _ => h' s
    rw [P.Ω.prob_sum] at this; linarith
  have hpos : 0 < ∑ s, adPrice P.Ω P.β P.ρ P.Y1 P.Y2 s := by
    refine Finset.sum_pos' (fun s _ => ?_) ⟨s0, Finset.mem_univ _, ?_⟩
    · unfold adPrice
      have := P.Ω.prob_nonneg s; have := P.beta_pos
      have := Real.rpow_nonneg (div_pos (P.worldOut2_pos s) P.worldOut1_pos).le (-P.ρ)
      positivity
    · unfold adPrice
      have := P.beta_pos
      have := Real.rpow_pos_of_pos (div_pos (P.worldOut2_pos s0) P.worldOut1_pos) (-P.ρ)
      positivity
  unfold R grossRate
  rw [← Finset.mul_sum, ← hK, ← Finset.sum_mul]
  field_simp

/-- **The bonds-and-shares allocation satisfies the complete-markets Euler equations**,
O&R §5.3.3, p. 303: `adPrice(s) · C₁ⁿ^{-ρ} = π(s) β C₂ⁿ(s)^{-ρ}` for every country and
state, i.e. (5) at prices (30). -/
theorem ad_euler (n : ι) (s : S) :
    adPrice P.Ω P.β P.ρ P.Y1 P.Y2 s * P.C1 n ^ (-P.ρ) =
      P.Ω.prob s * P.β * P.C2 n s ^ (-P.ρ) := by
  have hμ := P.μ_pos n
  unfold adPrice C1 C2
  rw [Real.mul_rpow hμ.le (P.worldOut2_pos _).le, Real.mul_rpow hμ.le P.worldOut1_pos.le,
    Real.div_rpow (P.worldOut2_pos s).le P.worldOut1_pos.le]
  have : 0 < worldOut1 P.Y1 ^ (-P.ρ) := Real.rpow_pos_of_pos P.worldOut1_pos _
  field_simp

/-- **The allocation satisfies the complete-markets budget constraints**, O&R §5.3.3, p. 303:
`C₁ⁿ + Σ_s adPrice(s) C₂ⁿ(s) = Y₁ⁿ + Σ_s adPrice(s) Y₂ⁿ(s)`. Together with `ad_euler`,
`ad_prices_normalised` and `market_clearing`, the equilibrium of §5.3.2 is a complete-markets
equilibrium, for any number of states `S` (in particular `S ≫ N + 1`). -/
theorem ad_budget (n : ι) :
    P.C1 n + ∑ s, adPrice P.Ω P.β P.ρ P.Y1 P.Y2 s * P.C2 n s =
      P.Y1 n + ∑ s, adPrice P.Ω P.β P.ρ P.Y1 P.Y2 s * P.Y2 n s := by
  have h := P.budget_date1 n
  rw [← V_eq_ad_value]
  unfold C1 C2 x at *
  rw [add_zero, ← Finset.mul_sum] at h
  rw [h]
  have e : ∑ s, adPrice P.Ω P.β P.ρ P.Y1 P.Y2 s * (P.μ n * worldOut2 P.Y2 s) =
      P.μ n * ∑ m, P.V m := by
    unfold worldOut2
    simp only [V_eq_ad_value, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun s _ => by ring
  rw [e, ← h]

/-! ## Exercise 4: the log-utility solution -/

/-- Share prices under log utility, O&R Exercise 4, p. 346:
`V₁ᵐ = β Σ_s π(s) (Y₁ᵂ/Y₂ᵂ(s)) Y₂ᵐ(s)`. -/
noncomputable def logV (m : ι) : ℝ :=
  P.β * ∑ s, P.Ω.prob s * (worldOut1 P.Y1 / worldOut2 P.Y2 s) * P.Y2 m s

/-- The guess (89), O&R p. 346: `C₁ⁿ = (Y₁ⁿ + V₁ⁿ)/(1 + β)`. -/
noncomputable def logC1 (n : ι) : ℝ := (P.Y1 n + P.logV n) / (1 + P.β)

/-- The guess (90), O&R p. 346:
`C₂ⁿ(s) = β/(1 + β) · (Y₁ⁿ + V₁ⁿ) · Σₘ Y₂ᵐ(s)/Σₘ V₁ᵐ`. -/
noncomputable def logC2 (n : ι) (s : S) : ℝ :=
  P.β / (1 + P.β) * (P.Y1 n + P.logV n) * (worldOut2 P.Y2 s / ∑ m, P.logV m)

/-- The portfolio behind (90): savings `β(Y₁ⁿ + V₁ⁿ)/(1 + β)` spread over the global fund, an
equal share `β(Y₁ⁿ + V₁ⁿ)/((1 + β) Σₘ V₁ᵐ)` of every country's output; bonds are zero. -/
noncomputable def logX (n _m : ι) : ℝ :=
  P.β * (P.Y1 n + P.logV n) / ((1 + P.β) * ∑ m, P.logV m)

/-- The gross interest rate under log utility: `1 + r = 1/(β Σ_s π(s) Y₁ᵂ/Y₂ᵂ(s))`
((49) with `ρ = 1`). -/
noncomputable def logR : ℝ := 1 / (P.β * ∑ s, P.Ω.prob s * (worldOut1 P.Y1 / worldOut2 P.Y2 s))

/-- Under log utility the value of all claims is `Σₘ V₁ᵐ = βY₁ᵂ` (Exercise 4). -/
theorem logV_sum : ∑ m, P.logV m = P.β * worldOut1 P.Y1 := by
  unfold logV
  rw [← Finset.mul_sum, Finset.sum_comm]
  congr 1
  have e : ∀ s, ∑ m, P.Ω.prob s * (worldOut1 P.Y1 / worldOut2 P.Y2 s) * P.Y2 m s =
      P.Ω.prob s * worldOut1 P.Y1 := fun s => by
    rw [← Finset.mul_sum]
    have := (P.worldOut2_pos s).ne'
    unfold worldOut2 at this ⊢
    field_simp
  simp only [e]
  rw [← Finset.sum_mul, P.Ω.prob_sum, one_mul]

/-- The log-utility share prices are (50) with `ρ = 1`. -/
theorem logV_eq_sharePrice (m : ι) : P.logV m = sharePrice P.Ω P.β 1 P.Y1 P.Y2 m := by
  unfold logV sharePrice
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Real.rpow_neg_one, inv_div]
  ring

/-- **Exercise 4: budget constraints** (42)–(43) hold for the guesses (89)–(90) with zero
bond holdings. -/
theorem log_budgets (n : ι) :
    P.Y1 n + P.logV n = P.logC1 n + 0 + ∑ m, P.logX n m * P.logV m ∧
      ∀ s, P.logC2 n s = P.logR * 0 + ∑ m, P.logX n m * P.Y2 m s := by
  have hW : 0 < ∑ m, P.logV m := by
    rw [P.logV_sum]; exact mul_pos P.beta_pos P.worldOut1_pos
  have hb := P.beta_pos
  refine ⟨?_, fun s => ?_⟩
  · unfold logC1 logX
    rw [← Finset.mul_sum, add_zero]
    field_simp
  · unfold logC2 logX worldOut2
    rw [mul_zero, zero_add, ← Finset.mul_sum]
    field_simp

/-- Consumption growth under the log guesses equals world output growth:
`C₂ⁿ(s)/C₁ⁿ = Y₂ᵂ(s)/Y₁ᵂ`. -/
theorem log_growth (n : ι) (s : S) :
    P.logC2 n s = P.logC1 n * (worldOut2 P.Y2 s / worldOut1 P.Y1) := by
  unfold logC2 logC1
  rw [P.logV_sum]
  have := P.beta_pos; have := P.worldOut1_pos.ne'
  field_simp

/-- **Exercise 4: first-order conditions.** Under log utility the share Euler equations (44)
`V₁ᵐ/C₁ⁿ = β Σ_s π(s) Y₂ᵐ(s)/C₂ⁿ(s)` and the bond Euler equation (8)
`1/C₁ⁿ = (1 + r) β Σ_s π(s)/C₂ⁿ(s)` hold at the prices `logV`, `logR`. -/
theorem log_eulers (n : ι) :
    (∀ m, P.logV m / P.logC1 n = P.β * ∑ s, P.Ω.prob s * P.Y2 m s / P.logC2 n s) ∧
      1 / P.logC1 n = P.logR * P.β * ∑ s, P.Ω.prob s / P.logC2 n s := by
  have hC1 : 0 < P.logC1 n := by
    unfold logC1
    have hV : 0 ≤ P.logV n := by
      unfold logV
      refine mul_nonneg P.beta_pos.le (Finset.sum_nonneg fun s _ => ?_)
      have := P.Ω.prob_nonneg s; have := P.Y2_pos n s
      have := div_pos P.worldOut1_pos (P.worldOut2_pos s)
      positivity
    have := P.Y1_pos n; have := P.beta_pos
    positivity
  have hY := P.worldOut1_pos
  simp only [P.log_growth]
  have e : ∀ s, 1 / (P.logC1 n * (worldOut2 P.Y2 s / worldOut1 P.Y1)) =
      (worldOut1 P.Y1 / worldOut2 P.Y2 s) / P.logC1 n := fun s => by
    have := (P.worldOut2_pos s).ne'
    field_simp
  refine ⟨fun m => ?_, ?_⟩
  · have e2 : ∀ s, P.Ω.prob s * P.Y2 m s / (P.logC1 n * (worldOut2 P.Y2 s / worldOut1 P.Y1)) =
        P.Ω.prob s * (worldOut1 P.Y1 / worldOut2 P.Y2 s) * P.Y2 m s / P.logC1 n := fun s => by
      have := (P.worldOut2_pos s).ne'
      field_simp
    simp only [e2, ← Finset.sum_div]
    unfold logV
    rw [mul_div_assoc]
  · have e2 : ∀ s, P.Ω.prob s / (P.logC1 n * (worldOut2 P.Y2 s / worldOut1 P.Y1)) =
        P.Ω.prob s * (worldOut1 P.Y1 / worldOut2 P.Y2 s) / P.logC1 n := fun s => by
      have := (P.worldOut2_pos s).ne'
      field_simp
    simp only [e2, ← Finset.sum_div]
    unfold logR
    set K := ∑ s, P.Ω.prob s * (worldOut1 P.Y1 / worldOut2 P.Y2 s) with hKdef
    have hK : 0 < ∑ s, P.Ω.prob s * (worldOut1 P.Y1 / worldOut2 P.Y2 s) := by
      have h := P.logV_sum
      have hpos : 0 < P.β * worldOut1 P.Y1 := mul_pos P.beta_pos hY
      rw [← h] at hpos
      unfold logV at hpos
      by_contra hc
      push Not at hc
      have hle : ∀ m, P.β * ∑ s, P.Ω.prob s * (worldOut1 P.Y1 / worldOut2 P.Y2 s) * P.Y2 m s
          ≤ 0 := fun m => by
        refine mul_nonpos_of_nonneg_of_nonpos P.beta_pos.le ?_
        have : ∀ s, 0 ≤ P.Ω.prob s * (worldOut1 P.Y1 / worldOut2 P.Y2 s) := fun s =>
          mul_nonneg (P.Ω.prob_nonneg s) (div_pos hY (P.worldOut2_pos s)).le
        have hz : ∀ s, P.Ω.prob s * (worldOut1 P.Y1 / worldOut2 P.Y2 s) = 0 := fun s =>
          le_antisymm ((Finset.single_le_sum (fun s _ => this s) (Finset.mem_univ s)).trans hc)
            (this s)
        simp [hz]
      linarith [Finset.sum_nonpos fun m (_ : m ∈ Finset.univ) => hle m]
    have := P.beta_pos
    field_simp
    rw [hKdef]; exact (div_self hK.ne').symm

/-- **Exercise 4: market clearing.** Every claim is fully held, and consumption exhausts
world output on both dates. -/
theorem log_clearing :
    (∀ m, ∑ n, P.logX n m = 1) ∧ ∑ n, P.logC1 n = worldOut1 P.Y1 ∧
      ∀ s, ∑ n, P.logC2 n s = worldOut2 P.Y2 s := by
  have hW := P.logV_sum
  have hb := P.beta_pos; have hY := P.worldOut1_pos
  have hsum : ∑ n, (P.Y1 n + P.logV n) = (1 + P.β) * worldOut1 P.Y1 := by
    rw [Finset.sum_add_distrib, hW]; unfold worldOut1; ring
  refine ⟨fun m => ?_, ?_, fun s => ?_⟩
  · unfold logX
    rw [← Finset.sum_div, ← Finset.mul_sum, hsum, hW]
    field_simp
  · unfold logC1
    rw [← Finset.sum_div, hsum]
    field_simp
  · unfold logC2
    rw [← Finset.sum_mul, ← Finset.mul_sum, hsum, hW]
    field_simp

/-- **Exercise 4 agrees with §5.3.2**: the log guess (89) is `C₁ⁿ = μⁿY₁ᵂ` with the wealth
share (45) computed at the `ρ = 1` share prices. -/
theorem logC1_eq_share (n : ι) :
    P.logC1 n = wealthShare P.Ω P.β 1 P.Y1 P.Y2 n * worldOut1 P.Y1 := by
  unfold wealthShare logC1
  simp only [← P.logV_eq_sharePrice]
  rw [Finset.sum_add_distrib, P.logV_sum, show ∑ m, P.Y1 m = worldOut1 P.Y1 from rfl]
  have := P.beta_pos; have := P.worldOut1_pos
  field_simp

end PortfolioEconomy

/-! ## Exercise 5: exponential (CARA) utility -/

namespace Exercise5

/-- The CARA pricing kernel sum `Σ_s π(s) exp(−κΔ(s))`, O&R Exercise 5, p. 346–347. -/
noncomputable def caraKernel (Ω : StateSpace S) (κ : ℝ) (Δ : S → ℝ) : ℝ :=
  ∑ s, Ω.prob s * Real.exp (-(κ * Δ s))

/-- The price of a claim to `Z(s)` under CARA risk sharing: `β Σ_s π(s) exp(−κΔ(s)) Z(s)`. -/
noncomputable def caraValue (Ω : StateSpace S) (β κ : ℝ) (Δ Z : S → ℝ) : ℝ :=
  β * ∑ s, Ω.prob s * Real.exp (-(κ * Δ s)) * Z s

/-- The gross riskless rate `1 + r = 1/(β Σ_s π(s) exp(−κΔ(s)))`. -/
noncomputable def caraRate (Ω : StateSpace S) (β κ : ℝ) (Δ : S → ℝ) : ℝ :=
  1 / (β * caraKernel Ω κ Δ)

/-- The CARA kernel sum is positive. -/
theorem caraKernel_pos (Ω : StateSpace S) (κ : ℝ) (Δ : S → ℝ) : 0 < caraKernel Ω κ Δ := by
  obtain ⟨s0, hs0⟩ : ∃ s, 0 < Ω.prob s := by
    by_contra h
    push Not at h
    have : ∑ s, Ω.prob s ≤ 0 := Finset.sum_nonpos fun s _ => h s
    rw [Ω.prob_sum] at this; linarith
  exact Finset.sum_pos' (fun s _ => mul_nonneg (Ω.prob_nonneg s) (Real.exp_pos _).le)
    ⟨s0, Finset.mem_univ _, mul_pos hs0 (Real.exp_pos _)⟩

/-- CARA Euler equation in ratio form (`u′(C) = e^{-γC}`), Exercise 5:
`q e^{-γa} = K e^{-γb}` iff `q = K e^{-γ(b − a)}`. -/
theorem cara_euler_iff {q K γ a b : ℝ} :
    q * Real.exp (-(γ * a)) = K * Real.exp (-(γ * b)) ↔ q = K * Real.exp (-(γ * (b - a))) := by
  have e : Real.exp (-(γ * b)) = Real.exp (-(γ * (b - a))) * Real.exp (-(γ * a)) := by
    rw [← Real.exp_add]; ring_nf
  rw [e, ← mul_assoc]
  exact mul_left_inj' (Real.exp_pos _).ne'

/-- **Share Euler equations under a linear sharing rule**: if `γ(c₂(s) − c₁) = κΔ(s)` then
for any payoff `Z`, `caraValue(Z) · e^{-γc₁} = β Σ_s π(s) e^{-γc₂(s)} Z(s)` (O&R (44) with
CARA utility). -/
theorem cara_share_euler (Ω : StateSpace S) {β γ κ c1 : ℝ} {c2 Δ : S → ℝ}
    (hrule : ∀ s, γ * (c2 s - c1) = κ * Δ s) (Z : S → ℝ) :
    caraValue Ω β κ Δ Z * Real.exp (-(γ * c1)) =
      β * ∑ s, Ω.prob s * Real.exp (-(γ * c2 s)) * Z s := by
  have e : ∀ s, Real.exp (-(γ * c2 s)) = Real.exp (-(κ * Δ s)) * Real.exp (-(γ * c1)) :=
    fun s => by rw [← Real.exp_add, ← hrule s]; ring_nf
  unfold caraValue
  simp only [e]
  rw [mul_assoc, Finset.sum_mul]
  congr 1
  exact Finset.sum_congr rfl fun s _ => by ring

/-- **Bond Euler equation under a linear sharing rule**: if `γ(c₂(s) − c₁) = κΔ(s)` and
`β > 0`, then `e^{-γc₁} = (1 + r) β Σ_s π(s) e^{-γc₂(s)}` at `1 + r = caraRate` (O&R (8)). -/
theorem cara_bond_euler (Ω : StateSpace S) {β γ κ c1 : ℝ} {c2 Δ : S → ℝ} (hβ : 0 < β)
    (hrule : ∀ s, γ * (c2 s - c1) = κ * Δ s) :
    Real.exp (-(γ * c1)) = caraRate Ω β κ Δ * β * ∑ s, Ω.prob s * Real.exp (-(γ * c2 s)) := by
  have h := cara_share_euler Ω (β := β) hrule (fun _ => 1)
  simp only [mul_one] at h
  have hK := caraKernel_pos Ω κ Δ
  rw [mul_assoc, ← h]
  unfold caraRate caraValue caraKernel at *
  simp only [mul_one]
  field_simp

/-- **Exercise 5(a): complete markets with CARA utility**, O&R p. 347. With a common
`γ > 0`, Euler equations `q(s) e^{-γC₁} = π(s) β e^{-γC₂(s)}` for Home and Foreign
(`π(s) > 0`, `β > 0`) and market clearing, (i) consumption differences are constant across
dates and states, `C₂(s) − C₂*(s) = C₁ − C₁*`; (ii) `C₁ = Y₁ᵂ/2 − μ`, `C₂(s) = Y₂ᵂ(s)/2 − μ`
and `C₁* = Y₁ᵂ/2 + μ`, `C₂*(s) = Y₂ᵂ(s)/2 + μ` with `μ = (C₁* − C₁)/2`; (iii) prices are
`q(s) = π(s) β exp(−γ(Y₂ᵂ(s) − Y₁ᵂ)/2)`. -/
theorem exercise5a (Ω : StateSpace S) {q C2 C2f Y2W : S → ℝ} {β γ C1 C1f Y1W : ℝ}
    (hπ : ∀ s, 0 < Ω.prob s) (hβ : 0 < β) (hγ : 0 < γ)
    (he : ∀ s, q s * Real.exp (-(γ * C1)) = Ω.prob s * β * Real.exp (-(γ * C2 s)))
    (hef : ∀ s, q s * Real.exp (-(γ * C1f)) = Ω.prob s * β * Real.exp (-(γ * C2f s)))
    (hc1 : C1 + C1f = Y1W) (hc2 : ∀ s, C2 s + C2f s = Y2W s) :
    (∀ s, C2 s - C2f s = C1 - C1f) ∧
      (C1 = Y1W / 2 - (C1f - C1) / 2 ∧ C1f = Y1W / 2 + (C1f - C1) / 2) ∧
      (∀ s, C2 s = Y2W s / 2 - (C1f - C1) / 2 ∧ C2f s = Y2W s / 2 + (C1f - C1) / 2) ∧
      ∀ s, q s = Ω.prob s * β * Real.exp (-(γ * ((Y2W s - Y1W) / 2))) := by
  have hd : ∀ s, C2 s - C1 = C2f s - C1f := by
    intro s
    have h1 := cara_euler_iff.1 (he s)
    have h2 := cara_euler_iff.1 (hef s)
    have hpb : 0 < Ω.prob s * β := mul_pos (hπ s) hβ
    have h3 := mul_left_cancel₀ hpb.ne' (h1.symm.trans h2)
    have h4 := Real.exp_injective h3
    have : γ * (C2 s - C1) = γ * (C2f s - C1f) := by linarith
    exact mul_left_cancel₀ hγ.ne' this
  refine ⟨fun s => by linarith [hd s], ⟨by linarith, by linarith⟩,
    fun s => ⟨by linarith [hd s, hc2 s], by linarith [hd s, hc2 s]⟩, fun s => ?_⟩
  rw [cara_euler_iff.1 (he s), show C2 s - C1 = (Y2W s - Y1W) / 2 by linarith [hd s, hc2 s]]

/-- **Exercise 5(a): the consumption gap** from Home's Arrow–Debreu budget constraint
`C₁ + Σ q C₂ = Y₁ + Σ q Y₂`: with `C₁ = Y₁ᵂ/2 − μ`, `C₂(s) = Y₂ᵂ(s)/2 − μ`,
`μ(1 + Σ_s q(s)) = Y₁ᵂ/2 + Σ_s q(s)Y₂ᵂ(s)/2 − Y₁ − Σ_s q(s)Y₂(s)`. -/
theorem exercise5a_gap {q Y2 Y2W : S → ℝ} {μ Y1 Y1W : ℝ}
    (hb : (Y1W / 2 - μ) + ∑ s, q s * (Y2W s / 2 - μ) = Y1 + ∑ s, q s * Y2 s) :
    μ * (1 + ∑ s, q s) = Y1W / 2 + ∑ s, q s * Y2W s / 2 - Y1 - ∑ s, q s * Y2 s := by
  have e : ∑ s, q s * (Y2W s / 2 - μ) = ∑ s, q s * Y2W s / 2 - μ * ∑ s, q s := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [e] at hb
  linarith

/-- **Exercise 5(b): bonds and shares support the efficient CARA allocation**, O&R p. 347.
Let `Δ(s) = Y₂ᵂ(s) − Y₁ᵂ`, share prices `V = caraValue(Y₂)`, `V* = caraValue(Y₂*)` and
`1 + r = caraRate`, all with `κ = γ/2`. Both countries hold half of each country's claim
(half the world fund); Home holds bonds `B = −μ/(1 + r)` (so for `μ > 0` Foreign lends to
Home). Then with `C = Yᵂ/2 − μ`, `C* = Yᵂ/2 + μ` on both dates:
the date-2 budgets (43) hold for both countries; Home's date-1 budget (42) implies Foreign's;
and all bond and share Euler equations (8), (44) hold in both countries. -/
theorem exercise5b (Ω : StateSpace S) {Y2 Y2f : S → ℝ} {β γ μ Y1 Y1f : ℝ} (hβ : 0 < β) :
    let Δ := fun s => (Y2 s + Y2f s) - (Y1 + Y1f)
    let R := caraRate Ω β (γ / 2) Δ
    let V := caraValue Ω β (γ / 2) Δ Y2
    let Vf := caraValue Ω β (γ / 2) Δ Y2f
    let B := -μ / R
    (∀ s, (Y2 s + Y2f s) / 2 - μ = R * B + 1 / 2 * Y2 s + 1 / 2 * Y2f s) ∧
      (∀ s, (Y2 s + Y2f s) / 2 + μ = R * (-B) + 1 / 2 * Y2 s + 1 / 2 * Y2f s) ∧
      (Y1 + V = ((Y1 + Y1f) / 2 - μ) + B + 1 / 2 * V + 1 / 2 * Vf →
        Y1f + Vf = ((Y1 + Y1f) / 2 + μ) + (-B) + 1 / 2 * V + 1 / 2 * Vf) ∧
      (∀ δ : ℝ,
        Real.exp (-(γ * ((Y1 + Y1f) / 2 + δ))) =
          R * β * ∑ s, Ω.prob s * Real.exp (-(γ * ((Y2 s + Y2f s) / 2 + δ))) ∧
        V * Real.exp (-(γ * ((Y1 + Y1f) / 2 + δ))) =
          β * ∑ s, Ω.prob s * Real.exp (-(γ * ((Y2 s + Y2f s) / 2 + δ))) * Y2 s ∧
        Vf * Real.exp (-(γ * ((Y1 + Y1f) / 2 + δ))) =
          β * ∑ s, Ω.prob s * Real.exp (-(γ * ((Y2 s + Y2f s) / 2 + δ))) * Y2f s) := by
  intro Δ R V Vf B
  have hR : R ≠ 0 := by
    have := caraKernel_pos Ω (γ / 2) Δ
    change 1 / (β * caraKernel Ω (γ / 2) Δ) ≠ 0
    positivity
  have hRB : R * B = -μ := by change R * (-μ / R) = -μ; field_simp
  refine ⟨fun s => by rw [hRB]; ring, fun s => by rw [mul_neg, hRB]; ring,
    fun h => by linarith, fun δ => ?_⟩
  have hrule : ∀ s, γ * (((Y2 s + Y2f s) / 2 + δ) - ((Y1 + Y1f) / 2 + δ)) = γ / 2 * Δ s :=
    fun s => by simp only [Δ]; ring
  exact ⟨cara_bond_euler Ω hβ hrule, cara_share_euler Ω hrule Y2, cara_share_euler Ω hrule Y2f⟩

/-- **Exercise 5(b): the bonds-and-shares allocation is efficient**, O&R p. 347: it
satisfies the complete-markets Euler equations of 5(a) at `q(s) = π(s)β exp(−(γ/2)Δ(s))`,
share prices are Arrow–Debreu values `V = Σ q(s)Y₂(s)`, and `1 + r = 1/Σ_s q(s)`. -/
theorem exercise5b_efficient (Ω : StateSpace S) {Y2 Y2f : S → ℝ} {β γ δ Y1 Y1f : ℝ} :
    let Δ := fun s => (Y2 s + Y2f s) - (Y1 + Y1f)
    let q := fun s => Ω.prob s * β * Real.exp (-(γ / 2 * Δ s))
    (∀ s, q s * Real.exp (-(γ * ((Y1 + Y1f) / 2 + δ))) =
        Ω.prob s * β * Real.exp (-(γ * ((Y2 s + Y2f s) / 2 + δ)))) ∧
      caraValue Ω β (γ / 2) Δ Y2 = ∑ s, q s * Y2 s ∧
      caraRate Ω β (γ / 2) Δ = 1 / ∑ s, q s := by
  intro Δ q
  refine ⟨fun s => ?_, ?_, ?_⟩
  · refine cara_euler_iff.2 ?_
    change Ω.prob s * β * Real.exp (-(γ / 2 * Δ s)) = _
    congr 3
    simp only [Δ]; ring
  · unfold caraValue
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => by simp only [q]; ring
  · unfold caraRate caraKernel
    congr 1
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => by simp only [q]; ring

/-- **Exercise 5(c): linear sharing with different CARA coefficients**, O&R p. 347. With
Home `γ > 0`, Foreign `γ* > 0`, common Arrow–Debreu prices, `π(s) > 0`, `β > 0` and market
clearing, consumption changes are shared linearly: Home absorbs the fraction
`θ = γ*/(γ + γ*)` of every change in world output, `C₂(s) − C₁ = θ(Y₂ᵂ(s) − Y₁ᵂ)`, and Foreign
the fraction `1 − θ`. -/
theorem exercise5c_sharing (Ω : StateSpace S) {q C2 C2f Y2W : S → ℝ}
    {β γ γf C1 C1f Y1W : ℝ} (hπ : ∀ s, 0 < Ω.prob s) (hβ : 0 < β) (hγ : 0 < γ) (hγf : 0 < γf)
    (he : ∀ s, q s * Real.exp (-(γ * C1)) = Ω.prob s * β * Real.exp (-(γ * C2 s)))
    (hef : ∀ s, q s * Real.exp (-(γf * C1f)) = Ω.prob s * β * Real.exp (-(γf * C2f s)))
    (hc1 : C1 + C1f = Y1W) (hc2 : ∀ s, C2 s + C2f s = Y2W s) (s : S) :
    C2 s - C1 = γf / (γ + γf) * (Y2W s - Y1W) ∧
      C2f s - C1f = γ / (γ + γf) * (Y2W s - Y1W) := by
  have h1 := cara_euler_iff.1 (he s)
  have h2 := cara_euler_iff.1 (hef s)
  have hpb : 0 < Ω.prob s * β := mul_pos (hπ s) hβ
  have h4 := Real.exp_injective (mul_left_cancel₀ hpb.ne' (h1.symm.trans h2))
  have hs : 0 < γ + γf := by linarith
  have hsum : (C2 s - C1) + (C2f s - C1f) = Y2W s - Y1W := by linarith [hc2 s]
  constructor
  · rw [div_mul_eq_mul_div, eq_div_iff hs.ne']
    linear_combination (-1) * h4 + γf * hsum
  · rw [div_mul_eq_mul_div, eq_div_iff hs.ne']
    linear_combination h4 + γ * hsum

/-- **Exercise 5(c): bonds and shares support the linear sharing rule**, O&R p. 347 and
footnote 27. With `θ = γ*/(γ + γ*)` and `κ = γγ*/(γ + γ*)`, share prices `caraValue`, rate
`caraRate` (both at `κ`, `Δ = Y₂ᵂ − Y₁ᵂ`): Home holds the fraction `θ` of the world fund and
bonds `B = (C₁ − θY₁ᵂ)/(1 + r)`, Foreign holds `1 − θ` and `−B`. Then the date-2 budgets
(43) deliver `C₂ = C₁ + θΔ`, `C₂* = C₁* + (1 − θ)Δ`, Home's date-1 budget (42) implies
Foreign's, and every bond and share Euler equation holds in both countries at common prices.
The less risk-averse country (smaller `γ`) holds more than half of the risky fund. -/
theorem exercise5c_support (Ω : StateSpace S) {Y2 Y2f : S → ℝ} {β γ γf C1 C1f Y1 Y1f : ℝ}
    (hβ : 0 < β) (hγ : 0 < γ) (hγf : 0 < γf) (hc1 : C1 + C1f = Y1 + Y1f) :
    let θ := γf / (γ + γf)
    let κ := γ * γf / (γ + γf)
    let Δ := fun s => (Y2 s + Y2f s) - (Y1 + Y1f)
    let R := caraRate Ω β κ Δ
    let V := caraValue Ω β κ Δ Y2
    let Vf := caraValue Ω β κ Δ Y2f
    let B := (C1 - θ * (Y1 + Y1f)) / R
    (∀ s, C1 + θ * Δ s = R * B + θ * Y2 s + θ * Y2f s) ∧
      (∀ s, C1f + (1 - θ) * Δ s = R * (-B) + (1 - θ) * Y2 s + (1 - θ) * Y2f s) ∧
      (Y1 + V = C1 + B + θ * V + θ * Vf →
        Y1f + Vf = C1f + (-B) + (1 - θ) * V + (1 - θ) * Vf) ∧
      (Real.exp (-(γ * C1)) = R * β * ∑ s, Ω.prob s * Real.exp (-(γ * (C1 + θ * Δ s))) ∧
        ∀ Z : S → ℝ, caraValue Ω β κ Δ Z * Real.exp (-(γ * C1)) =
          β * ∑ s, Ω.prob s * Real.exp (-(γ * (C1 + θ * Δ s))) * Z s) ∧
      (Real.exp (-(γf * C1f)) =
          R * β * ∑ s, Ω.prob s * Real.exp (-(γf * (C1f + (1 - θ) * Δ s))) ∧
        ∀ Z : S → ℝ, caraValue Ω β κ Δ Z * Real.exp (-(γf * C1f)) =
          β * ∑ s, Ω.prob s * Real.exp (-(γf * (C1f + (1 - θ) * Δ s))) * Z s) := by
  intro θ κ Δ R V Vf B
  have hs : 0 < γ + γf := by linarith
  have hR : R ≠ 0 := by
    have := caraKernel_pos Ω κ Δ
    change 1 / (β * caraKernel Ω κ Δ) ≠ 0
    positivity
  have hRB : R * B = C1 - θ * (Y1 + Y1f) := by
    change R * ((C1 - θ * (Y1 + Y1f)) / R) = _; field_simp
  have hrule : ∀ s, γ * ((C1 + θ * Δ s) - C1) = κ * Δ s := fun s => by
    simp only [θ, κ]; field_simp; ring
  have hrulef : ∀ s, γf * ((C1f + (1 - θ) * Δ s) - C1f) = κ * Δ s := fun s => by
    simp only [θ, κ]; field_simp; ring
  refine ⟨fun s => ?_, fun s => ?_, fun h => ?_,
    ⟨cara_bond_euler Ω hβ hrule, cara_share_euler Ω hrule⟩,
    ⟨cara_bond_euler Ω hβ hrulef, cara_share_euler Ω hrulef⟩⟩
  · rw [hRB]; simp only [Δ]; ring
  · rw [mul_neg, hRB]; simp only [Δ]; linear_combination hc1
  · linear_combination (-1) * h + (-1) * hc1

end Exercise5

end ObstfeldRogoff.InternationalFinancialMarkets.PortfolioDiversification

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Spanning and completeness

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, Appendix 5A,
pp. 335–337, the spanning discussion on p. 304, and equation (7), p. 273.

`R` is the `S × (N + 1)` matrix of gross ex post returns (one column per asset: the riskless
bond and the `N` country funds). A portfolio `a` (amounts invested in each asset) pays
`R a` across states.

* The spanning condition (77), `rank R = S`, holds iff every state-contingent payoff is
  attainable; for square invertible `R` the Arrow–Debreu securities are `R⁻¹ 1ₛ`.
* `rank R ≤ min(S, N + 1)`, so spanning requires `S ≤ N + 1`; with more states than assets
  it fails.
* With linear (Arrow–Debreu) pricing of assets, attainable consumption plans are budget
  feasible; under spanning the attainable set *equals* the complete-markets budget set, and
  the Arrow–Debreu prices are uniquely determined by asset prices.
* The book's "Pareto efficiency can be ensured only when `S ≤ N + 1`" (p. 304) is imprecise:
  `S ≤ N + 1` is necessary for spanning but not sufficient (explicit counterexample), and it
  is not necessary for efficiency — the CRRA equilibrium of §5.3.2 is efficient for any `S`.
* Bond redundancy (7): the bond is replicated by `1 + r` units of every Arrow–Debreu security,
  so no arbitrage forces `Σ p(s) = 1`.
-/

namespace ObstfeldRogoff.InternationalFinancialMarkets.Spanning

open Matrix Finset

variable {S A : Type} [Fintype S] [Fintype A]

/-- **The spanning condition**, O&R (77), p. 336: `rank R = S` iff every payoff vector
`c : S → ℝ` is attained by some portfolio, `R a = c`. -/
theorem spans_iff_rank (R : Matrix S A ℝ) :
    Function.Surjective R.mulVec ↔ R.rank = Fintype.card S := by
  have hsurj : Function.Surjective R.mulVec ↔ LinearMap.range R.mulVecLin = ⊤ := by
    rw [LinearMap.range_eq_top]; rfl
  rw [hsurj, Matrix.rank]
  constructor
  · intro h
    rw [h, finrank_top, Module.finrank_fintype_fun_eq_card]
  · intro h
    exact Submodule.eq_top_of_finrank_eq (h.trans (Module.finrank_fintype_fun_eq_card ℝ).symm)

/-- **The rank bound**, O&R p. 336: `rank R ≤ min(S, N + 1)`. -/
theorem rank_le_min (R : Matrix S A ℝ) :
    R.rank ≤ min (Fintype.card S) (Fintype.card A) :=
  le_min (Matrix.rank_le_card_height R) (Matrix.rank_le_card_width R)

/-- **Spanning needs at least as many assets as states**, O&R p. 336: if every payoff is
attainable then `S ≤ N + 1`. -/
theorem card_le_of_spans {R : Matrix S A ℝ} (h : Function.Surjective R.mulVec) :
    Fintype.card S ≤ Fintype.card A := by
  rw [← (spans_iff_rank R).1 h]
  exact Matrix.rank_le_card_width R

/-- **With more states than assets spanning fails**, O&R p. 336 ("(77) couldn't possibly hold
were `N + 1 < S`"): some state-contingent payoff is not attainable. -/
theorem not_spans_of_card_lt {R : Matrix S A ℝ} (h : Fintype.card A < Fintype.card S) :
    ¬ Function.Surjective R.mulVec := fun hs => absurd (card_le_of_spans hs) (not_le.2 h)

/-- **Synthesising Arrow–Debreu securities**, O&R p. 336: if the square return matrix is
invertible, the portfolio `aₛ = R⁻¹1ₛ` pays one unit in state `s` and nothing otherwise. -/
theorem ad_security_replication [DecidableEq S] {R : Matrix S S ℝ} (h : IsUnit R.det)
    (s : S) : R *ᵥ (R⁻¹ *ᵥ Pi.single s 1) = Pi.single s 1 := by
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv R h, Matrix.one_mulVec]

/-- For a square return matrix, spanning is equivalent to invertibility, O&R p. 336. -/
theorem spans_iff_isUnit_det [DecidableEq S] (R : Matrix S S ℝ) :
    Function.Surjective R.mulVec ↔ IsUnit R.det := by
  rw [Matrix.mulVec_surjective_iff_isUnit, Matrix.isUnit_iff_isUnit_det]

/-- **`S ≤ N + 1` is not sufficient for spanning**, correcting O&R p. 304: with two states
and two assets — the bond with gross return `1 + r = 2` and a fund whose gross return is also
`2` in both states (a riskless country output) — the return matrix has rank one and the
Arrow–Debreu security for state 0 cannot be synthesised. -/
theorem card_le_not_sufficient :
    ∃ R : Matrix (Fin 2) (Fin 2) ℝ, Fintype.card (Fin 2) ≤ Fintype.card (Fin 2) ∧
      ¬ Function.Surjective R.mulVec := by
  refine ⟨Matrix.of fun _ _ => 2, le_refl _, fun h => ?_⟩
  obtain ⟨a, ha⟩ := h (Pi.single 0 1)
  have h0 := congrFun ha 0
  have h1 := congrFun ha 1
  simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at h0 h1
  linarith

/-- The cost of every asset per unit invested is one; asset prices are linear in
Arrow–Debreu prices `q` when `Σ_s q(s) R(s, j) = 1` for every asset `j` (O&R §5.4.1.1 and
p. 336). -/
def LinearPricing (q : S → ℝ) (R : Matrix S A ℝ) : Prop := ∀ j, ∑ s, q s * R s j = 1

/-- **Attainable plans are budget feasible**: under linear pricing, a portfolio costing
`Σ_j a(j)` finances a payoff with Arrow–Debreu value `Σ_s q(s)(Ra)(s) = Σ_j a(j)`. -/
theorem value_of_payoff {q : S → ℝ} {R : Matrix S A ℝ} (hq : LinearPricing q R) (a : A → ℝ) :
    ∑ s, q s * (R *ᵥ a) s = ∑ j, a j := by
  have h := Matrix.dotProduct_mulVec q R a
  simp only [dotProduct] at h
  rw [h]
  refine Finset.sum_congr rfl fun j _ => ?_
  have : (q ᵥ* R) j = 1 := hq j
  rw [this, one_mul]

/-- **Spanning makes asset markets complete**, O&R Appendix 5A, p. 336: under spanning and
linear pricing, the set of payoffs attainable with wealth `w`,
`{c | ∃ a, Ra = c, Σ_j a(j) = w}`, equals the complete-markets budget set
`{c | Σ_s q(s)c(s) = w}`. -/
theorem attainable_eq_budget {q : S → ℝ} {R : Matrix S A ℝ} (hq : LinearPricing q R)
    (hs : Function.Surjective R.mulVec) (w : ℝ) :
    {c : S → ℝ | ∃ a : A → ℝ, R *ᵥ a = c ∧ ∑ j, a j = w} =
      {c : S → ℝ | ∑ s, q s * c s = w} := by
  ext c
  constructor
  · rintro ⟨a, rfl, hw⟩
    change ∑ s, q s * (R *ᵥ a) s = w
    rw [value_of_payoff hq, hw]
  · intro hc
    obtain ⟨a, ha⟩ := hs c
    refine ⟨a, ha, ?_⟩
    change ∑ s, q s * c s = w at hc
    rw [← value_of_payoff hq, ha, hc]

/-- **Arrow–Debreu prices are pinned down under spanning**: two state-price vectors that both
price all assets linearly coincide when `R` spans. -/
theorem pricing_unique {q q' : S → ℝ} {R : Matrix S A ℝ} (hq : LinearPricing q R)
    (hq' : LinearPricing q' R) (hs : Function.Surjective R.mulVec) : q = q' := by
  classical
  funext s
  obtain ⟨a, ha⟩ := hs (Pi.single s 1)
  have h1 := value_of_payoff hq a
  have h2 := value_of_payoff hq' a
  rw [ha] at h1 h2
  simpa [Pi.single_apply] using h1.trans h2.symm

/-- **Bond redundancy**, O&R (7), p. 273: with a full set of Arrow–Debreu securities (payoff
matrix the identity, which spans), the bond's payoff `1 + r` in every state is replicated by
`1 + r` units of every Arrow–Debreu security, whose cost at prices `p(s)/(1 + r)` is `Σ_s p(s)`;
the law of one price (bond price `1`) therefore forces `Σ_s p(s) = 1`. -/
theorem bond_redundant [DecidableEq S] {p : S → ℝ} {r : ℝ} (hr : 1 + r ≠ 0) :
    Function.Surjective (1 : Matrix S S ℝ).mulVec ∧
      (1 : Matrix S S ℝ) *ᵥ (fun _ => 1 + r) = (fun _ => 1 + r) ∧
      ∑ s, p s / (1 + r) * (1 + r) = ∑ s, p s := by
  refine ⟨fun c => ⟨c, Matrix.one_mulVec c⟩, Matrix.one_mulVec _, ?_⟩
  exact Finset.sum_congr rfl fun s _ => div_mul_cancel₀ _ hr

/-! ## Spanning is not necessary for efficiency -/

/-- The gross-return matrix of the §5.3 economy, O&R p. 336: the bond column pays `1 + r`,
and country `m`'s column pays `1 + rᵐ(s) = Y₂ᵐ(s)/V₁ᵐ`. -/
noncomputable def returnMatrix {ι : Type} (r : ℝ) (V : ι → ℝ) (Y2 : ι → S → ℝ) :
    Matrix S (Option ι) ℝ :=
  Matrix.of fun s j => Option.elim j (1 + r) fun m => Y2 m s / V m

omit [Fintype S] in
/-- The payoff of a portfolio in the §5.3 economy, O&R p. 336: investing `a₀` in bonds and
`aₘ` in country `m`'s fund (a share `aₘ/V₁ᵐ` of its output) pays
`(1 + r)a₀ + Σₘ (aₘ/V₁ᵐ) Y₂ᵐ(s)`. -/
theorem returnMatrix_mulVec {ι : Type} [Fintype ι] (r : ℝ) (V : ι → ℝ) (Y2 : ι → S → ℝ)
    (a : Option ι → ℝ) (s : S) :
    (returnMatrix r V Y2 *ᵥ a) s = (1 + r) * a none + ∑ m, a (some m) / V m * Y2 m s := by
  simp only [Matrix.mulVec, dotProduct, returnMatrix, Matrix.of_apply, Fintype.sum_option,
    Option.elim]
  exact congrArg₂ (· + ·) (by ring) (Finset.sum_congr rfl fun m _ => by ring)

/-- **Efficiency without spanning**, O&R §5.3.3 (p. 303) versus p. 304: in the CRRA economy
of §5.3.2 with more states than assets (`S > N + 1`), bonds and shares cannot span the
state space — some payoffs are unattainable — yet the equilibrium allocation satisfies all
the complete-markets Euler equations at the Arrow–Debreu prices (30) (and the complete-markets
budget constraints, `PortfolioEconomy.ad_budget`). So `S ≤ N + 1` is not necessary for
Pareto efficiency. -/
theorem efficient_without_spanning {ι : Type} [Fintype ι]
    (P : PortfolioDiversification.PortfolioEconomy ι S)
    (hS : Fintype.card ι + 1 < Fintype.card S) :
    ¬ Function.Surjective (returnMatrix P.R P.V P.Y2).mulVec ∧
      ∀ n s, PortfolioDiversification.adPrice P.Ω P.β P.ρ P.Y1 P.Y2 s * P.C1 n ^ (-P.ρ) =
        P.Ω.prob s * P.β * P.C2 n s ^ (-P.ρ) := by
  refine ⟨not_spans_of_card_lt ?_, fun n s => P.ad_euler n s⟩
  rw [Fintype.card_option]
  exact hS

end ObstfeldRogoff.InternationalFinancialMarkets.Spanning

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Asset pricing: the consumption-based CAPM

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §5.4,
pp. 306–319, and the Lucas welfare-cost application of §5.5, pp. 329–331.

Uncertainty is a finite state space (`InternationalFinancialMarkets.Model`), with moments from
`InternationalFinancialMarkets.Probability`. The stochastic discount factor (intertemporal
marginal rate of substitution) is `M(s) = βu′(C₂(s))/u′(C₁)`. We prove:
* (51) `V = E[MY]` from the Arrow–Debreu (AD) pricing condition (6), the bond price
  `E[M] = 1/(1+r)` from `Σ p(s) = 1`, (52) `V = E[Y]/(1+r) + Cov(M, Y)`, and the
  consumption CAPM (53), together with footnote 32 (shift invariance of the covariance);
* §5.4.1.3: under incomplete markets, every country that trades bonds and the country-`m`
  share has the same `Cov(Mⁿ, rᵐ)`, and with multiplicative productivity shocks spanned by
  bonds and shares every owner values investment identically, including its derivative;
* the Hansen–Jagannathan bound (footnote 38);
* the equity-premium relation, exactly, for the linearised discount factor
  `M = β(1 − ρ(C₂/C₁ − 1))` (the Taylor approximation leading to it is informal in the book),
  and the Mankiw–Zeldes calibration `ρ ≈ 25.7`;
* the lognormal riskless rate (p. 313), exact under the lognormal moment-generating identity
  (taken as a hypothesis), and the 3.34 percent figure;
* Lucas's welfare cost of consumption variability (75): the closed forms, the book's
  `τ = {exp[½(1−ρ)ρV]}^{1/(1−ρ)} − 1` equals exactly `exp(ρV/2) − 1` (so `τ ≥ ρV/2`), and
  `τ ≈ 0.35%` at `ρ = 10`;
* infinite-horizon pricing (59) and (61) in a deterministic (perfect-foresight) economy:
  the truncated identity, and the limit under an explicit no-bubble hypothesis; plus the
  date-by-date decomposition of (59) into discount factors (60) and covariances.
-/

namespace ObstfeldRogoff.InternationalFinancialMarkets.AssetPricing

open Finset Filter Topology

variable {S : Type} [Fintype S] (Ω : StateSpace S)

/-! ## The consumption CAPM (§5.4.1, pp. 306–308) -/

/-- **O&R (5.51), pp. 306–307**: if AD prices satisfy the first-order condition (6),
`p(s)/(1+r) = π(s)M(s)` with `M = βu′(C₂)/u′(C₁)`, then the AD value of the payoff `Y`
equals `E[MY]`. -/
theorem price_eq_expect_sdf (p M Y : S → ℝ) (r : ℝ)
    (hfoc : ∀ s, p s / (1 + r) = Ω.prob s * M s) :
    ∑ s, p s * Y s / (1 + r) = Ω.expect (fun s => M s * Y s) := by
  unfold StateSpace.expect
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [mul_div_right_comm, hfoc s]
  ring

/-- **The bond price**, O&R (5.8) as used on p. 307: with `Σ p(s) = 1` (O&R (5.7)) and the
first-order conditions (6), `E[M] = 1/(1+r)`. -/
theorem expect_sdf_eq_bond_price (p M : S → ℝ) {r : ℝ}
    (hp : ∑ s, p s = 1) (hfoc : ∀ s, p s / (1 + r) = Ω.prob s * M s) :
    Ω.expect M = 1 / (1 + r) := by
  unfold StateSpace.expect
  rw [← Finset.sum_congr rfl fun s _ => hfoc s, ← Finset.sum_div, hp]

/-- **O&R (5.52), p. 307**: if `V = E[MY]` and the bond is priced by `E[M] = 1/(1+r)`, then
`V = E[Y]/(1+r) + Cov(M, Y)`. -/
theorem price_eq_discounted_mean_add_cov (M Y : S → ℝ) {r V : ℝ}
    (hV : V = Ω.expect (fun s => M s * Y s)) (hbond : Ω.expect M = 1 / (1 + r)) :
    V = Ω.expect Y / (1 + r) + Ω.cov M Y := by
  rw [hV, Ω.expect_mul_eq, hbond]
  ring

/-- **Pricing a gross return**, O&R p. 307: a gross return `R` with `E[MR] = 1`, and the bond
Euler equation `E[M] = 1/(1+r)` (`r > −1`), satisfy `E[R] − (1+r) = −(1+r) Cov(M, R)`. -/
theorem expect_gross_return_sub (M R : S → ℝ) {r : ℝ} (hr : 1 + r ≠ 0)
    (hR : Ω.expect (fun s => M s * R s) = 1) (hbond : Ω.expect M = 1 / (1 + r)) :
    Ω.expect R - (1 + r) = -(1 + r) * Ω.cov M R := by
  have h := Ω.expect_mul_eq M R
  rw [hR, hbond] at h
  field_simp at h ⊢
  linarith

/-- **The consumption-based CAPM, O&R (5.53), p. 307**: with `V = E[MY] ≠ 0`, the bond price
`E[M] = 1/(1+r)` and the net return `rᵐ = (Y − V)/V`,
`E[rᵐ] − r = −(1+r)Cov(M, 1 + rᵐ) = −(1+r)Cov(M, rᵐ − r)`. -/
theorem consumption_capm (M Y : S → ℝ) {r V : ℝ} (hr : 1 + r ≠ 0) (hV0 : V ≠ 0)
    (hV : V = Ω.expect (fun s => M s * Y s)) (hbond : Ω.expect M = 1 / (1 + r)) :
    Ω.expect (fun s => (Y s - V) / V) - r =
        -(1 + r) * Ω.cov M (fun s => 1 + (Y s - V) / V) ∧
      Ω.expect (fun s => (Y s - V) / V) - r =
        -(1 + r) * Ω.cov M (fun s => (Y s - V) / V - r) := by
  have hR : Ω.expect (fun s => M s * (1 + (Y s - V) / V)) = 1 := by
    have e : (fun s => M s * (1 + (Y s - V) / V)) = fun s => V⁻¹ * (M s * Y s) := by
      funext s; field_simp; ring
    rw [e, Ω.expect_smul, ← hV, inv_mul_cancel₀ hV0]
  have h := expect_gross_return_sub Ω M (fun s => 1 + (Y s - V) / V) hr hR hbond
  rw [Ω.expect_add, Ω.expect_const] at h
  have hshift : Ω.cov M (fun s => (Y s - V) / V - r) =
      Ω.cov M (fun s => 1 + (Y s - V) / V) := by
    rw [Ω.cov_comm, Ω.cov_comm M (fun s => 1 + (Y s - V) / V)]
    have e1 : (fun s => (Y s - V) / V - r) = fun s => -r + (Y s - V) / V := by
      funext s; ring
    rw [e1, Ω.cov_const_add, Ω.cov_const_add]
  refine ⟨by linarith, by rw [hshift]; linarith⟩

/-- **O&R footnote 32, p. 308**: `Cov(M, rᵐ + a₀) = Cov(M, rᵐ)` for any constant `a₀`. -/
theorem cov_add_const_right (M X : S → ℝ) (a₀ : ℝ) :
    Ω.cov M (fun s => X s + a₀) = Ω.cov M X := by
  rw [Ω.cov_comm, Ω.cov_comm M X]
  have e : (fun s => X s + a₀) = fun s => a₀ + X s := by funext s; ring
  rw [e, Ω.cov_const_add]

/-! ## Incomplete markets (§5.4.1.3, pp. 308–309) -/

/-- **O&R §5.4.1.3, p. 308**: under incomplete markets, if every country `n` trades the
riskless bond (Euler equation (8), `E[Mⁿ] = 1/(1+r)`) and the country-`m` share (Euler
equation (44), `E[Mⁿ(1 + rᵐ)] = 1`), then
`Cov(Mⁿ, rᵐ) = (1/(1+r))(1 + r − E(1 + rᵐ))`, the same for every country. -/
theorem cov_sdf_return_incomplete {ι : Type} (M : ι → S → ℝ) (rm : S → ℝ) {r : ℝ}
    (hr : 1 + r ≠ 0)
    (hbond : ∀ n, Ω.expect (M n) = 1 / (1 + r))
    (hshare : ∀ n, Ω.expect (fun s => M n s * (1 + rm s)) = 1) :
    (∀ n, Ω.cov (M n) rm = 1 / (1 + r) * (1 + r - Ω.expect (fun s => 1 + rm s))) ∧
      ∀ n k, Ω.cov (M n) rm = Ω.cov (M k) rm := by
  have key : ∀ n, Ω.cov (M n) rm = 1 / (1 + r) * (1 + r - Ω.expect (fun s => 1 + rm s)) := by
    intro n
    have h := Ω.expect_mul_eq (M n) (fun s => 1 + rm s)
    rw [hshare n, hbond n] at h
    have hc : Ω.cov (M n) (fun s => 1 + rm s) = Ω.cov (M n) rm := by
      rw [Ω.cov_comm, Ω.cov_const_add, Ω.cov_comm]
    rw [← hc]
    field_simp at h ⊢
    linarith
  exact ⟨key, fun n k => by rw [key n, key k]⟩

/-- **Investment under incomplete markets, O&R pp. 308–309**: the country-`m` firm pays
`A(s)F(K) + K` (multiplicative productivity uncertainty, no depreciation, footnote 35). If
every owner `n` prices the bond (`E[Mⁿ] = 1/(1+r)`) and the firm's shares at the installed
capital `K₀` (`E[Mⁿ(AF(K₀) + K₀)] = V₀`, the common share price) and `F(K₀) ≠ 0`, then for
EVERY `K` all owners agree on the net value `V − K`, which equals
`E[AF(K) + K]/(1+r) + Cov(Mⁿ, A)F(K) − K`. -/
theorem investment_value_invariant {ι : Type} (M : ι → S → ℝ) (A : S → ℝ) (F : ℝ → ℝ)
    {r K₀ V₀ : ℝ} (hF : F K₀ ≠ 0) (hbond : ∀ n, Ω.expect (M n) = 1 / (1 + r))
    (hshare : ∀ n, Ω.expect (fun s => M n s * (A s * F K₀ + K₀)) = V₀) (K : ℝ) :
    (∀ n, Ω.expect (fun s => M n s * (A s * F K + K)) - K =
        Ω.expect (fun s => A s * F K + K) / (1 + r) + Ω.cov (M n) A * F K - K) ∧
      ∀ n k, Ω.expect (fun s => M n s * (A s * F K + K)) - K =
        Ω.expect (fun s => M k s * (A s * F K + K)) - K := by
  have lin : ∀ n (x y : ℝ), Ω.expect (fun s => M n s * (A s * x + y)) =
      x * Ω.expect (fun s => M n s * A s) + y * Ω.expect (M n) := by
    intro n x y
    have e : (fun s => M n s * (A s * x + y)) = fun s => x * (M n s * A s) + y * M n s := by
      funext s; ring
    rw [e, Ω.expect_add, Ω.expect_smul, Ω.expect_smul]
  have hMA : ∀ n, Ω.expect (fun s => M n s * A s) = (V₀ - K₀ / (1 + r)) / F K₀ := by
    intro n
    have h := hshare n
    rw [lin, hbond, mul_one_div] at h
    rw [eq_div_iff hF]
    linarith
  refine ⟨fun n => ?_, fun n k => by rw [lin, lin, hMA, hMA, hbond, hbond]⟩
  have e2 : (fun s => A s * F K + K) = fun s => K + F K * A s := by funext s; ring
  rw [lin, e2, Ω.expect_add, Ω.expect_const, Ω.expect_smul, Ω.expect_mul_eq, hbond]
  ring

/-- **The investment derivative, O&R p. 309**: with the net value written as in
`investment_value_invariant`, `d(V − K)/dK = E[(AF′(K) + 1)/(1+r)] + Cov(Mⁿ, A)F′(K) − 1`,
which (by `investment_value_invariant`) does not depend on the owner `n`. -/
theorem investment_value_hasDerivAt (M A : S → ℝ) (F : ℝ → ℝ) {r F' K : ℝ}
    (hFd : HasDerivAt F F' K) :
    HasDerivAt (fun k => Ω.expect (fun s => A s * F k + k) / (1 + r) + Ω.cov M A * F k - k)
      (Ω.expect (fun s => (A s * F' + 1) / (1 + r)) + Ω.cov M A * F' - 1) K := by
  have e : (fun k => Ω.expect (fun s => A s * F k + k) / (1 + r) + Ω.cov M A * F k - k) =
      fun k => (Ω.expect A / (1 + r) + Ω.cov M A) * F k + (1 / (1 + r) - 1) * k := by
    funext k
    have e2 : (fun s => A s * F k + k) = fun s => k + F k * A s := by funext s; ring
    rw [e2, Ω.expect_add, Ω.expect_const, Ω.expect_smul]
    ring
  have e3 : Ω.expect (fun s => (A s * F' + 1) / (1 + r)) =
      Ω.expect A * F' / (1 + r) + 1 / (1 + r) := by
    have e4 : (fun s => (A s * F' + 1) / (1 + r)) =
        fun s => 1 / (1 + r) + (F' / (1 + r)) * A s := by
      funext s; ring
    rw [e4, Ω.expect_add, Ω.expect_const, Ω.expect_smul]
    ring
  rw [e, e3]
  have h1 := (hFd.const_mul (Ω.expect A / (1 + r) + Ω.cov M A))
  have h2 := ((hasDerivAt_id' K).const_mul (1 / (1 + r) - 1))
  refine (HasDerivAt.add h1 h2).congr_deriv ?_
  ring

/-! ## The Hansen–Jagannathan bound (footnote 38, pp. 311–312) -/

/-- **The Hansen–Jagannathan bound, O&R footnote 38**: if the gross return `R = 1 + rᵐ`
satisfies the Euler equation `E[MR] = 1`, then `Std(M)Std(R) ≥ 1 − E(M)E(R)`. -/
theorem hansen_jagannathan (M R : S → ℝ) (hR : Ω.expect (fun s => M s * R s) = 1) :
    1 - Ω.expect M * Ω.expect R ≤ Ω.std M * Ω.std R := by
  have h := Ω.expect_mul_eq M R
  rw [hR] at h
  have hc : Ω.cov M R = 1 - Ω.expect M * Ω.expect R := by linarith
  rw [← hc]
  exact (le_abs_self _).trans (Ω.abs_cov_le M R)

/-- **The Hansen–Jagannathan bound in ratio form**, O&R footnote 38:
`Std(M) ≥ (1 − E(M)E(R))/Std(R)` when `Std(R) > 0`. -/
theorem hansen_jagannathan_div (M R : S → ℝ) (hR : Ω.expect (fun s => M s * R s) = 1)
    (hstd : 0 < Ω.std R) :
    (1 - Ω.expect M * Ω.expect R) / Ω.std R ≤ Ω.std M := by
  rw [div_le_iff₀ hstd]
  exact hansen_jagannathan Ω M R hR

/-! ## The equity premium (§5.4.2, pp. 310–312) -/

/-- **The equity premium, exact version of O&R p. 311**: if the discount factor is exactly
the linearised `M = β(1 − ρ(g − 1))`, `g = C₂/C₁` (the book obtains this only by a Taylor
approximation), `E[M] = 1/(1+r)` and `E[M(1 + rᵐ)] = 1`, then
`E[rᵐ] − r = (1+r)βρ Cov(g − 1, rᵐ − r) = (1+r)βρ Cov(g, rᵐ)`. -/
theorem equity_premium_linear_sdf (g rm : S → ℝ) {β ρ r : ℝ} (hr : 1 + r ≠ 0)
    (hbond : Ω.expect (fun s => β * (1 - ρ * (g s - 1))) = 1 / (1 + r))
    (hshare : Ω.expect (fun s => β * (1 - ρ * (g s - 1)) * (1 + rm s)) = 1) :
    Ω.expect rm - r = (1 + r) * β * ρ * Ω.cov (fun s => g s - 1) (fun s => rm s - r) ∧
      Ω.expect rm - r = (1 + r) * β * ρ * Ω.cov g rm := by
  have h := expect_gross_return_sub Ω (fun s => β * (1 - ρ * (g s - 1))) (fun s => 1 + rm s)
    hr hshare hbond
  rw [Ω.expect_add, Ω.expect_const] at h
  have hM : (fun s => β * (1 - ρ * (g s - 1))) = fun s => (β + β * ρ) + (-(β * ρ)) * g s := by
    funext s; ring
  have hc : Ω.cov (fun s => β * (1 - ρ * (g s - 1))) (fun s => 1 + rm s) =
      -(β * ρ) * Ω.cov g rm := by
    rw [hM, Ω.cov_const_add, Ω.cov_smul, Ω.cov_comm, Ω.cov_const_add, Ω.cov_comm]
  have hc2 : Ω.cov (fun s => g s - 1) (fun s => rm s - r) = Ω.cov g rm := by
    have e1 : (fun s => g s - 1) = fun s => -1 + g s := by funext s; ring
    have e2 : (fun s => rm s - r) = fun s => -r + rm s := by funext s; ring
    rw [e1, e2, Ω.cov_const_add, Ω.cov_comm, Ω.cov_const_add, Ω.cov_comm]
  rw [hc] at h
  rw [hc2]
  exact ⟨by linarith, by linarith⟩

/-- **Covariance via correlation**, O&R p. 311: `Cov(X, Y) = Corr(X, Y)·Std(X)·Std(Y)` when
both standard deviations are positive (so the equity premium is `(1+r)βρκ Std Std`). -/
theorem cov_eq_corr_mul_std (X Y : S → ℝ) (hX : 0 < Ω.std X) (hY : 0 < Ω.std Y) :
    Ω.cov X Y = Ω.corr X Y * Ω.std X * Ω.std Y := by
  unfold StateSpace.corr
  field_simp

/-- **The Mankiw–Zeldes calibration, O&R p. 311**: with `(1+r)β = 1`, `κ = 0.4`,
`Std(g) = 0.036`, `Std(rᵐ − r) = 0.167`, matching the premium `0.0618` requires
`ρ = 0.0618/(0.4·0.036·0.167) ≈ 25.7` ("roughly 26"). -/
theorem mankiw_zeldes_rho :
    (25.6 : ℝ) < 0.0618 / (0.4 * 0.036 * 0.167) ∧
      (0.0618 : ℝ) / (0.4 * 0.036 * 0.167) < 25.8 := by
  constructor <;> norm_num

/-! ## The riskless-rate puzzle (p. 313) -/

/-- **The lognormal riskless rate, O&R p. 313**: with CRRA utility the bond Euler equation is
`(1+r)E[βg^{−ρ}] = 1`, `g = C_{t+1}/C_t > 0`. If `log g` satisfies the lognormal
moment-generating identity at `k = −ρ`,
`E[exp(−ρ log g)] = exp(−ρE log g + (ρ²/2)Var(log g))` (an explicit hypothesis; footnote 41),
then exactly `log(1+r) = ρE log g − (ρ²/2)Var(log g) − log β`. -/
theorem log_riskless_rate_lognormal (g : S → ℝ) {β ρ r : ℝ} (hβ : 0 < β)
    (hg : ∀ s, 0 < g s)
    (heuler : (1 + r) * Ω.expect (fun s => β * g s ^ (-ρ)) = 1)
    (hmgf : Ω.expect (fun s => Real.exp (-ρ * Real.log (g s))) =
      Real.exp (-ρ * Ω.expect (fun s => Real.log (g s)) +
        ρ ^ 2 / 2 * Ω.var (fun s => Real.log (g s)))) :
    Real.log (1 + r) = ρ * Ω.expect (fun s => Real.log (g s)) -
      ρ ^ 2 / 2 * Ω.var (fun s => Real.log (g s)) - Real.log β := by
  have hpow : (fun s => β * g s ^ (-ρ)) = fun s => β * Real.exp (-ρ * Real.log (g s)) := by
    funext s
    rw [Real.rpow_def_of_pos (hg s), mul_comm (Real.log (g s))]
  rw [hpow, Ω.expect_smul, hmgf] at heuler
  have h1 : 1 + r = (β * Real.exp (-ρ * Ω.expect (fun s => Real.log (g s)) +
      ρ ^ 2 / 2 * Ω.var (fun s => Real.log (g s))))⁻¹ := by
    exact eq_inv_of_mul_eq_one_left heuler
  rw [h1, Real.log_inv, Real.log_mul hβ.ne' (Real.exp_pos _).ne', Real.log_exp]
  ring

/-- **The 3.34 percent figure, O&R p. 313**: with `E log g = 0.018`, `Var(log g) = 0.0013`,
`ρ = 2`, `β = 1`, the formula gives `log(1+r) = 0.0334`. -/
theorem riskless_rate_mehra_prescott :
    (2 : ℝ) * 0.018 - (2 : ℝ) ^ 2 / 2 * 0.0013 - Real.log 1 = 0.0334 := by
  rw [Real.log_one]; norm_num

/-! ## Lucas's welfare cost of consumption variability (pp. 329–331) -/

/-- Lucas's consumption path, O&R p. 330: `C_{t+n}(ε) = (1+g)ⁿ C̄ exp(ε − V/2)`, where `ε` is
the (i.i.d.) shock with variance `V`. -/
noncomputable def lucasConsumption (g Cbar V : ℝ) (n : ℕ) (e : ℝ) : ℝ :=
  (1 + g) ^ n * Cbar * Real.exp (e - V / 2)

/-- **Expected utility per period, O&R p. 330**: if the shock satisfies the lognormal
moment-generating identity `E[exp((1−ρ)ε)] = exp((1−ρ)²V/2)` (hypothesis), then
`E[C_{t+n}^{1−ρ}] = ((1+g)ⁿC̄)^{1−ρ} exp[−½(1−ρ)ρV]`. -/
theorem expect_lucas_rpow (ε : S → ℝ) {g Cbar V ρ : ℝ} (hg : -1 < g) (hC : 0 < Cbar)
    (hmgf : Ω.expect (fun s => Real.exp ((1 - ρ) * ε s)) = Real.exp ((1 - ρ) ^ 2 * V / 2))
    (n : ℕ) :
    Ω.expect (fun s => lucasConsumption g Cbar V n (ε s) ^ (1 - ρ)) =
      ((1 + g) ^ n * Cbar) ^ (1 - ρ) * Real.exp (-(1 / 2) * (1 - ρ) * ρ * V) := by
  have hpos : 0 ≤ (1 + g) ^ n * Cbar := by
    have : 0 < 1 + g := by linarith
    positivity
  have e : (fun s => lucasConsumption g Cbar V n (ε s) ^ (1 - ρ)) =
      fun s => (((1 + g) ^ n * Cbar) ^ (1 - ρ) * Real.exp (-((1 - ρ) * V / 2))) *
        Real.exp ((1 - ρ) * ε s) := by
    funext s
    unfold lucasConsumption
    rw [Real.mul_rpow hpos (Real.exp_pos _).le, ← Real.exp_mul, mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [e, Ω.expect_smul, hmgf, mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- **Expected consumption, O&R p. 330**: with `E[exp ε] = exp(V/2)` (lognormal identity at
`k = 1`, hypothesis), `E[C_{t+n}] = (1+g)ⁿC̄`, the certainty path `C̄_s = E_t C_s`. -/
theorem expect_lucas_consumption (ε : S → ℝ) {g Cbar V : ℝ}
    (hmgf1 : Ω.expect (fun s => Real.exp (ε s)) = Real.exp (V / 2)) (n : ℕ) :
    Ω.expect (fun s => lucasConsumption g Cbar V n (ε s)) = (1 + g) ^ n * Cbar := by
  have e : (fun s => lucasConsumption g Cbar V n (ε s)) =
      fun s => ((1 + g) ^ n * Cbar * Real.exp (-(V / 2))) * Real.exp (ε s) := by
    funext s
    unfold lucasConsumption
    rw [mul_assoc ((1 + g) ^ n * Cbar), ← Real.exp_add]
    congr 2
    ring
  rw [e, Ω.expect_smul, hmgf1, mul_assoc, ← Real.exp_add]
  simp

/-- **Lifetime utility under uncertainty, O&R p. 330**: with `β > 0`, `g > −1`, `ρ ≠ 1` and
`β(1+g)^{1−ρ} < 1`, `U_t = Σ βⁿ E[C_{t+n}^{1−ρ}]/(1−ρ)` converges to
`C̄^{1−ρ}/(1−ρ) · 1/(1 − β(1+g)^{1−ρ}) · exp[−½(1−ρ)ρV]`. -/
theorem lucas_lifetime_utility (ε : S → ℝ) {β g Cbar V ρ : ℝ} (hβ : 0 < β) (hg : -1 < g)
    (hC : 0 < Cbar) (hconv : β * (1 + g) ^ (1 - ρ) < 1)
    (hmgf : Ω.expect (fun s => Real.exp ((1 - ρ) * ε s)) = Real.exp ((1 - ρ) ^ 2 * V / 2)) :
    HasSum (fun n : ℕ => β ^ n *
        Ω.expect (fun s => lucasConsumption g Cbar V n (ε s) ^ (1 - ρ)) / (1 - ρ))
      (Cbar ^ (1 - ρ) / (1 - ρ) * (1 / (1 - β * (1 + g) ^ (1 - ρ))) *
        Real.exp (-(1 / 2) * (1 - ρ) * ρ * V)) := by
  have h1g : 0 < 1 + g := by linarith
  have hq0 : 0 ≤ β * (1 + g) ^ (1 - ρ) := by positivity
  have hgeo := (hasSum_geometric_of_lt_one hq0 hconv).mul_left
    (Cbar ^ (1 - ρ) / (1 - ρ) * Real.exp (-(1 / 2) * (1 - ρ) * ρ * V))
  convert hgeo using 1
  · funext n
    rw [expect_lucas_rpow Ω ε hg hC hmgf n, Real.mul_rpow (by positivity) hC.le,
      ← Real.rpow_pow_comm h1g.le, mul_pow]
    ring
  · rw [one_div]; ring

/-- **Lifetime utility on the certainty path, O&R p. 330**: `Ū_t = Σ βⁿ((1+g)ⁿC̄)^{1−ρ}/(1−ρ)
= C̄^{1−ρ}/(1−ρ) · 1/(1 − β(1+g)^{1−ρ})`. -/
theorem lucas_certain_utility {β g Cbar ρ : ℝ} (hβ : 0 < β) (hg : -1 < g) (hC : 0 < Cbar)
    (hconv : β * (1 + g) ^ (1 - ρ) < 1) :
    HasSum (fun n : ℕ => β ^ n * ((1 + g) ^ n * Cbar) ^ (1 - ρ) / (1 - ρ))
      (Cbar ^ (1 - ρ) / (1 - ρ) * (1 / (1 - β * (1 + g) ^ (1 - ρ)))) := by
  have h1g : 0 < 1 + g := by linarith
  have hq0 : 0 ≤ β * (1 + g) ^ (1 - ρ) := by positivity
  have hgeo := (hasSum_geometric_of_lt_one hq0 hconv).mul_left (Cbar ^ (1 - ρ) / (1 - ρ))
  convert hgeo using 1
  · funext n
    rw [Real.mul_rpow (by positivity) hC.le, ← Real.rpow_pow_comm h1g.le, mul_pow]
    ring
  · rw [one_div]

/-- **The book's welfare cost simplifies exactly, O&R (75), p. 330**: for `ρ ≠ 1`,
`{exp[½(1−ρ)ρV]}^{1/(1−ρ)} − 1 = exp(ρV/2) − 1`. (The book reports only the unsimplified
formula and the first-order approximation `τ ≈ ρV/2`.) -/
theorem lucas_tau_simplifies {ρ V : ℝ} (hρ : ρ ≠ 1) :
    Real.exp (1 / 2 * (1 - ρ) * ρ * V) ^ (1 / (1 - ρ)) - 1 = Real.exp (ρ * V / 2) - 1 := by
  have h : 1 - ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm hρ)
  rw [← Real.exp_mul]
  congr 2
  field_simp

/-- **The equivalent variation, O&R p. 330**: for `C̄ > 0` and `ρ ≠ 1`, `τ > −1` solves
`[(1+τ)C̄]^{1−ρ}/(1−ρ) · exp[−½(1−ρ)ρV] = C̄^{1−ρ}/(1−ρ)` if and only if
`τ = exp(ρV/2) − 1`. -/
theorem lucas_tau_iff {ρ V Cbar τ : ℝ} (hρ : ρ ≠ 1) (hC : 0 < Cbar) (hτ : -1 < τ) :
    ((1 + τ) * Cbar) ^ (1 - ρ) / (1 - ρ) * Real.exp (-(1 / 2) * (1 - ρ) * ρ * V) =
        Cbar ^ (1 - ρ) / (1 - ρ) ↔ τ = Real.exp (ρ * V / 2) - 1 := by
  have h : 1 - ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm hρ)
  have h1 : 0 < 1 + τ := by linarith
  have hCp : 0 < Cbar ^ (1 - ρ) := Real.rpow_pos_of_pos hC _
  have hcne : Cbar ^ (1 - ρ) / (1 - ρ) ≠ 0 := div_ne_zero hCp.ne' h
  have hE : Real.exp (ρ * V / 2 * (1 - ρ)) * Real.exp (-(1 / 2) * (1 - ρ) * ρ * V) = 1 := by
    rw [← Real.exp_add, show ρ * V / 2 * (1 - ρ) + -(1 / 2) * (1 - ρ) * ρ * V = 0 by ring,
      Real.exp_zero]
  rw [Real.mul_rpow h1.le hC.le]
  have step1 : ((1 + τ) ^ (1 - ρ) * Cbar ^ (1 - ρ) / (1 - ρ) *
      Real.exp (-(1 / 2) * (1 - ρ) * ρ * V) = Cbar ^ (1 - ρ) / (1 - ρ)) ↔
      (1 + τ) ^ (1 - ρ) * Real.exp (-(1 / 2) * (1 - ρ) * ρ * V) = 1 := by
    constructor
    · intro heq
      refine mul_left_cancel₀ hcne ?_
      linear_combination heq
    · intro heq
      calc (1 + τ) ^ (1 - ρ) * Cbar ^ (1 - ρ) / (1 - ρ) * Real.exp (-(1 / 2) * (1 - ρ) * ρ * V)
          = Cbar ^ (1 - ρ) / (1 - ρ) *
              ((1 + τ) ^ (1 - ρ) * Real.exp (-(1 / 2) * (1 - ρ) * ρ * V)) := by ring
        _ = Cbar ^ (1 - ρ) / (1 - ρ) := by rw [heq, mul_one]
  have step2 : (1 + τ) ^ (1 - ρ) * Real.exp (-(1 / 2) * (1 - ρ) * ρ * V) = 1 ↔
      (1 + τ) ^ (1 - ρ) = Real.exp (ρ * V / 2) ^ (1 - ρ) := by
    rw [← Real.exp_mul]
    constructor
    · intro heq
      calc (1 + τ) ^ (1 - ρ)
          = (1 + τ) ^ (1 - ρ) * (Real.exp (ρ * V / 2 * (1 - ρ)) *
              Real.exp (-(1 / 2) * (1 - ρ) * ρ * V)) := by rw [hE, mul_one]
        _ = Real.exp (ρ * V / 2 * (1 - ρ)) *
              ((1 + τ) ^ (1 - ρ) * Real.exp (-(1 / 2) * (1 - ρ) * ρ * V)) := by ring
        _ = Real.exp (ρ * V / 2 * (1 - ρ)) := by rw [heq, mul_one]
    · intro heq
      rw [heq, hE]
  rw [step1, step2]
  constructor
  · intro heq
    have := Real.rpow_left_injOn h (show (0 : ℝ) ≤ 1 + τ from h1.le)
      (show (0 : ℝ) ≤ Real.exp (ρ * V / 2) from (Real.exp_pos _).le) heq
    linarith
  · intro heq
    rw [show 1 + τ = Real.exp (ρ * V / 2) by linarith]

/-- **The first-order approximation (75) is a lower bound**, O&R p. 330: the exact cost
`τ = exp(ρV/2) − 1` satisfies `ρV/2 ≤ τ`, and `τ ≤ (ρV/2)/(1 − ρV/2)` when `0 ≤ ρV/2 < 1`. -/
theorem lucas_tau_bounds {ρ V : ℝ} (h0 : 0 ≤ ρ * V / 2) (h1 : ρ * V / 2 < 1) :
    ρ * V / 2 ≤ Real.exp (ρ * V / 2) - 1 ∧
      Real.exp (ρ * V / 2) - 1 ≤ (ρ * V / 2) / (1 - ρ * V / 2) := by
  constructor
  · linarith [Real.add_one_le_exp (ρ * V / 2)]
  · have h := Real.exp_bound_div_one_sub_of_interval h0 h1
    have hpos : 0 < 1 - ρ * V / 2 := by linarith
    have e : ρ * V / 2 / (1 - ρ * V / 2) = 1 / (1 - ρ * V / 2) - 1 := by
      rw [div_sub_one hpos.ne', sub_sub_cancel]
    rw [e]; linarith

/-- **Lucas's number, O&R p. 330**: with `Var(ε) = 0.000708` and `ρ = 10`, the exact cost
`τ = exp(ρV/2) − 1` lies between 0.35 and 0.36 percent ("about a third of a percent"). -/
theorem lucas_tau_numeric :
    (0.0035 : ℝ) < Real.exp (10 * 0.000708 / 2) - 1 ∧
      Real.exp (10 * 0.000708 / 2) - 1 < (0.0036 : ℝ) := by
  obtain ⟨hl, hu⟩ := lucas_tau_bounds (ρ := 10) (V := 0.000708) (by norm_num) (by norm_num)
  constructor
  · have : (0.0035 : ℝ) < 10 * 0.000708 / 2 := by norm_num
    linarith
  · have : (10 : ℝ) * 0.000708 / 2 / (1 - 10 * 0.000708 / 2) < 0.0036 := by norm_num
    linarith

/-! ## Infinite-horizon pricing (§5.4.3, pp. 315–317), perfect-foresight version -/

/-- **Truncated forward iteration of (57), O&R p. 316** (deterministic economy). If the equity
Euler equation `u′(C_s)V_s = βu′(C_{s+1})(Y_{s+1} + V_{s+1})` holds on every date, with
marginal utilities `m s = u′(C_s) ≠ 0`, then for every horizon `T`,
`V_t = Σ_{k<T} β^{k+1}(m_{t+k+1}/m_t)Y_{t+k+1} + β^T(m_{t+T}/m_t)V_{t+T}`. -/
theorem price_truncated (m V Y : ℕ → ℝ) {β : ℝ} (hm : ∀ s, m s ≠ 0)
    (heuler : ∀ s, m s * V s = β * m (s + 1) * (Y (s + 1) + V (s + 1))) (t T : ℕ) :
    V t = ∑ k ∈ range T, β ^ (k + 1) * (m (t + k + 1) / m t) * Y (t + k + 1) +
      β ^ T * (m (t + T) / m t) * V (t + T) := by
  induction T with
  | zero => simp [hm t]
  | succ T ih =>
    rw [ih, Finset.sum_range_succ]
    have h := heuler (t + T)
    have hV : V (t + T) = β * m (t + T + 1) * (Y (t + T + 1) + V (t + T + 1)) / m (t + T) := by
      rw [← h]; field_simp [hm (t + T)]
    rw [hV, show t + (T + 1) = t + T + 1 by ring]
    field_simp [hm t, hm (t + T)]
    ring

/-- **O&R (5.59), p. 316** (deterministic economy): with the Euler equation (57) on every
date, `β ≥ 0`, positive marginal utilities, nonnegative dividends, and the no-bubble condition
`β^T(m_{t+T}/m_t)V_{t+T} → 0`, the price is the present value
`V_t = Σ_{k≥0} β^{k+1}(m_{t+k+1}/m_t)Y_{t+k+1}`. -/
theorem price_eq_present_value (m V Y : ℕ → ℝ) {β : ℝ} (hβ : 0 ≤ β) (hm : ∀ s, 0 < m s)
    (hY : ∀ s, 0 ≤ Y s)
    (heuler : ∀ s, m s * V s = β * m (s + 1) * (Y (s + 1) + V (s + 1))) (t : ℕ)
    (hbubble : Tendsto (fun T => β ^ T * (m (t + T) / m t) * V (t + T)) atTop (𝓝 0)) :
    HasSum (fun k => β ^ (k + 1) * (m (t + k + 1) / m t) * Y (t + k + 1)) (V t) := by
  have hnn : ∀ k, 0 ≤ β ^ (k + 1) * (m (t + k + 1) / m t) * Y (t + k + 1) := by
    intro k
    have := hm t
    have := hm (t + k + 1)
    have := hY (t + k + 1)
    positivity
  rw [hasSum_iff_tendsto_nat_of_nonneg hnn]
  have hpart : (fun T => ∑ k ∈ range T, β ^ (k + 1) * (m (t + k + 1) / m t) * Y (t + k + 1)) =
      fun T => V t - β ^ T * (m (t + T) / m t) * V (t + T) := by
    funext T
    have := price_truncated m V Y (fun s => (hm s).ne') heuler t T
    linarith
  rw [hpart]
  simpa using (tendsto_const_nhds (x := V t)).sub hbubble

/-- **O&R (5.61), p. 317** (deterministic economy): with CRRA marginal utility
`u′(C) = C^{−ρ}` and each country consuming a constant share `μ > 0` of world output `Y^W > 0`,
the discount factor in (59) is `β^{s−t}(Y^W_s/Y^W_t)^{−ρ}`, independent of `μ`. -/
theorem crra_share_discount (YW : ℕ → ℝ) {μ ρ : ℝ} (hμ : 0 < μ) (hY : ∀ s, 0 < YW s)
    (t s : ℕ) :
    (μ * YW s) ^ (-ρ) / (μ * YW t) ^ (-ρ) = (YW s / YW t) ^ (-ρ) := by
  rw [Real.mul_rpow hμ.le (hY s).le, Real.mul_rpow hμ.le (hY t).le,
    Real.div_rpow (hY s).le (hY t).le]
  have : 0 < μ ^ (-ρ) := Real.rpow_pos_of_pos hμ _
  field_simp

/-- **O&R (5.61), p. 317** (deterministic economy): combining `price_eq_present_value` and
`crra_share_discount`, `V_t = Σ_{s>t} β^{s−t}(Y^W_s/Y^W_t)^{−ρ}Yᵐ_s` under the Euler equation
for `C = μY^W` and the no-bubble condition. -/
theorem price_crra_world_output (YW V Y : ℕ → ℝ) {β μ ρ : ℝ} (hβ : 0 ≤ β) (hμ : 0 < μ)
    (hYW : ∀ s, 0 < YW s) (hY : ∀ s, 0 ≤ Y s)
    (heuler : ∀ s, (μ * YW s) ^ (-ρ) * V s =
      β * (μ * YW (s + 1)) ^ (-ρ) * (Y (s + 1) + V (s + 1))) (t : ℕ)
    (hbubble : Tendsto (fun T => β ^ T * ((μ * YW (t + T)) ^ (-ρ) / (μ * YW t) ^ (-ρ)) *
      V (t + T)) atTop (𝓝 0)) :
    HasSum (fun k => β ^ (k + 1) * (YW (t + k + 1) / YW t) ^ (-ρ) * Y (t + k + 1)) (V t) := by
  have h := price_eq_present_value (fun s => (μ * YW s) ^ (-ρ)) V Y hβ
    (fun s => Real.rpow_pos_of_pos (mul_pos hμ (hYW s)) _) hY heuler t hbubble
  simpa only [crra_share_discount YW hμ hYW] using h

/-- **The decomposition in (59), O&R pp. 316–317**: date by date, the value of the date-`k`
payoff `E_k[M_k Y_k]` equals `R_k E_k[Y_k] + Cov_k(M_k, Y_k)` with the discount factor
`R_k = E_k[M_k]` of (60); summing over a finite horizon gives the truncated form of (59). -/
theorem truncated_price_decomposition (Ωk : ℕ → StateSpace S) (M Y : ℕ → S → ℝ) (T : ℕ) :
    ∑ k ∈ range T, (Ωk k).expect (fun s => M k s * Y k s) =
      ∑ k ∈ range T, (Ωk k).expect (M k) * (Ωk k).expect (Y k) +
        ∑ k ∈ range T, (Ωk k).cov (M k) (Y k) := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => (Ωk k).expect_mul_eq (M k) (Y k)

end ObstfeldRogoff.InternationalFinancialMarkets.AssetPricing

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The role of nontradables

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §5.5,
pp. 319–329.

`N` countries (a type `ι`) consume a tradable good `C_T` and a nontradable good `C_N`, with
period utility `u(C_T, C_N)` (O&R (62)); date-2 states are a finite type `S` with
probabilities `π(s)`. AD securities pay tradables; each country has its own relative price of
nontradables `p_N`. Marginal utilities are given as functions `uT, uN : ℝ → ℝ → ℝ`
(`uT C_T C_N = ∂u/∂C_T`). We prove:
* the efficiency condition (67) from the Euler equations (65) and nontradables market
  clearing (66), and that the second Euler equation in (65) follows from the first and the
  intratemporal condition (64);
* the claim prices (68)–(69) do not depend on whose marginal rate of substitution is used;
* preference shocks: (71) from (70);
* additively separable utility `C_T^{1−ρ}/(1−ρ) + v(C_N)`: tradables consumption growth is
  equalised and equals world tradables growth (74), and the home-bias portfolio
  (footnote 48) satisfies every country's Euler equation for every nontradables claim;
* CES–CRRA utility (72): its marginal utilities (as exact derivatives), the cross-partial
  `∂²u/∂C_N∂C_T` has the sign of `1 − θρ`, the revenue `p_N Y_N` increases in `Y_N` iff
  `θ > 1`, (72) is additively separable iff `θρ = 1`, and the log-linearised equation (73)
  as an exact identity between logarithmic derivatives along any differentiable path;
* log Cobb–Douglas: `p_N Y_N = ((1−γ)/γ) C_T`, so nontradables payoffs are perfectly
  correlated with world tradables and portfolios are indeterminate (p. 329).
-/

namespace ObstfeldRogoff.InternationalFinancialMarkets.Nontradables

open Finset Filter Topology

variable {S : Type} {ι : Type}

/-! ## Complete markets in tradables (§5.5.1, pp. 319–322) -/

/-- **O&R (5.67), p. 321**: if every country's tradables Euler equation (65),
`[p(s)/(1+r)]u_T(C_{T,1}ⁿ, C_{N,1}ⁿ) = π(s)βu_T(C_{T,2}ⁿ(s), C_{N,2}ⁿ(s))`, holds, nontradables
markets clear (66), `C_N = Y_N`, and date-1 marginal utilities are nonzero, then the ex post
marginal rates of substitution for tradables are equal across countries. -/
theorem efficiency_tradables (π p : S → ℝ) (r β : ℝ) (uT : ℝ → ℝ → ℝ)
    (CT1 CN1 YN1 : ι → ℝ) (CT2 CN2 YN2 : ι → S → ℝ)
    (hu : ∀ n, uT (CT1 n) (CN1 n) ≠ 0)
    (heuler : ∀ n s, p s / (1 + r) * uT (CT1 n) (CN1 n) = π s * β * uT (CT2 n s) (CN2 n s))
    (hclear1 : ∀ n, CN1 n = YN1 n) (hclear2 : ∀ n s, CN2 n s = YN2 n s) (m n : ι) (s : S) :
    π s * β * uT (CT2 m s) (YN2 m s) / uT (CT1 m) (YN1 m) =
      π s * β * uT (CT2 n s) (YN2 n s) / uT (CT1 n) (YN1 n) := by
  have key : ∀ k, π s * β * uT (CT2 k s) (YN2 k s) / uT (CT1 k) (YN1 k) = p s / (1 + r) := by
    intro k
    rw [← hclear1, ← hclear2, ← heuler k s]
    field_simp [hu k]
  rw [key m, key n]

/-- **The second Euler equation in (65), O&R p. 320**: it follows from the first and the
intratemporal condition (64), `u_N = p_N u_T`, on date 1 and in state `s` (with `p_{N,1} ≠ 0`):
`(1/p_{N,1})[p_{N,2}(s)p(s)/(1+r)]u_N(date 1) = π(s)βu_N(date 2, s)`. -/
theorem euler_nontradables_of_intratemporal (π p : S → ℝ) (r β pN1 uT1 uN1 : ℝ)
    (pN2 uT2 uN2 : S → ℝ) (hpN1 : pN1 ≠ 0) (h64₁ : uN1 = pN1 * uT1)
    (h64₂ : ∀ s, uN2 s = pN2 s * uT2 s) (heuler : ∀ s, p s / (1 + r) * uT1 = π s * β * uT2 s)
    (s : S) :
    1 / pN1 * (pN2 s * p s / (1 + r)) * uN1 = π s * β * uN2 s := by
  rw [h64₁, h64₂ s]
  have h := heuler s
  field_simp at h ⊢
  linear_combination pN2 s * h

/-- **O&R (5.68)–(5.69), pp. 322**: under the hypotheses of `efficiency_tradables`, the AD
value `Σ p(s)X(s)/(1+r)` of any tradables-denominated payoff `X` equals
`Σ π(s)β[u_T(C_{T,2}ⁿ(s), Y_{N,2}ⁿ(s))/u_T(C_{T,1}ⁿ, Y_{N,1}ⁿ)]X(s)` for EVERY country `n`.
With `X = Y_{T,2}ᵐ` this is (68) (`V_{T,1}ᵐ`), with `X = p_{N,2}ᵐY_{N,2}ᵐ` it is (69)
(`V_{N,1}ᵐ`). -/
theorem claim_price_any_country [Fintype S] (π p : S → ℝ) (r β : ℝ) (uT : ℝ → ℝ → ℝ)
    (CT1 CN1 YN1 : ι → ℝ) (CT2 CN2 YN2 : ι → S → ℝ)
    (hu : ∀ n, uT (CT1 n) (CN1 n) ≠ 0)
    (heuler : ∀ n s, p s / (1 + r) * uT (CT1 n) (CN1 n) = π s * β * uT (CT2 n s) (CN2 n s))
    (hclear1 : ∀ n, CN1 n = YN1 n) (hclear2 : ∀ n s, CN2 n s = YN2 n s) (X : S → ℝ) (n : ι) :
    ∑ s, p s * X s / (1 + r) =
      ∑ s, π s * β * uT (CT2 n s) (YN2 n s) / uT (CT1 n) (YN1 n) * X s := by
  refine Finset.sum_congr rfl fun s _ => ?_
  have h := heuler n s
  rw [hclear1, hclear2] at h
  have hu' := hu n
  rw [hclear1] at hu'
  rw [← h]
  field_simp [hu']

/-- **O&R (5.68)–(5.69), p. 322, independence of the country**: the valuations of any
tradables-denominated payoff by the marginal rates of substitution of countries `n` and `k`
coincide. -/
theorem claim_price_independent [Fintype S] (π p : S → ℝ) (r β : ℝ) (uT : ℝ → ℝ → ℝ)
    (CT1 CN1 YN1 : ι → ℝ) (CT2 CN2 YN2 : ι → S → ℝ)
    (hu : ∀ n, uT (CT1 n) (CN1 n) ≠ 0)
    (heuler : ∀ n s, p s / (1 + r) * uT (CT1 n) (CN1 n) = π s * β * uT (CT2 n s) (CN2 n s))
    (hclear1 : ∀ n, CN1 n = YN1 n) (hclear2 : ∀ n s, CN2 n s = YN2 n s) (X : S → ℝ)
    (n k : ι) :
    ∑ s, π s * β * uT (CT2 n s) (YN2 n s) / uT (CT1 n) (YN1 n) * X s =
      ∑ s, π s * β * uT (CT2 k s) (YN2 k s) / uT (CT1 k) (YN1 k) * X s := by
  rw [← claim_price_any_country π p r β uT CT1 CN1 YN1 CT2 CN2 YN2 hu heuler hclear1 hclear2,
    ← claim_price_any_country π p r β uT CT1 CN1 YN1 CT2 CN2 YN2 hu heuler hclear1 hclear2]

/-! ## Preference shocks (§5.5.2, pp. 322–323) -/

/-- **O&R (5.71), p. 323**: with state-dependent preferences `u(C₂(s); εⁿ(s))` (O&R (70)),
the Euler equations `[p(s)/(1+r)]u′(C₁ⁿ) = π(s)βu′(C₂ⁿ(s); εⁿ(s))` for all countries imply
equal marginal rates of substitution (nonzero date-1 marginal utilities). -/
theorem efficiency_preference_shocks (π p : S → ℝ) (r β : ℝ) (u1' : ℝ → ℝ)
    (u2' : ℝ → ℝ → ℝ) (C1 : ι → ℝ) (C2 ε : ι → S → ℝ) (hu : ∀ n, u1' (C1 n) ≠ 0)
    (heuler : ∀ n s, p s / (1 + r) * u1' (C1 n) = π s * β * u2' (C2 n s) (ε n s))
    (m n : ι) (s : S) :
    π s * β * u2' (C2 m s) (ε m s) / u1' (C1 m) = π s * β * u2' (C2 n s) (ε n s) / u1' (C1 n) := by
  rw [← heuler m s, ← heuler n s]
  field_simp [hu m, hu n]

/-! ## Additively separable utility (§5.5.3, pp. 326–327) -/

/-- **Equal tradables growth, O&R p. 322 and (5.74), p. 326**: with additive utility
`C_T^{1−ρ}/(1−ρ) + v(C_N)` (so `u_T = C_T^{−ρ}`, `ρ > 0`), the tradables Euler equations
`[p(s)/(1+r)](C_{T,1}ⁿ)^{−ρ} = π(s)β(C_{T,2}ⁿ(s))^{−ρ}` with `π(s), β > 0` and positive
consumptions imply that tradables consumption growth is the same in every country. -/
theorem additive_tradables_growth_equal (π p : S → ℝ) {r β ρ : ℝ} (hρ : 0 < ρ) (hβ : 0 < β)
    (hπ : ∀ s, 0 < π s) (CT1 : ι → ℝ) (CT2 : ι → S → ℝ) (h1 : ∀ n, 0 < CT1 n)
    (h2 : ∀ n s, 0 < CT2 n s)
    (heuler : ∀ n s, p s / (1 + r) * CT1 n ^ (-ρ) = π s * β * CT2 n s ^ (-ρ)) (m n : ι)
    (s : S) :
    CT2 m s / CT1 m = CT2 n s / CT1 n := by
  have key : ∀ k, (CT2 k s / CT1 k) ^ (-ρ) = p s / (1 + r) / (π s * β) := by
    intro k
    have hpb : 0 < π s * β := mul_pos (hπ s) hβ
    have hc : 0 < CT1 k ^ (-ρ) := Real.rpow_pos_of_pos (h1 k) _
    rw [Real.div_rpow (h2 k s).le (h1 k).le, eq_div_iff hpb.ne', div_mul_eq_mul_div,
      div_eq_iff hc.ne', heuler k s]
    ring
  have hne : -ρ ≠ 0 := by linarith
  exact Real.rpow_left_injOn hne (div_pos (h2 m s) (h1 m)).le (div_pos (h2 n s) (h1 n)).le
    (by simp only [key m, key n])

/-- **O&R (5.74), p. 326**: under the hypotheses of `additive_tradables_growth_equal`, with
finitely many countries and world tradables market clearing on both dates
(`Σₙ C_{T,1}ⁿ = Y_{T,1}^W`, `Σₙ C_{T,2}ⁿ(s) = Y_{T,2}^W(s)`), every country's tradables
growth equals world tradables growth: `C_{T,2}ⁿ(s)/C_{T,1}ⁿ = Y_{T,2}^W(s)/Y_{T,1}^W`. -/
theorem additive_tradables_growth_world [Fintype ι] (π p : S → ℝ) {r β ρ : ℝ} (hρ : 0 < ρ)
    (hβ : 0 < β) (hπ : ∀ s, 0 < π s) (CT1 : ι → ℝ) (CT2 : ι → S → ℝ) (h1 : ∀ n, 0 < CT1 n)
    (h2 : ∀ n s, 0 < CT2 n s)
    (heuler : ∀ n s, p s / (1 + r) * CT1 n ^ (-ρ) = π s * β * CT2 n s ^ (-ρ))
    {YW1 : ℝ} {YW2 : S → ℝ} (hYW1 : YW1 ≠ 0) (hc1 : ∑ n, CT1 n = YW1)
    (hc2 : ∀ s, ∑ n, CT2 n s = YW2 s) (n : ι) (s : S) :
    CT2 n s / CT1 n = YW2 s / YW1 := by
  have hk : ∀ k, CT2 k s = CT2 n s / CT1 n * CT1 k := by
    intro k
    rw [← additive_tradables_growth_equal π p hρ hβ hπ CT1 CT2 h1 h2 heuler k n s]
    field_simp [(h1 k).ne']
  have hsum : YW2 s = CT2 n s / CT1 n * YW1 := by
    rw [← hc2 s, ← hc1, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => hk k
  rw [hsum]
  field_simp

/-- **The home-bias equilibrium, O&R p. 327 and footnote 48**: with additive utility, let each
country consume a constant share `μₙ > 0` of world tradables on both dates (the equilibrium
(74)) and price every nontradables claim by
`V_{N,1}ᵐ = Σ π(s)β(Y_{T,2}^W(s)/Y_{T,1}^W)^{−ρ}p_{N,2}ᵐ(s)Y_{N,2}ᵐ(s)`. Then every country
`n`'s Euler equation for every claim `m`,
`(C_{T,1}ⁿ)^{−ρ}V_{N,1}ᵐ = βΣπ(s)(C_{T,2}ⁿ(s))^{−ρ}p_{N,2}ᵐ(s)Y_{N,2}ᵐ(s)`, holds; and the
home-bias holdings `x_{N,m}ⁿ = 1` if `m = n`, `0` otherwise, clear every claim market. Since
with additive utility tradables consumption does not depend on nontradables holdings, no
country gains from diversifying its nontradables portfolio. -/
theorem home_bias_equilibrium [Fintype S] [Fintype ι] [DecidableEq ι] (π : S → ℝ) {β ρ YW1 : ℝ}
    (YW2 : S → ℝ) (μ CT1 : ι → ℝ) (CT2 pN2 YN2 : ι → S → ℝ) (hμ : ∀ n, 0 < μ n)
    (hYW1 : 0 < YW1) (hYW2 : ∀ s, 0 < YW2 s) (hC1 : ∀ n, CT1 n = μ n * YW1)
    (hC2 : ∀ n s, CT2 n s = μ n * YW2 s) :
    (∀ n m, CT1 n ^ (-ρ) *
        (∑ s, π s * β * (YW2 s / YW1) ^ (-ρ) * (pN2 m s * YN2 m s)) =
      β * ∑ s, π s * CT2 n s ^ (-ρ) * (pN2 m s * YN2 m s)) ∧
      ∀ m, ∑ n : ι, (if m = n then (1 : ℝ) else 0) = 1 := by
  refine ⟨fun n m => ?_, fun m => by simp⟩
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [hC1, hC2, Real.div_rpow (hYW2 s).le hYW1.le, Real.mul_rpow (hμ n).le hYW1.le,
    Real.mul_rpow (hμ n).le (hYW2 s).le]
  have : 0 < YW1 ^ (-ρ) := Real.rpow_pos_of_pos hYW1 _
  field_simp

/-! ## CES–CRRA utility (§5.5.2–5.5.3, pp. 324–328) -/

/-- The CES aggregator's inner sum in O&R (5.72), p. 324:
`Z = γ^{1/θ}C_T^{(θ−1)/θ} + (1−γ)^{1/θ}C_N^{(θ−1)/θ}`. -/
noncomputable def cesInner (γ θ CT CN : ℝ) : ℝ :=
  γ ^ (1 / θ) * CT ^ ((θ - 1) / θ) + (1 - γ) ^ (1 / θ) * CN ^ ((θ - 1) / θ)

/-- **CES–CRRA utility, O&R (5.72), p. 324**: `u = [Z^{θ/(θ−1)}]^{1−ρ}/(1−ρ)`. -/
noncomputable def cesCrraUtility (γ θ ρ CT CN : ℝ) : ℝ :=
  (cesInner γ θ CT CN ^ (θ / (θ - 1))) ^ (1 - ρ) / (1 - ρ)

/-- The marginal utility of tradables for (5.72), O&R p. 324:
`u_T = γ^{1/θ}C_T^{(θ−1)/θ − 1}Z^{θ(1−ρ)/(θ−1) − 1}`. -/
noncomputable def cesMUT (γ θ ρ CT CN : ℝ) : ℝ :=
  γ ^ (1 / θ) * CT ^ ((θ - 1) / θ - 1) * cesInner γ θ CT CN ^ (θ * (1 - ρ) / (θ - 1) - 1)

/-- The marginal utility of nontradables for (5.72), O&R p. 324:
`u_N = (1−γ)^{1/θ}C_N^{(θ−1)/θ − 1}Z^{θ(1−ρ)/(θ−1) − 1}`. -/
noncomputable def cesMUN (γ θ ρ CT CN : ℝ) : ℝ :=
  (1 - γ) ^ (1 / θ) * CN ^ ((θ - 1) / θ - 1) * cesInner γ θ CT CN ^ (θ * (1 - ρ) / (θ - 1) - 1)

/-- The inner sum is positive at positive consumptions, O&R p. 324 (`0 < γ < 1`). -/
theorem cesInner_pos {γ θ CT CN : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hT : 0 < CT) (hN : 0 < CN) :
    0 < cesInner γ θ CT CN := by
  unfold cesInner
  have : 0 < 1 - γ := by linarith
  positivity

/-- **`u_T` is the partial derivative of (5.72) in `C_T`**, O&R p. 324 (`θ > 0`, `θ ≠ 1`,
`ρ ≠ 1`, `0 < γ < 1`, positive consumptions). -/
theorem hasDerivAt_cesCrra_T {γ θ ρ CT CN : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hθ : 0 < θ)
    (hθ1 : θ ≠ 1) (hρ1 : ρ ≠ 1) (hT : 0 < CT) (hN : 0 < CN) :
    HasDerivAt (fun c => cesCrraUtility γ θ ρ c CN) (cesMUT γ θ ρ CT CN) CT := by
  have hZ := cesInner_pos (θ := θ) hγ0 hγ1 hT hN
  have hθ1' : θ - 1 ≠ 0 := sub_ne_zero.mpr hθ1
  have h1ρ : 1 - ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm hρ1)
  have hd1 := ((Real.hasDerivAt_rpow_const (p := (θ - 1) / θ) (Or.inl hT.ne')).const_mul
    (γ ^ (1 / θ))).add_const ((1 - γ) ^ (1 / θ) * CN ^ ((θ - 1) / θ))
  have hd2 := hd1.rpow_const (p := θ / (θ - 1)) (Or.inl hZ.ne')
  have hZa : 0 < cesInner γ θ CT CN ^ (θ / (θ - 1)) := Real.rpow_pos_of_pos hZ _
  have hd3 := (hd2.rpow_const (p := 1 - ρ) (Or.inl hZa.ne')).div_const (1 - ρ)
  unfold cesCrraUtility cesInner
  convert hd3 using 1
  unfold cesMUT
  change _ = γ ^ (1 / θ) * ((θ - 1) / θ * CT ^ ((θ - 1) / θ - 1)) * (θ / (θ - 1)) *
      cesInner γ θ CT CN ^ (θ / (θ - 1) - 1) * (1 - ρ) *
      (cesInner γ θ CT CN ^ (θ / (θ - 1))) ^ (1 - ρ - 1) / (1 - ρ)
  rw [← Real.rpow_mul hZ.le]
  have hexp : θ * (1 - ρ) / (θ - 1) - 1 = (θ / (θ - 1) - 1) + θ / (θ - 1) * (1 - ρ - 1) := by
    field_simp; ring
  rw [hexp, Real.rpow_add hZ]
  field_simp

/-- **`u_N` is the partial derivative of (5.72) in `C_N`**, O&R p. 324 (same hypotheses). -/
theorem hasDerivAt_cesCrra_N {γ θ ρ CT CN : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hθ : 0 < θ)
    (hθ1 : θ ≠ 1) (hρ1 : ρ ≠ 1) (hT : 0 < CT) (hN : 0 < CN) :
    HasDerivAt (fun c => cesCrraUtility γ θ ρ CT c) (cesMUN γ θ ρ CT CN) CN := by
  have hZ := cesInner_pos (θ := θ) hγ0 hγ1 hT hN
  have hθ1' : θ - 1 ≠ 0 := sub_ne_zero.mpr hθ1
  have h1ρ : 1 - ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm hρ1)
  have hd1 := ((Real.hasDerivAt_rpow_const (p := (θ - 1) / θ) (Or.inl hN.ne')).const_mul
    ((1 - γ) ^ (1 / θ))).const_add (γ ^ (1 / θ) * CT ^ ((θ - 1) / θ))
  have hd2 := hd1.rpow_const (p := θ / (θ - 1)) (Or.inl hZ.ne')
  have hZa : 0 < cesInner γ θ CT CN ^ (θ / (θ - 1)) := Real.rpow_pos_of_pos hZ _
  have hd3 := (hd2.rpow_const (p := 1 - ρ) (Or.inl hZa.ne')).div_const (1 - ρ)
  unfold cesCrraUtility cesInner
  convert hd3 using 1
  unfold cesMUN
  change _ = (1 - γ) ^ (1 / θ) * ((θ - 1) / θ * CN ^ ((θ - 1) / θ - 1)) * (θ / (θ - 1)) *
      cesInner γ θ CT CN ^ (θ / (θ - 1) - 1) * (1 - ρ) *
      (cesInner γ θ CT CN ^ (θ / (θ - 1))) ^ (1 - ρ - 1) / (1 - ρ)
  rw [← Real.rpow_mul hZ.le]
  have hexp : θ * (1 - ρ) / (θ - 1) - 1 = (θ / (θ - 1) - 1) + θ / (θ - 1) * (1 - ρ - 1) := by
    field_simp; ring
  rw [hexp, Real.rpow_add hZ]
  field_simp

/-- The cross-partial `∂²u/∂C_N∂C_T` of (5.72), O&R p. 328, in closed form:
`((1 − θρ)/θ)·γ^{1/θ}(1−γ)^{1/θ}C_T^{(θ−1)/θ − 1}C_N^{(θ−1)/θ − 1}Z^{θ(1−ρ)/(θ−1) − 2}`. -/
noncomputable def cesCross (γ θ ρ CT CN : ℝ) : ℝ :=
  (1 - θ * ρ) / θ * (γ ^ (1 / θ) * (1 - γ) ^ (1 / θ) * CT ^ ((θ - 1) / θ - 1) *
    CN ^ ((θ - 1) / θ - 1) * cesInner γ θ CT CN ^ (θ * (1 - ρ) / (θ - 1) - 1 - 1))

/-- **The cross-partial of (5.72), O&R p. 328**: `cesCross` is the derivative of `u_T` in
`C_N` (hypotheses as in `hasDerivAt_cesCrra_T`, except that `ρ = 1` is allowed). -/
theorem hasDerivAt_cesMUT_N {γ θ ρ CT CN : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hθ : 0 < θ)
    (hθ1 : θ ≠ 1) (hT : 0 < CT) (hN : 0 < CN) :
    HasDerivAt (fun c => cesMUT γ θ ρ CT c) (cesCross γ θ ρ CT CN) CN := by
  have hZ := cesInner_pos (θ := θ) hγ0 hγ1 hT hN
  have hθ1' : θ - 1 ≠ 0 := sub_ne_zero.mpr hθ1
  have hd1 := ((Real.hasDerivAt_rpow_const (p := (θ - 1) / θ) (Or.inl hN.ne')).const_mul
    ((1 - γ) ^ (1 / θ))).const_add (γ ^ (1 / θ) * CT ^ ((θ - 1) / θ))
  have hd2 := (hd1.rpow_const (p := θ * (1 - ρ) / (θ - 1) - 1) (Or.inl hZ.ne')).const_mul
    (γ ^ (1 / θ) * CT ^ ((θ - 1) / θ - 1))
  unfold cesMUT cesInner
  convert hd2 using 1
  unfold cesCross
  change _ = γ ^ (1 / θ) * CT ^ ((θ - 1) / θ - 1) * ((1 - γ) ^ (1 / θ) *
      ((θ - 1) / θ * CN ^ ((θ - 1) / θ - 1)) * (θ * (1 - ρ) / (θ - 1) - 1) *
      cesInner γ θ CT CN ^ (θ * (1 - ρ) / (θ - 1) - 1 - 1))
  field_simp
  ring

/-- **The sign of the cross-partial, O&R p. 328**: at positive consumptions,
`∂²u/∂C_N∂C_T > 0 ↔ θρ < 1` and `∂²u/∂C_N∂C_T < 0 ↔ θρ > 1` (so when `θ > 1/ρ` a higher
nontradables endowment lowers the marginal utility of tradables). -/
theorem cesCross_sign {γ θ ρ CT CN : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hθ : 0 < θ)
    (hT : 0 < CT) (hN : 0 < CN) :
    (0 < cesCross γ θ ρ CT CN ↔ θ * ρ < 1) ∧ (cesCross γ θ ρ CT CN < 0 ↔ 1 < θ * ρ) := by
  have hZ := cesInner_pos (θ := θ) hγ0 hγ1 hT hN
  have h1γ : 0 < 1 - γ := by linarith
  have hP : 0 < γ ^ (1 / θ) * (1 - γ) ^ (1 / θ) * CT ^ ((θ - 1) / θ - 1) *
      CN ^ ((θ - 1) / θ - 1) * cesInner γ θ CT CN ^ (θ * (1 - ρ) / (θ - 1) - 1 - 1) := by
    positivity
  unfold cesCross
  set P := γ ^ (1 / θ) * (1 - γ) ^ (1 / θ) * CT ^ ((θ - 1) / θ - 1) *
      CN ^ ((θ - 1) / θ - 1) * cesInner γ θ CT CN ^ (θ * (1 - ρ) / (θ - 1) - 1 - 1) with hPdef
  have hQ : 0 < P / θ := div_pos hP hθ
  have e : (1 - θ * ρ) / θ * P = (1 - θ * ρ) * (P / θ) := by ring
  rw [e]
  constructor
  · rw [mul_pos_iff_of_pos_right hQ]
    constructor <;> intro h <;> linarith
  · rw [← neg_pos, ← neg_mul, mul_pos_iff_of_pos_right hQ]
    constructor <;> intro h <;> linarith

/-- **(5.72) is additive when `θρ = 1`, O&R p. 324**: then
`u = γ^{1/θ}C_T^{1−ρ}/(1−ρ) + (1−γ)^{1/θ}C_N^{1−ρ}/(1−ρ)`. -/
theorem cesCrra_additive_of_theta_rho {γ θ ρ CT CN : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hθ : 0 < θ) (hθ1 : θ ≠ 1) (hθρ : θ * ρ = 1) (hT : 0 < CT) (hN : 0 < CN) :
    cesCrraUtility γ θ ρ CT CN =
      γ ^ (1 / θ) * CT ^ (1 - ρ) / (1 - ρ) + (1 - γ) ^ (1 / θ) * CN ^ (1 - ρ) / (1 - ρ) := by
  have hZ := cesInner_pos (θ := θ) hγ0 hγ1 hT hN
  have hθ1' : θ - 1 ≠ 0 := sub_ne_zero.mpr hθ1
  have hρ : ρ = 1 / θ := by field_simp; linarith
  have hk : (θ - 1) / θ = 1 - ρ := by rw [hρ]; field_simp
  have ha : θ / (θ - 1) * (1 - ρ) = 1 := by rw [hρ]; field_simp
  unfold cesCrraUtility
  rw [← Real.rpow_mul hZ.le, ha, Real.rpow_one]
  unfold cesInner
  rw [hk]
  ring

/-- **Additivity forces `θρ = 1`, O&R p. 324**: if (5.72) is additively separable on the
positive orthant, `u(C_T, C_N) = f(C_T) + g(C_N)`, then `θρ = 1`. -/
theorem theta_rho_of_cesCrra_additive {γ θ ρ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hθ : 0 < θ)
    (hθ1 : θ ≠ 1) (hρ1 : ρ ≠ 1)
    (hsep : ∃ f g : ℝ → ℝ, ∀ CT CN, 0 < CT → 0 < CN → cesCrraUtility γ θ ρ CT CN = f CT + g CN) :
    θ * ρ = 1 := by
  obtain ⟨f, g, hfg⟩ := hsep
  -- `u_T(1, ·)` is constant on `(0, ∞)`
  have hf : ∀ CN, 0 < CN → HasDerivAt f (cesMUT γ θ ρ 1 CN) 1 := by
    intro CN hN
    have h := hasDerivAt_cesCrra_T hγ0 hγ1 hθ hθ1 hρ1 one_pos hN
    have hev : (fun c => f c + g CN) =ᶠ[𝓝 1] fun c => cesCrraUtility γ θ ρ c CN :=
      (eventually_gt_nhds one_pos).mono fun c hc => (hfg c CN hc hN).symm
    have h2 := (h.congr_of_eventuallyEq hev).add_const (-g CN)
    simpa using h2
  have hconst : ∀ CN, 0 < CN → cesMUT γ θ ρ 1 CN = cesMUT γ θ ρ 1 1 :=
    fun CN hN => (hf CN hN).unique (hf 1 one_pos)
  have hd := hasDerivAt_cesMUT_N (ρ := ρ) hγ0 hγ1 hθ hθ1 one_pos one_pos
  have hev : (fun _ : ℝ => cesMUT γ θ ρ 1 1) =ᶠ[𝓝 1] fun c => cesMUT γ θ ρ 1 c :=
    (eventually_gt_nhds one_pos).mono fun c hc => (hconst c hc).symm
  have h0 : cesCross γ θ ρ 1 1 = 0 :=
    (hd.congr_of_eventuallyEq hev).unique (hasDerivAt_const (1 : ℝ) (cesMUT γ θ ρ 1 1))
  have hs := cesCross_sign (ρ := ρ) hγ0 hγ1 hθ one_pos one_pos
  rw [h0] at hs
  rcases lt_trichotomy (θ * ρ) 1 with h | h | h
  · exact absurd (hs.1.mpr h) (lt_irrefl 0)
  · exact h
  · exact absurd (hs.2.mpr h) (lt_irrefl 0)

/-- **O&R p. 324: (5.72) is additively separable iff `θρ = 1`** (on the positive orthant;
`θ > 0`, `θ ≠ 1`, `ρ ≠ 1`, `0 < γ < 1`). -/
theorem cesCrra_additive_iff {γ θ ρ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hθ : 0 < θ)
    (hθ1 : θ ≠ 1) (hρ1 : ρ ≠ 1) :
    (∃ f g : ℝ → ℝ, ∀ CT CN, 0 < CT → 0 < CN → cesCrraUtility γ θ ρ CT CN = f CT + g CN) ↔
      θ * ρ = 1 :=
  ⟨theta_rho_of_cesCrra_additive hγ0 hγ1 hθ hθ1 hρ1, fun hθρ =>
    ⟨fun CT => γ ^ (1 / θ) * CT ^ (1 - ρ) / (1 - ρ),
      fun CN => (1 - γ) ^ (1 / θ) * CN ^ (1 - ρ) / (1 - ρ),
      fun _ _ hT hN => cesCrra_additive_of_theta_rho hγ0 hγ1 hθ hθ1 hθρ hT hN⟩⟩

/-- **The relative price of nontradables under (5.72), O&R (5.64), p. 320**:
`p_N = u_N/u_T = (1−γ)^{1/θ}C_N^{(θ−1)/θ − 1}/(γ^{1/θ}C_T^{(θ−1)/θ − 1})`. -/
theorem ces_relative_price {γ θ ρ CT CN : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hT : 0 < CT)
    (hN : 0 < CN) :
    cesMUN γ θ ρ CT CN / cesMUT γ θ ρ CT CN =
      (1 - γ) ^ (1 / θ) * CN ^ ((θ - 1) / θ - 1) / (γ ^ (1 / θ) * CT ^ ((θ - 1) / θ - 1)) := by
  have hZ := cesInner_pos (θ := θ) hγ0 hγ1 hT hN
  unfold cesMUN cesMUT
  have : 0 < cesInner γ θ CT CN ^ (θ * (1 - ρ) / (θ - 1) - 1) := Real.rpow_pos_of_pos hZ _
  have : 0 < γ ^ (1 / θ) := Real.rpow_pos_of_pos hγ0 _
  have : 0 < CT ^ ((θ - 1) / θ - 1) := Real.rpow_pos_of_pos hT _
  field_simp

/-- **Nontradables revenue, O&R p. 328**: under (5.72) with `C_N = Y_N` and `C_T` held fixed,
`p_N Y_N = (1−γ)^{1/θ}Y_N^{(θ−1)/θ}/(γ^{1/θ}C_T^{(θ−1)/θ − 1})`, which is strictly increasing
in `Y_N > 0` if and only if `θ > 1` (`θ > 0`). -/
theorem ces_revenue_strictMono_iff {γ θ ρ CT : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hθ : 0 < θ)
    (hT : 0 < CT) :
    StrictMonoOn (fun Y => cesMUN γ θ ρ CT Y / cesMUT γ θ ρ CT Y * Y) (Set.Ioi 0) ↔ 1 < θ := by
  set c := (1 - γ) ^ (1 / θ) / (γ ^ (1 / θ) * CT ^ ((θ - 1) / θ - 1)) with hc
  have h1γ : 0 < 1 - γ := by linarith
  have hcpos : 0 < c := by positivity
  have hform : ∀ Y, 0 < Y → cesMUN γ θ ρ CT Y / cesMUT γ θ ρ CT Y * Y = c * Y ^ ((θ - 1) / θ) := by
    intro Y hY
    rw [ces_relative_price hγ0 hγ1 hT hY, Real.rpow_sub_one hY.ne', hc]
    field_simp
  constructor
  · intro hmono
    by_contra hle
    push Not at hle
    have hk : (θ - 1) / θ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hθ.le
    have h12 := hmono (Set.mem_Ioi.mpr one_pos) (Set.mem_Ioi.mpr two_pos) one_lt_two
    simp only at h12
    rw [hform 1 one_pos, hform 2 two_pos] at h12
    have := Real.rpow_le_rpow_of_nonpos one_pos one_le_two hk
    nlinarith
  · intro hθ1'
    have hk : 0 < (θ - 1) / θ := div_pos (by linarith) hθ
    intro x hx y hy hxy
    simp only
    rw [hform x hx, hform y hy]
    exact mul_lt_mul_of_pos_left (Real.rpow_lt_rpow (le_of_lt hx) hxy hk) hcpos

/-- **The log-linearised equation (5.73) as an exact identity, O&R p. 324**: along any path
`t ↦ (C_T(t), Y_N(t), λ(t))` of positive values differentiable at `t₀` on which the
efficiency condition `u_T(C_T, Y_N) = λ` holds identically, the logarithmic derivatives
(`x̂ = x′/x`) satisfy
`Ĉ_T = [−θλ̂ + (1−φ)(1−θρ)Ŷ_N]/[1 − φ(1−θρ)]`, with
`φ = γ^{1/θ}C_T^{(θ−1)/θ}/Z ∈ (0, 1)`; the denominator is positive. (Hypotheses: `θ > 0`,
`θ ≠ 1`, `ρ > 0`, `0 < γ < 1`.) -/
theorem ces_loglinear_exact {γ θ ρ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hθ : 0 < θ)
    (hθ1 : θ ≠ 1) (hρ : 0 < ρ) (c y l : ℝ → ℝ) {c' y' l' t₀ : ℝ} (hc0 : ∀ t, 0 < c t)
    (hy0 : ∀ t, 0 < y t) (hpath : ∀ t, cesMUT γ θ ρ (c t) (y t) = l t)
    (hc : HasDerivAt c c' t₀) (hy : HasDerivAt y y' t₀) (hl : HasDerivAt l l' t₀) :
    0 < 1 - γ ^ (1 / θ) * c t₀ ^ ((θ - 1) / θ) / cesInner γ θ (c t₀) (y t₀) *
        (1 - θ * ρ) ∧
      c' / c t₀ = (-θ * (l' / l t₀) + (1 - γ ^ (1 / θ) * c t₀ ^ ((θ - 1) / θ) /
          cesInner γ θ (c t₀) (y t₀)) * (1 - θ * ρ) * (y' / y t₀)) /
        (1 - γ ^ (1 / θ) * c t₀ ^ ((θ - 1) / θ) / cesInner γ θ (c t₀) (y t₀) * (1 - θ * ρ)) := by
  have hθ1' : θ - 1 ≠ 0 := sub_ne_zero.mpr hθ1
  have h1γ : 0 < 1 - γ := by linarith
  have hZ := cesInner_pos (θ := θ) hγ0 hγ1 (hc0 t₀) (hy0 t₀)
  have hA : 0 < γ ^ (1 / θ) := Real.rpow_pos_of_pos hγ0 _
  have hB : 0 < (1 - γ) ^ (1 / θ) := Real.rpow_pos_of_pos h1γ _
  have hX : 0 < c t₀ ^ ((θ - 1) / θ) := Real.rpow_pos_of_pos (hc0 t₀) _
  have hYk : 0 < y t₀ ^ ((θ - 1) / θ) := Real.rpow_pos_of_pos (hy0 t₀) _
  -- the share `φ` lies in `(0, 1)`
  have hφ0 : 0 < γ ^ (1 / θ) * c t₀ ^ ((θ - 1) / θ) / cesInner γ θ (c t₀) (y t₀) := by
    positivity
  have hφ1 : γ ^ (1 / θ) * c t₀ ^ ((θ - 1) / θ) / cesInner γ θ (c t₀) (y t₀) < 1 := by
    rw [div_lt_one hZ]; unfold cesInner; nlinarith [mul_pos hB hYk]
  have hden : 0 < 1 - γ ^ (1 / θ) * c t₀ ^ ((θ - 1) / θ) / cesInner γ θ (c t₀) (y t₀) *
      (1 - θ * ρ) := by
    nlinarith [mul_pos hφ0 (mul_pos hθ hρ)]
  refine ⟨hden, ?_⟩
  -- differentiate `u_T(c(t), y(t))`
  have hZd := ((hc.rpow_const (p := (θ - 1) / θ) (Or.inl (hc0 t₀).ne')).const_mul
    (γ ^ (1 / θ))).add ((hy.rpow_const (p := (θ - 1) / θ) (Or.inl (hy0 t₀).ne')).const_mul
    ((1 - γ) ^ (1 / θ)))
  have hMd := ((hc.rpow_const (p := (θ - 1) / θ - 1) (Or.inl (hc0 t₀).ne')).const_mul
    (γ ^ (1 / θ))).mul (hZd.rpow_const (p := θ * (1 - ρ) / (θ - 1) - 1) (Or.inl hZ.ne'))
  have hMd' := hMd.congr_of_eventuallyEq (f₁ := l) (Filter.Eventually.of_forall fun t => by
    rw [← hpath t]; rfl)
  have hl' := hl.unique hMd'
  have hlt : l t₀ = cesMUT γ θ ρ (c t₀) (y t₀) := (hpath t₀).symm
  rw [hl', hlt, eq_div_iff hden.ne']
  unfold cesMUT
  unfold cesInner at hZ ⊢
  simp only [Pi.add_apply, Real.rpow_sub_one (hc0 t₀).ne', Real.rpow_sub_one (hy0 t₀).ne',
    Real.rpow_sub_one hZ.ne']
  have hc0' := hc0 t₀
  have hy0' := hy0 t₀
  have hW : 0 < (γ ^ (1 / θ) * c t₀ ^ ((θ - 1) / θ) + (1 - γ) ^ (1 / θ) * y t₀ ^ ((θ - 1) / θ)) ^
      (θ * (1 - ρ) / (θ - 1)) := Real.rpow_pos_of_pos hZ _
  generalize c t₀ ^ ((θ - 1) / θ) = X at *
  generalize y t₀ ^ ((θ - 1) / θ) = Yk at *
  generalize (γ ^ (1 / θ) * X + (1 - γ) ^ (1 / θ) * Yk) ^ (θ * (1 - ρ) / (θ - 1)) = W at *
  generalize γ ^ (1 / θ) = A at *
  generalize (1 - γ) ^ (1 / θ) = B at *
  field_simp
  ring

/-! ## Log Cobb–Douglas utility (p. 328–329) -/

/-- The relative price of nontradables under `u = γ log C_T + (1−γ) log C_N`, O&R p. 328:
`p_N = u_N/u_T = ((1−γ)/C_N)/(γ/C_T)`. -/
noncomputable def cdRelPrice (γ CT CN : ℝ) : ℝ := ((1 - γ) / CN) / (γ / CT)

/-- **The Cobb–Douglas marginal utilities, O&R p. 328**: `∂u/∂C_T = γ/C_T` and
`∂u/∂C_N = (1−γ)/C_N` at positive consumptions, so `p_N = cdRelPrice`. -/
theorem cd_marginal_utilities {γ CT CN : ℝ} (hT : 0 < CT) (hN : 0 < CN) :
    HasDerivAt (fun c => γ * Real.log c + (1 - γ) * Real.log CN) (γ / CT) CT ∧
      HasDerivAt (fun c => γ * Real.log CT + (1 - γ) * Real.log c) ((1 - γ) / CN) CN := by
  constructor
  · have h := ((Real.hasDerivAt_log hT.ne').const_mul γ).add_const ((1 - γ) * Real.log CN)
    convert h using 1
    field_simp
  · have h := ((Real.hasDerivAt_log hN.ne').const_mul (1 - γ)).const_add (γ * Real.log CT)
    convert h using 1
    field_simp

/-- **Cobb–Douglas nontradables revenue, O&R p. 328–329**: with `C_N = Y_N`,
`p_N Y_N = ((1−γ)/γ)C_T`, independent of `Y_N`. -/
theorem cd_revenue {γ CT YN : ℝ} (hγ : γ ≠ 0) (hT : CT ≠ 0) (hN : YN ≠ 0) :
    cdRelPrice γ CT YN * YN = (1 - γ) / γ * CT := by
  unfold cdRelPrice
  field_simp

/-- **Portfolio indeterminacy, O&R p. 329**: under log Cobb–Douglas utility, if a country's
tradables consumption is a share `μ > 0` of world tradables output `Y_T^W` in every state,
the payoff `p_N Y_N` of its nontradables claim is perfectly correlated with `Y_T^W`
(`Corr = 1`, given `Var(Y_T^W) > 0`), so it is a perfect substitute for the world tradables
portfolio. -/
theorem cd_payoff_corr_one [Fintype S] (Ω : StateSpace S) (YW CT YN : S → ℝ) {γ μ : ℝ} (hγ0 : 0 < γ)
    (hγ1 : γ < 1) (hμ : 0 < μ) (hYN : ∀ s, YN s ≠ 0) (hCT : ∀ s, CT s = μ * YW s)
    (hYW : ∀ s, YW s ≠ 0) (hvar : 0 < Ω.var YW) :
    Ω.corr YW (fun s => cdRelPrice γ (CT s) (YN s) * YN s) = 1 := by
  have e : (fun s => cdRelPrice γ (CT s) (YN s) * YN s) =
      fun s => 0 + ((1 - γ) / γ * μ) * YW s := by
    funext s
    rw [cd_revenue hγ0.ne' (by rw [hCT]; exact mul_ne_zero hμ.ne' (hYW s)) (hYN s), hCT]
    ring
  rw [e]
  have hb : 0 < (1 - γ) / γ * μ := by
    have : 0 < 1 - γ := by linarith
    positivity
  exact Ω.corr_affine hb hvar

end ObstfeldRogoff.InternationalFinancialMarkets.Nontradables

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Event trees, many-period Arrow–Debreu markets and dynamic consistency

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*,
Appendix 5C (pp. 341–343), Appendix 5D (pp. 343–344) and Supplement A to Chapter 5
(pp. 742–744).

**Histories.** One event from a finite set `S` is revealed at each date after date 1. The
date-1 history `h₁` is fixed; a date-`t` history (a continuation of `h₁` through date `t`)
is the list of the `n = t − 1` later events, `h : Fin n → S`. The one-step conditional
probability of event `s` after a history `g` of `k` events is `q k g s`; the conditional
probability `π(h_t | h_1)` is the product of the one-step probabilities along the history
(`histProb`), and `π(h_t | h_m)` is the product over the steps after date `m`
(`condProb`). We prove that the probabilities of all date-`t` histories sum to one and
Bayes' rule, O&R footnote 53.

**Appendix 5C.** A finite horizon `T` replaces the book's infinite horizon: the dates after 1
are `t = n + 1`, `n ∈ [1, T)`. We derive the noncontingent-bond Euler equation (85) and the
analogue of (9) from the first-order conditions (84), prove that (84) plus the budget
constraint (83) give a global optimum when `u` is concave (supporting-line inequality),
verify the CRRA equilibrium `C(h_t) = μ Y^W(h_t)` with its prices and long-term interest
factor `R_{1,t}`, and conversely derive the constant shares from the first-order conditions
and market clearing.

**Appendix 5D.** Prices in date-1 units `p̃ = p R`; from (86) the date-1 plan satisfies
(88), which by Bayes' rule and the no-arbitrage identity `p̃(h_t|h_1)/p̃(h_2|h_1) = p̃(h_t|h_2)`
(taken as a hypothesis, as in the book's arbitrage argument) is (87); the old plan is
therefore optimal for the date-2 problem with ongoing trade (dynamic consistency).

**Supplement A.** Log utility gives the consumption share `μ = 1 − β`; the CRRA share
recursion `μ_t = (1 + [βE{(1+r°)^{1−ρ} μ_{t+1}^{−ρ}}]^{1/ρ})^{−1}` is equivalent to the
consumption Euler equation, and its i.i.d. fixed point is `μ = 1 − [βE(1+r°)^{1−ρ}]^{1/ρ}`.
-/

namespace ObstfeldRogoff.InternationalFinancialMarkets.EventTree

open Finset

/-- An event tree (O&R Appendix 5C, p. 341): after a history of `k` events `g : Fin k → S`,
the next event is `s` with conditional probability `q k g s`. -/
structure Tree (S : Type) [Fintype S] where
  q : (k : ℕ) → (Fin k → S) → S → ℝ
  q_nonneg : ∀ k g s, 0 ≤ q k g s
  q_sum : ∀ k g, ∑ s, q k g s = 1

variable {S : Type} [Fintype S]

/-- The restriction of a history `h` of `n` events to its first `k ≤ n` events, i.e. the
history through the earlier date `k + 1` (O&R Appendix 5C, p. 341). -/
def restr {n : ℕ} (h : Fin n → S) (k : ℕ) (hk : k ≤ n) : Fin k → S :=
  fun j => h ⟨j, lt_of_lt_of_le j.2 hk⟩

namespace Tree

variable (tr : Tree S)

/-- The one-step conditional probability `π(h_{i+2} | h_{i+1})` of the `i`-th event of the
history `h` given the events before it (O&R Appendix 5C, p. 341); `1` beyond the history. -/
noncomputable def step {n : ℕ} (h : Fin n → S) (i : ℕ) : ℝ :=
  if hi : i < n then tr.q i (restr h i hi.le) (h ⟨i, hi⟩) else 1

/-- The conditional probability `π(h_{n+1} | h_{m+1})` of the history `h` (of `n` events)
given its first `m` events: the product of the one-step probabilities after step `m`
(O&R Appendix 5C, p. 341, and footnote 53, p. 344). -/
noncomputable def condProb {n : ℕ} (h : Fin n → S) (m : ℕ) : ℝ :=
  ∏ i ∈ Ico m n, tr.step h i

/-- The probability `π(h_t | h_1)` of the date-`t` history `h`, `t = n + 1`
(O&R Appendix 5C, p. 341). -/
noncomputable def histProb {n : ℕ} (h : Fin n → S) : ℝ :=
  tr.condProb h 0

/-- One-step probabilities are nonnegative (O&R Appendix 5C, p. 341). -/
theorem step_nonneg {n : ℕ} (h : Fin n → S) (i : ℕ) : 0 ≤ tr.step h i := by
  unfold step
  split_ifs
  · exact tr.q_nonneg _ _ _
  · exact zero_le_one

/-- History probabilities are nonnegative (O&R Appendix 5C, p. 341). -/
theorem histProb_nonneg {n : ℕ} (h : Fin n → S) : 0 ≤ tr.histProb h :=
  by unfold histProb condProb; exact Finset.prod_nonneg fun i _ => tr.step_nonneg h i

/-- Appending an event does not change the earlier one-step probabilities. -/
theorem step_snoc_lt {n : ℕ} (h : Fin n → S) (s : S) {i : ℕ} (hi : i < n) :
    tr.step (Fin.snoc h s : Fin (n + 1) → S) i = tr.step h i := by
  have hi' : i < n + 1 := by omega
  simp only [step, hi, hi', dite_true]
  have h1 : (Fin.snoc h s : Fin (n + 1) → S) ⟨i, hi'⟩ = h ⟨i, hi⟩ := by
    simp [Fin.snoc, hi]
  have h2 : restr (Fin.snoc h s : Fin (n + 1) → S) i hi'.le = restr h i hi.le := by
    funext j
    have hj : (j : ℕ) < n := by omega
    simp [restr, Fin.snoc, hj]
  rw [h1, h2]

/-- The last one-step probability of `snoc h s` is `q n h s`. -/
theorem step_snoc_last {n : ℕ} (h : Fin n → S) (s : S) :
    tr.step (Fin.snoc h s : Fin (n + 1) → S) n = tr.q n h s := by
  have hn : n < n + 1 := by omega
  simp only [step, hn, dite_true]
  have h1 : (Fin.snoc h s : Fin (n + 1) → S) ⟨n, hn⟩ = s := by
    simp [Fin.snoc]
  have h2 : restr (Fin.snoc h s : Fin (n + 1) → S) n hn.le = h := by
    funext j
    have hj : (j : ℕ) < n := j.2
    simp [restr, Fin.snoc, hj]
  rw [h1, h2]

/-- The probabilities of all date-`t` histories sum to one, `Σ_{h_t} π(h_t | h_1) = 1`
(O&R Appendix 5C, p. 341; used for (85), p. 342). -/
theorem histProb_sum_eq_one (n : ℕ) : ∑ h : Fin n → S, tr.histProb h = 1 := by
  induction n with
  | zero => simp [histProb, condProb]
  | succ n ih =>
    rw [← (Fin.snocEquiv (fun _ : Fin (n + 1) => S)).sum_comp]
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    have key : ∀ (g : Fin n → S) (s : S),
        tr.histProb (Fin.snoc g s : Fin (n + 1) → S) = tr.histProb g * tr.q n g s := by
      intro g s
      simp only [histProb, condProb, Nat.Ico_zero_eq_range]
      rw [Finset.prod_range_succ, tr.step_snoc_last]
      congr 1
      exact Finset.prod_congr rfl fun i hi => tr.step_snoc_lt g s (Finset.mem_range.mp hi)
    have e : ∀ (g : Fin n → S) (s : S),
        (Fin.snocEquiv fun _ : Fin (n + 1) => S) (s, g) = Fin.snoc g s := fun _ _ => rfl
    simp only [e, key, ← Finset.mul_sum, tr.q_sum, mul_one]
    exact ih

/-- Restricting a history to an earlier date leaves the earlier one-step probabilities
unchanged (O&R Appendix 5C, p. 341). -/
theorem step_restr {n k : ℕ} (h : Fin n → S) (hk : k ≤ n) {i : ℕ} (hi : i < k) :
    tr.step (restr h k hk) i = tr.step h i := by
  have hin : i < n := lt_of_lt_of_le hi hk
  simp only [step, hi, hin, dite_true]
  rfl

/-- The chain rule for conditional probabilities along a history,
`π(h_n | h_m) = π(h_k | h_m) π(h_n | h_k)` for `m ≤ k ≤ n` (O&R footnote 53, p. 344). -/
theorem condProb_chain {n : ℕ} (h : Fin n → S) {m k : ℕ} (hmk : m ≤ k) (hk : k ≤ n) :
    tr.condProb h m = tr.condProb (restr h k hk) m * tr.condProb h k := by
  have e : tr.condProb (restr h k hk) m = ∏ i ∈ Ico m k, tr.step h i :=
    Finset.prod_congr rfl fun i hi => tr.step_restr h hk (Finset.mem_Ico.mp hi).2
  rw [e]
  exact (Finset.prod_Ico_consecutive _ hmk hk).symm

/-- Bayes' rule, O&R footnote 53, p. 344: for a history `h` continuing `h_{t+1}` (its first
`t + 1` events), `π(h | h_{t+1}) = π(h | h_t)/π(h_{t+1} | h_t)` whenever
`π(h_{t+1} | h_t) ≠ 0`. -/
theorem bayes_rule {n : ℕ} (h : Fin n → S) {t : ℕ} (ht : t + 1 ≤ n)
    (hpos : tr.condProb (restr h (t + 1) ht) t ≠ 0) :
    tr.condProb h (t + 1) = tr.condProb h t / tr.condProb (restr h (t + 1) ht) t := by
  rw [eq_div_iff hpos, tr.condProb_chain h (Nat.le_succ t) ht, mul_comm]

/-- The date-2 form of Bayes' rule used in Appendix 5D, O&R p. 344:
`π(h_t | h_1)/π(h_2 | h_1) = π(h_t | h_2)`, where `h_2` is the first event of `h_t`. -/
theorem histProb_div_date2 {n : ℕ} (h : Fin n → S) (hn : 1 ≤ n)
    (hpos : tr.histProb (restr h 1 hn) ≠ 0) :
    tr.histProb h / tr.histProb (restr h 1 hn) = tr.condProb h 1 := by
  rw [div_eq_iff hpos, histProb, histProb, tr.condProb_chain h (Nat.zero_le 1) hn, mul_comm]

/-- The date-2 probability `π(h_2 | h_1)` of the first event of `h` is its first one-step
probability (O&R Appendix 5D, p. 344). -/
theorem histProb_restr_one {n : ℕ} (h : Fin n → S) (hn : 1 ≤ n) :
    tr.histProb (restr h 1 hn) = tr.step h 0 := by
  have e : tr.histProb (restr h 1 hn) = tr.step (restr h 1 hn) 0 := by
    simp [histProb, condProb]
  rw [e, tr.step_restr h hn Nat.zero_lt_one]

/-- Conditional probabilities are nonnegative (O&R Appendix 5C, p. 341). -/
theorem condProb_nonneg {n : ℕ} (h : Fin n → S) (m : ℕ) : 0 ≤ tr.condProb h m :=
  Finset.prod_nonneg fun i _ => tr.step_nonneg h i

end Tree

/-! ## Appendix 5C: individual optimality -/

/-- The supporting-line (tangent) inequality for log utility,
`log y ≤ log x + (1/x)(y − x)` for `x, y > 0`: log is concave (used for O&R Appendix 5C and
Supplement A). -/
theorem log_tangent {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Real.log y ≤ Real.log x + 1 / x * (y - x) := by
  have h := Real.log_le_sub_one_of_pos (div_pos hy hx)
  rw [Real.log_div hy.ne' hx.ne'] at h
  have e : y / x - 1 = 1 / x * (y - x) := by field_simp
  linarith

/-- Sufficiency of the first-order conditions under concavity (O&R Appendix 5C, p. 342, and
Appendix 5D, p. 344). Consider nodes `h ∈ A n` for `n ∈ N`, with nonnegative utility weights
`w` and prices `q` of contingent consumption in units of current consumption. If `u` lies
below its tangent lines with slope `du` (concavity), `du(c₀) ≥ 0`, the plan `(c₀, c)`
satisfies the first-order conditions `q(h) u′(c₀) = w(h) u′(c(h))`, and the plan
`(c₀′, c′)` costs no more, then `(c₀′, c′)` gives no more utility. -/
theorem foc_plan_optimal {H : ℕ → Type} (N : Finset ℕ) (A : (n : ℕ) → Finset (H n))
    (u du : ℝ → ℝ) (htan : ∀ x y, 0 < x → 0 < y → u y ≤ u x + du x * (y - x))
    (w q : (n : ℕ) → H n → ℝ) (hw : ∀ n ∈ N, ∀ h ∈ A n, 0 ≤ w n h)
    {c₀ c₀' : ℝ} {c c' : (n : ℕ) → H n → ℝ} (hc₀ : 0 < c₀) (hc₀' : 0 < c₀')
    (hc : ∀ n ∈ N, ∀ h ∈ A n, 0 < c n h) (hc' : ∀ n ∈ N, ∀ h ∈ A n, 0 < c' n h)
    (hdu : 0 ≤ du c₀)
    (hfoc : ∀ n ∈ N, ∀ h ∈ A n, q n h * du c₀ = w n h * du (c n h))
    (hbud : c₀' + ∑ n ∈ N, ∑ h ∈ A n, q n h * c' n h
      ≤ c₀ + ∑ n ∈ N, ∑ h ∈ A n, q n h * c n h) :
    u c₀' + ∑ n ∈ N, ∑ h ∈ A n, w n h * u (c' n h)
      ≤ u c₀ + ∑ n ∈ N, ∑ h ∈ A n, w n h * u (c n h) := by
  have key : ∀ n ∈ N, ∀ h ∈ A n, w n h * u (c' n h)
      ≤ w n h * u (c n h) + du c₀ * (q n h * c' n h - q n h * c n h) := by
    intro n hn h hh
    have t := htan _ _ (hc n hn h hh) (hc' n hn h hh)
    have t2 := mul_le_mul_of_nonneg_left t (hw n hn h hh)
    have e : du c₀ * (q n h * c' n h - q n h * c n h)
        = w n h * du (c n h) * (c' n h - c n h) := by
      rw [← hfoc n hn h hh]; ring
    rw [e]; nlinarith
  have hsum : ∑ n ∈ N, ∑ h ∈ A n, w n h * u (c' n h)
      ≤ ∑ n ∈ N, ∑ h ∈ A n, w n h * u (c n h)
        + du c₀ * (∑ n ∈ N, ∑ h ∈ A n, q n h * c' n h
          - ∑ n ∈ N, ∑ h ∈ A n, q n h * c n h) := by
    rw [mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun n hn => ?_
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun h hh => ?_
    have := key n hn h hh
    linarith
  have t0 := htan _ _ hc₀ hc₀'
  have hgap : du c₀ * (c₀' - c₀ + (∑ n ∈ N, ∑ h ∈ A n, q n h * c' n h
      - ∑ n ∈ N, ∑ h ∈ A n, q n h * c n h)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hdu (by linarith)
  nlinarith

/-- The many-period Arrow–Debreu problem, O&R (82)–(84), pp. 341–342, over a finite horizon
`T` (dates `t = n + 1 ≤ T`): if the plan `(C₁, C)` satisfies the first-order conditions (84)
`R_{1,t} p(h_t|h_1) u′(C₁) = π(h_t|h_1) β^{t−1} u′(C(h_t))` and `u` is concave with
`u′(C₁) ≥ 0`, then every positive plan satisfying the budget constraint (83) (at no greater
cost) gives no more expected utility (82). -/
theorem arrowDebreu_plan_optimal (tr : Tree S) (T : ℕ) (u du : ℝ → ℝ)
    (htan : ∀ x y, 0 < x → 0 < y → u y ≤ u x + du x * (y - x)) {β : ℝ} (hβ : 0 ≤ β)
    (R : ℕ → ℝ) (p : (n : ℕ) → (Fin n → S) → ℝ)
    {C₁ C₁' : ℝ} {C C' : (n : ℕ) → (Fin n → S) → ℝ} (hC₁ : 0 < C₁) (hC₁' : 0 < C₁')
    (hC : ∀ n h, 0 < C n h) (hC' : ∀ n h, 0 < C' n h) (hdu : 0 ≤ du C₁)
    (hfoc : ∀ n ∈ Ico 1 T, ∀ h, R n * p n h * du C₁ = tr.histProb h * β ^ n * du (C n h))
    (hbud : C₁' + ∑ n ∈ Ico 1 T, R n * ∑ h, p n h * C' n h
      ≤ C₁ + ∑ n ∈ Ico 1 T, R n * ∑ h, p n h * C n h) :
    u C₁' + ∑ n ∈ Ico 1 T, β ^ n * ∑ h, tr.histProb h * u (C' n h)
      ≤ u C₁ + ∑ n ∈ Ico 1 T, β ^ n * ∑ h, tr.histProb h * u (C n h) := by
  simp only [Finset.mul_sum, ← mul_assoc] at hbud ⊢
  exact foc_plan_optimal (Ico 1 T) (fun _ => Finset.univ) u du htan
    (fun n h => β ^ n * tr.histProb h) (fun n h => R n * p n h)
    (fun n _ h _ => mul_nonneg (pow_nonneg hβ n) (tr.histProb_nonneg h)) hC₁ hC₁'
    (fun n _ h _ => hC n h) (fun n _ h _ => hC' n h) hdu
    (fun n hn h _ => by rw [hfoc n hn h]; ring) hbud

/-- The noncontingent-bond Euler equation, O&R (85), p. 342: summing the first-order
conditions (84) over date-`t` histories and using `Σ_{h_t} p(h_t|h_1) = 1` gives
`u′(C₁) = (β^{t−1}/R_{1,t}) Σ_{h_t} π(h_t|h_1) u′(C(h_t))`. -/
theorem euler_bond (tr : Tree S) (du : ℝ → ℝ) (β : ℝ) (n : ℕ) {R C₁ : ℝ}
    {p C : (Fin n → S) → ℝ} (hR : R ≠ 0) (hp : ∑ h, p h = 1)
    (hfoc : ∀ h, R * p h * du C₁ = tr.histProb h * β ^ n * du (C h)) :
    du C₁ = β ^ n / R * ∑ h, tr.histProb h * du (C h) := by
  have hs : ∑ h, R * p h * du C₁ = ∑ h, tr.histProb h * β ^ n * du (C h) :=
    Finset.sum_congr rfl fun h _ => hfoc h
  rw [← Finset.sum_mul, ← Finset.mul_sum, hp] at hs
  have e : ∑ h, tr.histProb h * β ^ n * du (C h) = β ^ n * ∑ h, tr.histProb h * du (C h) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun h _ => by ring
  rw [e] at hs
  field_simp
  linarith

/-- The analogue of O&R (9) in Appendix 5C, p. 342: for two date-`t` histories,
`π(h¹)u′(C(h¹))/(π(h²)u′(C(h²))) = p(h¹|h_1)/p(h²|h_1)`, from the first-order conditions (84)
(given `R_{1,t}, u′(C₁), β, p(h²|h_1) ≠ 0`). -/
theorem foc_ratio (tr : Tree S) (du : ℝ → ℝ) (n : ℕ) {β R C₁ : ℝ}
    {p C : (Fin n → S) → ℝ} (hR : R ≠ 0) (hduC : du C₁ ≠ 0) (hβ : β ≠ 0)
    (hfoc : ∀ h, R * p h * du C₁ = tr.histProb h * β ^ n * du (C h))
    (h₁ h₂ : Fin n → S) (hp₂ : p h₂ ≠ 0) :
    tr.histProb h₁ * du (C h₁) / (tr.histProb h₂ * du (C h₂)) = p h₁ / p h₂ := by
  have hb : β ^ n ≠ 0 := pow_ne_zero n hβ
  have e : ∀ h, tr.histProb h * du (C h) = R * p h * du C₁ / β ^ n := by
    intro h
    rw [eq_div_iff hb]
    linarith [hfoc h]
  rw [e h₁, e h₂]
  field_simp

/-! ## Appendix 5C.3: the CRRA equilibrium -/

/-- The normalising sum `Σ_{h_t} π(h_t|h_1) Y^W(h_t)^{−ρ}` (O&R Appendix 5C.3, p. 342). -/
noncomputable def crraMass (tr : Tree S) (ρ : ℝ) (n : ℕ) (Y : (Fin n → S) → ℝ) : ℝ :=
  ∑ h, tr.histProb h * Y h ^ (-ρ)

/-- The equilibrium long-term interest factor, O&R Appendix 5C.3, p. 342:
`R_{1,t} = β^{t−1} Σ_{h_t} π(h_t|h_1) Y^W(h_t)^{−ρ} / (Y^W_1)^{−ρ}`. -/
noncomputable def crraR (tr : Tree S) (β ρ Y₁ : ℝ) (n : ℕ) (Y : (Fin n → S) → ℝ) : ℝ :=
  β ^ n * crraMass tr ρ n Y / Y₁ ^ (-ρ)

/-- The equilibrium history-contingent prices (left as an exercise in O&R Appendix 5C.3,
p. 342): `p(h_t|h_1) = π(h_t|h_1) Y^W(h_t)^{−ρ} / Σ_{h'} π(h'|h_1) Y^W(h')^{−ρ}`. -/
noncomputable def crraPrice (tr : Tree S) (ρ : ℝ) (n : ℕ) (Y : (Fin n → S) → ℝ)
    (h : Fin n → S) : ℝ :=
  tr.histProb h * Y h ^ (-ρ) / crraMass tr ρ n Y

/-- The normalising sum is positive when world output is positive (O&R Appendix 5C.3). -/
theorem crraMass_pos (tr : Tree S) (ρ : ℝ) (n : ℕ) {Y : (Fin n → S) → ℝ}
    (hY : ∀ h, 0 < Y h) : 0 < crraMass tr ρ n Y := by
  have hlt : ∑ _h : Fin n → S, (0 : ℝ) < ∑ h : Fin n → S, tr.histProb h := by
    rw [tr.histProb_sum_eq_one]; simp
  obtain ⟨h₀, -, hh₀⟩ := Finset.exists_lt_of_sum_lt hlt
  exact Finset.sum_pos' (fun h _ => mul_nonneg (tr.histProb_nonneg h)
    (Real.rpow_nonneg (hY h).le _)) ⟨h₀, Finset.mem_univ _,
      mul_pos hh₀ (Real.rpow_pos_of_pos (hY h₀) _)⟩

/-- The CRRA equilibrium prices of date-`t` Arrow–Debreu securities sum to one, the
no-arbitrage condition `Σ_{h_t} p(h_t|h_1) = 1` of O&R Appendix 5C, p. 342. -/
theorem crraPrice_sum (tr : Tree S) (ρ : ℝ) (n : ℕ) {Y : (Fin n → S) → ℝ}
    (hY : ∀ h, 0 < Y h) : ∑ h, crraPrice tr ρ n Y h = 1 := by
  simp only [crraPrice, ← Finset.sum_div]
  exact div_self (crraMass_pos tr ρ n hY).ne'

/-- The CRRA equilibrium of O&R Appendix 5C.3, p. 342: at the prices `crraR`, `crraPrice`
the constant-share plan `C₁ = μY^W_1`, `C(h_t) = μY^W(h_t)` satisfies the first-order
conditions (84) with `u′(C) = C^{−ρ}`, for every country share `μ > 0`. -/
theorem crra_foc (tr : Tree S) (β ρ : ℝ) (n : ℕ) {μ Y₁ : ℝ} {Y : (Fin n → S) → ℝ}
    (hμ : 0 < μ) (hY₁ : 0 < Y₁) (hY : ∀ h, 0 < Y h) (h : Fin n → S) :
    crraR tr β ρ Y₁ n Y * crraPrice tr ρ n Y h * (μ * Y₁) ^ (-ρ)
      = tr.histProb h * β ^ n * (μ * Y h) ^ (-ρ) := by
  have hD := (crraMass_pos tr ρ n hY).ne'
  have hY₁' : Y₁ ^ (-ρ) ≠ 0 := (Real.rpow_pos_of_pos hY₁ _).ne'
  simp only [crraR, crraPrice]
  rw [Real.mul_rpow hμ.le hY₁.le, Real.mul_rpow hμ.le (hY h).le]
  field_simp

/-- Present value at date 1 of a history-contingent stream `x`, in date-1 output
(O&R (83), p. 341): `x₁ + Σ_t R_{1,t} Σ_{h_t} p(h_t|h_1) x(h_t)`. -/
noncomputable def presentValue (T : ℕ) (R : ℕ → ℝ) (p : (n : ℕ) → (Fin n → S) → ℝ)
    (x₁ : ℝ) (x : (n : ℕ) → (Fin n → S) → ℝ) : ℝ :=
  x₁ + ∑ n ∈ Ico 1 T, R n * ∑ h, p n h * x n h

/-- The budget constraint (83) at the constant-share plan, O&R Appendix 5C.3, p. 342: at any
prices, if `μ` is country `n`'s share of the date-1 present value of world output, the plan
`C = μY^W` exactly exhausts country `n`'s present value of endowments. -/
theorem budget_of_share (T : ℕ) (R : ℕ → ℝ) (p : (n : ℕ) → (Fin n → S) → ℝ)
    {Yw₁ Yi₁ : ℝ} {Yw Yi : (n : ℕ) → (Fin n → S) → ℝ}
    (hW : presentValue T R p Yw₁ Yw ≠ 0) :
    presentValue T R p (presentValue T R p Yi₁ Yi / presentValue T R p Yw₁ Yw * Yw₁)
        (fun n h => presentValue T R p Yi₁ Yi / presentValue T R p Yw₁ Yw * Yw n h)
      = presentValue T R p Yi₁ Yi := by
  set μ := presentValue T R p Yi₁ Yi / presentValue T R p Yw₁ Yw with hμ
  have lin : presentValue T R p (μ * Yw₁) (fun n h => μ * Yw n h)
      = μ * presentValue T R p Yw₁ Yw := by
    simp only [presentValue, mul_add, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun h _ => by ring
  rw [lin, hμ, div_mul_cancel₀ _ hW]

/-- Constant consumption shares from the first-order conditions, O&R Appendix 5C.3, p. 342:
if Home and Foreign both satisfy (84) with CRRA marginal utility `C^{−ρ}` (`ρ ≠ 0`) at
common prices, and world markets clear at date 1 and at `h_t`, then
`C(h_t) = μ Y^W(h_t)` with `μ = C₁/Y^W_1` (requires `π(h_t|h_1) > 0`, `β > 0`). -/
theorem crra_constant_share (tr : Tree S) {β ρ : ℝ} (hβ : 0 < β) (hρ : ρ ≠ 0) (n : ℕ)
    {R P C₁ C₁' Y₁ : ℝ} {h : Fin n → S} {Ch Ch' Yh : ℝ}
    (hπ : 0 < tr.histProb h) (hC₁ : 0 < C₁) (hC₁' : 0 < C₁') (hCh : 0 < Ch) (hCh' : 0 < Ch')
    (hfoc : R * P * C₁ ^ (-ρ) = tr.histProb h * β ^ n * Ch ^ (-ρ))
    (hfoc' : R * P * C₁' ^ (-ρ) = tr.histProb h * β ^ n * Ch' ^ (-ρ))
    (hclear₁ : C₁ + C₁' = Y₁) (hclear : Ch + Ch' = Yh) :
    Ch = C₁ / Y₁ * Yh := by
  have hk : 0 < tr.histProb h * β ^ n := mul_pos hπ (pow_pos hβ n)
  have r1 : (Ch / C₁) ^ (-ρ) = R * P / (tr.histProb h * β ^ n) := by
    rw [Real.div_rpow hCh.le hC₁.le, eq_div_iff hk.ne',
      div_mul_eq_mul_div, div_eq_iff (Real.rpow_pos_of_pos hC₁ _).ne']
    linarith
  have r2 : (Ch' / C₁') ^ (-ρ) = R * P / (tr.histProb h * β ^ n) := by
    rw [Real.div_rpow hCh'.le hC₁'.le, eq_div_iff hk.ne',
      div_mul_eq_mul_div, div_eq_iff (Real.rpow_pos_of_pos hC₁' _).ne']
    linarith
  have hg : Ch / C₁ = Ch' / C₁' :=
    (Real.rpow_left_inj (div_pos hCh hC₁).le (div_pos hCh' hC₁').le (neg_ne_zero.mpr hρ)).mp
      (r1.trans r2.symm)
  rw [← hclear₁, ← hclear]
  field_simp at hg ⊢
  nlinarith

/-- The equilibrium long-term interest factor, O&R Appendix 5C.3, p. 342: if the bond Euler
equation (85) holds with CRRA marginal utility at the constant-share allocation `C = μY^W`,
then `R_{1,t} = β^{t−1} Σ π(h_t|h_1) Y^W(h_t)^{−ρ}/(Y^W_1)^{−ρ}`. -/
theorem crra_interest_factor (tr : Tree S) (β ρ : ℝ) (n : ℕ) {R μ Y₁ : ℝ}
    {Y : (Fin n → S) → ℝ} (hR : R ≠ 0) (hμ : 0 < μ) (hY₁ : 0 < Y₁) (hY : ∀ h, 0 < Y h)
    (heuler : (μ * Y₁) ^ (-ρ) = β ^ n / R * ∑ h, tr.histProb h * (μ * Y h) ^ (-ρ)) :
    R = crraR tr β ρ Y₁ n Y := by
  have hm : 0 < μ ^ (-ρ) := Real.rpow_pos_of_pos hμ _
  have hY₁' : 0 < Y₁ ^ (-ρ) := Real.rpow_pos_of_pos hY₁ _
  have e : ∑ h, tr.histProb h * (μ * Y h) ^ (-ρ) = μ ^ (-ρ) * crraMass tr ρ n Y := by
    rw [crraMass, Finset.mul_sum]
    exact Finset.sum_congr rfl fun h _ => by rw [Real.mul_rpow hμ.le (hY h).le]; ring
  rw [e, Real.mul_rpow hμ.le hY₁.le] at heuler
  unfold crraR
  field_simp at heuler ⊢
  nlinarith

/-! ## Appendix 5D: ongoing trade and dynamic consistency -/

/-- O&R (88), p. 344: if the date-1 plan satisfies the first-order conditions (84)/(86) in
date-1 prices `p̃ = pR` at a date-`t` history `h` (`t = m + 2`) and at its date-2 history
`h_2`, then `[p̃(h_t|h_1)/p̃(h_2|h_1)] u′(C(h_2)) = [π(h_t|h_1)/π(h_2|h_1)] β^{t−2} u′(C(h_t))`
(given positive marginal utilities, `β > 0`, `π(h_2|h_1) > 0`). -/
theorem foc_date2_ratio (tr : Tree S) (du : ℝ → ℝ) {β : ℝ} (hβ : 0 < β) {m : ℕ}
    (h : Fin (m + 1) → S) {P₁ Pt C₁ C₂ Ct : ℝ}
    (hπ₂ : 0 < tr.histProb (restr h 1 (by omega))) (hdu₁ : 0 < du C₁) (hdu₂ : 0 < du C₂)
    (hfoc₂ : P₁ * du C₁ = tr.histProb (restr h 1 (by omega)) * β ^ 1 * du C₂)
    (hfoct : Pt * du C₁ = tr.histProb h * β ^ (m + 1) * du Ct) :
    Pt / P₁ * du C₂ = tr.histProb h / tr.histProb (restr h 1 (by omega)) * β ^ m * du Ct := by
  have hP₁ : P₁ = tr.histProb (restr h 1 (by omega)) * β * du C₂ / du C₁ := by
    rw [eq_div_iff hdu₁.ne']; linarith [hfoc₂, pow_one β]
  have hPt : Pt = tr.histProb h * β ^ (m + 1) * du Ct / du C₁ := by
    rw [eq_div_iff hdu₁.ne']; linarith
  rw [hP₁, hPt, pow_succ]
  field_simp

/-- O&R (87), p. 344: with Bayes' rule and the no-arbitrage identity
`p̃(h_t|h_1)/p̃(h_2|h_1) = p̃(h_t|h_2)` (a hypothesis here, the book's arbitrage argument),
equation (88) becomes the date-2 first-order condition
`p̃(h_t|h_2) u′(C(h_2)) = π(h_t|h_2) β^{t−2} u′(C(h_t))`. -/
theorem foc_date2 (tr : Tree S) (du : ℝ → ℝ) {β : ℝ} (hβ : 0 < β) {m : ℕ}
    (h : Fin (m + 1) → S) {P₁ Pt P₂ C₁ C₂ Ct : ℝ}
    (hπ₂ : 0 < tr.histProb (restr h 1 (by omega))) (hdu₁ : 0 < du C₁) (hdu₂ : 0 < du C₂)
    (hfoc₂ : P₁ * du C₁ = tr.histProb (restr h 1 (by omega)) * β ^ 1 * du C₂)
    (hfoct : Pt * du C₁ = tr.histProb h * β ^ (m + 1) * du Ct)
    (harb : Pt / P₁ = P₂) :
    P₂ * du C₂ = tr.condProb h 1 * β ^ m * du Ct := by
  rw [← harb, foc_date2_ratio tr du hβ h hπ₂ hdu₁ hdu₂ hfoc₂ hfoct,
    tr.histProb_div_date2 h (by omega) hπ₂.ne']

/-- Dynamic consistency, O&R Appendix 5D, pp. 343–344. Suppose the date-1 plan `(C₁, C)`
satisfies the first-order conditions (84) at date-1 prices `R_{1,t} p(h_t|h_1)` for all dates
`t = n + 1 ≤ T`, and date-2 prices `P₂` (of date-`t` claims, `t = m + 2`, in date-2 output)
obey the no-arbitrage identity `p̃(h_t|h_1)/p̃(h_2|h_1) = p̃(h_t|h_2)`. When the date-2 event is
`s₂` (with `π(h_2|h_1) > 0`) and markets reopen, any positive plan `(c₂′, c′)` affordable
from the contracted positions (the date-2 budget constraint on p. 344) gives no more
date-2 expected utility than the original plan: with concave `u`, the date-1 plan remains
optimal on date 2. -/
theorem dynamic_consistency [DecidableEq S] (tr : Tree S) (T : ℕ) (u du : ℝ → ℝ)
    (htan : ∀ x y, 0 < x → 0 < y → u y ≤ u x + du x * (y - x))
    (hdu : ∀ x, 0 < x → 0 < du x) {β : ℝ} (hβ : 0 < β) (R : ℕ → ℝ)
    (p : (n : ℕ) → (Fin n → S) → ℝ) (P₂ : (m : ℕ) → (Fin (m + 1) → S) → ℝ)
    {C₁ : ℝ} {C : (n : ℕ) → (Fin n → S) → ℝ} (hC₁ : 0 < C₁) (hC : ∀ n h, 0 < C n h)
    (s₂ : S) (hπ₂ : 0 < tr.histProb (fun _ : Fin 1 => s₂))
    (hfoc : ∀ n, 1 ≤ n → n < T → ∀ h,
      R n * p n h * du C₁ = tr.histProb h * β ^ n * du (C n h))
    (harb : ∀ m ∈ Ico 1 (T - 1), ∀ h : Fin (m + 1) → S, h 0 = s₂ →
      R (m + 1) * p (m + 1) h / (R 1 * p 1 (fun _ => s₂)) = P₂ m h)
    {c₂' : ℝ} {c' : (m : ℕ) → (Fin (m + 1) → S) → ℝ} (hc₂' : 0 < c₂')
    (hc' : ∀ m h, 0 < c' m h)
    (hbud : c₂' + ∑ m ∈ Ico 1 (T - 1), ∑ h ∈ univ.filter (fun h : Fin (m + 1) → S => h 0 = s₂),
        P₂ m h * c' m h
      ≤ C 1 (fun _ => s₂) + ∑ m ∈ Ico 1 (T - 1),
        ∑ h ∈ univ.filter (fun h : Fin (m + 1) → S => h 0 = s₂), P₂ m h * C (m + 1) h) :
    u c₂' + ∑ m ∈ Ico 1 (T - 1), ∑ h ∈ univ.filter (fun h : Fin (m + 1) → S => h 0 = s₂),
        β ^ m * tr.condProb h 1 * u (c' m h)
      ≤ u (C 1 (fun _ => s₂)) + ∑ m ∈ Ico 1 (T - 1),
        ∑ h ∈ univ.filter (fun h : Fin (m + 1) → S => h 0 = s₂),
          β ^ m * tr.condProb h 1 * u (C (m + 1) h) := by
  refine foc_plan_optimal (Ico 1 (T - 1))
    (fun m => univ.filter (fun h : Fin (m + 1) → S => h 0 = s₂)) u du htan
    (fun m h => β ^ m * tr.condProb h 1) P₂
    (fun m _ h _ => mul_nonneg (pow_nonneg hβ.le m) (tr.condProb_nonneg h 1))
    (hC 1 _) hc₂' (fun m _ h _ => hC (m + 1) h) (fun m _ h _ => hc' m h)
    (hdu _ (hC 1 _)).le ?_ hbud
  intro m hm h hh
  have hh0 : h 0 = s₂ := (Finset.mem_filter.mp hh).2
  have hmT := Finset.mem_Ico.mp hm
  have hg : restr h 1 (by omega) = fun _ : Fin 1 => s₂ := by
    funext j
    rw [Fin.fin_one_eq_zero j, ← hh0]
    rfl
  have hπ : 0 < tr.histProb (restr h 1 (by omega)) := by rw [hg]; exact hπ₂
  have hf₂ : R 1 * p 1 (fun _ => s₂) * du C₁
      = tr.histProb (restr h 1 (by omega)) * β ^ 1 * du (C 1 (fun _ => s₂)) := by
    rw [hg]; exact hfoc 1 le_rfl (by omega) _
  have key := foc_date2 tr du hβ h hπ (hdu _ hC₁) (hdu _ (hC 1 _)) hf₂
    (hfoc (m + 1) (by omega) (by omega) h) (harb m hm h hh0)
  rw [key]; ring

/-! ## Supplement A to Chapter 5: multiperiod portfolio selection -/

/-- Log utility, O&R Supplement A, p. 743: with consumption `C_s = μW_s`, wealth
`W_{t+1} = (1 + r°_{t+1})(W_t − C_t)` and next-period return `r°(s)` in state `s` (probabilities
`π`, `Σπ = 1`, `1 + r°(s) > 0`), the Euler equation `1/C_t = βE_t{(1 + r°_{t+1})/C_{t+1}}` holds
if and only if `μ = 1 − β` (for `0 < μ < 1`, `W_t > 0`), whatever the return distribution. -/
theorem log_share_iff {ι : Type} [Fintype ι] (π r : ι → ℝ) (hπ : ∑ s, π s = 1)
    (hr : ∀ s, 0 < 1 + r s) {β μ W : ℝ} (hμ0 : 0 < μ) (hμ1 : μ < 1) (hW : 0 < W) :
    1 / (μ * W) = β * ∑ s, π s * ((1 + r s) * (1 / (μ * ((1 + r s) * ((1 - μ) * W)))))
      ↔ μ = 1 - β := by
  have h1 : 0 < 1 - μ := by linarith
  have e : ∀ s, π s * ((1 + r s) * (1 / (μ * ((1 + r s) * ((1 - μ) * W)))))
      = π s * (1 / (μ * ((1 - μ) * W))) := by
    intro s
    have := (hr s).ne'
    field_simp
  simp only [e, ← Finset.sum_mul, hπ, one_mul]
  rw [mul_one_div, div_eq_div_iff (by positivity) (by positivity)]
  constructor
  · intro h
    have h2 : (1 - μ) * (μ * W) = β * (μ * W) := by linarith
    have := mul_right_cancel₀ (mul_pos hμ0 hW).ne' h2
    linarith
  · intro h
    rw [h]; ring

/-- The share formula behind O&R's CRRA recursion, Supplement A, p. 744: for `0 < μ < 1`,
`ρ > 0` and `K ≥ 0`, `μ = (1 + K^{1/ρ})^{−1}` if and only if `K = ((1 − μ)/μ)^ρ`. -/
theorem share_formula_iff {μ ρ K : ℝ} (hμ0 : 0 < μ) (hμ1 : μ < 1) (hρ : 0 < ρ)
    (hK : 0 ≤ K) : μ = (1 + K ^ (1 / ρ))⁻¹ ↔ K = ((1 - μ) / μ) ^ ρ := by
  have h1 : 0 < 1 - μ := by linarith
  have hq : 0 ≤ (1 - μ) / μ := (div_pos h1 hμ0).le
  have hKr : 0 ≤ K ^ (1 / ρ) := Real.rpow_nonneg hK _
  constructor
  · intro h
    have e : K ^ (1 / ρ) = (1 - μ) / μ := by
      rw [h]; field_simp; ring
    rw [← e, one_div, Real.rpow_inv_rpow hK hρ.ne']
  · intro h
    have e : K ^ (1 / ρ) = (1 - μ) / μ := by
      rw [h, one_div, Real.rpow_rpow_inv hq hρ.ne']
    rw [e]
    field_simp
    ring

/-- The CRRA consumption-share recursion, O&R Supplement A, p. 744. With `u′(C) = C^{−ρ}`,
`C_t = μ_t W_t`, `C_{t+1}(s) = μ_{t+1}(s) W_{t+1}(s)` and
`W_{t+1}(s) = (1 + r°(s))(1 − μ_t)W_t`, the consumption Euler equation
`C_t^{−ρ} = βE_t{(1 + r°_{t+1}) C_{t+1}^{−ρ}}` holds if and only if
`μ_t = (1 + [βE_t{(1 + r°_{t+1})^{1−ρ} μ_{t+1}^{−ρ}}]^{1/ρ})^{−1}`
(for `0 < μ_t < 1`, `μ_{t+1} > 0`, `W_t > 0`, `1 + r° > 0`, `β ≥ 0`, `π ≥ 0`, `ρ > 0`). -/
theorem crra_share_recursion {ι : Type} [Fintype ι] (π r μ' : ι → ℝ)
    (hπ : ∀ s, 0 ≤ π s) (hr : ∀ s, 0 < 1 + r s) (hμ' : ∀ s, 0 < μ' s) {β ρ μ W : ℝ}
    (hβ : 0 ≤ β) (hρ : 0 < ρ) (hμ0 : 0 < μ) (hμ1 : μ < 1) (hW : 0 < W) :
    (μ * W) ^ (-ρ) = β * ∑ s, π s * ((1 + r s) * (μ' s * ((1 + r s) * (1 - μ) * W)) ^ (-ρ))
      ↔ μ = (1 + (β * ∑ s, π s * ((1 + r s) ^ (1 - ρ) * μ' s ^ (-ρ))) ^ (1 / ρ))⁻¹ := by
  have h1 : 0 < 1 - μ := by linarith
  set E := ∑ s, π s * ((1 + r s) ^ (1 - ρ) * μ' s ^ (-ρ)) with hE
  have hE0 : 0 ≤ E := Finset.sum_nonneg fun s _ =>
    mul_nonneg (hπ s) (mul_nonneg (Real.rpow_nonneg (hr s).le _)
      (Real.rpow_nonneg (hμ' s).le _))
  have e : ∀ s, π s * ((1 + r s) * (μ' s * ((1 + r s) * (1 - μ) * W)) ^ (-ρ))
      = π s * ((1 + r s) ^ (1 - ρ) * μ' s ^ (-ρ)) * ((1 - μ) * W) ^ (-ρ) := by
    intro s
    have hrs := hr s
    rw [show μ' s * ((1 + r s) * (1 - μ) * W) = μ' s * ((1 + r s) * ((1 - μ) * W)) by ring,
      Real.mul_rpow (hμ' s).le (by positivity), Real.mul_rpow hrs.le (by positivity),
      show (1 : ℝ) - ρ = 1 + -ρ by ring, Real.rpow_add hrs, Real.rpow_one]
    ring
  simp only [e, ← Finset.sum_mul]
  rw [← hE, share_formula_iff hμ0 hμ1 hρ (mul_nonneg hβ hE0), Real.mul_rpow hμ0.le hW.le,
    Real.mul_rpow h1.le hW.le, Real.div_rpow h1.le hμ0.le]
  have hWr : 0 < W ^ (-ρ) := Real.rpow_pos_of_pos hW _
  have hμr : 0 < μ ^ ρ := Real.rpow_pos_of_pos hμ0 _
  rw [Real.rpow_neg hμ0.le, Real.rpow_neg h1.le, Real.rpow_neg hW.le]
  have h1r : 0 < (1 - μ) ^ ρ := Real.rpow_pos_of_pos h1 _
  have hWr' : 0 < W ^ ρ := Real.rpow_pos_of_pos hW _
  constructor
  · intro h
    field_simp at h
    rw [eq_div_iff hμr.ne']
    nlinarith
  · intro h
    have e2 : β * (E * (((1 - μ) ^ ρ)⁻¹ * (W ^ ρ)⁻¹)) = β * E * (((1 - μ) ^ ρ)⁻¹ * (W ^ ρ)⁻¹) :=
      by ring
    rw [e2, h]
    field_simp

/-- The i.i.d. fixed point, O&R Supplement A, p. 744: with a constant share `μ_{t+1} = μ`, the
recursion `μ = (1 + [βE{(1 + r°)^{1−ρ} μ^{−ρ}}]^{1/ρ})^{−1}` holds if and only if
`μ = 1 − [βE(1 + r°)^{1−ρ}]^{1/ρ}` (for `0 < μ < 1`, `ρ > 0`, `β ≥ 0`, `π ≥ 0`,
`1 + r° > 0`). So the book's formula is a fixed point, and the only one in `(0, 1)`. -/
theorem crra_iid_share {ι : Type} [Fintype ι] (π r : ι → ℝ) (hπ : ∀ s, 0 ≤ π s)
    (hr : ∀ s, 0 < 1 + r s) {β ρ μ : ℝ} (hβ : 0 ≤ β) (hρ : 0 < ρ) (hμ0 : 0 < μ)
    (hμ1 : μ < 1) :
    μ = (1 + (β * ∑ s, π s * ((1 + r s) ^ (1 - ρ) * μ ^ (-ρ))) ^ (1 / ρ))⁻¹
      ↔ μ = 1 - (β * ∑ s, π s * (1 + r s) ^ (1 - ρ)) ^ (1 / ρ) := by
  set B := β * ∑ s, π s * (1 + r s) ^ (1 - ρ) with hB
  have hB0 : 0 ≤ B := mul_nonneg hβ (Finset.sum_nonneg fun s _ =>
    mul_nonneg (hπ s) (Real.rpow_nonneg (hr s).le _))
  have h1 : 0 < 1 - μ := by linarith
  have eK : β * ∑ s, π s * ((1 + r s) ^ (1 - ρ) * μ ^ (-ρ)) = B * μ ^ (-ρ) := by
    rw [hB, mul_assoc, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun s _ => by ring
  have hμr : 0 < μ ^ ρ := Real.rpow_pos_of_pos hμ0 _
  rw [eK, share_formula_iff hμ0 hμ1 hρ (mul_nonneg hB0 (Real.rpow_nonneg hμ0.le _)),
    Real.div_rpow h1.le hμ0.le, Real.rpow_neg hμ0.le]
  constructor
  · intro h
    have hB' : B = (1 - μ) ^ ρ := by
      field_simp at h
      exact h
    rw [hB', one_div, Real.rpow_rpow_inv h1.le hρ.ne']
    ring
  · intro h
    have hb : (1 - μ) = B ^ (1 / ρ) := by linarith
    rw [hb, one_div, Real.rpow_inv_rpow hB0 hρ.ne']
    field_simp

/-- The log case of the i.i.d. share, O&R Supplement A, pp. 743–744: at `ρ = 1` the formula
`1 − [βE(1 + r°)^{1−ρ}]^{1/ρ}` reduces to `1 − β` (given `Σπ = 1`). -/
theorem crra_iid_share_log {ι : Type} [Fintype ι] (π r : ι → ℝ) (hπ : ∑ s, π s = 1)
    (β : ℝ) : 1 - (β * ∑ s, π s * (1 + r s) ^ ((1 : ℝ) - 1)) ^ ((1 : ℝ) / 1) = 1 - β := by
  simp [hπ]

end ObstfeldRogoff.InternationalFinancialMarkets.EventTree

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Intragenerational risk sharing and the Lucas two-good model

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §5.6,
pp. 332–335, and Chapter 5 Exercise 6, p. 347.

**§5.6.** Home and Foreign residents live two periods and have log utility
`log c^Y_t + βE_t log c^O_{t+1}`. Everyone in Home receives `y_t` (Foreign `y*_t`); date-`t+1`
states `s` have probabilities `π_t(s)`. The young of date `t` trade Arrow–Debreu claims on
date-`t+1` consumption only among themselves. We prove:
* at the book's prices `1 + r_{t+1} = (y_t + y*_t)^{−1}/(βE_t[(y_{t+1} + y*_{t+1})^{−1}])` and
  `p_t(s) = π_t(s)(y_{t+1}(s) + y*_{t+1}(s))^{−1}/E_t[(y_{t+1} + y*_{t+1})^{−1}]`, the allocation
  `c^Y = μ_t(y + y*)`, `c^O(s) = μ_t(y_{t+1}(s) + y*_{t+1}(s))` (and `1 − μ_t` for Foreign)
  satisfies both cohorts' first-order conditions and budget constraints, markets clear, and
  it is optimal for each young agent (log concavity);
* conversely every such within-cohort equilibrium has this allocation, the book's share
  `μ_t = [y_t/(y_t + y*_t) + βE_t{y_{t+1}/(y_{t+1} + y*_{t+1})}]/(1 + β)` (footnote 16 with
  `ρ = 1`), and these prices;
* aggregate consumption (76).

**Exercise 6** (Lucas 1982). With identical tastes and equal pooled portfolios both countries
have wealth `½(X + pY)`, so identical demands and market clearing give `C_X = X/2`,
`C_Y = Y/2` and `p = u_Y/u_X` at `(X/2, Y/2)`. For asset prices we take a finite Markov chain
for the endowment state and a truncated horizon: the Euler equation
`V_t u_X(t) = βE_t[u_X(t+1)(V_{t+1} + D_{t+1})]` with zero terminal value gives the finite
present-value sum `V_t = Σ_k β^k E_t[u_X(t+k) D_{t+k}]/u_X(t)` (for `V_X`, `D = X`; for `V_Y`,
`D = pY`), converging to the infinite sum when it is summable. The riskless bond price is
`βE_t[u_X(t+1)]/u_X(t)` and the price of sure `Y` in units of `Y` is
`βE_t[u_Y(t+1)]/u_Y(t)` (the own-rate of interest on `Y` is its reciprocal minus one).
-/

namespace ObstfeldRogoff.InternationalFinancialMarkets.OLGRiskSharing

open Finset Filter Topology

variable {S : Type} [Fintype S]

/-! ## §5.6: the within-cohort equilibrium -/

/-- The Home cohort's consumption share, O&R §5.6, p. 334 (footnote 16 with `ρ = 1`):
`μ_t = [y_t/(y_t + y*_t) + βΣ_s π_t(s) y_{t+1}(s)/(y_{t+1}(s) + y*_{t+1}(s))]/(1 + β)`. -/
noncomputable def cohortShare (β : ℝ) (π : S → ℝ) (y ys : ℝ) (y1 ys1 : S → ℝ) : ℝ :=
  1 / (1 + β) * (y / (y + ys) + β * ∑ s, π s * (y1 s / (y1 s + ys1 s)))

/-- The equilibrium gross interest rate, O&R §5.6, p. 334:
`1 + r_{t+1} = (y_t + y*_t)^{−1}/(βE_t[(y_{t+1} + y*_{t+1})^{−1}])`. -/
noncomputable def cohortGrossRate (β : ℝ) (π : S → ℝ) (y ys : ℝ) (y1 ys1 : S → ℝ) : ℝ :=
  1 / (y + ys) / (β * ∑ s, π s * (1 / (y1 s + ys1 s)))

/-- The equilibrium Arrow–Debreu prices, O&R §5.6, p. 334:
`p_t(s) = π_t(s)(y_{t+1}(s) + y*_{t+1}(s))^{−1}/E_t[(y_{t+1} + y*_{t+1})^{−1}]`. -/
noncomputable def cohortPrice (π : S → ℝ) (y1 ys1 : S → ℝ) (s : S) : ℝ :=
  π s * (1 / (y1 s + ys1 s)) / ∑ s', π s' * (1 / (y1 s' + ys1 s'))

/-- The expected inverse of next-period world output is positive (O&R §5.6, p. 334). -/
theorem expected_inverse_pos (π : S → ℝ) (hπ0 : ∀ s, 0 ≤ π s) (hπ1 : ∑ s, π s = 1)
    {y1 ys1 : S → ℝ} (hy1 : ∀ s, 0 < y1 s + ys1 s) :
    0 < ∑ s, π s * (1 / (y1 s + ys1 s)) := by
  have hlt : ∑ _s : S, (0 : ℝ) < ∑ s, π s := by rw [hπ1]; simp
  obtain ⟨s₀, -, hs₀⟩ := Finset.exists_lt_of_sum_lt hlt
  exact Finset.sum_pos' (fun s _ => mul_nonneg (hπ0 s) (one_div_pos.mpr (hy1 s)).le)
    ⟨s₀, Finset.mem_univ _, mul_pos hs₀ (one_div_pos.mpr (hy1 s₀))⟩

/-- The equilibrium Arrow–Debreu prices sum to one (O&R §5.6, p. 334; the no-arbitrage
condition (7) with a riskless bond). -/
theorem cohortPrice_sum (π : S → ℝ) (hπ0 : ∀ s, 0 ≤ π s) (hπ1 : ∑ s, π s = 1)
    {y1 ys1 : S → ℝ} (hy1 : ∀ s, 0 < y1 s + ys1 s) :
    ∑ s, cohortPrice π y1 ys1 s = 1 := by
  simp only [cohortPrice, ← Finset.sum_div]
  exact div_self (expected_inverse_pos π hπ0 hπ1 hy1).ne'

/-- The Home and Foreign cohort shares sum to one, O&R §5.6, p. 334: Foreign's share is
`1 − μ_t`. -/
theorem cohortShare_add (β : ℝ) (π : S → ℝ) (hπ1 : ∑ s, π s = 1) {y ys : ℝ}
    {y1 ys1 : S → ℝ} (hβ : 0 < β) (hy : 0 < y + ys) (hy1 : ∀ s, 0 < y1 s + ys1 s) :
    cohortShare β π y ys y1 ys1 + cohortShare β π ys y ys1 y1 = 1 := by
  have e : ∀ s, π s * (y1 s / (y1 s + ys1 s)) + π s * (ys1 s / (ys1 s + y1 s)) = π s := by
    intro s
    have := (hy1 s).ne'
    rw [add_comm (ys1 s) (y1 s)]
    field_simp
  have hsum : ∑ s, π s * (y1 s / (y1 s + ys1 s)) + ∑ s, π s * (ys1 s / (ys1 s + y1 s)) = 1 := by
    rw [← Finset.sum_add_distrib, ← hπ1]
    exact Finset.sum_congr rfl fun s _ => e s
  unfold cohortShare
  rw [add_comm ys y]
  set A := ∑ s, π s * (y1 s / (y1 s + ys1 s))
  set B := ∑ s, π s * (ys1 s / (ys1 s + y1 s))
  have h1 : (1 : ℝ) + β ≠ 0 := by linarith
  field_simp
  linear_combination (y + ys) * β * hsum

/-- The equilibrium interest rate and Arrow–Debreu prices of O&R §5.6, p. 334 depend on Home
and Foreign endowments only through world output, so they are the same whether computed
from Home's or from Foreign's side. -/
theorem cohort_prices_symm (β : ℝ) (π : S → ℝ) (y ys : ℝ) (y1 ys1 : S → ℝ) (s : S) :
    cohortGrossRate β π ys y ys1 y1 = cohortGrossRate β π y ys y1 ys1 ∧
      cohortPrice π ys1 y1 s = cohortPrice π y1 ys1 s := by
  refine ⟨?_, ?_⟩ <;>
    simp only [cohortGrossRate, cohortPrice, add_comm ys y, add_comm (ys1 _) (y1 _)]

/-- The within-cohort equilibrium of O&R §5.6, p. 334 (verification). At the book's prices,
the allocation `c^Y = μ(y + y*)`, `c^O(s) = μ(y_{t+1}(s) + y*_{t+1}(s))` for Home, with
`μ = μ_t`, satisfies Home's log-utility first-order conditions
`[p(s)/(1 + r)](1/c^Y) = βπ(s)/c^O(s)` and Home's budget constraint
`c^Y + Σ_s p(s)c^O(s)/(1 + r) = y + Σ_s p(s)y_{t+1}(s)/(1 + r)`. (Foreign is the same
statement with the roles of `y`, `y*` exchanged, by `cohortShare_add`.) -/
theorem cohort_equilibrium (π : S → ℝ) (hπ0 : ∀ s, 0 ≤ π s) (hπ1 : ∑ s, π s = 1)
    {β y ys : ℝ} {y1 ys1 : S → ℝ} (hβ : 0 < β) (hy : 0 < y + ys)
    (hy1 : ∀ s, 0 < y1 s + ys1 s) (hμ : 0 < cohortShare β π y ys y1 ys1) :
    (∀ s, cohortPrice π y1 ys1 s / cohortGrossRate β π y ys y1 ys1
        * (1 / (cohortShare β π y ys y1 ys1 * (y + ys)))
      = β * π s * (1 / (cohortShare β π y ys y1 ys1 * (y1 s + ys1 s)))) ∧
    cohortShare β π y ys y1 ys1 * (y + ys) + 1 / cohortGrossRate β π y ys y1 ys1
        * ∑ s, cohortPrice π y1 ys1 s * (cohortShare β π y ys y1 ys1 * (y1 s + ys1 s))
      = y + 1 / cohortGrossRate β π y ys y1 ys1 * ∑ s, cohortPrice π y1 ys1 s * y1 s := by
  have hE := expected_inverse_pos π hπ0 hπ1 hy1
  set E := ∑ s, π s * (1 / (y1 s + ys1 s)) with hEdef
  set μ := cohortShare β π y ys y1 ys1 with hμdef
  -- the price of a claim in date-`t` units
  have hq : ∀ s, cohortPrice π y1 ys1 s / cohortGrossRate β π y ys y1 ys1
      = β * π s * (y + ys) / (y1 s + ys1 s) := by
    intro s
    have := (hy1 s).ne'
    simp only [cohortPrice, cohortGrossRate, ← hEdef]
    field_simp
  refine ⟨fun s => ?_, ?_⟩
  · rw [hq s]
    have := (hy1 s).ne'
    field_simp
  · have e1 : ∀ s, 1 / cohortGrossRate β π y ys y1 ys1 * cohortPrice π y1 ys1 s
        = β * π s * (y + ys) / (y1 s + ys1 s) := by
      intro s; rw [← hq s]; ring
    simp only [Finset.mul_sum, ← mul_assoc, e1]
    have e2 : ∀ s, β * π s * (y + ys) / (y1 s + ys1 s) * μ * (y1 s + ys1 s)
        = μ * β * (y + ys) * π s := by
      intro s; have := (hy1 s).ne'; field_simp
    have e3 : ∀ s, β * π s * (y + ys) / (y1 s + ys1 s) * y1 s
        = β * (y + ys) * (π s * (y1 s / (y1 s + ys1 s))) := by
      intro s; have := (hy1 s).ne'; field_simp
    simp only [e2, e3, ← Finset.mul_sum, hπ1, mul_one]
    rw [hμdef, cohortShare]
    have h1 : (1 : ℝ) + β ≠ 0 := by linarith
    field_simp

/-- Optimality of the young agent's plan, O&R §5.6, p. 333: with log utility, a positive plan
`(c^Y, c^O)` satisfying the first-order conditions `q(s)/c^Y = βπ(s)/c^O(s)` (where
`q(s) = p(s)/(1 + r)` is the date-`t` price of the state-`s` claim) maximises
`log c^Y + βΣπ(s) log c^O(s)` among positive plans that cost no more. -/
theorem young_plan_optimal (π q : S → ℝ) (hπ0 : ∀ s, 0 ≤ π s) {β : ℝ} (hβ : 0 ≤ β)
    {cY cY' : ℝ} {cO cO' : S → ℝ} (hcY : 0 < cY) (hcY' : 0 < cY') (hcO : ∀ s, 0 < cO s)
    (hcO' : ∀ s, 0 < cO' s) (hfoc : ∀ s, q s * (1 / cY) = β * π s * (1 / cO s))
    (hbud : cY' + ∑ s, q s * cO' s ≤ cY + ∑ s, q s * cO s) :
    Real.log cY' + β * ∑ s, π s * Real.log (cO' s)
      ≤ Real.log cY + β * ∑ s, π s * Real.log (cO s) := by
  have h := EventTree.foc_plan_optimal (H := fun _ => S) {0} (fun _ => Finset.univ)
    Real.log (fun x => 1 / x) (fun x y hx hy => EventTree.log_tangent hx hy)
    (fun _ s => β * π s) (fun _ s => q s)
    (fun _ _ s _ => mul_nonneg hβ (hπ0 s)) hcY hcY' (fun _ _ s _ => hcO s)
    (fun _ _ s _ => hcO' s) (one_div_pos.mpr hcY).le (fun _ _ s _ => hfoc s)
    (by simpa using hbud)
  simp only [Finset.sum_singleton, mul_assoc, ← Finset.mul_sum] at h
  exact h

/-- Characterisation of the within-cohort equilibrium, O&R §5.6, p. 334 ("you can confirm").
Suppose the Home and Foreign young both satisfy their log-utility first-order conditions
`[p(s)/R] c^O(s) = βπ(s) c^Y` at common prices (gross rate `R > 0`, `p(s) > 0`, `Σp = 1`),
Home's budget constraint holds, and markets clear today and in every state tomorrow. Then
`c^Y = μ_t(y + y*)`, `c^O(s) = μ_t(y_{t+1}(s) + y*_{t+1}(s))` with the book's `μ_t`, and `R`,
`p` are the book's prices. -/
theorem cohort_equilibrium_unique (π : S → ℝ) (hπ0 : ∀ s, 0 ≤ π s) (hπ1 : ∑ s, π s = 1)
    {β y ys R : ℝ} {y1 ys1 p : S → ℝ} (hβ : 0 < β) (hy : 0 < y + ys)
    (hy1 : ∀ s, 0 < y1 s + ys1 s) (hR : 0 < R) (hp : ∀ s, 0 < p s) (hpsum : ∑ s, p s = 1)
    {cY cYs : ℝ} {cO cOs : S → ℝ} (hcY : 0 < cY)
    (hfoc : ∀ s, p s / R * cO s = β * π s * cY)
    (hfocs : ∀ s, p s / R * cOs s = β * π s * cYs)
    (hbud : cY + 1 / R * ∑ s, p s * cO s = y + 1 / R * ∑ s, p s * y1 s)
    (hclear : cY + cYs = y + ys) (hclear1 : ∀ s, cO s + cOs s = y1 s + ys1 s) :
    cY = cohortShare β π y ys y1 ys1 * (y + ys) ∧
    (∀ s, cO s = cohortShare β π y ys y1 ys1 * (y1 s + ys1 s)) ∧
    R = cohortGrossRate β π y ys y1 ys1 ∧ ∀ s, p s = cohortPrice π y1 ys1 s := by
  have hW := hy.ne'
  -- consumption growth is equalised: `c^O(s) = (c^Y/(y + y*))(y_{t+1}(s) + y*_{t+1}(s))`
  have hcO : ∀ s, cO s = cY / (y + ys) * (y1 s + ys1 s) := by
    intro s
    have hq : 0 < p s / R := div_pos (hp s) hR
    have h1 : p s / R * (cO s * cYs) = p s / R * (cOs s * cY) := by
      linear_combination cYs * hfoc s - cY * hfocs s
    have h2 := mul_left_cancel₀ hq.ne' h1
    rw [div_mul_eq_mul_div, eq_div_iff hW]
    linear_combination h2 - cO s * hclear + cY * hclear1 s
  -- date-`t` claim prices
  have hq : ∀ s, p s / R = β * π s * (y + ys) / (y1 s + ys1 s) := by
    intro s
    have h := hfoc s
    rw [hcO s] at h
    have := (hy1 s).ne'
    rw [eq_div_iff this]
    field_simp at h
    rw [div_mul_eq_mul_div, div_eq_iff hR.ne']
    linarith
  have hbud' : cY + β * cY = y + β * (y + ys) * ∑ s, π s * (y1 s / (y1 s + ys1 s)) := by
    have e1 : 1 / R * ∑ s, p s * cO s = β * cY := by
      rw [Finset.mul_sum]
      rw [show β * cY = ∑ s, β * π s * cY by
        rw [← Finset.sum_mul, ← Finset.mul_sum, hπ1]; ring]
      exact Finset.sum_congr rfl fun s _ => by rw [← hfoc s]; ring
    have e2 : 1 / R * ∑ s, p s * y1 s
        = β * (y + ys) * ∑ s, π s * (y1 s / (y1 s + ys1 s)) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      have := (hy1 s).ne'
      rw [show 1 / R * (p s * y1 s) = p s / R * y1 s by ring, hq s]
      field_simp
    rw [e1, e2] at hbud
    exact hbud
  have hshare : cY = cohortShare β π y ys y1 ys1 * (y + ys) := by
    unfold cohortShare
    set A := ∑ s, π s * (y1 s / (y1 s + ys1 s))
    have h1 : (1 : ℝ) + β ≠ 0 := by linarith
    field_simp
    linarith
  have hE := expected_inverse_pos π hπ0 hπ1 hy1
  set E := ∑ s, π s * (1 / (y1 s + ys1 s)) with hEd
  clear_value E
  -- the price normalisation pins down `R`
  have hRinv : 1 / R = β * (y + ys) * E := by
    calc 1 / R = 1 / R * ∑ s, p s := by rw [hpsum, mul_one]
      _ = _ := ?_
    rw [hEd, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [show 1 / R * p s = p s / R by ring, hq s]
    field_simp
  have hRv : R = cohortGrossRate β π y ys y1 ys1 := by
    unfold cohortGrossRate
    rw [← hEd, eq_div_iff (mul_pos hβ hE).ne', eq_div_iff hW]
    field_simp at hRinv
    linarith
  refine ⟨hshare, fun s => ?_, hRv, fun s => ?_⟩
  · rw [hcO s, hshare]; field_simp
  · have h := hq s
    rw [div_eq_iff hR.ne'] at h
    rw [h, hRv]
    unfold cohortGrossRate cohortPrice
    rw [← hEd]
    have := (hy1 s).ne'
    field_simp

/-- Aggregate Home per capita consumption, O&R (76), p. 334: the young of date `t` consume
`μ_t(y_t + y*_t)` and the old (young at `t − 1`) consume `μ_{t−1}(y_t + y*_t)`, so
`c_t = ½(μ_t + μ_{t−1})(y_t + y*_t)`, which expands to
`(y_t + y*_t)/(2(1 + β)) · [y_t/(y_t + y*_t) + βE_t{…} + y_{t−1}/(y_{t−1} + y*_{t−1}) +
βE_{t−1}{y_t/(y_t + y*_t)}]`. Here date-`t` endowments are functions of the date-`t` state
(`yt`, `yst`, probabilities `πprev` from date `t − 1`) and `s₀` is the realised state. -/
theorem aggregate_consumption (β : ℝ) (hβ : 0 < β) (π πprev : S → ℝ)
    (yprev ysprev : ℝ) (yt yst y1 ys1 : S → ℝ) (s₀ : S) :
    1 / 2 * (cohortShare β π (yt s₀) (yst s₀) y1 ys1 * (yt s₀ + yst s₀)
        + cohortShare β πprev yprev ysprev yt yst * (yt s₀ + yst s₀))
      = (yt s₀ + yst s₀) / (2 * (1 + β))
        * (yt s₀ / (yt s₀ + yst s₀) + β * ∑ s, π s * (y1 s / (y1 s + ys1 s))
          + yprev / (yprev + ysprev) + β * ∑ s, πprev s * (yt s / (yt s + yst s))) := by
  unfold cohortShare
  have h1 : (1 : ℝ) + β ≠ 0 := by linarith
  field_simp
  ring

/-- O&R §5.6, p. 334: if Home's output is exactly half of world output today and expected to
be half tomorrow, the current Home young consume exactly half of their generation's world
output in both periods of life: `μ_t = 1/2`. -/
theorem cohortShare_half (π : S → ℝ) {β y ys : ℝ} {y1 ys1 : S → ℝ} (hβ : 0 < β)
    (h0 : y / (y + ys) = 1 / 2) (h1 : ∑ s, π s * (y1 s / (y1 s + ys1 s)) = 1 / 2) :
    cohortShare β π y ys y1 ys1 = 1 / 2 := by
  unfold cohortShare
  rw [h0, h1]
  have : (1 : ℝ) + β ≠ 0 := by linarith
  field_simp

/-! ## Exercise 6: the Lucas (1982) two-good model -/

/-- Exercise 6(b), O&R p. 347 (static allocation). Suppose both countries have the same
demand function `D(p, w) = (C_X, C_Y)` (identical tastes) and, holding equal pooled
portfolios, the same wealth `w = ½(X + pY)`. Then market clearing in both goods gives
`C_X = X/2`, `C_Y = Y/2`, and if the common first-order condition `u_Y = p u_X` holds at the
demanded bundle with `u_X > 0`, then `p = u_Y(X/2, Y/2)/u_X(X/2, Y/2)`. -/
theorem lucas_allocation (D : ℝ → ℝ → ℝ × ℝ) (uX uY : ℝ → ℝ → ℝ) {X Y p : ℝ}
    (hX : (D p ((X + p * Y) / 2)).1 + (D p ((X + p * Y) / 2)).1 = X)
    (hY : (D p ((X + p * Y) / 2)).2 + (D p ((X + p * Y) / 2)).2 = Y)
    (hfoc : uY (D p ((X + p * Y) / 2)).1 (D p ((X + p * Y) / 2)).2
      = p * uX (D p ((X + p * Y) / 2)).1 (D p ((X + p * Y) / 2)).2)
    (huX : 0 < uX (X / 2) (Y / 2)) :
    (D p ((X + p * Y) / 2)).1 = X / 2 ∧ (D p ((X + p * Y) / 2)).2 = Y / 2 ∧
      p = uY (X / 2) (Y / 2) / uX (X / 2) (Y / 2) := by
  have h1 : (D p ((X + p * Y) / 2)).1 = X / 2 := by linarith
  have h2 : (D p ((X + p * Y) / 2)).2 = Y / 2 := by linarith
  refine ⟨h1, h2, ?_⟩
  rw [h1, h2] at hfoc
  rw [eq_div_iff huX.ne', hfoc]

/-- The `k`-step conditional expectation `E_s[f(s_{t+k})]` for a Markov chain with transition
probabilities `P s s'` (used for Exercise 6(c), O&R p. 347). -/
noncomputable def iterExpect (P : S → S → ℝ) : ℕ → (S → ℝ) → S → ℝ
  | 0, f => f
  | k + 1, f => fun s => ∑ s', P s s' * iterExpect P k f s'

/-- Truncated present-value pricing, Exercise 6(a),(c), O&R p. 347 (cf. (56)–(58), (61)).
Let `m(s) = u_X(X(s)/2, Y(s)/2)` be marginal utility of good `X` at the equilibrium
allocation and `D` a dividend in units of `X` (`D = X` for Home's claim, `D = pY` for
Foreign's). If claim prices `V_N` (with `N` periods of dividends left, `V_0 = 0`) satisfy the
Euler equation `m(s)V_{N+1}(s) = βE_s[m(s′)(D(s′) + V_N(s′))]`, then
`m(s)V_N(s) = Σ_{k<N} β^{k+1} E_s[m(s_{t+k+1}) D(s_{t+k+1})]`. -/
theorem lucas_claim_price (P : S → S → ℝ) (β : ℝ) (m D : S → ℝ) (V : ℕ → S → ℝ)
    (hV0 : ∀ s, V 0 s = 0)
    (heuler : ∀ N s, m s * V (N + 1) s = β * ∑ s', P s s' * (m s' * (D s' + V N s'))) :
    ∀ N s, m s * V N s
      = ∑ k ∈ range N, β ^ (k + 1) * iterExpect P (k + 1) (fun s' => m s' * D s') s := by
  intro N
  induction N with
  | zero => intro s; simp [hV0]
  | succ N ih =>
    intro s
    rw [heuler, Finset.sum_range_succ']
    simp only [Finset.sum_add_distrib, ih, Finset.mul_sum, mul_add]
    rw [Finset.sum_comm, add_comm]
    congr 1
    · refine Finset.sum_congr rfl fun k _ => ?_
      simp only [iterExpect, Finset.mul_sum]
      refine Finset.sum_congr rfl fun s' _ => ?_
      ring_nf
    · simp [iterExpect, Finset.mul_sum]

/-- The infinite-horizon claim price as a limit, Exercise 6(c), O&R p. 347: if the discounted
expected dividends `β^{k+1}E_s[m D]` are summable with sum `L`, the truncated prices converge,
`m(s)V_N(s) → L`, so `V(s) = L/m(s)` is the expected present value. -/
theorem lucas_claim_price_limit (P : S → S → ℝ) (β : ℝ) (m D : S → ℝ) (V : ℕ → S → ℝ)
    (hV0 : ∀ s, V 0 s = 0)
    (heuler : ∀ N s, m s * V (N + 1) s = β * ∑ s', P s s' * (m s' * (D s' + V N s')))
    (s : S) {L : ℝ}
    (hL : HasSum (fun k => β ^ (k + 1) * iterExpect P (k + 1) (fun s' => m s' * D s') s) L) :
    Tendsto (fun N => m s * V N s) atTop (𝓝 L) := by
  have e : (fun N => m s * V N s)
      = fun N => ∑ k ∈ range N, β ^ (k + 1) * iterExpect P (k + 1) (fun s' => m s' * D s') s :=
    funext fun N => lucas_claim_price P β m D V hV0 heuler N s
  rw [e]
  exact hL.tendsto_sum_nat

/-- Riskless rates in the Lucas model, Exercise 6(d), O&R p. 347. A one-period claim paying
one unit of `X` has Euler equation `q m_X(s) = βE_s[m_X(s′)]`, so its price is
`βE_s[u_X(s′)]/u_X(s)`. A sure unit of `Y` next period is worth `βE_s[u_X(s′)p(s′)]` in `X`
utility; since `u_X p = u_Y` at the equilibrium, its price in units of current `Y`
(`p(s) = u_Y(s)/u_X(s)`) is `βE_s[u_Y(s′)]/u_Y(s)`, whose reciprocal is one plus the
own-rate of interest on `Y`. -/
theorem lucas_riskless_prices (P : S → S → ℝ) (β : ℝ) (mX mY p : S → ℝ) (s : S)
    (hmX : 0 < mX s) (hmY : 0 < mY s) (hp : ∀ s', p s' = mY s' / mX s')
    (hmX' : ∀ s', 0 < mX s') {qX qY : ℝ}
    (hqX : qX * mX s = β * ∑ s', P s s' * mX s')
    (hqY : qY * p s * mX s = β * ∑ s', P s s' * (mX s' * p s')) :
    qX = β * (∑ s', P s s' * mX s') / mX s ∧ qY = β * (∑ s', P s s' * mY s') / mY s := by
  refine ⟨by rw [eq_div_iff hmX.ne']; linarith, ?_⟩
  have e : ∀ s', mX s' * p s' = mY s' := fun s' => by
    rw [hp s']; field_simp [(hmX' s').ne']
  simp only [e] at hqY
  rw [hp s] at hqY
  rw [eq_div_iff hmY.ne']
  field_simp at hqY
  linarith

end ObstfeldRogoff.InternationalFinancialMarkets.OLGRiskSharing

set_option linter.style.longLine false
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.StateSpace
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.StateSpace.mk
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.StateSpace.prob
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.StateSpace.prob_nonneg
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.StateSpace.prob_sum
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.StateSpace.expect
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.StateSpace.expect_const
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.StateSpace.expect_add
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.StateSpace.cov
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.StateSpace.var
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.StateSpace.std
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.StateSpace.corr
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.StateSpace.expect_smul
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.StateSpace.expect_sub
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.StateSpace.expect_mono
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.StateSpace.expect_nonneg
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.StateSpace.expect_mul_eq
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.StateSpace.cov_comm
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.StateSpace.cov_const_add
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.StateSpace.cov_smul
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.StateSpace.cov_const
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.StateSpace.cov_eq_expect_centred
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.StateSpace.var_nonneg
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.StateSpace.var_affine
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.StateSpace.cov_sq_le
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.StateSpace.abs_cov_le
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.StateSpace.abs_corr_le_one
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.StateSpace.corr_affine
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.SmallCountry.adPayoff
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.SmallCountry.portfolioPayoff
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.SmallCountry.portfolioCost
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.SmallCountry.NoArbitrage
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.SmallCountry.portfolioPayoff_eq
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.SmallCountry.ad_span
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.SmallCountry.noArbitrage_iff
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.SmallCountry.bond_redundant
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.SmallCountry.budget_iff
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.SmallCountry.budget_pv_iff
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.SmallCountry.bond_euler
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.SmallCountry.mrs_eq_price
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.SmallCountry.mrs_ratio_eq_price_ratio
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.SmallCountry.supergradient_of_concaveOn
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.SmallCountry.lifetimeUtility
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.SmallCountry.foc_sufficient
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.SmallCountry.full_insurance_iff_fair
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.SmallCountry.full_insurance_iff_fair_ratio
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.SmallCountry.crra_log_ratio
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.SmallCountry.crra_arrow_pratt
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.SmallCountry.log_state_spending_eq
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.SmallCountry.log_consumption_demands
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.SmallCountry.log_current_account
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.SmallCountry.value_eq_expectation_iff
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.SmallCountry.value_eq_expectation_two_iff
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.SmallCountry.rCA_formula
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.SmallCountry.rA_formula
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.SmallCountry.current_account_eq_mul_rCA
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.SmallCountry.current_account_sign_iff
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.SmallCountry.current_account_sign_not_autarky_rate
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.SmallCountry.no_output_risk
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.SmallCountry.autarky_prices_log
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.SmallCountry.current_account_autarky_prices
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.SmallCountry.gross_flows_balanced
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.SmallCountry.exercise1_gross_purchases
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.SmallCountry.quadU
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.SmallCountry.quadLifetime
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.SmallCountry.quadCstar
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.SmallCountry.quad_expect
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.SmallCountry.quad_euler_iff
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.SmallCountry.quad_lifetime_eq
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.SmallCountry.quad_C2_at_optimum
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.SmallCountry.quad_feasible_iff
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.SmallCountry.quad_nonbinding
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.SmallCountry.quad_binding
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.SmallCountry.quad_complete_markets
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ComparativeAdvantage.bundleValue
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ComparativeAdvantage.continuous_bundleValue
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ComparativeAdvantage.LocallyNonsatiated
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ComparativeAdvantage.walras_law
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ComparativeAdvantage.revealed_preference
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ComparativeAdvantage.comparative_advantage
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ComparativeAdvantage.comparative_advantage_one_state
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ComparativeAdvantage.comparative_advantage_utility
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.TwoStageBudgeting.one_add_mul_le_rpow_of_neg
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.TwoStageBudgeting.rpow_le_tangent
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.TwoStageBudgeting.tangent_le_rpow_of_neg
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.TwoStageBudgeting.cesIndex
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.TwoStageBudgeting.priceIndex
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.TwoStageBudgeting.cesDemand
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.TwoStageBudgeting.univ_nonempty_of_stateSpace
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.TwoStageBudgeting.priceSum_pos
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.TwoStageBudgeting.priceIndex_pos
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.TwoStageBudgeting.demand_cost
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.TwoStageBudgeting.demand_foc
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.TwoStageBudgeting.cesIndex_demand
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.TwoStageBudgeting.cesIndex_le
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.TwoStageBudgeting.lifetime_le_two_stage
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.TwoStageBudgeting.priceIndex_le_one
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.TwoStageBudgeting.euler_27
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.TwoStageBudgeting.consumption_27
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.TwoStageBudgeting.current_account_sign_rCA
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.TwoStageBudgeting.consumption_vs_certainty
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.TwoStageBudgeting.consumption_sigma_one
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.TwoStageBudgeting.consumption_fair_prices
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.TwoStageBudgeting.current_account_fair_rate
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.GlobalEquilibrium.crra_euler_iff
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.GlobalEquilibrium.rpow_neg_inj
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.GlobalEquilibrium.GlobalEqm
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.GlobalEquilibrium.GlobalEqm.mk
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.GlobalEquilibrium.GlobalEqm.Ω
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.GlobalEquilibrium.GlobalEqm.β
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.GlobalEquilibrium.GlobalEqm.ρ
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.GlobalEquilibrium.GlobalEqm.r
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.GlobalEquilibrium.GlobalEqm.p
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.GlobalEquilibrium.GlobalEqm.Y1
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.GlobalEquilibrium.GlobalEqm.Y1f
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.GlobalEquilibrium.GlobalEqm.Y2
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.GlobalEquilibrium.GlobalEqm.Y2f
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.GlobalEquilibrium.GlobalEqm.C1
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.GlobalEquilibrium.GlobalEqm.C1f
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.GlobalEquilibrium.GlobalEqm.C2
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.GlobalEquilibrium.GlobalEqm.C2f
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.GlobalEquilibrium.GlobalEqm.prob_pos
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.GlobalEquilibrium.GlobalEqm.beta_pos
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.GlobalEquilibrium.GlobalEqm.rho_pos
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.GlobalEquilibrium.GlobalEqm.gross_pos
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.GlobalEquilibrium.GlobalEqm.C1_pos
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.GlobalEquilibrium.GlobalEqm.C1f_pos
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.GlobalEquilibrium.GlobalEqm.C2_pos
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.GlobalEquilibrium.GlobalEqm.C2f_pos
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.GlobalEquilibrium.GlobalEqm.euler
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.GlobalEquilibrium.GlobalEqm.euler_f
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.GlobalEquilibrium.GlobalEqm.clear1
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.GlobalEquilibrium.GlobalEqm.clear2
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.GlobalEquilibrium.GlobalEqm.price_sum
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.GlobalEquilibrium.GlobalEqm.budget
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.GlobalEquilibrium.GlobalEqm.worldY1
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.GlobalEquilibrium.GlobalEqm.worldY2
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.GlobalEquilibrium.GlobalEqm.worldY1_pos
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.GlobalEquilibrium.GlobalEqm.worldY2_pos
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.GlobalEquilibrium.GlobalEqm.growth_eq
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.GlobalEquilibrium.GlobalEqm.growth_eq_world
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.GlobalEquilibrium.GlobalEqm.ad_price
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.GlobalEquilibrium.GlobalEqm.price_expand
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.GlobalEquilibrium.GlobalEqm.price_ratio
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.GlobalEquilibrium.GlobalEqm.kernel_sum_pos
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.GlobalEquilibrium.GlobalEqm.normalisation
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.GlobalEquilibrium.GlobalEqm.price_formula
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.GlobalEquilibrium.GlobalEqm.interest_formula
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.GlobalEquilibrium.GlobalEqm.fair_iff_no_aggregate_risk
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.GlobalEquilibrium.GlobalEqm.share
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.GlobalEquilibrium.GlobalEqm.share_mem
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.GlobalEquilibrium.GlobalEqm.C1_eq
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.GlobalEquilibrium.GlobalEqm.C1f_eq
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.GlobalEquilibrium.GlobalEqm.C2_eq
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.GlobalEquilibrium.GlobalEqm.C2f_eq
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.GlobalEquilibrium.GlobalEqm.consumption_ratio_across_states
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.GlobalEquilibrium.GlobalEqm.ad_price_expand
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.GlobalEquilibrium.GlobalEqm.share_eq_wealth_share
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.GlobalEquilibrium.GlobalEqm.share_closed_form
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.GlobalEquilibrium.crraU
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.GlobalEquilibrium.pow_tangent
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.GlobalEquilibrium.crraU_le_tangent
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.GlobalEquilibrium.planner_pair_le
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.GlobalEquilibrium.plannerWeight
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.GlobalEquilibrium.plannerWeight_mem
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.GlobalEquilibrium.planner_foc
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.GlobalEquilibrium.socialWelfare
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.GlobalEquilibrium.socialWelfare_eq
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.GlobalEquilibrium.GlobalEqm.planner_optimal
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.GlobalEquilibrium.log_growth_relation
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.GlobalEquilibrium.corr_symm
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.GlobalEquilibrium.corr_growth_eq_one
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.GlobalEquilibrium.firmValue
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.GlobalEquilibrium.firmValue_hasDerivAt
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.GlobalEquilibrium.investment_foc
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.GlobalEquilibrium.investment_rate
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.GlobalEquilibrium.investment_euler
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.GlobalEquilibrium.log_investment_price
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.GlobalEquilibrium.log_linear_world_investment
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.GlobalEquilibrium.exercise2
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.GlobalEquilibrium.exercise2_indeterminate
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.Aggregation.euler_level_iff
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.Aggregation.perCapita
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.Aggregation.perCapita_affine
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.Aggregation.hara_aggregation
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.Aggregation.perCapita_budget
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.Aggregation.geoMean
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.Aggregation.harmonicMean
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.Aggregation.geometric_aggregation
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.Aggregation.logBondEuler
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.Aggregation.bonds_only_aggregation_fails
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.PortfolioDiversification.worldOut1
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.PortfolioDiversification.worldOut2
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.PortfolioDiversification.grossRate
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.PortfolioDiversification.adPrice
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.PortfolioDiversification.sharePrice
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.PortfolioDiversification.wealthShare
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.PortfolioDiversification.PortfolioEconomy
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.PortfolioDiversification.PortfolioEconomy.mk
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.PortfolioDiversification.PortfolioEconomy.Ω
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.PortfolioDiversification.PortfolioEconomy.β
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.PortfolioDiversification.PortfolioEconomy.ρ
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.PortfolioDiversification.PortfolioEconomy.Y1
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.PortfolioDiversification.PortfolioEconomy.Y2
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.PortfolioDiversification.PortfolioEconomy.nonempty
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.PortfolioDiversification.PortfolioEconomy.beta_pos
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.PortfolioDiversification.PortfolioEconomy.Y1_pos
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.PortfolioDiversification.PortfolioEconomy.Y2_pos
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.PortfolioDiversification.PortfolioEconomy.R
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.PortfolioDiversification.PortfolioEconomy.V
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.PortfolioDiversification.PortfolioEconomy.μ
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.PortfolioDiversification.PortfolioEconomy.C1
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.PortfolioDiversification.PortfolioEconomy.C2
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.PortfolioDiversification.PortfolioEconomy.x
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.PortfolioDiversification.PortfolioEconomy.worldOut1_pos
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.PortfolioDiversification.PortfolioEconomy.worldOut2_pos
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.PortfolioDiversification.PortfolioEconomy.V_nonneg
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.PortfolioDiversification.PortfolioEconomy.wealth_pos
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.PortfolioDiversification.PortfolioEconomy.μ_pos
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.PortfolioDiversification.PortfolioEconomy.sum_μ
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.PortfolioDiversification.PortfolioEconomy.V_mul
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.PortfolioDiversification.PortfolioEconomy.budget_date1
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.PortfolioDiversification.PortfolioEconomy.budget_date2
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.PortfolioDiversification.PortfolioEconomy.bond_euler
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.PortfolioDiversification.PortfolioEconomy.share_euler
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.PortfolioDiversification.PortfolioEconomy.market_clearing
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.PortfolioDiversification.PortfolioEconomy.V_eq_ad_value
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.PortfolioDiversification.PortfolioEconomy.ad_prices_normalised
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.PortfolioDiversification.PortfolioEconomy.ad_euler
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.PortfolioDiversification.PortfolioEconomy.ad_budget
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.PortfolioDiversification.PortfolioEconomy.logV
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.PortfolioDiversification.PortfolioEconomy.logC1
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.PortfolioDiversification.PortfolioEconomy.logC2
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.PortfolioDiversification.PortfolioEconomy.logX
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.PortfolioDiversification.PortfolioEconomy.logR
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.PortfolioDiversification.PortfolioEconomy.logV_sum
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.PortfolioDiversification.PortfolioEconomy.logV_eq_sharePrice
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.PortfolioDiversification.PortfolioEconomy.log_budgets
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.PortfolioDiversification.PortfolioEconomy.log_growth
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.PortfolioDiversification.PortfolioEconomy.log_eulers
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.PortfolioDiversification.PortfolioEconomy.log_clearing
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.PortfolioDiversification.PortfolioEconomy.logC1_eq_share
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.PortfolioDiversification.Exercise5.caraKernel
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.PortfolioDiversification.Exercise5.caraValue
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.PortfolioDiversification.Exercise5.caraRate
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.PortfolioDiversification.Exercise5.caraKernel_pos
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.PortfolioDiversification.Exercise5.cara_euler_iff
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.PortfolioDiversification.Exercise5.cara_share_euler
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.PortfolioDiversification.Exercise5.cara_bond_euler
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.PortfolioDiversification.Exercise5.exercise5a
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.PortfolioDiversification.Exercise5.exercise5a_gap
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.PortfolioDiversification.Exercise5.exercise5b
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.PortfolioDiversification.Exercise5.exercise5b_efficient
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.PortfolioDiversification.Exercise5.exercise5c_sharing
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.PortfolioDiversification.Exercise5.exercise5c_support
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.Spanning.spans_iff_rank
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.Spanning.rank_le_min
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.Spanning.card_le_of_spans
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.Spanning.not_spans_of_card_lt
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.Spanning.ad_security_replication
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.Spanning.spans_iff_isUnit_det
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.Spanning.card_le_not_sufficient
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.Spanning.LinearPricing
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.Spanning.value_of_payoff
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.Spanning.attainable_eq_budget
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.Spanning.pricing_unique
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.Spanning.bond_redundant
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.Spanning.returnMatrix
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.Spanning.returnMatrix_mulVec
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.Spanning.efficient_without_spanning
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.AssetPricing.price_eq_expect_sdf
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.AssetPricing.expect_sdf_eq_bond_price
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.AssetPricing.price_eq_discounted_mean_add_cov
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.AssetPricing.expect_gross_return_sub
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.AssetPricing.consumption_capm
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.AssetPricing.cov_add_const_right
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.AssetPricing.cov_sdf_return_incomplete
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.AssetPricing.investment_value_invariant
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.AssetPricing.investment_value_hasDerivAt
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.AssetPricing.hansen_jagannathan
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.AssetPricing.hansen_jagannathan_div
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.AssetPricing.equity_premium_linear_sdf
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.AssetPricing.cov_eq_corr_mul_std
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.AssetPricing.mankiw_zeldes_rho
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.AssetPricing.log_riskless_rate_lognormal
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.AssetPricing.riskless_rate_mehra_prescott
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.AssetPricing.lucasConsumption
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.AssetPricing.expect_lucas_rpow
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.AssetPricing.expect_lucas_consumption
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.AssetPricing.lucas_lifetime_utility
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.AssetPricing.lucas_certain_utility
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.AssetPricing.lucas_tau_simplifies
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.AssetPricing.lucas_tau_iff
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.AssetPricing.lucas_tau_bounds
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.AssetPricing.lucas_tau_numeric
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.AssetPricing.price_truncated
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.AssetPricing.price_eq_present_value
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.AssetPricing.crra_share_discount
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.AssetPricing.price_crra_world_output
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.AssetPricing.truncated_price_decomposition
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.Nontradables.efficiency_tradables
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.Nontradables.euler_nontradables_of_intratemporal
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.Nontradables.claim_price_any_country
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.Nontradables.claim_price_independent
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.Nontradables.efficiency_preference_shocks
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.Nontradables.additive_tradables_growth_equal
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.Nontradables.additive_tradables_growth_world
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.Nontradables.home_bias_equilibrium
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.Nontradables.cesInner
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.Nontradables.cesCrraUtility
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.Nontradables.cesMUT
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.Nontradables.cesMUN
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.Nontradables.cesInner_pos
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.Nontradables.hasDerivAt_cesCrra_T
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.Nontradables.hasDerivAt_cesCrra_N
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.Nontradables.cesCross
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.Nontradables.hasDerivAt_cesMUT_N
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.Nontradables.cesCross_sign
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.Nontradables.cesCrra_additive_of_theta_rho
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.Nontradables.theta_rho_of_cesCrra_additive
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.Nontradables.cesCrra_additive_iff
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.Nontradables.ces_relative_price
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.Nontradables.ces_revenue_strictMono_iff
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.Nontradables.ces_loglinear_exact
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.Nontradables.cdRelPrice
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.Nontradables.cd_marginal_utilities
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.Nontradables.cd_revenue
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.Nontradables.cd_payoff_corr_one
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.EventTree.Tree
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.EventTree.Tree.mk
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.EventTree.Tree.q
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.EventTree.Tree.q_nonneg
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.EventTree.Tree.q_sum
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.EventTree.restr
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.EventTree.Tree.step
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.EventTree.Tree.condProb
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.EventTree.Tree.histProb
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.EventTree.Tree.step_nonneg
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.EventTree.Tree.histProb_nonneg
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.EventTree.Tree.step_snoc_lt
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.EventTree.Tree.step_snoc_last
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.EventTree.Tree.histProb_sum_eq_one
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.EventTree.Tree.step_restr
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.EventTree.Tree.condProb_chain
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.EventTree.Tree.bayes_rule
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.EventTree.Tree.histProb_div_date2
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.EventTree.Tree.histProb_restr_one
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.EventTree.Tree.condProb_nonneg
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.EventTree.log_tangent
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.EventTree.foc_plan_optimal
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.EventTree.arrowDebreu_plan_optimal
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.EventTree.euler_bond
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.EventTree.foc_ratio
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.EventTree.crraMass
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.EventTree.crraR
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.EventTree.crraPrice
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.EventTree.crraMass_pos
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.EventTree.crraPrice_sum
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.EventTree.crra_foc
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.EventTree.presentValue
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.EventTree.budget_of_share
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.EventTree.crra_constant_share
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.EventTree.crra_interest_factor
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.EventTree.foc_date2_ratio
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.EventTree.foc_date2
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.EventTree.dynamic_consistency
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.EventTree.log_share_iff
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.EventTree.share_formula_iff
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.EventTree.crra_share_recursion
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.EventTree.crra_iid_share
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.EventTree.crra_iid_share_log
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.OLGRiskSharing.cohortShare
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.OLGRiskSharing.cohortGrossRate
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.OLGRiskSharing.cohortPrice
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.OLGRiskSharing.expected_inverse_pos
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.OLGRiskSharing.cohortPrice_sum
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.OLGRiskSharing.cohortShare_add
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.OLGRiskSharing.cohort_prices_symm
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.OLGRiskSharing.cohort_equilibrium
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.OLGRiskSharing.young_plan_optimal
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.OLGRiskSharing.cohort_equilibrium_unique
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.OLGRiskSharing.aggregate_consumption
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.OLGRiskSharing.cohortShare_half
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.OLGRiskSharing.lucas_allocation
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.OLGRiskSharing.iterExpect
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.OLGRiskSharing.lucas_claim_price
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.OLGRiskSharing.lucas_claim_price_limit
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.OLGRiskSharing.lucas_riskless_prices
