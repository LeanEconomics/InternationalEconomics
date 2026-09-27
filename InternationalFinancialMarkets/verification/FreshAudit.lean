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
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
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
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.Calculus.Deriv.Pow
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
* necessity of (5)–(6) at any optimum interior to an open consumption domain `D` (e.g.
  `(0, ∞)`) at which `u` is differentiable, with no concavity: for the book's problem in the
  AD holdings `B₂` and for plans under both the equality and the `≤` form of the budget (4),
  by a one-dimensional perturbation along the budget line; (6), (8) and (9) follow as
  corollaries of optimality; under the `≤` form the budget binds when `u′(C₁) ≠ 0`; and, for
  concave differentiable `u`, iff characterisations of the optimum by (5) (plus a binding
  budget in the `≤` form with `u′ > 0`);
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

/-! ## Necessity of the first-order conditions (§5.1.4, pp. 275–277)

A consumption plan is a pair `(C₁, C₂(·))`. Consumption is restricted to an open set `D`
(for instance `D = (0, ∞)`, the domain of CRRA or log utility), so the optimum is interior and
corner solutions are excluded by hypothesis rather than by assumption on `u`. -/

/-- Expected lifetime utility of a consumption plan, O&R (1), p. 273:
`u(C₁) + Σ π(s)βu(C₂(s))`. -/
noncomputable def planUtility (Ω : StateSpace S) (u : ℝ → ℝ) (β C1 : ℝ) (C2 : S → ℝ) : ℝ :=
  u C1 + ∑ s, Ω.prob s * β * u (C2 s)

/-- The date-1 present value of a consumption plan at AD prices, the left-hand side of O&R (4),
p. 275: `C₁ + Σ p(s)C₂(s)/(1+r)`. The budget constraint (4) is
`planValue p r C₁ C₂ = planValue p r Y₁ Y₂`. -/
noncomputable def planValue (p : S → ℝ) (r C1 : ℝ) (C2 : S → ℝ) : ℝ :=
  C1 + ∑ s, p s / (1 + r) * C2 s

/-- Optimality of a plan along its budget line, O&R §5.1.4, p. 276: `(C₁, C₂)` (with
consumption in `D`) does at least as well as every plan with consumption in `D` and the same
present value (4). Both forms of the budget constraint (equality and `≤`) and the book's
unconstrained problem in `B₂` imply it (see `isPlanOptimum_of_budget_eq`,
`isPlanOptimum_of_budget_le`, `isPlanOptimum_of_lifetime`). -/
def IsPlanOptimum (Ω : StateSpace S) (D : Set ℝ) (u : ℝ → ℝ) (p : S → ℝ) (r β C1 : ℝ)
    (C2 : S → ℝ) : Prop :=
  ∀ (C1' : ℝ) (C2' : S → ℝ), C1' ∈ D → (∀ s, C2' s ∈ D) →
    planValue p r C1' C2' = planValue p r C1 C2 →
      planUtility Ω u β C1' C2' ≤ planUtility Ω u β C1 C2

/-- The book's objective in terms of asset holdings is the plan objective, O&R p. 276:
`U₁(B₂) = u(C₁) + Σ π(s)βu(C₂(s))` with `C₁ = Y₁ − Σ p(s)B₂(s)/(1+r)`, `C₂ = Y₂ + B₂`. -/
theorem lifetimeUtility_eq_planUtility (Ω : StateSpace S) (u : ℝ → ℝ) (p : S → ℝ)
    (r β Y1 : ℝ) (Y2 B : S → ℝ) :
    lifetimeUtility Ω u p r β Y1 Y2 B =
      planUtility Ω u β (Y1 - ∑ s, p s / (1 + r) * B s) (fun s => Y2 s + B s) := rfl

/-- The plan financed by AD holdings `B₂` satisfies the budget constraint (4), O&R p. 275:
its present value equals that of the endowment. -/
theorem planValue_of_holdings (p : S → ℝ) (r Y1 : ℝ) (Y2 B : S → ℝ) :
    planValue p r (Y1 - ∑ s, p s / (1 + r) * B s) (fun s => Y2 s + B s) =
      planValue p r Y1 Y2 := by
  simp only [planValue, mul_add, Finset.sum_add_distrib]
  ring

/-- The equality form of the budget constraint (4)/(18), O&R p. 275: if `(C₁, C₂)` satisfies
(4) and maximises expected utility over all plans in `D` satisfying (4), it is a plan
optimum. -/
theorem isPlanOptimum_of_budget_eq (Ω : StateSpace S) {D : Set ℝ} {u : ℝ → ℝ} (p : S → ℝ)
    (r β Y1 C1 : ℝ) (Y2 C2 : S → ℝ) (hbud : planValue p r C1 C2 = planValue p r Y1 Y2)
    (hmax : ∀ (C1' : ℝ) (C2' : S → ℝ), C1' ∈ D → (∀ s, C2' s ∈ D) →
      planValue p r C1' C2' = planValue p r Y1 Y2 →
        planUtility Ω u β C1' C2' ≤ planUtility Ω u β C1 C2) :
    IsPlanOptimum Ω D u p r β C1 C2 :=
  fun C1' C2' h1 h2 hv => hmax C1' C2' h1 h2 (hv.trans hbud)

/-- The `≤` form of the budget constraint (4), O&R p. 275: if `(C₁, C₂)` satisfies
`planValue ≤ planValue(Y₁, Y₂)` and maximises expected utility over all plans in `D` doing
so, it is a plan optimum (whether or not its budget binds). -/
theorem isPlanOptimum_of_budget_le (Ω : StateSpace S) {D : Set ℝ} {u : ℝ → ℝ} (p : S → ℝ)
    (r β Y1 C1 : ℝ) (Y2 C2 : S → ℝ) (hbud : planValue p r C1 C2 ≤ planValue p r Y1 Y2)
    (hmax : ∀ (C1' : ℝ) (C2' : S → ℝ), C1' ∈ D → (∀ s, C2' s ∈ D) →
      planValue p r C1' C2' ≤ planValue p r Y1 Y2 →
        planUtility Ω u β C1' C2' ≤ planUtility Ω u β C1 C2) :
    IsPlanOptimum Ω D u p r β C1 C2 :=
  fun C1' C2' h1 h2 hv => hmax C1' C2' h1 h2 (hv.trans_le hbud)

/-- The book's unconstrained problem in the AD holdings, O&R p. 276: if `B₂` maximises
`U₁(B₂) = u(Y₁ − Σ p(s)B₂(s)/(1+r)) + Σ π(s)βu(Y₂(s) + B₂(s))` over all holdings whose
consumption stays in `D`, the plan it finances is a plan optimum. -/
theorem isPlanOptimum_of_lifetime (Ω : StateSpace S) {D : Set ℝ} {u : ℝ → ℝ} (p : S → ℝ)
    (r β Y1 : ℝ) (Y2 B : S → ℝ)
    (hmax : ∀ B' : S → ℝ, Y1 - ∑ s, p s / (1 + r) * B' s ∈ D → (∀ s, Y2 s + B' s ∈ D) →
      lifetimeUtility Ω u p r β Y1 Y2 B' ≤ lifetimeUtility Ω u p r β Y1 Y2 B) :
    IsPlanOptimum Ω D u p r β (Y1 - ∑ s, p s / (1 + r) * B s) (fun s => Y2 s + B s) := by
  intro C1' C2' h1 h2 hv
  rw [planValue_of_holdings] at hv
  have hC1' : Y1 - ∑ s, p s / (1 + r) * (C2' s - Y2 s) = C1' := by
    simp only [planValue, mul_sub, Finset.sum_sub_distrib] at hv ⊢
    linarith
  have hC2' : (fun s => Y2 s + (C2' s - Y2 s)) = C2' := funext fun s => by ring
  have h := hmax (fun s => C2' s - Y2 s) (by rw [hC1']; exact h1)
    (fun s => by simpa using h2 s)
  rw [lifetimeUtility_eq_planUtility, lifetimeUtility_eq_planUtility, hC1', hC2'] at h
  exact h

/-- Necessity of the first-order conditions (5)–(6), O&R pp. 276–277: if `(C₁, C₂)` is a plan
optimum with consumption in an open set `D`, and `u` has derivative `du x` at `C₁` and at every
`C₂(s)`, then for every state `s`, `p(s)u′(C₁)/(1+r) = π(s)βu′(C₂(s))`. No concavity is used.
Proof: the one-dimensional perturbation `C₁ − p(s)t/(1+r)`, `C₂(s) + t` stays on the budget
line and in `D` for small `t`, so `t = 0` is a local maximum of expected utility along it and
its derivative `−p(s)u′(C₁)/(1+r) + π(s)βu′(C₂(s))` vanishes. -/
theorem foc_of_isPlanOptimum (Ω : StateSpace S) {D : Set ℝ} (hD : IsOpen D) {u du : ℝ → ℝ}
    (p : S → ℝ) {r β C1 : ℝ} {C2 : S → ℝ} (hC1 : C1 ∈ D) (hC2 : ∀ s, C2 s ∈ D)
    (hu1 : HasDerivAt u (du C1) C1) (hu2 : ∀ s, HasDerivAt u (du (C2 s)) (C2 s))
    (hopt : IsPlanOptimum Ω D u p r β C1 C2) (s : S) :
    p s / (1 + r) * du C1 = Ω.prob s * β * du (C2 s) := by
  classical
  set q := p s / (1 + r) with hq
  set e : S → ℝ := fun s' => if s' = s then 1 else 0 with he
  set g : ℝ → ℝ := fun t => planUtility Ω u β (C1 - q * t) (fun s' => C2 s' + t * e s')
    with hg
  have hloc : IsLocalMax g 0 := by
    have h1 : ∀ᶠ t in nhds (0 : ℝ), C1 - q * t ∈ D := by
      have hc : Continuous (fun t : ℝ => C1 - q * t) := by fun_prop
      exact hc.continuousAt.preimage_mem_nhds (by simpa using hD.mem_nhds hC1)
    have h2 : ∀ᶠ t in nhds (0 : ℝ), C2 s + t ∈ D := by
      have hc : Continuous (fun t : ℝ => C2 s + t) := by fun_prop
      exact hc.continuousAt.preimage_mem_nhds (by simpa using hD.mem_nhds (hC2 s))
    filter_upwards [h1, h2] with t ht1 ht2
    have hg0 : g 0 = planUtility Ω u β C1 C2 := by simp [hg]
    rw [hg0]
    refine hopt _ _ ht1 (fun s' => ?_) ?_
    · by_cases hs : s' = s
      · subst hs; simpa [he] using ht2
      · simpa [he, hs] using hC2 s'
    · simp only [planValue, mul_add, Finset.sum_add_distrib, he, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      ring
  have hderiv : HasDerivAt g
      (du C1 * (-q) + ∑ s', Ω.prob s' * β * (du (C2 s') * e s')) 0 := by
    have hin : HasDerivAt (fun t : ℝ => C1 - q * t) (-q) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).const_mul q).const_sub C1
    have hu1' : HasDerivAt u (du C1) (C1 - q * 0) := by simpa using hu1
    have hA : HasDerivAt (fun t => u (C1 - q * t)) (du C1 * (-q)) 0 := hu1'.comp 0 hin
    have hB : ∀ s' ∈ Finset.univ, HasDerivAt (fun t => Ω.prob s' * β * u (C2 s' + t * e s'))
        (Ω.prob s' * β * (du (C2 s') * e s')) 0 := by
      intro s' _
      have hin' : HasDerivAt (fun t : ℝ => C2 s' + t * e s') (e s') 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (e s')).const_add (C2 s')
      have hu2' : HasDerivAt u (du (C2 s')) (C2 s' + 0 * e s') := by simpa using hu2 s'
      exact (hu2'.comp 0 hin').const_mul _
    exact hA.add (HasDerivAt.fun_sum hB)
  have h0 := hloc.hasDerivAt_eq_zero hderiv
  simp only [he, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true] at h0
  linarith

/-- Necessity of the first-order conditions (5), O&R p. 276, in the book's own form (the FOC
in `B₂(s)`): if the AD holdings `B₂` maximise `U₁(B₂)` over all holdings with consumption in
the open set `D`, and `u` is differentiable at `C₁` and every `C₂(s)`, then (5) holds in every
state. -/
theorem foc_necessary (Ω : StateSpace S) {D : Set ℝ} (hD : IsOpen D) {u du : ℝ → ℝ}
    (p : S → ℝ) (r β Y1 : ℝ) (Y2 B : S → ℝ)
    (hC1 : Y1 - ∑ s, p s / (1 + r) * B s ∈ D) (hC2 : ∀ s, Y2 s + B s ∈ D)
    (hu1 : HasDerivAt u (du (Y1 - ∑ s, p s / (1 + r) * B s))
      (Y1 - ∑ s, p s / (1 + r) * B s))
    (hu2 : ∀ s, HasDerivAt u (du (Y2 s + B s)) (Y2 s + B s))
    (hmax : ∀ B' : S → ℝ, Y1 - ∑ s, p s / (1 + r) * B' s ∈ D → (∀ s, Y2 s + B' s ∈ D) →
      lifetimeUtility Ω u p r β Y1 Y2 B' ≤ lifetimeUtility Ω u p r β Y1 Y2 B) (s : S) :
    p s / (1 + r) * du (Y1 - ∑ s, p s / (1 + r) * B s) = Ω.prob s * β * du (Y2 s + B s) :=
  foc_of_isPlanOptimum Ω hD p (C2 := fun s => Y2 s + B s) hC1 hC2 hu1 hu2
    (isPlanOptimum_of_lifetime Ω p r β Y1 Y2 B hmax) s

/-- Necessity of (5) on the positive orthant, O&R pp. 275–277: with consumption restricted to
`(0, ∞)` (the domain of CRRA and log utility) and the equality budget (4), an optimum with
`C₁ > 0`, `C₂ > 0` at which `u` is differentiable satisfies (5) in every state. -/
theorem foc_necessary_pos (Ω : StateSpace S) {u du : ℝ → ℝ} (p : S → ℝ) (r β Y1 C1 : ℝ)
    (Y2 C2 : S → ℝ) (hC1 : 0 < C1) (hC2 : ∀ s, 0 < C2 s)
    (hu1 : HasDerivAt u (du C1) C1) (hu2 : ∀ s, HasDerivAt u (du (C2 s)) (C2 s))
    (hbud : planValue p r C1 C2 = planValue p r Y1 Y2)
    (hmax : ∀ (C1' : ℝ) (C2' : S → ℝ), 0 < C1' → (∀ s, 0 < C2' s) →
      planValue p r C1' C2' = planValue p r Y1 Y2 →
        planUtility Ω u β C1' C2' ≤ planUtility Ω u β C1 C2) (s : S) :
    p s / (1 + r) * du C1 = Ω.prob s * β * du (C2 s) :=
  foc_of_isPlanOptimum Ω isOpen_Ioi p hC1 hC2 hu1 hu2
    (isPlanOptimum_of_budget_eq Ω (D := Set.Ioi 0) p r β Y1 C1 Y2 C2 hbud
      fun C1' C2' h1 h2 hv => hmax C1' C2' h1 h2 hv) s

/-- O&R (6), p. 276, as a consequence of optimality: at a plan optimum in an open `D` with
`u` differentiable at the plan and `u′(C₁) ≠ 0`, the marginal rate of substitution equals the
relative price, `π(s)βu′(C₂(s))/u′(C₁) = p(s)/(1+r)`. -/
theorem mrs_eq_price_of_optimum (Ω : StateSpace S) {D : Set ℝ} (hD : IsOpen D)
    {u du : ℝ → ℝ} (p : S → ℝ) {r β C1 : ℝ} {C2 : S → ℝ} (hC1 : C1 ∈ D)
    (hC2 : ∀ s, C2 s ∈ D) (hu1 : HasDerivAt u (du C1) C1)
    (hu2 : ∀ s, HasDerivAt u (du (C2 s)) (C2 s)) (hopt : IsPlanOptimum Ω D u p r β C1 C2)
    (hd : du C1 ≠ 0) (s : S) :
    Ω.prob s * β * du (C2 s) / du C1 = p s / (1 + r) :=
  mrs_eq_price Ω p r β du C1 C2 hd (foc_of_isPlanOptimum Ω hD p hC1 hC2 hu1 hu2 hopt) s

/-- The stochastic Euler equation for bonds (8), O&R p. 277, as a consequence of optimality:
at a plan optimum in an open `D` with `u` differentiable at the plan, `Σ p(s) = 1` (O&R (7))
and `1 + r ≠ 0`, `u′(C₁) = (1+r)βE[u′(C₂)]`. -/
theorem bond_euler_of_optimum (Ω : StateSpace S) {D : Set ℝ} (hD : IsOpen D)
    {u du : ℝ → ℝ} (p : S → ℝ) {r β C1 : ℝ} {C2 : S → ℝ} (hr : 1 + r ≠ 0)
    (hsum : ∑ s, p s = 1) (hC1 : C1 ∈ D) (hC2 : ∀ s, C2 s ∈ D)
    (hu1 : HasDerivAt u (du C1) C1) (hu2 : ∀ s, HasDerivAt u (du (C2 s)) (C2 s))
    (hopt : IsPlanOptimum Ω D u p r β C1 C2) :
    du C1 = (1 + r) * β * Ω.expect (fun s => du (C2 s)) :=
  bond_euler Ω p hr hsum β du C1 C2 (foc_of_isPlanOptimum Ω hD p hC1 hC2 hu1 hu2 hopt)

/-- The across-state condition (9), O&R p. 277, as a consequence of optimality: at a plan
optimum in an open `D` with `u` differentiable at the plan, `1 + r ≠ 0`, `β ≠ 0` and
`u′(C₁) ≠ 0`, `π(s)u′(C₂(s))/[π(t)u′(C₂(t))] = p(s)/p(t)`. -/
theorem mrs_ratio_of_optimum (Ω : StateSpace S) {D : Set ℝ} (hD : IsOpen D)
    {u du : ℝ → ℝ} (p : S → ℝ) {r β C1 : ℝ} {C2 : S → ℝ} (hr : 1 + r ≠ 0) (hβ : β ≠ 0)
    (hC1 : C1 ∈ D) (hC2 : ∀ s, C2 s ∈ D) (hu1 : HasDerivAt u (du C1) C1)
    (hu2 : ∀ s, HasDerivAt u (du (C2 s)) (C2 s)) (hopt : IsPlanOptimum Ω D u p r β C1 C2)
    (hd : du C1 ≠ 0) (s t : S) :
    Ω.prob s * du (C2 s) / (Ω.prob t * du (C2 t)) = p s / p t :=
  mrs_ratio_eq_price_ratio Ω p hr hβ du C1 C2 hd
    (foc_of_isPlanOptimum Ω hD p hC1 hC2 hu1 hu2 hopt) s t

/-- The budget binds at an optimum when date-1 marginal utility is nonzero, O&R p. 275
(implicit): under the `≤` form of (4), if `(C₁, C₂)` is optimal among plans in the open set
`D`, `u` is differentiable at `C₁` and `u′(C₁) ≠ 0`, then (4) holds with equality. Proof: with
slack, `C₁ + t` is feasible for small `t` of either sign, forcing `u′(C₁) = 0`. -/
theorem budget_binds_of_optimum (Ω : StateSpace S) {D : Set ℝ} (hD : IsOpen D)
    {u du : ℝ → ℝ} (p : S → ℝ) (r β Y1 C1 : ℝ) (Y2 C2 : S → ℝ) (hC1 : C1 ∈ D)
    (hC2 : ∀ s, C2 s ∈ D) (hu1 : HasDerivAt u (du C1) C1)
    (hbud : planValue p r C1 C2 ≤ planValue p r Y1 Y2)
    (hmax : ∀ (C1' : ℝ) (C2' : S → ℝ), C1' ∈ D → (∀ s, C2' s ∈ D) →
      planValue p r C1' C2' ≤ planValue p r Y1 Y2 →
        planUtility Ω u β C1' C2' ≤ planUtility Ω u β C1 C2)
    (hd : du C1 ≠ 0) :
    planValue p r C1 C2 = planValue p r Y1 Y2 := by
  by_contra hne
  have hlt : planValue p r C1 C2 < planValue p r Y1 Y2 := lt_of_le_of_ne hbud hne
  set g : ℝ → ℝ := fun t => planUtility Ω u β (C1 + t) C2 with hg
  have hloc : IsLocalMax g 0 := by
    have h1 : ∀ᶠ t in nhds (0 : ℝ), C1 + t ∈ D := by
      have hc : Continuous (fun t : ℝ => C1 + t) := by fun_prop
      exact hc.continuousAt.preimage_mem_nhds (by simpa using hD.mem_nhds hC1)
    filter_upwards [h1, eventually_lt_nhds (sub_pos.mpr hlt)] with t ht1 ht2
    have hg0 : g 0 = planUtility Ω u β C1 C2 := by simp [hg]
    rw [hg0]
    refine hmax _ _ ht1 hC2 ?_
    simp only [planValue] at ht2 ⊢
    linarith
  have hderiv : HasDerivAt g (du C1) 0 := by
    have hin : HasDerivAt (fun t : ℝ => C1 + t) 1 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_add C1
    have hu1' : HasDerivAt u (du C1) (C1 + 0) := by simpa using hu1
    have hA := (hu1'.comp 0 hin).add_const (∑ s, Ω.prob s * β * u (C2 s))
    rw [mul_one] at hA
    exact hA
  exact hd (hloc.hasDerivAt_eq_zero hderiv)

/-- The concave-tangent bound for plans (used for sufficiency of (5), O&R p. 276): if `u` is
concave on `D` with derivative `du x` at every `x ∈ D`, `β ≥ 0`, every `π(s) ≥ 0`, and
`(C₁, C₂)` in `D` satisfies (5), then for every plan `(C₁′, C₂′)` in `D`,
`U(C₁′, C₂′) ≤ U(C₁, C₂) + u′(C₁)·[PV(C₁′, C₂′) − PV(C₁, C₂)]`. -/
theorem planUtility_le_of_foc (Ω : StateSpace S) {D : Set ℝ} {u du : ℝ → ℝ}
    (hconc : ConcaveOn ℝ D u) (hu : ∀ x ∈ D, HasDerivAt u (du x) x) (p : S → ℝ)
    {r β : ℝ} (hβ : 0 ≤ β) {C1 C1' : ℝ} {C2 C2' : S → ℝ} (hC1 : C1 ∈ D)
    (hC2 : ∀ s, C2 s ∈ D) (hC1' : C1' ∈ D) (hC2' : ∀ s, C2' s ∈ D)
    (hfoc : ∀ s, p s / (1 + r) * du C1 = Ω.prob s * β * du (C2 s)) :
    planUtility Ω u β C1' C2' ≤
      planUtility Ω u β C1 C2 + du C1 * (planValue p r C1' C2' - planValue p r C1 C2) := by
  have h1 := supergradient_of_concaveOn hconc hC1 hC1' (hu C1 hC1)
  have h2 : ∀ s, Ω.prob s * β * u (C2' s) ≤
      Ω.prob s * β * u (C2 s) + p s / (1 + r) * du C1 * (C2' s - C2 s) := fun s => by
    have := supergradient_of_concaveOn hconc (hC2 s) (hC2' s) (hu _ (hC2 s))
    rw [hfoc s]
    have hk := mul_le_mul_of_nonneg_left this (mul_nonneg (Ω.prob_nonneg s) hβ)
    linarith
  have hsum := Finset.sum_le_sum fun s (_ : s ∈ Finset.univ) => h2 s
  rw [Finset.sum_add_distrib] at hsum
  have e : ∑ s, p s / (1 + r) * du C1 * (C2' s - C2 s) =
      du C1 * (∑ s, p s / (1 + r) * C2' s - ∑ s, p s / (1 + r) * C2 s) := by
    rw [mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun s _ => by ring
  simp only [planUtility, planValue]
  rw [e] at hsum
  nlinarith

/-- Characterisation of the optimum under the equality budget (4)/(18), O&R pp. 275–277: for
`u` concave on an open set `D` and differentiable there, `β ≥ 0`, and a
plan `(C₁, C₂)` in `D` satisfying (4), the plan maximises expected utility over all plans in
`D` satisfying (4) iff the first-order conditions (5) hold in every state. -/
theorem optimum_iff_foc_budget_eq (Ω : StateSpace S) {D : Set ℝ} (hD : IsOpen D)
    {u du : ℝ → ℝ} (hconc : ConcaveOn ℝ D u) (hu : ∀ x ∈ D, HasDerivAt u (du x) x)
    (p : S → ℝ) {r β : ℝ} (hβ : 0 ≤ β) (Y1 C1 : ℝ) (Y2 C2 : S → ℝ) (hC1 : C1 ∈ D)
    (hC2 : ∀ s, C2 s ∈ D) (hbud : planValue p r C1 C2 = planValue p r Y1 Y2) :
    (∀ (C1' : ℝ) (C2' : S → ℝ), C1' ∈ D → (∀ s, C2' s ∈ D) →
      planValue p r C1' C2' = planValue p r Y1 Y2 →
        planUtility Ω u β C1' C2' ≤ planUtility Ω u β C1 C2) ↔
      ∀ s, p s / (1 + r) * du C1 = Ω.prob s * β * du (C2 s) := by
  constructor
  · intro hmax
    exact foc_of_isPlanOptimum Ω hD p hC1 hC2 (hu C1 hC1) (fun s => hu _ (hC2 s))
      (isPlanOptimum_of_budget_eq Ω p r β Y1 C1 Y2 C2 hbud hmax)
  · intro hfoc C1' C2' h1 h2 hv
    have := planUtility_le_of_foc Ω hconc hu p hβ hC1 hC2 h1 h2 hfoc
    rw [hv, hbud, sub_self, mul_zero, add_zero] at this
    exact this

/-- Characterisation of the optimum under the `≤` budget, O&R pp. 275–277: for `u` concave and
differentiable on an open set `D` with `u′ > 0` on `D` (more is preferred), `β ≥ 0`, and a
plan `(C₁, C₂)` in `D` with `PV ≤ PV(Y₁, Y₂)`, the plan maximises expected utility over all
plans in `D` with `PV ≤ PV(Y₁, Y₂)` iff the budget (4) binds and (5) holds in every state. -/
theorem optimum_iff_foc_budget_le (Ω : StateSpace S) {D : Set ℝ} (hD : IsOpen D)
    {u du : ℝ → ℝ} (hconc : ConcaveOn ℝ D u) (hu : ∀ x ∈ D, HasDerivAt u (du x) x)
    (hdpos : ∀ x ∈ D, 0 < du x) (p : S → ℝ) {r β : ℝ} (hβ : 0 ≤ β) (Y1 C1 : ℝ)
    (Y2 C2 : S → ℝ) (hC1 : C1 ∈ D) (hC2 : ∀ s, C2 s ∈ D)
    (hbud : planValue p r C1 C2 ≤ planValue p r Y1 Y2) :
    (∀ (C1' : ℝ) (C2' : S → ℝ), C1' ∈ D → (∀ s, C2' s ∈ D) →
      planValue p r C1' C2' ≤ planValue p r Y1 Y2 →
        planUtility Ω u β C1' C2' ≤ planUtility Ω u β C1 C2) ↔
      planValue p r C1 C2 = planValue p r Y1 Y2 ∧
        ∀ s, p s / (1 + r) * du C1 = Ω.prob s * β * du (C2 s) := by
  constructor
  · intro hmax
    exact ⟨budget_binds_of_optimum Ω hD p r β Y1 C1 Y2 C2 hC1 hC2 (hu C1 hC1) hbud hmax
        (hdpos C1 hC1).ne',
      foc_of_isPlanOptimum Ω hD p hC1 hC2 (hu C1 hC1) (fun s => hu _ (hC2 s))
        (isPlanOptimum_of_budget_le Ω p r β Y1 C1 Y2 C2 hbud hmax)⟩
  · rintro ⟨heq, hfoc⟩ C1' C2' h1 h2 hv
    have := planUtility_le_of_foc Ω hconc hu p hβ hC1 hC2 h1 h2 hfoc
    have hneg : du C1 * (planValue p r C1' C2' - planValue p r C1 C2) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (hdpos C1 hC1).le (by rw [heq]; linarith)
    linarith

/-- Characterisation of the optimum in the book's problem in `B₂`, O&R p. 276: for `u` concave
and differentiable on an open set `D`, `β ≥ 0`, and holdings `B₂` with consumption in `D`, the
holdings maximise `U₁` over all holdings with consumption in `D` iff the first-order
conditions (5) hold in every state (necessity: `foc_necessary`; sufficiency:
`foc_sufficient`). -/
theorem foc_iff (Ω : StateSpace S) {D : Set ℝ} (hD : IsOpen D) {u du : ℝ → ℝ}
    (hconc : ConcaveOn ℝ D u) (hu : ∀ x ∈ D, HasDerivAt u (du x) x) (p : S → ℝ)
    {r β : ℝ} (hβ : 0 ≤ β) (Y1 : ℝ) (Y2 B : S → ℝ)
    (hC1 : Y1 - ∑ s, p s / (1 + r) * B s ∈ D) (hC2 : ∀ s, Y2 s + B s ∈ D) :
    (∀ B' : S → ℝ, Y1 - ∑ s, p s / (1 + r) * B' s ∈ D → (∀ s, Y2 s + B' s ∈ D) →
      lifetimeUtility Ω u p r β Y1 Y2 B' ≤ lifetimeUtility Ω u p r β Y1 Y2 B) ↔
      ∀ s, p s / (1 + r) * du (Y1 - ∑ s, p s / (1 + r) * B s) =
        Ω.prob s * β * du (Y2 s + B s) := by
  constructor
  · intro hmax
    exact foc_necessary Ω hD p r β Y1 Y2 B hC1 hC2 (hu _ hC1) (fun s => hu _ (hC2 s)) hmax
  · intro hfoc B' h1 h2
    exact foc_sufficient Ω hconc hu p hβ Y1 Y2 B B' hC1 hC2 h1 h2 hfoc

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
pp. 282–285, including footnotes 13 and 14.

Lifetime utility is `u(C₁) + βu(Ω(C₂))` (O&R (20)) with the CES certainty equivalent
`Ω(C₂) = [Σ π(s)C₂(s)^{1−ρ}]^{1/(1−ρ)}` (O&R (23)), `0 < ρ ≠ 1`, or its log limit (the
geometric mean `exp(Σ π(s) log C₂(s))`) at `ρ = 1` (footnote 13). Date-1 prices of state
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
  `β(1+r) = 1` and `Y₁ = Σ p(s)Y₂(s)`, `CA₁ > 0` when `σ > 1` and `CA₁ < 0` when `σ < 1`;
* stage 2 at `ρ = 1` (demands `π(s)Z₂/p(s)`, `P = exp(Σ π(s) log(p(s)/π(s)))`), so that
  stage 2 holds for every `ρ > 0`;
* stage 1 in full for isoelastic `u(C) = C^{1−1/σ}/(1 − 1/σ)` (log at `σ = 1`): the consumption
  function maximises (21) subject to (22) (sufficiency, by concavity), strictly, so any
  maximiser equals it (necessity and uniqueness); a feasible point is optimal iff it satisfies
  (27), iff it satisfies the Euler equation;
* two-stage budgeting solves (20): the two-stage plan maximises `u(C₁) + βu(Ω(C₂))` over all
  positive state-contingent plans on the budget line and is the unique maximiser, for any
  index with the stage-2 properties;
* the Epstein–Zin/Kreps–Porteus preferences (26) (as printed, and with the `ρ = 1`, `σ = 1`
  log limits of footnote 13): their unique optimum is the two-stage plan, with stage 2 as under
  expected utility and stage 1 using `σ`; when `σ = 1/ρ`, (26) equals expected utility
  `C₁^{1−ρ}/(1−ρ) + βΣ π(s)C₂(s)^{1−ρ}/(1−ρ)` identically, so the two rank all plans alike
  and have the same unique optimum; conversely (26) ranks positive plans as expected utility
  does only when `σ = 1/ρ`;
* the current-account statements of p. 285 and footnote 14 restated at the optimum of (26).
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


/-! ## The log limit `ρ = 1` of the certainty equivalent (O&R footnote 13) -/

/-- The tangent-line inequality for `log` (used for the `ρ = 1` and `σ = 1` cases of O&R
§5.1.8, footnote 13): `log x ≤ log y + (x − y)/y` for `x, y > 0`, strictly if `x ≠ y`. -/
theorem log_le_tangent {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Real.log x ≤ Real.log y + (x - y) / y ∧
      (x ≠ y → Real.log x < Real.log y + (x - y) / y) := by
  have e : Real.log x - Real.log y = Real.log (x / y) := (Real.log_div hx.ne' hy.ne').symm
  have e2 : (x - y) / y = x / y - 1 := by field_simp
  refine ⟨by linarith [Real.log_le_sub_one_of_pos (div_pos hx hy)], fun hxy => ?_⟩
  have := Real.log_lt_sub_one_of_pos (div_pos hx hy)
    (fun h => hxy ((div_eq_one_iff_eq hy.ne').mp h))
  linarith

/-- The certainty equivalent (23) in its `ρ = 1` (log) limit, O&R footnote 13, p. 284: the
geometric mean `Ω(C₂) = exp(Σ π(s) log C₂(s))` (the L'Hospital limit of (23) as `ρ → 1`). -/
noncomputable def geoIndex (Ω : StateSpace S) (C : S → ℝ) : ℝ :=
  Real.exp (∑ s, Ω.prob s * Real.log (C s))

/-- The price index (25) in its `ρ = 1` limit, O&R footnote 13, p. 284:
`P = exp(Σ π(s) log(p(s)/π(s)))`. -/
noncomputable def geoPrice (Ω : StateSpace S) (p : S → ℝ) : ℝ :=
  Real.exp (∑ s, Ω.prob s * Real.log (p s / Ω.prob s))

/-- The demands (24) at `ρ = 1`, O&R (24) and footnote 13, p. 283–284:
`C₂(s) = π(s)Z₂/p(s)`. -/
noncomputable def geoDemand (Ω : StateSpace S) (p : S → ℝ) (Z : ℝ) (s : S) : ℝ :=
  Ω.prob s * Z / p s

/-- The `ρ = 1` demands are the formula (24) with `ρ = 1`, O&R (24), p. 283:
`[(p(s)/π(s))/P]^{−1} Z₂/P = π(s)Z₂/p(s)` (for `π(s), p(s), P > 0`). -/
theorem geoDemand_eq_24 (Ω : StateSpace S) (p : S → ℝ) {P Z : ℝ} {s : S}
    (hπ : 0 < Ω.prob s) (hp : 0 < p s) (hP : 0 < P) :
    (p s / Ω.prob s / P) ^ (-1 / (1 : ℝ)) * (Z / P) = geoDemand Ω p Z s := by
  rw [div_one, Real.rpow_neg_one, geoDemand]
  field_simp

/-- Stage 2 at `ρ = 1`, O&R (24)–(25) and footnote 13, pp. 283–284: for `π, p, Z₂ > 0` the
demands `π(s)Z₂/p(s)` are positive, cost exactly `Z₂`, and attain `Ω = Z₂/P`; and every
positive bundle costing at most `Z₂` has `Ω(C₂) ≤ Z₂/P`, strictly unless it is the demand
bundle. -/
theorem geo_stage_two (Ω : StateSpace S) (hπ : ∀ s, 0 < Ω.prob s) (p : S → ℝ)
    (hp : ∀ s, 0 < p s) {Z : ℝ} (hZ : 0 < Z) :
    (∀ s, 0 < geoDemand Ω p Z s) ∧ ∑ s, p s * geoDemand Ω p Z s = Z ∧
      geoIndex Ω (geoDemand Ω p Z) = Z / geoPrice Ω p ∧
      ∀ C : S → ℝ, (∀ s, 0 < C s) → ∑ s, p s * C s ≤ Z →
        geoIndex Ω C ≤ Z / geoPrice Ω p ∧
          ((∃ s, C s ≠ geoDemand Ω p Z s) → geoIndex Ω C < Z / geoPrice Ω p) := by
  have hD : ∀ s, 0 < geoDemand Ω p Z s := fun s => by
    have := hπ s; have := hp s; unfold geoDemand; positivity
  have hcost : ∑ s, p s * geoDemand Ω p Z s = Z := by
    rw [Finset.sum_congr rfl fun s _ => show p s * geoDemand Ω p Z s = Z * Ω.prob s by
      have := (hp s).ne'; unfold geoDemand; field_simp, ← Finset.mul_sum, Ω.prob_sum,
      mul_one]
  have hlogD : ∑ s, Ω.prob s * Real.log (geoDemand Ω p Z s) =
      Real.log Z - ∑ s, Ω.prob s * Real.log (p s / Ω.prob s) := by
    have e : ∀ s, Ω.prob s * Real.log (geoDemand Ω p Z s) =
        Ω.prob s * Real.log Z - Ω.prob s * Real.log (p s / Ω.prob s) := fun s => by
      have := hπ s; have := hp s
      unfold geoDemand
      simp (disch := positivity) only [Real.log_mul, Real.log_div]
      ring
    rw [Finset.sum_congr rfl fun s _ => e s, Finset.sum_sub_distrib, ← Finset.sum_mul,
      Ω.prob_sum, one_mul]
  have hval : geoIndex Ω (geoDemand Ω p Z) = Z / geoPrice Ω p := by
    rw [geoIndex, geoPrice, hlogD, Real.exp_sub, Real.exp_log hZ]
  refine ⟨hD, hcost, hval, fun C hC hbud => ?_⟩
  have hterm : ∀ s, Ω.prob s * Real.log (C s) ≤
      Ω.prob s * Real.log (geoDemand Ω p Z s) + (p s * C s / Z - Ω.prob s) := fun s => by
    have e : Ω.prob s * ((C s - geoDemand Ω p Z s) / geoDemand Ω p Z s) =
        p s * C s / Z - Ω.prob s := by
      have := (hπ s).ne'; have := (hp s).ne'; unfold geoDemand; field_simp
    have := mul_le_mul_of_nonneg_left (log_le_tangent (hC s) (hD s)).1 (hπ s).le
    linarith
  have hlin : ∑ s, (p s * C s / Z - Ω.prob s) ≤ 0 := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_div, Ω.prob_sum, sub_nonpos,
      div_le_one hZ]
    exact hbud
  have hsum := Finset.sum_le_sum fun s (_ : s ∈ Finset.univ) => hterm s
  rw [Finset.sum_add_distrib] at hsum
  rw [← hval]
  refine ⟨Real.exp_le_exp.mpr (by linarith), fun ⟨s0, hs0⟩ => ?_⟩
  have hlt := Finset.sum_lt_sum (fun s (_ : s ∈ Finset.univ) => hterm s)
    ⟨s0, Finset.mem_univ _, by
      have e : Ω.prob s0 * ((C s0 - geoDemand Ω p Z s0) / geoDemand Ω p Z s0) =
          p s0 * C s0 / Z - Ω.prob s0 := by
        have := (hπ s0).ne'; have := (hp s0).ne'; unfold geoDemand; field_simp
      have := mul_lt_mul_of_pos_left ((log_le_tangent (hC s0) (hD s0)).2 hs0) (hπ s0)
      linarith⟩
  rw [Finset.sum_add_distrib] at hlt
  exact Real.exp_lt_exp.mpr (by linarith)

/-- The CES certainty equivalent (23) of a positive bundle is positive, O&R p. 283 (for
`π > 0`). -/
theorem cesIndex_pos (Ω : StateSpace S) (hπ : ∀ s, 0 < Ω.prob s) (ρ : ℝ) {C : S → ℝ}
    (hC : ∀ s, 0 < C s) : 0 < cesIndex Ω ρ C :=
  Real.rpow_pos_of_pos (Finset.sum_pos (fun s _ => by have := hπ s; have := hC s; positivity)
    (univ_nonempty_of_stateSpace Ω)) _

/-! ## The risk index for every `ρ > 0` -/

/-- The certainty-equivalent index of O&R (23) for every `ρ > 0`: the CES form (23) for
`ρ ≠ 1` and its log limit, the geometric mean, for `ρ = 1` (footnote 13, p. 284). -/
noncomputable def riskIndex (Ω : StateSpace S) (ρ : ℝ) (C : S → ℝ) : ℝ :=
  if ρ = 1 then geoIndex Ω C else cesIndex Ω ρ C

/-- The price index (25) for every `ρ > 0` (log limit at `ρ = 1`, O&R footnote 13). -/
noncomputable def riskPrice (Ω : StateSpace S) (ρ : ℝ) (p : S → ℝ) : ℝ :=
  if ρ = 1 then geoPrice Ω p else priceIndex Ω ρ p

/-- The demands (24) for every `ρ > 0` (log limit at `ρ = 1`, O&R footnote 13). -/
noncomputable def riskDemand (Ω : StateSpace S) (ρ : ℝ) (p : S → ℝ) (Z : ℝ) (s : S) : ℝ :=
  if ρ = 1 then geoDemand Ω p Z s else cesDemand Ω ρ p Z s

/-- Stage 2 of two-stage budgeting for every `ρ > 0`, O&R (23)–(25), p. 283 and footnote 13:
for `π, p > 0`, the price index is positive, the index of a positive bundle is positive, and
for every `Z₂ > 0` the demands (24) are positive, cost `Z₂` and attain `Ω = Z₂/P`, while every
positive bundle costing at most `Z₂` has `Ω ≤ Z₂/P`, strictly unless it is the demand
bundle. -/
theorem risk_stage_two (Ω : StateSpace S) (hπ : ∀ s, 0 < Ω.prob s) (p : S → ℝ)
    (hp : ∀ s, 0 < p s) {ρ : ℝ} (hρ : 0 < ρ) :
    0 < riskPrice Ω ρ p ∧ (∀ C : S → ℝ, (∀ s, 0 < C s) → 0 < riskIndex Ω ρ C) ∧
      ∀ Z : ℝ, 0 < Z → (∀ s, 0 < riskDemand Ω ρ p Z s) ∧
        ∑ s, p s * riskDemand Ω ρ p Z s = Z ∧
        riskIndex Ω ρ (riskDemand Ω ρ p Z) = Z / riskPrice Ω ρ p ∧
        ∀ C : S → ℝ, (∀ s, 0 < C s) → ∑ s, p s * C s ≤ Z →
          riskIndex Ω ρ C ≤ Z / riskPrice Ω ρ p ∧
            ((∃ s, C s ≠ riskDemand Ω ρ p Z s) → riskIndex Ω ρ C < Z / riskPrice Ω ρ p) := by
  by_cases h1 : ρ = 1
  · have eI : riskIndex Ω ρ = geoIndex Ω := funext fun C => by simp [riskIndex, h1]
    have eP : riskPrice Ω ρ p = geoPrice Ω p := by simp [riskPrice, h1]
    have eD : riskDemand Ω ρ p = geoDemand Ω p := funext fun Z => funext fun s => by
      simp [riskDemand, h1]
    rw [eI, eP, eD]
    exact ⟨Real.exp_pos _, fun C _ => Real.exp_pos _, fun Z hZ => geo_stage_two Ω hπ p hp hZ⟩
  · have eI : riskIndex Ω ρ = cesIndex Ω ρ := funext fun C => by simp [riskIndex, h1]
    have eP : riskPrice Ω ρ p = priceIndex Ω ρ p := by simp [riskPrice, h1]
    have eD : riskDemand Ω ρ p = cesDemand Ω ρ p := funext fun Z => funext fun s => by
      simp [riskDemand, h1]
    rw [eI, eP, eD]
    have hP := priceIndex_pos Ω hπ p hp ρ
    refine ⟨hP, fun C hC => cesIndex_pos Ω hπ ρ hC, fun Z hZ => ⟨fun s => ?_,
      demand_cost Ω hπ p hp hρ h1 hZ, (cesIndex_demand Ω hπ p hp hρ h1 hZ).2,
      fun C hC hbud => cesIndex_le Ω hπ p hp hρ h1 hZ C hC hbud⟩⟩
    have := hπ s; have := hp s
    unfold cesDemand
    positivity

/-! ## Isoelastic period utility (O&R (26), p. 283) -/

/-- Isoelastic period utility with intertemporal substitution elasticity `σ > 0`, O&R (26),
p. 283: `u(C) = C^{1−1/σ}/(1 − 1/σ)`, with its log limit `u(C) = log C` at `σ = 1` (footnote
13, p. 284). -/
noncomputable def isoU (σ c : ℝ) : ℝ :=
  if σ = 1 then Real.log c else c ^ (1 - 1 / σ) / (1 - 1 / σ)

/-- The marginal utility of isoelastic utility, O&R p. 284: `u′(C) = C^{−1/σ}` for `σ, C > 0`
(including `σ = 1`, where `u′(C) = 1/C`). -/
theorem isoU_hasDerivAt {σ x : ℝ} (hσ : 0 < σ) (hx : 0 < x) :
    HasDerivAt (isoU σ) (x ^ (-1 / σ)) x := by
  by_cases h1 : σ = 1
  · have hf : isoU σ = Real.log := funext fun c => by simp [isoU, h1]
    rw [hf, h1, div_one, Real.rpow_neg_one]
    exact Real.hasDerivAt_log hx.ne'
  · have ha : 1 - 1 / σ ≠ 0 := by
      intro h
      have : 1 / σ = 1 := by linarith
      exact h1 (by rw [one_div, inv_eq_one] at this; exact this)
    have hf : isoU σ = fun c => c ^ (1 - 1 / σ) / (1 - 1 / σ) :=
      funext fun c => by simp [isoU, h1]
    rw [hf]
    refine ((Real.hasDerivAt_rpow_const (p := 1 - 1 / σ) (Or.inl hx.ne')).div_const
      (1 - 1 / σ)).congr_deriv ?_
    rw [show 1 - 1 / σ - 1 = -1 / σ by ring]
    field_simp

/-- The tangent-line inequality for isoelastic utility (concavity), O&R §5.1.8: for `σ > 0`
and `x, y > 0`, `u(x) ≤ u(y) + y^{−1/σ}(x − y)`, strictly if `x ≠ y`. -/
theorem isoU_tangent {σ x y : ℝ} (hσ : 0 < σ) (hx : 0 < x) (hy : 0 < y) :
    isoU σ x ≤ isoU σ y + y ^ (-1 / σ) * (x - y) ∧
      (x ≠ y → isoU σ x < isoU σ y + y ^ (-1 / σ) * (x - y)) := by
  by_cases h1 : σ = 1
  · have e : y ^ (-1 / σ) * (x - y) = (x - y) / y := by
      rw [h1, div_one, Real.rpow_neg_one]; field_simp
    simp only [isoU, h1, ite_true]
    rw [h1] at e
    rw [e]
    exact log_le_tangent hx hy
  · simp only [isoU, h1, ite_false]
    set a := 1 - 1 / σ with ha
    have ha1 : -1 / σ = a - 1 := by rw [ha]; ring
    rw [ha1]
    have key : x ^ a / a - (y ^ a / a + y ^ (a - 1) * (x - y)) =
        (x ^ a - (y ^ a + a * y ^ (a - 1) * (x - y))) / a := by
      have ha0 : a ≠ 0 := by
        intro h
        have : 1 / σ = 1 := by rw [ha] at h; linarith
        exact h1 (by rw [one_div, inv_eq_one] at this; exact this)
      field_simp
    rcases lt_or_gt_of_ne h1 with hlt | hgt
    · -- σ < 1: `a < 0`.
      have ha0 : a < 0 := by
        rw [ha, sub_neg, lt_div_iff₀ hσ]; linarith
      have h := tangent_le_rpow_of_neg ha0 hx hy
      refine ⟨?_, fun hxy => ?_⟩
      · have := div_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr h.1) ha0.le
        linarith
      · have := div_neg_of_pos_of_neg (sub_pos.mpr (h.2 hxy)) ha0
        linarith
    · -- σ > 1: `0 < a < 1`.
      have ha0 : 0 < a := by
        rw [ha, sub_pos, div_lt_one hσ]; exact hgt
      have ha1' : a < 1 := by
        rw [ha]; have : 0 < 1 / σ := by positivity
        linarith
      have h := rpow_le_tangent ha0 ha1' hx hy
      refine ⟨?_, fun hxy => ?_⟩
      · have := div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr h.1) ha0.le
        linarith
      · have := div_neg_of_neg_of_pos (sub_neg.mpr (h.2 hxy)) ha0
        linarith

/-- Isoelastic utility is strictly increasing on `(0, ∞)`, O&R (26): for `σ > 0` and
`0 < x < y`, `u(x) < u(y)`. -/
theorem isoU_lt_of_lt {σ x y : ℝ} (hσ : 0 < σ) (hx : 0 < x) (hxy : x < y) :
    isoU σ x < isoU σ y := by
  have hy : 0 < y := hx.trans hxy
  have h := (isoU_tangent hσ hx hy).2 hxy.ne
  have : y ^ (-1 / σ) * (x - y) < 0 :=
    mul_neg_of_pos_of_neg (Real.rpow_pos_of_pos hy _) (by linarith)
  linarith

/-- Isoelastic utility is monotone on `(0, ∞)`, O&R (26): for `σ > 0` and `0 < x ≤ y`,
`u(x) ≤ u(y)`. -/
theorem isoU_le_of_le {σ x y : ℝ} (hσ : 0 < σ) (hx : 0 < x) (hxy : x ≤ y) :
    isoU σ x ≤ isoU σ y := by
  rcases hxy.lt_or_eq with h | h
  · exact (isoU_lt_of_lt hσ hx h).le
  · rw [h]

/-! ## Stage 1: the optimal division of spending across dates (O&R (21), (22), (27)) -/

/-- The stage-1 objective (21), O&R p. 282, with isoelastic `u`: `u(C₁) + βu(Z₂/P)`. -/
noncomputable def stageOneObjective (σ β P C1 Z2 : ℝ) : ℝ :=
  isoU σ C1 + β * isoU σ (Z2 / P)

/-- The stage-1 consumption function, O&R p. 284:
`C₁ = W₁/(1 + ((1+r)/P)^{σ−1}β^σ)`. -/
noncomputable def stageOneC1 (σ r β P W1 : ℝ) : ℝ :=
  W1 / (1 + ((1 + r) / P) ^ (σ - 1) * β ^ σ)

/-- Stage-1 date-2 spending, O&R (22), p. 282: `Z₂ = (1+r)(W₁ − C₁)` at the stage-1
consumption function. -/
noncomputable def stageOneZ2 (σ r β P W1 : ℝ) : ℝ :=
  (1 + r) * (W1 - stageOneC1 σ r β P W1)

/-- The stage-1 solution satisfies (27), O&R p. 284:
`Z₂ = (1+r)^σ β^σ (1/P)^{σ−1} C₁` (for `1 + r, β, P > 0`). -/
theorem stageOneZ2_eq_27 {σ r β P W1 : ℝ} (hr : 0 < 1 + r) (hβ : 0 < β) (hP : 0 < P) :
    stageOneZ2 σ r β P W1 =
      (1 + r) ^ σ * β ^ σ * (1 / P) ^ (σ - 1) * stageOneC1 σ r β P W1 := by
  have hK : (1 + r) * (((1 + r) / P) ^ (σ - 1) * β ^ σ) =
      (1 + r) ^ σ * β ^ σ * (1 / P) ^ (σ - 1) := by
    rw [Real.div_rpow hr.le hP.le, Real.div_rpow zero_le_one hP.le, Real.one_rpow,
      Real.rpow_sub_one hr.ne']
    have : 0 < P ^ (σ - 1) := Real.rpow_pos_of_pos hP _
    field_simp
  have hKpos : 0 < ((1 + r) / P) ^ (σ - 1) * β ^ σ := by positivity
  rw [← hK, stageOneZ2, stageOneC1]
  field_simp
  ring

/-- The stage-1 solution is feasible, O&R (22), p. 282: for `W₁ > 0` (and `1 + r, β, P > 0`),
`C₁ > 0`, `Z₂ > 0` and `C₁ + Z₂/(1+r) = W₁`. -/
theorem stageOne_feasible {σ r β P W1 : ℝ} (hr : 0 < 1 + r) (hβ : 0 < β) (hP : 0 < P)
    (hW : 0 < W1) :
    0 < stageOneC1 σ r β P W1 ∧ 0 < stageOneZ2 σ r β P W1 ∧
      stageOneC1 σ r β P W1 + stageOneZ2 σ r β P W1 / (1 + r) = W1 := by
  have hC : 0 < stageOneC1 σ r β P W1 := by unfold stageOneC1; positivity
  refine ⟨hC, ?_, by rw [stageOneZ2]; field_simp; ring⟩
  rw [stageOneZ2_eq_27 hr hβ hP]
  positivity

/-- The stage-1 solution satisfies the bond Euler equation, O&R p. 284:
`u′(C₁) = (1+r)β(1/P)u′(Z₂/P)` with `u′(C) = C^{−1/σ}` (see `isoU_hasDerivAt`). -/
theorem stageOne_euler {σ r β P W1 : ℝ} (hσ : 0 < σ) (hr : 0 < 1 + r) (hβ : 0 < β)
    (hP : 0 < P) (hW : 0 < W1) :
    stageOneC1 σ r β P W1 ^ (-1 / σ) =
      (1 + r) * β * P⁻¹ * (stageOneZ2 σ r β P W1 / P) ^ (-1 / σ) := by
  obtain ⟨hC, hZ, -⟩ := stageOne_feasible (σ := σ) hr hβ hP hW
  exact (euler_27 hσ hr hβ hC hZ hP).mpr (stageOneZ2_eq_27 hr hβ hP)

/-- Stage-1 optimality (sufficiency, by concavity), O&R pp. 283–284: for `σ, β, P, W₁ > 0` and
`1 + r > 0`, the stage-1 solution maximises the objective (21) over all `C₁, Z₂ > 0` with
`C₁ + Z₂/(1+r) = W₁` (O&R (22)), strictly at every other feasible point. -/
theorem stageOne_optimal {σ r β P W1 : ℝ} (hσ : 0 < σ) (hr : 0 < 1 + r) (hβ : 0 < β)
    (hP : 0 < P) (hW : 0 < W1) {C1 Z2 : ℝ} (hC1 : 0 < C1) (hZ2 : 0 < Z2)
    (hbud : C1 + Z2 / (1 + r) = W1) :
    stageOneObjective σ β P C1 Z2 ≤
        stageOneObjective σ β P (stageOneC1 σ r β P W1) (stageOneZ2 σ r β P W1) ∧
      (C1 ≠ stageOneC1 σ r β P W1 → stageOneObjective σ β P C1 Z2 <
        stageOneObjective σ β P (stageOneC1 σ r β P W1) (stageOneZ2 σ r β P W1)) := by
  obtain ⟨hc, hz, hb⟩ := stageOne_feasible (σ := σ) hr hβ hP hW
  have heul := stageOne_euler hσ hr hβ hP hW
  set c := stageOneC1 σ r β P W1
  set z := stageOneZ2 σ r β P W1
  set e := c ^ (-1 / σ) with he
  set m := (z / P) ^ (-1 / σ) with hm
  have t1 := isoU_tangent hσ hC1 hc
  have t2 := (isoU_tangent hσ (div_pos hZ2 hP) (div_pos hz hP)).1
  rw [← he] at t1
  rw [← hm] at t2
  have hlin : β * (m * (Z2 / P - z / P)) = e * ((Z2 - z) / (1 + r)) := by
    rw [heul]; field_simp
  have hzero : e * (C1 - c) + e * ((Z2 - z) / (1 + r)) = 0 := by
    rw [← mul_add, show C1 - c + (Z2 - z) / (1 + r) = 0 by rw [sub_div]; linarith, mul_zero]
  have t2' := mul_le_mul_of_nonneg_left t2 hβ.le
  simp only [stageOneObjective]
  refine ⟨by nlinarith [t1.1], fun hne => by nlinarith [t1.2 hne]⟩

/-- Stage-1 uniqueness and necessity, O&R p. 284: any feasible `(C₁, Z₂)` (positive, with
`C₁ + Z₂/(1+r) = W₁`) doing at least as well as the stage-1 solution in (21) is the stage-1
solution. -/
theorem stageOne_unique {σ r β P W1 : ℝ} (hσ : 0 < σ) (hr : 0 < 1 + r) (hβ : 0 < β)
    (hP : 0 < P) (hW : 0 < W1) {C1 Z2 : ℝ} (hC1 : 0 < C1) (hZ2 : 0 < Z2)
    (hbud : C1 + Z2 / (1 + r) = W1)
    (hge : stageOneObjective σ β P (stageOneC1 σ r β P W1) (stageOneZ2 σ r β P W1) ≤
      stageOneObjective σ β P C1 Z2) :
    C1 = stageOneC1 σ r β P W1 ∧ Z2 = stageOneZ2 σ r β P W1 := by
  have hC : C1 = stageOneC1 σ r β P W1 := by
    by_contra hne
    exact absurd hge (not_le.mpr ((stageOne_optimal hσ hr hβ hP hW hC1 hZ2 hbud).2 hne))
  refine ⟨hC, ?_⟩
  obtain ⟨-, -, hb⟩ := stageOne_feasible (σ := σ) hr hβ hP hW
  rw [← hC] at hb
  have : Z2 / (1 + r) = stageOneZ2 σ r β P W1 / (1 + r) := by linarith
  field_simp at this
  exact this

/-- The stage-1 problem is solved exactly by the stage-1 solution, O&R pp. 283–284: a feasible
`(C₁, Z₂)` maximises (21) over the feasible set iff it equals
`(W₁/(1 + ((1+r)/P)^{σ−1}β^σ), (1+r)(W₁ − C₁))`. -/
theorem stageOne_maximiser_iff {σ r β P W1 : ℝ} (hσ : 0 < σ) (hr : 0 < 1 + r) (hβ : 0 < β)
    (hP : 0 < P) (hW : 0 < W1) {C1 Z2 : ℝ} (hC1 : 0 < C1) (hZ2 : 0 < Z2)
    (hbud : C1 + Z2 / (1 + r) = W1) :
    (∀ C1' Z2' : ℝ, 0 < C1' → 0 < Z2' → C1' + Z2' / (1 + r) = W1 →
      stageOneObjective σ β P C1' Z2' ≤ stageOneObjective σ β P C1 Z2) ↔
      C1 = stageOneC1 σ r β P W1 ∧ Z2 = stageOneZ2 σ r β P W1 := by
  obtain ⟨hc, hz, hb⟩ := stageOne_feasible (σ := σ) hr hβ hP hW
  constructor
  · intro hmax
    exact stageOne_unique hσ hr hβ hP hW hC1 hZ2 hbud (hmax _ _ hc hz hb)
  · rintro ⟨rfl, rfl⟩ C1' Z2' h1 h2 hb'
    exact (stageOne_optimal hσ hr hβ hP hW h1 h2 hb').1

/-- The stage-1 optimum is characterised by (27), O&R p. 284 (necessity and sufficiency): a
feasible `(C₁, Z₂)` maximises (21) subject to (22) iff `Z₂ = (1+r)^σβ^σ(1/P)^{σ−1}C₁`. -/
theorem stageOne_maximiser_iff_27 {σ r β P W1 : ℝ} (hσ : 0 < σ) (hr : 0 < 1 + r)
    (hβ : 0 < β) (hP : 0 < P) (hW : 0 < W1) {C1 Z2 : ℝ} (hC1 : 0 < C1) (hZ2 : 0 < Z2)
    (hbud : C1 + Z2 / (1 + r) = W1) :
    (∀ C1' Z2' : ℝ, 0 < C1' → 0 < Z2' → C1' + Z2' / (1 + r) = W1 →
      stageOneObjective σ β P C1' Z2' ≤ stageOneObjective σ β P C1 Z2) ↔
      Z2 = (1 + r) ^ σ * β ^ σ * (1 / P) ^ (σ - 1) * C1 := by
  rw [stageOne_maximiser_iff hσ hr hβ hP hW hC1 hZ2 hbud]
  constructor
  · rintro ⟨rfl, rfl⟩
    exact stageOneZ2_eq_27 hr hβ hP
  · intro h27
    have hC : C1 = stageOneC1 σ r β P W1 := consumption_27 hr hβ hP h27 hbud
    refine ⟨hC, ?_⟩
    rw [stageOneZ2, ← hC, ← hbud]
    field_simp
    ring

/-- The stage-1 optimum is characterised by the bond Euler equation, O&R p. 284: a feasible
`(C₁, Z₂)` maximises (21) subject to (22) iff `u′(C₁) = (1+r)β(1/P)u′(Z₂/P)` with
`u′(C) = C^{−1/σ}`. -/
theorem stageOne_maximiser_iff_euler {σ r β P W1 : ℝ} (hσ : 0 < σ) (hr : 0 < 1 + r)
    (hβ : 0 < β) (hP : 0 < P) (hW : 0 < W1) {C1 Z2 : ℝ} (hC1 : 0 < C1) (hZ2 : 0 < Z2)
    (hbud : C1 + Z2 / (1 + r) = W1) :
    (∀ C1' Z2' : ℝ, 0 < C1' → 0 < Z2' → C1' + Z2' / (1 + r) = W1 →
      stageOneObjective σ β P C1' Z2' ≤ stageOneObjective σ β P C1 Z2) ↔
      C1 ^ (-1 / σ) = (1 + r) * β * P⁻¹ * (Z2 / P) ^ (-1 / σ) := by
  rw [stageOne_maximiser_iff_27 hσ hr hβ hP hW hC1 hZ2 hbud, euler_27 hσ hr hβ hC1 hZ2 hP]

/-! ## Two-stage budgeting solves the original problem (O&R (20)–(22)) -/

/-- Two-stage budgeting solves (20), O&R pp. 282–284, for any consumption index `Ω` with the
stage-2 properties (positive on positive bundles; demands `D(Z₂)` positive, costing `Z₂` and
attaining `Z₂/P`; every positive bundle costing at most `Z₂` has index at most `Z₂/P`,
strictly unless it is `D(Z₂)`). With isoelastic `u` (`σ > 0`), `β, W₁ > 0`, `1 + r > 0`,
`p > 0` and at least one state: the plan `C₁* = W₁/(1 + ((1+r)/P)^{σ−1}β^σ)`,
`C₂* = D(Z₂*)`, `Z₂* = (1+r)(W₁ − C₁*)` is feasible for (22) with `Z₂ = Σ p(s)C₂(s)`; it
maximises `u(C₁) + βu(Ω(C₂))` over ALL positive state-contingent plans on the budget line;
and it is the unique maximiser (any feasible plan doing at least as well equals it). -/
theorem two_stage_optimal_of_index (p : S → ℝ) (hp : ∀ s, 0 < p s)
    (hne : (Finset.univ : Finset S).Nonempty) {I : (S → ℝ) → ℝ} {Dm : ℝ → S → ℝ} {P : ℝ}
    (hP : 0 < P) (hIpos : ∀ C : S → ℝ, (∀ s, 0 < C s) → 0 < I C)
    (hDpos : ∀ Z, 0 < Z → ∀ s, 0 < Dm Z s) (hcost : ∀ Z, 0 < Z → ∑ s, p s * Dm Z s = Z)
    (hval : ∀ Z, 0 < Z → I (Dm Z) = Z / P)
    (hle : ∀ Z, 0 < Z → ∀ C : S → ℝ, (∀ s, 0 < C s) → ∑ s, p s * C s ≤ Z →
      I C ≤ Z / P ∧ ((∃ s, C s ≠ Dm Z s) → I C < Z / P))
    {σ r β W1 : ℝ} (hσ : 0 < σ) (hr : 0 < 1 + r) (hβ : 0 < β) (hW : 0 < W1) :
    (0 < stageOneC1 σ r β P W1 ∧ (∀ s, 0 < Dm (stageOneZ2 σ r β P W1) s) ∧
      stageOneC1 σ r β P W1 + (∑ s, p s * Dm (stageOneZ2 σ r β P W1) s) / (1 + r) = W1) ∧
    (∀ (C1 : ℝ) (C2 : S → ℝ), 0 < C1 → (∀ s, 0 < C2 s) →
      C1 + (∑ s, p s * C2 s) / (1 + r) = W1 →
      isoU σ C1 + β * isoU σ (I C2) ≤ isoU σ (stageOneC1 σ r β P W1) +
        β * isoU σ (I (Dm (stageOneZ2 σ r β P W1)))) ∧
    (∀ (C1 : ℝ) (C2 : S → ℝ), 0 < C1 → (∀ s, 0 < C2 s) →
      C1 + (∑ s, p s * C2 s) / (1 + r) = W1 →
      isoU σ (stageOneC1 σ r β P W1) + β * isoU σ (I (Dm (stageOneZ2 σ r β P W1))) ≤
        isoU σ C1 + β * isoU σ (I C2) →
      C1 = stageOneC1 σ r β P W1 ∧ C2 = Dm (stageOneZ2 σ r β P W1)) := by
  obtain ⟨hc, hz, hb⟩ := stageOne_feasible (σ := σ) hr hβ hP hW
  set c := stageOneC1 σ r β P W1 with hcdef
  set z := stageOneZ2 σ r β P W1 with hzdef
  have hUstar : isoU σ c + β * isoU σ (I (Dm z)) = stageOneObjective σ β P c z := by
    rw [stageOneObjective, hval z hz]
  -- every feasible plan is bounded by its stage-1 value
  have hbound : ∀ (C1 : ℝ) (C2 : S → ℝ), (∀ s, 0 < C2 s) →
      isoU σ C1 + β * isoU σ (I C2) ≤ stageOneObjective σ β P C1 (∑ s, p s * C2 s) ∧
      ((∃ s, C2 s ≠ Dm (∑ s, p s * C2 s) s) →
        isoU σ C1 + β * isoU σ (I C2) < stageOneObjective σ β P C1 (∑ s, p s * C2 s)) := by
    intro C1 C2 hC2
    have hZ : 0 < ∑ s, p s * C2 s := Finset.sum_pos (fun s _ => mul_pos (hp s) (hC2 s)) hne
    have h := hle _ hZ C2 hC2 le_rfl
    simp only [stageOneObjective]
    refine ⟨?_, fun hex => ?_⟩
    · have := isoU_le_of_le hσ (hIpos C2 hC2) h.1
      nlinarith
    · have := isoU_lt_of_lt hσ (hIpos C2 hC2) (h.2 hex)
      nlinarith
  refine ⟨⟨hc, hDpos z hz, by rw [hcost z hz]; exact hb⟩, fun C1 C2 hC1 hC2 hbud => ?_,
    fun C1 C2 hC1 hC2 hbud hge => ?_⟩
  · have hZ : 0 < ∑ s, p s * C2 s := Finset.sum_pos (fun s _ => mul_pos (hp s) (hC2 s)) hne
    rw [hUstar]
    exact (hbound C1 C2 hC2).1.trans (stageOne_optimal hσ hr hβ hP hW hC1 hZ hbud).1
  · have hZ : 0 < ∑ s, p s * C2 s := Finset.sum_pos (fun s _ => mul_pos (hp s) (hC2 s)) hne
    rw [hUstar] at hge
    have h1 := (hbound C1 C2 hC2).1
    obtain ⟨hC, hZeq⟩ := stageOne_unique hσ hr hβ hP hW hC1 hZ hbud (hge.trans h1)
    refine ⟨hC, funext fun s => ?_⟩
    by_contra hne'
    have h2 := (hbound C1 C2 hC2).2 ⟨s, by rw [hZeq]; exact hne'⟩
    rw [hC, ← hcdef] at hge
    rw [hC, hZeq, ← hcdef, ← hzdef] at h2
    linarith

/-! ## The Epstein–Zin / Kreps–Porteus preferences (26) (O&R p. 283, footnote 13) -/

/-- The preferences (26), O&R p. 283: `U₁ = u(C₁) + βu(Ω(C₂))` with isoelastic
`u(C) = C^{1−1/σ}/(1 − 1/σ)` (intertemporal elasticity `σ > 0`, log at `σ = 1`) and the CES
certainty equivalent (23) with relative risk aversion `ρ > 0` (geometric mean at `ρ = 1`);
footnote 13 cites Epstein and Zin (1989) and Weil (1989b, 1990), and handles `ρ = 1` and
`σ = 1` by L'Hospital's rule, as here. -/
noncomputable def ezUtility (Ω : StateSpace S) (ρ σ β C1 : ℝ) (C2 : S → ℝ) : ℝ :=
  isoU σ C1 + β * isoU σ (riskIndex Ω ρ C2)

/-- The preferences (26) exactly as printed, O&R p. 283: for `σ ≠ 1`, `ρ ≠ 1`,
`U₁ = C₁^{1−1/σ}/(1 − 1/σ) + β{[Σ π(s)C₂(s)^{1−ρ}]^{1/(1−ρ)}}^{1−1/σ}/(1 − 1/σ)`. -/
theorem ezUtility_eq_printed (Ω : StateSpace S) {ρ σ : ℝ} (hρ : ρ ≠ 1) (hσ : σ ≠ 1)
    (β C1 : ℝ) (C2 : S → ℝ) :
    ezUtility Ω ρ σ β C1 C2 = C1 ^ (1 - 1 / σ) / (1 - 1 / σ) +
      β * (((∑ s, Ω.prob s * C2 s ^ (1 - ρ)) ^ (1 / (1 - ρ))) ^ (1 - 1 / σ) /
        (1 - 1 / σ)) := by
  simp only [ezUtility, isoU, riskIndex, cesIndex, hρ, hσ, ite_false]

/-- The two-stage solution of (26), O&R pp. 283–284: for `ρ, σ > 0`, `π, p > 0`, `β, W₁ > 0`
and `1 + r > 0`, with `P` the price index (25) (at risk aversion `ρ`), stage 2 is identical to
the expected-utility case (demands (24)) and stage 1 uses the intertemporal elasticity `σ`:
the plan `C₁* = W₁/(1 + ((1+r)/P)^{σ−1}β^σ)`, `C₂* = (24)` at `Z₂* = (1+r)(W₁ − C₁*)` is
feasible, maximises (26) over all positive plans with `C₁ + Σ p(s)C₂(s)/(1+r) = W₁`, and is
the unique maximiser. -/
theorem ez_two_stage_optimal (Ω : StateSpace S) (hπ : ∀ s, 0 < Ω.prob s) (p : S → ℝ)
    (hp : ∀ s, 0 < p s) {ρ σ r β W1 : ℝ} (hρ : 0 < ρ) (hσ : 0 < σ) (hr : 0 < 1 + r)
    (hβ : 0 < β) (hW : 0 < W1) :
    let P := riskPrice Ω ρ p
    let C1s := stageOneC1 σ r β P W1
    let C2s := riskDemand Ω ρ p (stageOneZ2 σ r β P W1)
    (0 < C1s ∧ (∀ s, 0 < C2s s) ∧ C1s + (∑ s, p s * C2s s) / (1 + r) = W1) ∧
    (∀ (C1 : ℝ) (C2 : S → ℝ), 0 < C1 → (∀ s, 0 < C2 s) →
      C1 + (∑ s, p s * C2 s) / (1 + r) = W1 →
      ezUtility Ω ρ σ β C1 C2 ≤ ezUtility Ω ρ σ β C1s C2s) ∧
    (∀ (C1 : ℝ) (C2 : S → ℝ), 0 < C1 → (∀ s, 0 < C2 s) →
      C1 + (∑ s, p s * C2 s) / (1 + r) = W1 →
      ezUtility Ω ρ σ β C1s C2s ≤ ezUtility Ω ρ σ β C1 C2 → C1 = C1s ∧ C2 = C2s) := by
  obtain ⟨hP, hIpos, h2⟩ := risk_stage_two Ω hπ p hp hρ
  exact two_stage_optimal_of_index p hp (univ_nonempty_of_stateSpace Ω) hP hIpos
    (fun Z hZ => (h2 Z hZ).1) (fun Z hZ => (h2 Z hZ).2.1) (fun Z hZ => (h2 Z hZ).2.2.1)
    (fun Z hZ => (h2 Z hZ).2.2.2) hσ hr hβ hW

/-- CRRA period utility with relative risk aversion `ρ > 0`, O&R (13), p. 278, and p. 284:
`u(C) = C^{1−ρ}/(1 − ρ)`, with `u(C) = log C` at `ρ = 1`. -/
noncomputable def crraU (ρ c : ℝ) : ℝ :=
  if ρ = 1 then Real.log c else c ^ (1 - ρ) / (1 - ρ)

/-- Expected lifetime utility, O&R p. 284 (the special case of (20)/(21) the book compares with
(26)): `U₁ = C₁^{1−ρ}/(1−ρ) + β Σ π(s)C₂(s)^{1−ρ}/(1−ρ)` (log at `ρ = 1`). -/
noncomputable def expectedUtility (Ω : StateSpace S) (ρ β C1 : ℝ) (C2 : S → ℝ) : ℝ :=
  crraU ρ C1 + β * ∑ s, Ω.prob s * crraU ρ (C2 s)

/-- Isoelastic utility with `σ = 1/ρ` is CRRA utility with coefficient `ρ`, O&R p. 284:
`C^{1−1/σ}/(1 − 1/σ) = C^{1−ρ}/(1 − ρ)` (and both are `log C` when `ρ = σ = 1`). -/
theorem isoU_inv_eq_crraU (ρ : ℝ) : isoU (1 / ρ) = crraU ρ := by
  funext c
  have hiff : 1 / ρ = 1 ↔ ρ = 1 := by
    rw [one_div, inv_eq_one]
  by_cases h1 : ρ = 1
  · simp [isoU, crraU, h1]
  · have h1' : ¬ (1 / ρ = 1) := fun h => h1 (hiff.mp h)
    simp only [isoU, crraU, h1, h1', ite_false, one_div_one_div]

/-- The reduction of (26) to expected utility, O&R p. 284: when `σ = 1/ρ`, (26)
coincides with expected utility, `U₁ = C₁^{1−ρ}/(1−ρ) + β Σ π(s)C₂(s)^{1−ρ}/(1−ρ)`, for every
plan with `C₂ ≥ 0` (the transform relating them is the identity, a strictly increasing
function; the book's `ρ > 0` is not needed for the identity). -/
theorem ez_eq_expectedUtility (Ω : StateSpace S) (ρ β C1 : ℝ)
    {C2 : S → ℝ} (hC2 : ∀ s, 0 ≤ C2 s) :
    ezUtility Ω ρ (1 / ρ) β C1 C2 = expectedUtility Ω ρ β C1 C2 := by
  rw [ezUtility, expectedUtility, isoU_inv_eq_crraU ρ]
  congr 2
  by_cases h1 : ρ = 1
  · simp only [crraU, riskIndex, geoIndex, h1, ite_true, Real.log_exp]
  · have h1ρ : 1 - ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
    have hX : 0 ≤ ∑ s, Ω.prob s * C2 s ^ (1 - ρ) :=
      Finset.sum_nonneg fun s _ =>
        mul_nonneg (Ω.prob_nonneg s) (Real.rpow_nonneg (hC2 s) _)
    simp only [crraU, riskIndex, cesIndex, h1, ite_false]
    rw [one_div, Real.rpow_inv_rpow hX h1ρ, Finset.sum_div]
    exact Finset.sum_congr rfl fun s _ => by ring

/-- (26) with `σ = 1/ρ` represents the expected-utility ordering, O&R p. 284: for all plans
with nonnegative date-2 consumption, `U^{EZ}(C) ≤ U^{EZ}(C′)` iff
`U^{EU}(C) ≤ U^{EU}(C′)`. -/
theorem ez_le_iff_expectedUtility (Ω : StateSpace S) (ρ β C1 C1' : ℝ)
    {C2 C2' : S → ℝ} (hC2 : ∀ s, 0 ≤ C2 s) (hC2' : ∀ s, 0 ≤ C2' s) :
    ezUtility Ω ρ (1 / ρ) β C1 C2 ≤ ezUtility Ω ρ (1 / ρ) β C1' C2' ↔
      expectedUtility Ω ρ β C1 C2 ≤ expectedUtility Ω ρ β C1' C2' := by
  rw [ez_eq_expectedUtility Ω ρ β C1 hC2, ez_eq_expectedUtility Ω ρ β C1' hC2']

/-- The expected-utility optimum is the two-stage optimum with `σ = 1/ρ`, O&R p. 284: for
`ρ > 0`, `π, p > 0`, `β, W₁ > 0`, `1 + r > 0`, the plan
`C₁* = W₁/(1 + ((1+r)/P)^{1/ρ−1}β^{1/ρ})`, `C₂* = (24)` at `Z₂* = (1+r)(W₁ − C₁*)` maximises
expected utility over all positive plans with `C₁ + Σ p(s)C₂(s)/(1+r) = W₁`, and is the unique
maximiser. -/
theorem expectedUtility_two_stage_optimal (Ω : StateSpace S) (hπ : ∀ s, 0 < Ω.prob s)
    (p : S → ℝ) (hp : ∀ s, 0 < p s) {ρ r β W1 : ℝ} (hρ : 0 < ρ) (hr : 0 < 1 + r)
    (hβ : 0 < β) (hW : 0 < W1) :
    let P := riskPrice Ω ρ p
    let C1s := stageOneC1 (1 / ρ) r β P W1
    let C2s := riskDemand Ω ρ p (stageOneZ2 (1 / ρ) r β P W1)
    (0 < C1s ∧ (∀ s, 0 < C2s s) ∧ C1s + (∑ s, p s * C2s s) / (1 + r) = W1) ∧
    (∀ (C1 : ℝ) (C2 : S → ℝ), 0 < C1 → (∀ s, 0 < C2 s) →
      C1 + (∑ s, p s * C2 s) / (1 + r) = W1 →
      expectedUtility Ω ρ β C1 C2 ≤ expectedUtility Ω ρ β C1s C2s) ∧
    (∀ (C1 : ℝ) (C2 : S → ℝ), 0 < C1 → (∀ s, 0 < C2 s) →
      C1 + (∑ s, p s * C2 s) / (1 + r) = W1 →
      expectedUtility Ω ρ β C1s C2s ≤ expectedUtility Ω ρ β C1 C2 → C1 = C1s ∧ C2 = C2s) := by
  intro P C1s C2s
  obtain ⟨hfeas, hopt, huniq⟩ :=
    ez_two_stage_optimal Ω hπ p hp (σ := 1 / ρ) (r := r) (β := β) (W1 := W1) hρ
      (by positivity) hr hβ hW
  have hs : ∀ s, 0 ≤ C2s s := fun s => (hfeas.2.1 s).le
  refine ⟨hfeas, fun C1 C2 hC1 hC2 hbud => ?_, fun C1 C2 hC1 hC2 hbud hge => ?_⟩
  · have := hopt C1 C2 hC1 hC2 hbud
    rwa [ez_le_iff_expectedUtility Ω ρ β C1 _ (fun s => (hC2 s).le) hs] at this
  · refine huniq C1 C2 hC1 hC2 hbud ?_
    rwa [ez_le_iff_expectedUtility Ω ρ β _ C1 hs (fun s => (hC2 s).le)]

/-- "Only when `σ = 1/ρ`", O&R p. 284: for `ρ, σ, β > 0` and `π, p > 0`, the preferences (26)
rank all positive plans exactly as expected utility (with risk aversion `ρ`) does iff
`σ = 1/ρ`. The converse direction compares the unique optima at `W₁ = 1` and
`1 + r = P` and `1 + r = 2P`: equal date-1 consumption at both rates forces
`2^{σ−1} = 2^{1/ρ−1}`. -/
theorem ez_same_ordering_iff (Ω : StateSpace S) (hπ : ∀ s, 0 < Ω.prob s) (p : S → ℝ)
    (hp : ∀ s, 0 < p s) {ρ σ β : ℝ} (hρ : 0 < ρ) (hσ : 0 < σ) (hβ : 0 < β) :
    (∀ (C1 C1' : ℝ) (C2 C2' : S → ℝ), 0 < C1 → 0 < C1' → (∀ s, 0 < C2 s) →
      (∀ s, 0 < C2' s) →
      (ezUtility Ω ρ σ β C1 C2 ≤ ezUtility Ω ρ σ β C1' C2' ↔
        expectedUtility Ω ρ β C1 C2 ≤ expectedUtility Ω ρ β C1' C2')) ↔ σ = 1 / ρ := by
  constructor
  · intro hord
    obtain ⟨hP, -, -⟩ := risk_stage_two Ω hπ p hp hρ
    set P := riskPrice Ω ρ p with hPdef
    have key : ∀ R : ℝ, 0 < R →
        (R / P) ^ (σ - 1) * β ^ σ = (R / P) ^ (1 / ρ - 1) * β ^ (1 / ρ) := by
      intro R hR
      have hr : 0 < 1 + (R - 1) := by linarith
      obtain ⟨hf1, -, hu1⟩ := ez_two_stage_optimal Ω hπ p hp (σ := σ) (r := R - 1) (β := β)
        (W1 := 1) hρ hσ hr hβ one_pos
      obtain ⟨hf2, ho2, -⟩ := expectedUtility_two_stage_optimal Ω hπ p hp (r := R - 1)
        (β := β) (W1 := 1) hρ hr hβ one_pos
      have h1 := ho2 _ _ hf1.1 hf1.2.1 hf1.2.2
      have h2 := (hord _ _ _ _ hf1.1 hf2.1 hf1.2.1 hf2.2.1).mpr h1
      have h3 := (hu1 _ _ hf2.1 hf2.2.1 hf2.2.2 h2).1
      simp only [stageOneC1, show 1 + (R - 1) = R by ring, ← hPdef] at h3
      have hA : 0 < (R / P) ^ (σ - 1) * β ^ σ := by positivity
      have hB : 0 < (R / P) ^ (1 / ρ - 1) * β ^ (1 / ρ) := by positivity
      rw [div_eq_div_iff (by positivity) (by positivity)] at h3
      linarith
    have k1 := key P hP
    have k2 := key (2 * P) (by positivity)
    rw [div_self hP.ne', Real.one_rpow, Real.one_rpow, one_mul, one_mul] at k1
    rw [mul_div_assoc, div_self hP.ne', mul_one, k1] at k2
    have hb : 0 < β ^ (1 / ρ) := by positivity
    have k3 : (2 : ℝ) ^ (σ - 1) = 2 ^ (1 / ρ - 1) := mul_right_cancel₀ hb.ne' k2
    have k4 := congrArg Real.log k3
    rw [Real.log_rpow two_pos, Real.log_rpow two_pos] at k4
    have hl : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
    have := mul_right_cancel₀ hl k4
    linarith
  · intro h
    subst h
    intro C1 C1' C2 C2' _ _ hC2 hC2'
    exact ez_le_iff_expectedUtility Ω ρ β C1 C1' (fun s => (hC2 s).le) (fun s => (hC2' s).le)

/-! ## The current account under (26) (O&R p. 285, footnote 14) -/

/-- The current account at the optimum of (26), O&R footnote 14, p. 285: with
`W₁ = Y₁ + V/(1+r)`, `V = Σ p(s)Y₂(s) > 0`, the optimal `C₁` (stage 1 with elasticity `σ`) gives
`CA₁ = Y₁ − C₁ > 0` iff `r > r^CA`, `< 0` iff `r < r^CA`, `= 0` iff `r = r^CA`, where
`1 + r^CA = (1/β)[V/(P^{1−σ}Y₁)]^{1/σ}`. -/
theorem ez_current_account_sign {σ r β P Y1 V : ℝ} (hσ : 0 < σ) (hr : 0 < 1 + r)
    (hβ : 0 < β) (hP : 0 < P) (hY1 : 0 < Y1) (hV : 0 < V) :
    (0 < Y1 - stageOneC1 σ r β P (Y1 + V / (1 + r)) ↔
        1 / β * (V / (P ^ (1 - σ) * Y1)) ^ (1 / σ) < 1 + r) ∧
      (Y1 - stageOneC1 σ r β P (Y1 + V / (1 + r)) < 0 ↔
        1 + r < 1 / β * (V / (P ^ (1 - σ) * Y1)) ^ (1 / σ)) ∧
      (Y1 - stageOneC1 σ r β P (Y1 + V / (1 + r)) = 0 ↔
        1 + r = 1 / β * (V / (P ^ (1 - σ) * Y1)) ^ (1 / σ)) :=
  current_account_sign_rCA hσ hr hβ hP hY1 hV

/-- Risk and the current account under (26), O&R p. 285: with `P < 1` (prices not actuarially
fair), optimal `C₁` is strictly below its certainty benchmark (`P = 1`) if `σ > 1` and strictly
above it if `σ < 1`, whatever the risk aversion `ρ`; and with `β(1+r) = 1`,
`Y₁ = V = Σ p(s)Y₂(s)`, the optimum has `CA₁ > 0` if `σ > 1` and `CA₁ < 0` if `σ < 1`. -/
theorem ez_consumption_vs_certainty {σ r β P W1 Y1 : ℝ} (hr : 0 < 1 + r) (hβ : 0 < β)
    (hP0 : 0 < P) (hP1 : P < 1) (hW : 0 < W1) (hY1 : 0 < Y1) :
    (1 < σ → stageOneC1 σ r β P W1 < stageOneC1 σ r β 1 W1) ∧
      (σ < 1 → stageOneC1 σ r β 1 W1 < stageOneC1 σ r β P W1) ∧
      (β * (1 + r) = 1 → (1 < σ → 0 < Y1 - stageOneC1 σ r β P (Y1 + Y1 / (1 + r))) ∧
        (σ < 1 → Y1 - stageOneC1 σ r β P (Y1 + Y1 / (1 + r)) < 0)) := by
  have h := consumption_vs_certainty (σ := σ) hr hβ hP0 hP1 hW
  simp only [stageOneC1, div_one]
  exact ⟨h.1, h.2, fun hβR => current_account_fair_rate hr hβR hP0 hP1 hY1⟩

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

**Appendix 5C, infinite horizon.** A plan `C : (n : ℕ) → (Fin n → S) → ℝ` assigns consumption
to every history of every date `t = n + 1` (date 1 is `n = 0`). Lifetime expected utility (82)
is the infinite sum `Σ_n β^n Σ_h π(h) u(C n h)` and the budget constraint (83) equates infinite
sums of date-1 values `Σ_n Σ_h P(h) x(h)`, with prices `P(h_t) = R_{1,t} p(h_t|h_1)` in date-1
output; a plan is admissible when these series converge (explicit `Summable` hypotheses). We
prove that the first-order conditions (84) with the budget give a global optimum when `u` is
concave (supporting-line inequality summed with `tsum`), and conversely that an interior optimum
with differentiable `u` satisfies (84) at every history (single-history perturbation); the
bond Euler equation (85) and the analogue of (9) follow. In the CRRA economy, under the primitive
condition that `Σ_t β^{t−1} E[(Y^W)^{−ρ} Y^n]` converges for every country, the prices, the
present-value shares `μ^n` and `C^n = μ^n Y^W` form an equilibrium (first-order conditions,
infinite budget, market clearing, optimality); conversely the first-order conditions and market
clearing force constant shares, and the infinite budget pins down `μ^n`. `R_{1,t}` is given in
closed form. The log case `ρ = 1` is covered too, with the one extra primitive condition that
`Σ_t β^{t−1} E log Y^W` converges (and `β < 1`). Finite-horizon versions of the optimality and
budget results are kept as lemmas.

**Appendix 5D.** Prices in date-1 units `p̃ = p R`; from (86) the date-1 plan satisfies
(88), which by Bayes' rule and the no-arbitrage identity `p̃(h_t|h_1)/p̃(h_2|h_1) = p̃(h_t|h_2)`
(taken as a hypothesis, as in the book's arbitrage argument, which is about the trading
technology rather than a consequence of the model's primitives) is (87). Over the infinite
horizon the continuation of the date-1 plan after any date-2 event with positive probability is
admissible (when its utility series converges absolutely) and optimal for the date-2 problem
with reopened markets (dynamic consistency).

**Supplement A.** (The infinite-horizon consumption–portfolio problem with its Bellman
equation and verification theorem is in `ConsumptionPortfolio`.) Log utility gives the
consumption share `μ = 1 − β`; the CRRA share
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

/-- The probability of a history extended by one event, `π(h_{t+1}|h_1) = π(h_t|h_1) q(s|h_t)`
where `h_{t+1} = {s} ∪ h_t` (O&R Appendix 5C, p. 341). -/
theorem histProb_snoc {n : ℕ} (h : Fin n → S) (s : S) :
    tr.histProb (Fin.snoc h s : Fin (n + 1) → S) = tr.histProb h * tr.q n h s := by
  simp only [histProb, condProb, Nat.Ico_zero_eq_range]
  rw [Finset.prod_range_succ, tr.step_snoc_last]
  congr 1
  exact Finset.prod_congr rfl fun i hi => tr.step_snoc_lt h s (Finset.mem_range.mp hi)

/-- The date-1 history has probability one, `π(h_1|h_1) = 1` (O&R Appendix 5C, p. 341). -/
theorem histProb_zero (h : Fin 0 → S) : tr.histProb h = 1 := by
  simp [histProb, condProb]

/-- The probability of the date-2 history `{s}` is the first one-step probability
`π(h_2|h_1) = q(s|h_1)` (O&R Appendix 5D, p. 344). -/
theorem histProb_one (s : S) : tr.histProb (fun _ : Fin 1 => s) = tr.q 0 Fin.elim0 s := by
  have e : restr (fun _ : Fin 1 => s) 0 (Nat.zero_le 1) = Fin.elim0 := Subsingleton.elim _ _
  simp [histProb, condProb, step, e]

/-- A date-`t` history's probability factors through its date-2 event,
`π(h_t|h_1) = π(h_2|h_1) π(h_t|h_2)` (O&R Appendix 5D, p. 344, and footnote 53). -/
theorem histProb_eq_first_mul_condProb {m : ℕ} (h : Fin (m + 1) → S) :
    tr.histProb h = tr.q 0 Fin.elim0 (h 0) * tr.condProb h 1 := by
  have e : restr h 0 (Nat.zero_le _) = Fin.elim0 := Subsingleton.elim _ _
  have h1 : tr.histProb (restr h 1 (by omega)) = tr.q 0 Fin.elim0 (h 0) := by
    rw [tr.histProb_restr_one h (by omega)]
    simp only [step, Nat.zero_lt_succ, dite_true, e]
    rfl
  rw [histProb, tr.condProb_chain h (Nat.zero_le 1) (by omega), ← histProb, h1]

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

/-- Finite-horizon lemma (the infinite-horizon statement is `arrowDebreu_optimal_infinite`).
The many-period Arrow–Debreu problem, O&R (82)–(84), pp. 341–342, over a finite horizon
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

/-- Finite-horizon present value (the infinite-horizon one is `dateOneValue`): the value at
date 1 of a history-contingent stream `x` through date `T`, in date-1 output (O&R (83), p. 341):
`x₁ + Σ_t R_{1,t} Σ_{h_t} p(h_t|h_1) x(h_t)`. -/
noncomputable def presentValue (T : ℕ) (R : ℕ → ℝ) (p : (n : ℕ) → (Fin n → S) → ℝ)
    (x₁ : ℝ) (x : (n : ℕ) → (Fin n → S) → ℝ) : ℝ :=
  x₁ + ∑ n ∈ Ico 1 T, R n * ∑ h, p n h * x n h

/-- Finite-horizon lemma (the infinite-horizon statement is part of
`crra_equilibrium_infinite`). The budget constraint (83) at the constant-share plan, O&R
Appendix 5C.3, p. 342: at any prices, if `μ` is country `n`'s share of the date-1 present
value of world output, the plan
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

/-- Finite-horizon lemma (the infinite-horizon statement is `dynamic_consistency_infinite`).
Dynamic consistency, O&R Appendix 5D, pp. 343–344. Suppose the date-1 plan `(C₁, C)`
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

/-! ## Appendix 5C with the book's infinite horizon

A plan is `C : (n : ℕ) → (Fin n → S) → ℝ` over all dates `t = n + 1`, date 1 being `n = 0`
(the unique empty history). Prices `P n h` are in date-1 output, `P(h_t) = R_{1,t} p(h_t|h_1)`
(the book's `p̃` of Appendix 5D), with `P(h_1) = 1`. -/

/-- A sum over date-`(t+1)` histories is a sum over date-`t` histories and the next event
(O&R Appendix 5C, p. 341: `h_{t+1} = {s_{t+1}} ∪ h_t`). -/
theorem sum_snoc {n : ℕ} (f : (Fin (n + 1) → S) → ℝ) :
    ∑ g, f g = ∑ h : Fin n → S, ∑ s, f (Fin.snoc h s) := by
  rw [← (Fin.snocEquiv (fun _ : Fin (n + 1) => S)).sum_comp, Fintype.sum_prod_type,
    Finset.sum_comm]
  rfl

/-- CRRA utility `u(C) = C^{1−ρ}/(1−ρ)`, O&R Appendix 5C.3, p. 342 (and Supplement A). -/
noncomputable def crraUtil (ρ C : ℝ) : ℝ := C ^ (1 - ρ) / (1 - ρ)

/-- The supporting-line inequality for CRRA utility (concavity), used for O&R Appendix 5C.3
and Supplement A: for `ρ > 0`, `ρ ≠ 1`, `x, y > 0`,
`y^{1−ρ}/(1−ρ) ≤ x^{1−ρ}/(1−ρ) + x^{−ρ}(y − x)`. -/
theorem crra_tangent {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≠ 1) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    crraUtil ρ y ≤ crraUtil ρ x + x ^ (-ρ) * (y - x) := by
  unfold crraUtil
  set t := y / x with ht_def
  have ht : 0 < t := div_pos hy hx
  have hyx : y = x * t := by rw [ht_def]; field_simp
  have hy' : y ^ (1 - ρ) = x ^ (1 - ρ) * t ^ (1 - ρ) := by rw [hyx, Real.mul_rpow hx.le ht.le]
  have hxr : x ^ (-ρ) * (y - x) = x ^ (1 - ρ) * (t - 1) := by
    rw [show (1 : ℝ) - ρ = -ρ + 1 by ring, Real.rpow_add hx, Real.rpow_one, hyx]; ring
  have hxp : 0 < x ^ (1 - ρ) := Real.rpow_pos_of_pos hx _
  rw [hy', hxr]
  have key : t ^ (1 - ρ) / (1 - ρ) ≤ 1 / (1 - ρ) + (t - 1) := by
    rcases lt_or_gt_of_ne hρ1 with h | h
    · have hp : 0 < 1 - ρ := by linarith
      have b := rpow_one_add_le_one_add_mul_self (s := t - 1) (by linarith) hp.le
        (by linarith)
      rw [show 1 + (t - 1) = t by ring] at b
      have e : t ^ (1 - ρ) / (1 - ρ) - (1 / (1 - ρ) + (t - 1))
          = (t ^ (1 - ρ) - (1 + (1 - ρ) * (t - 1))) / (1 - ρ) := by field_simp
      have : (t ^ (1 - ρ) - (1 + (1 - ρ) * (t - 1))) / (1 - ρ) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (by linarith) hp.le
      linarith
    · have hp : 1 - ρ < 0 := by linarith
      have e1 : 1 + (1 - ρ) * Real.log t ≤ t ^ (1 - ρ) := by
        rw [Real.rpow_def_of_pos ht]
        have := Real.add_one_le_exp (Real.log t * (1 - ρ))
        linarith [mul_comm (Real.log t) (1 - ρ)]
      have e2 : Real.log t ≤ t - 1 := Real.log_le_sub_one_of_pos ht
      have e3 : (1 - ρ) * (t - 1) ≤ (1 - ρ) * Real.log t := mul_le_mul_of_nonpos_left e2 hp.le
      have e : t ^ (1 - ρ) / (1 - ρ) - (1 / (1 - ρ) + (t - 1))
          = (t ^ (1 - ρ) - (1 + (1 - ρ) * (t - 1))) / (1 - ρ) := by field_simp
      have : (t ^ (1 - ρ) - (1 + (1 - ρ) * (t - 1))) / (1 - ρ) ≤ 0 :=
        div_nonpos_of_nonneg_of_nonpos (by linarith) hp.le
      linarith
  calc x ^ (1 - ρ) * t ^ (1 - ρ) / (1 - ρ) = x ^ (1 - ρ) * (t ^ (1 - ρ) / (1 - ρ)) := by ring
    _ ≤ x ^ (1 - ρ) * (1 / (1 - ρ) + (t - 1)) := mul_le_mul_of_nonneg_left key hxp.le
    _ = x ^ (1 - ρ) / (1 - ρ) + x ^ (1 - ρ) * (t - 1) := by ring

/-- The date-`t` term of lifetime expected utility (82), O&R p. 341 (`t = n + 1`):
`β^{t−1} Σ_{h_t} π(h_t|h_1) u(C(h_t))`; the date-1 term (`n = 0`) is `u(C₁)`. -/
noncomputable def utilSeries (tr : Tree S) (β : ℝ) (u : ℝ → ℝ)
    (C : (n : ℕ) → (Fin n → S) → ℝ) (n : ℕ) : ℝ :=
  β ^ n * ∑ h, tr.histProb h * u (C n h)

/-- Lifetime expected utility (82), O&R p. 341, over the infinite horizon:
`U₁ = u(C₁) + Σ_{t≥2} β^{t−1} Σ_{h_t} π(h_t|h_1) u(C(h_t))`. It is meaningful for plans whose
series `utilSeries` is summable (admissible plans); results always assume that explicitly. -/
noncomputable def expectedUtility (tr : Tree S) (β : ℝ) (u : ℝ → ℝ)
    (C : (n : ℕ) → (Fin n → S) → ℝ) : ℝ :=
  ∑' n, utilSeries tr β u C n

/-- The date-`t` term `Σ_{h_t} P(h_t) x(h_t)` of the date-1 value of a contingent stream `x`
at date-1 prices `P(h_t) = R_{1,t} p(h_t|h_1)` (O&R (83), p. 341). -/
noncomputable def valueSeries (P x : (n : ℕ) → (Fin n → S) → ℝ) (n : ℕ) : ℝ :=
  ∑ h, P n h * x n h

/-- The date-1 value of a contingent stream `x`, the two sides of the budget constraint (83),
O&R p. 341: `Σ_{t≥1} Σ_{h_t} P(h_t) x(h_t)` (meaningful when `valueSeries` is summable). -/
noncomputable def dateOneValue (P x : (n : ℕ) → (Fin n → S) → ℝ) : ℝ :=
  ∑' n, valueSeries P x n

/-- Lifetime expected utility in the book's form (82), O&R p. 341:
`U₁ = u(C₁) + Σ_{t=2}^∞ β^{t−1} Σ_{h_t} π(h_t|h_1) u(C(h_t))`, for an admissible plan. -/
theorem expectedUtility_eq_book (tr : Tree S) (β : ℝ) (u : ℝ → ℝ)
    (C : (n : ℕ) → (Fin n → S) → ℝ) (hU : Summable (utilSeries tr β u C)) :
    expectedUtility tr β u C = u (C 0 Fin.elim0)
      + ∑' n, β ^ (n + 1) * ∑ h : Fin (n + 1) → S, tr.histProb h * u (C (n + 1) h) := by
  rw [expectedUtility, hU.tsum_eq_zero_add]
  congr 1
  rw [utilSeries, Fintype.sum_unique, tr.histProb_zero, Subsingleton.elim default Fin.elim0]
  ring

/-- The budget constraint's value in the book's form (83), O&R p. 341: with `P(h_1) = 1` and
`P(h_t) = R_{1,t} p(h_t|h_1)`, the date-1 value of `x` is
`x₁ + Σ_{t=2}^∞ R_{1,t} Σ_{h_t} p(h_t|h_1) x(h_t)`. -/
theorem dateOneValue_eq_book (R : ℕ → ℝ) (p P x : (n : ℕ) → (Fin n → S) → ℝ)
    (hP0 : P 0 Fin.elim0 = 1) (hP : ∀ n h, P (n + 1) h = R (n + 1) * p (n + 1) h)
    (hV : Summable (valueSeries P x)) :
    dateOneValue P x = x 0 Fin.elim0 + ∑' n, R (n + 1) * ∑ h, p (n + 1) h * x (n + 1) h := by
  rw [dateOneValue, hV.tsum_eq_zero_add]
  congr 1
  · rw [valueSeries, Fintype.sum_unique, Subsingleton.elim default Fin.elim0, hP0, one_mul]
  · refine tsum_congr fun n => ?_
    rw [valueSeries, Finset.mul_sum]
    exact Finset.sum_congr rfl fun h _ => by rw [hP]; ring

/-- Sufficiency of the first-order conditions over an infinite horizon (O&R Appendix 5C,
pp. 341–342, and Appendix 5D, p. 344): the supporting-line inequality summed with `tsum`.
Dates `n : ℕ` carry finitely many nodes `h ∈ A n` with utility weights `w ≥ 0` and prices `q`.
If `u` lies below its tangent lines of slope `du`, the plan `c` satisfies
`q(h) λ = w(h) u′(c(h))` with multiplier `λ ≥ 0`, both plans have convergent utility and value
series, and `c′` costs no more than `c`, then `c′` gives no more utility. -/
theorem foc_plan_optimal_tsum {H : ℕ → Type} (A : (n : ℕ) → Finset (H n)) (u du : ℝ → ℝ)
    (htan : ∀ x y, 0 < x → 0 < y → u y ≤ u x + du x * (y - x))
    (w q : (n : ℕ) → H n → ℝ) (hw : ∀ n, ∀ h ∈ A n, 0 ≤ w n h) {lam : ℝ} (hlam : 0 ≤ lam)
    {c c' : (n : ℕ) → H n → ℝ} (hc : ∀ n, ∀ h ∈ A n, 0 < c n h)
    (hc' : ∀ n, ∀ h ∈ A n, 0 < c' n h)
    (hfoc : ∀ n, ∀ h ∈ A n, q n h * lam = w n h * du (c n h))
    (hU : Summable fun n => ∑ h ∈ A n, w n h * u (c n h))
    (hU' : Summable fun n => ∑ h ∈ A n, w n h * u (c' n h))
    (hV : Summable fun n => ∑ h ∈ A n, q n h * c n h)
    (hV' : Summable fun n => ∑ h ∈ A n, q n h * c' n h)
    (hbud : ∑' n, ∑ h ∈ A n, q n h * c' n h ≤ ∑' n, ∑ h ∈ A n, q n h * c n h) :
    ∑' n, ∑ h ∈ A n, w n h * u (c' n h) ≤ ∑' n, ∑ h ∈ A n, w n h * u (c n h) := by
  have key : ∀ n, ∑ h ∈ A n, w n h * u (c' n h) ≤ ∑ h ∈ A n, w n h * u (c n h)
      + lam * (∑ h ∈ A n, q n h * c' n h - ∑ h ∈ A n, q n h * c n h) := by
    intro n
    rw [mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun h hh => ?_
    have t := htan _ _ (hc n h hh) (hc' n h hh)
    have t2 := mul_le_mul_of_nonneg_left t (hw n h hh)
    have e : lam * (q n h * c' n h) - lam * (q n h * c n h)
        = w n h * du (c n h) * (c' n h - c n h) := by
      rw [show lam * (q n h * c' n h) - lam * (q n h * c n h)
        = q n h * lam * (c' n h - c n h) by ring, hfoc n h hh]
    rw [e]; nlinarith
  have hR := hU.add ((hV'.sub hV).mul_left lam)
  have h1 := Summable.tsum_le_tsum key hU' hR
  rw [Summable.tsum_add hU ((hV'.sub hV).mul_left lam), Summable.tsum_mul_left lam (hV'.sub hV),
    Summable.tsum_sub hV' hV] at h1
  have hgap : lam * (∑' n, ∑ h ∈ A n, q n h * c' n h - ∑' n, ∑ h ∈ A n, q n h * c n h) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hlam (by linarith)
  linarith

/-- O&R (82)–(84), pp. 341–342, over the book's infinite horizon: if the plan `C` satisfies the
first-order conditions (84), `R_{1,t} p(h_t|h_1) u′(C₁) = π(h_t|h_1) β^{t−1} u′(C(h_t))` (in
date-1 prices `P = R p`, at every date including date 1), exhausts the budget (83), and `u` is
concave with `u′(C₁) ≥ 0`, then every positive admissible plan `C′` (convergent utility and
budget series) satisfying the budget constraint (83) gives no more lifetime expected utility. -/
theorem arrowDebreu_optimal_infinite (tr : Tree S) (u du : ℝ → ℝ)
    (htan : ∀ x y, 0 < x → 0 < y → u y ≤ u x + du x * (y - x)) {β : ℝ} (hβ : 0 ≤ β)
    (P Y : (n : ℕ) → (Fin n → S) → ℝ) {C C' : (n : ℕ) → (Fin n → S) → ℝ}
    (hC : ∀ n h, 0 < C n h) (hC' : ∀ n h, 0 < C' n h) (hdu : 0 ≤ du (C 0 Fin.elim0))
    (hfoc : ∀ n h, P n h * du (C 0 Fin.elim0) = tr.histProb h * β ^ n * du (C n h))
    (hU : Summable (utilSeries tr β u C)) (hU' : Summable (utilSeries tr β u C'))
    (hV : Summable (valueSeries P C)) (hV' : Summable (valueSeries P C'))
    (hbud : dateOneValue P C = dateOneValue P Y) (hbud' : dateOneValue P C' ≤ dateOneValue P Y) :
    expectedUtility tr β u C' ≤ expectedUtility tr β u C := by
  have e : ∀ D : (n : ℕ) → (Fin n → S) → ℝ, utilSeries tr β u D
      = fun n => ∑ h ∈ univ, β ^ n * tr.histProb h * u (D n h) := by
    intro D; funext n
    rw [utilSeries, Finset.mul_sum]
    exact Finset.sum_congr rfl fun h _ => by ring
  unfold expectedUtility
  rw [e C] at hU; rw [e C'] at hU'; rw [e C, e C']
  unfold dateOneValue valueSeries at hbud hbud'
  unfold valueSeries at hV hV'
  exact foc_plan_optimal_tsum (fun _ => univ) u du htan (fun n h => β ^ n * tr.histProb h) P
    (fun n h _ => mul_nonneg (pow_nonneg hβ n) (tr.histProb_nonneg h)) hdu
    (fun n h _ => hC n h) (fun n h _ => hC' n h)
    (fun n h _ => by rw [hfoc n h]; ring) hU hU' hV hV' (by rw [← hbud] at hbud'; exact hbud')

/-- The noncontingent-bond Euler equation (85), O&R p. 342, from the plan's first-order
conditions (84) in date-1 prices: with `R_{1,t} = Σ_{h_t} P(h_t)` (the date-1 price of a sure
unit on date `t`, since `Σ p(h_t|h_1) = 1`), `u′(C₁) = (β^{t−1}/R_{1,t}) E₁ u′(C(h_t))`. -/
theorem euler_bond_plan (tr : Tree S) (du : ℝ → ℝ) (β : ℝ)
    (P C : (n : ℕ) → (Fin n → S) → ℝ)
    (hfoc : ∀ n h, P n h * du (C 0 Fin.elim0) = tr.histProb h * β ^ n * du (C n h))
    (n : ℕ) (hR : ∑ h, P n h ≠ 0) :
    du (C 0 Fin.elim0) = β ^ n / (∑ h, P n h) * ∑ h, tr.histProb h * du (C n h) := by
  have hs : ∑ h, P n h * du (C 0 Fin.elim0) = ∑ h, tr.histProb h * β ^ n * du (C n h) :=
    Finset.sum_congr rfl fun h _ => hfoc n h
  rw [← Finset.sum_mul] at hs
  have e : ∑ h, tr.histProb h * β ^ n * du (C n h) = β ^ n * ∑ h, tr.histProb h * du (C n h) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun h _ => by ring
  rw [e] at hs
  field_simp
  linarith

/-- One unit of consumption at the single date-`(n+1)` history `h` and nothing elsewhere: the
direction of the single-history perturbation behind the necessity of (84), O&R p. 342. -/
noncomputable def histBump [DecidableEq S] (n : ℕ) (h : Fin n → S) :
    (m : ℕ) → (Fin m → S) → ℝ :=
  fun m g => if (⟨m, g⟩ : (k : ℕ) × (Fin k → S)) = ⟨n, h⟩ then 1 else 0

omit [Fintype S] in
/-- The bump at `h` evaluated at a history `g` of the same date (O&R p. 342). -/
theorem histBump_self [DecidableEq S] {n : ℕ} (h g : Fin n → S) :
    histBump n h n g = if g = h then 1 else 0 := by
  simp [histBump]

omit [Fintype S] in
/-- The bump at a date-`(n+1)` history vanishes at every other date (O&R p. 342). -/
theorem histBump_ne [DecidableEq S] {n m : ℕ} (h : Fin n → S) (g : Fin m → S) (hm : m ≠ n) :
    histBump n h m g = 0 := by
  simp [histBump, hm]

/-- The single-history perturbation of a plan (O&R Appendix 5C, p. 342): `ε` more consumption at
the date-`(n+1)` history `h`, paid for by `ε P(h)` less date-1 consumption. -/
noncomputable def perturbPlan [DecidableEq S] (C P : (n : ℕ) → (Fin n → S) → ℝ) (n : ℕ)
    (h : Fin n → S) (ε : ℝ) : (m : ℕ) → (Fin m → S) → ℝ :=
  fun m g => C m g + ε * histBump n h m g - ε * P n h * histBump 0 Fin.elim0 m g

/-- The utility series of the perturbed plan differs from the original in two terms only
(O&R Appendix 5C, p. 342). -/
theorem utilSeries_perturbPlan [DecidableEq S] (tr : Tree S) (β : ℝ) (u : ℝ → ℝ)
    (C P : (n : ℕ) → (Fin n → S) → ℝ) {n : ℕ} (hn : n ≠ 0) (h : Fin n → S) (ε : ℝ) (m : ℕ) :
    utilSeries tr β u (perturbPlan C P n h ε) m = utilSeries tr β u C m
      + (if m = n then β ^ n * (tr.histProb h * (u (C n h + ε) - u (C n h))) else 0)
      + (if m = 0 then u (C 0 Fin.elim0 - ε * P n h) - u (C 0 Fin.elim0) else 0) := by
  by_cases hm0 : m = 0
  · subst hm0
    have hn' : (0 : ℕ) ≠ n := fun e => hn e.symm
    have hb : histBump 0 (Fin.elim0 : Fin 0 → S) 0 Fin.elim0 = 1 := by
      rw [histBump_self]; simp
    simp only [utilSeries, perturbPlan, Fintype.sum_unique, hn', ↓reduceIte,
      histBump_ne h _ hn', hb, tr.histProb_zero, Subsingleton.elim (default : Fin 0 → S) Fin.elim0]
    ring_nf
  · by_cases hmn : m = n
    · subst hmn
      have hs : ∑ g, tr.histProb g * u (C m g + ε * histBump m h m g
            - ε * P m h * histBump 0 Fin.elim0 m g) - ∑ g, tr.histProb g * u (C m g)
          = tr.histProb h * (u (C m h + ε) - u (C m h)) := by
        rw [← Finset.sum_sub_distrib, Finset.sum_eq_single h]
        · simp [histBump_self, histBump_ne _ _ hm0]; ring
        · intro g _ hg
          simp [histBump_self, histBump_ne _ _ hm0, hg]
        · intro hh; exact absurd (Finset.mem_univ h) hh
      simp only [utilSeries, perturbPlan, hm0, ↓reduceIte]
      linear_combination β ^ m * hs
    · simp [utilSeries, perturbPlan, histBump_ne _ _ hmn, histBump_ne _ _ hm0, hmn, hm0]

/-- The date-1 value series of the perturbed plan: `ε P(h)` more at date `n + 1`, `ε P(h)` less at
date 1, when `P(h_1) = 1` (O&R Appendix 5C, p. 342). -/
theorem valueSeries_perturbPlan [DecidableEq S] (C P : (n : ℕ) → (Fin n → S) → ℝ)
    (hP0 : P 0 Fin.elim0 = 1) {n : ℕ} (hn : n ≠ 0) (h : Fin n → S) (ε : ℝ) (m : ℕ) :
    valueSeries P (perturbPlan C P n h ε) m = valueSeries P C m
      + (if m = n then P n h * ε else 0) + (if m = 0 then -(ε * P n h) else 0) := by
  by_cases hm0 : m = 0
  · subst hm0
    have hn' : (0 : ℕ) ≠ n := fun e => hn e.symm
    have hb : histBump 0 (Fin.elim0 : Fin 0 → S) 0 Fin.elim0 = 1 := by
      rw [histBump_self]; simp
    simp only [valueSeries, perturbPlan, Fintype.sum_unique, hn', ↓reduceIte,
      histBump_ne h _ hn', hb, Subsingleton.elim (default : Fin 0 → S) Fin.elim0, hP0]
    ring
  · by_cases hmn : m = n
    · subst hmn
      have hs : ∑ g, P m g * (C m g + ε * histBump m h m g
            - ε * P m h * histBump 0 Fin.elim0 m g) - ∑ g, P m g * C m g = P m h * ε := by
        rw [← Finset.sum_sub_distrib, Finset.sum_eq_single h]
        · simp [histBump_self, histBump_ne _ _ hm0]; ring
        · intro g _ hg
          simp [histBump_self, histBump_ne _ _ hm0, hg]
        · intro hh; exact absurd (Finset.mem_univ h) hh
      simp only [valueSeries, perturbPlan, hm0, ↓reduceIte]
      linear_combination hs
    · simp [valueSeries, perturbPlan, histBump_ne _ _ hmn, histBump_ne _ _ hm0, hmn, hm0]

/-- Necessity of the first-order conditions (84), O&R p. 342, over the infinite horizon. Let
prices be in date-1 output with `P(h_1) = 1`, let `u` be differentiable on `(0, ∞)` with
derivative `du`, and let the positive admissible plan `C` be optimal: it satisfies the budget
(83) and no positive admissible plan satisfying (83) gives more expected utility (82). Then at
every history `R_{1,t} p(h_t|h_1) u′(C₁) = π(h_t|h_1) β^{t−1} u′(C(h_t))`. The proof perturbs
consumption at the single history `h_t` against date-1 consumption, which keeps the plan
admissible (only two terms of each series change) and within the budget. -/
theorem arrowDebreu_foc_necessary (tr : Tree S) (u du : ℝ → ℝ)
    (hu : ∀ x, 0 < x → HasDerivAt u (du x) x) (β : ℝ) (P Y : (n : ℕ) → (Fin n → S) → ℝ)
    (hP0 : P 0 Fin.elim0 = 1) {C : (n : ℕ) → (Fin n → S) → ℝ} (hC : ∀ n h, 0 < C n h)
    (hU : Summable (utilSeries tr β u C)) (hV : Summable (valueSeries P C))
    (hbud : dateOneValue P C ≤ dateOneValue P Y)
    (hopt : ∀ C' : (n : ℕ) → (Fin n → S) → ℝ, (∀ n h, 0 < C' n h) →
      Summable (utilSeries tr β u C') → Summable (valueSeries P C') →
      dateOneValue P C' ≤ dateOneValue P Y → expectedUtility tr β u C' ≤ expectedUtility tr β u C)
    (n : ℕ) (h : Fin n → S) :
    P n h * du (C 0 Fin.elim0) = tr.histProb h * β ^ n * du (C n h) := by
  classical
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    rw [Subsingleton.elim h Fin.elim0, hP0, tr.histProb_zero]; ring
  have hn0 : n ≠ 0 := hn.ne'
  have hsa : ∀ ε : ℝ, Summable (fun m : ℕ =>
      if m = n then β ^ n * (tr.histProb h * (u (C n h + ε) - u (C n h))) else 0) :=
    fun ε => (hasSum_ite_eq n _).summable
  have hsb : ∀ ε : ℝ, Summable (fun m : ℕ =>
      if m = 0 then u (C 0 Fin.elim0 - ε * P n h) - u (C 0 Fin.elim0) else 0) :=
    fun ε => (hasSum_ite_eq 0 _).summable
  have hUe : ∀ ε, utilSeries tr β u (perturbPlan C P n h ε) = fun m => utilSeries tr β u C m
      + (if m = n then β ^ n * (tr.histProb h * (u (C n h + ε) - u (C n h))) else 0)
      + (if m = 0 then u (C 0 Fin.elim0 - ε * P n h) - u (C 0 Fin.elim0) else 0) :=
    fun ε => funext (utilSeries_perturbPlan tr β u C P hn0 h ε)
  have hSU : ∀ ε, Summable (utilSeries tr β u (perturbPlan C P n h ε)) := by
    intro ε; rw [hUe]; exact (hU.add (hsa ε)).add (hsb ε)
  have hEU : ∀ ε, expectedUtility tr β u (perturbPlan C P n h ε) = expectedUtility tr β u C
      + β ^ n * (tr.histProb h * (u (C n h + ε) - u (C n h)))
      + (u (C 0 Fin.elim0 - ε * P n h) - u (C 0 Fin.elim0)) := by
    intro ε; unfold expectedUtility
    rw [hUe, Summable.tsum_add (hU.add (hsa ε)) (hsb ε), Summable.tsum_add hU (hsa ε),
      tsum_ite_eq, tsum_ite_eq]
  have hsc : ∀ ε : ℝ, Summable (fun m : ℕ => if m = n then P n h * ε else 0) :=
    fun ε => (hasSum_ite_eq n _).summable
  have hsd : ∀ ε : ℝ, Summable (fun m : ℕ => if m = 0 then -(ε * P n h) else 0) :=
    fun ε => (hasSum_ite_eq 0 _).summable
  have hVe : ∀ ε, valueSeries P (perturbPlan C P n h ε) = fun m => valueSeries P C m
      + (if m = n then P n h * ε else 0) + (if m = 0 then -(ε * P n h) else 0) :=
    fun ε => funext (valueSeries_perturbPlan C P hP0 hn0 h ε)
  have hSV : ∀ ε, Summable (valueSeries P (perturbPlan C P n h ε)) := by
    intro ε; rw [hVe]; exact (hV.add (hsc ε)).add (hsd ε)
  have hDV : ∀ ε, dateOneValue P (perturbPlan C P n h ε) = dateOneValue P C := by
    intro ε; unfold dateOneValue
    rw [hVe, Summable.tsum_add (hV.add (hsc ε)) (hsd ε), Summable.tsum_add hV (hsc ε),
      tsum_ite_eq, tsum_ite_eq]
    ring
  have hpos : ∀ᶠ ε in nhds (0 : ℝ), 0 < C 0 Fin.elim0 - ε * P n h ∧ 0 < C n h + ε := by
    have c1 : ContinuousAt (fun ε : ℝ => C 0 Fin.elim0 - ε * P n h) 0 := by fun_prop
    have c2 : ContinuousAt (fun ε : ℝ => C n h + ε) 0 := by fun_prop
    exact (c1.eventually (lt_mem_nhds (by simpa using hC 0 Fin.elim0))).and
      (c2.eventually (lt_mem_nhds (by simpa using hC n h)))
  have hmax : IsLocalMax (fun ε => expectedUtility tr β u C
      + β ^ n * (tr.histProb h * (u (C n h + ε) - u (C n h)))
      + (u (C 0 Fin.elim0 - ε * P n h) - u (C 0 Fin.elim0))) 0 := by
    filter_upwards [hpos] with ε hε
    simp only [add_zero, zero_mul, sub_zero, sub_self, mul_zero]
    rw [← hEU ε]
    refine hopt _ ?_ (hSU ε) (hSV ε) (by rw [hDV]; exact hbud)
    intro m g
    by_cases hm0 : m = 0
    · subst hm0
      have hn' : (0 : ℕ) ≠ n := fun e => hn0 e.symm
      obtain rfl : g = Fin.elim0 := Subsingleton.elim _ _
      have hb : histBump 0 (Fin.elim0 : Fin 0 → S) 0 Fin.elim0 = 1 := by
        rw [histBump_self]; simp
      simp only [perturbPlan, histBump_ne h _ hn', hb]
      linarith [hε.1]
    · by_cases hmn : m = n
      · subst hmn
        simp only [perturbPlan, histBump_self, histBump_ne _ _ hm0]
        by_cases hg : g = h
        · subst hg; simp only [↓reduceIte]; linarith [hε.2]
        · simp only [hg, ↓reduceIte]; linarith [hC m g]
      · simp only [perturbPlan, histBump_ne _ _ hmn, histBump_ne _ _ hm0]
        linarith [hC m g]
  have hda : HasDerivAt (fun ε => β ^ n * (tr.histProb h * (u (C n h + ε) - u (C n h))))
      (β ^ n * (tr.histProb h * (du (C n h) * 1))) 0 := by
    have h1 : HasDerivAt (fun ε : ℝ => C n h + ε) 1 0 :=
      HasDerivAt.const_add (C n h) (hasDerivAt_id (0 : ℝ))
    have h2 := HasDerivAt.comp_of_eq 0 (hu _ (hC n h)) h1 (by simp)
    exact HasDerivAt.const_mul (β ^ n)
      (HasDerivAt.const_mul (tr.histProb h) (HasDerivAt.sub_const (u (C n h)) h2))
  have hdb : HasDerivAt (fun ε => u (C 0 Fin.elim0 - ε * P n h) - u (C 0 Fin.elim0))
      (du (C 0 Fin.elim0) * (-P n h)) 0 := by
    have h1 : HasDerivAt (fun ε : ℝ => C 0 Fin.elim0 - ε * P n h) (-P n h) 0 := by
      simpa using HasDerivAt.const_sub (C 0 Fin.elim0)
        (HasDerivAt.mul_const (hasDerivAt_id (0 : ℝ)) (P n h))
    exact HasDerivAt.sub_const _ (HasDerivAt.comp_of_eq 0 (hu _ (hC 0 Fin.elim0)) h1 (by simp))
  have hd := HasDerivAt.add (HasDerivAt.add (hasDerivAt_const (0 : ℝ) (expectedUtility tr β u C))
    hda) hdb
  have h0 := hmax.hasDerivAt_eq_zero hd
  linarith

/-! ### Appendix 5C.3: the CRRA equilibrium of the infinite economy -/

/-- World output `Y^W(h_t) = Σ_n Y^n(h_t)`, summed over countries (O&R Appendix 5C.3, p. 342). -/
noncomputable def worldOutput {ι : Type} [Fintype ι] (Y : ι → (n : ℕ) → (Fin n → S) → ℝ) :
    (n : ℕ) → (Fin n → S) → ℝ :=
  fun n h => ∑ i, Y i n h

/-- CRRA equilibrium prices in date-1 output, O&R Appendix 5C.3, p. 342 (left as an exercise
there): `R_{1,t} p(h_t|h_1) = β^{t−1} π(h_t|h_1) Y^W(h_t)^{−ρ}/(Y^W_1)^{−ρ}`. -/
noncomputable def crraDatePrice (tr : Tree S) (β ρ : ℝ) (Yw : (n : ℕ) → (Fin n → S) → ℝ) :
    (n : ℕ) → (Fin n → S) → ℝ :=
  fun n h => β ^ n * tr.histProb h * Yw n h ^ (-ρ) / Yw 0 Fin.elim0 ^ (-ρ)

/-- Date-1 output is the numeraire at the CRRA prices, `P(h_1) = 1` (O&R Appendix 5C.3). -/
theorem crraDatePrice_zero (tr : Tree S) (β ρ : ℝ) (Yw : (n : ℕ) → (Fin n → S) → ℝ)
    (hY : 0 < Yw 0 Fin.elim0) : crraDatePrice tr β ρ Yw 0 Fin.elim0 = 1 := by
  have := (Real.rpow_pos_of_pos hY (-ρ)).ne'
  simp [crraDatePrice, tr.histProb_zero, this]

/-- The CRRA date-1 prices factor as `R_{1,t} p(h_t|h_1)` with the book's long-term interest
factor `R_{1,t}` (`crraR`) and history prices `p(h_t|h_1)` (`crraPrice`), O&R Appendix 5C.3,
p. 342. -/
theorem crraDatePrice_eq (tr : Tree S) (β ρ : ℝ) (Yw : (n : ℕ) → (Fin n → S) → ℝ)
    (hY : ∀ n h, 0 < Yw n h) (n : ℕ) (h : Fin n → S) :
    crraDatePrice tr β ρ Yw n h
      = crraR tr β ρ (Yw 0 Fin.elim0) n (Yw n) * crraPrice tr ρ n (Yw n) h := by
  have hD := (crraMass_pos tr ρ n (hY n)).ne'
  simp only [crraDatePrice, crraR, crraPrice]
  field_simp

/-- The long-term interest factor in closed form, O&R Appendix 5C.3, p. 342: the date-1 price of
a sure unit on date `t` at the CRRA prices is
`R_{1,t} = β^{t−1} Σ_{h_t} π(h_t|h_1) Y^W(h_t)^{−ρ}/(Y^W_1)^{−ρ}`. -/
theorem crraDatePrice_sum (tr : Tree S) (β ρ : ℝ) (Yw : (n : ℕ) → (Fin n → S) → ℝ) (n : ℕ) :
    ∑ h, crraDatePrice tr β ρ Yw n h = crraR tr β ρ (Yw 0 Fin.elim0) n (Yw n) := by
  simp only [crraDatePrice, crraR, crraMass, Finset.mul_sum, Finset.sum_div]
  exact Finset.sum_congr rfl fun h _ => by ring

/-- The first-order conditions (84) at the CRRA prices, over all dates, O&R Appendix 5C.3,
p. 342: the constant-share plan `C = μY^W` satisfies
`P(h_t) (μY^W_1)^{−ρ} = π(h_t|h_1) β^{t−1} (μY^W(h_t))^{−ρ}` for every `μ > 0`. -/
theorem crra_foc_infinite (tr : Tree S) (β ρ : ℝ) {Yw : (n : ℕ) → (Fin n → S) → ℝ}
    (hY : ∀ n h, 0 < Yw n h) {μ : ℝ} (hμ : 0 < μ) (n : ℕ) (h : Fin n → S) :
    crraDatePrice tr β ρ Yw n h * (μ * Yw 0 Fin.elim0) ^ (-ρ)
      = tr.histProb h * β ^ n * (μ * Yw n h) ^ (-ρ) := by
  have h1 := (Real.rpow_pos_of_pos (hY 0 Fin.elim0) (-ρ)).ne'
  rw [Real.mul_rpow hμ.le (hY 0 Fin.elim0).le, Real.mul_rpow hμ.le (hY n h).le]
  simp only [crraDatePrice]
  field_simp

/-- The date-`t` term of the date-1 value of a stream at the CRRA prices, O&R (83) with
Appendix 5C.3: `β^{t−1} E₁[Y^W(h_t)^{−ρ} x(h_t)]/(Y^W_1)^{−ρ}`. -/
theorem crra_valueSeries (tr : Tree S) (β ρ : ℝ) (Yw x : (n : ℕ) → (Fin n → S) → ℝ) (n : ℕ) :
    valueSeries (crraDatePrice tr β ρ Yw) x n
      = β ^ n * (∑ h, tr.histProb h * (Yw n h ^ (-ρ) * x n h)) / Yw 0 Fin.elim0 ^ (-ρ) := by
  simp only [valueSeries, crraDatePrice, Finset.mul_sum, Finset.sum_div]
  exact Finset.sum_congr rfl fun h _ => by ring

/-- The CRRA equilibrium of the infinite economy, O&R Appendix 5C.3, p. 342. Countries `j`
have positive endowments `Y^j(h_t)`, common CRRA utility (`ρ > 0`, `ρ ≠ 1`) and discount factor
`β > 0`. Primitive condition: for each country the series
`Σ_t β^{t−1} E₁[Y^W(h_t)^{−ρ} Y^j(h_t)]` converges. Then at the prices `crraDatePrice`, with
`μ^j` country `j`'s share of the date-1 present value of world output and `C^j = μ^j Y^W`:
the shares are positive and sum to one; each plan satisfies the first-order conditions (84) at
every history, the infinite budget constraint (83) with equality (the value series converges),
and is admissible (its utility series converges); markets clear at every history; and each
plan is optimal: no positive admissible plan satisfying (83) gives more expected utility. -/
theorem crra_equilibrium_infinite {ι : Type} [Fintype ι] (tr : Tree S) {β ρ : ℝ} (hβ : 0 < β)
    (hρ : 0 < ρ) (hρ1 : ρ ≠ 1) (Y : ι → (n : ℕ) → (Fin n → S) → ℝ)
    (hY : ∀ j n h, 0 < Y j n h)
    (hsum : ∀ j, Summable fun n =>
      β ^ n * ∑ h, tr.histProb h * (worldOutput Y n h ^ (-ρ) * Y j n h))
    (i : ι) :
    let P := crraDatePrice tr β ρ (worldOutput Y)
    let μ := fun j => dateOneValue P (Y j) / dateOneValue P (worldOutput Y)
    let C := fun j (n : ℕ) (h : Fin n → S) => μ j * worldOutput Y n h
    (0 < μ i ∧ ∑ j, μ j = 1) ∧
    (∀ n h, P n h * C i 0 Fin.elim0 ^ (-ρ) = tr.histProb h * β ^ n * C i n h ^ (-ρ)) ∧
    (Summable (valueSeries P (C i)) ∧ dateOneValue P (C i) = dateOneValue P (Y i)) ∧
    (∀ n h, ∑ j, C j n h = worldOutput Y n h) ∧
    Summable (utilSeries tr β (crraUtil ρ) (C i)) ∧
    (∀ C' : (n : ℕ) → (Fin n → S) → ℝ, (∀ n h, 0 < C' n h) →
      Summable (utilSeries tr β (crraUtil ρ) C') → Summable (valueSeries P C') →
      dateOneValue P C' ≤ dateOneValue P (Y i) →
      expectedUtility tr β (crraUtil ρ) C' ≤ expectedUtility tr β (crraUtil ρ) (C i)) := by
  intro P μ C
  set Yw := worldOutput Y with hYw_def
  have hYw : ∀ n h, 0 < Yw n h := fun n h =>
    Finset.sum_pos (fun j _ => hY j n h) ⟨i, Finset.mem_univ i⟩
  have hVs : ∀ j, Summable (valueSeries P (Y j)) := by
    intro j
    have e : valueSeries P (Y j) = fun n =>
        β ^ n * (∑ h, tr.histProb h * (Yw n h ^ (-ρ) * Y j n h)) / Yw 0 Fin.elim0 ^ (-ρ) :=
      funext (crra_valueSeries tr β ρ Yw (Y j))
    rw [e]; exact (hsum j).div_const _
  have hVwe : valueSeries P Yw = fun n => ∑ j, valueSeries P (Y j) n := by
    funext n
    simp only [valueSeries, hYw_def, worldOutput, Finset.mul_sum]
    exact Finset.sum_comm
  have hVw : Summable (valueSeries P Yw) := by
    rw [hVwe]; exact summable_sum fun j _ => hVs j
  have hDw : dateOneValue P Yw = ∑ j, dateOneValue P (Y j) := by
    unfold dateOneValue; rw [hVwe, Summable.tsum_finsetSum fun j _ => hVs j]
  have hP0 : P 0 Fin.elim0 = 1 := crraDatePrice_zero tr β ρ Yw (hYw 0 Fin.elim0)
  have hPnn : ∀ n h, 0 ≤ P n h := fun n h =>
    div_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hβ.le n) (tr.histProb_nonneg h))
      (Real.rpow_nonneg (hYw n h).le _)) (Real.rpow_nonneg (hYw 0 Fin.elim0).le _)
  have hDpos : ∀ x : (n : ℕ) → (Fin n → S) → ℝ, (∀ n h, 0 < x n h) →
      Summable (valueSeries P x) → 0 < dateOneValue P x := by
    intro x hx hs
    refine hs.tsum_pos (fun n => Finset.sum_nonneg fun h _ =>
      mul_nonneg (hPnn n h) (hx n h).le) 0 ?_
    rw [valueSeries, Fintype.sum_unique, Subsingleton.elim default Fin.elim0, hP0, one_mul]
    exact hx 0 Fin.elim0
  have hVwpos : 0 < dateOneValue P Yw := hDpos Yw hYw hVw
  have hμ : ∀ j, 0 < μ j := fun j => div_pos (hDpos (Y j) (hY j) (hVs j)) hVwpos
  have hμsum : ∑ j, μ j = 1 := by
    simp only [μ]
    rw [← Finset.sum_div, ← hDw, div_self hVwpos.ne']
  have hCe : valueSeries P (C i) = fun n => μ i * valueSeries P Yw n := by
    funext n
    simp only [valueSeries, C, Finset.mul_sum]
    exact Finset.sum_congr rfl fun h _ => by ring
  have hVC : Summable (valueSeries P (C i)) := by rw [hCe]; exact hVw.mul_left _
  have hbud : dateOneValue P (C i) = dateOneValue P (Y i) := by
    unfold dateOneValue
    rw [hCe, tsum_mul_left]
    exact div_mul_cancel₀ _ hVwpos.ne'
  have hfoc : ∀ n h, P n h * C i 0 Fin.elim0 ^ (-ρ) = tr.histProb h * β ^ n * C i n h ^ (-ρ) :=
    crra_foc_infinite tr β ρ hYw (hμ i)
  have hUe : utilSeries tr β (crraUtil ρ) (C i) = fun n => μ i ^ (1 - ρ) / (1 - ρ)
      * ∑ j, β ^ n * ∑ h, tr.histProb h * (Yw n h ^ (-ρ) * Y j n h) := by
    funext n
    have e1 : ∑ j, β ^ n * ∑ h, tr.histProb h * (Yw n h ^ (-ρ) * Y j n h)
        = β ^ n * ∑ h, tr.histProb h * Yw n h ^ (1 - ρ) := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      congr 1
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [← Finset.mul_sum, ← Finset.mul_sum, show (1 : ℝ) - ρ = -ρ + 1 by ring,
        Real.rpow_add (hYw n h), Real.rpow_one]
      rfl
    rw [e1]
    simp only [utilSeries, crraUtil, C, Finset.mul_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [Real.mul_rpow (hμ i).le (hYw n h).le]
    ring
  have hU : Summable (utilSeries tr β (crraUtil ρ) (C i)) := by
    rw [hUe]; exact (summable_sum fun j _ => hsum j).mul_left _
  have hC : ∀ n h, 0 < C i n h := fun n h => mul_pos (hμ i) (hYw n h)
  refine ⟨⟨hμ i, hμsum⟩, hfoc, ⟨hVC, hbud⟩, ?_, hU, ?_⟩
  · intro n h
    simp only [C]
    rw [← Finset.sum_mul, hμsum, one_mul]
  · intro C' hC' hU' hV' hbud'
    exact arrowDebreu_optimal_infinite tr (crraUtil ρ) (fun x => x ^ (-ρ))
      (fun x y hx hy => crra_tangent hρ hρ1 hx hy) hβ.le P (Y i) hC hC'
      (Real.rpow_nonneg (hC 0 Fin.elim0).le _) hfoc hU hU' hVC hV' hbud hbud'

/-- Constant consumption shares in the infinite economy, O&R Appendix 5C.3, p. 342: if every
country's plan satisfies the first-order conditions (84) with CRRA marginal utility `C^{−ρ}`
(`ρ ≠ 0`) at common date-1 prices at every history, and world markets clear at every history,
then `C^j(h_t) = μ^j Y^W(h_t)` with the date-1 share `μ^j = C^j_1/Y^W_1`, at every history with
`π(h_t|h_1) > 0` (and `β > 0`). -/
theorem crra_constant_share_infinite {ι : Type} [Fintype ι] (tr : Tree S) {β ρ : ℝ}
    (hβ : 0 < β) (hρ : ρ ≠ 0) (P Yw : (n : ℕ) → (Fin n → S) → ℝ)
    (C : ι → (n : ℕ) → (Fin n → S) → ℝ) (hC : ∀ j n h, 0 < C j n h)
    (hfoc : ∀ j n h, P n h * C j 0 Fin.elim0 ^ (-ρ) = tr.histProb h * β ^ n * C j n h ^ (-ρ))
    (hclear : ∀ n h, ∑ j, C j n h = Yw n h) (i : ι) (n : ℕ) (h : Fin n → S)
    (hπ : 0 < tr.histProb h) :
    C i n h = C i 0 Fin.elim0 / Yw 0 Fin.elim0 * Yw n h := by
  have hk : 0 < tr.histProb h * β ^ n := mul_pos hπ (pow_pos hβ n)
  have ratio : ∀ j, (C j n h / C j 0 Fin.elim0) ^ (-ρ) = P n h / (tr.histProb h * β ^ n) := by
    intro j
    have h0 := hC j 0 Fin.elim0
    rw [Real.div_rpow (hC j n h).le h0.le, eq_div_iff hk.ne',
      div_mul_eq_mul_div, div_eq_iff (Real.rpow_pos_of_pos h0 _).ne']
    linarith [hfoc j n h]
  have hg : ∀ j, C j n h / C j 0 Fin.elim0 = C i n h / C i 0 Fin.elim0 := fun j =>
    (Real.rpow_left_inj (div_pos (hC j n h) (hC j 0 _)).le (div_pos (hC i n h) (hC i 0 _)).le
      (neg_ne_zero.mpr hρ)).mp ((ratio j).trans (ratio i).symm)
  have hY0 : 0 < Yw 0 Fin.elim0 := by
    rw [← hclear]; exact Finset.sum_pos (fun j _ => hC j 0 _) ⟨i, Finset.mem_univ i⟩
  have hYn : Yw n h = C i n h / C i 0 Fin.elim0 * Yw 0 Fin.elim0 := by
    rw [← hclear, ← hclear, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hg j, div_mul_cancel₀ _ (hC j 0 _).ne']
  have := (hC i 0 Fin.elim0).ne'
  rw [hYn]
  field_simp

/-- The share is pinned down by the infinite budget constraint, O&R Appendix 5C.3, p. 342: if the
plan `C = μY^W` exhausts the date-1 value of the endowment `Y` (83), then `μ` is the country's
share of the date-1 present value of world output, `μ = PV(Y)/PV(Y^W)` (given `PV(Y^W) ≠ 0`). -/
theorem crra_share_of_budget (P Y Yw : (n : ℕ) → (Fin n → S) → ℝ) {μ : ℝ}
    (hW : dateOneValue P Yw ≠ 0)
    (hbud : dateOneValue P (fun n h => μ * Yw n h) = dateOneValue P Y) :
    μ = dateOneValue P Y / dateOneValue P Yw := by
  have e : dateOneValue P (fun n h => μ * Yw n h) = μ * dateOneValue P Yw := by
    unfold dateOneValue valueSeries
    rw [← tsum_mul_left]
    refine tsum_congr fun n => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun h _ => by ring
  rw [eq_div_iff hW, ← hbud, e, mul_comm]

/-- The log-utility (`ρ = 1`) equilibrium of the infinite economy, O&R Appendix 5C.3, p. 342
(the limit `ρ → 1` of CRRA utility). Countries `j` have positive endowments and common log
utility with discount factor `0 < β < 1`. The prices are `crraDatePrice` at `ρ = 1`,
`P(h_t) = β^{t−1} π(h_t|h_1) Y^W_1/Y^W(h_t)`. The budget series of every endowment converges
automatically (`Y^j/Y^W ≤ 1` and `β < 1`); the one extra primitive condition, needed exactly for
the equilibrium utility series `Σ β^{t−1}E₁ log(μ^j Y^W)` to converge, is that
`Σ_t β^{t−1} E₁ log Y^W(h_t)` converges. Then, with `μ^j` the present-value share and
`C^j = μ^j Y^W`: the shares are positive and sum to one; each plan satisfies the log first-order
conditions (84) `P(h_t)/C^j_1 = π(h_t|h_1) β^{t−1}/C^j(h_t)`, the infinite budget (83) with
equality, market clearing, admissibility, and optimality against every positive admissible plan
satisfying (83). -/
theorem log_equilibrium_infinite {ι : Type} [Fintype ι] (tr : Tree S) {β : ℝ} (hβ : 0 < β)
    (hβ1 : β < 1) (Y : ι → (n : ℕ) → (Fin n → S) → ℝ) (hY : ∀ j n h, 0 < Y j n h)
    (hlog : Summable fun n => β ^ n * ∑ h, tr.histProb h * Real.log (worldOutput Y n h))
    (i : ι) :
    let P := crraDatePrice tr β 1 (worldOutput Y)
    let μ := fun j => dateOneValue P (Y j) / dateOneValue P (worldOutput Y)
    let C := fun j (n : ℕ) (h : Fin n → S) => μ j * worldOutput Y n h
    (0 < μ i ∧ ∑ j, μ j = 1) ∧
    (∀ n h, P n h * (C i 0 Fin.elim0)⁻¹ = tr.histProb h * β ^ n * (C i n h)⁻¹) ∧
    (Summable (valueSeries P (C i)) ∧ dateOneValue P (C i) = dateOneValue P (Y i)) ∧
    (∀ n h, ∑ j, C j n h = worldOutput Y n h) ∧
    Summable (utilSeries tr β Real.log (C i)) ∧
    (∀ C' : (n : ℕ) → (Fin n → S) → ℝ, (∀ n h, 0 < C' n h) →
      Summable (utilSeries tr β Real.log C') → Summable (valueSeries P C') →
      dateOneValue P C' ≤ dateOneValue P (Y i) →
      expectedUtility tr β Real.log C' ≤ expectedUtility tr β Real.log (C i)) := by
  intro P μ C
  set Yw := worldOutput Y with hYw_def
  have hYw : ∀ n h, 0 < Yw n h := fun n h =>
    Finset.sum_pos (fun j _ => hY j n h) ⟨i, Finset.mem_univ i⟩
  have hP0 : P 0 Fin.elim0 = 1 := crraDatePrice_zero tr β 1 Yw (hYw 0 Fin.elim0)
  have hPnn : ∀ n h, 0 ≤ P n h := fun n h =>
    div_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hβ.le n) (tr.histProb_nonneg h))
      (Real.rpow_nonneg (hYw n h).le _)) (Real.rpow_nonneg (hYw 0 Fin.elim0).le _)
  have hY1 : 0 < Yw 0 Fin.elim0 ^ (-(1 : ℝ)) := Real.rpow_pos_of_pos (hYw 0 Fin.elim0) _
  have hVs : ∀ j, Summable (valueSeries P (Y j)) := by
    intro j
    refine Summable.of_nonneg_of_le (fun n => Finset.sum_nonneg fun h _ =>
      mul_nonneg (hPnn n h) (hY j n h).le) (fun n => ?_)
      ((summable_geometric_of_lt_one hβ.le hβ1).div_const (Yw 0 Fin.elim0 ^ (-(1 : ℝ))))
    rw [crra_valueSeries]
    refine div_le_div_of_nonneg_right ?_ hY1.le
    refine mul_le_of_le_one_right (pow_nonneg hβ.le n) ?_
    calc ∑ h, tr.histProb h * (Yw n h ^ (-(1 : ℝ)) * Y j n h) ≤ ∑ h, tr.histProb h * 1 :=
          Finset.sum_le_sum fun h _ => mul_le_mul_of_nonneg_left (by
            rw [Real.rpow_neg_one, inv_mul_le_one₀ (hYw n h)]
            exact Finset.single_le_sum (f := fun j => Y j n h) (fun j _ => (hY j n h).le)
              (Finset.mem_univ j)) (tr.histProb_nonneg h)
      _ = 1 := by simp [tr.histProb_sum_eq_one]
  have hVwe : valueSeries P Yw = fun n => ∑ j, valueSeries P (Y j) n := by
    funext n
    simp only [valueSeries, hYw_def, worldOutput, Finset.mul_sum]
    exact Finset.sum_comm
  have hVw : Summable (valueSeries P Yw) := by
    rw [hVwe]; exact summable_sum fun j _ => hVs j
  have hDw : dateOneValue P Yw = ∑ j, dateOneValue P (Y j) := by
    unfold dateOneValue; rw [hVwe, Summable.tsum_finsetSum fun j _ => hVs j]
  have hDpos : ∀ x : (n : ℕ) → (Fin n → S) → ℝ, (∀ n h, 0 < x n h) →
      Summable (valueSeries P x) → 0 < dateOneValue P x := by
    intro x hx hs
    refine hs.tsum_pos (fun n => Finset.sum_nonneg fun h _ =>
      mul_nonneg (hPnn n h) (hx n h).le) 0 ?_
    rw [valueSeries, Fintype.sum_unique, Subsingleton.elim default Fin.elim0, hP0, one_mul]
    exact hx 0 Fin.elim0
  have hVwpos : 0 < dateOneValue P Yw := hDpos Yw hYw hVw
  have hμ : ∀ j, 0 < μ j := fun j => div_pos (hDpos (Y j) (hY j) (hVs j)) hVwpos
  have hμsum : ∑ j, μ j = 1 := by
    simp only [μ]
    rw [← Finset.sum_div, ← hDw, div_self hVwpos.ne']
  have hCe : valueSeries P (C i) = fun n => μ i * valueSeries P Yw n := by
    funext n
    simp only [valueSeries, C, Finset.mul_sum]
    exact Finset.sum_congr rfl fun h _ => by ring
  have hVC : Summable (valueSeries P (C i)) := by rw [hCe]; exact hVw.mul_left _
  have hbud : dateOneValue P (C i) = dateOneValue P (Y i) := by
    unfold dateOneValue
    rw [hCe, tsum_mul_left]
    exact div_mul_cancel₀ _ hVwpos.ne'
  have hfoc : ∀ n h, P n h * (C i 0 Fin.elim0)⁻¹ = tr.histProb h * β ^ n * (C i n h)⁻¹ := by
    intro n h
    have := crra_foc_infinite tr β 1 hYw (hμ i) n h
    simp only [Real.rpow_neg_one] at this
    exact this
  have hUe : utilSeries tr β Real.log (C i) = fun n => Real.log (μ i) * β ^ n
      + β ^ n * ∑ h, tr.histProb h * Real.log (Yw n h) := by
    funext n
    have e : ∀ h, Real.log (μ i * worldOutput Y n h) = Real.log (μ i) + Real.log (Yw n h) :=
      fun h => Real.log_mul (hμ i).ne' (hYw n h).ne'
    simp only [utilSeries, C, e, mul_add,
      Finset.sum_add_distrib, ← Finset.sum_mul, tr.histProb_sum_eq_one, one_mul]
    ring
  have hU : Summable (utilSeries tr β Real.log (C i)) := by
    rw [hUe]; exact ((summable_geometric_of_lt_one hβ.le hβ1).mul_left _).add hlog
  have hC : ∀ n h, 0 < C i n h := fun n h => mul_pos (hμ i) (hYw n h)
  refine ⟨⟨hμ i, hμsum⟩, hfoc, ⟨hVC, hbud⟩, ?_, hU, ?_⟩
  · intro n h
    simp only [C]
    rw [← Finset.sum_mul, hμsum, one_mul]
  · intro C' hC' hU' hV' hbud'
    exact arrowDebreu_optimal_infinite tr Real.log (fun x => x⁻¹)
      (fun x y hx hy => by simpa [one_div] using log_tangent hx hy) hβ.le P (Y i) hC hC'
      (inv_nonneg.mpr (hC 0 Fin.elim0).le) hfoc hU hU' hVC hV' hbud hbud'

/-! ### Appendix 5D: dynamic consistency in the infinite economy -/

/-- The date-`(m+2)` term of date-2 expected utility after the date-2 event `s₂`, O&R Appendix
5D, p. 344: `β^{t−2} Σ_{h_t ∈ H_t(h_2)} π(h_t|h_2) u(c(h_t))`, `t = m + 2`, for a plan `c` on
the histories continuing `h_2 = {s₂} ∪ h_1` (date 2 itself is `m = 0`). -/
noncomputable def dateTwoUtilSeries [DecidableEq S] (tr : Tree S) (β : ℝ) (u : ℝ → ℝ) (s₂ : S)
    (c : (m : ℕ) → (Fin (m + 1) → S) → ℝ) (m : ℕ) : ℝ :=
  ∑ h ∈ univ.filter (fun h : Fin (m + 1) → S => h 0 = s₂), β ^ m * tr.condProb h 1 * u (c m h)

/-- The date-`(m+2)` term `Σ_{h_t ∈ H_t(h_2)} p̃(h_t|h_2) c(h_t)` of the date-2 budget
constraint, O&R Appendix 5D, p. 344, with date-2 prices `P₂ = p̃(·|h_2)` in date-2 output. -/
noncomputable def dateTwoValueSeries [DecidableEq S] (s₂ : S)
    (P₂ c : (m : ℕ) → (Fin (m + 1) → S) → ℝ) (m : ℕ) : ℝ :=
  ∑ h ∈ univ.filter (fun h : Fin (m + 1) → S => h 0 = s₂), P₂ m h * c m h

/-- The date-1 plan, continued after the date-2 event `s₂`, is admissible for the date-2
problem (O&R Appendix 5D, p. 344): if it satisfies (84) with `u′ > 0` at date-1 prices, its
budget series converges and its utility series converges absolutely (expected discounted utility
integrable over the event tree), and `π(h_2|h_1) > 0`, then with the no-arbitrage date-2 prices
`p̃(h_t|h_2) = p̃(h_t|h_1)/p̃(h_2|h_1)` its date-2 utility and budget series converge. -/
theorem dateTwo_restriction_admissible [DecidableEq S] (tr : Tree S) (u du : ℝ → ℝ)
    (hdu : ∀ x, 0 < x → 0 < du x) {β : ℝ} (hβ : 0 < β)
    (P : (n : ℕ) → (Fin n → S) → ℝ) (P₂ : (m : ℕ) → (Fin (m + 1) → S) → ℝ)
    {C : (n : ℕ) → (Fin n → S) → ℝ} (hC : ∀ n h, 0 < C n h)
    (hfoc : ∀ n h, P n h * du (C 0 Fin.elim0) = tr.histProb h * β ^ n * du (C n h))
    (hUabs : Summable fun n => β ^ n * ∑ h, tr.histProb h * |u (C n h)|)
    (hV : Summable (valueSeries P C)) (s₂ : S) (hπ₂ : 0 < tr.q 0 Fin.elim0 s₂)
    (harb : ∀ m (h : Fin (m + 1) → S), h 0 = s₂ → P (m + 1) h / P 1 (fun _ => s₂) = P₂ m h) :
    Summable (dateTwoUtilSeries tr β u s₂ fun m h => C (m + 1) h) ∧
      Summable (dateTwoValueSeries s₂ P₂ fun m h => C (m + 1) h) := by
  have hdu1 := hdu _ (hC 0 Fin.elim0)
  have hPnn : ∀ n h, 0 ≤ P n h := by
    intro n h
    have e : P n h = tr.histProb h * β ^ n * du (C n h) / du (C 0 Fin.elim0) := by
      rw [eq_div_iff hdu1.ne']; exact hfoc n h
    rw [e]
    exact div_nonneg (mul_nonneg (mul_nonneg (tr.histProb_nonneg h) (pow_nonneg hβ.le n))
      (hdu _ (hC n h)).le) hdu1.le
  have hP1 : 0 < P 1 (fun _ => s₂) := by
    have e : P 1 (fun _ => s₂)
        = tr.histProb (fun _ : Fin 1 => s₂) * β ^ 1 * du (C 1 fun _ => s₂) / du (C 0 Fin.elim0) :=
      by rw [eq_div_iff hdu1.ne']; exact hfoc 1 _
    rw [e, tr.histProb_one]
    exact div_pos (mul_pos (mul_pos hπ₂ (pow_pos hβ 1)) (hdu _ (hC 1 _))) hdu1
  constructor
  · refine Summable.of_norm_bounded (((summable_nat_add_iff 1).mpr hUabs).div_const
      (β * tr.q 0 Fin.elim0 s₂)) fun m => ?_
    have hk : 0 < β * tr.q 0 Fin.elim0 s₂ := mul_pos hβ hπ₂
    rw [Real.norm_eq_abs, le_div_iff₀ hk]
    refine le_trans (mul_le_mul_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) hk.le) ?_
    rw [Finset.sum_mul, Finset.mul_sum]
    refine le_trans ?_ (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset (fun h : Fin (m + 1) → S => h 0 = s₂) univ)
      fun h _ _ => mul_nonneg (pow_nonneg hβ.le _)
        (mul_nonneg (tr.histProb_nonneg h) (abs_nonneg _)))
    refine le_of_eq (Finset.sum_congr rfl fun h hh => ?_)
    have hh0 : h 0 = s₂ := (Finset.mem_filter.mp hh).2
    rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hβ.le m),
      abs_of_nonneg (tr.condProb_nonneg h 1), tr.histProb_eq_first_mul_condProb, hh0]
    ring
  · refine Summable.of_nonneg_of_le (fun m => Finset.sum_nonneg fun h hh => ?_) (fun m => ?_)
      (((summable_nat_add_iff 1).mpr hV).div_const (P 1 fun _ => s₂))
    · rw [← harb m h (Finset.mem_filter.mp hh).2]
      exact mul_nonneg (div_nonneg (hPnn _ h) hP1.le) (hC _ h).le
    · simp only [dateTwoValueSeries, valueSeries]
      rw [le_div_iff₀ hP1, Finset.sum_mul]
      refine le_trans (le_of_eq (Finset.sum_congr rfl fun h hh => ?_))
        (Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.filter_subset (fun h : Fin (m + 1) → S => h 0 = s₂) univ)
      fun h _ _ => mul_nonneg (hPnn _ h) (hC _ h).le)
      rw [← harb m h (Finset.mem_filter.mp hh).2]
      field_simp

/-- Dynamic consistency over the infinite horizon, O&R Appendix 5D, pp. 343–344. Suppose the
date-1 plan `C` satisfies the first-order conditions (84)/(86) at date-1 prices
`p̃(h_t|h_1) = R_{1,t} p(h_t|h_1)` at every history, `u` is concave with `u′ > 0`, the plan's
budget series converges and its utility series converges absolutely. Markets reopen on date 2
after the event `s₂` (with `π(h_2|h_1) > 0`) at date-2 prices obeying the book's no-arbitrage
identity `p̃(h_t|h_1)/p̃(h_2|h_1) = p̃(h_t|h_2)` (a hypothesis: O&R justify it by an arbitrage
argument, buying a date-`t` claim directly or via a date-2 claim, not by the model's
primitives). Then every positive plan `c′` on the date-2 subtree whose utility and budget
series converge and which satisfies the date-2 budget constraint (p. 344) gives no more date-2
expected utility than the continuation of the date-1 plan: the date-1 plan remains optimal. -/
theorem dynamic_consistency_infinite [DecidableEq S] (tr : Tree S) (u du : ℝ → ℝ)
    (htan : ∀ x y, 0 < x → 0 < y → u y ≤ u x + du x * (y - x))
    (hdu : ∀ x, 0 < x → 0 < du x) {β : ℝ} (hβ : 0 < β)
    (P : (n : ℕ) → (Fin n → S) → ℝ) (P₂ : (m : ℕ) → (Fin (m + 1) → S) → ℝ)
    {C : (n : ℕ) → (Fin n → S) → ℝ} (hC : ∀ n h, 0 < C n h)
    (hfoc : ∀ n h, P n h * du (C 0 Fin.elim0) = tr.histProb h * β ^ n * du (C n h))
    (hUabs : Summable fun n => β ^ n * ∑ h, tr.histProb h * |u (C n h)|)
    (hV : Summable (valueSeries P C)) (s₂ : S) (hπ₂ : 0 < tr.q 0 Fin.elim0 s₂)
    (harb : ∀ m (h : Fin (m + 1) → S), h 0 = s₂ → P (m + 1) h / P 1 (fun _ => s₂) = P₂ m h)
    {c' : (m : ℕ) → (Fin (m + 1) → S) → ℝ}
    (hc' : ∀ m (h : Fin (m + 1) → S), h 0 = s₂ → 0 < c' m h)
    (hU' : Summable (dateTwoUtilSeries tr β u s₂ c'))
    (hV' : Summable (dateTwoValueSeries s₂ P₂ c'))
    (hbud : ∑' m, dateTwoValueSeries s₂ P₂ c' m
      ≤ ∑' m, dateTwoValueSeries s₂ P₂ (fun m h => C (m + 1) h) m) :
    ∑' m, dateTwoUtilSeries tr β u s₂ c' m
      ≤ ∑' m, dateTwoUtilSeries tr β u s₂ (fun m h => C (m + 1) h) m := by
  obtain ⟨hU, hVr⟩ := dateTwo_restriction_admissible tr u du hdu hβ P P₂ hC hfoc hUabs hV s₂
    hπ₂ harb
  have hπ₂' : 0 < tr.histProb (fun _ : Fin 1 => s₂) := by rw [tr.histProb_one]; exact hπ₂
  refine foc_plan_optimal_tsum (fun m => univ.filter (fun h : Fin (m + 1) → S => h 0 = s₂))
    u du htan (fun m h => β ^ m * tr.condProb h 1) P₂
    (fun m h _ => mul_nonneg (pow_nonneg hβ.le m) (tr.condProb_nonneg h 1))
    (hdu _ (hC 1 fun _ => s₂)).le (fun m h _ => hC (m + 1) h)
    (fun m h hh => hc' m h (Finset.mem_filter.mp hh).2) ?_ hU hU' hVr hV' hbud
  intro m h hh
  have hh0 : h 0 = s₂ := (Finset.mem_filter.mp hh).2
  have hg : restr h 1 (by omega) = fun _ : Fin 1 => s₂ := by
    funext j
    rw [Fin.fin_one_eq_zero j, ← hh0]
    rfl
  have hπ : 0 < tr.histProb (restr h 1 (by omega)) := by rw [hg]; exact hπ₂'
  have hf₂ : P 1 (fun _ => s₂) * du (C 0 Fin.elim0)
      = tr.histProb (restr h 1 (by omega)) * β ^ 1 * du (C 1 (fun _ => s₂)) := by
    rw [hg]; exact hfoc 1 _
  have key := foc_date2 tr du hβ h hπ (hdu _ (hC 0 _)) (hdu _ (hC 1 _)) hf₂
    (hfoc (m + 1) h) (harb m h hh0)
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
# Infinite-horizon consumption and portfolio choice

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, Supplement A to
Chapter 5, "Multiperiod Portfolio Selection", pp. 742–744.

An investor with financial wealth `W` and no other income chooses consumption `C` and shares
`x_n` (`Σ_n x_n = 1`) of `N` assets with net returns `r^n`. Uncertainty is an i.i.d. event tree
(`iidTree`, one-step probabilities `q k g s = π(s)` in `EventTree.Tree`): wealth evolves as
`W_{t+1} = (1 + r°(x_t))(W_t − C_t)`, with portfolio return `r° = Σ_n x_n r^n`
(`= r^N + Σ_{n<N} x_n (r^n − r^N)`, the book's form).

* **Portfolio condition (2).** With CRRA utility (`ρ > 0`, `ρ ≠ 1`) and consumption proportional
  to wealth, (2) is `E[(r^n − r^N)(1 + r°)^{−ρ}] = 0`, independent of wealth. It is the
  first-order condition of maximising the portfolio objective `E[(1 + r°)^{1−ρ}]/(1−ρ)`:
  sufficient (concavity) and necessary (at an interior optimum). Log utility likewise with
  `E log(1 + r°)`.
* **Bellman equation.** `V(W) = μ^{−ρ} W^{1−ρ}/(1−ρ)` with `μ = 1 − [βE(1+r°)^{1−ρ}]^{1/ρ}`
  satisfies the Bellman equation exactly, the maximum attained at `C = μW` and the optimal
  portfolio. Conversely a guess `A W^{1−ρ}/(1−ρ)` whose maximum is at `C = μW` forces
  `A = μ^{−ρ}` and the book's `μ`; `μ` is the i.i.d. fixed point of the share recursion
  (`EventTree.crra_iid_share`) and satisfies the Euler equation (1). Log utility gives
  `μ = 1 − β`.
* **Verification.** On the i.i.d. tree, over the infinite horizon, under the parameter
  condition `βE(1+r°)^{1−ρ} < 1` (log: `0 < β < 1`): every admissible plan (consumption and
  portfolio at each history, `0 < C ≤ W`, utility series convergent) satisfies the
  transversality property `β^t E V(W_t) → 0`, which we prove, and achieves at most `V(W₀)`;
  the policy `C = μW` with the optimal portfolio is admissible and attains `V(W₀)`.
* **Existence of the optimal portfolio.** Under positive state probabilities, a no-arbitrage
  (non-redundancy) condition on the return matrix (no `d ≠ 0`, `Σd = 0`, with `Σ d_n r^n ≥ 0` in
  every state) and some feasible portfolio, the closed feasible set is compact and an optimal
  portfolio exists and is interior, so it satisfies (2): for `ρ > 1` and log utility the
  objective tends to `−∞` at the boundary; for `ρ < 1` infinite marginal utility at a zero
  gross return rules the boundary out. The verification theorems are restated with only these
  primitive conditions (and the growth condition at the optimum).
* **Returns varying with the history.** On a general event tree with history-dependent returns
  the book's recursion `μ_t = (1 + [βE_t{(1 + r°_{t+1})^{1−ρ} μ_{t+1}^{−ρ}}]^{1/ρ})^{−1}` has a
  solution, the limit of backward iterations from `μ ≡ 1`, under a uniform growth condition;
  `C = μ_t W` with the date-`t` optimal portfolios attains `V_t(W) = μ_t^{−ρ}W^{1−ρ}/(1−ρ)` and
  no admissible plan does better. With log utility `μ = 1 − β` for any return process, the
  portfolio is chosen myopically to maximise `E_t log(1 + r°)`, and
  `V_t(W) = log W/(1 − β) + K_t` with `K_t` a backward-summed series that converges when the
  optimal `E_t log(1 + r°)` is uniformly bounded.
-/

namespace ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio

open Finset Filter Topology EventTree

variable {S : Type} [Fintype S] {N : ℕ}

/-- The i.i.d. event tree of O&R Supplement A, p. 744: whatever the history, the next event is
`s` with probability `π(s)`. -/
def iidTree (Ω : StateSpace S) : EventTree.Tree S :=
  ⟨fun _ _ s => Ω.prob s, fun _ _ s => Ω.prob_nonneg s, fun _ _ => Ω.prob_sum⟩

/-- The return on a portfolio `x` of the `N` assets in state `s`, `r° = Σ_n x_n r^n`
(O&R Supplement A, p. 743). -/
def portRet (r : Fin N → S → ℝ) (x : Fin N → ℝ) (s : S) : ℝ := ∑ i, x i * r i s

/-- A feasible portfolio (O&R Supplement A, p. 742): shares add up to one, `Σ_n x_n = 1`, and
the gross return `1 + r°` is positive in every state. -/
def PortFeasible (r : Fin N → S → ℝ) (x : Fin N → ℝ) : Prop :=
  ∑ i, x i = 1 ∧ ∀ s, 0 < 1 + portRet r x s

omit [Fintype S] in
/-- The book's form of the portfolio return, O&R Supplement A, p. 743: with `Σ_n x_n = 1` and
reference asset `k` (the book's asset `N`), `r° = r^k + Σ_n x_n (r^n − r^k)` (the `n = k` term
vanishes). -/
theorem portRet_eq_book (r : Fin N → S → ℝ) {x : Fin N → ℝ} (hx : ∑ i, x i = 1) (k : Fin N)
    (s : S) : portRet r x s = r k s + ∑ i, x i * (r i s - r k s) := by
  simp only [portRet, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hx, one_mul]
  ring

omit [Fintype S] in
/-- The reformulated wealth-accumulation constraint, O&R Supplement A, p. 742:
`Σ_n x_n (1 + r^n)(W − C) = (1 + r°)(W − C)` when `Σ_n x_n = 1`. -/
theorem wealth_accumulation_book (r : Fin N → S → ℝ) {x : Fin N → ℝ} (hx : ∑ i, x i = 1)
    (W C : ℝ) (s : S) :
    ∑ i, x i * (1 + r i s) * (W - C) = (1 + portRet r x s) * (W - C) := by
  simp only [portRet, mul_add, mul_one, Finset.sum_add_distrib, ← Finset.sum_mul, hx]

/-- The CRRA portfolio objective, O&R Supplement A, pp. 743–744: `E[(1 + r°)^{1−ρ}]/(1−ρ)`, the
expected utility of the gross portfolio return. -/
noncomputable def portObj (Ω : StateSpace S) (ρ : ℝ) (r : Fin N → S → ℝ) (x : Fin N → ℝ) : ℝ :=
  Ω.expect fun s => crraUtil ρ (1 + portRet r x s)

/-- The log portfolio objective, O&R Supplement A, p. 743: `E log(1 + r°)`. -/
noncomputable def logPortObj (Ω : StateSpace S) (r : Fin N → S → ℝ) (x : Fin N → ℝ) : ℝ :=
  Ω.expect fun s => Real.log (1 + portRet r x s)

/-- The portfolio condition (2) of O&R Supplement A, p. 743, at consumption proportional to
wealth and CRRA marginal utility: `E[(r^n − r^k)(1 + r°)^{−ρ}] = 0` for every asset `n`, with
reference asset `k` (the book's `N`). -/
def PortfolioCondition (Ω : StateSpace S) (ρ : ℝ) (r : Fin N → S → ℝ) (k : Fin N)
    (x : Fin N → ℝ) : Prop :=
  ∀ n, Ω.expect (fun s => (r n s - r k s) * (1 + portRet r x s) ^ (-ρ)) = 0

/-- The portfolio condition (2) in the log case, O&R Supplement A, p. 743:
`E[(r^n − r^k)(1 + r°)^{−1}] = 0` for every asset `n`. -/
def LogPortfolioCondition (Ω : StateSpace S) (r : Fin N → S → ℝ) (k : Fin N)
    (x : Fin N → ℝ) : Prop :=
  ∀ n, Ω.expect (fun s => (r n s - r k s) * (1 + portRet r x s)⁻¹) = 0

/-- Wealth invariance of the portfolio condition, O&R Supplement A, p. 743 ("multiplication of
both sides by `W_t`"): with `C_{t+1} = μW_{t+1}` and `W_{t+1} = (1 + r°)(1 − μ)W_t`, the
condition (2) `E[(r^n − r^k) u′(C_{t+1})] = 0` with `u′(C) = C^{−ρ}` holds iff
`E[(r^n − r^k)(1 + r°)^{−ρ}] = 0`, whatever `W_t > 0` (any real `ρ`; `ρ = 1` is the log case). -/
theorem portfolio_condition_wealth_invariant (Ω : StateSpace S) (ρ : ℝ) (r : Fin N → S → ℝ)
    (n k : Fin N) {x : Fin N → ℝ} (hx : ∀ s, 0 < 1 + portRet r x s) {μ W : ℝ} (hμ0 : 0 < μ)
    (hμ1 : μ < 1) (hW : 0 < W) :
    Ω.expect (fun s => (r n s - r k s) * (μ * ((1 + portRet r x s) * (1 - μ) * W)) ^ (-ρ)) = 0
      ↔ Ω.expect (fun s => (r n s - r k s) * (1 + portRet r x s) ^ (-ρ)) = 0 := by
  have h1 : 0 < 1 - μ := by linarith
  have hK : 0 < (μ * ((1 - μ) * W)) ^ (-ρ) := Real.rpow_pos_of_pos (by positivity) _
  have e : Ω.expect (fun s => (r n s - r k s) * (μ * ((1 + portRet r x s) * (1 - μ) * W)) ^ (-ρ))
      = (μ * ((1 - μ) * W)) ^ (-ρ)
        * Ω.expect (fun s => (r n s - r k s) * (1 + portRet r x s) ^ (-ρ)) := by
    simp only [StateSpace.expect, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [show μ * ((1 + portRet r x s) * (1 - μ) * W) = (μ * ((1 - μ) * W)) * (1 + portRet r x s)
      by ring, Real.mul_rpow (by positivity) (hx s).le]
    ring
  rw [e]
  constructor
  · intro h; exact (mul_eq_zero.mp h).resolve_left hK.ne'
  · intro h; rw [h, mul_zero]

/-- The perturbed portfolio `x + ε(e_n − e_k)`: move a fraction `ε` of wealth from asset `k` to
asset `n` (O&R Supplement A, p. 743, the unconstrained shares `x_n`, `n < N`). -/
def portShift (x : Fin N → ℝ) (n k : Fin N) (ε : ℝ) : Fin N → ℝ :=
  fun i => x i + ε * ((if i = n then 1 else 0) - (if i = k then 1 else 0))

/-- Shifting between assets keeps the shares adding up to one (O&R Supplement A, p. 742). -/
theorem portShift_sum (x : Fin N → ℝ) (n k : Fin N) (ε : ℝ) :
    ∑ i, portShift x n k ε i = ∑ i, x i := by
  simp [portShift, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib]

omit [Fintype S] in
/-- The return on the shifted portfolio, `r°(x + ε(e_n − e_k)) = r°(x) + ε(r^n − r^k)`
(O&R Supplement A, p. 743). -/
theorem portRet_portShift (r : Fin N → S → ℝ) (x : Fin N → ℝ) (n k : Fin N) (ε : ℝ) (s : S) :
    portRet r (portShift x n k ε) s = portRet r x s + ε * (r n s - r k s) := by
  simp only [portRet, portShift, add_mul, Finset.sum_add_distrib, sub_mul, mul_assoc,
    Finset.sum_sub_distrib, ← Finset.mul_sum, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte]

/-- Sufficiency of the portfolio condition (2), O&R Supplement A, p. 743: for CRRA utility
(`ρ > 0`, `ρ ≠ 1`), a feasible portfolio `x*` satisfying (2) maximises the portfolio objective
`E[(1 + r°)^{1−ρ}]/(1−ρ)` over all feasible portfolios (concavity). -/
theorem portfolio_condition_sufficient (Ω : StateSpace S) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≠ 1)
    (r : Fin N → S → ℝ) (k : Fin N) {xs : Fin N → ℝ} (hxs : PortFeasible r xs)
    (hfoc : PortfolioCondition Ω ρ r k xs) {x : Fin N → ℝ} (hx : PortFeasible r x) :
    portObj Ω ρ r x ≤ portObj Ω ρ r xs := by
  have hd : ∀ s, portRet r x s - portRet r xs s = ∑ i, (x i - xs i) * (r i s - r k s) := by
    intro s
    rw [portRet_eq_book r hx.1 k, portRet_eq_book r hxs.1 k]
    simp only [sub_mul, Finset.sum_sub_distrib]
    ring
  have hzero : Ω.expect (fun s => (1 + portRet r xs s) ^ (-ρ)
      * ((1 + portRet r x s) - (1 + portRet r xs s))) = 0 := by
    have e : Ω.expect (fun s => (1 + portRet r xs s) ^ (-ρ)
        * ((1 + portRet r x s) - (1 + portRet r xs s)))
        = ∑ i, (x i - xs i) * Ω.expect (fun s => (r i s - r k s) * (1 + portRet r xs s) ^ (-ρ))
        := by
      simp only [StateSpace.expect, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [show 1 + portRet r x s - (1 + portRet r xs s) = portRet r x s - portRet r xs s by ring,
        hd s, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e]
    exact Finset.sum_eq_zero fun i _ => by rw [hfoc i, mul_zero]
  have hle : ∀ s, Ω.prob s * crraUtil ρ (1 + portRet r x s) ≤ Ω.prob s
      * (crraUtil ρ (1 + portRet r xs s) + (1 + portRet r xs s) ^ (-ρ)
        * ((1 + portRet r x s) - (1 + portRet r xs s))) := fun s =>
    mul_le_mul_of_nonneg_left (crra_tangent hρ hρ1 (hxs.2 s) (hx.2 s)) (Ω.prob_nonneg s)
  have h2 := Finset.sum_le_sum fun s (_ : s ∈ univ) => hle s
  simp only [mul_add, Finset.sum_add_distrib] at h2
  unfold portObj StateSpace.expect
  unfold StateSpace.expect at hzero
  linarith

/-- Necessity of the portfolio condition (2), O&R Supplement A, p. 743: if a feasible portfolio
`x*` maximises the CRRA portfolio objective over feasible portfolios (`ρ ≠ 1`), it satisfies
`E[(r^n − r^k)(1 + r°)^{−ρ}] = 0` for every asset `n` (shift wealth between `n` and `k`). -/
theorem portfolio_condition_necessary (Ω : StateSpace S) {ρ : ℝ} (hρ1 : ρ ≠ 1)
    (r : Fin N → S → ℝ) (k : Fin N) {xs : Fin N → ℝ} (hxs : PortFeasible r xs)
    (hmax : ∀ x, PortFeasible r x → portObj Ω ρ r x ≤ portObj Ω ρ r xs) :
    PortfolioCondition Ω ρ r k xs := by
  intro n
  have hp : (1 : ℝ) - ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm hρ1)
  have hφ : ∀ ε, portObj Ω ρ r (portShift xs n k ε)
      = ∑ s, Ω.prob s * ((1 + portRet r xs s + ε * (r n s - r k s)) ^ (1 - ρ) / (1 - ρ)) := by
    intro ε
    simp only [portObj, StateSpace.expect, crraUtil, portRet_portShift, add_assoc]
  have hpos : ∀ᶠ ε in nhds (0 : ℝ), ∀ s, 0 < 1 + portRet r xs s + ε * (r n s - r k s) := by
    rw [Filter.eventually_all]
    intro s
    have c : ContinuousAt (fun ε : ℝ => 1 + portRet r xs s + ε * (r n s - r k s)) 0 := by
      fun_prop
    exact c.eventually (lt_mem_nhds (by simpa using hxs.2 s))
  have hloc : IsLocalMax (fun ε => ∑ s, Ω.prob s
      * ((1 + portRet r xs s + ε * (r n s - r k s)) ^ (1 - ρ) / (1 - ρ))) 0 := by
    filter_upwards [hpos] with ε hε
    rw [← hφ, ← hφ]
    have e0 : portShift xs n k 0 = xs := by funext i; simp [portShift]
    rw [e0]
    refine hmax _ ⟨by rw [portShift_sum]; exact hxs.1, fun s => ?_⟩
    rw [portRet_portShift, ← add_assoc]; exact hε s
  have hd : HasDerivAt (fun ε => ∑ s, Ω.prob s
      * ((1 + portRet r xs s + ε * (r n s - r k s)) ^ (1 - ρ) / (1 - ρ)))
      (∑ s, Ω.prob s * ((r n s - r k s) * (1 + portRet r xs s) ^ (-ρ))) 0 := by
    refine HasDerivAt.fun_sum fun s _ => ?_
    have h1 : HasDerivAt (fun ε : ℝ => 1 + portRet r xs s + ε * (r n s - r k s))
        (r n s - r k s) 0 := by
      simpa using HasDerivAt.const_add (1 + portRet r xs s)
        (HasDerivAt.mul_const (hasDerivAt_id (0 : ℝ)) (r n s - r k s))
    have h2 := HasDerivAt.rpow_const (p := 1 - ρ) h1 (Or.inl (by simpa using (hxs.2 s).ne'))
    have h3 := HasDerivAt.const_mul (Ω.prob s) (HasDerivAt.div_const h2 (1 - ρ))
    convert h3 using 1
    simp only [zero_mul, add_zero, show (1 : ℝ) - ρ - 1 = -ρ by ring]
    field_simp
  have := hloc.hasDerivAt_eq_zero hd
  simpa [StateSpace.expect] using this

/-- Sufficiency of the log portfolio condition, O&R Supplement A, p. 743: a feasible portfolio
satisfying `E[(r^n − r^k)(1 + r°)^{−1}] = 0` maximises `E log(1 + r°)` over feasible
portfolios. -/
theorem log_portfolio_condition_sufficient (Ω : StateSpace S) (r : Fin N → S → ℝ) (k : Fin N)
    {xs : Fin N → ℝ} (hxs : PortFeasible r xs) (hfoc : LogPortfolioCondition Ω r k xs)
    {x : Fin N → ℝ} (hx : PortFeasible r x) : logPortObj Ω r x ≤ logPortObj Ω r xs := by
  have hd : ∀ s, portRet r x s - portRet r xs s = ∑ i, (x i - xs i) * (r i s - r k s) := by
    intro s
    rw [portRet_eq_book r hx.1 k, portRet_eq_book r hxs.1 k]
    simp only [sub_mul, Finset.sum_sub_distrib]
    ring
  have hzero : Ω.expect (fun s => 1 / (1 + portRet r xs s)
      * ((1 + portRet r x s) - (1 + portRet r xs s))) = 0 := by
    have e : Ω.expect (fun s => 1 / (1 + portRet r xs s)
        * ((1 + portRet r x s) - (1 + portRet r xs s)))
        = ∑ i, (x i - xs i) * Ω.expect (fun s => (r i s - r k s) * (1 + portRet r xs s)⁻¹) := by
      simp only [StateSpace.expect, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [show 1 + portRet r x s - (1 + portRet r xs s) = portRet r x s - portRet r xs s by ring,
        hd s, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e]
    exact Finset.sum_eq_zero fun i _ => by rw [hfoc i, mul_zero]
  have hle : ∀ s, Ω.prob s * Real.log (1 + portRet r x s) ≤ Ω.prob s
      * (Real.log (1 + portRet r xs s) + 1 / (1 + portRet r xs s)
        * ((1 + portRet r x s) - (1 + portRet r xs s))) := fun s =>
    mul_le_mul_of_nonneg_left (log_tangent (hxs.2 s) (hx.2 s)) (Ω.prob_nonneg s)
  have h2 := Finset.sum_le_sum fun s (_ : s ∈ univ) => hle s
  simp only [mul_add, Finset.sum_add_distrib] at h2
  unfold logPortObj StateSpace.expect
  unfold StateSpace.expect at hzero
  linarith

/-- Necessity of the log portfolio condition, O&R Supplement A, p. 743: a feasible portfolio
maximising `E log(1 + r°)` over feasible portfolios satisfies
`E[(r^n − r^k)(1 + r°)^{−1}] = 0` for every asset `n`. -/
theorem log_portfolio_condition_necessary (Ω : StateSpace S) (r : Fin N → S → ℝ) (k : Fin N)
    {xs : Fin N → ℝ} (hxs : PortFeasible r xs)
    (hmax : ∀ x, PortFeasible r x → logPortObj Ω r x ≤ logPortObj Ω r xs) :
    LogPortfolioCondition Ω r k xs := by
  intro n
  have hφ : ∀ ε, logPortObj Ω r (portShift xs n k ε)
      = ∑ s, Ω.prob s * Real.log (1 + portRet r xs s + ε * (r n s - r k s)) := by
    intro ε
    simp only [logPortObj, StateSpace.expect, portRet_portShift, add_assoc]
  have hpos : ∀ᶠ ε in nhds (0 : ℝ), ∀ s, 0 < 1 + portRet r xs s + ε * (r n s - r k s) := by
    rw [Filter.eventually_all]
    intro s
    have c : ContinuousAt (fun ε : ℝ => 1 + portRet r xs s + ε * (r n s - r k s)) 0 := by
      fun_prop
    exact c.eventually (lt_mem_nhds (by simpa using hxs.2 s))
  have hloc : IsLocalMax (fun ε => ∑ s, Ω.prob s
      * Real.log (1 + portRet r xs s + ε * (r n s - r k s))) 0 := by
    filter_upwards [hpos] with ε hε
    rw [← hφ, ← hφ]
    have e0 : portShift xs n k 0 = xs := by funext i; simp [portShift]
    rw [e0]
    refine hmax _ ⟨by rw [portShift_sum]; exact hxs.1, fun s => ?_⟩
    rw [portRet_portShift, ← add_assoc]; exact hε s
  have hd : HasDerivAt (fun ε => ∑ s, Ω.prob s
      * Real.log (1 + portRet r xs s + ε * (r n s - r k s)))
      (∑ s, Ω.prob s * ((r n s - r k s) * (1 + portRet r xs s)⁻¹)) 0 := by
    refine HasDerivAt.fun_sum fun s _ => ?_
    have h1 : HasDerivAt (fun ε : ℝ => 1 + portRet r xs s + ε * (r n s - r k s))
        (r n s - r k s) 0 := by
      simpa using HasDerivAt.const_add (1 + portRet r xs s)
        (HasDerivAt.mul_const (hasDerivAt_id (0 : ℝ)) (r n s - r k s))
    have h2 := HasDerivAt.log h1 (by simpa using (hxs.2 s).ne')
    have h3 := HasDerivAt.const_mul (Ω.prob s) h2
    convert h3 using 1
    simp only [zero_mul, add_zero, div_eq_mul_inv]
  have := hloc.hasDerivAt_eq_zero hd
  simpa [StateSpace.expect] using this

/-! ## The Bellman equation -/

/-- The certainty-equivalent growth factor `βE(1 + r°)^{1−ρ}` of a portfolio `x`, O&R
Supplement A, p. 744. -/
noncomputable def growthFactor (Ω : StateSpace S) (β ρ : ℝ) (r : Fin N → S → ℝ)
    (x : Fin N → ℝ) : ℝ :=
  β * Ω.expect fun s => (1 + portRet r x s) ^ (1 - ρ)

/-- The CRRA consumption share `μ = 1 − [βE(1 + r°)^{1−ρ}]^{1/ρ}` at the portfolio `x`,
O&R Supplement A, p. 744. -/
noncomputable def crraShare (Ω : StateSpace S) (β ρ : ℝ) (r : Fin N → S → ℝ)
    (x : Fin N → ℝ) : ℝ :=
  1 - growthFactor Ω β ρ r x ^ (1 / ρ)

/-- The CRRA value function `V(W) = μ^{−ρ} W^{1−ρ}/(1−ρ)` (O&R Supplement A, pp. 742–744: the
book's guess `C = μW` corresponds to `V(W) = A W^{1−ρ}/(1−ρ)` with `A = μ^{−ρ}`). -/
noncomputable def crraValue (μ ρ W : ℝ) : ℝ := μ ^ (-ρ) * crraUtil ρ W

/-- The right-hand side of the Bellman equation, O&R Supplement A, p. 742:
`u(C) + βE V((1 + r°(x))(W − C))`, maximised over consumption `C` and portfolio `x`. -/
noncomputable def bellmanRHS (Ω : StateSpace S) (β : ℝ) (u V : ℝ → ℝ) (r : Fin N → S → ℝ)
    (W C : ℝ) (x : Fin N → ℝ) : ℝ :=
  u C + β * Ω.expect fun s => V ((1 + portRet r x s) * (W - C))

/-- An expectation of a positive random variable is positive (the probabilities sum to one),
O&R §5.1 conventions, used in Supplement A. -/
theorem expect_pos (Ω : StateSpace S) {f : S → ℝ} (hf : ∀ s, 0 < f s) : 0 < Ω.expect f := by
  have hlt : ∑ _s : S, (0 : ℝ) < ∑ s, Ω.prob s := by rw [Ω.prob_sum]; simp
  obtain ⟨s₀, -, hs₀⟩ := Finset.exists_lt_of_sum_lt hlt
  exact Finset.sum_pos' (fun s _ => mul_nonneg (Ω.prob_nonneg s) (hf s).le)
    ⟨s₀, Finset.mem_univ _, mul_pos hs₀ (hf s₀)⟩

/-- The growth factor is positive for a feasible portfolio and `β > 0` (O&R p. 744). -/
theorem growthFactor_pos (Ω : StateSpace S) {β : ℝ} (hβ : 0 < β) (ρ : ℝ) (r : Fin N → S → ℝ)
    {x : Fin N → ℝ} (hx : PortFeasible r x) : 0 < growthFactor Ω β ρ r x :=
  mul_pos hβ (expect_pos Ω fun s => Real.rpow_pos_of_pos (hx.2 s) _)

/-- Under the parameter condition `βE(1 + r°)^{1−ρ} < 1` the share lies in `(0, 1)`, and
`(1 − μ)^ρ = βE(1 + r°)^{1−ρ}` (O&R Supplement A, p. 744). -/
theorem crraShare_mem (Ω : StateSpace S) {β ρ : ℝ} (hβ : 0 < β) (hρ : 0 < ρ)
    (r : Fin N → S → ℝ) {x : Fin N → ℝ} (hx : PortFeasible r x)
    (hB : growthFactor Ω β ρ r x < 1) :
    0 < crraShare Ω β ρ r x ∧ crraShare Ω β ρ r x < 1
      ∧ (1 - crraShare Ω β ρ r x) ^ ρ = growthFactor Ω β ρ r x := by
  have hB0 := growthFactor_pos Ω hβ ρ r hx
  have h1 : growthFactor Ω β ρ r x ^ (1 / ρ) < 1 :=
    Real.rpow_lt_one hB0.le hB (one_div_pos.mpr hρ)
  have h2 : 0 < growthFactor Ω β ρ r x ^ (1 / ρ) := Real.rpow_pos_of_pos hB0 _
  refine ⟨by unfold crraShare; linarith, by unfold crraShare; linarith, ?_⟩
  rw [crraShare, sub_sub_cancel, one_div, Real.rpow_inv_rpow hB0.le hρ.ne']

/-- The continuation value at the CRRA guess, O&R Supplement A, p. 743: for `W − C > 0` and a
feasible portfolio, `βE[A u((1 + r°)(W − C))] = A · βE(1 + r°)^{1−ρ} · u(W − C)` with
`u(C) = C^{1−ρ}/(1−ρ)`: the portfolio and saving decisions separate. -/
theorem expect_next_crra (Ω : StateSpace S) (β ρ A : ℝ) (r : Fin N → S → ℝ) {x : Fin N → ℝ}
    (hx : PortFeasible r x) {D : ℝ} (hD : 0 < D) :
    β * Ω.expect (fun s => A * crraUtil ρ ((1 + portRet r x s) * D))
      = A * growthFactor Ω β ρ r x * crraUtil ρ D := by
  simp only [growthFactor, StateSpace.expect, crraUtil, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Real.mul_rpow (hx.2 s).le hD.le]
  ring

/-- The growth factor times utility of saving equals `β(W − C)^{1−ρ}` times the portfolio
objective (O&R Supplement A, p. 743; `ρ ≠ 1`). -/
theorem growthFactor_mul_crraUtil (Ω : StateSpace S) (β : ℝ) {ρ : ℝ} (hρ1 : ρ ≠ 1)
    (r : Fin N → S → ℝ) (x : Fin N → ℝ) (D : ℝ) :
    growthFactor Ω β ρ r x * crraUtil ρ D = β * D ^ (1 - ρ) * portObj Ω ρ r x := by
  have hp : (1 : ℝ) - ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm hρ1)
  simp only [growthFactor, portObj, StateSpace.expect, crraUtil, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun s _ => ?_
  field_simp

/-- The consumption split at the CRRA guess, O&R Supplement A, p. 744: for `0 < μ < 1`,
`0 < C < W`, `u(C) + μ^{−ρ}(1 − μ)^ρ u(W − C) ≤ μ^{−ρ} u(W)` (supporting lines at `μW` and
`(1 − μ)W`). -/
theorem crra_split_le {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≠ 1) {μ W C : ℝ} (hμ0 : 0 < μ)
    (hμ1 : μ < 1) (hC : 0 < C) (hCW : C < W) :
    crraUtil ρ C + μ ^ (-ρ) * (1 - μ) ^ ρ * crraUtil ρ (W - C) ≤ μ ^ (-ρ) * crraUtil ρ W := by
  have hW : 0 < W := hC.trans hCW
  have h1 : 0 < 1 - μ := by linarith
  have hμW : 0 < μ * W := mul_pos hμ0 hW
  have h1W : 0 < (1 - μ) * W := mul_pos h1 hW
  have hD : 0 < W - C := by linarith
  have t1 := crra_tangent hρ hρ1 hμW hC
  have t2 := crra_tangent hρ hρ1 h1W hD
  have hK : 0 ≤ μ ^ (-ρ) * (1 - μ) ^ ρ :=
    mul_nonneg (Real.rpow_nonneg hμ0.le _) (Real.rpow_nonneg h1.le _)
  have hbb : (1 - μ) ^ ρ * (1 - μ) ^ (-ρ) = 1 := by
    rw [Real.rpow_neg h1.le, mul_inv_cancel₀ (Real.rpow_pos_of_pos h1 _).ne']
  have hμp : μ ^ (1 - ρ) = μ ^ (-ρ) * μ := by
    rw [show (1 : ℝ) - ρ = -ρ + 1 by ring, Real.rpow_add hμ0, Real.rpow_one]
  have h1p : (1 - μ) ^ (1 - ρ) = (1 - μ) ^ (-ρ) * (1 - μ) := by
    rw [show (1 : ℝ) - ρ = -ρ + 1 by ring, Real.rpow_add h1, Real.rpow_one]
  have i1 : μ ^ (-ρ) * (1 - μ) ^ ρ * ((1 - μ) * W) ^ (-ρ) = (μ * W) ^ (-ρ) := by
    rw [Real.mul_rpow h1.le hW.le, Real.mul_rpow hμ0.le hW.le]
    linear_combination μ ^ (-ρ) * W ^ (-ρ) * hbb
  have i2 : crraUtil ρ (μ * W) + μ ^ (-ρ) * (1 - μ) ^ ρ * crraUtil ρ ((1 - μ) * W)
      = μ ^ (-ρ) * crraUtil ρ W := by
    simp only [crraUtil]
    rw [Real.mul_rpow hμ0.le hW.le, Real.mul_rpow h1.le hW.le, hμp, h1p]
    linear_combination μ ^ (-ρ) * (1 - μ) * W ^ (1 - ρ) / (1 - ρ) * hbb
  have t2' := mul_le_mul_of_nonneg_left t2 hK
  calc crraUtil ρ C + μ ^ (-ρ) * (1 - μ) ^ ρ * crraUtil ρ (W - C)
      ≤ crraUtil ρ (μ * W) + (μ * W) ^ (-ρ) * (C - μ * W)
        + μ ^ (-ρ) * (1 - μ) ^ ρ * (crraUtil ρ ((1 - μ) * W)
          + ((1 - μ) * W) ^ (-ρ) * (W - C - (1 - μ) * W)) := by linarith
    _ = μ ^ (-ρ) * crraUtil ρ W := by
      linear_combination i2 + (W - C - (1 - μ) * W) * i1

/-- Equality in the consumption split at `C = μW`, O&R Supplement A, p. 744:
`u(μW) + μ^{−ρ}(1 − μ)^ρ u(W − μW) = μ^{−ρ} u(W)`. -/
theorem crra_split_eq {ρ : ℝ} {μ W : ℝ} (hμ0 : 0 < μ) (hμ1 : μ < 1) (hW : 0 < W) :
    crraUtil ρ (μ * W) + μ ^ (-ρ) * (1 - μ) ^ ρ * crraUtil ρ (W - μ * W)
      = μ ^ (-ρ) * crraUtil ρ W := by
  have h1 : 0 < 1 - μ := by linarith
  have hbb : (1 - μ) ^ ρ * (1 - μ) ^ (-ρ) = 1 := by
    rw [Real.rpow_neg h1.le, mul_inv_cancel₀ (Real.rpow_pos_of_pos h1 _).ne']
  have hμp : μ ^ (1 - ρ) = μ ^ (-ρ) * μ := by
    rw [show (1 : ℝ) - ρ = -ρ + 1 by ring, Real.rpow_add hμ0, Real.rpow_one]
  have h1p : (1 - μ) ^ (1 - ρ) = (1 - μ) ^ (-ρ) * (1 - μ) := by
    rw [show (1 : ℝ) - ρ = -ρ + 1 by ring, Real.rpow_add h1, Real.rpow_one]
  rw [show W - μ * W = (1 - μ) * W by ring]
  simp only [crraUtil]
  rw [Real.mul_rpow hμ0.le hW.le, Real.mul_rpow h1.le hW.le, hμp, h1p]
  linear_combination μ ^ (-ρ) * (1 - μ) * W ^ (1 - ρ) / (1 - ρ) * hbb

/-- The Bellman equation of O&R Supplement A, pp. 742–744, solved exactly. Let `ρ > 0`,
`ρ ≠ 1`, `β > 0`, let the feasible portfolio `x*` satisfy the portfolio condition (2), and
assume `βE(1 + r°(x*))^{1−ρ} < 1`. With `μ = 1 − [βE(1 + r°)^{1−ρ}]^{1/ρ}` and
`V(W) = μ^{−ρ} W^{1−ρ}/(1−ρ)`, for every `W > 0`: every consumption `0 < C < W` and feasible
portfolio give `u(C) + βE V((1 + r°)(W − C)) ≤ V(W)`, with equality at `C = μW` and `x*`. -/
theorem bellman_crra (Ω : StateSpace S) {β ρ : ℝ} (hβ : 0 < β) (hρ : 0 < ρ) (hρ1 : ρ ≠ 1)
    (r : Fin N → S → ℝ) (k : Fin N) {xs : Fin N → ℝ} (hxs : PortFeasible r xs)
    (hfoc : PortfolioCondition Ω ρ r k xs) (hB : growthFactor Ω β ρ r xs < 1) {W : ℝ}
    (hW : 0 < W) :
    (∀ C x, 0 < C → C < W → PortFeasible r x →
      bellmanRHS Ω β (crraUtil ρ) (crraValue (crraShare Ω β ρ r xs) ρ) r W C x
        ≤ crraValue (crraShare Ω β ρ r xs) ρ W) ∧
    bellmanRHS Ω β (crraUtil ρ) (crraValue (crraShare Ω β ρ r xs) ρ) r W
        (crraShare Ω β ρ r xs * W) xs = crraValue (crraShare Ω β ρ r xs) ρ W := by
  obtain ⟨hμ0, hμ1, hBμ⟩ := crraShare_mem Ω hβ hρ r hxs hB
  set μ := crraShare Ω β ρ r xs
  have hcont : ∀ C x, C < W → PortFeasible r x → bellmanRHS Ω β (crraUtil ρ) (crraValue μ ρ) r W C x
      = crraUtil ρ C + μ ^ (-ρ) * growthFactor Ω β ρ r x * crraUtil ρ (W - C) := by
    intro C x hCW hx
    rw [bellmanRHS, ← expect_next_crra Ω β ρ (μ ^ (-ρ)) r hx (by linarith : 0 < W - C)]
    rfl
  refine ⟨fun C x hC hCW hx => ?_, ?_⟩
  · rw [hcont C x hCW hx]
    have hp : growthFactor Ω β ρ r x * crraUtil ρ (W - C)
        ≤ growthFactor Ω β ρ r xs * crraUtil ρ (W - C) := by
      rw [growthFactor_mul_crraUtil Ω β hρ1, growthFactor_mul_crraUtil Ω β hρ1]
      exact mul_le_mul_of_nonneg_left (portfolio_condition_sufficient Ω hρ hρ1 r k hxs hfoc hx)
        (mul_nonneg hβ.le (Real.rpow_nonneg (by linarith) _))
    have hμr : 0 ≤ μ ^ (-ρ) := Real.rpow_nonneg hμ0.le _
    have := crra_split_le hρ hρ1 hμ0 hμ1 hC hCW
    rw [hBμ] at this
    unfold crraValue
    nlinarith [mul_le_mul_of_nonneg_left hp hμr]
  · rw [hcont _ xs (by nlinarith) hxs, ← hBμ, mul_assoc (μ ^ (-ρ))]
    unfold crraValue
    rw [← mul_assoc]
    exact crra_split_eq hμ0 hμ1 hW

/-- The derivative of CRRA utility, `u′(C) = C^{−ρ}` (O&R Supplement A, p. 742; `ρ ≠ 1`). -/
theorem hasDerivAt_crraUtil {ρ : ℝ} (hρ1 : ρ ≠ 1) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (crraUtil ρ) (x ^ (-ρ)) x := by
  have hp : (1 : ℝ) - ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm hρ1)
  have h := HasDerivAt.div_const (HasDerivAt.rpow_const (p := 1 - ρ) (hasDerivAt_id x)
    (Or.inl hx.ne')) (1 - ρ)
  simp only [id] at h
  rw [show (1 : ℝ) - ρ - 1 = -ρ by ring] at h
  have e : 1 * (1 - ρ) * x ^ (-ρ) / (1 - ρ) = x ^ (-ρ) := by field_simp
  rw [e] at h
  exact h

/-- Solving the Bellman equation for the guess, O&R Supplement A, pp. 743–744. Suppose
`V(W) = A W^{1−ρ}/(1−ρ)` satisfies the Bellman equation at some `W > 0` with the
optimal portfolio `x*`, the maximum over consumption `0 < C < W` being attained at `C = μW` with
`0 < μ < 1`. Then `A = μ^{−ρ}` and `μ = 1 − [βE(1 + r°)^{1−ρ}]^{1/ρ}` (the first-order condition
in `C` and value matching; `ρ > 0`, `ρ ≠ 1`, `β > 0`). -/
theorem bellman_guess_pins_share (Ω : StateSpace S) {β ρ : ℝ} (hβ : 0 < β) (hρ : 0 < ρ)
    (hρ1 : ρ ≠ 1) (r : Fin N → S → ℝ) {xs : Fin N → ℝ} (hxs : PortFeasible r xs)
    {A μ W : ℝ} (hμ0 : 0 < μ) (hμ1 : μ < 1) (hW : 0 < W)
    (hmax : ∀ C, 0 < C → C < W → bellmanRHS Ω β (crraUtil ρ) (fun w => A * crraUtil ρ w) r W C xs
      ≤ bellmanRHS Ω β (crraUtil ρ) (fun w => A * crraUtil ρ w) r W (μ * W) xs)
    (hval : bellmanRHS Ω β (crraUtil ρ) (fun w => A * crraUtil ρ w) r W (μ * W) xs
      = A * crraUtil ρ W) :
    A = μ ^ (-ρ) ∧ μ = crraShare Ω β ρ r xs := by
  set B := growthFactor Ω β ρ r xs with hB_def
  have hB := growthFactor_pos Ω hβ ρ r hxs
  have h1 : 0 < 1 - μ := by linarith
  have hμW : 0 < μ * W := mul_pos hμ0 hW
  have hp : (1 : ℝ) - ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm hρ1)
  have hg : ∀ C, C < W → bellmanRHS Ω β (crraUtil ρ) (fun w => A * crraUtil ρ w) r W C xs
      = crraUtil ρ C + A * B * crraUtil ρ (W - C) := by
    intro C hCW
    rw [bellmanRHS, ← expect_next_crra Ω β ρ A r hxs (by linarith : 0 < W - C)]
  have hμWW : μ * W < W := by nlinarith
  have hloc : IsLocalMax (fun C => crraUtil ρ C + A * B * crraUtil ρ (W - C)) (μ * W) := by
    filter_upwards [Ioo_mem_nhds hμW hμWW] with C hC
    rw [← hg C hC.2, ← hg _ hμWW]
    exact hmax C hC.1 hC.2
  have hd : HasDerivAt (fun C => crraUtil ρ C + A * B * crraUtil ρ (W - C))
      ((μ * W) ^ (-ρ) + A * B * ((W - μ * W) ^ (-ρ) * (-1))) (μ * W) := by
    have hin : HasDerivAt (fun C : ℝ => W - C) (-1) (μ * W) := by
      simpa using HasDerivAt.const_sub W (hasDerivAt_id (μ * W))
    have hout := HasDerivAt.comp_of_eq (μ * W) (hasDerivAt_crraUtil hρ1
      (by linarith : 0 < W - μ * W)) hin rfl
    exact HasDerivAt.add (hasDerivAt_crraUtil hρ1 hμW) (HasDerivAt.const_mul (A * B) hout)
  have hfoc := hloc.hasDerivAt_eq_zero hd
  rw [show W - μ * W = (1 - μ) * W by ring, Real.mul_rpow hμ0.le hW.le,
    Real.mul_rpow h1.le hW.le] at hfoc
  have hWr : 0 < W ^ (-ρ) := Real.rpow_pos_of_pos hW _
  have foc : μ ^ (-ρ) = A * B * (1 - μ) ^ (-ρ) := by
    have : W ^ (-ρ) * (μ ^ (-ρ) - A * B * (1 - μ) ^ (-ρ)) = 0 := by linarith
    have := (mul_eq_zero.mp this).resolve_left hWr.ne'
    linarith
  rw [hg _ hμWW] at hval
  have hμp : μ ^ (1 - ρ) = μ ^ (-ρ) * μ := by
    rw [show (1 : ℝ) - ρ = -ρ + 1 by ring, Real.rpow_add hμ0, Real.rpow_one]
  have h1p : (1 - μ) ^ (1 - ρ) = (1 - μ) ^ (-ρ) * (1 - μ) := by
    rw [show (1 : ℝ) - ρ = -ρ + 1 by ring, Real.rpow_add h1, Real.rpow_one]
  rw [show W - μ * W = (1 - μ) * W by ring] at hval
  simp only [crraUtil] at hval
  rw [Real.mul_rpow hμ0.le hW.le, Real.mul_rpow h1.le hW.le, hμp, h1p] at hval
  field_simp at hval
  have hA' : A = μ ^ (-ρ) := by linear_combination -hval - (1 - μ) * foc
  refine ⟨hA', ?_⟩
  have hμr : 0 < μ ^ (-ρ) := Real.rpow_pos_of_pos hμ0 _
  have hB1 : B * (1 - μ) ^ (-ρ) = 1 := by
    rw [hA'] at foc
    have : μ ^ (-ρ) * (B * (1 - μ) ^ (-ρ) - 1) = 0 := by linear_combination -foc
    have := (mul_eq_zero.mp this).resolve_left hμr.ne'
    linarith
  have hBe : B = (1 - μ) ^ ρ := by
    rw [Real.rpow_neg h1.le] at hB1
    field_simp at hB1
    exact hB1
  rw [crraShare, ← hB_def, hBe, one_div, Real.rpow_rpow_inv h1.le hρ.ne']
  ring

/-- The share is the i.i.d. fixed point of the book's recursion, O&R Supplement A, p. 744:
`μ = (1 + [βE{(1 + r°)^{1−ρ} μ^{−ρ}}]^{1/ρ})^{−1}` (via `EventTree.crra_iid_share`). -/
theorem crraShare_iid_recursion (Ω : StateSpace S) {β ρ : ℝ} (hβ : 0 < β) (hρ : 0 < ρ)
    (r : Fin N → S → ℝ) {xs : Fin N → ℝ} (hxs : PortFeasible r xs)
    (hB : growthFactor Ω β ρ r xs < 1) :
    crraShare Ω β ρ r xs = (1 + (β * ∑ s, Ω.prob s * ((1 + portRet r xs s) ^ (1 - ρ)
      * crraShare Ω β ρ r xs ^ (-ρ))) ^ (1 / ρ))⁻¹ := by
  obtain ⟨hμ0, hμ1, -⟩ := crraShare_mem Ω hβ hρ r hxs hB
  exact (crra_iid_share Ω.prob (portRet r xs) Ω.prob_nonneg hxs.2 hβ.le hρ hμ0 hμ1).mpr rfl

/-- The consumption Euler equation (1), O&R Supplement A, pp. 742–744, at the solution:
with `C_t = μW_t`, `W_{t+1} = (1 + r°)(1 − μ)W_t` and `C_{t+1} = μW_{t+1}`,
`C_t^{−ρ} = βE[(1 + r°) C_{t+1}^{−ρ}]` for every `W_t > 0` (via
`EventTree.crra_share_recursion`). -/
theorem crraShare_euler (Ω : StateSpace S) {β ρ : ℝ} (hβ : 0 < β) (hρ : 0 < ρ)
    (r : Fin N → S → ℝ) {xs : Fin N → ℝ} (hxs : PortFeasible r xs)
    (hB : growthFactor Ω β ρ r xs < 1) {W : ℝ} (hW : 0 < W) :
    (crraShare Ω β ρ r xs * W) ^ (-ρ) = β * ∑ s, Ω.prob s * ((1 + portRet r xs s)
      * (crraShare Ω β ρ r xs * ((1 + portRet r xs s) * (1 - crraShare Ω β ρ r xs) * W))
        ^ (-ρ)) := by
  obtain ⟨hμ0, hμ1, -⟩ := crraShare_mem Ω hβ hρ r hxs hB
  exact (crra_share_recursion Ω.prob (portRet r xs) (fun _ => crraShare Ω β ρ r xs)
    Ω.prob_nonneg hxs.2 (fun _ => hμ0) hβ.le hρ hμ0 hμ1 hW).mpr
    (crraShare_iid_recursion Ω hβ hρ r hxs hB)

/-! ## The log case -/

/-- The constant of the log value function (O&R Supplement A, p. 743):
`K = [log(1 − β) + (β/(1 − β))(log β + E log(1 + r°))]/(1 − β)` at the portfolio `x`. -/
noncomputable def logValueConst (Ω : StateSpace S) (β : ℝ) (r : Fin N → S → ℝ)
    (x : Fin N → ℝ) : ℝ :=
  (Real.log (1 - β) + β / (1 - β) * (Real.log β + logPortObj Ω r x)) / (1 - β)

/-- The log value function `V(W) = log W/(1 − β) + K` (O&R Supplement A, p. 743). -/
noncomputable def logValue (Ω : StateSpace S) (β : ℝ) (r : Fin N → S → ℝ) (x : Fin N → ℝ)
    (W : ℝ) : ℝ :=
  Real.log W / (1 - β) + logValueConst Ω β r x

/-- The log continuation value, O&R Supplement A, p. 743: for `D = W − C > 0` and a feasible
portfolio `x`, `βE V((1 + r°(x))D) = (β/(1 − β))(E log(1 + r°(x)) + log D) + βK`. -/
theorem expect_next_log (Ω : StateSpace S) (β : ℝ) (r : Fin N → S → ℝ) (xs : Fin N → ℝ)
    {x : Fin N → ℝ} (hx : PortFeasible r x) {D : ℝ} (hD : 0 < D) :
    β * Ω.expect (fun s => logValue Ω β r xs ((1 + portRet r x s) * D))
      = β / (1 - β) * (logPortObj Ω r x + Real.log D) + β * logValueConst Ω β r xs := by
  have e : ∀ s, Ω.prob s * logValue Ω β r xs ((1 + portRet r x s) * D)
      = Ω.prob s * Real.log (1 + portRet r x s) / (1 - β)
        + Ω.prob s * (Real.log D / (1 - β) + logValueConst Ω β r xs) := by
    intro s
    rw [logValue, Real.log_mul (hx.2 s).ne' hD.ne']
    ring
  simp only [StateSpace.expect, e, Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_mul,
    Ω.prob_sum, logPortObj]
  ring

/-- The Bellman equation with log utility, O&R Supplement A, p. 743, solved exactly: for
`0 < β < 1` and a feasible portfolio `x*` satisfying the log portfolio condition, with
`V(W) = log W/(1 − β) + K`, every `0 < C < W` and feasible portfolio give
`log C + βE V((1 + r°)(W − C)) ≤ V(W)`, with equality at `C = (1 − β)W` and `x*`: the book's
`μ = 1 − β`, whatever the return distribution. -/
theorem bellman_log (Ω : StateSpace S) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (r : Fin N → S → ℝ) (k : Fin N) {xs : Fin N → ℝ} (hxs : PortFeasible r xs)
    (hfoc : LogPortfolioCondition Ω r k xs) {W : ℝ} (hW : 0 < W) :
    (∀ C x, 0 < C → C < W → PortFeasible r x →
      bellmanRHS Ω β Real.log (logValue Ω β r xs) r W C x ≤ logValue Ω β r xs W) ∧
    bellmanRHS Ω β Real.log (logValue Ω β r xs) r W ((1 - β) * W) xs = logValue Ω β r xs W := by
  have h1 : 0 < 1 - β := by linarith
  have hconst : Real.log ((1 - β) * W) + β / (1 - β) * (logPortObj Ω r xs + Real.log (β * W))
      + β * logValueConst Ω β r xs = logValue Ω β r xs W := by
    rw [logValue, logValueConst, Real.log_mul h1.ne' hW.ne', Real.log_mul hβ0.ne' hW.ne']
    field_simp
    ring
  refine ⟨fun C x hC hCW hx => ?_, ?_⟩
  · have hD : 0 < W - C := by linarith
    rw [bellmanRHS, expect_next_log Ω β r xs hx hD]
    have hp := log_portfolio_condition_sufficient Ω r k hxs hfoc hx
    have hc : 0 ≤ β / (1 - β) := div_nonneg hβ0.le h1.le
    have t1 := log_tangent (mul_pos h1 hW) hC
    have t2 := log_tangent (mul_pos hβ0 hW) hD
    have e1 : β / (1 - β) * (1 / (β * W)) = 1 / ((1 - β) * W) := by field_simp
    have t2' := mul_le_mul_of_nonneg_left t2 hc
    rw [← hconst]
    have lin : 1 / ((1 - β) * W) * (C - (1 - β) * W)
        + β / (1 - β) * (1 / (β * W) * (W - C - β * W)) = 0 := by
      rw [← mul_assoc, e1]; ring
    nlinarith [mul_le_mul_of_nonneg_left hp hc]
  · rw [bellmanRHS, expect_next_log Ω β r xs hxs (by nlinarith), ← hconst,
      show W - (1 - β) * W = β * W by ring]
    ring

/-! ## Verification on the i.i.d. event tree

A plan chooses consumption `c n h` and a portfolio `x n h` at every history `h` of every date
`t = n + 1` of the i.i.d. tree; wealth then follows `W_{t+1} = (1 + r°(x_t))(W_t − C_t)`. -/

/-- Wealth along a plan (O&R Supplement A, p. 742): `W₁ = W₀` and, after the event `s` following
the history `h`, `W(h, s) = (1 + r°(x(h))(s))(W(h) − c(h))`. -/
noncomputable def wealth (r : Fin N → S → ℝ) (W₀ : ℝ) (c : (n : ℕ) → (Fin n → S) → ℝ)
    (x : (n : ℕ) → (Fin n → S) → Fin N → ℝ) : (n : ℕ) → (Fin n → S) → ℝ
  | 0, _ => W₀
  | n + 1, g => (1 + portRet r (x n (Fin.init g)) (g (Fin.last n)))
      * (wealth r W₀ c x n (Fin.init g) - c n (Fin.init g))

omit [Fintype S] in
/-- The wealth-accumulation identity along a plan, O&R Supplement A, p. 742:
`W_{t+1} = (1 + r°_{t+1})(W_t − C_t)` after the event `s`. -/
theorem wealth_snoc (r : Fin N → S → ℝ) (W₀ : ℝ) (c : (n : ℕ) → (Fin n → S) → ℝ)
    (x : (n : ℕ) → (Fin n → S) → Fin N → ℝ) {n : ℕ} (h : Fin n → S) (s : S) :
    wealth r W₀ c x (n + 1) (Fin.snoc h s)
      = (1 + portRet r (x n h) s) * (wealth r W₀ c x n h - c n h) := by
  simp only [wealth, Fin.init_snoc, Fin.snoc_last]

/-- An admissible plan (O&R Supplement A, p. 742): positive consumption, never more than current
wealth (end-of-period financial wealth `W − C ≥ 0`), and portfolio shares adding up to one at
every history. Admissibility for the infinite-horizon problem also requires the utility series
to converge; results state that as a separate `Summable` hypothesis. -/
def Admissible (r : Fin N → S → ℝ) (W₀ : ℝ) (c : (n : ℕ) → (Fin n → S) → ℝ)
    (x : (n : ℕ) → (Fin n → S) → Fin N → ℝ) : Prop :=
  (∀ n h, 0 < c n h) ∧ (∀ n h, c n h ≤ wealth r W₀ c x n h) ∧ (∀ n h, ∑ i, x n h i = 1)

/-- Along an admissible plan the investor saves a positive amount and holds a feasible portfolio
at every history (O&R Supplement A, p. 743, footnote 1: `W_t > C_t`): next period's consumption
must be positive in every state, which forces `W − C > 0` and `1 + r° > 0`. -/
theorem admissible_step (Ω : StateSpace S) (r : Fin N → S → ℝ) (W₀ : ℝ)
    {c : (n : ℕ) → (Fin n → S) → ℝ} {x : (n : ℕ) → (Fin n → S) → Fin N → ℝ}
    (hadm : Admissible r W₀ c x) (n : ℕ) (h : Fin n → S) :
    c n h < wealth r W₀ c x n h ∧ PortFeasible r (x n h) := by
  have hS : Nonempty S := by
    by_contra hS
    rw [not_nonempty_iff] at hS
    have := Ω.prob_sum
    simp [Finset.univ_eq_empty] at this
  have hD : 0 ≤ wealth r W₀ c x n h - c n h := by linarith [hadm.2.1 n h]
  have key : ∀ s, 0 < (1 + portRet r (x n h) s) * (wealth r W₀ c x n h - c n h) := by
    intro s
    rw [← wealth_snoc]
    exact lt_of_lt_of_le (hadm.1 _ _) (hadm.2.1 _ _)
  obtain ⟨s₀⟩ := hS
  have hD' : 0 < wealth r W₀ c x n h - c n h := by
    rcases hD.lt_or_eq with h' | h'
    · exact h'
    · have := key s₀; rw [← h', mul_zero] at this; exact absurd this (lt_irrefl 0)
  exact ⟨by linarith, hadm.2.2 n h, fun s => pos_of_mul_pos_left (key s) hD'.le⟩

/-- Expectation at date `t + 1` on the i.i.d. tree as an expectation over date-`t` histories of
the conditional expectation over the next event (O&R Supplement A, p. 744; the law of iterated
expectations on the event tree of Appendix 5C). -/
theorem sum_succ_iid (Ω : StateSpace S) (n : ℕ) (f : (Fin (n + 1) → S) → ℝ) :
    ∑ g, (iidTree Ω).histProb g * f g
      = ∑ h, (iidTree Ω).histProb h * Ω.expect (fun s => f (Fin.snoc h s)) := by
  rw [sum_snoc]
  refine Finset.sum_congr rfl fun h _ => ?_
  simp only [(iidTree Ω).histProb_snoc, StateSpace.expect, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [iidTree]
  ring

/-- The dynamic-programming inequality summed along a plan (O&R Supplement A, p. 742): if
`u(c) + βE V(W′) ≤ V(W)` holds at every history, then for every horizon `n`,
`Σ_{t<n} β^t E u(C_t) + β^n E V(W_n) ≤ V(W₀)`. -/
theorem telescope_le (Ω : StateSpace S) {β : ℝ} (hβ : 0 ≤ β) (u V : ℝ → ℝ)
    (r : Fin N → S → ℝ) (W₀ : ℝ) (c : (n : ℕ) → (Fin n → S) → ℝ)
    (x : (n : ℕ) → (Fin n → S) → Fin N → ℝ)
    (hstep : ∀ n h, u (c n h) + β * Ω.expect (fun s => V ((1 + portRet r (x n h) s)
      * (wealth r W₀ c x n h - c n h))) ≤ V (wealth r W₀ c x n h)) (n : ℕ) :
    ∑ k ∈ range n, utilSeries (iidTree Ω) β u c k
      + β ^ n * ∑ h, (iidTree Ω).histProb h * V (wealth r W₀ c x n h) ≤ V W₀ := by
  induction n with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, pow_zero, one_mul, zero_add,
      Fintype.sum_unique, (iidTree Ω).histProb_zero]
    rfl
  | succ n ih =>
    rw [Finset.sum_range_succ, sum_succ_iid]
    simp only [wealth_snoc]
    have hle : utilSeries (iidTree Ω) β u c n + β ^ (n + 1) * ∑ h, (iidTree Ω).histProb h
        * Ω.expect (fun s => V ((1 + portRet r (x n h) s) * (wealth r W₀ c x n h - c n h)))
        ≤ β ^ n * ∑ h, (iidTree Ω).histProb h * V (wealth r W₀ c x n h) := by
      rw [utilSeries, pow_succ, mul_assoc, ← mul_add, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun h _ => ?_) (pow_nonneg hβ n)
      have := mul_le_mul_of_nonneg_left (hstep n h) ((iidTree Ω).histProb_nonneg h)
      linarith
    linarith

/-- CRRA utility is increasing: `u(c) ≤ u(W)` for `0 < c ≤ W` (from the supporting line at `W`;
O&R Supplement A). -/
theorem crraUtil_mono {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≠ 1) {c W : ℝ} (hc : 0 < c) (hcW : c ≤ W) :
    crraUtil ρ c ≤ crraUtil ρ W := by
  have hW : 0 < W := lt_of_lt_of_le hc hcW
  have t := crra_tangent hρ hρ1 hW hc
  have : W ^ (-ρ) * (c - W) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg hW.le _) (by linarith)
  linarith

/-- The transversality property of the CRRA value function, O&R Supplement A (proved, not
assumed): for every admissible plan with convergent utility series,
`β^t E V(W_t) → 0`, where `V(W) = μ^{−ρ}W^{1−ρ}/(1−ρ)`, under `βE(1 + r°(x*))^{1−ρ} < 1`.
From below, `V(W_t) ≥ μ^{−ρ}u(C_t)` and the terms of a convergent series vanish; from above,
`V ≤ 0` when `ρ > 1`, and `β^{t+1}E V(W_{t+1}) ≤ βE(1+r°)^{1−ρ} · β^t E V(W_t)` when `ρ < 1`. -/
theorem transversality_crra (Ω : StateSpace S) {β ρ : ℝ} (hβ : 0 < β) (hρ : 0 < ρ)
    (hρ1 : ρ ≠ 1) (r : Fin N → S → ℝ) (k : Fin N) {xs : Fin N → ℝ} (hxs : PortFeasible r xs)
    (hfoc : PortfolioCondition Ω ρ r k xs) (hB : growthFactor Ω β ρ r xs < 1) (W₀ : ℝ)
    {c : (n : ℕ) → (Fin n → S) → ℝ} {x : (n : ℕ) → (Fin n → S) → Fin N → ℝ}
    (hadm : Admissible r W₀ c x) (hU : Summable (utilSeries (iidTree Ω) β (crraUtil ρ) c)) :
    Tendsto (fun n => β ^ n * ∑ h, (iidTree Ω).histProb h
      * crraValue (crraShare Ω β ρ r xs) ρ (wealth r W₀ c x n h)) atTop (𝓝 0) := by
  obtain ⟨hμ0, -, -⟩ := crraShare_mem Ω hβ hρ r hxs hB
  set μ := crraShare Ω β ρ r xs
  have hμr : 0 ≤ μ ^ (-ρ) := Real.rpow_nonneg hμ0.le _
  set T := fun n => β ^ n * ∑ h, (iidTree Ω).histProb h * crraValue μ ρ (wealth r W₀ c x n h)
    with hT
  have hlow : ∀ n, μ ^ (-ρ) * utilSeries (iidTree Ω) β (crraUtil ρ) c n ≤ T n := by
    intro n
    rw [hT, utilSeries, ← mul_assoc, mul_comm (μ ^ (-ρ)), mul_assoc, Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun h _ => ?_) (pow_nonneg hβ.le n)
    have hm := crraUtil_mono hρ hρ1 (hadm.1 n h) (hadm.2.1 n h)
    have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hm hμr)
      ((iidTree Ω).histProb_nonneg h)
    unfold crraValue
    linarith
  have hlowT : Tendsto (fun n => μ ^ (-ρ) * utilSeries (iidTree Ω) β (crraUtil ρ) c n) atTop
      (𝓝 0) := by
    simpa using hU.tendsto_atTop_zero.const_mul (μ ^ (-ρ))
  rcases lt_or_gt_of_ne hρ1 with hlt | hgt
  · -- ρ < 1: geometric decay at rate βE(1+r°)^{1−ρ}
    set B := growthFactor Ω β ρ r xs
    have hB0 := growthFactor_pos Ω hβ ρ r hxs
    have hrec : ∀ n, T (n + 1) ≤ B * T n := by
      intro n
      simp only [hT]
      rw [sum_succ_iid]
      simp only [wealth_snoc]
      simp only [Finset.mul_sum]
      refine Finset.sum_le_sum fun h _ => ?_
      obtain ⟨hlt', hxn⟩ := admissible_step Ω r W₀ hadm n h
      have hD : 0 < wealth r W₀ c x n h - c n h := by linarith
      have e := expect_next_crra Ω β ρ (μ ^ (-ρ)) r hxn hD
      have hp : growthFactor Ω β ρ r (x n h) * crraUtil ρ (wealth r W₀ c x n h - c n h)
          ≤ B * crraUtil ρ (wealth r W₀ c x n h - c n h) := by
        rw [growthFactor_mul_crraUtil Ω β hρ1, growthFactor_mul_crraUtil Ω β hρ1]
        exact mul_le_mul_of_nonneg_left
          (portfolio_condition_sufficient Ω hρ hρ1 r k hxs hfoc hxn)
          (mul_nonneg hβ.le (Real.rpow_nonneg hD.le _))
      have hm := crraUtil_mono hρ hρ1 hD (by linarith [hadm.1 n h] :
        wealth r W₀ c x n h - c n h ≤ wealth r W₀ c x n h)
      have hchain : β * Ω.expect (fun s => crraValue μ ρ ((1 + portRet r (x n h) s)
          * (wealth r W₀ c x n h - c n h))) ≤ B * crraValue μ ρ (wealth r W₀ c x n h) := by
        have e' : β * Ω.expect (fun s => crraValue μ ρ ((1 + portRet r (x n h) s)
            * (wealth r W₀ c x n h - c n h))) = μ ^ (-ρ) * growthFactor Ω β ρ r (x n h)
              * crraUtil ρ (wealth r W₀ c x n h - c n h) := e
        rw [e']
        unfold crraValue
        nlinarith [mul_le_mul_of_nonneg_left hp hμr, mul_le_mul_of_nonneg_left hm
          (mul_nonneg hμr hB0.le)]
      have h3 := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hchain ((iidTree Ω).histProb_nonneg h)) (pow_nonneg hβ.le n)
      calc β ^ (n + 1) * ((iidTree Ω).histProb h * Ω.expect (fun s => crraValue μ ρ
            ((1 + portRet r (x n h) s) * (wealth r W₀ c x n h - c n h))))
          = β ^ n * ((iidTree Ω).histProb h * (β * Ω.expect (fun s => crraValue μ ρ
            ((1 + portRet r (x n h) s) * (wealth r W₀ c x n h - c n h))))) := by ring
        _ ≤ β ^ n * ((iidTree Ω).histProb h * (B * crraValue μ ρ (wealth r W₀ c x n h))) := h3
        _ = B * (β ^ n * ((iidTree Ω).histProb h * crraValue μ ρ (wealth r W₀ c x n h))) := by
          ring
    have hgeo : ∀ n, T n ≤ B ^ n * T 0 := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        calc T (n + 1) ≤ B * T n := hrec n
          _ ≤ B * (B ^ n * T 0) := mul_le_mul_of_nonneg_left ih hB0.le
          _ = B ^ (n + 1) * T 0 := by ring
    have hup : Tendsto (fun n => B ^ n * T 0) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hB0.le hB).mul_const (T 0)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlowT hup hlow hgeo
  · -- ρ > 1: the value function is negative
    have hup : ∀ n, T n ≤ 0 := by
      intro n
      refine mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hβ.le n)
        (Finset.sum_nonpos fun h _ => mul_nonpos_of_nonneg_of_nonpos
          ((iidTree Ω).histProb_nonneg h) ?_)
      exact mul_nonpos_of_nonneg_of_nonpos hμr (div_nonpos_of_nonneg_of_nonpos
        (Real.rpow_nonneg (lt_of_lt_of_le (hadm.1 n h) (hadm.2.1 n h)).le _) (by linarith))
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlowT tendsto_const_nhds hlow hup

/-- The upper half of the verification theorem, O&R Supplement A, pp. 742–744: under the
hypotheses of `bellman_crra` (`ρ > 0`, `ρ ≠ 1`, `β > 0`, `x*` feasible with the portfolio
condition (2), `βE(1 + r°(x*))^{1−ρ} < 1`) and `W₀ > 0`, every admissible plan whose utility
series converges achieves lifetime expected utility at most `V(W₀) = μ^{−ρ}W₀^{1−ρ}/(1−ρ)`. -/
theorem verification_upper_crra (Ω : StateSpace S) {β ρ : ℝ} (hβ : 0 < β) (hρ : 0 < ρ)
    (hρ1 : ρ ≠ 1) (r : Fin N → S → ℝ) (k : Fin N) {xs : Fin N → ℝ} (hxs : PortFeasible r xs)
    (hfoc : PortfolioCondition Ω ρ r k xs) (hB : growthFactor Ω β ρ r xs < 1) (W₀ : ℝ)
    {c : (n : ℕ) → (Fin n → S) → ℝ} {x : (n : ℕ) → (Fin n → S) → Fin N → ℝ}
    (hadm : Admissible r W₀ c x) (hU : Summable (utilSeries (iidTree Ω) β (crraUtil ρ) c)) :
    expectedUtility (iidTree Ω) β (crraUtil ρ) c ≤ crraValue (crraShare Ω β ρ r xs) ρ W₀ := by
  have hstep : ∀ n h, crraUtil ρ (c n h) + β * Ω.expect (fun s =>
      crraValue (crraShare Ω β ρ r xs) ρ ((1 + portRet r (x n h) s)
        * (wealth r W₀ c x n h - c n h))) ≤ crraValue (crraShare Ω β ρ r xs) ρ
          (wealth r W₀ c x n h) := by
    intro n h
    obtain ⟨hlt, hxn⟩ := admissible_step Ω r W₀ hadm n h
    exact (bellman_crra Ω hβ hρ hρ1 r k hxs hfoc hB
      (lt_of_lt_of_le (hadm.1 n h) (hadm.2.1 n h))).1 _ _ (hadm.1 n h) hlt hxn
  have htel := telescope_le Ω hβ.le (crraUtil ρ) (crraValue (crraShare Ω β ρ r xs) ρ) r W₀ c x
    hstep
  have hT := transversality_crra Ω hβ hρ hρ1 r k hxs hfoc hB W₀ hadm hU
  have h2 := (tendsto_const_nhds (x := crraValue (crraShare Ω β ρ r xs) ρ W₀)).sub hT
  rw [sub_zero] at h2
  exact le_of_tendsto_of_tendsto' hU.hasSum.tendsto_sum_nat h2 fun n => by linarith [htel n]

/-- Wealth under the optimal policy (O&R Supplement A, p. 744): `W*₁ = W₀` and
`W*(h, s) = (1 + r°(x*)(s))(1 − μ)W*(h)`. -/
noncomputable def optWealth (r : Fin N → S → ℝ) (xs : Fin N → ℝ) (μ W₀ : ℝ) :
    (n : ℕ) → (Fin n → S) → ℝ
  | 0, _ => W₀
  | n + 1, g => (1 + portRet r xs (g (Fin.last n))) * ((1 - μ) * optWealth r xs μ W₀ n (Fin.init g))

omit [Fintype S] in
/-- Optimal wealth after the event `s`, `W*(h, s) = (1 + r°(x*)(s))(1 − μ)W*(h)`
(O&R Supplement A, p. 744). -/
theorem optWealth_snoc (r : Fin N → S → ℝ) (xs : Fin N → ℝ) (μ W₀ : ℝ) {n : ℕ}
    (h : Fin n → S) (s : S) :
    optWealth r xs μ W₀ (n + 1) (Fin.snoc h s)
      = (1 + portRet r xs s) * ((1 - μ) * optWealth r xs μ W₀ n h) := by
  simp only [optWealth, Fin.init_snoc, Fin.snoc_last]

omit [Fintype S] in
/-- Optimal wealth stays positive (O&R Supplement A, p. 744; `μ < 1`, `1 + r°(x*) > 0`). -/
theorem optWealth_pos (r : Fin N → S → ℝ) {xs : Fin N → ℝ} (hxs : ∀ s, 0 < 1 + portRet r xs s)
    {μ W₀ : ℝ} (hμ1 : μ < 1) (hW₀ : 0 < W₀) : ∀ n h, 0 < optWealth r xs μ W₀ n h := by
  intro n
  induction n with
  | zero => intro h; exact hW₀
  | succ n ih =>
    intro g
    simp only [optWealth]
    exact mul_pos (hxs _) (mul_pos (by linarith) (ih _))

omit [Fintype S] in
/-- The policy `C = μW` with the portfolio `x*` generates the optimal wealth path: the wealth
of the plan `c = μW*`, `x = x*` is `W*` (O&R Supplement A, p. 744). -/
theorem wealth_optPlan (r : Fin N → S → ℝ) (xs : Fin N → ℝ) (μ W₀ : ℝ) :
    wealth r W₀ (fun n h => μ * optWealth r xs μ W₀ n h) (fun _ _ => xs)
      = optWealth r xs μ W₀ := by
  funext n
  induction n with
  | zero => rfl
  | succ n ih =>
    funext g
    simp only [wealth, optWealth, ih]
    ring

omit [Fintype S] in
/-- The optimal policy is admissible (O&R Supplement A, p. 744): `C = μW` with `0 < μ < 1` and
a feasible portfolio `x*` held at every history. -/
theorem optPlan_admissible (r : Fin N → S → ℝ) {xs : Fin N → ℝ} (hxs : PortFeasible r xs)
    {μ W₀ : ℝ} (hμ0 : 0 < μ) (hμ1 : μ < 1) (hW₀ : 0 < W₀) :
    Admissible r W₀ (fun n h => μ * optWealth r xs μ W₀ n h) (fun _ _ => xs) := by
  have hp := optWealth_pos r hxs.2 hμ1 hW₀
  refine ⟨fun n h => mul_pos hμ0 (hp n h), fun n h => ?_, fun _ _ => hxs.1⟩
  rw [wealth_optPlan]
  have := hp n h
  nlinarith

/-- The `(1−ρ)`-th moment of optimal wealth, O&R Supplement A, p. 744: with
`(1 − μ)^ρ = βE(1 + r°)^{1−ρ}`, `β^t E[(W*_t)^{1−ρ}] = (1 − μ)^t W₀^{1−ρ}`. -/
theorem optWealth_moment (Ω : StateSpace S) (β ρ : ℝ) (r : Fin N → S → ℝ) {xs : Fin N → ℝ}
    (hxs : PortFeasible r xs) {μ W₀ : ℝ} (hμ1 : μ < 1) (hW₀ : 0 < W₀)
    (hBμ : (1 - μ) ^ ρ = growthFactor Ω β ρ r xs) (n : ℕ) :
    β ^ n * ∑ h, (iidTree Ω).histProb h * optWealth r xs μ W₀ n h ^ (1 - ρ)
      = (1 - μ) ^ n * W₀ ^ (1 - ρ) := by
  have h1 : 0 < 1 - μ := by linarith
  have hp := optWealth_pos r hxs.2 hμ1 hW₀
  have hcomb : growthFactor Ω β ρ r xs * (1 - μ) ^ (1 - ρ) = 1 - μ := by
    rw [← hBμ, ← Real.rpow_add h1, show ρ + (1 - ρ) = 1 by ring, Real.rpow_one]
  induction n with
  | zero =>
    simp only [pow_zero, one_mul, Fintype.sum_unique, (iidTree Ω).histProb_zero]
    rfl
  | succ n ih =>
    rw [sum_succ_iid]
    simp only [optWealth_snoc]
    have e : ∀ h, Ω.expect (fun s => ((1 + portRet r xs s) * ((1 - μ) * optWealth r xs μ W₀ n h))
        ^ (1 - ρ)) = Ω.expect (fun s => (1 + portRet r xs s) ^ (1 - ρ)) * (1 - μ) ^ (1 - ρ)
          * optWealth r xs μ W₀ n h ^ (1 - ρ) := by
      intro h
      simp only [StateSpace.expect, Finset.sum_mul]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [Real.mul_rpow (hxs.2 s).le (mul_pos h1 (hp n h)).le,
        Real.mul_rpow h1.le (hp n h).le]
      ring
    simp only [e]
    have e2 : β ^ (n + 1) * ∑ h, (iidTree Ω).histProb h * (Ω.expect (fun s =>
        (1 + portRet r xs s) ^ (1 - ρ)) * (1 - μ) ^ (1 - ρ) * optWealth r xs μ W₀ n h ^ (1 - ρ))
        = growthFactor Ω β ρ r xs * (1 - μ) ^ (1 - ρ)
          * (β ^ n * ∑ h, (iidTree Ω).histProb h * optWealth r xs μ W₀ n h ^ (1 - ρ)) := by
      simp only [growthFactor, Finset.mul_sum]
      refine Finset.sum_congr rfl fun h _ => ?_
      ring
    rw [e2, ih, hcomb]
    ring

/-- The verification theorem for CRRA utility, O&R Supplement A, pp. 742–744, on the i.i.d.
tree over the infinite horizon. Assume `ρ > 0`, `ρ ≠ 1`, `β > 0`, a feasible portfolio `x*`
satisfying the portfolio condition (2), the parameter condition `βE(1 + r°(x*))^{1−ρ} < 1`,
and initial wealth `W₀ > 0`; let `μ = 1 − [βE(1 + r°(x*))^{1−ρ}]^{1/ρ}` and
`V(W) = μ^{−ρ}W^{1−ρ}/(1−ρ)`. Then the policy `C = μW`, `x = x*` is admissible, its utility
series converges and it attains `V(W₀)`; and every admissible plan (any consumption and
portfolio at each history, `0 < C ≤ W`, convergent utility series) achieves at most `V(W₀)`. -/
theorem verification_crra (Ω : StateSpace S) {β ρ : ℝ} (hβ : 0 < β) (hρ : 0 < ρ)
    (hρ1 : ρ ≠ 1) (r : Fin N → S → ℝ) (k : Fin N) {xs : Fin N → ℝ} (hxs : PortFeasible r xs)
    (hfoc : PortfolioCondition Ω ρ r k xs) (hB : growthFactor Ω β ρ r xs < 1) {W₀ : ℝ}
    (hW₀ : 0 < W₀) :
    let μ := crraShare Ω β ρ r xs
    let cStar := fun n (h : Fin n → S) => μ * optWealth r xs μ W₀ n h
    Admissible r W₀ cStar (fun _ _ => xs) ∧
      Summable (utilSeries (iidTree Ω) β (crraUtil ρ) cStar) ∧
      expectedUtility (iidTree Ω) β (crraUtil ρ) cStar = crraValue μ ρ W₀ ∧
      ∀ (c : (n : ℕ) → (Fin n → S) → ℝ) (x : (n : ℕ) → (Fin n → S) → Fin N → ℝ),
        Admissible r W₀ c x → Summable (utilSeries (iidTree Ω) β (crraUtil ρ) c) →
        expectedUtility (iidTree Ω) β (crraUtil ρ) c ≤ crraValue μ ρ W₀ := by
  intro μ cStar
  obtain ⟨hμ0, hμ1, hBμ⟩ := crraShare_mem Ω hβ hρ r hxs hB
  have h1 : 0 < 1 - μ := by linarith
  have hp := optWealth_pos r hxs.2 hμ1 hW₀
  have hμp : μ ^ (1 - ρ) = μ ^ (-ρ) * μ := by
    rw [show (1 : ℝ) - ρ = -ρ + 1 by ring, Real.rpow_add hμ0, Real.rpow_one]
  have hterm : ∀ n, utilSeries (iidTree Ω) β (crraUtil ρ) cStar n
      = μ ^ (1 - ρ) / (1 - ρ) * W₀ ^ (1 - ρ) * (1 - μ) ^ n := by
    intro n
    have hm := optWealth_moment Ω β ρ r hxs hμ1 hW₀ hBμ n
    have e : utilSeries (iidTree Ω) β (crraUtil ρ) cStar n = μ ^ (1 - ρ) / (1 - ρ)
        * (β ^ n * ∑ h, (iidTree Ω).histProb h * optWealth r xs μ W₀ n h ^ (1 - ρ)) := by
      simp only [utilSeries, cStar, crraUtil, Finset.mul_sum]
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [Real.mul_rpow hμ0.le (hp n h).le]
      ring
    rw [e, hm]
    ring
  have hsum : HasSum (utilSeries (iidTree Ω) β (crraUtil ρ) cStar) (crraValue μ ρ W₀) := by
    have hg := (hasSum_geometric_of_lt_one h1.le (by linarith : 1 - μ < 1)).mul_left
      (μ ^ (1 - ρ) / (1 - ρ) * W₀ ^ (1 - ρ))
    have hv : μ ^ (1 - ρ) / (1 - ρ) * W₀ ^ (1 - ρ) * (1 - (1 - μ))⁻¹ = crraValue μ ρ W₀ := by
      have hμne : μ ≠ 0 := hμ0.ne'
      rw [crraValue, crraUtil, hμp, sub_sub_cancel]
      field_simp
    rw [hv] at hg
    exact (funext hterm) ▸ hg
  exact ⟨optPlan_admissible r hxs hμ0 hμ1 hW₀, hsum.summable, hsum.tsum_eq,
    fun c x hadm hU => verification_upper_crra Ω hβ hρ hρ1 r k hxs hfoc hB W₀ hadm hU⟩

/-! ## Verification with log utility -/

/-- The expected log of wealth grows by at most `E log(1 + r°(x*))` per period along an
admissible plan (O&R Supplement A, p. 743): `Σ_h π(h) log W_t(h) ≤ log W₀ + t E log(1 + r°(x*))`
when `x*` satisfies the log portfolio condition. -/
theorem expect_log_wealth_le (Ω : StateSpace S) (r : Fin N → S → ℝ) (k : Fin N)
    {xs : Fin N → ℝ} (hxs : PortFeasible r xs) (hfoc : LogPortfolioCondition Ω r k xs)
    (W₀ : ℝ) {c : (n : ℕ) → (Fin n → S) → ℝ} {x : (n : ℕ) → (Fin n → S) → Fin N → ℝ}
    (hadm : Admissible r W₀ c x) (n : ℕ) :
    ∑ h, (iidTree Ω).histProb h * Real.log (wealth r W₀ c x n h)
      ≤ Real.log W₀ + n * logPortObj Ω r xs := by
  induction n with
  | zero =>
    simp only [Fintype.sum_unique, (iidTree Ω).histProb_zero, one_mul, CharP.cast_eq_zero,
      zero_mul, add_zero]
    rfl
  | succ n ih =>
    rw [sum_succ_iid]
    simp only [wealth_snoc]
    have hnode : ∀ h, (iidTree Ω).histProb h * Ω.expect (fun s => Real.log
        ((1 + portRet r (x n h) s) * (wealth r W₀ c x n h - c n h)))
        ≤ (iidTree Ω).histProb h * (logPortObj Ω r xs + Real.log (wealth r W₀ c x n h)) := by
      intro h
      obtain ⟨hlt, hxn⟩ := admissible_step Ω r W₀ hadm n h
      have hD : 0 < wealth r W₀ c x n h - c n h := by linarith
      have e : Ω.expect (fun s => Real.log ((1 + portRet r (x n h) s)
          * (wealth r W₀ c x n h - c n h)))
          = logPortObj Ω r (x n h) + Real.log (wealth r W₀ c x n h - c n h) := by
        simp only [StateSpace.expect, logPortObj]
        simp only [Real.log_mul (hxn.2 _).ne' hD.ne', mul_add, Finset.sum_add_distrib,
          ← Finset.sum_mul, Ω.prob_sum, one_mul]
      rw [e]
      refine mul_le_mul_of_nonneg_left ?_ ((iidTree Ω).histProb_nonneg h)
      have h1 := log_portfolio_condition_sufficient Ω r k hxs hfoc hxn
      have h2 := Real.log_le_log hD (by linarith [hadm.1 n h] :
        wealth r W₀ c x n h - c n h ≤ wealth r W₀ c x n h)
      linarith
    have hs := Finset.sum_le_sum fun h (_ : h ∈ univ) => hnode h
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul,
      (iidTree Ω).histProb_sum_eq_one, one_mul] at hs
    push_cast
    linarith

/-- The transversality property of the log value function, O&R Supplement A, p. 743 (proved,
not assumed): for `0 < β < 1` and every admissible plan with convergent utility series,
`β^t E V(W_t) → 0`, where `V(W) = log W/(1 − β) + K`. From below `V(W_t) ≥ log C_t/(1 − β) + K`;
from above `E log W_t ≤ log W₀ + tE log(1 + r°(x*))` and `tβ^t → 0`. -/
theorem transversality_log (Ω : StateSpace S) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (r : Fin N → S → ℝ) (k : Fin N) {xs : Fin N → ℝ} (hxs : PortFeasible r xs)
    (hfoc : LogPortfolioCondition Ω r k xs) (W₀ : ℝ) {c : (n : ℕ) → (Fin n → S) → ℝ}
    {x : (n : ℕ) → (Fin n → S) → Fin N → ℝ} (hadm : Admissible r W₀ c x)
    (hU : Summable (utilSeries (iidTree Ω) β Real.log c)) :
    Tendsto (fun n => β ^ n * ∑ h, (iidTree Ω).histProb h
      * logValue Ω β r xs (wealth r W₀ c x n h)) atTop (𝓝 0) := by
  have h1 : 0 < 1 - β := by linarith
  set K := logValueConst Ω β r xs
  set G := logPortObj Ω r xs
  have hT : ∀ n, β ^ n * ∑ h, (iidTree Ω).histProb h * logValue Ω β r xs (wealth r W₀ c x n h)
      = β ^ n * (∑ h, (iidTree Ω).histProb h * Real.log (wealth r W₀ c x n h)) / (1 - β)
        + β ^ n * K := by
    intro n
    have e : ∑ h, (iidTree Ω).histProb h * logValue Ω β r xs (wealth r W₀ c x n h)
        = (∑ h, (iidTree Ω).histProb h * Real.log (wealth r W₀ c x n h)) / (1 - β)
          + (∑ h : Fin n → S, (iidTree Ω).histProb h) * K := by
      rw [Finset.sum_div, Finset.sum_mul, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun h _ => by unfold logValue; ring
    rw [e, (iidTree Ω).histProb_sum_eq_one]
    ring
  have hlow : ∀ n, utilSeries (iidTree Ω) β Real.log c n / (1 - β) + β ^ n * K
      ≤ β ^ n * ∑ h, (iidTree Ω).histProb h * logValue Ω β r xs (wealth r W₀ c x n h) := by
    intro n
    rw [hT, utilSeries]
    have : ∑ h, (iidTree Ω).histProb h * Real.log (c n h)
        ≤ ∑ h, (iidTree Ω).histProb h * Real.log (wealth r W₀ c x n h) :=
      Finset.sum_le_sum fun h _ => mul_le_mul_of_nonneg_left
        (Real.log_le_log (hadm.1 n h) (hadm.2.1 n h)) ((iidTree Ω).histProb_nonneg h)
    have := mul_le_mul_of_nonneg_left this (pow_nonneg hβ0.le n)
    have := div_le_div_of_nonneg_right this h1.le
    linarith
  have hup : ∀ n, β ^ n * ∑ h, (iidTree Ω).histProb h * logValue Ω β r xs (wealth r W₀ c x n h)
      ≤ (Real.log W₀ / (1 - β) + K) * β ^ n + G / (1 - β) * (n * β ^ n) := by
    intro n
    rw [hT]
    have := mul_le_mul_of_nonneg_left (expect_log_wealth_le Ω r k hxs hfoc W₀ hadm n)
      (pow_nonneg hβ0.le n)
    have := div_le_div_of_nonneg_right this h1.le
    have e : β ^ n * (Real.log W₀ + n * G) / (1 - β) + β ^ n * K
        = (Real.log W₀ / (1 - β) + K) * β ^ n + G / (1 - β) * (n * β ^ n) := by ring
    linarith
  have hgeo := tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1
  have hlowT : Tendsto (fun n => utilSeries (iidTree Ω) β Real.log c n / (1 - β) + β ^ n * K)
      atTop (𝓝 0) := by
    simpa using (hU.tendsto_atTop_zero.div_const (1 - β)).add (hgeo.mul_const K)
  have hupT : Tendsto (fun n : ℕ => (Real.log W₀ / (1 - β) + K) * β ^ n
      + G / (1 - β) * (n * β ^ n)) atTop (𝓝 0) := by
    simpa using (hgeo.const_mul (Real.log W₀ / (1 - β) + K)).add
      ((tendsto_self_mul_const_pow_of_lt_one hβ0.le hβ1).const_mul (G / (1 - β)))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlowT hupT hlow hup

/-- The upper half of the log verification theorem, O&R Supplement A, p. 743: for `0 < β < 1`,
a feasible portfolio `x*` satisfying the log portfolio condition, every admissible plan whose
utility series converges achieves lifetime expected utility at most `V(W₀)`. -/
theorem verification_upper_log (Ω : StateSpace S) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (r : Fin N → S → ℝ) (k : Fin N) {xs : Fin N → ℝ} (hxs : PortFeasible r xs)
    (hfoc : LogPortfolioCondition Ω r k xs) (W₀ : ℝ) {c : (n : ℕ) → (Fin n → S) → ℝ}
    {x : (n : ℕ) → (Fin n → S) → Fin N → ℝ} (hadm : Admissible r W₀ c x)
    (hU : Summable (utilSeries (iidTree Ω) β Real.log c)) :
    expectedUtility (iidTree Ω) β Real.log c ≤ logValue Ω β r xs W₀ := by
  have hstep : ∀ n h, Real.log (c n h) + β * Ω.expect (fun s => logValue Ω β r xs
      ((1 + portRet r (x n h) s) * (wealth r W₀ c x n h - c n h)))
        ≤ logValue Ω β r xs (wealth r W₀ c x n h) := by
    intro n h
    obtain ⟨hlt, hxn⟩ := admissible_step Ω r W₀ hadm n h
    exact (bellman_log Ω hβ0 hβ1 r k hxs hfoc
      (lt_of_lt_of_le (hadm.1 n h) (hadm.2.1 n h))).1 _ _ (hadm.1 n h) hlt hxn
  have htel := telescope_le Ω hβ0.le Real.log (logValue Ω β r xs) r W₀ c x hstep
  have hT := transversality_log Ω hβ0 hβ1 r k hxs hfoc W₀ hadm hU
  have h2 := (tendsto_const_nhds (x := logValue Ω β r xs W₀)).sub hT
  rw [sub_zero] at h2
  exact le_of_tendsto_of_tendsto' hU.hasSum.tendsto_sum_nat h2 fun n => by linarith [htel n]

/-- Expected log of optimal wealth under log utility (O&R Supplement A, p. 744): with
`C = (1 − β)W`, `Σ_h π(h) log W*_t(h) = log W₀ + t(log β + E log(1 + r°(x*)))`. -/
theorem optWealth_expect_log (Ω : StateSpace S) {β : ℝ} (hβ0 : 0 < β) (r : Fin N → S → ℝ)
    {xs : Fin N → ℝ} (hxs : PortFeasible r xs) {W₀ : ℝ} (hW₀ : 0 < W₀) (n : ℕ) :
    ∑ h, (iidTree Ω).histProb h * Real.log (optWealth r xs (1 - β) W₀ n h)
      = Real.log W₀ + n * (Real.log β + logPortObj Ω r xs) := by
  have hp := optWealth_pos r hxs.2 (by linarith : 1 - β < 1) hW₀
  induction n with
  | zero =>
    simp only [Fintype.sum_unique, (iidTree Ω).histProb_zero, one_mul, CharP.cast_eq_zero,
      zero_mul, add_zero]
    rfl
  | succ n ih =>
    rw [sum_succ_iid]
    simp only [optWealth_snoc, sub_sub_cancel]
    have e : ∀ h, Ω.expect (fun s => Real.log ((1 + portRet r xs s)
        * (β * optWealth r xs (1 - β) W₀ n h)))
        = logPortObj Ω r xs + Real.log β + Real.log (optWealth r xs (1 - β) W₀ n h) := by
      intro h
      simp only [StateSpace.expect, logPortObj]
      simp only [Real.log_mul (hxs.2 _).ne' (mul_pos hβ0 (hp n h)).ne',
        Real.log_mul hβ0.ne' (hp n h).ne', mul_add, Finset.sum_add_distrib,
        ← Finset.sum_mul, Ω.prob_sum, one_mul]
      ring
    simp only [e, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul,
      (iidTree Ω).histProb_sum_eq_one, one_mul, ih]
    push_cast
    ring

/-- The verification theorem for log utility, O&R Supplement A, pp. 743–744, on the i.i.d. tree
over the infinite horizon: for `0 < β < 1`, a feasible portfolio `x*` satisfying the log
portfolio condition and `W₀ > 0`, with `V(W) = log W/(1 − β) + K`, the policy `C = (1 − β)W`,
`x = x*` (the book's `μ = 1 − β`) is admissible, its utility series converges and it attains
`V(W₀)`; every admissible plan with convergent utility series achieves at most `V(W₀)`. -/
theorem verification_log (Ω : StateSpace S) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (r : Fin N → S → ℝ) (k : Fin N) {xs : Fin N → ℝ} (hxs : PortFeasible r xs)
    (hfoc : LogPortfolioCondition Ω r k xs) {W₀ : ℝ} (hW₀ : 0 < W₀) :
    let cStar := fun n (h : Fin n → S) => (1 - β) * optWealth r xs (1 - β) W₀ n h
    Admissible r W₀ cStar (fun _ _ => xs) ∧
      Summable (utilSeries (iidTree Ω) β Real.log cStar) ∧
      expectedUtility (iidTree Ω) β Real.log cStar = logValue Ω β r xs W₀ ∧
      ∀ (c : (n : ℕ) → (Fin n → S) → ℝ) (x : (n : ℕ) → (Fin n → S) → Fin N → ℝ),
        Admissible r W₀ c x → Summable (utilSeries (iidTree Ω) β Real.log c) →
        expectedUtility (iidTree Ω) β Real.log c ≤ logValue Ω β r xs W₀ := by
  intro cStar
  have h1 : 0 < 1 - β := by linarith
  have hp := optWealth_pos r hxs.2 (by linarith : 1 - β < 1) hW₀
  set a := Real.log (1 - β) + Real.log W₀
  set b := Real.log β + logPortObj Ω r xs
  have hterm : ∀ n, utilSeries (iidTree Ω) β Real.log cStar n = a * β ^ n + b * (n * β ^ n) := by
    intro n
    have e : utilSeries (iidTree Ω) β Real.log cStar n = β ^ n * (Real.log (1 - β)
        + ∑ h, (iidTree Ω).histProb h * Real.log (optWealth r xs (1 - β) W₀ n h)) := by
      simp only [utilSeries, cStar, Real.log_mul h1.ne' (hp n _).ne', mul_add,
        Finset.sum_add_distrib, ← Finset.sum_mul, (iidTree Ω).histProb_sum_eq_one, one_mul]
    rw [e, optWealth_expect_log Ω hβ0 r hxs hW₀ n]
    ring
  have hnorm : ‖β‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos hβ0]; exact hβ1
  have hsum : HasSum (utilSeries (iidTree Ω) β Real.log cStar) (logValue Ω β r xs W₀) := by
    have hg := ((hasSum_geometric_of_lt_one hβ0.le hβ1).mul_left a).add
      ((hasSum_coe_mul_geometric_of_norm_lt_one hnorm).mul_left b)
    have hv : a * (1 - β)⁻¹ + b * (β / (1 - β) ^ 2) = logValue Ω β r xs W₀ := by
      simp only [a, b, logValue, logValueConst]
      field_simp
      ring
    rw [hv] at hg
    exact (funext hterm) ▸ hg
  exact ⟨optPlan_admissible r hxs h1 (by linarith) hW₀, hsum.summable, hsum.tsum_eq,
    fun c x hadm hU => verification_upper_log Ω hβ0 hβ1 r k hxs hfoc W₀ hadm hU⟩

/-! ## Existence of the optimal portfolio

The feasible portfolios form the relatively open set `{Σx = 1, 1 + r° > 0}`. Under a
no-arbitrage (non-redundancy) condition on the finite return matrix its closure is compact;
the concave portfolio objective then has a maximiser, which is interior, so it satisfies (2). -/

/-- No arbitrage and no redundant assets (a condition on the primitives of O&R Supplement A,
p. 742): no zero-cost reallocation `d ≠ 0` (`Σ_n d_n = 0`) has a nonnegative payoff
`Σ_n d_n r^n(s) ≥ 0` in every state. -/
def NoArbitrage (r : Fin N → S → ℝ) : Prop :=
  ∀ d : Fin N → ℝ, ∑ i, d i = 0 → (∀ s, 0 ≤ portRet r d s) → d = 0

/-- The closed feasible set `{Σ_n x_n = 1, 1 + r°(x) ≥ δ in every state}` (O&R Supplement A,
p. 742); `δ = 0` is the closure of the feasible portfolios. -/
def feasibleSet (r : Fin N → S → ℝ) (δ : ℝ) : Set (Fin N → ℝ) :=
  {x | ∑ i, x i = 1 ∧ ∀ s, δ ≤ 1 + portRet r x s}

/-- A probability space of states is nonempty (the probabilities sum to one). -/
theorem nonempty_of_stateSpace (Ω : StateSpace S) : Nonempty S := by
  by_contra hS
  rw [not_nonempty_iff] at hS
  have := Ω.prob_sum
  simp [Finset.univ_eq_empty] at this

omit [Fintype S] in
/-- The portfolio return is linear in the portfolio, `r°(a + c b) = r°(a) + c r°(b)`
(O&R Supplement A, p. 743). -/
theorem portRet_add_smul (r : Fin N → S → ℝ) (a b : Fin N → ℝ) (c : ℝ) (s : S) :
    portRet r (fun i => a i + c * b i) s = portRet r a s + c * portRet r b s := by
  simp only [portRet, add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]

omit [Fintype S] in
/-- Boundedness of the feasible set under no arbitrage (O&R Supplement A, p. 742): there is `R`
with `‖x − e_k‖ ≤ R` for every portfolio with `Σx = 1` and `1 + r°(x) ≥ 0` in every state. The
continuous function `d ↦ Σ_s max(0, −r°(d)(s))` is positive on the compact set of zero-cost
directions of norm one, so it has a positive minimum `ε`; along such a direction some state loses
at least `ε/#S` per unit, which bounds how far a feasible portfolio can go. -/
theorem feasible_bounded [Finite S] [Nonempty S] (r : Fin N → S → ℝ) (hNA : NoArbitrage r)
    (k : Fin N) :
    ∃ R, ∀ x ∈ feasibleSet r 0, ‖x - Pi.single k 1‖ ≤ R := by
  have := Fintype.ofFinite S
  set e : Fin N → ℝ := Pi.single k 1 with he
  have hesum : ∑ i, e i = 1 := by simp [he]
  have hret_e : ∀ s, portRet r e s = r k s := by
    intro s; simp [portRet, he, Pi.single_apply, ite_mul]
  set D : Set (Fin N → ℝ) := Metric.sphere 0 1 ∩ {d | ∑ i, d i = 0} with hD
  have hDc : IsCompact D :=
    (isCompact_sphere 0 1).inter_right (isClosed_eq (by fun_prop) continuous_const)
  set f : (Fin N → ℝ) → ℝ := fun d => ∑ s, max 0 (-portRet r d s) with hf
  have hfc : Continuous f := by
    simp only [hf, portRet]
    fun_prop
  have key : ∀ x ∈ feasibleSet r 0, ∀ d ∈ D, ∀ t : ℝ, 0 ≤ t → x = (fun i => e i + t * d i) →
      t * f d ≤ (1 + ∑ s, |r k s|) * Fintype.card S := by
    intro x hx d _ t ht hxd
    have hs : ∀ s, max 0 (-portRet r d s) * t ≤ 1 + ∑ s, |r k s| := by
      intro s
      have h0 := hx.2 s
      rw [hxd, portRet_add_smul, hret_e] at h0
      have hr : r k s ≤ ∑ s, |r k s| :=
        (le_abs_self _).trans (Finset.single_le_sum (f := fun s => |r k s|)
          (fun s _ => abs_nonneg _) (Finset.mem_univ s))
      rcases le_total 0 (-portRet r d s) with hp | hp
      · rw [max_eq_right hp]; nlinarith
      · rw [max_eq_left hp]; linarith [Finset.sum_nonneg fun s (_ : s ∈ univ) => abs_nonneg (r k s)]
    calc t * f d = ∑ s, max 0 (-portRet r d s) * t := by rw [hf, Finset.mul_sum]; simp [mul_comm]
      _ ≤ ∑ _s : S, (1 + ∑ s, |r k s|) := Finset.sum_le_sum fun s _ => hs s
      _ = (1 + ∑ s, |r k s|) * Fintype.card S := by simp; ring
  have hdecomp : ∀ x ∈ feasibleSet r 0, x - e ≠ 0 →
      ‖x - e‖⁻¹ • (x - e) ∈ D ∧ x = fun i => e i + ‖x - e‖ * (‖x - e‖⁻¹ • (x - e)) i := by
    intro x hx hne
    have hn : ‖x - e‖ ≠ 0 := norm_ne_zero_iff.mpr hne
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]
    · simp only [Set.mem_ofPred_eq, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, ← Finset.mul_sum,
        Finset.sum_sub_distrib, hx.1, hesum, sub_self, mul_zero]
    · funext i
      simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      field_simp
      ring
  by_cases hDn : D.Nonempty
  · obtain ⟨d₀, hd₀, hmin⟩ := hDc.exists_isMinOn hDn hfc.continuousOn
    have hε : 0 < f d₀ := by
      have hnn : ∀ s ∈ univ, 0 ≤ max 0 (-portRet r d₀ s) := fun s _ => le_max_left _ _
      rcases (Finset.sum_nonneg hnn).lt_or_eq with h | h
      · exact h
      · exfalso
        have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h.symm
        have hd0 : d₀ = 0 := hNA d₀ hd₀.2 fun s => by
          have := hz s (Finset.mem_univ s)
          have h2 := le_max_right 0 (-portRet r d₀ s)
          linarith
        have := hd₀.1
        rw [hd0, mem_sphere_zero_iff_norm, norm_zero] at this
        exact zero_ne_one this
    refine ⟨(1 + ∑ s, |r k s|) * Fintype.card S / f d₀, fun x hx => ?_⟩
    rw [le_div_iff₀ hε]
    by_cases hne : x - e = 0
    · rw [hne, norm_zero, zero_mul]
      positivity
    · obtain ⟨hdD, hxd⟩ := hdecomp x hx hne
      have := key x hx _ hdD ‖x - e‖ (norm_nonneg _) hxd
      have hm : f d₀ ≤ f (‖x - e‖⁻¹ • (x - e)) := hmin hdD
      nlinarith [norm_nonneg (x - e)]
  · refine ⟨0, fun x hx => ?_⟩
    by_contra hne
    have hne' : x - e ≠ 0 := by
      intro h; rw [h, norm_zero] at hne; exact hne le_rfl
    exact hDn ⟨_, (hdecomp x hx hne').1⟩

omit [Fintype S] in
/-- The closed feasible sets are compact under no arbitrage (O&R Supplement A, p. 742). -/
theorem isCompact_feasibleSet [Finite S] [Nonempty S] (r : Fin N → S → ℝ) (hNA : NoArbitrage r)
    (k : Fin N) {δ : ℝ} (hδ : 0 ≤ δ) : IsCompact (feasibleSet r δ) := by
  obtain ⟨R, hR⟩ := feasible_bounded r hNA k
  have hcl : IsClosed (feasibleSet r δ) := by
    have e : feasibleSet r δ = {x : Fin N → ℝ | ∑ i, x i = 1}
        ∩ ⋂ s, {x : Fin N → ℝ | δ ≤ 1 + portRet r x s} := by
      ext x; simp [feasibleSet]
    rw [e]
    refine (isClosed_eq (by fun_prop) continuous_const).inter (isClosed_iInter fun s => ?_)
    exact isClosed_le continuous_const (by simp only [portRet]; fun_prop)
  refine (isCompact_closedBall (Pi.single k 1) R).of_isClosed_subset hcl fun x hx => ?_
  rw [Metric.mem_closedBall, dist_eq_norm]
  exact hR x ⟨hx.1, fun s => hδ.trans (hx.2 s)⟩

omit [Fintype S] in
/-- A uniform bound on gross portfolio returns over the closed feasible set under no arbitrage
(O&R Supplement A, p. 742): `1 + r°(x)(s) ≤ Ȳ` for some `Ȳ ≥ 0`. -/
theorem feasible_return_bounded [Finite S] [Nonempty S] (r : Fin N → S → ℝ) (hNA : NoArbitrage r)
    (k : Fin N) : ∃ Yb, 0 ≤ Yb ∧ ∀ x ∈ feasibleSet r 0, ∀ s, 1 + portRet r x s ≤ Yb := by
  have := Fintype.ofFinite S
  obtain ⟨R, hR⟩ := feasible_bounded r hNA k
  set M := ∑ s, ∑ i, |r i s|
  have hM : 0 ≤ M := Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun i _ => abs_nonneg _
  refine ⟨1 + (|R| + 1) * M, by positivity, fun x hx s => ?_⟩
  have hxi : ∀ i, |x i| ≤ |R| + 1 := by
    intro i
    have h1 := (norm_le_pi_norm (x - Pi.single k 1) i).trans (hR x hx)
    have h2 : |(Pi.single k (1 : ℝ) : Fin N → ℝ) i| ≤ 1 := by
      by_cases hi : i = k
      · subst hi; simp
      · simp [hi]
    have h3 : |x i| ≤ |x i - (Pi.single k (1 : ℝ) : Fin N → ℝ) i|
        + |(Pi.single k (1 : ℝ) : Fin N → ℝ) i| := by
      have := abs_add_le (x i - (Pi.single k (1 : ℝ) : Fin N → ℝ) i)
        ((Pi.single k (1 : ℝ) : Fin N → ℝ) i)
      simpa using this
    have h4 : |x i - (Pi.single k (1 : ℝ) : Fin N → ℝ) i| ≤ R := by
      simpa [Real.norm_eq_abs] using h1
    linarith [le_abs_self R]
  have hsum : portRet r x s ≤ (|R| + 1) * ∑ i, |r i s| := by
    simp only [portRet, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    calc x i * r i s ≤ |x i * r i s| := le_abs_self _
      _ = |x i| * |r i s| := abs_mul _ _
      _ ≤ (|R| + 1) * |r i s| := mul_le_mul_of_nonneg_right (hxi i) (abs_nonneg _)
  have hs : ∑ i, |r i s| ≤ M :=
    Finset.single_le_sum (f := fun s => ∑ i, |r i s|)
      (fun s _ => Finset.sum_nonneg fun i _ => abs_nonneg _) (Finset.mem_univ s)
  nlinarith [abs_nonneg R]

omit [Fintype S] in
/-- From a portfolio maximising the objective over a closed feasible set that captures every
better portfolio, a maximiser over all feasible portfolios (O&R Supplement A, p. 743). -/
theorem exists_max_of_capture (r : Fin N → S → ℝ) (Φ : (Fin N → ℝ) → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hK : IsCompact (feasibleSet r δ)) (hc : ContinuousOn Φ (feasibleSet r δ))
    {x₀ : Fin N → ℝ} (hx₀ : PortFeasible r x₀)
    (hcap : ∀ x, PortFeasible r x → (∃ s, 1 + portRet r x s < δ) → Φ x < Φ x₀) :
    ∃ xs, PortFeasible r xs ∧ ∀ x, PortFeasible r x → Φ x ≤ Φ xs := by
  have hx₀K : x₀ ∈ feasibleSet r δ := by
    refine ⟨hx₀.1, fun s => ?_⟩
    by_contra h
    exact lt_irrefl _ (hcap x₀ hx₀ ⟨s, lt_of_not_ge h⟩)
  obtain ⟨xs, hxsK, hmax⟩ := hK.exists_isMaxOn ⟨x₀, hx₀K⟩ hc
  refine ⟨xs, ⟨hxsK.1, fun s => lt_of_lt_of_le hδ (hxsK.2 s)⟩, fun x hx => ?_⟩
  by_cases hxK : ∀ s, δ ≤ 1 + portRet r x s
  · exact hmax ⟨hx.1, hxK⟩
  · push Not at hxK
    exact (hcap x hx hxK).le.trans (hmax hx₀K)

/-- Existence of the optimal portfolio for CRRA utility with `ρ > 1`, O&R Supplement A,
p. 743: with all state probabilities positive, no arbitrage and some feasible portfolio, the
objective tends to `−∞` as any gross return tends to zero, so a maximiser exists. -/
theorem exists_optimal_portfolio_gt_one (Ω : StateSpace S) {ρ : ℝ} (hρ : 1 < ρ)
    (r : Fin N → S → ℝ) (k : Fin N) (hπ : ∀ s, 0 < Ω.prob s) (hNA : NoArbitrage r)
    (hF : ∃ x₀, PortFeasible r x₀) :
    ∃ xs, PortFeasible r xs ∧ ∀ x, PortFeasible r x → portObj Ω ρ r x ≤ portObj Ω ρ r xs := by
  classical
  have := nonempty_of_stateSpace Ω
  obtain ⟨x₀, hx₀⟩ := hF
  obtain ⟨s₀, hs₀⟩ := Finite.exists_min Ω.prob
  have hρ0 : 0 < ρ := by linarith
  have hρ1 : ρ ≠ 1 := hρ.ne'
  have hp : 1 - ρ < 0 := by linarith
  set p := Ω.prob s₀
  have hpp : 0 < p := hπ s₀
  have hneg : ∀ y, 0 < y → crraUtil ρ y ≤ 0 := fun y hy =>
    div_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg hy.le _) hp.le
  set Φ₀ := portObj Ω ρ r x₀
  have hΦ₀ : Φ₀ ≤ 0 := Finset.sum_nonpos fun s _ =>
    mul_nonpos_of_nonneg_of_nonpos (Ω.prob_nonneg s) (hneg _ (hx₀.2 s))
  set a := (ρ - 1) * (1 - Φ₀ / p) with ha_def
  have ha : 0 < a := mul_pos (by linarith) (by
    have : Φ₀ / p ≤ 0 := div_nonpos_of_nonpos_of_nonneg hΦ₀ hpp.le
    linarith)
  set δ := a ^ (1 / (1 - ρ)) with hδ_def
  have hδ : 0 < δ := Real.rpow_pos_of_pos ha _
  have huδ : crraUtil ρ δ = Φ₀ / p - 1 := by
    rw [crraUtil, hδ_def, one_div, Real.rpow_inv_rpow ha.le hp.ne, ha_def]
    field_simp
    ring
  refine exists_max_of_capture r (portObj Ω ρ r) hδ (isCompact_feasibleSet r hNA k hδ.le) ?_ hx₀
    ?_
  · refine continuousOn_finsetSum _ fun s _ => continuousOn_const.mul ?_
    refine ContinuousOn.div_const (ContinuousOn.rpow_const (by simp only [portRet]; fun_prop)
      fun x hx => Or.inl (lt_of_lt_of_le hδ (hx.2 s)).ne') _
  · rintro x hx ⟨s, hs⟩
    have h1 : portObj Ω ρ r x ≤ Ω.prob s * crraUtil ρ (1 + portRet r x s) := by
      unfold portObj StateSpace.expect
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ s)]
      have : ∑ s' ∈ univ.erase s, Ω.prob s' * crraUtil ρ (1 + portRet r x s') ≤ 0 :=
        Finset.sum_nonpos fun s' _ => mul_nonpos_of_nonneg_of_nonpos (Ω.prob_nonneg s')
          (hneg _ (hx.2 s'))
      linarith
    have h2 : Ω.prob s * crraUtil ρ (1 + portRet r x s) ≤ Ω.prob s * crraUtil ρ δ :=
      mul_le_mul_of_nonneg_left (crraUtil_mono hρ0 hρ1 (hx.2 s) hs.le) (Ω.prob_nonneg s)
    have h3 : Ω.prob s * crraUtil ρ δ ≤ p * crraUtil ρ δ :=
      mul_le_mul_of_nonpos_right (hs₀ s) (hneg δ hδ)
    have h4 : p * crraUtil ρ δ = Φ₀ - p := by rw [huδ]; field_simp
    linarith

/-- Existence of the optimal portfolio for log utility, O&R Supplement A, p. 743: with all state
probabilities positive, no arbitrage and some feasible portfolio, `E log(1 + r°)` has a
maximiser over the feasible portfolios (it tends to `−∞` at the boundary, and returns are
bounded above on the feasible set). -/
theorem exists_optimal_portfolio_log (Ω : StateSpace S) (r : Fin N → S → ℝ) (k : Fin N)
    (hπ : ∀ s, 0 < Ω.prob s) (hNA : NoArbitrage r) (hF : ∃ x₀, PortFeasible r x₀) :
    ∃ xs, PortFeasible r xs ∧ ∀ x, PortFeasible r x → logPortObj Ω r x ≤ logPortObj Ω r xs := by
  classical
  have := nonempty_of_stateSpace Ω
  obtain ⟨x₀, hx₀⟩ := hF
  obtain ⟨s₀, hs₀⟩ := Finite.exists_min Ω.prob
  obtain ⟨Yb, hYb0, hYb⟩ := feasible_return_bounded r hNA k
  set p := Ω.prob s₀
  have hpp : 0 < p := hπ s₀
  have hlogY : ∀ x ∈ feasibleSet r 0, ∀ s, 0 < 1 + portRet r x s →
      Real.log (1 + portRet r x s) ≤ Yb := fun x hx s hs =>
    ((Real.log_le_sub_one_of_pos hs).trans (by linarith)).trans (hYb x hx s)
  set Φ₀ := logPortObj Ω r x₀
  have hx₀c : x₀ ∈ feasibleSet r 0 := ⟨hx₀.1, fun s => (hx₀.2 s).le⟩
  have hΦ₀ : Φ₀ ≤ Yb := by
    calc Φ₀ ≤ ∑ s, Ω.prob s * Yb := Finset.sum_le_sum fun s _ =>
          mul_le_mul_of_nonneg_left (hlogY x₀ hx₀c s (hx₀.2 s)) (Ω.prob_nonneg s)
      _ = Yb := by rw [← Finset.sum_mul, Ω.prob_sum, one_mul]
  set δ := Real.exp ((Φ₀ - Yb - 1) / p)
  have hδ : 0 < δ := Real.exp_pos _
  have hlogδ : Real.log δ = (Φ₀ - Yb - 1) / p := Real.log_exp _
  have hlogδ0 : Real.log δ ≤ 0 := by
    rw [hlogδ]; exact div_nonpos_of_nonpos_of_nonneg (by linarith) hpp.le
  refine exists_max_of_capture r (logPortObj Ω r) hδ (isCompact_feasibleSet r hNA k hδ.le) ?_
    hx₀ ?_
  · refine continuousOn_finsetSum _ fun s _ => continuousOn_const.mul ?_
    exact ContinuousOn.log (by simp only [portRet]; fun_prop)
      fun x hx => (lt_of_lt_of_le hδ (hx.2 s)).ne'
  · rintro x hx ⟨s, hs⟩
    have hxc : x ∈ feasibleSet r 0 := ⟨hx.1, fun s => (hx.2 s).le⟩
    have h1 : logPortObj Ω r x ≤ Ω.prob s * Real.log (1 + portRet r x s) + Yb := by
      unfold logPortObj StateSpace.expect
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ s)]
      have : ∑ s' ∈ univ.erase s, Ω.prob s' * Real.log (1 + portRet r x s')
          ≤ ∑ s' ∈ univ.erase s, Ω.prob s' * Yb := Finset.sum_le_sum fun s' _ =>
        mul_le_mul_of_nonneg_left (hlogY x hxc s' (hx.2 s')) (Ω.prob_nonneg s')
      have h2 : ∑ s' ∈ univ.erase s, Ω.prob s' * Yb ≤ Yb := by
        rw [← Finset.sum_mul]
        have : ∑ s' ∈ univ.erase s, Ω.prob s' ≤ 1 := by
          rw [← Ω.prob_sum]
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
            fun s' _ _ => Ω.prob_nonneg s'
        nlinarith
      linarith
    have h2 : Real.log (1 + portRet r x s) ≤ Real.log δ := Real.log_le_log (hx.2 s) hs.le
    have h3 : Ω.prob s * Real.log (1 + portRet r x s) ≤ p * Real.log δ := by
      calc Ω.prob s * Real.log (1 + portRet r x s) ≤ Ω.prob s * Real.log δ :=
            mul_le_mul_of_nonneg_left h2 (Ω.prob_nonneg s)
        _ ≤ p * Real.log δ := mul_le_mul_of_nonpos_right (hs₀ s) hlogδ0
    have h4 : p * Real.log δ = Φ₀ - Yb - 1 := by rw [hlogδ]; field_simp
    linarith

/-- Existence of the optimal portfolio for CRRA utility with `0 < ρ < 1`, O&R Supplement A,
p. 743. The objective is continuous on the compact closure of the feasible set, so it has a
maximiser there; the maximiser is interior because marginal utility is infinite at a zero gross
return: moving a fraction `t` towards a feasible portfolio gains at least of order `t^{1−ρ}` in a
state where the gross return was zero and loses at most of order `t` elsewhere (concavity). -/
theorem exists_optimal_portfolio_lt_one (Ω : StateSpace S) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ : ρ < 1)
    (r : Fin N → S → ℝ) (k : Fin N) (hπ : ∀ s, 0 < Ω.prob s) (hNA : NoArbitrage r)
    (hF : ∃ x₀, PortFeasible r x₀) :
    ∃ xs, PortFeasible r xs ∧ ∀ x, PortFeasible r x → portObj Ω ρ r x ≤ portObj Ω ρ r xs := by
  have := nonempty_of_stateSpace Ω
  obtain ⟨x₀, hx₀⟩ := hF
  set p := 1 - ρ with hp_def
  have hp0 : 0 < p := by linarith
  have hp1 : p < 1 := by linarith
  have hx₀K : x₀ ∈ feasibleSet r 0 := ⟨hx₀.1, fun s => (hx₀.2 s).le⟩
  have hcont : Continuous (portObj Ω ρ r) := by
    unfold portObj StateSpace.expect crraUtil
    refine continuous_finsetSum _ fun s _ => continuous_const.mul ?_
    exact (Continuous.rpow_const (by simp only [portRet]; fun_prop)
      fun _ => Or.inr hp0.le).div_const _
  obtain ⟨xb, hxbK, hmax⟩ := (isCompact_feasibleSet r hNA k le_rfl).exists_isMaxOn ⟨x₀, hx₀K⟩
    hcont.continuousOn
  have hint : ∀ s, 0 < 1 + portRet r xb s := by
    by_contra hcon
    push Not at hcon
    obtain ⟨s₀, hs₀⟩ := hcon
    have hb0 : 1 + portRet r xb s₀ = 0 := le_antisymm hs₀ (hxbK.2 s₀)
    set b := fun s => 1 + portRet r xb s
    set a := fun s => 1 + portRet r x₀ s
    have hline : ∀ t : ℝ, ∀ s, 1 + portRet r (fun i => xb i + t * (x₀ i - xb i)) s
        = (1 - t) * b s + t * a s := by
      intro t s
      rw [portRet_add_smul]
      simp only [b, a, portRet, sub_mul, Finset.sum_sub_distrib]
      ring
    have hmem : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        (fun i => xb i + t * (x₀ i - xb i)) ∈ feasibleSet r 0 := by
      intro t ht0 ht1
      refine ⟨?_, fun s => ?_⟩
      · simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, hx₀.1,
          hxbK.1, sub_self, mul_zero, add_zero]
      · rw [hline]
        have := hxbK.2 s
        have := (hx₀.2 s).le
        nlinarith
    set c := Ω.prob s₀ * (a s₀ ^ p / p)
    have hc : 0 < c := mul_pos (hπ s₀) (div_pos (Real.rpow_pos_of_pos (hx₀.2 s₀) _) hp0)
    set M := portObj Ω ρ r xb - portObj Ω ρ r x₀
    have hM : 0 ≤ M := by
      have h : portObj Ω ρ r x₀ ≤ portObj Ω ρ r xb := hmax hx₀K
      simp only [M]; linarith
    set t := (c / (2 * (c + M))) ^ (1 / ρ) with ht_def
    have hq : 0 < c / (2 * (c + M)) := by positivity
    have hq1 : c / (2 * (c + M)) < 1 := by rw [div_lt_one (by positivity)]; linarith
    have ht0 : 0 < t := Real.rpow_pos_of_pos hq _
    have ht1 : t < 1 := Real.rpow_lt_one hq.le hq1 (one_div_pos.mpr hρ0)
    have htρ : t ^ ρ = c / (2 * (c + M)) := by
      rw [ht_def, one_div, Real.rpow_inv_rpow hq.le hρ0.ne']
    have htp : c * t ^ p = 2 * (c + M) * t := by
      rw [hp_def, show (1 : ℝ) - ρ = 1 + -ρ by ring, Real.rpow_add ht0, Real.rpow_one,
        Real.rpow_neg ht0.le, htρ]
      field_simp
    -- per-state concavity bounds
    have hconc : ∀ s, (1 - t) * (b s ^ p / p) + t * (a s ^ p / p)
        ≤ ((1 - t) * b s + t * a s) ^ p / p := by
      intro s
      have h := (Real.concaveOn_rpow hp0.le hp1.le).2 (Set.mem_Ici.mpr (hxbK.2 s))
        (Set.mem_Ici.mpr (hx₀.2 s).le) (by linarith : (0 : ℝ) ≤ 1 - t) ht0.le (by ring)
      simp only [smul_eq_mul] at h
      calc (1 - t) * (b s ^ p / p) + t * (a s ^ p / p) = ((1 - t) * b s ^ p + t * a s ^ p) / p
            := by ring
        _ ≤ ((1 - t) * b s + t * a s) ^ p / p := div_le_div_of_nonneg_right h hp0.le
    have hs0 : ((1 - t) * b s₀ + t * a s₀) ^ p / p
        = (1 - t) * (b s₀ ^ p / p) + t * (a s₀ ^ p / p) + (t ^ p - t) * (a s₀ ^ p / p) := by
      simp only [b] at hb0 ⊢
      rw [hb0, mul_zero, zero_add, Real.mul_rpow ht0.le (hx₀.2 s₀).le,
        Real.zero_rpow hp0.ne']
      ring
    have hsum : (1 - t) * portObj Ω ρ r xb + t * portObj Ω ρ r x₀ + (t ^ p - t) * c
        ≤ portObj Ω ρ r (fun i => xb i + t * (x₀ i - xb i)) := by
      have hterm : ∀ s ∈ univ, 0 ≤ Ω.prob s * (((1 - t) * b s + t * a s) ^ p / p
          - ((1 - t) * (b s ^ p / p) + t * (a s ^ p / p))) := fun s _ =>
        mul_nonneg (Ω.prob_nonneg s) (by linarith [hconc s])
      have hsingle := Finset.single_le_sum hterm (Finset.mem_univ s₀)
      rw [hs0] at hsingle
      have e1 : portObj Ω ρ r (fun i => xb i + t * (x₀ i - xb i))
          = ∑ s, Ω.prob s * (((1 - t) * b s + t * a s) ^ p / p) := by
        simp only [portObj, StateSpace.expect, crraUtil, hline, hp_def]
      have e2 : (1 - t) * portObj Ω ρ r xb + t * portObj Ω ρ r x₀
          = ∑ s, Ω.prob s * ((1 - t) * (b s ^ p / p) + t * (a s ^ p / p)) := by
        simp only [portObj, StateSpace.expect, crraUtil, hp_def, b, a, Finset.mul_sum,
          ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun s _ => by ring
      have e3 : ∑ s, Ω.prob s * (((1 - t) * b s + t * a s) ^ p / p
          - ((1 - t) * (b s ^ p / p) + t * (a s ^ p / p)))
          = ∑ s, Ω.prob s * (((1 - t) * b s + t * a s) ^ p / p)
            - ∑ s, Ω.prob s * ((1 - t) * (b s ^ p / p) + t * (a s ^ p / p)) := by
        rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun s _ => by ring
      rw [e1, e2]
      rw [e3] at hsingle
      have : Ω.prob s₀ * ((1 - t) * (b s₀ ^ p / p) + t * (a s₀ ^ p / p)
          + (t ^ p - t) * (a s₀ ^ p / p) - ((1 - t) * (b s₀ ^ p / p) + t * (a s₀ ^ p / p)))
          = (t ^ p - t) * c := by simp only [c]; ring
      linarith
    have hle : portObj Ω ρ r (fun i => xb i + t * (x₀ i - xb i)) ≤ portObj Ω ρ r xb :=
      hmax (hmem t ht0.le ht1.le)
    have : portObj Ω ρ r xb < portObj Ω ρ r (fun i => xb i + t * (x₀ i - xb i)) := by
      have e : (1 - t) * portObj Ω ρ r xb + t * portObj Ω ρ r x₀ + (t ^ p - t) * c
          = portObj Ω ρ r xb + t * (c + M) := by
        simp only [M]; linear_combination htp
      nlinarith
    linarith
  exact ⟨xb, ⟨hxbK.1, hint⟩, fun x hx => hmax ⟨hx.1, fun s => (hx.2 s).le⟩⟩

/-- Existence of an optimal portfolio satisfying the portfolio condition (2), CRRA utility
(`ρ > 0`, `ρ ≠ 1`), O&R Supplement A, p. 743: under positive state probabilities, no arbitrage
and the existence of some feasible portfolio, there is a feasible portfolio maximising the
portfolio objective, and it satisfies (2). -/
theorem exists_optimal_portfolio (Ω : StateSpace S) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≠ 1)
    (r : Fin N → S → ℝ) (k : Fin N) (hπ : ∀ s, 0 < Ω.prob s) (hNA : NoArbitrage r)
    (hF : ∃ x₀, PortFeasible r x₀) :
    ∃ xs, PortFeasible r xs ∧ (∀ x, PortFeasible r x → portObj Ω ρ r x ≤ portObj Ω ρ r xs)
      ∧ PortfolioCondition Ω ρ r k xs := by
  obtain ⟨xs, hxs, hmax⟩ : ∃ xs, PortFeasible r xs ∧
      ∀ x, PortFeasible r x → portObj Ω ρ r x ≤ portObj Ω ρ r xs := by
    rcases lt_or_gt_of_ne hρ1 with h | h
    · exact exists_optimal_portfolio_lt_one Ω hρ h r k hπ hNA hF
    · exact exists_optimal_portfolio_gt_one Ω h r k hπ hNA hF
  exact ⟨xs, hxs, hmax, portfolio_condition_necessary Ω hρ1 r k hxs hmax⟩

/-- Existence of an optimal log portfolio satisfying the log portfolio condition, O&R
Supplement A, p. 743 (positive state probabilities, no arbitrage, some feasible portfolio). -/
theorem exists_optimal_log_portfolio (Ω : StateSpace S) (r : Fin N → S → ℝ) (k : Fin N)
    (hπ : ∀ s, 0 < Ω.prob s) (hNA : NoArbitrage r) (hF : ∃ x₀, PortFeasible r x₀) :
    ∃ xs, PortFeasible r xs ∧ (∀ x, PortFeasible r x → logPortObj Ω r x ≤ logPortObj Ω r xs)
      ∧ LogPortfolioCondition Ω r k xs := by
  obtain ⟨xs, hxs, hmax⟩ := exists_optimal_portfolio_log Ω r k hπ hNA hF
  exact ⟨xs, hxs, hmax, log_portfolio_condition_necessary Ω r k hxs hmax⟩

/-- The verification theorem for CRRA utility from primitives, O&R Supplement A, pp. 742–744:
under positive state probabilities, no arbitrage, some feasible portfolio, and the growth
condition `βE(1 + r°)^{1−ρ} < 1` at optimal portfolios (all optimal portfolios give the same
value, hence the same growth factor), an optimal portfolio `x*` satisfying (2) exists, and with
`μ = 1 − [βE(1 + r°(x*))^{1−ρ}]^{1/ρ}` the policy `C = μW`, `x = x*` attains
`V(W₀) = μ^{−ρ}W₀^{1−ρ}/(1−ρ)`, which no admissible plan exceeds. -/
theorem verification_crra_of_noArbitrage (Ω : StateSpace S) {β ρ : ℝ} (hβ : 0 < β)
    (hρ : 0 < ρ) (hρ1 : ρ ≠ 1) (r : Fin N → S → ℝ) (k : Fin N) (hπ : ∀ s, 0 < Ω.prob s)
    (hNA : NoArbitrage r) (hF : ∃ x₀, PortFeasible r x₀)
    (hB : ∀ x, PortFeasible r x → (∀ x', PortFeasible r x' → portObj Ω ρ r x' ≤ portObj Ω ρ r x)
      → growthFactor Ω β ρ r x < 1) {W₀ : ℝ} (hW₀ : 0 < W₀) :
    ∃ xs, PortFeasible r xs ∧ PortfolioCondition Ω ρ r k xs ∧
      Admissible r W₀ (fun n h => crraShare Ω β ρ r xs * optWealth r xs (crraShare Ω β ρ r xs)
        W₀ n h) (fun _ _ => xs) ∧
      Summable (utilSeries (iidTree Ω) β (crraUtil ρ) fun n h => crraShare Ω β ρ r xs
        * optWealth r xs (crraShare Ω β ρ r xs) W₀ n h) ∧
      expectedUtility (iidTree Ω) β (crraUtil ρ) (fun n h => crraShare Ω β ρ r xs
        * optWealth r xs (crraShare Ω β ρ r xs) W₀ n h) = crraValue (crraShare Ω β ρ r xs) ρ W₀ ∧
      ∀ (c : (n : ℕ) → (Fin n → S) → ℝ) (x : (n : ℕ) → (Fin n → S) → Fin N → ℝ),
        Admissible r W₀ c x → Summable (utilSeries (iidTree Ω) β (crraUtil ρ) c) →
        expectedUtility (iidTree Ω) β (crraUtil ρ) c ≤ crraValue (crraShare Ω β ρ r xs) ρ W₀ := by
  obtain ⟨xs, hxs, hmax, hfoc⟩ := exists_optimal_portfolio Ω hρ hρ1 r k hπ hNA hF
  exact ⟨xs, hxs, hfoc, verification_crra Ω hβ hρ hρ1 r k hxs hfoc (hB xs hxs hmax) hW₀⟩

/-- The verification theorem for log utility from primitives, O&R Supplement A, pp. 743–744:
for `0 < β < 1`, positive state probabilities, no arbitrage and some feasible portfolio, an
optimal portfolio `x*` satisfying the log portfolio condition exists, and the policy
`C = (1 − β)W`, `x = x*` attains `V(W₀) = log W₀/(1 − β) + K`, which no admissible plan
exceeds. -/
theorem verification_log_of_noArbitrage (Ω : StateSpace S) {β : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (r : Fin N → S → ℝ) (k : Fin N) (hπ : ∀ s, 0 < Ω.prob s)
    (hNA : NoArbitrage r) (hF : ∃ x₀, PortFeasible r x₀) {W₀ : ℝ} (hW₀ : 0 < W₀) :
    ∃ xs, PortFeasible r xs ∧ LogPortfolioCondition Ω r k xs ∧
      Admissible r W₀ (fun n h => (1 - β) * optWealth r xs (1 - β) W₀ n h) (fun _ _ => xs) ∧
      Summable (utilSeries (iidTree Ω) β Real.log fun n h =>
        (1 - β) * optWealth r xs (1 - β) W₀ n h) ∧
      expectedUtility (iidTree Ω) β Real.log (fun n h => (1 - β) * optWealth r xs (1 - β) W₀ n h)
        = logValue Ω β r xs W₀ ∧
      ∀ (c : (n : ℕ) → (Fin n → S) → ℝ) (x : (n : ℕ) → (Fin n → S) → Fin N → ℝ),
        Admissible r W₀ c x → Summable (utilSeries (iidTree Ω) β Real.log c) →
        expectedUtility (iidTree Ω) β Real.log c ≤ logValue Ω β r xs W₀ := by
  obtain ⟨xs, hxs, -, hfoc⟩ := exists_optimal_log_portfolio Ω r k hπ hNA hF
  exact ⟨xs, hxs, hfoc, verification_log Ω hβ0 hβ1 r k hxs hfoc hW₀⟩

/-! ## Returns whose distribution varies with the history

O&R Supplement A, p. 744: "for CRRA preferences … `μ` is a function of time … `C = μ_t W`, where
`μ_t` varies only because of variation in the conditional distribution of expected future
returns", with the recursion `μ_t = (1 + [βE_t{(1 + r°_{t+1})^{1−ρ} μ_{t+1}^{−ρ}}]^{1/ρ})^{−1}`.
Here returns `R n h` from a date-`t` history `h` to the next event, and the conditional
probabilities `q n h` of a general event tree, may depend on the history. -/

/-- The weighted portfolio objective `Σ_s w(s)(1 + r°(x)(s))^{1−ρ}/(1−ρ)` (O&R Supplement A,
p. 744: with weights `w(s) = β q(s) μ_{t+1}(s)^{−ρ}` it is the continuation value of a unit of
saving). -/
noncomputable def weightedObj (ρ : ℝ) (r : Fin N → S → ℝ) (w : S → ℝ) (x : Fin N → ℝ) : ℝ :=
  (∑ s, w s * (1 + portRet r x s) ^ (1 - ρ)) / (1 - ρ)

/-- Existence of an optimal portfolio for positive state weights, O&R Supplement A, p. 744: the
weighted problem is the portfolio problem of `exists_optimal_portfolio` under the normalised
weights as probabilities. The maximiser also satisfies the weighted portfolio condition (2),
`Σ_s w(s)(r^n(s) − r^k(s))(1 + r°(s))^{−ρ} = 0`. -/
theorem exists_optimal_weighted [Nonempty S] {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≠ 1)
    (r : Fin N → S → ℝ) (k : Fin N) (w : S → ℝ) (hw : ∀ s, 0 < w s) (hNA : NoArbitrage r)
    (hF : ∃ x₀, PortFeasible r x₀) :
    ∃ xs, PortFeasible r xs ∧ (∀ x, PortFeasible r x → weightedObj ρ r w x ≤ weightedObj ρ r w xs)
      ∧ ∀ n, ∑ s, w s * ((r n s - r k s) * (1 + portRet r xs s) ^ (-ρ)) = 0 := by
  obtain ⟨s₀⟩ := ‹Nonempty S›
  set Z := ∑ s, w s with hZ
  have hZ0 : 0 < Z := Finset.sum_pos (fun s _ => hw s) ⟨s₀, Finset.mem_univ _⟩
  let Ω' : StateSpace S := ⟨fun s => w s / Z, fun s => (div_pos (hw s) hZ0).le, by
    rw [← Finset.sum_div, ← hZ, div_self hZ0.ne']⟩
  have e : ∀ x, portObj Ω' ρ r x = weightedObj ρ r w x / Z := by
    intro x
    simp only [portObj, StateSpace.expect, crraUtil, weightedObj, Ω', Finset.sum_div]
    exact Finset.sum_congr rfl fun s _ => by ring
  obtain ⟨xs, hxs, hmax, hfoc⟩ := exists_optimal_portfolio Ω' hρ hρ1 r k
    (fun s => div_pos (hw s) hZ0) hNA hF
  refine ⟨xs, hxs, fun x hx => ?_, fun n => ?_⟩
  · have := hmax x hx
    rw [e, e] at this
    exact (div_le_div_iff_of_pos_right hZ0).mp this
  · have := hfoc n
    simp only [StateSpace.expect, Ω'] at this
    have e2 : ∑ s, w s / Z * ((r n s - r k s) * (1 + portRet r xs s) ^ (-ρ))
        = (∑ s, w s * ((r n s - r k s) * (1 + portRet r xs s) ^ (-ρ))) / Z := by
      rw [Finset.sum_div]; exact Finset.sum_congr rfl fun s _ => by ring
    rw [e2, div_eq_zero_iff] at this
    exact this.resolve_right hZ0.ne'

/-- A chosen optimal portfolio for the weights `w` (O&R Supplement A, p. 744), by Hilbert choice;
`optPortW_spec` gives its optimality whenever an optimal portfolio exists. -/
noncomputable def optPortW (ρ : ℝ) (r : Fin N → S → ℝ) (w : S → ℝ) : Fin N → ℝ :=
  Classical.epsilon fun xs => PortFeasible r xs ∧
    ∀ x, PortFeasible r x → weightedObj ρ r w x ≤ weightedObj ρ r w xs

/-- The chosen portfolio is feasible and optimal for the weights `w`, under the hypotheses of
`exists_optimal_weighted` (O&R Supplement A, p. 744). -/
theorem optPortW_spec [Nonempty S] {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≠ 1) (r : Fin N → S → ℝ)
    (k : Fin N) (w : S → ℝ) (hw : ∀ s, 0 < w s) (hNA : NoArbitrage r)
    (hF : ∃ x₀, PortFeasible r x₀) :
    PortFeasible r (optPortW ρ r w) ∧ ∀ x, PortFeasible r x →
      weightedObj ρ r w x ≤ weightedObj ρ r w (optPortW ρ r w) := by
  obtain ⟨xs, hxs, hmax, -⟩ := exists_optimal_weighted hρ hρ1 r k w hw hNA hF
  exact Classical.epsilon_spec (p := fun xs => PortFeasible r xs ∧
    ∀ x, PortFeasible r x → weightedObj ρ r w x ≤ weightedObj ρ r w xs) ⟨xs, hxs, hmax⟩

/-- The optimal weighted growth `J(w) = Σ_s w(s)(1 + r°*(s))^{1−ρ}` at the chosen optimal
portfolio (O&R Supplement A, p. 744: `βE_t{(1 + r°_{t+1})^{1−ρ} μ_{t+1}^{−ρ}}`). -/
noncomputable def optJ (ρ : ℝ) (r : Fin N → S → ℝ) (w : S → ℝ) : ℝ :=
  ∑ s, w s * (1 + portRet r (optPortW ρ r w) s) ^ (1 - ρ)

/-- The weighted growth at any portfolio versus the optimum (O&R Supplement A, p. 744): for
`ρ < 1`, `Σ w(1 + r°)^{1−ρ} ≤ J(w)` for every feasible portfolio; for `ρ > 1`, `J(w) ≤` it. -/
theorem optJ_compare [Nonempty S] {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≠ 1) (r : Fin N → S → ℝ)
    (k : Fin N) (w : S → ℝ) (hw : ∀ s, 0 < w s) (hNA : NoArbitrage r)
    (hF : ∃ x₀, PortFeasible r x₀) {x : Fin N → ℝ} (hx : PortFeasible r x) :
    (ρ < 1 → ∑ s, w s * (1 + portRet r x s) ^ (1 - ρ) ≤ optJ ρ r w) ∧
    (1 < ρ → optJ ρ r w ≤ ∑ s, w s * (1 + portRet r x s) ^ (1 - ρ)) := by
  have h := (optPortW_spec hρ hρ1 r k w hw hNA hF).2 x hx
  unfold weightedObj at h
  refine ⟨fun hlt => ?_, fun hgt => ?_⟩
  · exact (div_le_div_iff_of_pos_right (by linarith)).mp h
  · exact (div_le_div_right_of_neg (by linarith)).mp h

/-- The optimal weighted growth is positive for positive weights (O&R Supplement A,
p. 744). -/
theorem optJ_pos [Nonempty S] {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≠ 1) (r : Fin N → S → ℝ)
    (k : Fin N) (w : S → ℝ) (hw : ∀ s, 0 < w s) (hNA : NoArbitrage r)
    (hF : ∃ x₀, PortFeasible r x₀) : 0 < optJ ρ r w := by
  obtain ⟨s₀⟩ := ‹Nonempty S›
  have hf := (optPortW_spec hρ hρ1 r k w hw hNA hF).1
  exact Finset.sum_pos (fun s _ => mul_pos (hw s) (Real.rpow_pos_of_pos (hf.2 s) _))
    ⟨s₀, Finset.mem_univ _⟩

/-- The one-period problem at the date-`t` history `h` of a general event tree: the conditional
probabilities `q(s|h)` as a state space (O&R Appendix 5C, p. 341; Supplement A, p. 744). -/
def nodeSpace (tr : EventTree.Tree S) (n : ℕ) (h : Fin n → S) : StateSpace S :=
  ⟨tr.q n h, tr.q_nonneg n h, tr.q_sum n h⟩

/-- The book's `βE_t{(1 + r°_{t+1})^{1−ρ} μ_{t+1}^{−ρ}}` at the history `h` for the portfolio
`x` (O&R Supplement A, p. 744), with returns `R n h` and next-date shares `μ(h, s)`. -/
noncomputable def nodeGrowth (tr : EventTree.Tree S) (β ρ : ℝ)
    (R : (n : ℕ) → (Fin n → S) → Fin N → S → ℝ) (μ : (n : ℕ) → (Fin n → S) → ℝ) (n : ℕ)
    (h : Fin n → S) (x : Fin N → ℝ) : ℝ :=
  β * ∑ s, tr.q n h s * ((1 + portRet (R n h) x s) ^ (1 - ρ) * μ (n + 1) (Fin.snoc h s) ^ (-ρ))

/-- A solution of the book's share recursion, O&R Supplement A, p. 744: shares
`0 < μ_t(h) < 1` and feasible portfolios `x_t(h)` at every history such that `x_t(h)` maximises
the continuation objective `βE_t{(1 + r°)^{1−ρ} μ_{t+1}^{−ρ}}/(1−ρ)` over feasible portfolios and
`μ_t = (1 + [βE_t{(1 + r°_{t+1})^{1−ρ} μ_{t+1}^{−ρ}}]^{1/ρ})^{−1}` with `r°` the return on
`x_t(h)`. -/
def SolvesShareRecursion (tr : EventTree.Tree S) (β ρ : ℝ)
    (R : (n : ℕ) → (Fin n → S) → Fin N → S → ℝ) (μ : (n : ℕ) → (Fin n → S) → ℝ)
    (xs : (n : ℕ) → (Fin n → S) → Fin N → ℝ) : Prop :=
  (∀ n h, 0 < μ n h ∧ μ n h < 1) ∧ (∀ n h, PortFeasible (R n h) (xs n h)) ∧
  (∀ n h x, PortFeasible (R n h) x →
    nodeGrowth tr β ρ R μ n h x / (1 - ρ) ≤ nodeGrowth tr β ρ R μ n h (xs n h) / (1 - ρ)) ∧
  (∀ n h, μ n h = (1 + nodeGrowth tr β ρ R μ n h (xs n h) ^ (1 / ρ))⁻¹)

/-- The weights `β q(s|h) A(h, s)` of the continuation objective at `h`, for value coefficients
`A = μ^{−ρ}` (O&R Supplement A, p. 744). -/
noncomputable def nodeWeights (tr : EventTree.Tree S) (β : ℝ) (A : (n : ℕ) → (Fin n → S) → ℝ)
    (n : ℕ) (h : Fin n → S) : S → ℝ :=
  fun s => β * tr.q n h s * A (n + 1) (Fin.snoc h s)

/-- The value-coefficient map `J ↦ (1 + J^{1/ρ})^ρ`: the book's recursion in terms of
`A_t = μ_t^{−ρ}` (O&R Supplement A, p. 744). -/
noncomputable def shareMap (ρ J : ℝ) : ℝ := (1 + J ^ (1 / ρ)) ^ ρ

/-- Backward iteration of the share recursion from `μ ≡ 1` (a final date on which all wealth is
consumed), O&R Supplement A, p. 744: `iterA m` are the value coefficients `μ^{−ρ}` with `m`
further iterations. -/
noncomputable def iterA (tr : EventTree.Tree S) (β ρ : ℝ)
    (R : (n : ℕ) → (Fin n → S) → Fin N → S → ℝ) : ℕ → (n : ℕ) → (Fin n → S) → ℝ
  | 0 => fun _ _ => 1
  | m + 1 => fun n h => shareMap ρ (optJ ρ (R n h) (nodeWeights tr β (iterA tr β ρ R m) n h))

/-- Monotonicity of the optimal weighted growth in the weights (O&R Supplement A, p. 744). -/
theorem optJ_mono [Nonempty S] {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≠ 1) (r : Fin N → S → ℝ)
    (k : Fin N) (hNA : NoArbitrage r) (hF : ∃ x₀, PortFeasible r x₀) {w w' : S → ℝ}
    (hw : ∀ s, 0 < w s) (hww : ∀ s, w s ≤ w' s) : optJ ρ r w ≤ optJ ρ r w' := by
  have hw' : ∀ s, 0 < w' s := fun s => lt_of_lt_of_le (hw s) (hww s)
  have hx := (optPortW_spec hρ hρ1 r k w hw hNA hF).1
  have hx' := (optPortW_spec hρ hρ1 r k w' hw' hNA hF).1
  have hsum : ∀ x, PortFeasible r x → ∑ s, w s * (1 + portRet r x s) ^ (1 - ρ)
      ≤ ∑ s, w' s * (1 + portRet r x s) ^ (1 - ρ) := fun x hx =>
    Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_right (hww s)
      (Real.rpow_nonneg (hx.2 s).le _)
  rcases lt_or_gt_of_ne hρ1 with hlt | hgt
  · exact (hsum _ hx).trans ((optJ_compare hρ hρ1 r k w' hw' hNA hF hx).1 hlt)
  · exact ((optJ_compare hρ hρ1 r k w hw hNA hF hx').2 hgt).trans (hsum _ hx')

/-- The growth factor is `β(1 − ρ)` times the portfolio objective (O&R Supplement A, p. 744;
`ρ ≠ 1`). -/
theorem growthFactor_eq_portObj (Ω : StateSpace S) (β : ℝ) {ρ : ℝ} (hρ1 : ρ ≠ 1)
    (r : Fin N → S → ℝ) (x : Fin N → ℝ) :
    growthFactor Ω β ρ r x = β * (1 - ρ) * portObj Ω ρ r x := by
  have hp : (1 : ℝ) - ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm hρ1)
  simp only [growthFactor, portObj, StateSpace.expect, crraUtil, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  field_simp

/-- A bound on the optimal weighted growth by the uniform growth condition (O&R Supplement A,
p. 744): if `w(s) ≤ c β q(s)` and the one-period optimal growth factor `βE(1 + r°)^{1−ρ}` at the
node is at most `G`, then `J(w) ≤ cG`. -/
theorem optJ_le_growth (Ω : StateSpace S) {β ρ : ℝ} (hβ : 0 < β) (hρ : 0 < ρ) (hρ1 : ρ ≠ 1)
    (r : Fin N → S → ℝ) (k : Fin N) (hπ : ∀ s, 0 < Ω.prob s) (hNA : NoArbitrage r)
    (hF : ∃ x₀, PortFeasible r x₀) {G c : ℝ} (hc : 0 ≤ c)
    (hG : ∀ x, PortFeasible r x → (∀ x', PortFeasible r x' → portObj Ω ρ r x' ≤ portObj Ω ρ r x)
      → growthFactor Ω β ρ r x ≤ G)
    {w : S → ℝ} (hw : ∀ s, 0 < w s) (hwle : ∀ s, w s ≤ c * (β * Ω.prob s)) :
    optJ ρ r w ≤ c * G := by
  have := nonempty_of_stateSpace Ω
  obtain ⟨xu, hxu, hmax, -⟩ := exists_optimal_portfolio Ω hρ hρ1 r k hπ hNA hF
  have hGu := hG xu hxu hmax
  have hbound : ∀ x, PortFeasible r x →
      ∑ s, w s * (1 + portRet r x s) ^ (1 - ρ) ≤ c * growthFactor Ω β ρ r x := by
    intro x hx
    simp only [growthFactor, StateSpace.expect, Finset.mul_sum]
    refine Finset.sum_le_sum fun s _ => ?_
    have := mul_le_mul_of_nonneg_right (hwle s) (Real.rpow_nonneg (hx.2 s).le (1 - ρ))
    linarith
  rcases lt_or_gt_of_ne hρ1 with hlt | hgt
  · have hx := (optPortW_spec hρ hρ1 r k w hw hNA hF).1
    have hg : growthFactor Ω β ρ r (optPortW ρ r w) ≤ growthFactor Ω β ρ r xu := by
      rw [growthFactor_eq_portObj Ω β hρ1, growthFactor_eq_portObj Ω β hρ1]
      exact mul_le_mul_of_nonneg_left (hmax _ hx) (mul_nonneg hβ.le (by linarith))
    calc optJ ρ r w ≤ c * growthFactor Ω β ρ r (optPortW ρ r w) := hbound _ hx
      _ ≤ c * G := mul_le_mul_of_nonneg_left (hg.trans hGu) hc
  · calc optJ ρ r w ≤ ∑ s, w s * (1 + portRet r xu s) ^ (1 - ρ) :=
          (optJ_compare hρ hρ1 r k w hw hNA hF hxu).2 hgt
      _ ≤ c * growthFactor Ω β ρ r xu := hbound _ hxu
      _ ≤ c * G := mul_le_mul_of_nonneg_left hGu hc

/-- Continuity of the optimal weighted growth along increasing weights (O&R Supplement A,
p. 744): if `w_m(s) → w(s)` with `0 < w_low(s) ≤ w_m(s) ≤ w(s)`, then `J(w_m) → J(w)`. For
`ρ < 1` compare at the limit optimum; for `ρ > 1` the gross returns of the `w_m`-optima are
bounded through `w_low(s)(1 + r°(s))^{1−ρ} ≤ J(w_m) ≤ J(w)`. -/
theorem optJ_tendsto [Nonempty S] {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≠ 1) (r : Fin N → S → ℝ)
    (k : Fin N) (hNA : NoArbitrage r) (hF : ∃ x₀, PortFeasible r x₀) (w : ℕ → S → ℝ)
    (ws wl : S → ℝ) (hwl : ∀ s, 0 < wl s) (hle1 : ∀ m s, wl s ≤ w m s)
    (hle2 : ∀ m s, w m s ≤ ws s) (hlim : ∀ s, Tendsto (fun m => w m s) atTop (𝓝 (ws s))) :
    Tendsto (fun m => optJ ρ r (w m)) atTop (𝓝 (optJ ρ r ws)) := by
  have hw : ∀ m s, 0 < w m s := fun m s => lt_of_lt_of_le (hwl s) (hle1 m s)
  have hws : ∀ s, 0 < ws s := fun s => lt_of_lt_of_le (hw 0 s) (hle2 0 s)
  have hup : ∀ m, optJ ρ r (w m) ≤ optJ ρ r ws := fun m =>
    optJ_mono hρ hρ1 r k hNA hF (hw m) (hle2 m)
  obtain ⟨K, hlow⟩ : ∃ K : S → ℝ, ∀ m,
      optJ ρ r ws - ∑ s, (ws s - w m s) * K s ≤ optJ ρ r (w m) := by
    rcases lt_or_gt_of_ne hρ1 with hlt | hgt
    · refine ⟨fun s => (1 + portRet r (optPortW ρ r ws) s) ^ (1 - ρ), fun m => ?_⟩
      have hx := (optPortW_spec hρ hρ1 r k ws hws hNA hF).1
      have h1 := (optJ_compare hρ hρ1 r k (w m) (hw m) hNA hF hx).1 hlt
      have e : optJ ρ r ws - ∑ s, (ws s - w m s) * (1 + portRet r (optPortW ρ r ws) s) ^ (1 - ρ)
          = ∑ s, w m s * (1 + portRet r (optPortW ρ r ws) s) ^ (1 - ρ) := by
        rw [optJ, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun s _ => by ring
      rw [e]; exact h1
    · refine ⟨fun s => optJ ρ r ws / wl s, fun m => ?_⟩
      have hxm := (optPortW_spec hρ hρ1 r k (w m) (hw m) hNA hF).1
      have h1 := (optJ_compare hρ hρ1 r k ws hws hNA hF hxm).2 hgt
      have hy : ∀ s, (1 + portRet r (optPortW ρ r (w m)) s) ^ (1 - ρ) ≤ optJ ρ r ws / wl s := by
        intro s
        rw [le_div_iff₀ (hwl s)]
        have hsingle : w m s * (1 + portRet r (optPortW ρ r (w m)) s) ^ (1 - ρ)
            ≤ optJ ρ r (w m) := Finset.single_le_sum (f := fun s =>
          w m s * (1 + portRet r (optPortW ρ r (w m)) s) ^ (1 - ρ))
          (fun s _ => mul_nonneg (hw m s).le (Real.rpow_nonneg (hxm.2 s).le _))
          (Finset.mem_univ s)
        have h2 := mul_le_mul_of_nonneg_right (hle1 m s)
          (Real.rpow_nonneg (hxm.2 s).le (1 - ρ))
        have h3 := hup m
        linarith
      have e : ∑ s, ws s * (1 + portRet r (optPortW ρ r (w m)) s) ^ (1 - ρ)
          = optJ ρ r (w m) + ∑ s, (ws s - w m s)
            * (1 + portRet r (optPortW ρ r (w m)) s) ^ (1 - ρ) := by
        rw [optJ, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun s _ => by ring
      have h4 : ∑ s, (ws s - w m s) * (1 + portRet r (optPortW ρ r (w m)) s) ^ (1 - ρ)
          ≤ ∑ s, (ws s - w m s) * (optJ ρ r ws / wl s) :=
        Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hy s)
          (by linarith [hle2 m s])
      linarith
  have hT : Tendsto (fun m => optJ ρ r ws - ∑ s, (ws s - w m s) * K s) atTop
      (𝓝 (optJ ρ r ws)) := by
    have : Tendsto (fun m => ∑ s, (ws s - w m s) * K s) atTop (𝓝 (∑ _s : S, (0 : ℝ))) :=
      tendsto_finsetSum _ fun s _ => by
        simpa using ((tendsto_const_nhds (x := ws s)).sub (hlim s)).mul_const (K s)
    simpa using (tendsto_const_nhds (x := optJ ρ r ws)).sub this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hT tendsto_const_nhds hlow hup

/-- The value-coefficient map is monotone on `[0, ∞)` (O&R Supplement A, p. 744). -/
theorem shareMap_mono {ρ : ℝ} (hρ : 0 < ρ) {J J' : ℝ} (hJ : 0 ≤ J) (hJJ : J ≤ J') :
    shareMap ρ J ≤ shareMap ρ J' := by
  unfold shareMap
  have h1 : J ^ (1 / ρ) ≤ J' ^ (1 / ρ) := Real.rpow_le_rpow hJ hJJ (by positivity)
  exact Real.rpow_le_rpow (by positivity) (by linarith) hρ.le

/-- The value-coefficient map is at least one on `[0, ∞)` (O&R Supplement A, p. 744). -/
theorem one_le_shareMap {ρ : ℝ} (hρ : 0 < ρ) {J : ℝ} (hJ : 0 ≤ J) : 1 ≤ shareMap ρ J :=
  Real.one_le_rpow (by linarith [Real.rpow_nonneg hJ (1 / ρ)]) hρ.le

/-- The value-coefficient map is continuous (O&R Supplement A, p. 744; `ρ > 0`). -/
theorem continuous_shareMap {ρ : ℝ} (hρ : 0 < ρ) : Continuous (shareMap ρ) := by
  unfold shareMap
  exact (continuous_const.add (continuous_id.rpow_const fun _ => Or.inr (by positivity))).rpow_const
    fun _ => Or.inr hρ.le

/-- The bound `Ā = (1 − G^{1/ρ})^{−ρ}` is a fixed point of `A ↦ (1 + (AG)^{1/ρ})^ρ`
(O&R Supplement A, p. 744; `0 ≤ G < 1`). -/
theorem shareMap_bound {ρ : ℝ} (hρ : 0 < ρ) {G : ℝ} (hG0 : 0 ≤ G) (hG1 : G < 1) :
    shareMap ρ ((1 - G ^ (1 / ρ)) ^ (-ρ) * G) = (1 - G ^ (1 / ρ)) ^ (-ρ) := by
  set g := G ^ (1 / ρ) with hg
  have hg0 : 0 ≤ g := Real.rpow_nonneg hG0 _
  have hg1 : g < 1 := Real.rpow_lt_one hG0 hG1 (by positivity)
  have h1 : 0 < 1 - g := by linarith
  have hGg : G = g ^ ρ := by rw [hg, one_div, Real.rpow_inv_rpow hG0 hρ.ne']
  have e1 : ((1 - g) ^ (-ρ)) ^ (1 / ρ) = (1 - g)⁻¹ := by
    rw [← Real.rpow_mul h1.le, show -ρ * (1 / ρ) = -1 by field_simp, Real.rpow_neg_one]
  have e2 : (g ^ ρ) ^ (1 / ρ) = g := by rw [one_div, Real.rpow_rpow_inv hg0 hρ.ne']
  unfold shareMap
  rw [hGg, Real.mul_rpow (Real.rpow_nonneg h1.le _) (Real.rpow_nonneg hg0 _), e1, e2,
    show 1 + (1 - g)⁻¹ * g = (1 - g)⁻¹ by field_simp; ring, Real.inv_rpow h1.le,
    Real.rpow_neg h1.le]

/-- A general event tree whose one-step probabilities sum to one has a nonempty set of events. -/
theorem nonempty_of_tree (tr : EventTree.Tree S) : Nonempty S :=
  nonempty_of_stateSpace (nodeSpace tr 0 Fin.elim0)

/-- Existence of a solution of the book's share recursion, O&R Supplement A, p. 744, for returns
and probabilities that vary with the history, as the limit of backward iterations. Assume
positive one-step probabilities, no arbitrage and some feasible portfolio at every history, and
the uniform growth condition: at every history the one-period optimal growth factor
`βE_t(1 + r°)^{1−ρ}` is at most `G < 1`. Then the iterates `iterA m` from `μ ≡ 1` increase to
the value coefficients `μ_t^{−ρ}` of a solution `(μ, x)` of the recursion, with
`μ_t ≥ 1 − G^{1/ρ}` at every history. -/
theorem exists_share_recursion_solution (tr : EventTree.Tree S) (hq : ∀ n h s, 0 < tr.q n h s)
    {β ρ : ℝ} (hβ : 0 < β) (hρ : 0 < ρ) (hρ1 : ρ ≠ 1)
    (R : (n : ℕ) → (Fin n → S) → Fin N → S → ℝ) (k : Fin N) (hNA : ∀ n h, NoArbitrage (R n h))
    (hF : ∀ n h, ∃ x₀, PortFeasible (R n h) x₀) {G : ℝ} (hG0 : 0 ≤ G) (hG1 : G < 1)
    (hG : ∀ n h x, PortFeasible (R n h) x → (∀ x', PortFeasible (R n h) x' →
      portObj (nodeSpace tr n h) ρ (R n h) x' ≤ portObj (nodeSpace tr n h) ρ (R n h) x) →
      growthFactor (nodeSpace tr n h) β ρ (R n h) x ≤ G) :
    ∃ μ xs, SolvesShareRecursion tr β ρ R μ xs ∧ (∀ n h, 1 - G ^ (1 / ρ) ≤ μ n h) ∧
      ∀ n h, Tendsto (fun m => iterA tr β ρ R m n h) atTop (𝓝 (μ n h ^ (-ρ))) := by
  have := nonempty_of_tree tr
  set Ab := (1 - G ^ (1 / ρ)) ^ (-ρ) with hAb
  have hg1 : G ^ (1 / ρ) < 1 := Real.rpow_lt_one hG0 hG1 (by positivity)
  have hAb0 : 0 ≤ Ab := Real.rpow_nonneg (by linarith) _
  -- bounds and monotonicity of the iterates
  have hbd : ∀ m n h, 1 ≤ iterA tr β ρ R m n h ∧ iterA tr β ρ R m n h ≤ Ab := by
    intro m
    induction m with
    | zero =>
      intro n h
      refine ⟨le_rfl, ?_⟩
      exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos (by linarith)
        (by linarith [Real.rpow_nonneg hG0 (1 / ρ)]) (by linarith)
    | succ m ih =>
      intro n h
      have hw : ∀ s, 0 < nodeWeights tr β (iterA tr β ρ R m) n h s := fun s =>
        mul_pos (mul_pos hβ (hq n h s)) (by linarith [(ih (n + 1) (Fin.snoc h s)).1])
      have hJ0 := (optJ_pos hρ hρ1 (R n h) k _ hw (hNA n h) (hF n h)).le
      refine ⟨one_le_shareMap hρ hJ0, ?_⟩
      have hJ : optJ ρ (R n h) (nodeWeights tr β (iterA tr β ρ R m) n h) ≤ Ab * G :=
        optJ_le_growth (nodeSpace tr n h) hβ hρ hρ1 (R n h) k (hq n h) (hNA n h) (hF n h)
          hAb0 (hG n h) hw fun s => by
            simp only [nodeWeights, nodeSpace]
            have := (ih (n + 1) (Fin.snoc h s)).2
            have hqs := (hq n h s).le
            nlinarith [mul_nonneg hβ.le hqs]
      calc iterA tr β ρ R (m + 1) n h
          = shareMap ρ (optJ ρ (R n h) (nodeWeights tr β (iterA tr β ρ R m) n h)) := rfl
        _ ≤ shareMap ρ (Ab * G) := shareMap_mono hρ hJ0 hJ
        _ = Ab := shareMap_bound hρ hG0 hG1
  have hwpos : ∀ (A : (n : ℕ) → (Fin n → S) → ℝ), (∀ n h, 1 ≤ A n h) → ∀ n h s,
      0 < nodeWeights tr β A n h s := fun A hA n h s =>
    mul_pos (mul_pos hβ (hq n h s)) (by linarith [hA (n + 1) (Fin.snoc h s)])
  have hmono : ∀ m n h, iterA tr β ρ R m n h ≤ iterA tr β ρ R (m + 1) n h := by
    intro m
    induction m with
    | zero => intro n h; exact (hbd 1 n h).1
    | succ m ih =>
      intro n h
      have hJ0 := (optJ_pos hρ hρ1 (R n h) k _ (hwpos _ (fun n h => (hbd m n h).1) n h)
        (hNA n h) (hF n h)).le
      refine shareMap_mono hρ hJ0 (optJ_mono hρ hρ1 (R n h) k (hNA n h) (hF n h)
        (hwpos _ (fun n h => (hbd m n h).1) n h) fun s => ?_)
      simp only [nodeWeights]
      exact mul_le_mul_of_nonneg_left (ih (n + 1) (Fin.snoc h s))
        (mul_nonneg hβ.le (hq n h s).le)
  have hMono : ∀ n h, Monotone fun m => iterA tr β ρ R m n h := fun n h =>
    monotone_nat_of_le_succ fun m => hmono m n h
  have hBdd : ∀ n h, BddAbove (Set.range fun m => iterA tr β ρ R m n h) := fun n h =>
    ⟨Ab, by rintro _ ⟨m, rfl⟩; exact (hbd m n h).2⟩
  set As : (n : ℕ) → (Fin n → S) → ℝ := fun n h => ⨆ m, iterA tr β ρ R m n h with hAs
  have hlimA : ∀ n h, Tendsto (fun m => iterA tr β ρ R m n h) atTop (𝓝 (As n h)) := fun n h =>
    tendsto_atTop_ciSup (hMono n h) (hBdd n h)
  have hAs1 : ∀ n h, 1 ≤ As n h := fun n h =>
    le_trans (hbd 0 n h).1 (le_ciSup (hBdd n h) 0)
  have hAsb : ∀ n h, As n h ≤ Ab := fun n h => ciSup_le fun m => (hbd m n h).2
  have hAs0 : ∀ n h, 0 < As n h := fun n h => by linarith [hAs1 n h]
  -- the limit solves the recursion
  have hrec : ∀ n h, As n h = shareMap ρ (optJ ρ (R n h) (nodeWeights tr β As n h)) := by
    intro n h
    have hJ := optJ_tendsto hρ hρ1 (R n h) k (hNA n h) (hF n h)
      (fun m => nodeWeights tr β (iterA tr β ρ R m) n h) (nodeWeights tr β As n h)
      (nodeWeights tr β (fun _ _ => 1) n h) (hwpos _ (fun _ _ => le_rfl) n h)
      (fun m s => by
        simp only [nodeWeights]
        exact mul_le_mul_of_nonneg_left (hbd m (n + 1) (Fin.snoc h s)).1
          (mul_nonneg hβ.le (hq n h s).le))
      (fun m s => by
        simp only [nodeWeights]
        exact mul_le_mul_of_nonneg_left (le_ciSup (hBdd (n + 1) (Fin.snoc h s)) m)
          (mul_nonneg hβ.le (hq n h s).le))
      (fun s => (hlimA (n + 1) (Fin.snoc h s)).const_mul _)
    have h1 : Tendsto (fun m => iterA tr β ρ R (m + 1) n h) atTop
        (𝓝 (shareMap ρ (optJ ρ (R n h) (nodeWeights tr β As n h)))) :=
      ((continuous_shareMap hρ).tendsto _).comp hJ
    have h2 : Tendsto (fun m => iterA tr β ρ R (m + 1) n h) atTop (𝓝 (As n h)) :=
      (tendsto_add_atTop_iff_nat 1).mpr (hlimA n h)
    exact tendsto_nhds_unique h2 h1
  -- the shares and portfolios
  set μ : (n : ℕ) → (Fin n → S) → ℝ := fun n h => (As n h ^ (1 / ρ))⁻¹ with hμ
  set xs : (n : ℕ) → (Fin n → S) → Fin N → ℝ :=
    fun n h => optPortW ρ (R n h) (nodeWeights tr β As n h) with hxs
  have hμA : ∀ n h, μ n h ^ (-ρ) = As n h := by
    intro n h
    simp only [hμ]
    rw [Real.inv_rpow (Real.rpow_nonneg (hAs0 n h).le _), ← Real.rpow_mul (hAs0 n h).le,
      show 1 / ρ * -ρ = -1 by field_simp, Real.rpow_neg_one, inv_inv]
  have hgrowth : ∀ n h x, nodeGrowth tr β ρ R μ n h x
      = ∑ s, nodeWeights tr β As n h s * (1 + portRet (R n h) x s) ^ (1 - ρ) := by
    intro n h x
    simp only [nodeGrowth, nodeWeights, hμA, Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => by ring
  have hwAs := hwpos As hAs1
  refine ⟨μ, xs, ⟨fun n h => ?_, fun n h => ?_, fun n h x hx => ?_, fun n h => ?_⟩,
    fun n h => ?_, fun n h => ?_⟩
  · have hJ := optJ_pos hρ hρ1 (R n h) k _ (hwAs n h) (hNA n h) (hF n h)
    have e : As n h ^ (1 / ρ) = 1 + optJ ρ (R n h) (nodeWeights tr β As n h) ^ (1 / ρ) := by
      rw [hrec n h, shareMap, ← Real.rpow_mul (by positivity), mul_one_div_cancel hρ.ne',
        Real.rpow_one]
    have hpos : 0 < optJ ρ (R n h) (nodeWeights tr β As n h) ^ (1 / ρ) :=
      Real.rpow_pos_of_pos hJ _
    simp only [hμ]
    rw [e]
    exact ⟨inv_pos.mpr (by linarith), inv_lt_one_of_one_lt₀ (by linarith)⟩
  · exact (optPortW_spec hρ hρ1 (R n h) k _ (hwAs n h) (hNA n h) (hF n h)).1
  · have := (optPortW_spec hρ hρ1 (R n h) k _ (hwAs n h) (hNA n h) (hF n h)).2 x hx
    simp only [weightedObj] at this
    rw [hgrowth, hgrowth]
    exact this
  · have e : As n h ^ (1 / ρ) = 1 + optJ ρ (R n h) (nodeWeights tr β As n h) ^ (1 / ρ) := by
      have h0 : 0 ≤ 1 + optJ ρ (R n h) (nodeWeights tr β As n h) ^ (1 / ρ) := by
        have := optJ_pos hρ hρ1 (R n h) k _ (hwAs n h) (hNA n h) (hF n h)
        positivity
      conv_lhs => rw [hrec n h, shareMap]
      rw [← Real.rpow_mul h0, mul_one_div_cancel hρ.ne', Real.rpow_one]
    simp only [hμ]
    rw [e, hgrowth]
    rfl
  · simp only [hμ]
    have h1 : As n h ^ (1 / ρ) ≤ Ab ^ (1 / ρ) :=
      Real.rpow_le_rpow (hAs0 n h).le (hAsb n h) (by positivity)
    have h2 : Ab ^ (1 / ρ) = (1 - G ^ (1 / ρ))⁻¹ := by
      rw [hAb, ← Real.rpow_mul (by linarith), show -ρ * (1 / ρ) = -1 by field_simp,
        Real.rpow_neg_one]
    rw [h2] at h1
    have h3 := inv_anti₀ (Real.rpow_pos_of_pos (hAs0 n h) _) h1
    rwa [inv_inv] at h3
  · rw [hμA]; exact hlimA n h

/-! ### Verification with history-dependent returns -/

/-- Wealth along a plan when returns depend on the history (O&R Supplement A, p. 742):
`W(h, s) = (1 + r°_h(x(h))(s))(W(h) − c(h))` with the returns `R n h` at `h`. -/
noncomputable def wealthT (R : (n : ℕ) → (Fin n → S) → Fin N → S → ℝ) (W₀ : ℝ)
    (c : (n : ℕ) → (Fin n → S) → ℝ) (x : (n : ℕ) → (Fin n → S) → Fin N → ℝ) :
    (n : ℕ) → (Fin n → S) → ℝ
  | 0, _ => W₀
  | n + 1, g => (1 + portRet (R n (Fin.init g)) (x n (Fin.init g)) (g (Fin.last n)))
      * (wealthT R W₀ c x n (Fin.init g) - c n (Fin.init g))

omit [Fintype S] in
/-- The wealth-accumulation identity with history-dependent returns (O&R Supplement A,
p. 742). -/
theorem wealthT_snoc (R : (n : ℕ) → (Fin n → S) → Fin N → S → ℝ) (W₀ : ℝ)
    (c : (n : ℕ) → (Fin n → S) → ℝ) (x : (n : ℕ) → (Fin n → S) → Fin N → ℝ) {n : ℕ}
    (h : Fin n → S) (s : S) :
    wealthT R W₀ c x (n + 1) (Fin.snoc h s)
      = (1 + portRet (R n h) (x n h) s) * (wealthT R W₀ c x n h - c n h) := by
  simp only [wealthT, Fin.init_snoc, Fin.snoc_last]

/-- An admissible plan with history-dependent returns (O&R Supplement A, p. 742): positive
consumption not exceeding wealth, shares adding up to one, at every history. -/
def AdmissibleT (R : (n : ℕ) → (Fin n → S) → Fin N → S → ℝ) (W₀ : ℝ)
    (c : (n : ℕ) → (Fin n → S) → ℝ) (x : (n : ℕ) → (Fin n → S) → Fin N → ℝ) : Prop :=
  (∀ n h, 0 < c n h) ∧ (∀ n h, c n h ≤ wealthT R W₀ c x n h) ∧ (∀ n h, ∑ i, x n h i = 1)

omit [Fintype S] in
/-- Along an admissible plan the investor saves a positive amount and holds a feasible portfolio
at every history (O&R Supplement A, p. 743, footnote 1). -/
theorem admissibleT_step [Nonempty S] (R : (n : ℕ) → (Fin n → S) → Fin N → S → ℝ) (W₀ : ℝ)
    {c : (n : ℕ) → (Fin n → S) → ℝ} {x : (n : ℕ) → (Fin n → S) → Fin N → ℝ}
    (hadm : AdmissibleT R W₀ c x) (n : ℕ) (h : Fin n → S) :
    c n h < wealthT R W₀ c x n h ∧ PortFeasible (R n h) (x n h) := by
  have hD : 0 ≤ wealthT R W₀ c x n h - c n h := by linarith [hadm.2.1 n h]
  have key : ∀ s, 0 < (1 + portRet (R n h) (x n h) s) * (wealthT R W₀ c x n h - c n h) := by
    intro s
    rw [← wealthT_snoc]
    exact lt_of_lt_of_le (hadm.1 _ _) (hadm.2.1 _ _)
  obtain ⟨s₀⟩ := ‹Nonempty S›
  have hD' : 0 < wealthT R W₀ c x n h - c n h := by
    rcases hD.lt_or_eq with h' | h'
    · exact h'
    · have := key s₀; rw [← h', mul_zero] at this; exact absurd this (lt_irrefl 0)
  exact ⟨by linarith, hadm.2.2 n h, fun s => pos_of_mul_pos_left (key s) hD'.le⟩

/-- The law of iterated expectations on a general event tree (O&R Appendix 5C, p. 341):
`Σ_{h_{t+1}} π(h_{t+1}) f = Σ_{h_t} π(h_t) Σ_s q(s|h_t) f(h_t, s)`. -/
theorem sum_succ_tree (tr : EventTree.Tree S) (n : ℕ) (f : (Fin (n + 1) → S) → ℝ) :
    ∑ g, tr.histProb g * f g = ∑ h, tr.histProb h * ∑ s, tr.q n h s * f (Fin.snoc h s) := by
  rw [sum_snoc]
  refine Finset.sum_congr rfl fun h _ => ?_
  simp only [tr.histProb_snoc, Finset.mul_sum]
  exact Finset.sum_congr rfl fun s _ => by ring

/-- The dynamic-programming inequality summed along a plan on a general tree (O&R Supplement A,
p. 742): if `u(c(h)) + βΣ_s q(s|h) v(h, s) ≤ v(h)` at every history, then
`Σ_{t<n} β^t E u(C_t) + β^n E v_n ≤ v(h_1)`. -/
theorem telescope_tree_le (tr : EventTree.Tree S) {β : ℝ} (hβ : 0 ≤ β) (u : ℝ → ℝ)
    (c v : (n : ℕ) → (Fin n → S) → ℝ)
    (hstep : ∀ n h, u (c n h) + β * ∑ s, tr.q n h s * v (n + 1) (Fin.snoc h s) ≤ v n h)
    (n : ℕ) :
    ∑ k ∈ range n, utilSeries tr β u c k + β ^ n * ∑ h, tr.histProb h * v n h
      ≤ v 0 Fin.elim0 := by
  induction n with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, pow_zero, one_mul, zero_add,
      Fintype.sum_unique, tr.histProb_zero]
    rw [Subsingleton.elim default Fin.elim0]
  | succ n ih =>
    rw [Finset.sum_range_succ, sum_succ_tree]
    have hle : utilSeries tr β u c n + β ^ (n + 1) * ∑ h, tr.histProb h
        * ∑ s, tr.q n h s * v (n + 1) (Fin.snoc h s)
        ≤ β ^ n * ∑ h, tr.histProb h * v n h := by
      rw [utilSeries, pow_succ, mul_assoc, ← mul_add, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun h _ => ?_) (pow_nonneg hβ n)
      have := mul_le_mul_of_nonneg_left (hstep n h) (tr.histProb_nonneg h)
      linarith
    linarith

/-- The summed dynamic-programming identity when the step holds with equality (O&R
Supplement A, p. 742). -/
theorem telescope_tree_eq (tr : EventTree.Tree S) (β : ℝ) (u : ℝ → ℝ)
    (c v : (n : ℕ) → (Fin n → S) → ℝ)
    (hstep : ∀ n h, u (c n h) + β * ∑ s, tr.q n h s * v (n + 1) (Fin.snoc h s) = v n h)
    (n : ℕ) :
    ∑ k ∈ range n, utilSeries tr β u c k + β ^ n * ∑ h, tr.histProb h * v n h
      = v 0 Fin.elim0 := by
  induction n with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, pow_zero, one_mul, zero_add,
      Fintype.sum_unique, tr.histProb_zero]
    rw [Subsingleton.elim default Fin.elim0]
  | succ n ih =>
    rw [Finset.sum_range_succ, sum_succ_tree]
    have heq : utilSeries tr β u c n + β ^ (n + 1) * ∑ h, tr.histProb h
        * ∑ s, tr.q n h s * v (n + 1) (Fin.snoc h s)
        = β ^ n * ∑ h, tr.histProb h * v n h := by
      rw [utilSeries, pow_succ, mul_assoc, ← mul_add, Finset.mul_sum, ← Finset.sum_add_distrib]
      congr 1
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [← hstep n h]; ring
    linarith

/-- The share identity of the recursion, O&R Supplement A, p. 744: if
`μ = (1 + J^{1/ρ})^{−1}` with `J ≥ 0`, then `μ^{−ρ}(1 − μ)^ρ = J`. -/
theorem share_identity {ρ : ℝ} (hρ : 0 < ρ) {J μ : ℝ} (hJ : 0 ≤ J)
    (hμ : μ = (1 + J ^ (1 / ρ))⁻¹) : μ ^ (-ρ) * (1 - μ) ^ ρ = J := by
  have hJr : 0 ≤ J ^ (1 / ρ) := Real.rpow_nonneg hJ _
  have hμ0 : 0 < μ := by rw [hμ]; positivity
  have h1 : 1 - μ = J ^ (1 / ρ) * μ := by
    rw [hμ]; field_simp; ring
  rw [h1, Real.mul_rpow hJr hμ0.le, one_div, Real.rpow_inv_rpow hJ hρ.ne', Real.rpow_neg hμ0.le]
  field_simp

/-- The continuation value at a history, O&R Supplement A, pp. 743–744: with next-date values
`V_{t+1}(h, s; W) = μ_{t+1}(h, s)^{−ρ}W^{1−ρ}/(1−ρ)`, saving `D > 0` in a feasible portfolio `x`
gives `βE_t V_{t+1}((1 + r°)D) = [βE_t{(1 + r°)^{1−ρ} μ_{t+1}^{−ρ}}] · D^{1−ρ}/(1−ρ)`. -/
theorem node_continuation (tr : EventTree.Tree S) (β ρ : ℝ)
    (R : (n : ℕ) → (Fin n → S) → Fin N → S → ℝ) (μ : (n : ℕ) → (Fin n → S) → ℝ) (n : ℕ)
    (h : Fin n → S) {x : Fin N → ℝ} (hx : PortFeasible (R n h) x) {D : ℝ} (hD : 0 < D) :
    β * ∑ s, tr.q n h s * crraValue (μ (n + 1) (Fin.snoc h s)) ρ ((1 + portRet (R n h) x s) * D)
      = nodeGrowth tr β ρ R μ n h x * crraUtil ρ D := by
  simp only [nodeGrowth, crraValue, crraUtil, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Real.mul_rpow (hx.2 s).le hD.le]
  ring

/-- The Bellman inequality at a history, O&R Supplement A, pp. 742–744: at a solution of the
share recursion, `u(C) + βE_t V_{t+1}((1 + r°(x))(W − C)) ≤ V_t(W)` for every `0 < C < W` and
feasible portfolio `x`, with `V_t(W) = μ_t^{−ρ}W^{1−ρ}/(1−ρ)`. -/
theorem bellman_node_le (tr : EventTree.Tree S) {β ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≠ 1)
    (R : (n : ℕ) → (Fin n → S) → Fin N → S → ℝ) {μ : (n : ℕ) → (Fin n → S) → ℝ}
    {xs : (n : ℕ) → (Fin n → S) → Fin N → ℝ} (hsol : SolvesShareRecursion tr β ρ R μ xs)
    (hJ : ∀ n h, 0 ≤ nodeGrowth tr β ρ R μ n h (xs n h)) (n : ℕ) (h : Fin n → S)
    {W C : ℝ} {x : Fin N → ℝ} (hC : 0 < C) (hCW : C < W) (hx : PortFeasible (R n h) x) :
    crraUtil ρ C + β * ∑ s, tr.q n h s * crraValue (μ (n + 1) (Fin.snoc h s)) ρ
      ((1 + portRet (R n h) x s) * (W - C)) ≤ crraValue (μ n h) ρ W := by
  have hD : 0 < W - C := by linarith
  rw [node_continuation tr β ρ R μ n h hx hD]
  have hopt := hsol.2.2.1 n h x hx
  have hp : nodeGrowth tr β ρ R μ n h x * crraUtil ρ (W - C)
      ≤ nodeGrowth tr β ρ R μ n h (xs n h) * crraUtil ρ (W - C) := by
    have e : ∀ y, y * crraUtil ρ (W - C) = y / (1 - ρ) * (W - C) ^ (1 - ρ) := fun y => by
      unfold crraUtil; ring
    rw [e, e]
    exact mul_le_mul_of_nonneg_right hopt (Real.rpow_nonneg hD.le _)
  have hid := share_identity hρ (hJ n h) (hsol.2.2.2 n h)
  have hsplit := crra_split_le hρ hρ1 (hsol.1 n h).1 (hsol.1 n h).2 hC hCW
  rw [hid] at hsplit
  unfold crraValue
  linarith

/-- The Bellman equation holds with equality at `C = μ_t W` and the portfolio `x_t(h)`, O&R
Supplement A, p. 744, and the continuation is `(1 − μ_t)V_t(W)`. -/
theorem bellman_node_eq (tr : EventTree.Tree S) {β ρ : ℝ} (hρ : 0 < ρ)
    (R : (n : ℕ) → (Fin n → S) → Fin N → S → ℝ) {μ : (n : ℕ) → (Fin n → S) → ℝ}
    {xs : (n : ℕ) → (Fin n → S) → Fin N → ℝ} (hsol : SolvesShareRecursion tr β ρ R μ xs)
    (hJ : ∀ n h, 0 ≤ nodeGrowth tr β ρ R μ n h (xs n h)) (n : ℕ) (h : Fin n → S) {W : ℝ}
    (hW : 0 < W) :
    β * ∑ s, tr.q n h s * crraValue (μ (n + 1) (Fin.snoc h s)) ρ
      ((1 + portRet (R n h) (xs n h) s) * ((1 - μ n h) * W))
        = (1 - μ n h) * crraValue (μ n h) ρ W ∧
    crraUtil ρ (μ n h * W) + β * ∑ s, tr.q n h s * crraValue (μ (n + 1) (Fin.snoc h s)) ρ
      ((1 + portRet (R n h) (xs n h) s) * ((1 - μ n h) * W)) = crraValue (μ n h) ρ W := by
  obtain ⟨hμ0, hμ1⟩ := hsol.1 n h
  have h1 : 0 < 1 - μ n h := by linarith
  have hid := share_identity hρ (hJ n h) (hsol.2.2.2 n h)
  have hc := node_continuation tr β ρ R μ n h (hsol.2.1 n h) (mul_pos h1 hW)
  have hbb : (1 - μ n h) ^ ρ * (1 - μ n h) ^ (1 - ρ) = 1 - μ n h := by
    rw [← Real.rpow_add h1, show ρ + (1 - ρ) = 1 by ring, Real.rpow_one]
  have e1 : nodeGrowth tr β ρ R μ n h (xs n h) * crraUtil ρ ((1 - μ n h) * W)
      = (1 - μ n h) * crraValue (μ n h) ρ W := by
    rw [← hid, crraValue, crraUtil, crraUtil, Real.mul_rpow h1.le hW.le]
    linear_combination μ n h ^ (-ρ) * W ^ (1 - ρ) / (1 - ρ) * hbb
  refine ⟨hc.trans e1, ?_⟩
  rw [hc, e1]
  have := crra_split_eq (ρ := ρ) hμ0 hμ1 hW
  rw [show W - μ n h * W = (1 - μ n h) * W by ring, hid] at this
  rw [← e1]
  unfold crraValue
  linarith

/-- The growth term of a solution is nonnegative (O&R Supplement A, p. 744). -/
theorem nodeGrowth_nonneg (tr : EventTree.Tree S) {β ρ : ℝ} (hβ : 0 ≤ β)
    (R : (n : ℕ) → (Fin n → S) → Fin N → S → ℝ) {μ : (n : ℕ) → (Fin n → S) → ℝ}
    {xs : (n : ℕ) → (Fin n → S) → Fin N → ℝ} (hsol : SolvesShareRecursion tr β ρ R μ xs)
    (n : ℕ) (h : Fin n → S) : 0 ≤ nodeGrowth tr β ρ R μ n h (xs n h) :=
  mul_nonneg hβ (Finset.sum_nonneg fun s _ => mul_nonneg (tr.q_nonneg n h s)
    (mul_nonneg (Real.rpow_nonneg ((hsol.2.1 n h).2 s).le _)
      (Real.rpow_nonneg (hsol.1 _ _).1.le _)))

/-- The transversality property with history-dependent returns, O&R Supplement A, p. 744
(proved, not assumed): at a solution of the share recursion with `μ_t ≥ μ₀ > 0` everywhere,
every admissible plan with convergent utility series has `β^t E V_t(W_t) → 0`. -/
theorem transversality_tree (tr : EventTree.Tree S) {β ρ : ℝ} (hβ : 0 < β) (hρ : 0 < ρ)
    (hρ1 : ρ ≠ 1) (R : (n : ℕ) → (Fin n → S) → Fin N → S → ℝ)
    {μ : (n : ℕ) → (Fin n → S) → ℝ} {xs : (n : ℕ) → (Fin n → S) → Fin N → ℝ}
    (hsol : SolvesShareRecursion tr β ρ R μ xs) {μ₀ : ℝ} (hμ₀ : 0 < μ₀)
    (hlow : ∀ n h, μ₀ ≤ μ n h) (W₀ : ℝ) {c : (n : ℕ) → (Fin n → S) → ℝ}
    {x : (n : ℕ) → (Fin n → S) → Fin N → ℝ} (hadm : AdmissibleT R W₀ c x)
    (hU : Summable (utilSeries tr β (crraUtil ρ) c)) :
    Tendsto (fun n => β ^ n * ∑ h, tr.histProb h
      * crraValue (μ n h) ρ (wealthT R W₀ c x n h)) atTop (𝓝 0) := by
  have := nonempty_of_tree tr
  set T := fun n => β ^ n * ∑ h, tr.histProb h * crraValue (μ n h) ρ (wealthT R W₀ c x n h)
    with hT
  have hW : ∀ n h, 0 < wealthT R W₀ c x n h := fun n h =>
    lt_of_lt_of_le (hadm.1 n h) (hadm.2.1 n h)
  have hJ := nodeGrowth_nonneg tr hβ.le R hsol
  rcases lt_or_gt_of_ne hρ1 with hlt | hgt
  · have hVnn : ∀ n h, 0 ≤ crraValue (μ n h) ρ (wealthT R W₀ c x n h) := fun n h =>
      mul_nonneg (Real.rpow_nonneg (hsol.1 n h).1.le _)
        (div_nonneg (Real.rpow_nonneg (hW n h).le _) (by linarith))
    have hT0 : ∀ n, 0 ≤ T n := fun n => mul_nonneg (pow_nonneg hβ.le n)
      (Finset.sum_nonneg fun h _ => mul_nonneg (tr.histProb_nonneg h) (hVnn n h))
    have hμ₀1 : μ₀ < 1 := lt_of_le_of_lt (hlow 0 Fin.elim0) (hsol.1 0 Fin.elim0).2
    set θ := (1 - μ₀) ^ ρ
    have hθ0 : 0 ≤ θ := Real.rpow_nonneg (by linarith) _
    have hθ1 : θ < 1 := Real.rpow_lt_one (by linarith) (by linarith) hρ
    have hrec : ∀ n, T (n + 1) ≤ θ * T n := by
      intro n
      have hms : ∀ (a : ℝ) (f : (Fin n → S) → ℝ), a * ∑ h, f h = ∑ h, a * f h :=
        fun a f => Finset.mul_sum _ _ _
      simp only [hT]
      rw [sum_succ_tree]
      simp only [wealthT_snoc, hms]
      refine Finset.sum_le_sum fun h _ => ?_
      obtain ⟨hlt', hxn⟩ := admissibleT_step R W₀ hadm n h
      have hD : 0 < wealthT R W₀ c x n h - c n h := by linarith
      have hc := node_continuation tr β ρ R μ n h hxn hD
      have hopt := hsol.2.2.1 n h (x n h) hxn
      have hle1 : nodeGrowth tr β ρ R μ n h (x n h) * crraUtil ρ (wealthT R W₀ c x n h - c n h)
          ≤ nodeGrowth tr β ρ R μ n h (xs n h) * crraUtil ρ (wealthT R W₀ c x n h) := by
        have e : ∀ y D, y * crraUtil ρ D = y / (1 - ρ) * D ^ (1 - ρ) := fun y D => by
          unfold crraUtil; ring
        have hm := crraUtil_mono hρ hρ1 hD (by linarith [hadm.1 n h] :
          wealthT R W₀ c x n h - c n h ≤ wealthT R W₀ c x n h)
        calc nodeGrowth tr β ρ R μ n h (x n h) * crraUtil ρ (wealthT R W₀ c x n h - c n h)
            ≤ nodeGrowth tr β ρ R μ n h (xs n h) * crraUtil ρ (wealthT R W₀ c x n h - c n h) := by
              rw [e, e]; exact mul_le_mul_of_nonneg_right hopt (Real.rpow_nonneg hD.le _)
          _ ≤ nodeGrowth tr β ρ R μ n h (xs n h) * crraUtil ρ (wealthT R W₀ c x n h) :=
              mul_le_mul_of_nonneg_left hm (hJ n h)
      have hid := share_identity hρ (hJ n h) (hsol.2.2.2 n h)
      have hθle : (1 - μ n h) ^ ρ ≤ θ :=
        Real.rpow_le_rpow (by linarith [(hsol.1 n h).2]) (by linarith [hlow n h]) hρ.le
      have hchain : β * ∑ s, tr.q n h s * crraValue (μ (n + 1) (Fin.snoc h s)) ρ
          ((1 + portRet (R n h) (x n h) s) * (wealthT R W₀ c x n h - c n h))
          ≤ θ * crraValue (μ n h) ρ (wealthT R W₀ c x n h) := by
        rw [hc]
        refine hle1.trans ?_
        rw [← hid]
        have := hVnn n h
        unfold crraValue at this ⊢
        have hu : 0 ≤ crraUtil ρ (wealthT R W₀ c x n h) :=
          div_nonneg (Real.rpow_nonneg (hW n h).le _) (by linarith)
        have hμr : 0 ≤ μ n h ^ (-ρ) := Real.rpow_nonneg (hsol.1 n h).1.le _
        nlinarith [mul_le_mul_of_nonneg_right hθle (mul_nonneg hμr hu)]
      have h3 := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hchain (tr.histProb_nonneg h)) (pow_nonneg hβ.le n)
      calc β ^ (n + 1) * (tr.histProb h * ∑ s, tr.q n h s * crraValue (μ (n + 1)
            (Fin.snoc h s)) ρ ((1 + portRet (R n h) (x n h) s)
              * (wealthT R W₀ c x n h - c n h)))
          = β ^ n * (tr.histProb h * (β * ∑ s, tr.q n h s * crraValue (μ (n + 1)
            (Fin.snoc h s)) ρ ((1 + portRet (R n h) (x n h) s)
              * (wealthT R W₀ c x n h - c n h)))) := by ring
        _ ≤ β ^ n * (tr.histProb h * (θ * crraValue (μ n h) ρ (wealthT R W₀ c x n h))) := h3
        _ = θ * (β ^ n * (tr.histProb h * crraValue (μ n h) ρ (wealthT R W₀ c x n h))) := by
          ring
    have hgeo : ∀ n, T n ≤ θ ^ n * T 0 := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        calc T (n + 1) ≤ θ * T n := hrec n
          _ ≤ θ * (θ ^ n * T 0) := mul_le_mul_of_nonneg_left ih hθ0
          _ = θ ^ (n + 1) * T 0 := by ring
    have hup : Tendsto (fun n => θ ^ n * T 0) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hθ0 hθ1).mul_const (T 0)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup hT0 hgeo
  · have hlowb : ∀ n, μ₀ ^ (-ρ) * utilSeries tr β (crraUtil ρ) c n ≤ T n := by
      intro n
      simp only [hT, utilSeries]
      rw [← mul_assoc, mul_comm (μ₀ ^ (-ρ)), mul_assoc, Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun h _ => ?_) (pow_nonneg hβ.le n)
      have hm := crraUtil_mono hρ hρ1 (hadm.1 n h) (hadm.2.1 n h)
      have hu : crraUtil ρ (c n h) ≤ 0 :=
        div_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg (hadm.1 n h).le _) (by linarith)
      have hμle : μ n h ^ (-ρ) ≤ μ₀ ^ (-ρ) :=
        Real.rpow_le_rpow_of_nonpos hμ₀ (hlow n h) (by linarith)
      have hμr : 0 ≤ μ n h ^ (-ρ) := Real.rpow_nonneg (hsol.1 n h).1.le _
      have h1 : μ₀ ^ (-ρ) * crraUtil ρ (c n h) ≤ μ n h ^ (-ρ) * crraUtil ρ (c n h) := by
        nlinarith
      have h2 := mul_le_mul_of_nonneg_left hm hμr
      have := mul_le_mul_of_nonneg_left (h1.trans h2) (tr.histProb_nonneg h)
      unfold crraValue
      linarith
    have hup : ∀ n, T n ≤ 0 := by
      intro n
      refine mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hβ.le n)
        (Finset.sum_nonpos fun h _ => mul_nonpos_of_nonneg_of_nonpos
          (tr.histProb_nonneg h) ?_)
      exact mul_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg (hsol.1 n h).1.le _)
        (div_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg (hW n h).le _) (by linarith))
    have hlowT : Tendsto (fun n => μ₀ ^ (-ρ) * utilSeries tr β (crraUtil ρ) c n) atTop
        (𝓝 0) := by
      simpa using hU.tendsto_atTop_zero.const_mul (μ₀ ^ (-ρ))
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlowT tendsto_const_nhds hlowb hup

/-- Wealth under the policy `C = μ_t W` with portfolios `x_t(h)` (O&R Supplement A, p. 744):
`W*(h, s) = (1 + r°_h(x_t(h))(s))(1 − μ_t(h))W*(h)`. -/
noncomputable def optWealthT (R : (n : ℕ) → (Fin n → S) → Fin N → S → ℝ)
    (xs : (n : ℕ) → (Fin n → S) → Fin N → ℝ) (μ : (n : ℕ) → (Fin n → S) → ℝ) (W₀ : ℝ) :
    (n : ℕ) → (Fin n → S) → ℝ
  | 0, _ => W₀
  | n + 1, g => (1 + portRet (R n (Fin.init g)) (xs n (Fin.init g)) (g (Fin.last n)))
      * ((1 - μ n (Fin.init g)) * optWealthT R xs μ W₀ n (Fin.init g))

omit [Fintype S] in
/-- The policy `C = μ_t W`, `x = x_t(h)` generates the wealth path `W*` (O&R Supplement A,
p. 744). -/
theorem wealthT_optPlan (R : (n : ℕ) → (Fin n → S) → Fin N → S → ℝ)
    (xs : (n : ℕ) → (Fin n → S) → Fin N → ℝ) (μ : (n : ℕ) → (Fin n → S) → ℝ) (W₀ : ℝ) :
    wealthT R W₀ (fun n h => μ n h * optWealthT R xs μ W₀ n h) xs = optWealthT R xs μ W₀ := by
  funext n
  induction n with
  | zero => rfl
  | succ n ih =>
    funext g
    simp only [wealthT, optWealthT, ih]
    ring

omit [Fintype S] in
/-- Optimal wealth stays positive (O&R Supplement A, p. 744). -/
theorem optWealthT_pos (R : (n : ℕ) → (Fin n → S) → Fin N → S → ℝ)
    {xs : (n : ℕ) → (Fin n → S) → Fin N → ℝ} {μ : (n : ℕ) → (Fin n → S) → ℝ}
    (hxs : ∀ n h s, 0 < 1 + portRet (R n h) (xs n h) s) (hμ1 : ∀ n h, μ n h < 1) {W₀ : ℝ}
    (hW₀ : 0 < W₀) : ∀ n h, 0 < optWealthT R xs μ W₀ n h := by
  intro n
  induction n with
  | zero => intro h; exact hW₀
  | succ n ih =>
    intro g
    simp only [optWealthT]
    exact mul_pos (hxs _ _ _) (mul_pos (by linarith [hμ1 n (Fin.init g)]) (ih _))

/-- The verification theorem with history-dependent returns, O&R Supplement A, p. 744. Let
`(μ, x)` solve the share recursion on the event tree `tr` (`ρ > 0`, `ρ ≠ 1`, `β > 0`), with
`μ_t ≥ μ₀ > 0` at every history, and let `W₀ > 0`. Then the policy `C = μ_t W` with portfolios
`x_t(h)` is admissible, its utility series converges and it attains
`V_1(W₀) = μ_1^{−ρ}W₀^{1−ρ}/(1−ρ)`; every admissible plan with convergent utility series
achieves at most `V_1(W₀)`. -/
theorem verification_tree (tr : EventTree.Tree S) {β ρ : ℝ} (hβ : 0 < β) (hρ : 0 < ρ)
    (hρ1 : ρ ≠ 1) (R : (n : ℕ) → (Fin n → S) → Fin N → S → ℝ)
    {μ : (n : ℕ) → (Fin n → S) → ℝ} {xs : (n : ℕ) → (Fin n → S) → Fin N → ℝ}
    (hsol : SolvesShareRecursion tr β ρ R μ xs) {μ₀ : ℝ} (hμ₀ : 0 < μ₀)
    (hlow : ∀ n h, μ₀ ≤ μ n h) {W₀ : ℝ} (hW₀ : 0 < W₀) :
    AdmissibleT R W₀ (fun n h => μ n h * optWealthT R xs μ W₀ n h) xs ∧
      Summable (utilSeries tr β (crraUtil ρ) fun n h => μ n h * optWealthT R xs μ W₀ n h) ∧
      expectedUtility tr β (crraUtil ρ) (fun n h => μ n h * optWealthT R xs μ W₀ n h)
        = crraValue (μ 0 Fin.elim0) ρ W₀ ∧
      ∀ (c : (n : ℕ) → (Fin n → S) → ℝ) (x : (n : ℕ) → (Fin n → S) → Fin N → ℝ),
        AdmissibleT R W₀ c x → Summable (utilSeries tr β (crraUtil ρ) c) →
        expectedUtility tr β (crraUtil ρ) c ≤ crraValue (μ 0 Fin.elim0) ρ W₀ := by
  have := nonempty_of_tree tr
  have hJ := nodeGrowth_nonneg tr hβ.le R hsol
  set Ws := optWealthT R xs μ W₀ with hWs
  set cs := fun n (h : Fin n → S) => μ n h * Ws n h with hcs
  have hWpos := optWealthT_pos R (fun n h s => (hsol.2.1 n h).2 s)
    (fun n h => (hsol.1 n h).2) hW₀
  have hadm : AdmissibleT R W₀ cs xs := by
    refine ⟨fun n h => mul_pos (hsol.1 n h).1 (hWpos n h), fun n h => ?_,
      fun n h => (hsol.2.1 n h).1⟩
    rw [hcs, wealthT_optPlan]
    have := hWpos n h
    nlinarith [(hsol.1 n h).2]
  -- upper bound for every admissible plan
  have hupper : ∀ (c : (n : ℕ) → (Fin n → S) → ℝ) (x : (n : ℕ) → (Fin n → S) → Fin N → ℝ),
      AdmissibleT R W₀ c x → Summable (utilSeries tr β (crraUtil ρ) c) →
      expectedUtility tr β (crraUtil ρ) c ≤ crraValue (μ 0 Fin.elim0) ρ W₀ := by
    intro c x hadm' hU
    have hstep : ∀ n h, crraUtil ρ (c n h) + β * ∑ s, tr.q n h s
        * (fun n h => crraValue (μ n h) ρ (wealthT R W₀ c x n h)) (n + 1) (Fin.snoc h s)
        ≤ (fun n h => crraValue (μ n h) ρ (wealthT R W₀ c x n h)) n h := by
      intro n h
      obtain ⟨hlt, hxn⟩ := admissibleT_step R W₀ hadm' n h
      simp only [wealthT_snoc]
      exact bellman_node_le tr hρ hρ1 R hsol hJ n h (hadm'.1 n h) hlt hxn
    have htel := telescope_tree_le tr hβ.le (crraUtil ρ) c
      (fun n h => crraValue (μ n h) ρ (wealthT R W₀ c x n h)) hstep
    have hT := transversality_tree tr hβ hρ hρ1 R hsol hμ₀ hlow W₀ hadm' hU
    have h2 := (tendsto_const_nhds (x := crraValue (μ 0 Fin.elim0) ρ W₀)).sub hT
    rw [sub_zero] at h2
    exact le_of_tendsto_of_tendsto' hU.hasSum.tendsto_sum_nat h2 fun n => by
      have := htel n
      beta_reduce at this
      rw [show wealthT R W₀ c x 0 Fin.elim0 = W₀ from rfl] at this
      linarith
  -- attainment
  set v := fun n (h : Fin n → S) => crraValue (μ n h) ρ (Ws n h) with hv
  have hWsnoc : ∀ n (h : Fin n → S) s, Ws (n + 1) (Fin.snoc h s)
      = (1 + portRet (R n h) (xs n h) s) * ((1 - μ n h) * Ws n h) := by
    intro n h s; simp only [hWs, optWealthT, Fin.init_snoc, Fin.snoc_last]
  have hstepEq : ∀ n h, crraUtil ρ (cs n h) + β * ∑ s, tr.q n h s * v (n + 1) (Fin.snoc h s)
      = v n h := by
    intro n h
    simp only [hv, hcs, hWsnoc]
    exact (bellman_node_eq tr hρ R hsol hJ n h (hWpos n h)).2
  have htel := telescope_tree_eq tr β (crraUtil ρ) cs v hstepEq
  set T := fun n => β ^ n * ∑ h, tr.histProb h * v n h with hT
  have hμ₀1 : μ₀ < 1 := lt_of_le_of_lt (hlow 0 Fin.elim0) (hsol.1 0 Fin.elim0).2
  have hTrec : ∀ n, T (n + 1) = β ^ n * ∑ h, tr.histProb h * ((1 - μ n h) * v n h) := by
    intro n
    simp only [hT]
    rw [sum_succ_tree, pow_succ, mul_assoc]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    have := (bellman_node_eq tr hρ R hsol hJ n h (hWpos n h)).1
    simp only [hv, hWsnoc]
    rw [← this]; ring
  have hTlim : Tendsto T atTop (𝓝 0) := by
    have hθ0 : 0 ≤ 1 - μ₀ := by linarith
    have hθ1 : 1 - μ₀ < 1 := by linarith
    have hgeo := tendsto_pow_atTop_nhds_zero_of_lt_one hθ0 hθ1
    rcases lt_or_gt_of_ne hρ1 with hlt | hgt
    · have hvnn : ∀ n h, 0 ≤ v n h := fun n h => mul_nonneg
        (Real.rpow_nonneg (hsol.1 n h).1.le _)
        (div_nonneg (Real.rpow_nonneg (hWpos n h).le _) (by linarith))
      have hT0 : ∀ n, 0 ≤ T n := fun n => mul_nonneg (pow_nonneg hβ.le n)
        (Finset.sum_nonneg fun h _ => mul_nonneg (tr.histProb_nonneg h) (hvnn n h))
      have hgeoT : ∀ n, T n ≤ (1 - μ₀) ^ n * T 0 := by
        intro n
        induction n with
        | zero => simp
        | succ n ih =>
          have hr : T (n + 1) ≤ (1 - μ₀) * T n := by
            rw [hTrec]
            simp only [hT, Finset.mul_sum]
            refine Finset.sum_le_sum fun h _ => ?_
            have := mul_le_mul_of_nonneg_right (by linarith [hlow n h] :
              1 - μ n h ≤ 1 - μ₀) (hvnn n h)
            have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left this
              (tr.histProb_nonneg h)) (pow_nonneg hβ.le n)
            linarith
          calc T (n + 1) ≤ (1 - μ₀) * T n := hr
            _ ≤ (1 - μ₀) * ((1 - μ₀) ^ n * T 0) := mul_le_mul_of_nonneg_left ih hθ0
            _ = (1 - μ₀) ^ (n + 1) * T 0 := by ring
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (by simpa using hgeo.mul_const (T 0)) hT0 hgeoT
    · have hvnp : ∀ n h, v n h ≤ 0 := fun n h => mul_nonpos_of_nonneg_of_nonpos
        (Real.rpow_nonneg (hsol.1 n h).1.le _)
        (div_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg (hWpos n h).le _) (by linarith))
      have hT0 : ∀ n, T n ≤ 0 := fun n => mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hβ.le n)
        (Finset.sum_nonpos fun h _ => mul_nonpos_of_nonneg_of_nonpos (tr.histProb_nonneg h)
          (hvnp n h))
      have hgeoT : ∀ n, (1 - μ₀) ^ n * T 0 ≤ T n := by
        intro n
        induction n with
        | zero => simp
        | succ n ih =>
          have hr : (1 - μ₀) * T n ≤ T (n + 1) := by
            rw [hTrec]
            simp only [hT, Finset.mul_sum]
            refine Finset.sum_le_sum fun h _ => ?_
            have := mul_le_mul_of_nonpos_right (by linarith [hlow n h] :
              1 - μ n h ≤ 1 - μ₀) (hvnp n h)
            have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left this
              (tr.histProb_nonneg h)) (pow_nonneg hβ.le n)
            linarith
          calc (1 - μ₀) ^ (n + 1) * T 0 = (1 - μ₀) * ((1 - μ₀) ^ n * T 0) := by ring
            _ ≤ (1 - μ₀) * T n := mul_le_mul_of_nonneg_left ih hθ0
            _ ≤ T (n + 1) := hr
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le (by simpa using hgeo.mul_const (T 0))
        tendsto_const_nhds hgeoT hT0
  have hpart : Tendsto (fun n => ∑ k ∈ range n, utilSeries tr β (crraUtil ρ) cs k) atTop
      (𝓝 (crraValue (μ 0 Fin.elim0) ρ W₀)) := by
    have e : ∀ n, ∑ k ∈ range n, utilSeries tr β (crraUtil ρ) cs k
        = v 0 Fin.elim0 - T n := fun n => by linarith [htel n]
    have hv0 : v 0 Fin.elim0 = crraValue (μ 0 Fin.elim0) ρ W₀ := rfl
    simp only [e]
    simpa [hv0] using (tendsto_const_nhds (x := v 0 Fin.elim0)).sub hTlim
  have hsumm : Summable (utilSeries tr β (crraUtil ρ) cs) := by
    have hterm : ∀ k h, crraUtil ρ (cs k h) = (cs k h) ^ (1 - ρ) / (1 - ρ) := fun _ _ => rfl
    rcases lt_or_gt_of_ne hρ1 with hlt | hgt
    · have hnn : ∀ k, 0 ≤ utilSeries tr β (crraUtil ρ) cs k := fun k =>
        mul_nonneg (pow_nonneg hβ.le k) (Finset.sum_nonneg fun h _ =>
          mul_nonneg (tr.histProb_nonneg h) (by
            rw [hterm]; exact div_nonneg (Real.rpow_nonneg (hadm.1 k h).le _) (by linarith)))
      refine summable_of_sum_range_le (c := v 0 Fin.elim0) hnn fun n => ?_
      have hTn : 0 ≤ T n := mul_nonneg (pow_nonneg hβ.le n) (Finset.sum_nonneg fun h _ =>
        mul_nonneg (tr.histProb_nonneg h) (mul_nonneg (Real.rpow_nonneg (hsol.1 n h).1.le _)
          (div_nonneg (Real.rpow_nonneg (hWpos n h).le _) (by linarith))))
      linarith [htel n]
    · have hnn : ∀ k, 0 ≤ -utilSeries tr β (crraUtil ρ) cs k := fun k => by
        have : utilSeries tr β (crraUtil ρ) cs k ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hβ.le k) (Finset.sum_nonpos fun h _ =>
            mul_nonpos_of_nonneg_of_nonpos (tr.histProb_nonneg h) (by
              rw [hterm]
              exact div_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg (hadm.1 k h).le _)
                (by linarith)))
        linarith
      have hTn : ∀ n, T n ≤ 0 := fun n => mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hβ.le n)
        (Finset.sum_nonpos fun h _ => mul_nonpos_of_nonneg_of_nonpos (tr.histProb_nonneg h)
          (mul_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg (hsol.1 n h).1.le _)
            (div_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg (hWpos n h).le _)
              (by linarith))))
      have := summable_of_sum_range_le (c := -v 0 Fin.elim0) hnn fun n => by
        rw [Finset.sum_neg_distrib]
        have h1 := hTn n
        simp only [hT] at h1
        linarith [htel n]
      simpa using this.neg
  exact ⟨hadm, hsumm, tendsto_nhds_unique hsumm.hasSum.tendsto_sum_nat hpart, hupper⟩

/-- The verification theorem with history-dependent returns from primitives, O&R Supplement A,
p. 744. On an event tree with positive one-step probabilities, with no arbitrage and some
feasible portfolio at every history, and under the uniform growth condition (the one-period
optimal growth factor `βE_t(1 + r°)^{1−ρ}` is at most `G < 1` at every history), a solution
`(μ, x)` of the recursion `μ_t = (1 + [βE_t{(1 + r°_{t+1})^{1−ρ} μ_{t+1}^{−ρ}}]^{1/ρ})^{−1}`
exists, obtained as the limit of backward iterations, with `μ_t ≥ 1 − G^{1/ρ}`; the policy
`C = μ_t W` with portfolios `x_t(h)` attains `V_1(W₀) = μ_1^{−ρ}W₀^{1−ρ}/(1−ρ)`, and no
admissible plan does better. -/
theorem verification_varying_returns (tr : EventTree.Tree S) (hq : ∀ n h s, 0 < tr.q n h s)
    {β ρ : ℝ} (hβ : 0 < β) (hρ : 0 < ρ) (hρ1 : ρ ≠ 1)
    (R : (n : ℕ) → (Fin n → S) → Fin N → S → ℝ) (k : Fin N) (hNA : ∀ n h, NoArbitrage (R n h))
    (hF : ∀ n h, ∃ x₀, PortFeasible (R n h) x₀) {G : ℝ} (hG0 : 0 ≤ G) (hG1 : G < 1)
    (hG : ∀ n h x, PortFeasible (R n h) x → (∀ x', PortFeasible (R n h) x' →
      portObj (nodeSpace tr n h) ρ (R n h) x' ≤ portObj (nodeSpace tr n h) ρ (R n h) x) →
      growthFactor (nodeSpace tr n h) β ρ (R n h) x ≤ G) {W₀ : ℝ} (hW₀ : 0 < W₀) :
    ∃ μ xs, SolvesShareRecursion tr β ρ R μ xs ∧ (∀ n h, 1 - G ^ (1 / ρ) ≤ μ n h) ∧
      (∀ n h, Tendsto (fun m => iterA tr β ρ R m n h) atTop (𝓝 (μ n h ^ (-ρ)))) ∧
      AdmissibleT R W₀ (fun n h => μ n h * optWealthT R xs μ W₀ n h) xs ∧
      Summable (utilSeries tr β (crraUtil ρ) fun n h => μ n h * optWealthT R xs μ W₀ n h) ∧
      expectedUtility tr β (crraUtil ρ) (fun n h => μ n h * optWealthT R xs μ W₀ n h)
        = crraValue (μ 0 Fin.elim0) ρ W₀ ∧
      ∀ (c : (n : ℕ) → (Fin n → S) → ℝ) (x : (n : ℕ) → (Fin n → S) → Fin N → ℝ),
        AdmissibleT R W₀ c x → Summable (utilSeries tr β (crraUtil ρ) c) →
        expectedUtility tr β (crraUtil ρ) c ≤ crraValue (μ 0 Fin.elim0) ρ W₀ := by
  obtain ⟨μ, xs, hsol, hlow, hlim⟩ :=
    exists_share_recursion_solution tr hq hβ hρ hρ1 R k hNA hF hG0 hG1 hG
  have hμ₀ : 0 < 1 - G ^ (1 / ρ) := by
    linarith [Real.rpow_lt_one hG0 hG1 (one_div_pos.mpr hρ)]
  exact ⟨μ, xs, hsol, hlow, hlim, verification_tree tr hβ hρ hρ1 R hsol hμ₀ hlow hW₀⟩

/-! ### Log utility with history-dependent returns

O&R Supplement A, pp. 743–744: with log utility `μ = 1 − β` whatever the return process, and
the portfolio is chosen myopically to maximise `E_t log(1 + r°)`. -/

/-- The myopic log portfolio at the history `h` (O&R Supplement A, p. 743): a feasible
maximiser of `E_t log(1 + r°)` under the conditional probabilities at `h`, by Hilbert choice
(`myopicPort_spec` gives its optimality). -/
noncomputable def myopicPort (tr : EventTree.Tree S) (R : (n : ℕ) → (Fin n → S) → Fin N → S → ℝ)
    (n : ℕ) (h : Fin n → S) : Fin N → ℝ :=
  Classical.epsilon fun xs => PortFeasible (R n h) xs ∧ ∀ x, PortFeasible (R n h) x →
    logPortObj (nodeSpace tr n h) (R n h) x ≤ logPortObj (nodeSpace tr n h) (R n h) xs

/-- Existence of the myopic log portfolio at every history (O&R Supplement A, p. 743): under
positive one-step probabilities, no arbitrage and some feasible portfolio at `h`, the chosen
portfolio is feasible and maximises `E_t log(1 + r°)`. -/
theorem myopicPort_spec (tr : EventTree.Tree S) (hq : ∀ n h s, 0 < tr.q n h s)
    (R : (n : ℕ) → (Fin n → S) → Fin N → S → ℝ) (k : Fin N) (hNA : ∀ n h, NoArbitrage (R n h))
    (hF : ∀ n h, ∃ x₀, PortFeasible (R n h) x₀) (n : ℕ) (h : Fin n → S) :
    PortFeasible (R n h) (myopicPort tr R n h) ∧ ∀ x, PortFeasible (R n h) x →
      logPortObj (nodeSpace tr n h) (R n h) x
        ≤ logPortObj (nodeSpace tr n h) (R n h) (myopicPort tr R n h) := by
  obtain ⟨xs, hxs, hmax, -⟩ := exists_optimal_log_portfolio (nodeSpace tr n h) (R n h) k
    (hq n h) (hNA n h) (hF n h)
  exact Classical.epsilon_spec (p := fun xs => PortFeasible (R n h) xs ∧
    ∀ x, PortFeasible (R n h) x →
      logPortObj (nodeSpace tr n h) (R n h) x ≤ logPortObj (nodeSpace tr n h) (R n h) xs)
    ⟨xs, hxs, hmax⟩

/-- The optimal expected log return `g_t(h) = max E_t log(1 + r°)` at the history `h`
(O&R Supplement A, p. 743). -/
noncomputable def myopicGrowth (tr : EventTree.Tree S)
    (R : (n : ℕ) → (Fin n → S) → Fin N → S → ℝ) (n : ℕ) (h : Fin n → S) : ℝ :=
  logPortObj (nodeSpace tr n h) (R n h) (myopicPort tr R n h)

/-- The terms of the backward-summed constant of the log value function (O&R Supplement A,
p. 743): `D_0(h) = log(1 − β) + (β/(1 − β))(log β + g_t(h))` and
`D_{j+1}(h) = βΣ_s q(s|h) D_j(h, s)`, so `D_j(h) = β^j E_h[D_0 at date t + j]`. -/
noncomputable def logSeriesTerm (tr : EventTree.Tree S) (β : ℝ)
    (R : (n : ℕ) → (Fin n → S) → Fin N → S → ℝ) : ℕ → (n : ℕ) → (Fin n → S) → ℝ
  | 0 => fun n h => Real.log (1 - β) + β / (1 - β) * (Real.log β + myopicGrowth tr R n h)
  | j + 1 => fun n h => β * ∑ s, tr.q n h s * logSeriesTerm tr β R j (n + 1) (Fin.snoc h s)

/-- The constant `K_t(h) = Σ_j D_j(h)` of the log value function with history-dependent returns
(O&R Supplement A, p. 743). -/
noncomputable def logConstT (tr : EventTree.Tree S) (β : ℝ)
    (R : (n : ℕ) → (Fin n → S) → Fin N → S → ℝ) (n : ℕ) (h : Fin n → S) : ℝ :=
  ∑' j, logSeriesTerm tr β R j n h

/-- The log value function `V_t(h, W) = log W/(1 − β) + K_t(h)` (O&R Supplement A, p. 743). -/
noncomputable def logValueT (tr : EventTree.Tree S) (β : ℝ)
    (R : (n : ℕ) → (Fin n → S) → Fin N → S → ℝ) (n : ℕ) (h : Fin n → S) (W : ℝ) : ℝ :=
  Real.log W / (1 - β) + logConstT tr β R n h

/-- Geometric bound on the series terms (O&R Supplement A, p. 743): if `|g_t| ≤ M` everywhere
then `|D_j(h)| ≤ β^j C` with `C = |log(1 − β)| + (β/(1 − β))(|log β| + M)`. -/
theorem logSeriesTerm_bound (tr : EventTree.Tree S) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (R : (n : ℕ) → (Fin n → S) → Fin N → S → ℝ) {M : ℝ}
    (hM : ∀ n h, |myopicGrowth tr R n h| ≤ M) (j : ℕ) :
    ∀ n h, |logSeriesTerm tr β R j n h|
      ≤ β ^ j * (|Real.log (1 - β)| + β / (1 - β) * (|Real.log β| + M)) := by
  have hb : 0 ≤ β / (1 - β) := div_nonneg hβ0.le (by linarith)
  induction j with
  | zero =>
    intro n h
    simp only [logSeriesTerm, pow_zero, one_mul]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_of_nonneg hb]
    have h2 := abs_add_le (Real.log β) (myopicGrowth tr R n h)
    have h3 := hM n h
    nlinarith
  | succ j ih =>
    intro n h
    simp only [logSeriesTerm]
    rw [abs_mul, abs_of_pos hβ0, pow_succ]
    have : |∑ s, tr.q n h s * logSeriesTerm tr β R j (n + 1) (Fin.snoc h s)|
        ≤ β ^ j * (|Real.log (1 - β)| + β / (1 - β) * (|Real.log β| + M)) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ s, |tr.q n h s * logSeriesTerm tr β R j (n + 1) (Fin.snoc h s)|
          ≤ ∑ s, tr.q n h s * (β ^ j * (|Real.log (1 - β)| + β / (1 - β) * (|Real.log β| + M)))
            := Finset.sum_le_sum fun s _ => by
              rw [abs_mul, abs_of_nonneg (tr.q_nonneg n h s)]
              exact mul_le_mul_of_nonneg_left (ih _ _) (tr.q_nonneg n h s)
        _ = β ^ j * (|Real.log (1 - β)| + β / (1 - β) * (|Real.log β| + M)) := by
          rw [← Finset.sum_mul, tr.q_sum, one_mul]
    nlinarith

/-- The backward-summed series converges (O&R Supplement A, p. 743), under `0 < β < 1` and
uniformly bounded optimal expected log returns `|g_t| ≤ M`. -/
theorem logSeries_summable (tr : EventTree.Tree S) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (R : (n : ℕ) → (Fin n → S) → Fin N → S → ℝ) {M : ℝ}
    (hM : ∀ n h, |myopicGrowth tr R n h| ≤ M) (n : ℕ) (h : Fin n → S) :
    Summable fun j => logSeriesTerm tr β R j n h :=
  Summable.of_norm_bounded ((summable_geometric_of_lt_one hβ0.le hβ1).mul_right _)
    fun j => by rw [Real.norm_eq_abs]; exact logSeriesTerm_bound tr hβ0 hβ1 R hM j n h

/-- The constant is bounded, `|K_t(h)| ≤ C/(1 − β)` (O&R Supplement A, p. 743). -/
theorem logConstT_bound (tr : EventTree.Tree S) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (R : (n : ℕ) → (Fin n → S) → Fin N → S → ℝ) {M : ℝ}
    (hM : ∀ n h, |myopicGrowth tr R n h| ≤ M) (n : ℕ) (h : Fin n → S) :
    |logConstT tr β R n h|
      ≤ (|Real.log (1 - β)| + β / (1 - β) * (|Real.log β| + M)) / (1 - β) := by
  set Cb := |Real.log (1 - β)| + β / (1 - β) * (|Real.log β| + M)
  have hg := (hasSum_geometric_of_lt_one hβ0.le hβ1).mul_right Cb
  have hs := logSeries_summable tr hβ0 hβ1 R hM n h
  have hb := fun j => logSeriesTerm_bound tr hβ0 hβ1 R hM j n h
  have e : Cb / (1 - β) = (1 - β)⁻¹ * Cb := by ring
  rw [e, abs_le]
  unfold logConstT
  constructor
  · have := Summable.tsum_le_tsum (fun j => neg_le_of_abs_le (hb j)) hg.summable.neg hs
    rw [tsum_neg, hg.tsum_eq] at this
    linarith
  · have := Summable.tsum_le_tsum (fun j => le_of_abs_le (hb j)) hs hg.summable
    rw [hg.tsum_eq] at this
    exact this

/-- The recursion for the constant, O&R Supplement A, p. 743:
`K_t(h) = log(1 − β) + (β/(1 − β))(log β + g_t(h)) + βΣ_s q(s|h) K_{t+1}(h, s)`. -/
theorem logConstT_recursion (tr : EventTree.Tree S) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (R : (n : ℕ) → (Fin n → S) → Fin N → S → ℝ) {M : ℝ}
    (hM : ∀ n h, |myopicGrowth tr R n h| ≤ M) (n : ℕ) (h : Fin n → S) :
    logConstT tr β R n h = Real.log (1 - β) + β / (1 - β) * (Real.log β + myopicGrowth tr R n h)
      + β * ∑ s, tr.q n h s * logConstT tr β R (n + 1) (Fin.snoc h s) := by
  have hs : ∀ s, Summable fun j => tr.q n h s * logSeriesTerm tr β R j (n + 1) (Fin.snoc h s) :=
    fun s => (logSeries_summable tr hβ0 hβ1 R hM _ _).mul_left _
  rw [logConstT, (logSeries_summable tr hβ0 hβ1 R hM n h).tsum_eq_zero_add]
  congr 1
  change ∑' j, β * ∑ s, tr.q n h s * logSeriesTerm tr β R j (n + 1) (Fin.snoc h s) = _
  rw [tsum_mul_left, Summable.tsum_finsetSum fun s _ => hs s]
  congr 1
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [tsum_mul_left]
  rfl

/-- The log consumption split (O&R Supplement A, p. 743): for `0 < β < 1`, `0 < C < W` and
expected log portfolio returns `G′ ≤ G`,
`log C + (β/(1 − β))(G′ + log(W − C)) ≤ log((1 − β)W) + (β/(1 − β))(G + log(βW))`. -/
theorem log_split_le {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {W C G G' : ℝ} (hC : 0 < C)
    (hCW : C < W) (hG : G' ≤ G) :
    Real.log C + β / (1 - β) * (G' + Real.log (W - C))
      ≤ Real.log ((1 - β) * W) + β / (1 - β) * (G + Real.log (β * W)) := by
  have h1 : 0 < 1 - β := by linarith
  have hW : 0 < W := hC.trans hCW
  have hD : 0 < W - C := by linarith
  have hc : 0 ≤ β / (1 - β) := div_nonneg hβ0.le h1.le
  have t1 := log_tangent (mul_pos h1 hW) hC
  have t2 := log_tangent (mul_pos hβ0 hW) hD
  have e1 : β / (1 - β) * (1 / (β * W)) = 1 / ((1 - β) * W) := by field_simp
  have t2' := mul_le_mul_of_nonneg_left t2 hc
  have lin : 1 / ((1 - β) * W) * (C - (1 - β) * W)
      + β / (1 - β) * (1 / (β * W) * (W - C - β * W)) = 0 := by
    rw [← mul_assoc, e1]; ring
  nlinarith [mul_le_mul_of_nonneg_left hG hc]

/-- The log continuation value at a history (O&R Supplement A, p. 743): saving `D > 0` in a
feasible portfolio `x` gives
`βE_t V_{t+1}((1 + r°)D) = (β/(1 − β))(E_t log(1 + r°) + log D) + βE_t K_{t+1}`. -/
theorem log_node_continuation (tr : EventTree.Tree S) (β : ℝ)
    (R : (n : ℕ) → (Fin n → S) → Fin N → S → ℝ) (n : ℕ) (h : Fin n → S) {x : Fin N → ℝ}
    (hx : PortFeasible (R n h) x) {D : ℝ} (hD : 0 < D) :
    β * ∑ s, tr.q n h s * logValueT tr β R (n + 1) (Fin.snoc h s)
        ((1 + portRet (R n h) x s) * D)
      = β / (1 - β) * (logPortObj (nodeSpace tr n h) (R n h) x + Real.log D)
        + β * ∑ s, tr.q n h s * logConstT tr β R (n + 1) (Fin.snoc h s) := by
  have e : ∀ s, tr.q n h s * logValueT tr β R (n + 1) (Fin.snoc h s)
      ((1 + portRet (R n h) x s) * D) = tr.q n h s * Real.log (1 + portRet (R n h) x s) / (1 - β)
        + tr.q n h s * Real.log D / (1 - β)
        + tr.q n h s * logConstT tr β R (n + 1) (Fin.snoc h s) := by
    intro s
    rw [logValueT, Real.log_mul (hx.2 s).ne' hD.ne']
    ring
  simp only [e, Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_mul, tr.q_sum,
    logPortObj, StateSpace.expect, nodeSpace]
  ring

/-- The Bellman equation for log utility with history-dependent returns, O&R Supplement A,
p. 743: at every history, every `0 < C < W` and feasible portfolio give
`log C + βE_t V_{t+1}((1 + r°)(W − C)) ≤ V_t(W)`, with equality at `C = (1 − β)W` and the myopic
portfolio. -/
theorem bellman_log_node (tr : EventTree.Tree S) (hq : ∀ n h s, 0 < tr.q n h s) {β : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (R : (n : ℕ) → (Fin n → S) → Fin N → S → ℝ) (k : Fin N)
    (hNA : ∀ n h, NoArbitrage (R n h)) (hF : ∀ n h, ∃ x₀, PortFeasible (R n h) x₀) {M : ℝ}
    (hM : ∀ n h, |myopicGrowth tr R n h| ≤ M) (n : ℕ) (h : Fin n → S) {W : ℝ} (hW : 0 < W) :
    (∀ C x, 0 < C → C < W → PortFeasible (R n h) x →
      Real.log C + β * ∑ s, tr.q n h s * logValueT tr β R (n + 1) (Fin.snoc h s)
        ((1 + portRet (R n h) x s) * (W - C)) ≤ logValueT tr β R n h W) ∧
    Real.log ((1 - β) * W) + β * ∑ s, tr.q n h s * logValueT tr β R (n + 1) (Fin.snoc h s)
        ((1 + portRet (R n h) (myopicPort tr R n h) s) * (W - (1 - β) * W))
      = logValueT tr β R n h W := by
  have h1 : 0 < 1 - β := by linarith
  obtain ⟨hxs, hmax⟩ := myopicPort_spec tr hq R k hNA hF n h
  have hconst : Real.log ((1 - β) * W) + β / (1 - β) * (myopicGrowth tr R n h
      + Real.log (β * W)) + β * ∑ s, tr.q n h s * logConstT tr β R (n + 1) (Fin.snoc h s)
      = logValueT tr β R n h W := by
    rw [logValueT, logConstT_recursion tr hβ0 hβ1 R hM n h, Real.log_mul h1.ne' hW.ne',
      Real.log_mul hβ0.ne' hW.ne']
    field_simp
    ring
  refine ⟨fun C x hC hCW hx => ?_, ?_⟩
  · rw [log_node_continuation tr β R n h hx (by linarith), ← hconst]
    have := log_split_le hβ0 hβ1 hC hCW (hmax x hx)
    unfold myopicGrowth
    linarith
  · rw [log_node_continuation tr β R n h hxs (by nlinarith), ← hconst,
      show W - (1 - β) * W = β * W by ring]
    unfold myopicGrowth
    ring

/-- The expected log of wealth along an admissible plan grows by at most `M` per period when
`|g_t| ≤ M` (O&R Supplement A, p. 743). -/
theorem expect_log_wealthT_le (tr : EventTree.Tree S) (hq : ∀ n h s, 0 < tr.q n h s)
    (R : (n : ℕ) → (Fin n → S) → Fin N → S → ℝ) (k : Fin N) (hNA : ∀ n h, NoArbitrage (R n h))
    (hF : ∀ n h, ∃ x₀, PortFeasible (R n h) x₀) {M : ℝ}
    (hM : ∀ n h, |myopicGrowth tr R n h| ≤ M) (W₀ : ℝ) {c : (n : ℕ) → (Fin n → S) → ℝ}
    {x : (n : ℕ) → (Fin n → S) → Fin N → ℝ} (hadm : AdmissibleT R W₀ c x) (n : ℕ) :
    ∑ h, tr.histProb h * Real.log (wealthT R W₀ c x n h) ≤ Real.log W₀ + n * M := by
  have := nonempty_of_tree tr
  induction n with
  | zero =>
    simp only [Fintype.sum_unique, tr.histProb_zero, one_mul, CharP.cast_eq_zero, zero_mul,
      add_zero]
    rfl
  | succ n ih =>
    rw [sum_succ_tree]
    simp only [wealthT_snoc]
    have hnode : ∀ h, tr.histProb h * ∑ s, tr.q n h s * Real.log
        ((1 + portRet (R n h) (x n h) s) * (wealthT R W₀ c x n h - c n h))
        ≤ tr.histProb h * (M + Real.log (wealthT R W₀ c x n h)) := by
      intro h
      obtain ⟨hlt, hxn⟩ := admissibleT_step R W₀ hadm n h
      have hD : 0 < wealthT R W₀ c x n h - c n h := by linarith
      have e : ∑ s, tr.q n h s * Real.log ((1 + portRet (R n h) (x n h) s)
          * (wealthT R W₀ c x n h - c n h))
          = logPortObj (nodeSpace tr n h) (R n h) (x n h)
            + Real.log (wealthT R W₀ c x n h - c n h) := by
        simp only [logPortObj, StateSpace.expect, nodeSpace,
          Real.log_mul (hxn.2 _).ne' hD.ne', mul_add, Finset.sum_add_distrib,
          ← Finset.sum_mul, tr.q_sum, one_mul]
      rw [e]
      refine mul_le_mul_of_nonneg_left ?_ (tr.histProb_nonneg h)
      have h1 := (myopicPort_spec tr hq R k hNA hF n h).2 _ hxn
      have h2 := Real.log_le_log hD (by linarith [hadm.1 n h] :
        wealthT R W₀ c x n h - c n h ≤ wealthT R W₀ c x n h)
      have h3 := le_of_abs_le (hM n h)
      unfold myopicGrowth at h3
      linarith
    have hs := Finset.sum_le_sum fun h (_ : h ∈ univ) => hnode h
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, tr.histProb_sum_eq_one,
      one_mul] at hs
    push_cast
    linarith

/-- `β^t E_t K_t` is bounded in absolute value by `β^t C/(1 − β)` (O&R Supplement A,
p. 743). -/
theorem abs_expect_logConstT_le (tr : EventTree.Tree S) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (R : (n : ℕ) → (Fin n → S) → Fin N → S → ℝ) {M : ℝ}
    (hM : ∀ n h, |myopicGrowth tr R n h| ≤ M) (n : ℕ) :
    |∑ h, tr.histProb h * logConstT tr β R n h|
      ≤ (|Real.log (1 - β)| + β / (1 - β) * (|Real.log β| + M)) / (1 - β) := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ h, |tr.histProb h * logConstT tr β R n h|
      ≤ ∑ h, tr.histProb h * ((|Real.log (1 - β)| + β / (1 - β) * (|Real.log β| + M))
        / (1 - β)) := Finset.sum_le_sum fun h _ => by
          rw [abs_mul, abs_of_nonneg (tr.histProb_nonneg h)]
          exact mul_le_mul_of_nonneg_left (logConstT_bound tr hβ0 hβ1 R hM n h)
            (tr.histProb_nonneg h)
    _ = _ := by rw [← Finset.sum_mul, tr.histProb_sum_eq_one, one_mul]

/-- The transversality property for log utility with history-dependent returns, O&R
Supplement A, p. 743 (proved, not assumed): for every admissible plan with convergent utility
series, `β^t E V_t(W_t) → 0`. -/
theorem transversality_log_tree (tr : EventTree.Tree S) (hq : ∀ n h s, 0 < tr.q n h s)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (R : (n : ℕ) → (Fin n → S) → Fin N → S → ℝ)
    (k : Fin N) (hNA : ∀ n h, NoArbitrage (R n h)) (hF : ∀ n h, ∃ x₀, PortFeasible (R n h) x₀)
    {M : ℝ} (hM : ∀ n h, |myopicGrowth tr R n h| ≤ M) (W₀ : ℝ)
    {c : (n : ℕ) → (Fin n → S) → ℝ} {x : (n : ℕ) → (Fin n → S) → Fin N → ℝ}
    (hadm : AdmissibleT R W₀ c x) (hU : Summable (utilSeries tr β Real.log c)) :
    Tendsto (fun n => β ^ n * ∑ h, tr.histProb h * logValueT tr β R n h (wealthT R W₀ c x n h))
      atTop (𝓝 0) := by
  have h1 : 0 < 1 - β := by linarith
  set Kb := (|Real.log (1 - β)| + β / (1 - β) * (|Real.log β| + M)) / (1 - β)
  have hT : ∀ n, β ^ n * ∑ h, tr.histProb h * logValueT tr β R n h (wealthT R W₀ c x n h)
      = β ^ n * (∑ h, tr.histProb h * Real.log (wealthT R W₀ c x n h)) / (1 - β)
        + β ^ n * ∑ h, tr.histProb h * logConstT tr β R n h := by
    intro n
    have e : ∑ h, tr.histProb h * logValueT tr β R n h (wealthT R W₀ c x n h)
        = (∑ h, tr.histProb h * Real.log (wealthT R W₀ c x n h)) / (1 - β)
          + ∑ h, tr.histProb h * logConstT tr β R n h := by
      rw [Finset.sum_div, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun h _ => by unfold logValueT; ring
    rw [e]; ring
  have hK := fun n => abs_le.mp (abs_expect_logConstT_le tr hβ0 hβ1 R hM n)
  have hlow : ∀ n, utilSeries tr β Real.log c n / (1 - β) - β ^ n * Kb
      ≤ β ^ n * ∑ h, tr.histProb h * logValueT tr β R n h (wealthT R W₀ c x n h) := by
    intro n
    rw [hT, utilSeries]
    have hl : ∑ h, tr.histProb h * Real.log (c n h)
        ≤ ∑ h, tr.histProb h * Real.log (wealthT R W₀ c x n h) :=
      Finset.sum_le_sum fun h _ => mul_le_mul_of_nonneg_left
        (Real.log_le_log (hadm.1 n h) (hadm.2.1 n h)) (tr.histProb_nonneg h)
    have := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hl (pow_nonneg hβ0.le n))
      h1.le
    have := mul_le_mul_of_nonneg_left (hK n).1 (pow_nonneg hβ0.le n)
    linarith
  have hup : ∀ n, β ^ n * ∑ h, tr.histProb h * logValueT tr β R n h (wealthT R W₀ c x n h)
      ≤ (Real.log W₀ / (1 - β) + Kb) * β ^ n + M / (1 - β) * (n * β ^ n) := by
    intro n
    rw [hT]
    have := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
      (expect_log_wealthT_le tr hq R k hNA hF hM W₀ hadm n) (pow_nonneg hβ0.le n)) h1.le
    have := mul_le_mul_of_nonneg_left (hK n).2 (pow_nonneg hβ0.le n)
    have e : β ^ n * (Real.log W₀ + n * M) / (1 - β) + β ^ n * Kb
        = (Real.log W₀ / (1 - β) + Kb) * β ^ n + M / (1 - β) * (n * β ^ n) := by ring
    linarith
  have hgeo := tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1
  have hlowT : Tendsto (fun n => utilSeries tr β Real.log c n / (1 - β) - β ^ n * Kb)
      atTop (𝓝 0) := by
    simpa using (hU.tendsto_atTop_zero.div_const (1 - β)).sub (hgeo.mul_const Kb)
  have hupT : Tendsto (fun n : ℕ => (Real.log W₀ / (1 - β) + Kb) * β ^ n
      + M / (1 - β) * (n * β ^ n)) atTop (𝓝 0) := by
    simpa using (hgeo.const_mul (Real.log W₀ / (1 - β) + Kb)).add
      ((tendsto_self_mul_const_pow_of_lt_one hβ0.le hβ1).const_mul (M / (1 - β)))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlowT hupT hlow hup

/-- The verification theorem for log utility with history-dependent returns, O&R Supplement A,
pp. 743–744. On an event tree with positive one-step probabilities, no arbitrage and some
feasible portfolio at every history, `0 < β < 1`, and uniformly bounded optimal expected log
returns `|max E_t log(1 + r°)| ≤ M` (the primitive condition making the backward-summed constant
converge), and `W₀ > 0`: the policy `C = (1 − β)W` (the book's `μ = 1 − β`, for any return
process) with the myopic portfolio maximising `E_t log(1 + r°)` is admissible, its utility series
converges, and it attains `V_1(W₀) = log W₀/(1 − β) + K_1`; every admissible plan with convergent
utility series achieves at most `V_1(W₀)`. -/
theorem verification_log_tree (tr : EventTree.Tree S) (hq : ∀ n h s, 0 < tr.q n h s)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (R : (n : ℕ) → (Fin n → S) → Fin N → S → ℝ)
    (k : Fin N) (hNA : ∀ n h, NoArbitrage (R n h)) (hF : ∀ n h, ∃ x₀, PortFeasible (R n h) x₀)
    {M : ℝ} (hM : ∀ n h, |myopicGrowth tr R n h| ≤ M) {W₀ : ℝ} (hW₀ : 0 < W₀) :
    AdmissibleT R W₀ (fun n h => (1 - β) * optWealthT R (myopicPort tr R) (fun _ _ => 1 - β)
        W₀ n h) (myopicPort tr R) ∧
      Summable (utilSeries tr β Real.log fun n h =>
        (1 - β) * optWealthT R (myopicPort tr R) (fun _ _ => 1 - β) W₀ n h) ∧
      expectedUtility tr β Real.log (fun n h =>
        (1 - β) * optWealthT R (myopicPort tr R) (fun _ _ => 1 - β) W₀ n h)
          = logValueT tr β R 0 Fin.elim0 W₀ ∧
      ∀ (c : (n : ℕ) → (Fin n → S) → ℝ) (x : (n : ℕ) → (Fin n → S) → Fin N → ℝ),
        AdmissibleT R W₀ c x → Summable (utilSeries tr β Real.log c) →
        expectedUtility tr β Real.log c ≤ logValueT tr β R 0 Fin.elim0 W₀ := by
  have := nonempty_of_tree tr
  have h1 : 0 < 1 - β := by linarith
  set xL := myopicPort tr R with hxL
  have hxLf : ∀ n h, PortFeasible (R n h) (xL n h) := fun n h =>
    (myopicPort_spec tr hq R k hNA hF n h).1
  set Ws := optWealthT R xL (fun _ _ => 1 - β) W₀ with hWs
  set cs := fun n (h : Fin n → S) => (1 - β) * Ws n h with hcs
  have hWpos := optWealthT_pos R (fun n h s => (hxLf n h).2 s)
    (fun _ _ => (by linarith : 1 - β < 1)) hW₀
  have hadm : AdmissibleT R W₀ cs xL := by
    refine ⟨fun n h => mul_pos h1 (hWpos n h), fun n h => ?_, fun n h => (hxLf n h).1⟩
    rw [hcs, wealthT_optPlan]
    have := hWpos n h
    nlinarith
  set Kb := (|Real.log (1 - β)| + β / (1 - β) * (|Real.log β| + M)) / (1 - β)
  have hK := fun n => abs_expect_logConstT_le tr hβ0 hβ1 R hM n
  -- upper bound
  have hupper : ∀ (c : (n : ℕ) → (Fin n → S) → ℝ) (x : (n : ℕ) → (Fin n → S) → Fin N → ℝ),
      AdmissibleT R W₀ c x → Summable (utilSeries tr β Real.log c) →
      expectedUtility tr β Real.log c ≤ logValueT tr β R 0 Fin.elim0 W₀ := by
    intro c x hadm' hU
    have hstep : ∀ n h, Real.log (c n h) + β * ∑ s, tr.q n h s
        * (fun n h => logValueT tr β R n h (wealthT R W₀ c x n h)) (n + 1) (Fin.snoc h s)
        ≤ (fun n h => logValueT tr β R n h (wealthT R W₀ c x n h)) n h := by
      intro n h
      obtain ⟨hlt, hxn⟩ := admissibleT_step R W₀ hadm' n h
      simp only [wealthT_snoc]
      exact (bellman_log_node tr hq hβ0 hβ1 R k hNA hF hM n h
        (lt_of_lt_of_le (hadm'.1 n h) (hadm'.2.1 n h))).1 _ _ (hadm'.1 n h) hlt hxn
    have htel := telescope_tree_le tr hβ0.le Real.log c
      (fun n h => logValueT tr β R n h (wealthT R W₀ c x n h)) hstep
    have hT := transversality_log_tree tr hq hβ0 hβ1 R k hNA hF hM W₀ hadm' hU
    have h2 := (tendsto_const_nhds (x := logValueT tr β R 0 Fin.elim0 W₀)).sub hT
    rw [sub_zero] at h2
    exact le_of_tendsto_of_tendsto' hU.hasSum.tendsto_sum_nat h2 fun n => by
      have := htel n
      beta_reduce at this
      rw [show wealthT R W₀ c x 0 Fin.elim0 = W₀ from rfl] at this
      linarith
  -- attainment
  have hWsnoc : ∀ n (h : Fin n → S) s, Ws (n + 1) (Fin.snoc h s)
      = (1 + portRet (R n h) (xL n h) s) * (Ws n h - (1 - β) * Ws n h) := by
    intro n h s
    simp only [hWs, optWealthT, Fin.init_snoc, Fin.snoc_last]
    ring
  set v := fun n (h : Fin n → S) => logValueT tr β R n h (Ws n h) with hv
  have hstepEq : ∀ n h, Real.log (cs n h) + β * ∑ s, tr.q n h s * v (n + 1) (Fin.snoc h s)
      = v n h := by
    intro n h
    simp only [hv, hcs, hWsnoc]
    exact (bellman_log_node tr hq hβ0 hβ1 R k hNA hF hM n h (hWpos n h)).2
  have htel := telescope_tree_eq tr β Real.log cs v hstepEq
  -- expected log of optimal wealth
  set L := fun n => ∑ h, tr.histProb h * Real.log (Ws n h) with hL
  have hLb : ∀ n, |L n| ≤ |Real.log W₀| + n * (|Real.log β| + M) := by
    intro n
    induction n with
    | zero =>
      simp only [hL, Fintype.sum_unique, tr.histProb_zero, one_mul, CharP.cast_eq_zero,
        zero_mul, add_zero]
      rfl
    | succ n ih =>
      have e : L (n + 1) = ∑ h, tr.histProb h * myopicGrowth tr R n h + Real.log β + L n := by
        simp only [hL]
        rw [sum_succ_tree]
        have e3 : ∀ h s, Real.log (Ws (n + 1) (Fin.snoc h s))
            = Real.log (1 + portRet (R n h) (xL n h) s) + Real.log β + Real.log (Ws n h) := by
          intro h s
          rw [hWsnoc, show Ws n h - (1 - β) * Ws n h = β * Ws n h by ring,
            Real.log_mul ((hxLf n h).2 s).ne' (mul_pos hβ0 (hWpos n h)).ne',
            Real.log_mul hβ0.ne' (hWpos n h).ne']
          ring
        have e4 : ∀ h, ∑ s, tr.q n h s * Real.log (Ws (n + 1) (Fin.snoc h s))
            = myopicGrowth tr R n h + Real.log β + Real.log (Ws n h) := by
          intro h
          simp only [e3, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, tr.q_sum, one_mul]
          rfl
        have e2 : ∀ h, tr.histProb h * ∑ s, tr.q n h s * Real.log (Ws (n + 1) (Fin.snoc h s))
            = tr.histProb h * myopicGrowth tr R n h + tr.histProb h * Real.log β
              + tr.histProb h * Real.log (Ws n h) := by
          intro h; rw [e4]; ring
        simp only [e2, Finset.sum_add_distrib, ← Finset.sum_mul, tr.histProb_sum_eq_one,
          one_mul]
      have hg : |∑ h, tr.histProb h * myopicGrowth tr R n h| ≤ M := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        calc ∑ h, |tr.histProb h * myopicGrowth tr R n h| ≤ ∑ h, tr.histProb h * M :=
              Finset.sum_le_sum fun h _ => by
                rw [abs_mul, abs_of_nonneg (tr.histProb_nonneg h)]
                exact mul_le_mul_of_nonneg_left (hM n h) (tr.histProb_nonneg h)
          _ = M := by rw [← Finset.sum_mul, tr.histProb_sum_eq_one, one_mul]
      rw [e]
      have := abs_add_le (∑ h, tr.histProb h * myopicGrowth tr R n h + Real.log β) (L n)
      have := abs_add_le (∑ h, tr.histProb h * myopicGrowth tr R n h) (Real.log β)
      push_cast
      linarith
  have hMn : 0 ≤ M := (abs_nonneg _).trans (hM 0 Fin.elim0)
  -- the utility terms are dominated by a summable sequence
  have hutil : ∀ n, utilSeries tr β Real.log cs n = β ^ n * (Real.log (1 - β) + L n) := by
    intro n
    have e : ∀ h, Real.log ((1 - β) * Ws n h) = Real.log (1 - β) + Real.log (Ws n h) :=
      fun h => Real.log_mul h1.ne' (hWpos n h).ne'
    simp only [utilSeries, hcs, hL, e, mul_add,
      Finset.sum_add_distrib, ← Finset.sum_mul, tr.histProb_sum_eq_one, one_mul]
  have hnorm : ‖β‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos hβ0]; exact hβ1
  have hdom : Summable fun n : ℕ => (|Real.log (1 - β)| + |Real.log W₀|) * β ^ n
      + (|Real.log β| + M) * (n * β ^ n) :=
    ((summable_geometric_of_lt_one hβ0.le hβ1).mul_left _).add
      ((hasSum_coe_mul_geometric_of_norm_lt_one hnorm).summable.mul_left _)
  have hsumm : Summable (utilSeries tr β Real.log cs) := by
    refine Summable.of_norm_bounded hdom fun n => ?_
    rw [hutil, Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0.le n)]
    have h2 := abs_add_le (Real.log (1 - β)) (L n)
    have h3 := hLb n
    have hb := pow_nonneg hβ0.le n
    have h4 : |Real.log (1 - β) + L n| ≤ |Real.log (1 - β)| + |Real.log W₀|
        + n * (|Real.log β| + M) := by linarith
    have h5 := mul_le_mul_of_nonneg_left h4 hb
    nlinarith
  -- the remainder vanishes
  have hTlim : Tendsto (fun n => β ^ n * ∑ h, tr.histProb h * v n h) atTop (𝓝 0) := by
    have hbound : ∀ n, ‖β ^ n * ∑ h, tr.histProb h * v n h‖
        ≤ (|Real.log W₀| / (1 - β) + Kb) * β ^ n
          + (|Real.log β| + M) / (1 - β) * (n * β ^ n) := by
      intro n
      have e : ∑ h, tr.histProb h * v n h
          = L n / (1 - β) + ∑ h, tr.histProb h * logConstT tr β R n h := by
        simp only [hv, hL]
        rw [Finset.sum_div, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun h _ => by unfold logValueT; ring
      rw [e, Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0.le n)]
      have hLd : |L n / (1 - β)| ≤ (|Real.log W₀| + n * (|Real.log β| + M)) / (1 - β) := by
        rw [abs_div, abs_of_pos h1]; exact div_le_div_of_nonneg_right (hLb n) h1.le
      have ha := abs_add_le (L n / (1 - β)) (∑ h, tr.histProb h * logConstT tr β R n h)
      have hb := pow_nonneg hβ0.le n
      have hsum : |L n / (1 - β) + ∑ h, tr.histProb h * logConstT tr β R n h|
          ≤ (|Real.log W₀| + n * (|Real.log β| + M)) / (1 - β) + Kb := by
        linarith [hK n]
      have := mul_le_mul_of_nonneg_left hsum hb
      have e2 : β ^ n * ((|Real.log W₀| + n * (|Real.log β| + M)) / (1 - β) + Kb)
          = (|Real.log W₀| / (1 - β) + Kb) * β ^ n
            + (|Real.log β| + M) / (1 - β) * (n * β ^ n) := by ring
      linarith
    have hgeo := tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1
    refine squeeze_zero_norm hbound ?_
    simpa using (hgeo.const_mul (|Real.log W₀| / (1 - β) + Kb)).add
      ((tendsto_self_mul_const_pow_of_lt_one hβ0.le hβ1).const_mul ((|Real.log β| + M) / (1 - β)))
  have hpart : Tendsto (fun n => ∑ k ∈ range n, utilSeries tr β Real.log cs k) atTop
      (𝓝 (logValueT tr β R 0 Fin.elim0 W₀)) := by
    have e : ∀ n, ∑ k ∈ range n, utilSeries tr β Real.log cs k
        = v 0 Fin.elim0 - β ^ n * ∑ h, tr.histProb h * v n h := fun n => by linarith [htel n]
    have hv0 : v 0 Fin.elim0 = logValueT tr β R 0 Fin.elim0 W₀ := rfl
    rw [← hv0]
    simp only [e]
    simpa using (tendsto_const_nhds (x := v 0 Fin.elim0)).sub hTlim
  exact ⟨hadm, hsumm, tendsto_nhds_unique hsumm.hasSum.tendsto_sum_nat hpart, hupper⟩

end ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Infinite-horizon consumption-based asset pricing on an event tree

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §5.4.3
(pp. 315–317), Chapter 5 Exercise 3(a) (pp. 345–346) and Exercise 6 (p. 347).

This module generalises the deterministic `AssetPricing.price_eq_present_value` /
`price_crra_world_output` and the truncated Markov results of `OLGRiskSharing` to a genuinely
stochastic, infinite-horizon economy.

**Uncertainty.** Histories are those of `EventTree` (`h : Fin n → S`, date `t = n + 1`), with
the tree's one-step conditional probabilities `q n h s`. A `TreeProcess` assigns a number to
every history, and `condE tr f k` is the `k`-step conditional expectation `E_t[f_{t+k}]`,
defined one step at a time; we prove the law of iterated expectations and that `condE` is
the sum over continuations weighted by `Tree.condProb` (`condE_eq_sum_condProb`); at the
root it is the sum over histories weighted by `Tree.histProb` (`condE_root_eq_sum_histProb`).

**(57)–(59).** From the Euler equation (57) at every history we prove the `K`-step identity
(price = `K` discounted expected dividends + `β^K` discounted expected price), and under the
book's no-bubble condition the price is the limit of the present-value partial sums (59)
(a genuine `HasSum` when dividends are nonnegative). Conversely, if the series converges at
every history it solves (57); every solution is the series plus a bubble `b` with
`b_t = βE_t[b_{t+1}]`; the price equals the series iff the no-bubble condition holds; and
without that condition prices are not unique (deterministic bubbles `c/β^{t−1}`). The
no-bubble condition is *derived* when `u′(C)V` is bounded and `0 ≤ β < 1`; with `u′(C)Y`
bounded the series converges (proved) and gives the unique bounded price.

**(60)–(61).** Each term splits into a riskless-discounted expectation plus a conditional
covariance with the marginal rate of substitution; `R_{t,s}` is the price of a riskless
discount bond (footnote 44). With CRRA utility and `C = μY^W` the marginal rate of
substitution is `(Y^W_s/Y^W_t)^{−ρ}` (61), and for bounded prices with `Y^W` bounded away
from zero no no-bubble hypothesis is needed. The constant share `C = μY^W` is also derived
from all countries' complete-markets first-order conditions and market clearing
(`price_crra_world_output_derived`).

**Exercise 6 (Lucas 1982).** (a) the finance constraint, feasibility of one-period
portfolio perturbations and the three Euler equations as first-order conditions;
(b) the no-trade equilibrium with `C_X = X/2`, `C_Y = Y/2`, `p = u_Y/u_X`, market clearing
and constant wealth shares; the no-trade plan is optimal over all admissible infinite plans
(concavity plus a transversality property proved from bounded holdings), and with strictly
concave `u` every equilibrium allocation is `(X/2, Y/2)`; (c) on a finite Markov chain
with `β < 1`, the claim prices are the (convergent) expected present values and the
unique stationary — and unique bounded history-dependent — solutions of their Euler
equations; (d) riskless and own-rates of interest, and multi-period bond prices.

**Exercise 3(a).** Quadratic utility discounted at `(1 + r)^{−1}`: the two-period
certainty-equivalent `C₁`, and over an infinite horizon on the tree the permanent-income
rule `C_t = [r/(1 + r)][(1 + r)B_t + Σ_k (1 + r)^{−k}E_t Y_{t+k}]`, derived from the Euler
equation, the budget constraint and the transversality condition; conversely the rule
satisfies the Euler equation and the transversality condition.
-/

namespace ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing

open Finset Filter Topology


variable {S : Type} [Fintype S]

/-- A stochastic process on the event tree (O&R §5.4.3, p. 315): a real number `f n h` at
every date-`(n + 1)` history `h : Fin n → S`. -/
abbrev TreeProcess (S : Type) : Type := (n : ℕ) → (Fin n → S) → ℝ

/-- The `k`-step conditional expectation `E_t[f_{t+k}]` on the event tree (O&R §5.4.3,
p. 316): at the history `h` of `n` events, average `f` over the continuations of `h` by `k`
further events, one step at a time, with the tree's one-step conditional probabilities
`q n h s = π(h, s | h)`. -/
noncomputable def condE (tr : EventTree.Tree S) (f : TreeProcess S) : ℕ → TreeProcess S
  | 0 => f
  | k + 1 => fun n h => ∑ s, tr.q n h s * condE tr f k (n + 1) (Fin.snoc h s)

namespace condE

variable (tr : EventTree.Tree S)

/-- `E_t[f_t] = f_t` (O&R §5.4.3, p. 316). -/
theorem zero_eq (f : TreeProcess S) : condE tr f 0 = f := rfl

/-- The defining recursion: `E_t[f_{t+k+1}] = Σ_s π(s|h) E_{t+1}[f_{t+k+1}](h, s)`
(O&R §5.4.3, p. 316). -/
theorem succ_eq (f : TreeProcess S) (k n : ℕ) (h : Fin n → S) :
    condE tr f (k + 1) n h = ∑ s, tr.q n h s * condE tr f k (n + 1) (Fin.snoc h s) := rfl

/-- The one-step conditional expectation `E_t[f_{t+1}] = Σ_s π(s|h) f(h, s)`
(O&R (57), p. 315). -/
theorem one_eq (f : TreeProcess S) (n : ℕ) (h : Fin n → S) :
    condE tr f 1 n h = ∑ s, tr.q n h s * f (n + 1) (Fin.snoc h s) := rfl

/-- The law of iterated expectations in its one-step form, `E_t[f_{t+k+1}] =
E_t[E_{t+k}[f_{t+k+1}]]` (O&R p. 316). -/
theorem succ_eq_iter (f : TreeProcess S) (k : ℕ) :
    condE tr f (k + 1) = condE tr (condE tr f 1) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    funext n h
    rw [succ_eq, succ_eq, ih]

/-- The law of iterated expectations, `E_t[f_{t+j+k}] = E_t[E_{t+k}[f_{t+k+j}]]`
(O&R p. 316: "`E_t{E_{t+1}{X}} = E_t{X}`"). -/
theorem add_eq_iter (j : ℕ) : ∀ (f : TreeProcess S) (k : ℕ),
    condE tr f (j + k) = condE tr (condE tr f j) k := by
  induction j with
  | zero => intro f k; simp [zero_eq]
  | succ j ih =>
    intro f k
    rw [show j + 1 + k = (j + k) + 1 by omega, succ_eq_iter, ih, ← succ_eq_iter]

/-- Conditional expectation is additive (O&R p. 316). -/
theorem add_apply (f g : TreeProcess S) (k : ℕ) : ∀ (n : ℕ) (h : Fin n → S),
    condE tr (fun m x => f m x + g m x) k n h = condE tr f k n h + condE tr g k n h := by
  induction k with
  | zero => intro n h; rfl
  | succ k ih =>
    intro n h
    simp only [succ_eq, ih, mul_add, Finset.sum_add_distrib]

/-- Constants pass through conditional expectations (O&R p. 316). -/
theorem smul_apply (c : ℝ) (f : TreeProcess S) (k : ℕ) : ∀ (n : ℕ) (h : Fin n → S),
    condE tr (fun m x => c * f m x) k n h = c * condE tr f k n h := by
  induction k with
  | zero => intro n h; rfl
  | succ k ih =>
    intro n h
    simp only [succ_eq, ih, Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => by ring

/-- Conditional expectation is subtractive (O&R p. 316). -/
theorem sub_apply (f g : TreeProcess S) (k n : ℕ) (h : Fin n → S) :
    condE tr (fun m x => f m x - g m x) k n h = condE tr f k n h - condE tr g k n h := by
  have e : (fun m x => f m x - g m x) = fun m x => f m x + (-1) * g m x := by
    funext m x; ring
  rw [e, add_apply, smul_apply]
  ring

/-- The conditional expectation of a constant is that constant (O&R p. 316). -/
theorem const_apply (c : ℝ) (k : ℕ) : ∀ (n : ℕ) (h : Fin n → S),
    condE tr (fun _ _ => c) k n h = c := by
  induction k with
  | zero => intro n h; rfl
  | succ k ih =>
    intro n h
    simp only [succ_eq, ih, ← Finset.sum_mul, tr.q_sum, one_mul]

/-- Conditional expectation is monotone (O&R p. 316). -/
theorem mono_apply {f g : TreeProcess S} (hfg : ∀ n h, f n h ≤ g n h) (k : ℕ) :
    ∀ (n : ℕ) (h : Fin n → S), condE tr f k n h ≤ condE tr g k n h := by
  induction k with
  | zero => intro n h; exact hfg n h
  | succ k ih =>
    intro n h
    exact Finset.sum_le_sum fun s _ =>
      mul_le_mul_of_nonneg_left (ih _ _) (tr.q_nonneg _ _ _)

/-- A process bounded by `B` in absolute value has conditional expectations bounded by `B`
(O&R p. 316). -/
theorem abs_le_of_bound {f : TreeProcess S} {B : ℝ} (hf : ∀ n h, |f n h| ≤ B) (k n : ℕ)
    (h : Fin n → S) : |condE tr f k n h| ≤ B := by
  rw [_root_.abs_le]
  constructor
  · have := mono_apply tr (f := fun _ _ => -B) (g := f) (fun n h => (abs_le.mp (hf n h)).1) k n h
    rwa [const_apply] at this
  · have := mono_apply tr (f := f) (g := fun _ _ => B) (fun n h => (abs_le.mp (hf n h)).2) k n h
    rwa [const_apply] at this

/-- Nonnegative processes have nonnegative conditional expectations (O&R p. 316). -/
theorem nonneg_apply {f : TreeProcess S} (hf : ∀ n h, 0 ≤ f n h) (k n : ℕ) (h : Fin n → S) :
    0 ≤ condE tr f k n h := by
  have := mono_apply tr (f := fun _ _ => 0) (g := f) hf k n h
  rwa [const_apply] at this

end condE

/-- Appending an event multiplies the conditional probability by its one-step probability,
`π(h, s | h_m) = π(h | h_m)π(s | h)` (O&R Appendix 5C, p. 341, and footnote 53, p. 344). -/
theorem condProb_snoc (tr : EventTree.Tree S) {n : ℕ} (x : Fin n → S) (s : S) {m : ℕ}
    (hm : m ≤ n) :
    tr.condProb (Fin.snoc x s : Fin (n + 1) → S) m = tr.condProb x m * tr.q n x s := by
  unfold EventTree.Tree.condProb
  rw [Finset.prod_Ico_succ_top hm, tr.step_snoc_last]
  congr 1
  exact Finset.prod_congr rfl fun i hi => tr.step_snoc_lt x s (Finset.mem_Ico.mp hi).2

/-- **The recursive conditional expectation is the tree's conditional expectation**
(O&R §5.4.3, p. 316, with the probabilities of Appendix 5C, p. 341): `E_t[f_{t+k}]` at `h`
is the sum over all `k`-event continuations `g` of `π(h ++ g | h) f(h ++ g)`, where
`π(· | h)` is `Tree.condProb`. -/
theorem condE_eq_sum_condProb (tr : EventTree.Tree S) (f : TreeProcess S) (k : ℕ) :
    ∀ (n : ℕ) (h : Fin n → S), condE tr f k n h
      = ∑ g : Fin k → S, tr.condProb (Fin.append h g) n * f (n + k) (Fin.append h g) := by
  induction k generalizing f with
  | zero =>
    intro n h
    rw [Fintype.sum_unique]
    have e : (Fin.append h (default : Fin 0 → S) : Fin (n + 0) → S) = h := by
      funext i
      simp [Fin.append_right_nil]
    simp [e, EventTree.Tree.condProb, condE.zero_eq]
  | succ k ih =>
    intro n h
    rw [condE.succ_eq_iter, ih]
    rw [← (Fin.snocEquiv (fun _ : Fin (k + 1) => S)).sum_comp, Fintype.sum_prod_type,
      Finset.sum_comm]
    refine Finset.sum_congr rfl fun g _ => ?_
    have e : ∀ s : S, (Fin.snocEquiv fun _ : Fin (k + 1) => S) (s, g) = Fin.snoc g s :=
      fun _ => rfl
    simp only [e, Fin.append_snoc, condProb_snoc tr _ _ (Nat.le_add_right n k), condE.one_eq,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => (mul_assoc _ _ _).symm


/-! ## §5.4.3: the Euler equation (57) and forward iteration to (59) -/

/-- The equity Euler equation (57), O&R p. 315, on the event tree: at every history `h`,
`u′(C(h))V(h) = βΣ_s π(s|h) u′(C(h,s))(Y(h,s) + V(h,s))`, where `M = u′(C)` is the marginal
utility process, `Y` the dividend and `V` the ex-dividend price. -/
def EulerEq (tr : EventTree.Tree S) (β : ℝ) (M Y V : TreeProcess S) : Prop :=
  ∀ (n : ℕ) (h : Fin n → S), M n h * V n h =
    β * ∑ s, tr.q n h s * (M (n + 1) (Fin.snoc h s) *
      (Y (n + 1) (Fin.snoc h s) + V (n + 1) (Fin.snoc h s)))

/-- The `K`-term partial sum of marginal-utility-weighted discounted expected dividends in
(59), O&R p. 316: `Σ_{k=1}^{K} β^k E_t[u′(C_{t+k})Y_{t+k}]`. -/
noncomputable def pvPartial (tr : EventTree.Tree S) (β : ℝ) (M Y : TreeProcess S) (K n : ℕ)
    (h : Fin n → S) : ℝ :=
  ∑ k ∈ range K, β ^ (k + 1) * condE tr (fun m g => M m g * Y m g) (k + 1) n h

variable (tr : EventTree.Tree S)

/-- The Euler equation (57) in conditional-expectation form, O&R p. 316:
`u′(C_t)V_t = β(E_t[u′(C_{t+1})Y_{t+1}] + E_t[u′(C_{t+1})V_{t+1}])`. -/
theorem eulerEq_iff (β : ℝ) (M Y V : TreeProcess S) :
    EulerEq tr β M Y V ↔ (fun m g => M m g * V m g) = fun m g =>
      β * (condE tr (fun m g => M m g * Y m g) 1 m g
        + condE tr (fun m g => M m g * V m g) 1 m g) := by
  constructor
  · intro he
    funext n h
    rw [he n h, condE.one_eq, condE.one_eq, ← Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_congr rfl fun s _ => by ring
  · intro he n h
    have := congrFun (congrFun he n) h
    rw [this, condE.one_eq, condE.one_eq, ← Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_congr rfl fun s _ => by ring

/-- **Forward iteration of (57), O&R p. 316** (stochastic, `K` steps): if the Euler equation
holds at every history then, for every horizon `K`,
`u′(C_t)V_t = Σ_{k=1}^{K} β^k E_t[u′(C_{t+k})Y_{t+k}] + β^K E_t[u′(C_{t+K})V_{t+K}]`. -/
theorem mu_price_k_step {β : ℝ} {M Y V : TreeProcess S} (he : EulerEq tr β M Y V) (K : ℕ) :
    ∀ (n : ℕ) (h : Fin n → S), M n h * V n h = pvPartial tr β M Y K n h
      + β ^ K * condE tr (fun m g => M m g * V m g) K n h := by
  have hfun := (eulerEq_iff tr β M Y V).mp he
  induction K with
  | zero => intro n h; simp [pvPartial, condE.zero_eq]
  | succ K ih =>
    intro n h
    have key : condE tr (fun m g => M m g * V m g) K n h
        = β * (condE tr (fun m g => M m g * Y m g) (K + 1) n h
          + condE tr (fun m g => M m g * V m g) (K + 1) n h) := by
      rw [hfun, condE.smul_apply, condE.add_apply, ← condE.succ_eq_iter,
        ← condE.succ_eq_iter, ← hfun]
    rw [ih n h, key, pvPartial, pvPartial, Finset.sum_range_succ]
    ring

/-- **The `K`-step price identity, O&R p. 316**: with `u′(C_t) ≠ 0`, the price is the sum of
the first `K` discounted expected dividends, each valued at the marginal rate of substitution
`β^k u′(C_{t+k})/u′(C_t)`, plus the discounted expected price
`β^K E_t[u′(C_{t+K})V_{t+K}]/u′(C_t)`. -/
theorem price_k_step {β : ℝ} {M Y V : TreeProcess S} (he : EulerEq tr β M Y V) (K n : ℕ)
    (h : Fin n → S) (hM : M n h ≠ 0) :
    V n h = pvPartial tr β M Y K n h / M n h
      + β ^ K * condE tr (fun m g => M m g * V m g) K n h / M n h := by
  rw [← add_div, ← mu_price_k_step tr he K n h]
  field_simp

/-- **O&R (59), p. 316**: under the book's no-bubble condition
`lim_{T→∞} E_t{β^T[u′(C_{t+T})/u′(C_t)]V_{t+T}} = 0`, the price is the infinite sum of
discounted expected dividends,
`V_t = lim_K Σ_{k=1}^{K} β^k E_t[u′(C_{t+k})Y_{t+k}]/u′(C_t)` (the limit of partial sums, as
the book's `Σ_{s=t+1}^∞` means; no summability is assumed). -/
theorem price_eq_series {β : ℝ} {M Y V : TreeProcess S} (he : EulerEq tr β M Y V) (n : ℕ)
    (h : Fin n → S) (hM : M n h ≠ 0)
    (hnb : Tendsto (fun K => β ^ K * condE tr (fun m g => M m g * V m g) K n h / M n h)
      atTop (𝓝 0)) :
    Tendsto (fun K => pvPartial tr β M Y K n h / M n h) atTop (𝓝 (V n h)) := by
  have e : (fun K => pvPartial tr β M Y K n h / M n h) = fun K =>
      V n h - β ^ K * condE tr (fun m g => M m g * V m g) K n h / M n h := by
    funext K
    rw [price_k_step tr he K n h hM]
    ring
  rw [e]
  simpa using (tendsto_const_nhds (x := V n h)).sub hnb

/-- **O&R (59), p. 316, as a sum**: when dividends and marginal utilities are nonnegative
(`u′(C)Y ≥ 0`), `β ≥ 0` and `u′(C_t) > 0`, the no-bubble condition gives
`V_t = Σ_{k≥1} β^k E_t[u′(C_{t+k})Y_{t+k}]/u′(C_t)` as a genuine (absolutely convergent)
series; summability is derived, not assumed. -/
theorem price_hasSum {β : ℝ} (hβ : 0 ≤ β) {M Y V : TreeProcess S} (he : EulerEq tr β M Y V)
    (hD : ∀ m g, 0 ≤ M m g * Y m g) (n : ℕ) (h : Fin n → S) (hM : 0 < M n h)
    (hnb : Tendsto (fun K => β ^ K * condE tr (fun m g => M m g * V m g) K n h / M n h)
      atTop (𝓝 0)) :
    HasSum (fun k => β ^ (k + 1) * condE tr (fun m g => M m g * Y m g) (k + 1) n h / M n h)
      (V n h) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg]
  · have := price_eq_series tr he n h hM.ne' hnb
    simpa [pvPartial, Finset.sum_div] using this
  · intro k
    exact div_nonneg (mul_nonneg (pow_nonneg hβ _) (condE.nonneg_apply tr hD _ _ _)) hM.le

/-- The recursion of the partial sums, O&R p. 316: `P_{K+1}(h) = βΣ_s π(s|h)
[u′(C(h,s))Y(h,s) + P_K(h,s)]`, where `P_K` is `pvPartial` with `K` terms. -/
theorem pvPartial_succ (β : ℝ) (M Y : TreeProcess S) (K n : ℕ) (h : Fin n → S) :
    pvPartial tr β M Y (K + 1) n h = β * ∑ s, tr.q n h s *
      (M (n + 1) (Fin.snoc h s) * Y (n + 1) (Fin.snoc h s)
        + pvPartial tr β M Y K (n + 1) (Fin.snoc h s)) := by
  simp only [pvPartial, Finset.sum_range_succ', condE.succ_eq, Finset.mul_sum, mul_add,
    Finset.sum_add_distrib, condE.zero_eq]
  rw [Finset.sum_comm, add_comm]
  congr 1
  · refine Finset.sum_congr rfl fun s _ => ?_
    ring
  · refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun k _ => ?_
    ring_nf

/-- The limit of the present-value series satisfies the Euler recursion, O&R p. 316: if at
every history the partial sums converge to `F`, then
`F(h) = βΣ_s π(s|h)[u′(C(h,s))Y(h,s) + F(h,s)]`. -/
theorem series_limit_recursion {β : ℝ} {M Y F : TreeProcess S}
    (hF : ∀ n h, Tendsto (fun K => pvPartial tr β M Y K n h) atTop (𝓝 (F n h))) (n : ℕ)
    (h : Fin n → S) :
    F n h = β * ∑ s, tr.q n h s * (M (n + 1) (Fin.snoc h s) * Y (n + 1) (Fin.snoc h s)
      + F (n + 1) (Fin.snoc h s)) := by
  have h1 : Tendsto (fun K => pvPartial tr β M Y (K + 1) n h) atTop (𝓝 (F n h)) :=
    (tendsto_add_atTop_iff_nat 1).mpr (hF n h)
  have h2 : Tendsto (fun K => pvPartial tr β M Y (K + 1) n h) atTop
      (𝓝 (β * ∑ s, tr.q n h s * (M (n + 1) (Fin.snoc h s) * Y (n + 1) (Fin.snoc h s)
        + F (n + 1) (Fin.snoc h s)))) := by
    simp_rw [pvPartial_succ]
    exact tendsto_const_nhds.mul (tendsto_finsetSum _ fun s _ =>
      tendsto_const_nhds.mul (tendsto_const_nhds.add (hF _ _)))
  exact tendsto_nhds_unique h1 h2

/-- **Existence, O&R (59), p. 316, converse**: if the present-value series converges at every
history (to `F`) and marginal utility never vanishes, then `V = F/u′(C)` satisfies the Euler
equation (57) at every history. -/
theorem euler_of_series {β : ℝ} {M Y F : TreeProcess S} (hM : ∀ n h, M n h ≠ 0)
    (hF : ∀ n h, Tendsto (fun K => pvPartial tr β M Y K n h) atTop (𝓝 (F n h))) :
    EulerEq tr β M Y (fun n h => F n h / M n h) := by
  intro n h
  rw [mul_div_cancel₀ _ (hM n h), series_limit_recursion tr hF n h]
  congr 1
  refine Finset.sum_congr rfl fun s _ => ?_
  have := hM (n + 1) (Fin.snoc h s)
  field_simp

/-- **Bubbles are discounted-marginal-utility martingales, O&R p. 316**: if `V` solves the
Euler equation and the present-value series converges to `F` at every history, the bubble
`b = u′(C)V − F` satisfies `b(h) = βΣ_s π(s|h) b(h,s)`, i.e. `β^t u′(C_t)(V_t − F_t/u′(C_t))`
is a martingale. -/
theorem bubble_recursion {β : ℝ} {M Y V F : TreeProcess S} (he : EulerEq tr β M Y V)
    (hF : ∀ n h, Tendsto (fun K => pvPartial tr β M Y K n h) atTop (𝓝 (F n h))) (n : ℕ)
    (h : Fin n → S) :
    M n h * V n h - F n h = β * ∑ s, tr.q n h s *
      (M (n + 1) (Fin.snoc h s) * V (n + 1) (Fin.snoc h s) - F (n + 1) (Fin.snoc h s)) := by
  rw [he n h, series_limit_recursion tr hF n h, ← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  exact Finset.sum_congr rfl fun s _ => by ring

/-- **The bubble term, O&R p. 316**: if `V` solves the Euler equation and the present-value
series converges to `F`, then `β^K E_t[u′(C_{t+K})V_{t+K}] → u′(C_t)V_t − F_t`: the limit in
the no-bubble condition is exactly the bubble component of the price. -/
theorem bubble_tendsto {β : ℝ} {M Y V F : TreeProcess S} (he : EulerEq tr β M Y V)
    (hF : ∀ n h, Tendsto (fun K => pvPartial tr β M Y K n h) atTop (𝓝 (F n h))) (n : ℕ)
    (h : Fin n → S) :
    Tendsto (fun K => β ^ K * condE tr (fun m g => M m g * V m g) K n h) atTop
      (𝓝 (M n h * V n h - F n h)) := by
  have e : (fun K => β ^ K * condE tr (fun m g => M m g * V m g) K n h)
      = fun K => M n h * V n h - pvPartial tr β M Y K n h := by
    funext K
    rw [mu_price_k_step tr he K n h]
    ring
  rw [e]
  exact (tendsto_const_nhds).sub (hF n h)

/-- **Uniqueness iff no bubble, O&R p. 316**: for an Euler solution `V`, with the series
converging to `F` and `u′(C_t) ≠ 0`, the price equals the fundamental `F_t/u′(C_t)` if and
only if the book's no-bubble condition holds at `h`. -/
theorem price_eq_fundamental_iff {β : ℝ} {M Y V F : TreeProcess S} (he : EulerEq tr β M Y V)
    (hF : ∀ n h, Tendsto (fun K => pvPartial tr β M Y K n h) atTop (𝓝 (F n h))) (n : ℕ)
    (h : Fin n → S) (hM : M n h ≠ 0) :
    V n h = F n h / M n h ↔
      Tendsto (fun K => β ^ K * condE tr (fun m g => M m g * V m g) K n h / M n h)
        atTop (𝓝 0) := by
  have hb := (bubble_tendsto tr he hF n h).div_const (M n h)
  constructor
  · intro hV
    have e : (M n h * V n h - F n h) / M n h = 0 := by
      rw [hV]; field_simp; ring
    rwa [e] at hb
  · intro hnb
    have e := tendsto_nhds_unique hb hnb
    rw [div_eq_zero_iff] at e
    rcases e with e | e
    · rw [eq_div_iff hM]; linarith
    · exact absurd e hM

/-- **Uniqueness under no bubbles, O&R p. 316**: two solutions of the Euler equation that
both satisfy the no-bubble condition at `h` (with `u′(C_t) ≠ 0`) have the same price at `h`;
no convergence of the series is assumed (it follows). -/
theorem price_unique_of_noBubble {β : ℝ} {M Y V W : TreeProcess S}
    (hV : EulerEq tr β M Y V) (hW : EulerEq tr β M Y W) (n : ℕ) (h : Fin n → S)
    (hM : M n h ≠ 0)
    (hnV : Tendsto (fun K => β ^ K * condE tr (fun m g => M m g * V m g) K n h / M n h)
      atTop (𝓝 0))
    (hnW : Tendsto (fun K => β ^ K * condE tr (fun m g => M m g * W m g) K n h / M n h)
      atTop (𝓝 0)) :
    V n h = W n h :=
  tendsto_nhds_unique (price_eq_series tr hV n h hM hnV) (price_eq_series tr hW n h hM hnW)

/-- **Adding a bubble, O&R p. 316**: if `V` solves the Euler equation and `b` satisfies the
martingale recursion `b(h) = βΣ_s π(s|h) b(h,s)`, then `V + b/u′(C)` also solves it. -/
theorem euler_add_bubble {β : ℝ} {M Y V : TreeProcess S} (he : EulerEq tr β M Y V)
    (hM : ∀ n h, M n h ≠ 0) (b : TreeProcess S)
    (hb : ∀ n h, b n h = β * ∑ s, tr.q n h s * b (n + 1) (Fin.snoc h s)) :
    EulerEq tr β M Y (fun n h => V n h + b n h / M n h) := by
  intro n h
  have e1 : M n h * (V n h + b n h / M n h) = M n h * V n h + b n h := by
    field_simp [hM n h]
  rw [e1, he n h, hb n h, ← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun s _ => ?_
  have := hM (n + 1) (Fin.snoc h s)
  field_simp
  ring

/-- **Without the no-bubble condition prices are not unique, O&R p. 316**: for `β > 0` and
any `c ≠ 0`, the deterministic bubble `b_t = c/β^{t−1}` satisfies the martingale recursion,
so `V + b/u′(C)` is a second Euler solution differing from `V` at every history. -/
theorem euler_nonunique_without_noBubble {β : ℝ} (hβ : 0 < β) {M Y V : TreeProcess S}
    (he : EulerEq tr β M Y V) (hM : ∀ n h, M n h ≠ 0) {c : ℝ} (hc : c ≠ 0) :
    EulerEq tr β M Y (fun n h => V n h + c / β ^ n / M n h) ∧
      ∀ n h, V n h + c / β ^ n / M n h ≠ V n h := by
  refine ⟨euler_add_bubble tr he hM (fun n _ => c / β ^ n) fun n h => ?_, fun n h => ?_⟩
  · rw [← Finset.sum_mul, tr.q_sum, one_mul, pow_succ]
    field_simp
  · have : c / β ^ n / M n h ≠ 0 :=
      div_ne_zero (div_ne_zero hc (pow_ne_zero _ hβ.ne')) (hM n h)
    intro hh
    exact this (by linarith)

/-! ## Deriving the no-bubble condition from primitives -/

/-- **The no-bubble condition from boundedness, O&R p. 316**: if marginal-utility-weighted
prices `u′(C)V` are bounded over the tree and `0 ≤ β < 1`, then
`β^K E_t[u′(C_{t+K})V_{t+K}]/u′(C_t) → 0`. -/
theorem noBubble_of_bounded {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {M V : TreeProcess S}
    {B : ℝ} (hB : ∀ n h, |M n h * V n h| ≤ B) (n : ℕ) (h : Fin n → S) :
    Tendsto (fun K => β ^ K * condE tr (fun m g => M m g * V m g) K n h / M n h) atTop
      (𝓝 0) := by
  have hlim : Tendsto (fun K : ℕ => β ^ K * B / |M n h|) atTop (𝓝 0) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 hβ1).mul_const B).div_const
      |M n h|
  refine squeeze_zero_norm (fun K => ?_) hlim
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_pow, abs_of_nonneg hβ0]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
    (condE.abs_le_of_bound tr hB K n h) (pow_nonneg hβ0 K)) (abs_nonneg _)

/-- **Convergence of the present-value series, O&R (59), p. 316**: if marginal-utility-weighted
dividends `u′(C)Y` are bounded by `B` and `0 ≤ β < 1`, the series
`Σ_{k≥1} β^k E_t[u′(C_{t+k})Y_{t+k}]` is (absolutely) summable at every history. -/
theorem series_summable_of_bounded {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {M Y : TreeProcess S}
    {B : ℝ} (hB : ∀ n h, |M n h * Y n h| ≤ B) (n : ℕ) (h : Fin n → S) :
    Summable (fun k => β ^ (k + 1) * condE tr (fun m g => M m g * Y m g) (k + 1) n h) := by
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hβ0 hβ1).mul_left (β * B))
    fun k => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hβ0]
  calc β ^ (k + 1) * |condE tr (fun m g => M m g * Y m g) (k + 1) n h|
      ≤ β ^ (k + 1) * B :=
        mul_le_mul_of_nonneg_left (condE.abs_le_of_bound tr hB _ n h) (pow_nonneg hβ0 _)
    _ = β * B * β ^ k := by ring

/-- The marginal-utility-weighted fundamental value `F_t = Σ_{k≥1} β^k E_t[u′(C_{t+k})Y_{t+k}]`,
O&R (59), p. 316 (a `tsum`; used only where summability is proved). -/
noncomputable def fundamentalMU (tr : EventTree.Tree S) (β : ℝ) (M Y : TreeProcess S) (n : ℕ)
    (h : Fin n → S) : ℝ :=
  ∑' k, β ^ (k + 1) * condE tr (fun m g => M m g * Y m g) (k + 1) n h

/-- The partial sums converge to the fundamental value when `u′(C)Y` is bounded and
`0 ≤ β < 1` (O&R (59), p. 316). -/
theorem fundamentalMU_tendsto {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {M Y : TreeProcess S}
    {B : ℝ} (hB : ∀ n h, |M n h * Y n h| ≤ B) (n : ℕ) (h : Fin n → S) :
    Tendsto (fun K => pvPartial tr β M Y K n h) atTop (𝓝 (fundamentalMU tr β M Y n h)) :=
  (series_summable_of_bounded tr hβ0 hβ1 hB n h).hasSum.tendsto_sum_nat

/-- The fundamental value is bounded, `|F_t| ≤ βB/(1 − β)`, when `|u′(C)Y| ≤ B` and
`0 ≤ β < 1` (O&R (59), p. 316). -/
theorem fundamentalMU_abs_le {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {M Y : TreeProcess S}
    {B : ℝ} (hB : ∀ n h, |M n h * Y n h| ≤ B) (n : ℕ) (h : Fin n → S) :
    |fundamentalMU tr β M Y n h| ≤ β * B / (1 - β) := by
  have hf := (series_summable_of_bounded tr hβ0 hβ1 hB n h).hasSum
  have hg := (hasSum_geometric_of_lt_one hβ0 hβ1).mul_left (β * B)
  have hle : ∀ k, |β ^ (k + 1) * condE tr (fun m g => M m g * Y m g) (k + 1) n h|
      ≤ β * B * β ^ k := by
    intro k
    rw [abs_mul, abs_pow, abs_of_nonneg hβ0]
    calc β ^ (k + 1) * |condE tr (fun m g => M m g * Y m g) (k + 1) n h|
        ≤ β ^ (k + 1) * B :=
          mul_le_mul_of_nonneg_left (condE.abs_le_of_bound tr hB _ n h) (pow_nonneg hβ0 _)
      _ = β * B * β ^ k := by ring
  rw [div_eq_mul_inv, _root_.abs_le]
  exact ⟨hasSum_le (fun k => by linarith [(_root_.abs_le.mp (hle k)).1]) hg.neg hf,
    hasSum_le (fun k => (_root_.abs_le.mp (hle k)).2) hf hg⟩

/-- **Existence and uniqueness of the bounded price, O&R (57)–(59), p. 316**. Suppose
`0 ≤ β < 1`, marginal utility is positive and `u′(C)Y` is bounded by `B`. Then the series
price `V = F/u′(C)` (with `F` the fundamental value, whose convergence is proved) solves the
Euler equation (57) at every history, `u′(C)V` is bounded by `βB/(1 − β)`, and every Euler
solution with bounded `u′(C)V` equals it: the no-bubble condition is derived from
boundedness. -/
theorem unique_bounded_price {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {M Y : TreeProcess S}
    (hM : ∀ n h, 0 < M n h) {B : ℝ} (hB : ∀ n h, |M n h * Y n h| ≤ B) :
    EulerEq tr β M Y (fun n h => fundamentalMU tr β M Y n h / M n h) ∧
      (∀ n h, |M n h * (fundamentalMU tr β M Y n h / M n h)| ≤ β * B / (1 - β)) ∧
      ∀ V : TreeProcess S, EulerEq tr β M Y V → (∃ B', ∀ n h, |M n h * V n h| ≤ B') →
        V = fun n h => fundamentalMU tr β M Y n h / M n h := by
  refine ⟨euler_of_series tr (fun n h => (hM n h).ne')
    (fundamentalMU_tendsto tr hβ0 hβ1 hB), fun n h => ?_, fun V hV ⟨B', hB'⟩ => ?_⟩
  · rw [mul_div_cancel₀ _ (hM n h).ne']
    exact fundamentalMU_abs_le tr hβ0 hβ1 hB n h
  · funext n h
    exact tendsto_nhds_unique
      (price_eq_series tr hV n h (hM n h).ne' (noBubble_of_bounded tr hβ0 hβ1 hB' n h))
      ((fundamentalMU_tendsto tr hβ0 hβ1 hB n h).div_const _)

/-- **Bounded prices are unique, O&R p. 316**: if `0 ≤ β < 1` and marginal utility lies in
`(0, M̄]`, any two Euler solutions with bounded prices coincide. -/
theorem bounded_prices_unique {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {M Y V W : TreeProcess S}
    {Mbar BV BW : ℝ} (hM : ∀ n h, 0 < M n h) (hMb : ∀ n h, M n h ≤ Mbar)
    (hV : EulerEq tr β M Y V) (hW : EulerEq tr β M Y W) (hBV : ∀ n h, |V n h| ≤ BV)
    (hBW : ∀ n h, |W n h| ≤ BW) : V = W := by
  have bnd : ∀ (Z : TreeProcess S) (BZ : ℝ), (∀ n h, |Z n h| ≤ BZ) →
      ∀ n h, |M n h * Z n h| ≤ Mbar * BZ := by
    intro Z BZ hZ n h
    rw [abs_mul, abs_of_pos (hM n h)]
    exact mul_le_mul (hMb n h) (hZ n h) (abs_nonneg _) ((hM n h).le.trans (hMb n h))
  funext n h
  exact price_unique_of_noBubble tr hV hW n h (hM n h).ne'
    (noBubble_of_bounded tr hβ0 hβ1 (bnd V BV hBV) n h)
    (noBubble_of_bounded tr hβ0 hβ1 (bnd W BW hBW) n h)

/-! ## (60): riskless discounting plus covariance terms -/

/-- The market discount factor (60), O&R p. 317: `R_{t,t+k} = E_t[β^k u′(C_{t+k})/u′(C_t)]`,
the date-`t` price of a unit of date-`t+k` consumption delivered for sure. -/
noncomputable def discountR (tr : EventTree.Tree S) (β : ℝ) (M : TreeProcess S) (k n : ℕ)
    (h : Fin n → S) : ℝ :=
  β ^ k * condE tr M k n h / M n h

/-- The `k`-step conditional covariance `Cov_t(X_{t+k}, Z_{t+k}) = E_t[XZ] − E_t[X]E_t[Z]`
(O&R (59), p. 316). -/
noncomputable def condCov (tr : EventTree.Tree S) (k : ℕ) (X Z : TreeProcess S) (n : ℕ)
    (h : Fin n → S) : ℝ :=
  condE tr (fun m g => X m g * Z m g) k n h - condE tr X k n h * condE tr Z k n h

/-- **One term of (59), O&R pp. 316–317**: the value of the date-`t+k` dividend is its
expectation discounted at the riskless rate plus a covariance with the marginal rate of
substitution,
`E_t[β^k u′(C_{t+k})Y_{t+k}]/u′(C_t) = R_{t,t+k}E_t[Y_{t+k}]
  + Cov_t(β^k u′(C_{t+k})/u′(C_t), Y_{t+k})`. -/
theorem value_term_decomposition (β : ℝ) (M Y : TreeProcess S) (k n : ℕ) (h : Fin n → S) :
    β ^ k * condE tr (fun m g => M m g * Y m g) k n h / M n h
      = discountR tr β M k n h * condE tr Y k n h
        + condCov tr k (fun m g => β ^ k * M m g / M n h) Y n h := by
  have e1 : condE tr (fun m g => β ^ k * M m g / M n h * Y m g) k n h
      = β ^ k / M n h * condE tr (fun m g => M m g * Y m g) k n h := by
    rw [← condE.smul_apply]
    congr 1
    funext m g
    ring
  have e2 : condE tr (fun m g => β ^ k * M m g / M n h) k n h
      = β ^ k / M n h * condE tr M k n h := by
    rw [← condE.smul_apply]
    congr 1
    funext m g
    ring
  rw [condCov, e1, e2, discountR]
  ring

/-- **O&R footnote 44, p. 317**: a riskless `k`-period discount bond (paying one unit after
`k` periods, `b_0 = 1`) priced by the Euler equation
`u′(C_t)b_{k+1,t} = βE_t[u′(C_{t+1})b_{k,t+1}]` has price `R_{t,t+k}` of (60), i.e.
`R_{t,t+k}u′(C_t) = β^k E_t[u′(C_{t+k})]`. -/
theorem bond_price_eq_discountR {β : ℝ} {M : TreeProcess S} (hM : ∀ n h, M n h ≠ 0)
    (b : ℕ → TreeProcess S) (hb0 : ∀ n h, b 0 n h = 1)
    (hb : ∀ k n (h : Fin n → S), M n h * b (k + 1) n h =
      β * ∑ s, tr.q n h s * (M (n + 1) (Fin.snoc h s) * b k (n + 1) (Fin.snoc h s))) :
    ∀ k n h, b k n h = discountR tr β M k n h := by
  intro k
  induction k with
  | zero => intro n h; rw [hb0, discountR, pow_zero, one_mul, condE.zero_eq, div_self (hM n h)]
  | succ k ih =>
    intro n h
    have e : ∀ s, M (n + 1) (Fin.snoc h s) * b k (n + 1) (Fin.snoc h s)
        = β ^ k * condE tr M k (n + 1) (Fin.snoc h s) := by
      intro s
      rw [ih, discountR]
      field_simp [hM (n + 1) (Fin.snoc h s)]
    rw [discountR, eq_div_iff (hM n h), mul_comm, hb]
    simp only [e, condE.succ_eq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    ring

/-- **O&R (59) second line, p. 316**: under the no-bubble condition the price is the sum of
expected dividends discounted at the riskless market discount factors (60) plus the sum of
the covariance risk adjustments,
`V_t = Σ_{s>t} R_{t,s}E_t[Y_s] + Σ_{s>t} Cov_t(β^{s−t}u′(C_s)/u′(C_t), Y_s)`
(as a limit of partial sums). -/
theorem price_eq_riskless_plus_cov {β : ℝ} {M Y V : TreeProcess S} (he : EulerEq tr β M Y V)
    (n : ℕ) (h : Fin n → S) (hM : M n h ≠ 0)
    (hnb : Tendsto (fun K => β ^ K * condE tr (fun m g => M m g * V m g) K n h / M n h)
      atTop (𝓝 0)) :
    Tendsto (fun K => ∑ k ∈ range K, (discountR tr β M (k + 1) n h * condE tr Y (k + 1) n h
      + condCov tr (k + 1) (fun m g => β ^ (k + 1) * M m g / M n h) Y n h)) atTop
      (𝓝 (V n h)) := by
  have e : (fun K => ∑ k ∈ range K, (discountR tr β M (k + 1) n h * condE tr Y (k + 1) n h
      + condCov tr (k + 1) (fun m g => β ^ (k + 1) * M m g / M n h) Y n h))
      = fun K => pvPartial tr β M Y K n h / M n h := by
    funext K
    rw [pvPartial, Finset.sum_div]
    exact Finset.sum_congr rfl fun k _ => (value_term_decomposition tr β M Y (k + 1) n h).symm
  rw [e]
  exact price_eq_series tr he n h hM hnb

/-! ## (61): CRRA utility and constant consumption shares -/

/-- With CRRA marginal utility `u′(C) = C^{−ρ}` and `C = μY^W` (`μ > 0`, `Y^W > 0`), the
marginal rate of substitution is `(Y^W_{t+k}/Y^W_t)^{−ρ}`, O&R (61), p. 317:
`β^k E_t[u′(C_{t+k})Y_{t+k}]/u′(C_t) = β^k E_t[(Y^W_{t+k}/Y^W_t)^{−ρ}Y_{t+k}]`. -/
theorem crra_value_term {μ ρ : ℝ} (hμ : 0 < μ) {YW : TreeProcess S}
    (hYW : ∀ n h, 0 < YW n h) (β : ℝ) (Y : TreeProcess S) (k n : ℕ) (h : Fin n → S) :
    β ^ k * condE tr (fun m g => (μ * YW m g) ^ (-ρ) * Y m g) k n h / (μ * YW n h) ^ (-ρ)
      = β ^ k * condE tr (fun m g => (YW m g / YW n h) ^ (-ρ) * Y m g) k n h := by
  have hpos : 0 < (μ * YW n h) ^ (-ρ) := Real.rpow_pos_of_pos (mul_pos hμ (hYW n h)) _
  have hpos' : 0 < YW n h ^ (-ρ) := Real.rpow_pos_of_pos (hYW n h) _
  have key : (fun m g => (μ * YW m g) ^ (-ρ) * Y m g)
      = fun m g => (μ * YW n h) ^ (-ρ) * ((YW m g / YW n h) ^ (-ρ) * Y m g) := by
    funext m g
    rw [Real.mul_rpow hμ.le (hYW m g).le, Real.mul_rpow hμ.le (hYW n h).le,
      Real.div_rpow (hYW m g).le (hYW n h).le]
    field_simp
  rw [key, condE.smul_apply]
  field_simp

/-- **O&R (61), p. 317** (stochastic, infinite horizon): with CRRA utility, consumption a
constant share `μ > 0` of world output `Y^W > 0`, the Euler equation (57) at every history and
the no-bubble condition, `V_t = Σ_{s>t} β^{s−t}E_t[(Y^W_s/Y^W_t)^{−ρ}Y_s]`. -/
theorem price_crra_world_output_tree {β μ ρ : ℝ} (hμ : 0 < μ) {YW Y V : TreeProcess S}
    (hYW : ∀ n h, 0 < YW n h) (he : EulerEq tr β (fun m g => (μ * YW m g) ^ (-ρ)) Y V)
    (n : ℕ) (h : Fin n → S)
    (hnb : Tendsto (fun K => β ^ K * condE tr (fun m g => (μ * YW m g) ^ (-ρ) * V m g) K n h
      / (μ * YW n h) ^ (-ρ)) atTop (𝓝 0)) :
    Tendsto (fun K => ∑ k ∈ range K,
      β ^ (k + 1) * condE tr (fun m g => (YW m g / YW n h) ^ (-ρ) * Y m g) (k + 1) n h)
      atTop (𝓝 (V n h)) := by
  have hM : (μ * YW n h) ^ (-ρ) ≠ 0 := (Real.rpow_pos_of_pos (mul_pos hμ (hYW n h)) _).ne'
  have := price_eq_series tr he n h hM hnb
  simp only [pvPartial, Finset.sum_div] at this
  simpa only [crra_value_term tr hμ hYW] using this

/-- **O&R (59)–(60) at a finite horizon, pp. 316–317**: for every horizon `K`, the price is
the sum over the first `K` dates of riskless-discounted expected dividends plus covariance
terms, plus the discounted expected resale value:
`V_t = Σ_{k=1}^{K}[R_{t,t+k}E_t Y_{t+k} + Cov_t(β^k u′(C_{t+k})/u′(C_t), Y_{t+k})]
  + β^K E_t[u′(C_{t+K})V_{t+K}]/u′(C_t)`. -/
theorem price_k_step_riskless_cov {β : ℝ} {M Y V : TreeProcess S} (he : EulerEq tr β M Y V)
    (K n : ℕ) (h : Fin n → S) (hM : M n h ≠ 0) :
    V n h = ∑ k ∈ range K, (discountR tr β M (k + 1) n h * condE tr Y (k + 1) n h
      + condCov tr (k + 1) (fun m g => β ^ (k + 1) * M m g / M n h) Y n h)
      + β ^ K * condE tr (fun m g => M m g * V m g) K n h / M n h := by
  rw [price_k_step tr he K n h hM, pvPartial, Finset.sum_div]
  congr 1
  exact Finset.sum_congr rfl fun k _ => value_term_decomposition tr β M Y (k + 1) n h

/-- **O&R (61), p. 317, with the no-bubble condition derived**: with CRRA utility (`ρ > 0`),
`C = μY^W` (`μ > 0`), world output bounded away from zero (`Y^W ≥ a > 0`) and `0 ≤ β < 1`,
every bounded price process solving the Euler equation (57) satisfies
`V_t = Σ_{s>t} β^{s−t}E_t[(Y^W_s/Y^W_t)^{−ρ}Y_s]`. -/
theorem price_crra_world_output_bounded {β μ ρ a BV : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hμ : 0 < μ) (hρ : 0 < ρ) (ha : 0 < a) {YW Y V : TreeProcess S}
    (hYW : ∀ n h, a ≤ YW n h) (he : EulerEq tr β (fun m g => (μ * YW m g) ^ (-ρ)) Y V)
    (hV : ∀ n h, |V n h| ≤ BV) (n : ℕ) (h : Fin n → S) :
    Tendsto (fun K => ∑ k ∈ range K,
      β ^ (k + 1) * condE tr (fun m g => (YW m g / YW n h) ^ (-ρ) * Y m g) (k + 1) n h)
      atTop (𝓝 (V n h)) := by
  have hYW' : ∀ n h, 0 < YW n h := fun n h => lt_of_lt_of_le ha (hYW n h)
  have hB : ∀ n h, |(μ * YW n h) ^ (-ρ) * V n h| ≤ (μ * a) ^ (-ρ) * BV := by
    intro n h
    rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos (mul_pos hμ (hYW' n h)) _)]
    exact mul_le_mul (Real.rpow_le_rpow_of_nonpos (mul_pos hμ ha)
      (mul_le_mul_of_nonneg_left (hYW n h) hμ.le) (by linarith)) (hV n h) (abs_nonneg _)
      (Real.rpow_pos_of_pos (mul_pos hμ ha) _).le
  exact price_crra_world_output_tree tr hμ hYW' he n h
    (noBubble_of_bounded tr hβ0 hβ1 hB n h)

/-! ## First-order conditions from one-period portfolio perturbations -/

/-- **Euler equations from a one-period perturbation, O&R (56)–(58), p. 315**. Buying `ε`
more units of an asset at price `a` lowers today's consumption to `c₀ − εa` and raises
consumption in each state `s` tomorrow to `c₁(s) + εz(s)`, where `z` is the asset's payoff
(dividend plus resale price). If the optimal plan is not improved by any small such
perturbation (a local maximum at `ε = 0` of today's utility plus discounted expected utility
tomorrow — implied by optimality of the plan), and the period utilities are differentiable,
then `u′₀ a = βΣ_s π(s) u′₁(s) z(s)`. -/
theorem euler_of_isLocalMax {U0 : ℝ → ℝ} {U1 : S → ℝ → ℝ} {d0 c0 : ℝ} {d1 c1 : S → ℝ}
    (h0 : HasDerivAt U0 d0 c0) (h1 : ∀ s, HasDerivAt (U1 s) (d1 s) (c1 s)) (β : ℝ)
    (π : S → ℝ) (a : ℝ) (z : S → ℝ)
    (hmax : IsLocalMax (fun ε => U0 (c0 - ε * a) + β * ∑ s, π s * U1 s (c1 s + ε * z s)) 0) :
    d0 * a = β * ∑ s, π s * (d1 s * z s) := by
  have hin0 : HasDerivAt (fun ε : ℝ => c0 - ε * a) (-a) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const a).const_sub c0
  have hin1 : ∀ s, HasDerivAt (fun ε : ℝ => c1 s + ε * z s) (z s) 0 := fun s => by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (z s)).const_add (c1 s)
  have hd0 := h0.comp_of_eq 0 hin0 (by simp)
  have hd1 : ∀ s, HasDerivAt (fun ε => π s * U1 s (c1 s + ε * z s)) (π s * (d1 s * z s)) 0 :=
    fun s => ((h1 s).comp_of_eq 0 (hin1 s) (by simp)).const_mul (π s)
  have hd := hd0.add ((HasDerivAt.fun_sum (u := Finset.univ) fun s _ => hd1 s).const_mul β)
  have := hmax.hasDerivAt_eq_zero hd
  linarith

/-! ## Exercise 6: the Lucas (1982) two-good model -/

/-- The finance constraint of Exercise 6(a), O&R p. 347 (the two-risky-asset version of (56),
p. 315): bonds `B′` and shares `x′, y′` of the Home and Foreign output claims bought at the
ex-dividend prices `V_X, V_Y` are paid for by gross bond income `(1 + r)B`, the dividends plus
resale value of the shares `x, y` held (Foreign's dividend is `pY` in units of `X`), less
consumption spending `C_X + pC_Y`. -/
def lucasFinance (r B x y VX VY X Y p CX CY B' x' y' : ℝ) : Prop :=
  B' + x' * VX + y' * VY = (1 + r) * B + x * (X + VX) + y * (p * Y + VY) - CX - p * CY

/-- **Feasible perturbations, Exercise 6(a), O&R p. 347**: if a plan satisfies the finance
constraint today and in some state tomorrow, then buying `ε` more of the Home claim (paid
from today's `X` consumption, resold tomorrow with its dividend), or of the Foreign claim, or
of the bond, gives a plan that again satisfies both constraints, with later holdings
unchanged. -/
theorem lucas_perturbation_feasible {r B x y VX VY X Y p CX CY B' x' y' r' VX' VY' X' Y' p'
    CX' CY' B'' x'' y'' : ℝ} (ht : lucasFinance r B x y VX VY X Y p CX CY B' x' y')
    (ht1 : lucasFinance r' B' x' y' VX' VY' X' Y' p' CX' CY' B'' x'' y'') (ε : ℝ) :
    (lucasFinance r B x y VX VY X Y p (CX - ε * VX) CY B' (x' + ε) y' ∧
      lucasFinance r' B' (x' + ε) y' VX' VY' X' Y' p' (CX' + ε * (X' + VX')) CY' B'' x'' y'')
    ∧ (lucasFinance r B x y VX VY X Y p (CX - ε * VY) CY B' x' (y' + ε) ∧
      lucasFinance r' B' x' (y' + ε) VX' VY' X' Y' p' (CX' + ε * (p' * Y' + VY')) CY' B''
        x'' y'')
    ∧ (lucasFinance r B x y VX VY X Y p (CX - ε * 1) CY (B' + ε) x' y' ∧
      lucasFinance r' (B' + ε) x' y' VX' VY' X' Y' p' (CX' + ε * (1 + r')) CY' B'' x'' y'') := by
  unfold lucasFinance at *
  exact ⟨⟨by linear_combination ht, by linear_combination ht1⟩,
    ⟨by linear_combination ht, by linear_combination ht1⟩,
    ⟨by linear_combination ht, by linear_combination ht1⟩⟩

/-- **Exercise 6(a), O&R p. 347: the three Euler equations**. Let `u_X` be the partial
derivative of `u(C_X, C_Y)` in `C_X`, and let the date-`t+1` states `s` have probabilities
`π(s)`. If the optimal plan cannot be improved by the feasible perturbations of
`lucas_perturbation_feasible` (buying a little more of the Home claim, the Foreign claim or
the bond), then
`u_X(t)V_{X,t} = βE_t[u_X(t+1)(X_{t+1} + V_{X,t+1})]`,
`u_X(t)V_{Y,t} = βE_t[u_X(t+1)(p_{t+1}Y_{t+1} + V_{Y,t+1})]` and
`u_X(t) = (1 + r_{t+1})βE_t[u_X(t+1)]`. -/
theorem lucas_euler_equations (u uX : ℝ → ℝ → ℝ)
    (huX : ∀ a b, HasDerivAt (fun c => u c b) (uX a b) a) (β : ℝ) (π : S → ℝ)
    {CX CY VX VY r' : ℝ} {CX' CY' X' Y' p' VX' VY' : S → ℝ}
    (hmaxX : IsLocalMax (fun ε => u (CX - ε * VX) CY
      + β * ∑ s, π s * u (CX' s + ε * (X' s + VX' s)) (CY' s)) 0)
    (hmaxY : IsLocalMax (fun ε => u (CX - ε * VY) CY
      + β * ∑ s, π s * u (CX' s + ε * (p' s * Y' s + VY' s)) (CY' s)) 0)
    (hmaxB : IsLocalMax (fun ε => u (CX - ε * 1) CY
      + β * ∑ s, π s * u (CX' s + ε * (1 + r')) (CY' s)) 0) :
    uX CX CY * VX = β * ∑ s, π s * (uX (CX' s) (CY' s) * (X' s + VX' s)) ∧
      uX CX CY * VY = β * ∑ s, π s * (uX (CX' s) (CY' s) * (p' s * Y' s + VY' s)) ∧
      uX CX CY = (1 + r') * (β * ∑ s, π s * uX (CX' s) (CY' s)) := by
  refine ⟨euler_of_isLocalMax (huX CX CY) (fun s => huX (CX' s) (CY' s)) β π VX _ hmaxX,
    euler_of_isLocalMax (huX CX CY) (fun s => huX (CX' s) (CY' s)) β π VY _ hmaxY, ?_⟩
  have := euler_of_isLocalMax (U1 := fun s c => u c (CY' s)) (huX CX CY)
    (fun s => huX (CX' s) (CY' s)) β π 1 (fun _ => 1 + r') hmaxB
  rw [mul_one] at this
  rw [this, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun s _ => by ring

/-! ### The endowment state as a finite Markov chain -/

/-- A finite Markov chain for the endowment state, Exercise 6, O&R p. 347: transition
probabilities `P s s′ ≥ 0` with `Σ_{s′} P s s′ = 1`. -/
structure EndowmentChain (S : Type) [Fintype S] where
  P : S → S → ℝ
  P_nonneg : ∀ s s', 0 ≤ P s s'
  P_sum : ∀ s, ∑ s', P s s' = 1

/-- The current state after a history `h` of `n` events started from `s₀` (Exercise 6,
O&R p. 347): the last event of `h`, or `s₀` if `h` is empty. -/
def lastState {T : Type} (s₀ : T) : (n : ℕ) → (Fin n → T) → T
  | 0, _ => s₀
  | n + 1, h => h (Fin.last n)

/-- Appending an event makes it the current state (Exercise 6, O&R p. 347). -/
theorem lastState_snoc {T : Type} (s₀ : T) (n : ℕ) (h : Fin n → T) (s : T) :
    lastState s₀ (n + 1) (Fin.snoc h s : Fin (n + 1) → T) = s := by
  simp [lastState]

namespace EndowmentChain

variable (mc : EndowmentChain S)

/-- The event tree generated by the Markov chain from the initial state `s₀` (Exercise 6,
O&R p. 347): the next event after `h` is `s` with probability `P(current state, s)`. -/
def toTree (s₀ : S) : EventTree.Tree S :=
  ⟨fun n g s => mc.P (lastState s₀ n g) s, fun _ _ _ => mc.P_nonneg _ _, fun _ _ => mc.P_sum _⟩

/-- The one-step probabilities of the chain's tree (Exercise 6, O&R p. 347). -/
theorem toTree_q (s₀ : S) (n : ℕ) (g : Fin n → S) (s : S) :
    (mc.toTree s₀).q n g s = mc.P (lastState s₀ n g) s := rfl

/-- The `k`-step conditional expectation `E[f(s_{t+k}) | s_t = s]` of the chain
(Exercise 6(c), O&R p. 347). -/
noncomputable def mExp : ℕ → (S → ℝ) → S → ℝ
  | 0, f => f
  | k + 1, f => fun s => ∑ s', mc.P s s' * mExp k f s'

/-- On the chain's tree, conditional expectations of functions of the current state are the
chain's `k`-step expectations (Exercise 6(c), O&R p. 347). -/
theorem condE_toTree (s₀ : S) (f : S → ℝ) (k : ℕ) : ∀ (n : ℕ) (h : Fin n → S),
    condE (mc.toTree s₀) (fun n h => f (lastState s₀ n h)) k n h
      = mc.mExp k f (lastState s₀ n h) := by
  induction k with
  | zero => intro n h; rfl
  | succ k ih =>
    intro n h
    rw [condE.succ_eq]
    simp only [ih, lastState_snoc, toTree_q]
    rfl

/-- The marginal-utility-weighted present value `Σ_{k≥1} β^k E[g(s_{t+k}) | s_t = s]`
(Exercise 6(c), O&R p. 347). -/
noncomputable def markovSeries (β : ℝ) (g : S → ℝ) (s : S) : ℝ :=
  ∑' k, β ^ (k + 1) * mc.mExp (k + 1) g s

/-- The stationary claim price `V(s) = Σ_{k≥1} β^k E[m(s_{t+k})D(s_{t+k}) | s]/m(s)` of a
dividend `D` valued with marginal utility `m` (Exercise 6(c), O&R p. 347). -/
noncomputable def markovPrice (β : ℝ) (m D : S → ℝ) (s : S) : ℝ :=
  mc.markovSeries β (fun s => m s * D s) s / m s

end EndowmentChain

/-- On a finite state space every function is bounded, `|f s| ≤ Σ_{s′}|f s′|` (used for
Exercise 6(c), O&R p. 347). -/
theorem abs_le_sum_abs (f : S → ℝ) (s : S) : |f s| ≤ ∑ s', |f s'| :=
  Finset.single_le_sum (fun s' _ => abs_nonneg (f s')) (Finset.mem_univ s)

/-- The chain's tree fundamental value is the stationary series at the current state
(Exercise 6(c), O&R p. 347). -/
theorem fundamentalMU_toTree (mc : EndowmentChain S) (s₀ : S) (β : ℝ) (m D : S → ℝ)
    (n : ℕ) (h : Fin n → S) :
    fundamentalMU (mc.toTree s₀) β (fun n h => m (lastState s₀ n h))
      (fun n h => D (lastState s₀ n h)) n h
      = mc.markovSeries β (fun s => m s * D s) (lastState s₀ n h) := by
  unfold fundamentalMU EndowmentChain.markovSeries
  exact tsum_congr fun k => by rw [← mc.condE_toTree s₀ (fun s => m s * D s) (k + 1) n h]

/-- **Claim prices on a finite Markov chain, Exercise 6(c), O&R p. 347**. Let `0 ≤ β < 1`,
marginal utility `m(s) > 0` and dividend `D(s)` (in units of `X`). Then
(i) the present-value series `Σ_{k≥1} β^k E[m D | s]` converges at every state (proved from
finiteness and `β < 1`, not assumed);
(ii) the stationary price `V(s) = Σ_{k≥1} β^k E[m D | s]/m(s)` solves the Euler equation
`m(s)V(s) = βΣ_{s′}P(s, s′)m(s′)(D(s′) + V(s′))`;
(iii) it is the only stationary solution; and
(iv) on the event tree generated from any initial state, every bounded (possibly
history-dependent) price process solving the Euler equation equals `V` of the current state:
there are no bounded bubbles. -/
theorem markov_price_unique (mc : EndowmentChain S) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (m D : S → ℝ) (hm : ∀ s, 0 < m s) :
    (∀ s, Summable (fun k => β ^ (k + 1) * mc.mExp (k + 1) (fun s => m s * D s) s)) ∧
    (∀ s, m s * mc.markovPrice β m D s
      = β * ∑ s', mc.P s s' * (m s' * (D s' + mc.markovPrice β m D s'))) ∧
    (∀ V : S → ℝ, (∀ s, m s * V s = β * ∑ s', mc.P s s' * (m s' * (D s' + V s'))) →
      V = mc.markovPrice β m D) ∧
    (∀ (s₀ : S) (W : TreeProcess S), EulerEq (mc.toTree s₀) β (fun n h => m (lastState s₀ n h))
      (fun n h => D (lastState s₀ n h)) W → (∃ B, ∀ n h, |W n h| ≤ B) →
      ∀ n h, W n h = mc.markovPrice β m D (lastState s₀ n h)) := by
  have hB : ∀ s₀ : S, ∀ n (h : Fin n → S),
      |m (lastState s₀ n h) * D (lastState s₀ n h)| ≤ ∑ s', |m s' * D s'| :=
    fun s₀ n h => abs_le_sum_abs (fun s => m s * D s) _
  have hM : ∀ s₀ : S, ∀ n (h : Fin n → S), 0 < m (lastState s₀ n h) := fun _ _ _ => hm _
  have U := fun s₀ => unique_bounded_price (mc.toTree s₀) hβ0 hβ1 (hM s₀) (hB s₀)
  have e0 : ∀ s : S, lastState s 0 (Fin.elim0 : Fin 0 → S) = s := fun _ => rfl
  -- the tree solution is the stationary price of the current state
  have hfund : ∀ s₀ n (h : Fin n → S),
      fundamentalMU (mc.toTree s₀) β (fun n h => m (lastState s₀ n h))
        (fun n h => D (lastState s₀ n h)) n h / m (lastState s₀ n h)
        = mc.markovPrice β m D (lastState s₀ n h) := by
    intro s₀ n h
    rw [fundamentalMU_toTree]
    rfl
  have hstat : ∀ V : S → ℝ, (∀ s, m s * V s = β * ∑ s', mc.P s s' * (m s' * (D s' + V s'))) →
      ∀ s₀, EulerEq (mc.toTree s₀) β (fun n h => m (lastState s₀ n h))
        (fun n h => D (lastState s₀ n h)) (fun n h => V (lastState s₀ n h)) := by
    intro V hV s₀ n h
    simp only [hV, lastState_snoc, EndowmentChain.toTree_q]
  refine ⟨fun s => ?_, fun s => ?_, fun V hV => ?_, fun s₀ W hW ⟨BW, hBW⟩ n h => ?_⟩
  · have := series_summable_of_bounded (mc.toTree s) hβ0 hβ1 (hB s) 0 Fin.elim0
    refine this.congr fun k => ?_
    rw [mc.condE_toTree s (fun s => m s * D s) (k + 1) 0 Fin.elim0]
    rfl
  · have E := (U s).1 0 Fin.elim0
    simp only [fundamentalMU_toTree, lastState_snoc, EndowmentChain.toTree_q, e0] at E
    exact E
  · funext s
    have hW := (U s).2.2 (fun n h => V (lastState s n h)) (hstat V hV s)
      ⟨∑ s', |m s' * V s'|, fun n h => abs_le_sum_abs (fun s => m s * V s) _⟩
    have := congrFun (congrFun hW 0) Fin.elim0
    simp only [fundamentalMU_toTree, e0] at this
    exact this
  · have hW' := (U s₀).2.2 W hW ⟨(∑ s', |m s'|) * BW, fun n h => by
      rw [abs_mul]
      exact mul_le_mul (abs_le_sum_abs m _) (hBW n h) (abs_nonneg _)
        (Finset.sum_nonneg fun s' _ => abs_nonneg _)⟩
    rw [hW']
    exact hfund s₀ n h

/-! ### Exercise 6(b)–(d) -/

/-- **Exercise 6(c), O&R p. 347: equilibrium claim prices as expected present values.** Let
`m_X(s) = u_X(X(s)/2, Y(s)/2) > 0` and `m_Y(s) = u_Y(X(s)/2, Y(s)/2)` be the equilibrium
marginal utilities, `p = m_Y/m_X` the relative price of `Y`, and `0 ≤ β < 1`. Then
`V_X(s) = Σ_{k≥1} β^k E[m_X X | s]/m_X(s)` and
`V_Y(s) = Σ_{k≥1} β^k E[m_X pY | s]/m_X(s) = Σ_{k≥1} β^k E[m_Y Y | s]/m_X(s)` (both series
converge) solve the Euler equations of part (a), and each is the unique stationary solution
of its Euler equation (bounded history-dependent solutions are covered by
`markov_price_unique`). -/
theorem lucas_claim_prices_infinite (mc : EndowmentChain S) {β : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) (mX mY X Y : S → ℝ) (hmX : ∀ s, 0 < mX s) :
    (∀ s, Summable (fun k => β ^ (k + 1) * mc.mExp (k + 1) (fun s => mX s * X s) s)) ∧
    (∀ s, Summable (fun k => β ^ (k + 1) * mc.mExp (k + 1) (fun s => mY s * Y s) s)) ∧
    (∀ s, mc.markovPrice β mX (fun s => mY s / mX s * Y s) s
      = mc.markovSeries β (fun s => mY s * Y s) s / mX s) ∧
    (∀ s, mX s * mc.markovPrice β mX X s
      = β * ∑ s', mc.P s s' * (mX s' * (X s' + mc.markovPrice β mX X s'))) ∧
    (∀ s, mX s * mc.markovPrice β mX (fun s => mY s / mX s * Y s) s
      = β * ∑ s', mc.P s s' * (mX s' * (mY s' / mX s' * Y s'
        + mc.markovPrice β mX (fun s => mY s / mX s * Y s) s'))) ∧
    (∀ V : S → ℝ, (∀ s, mX s * V s = β * ∑ s', mc.P s s' * (mX s' * (X s' + V s'))) →
      V = mc.markovPrice β mX X) ∧
    (∀ V : S → ℝ, (∀ s, mX s * V s
      = β * ∑ s', mc.P s s' * (mX s' * (mY s' / mX s' * Y s' + V s'))) →
      V = mc.markovPrice β mX (fun s => mY s / mX s * Y s)) := by
  have hX := markov_price_unique mc hβ0 hβ1 mX X hmX
  have hY := markov_price_unique mc hβ0 hβ1 mX (fun s => mY s / mX s * Y s) hmX
  have e : (fun s => mX s * (mY s / mX s * Y s)) = fun s => mY s * Y s := by
    funext s
    field_simp [(hmX s).ne']
  refine ⟨hX.1, fun s => ?_, fun s => ?_, hX.2.1, hY.2.1, hX.2.2.1, hY.2.2.1⟩
  · have := hY.1 s
    rwa [e] at this
  · unfold EndowmentChain.markovPrice
    rw [e]

/-- **Exercise 6(b), O&R p. 347: the equilibrium.** With identical tastes and equal pooled
portfolios, consider the no-trade plan in which each country keeps half of each claim
(`x = y = 1/2`), holds no bonds and consumes `C_X = X/2`, `C_Y = Y/2`. At the prices
`p = m_Y/m_X`, `V_X`, `V_Y` of part (c) and the bond rate `1 + r(s) = m_X(s)/(βE[m_X | s])`:
(i) the plan satisfies each country's finance constraint in every state (whatever the
previous interest rate); (ii) goods, share and bond markets clear; (iii) the intratemporal
condition `u_Y = p u_X` holds; (iv) the Euler equations for both claims and the bond hold at
the allocation, for both countries (their marginal utilities coincide); and (v) each country
owns half of world wealth `X + pY + V_X + V_Y` in every state. -/
theorem lucas_equilibrium (mc : EndowmentChain S) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (mX mY X Y : S → ℝ) (hmX : ∀ s, 0 < mX s) (r0 : ℝ) (s : S) :
    lucasFinance r0 0 (1 / 2) (1 / 2) (mc.markovPrice β mX X s)
      (mc.markovPrice β mX (fun s => mY s / mX s * Y s) s) (X s) (Y s) (mY s / mX s)
      (X s / 2) (Y s / 2) 0 (1 / 2) (1 / 2) ∧
    (X s / 2 + X s / 2 = X s ∧ Y s / 2 + Y s / 2 = Y s ∧ (1 : ℝ) / 2 + 1 / 2 = 1) ∧
    mY s = mY s / mX s * mX s ∧
    (mX s * mc.markovPrice β mX X s
      = β * ∑ s', mc.P s s' * (mX s' * (X s' + mc.markovPrice β mX X s'))) ∧
    (mX s * mc.markovPrice β mX (fun s => mY s / mX s * Y s) s
      = β * ∑ s', mc.P s s' * (mX s' * (mY s' / mX s' * Y s'
        + mc.markovPrice β mX (fun s => mY s / mX s * Y s) s'))) ∧
    mX s = mX s / (β * ∑ s', mc.P s s' * mX s') * (β * ∑ s', mc.P s s' * mX s') ∧
    1 / 2 * (X s + mc.markovPrice β mX X s) + 1 / 2 * (mY s / mX s * Y s
      + mc.markovPrice β mX (fun s => mY s / mX s * Y s) s)
      = 1 / 2 * (X s + mY s / mX s * Y s + mc.markovPrice β mX X s
        + mc.markovPrice β mX (fun s => mY s / mX s * Y s) s) := by
  have hc := lucas_claim_prices_infinite mc hβ0.le hβ1 mX mY X Y hmX
  have hE : 0 < β * ∑ s', mc.P s s' * mX s' := by
    refine mul_pos hβ0 ?_
    obtain ⟨s', hs'⟩ : ∃ s', 0 < mc.P s s' := by
      by_contra hcon
      push Not at hcon
      have h1 := mc.P_sum s
      have : ∑ s', mc.P s s' ≤ 0 := Finset.sum_nonpos fun s' _ => hcon s'
      linarith
    exact lt_of_lt_of_le (mul_pos hs' (hmX s'))
      (Finset.single_le_sum (f := fun s' => mc.P s s' * mX s')
        (fun i _ => mul_nonneg (mc.P_nonneg s i) (hmX i).le) (Finset.mem_univ s'))
  refine ⟨?_, ⟨by ring, by ring, by norm_num⟩, ?_, hc.2.2.2.1 s, hc.2.2.2.2.1 s, ?_, by ring⟩
  · unfold lucasFinance
    ring
  · field_simp [(hmX s).ne']
  · exact (div_mul_cancel₀ (mX s) hE.ne').symm

/-- **Exercise 6(d), O&R p. 347: riskless rates.** (i) The date-`t` price `q_X` of one unit
of `X` delivered for sure at `t + 1` is pinned down by its Euler equation
`q_X m_X(s) = βE[m_X | s]`, so `q_X = βE[m_X | s]/m_X(s)`; (ii) a sure unit of `Y` next period
costs `π_Y` units of `X` with `π_Y m_X(s) = βE[m_X p | s]`, so its price in units of current
`Y` is `π_Y/p(s) = βE[m_Y | s]/m_Y(s)`, whose reciprocal is one plus the own-rate of interest
on `Y`; (iii) a `k`-period sure claim on `X` priced by the Euler recursion
`m_X(s)b_{k+1}(s) = βE[m_X b_k | s]`, `b_0 = 1`, costs `β^k E[m_X(s_{t+k}) | s]/m_X(s)`. -/
theorem lucas_riskless_rates (mc : EndowmentChain S) (β : ℝ) (mX mY : S → ℝ)
    (hmX : ∀ s, 0 < mX s) (hmY : ∀ s, 0 < mY s) (s : S) :
    (∀ q : ℝ, q * mX s = β * ∑ s', mc.P s s' * mX s' →
      q = β * (∑ s', mc.P s s' * mX s') / mX s) ∧
    (∀ πY : ℝ, πY * mX s = β * ∑ s', mc.P s s' * (mX s' * (mY s' / mX s')) →
      πY / (mY s / mX s) = β * (∑ s', mc.P s s' * mY s') / mY s) ∧
    (∀ b : ℕ → S → ℝ, (∀ s, b 0 s = 1) →
      (∀ k s, mX s * b (k + 1) s = β * ∑ s', mc.P s s' * (mX s' * b k s')) →
      ∀ k s, b k s = β ^ k * mc.mExp k mX s / mX s) := by
  refine ⟨fun q hq => ?_, fun πY hπ => ?_, fun b hb0 hb => ?_⟩
  · rw [eq_div_iff (hmX s).ne', hq]
  · have e : ∀ s', mX s' * (mY s' / mX s') = mY s' := fun s' => by
      field_simp [(hmX s').ne']
    simp only [e] at hπ
    have h1 := (hmX s).ne'
    have h2 := (hmY s).ne'
    field_simp
    rw [hπ]
  · intro k
    induction k with
    | zero => intro s; rw [hb0, pow_zero, one_mul, EndowmentChain.mExp, div_self (hmX s).ne']
    | succ k ih =>
      intro s
      rw [eq_div_iff (hmX s).ne', mul_comm, hb]
      simp only [ih, EndowmentChain.mExp, Finset.mul_sum]
      refine Finset.sum_congr rfl fun s' _ => ?_
      field_simp [(hmX s').ne']
      ring

/-! ## Exercise 3(a): quadratic utility and certainty equivalence -/

/-- Quadratic period utility `u(C) = C − (a₀/2)C²` of Exercise 3, O&R p. 345. -/
noncomputable def quadU (a0 c : ℝ) : ℝ := c - a0 / 2 * c ^ 2

/-- Marginal utility of quadratic utility, `u′(C) = 1 − a₀C` (Exercise 3, O&R p. 346). -/
theorem quadU_hasDerivAt (a0 c : ℝ) : HasDerivAt (quadU a0) (1 - a0 * c) c := by
  have h := (hasDerivAt_id c).sub ((hasDerivAt_pow 2 c).const_mul (a0 / 2))
  exact h.congr_deriv (by simp; ring)

/-- **The bond Euler equation with quadratic utility, Exercise 3, O&R p. 346**: with utility
discounted at `(1 + r)^{−1}`, if saving `ε` more in the bond (consuming `(1 + r)ε` more in
every state next period) does not improve the plan locally, then
`1 − a₀C₁ = Σ_s π(s)(1 − a₀C₂(s))`. -/
theorem quadratic_euler (π : S → ℝ) {a0 r C1 : ℝ} {C2 : S → ℝ} (hr : 1 + r ≠ 0)
    (hmax : IsLocalMax (fun ε => quadU a0 (C1 - ε * 1)
      + (1 + r)⁻¹ * ∑ s, π s * quadU a0 (C2 s + ε * (1 + r))) 0) :
    1 - a0 * C1 = ∑ s, π s * (1 - a0 * C2 s) := by
  have h := euler_of_isLocalMax (U1 := fun _ => quadU a0) (quadU_hasDerivAt a0 C1)
    (fun s => quadU_hasDerivAt a0 (C2 s)) (1 + r)⁻¹ π 1 (fun _ => 1 + r) hmax
  rw [mul_one] at h
  rw [h, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  field_simp

/-- **Exercise 3(a), O&R p. 346 (two periods)**: with the bond Euler equation and the budget
constraints `C₁ + C₂(s)/(1 + r) = (1 + r)B₁ + Y₁ + Y₂(s)/(1 + r)` (nonnegativity of `C₂`
ignored), optimal date-1 consumption is
`C₁ = [(1 + r)/(2 + r)][(1 + r)B₁ + Y₁ + E₁Y₂/(1 + r)]`: it depends on `Y₂` only through its
mean (certainty equivalence). -/
theorem quadratic_two_period_consumption {π : S → ℝ} (hπ : ∑ s, π s = 1) {a0 r B1 Y1 C1 : ℝ}
    {Y2 C2 : S → ℝ} (ha0 : a0 ≠ 0) (hr : -1 < r)
    (heul : 1 - a0 * C1 = ∑ s, π s * (1 - a0 * C2 s))
    (hbud : ∀ s, C1 + C2 s / (1 + r) = (1 + r) * B1 + Y1 + Y2 s / (1 + r)) :
    C1 = (1 + r) / (2 + r) * ((1 + r) * B1 + Y1 + (∑ s, π s * Y2 s) / (1 + r)) := by
  have hr1 : (1 + r) ≠ 0 := by linarith
  have hr2 : (2 + r) ≠ 0 := by linarith
  have hC2 : ∀ s, C2 s = (1 + r) * ((1 + r) * B1 + Y1 - C1) + Y2 s := by
    intro s
    have := hbud s
    field_simp at this
    linarith
  have hmean : C1 = ∑ s, π s * C2 s := by
    have e : ∑ s, π s * (1 - a0 * C2 s) = 1 - a0 * ∑ s, π s * C2 s := by
      calc ∑ s, π s * (1 - a0 * C2 s) = ∑ s, π s - a0 * ∑ s, π s * C2 s := by
            rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
            exact Finset.sum_congr rfl fun s _ => by ring
        _ = 1 - a0 * ∑ s, π s * C2 s := by rw [hπ]
    rw [e] at heul
    have : a0 * (C1 - ∑ s, π s * C2 s) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h ha0
    · linarith
  have hsum : ∑ s, π s * C2 s = (1 + r) * ((1 + r) * B1 + Y1 - C1) + ∑ s, π s * Y2 s := by
    simp only [hC2, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hπ, one_mul]
  rw [hsum] at hmean
  field_simp
  linarith

/-- **Consumption is a martingale under quadratic utility, Exercise 3, O&R p. 346** (with
Chapter 2's `β(1 + r) = 1`): the bond Euler equation `1 − a₀C_t = E_t[1 − a₀C_{t+1}]` at every
history, with `a₀ ≠ 0`, gives `E_t[C_{t+k}] = C_t` for every `k`. -/
theorem quadratic_consumption_martingale {a0 : ℝ} (ha0 : a0 ≠ 0) {C : TreeProcess S}
    (heul : ∀ n (h : Fin n → S),
      1 - a0 * C n h = ∑ s, tr.q n h s * (1 - a0 * C (n + 1) (Fin.snoc h s))) :
    ∀ k n h, condE tr C k n h = C n h := by
  have h1 : condE tr C 1 = C := by
    funext n h
    have e : ∑ s, tr.q n h s * (1 - a0 * C (n + 1) (Fin.snoc h s))
        = 1 - a0 * ∑ s, tr.q n h s * C (n + 1) (Fin.snoc h s) := by
      calc ∑ s, tr.q n h s * (1 - a0 * C (n + 1) (Fin.snoc h s))
          = ∑ s, tr.q n h s - a0 * ∑ s, tr.q n h s * C (n + 1) (Fin.snoc h s) := by
            rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
            exact Finset.sum_congr rfl fun s _ => by ring
        _ = 1 - a0 * ∑ s, tr.q n h s * C (n + 1) (Fin.snoc h s) := by rw [tr.q_sum]
    have := heul n h
    rw [e] at this
    have h2 : a0 * (C n h - ∑ s, tr.q n h s * C (n + 1) (Fin.snoc h s)) = 0 := by linarith
    rw [condE.one_eq]
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact absurd h3 ha0
    · linarith
  intro k
  induction k with
  | zero => intro n h; rfl
  | succ k ih => intro n h; rw [condE.succ_eq_iter, h1, ih]

/-- **The `K`-period expected budget constraint, Exercise 3 (Chapter 2 analogue), O&R p. 346**:
if bonds evolve as `B_{t+1} = (1 + r)B_t + Y_t − C_t` (the same in every date-`t+1` state),
then with `ν = 1/(1 + r)`,
`Σ_{k<K} ν^k E_t[C_{t+k}] = (1 + r)B_t + Σ_{k<K} ν^k E_t[Y_{t+k}] − (1 + r)ν^K E_t[B_{t+K}]`. -/
theorem expected_budget_k_step {r : ℝ} (hr : 1 + r ≠ 0) {B Y C : TreeProcess S}
    (hbud : ∀ n (h : Fin n → S) s,
      B (n + 1) (Fin.snoc h s) = (1 + r) * B n h + Y n h - C n h) (K : ℕ) :
    ∀ n h, ∑ k ∈ range K, (1 / (1 + r)) ^ k * condE tr C k n h
      = (1 + r) * B n h + ∑ k ∈ range K, (1 / (1 + r)) ^ k * condE tr Y k n h
        - (1 + r) * (1 / (1 + r)) ^ K * condE tr B K n h := by
  have hB1 : condE tr B 1 = fun m g => (1 + r) * B m g + Y m g - C m g := by
    funext m g
    rw [condE.one_eq]
    simp only [hbud, ← Finset.sum_mul, tr.q_sum, one_mul]
  have hν : (1 + r) * (1 / (1 + r)) = 1 := by field_simp
  induction K with
  | zero => intro n h; simp [condE.zero_eq]
  | succ K ih =>
    intro n h
    have key : condE tr B (K + 1) n h
        = (1 + r) * condE tr B K n h + condE tr Y K n h - condE tr C K n h := by
      rw [condE.succ_eq_iter, hB1, condE.sub_apply, condE.add_apply, condE.smul_apply]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih n h, key, pow_succ]
    linear_combination ((1 / (1 + r)) ^ K * ((1 + r) * condE tr B K n h + condE tr Y K n h
      - condE tr C K n h)) * hν

/-- The human-wealth series `Σ_{k≥0} ν^k E_t[Y_{t+k}]` is summable when income is bounded and
`r > 0` (`ν = 1/(1 + r)`), Exercise 3, O&R p. 346. -/
theorem income_series_summable {r : ℝ} (hr : 0 < r) {Y : TreeProcess S} {BY : ℝ}
    (hY : ∀ n h, |Y n h| ≤ BY) (n : ℕ) (h : Fin n → S) :
    Summable (fun k => (1 / (1 + r)) ^ k * condE tr Y k n h) := by
  have hν0 : 0 ≤ 1 / (1 + r) := by positivity
  have hν1 : 1 / (1 + r) < 1 := by rw [div_lt_one (by linarith)]; linarith
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hν0 hν1).mul_right BY)
    fun k => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hν0]
  exact mul_le_mul_of_nonneg_left (condE.abs_le_of_bound tr hY k n h) (pow_nonneg hν0 k)

/-- **Exercise 3(a), infinite horizon, O&R p. 346 (with Chapter 2's formula)**: on the event
tree, with quadratic utility discounted at `(1 + r)^{−1}`, `r > 0`, `a₀ ≠ 0`, bounded income
`Y`, bonds evolving by `B_{t+1} = (1 + r)B_t + Y_t − C_t`, the bond Euler equation at every
history (from `quadratic_euler`) and the intertemporal-budget (transversality) condition
`lim_K (1 + r)^{−K}E_t[B_{t+K}] = 0`, optimal consumption is
`C_t = [r/(1 + r)][(1 + r)B_t + Σ_{k≥0} (1 + r)^{−k}E_t[Y_{t+k}]]`, the certainty-equivalent
permanent-income rule: income uncertainty matters only through conditional means. The
human-wealth series converges (proved). -/
theorem quadratic_infinite_horizon_consumption {r a0 : ℝ} (hr : 0 < r) (ha0 : a0 ≠ 0)
    {B Y C : TreeProcess S} {BY : ℝ} (hY : ∀ n h, |Y n h| ≤ BY)
    (heul : ∀ n (h : Fin n → S),
      1 - a0 * C n h = ∑ s, tr.q n h s * (1 - a0 * C (n + 1) (Fin.snoc h s)))
    (hbud : ∀ n (h : Fin n → S) s,
      B (n + 1) (Fin.snoc h s) = (1 + r) * B n h + Y n h - C n h)
    (htv : ∀ n h, Tendsto (fun K => (1 / (1 + r)) ^ K * condE tr B K n h) atTop (𝓝 0))
    (n : ℕ) (h : Fin n → S) :
    C n h = r / (1 + r) * ((1 + r) * B n h
      + ∑' k, (1 / (1 + r)) ^ k * condE tr Y k n h) := by
  have hr1 : 1 + r ≠ 0 := by linarith
  have hν0 : 0 ≤ 1 / (1 + r) := by positivity
  have hν1 : 1 / (1 + r) < 1 := by rw [div_lt_one (by linarith)]; linarith
  have hmart := quadratic_consumption_martingale tr ha0 heul
  have hk := expected_budget_k_step tr hr1 hbud
  have hC : HasSum (fun k => (1 / (1 + r)) ^ k * condE tr C k n h)
      (C n h * (1 - 1 / (1 + r))⁻¹) := by
    have := (hasSum_geometric_of_lt_one hν0 hν1).mul_left (C n h)
    refine this.congr_fun fun k => ?_
    simp only [hmart]
    ring
  have hL := hC.tendsto_sum_nat
  have hR : Tendsto (fun K => (1 + r) * B n h
      + ∑ k ∈ range K, (1 / (1 + r)) ^ k * condE tr Y k n h
      - (1 + r) * ((1 / (1 + r)) ^ K * condE tr B K n h)) atTop
      (𝓝 ((1 + r) * B n h + ∑' k, (1 / (1 + r)) ^ k * condE tr Y k n h - (1 + r) * 0)) :=
    (tendsto_const_nhds.add (income_series_summable tr hr hY n h).hasSum.tendsto_sum_nat).sub
      (tendsto_const_nhds.mul (htv n h))
  have e : (fun K => ∑ k ∈ range K, (1 / (1 + r)) ^ k * condE tr C k n h) = fun K =>
      (1 + r) * B n h + ∑ k ∈ range K, (1 / (1 + r)) ^ k * condE tr Y k n h
        - (1 + r) * ((1 / (1 + r)) ^ K * condE tr B K n h) := by
    funext K
    rw [hk K n h]
    ring
  rw [e] at hL
  have := tendsto_nhds_unique hL hR
  have h1 : 1 - 1 / (1 + r) = r / (1 + r) := by field_simp; ring
  rw [h1, mul_zero, sub_zero] at this
  rw [← this]
  field_simp [hr.ne']

/-- The recursion of human wealth `H_t = Σ_{k≥0} ν^k E_t[Y_{t+k}]`, Exercise 3, O&R p. 346:
`H(h) = Y(h) + νΣ_s π(s|h) H(h, s)` when income is bounded and `r > 0`. -/
theorem human_wealth_recursion {r : ℝ} (hr : 0 < r) {Y : TreeProcess S} {BY : ℝ}
    (hY : ∀ n h, |Y n h| ≤ BY) (n : ℕ) (h : Fin n → S) :
    ∑' k, (1 / (1 + r)) ^ k * condE tr Y k n h = Y n h + 1 / (1 + r) *
      ∑ s, tr.q n h s * ∑' k, (1 / (1 + r)) ^ k * condE tr Y k (n + 1) (Fin.snoc h s) := by
  rw [(income_series_summable tr hr hY n h).tsum_eq_zero_add]
  simp only [pow_zero, one_mul, condE.zero_eq]
  congr 1
  have hs := fun s => ((income_series_summable tr hr hY (n + 1) (Fin.snoc h s)).hasSum.mul_left
    (tr.q n h s))
  have := (hasSum_sum (s := Finset.univ) fun s _ => hs s).mul_left (1 / (1 + r))
  refine HasSum.tsum_eq (this.congr_fun fun k => ?_)
  rw [condE.succ_eq, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  ring

/-- **Exercise 3(a), infinite horizon: the permanent-income rule is optimal**, O&R p. 346.
With `r > 0`, bounded income, and bonds evolving by `B_{t+1} = (1 + r)B_t + Y_t − C_t` under
the rule `C_t = [r/(1 + r)][(1 + r)B_t + Σ_{k≥0}(1 + r)^{−k}E_t[Y_{t+k}]]`, consumption
satisfies the quadratic-utility bond Euler equation `1 − a₀C_t = E_t[1 − a₀C_{t+1}]` at every
history, and the transversality condition `(1 + r)^{−K}E_t[B_{t+K}] → 0` holds (derived, not
assumed): the rule and the conditions of `quadratic_infinite_horizon_consumption` are
consistent. -/
theorem quadratic_permanent_income_rule {r : ℝ} (hr : 0 < r) (a0 : ℝ) {B Y C : TreeProcess S}
    {BY : ℝ} (hY : ∀ n h, |Y n h| ≤ BY)
    (hC : ∀ n h, C n h = r / (1 + r) * ((1 + r) * B n h
      + ∑' k, (1 / (1 + r)) ^ k * condE tr Y k n h))
    (hbud : ∀ n (h : Fin n → S) s,
      B (n + 1) (Fin.snoc h s) = (1 + r) * B n h + Y n h - C n h) :
    (∀ n (h : Fin n → S),
      1 - a0 * C n h = ∑ s, tr.q n h s * (1 - a0 * C (n + 1) (Fin.snoc h s))) ∧
    ∀ n h, Tendsto (fun K => (1 / (1 + r)) ^ K * condE tr B K n h) atTop (𝓝 0) := by
  have hr1 : 1 + r ≠ 0 := by linarith
  have hν0 : 0 ≤ 1 / (1 + r) := by positivity
  have hν1 : 1 / (1 + r) < 1 := by rw [div_lt_one (by linarith)]; linarith
  have hmart1 : ∀ n (h : Fin n → S), C n h = ∑ s, tr.q n h s * C (n + 1) (Fin.snoc h s) := by
    intro n h
    have hs : ∀ s, tr.q n h s * C (n + 1) (Fin.snoc h s)
        = r / (1 + r) * ((1 + r) * ((1 + r) * B n h + Y n h - C n h)) * tr.q n h s
          + r / (1 + r) * (tr.q n h s
            * ∑' k, (1 / (1 + r)) ^ k * condE tr Y k (n + 1) (Fin.snoc h s)) := by
      intro s
      rw [hC (n + 1), hbud]
      ring
    rw [Finset.sum_congr rfl fun s _ => hs s, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, tr.q_sum]
    have hsumH : ∑ s, tr.q n h s * ∑' k, (1 / (1 + r)) ^ k * condE tr Y k (n + 1) (Fin.snoc h s)
        = (1 + r) * (∑' k, (1 / (1 + r)) ^ k * condE tr Y k n h - Y n h) := by
      rw [human_wealth_recursion tr hr hY n h]
      field_simp
      ring
    rw [hsumH, hC n h]
    field_simp
    ring
  have hmart : ∀ k n h, condE tr C k n h = C n h := by
    have h1 : condE tr C 1 = C := by
      funext n h
      rw [condE.one_eq, ← hmart1]
    intro k
    induction k with
    | zero => intro n h; rfl
    | succ k ih => intro n h; rw [condE.succ_eq_iter, h1, ih]
  refine ⟨fun n h => ?_, fun n h => ?_⟩
  · have e : ∑ s, tr.q n h s * (1 - a0 * C (n + 1) (Fin.snoc h s))
        = 1 - a0 * ∑ s, tr.q n h s * C (n + 1) (Fin.snoc h s) := by
      calc ∑ s, tr.q n h s * (1 - a0 * C (n + 1) (Fin.snoc h s))
          = ∑ s, tr.q n h s - a0 * ∑ s, tr.q n h s * C (n + 1) (Fin.snoc h s) := by
            rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
            exact Finset.sum_congr rfl fun s _ => by ring
        _ = 1 - a0 * ∑ s, tr.q n h s * C (n + 1) (Fin.snoc h s) := by rw [tr.q_sum]
    rw [e, ← hmart1]
  · have hk := expected_budget_k_step tr hr1 hbud
    have e : (fun K => (1 / (1 + r)) ^ K * condE tr B K n h) = fun K =>
        ((1 + r) * B n h + ∑ k ∈ range K, (1 / (1 + r)) ^ k * condE tr Y k n h
          - C n h * ∑ k ∈ range K, (1 / (1 + r)) ^ k) / (1 + r) := by
      funext K
      have := hk K n h
      simp only [hmart] at this
      have e2 : ∑ k ∈ range K, (1 / (1 + r)) ^ k * C n h
          = C n h * ∑ k ∈ range K, (1 / (1 + r)) ^ k := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
      rw [e2] at this
      field_simp
      linarith
    rw [e]
    have hlim : Tendsto (fun K => ((1 + r) * B n h
        + ∑ k ∈ range K, (1 / (1 + r)) ^ k * condE tr Y k n h
        - C n h * ∑ k ∈ range K, (1 / (1 + r)) ^ k) / (1 + r)) atTop
        (𝓝 (((1 + r) * B n h + ∑' k, (1 / (1 + r)) ^ k * condE tr Y k n h
          - C n h * (1 - 1 / (1 + r))⁻¹) / (1 + r))) :=
      ((tendsto_const_nhds.add (income_series_summable tr hr hY n h).hasSum.tendsto_sum_nat).sub
        (tendsto_const_nhds.mul
          (hasSum_geometric_of_lt_one hν0 hν1).tendsto_sum_nat)).div_const _
    have hz : ((1 + r) * B n h + ∑' k, (1 / (1 + r)) ^ k * condE tr Y k n h
        - C n h * (1 - 1 / (1 + r))⁻¹) / (1 + r) = 0 := by
      rw [hC n h]
      have h1 : 1 - 1 / (1 + r) = r / (1 + r) := by field_simp; ring
      rw [h1]
      field_simp [hr.ne']
      ring
    rwa [hz] at hlim

/-! ## Unconditional expectations at the root -/

/-- **Unconditional expectations, O&R §5.4.3 (p. 316) with Appendix 5C (p. 341)**: at the
date-1 history the `k`-step expectation is `E_1[f_{k+1}] = Σ_{h_{k+1}} π(h_{k+1} | h_1)
f(h_{k+1})`, the sum over date-`(k + 1)` histories weighted by `Tree.histProb`. -/
theorem condE_root_eq_sum_histProb (tr : EventTree.Tree S) (f : TreeProcess S) (k : ℕ)
    (h0 : Fin 0 → S) : condE tr f k 0 h0 = ∑ g : Fin k → S, tr.histProb g * f k g := by
  induction k generalizing f with
  | zero =>
    rw [Fintype.sum_unique, Subsingleton.elim h0 default]
    simp [EventTree.Tree.histProb, EventTree.Tree.condProb, condE.zero_eq]
  | succ k ih =>
    rw [condE.succ_eq_iter, ih]
    rw [← (Fin.snocEquiv (fun _ : Fin (k + 1) => S)).sum_comp, Fintype.sum_prod_type,
      Finset.sum_comm]
    refine Finset.sum_congr rfl fun g _ => ?_
    have e : ∀ s : S, (Fin.snocEquiv fun _ : Fin (k + 1) => S) (s, g) = Fin.snoc g s :=
      fun _ => rfl
    simp only [e, EventTree.Tree.histProb, condProb_snoc tr _ _ (Nat.zero_le k), condE.one_eq,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => (mul_assoc _ _ _).symm

/-! ## (61) with the constant consumption share derived -/

/-- **O&R (61), p. 317, with `C = μY^W` derived.** Let countries `j ∈ ι` have CRRA marginal
utility `C^{−ρ}` (`ρ ≠ 0`), `β > 0`, positive consumption, and satisfy the complete-markets
first-order conditions (84) in date-1 prices `P(h)`,
`P(h)C_j(h_1)^{−ρ} = π(h | h_1)β^{t−1}C_j(h)^{−ρ}`, at every history, with world market clearing
`Σ_j C_j = Y^W`, and let every history have positive probability. Then country `i`'s
consumption share is constant, `C_i = μY^W` with `μ = C_i(h_1)/Y^W(h_1)`
(`EventTree.crra_constant_share_infinite`), and any claim price `V` satisfying `i`'s Euler
equation (57) and the no-bubble condition obeys (61):
`V_t = Σ_{s>t} β^{s−t}E_t[(Y^W_s/Y^W_t)^{−ρ}Y_s]`. -/
theorem price_crra_world_output_derived {ι : Type} [Fintype ι] (tr : EventTree.Tree S)
    {β ρ : ℝ} (hβ : 0 < β) (hρ : ρ ≠ 0) (P YW : TreeProcess S) (C : ι → TreeProcess S)
    (hC : ∀ j n h, 0 < C j n h)
    (hfoc : ∀ j n h, P n h * C j 0 Fin.elim0 ^ (-ρ) = tr.histProb h * β ^ n * C j n h ^ (-ρ))
    (hclear : ∀ n h, ∑ j, C j n h = YW n h) (hπ : ∀ n (h : Fin n → S), 0 < tr.histProb h)
    (i : ι) {Y V : TreeProcess S} (he : EulerEq tr β (fun m g => C i m g ^ (-ρ)) Y V)
    (n : ℕ) (h : Fin n → S)
    (hnb : Tendsto (fun K => β ^ K * condE tr (fun m g => C i m g ^ (-ρ) * V m g) K n h
      / C i n h ^ (-ρ)) atTop (𝓝 0)) :
    Tendsto (fun K => ∑ k ∈ range K,
      β ^ (k + 1) * condE tr (fun m g => (YW m g / YW n h) ^ (-ρ) * Y m g) (k + 1) n h)
      atTop (𝓝 (V n h)) := by
  have hYW : ∀ n h, 0 < YW n h := fun n h => by
    rw [← hclear n h]
    exact Finset.sum_pos (fun j _ => hC j n h) ⟨i, Finset.mem_univ i⟩
  obtain ⟨μ, hμ⟩ : ∃ μ, μ = C i 0 Fin.elim0 / YW 0 Fin.elim0 := ⟨_, rfl⟩
  have hμpos : 0 < μ := hμ ▸ div_pos (hC i 0 _) (hYW 0 _)
  have hshare : ∀ m (g : Fin m → S), C i m g = μ * YW m g := fun m g => by
    rw [hμ]
    exact EventTree.crra_constant_share_infinite tr hβ hρ P YW C hC hfoc hclear i m g (hπ m g)
  simp only [hshare] at he hnb
  exact price_crra_world_output_tree tr hμpos hYW he n h hnb

/-! ## Exercise 6(b): global optimality and uniqueness of the no-trade allocation -/

/-- **The present value of a plan, O&R (56)–(59), p. 316**: if the cost `A` of the portfolio
chosen at each history and the spending `e` satisfy the pricing identity
`M_tA_t = βE_t[M_{t+1}(e_{t+1} + A_{t+1})]` (the Euler equation with `e` as dividend), then
`Σ_{k≤T} β^k E_t[M_{t+k}e_{t+k}] = M_t(A_t + e_t) − β^T E_t[M_{t+T}A_{t+T}]`. -/
theorem plan_value_identity {β : ℝ} {M e A : TreeProcess S} (he : EulerEq tr β M e A)
    (T n : ℕ) (h : Fin n → S) :
    ∑ k ∈ range (T + 1), β ^ k * condE tr (fun m g => M m g * e m g) k n h
      = M n h * (A n h + e n h) - β ^ T * condE tr (fun m g => M m g * A m g) T n h := by
  have hk := mu_price_k_step tr he T n h
  rw [pvPartial] at hk
  rw [Finset.sum_range_succ']
  simp only [pow_zero, one_mul, condE.zero_eq]
  linarith

/-- Discounted expectations of a bounded process are summable (`0 ≤ β < 1`), O&R (55),
p. 315: `Σ_t β^t E_1[f_t]` converges when `|f| ≤ K`. -/
theorem summable_discounted_condE {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {f : TreeProcess S}
    {K : ℝ} (hf : ∀ n h, |f n h| ≤ K) (n : ℕ) (h : Fin n → S) :
    Summable (fun k => β ^ k * condE tr f k n h) := by
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hβ0 hβ1).mul_right K)
    fun k => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hβ0]
  exact mul_le_mul_of_nonneg_left (condE.abs_le_of_bound tr hf k n h) (pow_nonneg hβ0 k)

/-- Expectations of a positive function under the chain are positive (Exercise 6,
O&R p. 347): `Σ_{s′} P(s, s′) f(s′) > 0` when `f > 0`. -/
theorem chain_expect_pos (mc : EndowmentChain S) {f : S → ℝ} (hf : ∀ s, 0 < f s) (s : S) :
    0 < ∑ s', mc.P s s' * f s' := by
  obtain ⟨s', hs'⟩ : ∃ s', 0 < mc.P s s' := by
    by_contra hcon
    push Not at hcon
    have h1 := mc.P_sum s
    have : ∑ s', mc.P s s' ≤ 0 := Finset.sum_nonpos fun s' _ => hcon s'
    linarith
  exact lt_of_lt_of_le (mul_pos hs' (hf s'))
    (Finset.single_le_sum (f := fun s' => mc.P s s' * f s')
      (fun i _ => mul_nonneg (mc.P_nonneg s i) (hf i).le) (Finset.mem_univ s'))

/-- A consumption–portfolio plan for one country in the Lucas model, Exercise 6, O&R p. 347:
at each history, consumption of `X` and `Y`, and the holdings of the Home claim, the Foreign
claim and bonds carried to the next date. -/
structure LucasPlan (S : Type) where
  cX : TreeProcess S
  cY : TreeProcess S
  x : TreeProcess S
  y : TreeProcess S
  B : TreeProcess S

/-- The admissible plans of Exercise 6(b), O&R p. 347, on the event tree of the endowment
chain from `s₀`: positive consumption; the finance constraint (56) at date 1 starting from the
pooled half portfolios and no bonds, and at every later history (the bond bought in state
`σ` pays `1 + r(σ)`); bounded holdings (the standard admissibility restriction, which rules
out Ponzi schemes); and a convergent expected-utility series. Prices `V_X, V_Y, p` and
the bond rate are functions of the current state. -/
def LucasAdmissible (mc : EndowmentChain S) (s₀ : S) (β : ℝ) (u : ℝ → ℝ → ℝ)
    (X Y VX VY p r : S → ℝ) (pl : LucasPlan S) : Prop :=
  (∀ n h, 0 < pl.cX n h ∧ 0 < pl.cY n h) ∧
  lucasFinance 0 0 (1 / 2) (1 / 2) (VX s₀) (VY s₀) (X s₀) (Y s₀) (p s₀) (pl.cX 0 Fin.elim0)
    (pl.cY 0 Fin.elim0) (pl.B 0 Fin.elim0) (pl.x 0 Fin.elim0) (pl.y 0 Fin.elim0) ∧
  (∀ n (h : Fin n → S) s, lucasFinance (r (lastState s₀ n h)) (pl.B n h) (pl.x n h)
    (pl.y n h) (VX s) (VY s) (X s) (Y s) (p s) (pl.cX (n + 1) (Fin.snoc h s))
    (pl.cY (n + 1) (Fin.snoc h s)) (pl.B (n + 1) (Fin.snoc h s)) (pl.x (n + 1) (Fin.snoc h s))
    (pl.y (n + 1) (Fin.snoc h s))) ∧
  (∃ K, ∀ n h, |pl.x n h| ≤ K ∧ |pl.y n h| ≤ K ∧ |pl.B n h| ≤ K) ∧
  Summable (fun n => β ^ n *
    condE (mc.toTree s₀) (fun m g => u (pl.cX m g) (pl.cY m g)) n 0 Fin.elim0)

/-- Expected lifetime utility (55), O&R p. 315, of a plan:
`U_1 = Σ_t β^{t−1}E_1[u(C_{X,t}, C_{Y,t})]`. -/
noncomputable def lucasUtility (mc : EndowmentChain S) (s₀ : S) (β : ℝ) (u : ℝ → ℝ → ℝ)
    (pl : LucasPlan S) : ℝ :=
  ∑' n, β ^ n * condE (mc.toTree s₀) (fun m g => u (pl.cX m g) (pl.cY m g)) n 0 Fin.elim0

/-- The no-trade plan of Exercise 6(b), O&R p. 347: consume `X/2`, `Y/2`, keep half of each
claim and hold no bonds. -/
noncomputable def lucasNoTrade (s₀ : S) (X Y : S → ℝ) : LucasPlan S :=
  ⟨fun n h => X (lastState s₀ n h) / 2, fun n h => Y (lastState s₀ n h) / 2,
    fun _ _ => 1 / 2, fun _ _ => 1 / 2, fun _ _ => 0⟩

/-- **The pricing identity for any admissible plan, Exercise 6(b), O&R p. 347**: if the
claim prices and bond rate satisfy the stationary Euler equations of part (a) with
marginal utility `m_X`, then along any plan satisfying the finance constraints, the cost
`A = B + xV_X + yV_Y` of the portfolio chosen and spending `e = C_X + pC_Y` satisfy
`m_X A_t = βE_t[m_X(e_{t+1} + A_{t+1})]`. -/
theorem lucas_plan_euler (mc : EndowmentChain S) (s₀ : S) (β : ℝ) (u : ℝ → ℝ → ℝ)
    {X Y VX VY p r mX : S → ℝ}
    (hEX : ∀ s, mX s * VX s = β * ∑ s', mc.P s s' * (mX s' * (X s' + VX s')))
    (hEY : ∀ s, mX s * VY s = β * ∑ s', mc.P s s' * (mX s' * (p s' * Y s' + VY s')))
    (hEB : ∀ s, mX s = (1 + r s) * (β * ∑ s', mc.P s s' * mX s'))
    {pl : LucasPlan S} (hpl : LucasAdmissible mc s₀ β u X Y VX VY p r pl) :
    EulerEq (mc.toTree s₀) β (fun n h => mX (lastState s₀ n h))
      (fun n h => pl.cX n h + p (lastState s₀ n h) * pl.cY n h)
      (fun n h => pl.B n h + pl.x n h * VX (lastState s₀ n h)
        + pl.y n h * VY (lastState s₀ n h)) := by
  intro n h
  simp only [EndowmentChain.toTree_q, lastState_snoc]
  have hpay : ∀ s, pl.cX (n + 1) (Fin.snoc h s) + p s * pl.cY (n + 1) (Fin.snoc h s)
      + (pl.B (n + 1) (Fin.snoc h s) + pl.x (n + 1) (Fin.snoc h s) * VX s
        + pl.y (n + 1) (Fin.snoc h s) * VY s)
      = (1 + r (lastState s₀ n h)) * pl.B n h + pl.x n h * (X s + VX s)
        + pl.y n h * (p s * Y s + VY s) := by
    intro s
    have := hpl.2.2.1 n h s
    unfold lucasFinance at this
    linarith
  simp only [hpay]
  have hsplit : ∑ s, mc.P (lastState s₀ n h) s * (mX s * ((1 + r (lastState s₀ n h))
      * pl.B n h + pl.x n h * (X s + VX s) + pl.y n h * (p s * Y s + VY s)))
      = (1 + r (lastState s₀ n h)) * pl.B n h * ∑ s, mc.P (lastState s₀ n h) s * mX s
        + pl.x n h * ∑ s, mc.P (lastState s₀ n h) s * (mX s * (X s + VX s))
        + pl.y n h * ∑ s, mc.P (lastState s₀ n h) s * (mX s * (p s * Y s + VY s)) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [hsplit]
  linear_combination pl.B n h * hEB (lastState s₀ n h) + pl.x n h * hEX (lastState s₀ n h)
    + pl.y n h * hEY (lastState s₀ n h)

/-- **Exercise 6(b), O&R p. 347: the no-trade allocation is optimal over all admissible
infinite plans.** Let `0 < β < 1`, `X, Y > 0`, `u` concave with partial derivatives
`u_X, u_Y` in the supporting-hyperplane sense, `m_X = u_X(X/2, Y/2) > 0`,
`m_Y = u_Y(X/2, Y/2)`, `p = m_Y/m_X`, `V_X, V_Y` the claim prices of part (c) and
`1 + r = m_X/(βE[m_X])`. Then the no-trade plan is admissible and gives each country at least
the expected utility of every admissible plan (finance constraints each period, bounded
holdings, convergent utility). The transversality property
`β^T E_1[m_X(A*_T − A_T)] → 0` is proved from boundedness of prices and holdings. -/
theorem lucas_noTrade_optimal (mc : EndowmentChain S) (s₀ : S) {β : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (u uX uY : ℝ → ℝ → ℝ) {X Y mX mY p VX VY r : S → ℝ}
    (hX : ∀ s, 0 < X s) (hY : ∀ s, 0 < Y s)
    (htan : ∀ a b a' b', 0 < a → 0 < b → 0 < a' → 0 < b' →
      u a' b' ≤ u a b + uX a b * (a' - a) + uY a b * (b' - b))
    (hmX : ∀ s, mX s = uX (X s / 2) (Y s / 2)) (hmY : ∀ s, mY s = uY (X s / 2) (Y s / 2))
    (hmXpos : ∀ s, 0 < mX s) (hp : ∀ s, p s = mY s / mX s)
    (hVX : VX = mc.markovPrice β mX X) (hVY : VY = mc.markovPrice β mX (fun s => p s * Y s))
    (hr : ∀ s, 1 + r s = mX s / (β * ∑ s', mc.P s s' * mX s')) :
    LucasAdmissible mc s₀ β u X Y VX VY p r (lucasNoTrade s₀ X Y) ∧
      ∀ pl, LucasAdmissible mc s₀ β u X Y VX VY p r pl →
        lucasUtility mc s₀ β u pl ≤ lucasUtility mc s₀ β u (lucasNoTrade s₀ X Y) := by
  have hEX : ∀ s, mX s * VX s = β * ∑ s', mc.P s s' * (mX s' * (X s' + VX s')) := by
    subst hVX; exact (markov_price_unique mc hβ0.le hβ1 mX X hmXpos).2.1
  have hEY : ∀ s, mX s * VY s = β * ∑ s', mc.P s s' * (mX s' * (p s' * Y s' + VY s')) := by
    subst hVY; exact (markov_price_unique mc hβ0.le hβ1 mX (fun s => p s * Y s) hmXpos).2.1
  have hEB : ∀ s, mX s = (1 + r s) * (β * ∑ s', mc.P s s' * mX s') := fun s => by
    rw [hr s, div_mul_cancel₀ _ (mul_pos hβ0 (chain_expect_pos mc hmXpos s)).ne']
  set tr := mc.toTree s₀ with htr
  -- bounds on state functions
  have bS : ∀ (f : S → ℝ) n (h : Fin n → S), |f (lastState s₀ n h)| ≤ ∑ s', |f s'| :=
    fun f n h => abs_le_sum_abs f _
  set ustar : TreeProcess S := fun m g => u (X (lastState s₀ m g) / 2) (Y (lastState s₀ m g) / 2)
    with hustar
  have hsumStar : Summable (fun n => β ^ n * condE tr ustar n 0 Fin.elim0) :=
    summable_discounted_condE tr hβ0.le hβ1
      (fun n h => bS (fun s => u (X s / 2) (Y s / 2)) n h) 0 Fin.elim0
  have hadm : LucasAdmissible mc s₀ β u X Y VX VY p r (lucasNoTrade s₀ X Y) := by
    refine ⟨fun n h => ⟨by simp [lucasNoTrade, hX], by simp [lucasNoTrade, hY]⟩, ?_, ?_,
      ⟨1 / 2, fun n h => by norm_num [lucasNoTrade]⟩, hsumStar⟩
    · simp only [lucasFinance, lucasNoTrade, lastState]
      ring
    · intro n h s
      simp only [lucasFinance, lucasNoTrade, lastState_snoc]
      ring
  refine ⟨hadm, fun pl hpl => ?_⟩
  obtain ⟨K, hK⟩ := hpl.2.2.2.1
  -- the two pricing identities
  have eP := lucas_plan_euler mc s₀ β u hEX hEY hEB hpl
  have eS := lucas_plan_euler mc s₀ β u hEX hEY hEB hadm
  set M : TreeProcess S := fun n h => mX (lastState s₀ n h) with hM
  set e1 : TreeProcess S := fun n h => pl.cX n h + p (lastState s₀ n h) * pl.cY n h with he1
  set A1 : TreeProcess S := fun n h => pl.B n h + pl.x n h * VX (lastState s₀ n h)
    + pl.y n h * VY (lastState s₀ n h) with hA1
  set e0 : TreeProcess S := fun n h => (lucasNoTrade s₀ X Y).cX n h
    + p (lastState s₀ n h) * (lucasNoTrade s₀ X Y).cY n h with he0
  set A0 : TreeProcess S := fun n h => (lucasNoTrade s₀ X Y).B n h
    + (lucasNoTrade s₀ X Y).x n h * VX (lastState s₀ n h)
    + (lucasNoTrade s₀ X Y).y n h * VY (lastState s₀ n h) with hA0
  -- date-1 wealth is the same
  have hroot : A1 0 Fin.elim0 + e1 0 Fin.elim0 = A0 0 Fin.elim0 + e0 0 Fin.elim0 := by
    have h1 := hpl.2.1
    have h2 := hadm.2.1
    simp only [lucasFinance] at h1 h2
    simp only [hA1, he1, hA0, he0, lastState]
    linarith
  -- concavity, date by date
  have hpt : ∀ m (g : Fin m → S), u (pl.cX m g) (pl.cY m g) - ustar m g
      ≤ M m g * e1 m g - M m g * e0 m g := by
    intro m g
    set σ := lastState s₀ m g
    have t := htan (X σ / 2) (Y σ / 2) (pl.cX m g) (pl.cY m g) (by linarith [hX σ])
      (by linarith [hY σ]) (hpl.1 m g).1 (hpl.1 m g).2
    rw [← hmX σ, ← hmY σ] at t
    have hmY' : mY σ = p σ * mX σ := by rw [hp σ]; field_simp [(hmXpos σ).ne']
    rw [hmY'] at t
    have e : M m g * e1 m g - M m g * e0 m g
        = mX σ * (pl.cX m g - X σ / 2) + p σ * mX σ * (pl.cY m g - Y σ / 2) := by
      simp only [hM, he1, he0, lucasNoTrade]
      ring
    rw [e]
    simp only [hustar]
    linarith
  have hterm : ∀ n, β ^ n * condE tr (fun m g => u (pl.cX m g) (pl.cY m g)) n 0 Fin.elim0
      - β ^ n * condE tr ustar n 0 Fin.elim0
      ≤ β ^ n * condE tr (fun m g => M m g * e1 m g) n 0 Fin.elim0
        - β ^ n * condE tr (fun m g => M m g * e0 m g) n 0 Fin.elim0 := by
    intro n
    rw [← mul_sub, ← mul_sub, ← condE.sub_apply, ← condE.sub_apply]
    exact mul_le_mul_of_nonneg_left (condE.mono_apply tr hpt n 0 Fin.elim0)
      (pow_nonneg hβ0.le n)
  -- transversality from bounded holdings and prices
  set KA : ℝ := (∑ s', |mX s'|) * (K + K * ∑ s', |VX s'| + K * ∑ s', |VY s'|)
    + (∑ s', |mX s'|) * (1 / 2 * ∑ s', |VX s'| + 1 / 2 * ∑ s', |VY s'|) with hKA
  have hbnd : ∀ m (g : Fin m → S), |M m g * A0 m g - M m g * A1 m g| ≤ KA := by
    intro m g
    have hx := (hK m g).1
    have hy := (hK m g).2.1
    have hB := (hK m g).2.2
    have hm := bS mX m g
    have hv := bS VX m g
    have hw := bS VY m g
    have h1 : |M m g * A1 m g| ≤ (∑ s', |mX s'|) * (K + K * ∑ s', |VX s'|
        + K * ∑ s', |VY s'|) := by
      rw [abs_mul]
      refine mul_le_mul hm ?_ (abs_nonneg _) (Finset.sum_nonneg fun _ _ => abs_nonneg _)
      calc |A1 m g| ≤ |pl.B m g| + |pl.x m g| * |VX (lastState s₀ m g)|
            + |pl.y m g| * |VY (lastState s₀ m g)| := by
            simp only [hA1]
            refine (abs_add_le _ _).trans ?_
            rw [abs_mul]
            gcongr
            refine (abs_add_le _ _).trans ?_
            rw [abs_mul]
        _ ≤ K + K * ∑ s', |VX s'| + K * ∑ s', |VY s'| := by
            gcongr
            · exact (abs_nonneg _).trans hx
            · exact (abs_nonneg _).trans hy
    have h0 : |M m g * A0 m g| ≤ (∑ s', |mX s'|) * (1 / 2 * ∑ s', |VX s'|
        + 1 / 2 * ∑ s', |VY s'|) := by
      rw [abs_mul]
      refine mul_le_mul hm ?_ (abs_nonneg _) (Finset.sum_nonneg fun _ _ => abs_nonneg _)
      simp only [hA0, lucasNoTrade, zero_add]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      gcongr
    calc |M m g * A0 m g - M m g * A1 m g| ≤ |M m g * A0 m g| + |M m g * A1 m g| :=
          abs_sub _ _
      _ ≤ KA := by rw [hKA]; linarith
  have htv : Tendsto (fun T => β ^ T * condE tr (fun m g => M m g * A0 m g
      - M m g * A1 m g) T 0 Fin.elim0) atTop (𝓝 0) := by
    have hlim : Tendsto (fun T : ℕ => β ^ T * KA) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).mul_const KA
    refine squeeze_zero_norm (fun T => ?_) hlim
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hβ0.le]
    exact mul_le_mul_of_nonneg_left (condE.abs_le_of_bound tr hbnd T 0 Fin.elim0)
      (pow_nonneg hβ0.le T)
  -- partial sums
  have hpart : ∀ T, ∑ n ∈ range (T + 1), (β ^ n * condE tr
      (fun m g => u (pl.cX m g) (pl.cY m g)) n 0 Fin.elim0
      - β ^ n * condE tr ustar n 0 Fin.elim0)
      ≤ β ^ T * condE tr (fun m g => M m g * A0 m g - M m g * A1 m g) T 0 Fin.elim0 := by
    intro T
    refine (Finset.sum_le_sum fun n _ => hterm n).trans (le_of_eq ?_)
    rw [Finset.sum_sub_distrib, plan_value_identity tr eP, plan_value_identity tr eS,
      condE.sub_apply, hroot]
    ring
  have hL : Tendsto (fun T => ∑ n ∈ range (T + 1), (β ^ n * condE tr
      (fun m g => u (pl.cX m g) (pl.cY m g)) n 0 Fin.elim0
      - β ^ n * condE tr ustar n 0 Fin.elim0)) atTop
      (𝓝 (lucasUtility mc s₀ β u pl - lucasUtility mc s₀ β u (lucasNoTrade s₀ X Y))) :=
    (tendsto_add_atTop_iff_nat 1).mpr (hpl.2.2.2.2.hasSum.sub hsumStar.hasSum).tendsto_sum_nat
  have := le_of_tendsto_of_tendsto' hL htv hpart
  linarith

/-- **Exercise 6(b), O&R p. 347: uniqueness of the equilibrium allocation.** Home and Foreign
have identical tastes `u`, strictly concave in the midpoint sense, and identical initial
portfolios, so they face the same admissible set (for any state-contingent prices `V_X, V_Y,
p` and bond rate `r`). If Home's plan `H` and Foreign's plan `F` are each optimal in that set
and goods markets clear (`C_X^H + C_X^F = X`, `C_Y^H + C_Y^F = Y`), then at every history of
positive probability `C_X = X/2` and `C_Y = Y/2` for both countries. (The average of the two
plans is admissible, consumes `(X/2, Y/2)`, and would otherwise be strictly better.) This is
the dynamic version of `OLGRiskSharing.lucas_allocation`. -/
theorem lucas_allocation_unique (mc : EndowmentChain S) (s₀ : S) {β : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (u : ℝ → ℝ → ℝ) {X Y VX VY p r : S → ℝ}
    (hstrict : ∀ a b a' b', 0 < a → 0 < b → 0 < a' → 0 < b' → (a ≠ a' ∨ b ≠ b') →
      (u a b + u a' b') / 2 < u ((a + a') / 2) ((b + b') / 2))
    {H F : LucasPlan S} (hH : LucasAdmissible mc s₀ β u X Y VX VY p r H)
    (hF : LucasAdmissible mc s₀ β u X Y VX VY p r F)
    (hHopt : ∀ pl, LucasAdmissible mc s₀ β u X Y VX VY p r pl →
      lucasUtility mc s₀ β u pl ≤ lucasUtility mc s₀ β u H)
    (hFopt : ∀ pl, LucasAdmissible mc s₀ β u X Y VX VY p r pl →
      lucasUtility mc s₀ β u pl ≤ lucasUtility mc s₀ β u F)
    (hcX : ∀ n h, H.cX n h + F.cX n h = X (lastState s₀ n h))
    (hcY : ∀ n h, H.cY n h + F.cY n h = Y (lastState s₀ n h))
    (n : ℕ) (h : Fin n → S) (hπ : 0 < (mc.toTree s₀).histProb h) :
    H.cX n h = X (lastState s₀ n h) / 2 ∧ H.cY n h = Y (lastState s₀ n h) / 2 ∧
      F.cX n h = X (lastState s₀ n h) / 2 ∧ F.cY n h = Y (lastState s₀ n h) / 2 := by
  set tr := mc.toTree s₀ with htr
  -- the average plan
  set mid : LucasPlan S := ⟨fun m g => (H.cX m g + F.cX m g) / 2,
    fun m g => (H.cY m g + F.cY m g) / 2, fun m g => (H.x m g + F.x m g) / 2,
    fun m g => (H.y m g + F.y m g) / 2, fun m g => (H.B m g + F.B m g) / 2⟩ with hmid
  set ustar : TreeProcess S := fun m g => u (X (lastState s₀ m g) / 2)
    (Y (lastState s₀ m g) / 2) with hustar
  have hmidu : (fun m g => u (mid.cX m g) (mid.cY m g)) = ustar := by
    funext m g
    simp only [hmid, hustar, hcX, hcY]
  have hsumStar : Summable (fun n => β ^ n * condE tr ustar n 0 Fin.elim0) :=
    summable_discounted_condE tr hβ0.le hβ1
      (fun n h => abs_le_sum_abs (fun s => u (X s / 2) (Y s / 2)) _) 0 Fin.elim0
  obtain ⟨KH, hKH⟩ := hH.2.2.2.1
  obtain ⟨KF, hKF⟩ := hF.2.2.2.1
  have hbd : ∀ a b : ℝ, |a| ≤ KH → |b| ≤ KF → |(a + b) / 2| ≤ (KH + KF) / 2 := by
    intro a b ha hb
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact div_le_div_of_nonneg_right ((abs_add_le a b).trans (add_le_add ha hb)) (by norm_num)
  have hadm : LucasAdmissible mc s₀ β u X Y VX VY p r mid := by
    refine ⟨fun m g => ⟨?_, ?_⟩, ?_, fun m g s => ?_, ⟨(KH + KF) / 2, fun m g =>
      ⟨hbd _ _ (hKH m g).1 (hKF m g).1, hbd _ _ (hKH m g).2.1 (hKF m g).2.1,
        hbd _ _ (hKH m g).2.2 (hKF m g).2.2⟩⟩, ?_⟩
    · simp only [hmid]; linarith [(hH.1 m g).1, (hF.1 m g).1]
    · simp only [hmid]; linarith [(hH.1 m g).2, (hF.1 m g).2]
    · have h1 := hH.2.1
      have h2 := hF.2.1
      simp only [lucasFinance, hmid] at h1 h2 ⊢
      linear_combination (h1 + h2) / 2
    · have h1 := hH.2.2.1 m g s
      have h2 := hF.2.2.1 m g s
      simp only [lucasFinance, hmid] at h1 h2 ⊢
      linear_combination (h1 + h2) / 2
    · rw [hmidu]; exact hsumStar
  have hUmid : lucasUtility mc s₀ β u mid = ∑' n, β ^ n * condE tr ustar n 0 Fin.elim0 := by
    unfold lucasUtility
    rw [hmidu]
  have hle1 := hHopt mid hadm
  have hle2 := hHopt F hF
  have hle3 := hFopt H hH
  -- pointwise weak midpoint concavity
  have hweak : ∀ m (g : Fin m → S), 1 / 2 * (u (H.cX m g) (H.cY m g) + u (F.cX m g) (F.cY m g))
      ≤ ustar m g := by
    intro m g
    have e1 : X (lastState s₀ m g) / 2 = (H.cX m g + F.cX m g) / 2 := by rw [hcX]
    have e2 : Y (lastState s₀ m g) / 2 = (H.cY m g + F.cY m g) / 2 := by rw [hcY]
    simp only [hustar, e1, e2]
    by_cases hc : H.cX m g ≠ F.cX m g ∨ H.cY m g ≠ F.cY m g
    · have := hstrict _ _ _ _ (hH.1 m g).1 (hH.1 m g).2 (hF.1 m g).1 (hF.1 m g).2 hc
      linarith
    · push Not at hc
      rw [hc.1, hc.2]
      have a1 : (F.cX m g + F.cX m g) / 2 = F.cX m g := by ring
      have a2 : (F.cY m g + F.cY m g) / 2 = F.cY m g := by ring
      rw [a1, a2]
      linarith
  by_contra hcon
  have hne : H.cX n h ≠ F.cX n h ∨ H.cY n h ≠ F.cY n h := by
    by_contra hc
    push Not at hc
    apply hcon
    have a := hcX n h
    have b := hcY n h
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [hc.1, hc.2]
  set avg : TreeProcess S := fun m g =>
    1 / 2 * (u (H.cX m g) (H.cY m g) + u (F.cX m g) (F.cY m g)) with havg
  have hsumAvg : HasSum (fun k => β ^ k * condE tr avg k 0 Fin.elim0)
      ((lucasUtility mc s₀ β u H + lucasUtility mc s₀ β u F) / 2) := by
    have := (hH.2.2.2.2.hasSum.add hF.2.2.2.2.hasSum).mul_left (1 / 2)
    unfold lucasUtility at this ⊢
    rw [show ∀ a b : ℝ, (a + b) / 2 = 1 / 2 * (a + b) from fun a b => by ring]
    refine this.congr_fun fun k => ?_
    simp only [havg, condE.smul_apply, condE.add_apply]
    ring
  have hlt : (lucasUtility mc s₀ β u H + lucasUtility mc s₀ β u F) / 2
      < ∑' k, β ^ k * condE tr ustar k 0 Fin.elim0 := by
    refine hasSum_lt (i := n) (fun k => mul_le_mul_of_nonneg_left
      (condE.mono_apply tr hweak k 0 Fin.elim0) (pow_nonneg hβ0.le k)) ?_ hsumAvg
      hsumStar.hasSum
    refine mul_lt_mul_of_pos_left ?_ (pow_pos hβ0 n)
    rw [condE_root_eq_sum_histProb, condE_root_eq_sum_histProb, ← sub_pos,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_pos' (fun g _ => ?_) ⟨h, Finset.mem_univ h, ?_⟩
    · rw [← mul_sub]
      exact mul_nonneg (tr.histProb_nonneg g) (sub_nonneg.mpr (hweak n g))
    · rw [← mul_sub]
      refine mul_pos hπ (sub_pos.mpr ?_)
      have e1 : X (lastState s₀ n h) / 2 = (H.cX n h + F.cX n h) / 2 := by rw [hcX]
      have e2 : Y (lastState s₀ n h) / 2 = (H.cY n h + F.cY n h) / 2 := by rw [hcY]
      simp only [hustar, e1, e2]
      have := hstrict _ _ _ _ (hH.1 n h).1 (hH.1 n h).2 (hF.1 n h).1 (hF.1 n h).2 hne
      linarith
  rw [← hUmid] at hlt
  linarith

end ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing

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
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.SmallCountry.planUtility
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.SmallCountry.planValue
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.SmallCountry.IsPlanOptimum
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.SmallCountry.lifetimeUtility_eq_planUtility
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.SmallCountry.planValue_of_holdings
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.SmallCountry.isPlanOptimum_of_budget_eq
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.SmallCountry.isPlanOptimum_of_budget_le
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.SmallCountry.isPlanOptimum_of_lifetime
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.SmallCountry.foc_of_isPlanOptimum
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.SmallCountry.foc_necessary
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.SmallCountry.foc_necessary_pos
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.SmallCountry.mrs_eq_price_of_optimum
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.SmallCountry.bond_euler_of_optimum
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.SmallCountry.mrs_ratio_of_optimum
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.SmallCountry.budget_binds_of_optimum
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.SmallCountry.planUtility_le_of_foc
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.SmallCountry.optimum_iff_foc_budget_eq
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.SmallCountry.optimum_iff_foc_budget_le
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.SmallCountry.foc_iff
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
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.TwoStageBudgeting.log_le_tangent
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.TwoStageBudgeting.geoIndex
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.TwoStageBudgeting.geoPrice
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.TwoStageBudgeting.geoDemand
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.TwoStageBudgeting.geoDemand_eq_24
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.TwoStageBudgeting.geo_stage_two
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.TwoStageBudgeting.cesIndex_pos
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.TwoStageBudgeting.riskIndex
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.TwoStageBudgeting.riskPrice
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.TwoStageBudgeting.riskDemand
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.TwoStageBudgeting.risk_stage_two
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.TwoStageBudgeting.isoU
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.TwoStageBudgeting.isoU_hasDerivAt
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.TwoStageBudgeting.isoU_tangent
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.TwoStageBudgeting.isoU_lt_of_lt
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.TwoStageBudgeting.isoU_le_of_le
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.TwoStageBudgeting.stageOneObjective
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.TwoStageBudgeting.stageOneC1
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.TwoStageBudgeting.stageOneZ2
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.TwoStageBudgeting.stageOneZ2_eq_27
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.TwoStageBudgeting.stageOne_feasible
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.TwoStageBudgeting.stageOne_euler
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.TwoStageBudgeting.stageOne_optimal
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.TwoStageBudgeting.stageOne_unique
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.TwoStageBudgeting.stageOne_maximiser_iff
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.TwoStageBudgeting.stageOne_maximiser_iff_27
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.TwoStageBudgeting.stageOne_maximiser_iff_euler
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.TwoStageBudgeting.two_stage_optimal_of_index
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.TwoStageBudgeting.ezUtility
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.TwoStageBudgeting.ezUtility_eq_printed
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.TwoStageBudgeting.ez_two_stage_optimal
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.TwoStageBudgeting.crraU
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.TwoStageBudgeting.expectedUtility
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.TwoStageBudgeting.isoU_inv_eq_crraU
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.TwoStageBudgeting.ez_eq_expectedUtility
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.TwoStageBudgeting.ez_le_iff_expectedUtility
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.TwoStageBudgeting.expectedUtility_two_stage_optimal
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.TwoStageBudgeting.ez_same_ordering_iff
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.TwoStageBudgeting.ez_current_account_sign
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.TwoStageBudgeting.ez_consumption_vs_certainty
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
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.EventTree.Tree.histProb_snoc
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.EventTree.Tree.histProb_zero
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.EventTree.Tree.histProb_one
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.EventTree.Tree.histProb_eq_first_mul_condProb
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
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.EventTree.sum_snoc
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.EventTree.crraUtil
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.EventTree.crra_tangent
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.EventTree.utilSeries
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.EventTree.expectedUtility
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.EventTree.valueSeries
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.EventTree.dateOneValue
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.EventTree.expectedUtility_eq_book
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.EventTree.dateOneValue_eq_book
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.EventTree.foc_plan_optimal_tsum
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.EventTree.arrowDebreu_optimal_infinite
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.EventTree.euler_bond_plan
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.EventTree.histBump
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.EventTree.histBump_self
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.EventTree.histBump_ne
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.EventTree.perturbPlan
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.EventTree.utilSeries_perturbPlan
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.EventTree.valueSeries_perturbPlan
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.EventTree.arrowDebreu_foc_necessary
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.EventTree.worldOutput
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.EventTree.crraDatePrice
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.EventTree.crraDatePrice_zero
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.EventTree.crraDatePrice_eq
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.EventTree.crraDatePrice_sum
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.EventTree.crra_foc_infinite
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.EventTree.crra_valueSeries
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.EventTree.crra_equilibrium_infinite
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.EventTree.crra_constant_share_infinite
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.EventTree.crra_share_of_budget
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.EventTree.log_equilibrium_infinite
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.EventTree.dateTwoUtilSeries
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.EventTree.dateTwoValueSeries
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.EventTree.dateTwo_restriction_admissible
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.EventTree.dynamic_consistency_infinite
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.EventTree.log_share_iff
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.EventTree.share_formula_iff
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.EventTree.crra_share_recursion
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.EventTree.crra_iid_share
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.EventTree.crra_iid_share_log
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.iidTree
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.portRet
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.PortFeasible
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.portRet_eq_book
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.wealth_accumulation_book
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.portObj
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.logPortObj
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.PortfolioCondition
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.LogPortfolioCondition
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.portfolio_condition_wealth_invariant
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.portShift
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.portShift_sum
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.portRet_portShift
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.portfolio_condition_sufficient
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.portfolio_condition_necessary
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.log_portfolio_condition_sufficient
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.log_portfolio_condition_necessary
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.growthFactor
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.crraShare
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.crraValue
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.bellmanRHS
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.expect_pos
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.growthFactor_pos
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.crraShare_mem
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.expect_next_crra
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.growthFactor_mul_crraUtil
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.crra_split_le
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.crra_split_eq
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.bellman_crra
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.hasDerivAt_crraUtil
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.bellman_guess_pins_share
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.crraShare_iid_recursion
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.crraShare_euler
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.logValueConst
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.logValue
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.expect_next_log
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.bellman_log
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.wealth
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.wealth_snoc
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.Admissible
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.admissible_step
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.sum_succ_iid
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.telescope_le
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.crraUtil_mono
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.transversality_crra
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.verification_upper_crra
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.optWealth
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.optWealth_snoc
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.optWealth_pos
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.wealth_optPlan
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.optPlan_admissible
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.optWealth_moment
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.verification_crra
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.expect_log_wealth_le
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.transversality_log
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.verification_upper_log
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.optWealth_expect_log
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.verification_log
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.NoArbitrage
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.feasibleSet
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.nonempty_of_stateSpace
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.portRet_add_smul
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.feasible_bounded
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.isCompact_feasibleSet
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.feasible_return_bounded
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.exists_max_of_capture
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.exists_optimal_portfolio_gt_one
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.exists_optimal_portfolio_log
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.exists_optimal_portfolio_lt_one
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.exists_optimal_portfolio
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.exists_optimal_log_portfolio
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.verification_crra_of_noArbitrage
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.verification_log_of_noArbitrage
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.weightedObj
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.exists_optimal_weighted
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.optPortW
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.optPortW_spec
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.optJ
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.optJ_compare
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.optJ_pos
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.nodeSpace
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.nodeGrowth
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.SolvesShareRecursion
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.nodeWeights
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.shareMap
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.iterA
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.optJ_mono
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.growthFactor_eq_portObj
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.optJ_le_growth
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.optJ_tendsto
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.shareMap_mono
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.one_le_shareMap
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.continuous_shareMap
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.shareMap_bound
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.nonempty_of_tree
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.exists_share_recursion_solution
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.wealthT
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.wealthT_snoc
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.AdmissibleT
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.admissibleT_step
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.sum_succ_tree
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.telescope_tree_le
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.telescope_tree_eq
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.share_identity
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.node_continuation
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.bellman_node_le
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.bellman_node_eq
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.nodeGrowth_nonneg
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.transversality_tree
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.optWealthT
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.wealthT_optPlan
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.optWealthT_pos
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.verification_tree
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.verification_varying_returns
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.myopicPort
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.myopicPort_spec
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.myopicGrowth
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.logSeriesTerm
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.logConstT
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.logValueT
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.logSeriesTerm_bound
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.logSeries_summable
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.logConstT_bound
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.logConstT_recursion
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.log_split_le
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.log_node_continuation
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.bellman_log_node
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.expect_log_wealthT_le
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.abs_expect_logConstT_le
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.transversality_log_tree
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio.verification_log_tree
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.TreeProcess
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.condE
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.condE.zero_eq
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.condE.succ_eq
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.condE.one_eq
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.condE.succ_eq_iter
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.condE.add_eq_iter
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.condE.add_apply
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.condE.smul_apply
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.condE.sub_apply
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.condE.const_apply
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.condE.mono_apply
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.condE.abs_le_of_bound
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.condE.nonneg_apply
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.condProb_snoc
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.condE_eq_sum_condProb
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.EulerEq
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.pvPartial
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.eulerEq_iff
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.mu_price_k_step
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.price_k_step
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.price_eq_series
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.price_hasSum
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.pvPartial_succ
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.series_limit_recursion
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.euler_of_series
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.bubble_recursion
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.bubble_tendsto
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.price_eq_fundamental_iff
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.price_unique_of_noBubble
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.euler_add_bubble
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.euler_nonunique_without_noBubble
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.noBubble_of_bounded
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.series_summable_of_bounded
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.fundamentalMU
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.fundamentalMU_tendsto
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.fundamentalMU_abs_le
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.unique_bounded_price
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.bounded_prices_unique
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.discountR
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.condCov
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.value_term_decomposition
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.bond_price_eq_discountR
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.price_eq_riskless_plus_cov
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.crra_value_term
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.price_crra_world_output_tree
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.price_k_step_riskless_cov
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.price_crra_world_output_bounded
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.euler_of_isLocalMax
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.lucasFinance
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.lucas_perturbation_feasible
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.lucas_euler_equations
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.EndowmentChain
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.EndowmentChain.mk
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.EndowmentChain.P
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.EndowmentChain.P_nonneg
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.EndowmentChain.P_sum
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.lastState
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.lastState_snoc
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.EndowmentChain.toTree
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.EndowmentChain.toTree_q
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.EndowmentChain.mExp
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.EndowmentChain.condE_toTree
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.EndowmentChain.markovSeries
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.EndowmentChain.markovPrice
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.abs_le_sum_abs
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.fundamentalMU_toTree
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.markov_price_unique
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.lucas_claim_prices_infinite
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.lucas_equilibrium
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.lucas_riskless_rates
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.quadU
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.quadU_hasDerivAt
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.quadratic_euler
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.quadratic_two_period_consumption
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.quadratic_consumption_martingale
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.expected_budget_k_step
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.income_series_summable
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.quadratic_infinite_horizon_consumption
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.human_wealth_recursion
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.quadratic_permanent_income_rule
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.condE_root_eq_sum_histProb
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.price_crra_world_output_derived
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.plan_value_identity
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.summable_discounted_condE
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.chain_expect_pos
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.LucasPlan
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.LucasPlan.mk
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.LucasPlan.cX
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.LucasPlan.cY
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.LucasPlan.x
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.LucasPlan.y
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.LucasPlan.B
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.LucasAdmissible
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.lucasUtility
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.lucasNoTrade
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.lucas_plan_euler
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.lucas_noTrade_optimal
#print axioms ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing.lucas_allocation_unique
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
