/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import InternationalFinancialMarkets.Model
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Algebra.Order.Chebyshev

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
