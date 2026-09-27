/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Investment with adjustment costs: Tobin's q

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §2.5.2,
pp. 105–114, Appendix 2B.2, p. 124, Exercise 9, pp. 126–127, and the worked example of
Supplement C to Chapter 2, pp. 736–737.

A firm with capital `K_s` pays the installation cost `χ I_s² / (2 K_s)` (2.62). The
first-order conditions are the investment equation (2.63), `I_s = (q_s − 1) K_s / χ`, and the
investment Euler equation (2.64),
`(1 + r) q_s = A_{s+1} F_K(K_{s+1}, L_{s+1}) + (χ/2)(I_{s+1}/K_{s+1})² + q_{s+1}`.

Contents.
* `forward_iterate`, `hasSum_of_tail`, `tail_of_hasSum`: the forward solution of any recursion
  `(1 + r) x_t = y_{t+1} + x_{t+1}`; applied to (2.64) this is (2.65), `q_forward_solution`.
* **Index typo in (2.65) (repeated on p. 124).** The book prints the summand as
  `A_{s+1} F_K(K_{s+1}, L_{s+1}) + (χ/2)(I_{s+1}/K_{s+1})²` with weight `(1 + r)^{-(s-t)}` and
  `s` running from `t + 1`. Iterating (2.64) gives the subscripts `s`, not `s + 1`. The printed
  sum is in fact `q_{t+1}`, not `q_t`: `book_formula_sums_to_next_q`.
* Appendix 2B.2: `q_t − PV_t = lim (1 + r)^{-T} q_{t+T}` (`bubble_identity`), so a positive
  bubble term means `q_t` exceeds the present value of marginal earnings.
* The exact dynamics (2.66)–(2.67), the steady state `q̄ = 1`, `A F_K(K̄, L) = r`, and its
  uniqueness.
* The linearisation (2.68)–(2.69), the slope of the `Δq = 0` locus, and the saddle-point
  theorem: the characteristic roots satisfy `ω₁ > 1 > ω₂ > 0`, the saddle path
  `K_t − K̄ = (K_0 − K̄) ω₂^t`, `q_t − 1 = (χ (ω₂ − 1)/K̄)(K_0 − K̄) ω₂^t` solves the linear
  system and converges, and it is the unique bounded solution from `K_0`.
* Marginal q equals average q (Hayashi), (2.70), and the rate-of-return form of (2.64).
* Exercise 9: the simplified model with cost `χ I² / 2`, its first-order conditions and steady
  state, and the failure of marginal = average q.
-/

namespace ObstfeldRogoff.SmallOpenEconomyDynamics.TobinQ

open Filter Topology Finset

/-! ## Forward solution of a first-order recursion -/

/-- **Finite-horizon forward iteration**, as used for O&R (2.65), p. 107: if
`(1 + r) x_t = y_{t+1} + x_{t+1}` for all `t`, then
`x_t = Σ_{s<T} (1 + r)^{-(s+1)} y_{t+s+1} + (1 + r)^{-T} x_{t+T}`. -/
theorem forward_iterate {r : ℝ} (hr : 1 + r ≠ 0) {x y : ℕ → ℝ}
    (h : ∀ t, (1 + r) * x t = y (t + 1) + x (t + 1)) (t T : ℕ) :
    x t = ∑ s ∈ range T, (1 + r)⁻¹ ^ (s + 1) * y (t + s + 1) + (1 + r)⁻¹ ^ T * x (t + T) := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [sum_range_succ, ih]
    have hx : x (t + T) = (1 + r)⁻¹ * (y (t + T + 1) + x (t + T + 1)) := by
      rw [← h (t + T)]; field_simp
    rw [hx, show t + (T + 1) = t + T + 1 by ring]
    ring

/-- A convergent present value forces the no-bubble condition: if the discounted `y` sum to
`x_t` then `(1 + r)^{-T} x_{t+T} → 0` (O&R p. 107). -/
theorem tail_of_hasSum {r : ℝ} (hr : 1 + r ≠ 0) {x y : ℕ → ℝ}
    (h : ∀ t, (1 + r) * x t = y (t + 1) + x (t + 1)) (t : ℕ)
    (hs : HasSum (fun s => (1 + r)⁻¹ ^ (s + 1) * y (t + s + 1)) (x t)) :
    Tendsto (fun T => (1 + r)⁻¹ ^ T * x (t + T)) atTop (𝓝 0) := by
  have h1 := (tendsto_const_nhds (x := x t)).sub hs.tendsto_sum_nat
  rw [sub_self] at h1
  refine h1.congr fun T => ?_
  rw [forward_iterate hr h t T]; ring

/-- **Forward solution under no bubbles**, O&R (2.65), p. 107: with a summable present value
and `(1 + r)^{-T} x_{t+T} → 0`, `x_t = Σ_{s ≥ 0} (1 + r)^{-(s+1)} y_{t+s+1}`. -/
theorem hasSum_of_tail {r : ℝ} (hr : 1 + r ≠ 0) {x y : ℕ → ℝ}
    (h : ∀ t, (1 + r) * x t = y (t + 1) + x (t + 1)) (t : ℕ)
    (hsum : Summable fun s => (1 + r)⁻¹ ^ (s + 1) * y (t + s + 1))
    (htail : Tendsto (fun T => (1 + r)⁻¹ ^ T * x (t + T)) atTop (𝓝 0)) :
    HasSum (fun s => (1 + r)⁻¹ ^ (s + 1) * y (t + s + 1)) (x t) := by
  have hp : Tendsto (fun T => ∑ s ∈ range T, (1 + r)⁻¹ ^ (s + 1) * y (t + s + 1)) atTop
      (𝓝 (x t)) := by
    have h1 := (tendsto_const_nhds (x := x t)).sub htail
    rw [sub_zero] at h1
    refine h1.congr fun T => ?_
    rw [forward_iterate hr h t T]; ring
  have heq := tendsto_nhds_unique hsum.hasSum.tendsto_sum_nat hp
  rw [← heq]; exact hsum.hasSum

/-- **Bubble identity**, O&R Appendix 2B.2, p. 124: with a summable present value the
discounted terminal value converges, and its limit is exactly `x_t` minus the present value. -/
theorem bubble_identity {r : ℝ} (hr : 1 + r ≠ 0) {x y : ℕ → ℝ}
    (h : ∀ t, (1 + r) * x t = y (t + 1) + x (t + 1)) (t : ℕ)
    (hsum : Summable fun s => (1 + r)⁻¹ ^ (s + 1) * y (t + s + 1)) :
    Tendsto (fun T => (1 + r)⁻¹ ^ T * x (t + T)) atTop
      (𝓝 (x t - ∑' s, (1 + r)⁻¹ ^ (s + 1) * y (t + s + 1))) := by
  refine ((tendsto_const_nhds (x := x t)).sub hsum.hasSum.tendsto_sum_nat).congr fun T => ?_
  rw [forward_iterate hr h t T]; ring

/-- **A positive bubble overvalues the asset**, O&R Appendix 2B.2, p. 124: if the discounted
terminal value tends to `b > 0`, then `x_t` exceeds the present value, by exactly `b`. -/
theorem bubble_overvalues {r : ℝ} (hr : 1 + r ≠ 0) {x y : ℕ → ℝ}
    (h : ∀ t, (1 + r) * x t = y (t + 1) + x (t + 1)) (t : ℕ)
    (hsum : Summable fun s => (1 + r)⁻¹ ^ (s + 1) * y (t + s + 1)) {b : ℝ}
    (hb : Tendsto (fun T => (1 + r)⁻¹ ^ T * x (t + T)) atTop (𝓝 b)) (hbpos : 0 < b) :
    x t - ∑' s, (1 + r)⁻¹ ^ (s + 1) * y (t + s + 1) = b ∧
      ∑' s, (1 + r)⁻¹ ^ (s + 1) * y (t + s + 1) < x t := by
  have := tendsto_nhds_unique (bubble_identity hr h t hsum) hb
  exact ⟨this, by linarith⟩

/-! ## The q model: first-order conditions and the forward solution (2.65) -/

/-- The date-`s` marginal earnings of installed capital in O&R (2.64)–(2.65):
`A_s F_K(K_s, L_s) + (χ/2)(I_s/K_s)²`, the marginal product plus the marginal saving in
installation costs. `FK` is the marginal product of capital. -/
noncomputable def marginalEarnings (A : ℕ → ℝ) (FK : ℝ → ℝ → ℝ) (K L I : ℕ → ℝ) (χ : ℝ)
    (s : ℕ) : ℝ :=
  A s * FK (K s) (L s) + χ / 2 * (I s / K s) ^ 2

/-- **Investment first-order condition**, O&R p. 106: the derivative of the date-`s` terms of
the Lagrangian that involve `I_s`, `−(χ/2) I²/K − I + q I`, is `−χ I/K − 1 + q`. -/
theorem hasDerivAt_lagrangian_investment (χ K q I : ℝ) :
    HasDerivAt (fun i : ℝ => -(χ / 2) * (i ^ 2 / K) - i + q * i) (-(χ * I / K) - 1 + q) I := by
  have h1 : HasDerivAt (fun i : ℝ => i ^ 2) (2 * I) I := by
    simpa using hasDerivAt_pow 2 I
  have h2 := ((h1.div_const K).const_mul (-(χ / 2))).sub (hasDerivAt_id I)
  have h3 := h2.add ((hasDerivAt_id I).const_mul q)
  convert h3 using 1
  · funext i; simp only [Pi.add_apply, Pi.sub_apply, id]
  · field_simp

/-- **Tobin's investment equation**, O&R (2.63), p. 107: with `χ ≠ 0` and `K ≠ 0`, the
investment first-order condition `−χ I/K − 1 + q = 0` holds iff `I = (q − 1) K / χ`. -/
theorem investment_foc_iff {χ K q I : ℝ} (hχ : χ ≠ 0) (hK : K ≠ 0) :
    -(χ * I / K) - 1 + q = 0 ↔ I = (q - 1) / χ * K := by
  constructor
  · intro h
    field_simp at h ⊢
    linarith
  · intro h
    rw [h]; field_simp; ring

/-- **Capital first-order condition**, O&R p. 107: the terms of the Lagrangian involving
`K_{s+1}` are `−q_s K_{s+1}` plus the discounted date-`(s+1)` profit and constraint terms.
If `F(·, L_{s+1})` has derivative `FK` at `K ≠ 0`, their derivative is
`−q_s + (A F_K + (χ/2)(I_{s+1}/K)² + q_{s+1})/(1 + r)`. -/
theorem hasDerivAt_lagrangian_capital {F : ℝ → ℝ} {FK K : ℝ} (hF : HasDerivAt F FK K)
    (hK : K ≠ 0) (r A χ w L I q0 q1 K2 : ℝ) :
    HasDerivAt
      (fun k : ℝ => -q0 * k +
        (1 + r)⁻¹ * (A * F k - χ / 2 * (I ^ 2 / k) - w * L - I - q1 * (K2 - k - I)))
      (-q0 + (1 + r)⁻¹ * (A * FK + χ / 2 * (I / K) ^ 2 + q1)) K := by
  have hinv : HasDerivAt (fun k : ℝ => k⁻¹) (-(K ^ 2)⁻¹) K := hasDerivAt_inv hK
  have hc : HasDerivAt (fun k : ℝ => I ^ 2 / k) (I ^ 2 * -(K ^ 2)⁻¹) K := by
    simpa [div_eq_mul_inv] using hinv.const_mul (I ^ 2)
  have hlin : HasDerivAt (fun k : ℝ => q1 * (K2 - k - I)) (q1 * (-1)) K := by
    have : HasDerivAt (fun k : ℝ => K2 - k - I) (-1) K := by
      simpa using ((hasDerivAt_id K).const_sub K2).sub_const I
    exact this.const_mul q1
  have hin := ((((hF.const_mul A).sub (hc.const_mul (χ / 2))).sub_const (w * L)).sub_const
    I).sub hlin
  have h := ((hasDerivAt_id K).const_mul (-q0)).add (hin.const_mul (1 + r)⁻¹)
  convert h using 1
  · ext k; simp
  · field_simp; ring

/-- **Investment Euler equation**, O&R (2.64), p. 107: the capital first-order condition
equals zero iff `(1 + r) q_s = A F_K + (χ/2)(I_{s+1}/K_{s+1})² + q_{s+1}` (for `r ≠ -1`). -/
theorem capital_foc_iff {r FKval X q0 q1 : ℝ} (hr : 1 + r ≠ 0) :
    -q0 + (1 + r)⁻¹ * (FKval + X + q1) = 0 ↔ (1 + r) * q0 = FKval + X + q1 := by
  constructor
  · intro h; field_simp at h; linarith
  · intro h; rw [← h]; field_simp; ring

/-- **Forward solution for q**, O&R (2.65), p. 107, in corrected form: given the investment
Euler equation (2.64) at every date and a summable present value of marginal earnings, `q_t`
equals `Σ_{s ≥ t+1} (1 + r)^{-(s-t)} [A_s F_K(K_s, L_s) + (χ/2)(I_s/K_s)²]` iff the no-bubble
condition `lim (1 + r)^{-T} q_{t+T} = 0` holds. -/
theorem q_forward_solution {r χ : ℝ} (hr : 1 + r ≠ 0) {A : ℕ → ℝ} {FK : ℝ → ℝ → ℝ}
    {K L I q : ℕ → ℝ}
    (heuler : ∀ s, (1 + r) * q s = marginalEarnings A FK K L I χ (s + 1) + q (s + 1)) (t : ℕ)
    (hsum : Summable fun s => (1 + r)⁻¹ ^ (s + 1) * marginalEarnings A FK K L I χ (t + s + 1)) :
    HasSum (fun s => (1 + r)⁻¹ ^ (s + 1) * marginalEarnings A FK K L I χ (t + s + 1)) (q t) ↔
      Tendsto (fun T => (1 + r)⁻¹ ^ T * q (t + T)) atTop (𝓝 0) :=
  ⟨tail_of_hasSum hr heuler t, hasSum_of_tail hr heuler t hsum⟩

/-- **The printed (2.65) sums to `q_{t+1}`**, O&R p. 107 and p. 124. The book's summand, for
`s = t + 1 + n`, is `(1 + r)^{-(s-t)} X_{s+1} = (1 + r)^{-(n+1)} X_{t+n+2}` where `X` is
`marginalEarnings`. Under (2.64), summability and no bubbles, that series sums to `q_{t+1}`,
not `q_t`: the printed formula has its subscripts shifted by one. -/
theorem book_formula_sums_to_next_q {r χ : ℝ} (hr : 1 + r ≠ 0) {A : ℕ → ℝ}
    {FK : ℝ → ℝ → ℝ} {K L I q : ℕ → ℝ}
    (heuler : ∀ s, (1 + r) * q s = marginalEarnings A FK K L I χ (s + 1) + q (s + 1)) (t : ℕ)
    (hsum : Summable fun n => (1 + r)⁻¹ ^ (n + 1) * marginalEarnings A FK K L I χ (t + n + 2))
    (htail : Tendsto (fun T => (1 + r)⁻¹ ^ T * q (t + 1 + T)) atTop (𝓝 0)) :
    HasSum (fun n => (1 + r)⁻¹ ^ (n + 1) * marginalEarnings A FK K L I χ (t + n + 2))
      (q (t + 1)) := by
  have hf : (fun n => (1 + r)⁻¹ ^ (n + 1) * marginalEarnings A FK K L I χ (t + n + 2)) =
      fun n => (1 + r)⁻¹ ^ (n + 1) * marginalEarnings A FK K L I χ (t + 1 + n + 1) := by
    ext n; congr 2; ring
  rw [hf] at hsum ⊢
  exact hasSum_of_tail hr heuler (t + 1) hsum htail

/-- **The printed (2.65) is correct only by coincidence**: under the hypotheses of
`book_formula_sums_to_next_q`, the printed sum equals `q_t` iff `q_{t+1} = q_t`. -/
theorem book_formula_eq_q_iff {r χ : ℝ} (hr : 1 + r ≠ 0) {A : ℕ → ℝ}
    {FK : ℝ → ℝ → ℝ} {K L I q : ℕ → ℝ}
    (heuler : ∀ s, (1 + r) * q s = marginalEarnings A FK K L I χ (s + 1) + q (s + 1)) (t : ℕ)
    (hsum : Summable fun n => (1 + r)⁻¹ ^ (n + 1) * marginalEarnings A FK K L I χ (t + n + 2))
    (htail : Tendsto (fun T => (1 + r)⁻¹ ^ T * q (t + 1 + T)) atTop (𝓝 0)) :
    ∑' n, (1 + r)⁻¹ ^ (n + 1) * marginalEarnings A FK K L I χ (t + n + 2) = q t ↔
      q (t + 1) = q t := by
  rw [(book_formula_sums_to_next_q hr heuler t hsum htail).tsum_eq]

/-! ## Exact dynamics (2.66)–(2.67) and the steady state -/

/-- **Exact q dynamics**, O&R (2.66)–(2.67), p. 108, with constant `A` and `L`. From capital
accumulation, the investment equation (2.63) at `t` and `t + 1`, and the Euler equation (2.64)
at `t`: `K_{t+1} − K_t = ((q_t − 1)/χ) K_t` and
`q_{t+1} − q_t = r q_t − A F_K[K_t (1 + (q_t − 1)/χ), L] − (q_{t+1} − 1)²/(2χ)`. -/
theorem exact_dynamics {r χ A L : ℝ} (hχ : χ ≠ 0) {FK : ℝ → ℝ → ℝ} {K I q : ℕ → ℝ} {t : ℕ}
    (hK1 : K (t + 1) ≠ 0) (hacc : K (t + 1) = K t + I t)
    (hinv : ∀ s, I s = (q s - 1) / χ * K s)
    (heuler : (1 + r) * q t = A * FK (K (t + 1)) L + χ / 2 * (I (t + 1) / K (t + 1)) ^ 2
      + q (t + 1)) :
    K (t + 1) - K t = (q t - 1) / χ * K t ∧
      q (t + 1) - q t = r * q t - A * FK (K t * (1 + (q t - 1) / χ)) L
        - (q (t + 1) - 1) ^ 2 / (2 * χ) := by
  have hk : K (t + 1) = K t * (1 + (q t - 1) / χ) := by rw [hacc, hinv t]; ring
  refine ⟨by rw [hacc, hinv t]; ring, ?_⟩
  rw [← hk]
  have hI : I (t + 1) / K (t + 1) = (q (t + 1) - 1) / χ := by
    rw [hinv (t + 1)]; field_simp
  rw [hI] at heuler
  field_simp
  field_simp at heuler
  linear_combination (-1) * heuler

/-- **Steady state of the q model**, O&R p. 108: with `χ ≠ 0` and `K̄ ≠ 0`, `(q̄, K̄)` is a
rest point of (2.66)–(2.67) iff `q̄ = 1` and `A F_K(K̄, L) = r`. -/
theorem steady_state_iff {r χ A L qb Kb : ℝ} (hχ : χ ≠ 0) (hK : Kb ≠ 0) {FK : ℝ → ℝ → ℝ} :
    ((qb - 1) / χ * Kb = 0 ∧
      r * qb - A * FK (Kb * (1 + (qb - 1) / χ)) L - (qb - 1) ^ 2 / (2 * χ) = 0) ↔
      (qb = 1 ∧ A * FK Kb L = r) := by
  constructor
  · rintro ⟨h1, h2⟩
    have hq : qb = 1 := by
      rcases mul_eq_zero.1 h1 with h | h
      · rcases div_eq_zero_iff.1 h with h | h
        · linarith
        · exact absurd h hχ
      · exact absurd h hK
    subst hq
    refine ⟨rfl, ?_⟩
    simp at h2; linarith
  · rintro ⟨rfl, h⟩
    simp [h]

/-- **Uniqueness of the steady state**, O&R p. 108: if `A > 0` and `F_K(·, L)` is strictly
decreasing on `K > 0`, at most one `K̄ > 0` satisfies `A F_K(K̄, L) = r`. -/
theorem steady_state_unique {r A L : ℝ} (hA : 0 < A) {FK : ℝ → ℝ → ℝ}
    (hdec : StrictAntiOn (fun k => FK k L) (Set.Ioi 0)) {K1 K2 : ℝ} (h1 : 0 < K1)
    (h2 : 0 < K2) (e1 : A * FK K1 L = r) (e2 : A * FK K2 L = r) : K1 = K2 := by
  have : FK K1 L = FK K2 L := by
    have := e1.trans e2.symm
    exact mul_left_cancel₀ hA.ne' this
  exact hdec.injOn h1 h2 this

/-- **The `ΔK = 0` schedule is `q = 1`**, O&R p. 108 and footnote 43: for `K ≠ 0` and
`χ ≠ 0`, capital is stationary under (2.66) iff `q = 1`, globally (not only near `K̄`). -/
theorem capital_stationary_iff {χ K q : ℝ} (hχ : χ ≠ 0) (hK : K ≠ 0) :
    (q - 1) / χ * K = 0 ↔ q = 1 := by
  constructor
  · intro h
    rcases mul_eq_zero.1 h with h | h
    · rcases div_eq_zero_iff.1 h with h | h
      · linarith
      · exact absurd h hχ
    · exact absurd h hK
  · rintro rfl; simp

/-! ## Linearisation (2.68)–(2.69) -/

/-- **Linearised capital equation**, O&R (2.68), p. 108: the right side of (2.66),
`((q − 1)/χ) K̄`, has derivative `K̄/χ` in `q` at `q̄ = 1`. -/
theorem hasDerivAt_capital_dynamics_q (χ Kb : ℝ) :
    HasDerivAt (fun q : ℝ => (q - 1) / χ * Kb) (Kb / χ) 1 := by
  have := (((hasDerivAt_id (1 : ℝ)).sub_const 1).div_const χ).mul_const Kb
  convert this using 1
  · funext q; simp
  · ring

/-- **Linearised capital equation**, O&R (2.68), p. 108: at `q = 1` the right side of (2.66)
does not depend on `K`, so its derivative in `K` is `0`. -/
theorem hasDerivAt_capital_dynamics_K (χ Kb : ℝ) :
    HasDerivAt (fun k : ℝ => ((1 : ℝ) - 1) / χ * k) 0 Kb := by
  simpa using hasDerivAt_const Kb (0 : ℝ)

/-- **Linearised q equation, `q` coefficient**, O&R (2.69), p. 108: if `F_K(·, L)` has
derivative `F_KK` at `K̄`, then `q ↦ r q − A F_K(K̄(1 + (q − 1)/χ), L)` has derivative
`r − A K̄ F_KK/χ` at `q = 1`. -/
theorem hasDerivAt_q_dynamics_q {FK : ℝ → ℝ → ℝ} {L Kb FKK : ℝ}
    (hF : HasDerivAt (fun k => FK k L) FKK Kb) (r A χ : ℝ) :
    HasDerivAt (fun q : ℝ => r * q - A * FK (Kb * (1 + (q - 1) / χ)) L)
      (r - A * Kb * FKK / χ) 1 := by
  have hin : HasDerivAt (fun q : ℝ => Kb * (1 + (q - 1) / χ)) (Kb * (1 / χ)) 1 := by
    have := ((((hasDerivAt_id (1 : ℝ)).sub_const 1).div_const χ).const_add 1).const_mul Kb
    simpa using this
  have hF' : HasDerivAt (fun k => FK k L) FKK (Kb * (1 + ((1 : ℝ) - 1) / χ)) := by
    simpa using hF
  have hc := hF'.comp (1 : ℝ) hin
  have h := ((hasDerivAt_id (1 : ℝ)).const_mul r).sub (hc.const_mul A)
  convert h using 1
  · funext q; simp only [Pi.sub_apply, id, Function.comp]
  · field_simp

/-- **Linearised q equation, `K` coefficient**, O&R (2.69), p. 108: at `q = 1` the map
`K ↦ r − A F_K(K, L)` has derivative `−A F_KK` at `K̄`. -/
theorem hasDerivAt_q_dynamics_K {FK : ℝ → ℝ → ℝ} {L Kb FKK : ℝ}
    (hF : HasDerivAt (fun k => FK k L) FKK Kb) (r A χ : ℝ) :
    HasDerivAt (fun k : ℝ => r * 1 - A * FK (k * (1 + ((1 : ℝ) - 1) / χ)) L) (-(A * FKK)) Kb := by
  have h := (hF.const_mul A).const_sub (r * 1)
  convert h using 1
  funext k; simp

/-- **The quadratic term drops out of (2.69)**, O&R p. 108: `(q' − 1)²/(2χ)` has zero
derivative at `q' = 1`. -/
theorem hasDerivAt_q_dynamics_quadratic (χ : ℝ) :
    HasDerivAt (fun q' : ℝ => (q' - 1) ^ 2 / (2 * χ)) 0 1 := by
  have := (((hasDerivAt_id (1 : ℝ)).sub_const 1).pow 2).div_const (2 * χ)
  simpa using this

/-- **Slope of the `Δq = 0` schedule**, O&R p. 109: with `A > 0`, `F_KK < 0`, `r > 0`,
`K̄ > 0`, `χ > 0`, the linearised locus
`0 = (r − A K̄ F_KK/χ)(q − 1) − A F_KK (K − K̄)` is the line through `(K̄, 1)` with slope
`A F_KK / (r − A K̄ F_KK/χ)`, and that slope is negative. -/
theorem dq_locus {r χ A Kb FKK : ℝ} (hr : 0 < r) (hχ : 0 < χ) (hA : 0 < A) (hKb : 0 < Kb)
    (hFKK : FKK < 0) :
    (∀ K q : ℝ, (r - A * Kb * FKK / χ) * (q - 1) - A * FKK * (K - Kb) = 0 ↔
      q - 1 = A * FKK / (r - A * Kb * FKK / χ) * (K - Kb)) ∧
      A * FKK / (r - A * Kb * FKK / χ) < 0 := by
  have hD : 0 < r - A * Kb * FKK / χ := by
    have : A * Kb * FKK / χ < 0 :=
      div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (mul_pos hA hKb) hFKK) hχ
    linarith
  set D := r - A * Kb * FKK / χ with hDd
  refine ⟨fun K q => ?_, div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hA hFKK) hD⟩
  constructor
  · intro h
    rw [div_mul_eq_mul_div, eq_div_iff hD.ne']
    linarith
  · intro h
    rw [h, div_mul_eq_mul_div, mul_div_assoc', mul_div_cancel_left₀ _ hD.ne']
    ring

/-! ## The saddle-point theorem (O&R p. 109; Supplement C, pp. 736–737) -/

/-- The matrix of the linear system (2.68)–(2.69) in the variables `(q_t − q̄, K_t − K̄)`, as
in O&R Supplement C, p. 736, with `a = A F_KK(K̄, L)`. -/
noncomputable def qMatrix (r χ Kb a : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![1 + r - Kb * a / χ, -a; Kb / χ, 1]

/-- **Determinant and trace of the q system**, O&R Supplement C, p. 736: `det = 1 + r` and
`trace = 2 + r − A K̄ F_KK/χ`. -/
theorem qMatrix_det_trace {r χ Kb a : ℝ} (hχ : χ ≠ 0) :
    (qMatrix r χ Kb a).det = 1 + r ∧ (qMatrix r χ Kb a).trace = 2 + r - Kb * a / χ := by
  refine ⟨?_, ?_⟩
  · rw [qMatrix, Matrix.det_fin_two_of]; field_simp; ring
  · rw [qMatrix, Matrix.trace_fin_two_of]; ring

/-- The characteristic polynomial of the q system, `ω² − (2 + r + x) ω + (1 + r)`, where
`x = −A K̄ F_KK/χ` (O&R Supplement C, p. 736). -/
def qCharPoly (r x ω : ℝ) : ℝ := ω ^ 2 - (2 + r + x) * ω + (1 + r)

/-- The discriminant `(2 + r + x)² − 4(1 + r)` of `qCharPoly` (O&R p. 736). -/
def qDisc (r x : ℝ) : ℝ := (2 + r + x) ^ 2 - 4 * (1 + r)

/-- The stable root `ω₂ = ((2 + r + x) − √disc)/2` (O&R p. 736). -/
noncomputable def omegaStable (r x : ℝ) : ℝ := ((2 + r + x) - √(qDisc r x)) / 2

/-- The unstable root `ω₁ = ((2 + r + x) + √disc)/2` (O&R p. 736). -/
noncomputable def omegaUnstable (r x : ℝ) : ℝ := ((2 + r + x) + √(qDisc r x)) / 2

/-- The discriminant equals `(r + x)² + 4x`, so it is positive when `x > 0`: the roots are
real and distinct (O&R p. 736). -/
theorem qDisc_eq (r x : ℝ) : qDisc r x = (r + x) ^ 2 + 4 * x := by
  unfold qDisc; ring

/-- **Both roots solve the characteristic equation**, and `ω₁ + ω₂ = trace`,
`ω₁ ω₂ = 1 + r = det` (O&R p. 736, eq. (14) of Supplement C), when `x ≥ 0`. -/
theorem omega_roots {r x : ℝ} (hx : 0 ≤ x) :
    qCharPoly r x (omegaStable r x) = 0 ∧ qCharPoly r x (omegaUnstable r x) = 0 ∧
      omegaUnstable r x + omegaStable r x = 2 + r + x ∧
      omegaUnstable r x * omegaStable r x = 1 + r := by
  have hD : 0 ≤ qDisc r x := by rw [qDisc_eq]; positivity
  have hs : √(qDisc r x) ^ 2 = (2 + r + x) ^ 2 - 4 * (1 + r) := Real.sq_sqrt hD
  unfold qCharPoly omegaStable omegaUnstable
  refine ⟨?_, ?_, ?_, ?_⟩
  · linear_combination hs / 4
  · linear_combination hs / 4
  · ring
  · linear_combination (-1 / 4 : ℝ) * hs

/-- **Saddle-point root configuration**, O&R Supplement C, p. 736: if `1 + r > 0` and
`x = −A K̄ F_KK/χ > 0`, then `0 < ω₂ < 1 < ω₁`. (The book assumes Cobb–Douglas, where
`x = (1 − α) r / χ`; only `x > 0`, i.e. `F_KK < 0`, is needed.) -/
theorem omega_saddle {r x : ℝ} (hr : 0 < 1 + r) (hx : 0 < x) :
    0 < omegaStable r x ∧ omegaStable r x < 1 ∧ 1 < omegaUnstable r x := by
  have hD : 0 < qDisc r x := by rw [qDisc_eq]; positivity
  have hlt : (r + x) ^ 2 < qDisc r x := by rw [qDisc_eq]; linarith
  have h1 : r + x < √(qDisc r x) := Real.lt_sqrt_of_sq_lt hlt
  have h2 : -(r + x) < √(qDisc r x) := Real.lt_sqrt_of_sq_lt (by rw [neg_sq]; exact hlt)
  have h3 : √(qDisc r x) < 2 + r + x := by
    rw [Real.sqrt_lt' (by linarith)]
    unfold qDisc; linarith
  unfold omegaStable omegaUnstable
  refine ⟨by linarith, by linarith, by linarith⟩

/-- **Cobb–Douglas curvature**, O&R p. 736: with `F(K, L) = K^α L^{1−α}`, `K > 0`, the
marginal product `F_K = α K^{α−1} L^{1−α}` has derivative `F_KK = α(α − 1) K^{α−2} L^{1−α}`,
and if `A F_K(K̄, L) = r` then `−A K̄ F_KK(K̄, L) = (1 − α) r`. -/
theorem cobbDouglas_curvature {α A L Kb r : ℝ} (hKb : 0 < Kb)
    (hss : A * (α * Kb ^ (α - 1) * L ^ (1 - α)) = r) :
    HasDerivAt (fun k : ℝ => α * k ^ (α - 1) * L ^ (1 - α))
        (α * ((α - 1) * Kb ^ (α - 2)) * L ^ (1 - α)) Kb ∧
      -(A * Kb * (α * ((α - 1) * Kb ^ (α - 2)) * L ^ (1 - α))) = (1 - α) * r := by
  refine ⟨?_, ?_⟩
  · have := ((Real.hasDerivAt_rpow_const (p := α - 1) (Or.inl hKb.ne')).const_mul α).mul_const
      (L ^ (1 - α))
    convert this using 2
    ring_nf
  · have h : Kb ^ (α - 1) = Kb ^ (α - 2) * Kb := by
      rw [← Real.rpow_add_one hKb.ne']; ring_nf
    rw [← hss, h]; ring

/-- The linear system (2.68)–(2.69) in deviations `p_t = q_t − 1`, `k_t = K_t − K̄`, with
`a = A F_KK(K̄, L)` (O&R p. 108; Supplement C, p. 736):
`p_{t+1} = (1 + r − K̄ a/χ) p_t − a k_t` and `k_{t+1} = k_t + (K̄/χ) p_t`. -/
def IsLinearQPath (r χ Kb a : ℝ) (p k : ℕ → ℝ) : Prop :=
  ∀ t, p (t + 1) = (1 + r - Kb * a / χ) * p t - a * k t ∧ k (t + 1) = k t + Kb / χ * p t

/-- **The saddle path solves the linear system**, O&R Supplement C, p. 737: for any root `ω`
of the characteristic polynomial (with `x = −K̄ a/χ`), `k_t = k_0 ω^t` and
`p_t = (χ (ω − 1)/K̄) k_0 ω^t` satisfy (2.68)–(2.69). -/
theorem saddle_path_solves {r χ Kb a ω k0 : ℝ} (hχ : χ ≠ 0) (hKb : Kb ≠ 0)
    (hω : qCharPoly r (-(Kb * a / χ)) ω = 0) :
    IsLinearQPath r χ Kb a (fun t => χ * (ω - 1) / Kb * k0 * ω ^ t) (fun t => k0 * ω ^ t) := by
  intro t
  unfold qCharPoly at hω
  refine ⟨?_, ?_⟩
  · have h' : ω ^ 2 - (2 + r) * ω + (1 + r) = -(Kb * a / χ) * ω := by
      linear_combination hω
    dsimp only
    rw [pow_succ]
    linear_combination (norm := skip) (χ / Kb * k0 * ω ^ t) * h'
    field_simp
    ring
  · simp only [pow_succ]
    field_simp
    ring

/-- **The saddle path converges to the steady state**, O&R p. 737: with `0 < ω₂ < 1`, both
`K_t − K̄` and `q_t − 1` tend to zero along the saddle path. -/
theorem saddle_path_tendsto {χ Kb ω k0 : ℝ} (h0 : 0 < ω) (h1 : ω < 1) :
    Tendsto (fun t : ℕ => k0 * ω ^ t) atTop (𝓝 0) ∧
      Tendsto (fun t : ℕ => χ * (ω - 1) / Kb * k0 * ω ^ t) atTop (𝓝 0) := by
  have hp := tendsto_pow_atTop_nhds_zero_of_lt_one h0.le h1
  refine ⟨?_, ?_⟩
  · simpa using hp.const_mul k0
  · simpa using hp.const_mul (χ * (ω - 1) / Kb * k0)

/-- **`q > 1` exactly when capital starts below its steady state**, O&R p. 737 and p. 110:
along the saddle path with `χ > 0`, `K̄ > 0`, `0 < ω₂ < 1`, `q_t − 1 > 0` iff `K_0 < K̄`. -/
theorem saddle_q_above_one_iff {χ Kb ω k0 : ℝ} (hχ : 0 < χ) (hKb : 0 < Kb) (h0 : 0 < ω)
    (h1 : ω < 1) (t : ℕ) :
    0 < χ * (ω - 1) / Kb * k0 * ω ^ t ↔ k0 < 0 := by
  have hc : χ * (ω - 1) / Kb < 0 :=
    div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hχ (by linarith)) hKb
  have hpow : 0 < ω ^ t := pow_pos h0 t
  constructor
  · intro h
    by_contra hk
    push Not at hk
    have : χ * (ω - 1) / Kb * k0 * ω ^ t ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg hc.le hk) hpow.le
    linarith
  · intro hk
    exact mul_pos (mul_pos_of_neg_of_neg hc hk) hpow

/-- **Monotone convergence along the saddle path**, O&R p. 110: if `K_0 < K̄` then capital
rises strictly and `q` falls strictly toward `1` (with `χ > 0`, `K̄ > 0`, `0 < ω₂ < 1`). -/
theorem saddle_monotone {χ Kb ω k0 : ℝ} (hχ : 0 < χ) (hKb : 0 < Kb) (h0 : 0 < ω) (h1 : ω < 1)
    (hk : k0 < 0) :
    StrictMono (fun t : ℕ => k0 * ω ^ t) ∧
      StrictAnti (fun t : ℕ => χ * (ω - 1) / Kb * k0 * ω ^ t) := by
  have hc : χ * (ω - 1) / Kb < 0 :=
    div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hχ (by linarith)) hKb
  have ha := pow_right_strictAnti₀ h0 h1
  refine ⟨fun m n hmn => ?_, fun m n hmn => ?_⟩
  · exact mul_lt_mul_of_neg_left (ha hmn) hk
  · simp only
    rw [mul_assoc, mul_assoc]
    exact mul_lt_mul_of_neg_left (mul_lt_mul_of_neg_left (ha hmn) hk) hc

/-- **Uniqueness of the saddle path**, O&R p. 109 ("there is one and only one value of `q_t`
that places the firm on the stable adjustment path"). With `1 + r > 0`, `χ > 0`, `K̄ > 0` and
`a = A F_KK(K̄, L) < 0`, every bounded solution of the linear system (2.68)–(2.69) with
`K_0 − K̄ = k_0` is the saddle path `k_t = k_0 ω₂^t`, `p_t = (χ (ω₂ − 1)/K̄) k_0 ω₂^t`. -/
theorem saddle_path_unique {r χ Kb a : ℝ} (hr : 0 < 1 + r) (hχ : 0 < χ) (hKb : 0 < Kb)
    (ha : a < 0) {p k : ℕ → ℝ} (hsys : IsLinearQPath r χ Kb a p k) {B : ℝ}
    (hB : ∀ t, |p t| ≤ B ∧ |k t| ≤ B) (t : ℕ) :
    k t = k 0 * omegaStable r (-(Kb * a / χ)) ^ t ∧
      p t = χ * (omegaStable r (-(Kb * a / χ)) - 1) / Kb * k 0 *
        omegaStable r (-(Kb * a / χ)) ^ t := by
  set x := -(Kb * a / χ) with hxd
  have hx : 0 < x := by
    rw [hxd, neg_pos]; exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hKb ha) hχ
  obtain ⟨hr1, hr2, hsum, hprod⟩ := omega_roots hx.le
  obtain ⟨_, _, hω1⟩ := omega_saddle hr hx
  set ω1 := omegaUnstable r x
  set ω2 := omegaStable r x
  have hax : a = -(x * χ / Kb) := by rw [hxd]; field_simp
  clear_value x ω1 ω2
  -- the unstable combination `u_t = (ω₁ − 1) p_t − a k_t` grows by the factor `ω₁`
  have hu : ∀ t, (ω1 - 1) * p (t + 1) - a * k (t + 1) = ω1 * ((ω1 - 1) * p t - a * k t) := by
    intro t
    obtain ⟨hp, hk⟩ := hsys t
    unfold qCharPoly at hr2
    rw [hp, hk, show 1 + r - Kb * a / χ = 1 + r + x by rw [hxd]; ring]
    have : Kb / χ * a = -x := by rw [hxd]; field_simp
    linear_combination (-(p t)) * hr2 - p t * this
  have hupow : ∀ t, (ω1 - 1) * p t - a * k t = ω1 ^ t * ((ω1 - 1) * p 0 - a * k 0) := by
    intro t
    induction t with
    | zero => simp
    | succ n ih => rw [hu n, ih, pow_succ]; ring
  -- boundedness forces `u_0 = 0`
  have hu0 : (ω1 - 1) * p 0 - a * k 0 = 0 := by
    by_contra hne
    set u0 := (ω1 - 1) * p 0 - a * k 0
    have hpos : 0 < |u0| := abs_pos.2 hne
    set M := ((ω1 - 1) + |a|) * B
    have hev := (tendsto_pow_atTop_atTop_of_one_lt hω1).eventually_gt_atTop (M / |u0|)
    obtain ⟨n, hn⟩ := hev.exists
    have hbound : |(ω1 - 1) * p n - a * k n| ≤ M := by
      obtain ⟨hpB, hkB⟩ := hB n
      calc |(ω1 - 1) * p n - a * k n| ≤ |(ω1 - 1) * p n| + |a * k n| := abs_sub _ _
        _ = (ω1 - 1) * |p n| + |a| * |k n| := by
          rw [abs_mul, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < ω1 - 1)]
        _ ≤ (ω1 - 1) * B + |a| * B := by gcongr
        _ = M := by ring
    rw [hupow n, abs_mul, abs_of_pos (pow_pos (by linarith) n)] at hbound
    rw [div_lt_iff₀ hpos] at hn
    linarith
  -- hence `p_0 = c k_0` with `c = χ (ω₂ − 1)/K̄`
  have hp0 : p 0 = χ * (ω2 - 1) / Kb * k 0 := by
    have hω1ne : ω1 - 1 ≠ 0 := by linarith
    have hc : (ω1 - 1) * (χ * (ω2 - 1) / Kb) = a := by
      rw [hax]; field_simp
      linear_combination hprod - hsum
    have : (ω1 - 1) * p 0 = (ω1 - 1) * (χ * (ω2 - 1) / Kb * k 0) := by
      rw [← mul_assoc, hc]; linarith
    exact mul_left_cancel₀ hω1ne this
  -- the linear system is deterministic forward: induction
  have hr1' : qCharPoly r (-(Kb * a / χ)) ω2 = 0 := by rw [← hxd]; exact hr1
  have hsol := saddle_path_solves (k0 := k 0) hχ.ne' hKb.ne' hr1'
  induction t with
  | zero => simp [hp0]
  | succ n ih =>
    obtain ⟨hpn, hkn⟩ := hsys n
    obtain ⟨hps, hks⟩ := hsol n
    refine ⟨?_, ?_⟩
    · rw [hkn, ih.1, ih.2]; exact hks.symm
    · rw [hpn, ih.1, ih.2]; exact hps.symm

/-! ## Marginal q equals average q (Hayashi), (2.70) -/

/-- **Euler's theorem for a linearly homogeneous function**, used for O&R (2.70), p. 112: if
`F` is differentiable at `v` with derivative `DF` and `F(λ v) = λ F(v)` for all `λ > 0`, then
`F(v) = DF(v)`; for `v = (K, L)` this is `F = F_K K + F_L L`. -/
theorem euler_of_homogeneous {F : ℝ × ℝ → ℝ} {DF : ℝ × ℝ →L[ℝ] ℝ} {v : ℝ × ℝ}
    (hF : HasFDerivAt F DF v) (hhom : ∀ l : ℝ, 0 < l → F (l • v) = l * F v) :
    F v = DF (1, 0) * v.1 + DF (0, 1) * v.2 := by
  have hray : HasDerivAt (fun l : ℝ => l • v) ((1 : ℝ) • v) 1 :=
    (hasDerivAt_id (1 : ℝ)).smul_const v
  have hF1 : HasFDerivAt F DF ((1 : ℝ) • v) := by rwa [one_smul]
  have h1 : HasDerivAt (fun l : ℝ => F (l • v)) (DF ((1 : ℝ) • v)) 1 :=
    hF1.comp_hasDerivAt (1 : ℝ) hray
  have h2 : HasDerivAt (fun l : ℝ => l * F v) (F v) 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).mul_const (F v)
  have hev : (fun l : ℝ => F (l • v)) =ᶠ[𝓝 1] fun l => l * F v := by
    filter_upwards [Ioi_mem_nhds (zero_lt_one' ℝ)] with l hl using hhom l hl
  have h3 := h2.congr_of_eventuallyEq hev
  have hv : v = v.1 • ((1 : ℝ), (0 : ℝ)) + v.2 • ((0 : ℝ), (1 : ℝ)) := by
    ext <;> simp
  rw [h3.unique h1, one_smul]
  conv_lhs => rw [hv]
  rw [map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
  ring

/-- The firm's date-`s` dividend in O&R (2.62), p. 106:
`A_s F(K_s, L_s) − (χ/2)(I_s²/K_s) − w_s L_s − I_s`. -/
noncomputable def dividend (A w : ℕ → ℝ) (F : ℝ → ℝ → ℝ) (K L I : ℕ → ℝ) (χ : ℝ) (s : ℕ) : ℝ :=
  A s * F (K s) (L s) - χ / 2 * (I s ^ 2 / K s) - w s * L s - I s

/-- **The one-step Hayashi identity**, O&R p. 112: under capital accumulation, the investment
equation (2.63) in the form `q_s = 1 + χ I_s/K_s`, the Euler equation (2.64), Euler's theorem
`F = F_K K + F_L L` and the labour first-order condition `A F_L = w`,
`(1 + r) q_t K_{t+1} = d_{t+1} + q_{t+1} K_{t+2}`. -/
theorem hayashi_step {r χ : ℝ} {A w : ℕ → ℝ} {F FK FL : ℝ → ℝ → ℝ} {K L I q : ℕ → ℝ}
    (hK : ∀ s, K s ≠ 0) (hacc : ∀ s, K (s + 1) = K s + I s)
    (hinv : ∀ s, q s = 1 + χ * (I s / K s))
    (heuler : ∀ s, (1 + r) * q s = marginalEarnings A FK K L I χ (s + 1) + q (s + 1))
    (heul : ∀ s, F (K s) (L s) = FK (K s) (L s) * K s + FL (K s) (L s) * L s)
    (hlab : ∀ s, A s * FL (K s) (L s) = w s) (t : ℕ) :
    (1 + r) * (q t * K (t + 1)) = dividend A w F K L I χ (t + 1) + q (t + 1) * K (t + 1 + 1) := by
  have he := heuler t
  unfold marginalEarnings at he
  unfold dividend
  have hk := hK (t + 1)
  rw [show (1 + r) * (q t * K (t + 1)) = ((1 + r) * q t) * K (t + 1) by ring, he,
    hacc (t + 1), heul (t + 1), ← hlab (t + 1), hinv (t + 1)]
  field_simp
  ring

/-- **Marginal q equals average q**, O&R (2.70), p. 112 (Hayashi 1982): under the hypotheses
of `hayashi_step` and summable discounted dividends, `q_t K_{t+1} = V_t`, the present value
`Σ_{s ≥ t+1} (1 + r)^{-(s-t)} d_s` of future dividends, iff the no-bubble condition
`(1 + r)^{-T} q_{t+T} K_{t+T+1} → 0` holds. -/
theorem marginal_q_eq_average_q {r χ : ℝ} (hr : 1 + r ≠ 0) {A w : ℕ → ℝ}
    {F FK FL : ℝ → ℝ → ℝ} {K L I q : ℕ → ℝ}
    (hK : ∀ s, K s ≠ 0) (hacc : ∀ s, K (s + 1) = K s + I s)
    (hinv : ∀ s, q s = 1 + χ * (I s / K s))
    (heuler : ∀ s, (1 + r) * q s = marginalEarnings A FK K L I χ (s + 1) + q (s + 1))
    (heul : ∀ s, F (K s) (L s) = FK (K s) (L s) * K s + FL (K s) (L s) * L s)
    (hlab : ∀ s, A s * FL (K s) (L s) = w s) (t : ℕ)
    (hsum : Summable fun s => (1 + r)⁻¹ ^ (s + 1) * dividend A w F K L I χ (t + s + 1)) :
    HasSum (fun s => (1 + r)⁻¹ ^ (s + 1) * dividend A w F K L I χ (t + s + 1))
        (q t * K (t + 1)) ↔
      Tendsto (fun T => (1 + r)⁻¹ ^ T * (q (t + T) * K (t + T + 1))) atTop (𝓝 0) := by
  have h := hayashi_step hK hacc hinv heuler heul hlab
  exact ⟨tail_of_hasSum (x := fun s => q s * K (s + 1)) hr h t,
    hasSum_of_tail (x := fun s => q s * K (s + 1)) hr h t hsum⟩

/-- **Rate-of-return form of the Euler equation**, O&R p. 113: with `q_t ≠ 0` and
`K_{t+1} ≠ 0`, (2.64) with (2.63) and capital accumulation gives
`r = [A F_K − (χ/2)(I_{t+1}/K_{t+1})² − I_{t+1}/K_{t+1} + q_{t+1} K_{t+2}/K_{t+1} − q_t]/q_t`. -/
theorem rate_of_return_form {r χ : ℝ} {A : ℕ → ℝ} {FK : ℝ → ℝ → ℝ} {K L I q : ℕ → ℝ}
    {t : ℕ} (hq : q t ≠ 0) (hK : K (t + 1) ≠ 0) (hacc : K (t + 1 + 1) = K (t + 1) + I (t + 1))
    (hinv : q (t + 1) = 1 + χ * (I (t + 1) / K (t + 1)))
    (heuler : (1 + r) * q t = marginalEarnings A FK K L I χ (t + 1) + q (t + 1)) :
    r = (A (t + 1) * FK (K (t + 1)) (L (t + 1)) - χ / 2 * (I (t + 1) / K (t + 1)) ^ 2
      - I (t + 1) / K (t + 1) + q (t + 1) * K (t + 1 + 1) / K (t + 1) - q t) / q t := by
  unfold marginalEarnings at heuler
  rw [eq_div_iff hq, hacc, hinv]
  rw [hinv] at heuler
  field_simp
  field_simp at heuler
  linear_combination heuler

/-! ## Exercise 9: the simplified q model with cost `χ I²/2` (pp. 126–127) -/

/-- **Exercise 9(a), investment**, O&R p. 127: the derivative in `I` of the date-`s` terms
`A F(K) − I − χ I²/2 − q (K' − K − I)` is `−1 − χ I + q`. -/
theorem ex9_hasDerivAt_investment (AF χ q K K' I : ℝ) :
    HasDerivAt (fun i : ℝ => AF - i - χ * i ^ 2 / 2 - q * (K' - K - i)) (-1 - χ * I + q) I := by
  have h1 : HasDerivAt (fun i : ℝ => i ^ 2) (2 * I) I := by simpa using hasDerivAt_pow 2 I
  have hl : HasDerivAt (fun i : ℝ => K' - K - i) (-1) I := by
    simpa using (hasDerivAt_id I).const_sub (K' - K)
  have h := (((hasDerivAt_id I).const_sub AF).sub ((h1.const_mul χ).div_const 2)).sub
    (hl.const_mul q)
  convert h using 1
  · funext i; simp
  · ring

/-- **Exercise 9(a), capital**, O&R p. 127: if `F` has derivative `F'` at `K`, the derivative in
`K_{s+1}` of `−q_s K_{s+1} + (A F(K_{s+1}) − I − χ I²/2 − q_{s+1}(K_{s+2} − K_{s+1} − I))/(1 + r)`
is `−q_s + (A F'(K_{s+1}) + q_{s+1})/(1 + r)`. -/
theorem ex9_hasDerivAt_capital {F : ℝ → ℝ} {F' K : ℝ} (hF : HasDerivAt F F' K)
    (r A χ I q0 q1 K2 : ℝ) :
    HasDerivAt
      (fun k : ℝ => -q0 * k + (1 + r)⁻¹ * (A * F k - I - χ * I ^ 2 / 2 - q1 * (K2 - k - I)))
      (-q0 + (1 + r)⁻¹ * (A * F' + q1)) K := by
  have hl : HasDerivAt (fun k : ℝ => K2 - k - I) (-1) K := by
    simpa using ((hasDerivAt_id K).const_sub K2).sub_const I
  have h := ((hasDerivAt_id K).const_mul (-q0)).add
    (((((hF.const_mul A).sub_const I).sub_const (χ * I ^ 2 / 2)).sub (hl.const_mul q1)).const_mul
      (1 + r)⁻¹)
  convert h using 1
  · funext k; simp
  · ring

/-- **Exercise 9(b)**, O&R p. 127: the first-order conditions `−1 − χ I_t + q_t = 0` and
`(1 + r) q_t = A_{t+1} F'(K_{t+1}) + q_{t+1}` with `K_{t+1} = K_t + I_t` imply
`K_{t+1} − K_t = (q_t − 1)/χ` and `q_{t+1} − q_t = r q_t − A_{t+1} F'(K_t + (q_t − 1)/χ)`. -/
theorem ex9_system {r χ : ℝ} (hχ : χ ≠ 0) {A : ℕ → ℝ} {F' : ℝ → ℝ} {K I q : ℕ → ℝ} {t : ℕ}
    (hfoc : -1 - χ * I t + q t = 0) (hacc : K (t + 1) = K t + I t)
    (heuler : (1 + r) * q t = A (t + 1) * F' (K (t + 1)) + q (t + 1)) :
    K (t + 1) - K t = (q t - 1) / χ ∧
      q (t + 1) - q t = r * q t - A (t + 1) * F' (K t + (q t - 1) / χ) := by
  have hI : I t = (q t - 1) / χ := by field_simp; linarith
  have hk : K (t + 1) = K t + (q t - 1) / χ := by rw [hacc, hI]
  refine ⟨by rw [hk]; ring, ?_⟩
  rw [← hk]; linarith

/-- **Exercise 9(c)**, O&R p. 127: for any `χ ≠ 0`, `(q̄, K̄)` is a rest point of the
Exercise 9 system iff `q̄ = 1` and `A F'(K̄) = r`; the steady state does not depend on the
adjustment-cost parameter `χ`. -/
theorem ex9_steady_state_iff {r χ A qb Kb : ℝ} (hχ : χ ≠ 0) {F' : ℝ → ℝ} :
    ((qb - 1) / χ = 0 ∧ r * qb - A * F' (Kb + (qb - 1) / χ) = 0) ↔ (qb = 1 ∧ A * F' Kb = r) := by
  constructor
  · rintro ⟨h1, h2⟩
    have hq : qb = 1 := by
      rcases div_eq_zero_iff.1 h1 with h | h
      · linarith
      · exact absurd h hχ
    subst hq
    refine ⟨rfl, ?_⟩
    simp at h2; linarith
  · rintro ⟨rfl, h⟩
    simp [h]

/-- **The text's cost is homogeneous of degree one**, O&R (2.62), p. 106 and footnote 45:
`χ (λI)²/(2 λK) = λ χ I²/(2K)` for `λ ≠ 0`. -/
theorem text_cost_homogeneous (χ I K l : ℝ) (hl : l ≠ 0) :
    χ * (l * I) ^ 2 / (2 * (l * K)) = l * (χ * I ^ 2 / (2 * K)) := by
  by_cases hK : K = 0
  · simp [hK]
  · field_simp

/-- **Exercise 9(f): the cost `χ I²/2` is not homogeneous of degree one** in `(I, K)`, O&R
p. 127: doubling `(I, K) = (1, 1)` multiplies the cost by `4`, not `2` (for `χ ≠ 0`). -/
theorem ex9_cost_not_homogeneous {χ : ℝ} (hχ : χ ≠ 0) :
    χ * (2 * (1 : ℝ)) ^ 2 / 2 ≠ 2 * (χ * (1 : ℝ) ^ 2 / 2) := by
  intro h
  apply hχ
  linarith

/-- The Exercise 9 dividend `A_s F(K_s) − I_s − χ I_s²/2` (O&R p. 127). -/
noncomputable def ex9Dividend (A : ℕ → ℝ) (F : ℝ → ℝ) (K I : ℕ → ℝ) (χ : ℝ) (s : ℕ) : ℝ :=
  A s * F (K s) - I s - χ * I s ^ 2 / 2

/-- **Exercise 9(f), one-step identity**, O&R p. 127: in the Exercise 9 model, even with a
linear technology (`F'(K) K = F(K)`, the analogue of Euler's theorem when `L` is fixed), the
Hayashi recursion picks up an extra term:
`(1 + r) q_t K_{t+1} = (d_{t+1} − χ I_{t+1}²/2) + q_{t+1} K_{t+2}`. -/
theorem ex9_step {r χ : ℝ} {A : ℕ → ℝ} {F F' : ℝ → ℝ} {K I q : ℕ → ℝ}
    (hacc : ∀ s, K (s + 1) = K s + I s) (hfoc : ∀ s, -1 - χ * I s + q s = 0)
    (heuler : ∀ s, (1 + r) * q s = A (s + 1) * F' (K (s + 1)) + q (s + 1))
    (hlin : ∀ s, F' (K s) * K s = F (K s)) (t : ℕ) :
    (1 + r) * (q t * K (t + 1)) =
      (ex9Dividend A F K I χ (t + 1) - χ * I (t + 1) ^ 2 / 2) + q (t + 1) * K (t + 1 + 1) := by
  unfold ex9Dividend
  rw [hacc (t + 1), ← hlin (t + 1)]
  have hq : q (t + 1) = 1 + χ * I (t + 1) := by linarith [hfoc (t + 1)]
  rw [show (1 + r) * (q t * K (t + 1)) = ((1 + r) * q t) * K (t + 1) by ring, heuler t, hq]
  ring

/-- **Exercise 9(f): marginal q falls short of average q**, O&R p. 127. Under the hypotheses of
`ex9_step`, summable discounted dividends `V_t` and installation costs, and the no-bubble
condition on `q_s K_{s+1}`, `V_t − q_t K_{t+1} = Σ_{s ≥ t+1} (1 + r)^{-(s-t)} χ I_s²/2`. With
`r > −1`, `χ > 0` and some future `I_s ≠ 0`, this gap is strictly positive. -/
theorem ex9_average_q_gap {r χ : ℝ} (hr : 0 < 1 + r) (hχ : 0 < χ) {A : ℕ → ℝ}
    {F F' : ℝ → ℝ} {K I q : ℕ → ℝ}
    (hacc : ∀ s, K (s + 1) = K s + I s) (hfoc : ∀ s, -1 - χ * I s + q s = 0)
    (heuler : ∀ s, (1 + r) * q s = A (s + 1) * F' (K (s + 1)) + q (s + 1))
    (hlin : ∀ s, F' (K s) * K s = F (K s)) (t : ℕ) {V : ℝ}
    (hV : HasSum (fun s => (1 + r)⁻¹ ^ (s + 1) * ex9Dividend A F K I χ (t + s + 1)) V)
    (hc : Summable fun s => (1 + r)⁻¹ ^ (s + 1) * (χ * I (t + s + 1) ^ 2 / 2))
    (htail : Tendsto (fun T => (1 + r)⁻¹ ^ T * (q (t + T) * K (t + T + 1))) atTop (𝓝 0)) :
    V - q t * K (t + 1) = ∑' s, (1 + r)⁻¹ ^ (s + 1) * (χ * I (t + s + 1) ^ 2 / 2) ∧
      ((∃ n, I (t + n + 1) ≠ 0) → q t * K (t + 1) < V) := by
  have h := ex9_step (r := r) hacc hfoc heuler hlin
  have hsum : Summable fun s => (1 + r)⁻¹ ^ (s + 1) *
      (ex9Dividend A F K I χ (t + s + 1) - χ * I (t + s + 1) ^ 2 / 2) := by
    have := hV.summable.sub hc
    refine this.congr fun s => ?_
    ring
  have hq := hasSum_of_tail (x := fun s => q s * K (s + 1))
    (y := fun s => ex9Dividend A F K I χ s - χ * I s ^ 2 / 2) hr.ne' h t hsum htail
  have hdiff := hV.sub hq
  have hgap : V - q t * K (t + 1) = ∑' s, (1 + r)⁻¹ ^ (s + 1) * (χ * I (t + s + 1) ^ 2 / 2) := by
    refine (HasSum.tsum_eq ?_).symm
    refine hdiff.congr_fun fun s => ?_
    ring
  refine ⟨hgap, fun ⟨n, hn⟩ => ?_⟩
  have hb : 0 < (1 + r)⁻¹ := inv_pos.2 hr
  have hpos : 0 < ∑' s, (1 + r)⁻¹ ^ (s + 1) * (χ * I (t + s + 1) ^ 2 / 2) := by
    refine hc.tsum_pos (fun s => by positivity) n ?_
    have : 0 < I (t + n + 1) ^ 2 := by positivity
    positivity
  linarith

/-- **Exercise 9(f): an explicit counterexample**, O&R p. 127. Take `r = 1`, `A = 2`,
`F(K) = K`, `χ = 1`, `q_s = 2`, `I_s = 1`, `K_s = s + 1`. All first-order conditions and the
no-bubble condition hold, yet `q_0 K_1 = 4` differs from average q times capital:
`V_0 − q_0 K_1 = Σ 2^{-(s+1)}/2 = 1/2 > 0`. -/
theorem ex9_counterexample :
    let K : ℕ → ℝ := fun s => s + 1
    let I : ℕ → ℝ := fun _ => 1
    let q : ℕ → ℝ := fun _ => 2
    let A : ℕ → ℝ := fun _ => 2
    (∀ s, K (s + 1) = K s + I s) ∧ (∀ s, -1 - 1 * I s + q s = 0) ∧
      (∀ s, (1 + 1) * q s = A (s + 1) * (fun _ => (1 : ℝ)) (K (s + 1)) + q (s + 1)) ∧
      (∀ s, (fun _ => (1 : ℝ)) (K s) * K s = id (K s)) ∧
      Tendsto (fun T => (1 + 1 : ℝ)⁻¹ ^ T * (q (0 + T) * K (0 + T + 1))) atTop (𝓝 0) ∧
      ∃ V : ℝ, HasSum (fun s => (1 + 1 : ℝ)⁻¹ ^ (s + 1) * ex9Dividend A id K I 1 (0 + s + 1)) V ∧
        V - q 0 * K 1 = 1 / 2 := by
  intro K I q A
  have hhalf : (1 + 1 : ℝ)⁻¹ = 1 / 2 := by norm_num
  have hg := summable_geometric_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  have hn := summable_pow_mul_geometric_of_norm_lt_one (R := ℝ) 1 (r := 1 / 2) (by norm_num)
  have hVs : Summable fun s => (1 + 1 : ℝ)⁻¹ ^ (s + 1) * ex9Dividend A id K I 1 (0 + s + 1) := by
    refine (hn.add (hg.mul_left (5 / 4))).congr fun s => ?_
    simp only [ex9Dividend, K, I, A, id, hhalf]
    push_cast
    ring
  have hc : Summable fun s => (1 + 1 : ℝ)⁻¹ ^ (s + 1) * (1 * I (0 + s + 1) ^ 2 / 2) := by
    refine (hg.mul_left (1 / 4)).congr fun s => ?_
    simp only [I, hhalf]
    ring
  have htail : Tendsto (fun T => (1 + 1 : ℝ)⁻¹ ^ T * (q (0 + T) * K (0 + T + 1))) atTop
      (𝓝 0) := by
    have h1 := tendsto_self_mul_const_pow_of_lt_one (r := 1 / 2) (by norm_num) (by norm_num)
    have h2 := tendsto_pow_atTop_nhds_zero_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num)
      (by norm_num)
    have h3 := (h1.const_mul 2).add (h2.const_mul 4)
    simp only [mul_zero, add_zero] at h3
    refine h3.congr fun T => ?_
    simp only [q, K, hhalf]
    push_cast
    ring
  have hacc : ∀ s, K (s + 1) = K s + I s := fun s => by simp only [K, I]; push_cast; ring
  have hfoc : ∀ s, -1 - 1 * I s + q s = 0 := fun s => by simp only [I, q]; norm_num
  have heul : ∀ s, (1 + 1) * q s = A (s + 1) * (fun _ => (1 : ℝ)) (K (s + 1)) + q (s + 1) :=
    fun s => by simp only [A, q]; norm_num
  have hlin : ∀ s, (fun _ => (1 : ℝ)) (K s) * K s = id (K s) := fun s => by simp
  refine ⟨hacc, hfoc, heul, hlin, htail, _, hVs.hasSum, ?_⟩
  obtain ⟨hgap, -⟩ := ex9_average_q_gap (r := 1) (χ := 1) (by norm_num) (by norm_num)
    (A := A) (F := id) (F' := fun _ => 1) hacc hfoc heul hlin 0 hVs.hasSum hc htail
  rw [hgap]
  have : HasSum (fun s => (1 + 1 : ℝ)⁻¹ ^ (s + 1) * (1 * I (0 + s + 1) ^ 2 / 2)) (1 / 2) := by
    have := (hasSum_geometric_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)).mul_left
      (1 / 4)
    convert this using 1
    · funext s; simp only [I, hhalf]; ring
    · norm_num
  exact this.tsum_eq

end ObstfeldRogoff.SmallOpenEconomyDynamics.TobinQ
