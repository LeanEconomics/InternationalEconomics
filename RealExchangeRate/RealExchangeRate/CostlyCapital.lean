/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Costly capital mobility and short-run relative price adjustment

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*,
Appendix 4B, pp. 260–264. Capital is freely mobile into tradables but costly to
install in nontradables. Output there is `Y_N = A_N K_N^α L_N^{1−α}`. Preferences
have unit elasticities (`σ = θ = 1`) and `β(1 + r) = 1`, so tradables consumption
`C̄_T` is constant. Demand for nontradables in tradables units is
`D = (1 − γ)C̄_T/γ + G̃_N`.

* **Short-run equilibrium** (O&R (73)–(74)). With the labour first-order condition
  (69) and market clearing, employment in nontradables is `L_N = (1 − α)D/w`,
  independent of the capital stock. The relative price is
  `p = w^{1−α}D^α/((1 − α)^{1−α} A_N K_N^α)`, strictly decreasing in `K_N`.
* **The q dynamics** (O&R (75)). The value marginal product of capital is `αD/K`.
  The steady state is `q̄ = 1`, `K̄_N = αD/r`, with `K̄/L̄ = αw/((1 − α)r)`.
* **Saddle-point stability** (p. 263, Figure 4.15). The linearised system
  `x_{t+1} = (I + J)x_t` has `J = [[0, K̄/χ], [r/K̄, r(1 + 1/χ)]]`, and `I + J` has exactly
  one eigenvalue inside the unit circle for every `r, χ > 0`: one stable root in
  `(−1, 1)` and one unstable root above `1`.
-/

namespace ObstfeldRogoff.RealExchangeRate.CostlyCapital

/-- **Employment in nontradables**, O&R (74), p. 262: with the labour first-order condition
`w L^α = (1 − α) p A K^α` (equivalent to (69)) and market clearing `D = p A K^α L^{1−α}`,
employment is `L = (1 − α)D/w`, independent of `K`. -/
theorem employment_nontradables {α w p A K L D : ℝ} (hL : 0 < L)
    (hfoc : w * L ^ α = (1 - α) * p * A * K ^ α) (hclear : D = p * A * K ^ α * L ^ (1 - α))
    (hw : w ≠ 0) :
    L = (1 - α) * D / w := by
  have hLL : L ^ α * L ^ (1 - α) = L := by
    rw [← Real.rpow_add hL, add_sub_cancel, Real.rpow_one]
  rw [eq_div_iff hw, hclear]
  calc L * w = (w * L ^ α) * L ^ (1 - α) := by rw [mul_assoc, hLL]; ring
    _ = (1 - α) * (p * A * K ^ α * L ^ (1 - α)) := by rw [hfoc]; ring

/-- **The short-run relative price of nontradables**, O&R (73), p. 261:
`p = w^{1−α}D^α/((1 − α)^{1−α} A K^α)`. -/
theorem price_nontradables {α w p A K L D : ℝ} (hα1 : α < 1) (hw : 0 < w) (hA : 0 < A)
    (hK : 0 < K) (hL : 0 < L) (hD : 0 < D)
    (hfoc : w * L ^ α = (1 - α) * p * A * K ^ α) (hclear : D = p * A * K ^ α * L ^ (1 - α)) :
    p = w ^ (1 - α) * D ^ α / ((1 - α) ^ (1 - α) * A * K ^ α) := by
  have hL' := employment_nontradables hL hfoc hclear hw.ne'
  have h1a : 0 < 1 - α := by linarith
  have hKa : 0 < K ^ α := Real.rpow_pos_of_pos hK α
  have hp : p = w * L ^ α / ((1 - α) * A * K ^ α) := by
    rw [eq_div_iff (by positivity)]
    linarith [hfoc]
  rw [hp, hL', Real.div_rpow (by positivity) hw.le, Real.mul_rpow h1a.le hD.le]
  have hwa : 0 < w ^ α := Real.rpow_pos_of_pos hw α
  have h1aa : 0 < (1 - α) ^ α := Real.rpow_pos_of_pos h1a α
  have hw' : w ^ (1 - α) = w / w ^ α := by rw [Real.rpow_sub hw, Real.rpow_one]
  have h1' : (1 - α) ^ (1 - α) = (1 - α) / (1 - α) ^ α := by
    rw [Real.rpow_sub h1a, Real.rpow_one]
  rw [hw', h1']
  field_simp

/-- **The relative price falls as nontradables capital accumulates** (O&R p. 263, lower panel of
Figure 4.15): at given `w`, `D` and `A`, the price (73) is strictly decreasing in `K`. -/
theorem price_strictAnti_capital {α w A D : ℝ} (hα : 0 < α) (hα1 : α < 1) (hw : 0 < w)
    (hA : 0 < A) (hD : 0 < D) {K K' : ℝ} (hK : 0 < K) (hKK : K < K') :
    w ^ (1 - α) * D ^ α / ((1 - α) ^ (1 - α) * A * K' ^ α) <
      w ^ (1 - α) * D ^ α / ((1 - α) ^ (1 - α) * A * K ^ α) := by
  have h1a : 0 < 1 - α := by linarith
  have hnum : 0 < w ^ (1 - α) * D ^ α := by positivity
  have hc : 0 < (1 - α) ^ (1 - α) * A := by positivity
  have hpow : K ^ α < K' ^ α := Real.rpow_lt_rpow hK.le hKK hα
  apply div_lt_div_of_pos_left hnum (by positivity)
  exact mul_lt_mul_of_pos_left hpow hc

/-- **The value marginal product of capital**, used in O&R (75): with market clearing
`D = p A K^α L^{1−α}`, `p · α A K^{α−1} L^{1−α} = αD/K`. -/
theorem value_marginal_product {α p A K L D : ℝ} (hK : 0 < K)
    (hclear : D = p * A * K ^ α * L ^ (1 - α)) :
    p * (α * A * K ^ (α - 1) * L ^ (1 - α)) = α * D / K := by
  rw [hclear, Real.rpow_sub hK, Real.rpow_one]
  field_simp

/-- The right side of the `q` equation (75) without the second-order term:
`F(q, K) = rq − αD/(K(1 + (q − 1)/χ))`. -/
noncomputable def qDrift (r α D χ q K : ℝ) : ℝ := r * q - α * D / (K * (1 + (q - 1) / χ))

/-- **The steady state**, O&R p. 262: `q̄ = 1` and `K̄ = αD/r` make both `ΔK = (q − 1)K/χ` (70) and
the `q` equation stationary; `q̄ = 1` is forced by (70) and then `K̄ = αD/r` by (75). -/
theorem steady_state_iff {r α D χ K : ℝ} (hr : 0 < r) (hK : 0 < K) :
    qDrift r α D χ 1 K = 0 ↔ K = α * D / r := by
  unfold qDrift
  simp only [sub_self, zero_div, add_zero, mul_one]
  rw [sub_eq_zero, eq_div_iff hr.ne', eq_div_iff hK.ne']
  constructor <;> intro h <;> linarith

/-- **The steady-state capital–labour ratio**, O&R p. 262: `K̄/L̄ = αw/((1 − α)r)`, so the value
marginal product of capital is back to `r`. -/
theorem steady_capital_labour {r α D w : ℝ} (hr : 0 < r) (hα1 : α < 1) (hw : 0 < w)
    (hD : 0 < D) :
    (α * D / r) / ((1 - α) * D / w) = α * w / ((1 - α) * r) := by
  have h1a : (1 - α) ≠ 0 := by linarith
  field_simp

/-- **Linearisation in `q`**, O&R p. 262: at the steady state,
`∂F/∂q = r + αD/(χK̄) = r(1 + 1/χ)`. -/
theorem hasDerivAt_qDrift_q {r α D χ : ℝ} (hαD : 0 < α * D) :
    HasDerivAt (fun q => qDrift r α D χ q (α * D / r)) (r * (1 + 1 / χ)) 1 := by
  have hfun : (fun q => qDrift r α D χ q (α * D / r)) =
      fun q => r * q - r / (1 + (q - 1) / χ) := by
    funext q
    unfold qDrift
    rw [← div_div, div_div_cancel₀ hαD.ne']
  rw [hfun]
  have h1 : HasDerivAt (fun q : ℝ => r * q) r 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).const_mul r
  have h3 : HasDerivAt (fun q : ℝ => 1 + (q - 1) / χ) (1 / χ) 1 := by
    have := (((hasDerivAt_id (1 : ℝ)).sub_const 1).div_const χ).const_add 1
    simpa using this
  have h4 : HasDerivAt (fun q : ℝ => r / (1 + (q - 1) / χ))
      ((0 * (1 + (1 - 1) / χ) - r * (1 / χ)) / (1 + (1 - 1) / χ) ^ 2) 1 :=
    (hasDerivAt_const (1 : ℝ) r).div h3 (by simp)
  refine HasDerivAt.congr_deriv (HasDerivAt.sub h1 h4) ?_
  simp
  ring

/-- **Linearisation in `K`**, O&R p. 262: at the steady state, `∂F/∂K = αD/K̄² = r/K̄`. -/
theorem hasDerivAt_qDrift_K {r α D χ : ℝ} (hr : 0 < r) (hαD : 0 < α * D) :
    HasDerivAt (fun K => qDrift r α D χ 1 K) (r / (α * D / r)) (α * D / r) := by
  have hK : 0 < α * D / r := div_pos hαD hr
  have hfun : (fun K => qDrift r α D χ 1 K) = fun K => r - α * D / K := by
    funext K
    simp [qDrift]
  rw [hfun]
  have h2 : HasDerivAt (fun K : ℝ => α * D / K) (-(α * D) / (α * D / r) ^ 2) (α * D / r) := by
    have := (hasDerivAt_inv hK.ne').const_mul (α * D)
    convert this using 1
    · funext K; ring
    · field_simp
  refine HasDerivAt.congr_deriv (HasDerivAt.sub (hasDerivAt_const _ r) h2) ?_
  field_simp
  ring

/-! ### Saddle-point stability of the linearised system -/

/-- The characteristic polynomial of `J = [[0, K̄/χ], [r/K̄, r(1 + 1/χ)]]`:
`μ² − r(1 + 1/χ)μ − r/χ`. It does not depend on `K̄`. -/
noncomputable def charPolyJ (r χ μ : ℝ) : ℝ := μ ^ 2 - r * (1 + 1 / χ) * μ - r / χ

/-- The characteristic polynomial is the determinant of `J − μI` for any `K̄ ≠ 0`. -/
theorem charPolyJ_eq_det {r χ Kb μ : ℝ} (hKb : Kb ≠ 0) :
    charPolyJ r χ μ = (0 - μ) * (r * (1 + 1 / χ) - μ) - (Kb / χ) * (r / Kb) := by
  unfold charPolyJ
  field_simp
  ring

/-- The discriminant of the characteristic polynomial is positive: the roots are real and
distinct. -/
theorem charPolyJ_disc_pos {r χ : ℝ} (hr : 0 < r) (hχ : 0 < χ) :
    0 < (r * (1 + 1 / χ)) ^ 2 + 4 * (r / χ) := by positivity

/-- **The stable root of `J` lies in `(−2, 0)`** (O&R p. 263): the characteristic polynomial is
negative at `0` (`det J = −r/χ < 0`) and positive at `−2` (`4 + 2r + r/χ > 0`), so there is a root
`μ₋ ∈ (−2, 0)`; hence `1 + μ₋ ∈ (−1, 1)` is a stable eigenvalue of `I + J`. -/
theorem stable_root_mem {r χ : ℝ} (hr : 0 < r) (hχ : 0 < χ) :
    charPolyJ r χ 0 < 0 ∧ 0 < charPolyJ r χ (-2) := by
  unfold charPolyJ
  constructor
  · have : 0 < r / χ := div_pos hr hχ
    linarith
  · have : 0 < r / χ := div_pos hr hχ
    have e : r * (1 + 1 / χ) = r + r / χ := by ring
    rw [e]
    nlinarith

/-- The two roots of the characteristic polynomial, `μ = [b ∓ √(b² + 4c)]/2` with
`b = r(1 + 1/χ)`, `c = r/χ`. -/
noncomputable def rootJ (r χ : ℝ) (sgn : ℝ) : ℝ :=
  (r * (1 + 1 / χ) + sgn * Real.sqrt ((r * (1 + 1 / χ)) ^ 2 + 4 * (r / χ))) / 2

theorem rootJ_isRoot {r χ : ℝ} (hr : 0 < r) (hχ : 0 < χ) {sgn : ℝ} (hs : sgn ^ 2 = 1) :
    charPolyJ r χ (rootJ r χ sgn) = 0 := by
  unfold charPolyJ rootJ
  have hd := charPolyJ_disc_pos hr hχ
  have hsq := Real.sq_sqrt hd.le
  nlinarith [hsq, hs]

/-- **Saddle-point stability**, O&R p. 263 and Figure 4.15: for every `r, χ > 0` the eigenvalues
of `I + J` are real, one in `(−1, 1)` (the stable root) and one above `1` (the unstable root). -/
theorem saddle_point {r χ : ℝ} (hr : 0 < r) (hχ : 0 < χ) :
    -1 < 1 + rootJ r χ (-1) ∧ 1 + rootJ r χ (-1) < 1 ∧ 1 < 1 + rootJ r χ 1 := by
  have hd := charPolyJ_disc_pos hr hχ
  set b := r * (1 + 1 / χ) with hb
  set c := r / χ with hc
  have hbpos : 0 < b := by positivity
  have hcpos : 0 < c := div_pos hr hχ
  set s := Real.sqrt (b ^ 2 + 4 * c) with hs
  have hs2 : s ^ 2 = b ^ 2 + 4 * c := Real.sq_sqrt hd.le
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hsb : b < s := by nlinarith
  unfold rootJ
  rw [← hb, ← hc, ← hs]
  refine ⟨?_, ?_, ?_⟩
  · -- (b − s)/2 > −2  ⇔  s < b + 4  ⇔  b² + 4c < (b + 4)², i.e. c < 2b + 4 (true since b = r + c)
    have hbc : b = r + c := by rw [hb, hc]; ring
    have : s < b + 4 := by nlinarith
    linarith
  · linarith
  · linarith

end ObstfeldRogoff.RealExchangeRate.CostlyCapital
