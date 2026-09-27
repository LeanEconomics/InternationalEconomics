/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Tax smoothing à la Barro

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*,
Exercise 6 of Chapter 3, p. 197. A small open representative-consumer economy has
`β = 1/(1 + r)`. Taxes `T_t` distort output, which is `Y_t − aT_t²/2` with
`a > 0`. The government must finance spending `G_t` and satisfy its intertemporal
budget constraint `Σ(1 + r)^{-s} T_s = Σ(1 + r)^{-s} G_s − (1 + r)B^G_0`.

* **Welfare depends on the tax path.** Consolidating the private and government
  budget constraints, the consumer's wealth is
  `(1 + r)(B^P_0 + B^G_0) + PV(Y − G) − PV(aT²/2)`: taxes matter only through the
  present value of their distortions. The government is therefore not indifferent
  to the timing of taxes.
* **Taxes should be smoothed.** Among all tax paths raising a given present value,
  the constant path `T̄ = r/(1 + r) · PV(T)` minimises the present value of the
  distortion, and uniquely so. This is Jensen's inequality for the convex cost `T²`.
* **Deficits track temporary spending.** With constant taxes equal to the permanent
  value of spending net of initial assets, the government runs a deficit exactly
  when spending is above its permanent level. With constant spending it never runs
  a deficit or a surplus.

The discount factor and the discounted-telescoping idea are copied from
`SmallOpenEconomyDynamics.PresentValue` so that this project builds on its own.
-/

namespace ObstfeldRogoff.LifeCycleFiscalPolicy.TaxSmoothing

open Filter Topology

/-- The one-period discount factor `1/(1 + r)` (copied from `SmallOpenEconomyDynamics`). -/
noncomputable def taxDisc (r : ℝ) : ℝ := (1 + r)⁻¹

/-- `Σ_{s≥0} (1 + r)^{-s} = (1 + r)/r` for `r > 0`. -/
theorem hasSum_taxDisc_pow {r : ℝ} (hr : 0 < r) :
    HasSum (fun s => taxDisc r ^ s) ((1 + r) / r) := by
  have h0 : 0 ≤ taxDisc r := (inv_pos.2 (by linarith : (0 : ℝ) < 1 + r)).le
  have h1 : taxDisc r < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  convert hasSum_geometric_of_lt_one h0 h1 using 1
  have h2 : (1 : ℝ) + r ≠ 0 := by linarith
  have h3 : r ≠ 0 := hr.ne'
  have e : 1 - (1 + r)⁻¹ = r / (1 + r) := by field_simp; ring
  unfold taxDisc
  rw [e, inv_div]

/-- **Consolidated wealth**, Exercise 6: if the consumer's budget is
`PV(C) = (1 + r)B^P_0 + PV(Y − aT²/2 − T)` and the government's is
`PV(T) = PV(G) − (1 + r)B^G_0`, then
`PV(C) = (1 + r)(B^P_0 + B^G_0) + PV(Y − G) − PV(aT²/2)`. -/
theorem consolidated_wealth {r BP BG pvC pvY pvG pvT pvDist : ℝ}
    (hcons : pvC = (1 + r) * BP + (pvY - pvDist - pvT))
    (hgov : pvT = pvG - (1 + r) * BG) :
    pvC = (1 + r) * (BP + BG) + (pvY - pvG) - pvDist := by
  rw [hcons, hgov]
  ring

/-- **Taxes matter through their distortions**, Exercise 6: with flat consumption
`C = r/(1 + r) · PV(C)` (since `β(1 + r) = 1`), a tax path with a larger present value of
distortions gives strictly lower consumption in every period. -/
theorem consumption_lower_of_distortion {r BP BG pvY pvG d d' : ℝ} (hr : 0 < r) (hd : d < d') :
    r / (1 + r) * ((1 + r) * (BP + BG) + (pvY - pvG) - d') <
      r / (1 + r) * ((1 + r) * (BP + BG) + (pvY - pvG) - d) := by
  have : 0 < r / (1 + r) := div_pos hr (by linarith)
  exact mul_lt_mul_of_pos_left (by linarith) this

/-- **Tax smoothing**, Exercise 6: if `T` raises the same present value as the constant tax `T̄`,
the present value of the squared tax is at least that of the constant path. -/
theorem pv_sq_ge_of_pv_eq {r Tbar : ℝ} (hr : 0 < r) {T : ℕ → ℝ}
    (hT : Summable fun s => taxDisc r ^ s * T s)
    (hT2 : Summable fun s => taxDisc r ^ s * T s ^ 2)
    (hpv : ∑' s, taxDisc r ^ s * T s = ∑' s, taxDisc r ^ s * Tbar) :
    ∑' s, taxDisc r ^ s * Tbar ^ 2 ≤ ∑' s, taxDisc r ^ s * T s ^ 2 := by
  have hg := (hasSum_taxDisc_pow hr).summable
  have hc : Summable fun s => taxDisc r ^ s * Tbar := hg.mul_right Tbar
  have hc2 : Summable fun s => taxDisc r ^ s * Tbar ^ 2 := hg.mul_right (Tbar ^ 2)
  have hpos : ∀ s, 0 ≤ taxDisc r ^ s :=
    fun s => pow_nonneg (inv_pos.2 (by linarith : (0 : ℝ) < 1 + r)).le s
  -- the tangent-line bound T² ≥ T̄² + 2T̄(T − T̄), weighted by the discount factor
  have hterm : ∀ s, taxDisc r ^ s * Tbar ^ 2 + 2 * Tbar * (taxDisc r ^ s * T s -
      taxDisc r ^ s * Tbar) ≤ taxDisc r ^ s * T s ^ 2 := by
    intro s
    have := mul_nonneg (hpos s) (sq_nonneg (T s - Tbar))
    nlinarith
  have hsum : Summable fun s => taxDisc r ^ s * Tbar ^ 2 + 2 * Tbar * (taxDisc r ^ s * T s -
      taxDisc r ^ s * Tbar) := hc2.add ((hT.sub hc).mul_left _)
  have hle := hsum.tsum_le_tsum hterm hT2
  rw [hc2.tsum_add ((hT.sub hc).mul_left _), tsum_mul_left, hT.tsum_sub hc, hpv, sub_self,
    mul_zero, add_zero] at hle
  exact hle

/-- **Strict tax smoothing**: any tax path that raises the same present value as the constant path
but is not constant has a strictly larger present value of squared taxes. -/
theorem pv_sq_gt_of_pv_eq {r Tbar : ℝ} (hr : 0 < r) {T : ℕ → ℝ}
    (hT : Summable fun s => taxDisc r ^ s * T s)
    (hT2 : Summable fun s => taxDisc r ^ s * T s ^ 2)
    (hpv : ∑' s, taxDisc r ^ s * T s = ∑' s, taxDisc r ^ s * Tbar) {k : ℕ} (hk : T k ≠ Tbar) :
    ∑' s, taxDisc r ^ s * Tbar ^ 2 < ∑' s, taxDisc r ^ s * T s ^ 2 := by
  have hg := (hasSum_taxDisc_pow hr).summable
  have hc : Summable fun s => taxDisc r ^ s * Tbar := hg.mul_right Tbar
  have hc2 : Summable fun s => taxDisc r ^ s * Tbar ^ 2 := hg.mul_right (Tbar ^ 2)
  have hdpos : ∀ s, 0 < taxDisc r ^ s :=
    fun s => pow_pos (inv_pos.2 (by linarith : (0 : ℝ) < 1 + r)) s
  have hterm : ∀ s, taxDisc r ^ s * Tbar ^ 2 + 2 * Tbar * (taxDisc r ^ s * T s -
      taxDisc r ^ s * Tbar) ≤ taxDisc r ^ s * T s ^ 2 := by
    intro s
    have := mul_nonneg (hdpos s).le (sq_nonneg (T s - Tbar))
    nlinarith
  have hstrict : taxDisc r ^ k * Tbar ^ 2 + 2 * Tbar * (taxDisc r ^ k * T k -
      taxDisc r ^ k * Tbar) < taxDisc r ^ k * T k ^ 2 := by
    have := mul_pos (hdpos k) (pow_pos (abs_pos.2 (sub_ne_zero.2 hk)) 2)
    rw [sq_abs] at this
    nlinarith
  have hsum : Summable fun s => taxDisc r ^ s * Tbar ^ 2 + 2 * Tbar * (taxDisc r ^ s * T s -
      taxDisc r ^ s * Tbar) := hc2.add ((hT.sub hc).mul_left _)
  have hlt := hsum.tsum_lt_tsum hterm hstrict hT2
  rw [hc2.tsum_add ((hT.sub hc).mul_left _), tsum_mul_left, hT.tsum_sub hc, hpv, sub_self,
    mul_zero, add_zero] at hlt
  exact hlt

/-- **The optimal tax rule**, Exercise 6: with `a > 0`, the constant tax raising the required
present value minimises the present value of the distortion `aT²/2`, and every other tax path
raising the same present value is strictly worse. The government is not indifferent. -/
theorem constant_tax_optimal {r a Tbar : ℝ} (hr : 0 < r) (ha : 0 < a) {T : ℕ → ℝ}
    (hT : Summable fun s => taxDisc r ^ s * T s)
    (hT2 : Summable fun s => taxDisc r ^ s * T s ^ 2)
    (hpv : ∑' s, taxDisc r ^ s * T s = ∑' s, taxDisc r ^ s * Tbar) :
    a / 2 * ∑' s, taxDisc r ^ s * Tbar ^ 2 ≤ a / 2 * ∑' s, taxDisc r ^ s * T s ^ 2 ∧
      ((∃ k, T k ≠ Tbar) →
        a / 2 * ∑' s, taxDisc r ^ s * Tbar ^ 2 < a / 2 * ∑' s, taxDisc r ^ s * T s ^ 2) := by
  have ha2 : 0 < a / 2 := by linarith
  refine ⟨mul_le_mul_of_nonneg_left (pv_sq_ge_of_pv_eq hr hT hT2 hpv) ha2.le, ?_⟩
  rintro ⟨k, hk⟩
  exact mul_lt_mul_of_pos_left (pv_sq_gt_of_pv_eq hr hT hT2 hpv hk) ha2

/-- The constant tax raising present value `R` is `T̄ = r/(1 + r) · R`: the permanent value of the
required revenue. -/
theorem constant_tax_level {r R : ℝ} (hr : 0 < r) :
    ∑' s, taxDisc r ^ s * (r / (1 + r) * R) = R := by
  rw [tsum_mul_right, (hasSum_taxDisc_pow hr).tsum_eq]
  have h1 : (1 : ℝ) + r ≠ 0 := by linarith
  have h2 : r ≠ 0 := hr.ne'
  field_simp

/-- **Deficits track temporary spending**, Exercise 6: if the constant tax equals the permanent
value of spending net of interest on initial assets, `T̄ = G̃ − rB^G_0`, then the date-0 deficit
`G_0 − T̄ − rB^G_0` equals `G_0 − G̃`: the government borrows exactly when spending is above its
permanent level. -/
theorem deficit_eq_spending_gap {r Tbar G0 Gtilde BG0 : ℝ}
    (hT : Tbar = Gtilde - r * BG0) : G0 - Tbar - r * BG0 = G0 - Gtilde := by
  rw [hT]; ring

/-- **No deficits with constant spending**, Exercise 6: with constant spending `Ḡ` and the smooth
tax `T̄ = Ḡ − rB^G_0`, government assets obey `B_{t+1} = (1 + r)B_t + T̄ − Ḡ` and stay constant
at `B^G_0`. -/
theorem government_assets_constant {r Gbar BG0 : ℝ} {B : ℕ → ℝ} (h0 : B 0 = BG0)
    (hflow : ∀ t, B (t + 1) = (1 + r) * B t + (Gbar - r * BG0) - Gbar) (t : ℕ) :
    B t = BG0 := by
  induction t with
  | zero => exact h0
  | succ t ih => rw [hflow t, ih]; ring

end ObstfeldRogoff.LifeCycleFiscalPolicy.TaxSmoothing
