/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Traded and nontraded goods: the consumer price index

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*,
§4.1, pp. 199–202. With Cobb–Douglas preferences over a traded and a nontraded
good, the consumer price index is `P = P_T^γ P_N^{1−γ}` for `0 < γ < 1`. With the
traded good as numeraire, `P = p^{1−γ}` where `p = P_N/P_T` is the relative price
of nontradables.
-/

namespace ObstfeldRogoff.RealExchangeRate

/-- Cobb–Douglas weights on traded and nontraded consumption, `0 < γ < 1`. -/
structure CobbDouglasIndex where
  γ : ℝ
  γ_pos : 0 < γ
  γ_lt_one : γ < 1

namespace CobbDouglasIndex

/-- The consumer price index `P = P_T^γ P_N^{1−γ}` (O&R §4.1). -/
noncomputable def price (c : CobbDouglasIndex) (PT PN : ℝ) : ℝ := PT ^ c.γ * PN ^ (1 - c.γ)

/-- The price index is homogeneous of degree one in nominal prices. -/
theorem price_homogeneous (c : CobbDouglasIndex) {PT PN t : ℝ} (hT : 0 ≤ PT) (hN : 0 ≤ PN)
    (ht : 0 ≤ t) : c.price (t * PT) (t * PN) = t * c.price PT PN := by
  unfold price
  rw [Real.mul_rpow ht hT, Real.mul_rpow ht hN]
  have : t ^ c.γ * t ^ (1 - c.γ) = t := by
    rw [← Real.rpow_add_of_nonneg ht c.γ_pos.le (by linarith [c.γ_lt_one]), add_sub_cancel,
      Real.rpow_one]
  calc t ^ c.γ * PT ^ c.γ * (t ^ (1 - c.γ) * PN ^ (1 - c.γ))
      = (t ^ c.γ * t ^ (1 - c.γ)) * (PT ^ c.γ * PN ^ (1 - c.γ)) := by ring
    _ = t * (PT ^ c.γ * PN ^ (1 - c.γ)) := by rw [this]

/-- With the traded good as numeraire, the price index is `p^{1−γ}` (O&R §4.1). -/
theorem price_numeraire (c : CobbDouglasIndex) (p : ℝ) : c.price 1 p = p ^ (1 - c.γ) := by
  simp [price]

end CobbDouglasIndex

end ObstfeldRogoff.RealExchangeRate
