/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Cobb–Douglas production in intensive form

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*,
§7.1, pp. 430–432. With constant returns, `Y = K^α L^{1−α}` is `L f(k)` for the
intensive form `f(k) = k^α` and capital per worker `k = K/L`.
-/

namespace ObstfeldRogoff.GlobalGrowth

/-- Cobb–Douglas output per worker `f(k) = k^α` (O&R §7.1). -/
noncomputable def cobbDouglas (α k : ℝ) : ℝ := k ^ α

/-- Output per worker is positive at positive capital. -/
theorem cobbDouglas_pos (α : ℝ) {k : ℝ} (hk : 0 < k) : 0 < cobbDouglas α k :=
  Real.rpow_pos_of_pos hk α

/-- **Constant returns in intensive form** (O&R §7.1): `L f(K/L) = K^α L^{1−α}`. -/
theorem cobbDouglas_intensive (α : ℝ) {K L : ℝ} (hK : 0 < K) (hL : 0 < L) :
    L * cobbDouglas α (K / L) = K ^ α * L ^ (1 - α) := by
  unfold cobbDouglas
  rw [Real.div_rpow hK.le hL.le, Real.rpow_sub hL, Real.rpow_one]
  field_simp

end ObstfeldRogoff.GlobalGrowth
