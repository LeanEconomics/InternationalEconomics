/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# The Barro–Gordon loss function

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*,
§9.5, pp. 634–637. The policymaker's loss is `L = (y − k ȳ)² + χ π²` with target
output above the natural rate (`k > 1`).
-/

namespace ObstfeldRogoff.NominalRigidities

/-- The quadratic loss `(y − ky)² + χπ²` (O&R (9.5x), §9.5). -/
def loss (χ k ybar y π : ℝ) : ℝ := (y - k * ybar) ^ 2 + χ * π ^ 2

/-- The loss is nonnegative when `χ ≥ 0`. -/
theorem loss_nonneg {χ : ℝ} (hχ : 0 ≤ χ) (k ybar y π : ℝ) : 0 ≤ loss χ k ybar y π := by
  unfold loss
  have := sq_nonneg (y - k * ybar)
  have := mul_nonneg hχ (sq_nonneg π)
  linarith

/-- Zero inflation at target output gives zero loss (O&R §9.5). -/
theorem loss_at_target (χ k ybar : ℝ) : loss χ k ybar (k * ybar) 0 = 0 := by
  unfold loss
  ring

end ObstfeldRogoff.NominalRigidities
