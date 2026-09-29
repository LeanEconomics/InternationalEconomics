/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# CES demand for a differentiated good

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*,
§10.1.1, pp. 661–663. With elasticity of substitution `θ`, demand for a good priced
`p` relative to the price index `P` is `y = (p/P)^{−θ} C`.
-/

namespace ObstfeldRogoff.StickyPriceModels

/-- CES demand `(p/P)^{−θ} C` for a differentiated good (O&R (10.x), §10.1.1). -/
noncomputable def cesDemand (θ p P C : ℝ) : ℝ := (p / P) ^ (-θ) * C

/-- At the price index, demand equals aggregate consumption (O&R §10.1.1). -/
theorem cesDemand_at_index (θ : ℝ) {P : ℝ} (hP : P ≠ 0) (C : ℝ) :
    cesDemand θ P P C = C := by
  simp [cesDemand, div_self hP]

/-- Demand is positive for positive prices and consumption (O&R §10.1.1). -/
theorem cesDemand_pos (θ : ℝ) {p P C : ℝ} (hp : 0 < p) (hP : 0 < P) (hC : 0 < C) :
    0 < cesDemand θ p P C :=
  mul_pos (Real.rpow_pos_of_pos (div_pos hp hP) _) hC

end ObstfeldRogoff.StickyPriceModels
