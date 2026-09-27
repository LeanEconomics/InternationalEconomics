import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
set_option autoImplicit false

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The two-period overlapping generations endowment economy

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*,
§3.2.1, pp. 133–135. Each generation lives for two periods, has utility
`log c^Y_t + β log c^O_{t+1}` (O&R (3.9)), and faces the world rate `r`.
With lifetime wealth `W = y^Y − τ^Y + (y^O − τ^O)/(1 + r)` (O&R (3.10)), the
consumption demands are `c^Y = W/(1 + β)` and `c^O = (1 + r) β W/(1 + β)`
(O&R (3.12)–(3.13)).
-/

namespace ObstfeldRogoff.LifeCycleFiscalPolicy

/-- A small open two-period OLG economy with log utility and world rate `r > -1`. -/
structure LogOLG where
  β : ℝ
  r : ℝ
  β_pos : 0 < β
  one_add_r_pos : 0 < 1 + r

namespace LogOLG

/-- Consumption of the young out of lifetime wealth `W` (O&R (3.12)). -/
noncomputable def youngC (m : LogOLG) (W : ℝ) : ℝ := W / (1 + m.β)

/-- Consumption of the old out of lifetime wealth `W` (O&R (3.13)). -/
noncomputable def oldC (m : LogOLG) (W : ℝ) : ℝ := (1 + m.r) * m.β * W / (1 + m.β)

/-- The demands exhaust lifetime wealth: `c^Y + c^O/(1 + r) = W` (O&R (3.10)). -/
theorem budget (m : LogOLG) (W : ℝ) : m.youngC W + m.oldC W / (1 + m.r) = W := by
  have hr := m.one_add_r_pos.ne'
  have hb : 1 + m.β ≠ 0 := by linarith [m.β_pos]
  unfold youngC oldC
  field_simp

/-- The demands satisfy the Euler equation `c^O_{t+1} = (1 + r) β c^Y_t` (O&R (3.11)). -/
theorem euler (m : LogOLG) (W : ℝ) : m.oldC W = (1 + m.r) * m.β * m.youngC W := by
  unfold youngC oldC
  ring

end LogOLG

end ObstfeldRogoff.LifeCycleFiscalPolicy

set_option linter.style.longLine false
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.LogOLG
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.LogOLG.mk
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.LogOLG.β
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.LogOLG.r
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.LogOLG.β_pos
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.LogOLG.one_add_r_pos
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.LogOLG.youngC
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.LogOLG.oldC
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.LogOLG.budget
#print axioms ObstfeldRogoff.LifeCycleFiscalPolicy.LogOLG.euler
