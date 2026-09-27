import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
set_option autoImplicit false

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The small open economy with many periods

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*,
§2.1, pp. 60–61. A small open economy faces a constant world interest rate
`r > 0` (p. 66). Net foreign assets `B t` are predetermined at date `t`, and
the current account is `CA_t = B_{t+1} − B_t = Y_t + r B_t − C_t − G_t − I_t`
(O&R (2.2), p. 60).
-/

namespace ObstfeldRogoff.SmallOpenEconomyDynamics

/-- A small open economy facing the constant world rate `r > 0`. -/
structure Economy where
  r : ℝ
  r_pos : 0 < r

/-- Paths of net foreign assets, output, consumption, government spending and investment. -/
structure Paths where
  B : ℕ → ℝ
  Y : ℕ → ℝ
  C : ℕ → ℝ
  G : ℕ → ℝ
  I : ℕ → ℝ

namespace Economy

/-- The current account `CA_t = Y_t + r B_t − C_t − G_t − I_t` (O&R (2.2), p. 60). -/
def ca (e : Economy) (p : Paths) (t : ℕ) : ℝ :=
  p.Y t + e.r * p.B t - p.C t - p.G t - p.I t

/-- The period budget constraints: `B_{t+1} − B_t = CA_t` on every date. -/
def Flow (e : Economy) (p : Paths) : Prop :=
  ∀ t, p.B (t + 1) - p.B t = e.ca p t

/-- The period constraints in the form O&R (2.3), p. 60:
`(1 + r) B_t = C_t + G_t + I_t − Y_t + B_{t+1}`. -/
theorem flow_iff (e : Economy) (p : Paths) :
    e.Flow p ↔ ∀ t, (1 + e.r) * p.B t = p.C t + p.G t + p.I t - p.Y t + p.B (t + 1) := by
  unfold Flow ca
  constructor
  · intro h t
    linarith [h t]
  · intro h t
    linarith [h t]

end Economy

end ObstfeldRogoff.SmallOpenEconomyDynamics

set_option linter.style.longLine false
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.Economy
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.Economy.mk
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.Economy.r
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.Economy.r_pos
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.Paths
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.Paths.mk
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.Paths.B
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.Paths.Y
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.Paths.C
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.Paths.G
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.Paths.I
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.Economy.ca
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.Economy.Flow
#print axioms ObstfeldRogoff.SmallOpenEconomyDynamics.Economy.flow_iff
