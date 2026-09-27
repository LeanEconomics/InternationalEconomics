/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The two-period small open endowment economy

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*,
§1.1, pp. 1–7. A small open economy lives for two periods, takes the world
interest rate `r` as given, and starts and ends with zero net foreign assets
(`B₁ = B₃ = 0`, p. 7). The current account on date `t` is
`CA_t = Y_t + r B_t − C_t` (O&R (1.6), p. 6).
-/

namespace ObstfeldRogoff.IntertemporalTrade

/-- A two-period small open endowment economy facing the world rate `r > -1`. -/
structure Economy where
  r : ℝ
  Y1 : ℝ
  Y2 : ℝ
  one_add_r_pos : 0 < 1 + r

namespace Economy

/-- The intertemporal budget constraint O&R (1.2), p. 2. -/
def Budget (e : Economy) (C1 C2 : ℝ) : Prop :=
  C1 + C2 / (1 + e.r) = e.Y1 + e.Y2 / (1 + e.r)

/-- Date-1 current account with `B₁ = 0`: `CA₁ = Y₁ − C₁`. -/
def ca1 (e : Economy) (C1 : ℝ) : ℝ := e.Y1 - C1

/-- Date-2 current account, with `B₂ = CA₁`: `CA₂ = Y₂ + r B₂ − C₂`. -/
def ca2 (e : Economy) (C1 C2 : ℝ) : ℝ := e.Y2 + e.r * e.ca1 C1 - C2

/-- The budget line in slope form, `C₂ = Y₂ − (1 + r)(C₁ − Y₁)` (O&R p. 7). -/
theorem budget_iff (e : Economy) (C1 C2 : ℝ) :
    e.Budget C1 C2 ↔ C2 = e.Y2 - (1 + e.r) * (C1 - e.Y1) := by
  have h := e.one_add_r_pos.ne'
  unfold Budget
  constructor
  · intro hb
    field_simp at hb
    linarith
  · intro hc
    rw [hc]
    field_simp
    ring

/-- Over the two periods the current accounts sum to zero, `CA₁ + CA₂ = 0` (O&R p. 7). -/
theorem ca1_add_ca2 (e : Economy) {C1 C2 : ℝ} (hb : e.Budget C1 C2) :
    e.ca1 C1 + e.ca2 C1 C2 = 0 := by
  rw [budget_iff] at hb
  unfold ca2 ca1
  rw [hb]
  ring

end Economy

end ObstfeldRogoff.IntertemporalTrade
