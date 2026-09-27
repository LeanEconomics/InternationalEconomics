/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import IntertemporalTrade.Model
import IntertemporalTrade.Consumer

/-!
# The current account in the two-period economy

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*,
§1.1.2–1.1.6, pp. 5–12.

* GNP, GDP and the current account `CA_t = Y_t + r B_t − C_t` (O&R (1.6), pp. 6–7).
* Government consumption financed by lump-sum taxes: the budget (1.8) and
  `CA_t = Y_t + r B_t − C_t − G_t` (p. 11); the two current accounts again sum
  to zero.
* With flat consumption (`β(1 + r) = 1`), `CA₁ = [(Y₁ − G₁) − (Y₂ − G₂)]/(2 + r)`.
  So a permanent output change leaves the current account unchanged, a temporary
  rise in `Y₁` raises it, and a rise in `Y₂` lowers it (p. 11). A temporary rise in
  government spending produces a deficit `CA₁ = −G₁/(2 + r)` (p. 12).
-/

namespace ObstfeldRogoff.IntertemporalTrade.CurrentAccount

/-- GNP exceeds GDP by net factor income from abroad: `(Y + r B) − Y = r B` (O&R p. 6). -/
theorem gnp_sub_gdp (Y r B : ℝ) : (Y + r * B) - Y = r * B := by ring

/-- The date-2 current account is the negative of the date-1 current account (O&R p. 7). -/
theorem ca2_eq_neg_ca1 (e : Economy) {C1 C2 : ℝ} (hb : e.Budget C1 C2) :
    e.ca2 C1 C2 = -e.ca1 C1 := by
  linarith [e.ca1_add_ca2 hb]

/-- The date-1 current account with government spending, `CA₁ = Y₁ − C₁ − G₁` (`B₁ = 0`). -/
def caG1 (Y1 C1 G1 : ℝ) : ℝ := Y1 - C1 - G1

/-- The date-2 current account with government spending, `CA₂ = Y₂ + r CA₁ − C₂ − G₂`. -/
def caG2 (r Y1 Y2 C1 C2 G1 G2 : ℝ) : ℝ := Y2 + r * caG1 Y1 C1 G1 - C2 - G2

/-- The private budget with lump-sum taxes O&R (1.8), p. 11, in multiplied-through form,
`C₂ = (Y₂ − G₂) + (1 + r)[(Y₁ − G₁) − C₁]`, is equivalent to (1.8). -/
theorem budgetG_iff {r Y1 Y2 C1 C2 G1 G2 : ℝ} (hr : 0 < 1 + r) :
    C1 + C2 / (1 + r) = Y1 - G1 + (Y2 - G2) / (1 + r) ↔
      C2 = (Y2 - G2) + (1 + r) * ((Y1 - G1) - C1) := by
  have h := hr.ne'
  constructor
  · intro hb
    field_simp at hb
    linarith
  · intro hc
    rw [hc]
    field_simp
    ring

/-- With government spending the current accounts still sum to zero (O&R p. 11). -/
theorem caG1_add_caG2 {r Y1 Y2 C1 C2 G1 G2 : ℝ}
    (hb : C2 = (Y2 - G2) + (1 + r) * ((Y1 - G1) - C1)) :
    caG1 Y1 C1 G1 + caG2 r Y1 Y2 C1 C2 G1 G2 = 0 := by
  unfold caG2 caG1
  rw [hb]
  ring

/-- **Flat consumption and the current account** (O&R p. 11–12): if consumption is flat,
`CA₁ = [(Y₁ − G₁) − (Y₂ − G₂)]/(2 + r)`. -/
theorem caG1_of_flat {r Y1 Y2 C G1 G2 : ℝ} (hr : 0 < 1 + r)
    (hb : C = (Y2 - G2) + (1 + r) * ((Y1 - G1) - C)) :
    caG1 Y1 C G1 = ((Y1 - G1) - (Y2 - G2)) / (2 + r) := by
  have h2r : (2 + r) ≠ 0 := by linarith
  unfold caG1
  field_simp
  linarith

/-- The flat consumption level with government spending,
`C̄ = [(1 + r)(Y₁ − G₁) + (Y₂ − G₂)]/(2 + r)`. -/
theorem flat_level_G {r Y1 Y2 C G1 G2 : ℝ} (hr : 0 < 1 + r)
    (hb : C = (Y2 - G2) + (1 + r) * ((Y1 - G1) - C)) :
    C = ((1 + r) * (Y1 - G1) + (Y2 - G2)) / (2 + r) := by
  have h2r : (2 + r) ≠ 0 := by linarith
  field_simp
  linarith

/-- The flat-consumption current account as a function of the output path:
`CA₁(Y₁, Y₂) = (Y₁ − Y₂)/(2 + r)` (O&R p. 11). -/
noncomputable def flatCA1 (r Y1 Y2 : ℝ) : ℝ := (Y1 - Y2) / (2 + r)

/-- **A permanent output change leaves the current account unchanged** (O&R p. 11). -/
theorem flatCA1_permanent (r Y1 Y2 d : ℝ) : flatCA1 r (Y1 + d) (Y2 + d) = flatCA1 r Y1 Y2 := by
  unfold flatCA1
  ring_nf

/-- **A temporary rise in output raises the current account** (O&R p. 11). -/
theorem flatCA1_strictMono_Y1 {r Y2 : ℝ} (hr : 0 < 1 + r) :
    StrictMono fun Y1 => flatCA1 r Y1 Y2 := fun a b hab => by
  unfold flatCA1
  exact div_lt_div_of_pos_right (by linarith) (by linarith)

/-- **An anticipated rise in future output lowers the current account** (O&R p. 11). -/
theorem flatCA1_strictAnti_Y2 {r Y1 : ℝ} (hr : 0 < 1 + r) :
    StrictAnti fun Y2 => flatCA1 r Y1 Y2 := fun a b hab => by
  unfold flatCA1
  exact div_lt_div_of_pos_right (by linarith) (by linarith)

/-- **The optimal current account under `β(1 + r) = 1`** (O&R p. 11): combining the Euler
equation with the budget, `CA₁ = (Y₁ − Y₂)/(2 + r)`. -/
theorem ca1_of_optimal (h : Consumer.Household) {u' : ℝ → ℝ}
    (hu : ∀ c, 0 < c → HasDerivAt h.u (u' c) c) {r c1 c2 : ℝ} (hr : 0 < 1 + r)
    (hβr : h.β * (1 + r) = 1) (ho : h.IsOptimal r c1 c2) :
    h.Y1 - c1 = flatCA1 r h.Y1 h.Y2 := by
  have hflat := h.flat_of_beta_mul_eq_one hu hβr ho
  have hb := h.optimal_binds ho
  rw [← hflat] at hb
  have := caG1_of_flat (G1 := 0) (G2 := 0) hr (by simpa using hb)
  simpa [caG1, flatCA1] using this

/-- **Temporary government spending** (O&R p. 12): with `Y₁ = Y₂ = Ȳ`, `G₁ > 0` and `G₂ = 0`,
flat consumption is `C̄ = Ȳ − (1 + r) G₁/(2 + r)` and the current account is in deficit,
`CA₁ = −G₁/(2 + r) < 0`. -/
theorem temporary_government_deficit {r Y G1 C : ℝ} (hr : 0 < 1 + r) (hG : 0 < G1)
    (hb : C = (Y - 0) + (1 + r) * ((Y - G1) - C)) :
    C = Y - (1 + r) * G1 / (2 + r) ∧ caG1 Y C G1 = -G1 / (2 + r) ∧ caG1 Y C G1 < 0 := by
  have h2r : (0 : ℝ) < 2 + r := by linarith
  have hca := caG1_of_flat hr hb
  have hC := flat_level_G hr hb
  refine ⟨?_, ?_, ?_⟩
  · rw [hC]
    field_simp
    ring
  · rw [hca]
    ring
  · rw [hca]
    exact div_neg_of_neg_of_pos (by linarith) h2r

/-- **Permanent government spending** (O&R p. 12): with `Y₁ = Y₂` and `G₁ = G₂`, flat
consumption leaves the current account balanced. -/
theorem permanent_government_balanced {r Y G C : ℝ} (hr : 0 < 1 + r)
    (hb : C = (Y - G) + (1 + r) * ((Y - G) - C)) : caG1 Y C G = 0 := by
  rw [caG1_of_flat hr hb]
  simp

end ObstfeldRogoff.IntertemporalTrade.CurrentAccount
