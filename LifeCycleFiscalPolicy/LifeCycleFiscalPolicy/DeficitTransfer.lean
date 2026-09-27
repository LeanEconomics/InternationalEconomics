/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LifeCycleFiscalPolicy.Model

/-!
# The timing of taxes: a debt-financed transfer

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*,
§3.2.3, pp. 137–141, footnotes 9–10, and the transitory output shock of §3.3.1,
p. 148.

Preferences are homothetic: a generation with lifetime wealth `W` consumes
`(1 − s)W` when young and `(1 + r)sW` when old. With log utility,
`s = β/(1 + β)` (O&R (3.12)–(3.13)); O&R footnote 9 notes that the results hold
for any homothetic utility, and all statements below are for a general
`0 < s < 1`. Because demands are linear in wealth, consumption changes are the
share times the change in wealth.

At date 0 the government cuts the taxes of the young and old by `d/2` each,
sells bonds `d` to the young, and forever after levies the interest `rd/2` on
each generation's young and old; the principal is never repaid.
* The date-0 old consume their windfall: `Δc^O_0 = d/2` (3.24).
* The date-0 young gain `d/2` now and pay `rd/2` later: their wealth rises by
  `d/(2(1 + r))`, so `Δc^Y_0 = (1 − s)d/(2(1 + r))` (3.25).
* Date-0 consumption rises by `[1 + (1 − s)/(1 + r)]d/2 < d` (3.26).
* Every later generation loses `(2r + r²)/(1 + r) · d/2` of wealth, so its
  consumption falls in both periods (3.28)–(3.29).
* Date-1 consumption changes by `[s − (1 − s)(2r + r²)/(1 + r)]d/2`, whose sign is
  ambiguous (3.30) and footnote 9. From date 2 on it falls; in the flat case
  `β(1 + r) = 1` it falls by exactly `rd` (footnote 10).
* The current account worsens at date 0 by the consumption rise (3.31) and at
  date 1 by `s(1 + r)d/2` (3.32), then returns to its original path.
-/

namespace ObstfeldRogoff.LifeCycleFiscalPolicy.DeficitTransfer

/-- The wealth change of the date-0 young: `d/2` now, `−rd/2` when old (O&R p. 138). -/
noncomputable def youngWealthChange (r d : ℝ) : ℝ := d / 2 - r * (d / 2) / (1 + r)

/-- The wealth change of every generation born at date 1 or later: `−rd/2` in each period of life
(O&R p. 139). -/
noncomputable def laterWealthChange (r d : ℝ) : ℝ := -(r * (d / 2)) - r * (d / 2) / (1 + r)

theorem youngWealthChange_eq {r : ℝ} (hr : 0 < 1 + r) (d : ℝ) :
    youngWealthChange r d = d / (2 * (1 + r)) := by
  unfold youngWealthChange
  field_simp
  ring

/-- **Later generations lose** `(2r + r²)/(1 + r) · d/2`, O&R p. 139. -/
theorem laterWealthChange_eq {r : ℝ} (hr : 0 < 1 + r) (d : ℝ) :
    laterWealthChange r d = -((2 * r + r ^ 2) / (1 + r) * (d / 2)) := by
  unfold laterWealthChange
  field_simp
  ring

/-- **Consumption of the date-0 young**, O&R (3.25), p. 138: `Δc^Y_0 = (1 − s)/(1 + r) · d/2`. -/
theorem young0_consumption_change {r : ℝ} (hr : 0 < 1 + r) (s d : ℝ) :
    (1 - s) * youngWealthChange r d = (1 - s) / (1 + r) * (d / 2) := by
  rw [youngWealthChange_eq hr]
  field_simp

/-- **Date-0 aggregate consumption**, O&R (3.26), p. 139: the old's windfall `d/2` (3.24) plus the
young's response gives `ΔC₀ = [1 + (1 − s)/(1 + r)] d/2`. -/
theorem consumption0_change {r : ℝ} (hr : 0 < 1 + r) (s d : ℝ) :
    d / 2 + (1 - s) * youngWealthChange r d = (1 + (1 - s) / (1 + r)) * (d / 2) := by
  rw [young0_consumption_change hr]
  ring

/-- **Date-0 consumption rises by less than the transfer**, O&R p. 139: `0 < ΔC₀ < d` for `d > 0`,
`0 < s < 1` and `r > 0`. -/
theorem consumption0_change_lt {r s d : ℝ} (hr : 0 < r) (hs0 : 0 < s) (hs1 : s < 1) (hd : 0 < d) :
    0 < (1 + (1 - s) / (1 + r)) * (d / 2) ∧ (1 + (1 - s) / (1 + r)) * (d / 2) < d := by
  have h1 : 0 < (1 - s) / (1 + r) := div_pos (by linarith) (by linarith)
  have h2 : (1 - s) / (1 + r) < 1 := (div_lt_one (by linarith)).2 (by linarith)
  constructor <;> nlinarith

/-- **The date-1 old**, O&R (3.27), p. 139: `Δc^O_1 = (1 + r)s · Δw = s d/2`. -/
theorem old1_consumption_change {r : ℝ} (hr : 0 < 1 + r) (s d : ℝ) :
    (1 + r) * s * youngWealthChange r d = s * (d / 2) := by
  rw [youngWealthChange_eq hr]
  field_simp

/-- **Later young**, O&R (3.28), p. 139: `Δc^Y_t = −(1 − s)(2r + r²)/(1 + r) · d/2` for `t ≥ 1`. -/
theorem later_young_consumption_change {r : ℝ} (hr : 0 < 1 + r) (s d : ℝ) :
    (1 - s) * laterWealthChange r d = -((1 - s) * ((2 * r + r ^ 2) / (1 + r)) * (d / 2)) := by
  rw [laterWealthChange_eq hr]
  ring

/-- **Later old**, O&R (3.29), p. 139: `Δc^O_t = −s(2r + r²) · d/2` for `t ≥ 2`. -/
theorem later_old_consumption_change {r : ℝ} (hr : 0 < 1 + r) (s d : ℝ) :
    (1 + r) * s * laterWealthChange r d = -(s * (2 * r + r ^ 2) * (d / 2)) := by
  rw [laterWealthChange_eq hr]
  field_simp

/-- **Date-1 aggregate consumption**, O&R (3.30), p. 139:
`ΔC₁ = [s − (1 − s)(2r + r²)/(1 + r)] d/2`. -/
theorem consumption1_change {r : ℝ} (hr : 0 < 1 + r) (s d : ℝ) :
    (1 + r) * s * youngWealthChange r d + (1 - s) * laterWealthChange r d =
      (s - (1 - s) * (2 * r + r ^ 2) / (1 + r)) * (d / 2) := by
  rw [old1_consumption_change hr, later_young_consumption_change hr]
  ring

/-- **The sign of the date-1 change**, O&R footnote 9, p. 139: for `d > 0` and `0 < s < 1`, date-1
consumption rises iff `s/(1 − s) > (2r + r²)/(1 + r)`. -/
theorem consumption1_rises_iff {r s d : ℝ} (hr : 0 < 1 + r) (hs1 : s < 1) (hd : 0 < d) :
    0 < (s - (1 - s) * (2 * r + r ^ 2) / (1 + r)) * (d / 2) ↔
      (2 * r + r ^ 2) / (1 + r) < s / (1 - s) := by
  have h1s : 0 < 1 - s := by linarith
  rw [mul_pos_iff_of_pos_right (by linarith : (0 : ℝ) < d / 2), sub_pos, div_lt_div_iff₀ hr h1s,
    div_lt_iff₀ hr]
  constructor <;> intro h <;> nlinarith

/-- **The sign really is ambiguous** (O&R p. 139): with log utility and `β = 1`, date-1 consumption
rises at `r = 1/10` and falls at `r = 1`. -/
theorem consumption1_sign_ambiguous :
    0 < ((1 : ℝ) / 2 - (1 - 1 / 2) * (2 * (1 / 10) + (1 / 10) ^ 2) / (1 + 1 / 10)) ∧
      ((1 : ℝ) / 2 - (1 - 1 / 2) * (2 * 1 + 1 ^ 2) / (1 + 1)) < 0 := by
  norm_num

/-- **Consumption falls from date 2 on**, O&R p. 139: `ΔC_t = Δc^Y_t + Δc^O_t < 0` for `t ≥ 2` when
`r > 0`, `d > 0` and `0 < s < 1`. -/
theorem consumption_later_falls {r s d : ℝ} (hr : 0 < r) (hs0 : 0 < s) (hs1 : s < 1)
    (hd : 0 < d) :
    (1 - s) * laterWealthChange r d + (1 + r) * s * laterWealthChange r d < 0 := by
  rw [later_young_consumption_change (by linarith), later_old_consumption_change (by linarith)]
  have h1 : 0 < (1 - s) * ((2 * r + r ^ 2) / (1 + r)) * (d / 2) := by
    have : 0 < (2 * r + r ^ 2) / (1 + r) := div_pos (by nlinarith) (by linarith)
    positivity
  have h2 : 0 < s * (2 * r + r ^ 2) * (d / 2) := by
    have : 0 < 2 * r + r ^ 2 := by nlinarith
    positivity
  linarith

/-- **The long-run consumption fall**, O&R footnote 10, p. 139–140: from date 2 on, aggregate
consumption falls by `(1 + sr)(2r + r²)/(1 + r) · d/2`. With log utility (`s = β/(1 + β)`) this is
the book's `(1 + βr/(1 + β))(2r + r²)/(1 + r) · d/2`. -/
theorem consumption_later_change {r : ℝ} (hr : 0 < 1 + r) (s d : ℝ) :
    (1 - s) * laterWealthChange r d + (1 + r) * s * laterWealthChange r d =
      -((1 + s * r) * ((2 * r + r ^ 2) / (1 + r)) * (d / 2)) := by
  rw [later_young_consumption_change hr, later_old_consumption_change hr]
  field_simp
  ring

/-- **Flat consumption: the fall is exactly `rd`**, O&R footnote 10: with log utility and
`β(1 + r) = 1`, `s = β/(1 + β) = 1/(2 + r)` and the long-run fall is `rd`. -/
theorem consumption_later_change_flat {r : ℝ} (hr : 0 < 1 + r) (d : ℝ) :
    -((1 + 1 / (2 + r) * r) * ((2 * r + r ^ 2) / (1 + r)) * (d / 2)) = -(r * d) := by
  have h2 : (2 : ℝ) + r ≠ 0 := by linarith
  have h1 := hr.ne'
  field_simp
  ring

/-- With log utility and `β(1 + r) = 1`, the saving share `β/(1 + β)` equals `1/(2 + r)`. -/
theorem share_of_flat {β r : ℝ} (hr : 0 < 1 + r) (hβr : β * (1 + r) = 1) :
    β / (1 + β) = 1 / (2 + r) := by
  have hβ : β = 1 / (1 + r) := by field_simp; linarith
  rw [hβ]
  have h1 := hr.ne'
  have h2 : (2 : ℝ) + r ≠ 0 := by linarith
  field_simp
  ring

/-! ### The current account (O&R (3.31)–(3.32)) -/

/-- **Date-1 current account**, O&R (3.32), p. 140: the date-1 change is the interest on the date-0
change less the date-1 consumption change, `ΔCA₁ = rΔCA₀ − ΔC₁ = −s(1 + r)d/2`. -/
theorem current_account1_change {r : ℝ} (hr : 0 < 1 + r) (s d : ℝ) :
    r * (-((1 + (1 - s) / (1 + r)) * (d / 2))) -
        (s - (1 - s) * (2 * r + r ^ 2) / (1 + r)) * (d / 2) =
      -(s * (1 + r) * (d / 2)) := by
  field_simp
  ring

/-- **The current account returns to its path from date 2**, O&R p. 140: interest on the
accumulated foreign debt exactly matches the permanent consumption fall, so `ΔCA_t = 0` for
`t ≥ 2`: `r(ΔCA₀ + ΔCA₁) = ΔC_t`. -/
theorem current_account_later_zero {r : ℝ} (hr : 0 < 1 + r) (s d : ℝ) :
    r * (-((1 + (1 - s) / (1 + r)) * (d / 2)) + -(s * (1 + r) * (d / 2))) -
        (-((1 + s * r) * ((2 * r + r ^ 2) / (1 + r)) * (d / 2))) = 0 := by
  field_simp
  ring

/-! ### Transfers without deficits and transitory shocks -/

/-- **A tax-financed transfer from young to old**, O&R p. 141: a transfer `δ` raises the old's
consumption by `δ` and lowers the young's by `(1 − s)δ`, so aggregate consumption rises by
`sδ > 0` and the current account worsens with a balanced budget. -/
theorem balanced_transfer_consumption {s δ : ℝ} (hs0 : 0 < s) (hδ : 0 < δ) :
    δ + (1 - s) * (-δ) = s * δ ∧ 0 < s * δ :=
  ⟨by ring, mul_pos hs0 hδ⟩

/-- **A transitory output shock**, O&R §3.3.1, p. 148: output rises by `dy` for both generations
at date 0 only. The old consume theirs, the young consume `(1 − s)dy`, so `ΔCA₀ = s·dy`; at date
1 the old consume `(1 + r)s·dy` and `ΔCA₁ = r·s·dy − (1 + r)s·dy = −s·dy`. The two changes cancel,
so there is no long-run effect. -/
theorem transitory_shock_current_account (r s dy : ℝ) :
    2 * dy - (dy + (1 - s) * dy) = s * dy ∧
      r * (s * dy) - (1 + r) * s * dy = -(s * dy) ∧ s * dy + -(s * dy) = 0 := by
  refine ⟨by ring, by ring, by ring⟩

/-- With log utility the share is `s = β/(1 + β)`, so `1 − s = 1/(1 + β)`: the demands of O&R
(3.12)–(3.13) are the homothetic demands above. -/
theorem log_share (m : LogOLG) (W : ℝ) :
    m.youngC W = (1 - m.β / (1 + m.β)) * W ∧
      m.oldC W = (1 + m.r) * (m.β / (1 + m.β)) * W := by
  have hb : 1 + m.β ≠ 0 := by linarith [m.β_pos]
  unfold LogOLG.youngC LogOLG.oldC
  constructor
  · field_simp
    ring
  · field_simp

end ObstfeldRogoff.LifeCycleFiscalPolicy.DeficitTransfer
