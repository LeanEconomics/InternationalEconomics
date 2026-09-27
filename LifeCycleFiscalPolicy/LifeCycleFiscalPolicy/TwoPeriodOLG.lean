/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import LifeCycleFiscalPolicy.Model
import Mathlib.Algebra.BigOperators.Field

/-!
# Government deficits in a two-period overlapping generations economy

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*,
§3.2.1–§3.2.2, pp. 133–137, and Box 3.1 (generational accounting), pp. 142–144.
Each generation lives two periods with log utility (O&R (3.9)) and faces the
world rate `r`. It pays lump-sum taxes `τ^Y` when young and `τ^O` when old, so
its lifetime wealth is `W = y^Y − τ^Y + (y^O − τ^O)/(1 + r)` (O&R (3.10)). The
consumption demands (3.12)–(3.13) are `LogOLG.youngC` and `LogOLG.oldC`.

* **Ricardian equivalence fails** (p. 136). In a steady state, aggregate
  consumption is `C = [1 + (1 + r)β]/(1 + β) · W`. After substituting the
  government's steady-state budget `G = rB^G + τ^Y + τ^O`, `C` still depends on
  the tax on the young and on government assets, not only on `G`.
* **Saving accounting** (3.17)–(3.23): the current account is private plus
  government saving; the old dissave what they saved when young; with
  `β(1 + r) = 1` the young save `β/(1 + β)` times the fall in their disposable
  income.
* **Generational accounting** (Box 3.1): cutting a generation's youth tax by one
  unit and raising its old-age tax by `1 + r` raises the measured deficit but
  leaves every generation's lifetime wealth, and hence all consumption,
  unchanged.
-/

namespace ObstfeldRogoff.LifeCycleFiscalPolicy.TwoPeriodOLG

open LogOLG

/-- Lifetime wealth `W = y^Y − τ^Y + (y^O − τ^O)/(1 + r)` of a generation, O&R (3.10), p. 134. -/
noncomputable def lifetimeWealth (r yY yO τY τO : ℝ) : ℝ := yY - τY + (yO - τO) / (1 + r)

/-- **Steady-state aggregate consumption**, O&R p. 135: with constant endowments and taxes, the
young and old alive at any date consume `C = [1 + (1 + r)β]/(1 + β) · W`. -/
theorem aggregate_consumption_steady (m : LogOLG) (W : ℝ) :
    m.youngC W + m.oldC W = (1 + (1 + m.r) * m.β) / (1 + m.β) * W := by
  unfold youngC oldC
  ring

/-- **Steady-state consumption after the government budget**, O&R p. 136: using
`G = rB^G + τ^Y + τ^O` to eliminate `τ^O`,
`C = [1 + (1 + r)β]/(1 + β) · (y^Y + (y^O − G − rτ^Y + rB^G)/(1 + r))`. -/
theorem aggregate_consumption_government (m : LogOLG) {yY yO τY τO G BG : ℝ}
    (hG : G = m.r * BG + τY + τO) :
    m.youngC (lifetimeWealth m.r yY yO τY τO) + m.oldC (lifetimeWealth m.r yY yO τY τO) =
      (1 + (1 + m.r) * m.β) / (1 + m.β) *
        (yY + (yO - G - m.r * τY + m.r * BG) / (1 + m.r)) := by
  have hr := m.one_add_r_pos.ne'
  have hb : 1 + m.β ≠ 0 := by linarith [m.β_pos]
  rw [aggregate_consumption_steady]
  unfold lifetimeWealth
  rw [hG]
  field_simp
  ring

/-- **Ricardian equivalence fails in the OLG model** (O&R p. 136): holding government spending
and government assets fixed, a different split of taxes between young and old changes aggregate
consumption whenever `r ≠ 0`. -/
theorem consumption_depends_on_youth_tax (m : LogOLG) (hr0 : m.r ≠ 0) {yY yO G BG τY τY' : ℝ}
    (hτ : τY ≠ τY') :
    (1 + (1 + m.r) * m.β) / (1 + m.β) * (yY + (yO - G - m.r * τY + m.r * BG) / (1 + m.r)) ≠
      (1 + (1 + m.r) * m.β) / (1 + m.β) *
        (yY + (yO - G - m.r * τY' + m.r * BG) / (1 + m.r)) := by
  have hr := m.one_add_r_pos
  have hb := m.β_pos
  have hk : 0 < (1 + (1 + m.r) * m.β) / (1 + m.β) := by positivity
  intro heq
  have h1 := mul_left_cancel₀ hk.ne' heq
  have h2 : (yO - G - m.r * τY + m.r * BG) / (1 + m.r) =
      (yO - G - m.r * τY' + m.r * BG) / (1 + m.r) := by linarith
  rw [div_left_inj' hr.ne'] at h2
  exact hτ (mul_left_cancel₀ hr0 (by linarith))

/-- **Government assets matter** (O&R p. 136): holding spending and the youth tax fixed, higher
government assets `B^G` raise steady-state consumption when `r > 0`. -/
theorem consumption_increasing_in_government_assets (m : LogOLG) (hr0 : 0 < m.r)
    {yY yO G τY BG BG' : ℝ} (hB : BG < BG') :
    (1 + (1 + m.r) * m.β) / (1 + m.β) * (yY + (yO - G - m.r * τY + m.r * BG) / (1 + m.r)) <
      (1 + (1 + m.r) * m.β) / (1 + m.β) *
        (yY + (yO - G - m.r * τY + m.r * BG') / (1 + m.r)) := by
  have hr := m.one_add_r_pos
  have hb := m.β_pos
  have hk : 0 < (1 + (1 + m.r) * m.β) / (1 + m.β) := by positivity
  apply mul_lt_mul_of_pos_left _ hk
  have : (yO - G - m.r * τY + m.r * BG) / (1 + m.r) <
      (yO - G - m.r * τY + m.r * BG') / (1 + m.r) :=
    div_lt_div_of_pos_right (by nlinarith) hr
  linarith

/-! ### Saving and the current account (O&R §3.2.2) -/

/-- **The current account is private plus government saving**, O&R (3.17), p. 136: with
`B = B^P + B^G`, `CA_t = B_{t+1} − B_t = (B^P_{t+1} − B^P_t) + (B^G_{t+1} − B^G_t)`. -/
theorem current_account_split (BP BP' BG BG' : ℝ) :
    (BP' + BG') - (BP + BG) = (BP' - BP) + (BG' - BG) := by ring

/-- **The old dissave their youthful saving**, O&R (3.19), p. 137 and footnote 6: the old's saving
is interest on last period's saving plus disposable income less consumption; their budget
`y^O − τ^O − c^O = −(1 + r) S^Y_{t−1}` makes it `S^O_t = −S^Y_{t−1}`. -/
theorem old_saving {r SY yO τO cO : ℝ} (hbudget : yO - τO - cO = -(1 + r) * SY) :
    r * SY + yO - τO - cO = -SY := by linarith

/-- **Total private saving**, O&R (3.20)–(3.21), p. 137:
`S^P_t = S^Y_t + S^O_t = S^Y_t − S^Y_{t−1}`, the change in private assets `B^P_{t+1} − B^P_t`,
since `S^Y_t = B^P_{t+1}` (3.18). -/
theorem private_saving {SYprev SY SO : ℝ} (hSO : SO = -SYprev) : SY + SO = SY - SYprev := by
  rw [hSO]; ring

/-- **Saving by the young with flat consumption**, O&R (3.22), p. 137: if `β(1 + r) = 1`,
`S^Y = y^Y − τ^Y − c^Y = β/(1 + β) · [(y^Y − τ^Y) − (y^O − τ^O)]`. -/
theorem young_saving_flat (m : LogOLG) (hβr : m.β * (1 + m.r) = 1) (yY yO τY τO : ℝ) :
    yY - τY - m.youngC (lifetimeWealth m.r yY yO τY τO) =
      m.β / (1 + m.β) * ((yY - τY) - (yO - τO)) := by
  have hr := m.one_add_r_pos.ne'
  have hb : 1 + m.β ≠ 0 := by linarith [m.β_pos]
  have hinv : 1 / (1 + m.r) = m.β := by field_simp; linarith
  unfold youngC lifetimeWealth
  rw [div_eq_mul_one_div (yO - τO), hinv]
  field_simp
  ring

/-- **Aggregate private saving with flat consumption**, O&R (3.23), p. 137:
`S^P_t = β/(1 + β) · [Δ(y^Y − τ^Y) − Δ(y^O_{t+1} − τ^O_{t+1})]`, the difference of (3.22) at two
dates. -/
theorem private_saving_flat (β a a' b b' : ℝ) :
    β / (1 + β) * (a' - b') - β / (1 + β) * (a - b) = β / (1 + β) * ((a' - a) - (b' - b)) := by
  ring

/-- **Generational accounting**, O&R Box 3.1, pp. 142–144: cutting a generation's youth tax by one
unit and raising its old-age tax by `1 + r` leaves its lifetime wealth unchanged. -/
theorem generational_account_invariant {r : ℝ} (hr : 0 < 1 + r) (yY yO τY τO : ℝ) :
    lifetimeWealth r yY yO (τY - 1) (τO + (1 + r)) = lifetimeWealth r yY yO τY τO := by
  unfold lifetimeWealth
  field_simp
  ring

/-- Hence the swap leaves both consumption levels of that generation unchanged (Box 3.1), even
though it raises the government deficit in the generation's youth by one unit. -/
theorem generational_account_consumption (m : LogOLG) (yY yO τY τO : ℝ) :
    m.youngC (lifetimeWealth m.r yY yO (τY - 1) (τO + (1 + m.r))) =
        m.youngC (lifetimeWealth m.r yY yO τY τO) ∧
      m.oldC (lifetimeWealth m.r yY yO (τY - 1) (τO + (1 + m.r))) =
        m.oldC (lifetimeWealth m.r yY yO τY τO) := by
  rw [generational_account_invariant m.one_add_r_pos]
  exact ⟨rfl, rfl⟩

/-- **The government's accounts regroup by generation**, O&R Box 3.1: the present value of taxes
over dates equals the tax of the current old plus the present value, over generations, of each
generation's lifetime tax `τ^Y_s + τ^O_{s+1}/(1 + r)`, over any finite horizon. -/
theorem taxes_by_generation (r : ℝ) (τY τO : ℕ → ℝ) (T : ℕ) :
    ∑ s ∈ Finset.range (T + 1), ((1 + r)⁻¹) ^ s * (τY s + τO s) =
      τO 0 + ∑ s ∈ Finset.range T, ((1 + r)⁻¹) ^ s * (τY s + τO (s + 1) / (1 + r)) +
        ((1 + r)⁻¹) ^ T * τY T := by
  induction T with
  | zero => simp; ring
  | succ T ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    simp only [div_eq_mul_inv, pow_succ]
    ring

end ObstfeldRogoff.LifeCycleFiscalPolicy.TwoPeriodOLG
