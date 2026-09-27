/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import SmallOpenEconomyDynamics.PresentValue

/-!
# The fundamental current-account equation

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*,
§2.1.3 and §2.2, pp. 62–78. Date 0 stands for the book's date `t`. Net output
flows `Y, G, I` are sequences from date 0 on, `B₀` is initial net foreign
assets, and lifetime wealth is `W₀ = (1 + r)B₀ + PV(Y − G − I)` (O&R (2.19)).
The current account is `CA₀ = Y₀ + rB₀ − C₀ − G₀ − I₀` (O&R (2.2)).

* With flat consumption (`β(1 + r) = 1`), the intertemporal budget constraint
  pins down `C = rW₀/(1 + r)` (O&R (2.10), p. 62). The current account is then
  `CA = (Y − Ỹ) − (I − Ĩ) − (G − G̃)` (**O&R (2.18)**, p. 74), where `X̃` is the
  permanent value of O&R (2.17): output above its permanent level is saved,
  and investment or government spending above theirs is financed by borrowing.
* If consumption grows geometrically at gross rate `γ < 1 + r` (the isoelastic
  case, `γ = (1 + r)^σ β^σ`), then `C₀ = (r + ϑ)W₀/(1 + r)` with `ϑ = 1 − γ`
  (O&R (2.16), p. 71). The current account acquires the tilt term
  `−ϑ W₀/(1 + r)` (O&R (2.20), p. 75).
* With variable interest rates and discount weights `R_s`, the same algebra
  gives O&R (2.26), p. 78.
-/

namespace ObstfeldRogoff.SmallOpenEconomyDynamics.FundamentalCurrentAccount

open PresentValue

/-- Lifetime wealth `W₀ = (1 + r) B₀ + PV(Y − G − I)`, O&R (2.19), p. 71. -/
noncomputable def wealth (r B0 : ℝ) (Y G I : ℕ → ℝ) : ℝ :=
  (1 + r) * B0 + pv r (fun s => Y s - G s - I s)

/-- The date-0 current account `CA₀ = Y₀ + rB₀ − C₀ − G₀ − I₀`, O&R (2.2). -/
def currentAccount (r B0 C0 : ℝ) (Y G I : ℕ → ℝ) : ℝ := Y 0 + r * B0 - C0 - G 0 - I 0

/-- **Consumption with `β(1 + r) = 1`**, O&R (2.10), p. 62: if consumption is constant at `C̄` and
the intertemporal budget constraint `PV(C) = W₀` holds, then `C̄ = r W₀/(1 + r)`. -/
theorem flat_consumption_level {r B0 Cbar : ℝ} (hr : 0 < r) {Y G I : ℕ → ℝ}
    (hibc : pv r (fun _ => Cbar) = wealth r B0 Y G I) :
    Cbar = r / (1 + r) * wealth r B0 Y G I := by
  rw [pv_const hr] at hibc
  rw [← hibc]
  have : (1 : ℝ) + r ≠ 0 := by linarith
  field_simp

/-- Consumption out of wealth equals interest on assets plus permanent net output:
`r W₀/(1 + r) = rB₀ + (Y − G − I)~`. -/
theorem annuity_wealth (r B0 : ℝ) (hr : 0 < 1 + r) (Y G I : ℕ → ℝ) :
    r / (1 + r) * wealth r B0 Y G I = r * B0 + permanent r (fun s => Y s - G s - I s) := by
  unfold wealth permanent
  field_simp

/-- **The fundamental current-account equation**, O&R (2.18), p. 74: if consumption equals the
annuity value of wealth, `C₀ = rW₀/(1 + r)`, then
`CA₀ = (Y₀ − Ỹ) − (I₀ − Ĩ) − (G₀ − G̃)`. Summability of the three flows lets the permanent value
split. -/
theorem fundamental_current_account {r B0 C0 : ℝ} (hr : 0 < r) {Y G I : ℕ → ℝ}
    (hY : Summable fun s => disc r ^ s * Y s) (hG : Summable fun s => disc r ^ s * G s)
    (hI : Summable fun s => disc r ^ s * I s) (hC : C0 = r / (1 + r) * wealth r B0 Y G I) :
    currentAccount r B0 C0 Y G I =
      (Y 0 - permanent r Y) - (I 0 - permanent r I) - (G 0 - permanent r G) := by
  have hYG : Summable fun s => disc r ^ s * (Y s - G s) := by
    simpa [mul_sub] using hY.sub hG
  have hsplit : permanent r (fun s => Y s - G s - I s) =
      permanent r Y - permanent r G - permanent r I := by
    rw [permanent_sub hYG hI, permanent_sub hY hG]
  rw [currentAccount, hC, annuity_wealth r B0 (by linarith) Y G I, hsplit]
  ring

/-- **(2.10) ⇒ (2.18)**: with constant consumption satisfying the intertemporal budget constraint,
the current account obeys the fundamental equation. -/
theorem fundamental_current_account_of_flat {r B0 Cbar : ℝ} (hr : 0 < r) {Y G I : ℕ → ℝ}
    (hY : Summable fun s => disc r ^ s * Y s) (hG : Summable fun s => disc r ^ s * G s)
    (hI : Summable fun s => disc r ^ s * I s)
    (hibc : pv r (fun _ => Cbar) = wealth r B0 Y G I) :
    currentAccount r B0 Cbar Y G I =
      (Y 0 - permanent r Y) - (I 0 - permanent r I) - (G 0 - permanent r G) :=
  fundamental_current_account hr hY hG hI (flat_consumption_level hr hibc)

/-- **A permanent shock leaves the current account unchanged** (O&R p. 75): adding a constant `c`
to output adds `c` to permanent output as well. -/
theorem permanent_shock_no_ca {r : ℝ} (hr : 0 < r) {Y : ℕ → ℝ}
    (hY : Summable fun s => disc r ^ s * Y s) (c : ℝ) :
    (Y 0 + c) - permanent r (fun s => Y s + c) = Y 0 - permanent r Y := by
  have hc : Summable fun s => disc r ^ s * c :=
    (hasSum_disc_pow hr).summable.mul_right c
  rw [permanent_add hY hc, permanent_const hr]
  ring

/-- **A temporary shock is saved** (O&R pp. 74–75): raising date-0 output alone by `d` raises
`Y₀ − Ỹ` by `d/(1 + r)`, which is positive: most of a temporary windfall goes to the current
account. -/
theorem temporary_shock_ca {r : ℝ} (hr : 0 < r) {Y : ℕ → ℝ}
    (hY : Summable fun s => disc r ^ s * Y s) (d : ℝ) :
    (Y 0 + d) - permanent r (fun s => Y s + if s = 0 then d else 0) =
      (Y 0 - permanent r Y) + d / (1 + r) := by
  have hd : Summable fun s => disc r ^ s * (if s = 0 then d else 0) := by
    apply summable_of_ne_finset_zero (s := {0})
    intro s hs
    simp only [Finset.mem_singleton] at hs
    simp [hs]
  rw [permanent_add hY hd]
  have : permanent r (fun s => if s = 0 then d else 0) = r / (1 + r) * d := by
    unfold permanent pv
    rw [tsum_eq_single 0 (fun s hs => by simp [hs])]
    simp
  rw [this]
  have : (1 : ℝ) + r ≠ 0 := by linarith
  field_simp
  ring

/-! ### Tilted consumption (O&R (2.16), (2.20)) -/

/-- **Consumption with geometric growth**, O&R (2.16), p. 71: if `C_s = γ^s C₀` with
`0 ≤ γ < 1 + r` and `PV(C) = W₀`, then `C₀ = (1 + r − γ) W₀/(1 + r)`. In the isoelastic case
`γ = (1 + r)^σ β^σ`, this is `C₀ = (r + ϑ)W₀/(1 + r)` with `ϑ = 1 − γ`. -/
theorem geometric_consumption_level {r γ C0 W : ℝ} (hr : 0 < 1 + r) (hγ : 0 ≤ γ)
    (hγr : γ < 1 + r) (hibc : pv r (fun s => γ ^ s * C0) = W) :
    C0 = (1 + r - γ) / (1 + r) * W := by
  have hq0 : 0 ≤ γ / (1 + r) := div_nonneg hγ hr.le
  have hq1 : γ / (1 + r) < 1 := (div_lt_one hr).2 hγr
  unfold pv at hibc
  have e : ∀ s : ℕ, disc r ^ s * (γ ^ s * C0) = (γ / (1 + r)) ^ s * C0 := by
    intro s
    unfold disc
    rw [div_pow, inv_pow]
    ring
  simp_rw [e] at hibc
  rw [tsum_mul_right, tsum_geometric_of_lt_one hq0 hq1] at hibc
  rw [← hibc]
  have h1 : (1 : ℝ) + r ≠ 0 := hr.ne'
  have h2 : (1 + r - γ) ≠ 0 := by linarith
  have e2 : 1 - γ / (1 + r) = (1 + r - γ) / (1 + r) := by field_simp
  rw [e2, inv_div]
  field_simp

/-- **The tilted fundamental equation**, O&R (2.20), p. 75: if `C₀ = (r + ϑ)W₀/(1 + r)` then
`CA₀ = (Y₀ − Ỹ) − (I₀ − Ĩ) − (G₀ − G̃) − ϑ W₀/(1 + r)`. -/
theorem tilted_current_account {r ϑ B0 C0 : ℝ} (hr : 0 < r) {Y G I : ℕ → ℝ}
    (hY : Summable fun s => disc r ^ s * Y s) (hG : Summable fun s => disc r ^ s * G s)
    (hI : Summable fun s => disc r ^ s * I s)
    (hC : C0 = (r + ϑ) / (1 + r) * wealth r B0 Y G I) :
    currentAccount r B0 C0 Y G I =
      (Y 0 - permanent r Y) - (I 0 - permanent r I) - (G 0 - permanent r G) -
        ϑ * wealth r B0 Y G I / (1 + r) := by
  have h0 := fundamental_current_account hr hY hG hI (C0 := r / (1 + r) * wealth r B0 Y G I) rfl
  have e : currentAccount r B0 C0 Y G I = currentAccount r B0 (r / (1 + r) * wealth r B0 Y G I)
      Y G I - ϑ * wealth r B0 Y G I / (1 + r) := by
    unfold currentAccount
    rw [hC]
    ring
  rw [e, h0]

/-- **(2.16) ⇒ (2.20)**: with consumption growing at gross rate `γ = 1 − ϑ < 1 + r` and satisfying
the intertemporal budget constraint, the current account obeys the tilted equation. -/
theorem tilted_current_account_of_growth {r γ B0 C0 : ℝ} (hr : 0 < r) (hγ : 0 ≤ γ)
    (hγr : γ < 1 + r) {Y G I : ℕ → ℝ}
    (hY : Summable fun s => disc r ^ s * Y s) (hG : Summable fun s => disc r ^ s * G s)
    (hI : Summable fun s => disc r ^ s * I s)
    (hibc : pv r (fun s => γ ^ s * C0) = wealth r B0 Y G I) :
    currentAccount r B0 C0 Y G I =
      (Y 0 - permanent r Y) - (I 0 - permanent r I) - (G 0 - permanent r G) -
        (1 - γ) * wealth r B0 Y G I / (1 + r) := by
  refine tilted_current_account hr hY hG hI ?_
  rw [geometric_consumption_level (by linarith) hγ hγr hibc]
  ring_nf

/-- Rising consumption (`γ > 1`, i.e. `ϑ < 0`) lowers saving relative to the flat case when wealth
is positive: the tilt term `−ϑW₀/(1 + r)` is negative iff `ϑ > 0`. -/
theorem tilt_term_neg_iff {r ϑ W : ℝ} (hr : 0 < 1 + r) (hW : 0 < W) :
    -(ϑ * W / (1 + r)) < 0 ↔ 0 < ϑ := by
  rw [neg_lt_zero, div_pos_iff_of_pos_right hr]
  exact ⟨fun h => pos_of_mul_pos_left h hW.le, fun h => mul_pos h hW⟩

/-! ### Variable interest rates (O&R (2.25)–(2.26), pp. 77–78) -/

/-- **The fundamental equation with variable interest rates**, O&R (2.26), p. 78. Discount weights
`R_s` (with `R₀ = 1`), their sum `S`, weighted means `Ñ = Σ R_s N_s / S` of net output
`N = Y − G − I` and `Γ̃ = Σ R_s g_s / S` of consumption growth factors `g_s = C_s/C₀`, and
`r̃ = (1 + r₀)/S`. If `C_s = g_s C₀` satisfies the budget constraint
`Σ R_s C_s = (1 + r₀)B₀ + Σ R_s N_s`, then
`CA₀ = (r₀ − r̃)B₀ + (N₀ − Ñ) + ((Γ̃ − 1)/Γ̃)(r̃ B₀ + Ñ)`. -/
theorem variable_rate_current_account {r0 B0 C0 S SN SG N0 : ℝ} (hS : 0 < S) (hSG : 0 < SG)
    (hibc : C0 * SG = (1 + r0) * B0 + SN) :
    r0 * B0 + N0 - C0 =
      (r0 - (1 + r0) / S) * B0 + (N0 - SN / S) +
        ((SG / S - 1) / (SG / S)) * ((1 + r0) / S * B0 + SN / S) := by
  have hC : C0 = ((1 + r0) * B0 + SN) / SG := by
    field_simp
    linarith
  rw [hC]
  field_simp
  ring

/-- With constant consumption (`g_s = 1`, so `Γ̃ = 1`) the variable-rate equation reduces to
`CA₀ = (r₀ − r̃)B₀ + (N₀ − Ñ)` (O&R footnote 14, `σ = 0`). -/
theorem variable_rate_current_account_flat {r0 B0 C0 S SN N0 : ℝ} (hS : 0 < S)
    (hibc : C0 * S = (1 + r0) * B0 + SN) :
    r0 * B0 + N0 - C0 = (r0 - (1 + r0) / S) * B0 + (N0 - SN / S) := by
  have := variable_rate_current_account (N0 := N0) hS hS hibc
  rw [this, div_self hS.ne', sub_self, zero_div, zero_mul, add_zero]

end ObstfeldRogoff.SmallOpenEconomyDynamics.FundamentalCurrentAccount
