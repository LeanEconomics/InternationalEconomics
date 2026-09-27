/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import SmallOpenEconomyDynamics.FundamentalCurrentAccount
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# Consumer durables and the current account

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*,
§2.4, pp. 96–99. Date 0 stands for the book's date `t`. The consumer values
nondurables `C_s` and the end-of-period durables stock `D_s` by
`Σ β^s [γ log C_s + (1 − γ) log D_s]` (O&R (2.46)). Durables cost `p_s`,
depreciate at rate `δ`, and yield services in the period they are bought, so the
finance constraint is
`B_{s+1} − B_s = r B_s + Y_s − C_s − p_s[D_s − (1 − δ) D_{s−1}] − I_s − G_s`,
with `I_s = K_{s+1} − K_s`. The initial stock `D_{−1}` is the number `Dm`
(`prevStock`).

* **Euler equations** (p. 97): one-period perturbations of bonds and of durables
  that leave the finance constraint intact elsewhere have zero utility
  derivative at an optimum (`consumption_euler_of_isLocalMax`,
  `durable_euler_of_isLocalMax`).
* **User cost** (2.47): `(1 − γ)C_s/(γ D_s) = p_s − (1 − δ)p_{s+1}/(1 + r_{s+1}) = ι_s`.
* **Intertemporal budget constraint** (2.48), constant `r`: the combined stock
  `A_s = (1 + r)B_s + (1 − δ)p_s D_{s−1}` of bonds and resale value of durables
  obeys `A_{s+1} = (1 + r)(A_s + Z_s − C_s − ι_s D_s)` with `Z = Y − G − I`, so
  transversality on `A` is equivalent to
  `PV(C + ιD) = (1 + r)B_0 + (1 − δ)p_0 D_{−1} + PV(Y − G − I)` (`durables_ibc_iff`).
* **Consumption functions** (2.49) with `β(1 + r) = 1`.
* **Constant durables price** (2.50) and the lumpiness of durables purchases (p. 98).
* **The modified fundamental current-account equation** (2.51):
  `CA = (Y − Ỹ) − (I − Ĩ) − (G − G̃) + (ι − p)ΔD`, with `ι → p` as `δ → 1`.
-/

namespace ObstfeldRogoff.SmallOpenEconomyDynamics.Durables

open Filter Topology PresentValue FundamentalCurrentAccount

/-- The durables stock held at the start of date `s`, i.e. `D_{s−1}` (O&R p. 96); at date 0 it is
the initial stock `Dm = D_{t−1}`. -/
def prevStock (Dm : ℝ) (D : ℕ → ℝ) : ℕ → ℝ
  | 0 => Dm
  | s + 1 => D s

/-- The user cost of durables with a constant interest rate, O&R (2.47), p. 97:
`ι_s = p_s − (1 − δ) p_{s+1}/(1 + r)`. -/
noncomputable def userCost (r δ : ℝ) (p : ℕ → ℝ) (s : ℕ) : ℝ :=
  p s - (1 - δ) * p (s + 1) / (1 + r)

/-- Bonds plus the resale value of the depreciated durables stock at the start of date `s`,
`A_s = (1 + r) B_s + (1 − δ) p_s D_{s−1}`: the right side of O&R (2.48) at date `s`. -/
noncomputable def durableAssets (r δ Dm : ℝ) (B D p : ℕ → ℝ) (s : ℕ) : ℝ :=
  (1 + r) * B s + (1 - δ) * p s * prevStock Dm D s

/-- Durables-inclusive wealth `W^D = (1 + r)B_0 + (1 − δ)p_0 D_{−1} + PV(Y − G − I)`, the right side
of O&R (2.48), p. 97, built on the lifetime wealth of O&R (2.19). -/
noncomputable def durableWealth (r δ B0 p0 Dm : ℝ) (Y G I : ℕ → ℝ) : ℝ :=
  wealth r B0 Y G I + (1 - δ) * p0 * Dm

/-! ### Euler equations and the user cost -/

/-- **The durables perturbation is feasible**, O&R p. 97: buying `ε` more durables at date `s`
(paid out of nondurables) and selling the depreciated extra `(1 − δ)ε` at `s + 1` (spent on
nondurables) leaves total outlays `C + p[D − (1 − δ)D_{−1}]` unchanged at both dates, so the
bond path, and hence the finance constraint, is unaffected. -/
theorem durable_perturbation_feasible (Cs Cs1 Ds Ds1 Dprev ps ps1 δ ε : ℝ) :
    (Cs - ps * ε) + ps * ((Ds + ε) - (1 - δ) * Dprev) = Cs + ps * (Ds - (1 - δ) * Dprev) ∧
      (Cs1 + (1 - δ) * ps1 * ε) + ps1 * (Ds1 - (1 - δ) * (Ds + ε)) =
        Cs1 + ps1 * (Ds1 - (1 - δ) * Ds) := by
  constructor <;> ring

/-- **Utility derivative of the durables perturbation**, O&R p. 97: the utility terms of (2.46)
that the perturbation of `durable_perturbation_feasible` changes,
`γ log(C_s − p_s ε) + (1 − γ) log(D_s + ε) + βγ log(C_{s+1} + (1 − δ)p_{s+1} ε)`, have derivative
`(1 − γ)/D_s + β(1 − δ)γ p_{s+1}/C_{s+1} − γ p_s/C_s` at `ε = 0`. -/
theorem hasDerivAt_durable_perturbation {γ β δ Cs Cs1 Ds ps ps1 : ℝ} (hCs : Cs ≠ 0)
    (hCs1 : Cs1 ≠ 0) (hDs : Ds ≠ 0) :
    HasDerivAt (fun ε => γ * Real.log (Cs - ps * ε) + (1 - γ) * Real.log (Ds + ε) +
        β * (γ * Real.log (Cs1 + (1 - δ) * ps1 * ε)))
      ((1 - γ) / Ds + β * (1 - δ) * γ * ps1 / Cs1 - γ * ps / Cs) 0 := by
  have h1 : HasDerivAt (fun ε : ℝ => Cs - ps * ε) (-ps) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).const_mul ps).const_sub Cs
    simpa using this
  have h2 : HasDerivAt (fun ε : ℝ => Ds + ε) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_add Ds
  have h3 : HasDerivAt (fun ε : ℝ => Cs1 + (1 - δ) * ps1 * ε) ((1 - δ) * ps1) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul ((1 - δ) * ps1)).const_add Cs1
  have l1 := (h1.log (by simpa using hCs)).const_mul γ
  have l2 := (h2.log (by simpa using hDs)).const_mul (1 - γ)
  have l3 := ((h3.log (by simpa using hCs1)).const_mul γ).const_mul β
  have := HasDerivAt.add (HasDerivAt.add l1 l2) l3
  refine this.congr_deriv ?_
  simp only [mul_zero, sub_zero, add_zero]
  field_simp
  ring

/-- **Durables Euler equation**, O&R p. 97: if the durables perturbation cannot raise utility
(local maximum at `ε = 0`; positive consumption and stock make the logs well defined), then
`γ p_s/C_s = (1 − γ)/D_s + β(1 − δ)γ p_{s+1}/C_{s+1}`. -/
theorem durable_euler_of_isLocalMax {γ β δ Cs Cs1 Ds ps ps1 : ℝ} (hCs : 0 < Cs)
    (hCs1 : 0 < Cs1) (hDs : 0 < Ds)
    (hmax : IsLocalMax (fun ε => γ * Real.log (Cs - ps * ε) + (1 - γ) * Real.log (Ds + ε) +
        β * (γ * Real.log (Cs1 + (1 - δ) * ps1 * ε))) 0) :
    γ * ps / Cs = (1 - γ) / Ds + β * (1 - δ) * γ * ps1 / Cs1 := by
  have := hmax.hasDerivAt_eq_zero
    (hasDerivAt_durable_perturbation (γ := γ) (β := β) (δ := δ) (ps := ps) (ps1 := ps1)
      hCs.ne' hCs1.ne' hDs.ne')
  linarith

/-- **Utility derivative of the bond perturbation**, O&R p. 97: lending `ε` more at date `s` and
consuming the proceeds `(1 + r_{s+1})ε` at `s + 1` changes utility by
`γ log(C_s − ε) + βγ log(C_{s+1} + (1 + r_{s+1})ε)`, with derivative
`βγ(1 + r_{s+1})/C_{s+1} − γ/C_s` at `ε = 0`. -/
theorem hasDerivAt_bond_perturbation {γ β r1 Cs Cs1 : ℝ} (hCs : Cs ≠ 0) (hCs1 : Cs1 ≠ 0) :
    HasDerivAt (fun ε => γ * Real.log (Cs - ε) + β * (γ * Real.log (Cs1 + (1 + r1) * ε)))
      (β * γ * (1 + r1) / Cs1 - γ / Cs) 0 := by
  have h1 : HasDerivAt (fun ε : ℝ => Cs - ε) (-1) 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_sub Cs
  have h3 : HasDerivAt (fun ε : ℝ => Cs1 + (1 + r1) * ε) (1 + r1) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul (1 + r1)).const_add Cs1
  have l1 := (h1.log (by simpa using hCs)).const_mul γ
  have l3 := ((h3.log (by simpa using hCs1)).const_mul γ).const_mul β
  refine (HasDerivAt.add l1 l3).congr_deriv ?_
  simp only [mul_zero, sub_zero, add_zero]
  field_simp
  ring

/-- **Nondurables Euler equation**, O&R p. 97: at an optimum of the bond perturbation, with
`γ > 0` and positive consumption, `C_{s+1} = (1 + r_{s+1}) β C_s`. -/
theorem consumption_euler_of_isLocalMax {γ β r1 Cs Cs1 : ℝ} (hγ : 0 < γ) (hCs : 0 < Cs)
    (hCs1 : 0 < Cs1)
    (hmax : IsLocalMax
      (fun ε => γ * Real.log (Cs - ε) + β * (γ * Real.log (Cs1 + (1 + r1) * ε))) 0) :
    Cs1 = (1 + r1) * β * Cs := by
  have h := hmax.hasDerivAt_eq_zero
    (hasDerivAt_bond_perturbation (γ := γ) (β := β) (r1 := r1) hCs.ne' hCs1.ne')
  have e : β * γ * (1 + r1) / Cs1 = γ / Cs := by linarith
  field_simp at e
  rw [← e]
  ring

/-- **The user cost of durables**, O&R (2.47), p. 97, with variable interest rates: combining
the two Euler equations (eliminating `C_{s+1}`),
`(1 − γ) C_s/(γ D_s) = p_s − (1 − δ) p_{s+1}/(1 + r_{s+1})`. Requires `γ ≠ 0`, `β ≠ 0`,
`1 + r_{s+1} ≠ 0` and nonzero consumption and stock. -/
theorem user_cost_of_euler {γ β δ r1 Cs Cs1 Ds ps ps1 : ℝ} (hγ : γ ≠ 0) (hβ : β ≠ 0)
    (hr : 1 + r1 ≠ 0) (hCs : Cs ≠ 0) (hDs : Ds ≠ 0)
    (hC : Cs1 = (1 + r1) * β * Cs)
    (hD : γ * ps / Cs = (1 - γ) / Ds + β * (1 - δ) * γ * ps1 / Cs1) :
    (1 - γ) * Cs / (γ * Ds) = ps - (1 - δ) * ps1 / (1 + r1) := by
  subst hC
  field_simp at hD ⊢
  linear_combination (-1 : ℝ) * hD

/-- The constant-rate user cost is the (2.47) expression with `r_{s+1} = r`. -/
theorem user_cost_of_euler_const {γ β δ r Ds : ℝ} {C p : ℕ → ℝ} {s : ℕ} (hγ : γ ≠ 0)
    (hβ : β ≠ 0) (hr : 1 + r ≠ 0) (hCs : C s ≠ 0) (hDs : Ds ≠ 0)
    (hC : C (s + 1) = (1 + r) * β * C s)
    (hD : γ * p s / C s = (1 - γ) / Ds + β * (1 - δ) * γ * p (s + 1) / C (s + 1)) :
    (1 - γ) * C s / (γ * Ds) = userCost r δ p s :=
  user_cost_of_euler hγ hβ hr hCs hDs hC hD

/-! ### The intertemporal budget constraint with durables -/

/-- **Law of motion of bonds plus durables**, O&R p. 97: the finance constraint of p. 96 with a
constant rate implies `A_{s+1} = (1 + r)A_s + (1 + r)(Y_s − G_s − I_s − C_s − ι_s D_s)`. -/
theorem durableAssets_succ {r δ Dm : ℝ} (hr : 1 + r ≠ 0) {B C D p Y G I : ℕ → ℝ}
    (hB : ∀ s, B (s + 1) = (1 + r) * B s + Y s - G s - I s - C s -
      p s * (D s - (1 - δ) * prevStock Dm D s)) (s : ℕ) :
    durableAssets r δ Dm B D p (s + 1) = (1 + r) * durableAssets r δ Dm B D p s +
      (1 + r) * (Y s - G s - I s - (C s + userCost r δ p s * D s)) := by
  unfold durableAssets userCost
  rw [hB s]
  simp only [prevStock]
  field_simp
  ring

/-- **The intertemporal budget constraint with durables**, O&R (2.48), p. 97 (constant `r`, as in
the book): given the finance constraint and summable present values, the transversality
condition `(1 + r)^{-n} A_n → 0` on bonds plus durables holds iff
`Σ (1 + r)^{-s}(C_s + ι_s D_s) = (1 + r)B_0 + (1 − δ)p_0 D_{−1} + Σ (1 + r)^{-s}(Y − G − I)_s`. -/
theorem durables_ibc_iff {r δ Dm : ℝ} (hr : 0 < 1 + r) {B C D p Y G I : ℕ → ℝ}
    (hB : ∀ s, B (s + 1) = (1 + r) * B s + Y s - G s - I s - C s -
      p s * (D s - (1 - δ) * prevStock Dm D s))
    (hZ : Summable fun s => disc r ^ s * (Y s - G s - I s))
    (hX : Summable fun s => disc r ^ s * (C s + userCost r δ p s * D s)) :
    Tendsto (fun n => disc r ^ n * durableAssets r δ Dm B D p n) atTop (𝓝 0) ↔
      pv r (fun s => C s + userCost r δ p s * D s) =
        (1 + r) * B 0 + (1 - δ) * p 0 * Dm + pv r (fun s => Y s - G s - I s) := by
  have key : ∀ s, disc r ^ (s + 1) * ((1 + r) * (Y s - G s - I s -
      (C s + userCost r δ p s * D s))) = disc r ^ s * (Y s - G s - I s) -
        disc r ^ s * (C s + userCost r δ p s * D s) := by
    intro s
    have := one_add_mul_disc hr
    rw [pow_succ]
    linear_combination (disc r ^ s * (Y s - G s - I s - (C s + userCost r δ p s * D s))) * this
  have hs : Summable fun s => disc r ^ (s + 1) * ((1 + r) * (Y s - G s - I s -
      (C s + userCost r δ p s * D s))) := by
    simp_rw [key]
    exact hZ.sub hX
  rw [discounted_tendsto_zero_iff hr (durableAssets_succ hr.ne' hB) hs]
  simp_rw [key]
  rw [hZ.tsum_sub hX]
  unfold pv durableAssets
  simp only [prevStock]
  constructor <;> intro e <;> linarith

/-- **Transversality on bonds and on durables**, O&R p. 97: if `(1 + r)^{-n} B_n → 0` and
`(1 + r)^{-n} p_n D_{n−1} → 0`, the combined condition of `durables_ibc_iff` holds. -/
theorem durableAssets_transversality {r δ Dm : ℝ} {B D p : ℕ → ℝ}
    (hB : Tendsto (fun n => disc r ^ n * B n) atTop (𝓝 0))
    (hpD : Tendsto (fun n => disc r ^ n * (p n * prevStock Dm D n)) atTop (𝓝 0)) :
    Tendsto (fun n => disc r ^ n * durableAssets r δ Dm B D p n) atTop (𝓝 0) := by
  have := (hB.const_mul (1 + r)).add (hpD.const_mul (1 - δ))
  simp only [mul_zero, add_zero] at this
  refine this.congr (fun n => ?_)
  unfold durableAssets
  ring

/-! ### Consumption functions with `β = 1/(1 + r)` -/

/-- **Flat nondurables consumption**, O&R p. 98: with `β(1 + r) = 1` the Euler equation
`C_{s+1} = (1 + r)βC_s` makes nondurables consumption constant. -/
theorem flat_nondurables {r β : ℝ} {C : ℕ → ℝ} (hβ : β * (1 + r) = 1)
    (hE : ∀ s, C (s + 1) = (1 + r) * β * C s) (s : ℕ) : C s = C 0 := by
  induction s with
  | zero => rfl
  | succ n ih =>
    rw [hE n, ih]
    linear_combination C 0 * hβ

/-- **Nondurables consumption function**, O&R (2.49), p. 98: with flat nondurables consumption, the
user-cost relation `γ ι_s D_s = (1 − γ)C_s` of (2.47), and the budget constraint (2.48)
`PV(C + ιD) = W^D`, nondurables consumption is `C_t = γ r W^D/(1 + r)`. -/
theorem nondurables_consumption {r γ δ WD : ℝ} (hr : 0 < r) (hγ : γ ≠ 0) {C D p : ℕ → ℝ}
    (hflat : ∀ s, C s = C 0) (hι : ∀ s, γ * (userCost r δ p s * D s) = (1 - γ) * C s)
    (hibc : pv r (fun s => C s + userCost r δ p s * D s) = WD) :
    C 0 = γ * r / (1 + r) * WD := by
  have e : ∀ s, C s + userCost r δ p s * D s = C 0 / γ := by
    intro s
    have := hι s
    rw [hflat s] at this ⊢
    field_simp
    linear_combination this
  simp_rw [e, pv_const hr] at hibc
  rw [← hibc]
  have : (1 : ℝ) + r ≠ 0 := by linarith
  field_simp

/-- **Durables consumption function**, O&R (2.49), p. 98: under the hypotheses of
`nondurables_consumption`, and with a nonzero user cost, the durables stock at every date is
`D_s = (1 − γ) r W^D/(ι_s (1 + r))`; the book states it at `s = t`. -/
theorem durables_consumption {r γ δ WD : ℝ} (hr : 0 < r) (hγ : γ ≠ 0) {C D p : ℕ → ℝ}
    (hflat : ∀ s, C s = C 0) (hι : ∀ s, γ * (userCost r δ p s * D s) = (1 - γ) * C s)
    (hibc : pv r (fun s => C s + userCost r δ p s * D s) = WD) (s : ℕ)
    (hιs : userCost r δ p s ≠ 0) :
    D s = (1 - γ) * r * WD / (userCost r δ p s * (1 + r)) := by
  have hC := nondurables_consumption hr hγ hflat hι hibc
  have h := hι s
  rw [hflat s, hC] at h
  have : (1 : ℝ) + r ≠ 0 := by linarith
  field_simp
  field_simp at h
  linear_combination h

/-! ### A constant price of durables -/

/-- **Constant user cost**, O&R (2.50), p. 98: with a constant durables price `p`,
`ι = p(r + δ)/(1 + r)`. -/
theorem userCost_const {r δ p0 : ℝ} (hr : 1 + r ≠ 0) {p : ℕ → ℝ} (hp : ∀ s, p s = p0) (s : ℕ) :
    userCost r δ p s = p0 * (r + δ) / (1 + r) := by
  unfold userCost
  rw [hp s, hp (s + 1)]
  field_simp
  ring

/-- **The durables price and the consumption ratio**, O&R (2.50), p. 98: with a constant price
the user-cost relation `(1 − γ)C = γ ι D` gives `p = ((1 + r)/(r + δ))((1 − γ)/γ)(C/D)`
(for `r + δ ≠ 0`, `γ ≠ 0`, `D ≠ 0`). -/
theorem price_of_consumption_ratio {r δ γ p C D : ℝ} (hr : 1 + r ≠ 0) (hrδ : r + δ ≠ 0)
    (hγ : γ ≠ 0) (hD : D ≠ 0) (hι : γ * (p * (r + δ) / (1 + r) * D) = (1 - γ) * C) :
    p = (1 + r) / (r + δ) * ((1 - γ) / γ) * (C / D) := by
  field_simp
  field_simp at hι
  linear_combination hι

/-- **A constant durables stock**, O&R p. 98: with constant `p`, flat nondurables consumption
and the user-cost relation, and `p(r + δ) ≠ 0`, the durables stock is constant: the consumer
smooths the service flow. -/
theorem durables_stock_const {r δ γ p0 : ℝ} (hr : 1 + r ≠ 0) (hγ : γ ≠ 0)
    (hpι : p0 * (r + δ) ≠ 0) {C D p : ℕ → ℝ} (hp : ∀ s, p s = p0) (hflat : ∀ s, C s = C 0)
    (hι : ∀ s, γ * (userCost r δ p s * D s) = (1 - γ) * C s) (s : ℕ) : D s = D 0 := by
  have hs := hι s
  have h0 := hι 0
  rw [userCost_const hr hp, hflat s] at hs
  rw [userCost_const hr hp] at h0
  have hc : p0 * (r + δ) / (1 + r) ≠ 0 := div_ne_zero hpι hr
  have : γ * (p0 * (r + δ) / (1 + r)) * D s = γ * (p0 * (r + δ) / (1 + r)) * D 0 := by
    linear_combination hs - h0
  exact mul_left_cancel₀ (mul_ne_zero hγ hc) this

/-- **Durables expenditure after date `t` is replacement only**, O&R p. 98: under the hypotheses
of `durables_stock_const`, spending on durables at every date after `t` is `p δ D_t`, while the
date-`t` purchase is `p(D_t − (1 − δ)D_{t−1})`. Expenditures are not smoothed. -/
theorem durables_purchases_after_t {r δ γ p0 Dm : ℝ} (hr : 1 + r ≠ 0) (hγ : γ ≠ 0)
    (hpι : p0 * (r + δ) ≠ 0) {C D p : ℕ → ℝ} (hp : ∀ s, p s = p0) (hflat : ∀ s, C s = C 0)
    (hι : ∀ s, γ * (userCost r δ p s * D s) = (1 - γ) * C s) (s : ℕ) :
    p (s + 1) * (D (s + 1) - (1 - δ) * prevStock Dm D (s + 1)) = p0 * δ * D 0 := by
  simp only [prevStock]
  rw [hp, durables_stock_const hr hγ hpι hp hflat hι (s + 1),
    durables_stock_const hr hγ hpι hp hflat hι s]
  ring

/-- **Lump-sum durables purchases**, O&R p. 98: with constant `r` and `p` and no depreciation
(`δ = 0`, `p r ≠ 0`), all durables are bought at date `t`; purchases at every later date are
zero. -/
theorem durables_lump_sum {r γ p0 Dm : ℝ} (hr : 1 + r ≠ 0) (hγ : γ ≠ 0) (hpr : p0 * r ≠ 0)
    {C D p : ℕ → ℝ} (hp : ∀ s, p s = p0) (hflat : ∀ s, C s = C 0)
    (hι : ∀ s, γ * (userCost r 0 p s * D s) = (1 - γ) * C s) (s : ℕ) :
    p (s + 1) * (D (s + 1) - prevStock Dm D (s + 1)) = 0 := by
  have h := durables_purchases_after_t (Dm := Dm) hr hγ (by simpa using hpr) hp hflat hι s
  simpa using h

/-! ### The modified fundamental current-account equation -/

/-- The date-`t` current account with durables, O&R p. 98:
`CA_t = rB_t + Y_t − C_t − G_t − I_t − p[D_t − (1 − δ)D_{t−1}]`. -/
def currentAccountDurables (r δ B0 C0 p D0 Dm : ℝ) (Y G I : ℕ → ℝ) : ℝ :=
  currentAccount r B0 C0 Y G I - p * (D0 - (1 - δ) * Dm)

/-- **The modified fundamental current-account equation**, O&R (2.51), p. 99: with a constant
durables price `p`, nondurables consumption `C_t = γ r W^D/(1 + r)` from (2.49), and the
user-cost relation `(1 − γ)C_t = γ ι D_t` with `ι = p(r + δ)/(1 + r)` from (2.50),
`CA_t = (Y_t − Ỹ) − (I_t − Ĩ) − (G_t − G̃) + (ι − p)(D_t − D_{t−1})`. -/
theorem durables_current_account {r δ γ B0 C0 p D0 Dm : ℝ} (hr : 0 < r) (hγ : γ ≠ 0)
    {Y G I : ℕ → ℝ} (hY : Summable fun s => disc r ^ s * Y s)
    (hG : Summable fun s => disc r ^ s * G s) (hI : Summable fun s => disc r ^ s * I s)
    (hC : C0 = γ * r / (1 + r) * durableWealth r δ B0 p Dm Y G I)
    (hι : γ * (p * (r + δ) / (1 + r) * D0) = (1 - γ) * C0) :
    currentAccountDurables r δ B0 C0 p D0 Dm Y G I =
      (Y 0 - permanent r Y) - (I 0 - permanent r I) - (G 0 - permanent r G) +
        (p * (r + δ) / (1 + r) - p) * (D0 - Dm) := by
  have h0 := fundamental_current_account hr hY hG hI
    (C0 := r / (1 + r) * wealth r B0 Y G I) (B0 := B0) rfl
  have split : currentAccount r B0 C0 Y G I =
      currentAccount r B0 (r / (1 + r) * wealth r B0 Y G I) Y G I +
        (r / (1 + r) * wealth r B0 Y G I - C0) := by
    unfold currentAccount; ring
  rw [currentAccountDurables, split, h0]
  unfold durableWealth at hC
  have hr1 : (1 : ℝ) + r ≠ 0 := by linarith
  have e : γ * (r / (1 + r) * wealth r B0 Y G I - C0 - p * (D0 - (1 - δ) * Dm) -
      (p * (r + δ) / (1 + r) - p) * (D0 - Dm)) = 0 := by
    rw [hC] at hι ⊢
    field_simp at hι ⊢
    linear_combination (-γ) * hι
  have := (mul_eq_zero.1 e).resolve_left hγ
  linear_combination this

/-- **Full depreciation removes the durables term**, O&R p. 99: at `δ = 1` the user cost equals
the price, `ι_s = p_s`, for any price path. -/
theorem userCost_full_depreciation (r : ℝ) (p : ℕ → ℝ) (s : ℕ) : userCost r 1 p s = p s := by
  simp [userCost]

/-- **`ι → p` as `δ → 1`**, O&R p. 99: with a constant price, the user cost `p(r + δ)/(1 + r)`
tends to `p` as the depreciation rate tends to one. -/
theorem userCost_tendsto_price {r : ℝ} (hr : 1 + r ≠ 0) (p : ℝ) :
    Tendsto (fun δ : ℝ => p * (r + δ) / (1 + r)) (𝓝 1) (𝓝 p) := by
  have hc : Continuous fun δ : ℝ => p * (r + δ) / (1 + r) := by fun_prop
  have := hc.tendsto 1
  have e : p * (r + 1) / (1 + r) = p := by field_simp; ring
  rwa [e] at this

/-- **With full depreciation (2.51) reduces to (2.18)**, O&R p. 99: at `δ = 1` durables behave
like nondurables and the current account obeys the fundamental equation of O&R (2.18). -/
theorem durables_current_account_full_depreciation {r γ B0 C0 p D0 Dm : ℝ} (hr : 0 < r)
    (hγ : γ ≠ 0) {Y G I : ℕ → ℝ} (hY : Summable fun s => disc r ^ s * Y s)
    (hG : Summable fun s => disc r ^ s * G s) (hI : Summable fun s => disc r ^ s * I s)
    (hC : C0 = γ * r / (1 + r) * durableWealth r 1 B0 p Dm Y G I)
    (hι : γ * (p * (r + 1) / (1 + r) * D0) = (1 - γ) * C0) :
    currentAccountDurables r 1 B0 C0 p D0 Dm Y G I =
      (Y 0 - permanent r Y) - (I 0 - permanent r I) - (G 0 - permanent r G) := by
  rw [durables_current_account hr hγ hY hG hI hC hι]
  have : (1 : ℝ) + r ≠ 0 := by linarith
  have e : p * (r + 1) / (1 + r) - p = 0 := by field_simp; ring
  rw [e]
  ring

end ObstfeldRogoff.SmallOpenEconomyDynamics.Durables
