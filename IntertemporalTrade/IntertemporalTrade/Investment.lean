/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The role of investment

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §1.2,
pp. 14–22. Output is produced from capital, `Y = F(K)` (O&R (1.10), p. 14); capital is
the consumption good in another use, does not depreciate and can be eaten,
`K_{t+1} = K_t + I_t` (O&R (1.11), p. 15). A small open economy borrows and lends at
the world rate `r > -1`.

* §1.2.1: the current account and saving identities (1.12)–(1.14).
* §1.2.2: the intertemporal budget constraint (1.15), the reduced problem (1.16), and
  **Fisher separation**: whatever the preferences `(u, β)` and government spending
  `(G₁, G₂)`, an optimal plan's capital stock `K₂` maximises the present value of output
  net of investment, equivalently the profit `F(K) − rK`. This is proved with no
  derivatives at all; the first-order condition `F'(K₂) = r` (1.17) is a corollary, and
  strict concavity of `F` makes `K₂` unique, hence independent of `u`, `β`, `G₁`, `G₂`
  (no crowding out, p. 19).
* §1.2.3: the production possibilities frontier (1.18), its intercepts, slope
  `−(1 + F'(K₂))`, second derivative `F''(K₂)` (fn. 12) and strict concavity (proved from
  strict concavity of `F`, no second derivatives), autarky tangency and the gains from
  trade (pp. 20–21).
* §1.2.4: government consumption. With consumption demands depending on wealth, a
  temporary rise in `G₁` worsens the date-1 current account if date-2 consumption is
  normal, and a rise in `G₂` improves it if date-1 consumption is normal (p. 22).
-/

namespace ObstfeldRogoff.IntertemporalTrade.Investment

open Set Filter Topology

/-! ## §1.2.1 Current account, saving and investment -/

/-- The current account with investment, O&R (1.12), p. 15:
`CA_t = Y_t + r_t B_t − C_t − G_t − I_t`. -/
def currentAccount (Y r B C G I : ℝ) : ℝ := Y + r * B - C - G - I

/-- National saving, O&R (1.13), p. 15: `S_t = Y_t + r_t B_t − C_t − G_t`. -/
def saving (Y r B C G : ℝ) : ℝ := Y + r * B - C - G

/-- The saving–investment identity, O&R (1.14), p. 16: `CA_t = S_t − I_t`. -/
theorem currentAccount_eq_saving_sub_investment (Y r B C G I : ℝ) :
    currentAccount Y r B C G I = saving Y r B C G - I := by
  unfold currentAccount saving
  ring

/-- O&R p. 15: given capital accumulation `K_{t+1} = K_t + I_t` (1.11), the change in net
foreign assets is the current account (1.12) exactly when the change in total wealth
`B + K` is national saving. -/
theorem nfa_change_iff_wealth_change {Y r B C G I K K' B' : ℝ} (hK : K' = K + I) :
    B' - B = currentAccount Y r B C G I ↔ B' + K' - (B + K) = saving Y r B C G := by
  subst hK
  unfold currentAccount saving
  constructor <;> intro h <;> linarith

/-! ## §1.2.2 Budget constraint and individual maximisation -/

/-- The intertemporal budget constraint, O&R (1.15), p. 17: the two period current account
identities (1.12) with `B₁ = B₃ = 0` hold for some `B₂` exactly when
`C₁ + I₁ + (C₂ + I₂)/(1 + r) = Y₁ − G₁ + (Y₂ − G₂)/(1 + r)`. -/
theorem intertemporal_budget_iff {r Y1 Y2 C1 C2 G1 G2 I1 I2 : ℝ} (hr : 0 < 1 + r) :
    (∃ B2, B2 - 0 = currentAccount Y1 r 0 C1 G1 I1 ∧
        0 - B2 = currentAccount Y2 r B2 C2 G2 I2) ↔
      C1 + I1 + (C2 + I2) / (1 + r) = Y1 - G1 + (Y2 - G2) / (1 + r) := by
  have hr' := hr.ne'
  unfold currentAccount
  constructor
  · rintro ⟨B2, h1, h2⟩
    have hB : B2 = Y1 - C1 - G1 - I1 := by linarith
    subst hB
    field_simp
    linear_combination h2
  · intro h
    refine ⟨Y1 - C1 - G1 - I1, by ring, ?_⟩
    field_simp at h
    linear_combination h

/-- Second-period consumption implied by the budget constraint (1.15) when `Y = F(K)`,
`K₂ = K₁ + I₁` and `I₂ = −K₂` (`K₃ = 0`): the argument of `u` in O&R (1.16), p. 17. -/
def consumption2 (F : ℝ → ℝ) (r K1 G1 G2 C1 I1 : ℝ) : ℝ :=
  (1 + r) * (F K1 - C1 - G1 - I1) + F (I1 + K1) - G2 + I1 + K1

/-- The objective of the reduced problem O&R (1.16), p. 17:
`u(C₁) + β u(C₂)` with `C₂` eliminated through the budget constraint. -/
def utility (u : ℝ → ℝ) (β : ℝ) (F : ℝ → ℝ) (r K1 G1 G2 C1 I1 : ℝ) : ℝ :=
  u C1 + β * u (consumption2 F r K1 G1 G2 C1 I1)

/-- O&R (1.16), p. 17: with `Y₁ = F(K₁)`, `Y₂ = F(K₁ + I₁)` and `I₂ = −(K₁ + I₁)`, the budget
constraint (1.15) holds exactly when `C₂` is `consumption2`, the expression inside (1.16). -/
theorem budget_iff_consumption2 {F : ℝ → ℝ} {r K1 G1 G2 C1 C2 I1 : ℝ} (hr : 0 < 1 + r) :
    C1 + I1 + (C2 + -(K1 + I1)) / (1 + r) = F K1 - G1 + (F (K1 + I1) - G2) / (1 + r) ↔
      C2 = consumption2 F r K1 G1 G2 C1 I1 := by
  have hr' := hr.ne'
  unfold consumption2
  rw [add_comm I1 K1]
  constructor
  · intro h
    field_simp at h
    linear_combination h
  · intro h
    rw [h]
    field_simp
    ring

/-- A plan `(C₁, I₁)` solves the reduced problem (1.16), O&R p. 17, on the feasible set
`C₁ ∈ SC`, `K₂ = K₁ + I₁ ∈ SK` (e.g. `SK = [0, ∞)`; the book leaves the sets implicit). -/
def IsOptimal (u : ℝ → ℝ) (β : ℝ) (F : ℝ → ℝ) (r K1 G1 G2 : ℝ) (SC SK : Set ℝ)
    (C1 I1 : ℝ) : Prop :=
  C1 ∈ SC ∧ K1 + I1 ∈ SK ∧ ∀ C1' ∈ SC, ∀ I1' : ℝ, K1 + I1' ∈ SK →
    utility u β F r K1 G1 G2 C1' I1' ≤ utility u β F r K1 G1 G2 C1 I1

/-- The present value of output net of investment, O&R p. 21, when date-2 capital is `K₂`:
`F(K₁) − (K₂ − K₁) + (F(K₂) + K₂)/(1 + r)`. -/
noncomputable def pvNetOutput (F : ℝ → ℝ) (r K1 K2 : ℝ) : ℝ :=
  F K1 - (K2 - K1) + (F K2 + K2) / (1 + r)

/-- O&R p. 21: maximising the present value of net output is maximising the profit
`F(K₂) − r K₂`, since `PV = F(K₁) + K₁ + (F(K₂) − r K₂)/(1 + r)`. -/
theorem pvNetOutput_eq {F : ℝ → ℝ} {r : ℝ} (hr : 0 < 1 + r) (K1 K2 : ℝ) :
    pvNetOutput F r K1 K2 = F K1 + K1 + (F K2 - r * K2) / (1 + r) := by
  have hr' := hr.ne'
  unfold pvNetOutput
  field_simp
  ring

/-- O&R (1.15)–(1.16), p. 17: second-period consumption is `(1 + r)` times the present
value of net output less government spending and date-1 consumption. -/
theorem consumption2_eq_pv {F : ℝ → ℝ} {r : ℝ} (hr : 0 < 1 + r) (K1 G1 G2 C1 I1 : ℝ) :
    consumption2 F r K1 G1 G2 C1 I1 =
      (1 + r) * (pvNetOutput F r K1 (K1 + I1) - G1 - C1) - G2 := by
  have hr' := hr.ne'
  unfold consumption2 pvNetOutput
  rw [add_comm I1 K1]
  field_simp
  ring

/-- **Fisher separation**, O&R (1.17) and p. 19, derivative-free: if `u` is strictly
increasing on `(0, ∞)`, `β > 0`, and `(C₁, I₁)` solves (1.16) with `C₂ > 0`, then
`K₂ = K₁ + I₁` maximises the profit `F(K) − rK` over all feasible `K`, whatever `u`, `β`,
`G₁`, `G₂`. -/
theorem fisher_separation {u : ℝ → ℝ} {β : ℝ} {F : ℝ → ℝ} {r K1 G1 G2 : ℝ}
    {SC SK : Set ℝ} {C1 I1 : ℝ} (hu : StrictMonoOn u (Ioi 0)) (hβ : 0 < β)
    (hopt : IsOptimal u β F r K1 G1 G2 SC SK C1 I1)
    (hC2 : 0 < consumption2 F r K1 G1 G2 C1 I1) :
    ∀ K ∈ SK, F K - r * K ≤ F (K1 + I1) - r * (K1 + I1) := by
  intro K hK
  by_contra h
  push Not at h
  have hc : consumption2 F r K1 G1 G2 C1 I1 < consumption2 F r K1 G1 G2 C1 (K - K1) := by
    unfold consumption2
    rw [show K - K1 + K1 = K by ring, add_comm I1 K1]
    linarith
  have hle := hopt.2.2 C1 hopt.1 (K - K1) (by rwa [show K1 + (K - K1) = K by ring])
  unfold utility at hle
  have hlt := hu (mem_Ioi.2 hC2) (mem_Ioi.2 (hC2.trans hc)) hc
  nlinarith [mul_lt_mul_of_pos_left hlt hβ]

/-- Fisher separation in present-value form, O&R p. 21: an optimal plan's production point
maximises the present value of output net of investment. -/
theorem fisher_separation_pv {u : ℝ → ℝ} {β : ℝ} {F : ℝ → ℝ} {r K1 G1 G2 : ℝ}
    {SC SK : Set ℝ} {C1 I1 : ℝ} (hr : 0 < 1 + r) (hu : StrictMonoOn u (Ioi 0)) (hβ : 0 < β)
    (hopt : IsOptimal u β F r K1 G1 G2 SC SK C1 I1)
    (hC2 : 0 < consumption2 F r K1 G1 G2 C1 I1) :
    ∀ K ∈ SK, pvNetOutput F r K1 K ≤ pvNetOutput F r K1 (K1 + I1) := by
  intro K hK
  rw [pvNetOutput_eq hr, pvNetOutput_eq hr]
  have := div_le_div_of_nonneg_right (fisher_separation hu hβ hopt hC2 K hK) hr.le
  linarith

/-- O&R p. 19: with `F` strictly concave on a convex feasible set, the profit `F(K) − rK`
has at most one maximiser. -/
theorem profit_maximizer_unique {F : ℝ → ℝ} {r : ℝ} {SK : Set ℝ}
    (hF : StrictConcaveOn ℝ SK F) {a b : ℝ} (ha : a ∈ SK) (hb : b ∈ SK)
    (hma : ∀ K ∈ SK, F K - r * K ≤ F a - r * a)
    (hmb : ∀ K ∈ SK, F K - r * K ≤ F b - r * b) : a = b := by
  by_contra hne
  have hmid := hF.1 ha hb (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num)
  have hlt := hF.2 ha hb hne (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num)
  simp only [smul_eq_mul] at hmid hlt
  have h1 := hma _ hmid
  have h2 := hma b hb
  have h3 := hmb a ha
  linarith

/-- **Fisher separation: independence**, O&R p. 19. With `F` strictly concave on the
feasible capital set, two economies differing in preferences `(u, β)`, government
spending `(G₁, G₂)` and consumption sets choose the same investment `I₁`. -/
theorem fisher_separation_independent {u u' : ℝ → ℝ} {β β' : ℝ} {F : ℝ → ℝ}
    {r K1 G1 G2 G1' G2' : ℝ} {SC SC' SK : Set ℝ} {C1 I1 C1' I1' : ℝ}
    (hu : StrictMonoOn u (Ioi 0)) (hu' : StrictMonoOn u' (Ioi 0)) (hβ : 0 < β)
    (hβ' : 0 < β') (hF : StrictConcaveOn ℝ SK F)
    (hopt : IsOptimal u β F r K1 G1 G2 SC SK C1 I1)
    (hopt' : IsOptimal u' β' F r K1 G1' G2' SC' SK C1' I1')
    (hC2 : 0 < consumption2 F r K1 G1 G2 C1 I1)
    (hC2' : 0 < consumption2 F r K1 G1' G2' C1' I1') : I1 = I1' := by
  have := profit_maximizer_unique hF hopt.2.1 hopt'.2.1 (fisher_separation hu hβ hopt hC2)
    (fisher_separation hu' hβ' hopt' hC2')
  linarith

/-- **No crowding out**, O&R p. 19: in the small open economy, government consumption
`(G₁, G₂)` does not change the optimal investment `I₁` (for `F` strictly concave). -/
theorem no_crowding_out {u : ℝ → ℝ} {β : ℝ} {F : ℝ → ℝ} {r K1 G1 G2 G1' G2' : ℝ}
    {SC SK : Set ℝ} {C1 I1 C1' I1' : ℝ} (hu : StrictMonoOn u (Ioi 0)) (hβ : 0 < β)
    (hF : StrictConcaveOn ℝ SK F)
    (hopt : IsOptimal u β F r K1 G1 G2 SC SK C1 I1)
    (hopt' : IsOptimal u β F r K1 G1' G2' SC SK C1' I1')
    (hC2 : 0 < consumption2 F r K1 G1 G2 C1 I1)
    (hC2' : 0 < consumption2 F r K1 G1' G2' C1' I1') : I1 = I1' :=
  fisher_separation_independent hu hu hβ hβ hF hopt hopt' hC2 hC2'

/-- The investment first-order condition O&R (1.17), p. 17: at an optimum of (1.16) whose
capital stock `K₂` is interior to the feasible set, `F'(K₂) = r`. -/
theorem capital_foc {u : ℝ → ℝ} {β : ℝ} {F : ℝ → ℝ} {r K1 G1 G2 : ℝ}
    {SC SK : Set ℝ} {C1 I1 F' : ℝ} (hu : StrictMonoOn u (Ioi 0)) (hβ : 0 < β)
    (hopt : IsOptimal u β F r K1 G1 G2 SC SK C1 I1)
    (hC2 : 0 < consumption2 F r K1 G1 G2 C1 I1) (hint : SK ∈ 𝓝 (K1 + I1))
    (hF : HasDerivAt F F' (K1 + I1)) : F' = r := by
  have hmax : IsLocalMax (fun K => F K - r * K) (K1 + I1) :=
    Filter.mem_of_superset hint fun K hK => fisher_separation hu hβ hopt hC2 K hK
  have hd : HasDerivAt (fun K => F K - r * K) (F' - r * 1) (K1 + I1) :=
    hF.sub ((hasDerivAt_id (K1 + I1)).const_mul r)
  linarith [hmax.hasDerivAt_eq_zero hd]

/-- Converse of (1.17), O&R p. 17: for `F` concave on the feasible set, a feasible `K*` with
`F'(K*) = r` maximises the profit `F(K) − rK`. -/
theorem profit_max_of_deriv_eq {F : ℝ → ℝ} {r Ks : ℝ} {SK : Set ℝ}
    (hF : ConcaveOn ℝ SK F) (hs : Ks ∈ SK) (hd : HasDerivAt F r Ks) :
    ∀ K ∈ SK, F K - r * K ≤ F Ks - r * Ks := by
  intro K hK
  rcases lt_trichotomy K Ks with h | h | h
  · have := hF.le_slope_of_hasDerivAt hK hs h hd
    rw [slope_def_field, le_div_iff₀ (sub_pos.2 h)] at this
    linarith
  · rw [h]
  · have := hF.slope_le_of_hasDerivAt hs hK h hd
    rw [slope_def_field, div_le_iff₀ (sub_pos.2 h)] at this
    linarith

/-- **Fisher separation with (1.17)**, O&R pp. 17–19: if `F` is strictly concave on the
feasible set and `F'(K*) = r` at a feasible `K*`, every optimal plan of (1.16), for any
`u`, `β`, `G₁`, `G₂`, has `K₂ = K*`. -/
theorem optimal_capital_eq_of_deriv {u : ℝ → ℝ} {β : ℝ} {F : ℝ → ℝ} {r K1 G1 G2 : ℝ}
    {SC SK : Set ℝ} {C1 I1 Ks : ℝ} (hu : StrictMonoOn u (Ioi 0)) (hβ : 0 < β)
    (hF : StrictConcaveOn ℝ SK F) (hopt : IsOptimal u β F r K1 G1 G2 SC SK C1 I1)
    (hC2 : 0 < consumption2 F r K1 G1 G2 C1 I1) (hs : Ks ∈ SK) (hd : HasDerivAt F r Ks) :
    K1 + I1 = Ks :=
  profit_maximizer_unique hF hopt.2.1 hs (fisher_separation hu hβ hopt hC2)
    (profit_max_of_deriv_eq hF.concaveOn hs hd)

/-- The consumption first-order condition of (1.16), O&R p. 17 (the Euler equation (1.3)):
at an optimum with `C₁` interior, `u'(C₁) = β (1 + r) u'(C₂)`. -/
theorem consumption_foc {u : ℝ → ℝ} {β : ℝ} {F : ℝ → ℝ} {r K1 G1 G2 : ℝ}
    {SC SK : Set ℝ} {C1 I1 u1 u2 : ℝ} (hopt : IsOptimal u β F r K1 G1 G2 SC SK C1 I1)
    (hint : SC ∈ 𝓝 C1) (hu1 : HasDerivAt u u1 C1)
    (hu2 : HasDerivAt u u2 (consumption2 F r K1 G1 G2 C1 I1)) :
    u1 = β * (1 + r) * u2 := by
  have hmax : IsLocalMax (fun C => utility u β F r K1 G1 G2 C I1) C1 :=
    Filter.mem_of_superset hint fun C hC => hopt.2.2 C hC I1 hopt.2.1
  have hc : HasDerivAt (fun C => consumption2 F r K1 G1 G2 C I1) ((1 + r) * (0 - 1)) C1 :=
    (((((((hasDerivAt_const C1 (F K1)).sub (hasDerivAt_id C1)).sub_const G1).sub_const
      I1).const_mul (1 + r)).add_const (F (I1 + K1))).sub_const G2).add_const I1 |>.add_const K1
  have hU : HasDerivAt (fun C => utility u β F r K1 G1 G2 C I1)
      (u1 + β * (u2 * ((1 + r) * (0 - 1)))) C1 :=
    hu1.add ((hu2.comp C1 hc).const_mul β)
  linarith [hmax.hasDerivAt_eq_zero hU]

/-! ## §1.2.3 Production possibilities and equilibrium -/

/-- The intertemporal production possibilities frontier, O&R (1.18), p. 19, extended to
government spending as on p. 21: in autarky date-2 consumption is
`F(K₁ + F(K₁) − G₁ − C₁) + K₁ + F(K₁) − G₁ − C₁ − G₂`. -/
def ppf (F : ℝ → ℝ) (K1 G1 G2 C1 : ℝ) : ℝ :=
  F (K1 + F K1 - G1 - C1) + K1 + F K1 - G1 - C1 - G2

/-- O&R (1.18), p. 19: with `G₁ = G₂ = 0` the PPF is
`C₂ = F[K₁ + F(K₁) − C₁] + K₁ + F(K₁) − C₁`. -/
theorem ppf_no_government (F : ℝ → ℝ) (K1 C1 : ℝ) :
    ppf F K1 0 0 C1 = F (K1 + F K1 - C1) + K1 + F K1 - C1 := by
  simp only [ppf, sub_zero]

/-- O&R pp. 19–21: the PPF is the budget-feasible date-2 consumption of the plan with
current account zero, `I₁ = F(K₁) − G₁ − C₁`, whatever the world rate `r`. -/
theorem consumption2_autarky (F : ℝ → ℝ) (r K1 G1 G2 C1 : ℝ) :
    consumption2 F r K1 G1 G2 C1 (F K1 - G1 - C1) = ppf F K1 G1 G2 C1 := by
  unfold consumption2 ppf
  rw [show F K1 - G1 - C1 + K1 = K1 + F K1 - G1 - C1 by ring]
  ring

/-- Autarky market clearing, O&R p. 21: on the PPF the date-1 current account is zero
(`C₁ + I₁ = Y₁ − G₁`) and date-2 consumption is `Y₂ − G₂ − I₂` with `I₂ = −K₂`. -/
theorem autarky_market_clearing (F : ℝ → ℝ) (r K1 G1 G2 C1 : ℝ) :
    currentAccount (F K1) r 0 C1 G1 (F K1 - G1 - C1) = 0 ∧
      ppf F K1 G1 G2 C1 =
        F (K1 + (F K1 - G1 - C1)) - G2 - -(K1 + (F K1 - G1 - C1)) := by
  constructor
  · unfold currentAccount
    ring
  · unfold ppf
    rw [show K1 + (F K1 - G1 - C1) = K1 + F K1 - G1 - C1 by ring]
    ring

/-- The PPF's horizontal intercept, O&R p. 20: eating all inherited capital,
`C₁ = K₁ + F(K₁)`, leaves `C₂ = F(0) + 0 = 0` (using `F(0) = 0`, (1.10)). -/
theorem ppf_horizontal_intercept {F : ℝ → ℝ} (hF0 : F 0 = 0) (K1 : ℝ) :
    ppf F K1 0 0 (K1 + F K1) = 0 := by
  simp [ppf, hF0]

/-- The PPF's vertical intercept, O&R p. 20 (and fn. 13 with `G₁ > 0`): investing all of
date-1 resources gives `C₂ = F[K₁ + F(K₁) − G₁] + K₁ + F(K₁) − G₁`. -/
theorem ppf_vertical_intercept (F : ℝ → ℝ) (K1 G1 : ℝ) :
    ppf F K1 G1 0 0 = F (K1 + F K1 - G1) + K1 + F K1 - G1 := by
  simp only [ppf, sub_zero]

/-- O&R p. 21: government consumption shifts the PPF leftward by `G₁` and downward by
`G₂`. -/
theorem ppf_shift (F : ℝ → ℝ) (K1 G1 G2 C1 : ℝ) :
    ppf F K1 G1 G2 C1 = ppf F K1 0 0 (C1 + G1) - G2 := by
  unfold ppf
  rw [show K1 + F K1 - 0 - (C1 + G1) = K1 + F K1 - G1 - C1 by ring]
  ring

/-- The slope of the PPF, O&R p. 20: `dC₂/dC₁ = −[1 + F'(K₂)]` with
`K₂ = K₁ + F(K₁) − G₁ − C₁`. -/
theorem ppf_hasDerivAt {F : ℝ → ℝ} {K1 G1 G2 C1 F' : ℝ}
    (hF : HasDerivAt F F' (K1 + F K1 - G1 - C1)) :
    HasDerivAt (ppf F K1 G1 G2) (-(1 + F')) C1 := by
  have hk : HasDerivAt (fun C => K1 + F K1 - G1 - C) (-1) C1 := by
    simpa using (hasDerivAt_id C1).const_sub (K1 + F K1 - G1)
  have h := ((hF.comp C1 hk).add hk).sub_const G2
  have e : ppf F K1 G1 G2 =
      fun C => (F ∘ fun C => K1 + F K1 - G1 - C) C + (K1 + F K1 - G1 - C) - G2 := by
    funext C
    simp only [ppf, Function.comp]
    ring
  rw [e]
  convert h using 1
  ring

/-- O&R fn. 12, p. 20: the derivative of the PPF slope `−[1 + F'(K₂)]` with respect to
`C₁` is `F''(K₂)`. -/
theorem ppf_slope_hasDerivAt {F : ℝ → ℝ} {F' : ℝ → ℝ} {K1 G1 C1 F'' : ℝ}
    (h : HasDerivAt F' F'' (K1 + F K1 - G1 - C1)) :
    HasDerivAt (fun C => -(1 + F' (K1 + F K1 - G1 - C))) F'' C1 := by
  have hk : HasDerivAt (fun C => K1 + F K1 - G1 - C) (-1) C1 := by
    simpa using (hasDerivAt_id C1).const_sub (K1 + F K1 - G1)
  have h2 := ((h.comp C1 hk).const_add 1).neg
  convert h2 using 1
  · funext C
    simp only [Pi.neg_apply, Function.comp]
  · ring

/-- Strict concavity of the PPF, O&R p. 20 and fn. 12, proved from strict concavity of `F`
on `[0, ∞)` without second derivatives: the PPF is strictly concave in `C₁` on the region
`K₂ = K₁ + F(K₁) − G₁ − C₁ ≥ 0`. -/
theorem ppf_strictConcaveOn {F : ℝ → ℝ} (hF : StrictConcaveOn ℝ (Ici 0) F)
    (K1 G1 G2 : ℝ) : StrictConcaveOn ℝ (Iic (K1 + F K1 - G1)) (ppf F K1 G1 G2) := by
  refine ⟨convex_Iic _, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  unfold ppf
  set c := K1 + F K1 - G1 with hc
  have hx' : c - x ∈ Ici 0 := by
    simp only [mem_Iic] at hx
    simp only [mem_Ici]
    linarith
  have hy' : c - y ∈ Ici 0 := by
    simp only [mem_Iic] at hy
    simp only [mem_Ici]
    linarith
  have hne : c - x ≠ c - y := fun h => hxy (by linarith)
  have hlt := hF.2 hx' hy' hne ha hb hab
  simp only [smul_eq_mul] at hlt ⊢
  have e : a * (c - x) + b * (c - y) = c - (a * x + b * y) := by
    linear_combination c * hab
  rw [e] at hlt
  have e2 : a * (c - x - G2) + b * (c - y - G2) = c - (a * x + b * y) - G2 := by
    linear_combination (c - G2) * hab
  linarith

/-- Autarky tangency, O&R pp. 20–21: at an interior autarky optimum (point A) the
indifference curve is tangent to the PPF, `u'(C₁) = β (1 + F'(K₂)) u'(C₂)`; the common
slope is `−(1 + r^A)` with `r^A = F'(K₂)`, so (1.17) holds at the autarky rate. -/
theorem autarky_tangency {u F : ℝ → ℝ} {β K1 G1 G2 C1 u1 u2 F' : ℝ}
    (hmax : IsLocalMax (fun C => u C + β * u (ppf F K1 G1 G2 C)) C1)
    (hu1 : HasDerivAt u u1 C1) (hu2 : HasDerivAt u u2 (ppf F K1 G1 G2 C1))
    (hF : HasDerivAt F F' (K1 + F K1 - G1 - C1)) :
    u1 = β * (1 + F') * u2 := by
  have hU : HasDerivAt (fun C => u C + β * u (ppf F K1 G1 G2 C))
      (u1 + β * (u2 * -(1 + F'))) C1 :=
    hu1.add ((hu2.comp C1 (ppf_hasDerivAt (G2 := G2) hF)).const_mul β)
  linarith [hmax.hasDerivAt_eq_zero hU]

/-- Gains from trade, O&R p. 21: any feasible autarky point is affordable at world prices,
so the open-economy optimum is at least as good as every autarky allocation. -/
theorem gains_from_trade {u : ℝ → ℝ} {β : ℝ} {F : ℝ → ℝ} {r K1 G1 G2 : ℝ}
    {SC SK : Set ℝ} {C1 I1 Ca : ℝ} (hopt : IsOptimal u β F r K1 G1 G2 SC SK C1 I1)
    (hCa : Ca ∈ SC) (hKa : K1 + (F K1 - G1 - Ca) ∈ SK) :
    u Ca + β * u (ppf F K1 G1 G2 Ca) ≤ utility u β F r K1 G1 G2 C1 I1 := by
  have h := hopt.2.2 Ca hCa _ hKa
  rwa [utility, consumption2_autarky] at h

/-! ## §1.2.4 The model with government consumption -/

/-- Lifetime private wealth, O&R (1.15), p. 17: the present value of net output less the
present value of government consumption, given date-2 capital `K₂`. -/
noncomputable def wealth (F : ℝ → ℝ) (r K1 G1 G2 K2 : ℝ) : ℝ :=
  pvNetOutput F r K1 K2 - G1 - G2 / (1 + r)

/-- O&R (1.15), p. 17: a plan's consumption satisfies `C₁ + C₂/(1 + r) = W`, lifetime
wealth at its capital stock. -/
theorem consumption2_budget {F : ℝ → ℝ} {r : ℝ} (hr : 0 < 1 + r) (K1 G1 G2 C1 I1 : ℝ) :
    C1 + consumption2 F r K1 G1 G2 C1 I1 / (1 + r) = wealth F r K1 G1 G2 (K1 + I1) := by
  have hr' := hr.ne'
  rw [consumption2_eq_pv hr]
  unfold wealth
  field_simp
  ring

/-- Two-stage decision, O&R pp. 17–21: the consumption of an optimal plan of (1.16) solves
`max u(C₁) + β u(C₂)` subject to `C₁ + C₂/(1 + r) = W` at the plan's wealth. This is what
makes consumption a function of wealth, as used in §1.2.4. -/
theorem optimum_solves_wealth_problem {u : ℝ → ℝ} {β : ℝ} {F : ℝ → ℝ} {r K1 G1 G2 : ℝ}
    {SC SK : Set ℝ} {C1 I1 C1' C2' : ℝ} (hr : 0 < 1 + r)
    (hopt : IsOptimal u β F r K1 G1 G2 SC SK C1 I1) (hC1' : C1' ∈ SC)
    (hb : C1' + C2' / (1 + r) = wealth F r K1 G1 G2 (K1 + I1)) :
    u C1' + β * u C2' ≤ utility u β F r K1 G1 G2 C1 I1 := by
  have hr' := hr.ne'
  have h2 := consumption2_budget (F := F) hr K1 G1 G2 C1' I1
  have hC2 : C2' = consumption2 F r K1 G1 G2 C1' I1 := by
    have h3 : C2' / (1 + r) = consumption2 F r K1 G1 G2 C1' I1 / (1 + r) := by linarith
    field_simp at h3
    exact h3
  have h := hopt.2.2 C1' hC1' I1 hopt.2.1
  rwa [utility, ← hC2] at h

/-- The date-1 current account, O&R (1.12), p. 22, when consumption is a demand function
`c₁` of wealth and date-2 capital is `K₂` (which Fisher separation fixes independently of
`G₁`, `G₂`): `CA₁ = F(K₁) − G₁ − (K₂ − K₁) − c₁(W)`. -/
noncomputable def ca1 (c1 : ℝ → ℝ) (F : ℝ → ℝ) (r K1 G1 G2 K2 : ℝ) : ℝ :=
  F K1 - G1 - (K2 - K1) - c1 (wealth F r K1 G1 G2 K2)

/-- O&R (1.12), p. 15: `ca1` is the current account identity with `B₁ = 0`,
`I₁ = K₂ − K₁`. -/
theorem ca1_eq_currentAccount (c1 F : ℝ → ℝ) (r K1 G1 G2 K2 : ℝ) :
    ca1 c1 F r K1 G1 G2 K2 =
      currentAccount (F K1) r 0 (c1 (wealth F r K1 G1 G2 K2)) G1 (K2 - K1) := by
  unfold ca1 currentAccount
  ring

/-- Consumption smoothing, O&R p. 22: if consumption demands `c₁, c₂` exhaust wealth
(`c₁(W) + c₂(W)/(1 + r) = W`) and both are normal (strictly increasing), a fall `d > 0`
in wealth lowers `C₁` by strictly between `0` and `d`. -/
theorem consumption_smoothing {c1 c2 : ℝ → ℝ} {r : ℝ} (hr : 0 < 1 + r)
    (hbud : ∀ W, c1 W + c2 W / (1 + r) = W) (hc1 : StrictMono c1) (hc2 : StrictMono c2)
    {W d : ℝ} (hd : 0 < d) : 0 < c1 W - c1 (W - d) ∧ c1 W - c1 (W - d) < d := by
  have hlt : W - d < W := by linarith
  have h1 := hbud W
  have h2 := hbud (W - d)
  have h3 := div_lt_div_of_pos_right (hc2 hlt) hr
  constructor
  · linarith [hc1 hlt]
  · linarith

/-- O&R p. 22: a rise in date-1 government consumption, investment unchanged, lowers the
date-1 current account, provided date-2 consumption is normal (only this half of the
book's "normal on both dates" is needed). -/
theorem ca1_strictAnti_G1 {c1 c2 F : ℝ → ℝ} {r K1 G1 G1' G2 K2 : ℝ} (hr : 0 < 1 + r)
    (hbud : ∀ W, c1 W + c2 W / (1 + r) = W) (hc2 : StrictMono c2) (h : G1 < G1') :
    ca1 c1 F r K1 G1' G2 K2 < ca1 c1 F r K1 G1 G2 K2 := by
  have hW : wealth F r K1 G1' G2 K2 = wealth F r K1 G1 G2 K2 - (G1' - G1) := by
    unfold wealth
    ring
  unfold ca1
  rw [hW]
  have h1 := hbud (wealth F r K1 G1 G2 K2)
  have h2 := hbud (wealth F r K1 G1 G2 K2 - (G1' - G1))
  have h3 := div_lt_div_of_pos_right (hc2 (show wealth F r K1 G1 G2 K2 - (G1' - G1) <
    wealth F r K1 G1 G2 K2 by linarith)) hr
  linarith

/-- O&R p. 22, Figure 1.4: starting from a balanced current account with `G₁ = 0`, a
temporary positive `G₁` produces a date-1 current account deficit when date-2
consumption is normal. -/
theorem temporary_G1_deficit {c1 c2 F : ℝ → ℝ} {r K1 G1 G2 K2 : ℝ} (hr : 0 < 1 + r)
    (hbud : ∀ W, c1 W + c2 W / (1 + r) = W) (hc2 : StrictMono c2)
    (hbal : ca1 c1 F r K1 0 G2 K2 = 0) (hG1 : 0 < G1) : ca1 c1 F r K1 G1 G2 K2 < 0 :=
  hbal ▸ ca1_strictAnti_G1 hr hbud hc2 hG1

/-- O&R p. 22: a rise in future government consumption `G₂` raises the date-1 current
account, provided date-1 consumption is normal. -/
theorem ca1_strictMono_G2 {c1 F : ℝ → ℝ} {r K1 G1 G2 G2' K2 : ℝ} (hr : 0 < 1 + r)
    (hc1 : StrictMono c1) (h : G2 < G2') :
    ca1 c1 F r K1 G1 G2 K2 < ca1 c1 F r K1 G1 G2' K2 := by
  have hW : wealth F r K1 G1 G2' K2 = wealth F r K1 G1 G2 K2 - (G2' - G2) / (1 + r) := by
    unfold wealth
    ring
  have hpos : 0 < (G2' - G2) / (1 + r) := div_pos (by linarith) hr
  unfold ca1
  rw [hW]
  have := hc1 (show wealth F r K1 G1 G2 K2 - (G2' - G2) / (1 + r) <
    wealth F r K1 G1 G2 K2 by linarith)
  linarith

/-- O&R p. 22: starting from balance with `G₂ = 0`, expected future government consumption
`G₂ > 0` produces a date-1 current account surplus when date-1 consumption is normal. -/
theorem future_G2_surplus {c1 F : ℝ → ℝ} {r K1 G1 G2 K2 : ℝ} (hr : 0 < 1 + r)
    (hc1 : StrictMono c1) (hbal : ca1 c1 F r K1 G1 0 K2 = 0) (hG2 : 0 < G2) :
    0 < ca1 c1 F r K1 G1 G2 K2 :=
  hbal ▸ ca1_strictMono_G2 hr hc1 hG2

end ObstfeldRogoff.IntertemporalTrade.Investment
