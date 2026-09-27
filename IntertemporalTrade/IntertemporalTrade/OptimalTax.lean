/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import IntertemporalTrade.Consumer
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Taxation of foreign borrowing and lending

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §1.4,
pp. 42–45, footnote 19, and Exercise 8 (pp. 57–58).

Two-country pure endowment economy. Foreign (`Foreign`) is a competitive price-taker with log
utility; its saving schedule `S₁*(r)` (p. 42) is derived from its optimisation
(`Foreign.household_optimal`). Home is a `Consumer.Household` with general strictly increasing,
strictly concave `u` and a positive derivative `u'`; its government internalises its effect on
the world rate. Market clearing gives the rate `1 + r = Y₂*/[(1 + β*)(Y₁ − C₁) + β* Y₁*]` and
the Foreign offer curve TT, O&R (1.32).

* TT passes through the endowment A with slope `−(1 + r^{A*})` (`offer_slope_endowment`), is
  strictly concave and strictly decreasing, and the laissez-faire point B lies on it; when B ≠ A
  the arc of TT between A and B lies strictly outside the laissez-faire budget line.
* Point C (the planner optimum along TT) is characterised by tangency (necessary and
  sufficient). Existence of C is **not** proved: every result about C takes a planner optimum
  `hC : IsPlannerOptimal h F c1` as a hypothesis.
* With `r^A > r^{A*}`: `Y₁ < C₁^C < C₁^B`, `r^{A*} < r^τ < r^L`, the tax `τ` is positive and
  decentralises C with a lump-sum rebate, Home gains, Foreign loses, and the tax equilibrium is
  Pareto-inefficient. Footnote 19 (`r^A < r^{A*}`): the planner lends less and lending is taxed.
* Small country: the wedge vanishes when TT is a straight line, and tends to zero as Foreign is
  scaled up.
* Exercise 8 (general `U`, ad valorem tax): `τ = 1/(ζ* − 1)`; `ζ* > 1` needs an extra
  hypothesis (`ζ* ≥ 0`, or an upward-sloping Foreign saving schedule). The exercise's reference
  to "section 1.5's model" should read §1.4.
-/

namespace ObstfeldRogoff.IntertemporalTrade.OptimalTax

open Set Filter Topology Consumer

/-- The Foreign country of O&R §1.4, p. 42: a competitive price-taker with log utility
`log C₁* + β* log C₂*` and positive endowments `Y₁*, Y₂*`. -/
structure Foreign where
  β : ℝ
  Y1 : ℝ
  Y2 : ℝ
  β_pos : 0 < β
  Y1_pos : 0 < Y1
  Y2_pos : 0 < Y2

namespace Foreign

variable (F : Foreign)

/-- Foreign saving, O&R p. 42: `S₁*(r) = β*/(1+β*) Y₁* − Y₂*/((1+β*)(1+r))`. -/
noncomputable def saving (r : ℝ) : ℝ :=
  F.β / (1 + F.β) * F.Y1 - F.Y2 / ((1 + F.β) * (1 + r))

/-- Foreign's autarky gross interest rate `1 + r^{A*} = Y₂*/(β* Y₁*)` (O&R (1.7), p. 43). -/
noncomputable def autarkyGross : ℝ := F.Y2 / (F.β * F.Y1)

/-- Foreign as a `Consumer.Household` with `u = log` (O&R p. 42). -/
noncomputable def household : Household where
  u := Real.log
  β := F.β
  Y1 := F.Y1
  Y2 := F.Y2
  β_pos := F.β_pos
  Y1_pos := F.Y1_pos
  Y2_pos := F.Y2_pos
  mono := Real.strictMonoOn_log
  concave := strictConcaveOn_log_Ioi

/-- O&R p. 42: at any `r > −1` the log household's optimum is `C₁* = Y₁* − S₁*(r)`,
`C₂* = (1 + r) β* C₁*`; so `S₁*` is Foreign's competitive saving schedule. -/
theorem household_optimal {r : ℝ} (hr : 0 < 1 + r) :
    F.household.IsOptimal r (F.Y1 - F.saving r) ((1 + r) * F.β * (F.Y1 - F.saving r)) := by
  have hβ := F.β_pos
  have hY1 := F.Y1_pos
  have hY2 := F.Y2_pos
  have hc : F.Y1 - F.saving r = (F.Y1 + F.Y2 / (1 + r)) / (1 + F.β) := by
    unfold saving
    field_simp
    ring
  have hc1 : 0 < F.Y1 - F.saving r := by rw [hc]; positivity
  refine F.household.optimal_of_euler (u' := fun c => c⁻¹)
    (fun c hc => Real.hasDerivAt_log hc.ne') (fun c hc => inv_pos.2 hc) hc1 (by positivity)
    ?_ ?_
  · change _ = F.Y2 + (1 + r) * (F.Y1 - _)
    rw [hc]
    field_simp
    ring
  · change _ = (1 + r) * F.β * _
    field_simp

/-- Foreign lends (`S₁* > 0`) exactly when the world rate exceeds its autarky rate. -/
theorem saving_pos_iff {r : ℝ} (hr : 0 < 1 + r) :
    0 < F.saving r ↔ F.autarkyGross < 1 + r := by
  have hβ := F.β_pos
  have hY1 := F.Y1_pos
  have e : F.saving r = (F.β * F.Y1 * (1 + r) - F.Y2) / ((1 + F.β) * (1 + r)) := by
    unfold saving
    field_simp
  rw [e, autarkyGross, div_lt_iff₀ (by positivity), div_pos_iff_of_pos_right (by positivity)]
  constructor <;> intro h <;> linarith

/-! ### The Foreign offer curve TT -/

/-- The denominator `(1 + β*)(Y₁ − C₁) + β* Y₁*` of O&R p. 43; TT is defined where it is
positive. -/
def denom (Y1 c1 : ℝ) : ℝ := (1 + F.β) * (Y1 - c1) + F.β * F.Y1

/-- The world gross rate as seen by Home's government, O&R p. 43:
`1 + r = Y₂*/[(1 + β*)(Y₁ − C₁) + β* Y₁*]`. -/
noncomputable def rate (Y1 c1 : ℝ) : ℝ := F.Y2 / F.denom Y1 c1

/-- The Foreign offer curve TT, O&R (1.32), p. 43:
`C₂ = Y₂ + Y₂*(Y₁ − C₁)/[(1 + β*)(Y₁ − C₁) + β* Y₁*]`. -/
noncomputable def offer (Y1 Y2 c1 : ℝ) : ℝ := Y2 + F.Y2 * (Y1 - c1) / F.denom Y1 c1

/-- Market clearing, O&R p. 43: Home borrowing `C₁ − Y₁` equals Foreign saving `S₁*(r)` iff
`1 + r = Y₂*/[(1 + β*)(Y₁ − C₁) + β* Y₁*]`. -/
theorem market_clearing_iff {Y1 c1 r : ℝ} (hr : 0 < 1 + r) :
    c1 - Y1 = F.saving r ↔ 1 + r = F.rate Y1 c1 := by
  have hβ := F.β_pos
  have hY2 := F.Y2_pos
  unfold saving rate denom
  constructor
  · intro h
    have hD : (1 + F.β) * (Y1 - c1) + F.β * F.Y1 = F.Y2 / (1 + r) := by
      have h' : Y1 - c1 = -(F.β / (1 + F.β) * F.Y1 - F.Y2 / ((1 + F.β) * (1 + r))) := by
        linarith
      rw [h']
      field_simp
      ring
    rw [hD]
    field_simp
  · intro h
    have hD : (1 + F.β) * (Y1 - c1) + F.β * F.Y1 ≠ 0 := by
      intro h0
      rw [h0, div_zero] at h
      linarith
    rw [h]
    field_simp
    ring

/-- At a market-clearing point the denominator is positive: it equals `Y₂*/(1 + r)`. -/
theorem denom_pos_of_clearing {Y1 c1 r : ℝ} (hr : 0 < 1 + r) (h : c1 - Y1 = F.saving r) :
    0 < F.denom Y1 c1 := by
  have h1 := (F.market_clearing_iff hr).1 h
  unfold rate at h1
  by_contra hle
  push Not at hle
  have : F.Y2 / F.denom Y1 c1 ≤ 0 := div_nonpos_of_nonneg_of_nonpos F.Y2_pos.le hle
  linarith

/-- TT is Home's budget line at the rate it induces: `C₂ = Y₂ − (1 + r(C₁))(C₁ − Y₁)`,
O&R p. 43. -/
theorem offer_eq_budget (Y1 Y2 c1 : ℝ) :
    F.offer Y1 Y2 c1 = Y2 - F.rate Y1 c1 * (c1 - Y1) := by
  unfold offer rate
  ring

/-- TT passes through the endowment point A, O&R Figure 1.11. -/
theorem offer_endowment (Y1 Y2 : ℝ) : F.offer Y1 Y2 Y1 = Y2 := by
  simp [offer]

/-- At the endowment point the induced world rate is Foreign's autarky rate. -/
theorem rate_endowment (Y1 : ℝ) : F.rate Y1 Y1 = F.autarkyGross := by
  simp [rate, denom, autarkyGross]

/-- The slope of TT, from differentiating (1.32): `dC₂/dC₁ = −Y₂* β* Y₁* / D²` where `D` is
the denominator. -/
theorem hasDerivAt_offer {Y1 c1 : ℝ} (Y2 : ℝ) (hD : F.denom Y1 c1 ≠ 0) :
    HasDerivAt (F.offer Y1 Y2) (-(F.Y2 * (F.β * F.Y1)) / F.denom Y1 c1 ^ 2) c1 := by
  have hn : HasDerivAt (fun s => F.Y2 * (Y1 - s)) (F.Y2 * (-1)) c1 :=
    ((hasDerivAt_id c1).const_sub Y1).const_mul F.Y2
  have hd : HasDerivAt (fun s => F.denom Y1 s) ((1 + F.β) * (-1)) c1 :=
    (((hasDerivAt_id c1).const_sub Y1).const_mul (1 + F.β)).add_const (F.β * F.Y1)
  have hq := (hn.div hd hD).const_add Y2
  refine hq.congr_deriv ?_
  unfold denom at hD ⊢
  field_simp
  ring

/-- **O&R p. 43**: the slope of TT at the endowment point A is
`−Y₂*/(β* Y₁*) = −(1 + r^{A*})`. -/
theorem offer_slope_endowment (Y1 Y2 : ℝ) :
    HasDerivAt (F.offer Y1 Y2) (-F.autarkyGross) Y1 := by
  have hD : F.denom Y1 Y1 = F.β * F.Y1 := by simp [denom]
  have hc : F.β * F.Y1 ≠ 0 := (mul_pos F.β_pos F.Y1_pos).ne'
  refine (F.hasDerivAt_offer Y2 (hD ▸ hc)).congr_deriv ?_
  rw [hD, autarkyGross]
  field_simp

/-- TT in the form `K − M/D`: `C₂ = Y₂ + Y₂*/(1+β*) − (Y₂* β* Y₁*/(1+β*))/D`. -/
theorem offer_eq_alt {Y1 c1 : ℝ} (Y2 : ℝ) (hD : F.denom Y1 c1 ≠ 0) :
    F.offer Y1 Y2 c1 = Y2 + F.Y2 / (1 + F.β) -
      F.Y2 * (F.β * F.Y1) / (1 + F.β) / F.denom Y1 c1 := by
  have hβ := F.β_pos
  have e : Y1 - c1 = (F.denom Y1 c1 - F.β * F.Y1) / (1 + F.β) := by
    unfold denom
    field_simp
    ring
  unfold offer
  rw [e]
  field_simp
  ring

/-- The domain `D > 0` of TT is convex (a half-line). -/
theorem convex_denom_pos (Y1 : ℝ) : Convex ℝ {c1 | 0 < F.denom Y1 c1} := by
  intro x hx y hy a b ha hb hab
  simp only [mem_ofPred_eq, denom, smul_eq_mul] at hx hy ⊢
  have e : (1 + F.β) * (Y1 - (a * x + b * y)) + F.β * F.Y1 =
      a * ((1 + F.β) * (Y1 - x) + F.β * F.Y1) + b * ((1 + F.β) * (Y1 - y) + F.β * F.Y1) := by
    linear_combination (-(1 + F.β) * Y1 - F.β * F.Y1) * hab
  rw [e]
  rcases ha.lt_or_eq with ha' | ha'
  · positivity
  · subst ha'
    simp only [zero_add] at hab
    subst hab
    simpa using hy

/-- **TT is strictly concave** in `C₁` on its domain `(1 + β*)(Y₁ − C₁) + β* Y₁* > 0`
(the shape drawn in O&R Figure 1.11). -/
theorem offer_strictConcaveOn (Y1 Y2 : ℝ) :
    StrictConcaveOn ℝ {c1 | 0 < F.denom Y1 c1} (F.offer Y1 Y2) := by
  refine ⟨F.convex_denom_pos Y1, fun x hx y hy hxy a b ha hb hab => ?_⟩
  simp only [mem_ofPred_eq] at hx hy
  have hβ := F.β_pos
  have hM : 0 < F.Y2 * (F.β * F.Y1) / (1 + F.β) := by
    have := F.Y2_pos; have := F.Y1_pos; positivity
  have hz : F.denom Y1 (a • x + b • y) = a * F.denom Y1 x + b * F.denom Y1 y := by
    simp only [denom, smul_eq_mul]
    linear_combination (-(1 + F.β) * Y1 - F.β * F.Y1) * hab
  have hzpos : 0 < a * F.denom Y1 x + b * F.denom Y1 y := by positivity
  rw [F.offer_eq_alt Y2 hx.ne', F.offer_eq_alt Y2 hy.ne', F.offer_eq_alt Y2 (hz ▸ hzpos.ne'),
    hz]
  set M := F.Y2 * (F.β * F.Y1) / (1 + F.β)
  set p := F.denom Y1 x
  set q := F.denom Y1 y
  have hpq : p ≠ q := by
    intro he
    apply hxy
    simp only [p, q, denom] at he
    have : (1 + F.β) * (y - x) = 0 := by linarith
    rcases mul_eq_zero.1 this with h | h
    · linarith
    · linarith
  -- strict convexity of `1/D` along the affine `D`
  have key : 1 / (a * p + b * q) < a / p + b / q := by
    rw [div_add_div _ _ hx.ne' hy.ne', div_lt_div_iff₀ hzpos (by positivity)]
    have hsq : 0 < (p - q) ^ 2 := by
      have : p - q ≠ 0 := sub_ne_zero.2 hpq
      positivity
    have hb' : b = 1 - a := by linarith
    subst hb'
    nlinarith [mul_pos ha hb]
  have e1 : M / (a * p + b * q) = M * (1 / (a * p + b * q)) := by ring
  have e2 : a * (Y2 + F.Y2 / (1 + F.β) - M / p) + b * (Y2 + F.Y2 / (1 + F.β) - M / q) =
      (a + b) * (Y2 + F.Y2 / (1 + F.β)) - M * (a / p + b / q) := by ring
  simp only [smul_eq_mul]
  rw [e1, e2, hab]
  nlinarith [mul_lt_mul_of_pos_left key hM]

/-- TT slopes down: it is strictly decreasing on its domain. -/
theorem offer_strictAntiOn (Y1 Y2 : ℝ) :
    StrictAntiOn (F.offer Y1 Y2) {c1 | 0 < F.denom Y1 c1} := by
  intro x hx y hy hxy
  simp only [mem_ofPred_eq] at hx hy
  have hβ := F.β_pos
  have hM : 0 < F.Y2 * (F.β * F.Y1) / (1 + F.β) := by
    have := F.Y2_pos; have := F.Y1_pos; positivity
  rw [F.offer_eq_alt Y2 hx.ne', F.offer_eq_alt Y2 hy.ne']
  have hlt : F.denom Y1 y < F.denom Y1 x := by
    simp only [denom]; nlinarith
  have := div_lt_div_of_pos_left hM hy hlt
  linarith

/-- The world rate rises with Home borrowing (O&R p. 43: "the world interest rate rises as
`C₁` rises"). -/
theorem rate_strictMonoOn (Y1 : ℝ) :
    StrictMonoOn (F.rate Y1) {c1 | 0 < F.denom Y1 c1} := by
  intro x hx y hy hxy
  simp only [mem_ofPred_eq] at hx hy
  have hβ := F.β_pos
  have hlt : F.denom Y1 y < F.denom Y1 x := by
    simp only [denom]; nlinarith
  exact div_lt_div_of_pos_left F.Y2_pos hy hlt

end Foreign

open Foreign

/-! ### Laissez-faire equilibrium (point B) -/

/-- A laissez-faire equilibrium, O&R p. 43: Home's price-taking households optimise at the
world rate `r` and Home borrowing equals Foreign saving. -/
def IsLaissezFaire (h : Household) (F : Foreign) (r c1 c2 : ℝ) : Prop :=
  0 < 1 + r ∧ h.IsOptimal r c1 c2 ∧ c1 - h.Y1 = F.saving r

/-- **Point B lies on TT** (O&R p. 43): the laissez-faire allocation is on the Foreign offer
curve, at the rate TT induces. -/
theorem laissezFaire_on_offer {h : Household} {F : Foreign} {r c1 c2 : ℝ}
    (hB : IsLaissezFaire h F r c1 c2) :
    0 < F.denom h.Y1 c1 ∧ 1 + r = F.rate h.Y1 c1 ∧ c2 = F.offer h.Y1 h.Y2 c1 := by
  obtain ⟨hr, ho, hs⟩ := hB
  have hrate := (F.market_clearing_iff hr).1 hs
  refine ⟨F.denom_pos_of_clearing hr hs, hrate, ?_⟩
  rw [h.optimal_binds ho, F.offer_eq_budget, ← hrate]
  ring

/-- A derivative of a strictly concave `u` is antitone on `(0, ∞)`. -/
theorem deriv_anti {h : Household} {u' : ℝ → ℝ} (hu : ∀ c, 0 < c → HasDerivAt h.u (u' c) c)
    {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : u' y ≤ u' x := by
  rcases hxy.lt_or_eq with hlt | rfl
  · exact (deriv_lt_of_strictConcave h.concave (mem_Ioi.2 hx) (mem_Ioi.2 (hx.trans hlt)) hlt
      (hu x hx) (hu y (hx.trans hlt))).le
  · exact le_rfl

/-- **Home borrows under laissez-faire** (the case of O&R Figure 1.11): if Home's autarky gross
rate `u'(Y₁)/(β u'(Y₂))` exceeds Foreign's, `1 + r^A > 1 + r^{A*}`, then `C₁ > Y₁` at B. -/
theorem laissezFaire_borrows {h : Household} {F : Foreign} {u' : ℝ → ℝ}
    (hu : ∀ c, 0 < c → HasDerivAt h.u (u' c) c) (hpos : ∀ c, 0 < c → 0 < u' c)
    (hA : F.autarkyGross < u' h.Y1 / (h.β * u' h.Y2)) {r c1 c2 : ℝ}
    (hB : IsLaissezFaire h F r c1 c2) : h.Y1 < c1 := by
  obtain ⟨hr, ho, hs⟩ := hB
  by_contra hle
  push Not at hle
  have hS : ¬ 0 < F.saving r := by rw [← hs]; linarith
  rw [F.saving_pos_iff hr] at hS
  push Not at hS
  have he := h.euler_of_optimal hu ho
  have hb := h.optimal_binds ho
  obtain ⟨⟨hc1, hc2, -⟩, -⟩ := ho
  have hβ := h.β_pos
  have hY2 := hpos _ h.Y2_pos
  have h1 : u' h.Y1 ≤ u' c1 := deriv_anti hu hc1 hle
  have h2 : u' c2 ≤ u' h.Y2 := deriv_anti hu h.Y2_pos (by rw [hb]; nlinarith)
  rw [lt_div_iff₀ (by positivity)] at hA
  have h3 : (1 + r) * h.β * u' c2 ≤ (1 + r) * h.β * u' h.Y2 :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  have h4 : (1 + r) * h.β * u' h.Y2 ≤ F.autarkyGross * (h.β * u' h.Y2) := by
    have : 0 ≤ h.β * u' h.Y2 := by positivity
    nlinarith
  linarith

/-- Under laissez-faire the world rate exceeds Foreign's autarky rate, `r^L > r^{A*}`
(O&R p. 43). -/
theorem laissezFaire_rate_gt {h : Household} {F : Foreign} {u' : ℝ → ℝ}
    (hu : ∀ c, 0 < c → HasDerivAt h.u (u' c) c) (hpos : ∀ c, 0 < c → 0 < u' c)
    (hA : F.autarkyGross < u' h.Y1 / (h.β * u' h.Y2)) {r c1 c2 : ℝ}
    (hB : IsLaissezFaire h F r c1 c2) : F.autarkyGross < 1 + r := by
  have hb := laissezFaire_borrows hu hpos hA hB
  obtain ⟨hr, -, hs⟩ := hB
  exact (F.saving_pos_iff hr).1 (by rw [← hs]; linarith)

/-- **Part of TT lies strictly outside the laissez-faire budget line** (O&R p. 43): if B differs
from A, every point of TT strictly between A and B lies strictly above the line through A with
slope `−(1 + r^L)`. -/
theorem offer_above_laissezFaire_line {h : Household} {F : Foreign} {r c1 c2 : ℝ}
    (hB : IsLaissezFaire h F r c1 c2) (hne : c1 ≠ h.Y1) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) :
    h.Y2 + (1 + r) * (h.Y1 - (θ * h.Y1 + (1 - θ) * c1)) <
      F.offer h.Y1 h.Y2 (θ * h.Y1 + (1 - θ) * c1) := by
  obtain ⟨hD, hrate, hc2⟩ := laissezFaire_on_offer hB
  have hA : h.Y1 ∈ {c | 0 < F.denom h.Y1 c} := by
    simp only [mem_ofPred_eq, denom, sub_self, mul_zero, zero_add]
    exact mul_pos F.β_pos F.Y1_pos
  have hcc := (F.offer_strictConcaveOn h.Y1 h.Y2).2 hA hD hne.symm hθ0 (by linarith : 0 < 1 - θ)
    (by ring)
  simp only [smul_eq_mul, offer_endowment] at hcc
  have hb := h.optimal_binds hB.2.1
  rw [← hc2, hb] at hcc
  nlinarith

/-! ### The planner's problem and the optimal tax (point C) -/

/-- Points of TT available to Home's planner: `C₁ > 0`, the TT denominator positive, and
`C₂ > 0` on TT (O&R p. 43). -/
def PlannerFeasible (h : Household) (F : Foreign) (c1 : ℝ) : Prop :=
  0 < c1 ∧ 0 < F.denom h.Y1 c1 ∧ 0 < F.offer h.Y1 h.Y2 c1

/-- Point C, O&R p. 43: `C₁` maximises Home utility along the Foreign offer curve TT. -/
def IsPlannerOptimal (h : Household) (F : Foreign) (c1 : ℝ) : Prop :=
  PlannerFeasible h F c1 ∧ ∀ d1, PlannerFeasible h F d1 →
    h.utility d1 (F.offer h.Y1 h.Y2 d1) ≤ h.utility c1 (F.offer h.Y1 h.Y2 c1)

/-- The absolute slope of TT, `−dC₂/dC₁ = Y₂* β* Y₁*/D²` (differentiating (1.32)). -/
noncomputable def offerMRS (F : Foreign) (Y1 c1 : ℝ) : ℝ :=
  F.Y2 * (F.β * F.Y1) / F.denom Y1 c1 ^ 2

/-- The derivative of Home utility along TT. -/
theorem hasDerivAt_utility_offer {h : Household} {F : Foreign} {u' : ℝ → ℝ}
    (hu : ∀ c, 0 < c → HasDerivAt h.u (u' c) c) {c1 : ℝ} (hc : PlannerFeasible h F c1) :
    HasDerivAt (fun s => h.utility s (F.offer h.Y1 h.Y2 s))
      (u' c1 - h.β * u' (F.offer h.Y1 h.Y2 c1) * offerMRS F h.Y1 c1) c1 := by
  obtain ⟨hc1, hD, hc2⟩ := hc
  have h2 := ((hu _ hc2).comp c1 (F.hasDerivAt_offer h.Y2 hD.ne')).const_mul h.β
  refine ((hu c1 hc1).add h2).congr_deriv ?_
  unfold offerMRS
  ring

/-- **Tangency at C** (O&R p. 43, Figure 1.11): at the planner optimum the indifference curve is
tangent to TT, `u'(C₁) = β u'(C₂) · Y₂* β* Y₁*/D²`. -/
theorem planner_tangency {h : Household} {F : Foreign} {u' : ℝ → ℝ}
    (hu : ∀ c, 0 < c → HasDerivAt h.u (u' c) c) {c1 : ℝ} (hC : IsPlannerOptimal h F c1) :
    u' c1 = h.β * u' (F.offer h.Y1 h.Y2 c1) * offerMRS F h.Y1 c1 := by
  obtain ⟨hc, hmax⟩ := hC
  have hd := hasDerivAt_utility_offer hu hc
  obtain ⟨hc1, hD, hc2⟩ := hc
  have hDc : Continuous fun s => F.denom h.Y1 s := by unfold denom; fun_prop
  have hoc : ContinuousAt (F.offer h.Y1 h.Y2) c1 :=
    (F.hasDerivAt_offer h.Y2 hD.ne').continuousAt
  have hloc : IsLocalMax (fun s => h.utility s (F.offer h.Y1 h.Y2 s)) c1 := by
    filter_upwards [Ioi_mem_nhds hc1, (hDc.tendsto c1).eventually (lt_mem_nhds hD),
      hoc.eventually (lt_mem_nhds hc2)] with s hs1 hs2 hs3
    exact hmax s ⟨hs1, hs2, hs3⟩
  have := hloc.hasDerivAt_eq_zero hd
  linarith

/-- **Sufficiency of tangency**: a planner-feasible point satisfying the tangency condition is the
planner optimum (TT is concave and `u` concave increasing). -/
theorem plannerOptimal_of_tangency {h : Household} {F : Foreign} {u' : ℝ → ℝ}
    (hu : ∀ c, 0 < c → HasDerivAt h.u (u' c) c) (hpos : ∀ c, 0 < c → 0 < u' c) {c1 : ℝ}
    (hc : PlannerFeasible h F c1)
    (ht : u' c1 = h.β * u' (F.offer h.Y1 h.Y2 c1) * offerMRS F h.Y1 c1) :
    IsPlannerOptimal h F c1 := by
  refine ⟨hc, fun d1 hd => ?_⟩
  obtain ⟨hc1, hD, hc2⟩ := hc
  obtain ⟨hd1, hDd, hd2⟩ := hd
  have t1 := concave_le_tangent h.concave.concaveOn (mem_Ioi.2 hc1) (mem_Ioi.2 hd1) (hu c1 hc1)
  have t2 := concave_le_tangent h.concave.concaveOn (mem_Ioi.2 hc2) (mem_Ioi.2 hd2) (hu _ hc2)
  have t3 := concave_le_tangent (F.offer_strictConcaveOn h.Y1 h.Y2).concaveOn hD hDd
    (F.hasDerivAt_offer h.Y2 hD.ne')
  have hp := hpos _ hc2
  have hβ := h.β_pos
  have hnn : 0 ≤ h.β * u' (F.offer h.Y1 h.Y2 c1) := by positivity
  have key := mul_le_mul_of_nonneg_left t3 hnn
  have e : -(F.Y2 * (F.β * F.Y1)) / F.denom h.Y1 c1 ^ 2 = -offerMRS F h.Y1 c1 := by
    unfold offerMRS; ring
  rw [e] at key
  unfold Household.utility
  nlinarith

/-- **The planner borrows, but less than under laissez-faire** (O&R p. 43–44, Figure 1.11):
if `r^A > r^{A*}`, the planner optimum C satisfies `Y₁ < C₁^C < C₁^B`. -/
theorem planner_between {h : Household} {F : Foreign} {u' : ℝ → ℝ}
    (hu : ∀ c, 0 < c → HasDerivAt h.u (u' c) c) (hpos : ∀ c, 0 < c → 0 < u' c)
    (hA : F.autarkyGross < u' h.Y1 / (h.β * u' h.Y2)) {r b1 b2 c1 : ℝ}
    (hB : IsLaissezFaire h F r b1 b2) (hC : IsPlannerOptimal h F c1) :
    h.Y1 < c1 ∧ c1 < b1 := by
  have ht := planner_tangency hu hC
  obtain ⟨⟨hc1, hD, hc2⟩, -⟩ := hC
  have hβ := h.β_pos
  have hc0 : 0 < F.β * F.Y1 := mul_pos F.β_pos F.Y1_pos
  have hY2s := F.Y2_pos
  have hβs := F.β_pos
  have hdom : ∀ x, 0 < F.denom h.Y1 x → x ∈ {c | 0 < F.denom h.Y1 c} := fun x hx => hx
  constructor
  · by_contra hle
    push Not at hle
    have hDc : F.β * F.Y1 ≤ F.denom h.Y1 c1 := by unfold denom; nlinarith
    have hm : offerMRS F h.Y1 c1 ≤ F.autarkyGross := by
      unfold offerMRS Foreign.autarkyGross
      rw [div_le_div_iff₀ (by positivity) hc0]
      have : (F.β * F.Y1) ^ 2 ≤ F.denom h.Y1 c1 ^ 2 := by nlinarith
      nlinarith
    have hoY : F.offer h.Y1 h.Y2 h.Y1 ≤ F.offer h.Y1 h.Y2 c1 := by
      rcases hle.lt_or_eq with hlt | heq
      · have hA' : 0 < F.denom h.Y1 h.Y1 := by simpa [denom] using hc0
        exact (F.offer_strictAntiOn h.Y1 h.Y2 (hdom _ hD) (hdom _ hA') hlt).le
      · rw [heq]
    rw [offer_endowment] at hoY
    have h1 : u' h.Y1 ≤ u' c1 := deriv_anti hu hc1 hle
    have h2 : u' (F.offer h.Y1 h.Y2 c1) ≤ u' h.Y2 := deriv_anti hu h.Y2_pos hoY
    have hp2 := hpos _ hc2
    have hpY := hpos _ h.Y2_pos
    rw [lt_div_iff₀ (by positivity)] at hA
    have h3 : h.β * u' (F.offer h.Y1 h.Y2 c1) * offerMRS F h.Y1 c1 ≤
        h.β * u' h.Y2 * F.autarkyGross := by
      have hm0 : 0 ≤ offerMRS F h.Y1 c1 := by unfold offerMRS; positivity
      have := mul_le_mul_of_nonneg_left h2 hβ.le
      calc h.β * u' (F.offer h.Y1 h.Y2 c1) * offerMRS F h.Y1 c1
          ≤ h.β * u' h.Y2 * offerMRS F h.Y1 c1 := mul_le_mul_of_nonneg_right this hm0
        _ ≤ h.β * u' h.Y2 * F.autarkyGross := mul_le_mul_of_nonneg_left hm (by positivity)
    nlinarith
  · have hbY := laissezFaire_borrows hu hpos hA hB
    obtain ⟨hDB, hrate, hb2⟩ := laissezFaire_on_offer hB
    obtain ⟨hr, hoB, -⟩ := hB
    have he := h.euler_of_optimal hu hoB
    obtain ⟨⟨hb1, hb2pos, -⟩, -⟩ := hoB
    by_contra hle
    push Not at hle
    have hDB' : F.denom h.Y1 b1 < F.β * F.Y1 := by unfold denom; nlinarith
    have hDCB : F.denom h.Y1 c1 ≤ F.denom h.Y1 b1 := by unfold denom; nlinarith
    have hm : 1 + r < offerMRS F h.Y1 c1 := by
      rw [hrate]
      unfold offerMRS rate
      rw [div_lt_div_iff₀ hDB (by positivity)]
      have : F.denom h.Y1 c1 ^ 2 ≤ F.denom h.Y1 b1 ^ 2 := by nlinarith
      have h6 : F.denom h.Y1 b1 ^ 2 < F.β * F.Y1 * F.denom h.Y1 b1 := by nlinarith
      have h7 := mul_le_mul_of_nonneg_left this hY2s.le
      have h8 := mul_lt_mul_of_pos_left h6 hY2s
      have h5 : F.Y2 * F.denom h.Y1 c1 ^ 2 < F.Y2 * (F.β * F.Y1) * F.denom h.Y1 b1 := by
        linarith
      exact h5
    have hoC : F.offer h.Y1 h.Y2 c1 ≤ b2 := by
      rw [hb2]
      rcases hle.lt_or_eq with hlt | heq
      · exact (F.offer_strictAntiOn h.Y1 h.Y2 (hdom _ hDB) (hdom _ hD) hlt).le
      · rw [heq]
    have h1 : u' c1 ≤ u' b1 := deriv_anti hu hb1 hle
    have h2 : u' b2 ≤ u' (F.offer h.Y1 h.Y2 c1) := deriv_anti hu hc2 hoC
    have hpb := hpos _ hb2pos
    have h3 : h.β * u' b2 * (1 + r) < h.β * u' (F.offer h.Y1 h.Y2 c1) * offerMRS F h.Y1 c1 := by
      calc h.β * u' b2 * (1 + r) < h.β * u' b2 * offerMRS F h.Y1 c1 :=
            mul_lt_mul_of_pos_left hm (by positivity)
        _ ≤ h.β * u' (F.offer h.Y1 h.Y2 c1) * offerMRS F h.Y1 c1 := by
            have hm0 : 0 ≤ offerMRS F h.Y1 c1 := by unfold offerMRS; positivity
            exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hβ.le) hm0
    nlinarith

/-- **The tax lowers the world rate**, O&R p. 44: `r^{A*} < r^τ < r^L`, where `1 + r^τ` is the
world rate TT induces at the planner optimum C. -/
theorem rate_ordering {h : Household} {F : Foreign} {u' : ℝ → ℝ}
    (hu : ∀ c, 0 < c → HasDerivAt h.u (u' c) c) (hpos : ∀ c, 0 < c → 0 < u' c)
    (hA : F.autarkyGross < u' h.Y1 / (h.β * u' h.Y2)) {r b1 b2 c1 : ℝ}
    (hB : IsLaissezFaire h F r b1 b2) (hC : IsPlannerOptimal h F c1) :
    F.autarkyGross < F.rate h.Y1 c1 ∧ F.rate h.Y1 c1 < 1 + r := by
  obtain ⟨h1, h2⟩ := planner_between hu hpos hA hB hC
  obtain ⟨hDB, hrate, -⟩ := laissezFaire_on_offer hB
  have hDA : 0 < F.denom h.Y1 h.Y1 := by simpa [denom] using mul_pos F.β_pos F.Y1_pos
  have hD := hC.1.2.1
  refine ⟨?_, ?_⟩
  · rw [← F.rate_endowment h.Y1]
    exact F.rate_strictMonoOn h.Y1 hDA hD h1
  · rw [hrate]
    exact F.rate_strictMonoOn h.Y1 hD hDB h2

/-- The optimal (additive) tax on borrowing, O&R p. 43–44: the wedge
`τ = −(slope of TT at C) − (1 + r^τ)` between Home's MRS and the world gross rate. -/
noncomputable def optimalTax (F : Foreign) (Y1 c1 : ℝ) : ℝ :=
  offerMRS F Y1 c1 - F.rate Y1 c1

/-- Closed form of the optimal tax: `τ = (1 + β*) Y₂* (C₁ − Y₁)/D²`; it has the sign of Home
borrowing at C. -/
theorem optimalTax_eq (F : Foreign) {Y1 c1 : ℝ} (hD : F.denom Y1 c1 ≠ 0) :
    optimalTax F Y1 c1 = (1 + F.β) * F.Y2 * (c1 - Y1) / F.denom Y1 c1 ^ 2 := by
  unfold optimalTax offerMRS rate
  have e : F.β * F.Y1 = F.denom Y1 c1 - (1 + F.β) * (Y1 - c1) := by unfold denom; ring
  rw [e]
  field_simp
  ring

/-- **The optimal policy taxes borrowing** (O&R p. 43–44): when `r^A > r^{A*}` the wedge
`τ` at C is strictly positive. -/
theorem optimalTax_pos {h : Household} {F : Foreign} {u' : ℝ → ℝ}
    (hu : ∀ c, 0 < c → HasDerivAt h.u (u' c) c) (hpos : ∀ c, 0 < c → 0 < u' c)
    (hA : F.autarkyGross < u' h.Y1 / (h.β * u' h.Y2)) {r b1 b2 c1 : ℝ}
    (hB : IsLaissezFaire h F r b1 b2) (hC : IsPlannerOptimal h F c1) :
    0 < optimalTax F h.Y1 c1 := by
  have h1 := (planner_between hu hpos hA hB hC).1
  have hD := hC.1.2.1
  rw [optimalTax_eq F hD.ne']
  have := F.β_pos
  have := F.Y2_pos
  have : 0 < c1 - h.Y1 := by linarith
  positivity

/-- A Home resident's problem under the tax, O&R p. 44: gross borrowing rate `R + τ`, where `R`
is the world gross rate, and a lump-sum rebate `T` received at date 2. -/
def ResidentOptimal (h : Household) (R τ T c1 c2 : ℝ) : Prop :=
  (0 < c1 ∧ 0 < c2 ∧ c2 ≤ h.Y2 + T + (R + τ) * (h.Y1 - c1)) ∧
    ∀ d1 d2, 0 < d1 → 0 < d2 → d2 ≤ h.Y2 + T + (R + τ) * (h.Y1 - d1) →
      h.utility d1 d2 ≤ h.utility c1 c2

/-- **The tax decentralises C** (O&R p. 43–44): with world gross rate `R = 1 + r^τ` read off TT
at C, tax `τ = optimalTax` and rebate `T = τ (C₁ − Y₁)`, price-taking residents choose C;
Foreign's market clears at `r^τ`; and Home's trade is balanced at the world rate,
`Y₂ − C₂ = (1 + r^τ)(C₁ − Y₁)`. -/
theorem tax_decentralises {h : Household} {F : Foreign} {u' : ℝ → ℝ}
    (hu : ∀ c, 0 < c → HasDerivAt h.u (u' c) c) (hpos : ∀ c, 0 < c → 0 < u' c) {c1 : ℝ}
    (hC : IsPlannerOptimal h F c1) :
    ResidentOptimal h (F.rate h.Y1 c1) (optimalTax F h.Y1 c1)
        (optimalTax F h.Y1 c1 * (c1 - h.Y1)) c1 (F.offer h.Y1 h.Y2 c1) ∧
      c1 - h.Y1 = F.saving (F.rate h.Y1 c1 - 1) ∧
      h.Y2 - F.offer h.Y1 h.Y2 c1 = F.rate h.Y1 c1 * (c1 - h.Y1) := by
  have ht := planner_tangency hu hC
  obtain ⟨⟨hc1, hD, hc2⟩, -⟩ := hC
  have hR : 0 < F.rate h.Y1 c1 := div_pos F.Y2_pos hD
  set R := F.rate h.Y1 c1
  set τ := optimalTax F h.Y1 c1
  set c2 := F.offer h.Y1 h.Y2 c1
  have hRτ : R + τ = offerMRS F h.Y1 c1 := by simp only [τ, optimalTax]; ring
  have hbud : c2 = h.Y2 + τ * (c1 - h.Y1) + (R + τ) * (h.Y1 - c1) := by
    simp only [c2, R, offer_eq_budget]; ring
  refine ⟨⟨⟨hc1, hc2, hbud.le⟩, fun d1 d2 hd1 hd2 hdb => ?_⟩, ?_, ?_⟩
  · have t1 := concave_le_tangent h.concave.concaveOn (mem_Ioi.2 hc1) (mem_Ioi.2 hd1)
      (hu c1 hc1)
    have t2 := concave_le_tangent h.concave.concaveOn (mem_Ioi.2 hc2) (mem_Ioi.2 hd2)
      (hu c2 hc2)
    have hp := hpos c2 hc2
    have hβ := h.β_pos
    have hdiff : d2 - c2 ≤ -((R + τ) * (d1 - c1)) := by rw [hbud] at *; linarith
    have hnn : 0 ≤ h.β * u' c2 := by positivity
    have key := mul_le_mul_of_nonneg_left hdiff hnn
    rw [hRτ] at key
    unfold Household.utility
    nlinarith
  · exact (F.market_clearing_iff (by linarith)).2 (by ring)
  · simp only [c2, R, offer_eq_budget]; ring

/-- **Home gains from the tax** (O&R p. 43–44): if `r^A > r^{A*}`, Home utility at C strictly
exceeds its laissez-faire utility at B. -/
theorem home_gains {h : Household} {F : Foreign} {u' : ℝ → ℝ}
    (hu : ∀ c, 0 < c → HasDerivAt h.u (u' c) c) (hpos : ∀ c, 0 < c → 0 < u' c)
    (hA : F.autarkyGross < u' h.Y1 / (h.β * u' h.Y2)) {r b1 b2 c1 : ℝ}
    (hB : IsLaissezFaire h F r b1 b2) (hC : IsPlannerOptimal h F c1) :
    h.utility b1 b2 < h.utility c1 (F.offer h.Y1 h.Y2 c1) := by
  have hbY := laissezFaire_borrows hu hpos hA hB
  obtain ⟨hDB, hrate, hb2⟩ := laissezFaire_on_offer hB
  have hoB := hB.2.1
  have he := h.euler_of_optimal hu hoB
  obtain ⟨⟨hb1, hb2pos, -⟩, -⟩ := hoB
  have hfeas : PlannerFeasible h F b1 := ⟨hb1, hDB, hb2 ▸ hb2pos⟩
  have hle := hC.2 b1 hfeas
  rw [← hb2] at hle
  refine lt_of_le_of_ne hle fun heq => ?_
  -- if utilities were equal, B would be a planner optimum, so tangency would hold at B
  have hBopt : IsPlannerOptimal h F b1 :=
    ⟨hfeas, fun d1 hd => by rw [← hb2, heq]; exact hC.2 d1 hd⟩
  have ht := planner_tangency hu hBopt
  rw [← hb2] at ht
  have hc0 : 0 < F.β * F.Y1 := mul_pos F.β_pos F.Y1_pos
  have hDB' : F.denom h.Y1 b1 < F.β * F.Y1 := by unfold denom; nlinarith [F.β_pos]
  have hm : 1 + r < offerMRS F h.Y1 b1 := by
    rw [hrate]
    unfold offerMRS rate
    rw [div_lt_div_iff₀ hDB (by positivity)]
    have := F.Y2_pos
    have h6 : F.denom h.Y1 b1 ^ 2 < F.β * F.Y1 * F.denom h.Y1 b1 := by nlinarith
    nlinarith
  have hp := hpos _ hb2pos
  have hβ := h.β_pos
  have : h.β * u' b2 * (1 + r) < h.β * u' b2 * offerMRS F h.Y1 b1 :=
    mul_lt_mul_of_pos_left hm (by positivity)
  nlinarith

/-- **Revealed preference**: a strict lender at rate `r` is strictly better off at any higher
rate `r'` (used for Foreign's welfare loss, O&R p. 44–45). -/
theorem utility_lt_of_lender {h : Household} {r r' c1 c2 d1 d2 : ℝ}
    (hc : h.IsOptimal r c1 c2) (hd : h.IsOptimal r' d1 d2) (hrr : r < r')
    (hlend : c1 < h.Y1) : h.utility c1 c2 < h.utility d1 d2 := by
  have hb := h.optimal_binds hc
  obtain ⟨⟨hc1, hc2, -⟩, -⟩ := hc
  have hlt : c2 < h.Y2 + (1 + r') * (h.Y1 - c1) := by
    rw [hb]; nlinarith
  exact (h.utility_lt_utility_of_lt hc2 hlt).trans_le (hd.2 _ _ ⟨hc1, hc2.trans hlt, le_rfl⟩)

/-- **Foreign is impoverished by Home's tax** (O&R p. 44–45): if `r^A > r^{A*}`, Foreign's
competitive utility at the tax-equilibrium rate `r^τ` is strictly below its utility at `r^L`. -/
theorem foreign_loses {h : Household} {F : Foreign} {u' : ℝ → ℝ}
    (hu : ∀ c, 0 < c → HasDerivAt h.u (u' c) c) (hpos : ∀ c, 0 < c → 0 < u' c)
    (hA : F.autarkyGross < u' h.Y1 / (h.β * u' h.Y2)) {r b1 b2 c1 : ℝ}
    (hB : IsLaissezFaire h F r b1 b2) (hC : IsPlannerOptimal h F c1) :
    F.household.utility (F.Y1 - F.saving (F.rate h.Y1 c1 - 1))
        (F.rate h.Y1 c1 * F.β * (F.Y1 - F.saving (F.rate h.Y1 c1 - 1))) <
      F.household.utility (F.Y1 - F.saving r) ((1 + r) * F.β * (F.Y1 - F.saving r)) := by
  obtain ⟨hlo, hhi⟩ := rate_ordering hu hpos hA hB hC
  have hR : 0 < 1 + (F.rate h.Y1 c1 - 1) := by
    have : 0 < F.autarkyGross := div_pos F.Y2_pos (mul_pos F.β_pos F.Y1_pos)
    linarith
  have hopt := F.household_optimal hR
  rw [show 1 + (F.rate h.Y1 c1 - 1) = F.rate h.Y1 c1 by ring] at hopt
  refine utility_lt_of_lender hopt (F.household_optimal hB.1) (by linarith) ?_
  have hs := (F.saving_pos_iff hR).2 (by linarith)
  change _ < F.Y1
  linarith

/-! ### Pareto inefficiency (O&R p. 45) -/

/-- A function with positive derivative at `0` strictly exceeds its value at `0` just to the
right of `0`. -/
theorem eventually_gt_of_hasDerivAt_pos {g : ℝ → ℝ} {d : ℝ} (hg : HasDerivAt g d 0)
    (hd : 0 < d) : ∀ᶠ t in 𝓝[>] (0 : ℝ), g 0 < g t := by
  have h1 := (hasDerivAt_iff_tendsto_slope.1 hg).mono_left
    (nhdsWithin_mono (0 : ℝ) fun t (ht : t ∈ Ioi (0 : ℝ)) => (mem_Ioi.1 ht).ne')
  filter_upwards [h1.eventually (lt_mem_nhds hd), self_mem_nhdsWithin] with t ht ht0
  rw [slope_def_field, sub_zero] at ht
  have := (div_pos_iff_of_pos_right (mem_Ioi.1 ht0)).1 ht
  linarith

/-- **Unequal marginal rates of substitution leave room for a Pareto improvement** (O&R p. 45):
if agent 1's MRS `U₁/U₂` exceeds agent 2's, moving `t > 0` units of date-1 consumption from
agent 2 to agent 1 against `m t` units of date-2 consumption, for a suitable price `m`, makes
both strictly better off. Totals are unchanged, so the move is resource-feasible. -/
theorem exists_pareto_improvement {hH hF : Household} {c1 c2 d1 d2 a1 a2 b1 b2 : ℝ}
    (hc1 : 0 < c1) (hc2 : 0 < c2) (hd1 : 0 < d1) (hd2 : 0 < d2)
    (ha1 : HasDerivAt hH.u a1 c1) (ha2 : HasDerivAt hH.u a2 c2)
    (hb1 : HasDerivAt hF.u b1 d1) (hb2 : HasDerivAt hF.u b2 d2)
    (ha2p : 0 < a2) (hb1p : 0 < b1) (hb2p : 0 < b2)
    (hmrs : b1 / (hF.β * b2) < a1 / (hH.β * a2)) :
    ∃ t m, 0 < t ∧ 0 < c1 + t ∧ 0 < c2 - m * t ∧ 0 < d1 - t ∧ 0 < d2 + m * t ∧
      hH.utility c1 c2 < hH.utility (c1 + t) (c2 - m * t) ∧
      hF.utility d1 d2 < hF.utility (d1 - t) (d2 + m * t) := by
  set m := (b1 / (hF.β * b2) + a1 / (hH.β * a2)) / 2 with hm
  have hβH := hH.β_pos
  have hβF := hF.β_pos
  have hm0 : 0 < m := by
    have : 0 < b1 / (hF.β * b2) := by positivity
    rw [hm]; linarith
  have hmH : hH.β * a2 * m < a1 := by
    have : m < a1 / (hH.β * a2) := by rw [hm]; linarith
    rwa [lt_div_iff₀ (by positivity), mul_comm] at this
  have hmF : b1 < hF.β * b2 * m := by
    have : b1 / (hF.β * b2) < m := by rw [hm]; linarith
    rwa [div_lt_iff₀ (by positivity), mul_comm] at this
  have l1 : HasDerivAt (fun t : ℝ => c1 + t) 1 0 := (hasDerivAt_id' 0).const_add c1
  have l2 : HasDerivAt (fun t : ℝ => c2 - m * t) (-(m * 1)) 0 :=
    ((hasDerivAt_id' 0).const_mul m).const_sub c2
  have l3 : HasDerivAt (fun t : ℝ => d1 - t) (-1) 0 := (hasDerivAt_id' 0).const_sub d1
  have l4 : HasDerivAt (fun t : ℝ => d2 + m * t) (m * 1) 0 :=
    ((hasDerivAt_id' 0).const_mul m).const_add d2
  have ha1' : HasDerivAt hH.u a1 (c1 + 0) := by rwa [add_zero]
  have ha2' : HasDerivAt hH.u a2 (c2 - m * 0) := by rwa [mul_zero, sub_zero]
  have hb1' : HasDerivAt hF.u b1 (d1 - 0) := by rwa [sub_zero]
  have hb2' : HasDerivAt hF.u b2 (d2 + m * 0) := by rwa [mul_zero, add_zero]
  have gH : HasDerivAt (fun t => hH.utility (c1 + t) (c2 - m * t))
      (a1 * 1 + hH.β * (a2 * -(m * 1))) 0 :=
    (ha1'.comp 0 l1).add ((ha2'.comp 0 l2).const_mul hH.β)
  have gF : HasDerivAt (fun t => hF.utility (d1 - t) (d2 + m * t))
      (b1 * -1 + hF.β * (b2 * (m * 1))) 0 :=
    (hb1'.comp 0 l3).add ((hb2'.comp 0 l4).const_mul hF.β)
  have eH := eventually_gt_of_hasDerivAt_pos gH (by nlinarith)
  have eF := eventually_gt_of_hasDerivAt_pos gF (by nlinarith)
  have p2 : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < c2 - m * t :=
    continuousAt_const.eventually_lt (by fun_prop) (by simpa using hc2)
  have p3 : ∀ᶠ t in 𝓝 (0 : ℝ), 0 < d1 - t :=
    continuousAt_const.eventually_lt (by fun_prop) (by simpa using hd1)
  obtain ⟨t, h1, h2, h3, h4, h5⟩ := (eH.and (eF.and ((p2.filter_mono nhdsWithin_le_nhds).and
    ((p3.filter_mono nhdsWithin_le_nhds).and self_mem_nhdsWithin)))).exists
  simp only [add_zero, mul_zero, sub_zero] at h1 h2
  have ht : 0 < t := h5
  exact ⟨t, m, ht, by linarith, h3, h4, by positivity, h1, h2⟩

/-- Foreign's marginal rate of substitution at its competitive optimum equals the world gross
rate (log utility: `C₂*/(β* C₁*) = R` when `C₂* = R β* C₁*`). -/
theorem foreign_mrs {F : Foreign} {R c1 : ℝ} (hc1 : 0 < c1) (hR : 0 < R) :
    c1⁻¹ / (F.β * (R * F.β * c1)⁻¹) = R := by
  have := F.β_pos
  field_simp

/-- **The tax equilibrium is Pareto-inefficient** (O&R p. 45): at the planner's point C with
`C₁ ≠ Y₁`, and Foreign at its competitive optimum at `r^τ`, Home's MRS (`R + τ`) differs from
Foreign's (`R`), so some resource-feasible reallocation makes both countries strictly better
off; in particular Foreign could "bribe" Home not to tax. -/
theorem tax_equilibrium_pareto_inefficient {h : Household} {F : Foreign} {u' : ℝ → ℝ}
    (hu : ∀ c, 0 < c → HasDerivAt h.u (u' c) c) (hpos : ∀ c, 0 < c → 0 < u' c) {c1 : ℝ}
    (hC : IsPlannerOptimal h F c1) (hne : c1 ≠ h.Y1) :
    ∃ e1 e2 g1 g2, 0 < e1 ∧ 0 < e2 ∧ 0 < g1 ∧ 0 < g2 ∧
      e1 + g1 = c1 + (F.Y1 - F.saving (F.rate h.Y1 c1 - 1)) ∧
      e2 + g2 = F.offer h.Y1 h.Y2 c1 +
        F.rate h.Y1 c1 * F.β * (F.Y1 - F.saving (F.rate h.Y1 c1 - 1)) ∧
      h.utility c1 (F.offer h.Y1 h.Y2 c1) < h.utility e1 e2 ∧
      F.household.utility (F.Y1 - F.saving (F.rate h.Y1 c1 - 1))
          (F.rate h.Y1 c1 * F.β * (F.Y1 - F.saving (F.rate h.Y1 c1 - 1))) <
        F.household.utility g1 g2 := by
  have ht := planner_tangency hu hC
  obtain ⟨⟨hc1, hD, hc2⟩, -⟩ := hC
  have hR : 0 < F.rate h.Y1 c1 := div_pos F.Y2_pos hD
  have hR' : 0 < 1 + (F.rate h.Y1 c1 - 1) := by linarith
  have hopt := F.household_optimal hR'
  rw [show 1 + (F.rate h.Y1 c1 - 1) = F.rate h.Y1 c1 by ring] at hopt
  obtain ⟨⟨hf1, hf2, -⟩, -⟩ := hopt
  set R := F.rate h.Y1 c1
  set f1 := F.Y1 - F.saving (R - 1)
  set f2 := R * F.β * f1
  set o := F.offer h.Y1 h.Y2 c1
  have hβ := h.β_pos
  have hβs := F.β_pos
  have hpo := hpos o hc2
  have hmrsH : u' c1 / (h.β * u' o) = offerMRS F h.Y1 c1 := by
    rw [div_eq_iff (by positivity), ht]; ring
  have hmrsF : f1⁻¹ / (F.household.β * f2⁻¹) = R := by
    change f1⁻¹ / (F.β * (R * F.β * f1)⁻¹) = R
    exact foreign_mrs hf1 hR
  have hτ := optimalTax_eq F hD.ne'
  unfold optimalTax at hτ
  have hlog : ∀ c, 0 < c → HasDerivAt F.household.u c⁻¹ c :=
    fun c hc => Real.hasDerivAt_log hc.ne'
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- Home lends at C: Home's MRS is below the world rate
    have hlt' : offerMRS F h.Y1 c1 < R := by
      have : (1 + F.β) * F.Y2 * (c1 - h.Y1) / F.denom h.Y1 c1 ^ 2 < 0 :=
        div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by have := F.Y2_pos; positivity)
          (by linarith)) (by positivity)
      linarith
    obtain ⟨t, m, -, p1, p2, p3, p4, u1, u2⟩ := exists_pareto_improvement (hH := F.household)
      (hF := h) hf1 hf2 hc1 hc2 (hlog f1 hf1) (hlog f2 hf2) (hu c1 hc1) (hu o hc2)
      (inv_pos.2 hf2) (hpos c1 hc1) hpo (by rw [hmrsH, hmrsF]; exact hlt')
    exact ⟨c1 - t, o + m * t, f1 + t, f2 - m * t, p3, p4, p1, p2, by ring, by ring, u2, u1⟩
  · -- Home borrows at C: Home's MRS exceeds the world rate
    have hgt' : R < offerMRS F h.Y1 c1 := by
      have : 0 < (1 + F.β) * F.Y2 * (c1 - h.Y1) / F.denom h.Y1 c1 ^ 2 := by
        have := F.Y2_pos
        have : 0 < c1 - h.Y1 := by linarith
        positivity
      linarith
    obtain ⟨t, m, -, p1, p2, p3, p4, u1, u2⟩ := exists_pareto_improvement (hH := h)
      (hF := F.household) hc1 hc2 hf1 hf2 (hu c1 hc1) (hu o hc2) (hlog f1 hf1) (hlog f2 hf2)
      hpo (inv_pos.2 hf1) (inv_pos.2 hf2) (by rw [hmrsH, hmrsF]; exact hgt')
    exact ⟨c1 + t, o - m * t, f1 - t, f2 + m * t, p1, p2, p3, p4, by ring, by ring, u1, u2⟩

/-! ### A small country's optimal tax is zero (O&R p. 45) -/

/-- **Small country** (O&R p. 45): if Home cannot affect the world rate, the Foreign offer curve
is the straight line `C₂ = Y₂ + R(Y₁ − C₁)`, the planner's problem is the household problem at
`r = R − 1`, and the wedge between Home's MRS and the world rate `R` — the tax needed to
decentralise the planner optimum — is zero. -/
theorem small_country_zero_tax {h : Household} {u' : ℝ → ℝ}
    (hu : ∀ c, 0 < c → HasDerivAt h.u (u' c) c) (hpos : ∀ c, 0 < c → 0 < u' c)
    {R c1 c2 : ℝ} (hopt : h.IsOptimal (R - 1) c1 c2) :
    u' c1 / (h.β * u' c2) - R = 0 := by
  have he := h.euler_of_optimal hu hopt
  have hp := hpos c2 hopt.1.2.1
  have := h.β_pos
  rw [he, sub_eq_zero, div_eq_iff (by positivity)]
  ring

/-- Foreign scaled up by the factor `n + 1` (both endowments), used to model Home becoming a
small country. -/
noncomputable def Foreign.scale (F : Foreign) (n : ℕ) : Foreign where
  β := F.β
  Y1 := (n + 1) * F.Y1
  Y2 := (n + 1) * F.Y2
  β_pos := F.β_pos
  Y1_pos := mul_pos (by positivity) F.Y1_pos
  Y2_pos := mul_pos (by positivity) F.Y2_pos

/-- Scaling Foreign leaves its autarky rate `Y₂*/(β* Y₁*)` unchanged. -/
theorem Foreign.autarkyGross_scale (F : Foreign) (n : ℕ) :
    (F.scale n).autarkyGross = F.autarkyGross := by
  simp only [autarkyGross, Foreign.scale]
  field_simp

/-- The TT denominator per unit of Foreign size tends to `β* Y₁*` as Foreign grows. -/
theorem Foreign.tendsto_denom_scale (F : Foreign) (Y1 c1 : ℝ) :
    Tendsto (fun n : ℕ => (F.scale n).denom Y1 c1 / ((n : ℝ) + 1)) atTop
      (𝓝 (F.β * F.Y1)) := by
  have e : ∀ n : ℕ, (F.scale n).denom Y1 c1 / ((n : ℝ) + 1) =
      (1 + F.β) * (Y1 - c1) * (1 / ((n : ℝ) + 1)) + F.β * F.Y1 := by
    intro n
    simp only [denom, Foreign.scale]
    field_simp
  simp only [e]
  have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul ((1 + F.β) * (Y1 - c1))
  simpa using this.add_const (F.β * F.Y1)

/-- **A large Foreign pins the world rate at its autarky rate** (O&R p. 45): for any fixed
`C₁`, the rate TT induces tends to `Y₂*/(β* Y₁*)` as Foreign grows. -/
theorem Foreign.tendsto_rate_scale (F : Foreign) (Y1 c1 : ℝ) :
    Tendsto (fun n : ℕ => (F.scale n).rate Y1 c1) atTop (𝓝 F.autarkyGross) := by
  have e : ∀ n : ℕ, (F.scale n).rate Y1 c1 = F.Y2 / ((F.scale n).denom Y1 c1 / ((n : ℝ) + 1)) := by
    intro n
    simp only [rate, Foreign.scale]
    rw [div_div_eq_mul_div]
    ring
  simp only [e, autarkyGross]
  exact tendsto_const_nhds.div (F.tendsto_denom_scale Y1 c1)
    (mul_pos F.β_pos F.Y1_pos).ne'

/-- **A small country's optimal tax is zero** (O&R p. 45): for any fixed `C₁`, the wedge
`optimalTax` between the slope of TT and the world rate tends to zero as Foreign grows. -/
theorem Foreign.tendsto_optimalTax_scale (F : Foreign) (Y1 c1 : ℝ) :
    Tendsto (fun n : ℕ => optimalTax (F.scale n) Y1 c1) atTop (𝓝 0) := by
  have hc0 : F.β * F.Y1 ≠ 0 := (mul_pos F.β_pos F.Y1_pos).ne'
  have e : ∀ n : ℕ, offerMRS (F.scale n) Y1 c1 =
      F.Y2 * (F.β * F.Y1) / ((F.scale n).denom Y1 c1 / ((n : ℝ) + 1)) ^ 2 := by
    intro n
    simp only [offerMRS, Foreign.scale]
    rw [div_pow, div_div_eq_mul_div]
    ring
  have h1 : Tendsto (fun n : ℕ => offerMRS (F.scale n) Y1 c1) atTop
      (𝓝 (F.Y2 * (F.β * F.Y1) / (F.β * F.Y1) ^ 2)) := by
    simp only [e]
    exact tendsto_const_nhds.div ((F.tendsto_denom_scale Y1 c1).pow 2) (pow_ne_zero 2 hc0)
  have h2 := F.tendsto_rate_scale Y1 c1
  have hlim : F.Y2 * (F.β * F.Y1) / (F.β * F.Y1) ^ 2 - F.autarkyGross = 0 := by
    unfold autarkyGross
    field_simp
    ring
  rw [← hlim]
  exact h1.sub h2

/-! ### Footnote 19: when Home wants to lend, the optimal policy taxes lending -/

/-- Foreign borrows (`S₁* < 0`) exactly when the world rate is below its autarky rate. -/
theorem Foreign.saving_neg_iff (F : Foreign) {r : ℝ} (hr : 0 < 1 + r) :
    F.saving r < 0 ↔ 1 + r < F.autarkyGross := by
  have hβ := F.β_pos
  have hY1 := F.Y1_pos
  have e : F.saving r = (F.β * F.Y1 * (1 + r) - F.Y2) / ((1 + F.β) * (1 + r)) := by
    unfold saving
    field_simp
  rw [e, autarkyGross, lt_div_iff₀ (by positivity), div_neg_iff]
  constructor
  · rintro (⟨-, h⟩ | ⟨h, -⟩)
    · have : 0 < (1 + F.β) * (1 + r) := by positivity
      linarith
    · linarith
  · intro h
    exact Or.inr ⟨by linarith, by positivity⟩

/-- **Footnote 19, laissez-faire**: if `r^A < r^{A*}` then Home lends at B, `C₁ < Y₁`. -/
theorem laissezFaire_lends {h : Household} {F : Foreign} {u' : ℝ → ℝ}
    (hu : ∀ c, 0 < c → HasDerivAt h.u (u' c) c) (hpos : ∀ c, 0 < c → 0 < u' c)
    (hA : u' h.Y1 / (h.β * u' h.Y2) < F.autarkyGross) {r c1 c2 : ℝ}
    (hB : IsLaissezFaire h F r c1 c2) : c1 < h.Y1 := by
  obtain ⟨hr, ho, hs⟩ := hB
  by_contra hle
  push Not at hle
  have hS : ¬ F.saving r < 0 := by rw [← hs]; linarith
  rw [F.saving_neg_iff hr] at hS
  push Not at hS
  have he := h.euler_of_optimal hu ho
  have hb := h.optimal_binds ho
  obtain ⟨⟨hc1, hc2, -⟩, -⟩ := ho
  have hβ := h.β_pos
  have hY2 := hpos _ h.Y2_pos
  have h1 : u' c1 ≤ u' h.Y1 := deriv_anti hu h.Y1_pos hle
  have h2 : u' h.Y2 ≤ u' c2 := deriv_anti hu hc2 (by rw [hb]; nlinarith)
  rw [div_lt_iff₀ (by positivity)] at hA
  have h3 : (1 + r) * h.β * u' h.Y2 ≤ (1 + r) * h.β * u' c2 :=
    mul_le_mul_of_nonneg_left h2 (by positivity)
  have h4 : F.autarkyGross * (h.β * u' h.Y2) ≤ (1 + r) * h.β * u' h.Y2 := by
    have : 0 ≤ h.β * u' h.Y2 := by positivity
    nlinarith
  linarith

/-- **Footnote 19, planner**: if `r^A < r^{A*}`, the planner lends, but less than under
laissez-faire: `C₁^B < C₁^C < Y₁`. -/
theorem planner_between_lend {h : Household} {F : Foreign} {u' : ℝ → ℝ}
    (hu : ∀ c, 0 < c → HasDerivAt h.u (u' c) c) (hpos : ∀ c, 0 < c → 0 < u' c)
    (hA : u' h.Y1 / (h.β * u' h.Y2) < F.autarkyGross) {r b1 b2 c1 : ℝ}
    (hB : IsLaissezFaire h F r b1 b2) (hC : IsPlannerOptimal h F c1) :
    b1 < c1 ∧ c1 < h.Y1 := by
  have ht := planner_tangency hu hC
  obtain ⟨⟨hc1, hD, hc2⟩, -⟩ := hC
  have hβ := h.β_pos
  have hc0 : 0 < F.β * F.Y1 := mul_pos F.β_pos F.Y1_pos
  have hY2s := F.Y2_pos
  have hβs := F.β_pos
  have hdom : ∀ x, 0 < F.denom h.Y1 x → x ∈ {c | 0 < F.denom h.Y1 c} := fun x hx => hx
  have hm0 : 0 ≤ offerMRS F h.Y1 c1 := by unfold offerMRS; positivity
  constructor
  · have hbY := laissezFaire_lends hu hpos hA hB
    obtain ⟨hDB, hrate, hb2⟩ := laissezFaire_on_offer hB
    obtain ⟨hr, hoB, -⟩ := hB
    have he := h.euler_of_optimal hu hoB
    obtain ⟨⟨hb1, hb2pos, -⟩, -⟩ := hoB
    by_contra hle
    push Not at hle
    have hDB' : F.β * F.Y1 < F.denom h.Y1 b1 := by unfold denom; nlinarith
    have hDCB : F.denom h.Y1 b1 ≤ F.denom h.Y1 c1 := by unfold denom; nlinarith
    have hm : offerMRS F h.Y1 c1 < 1 + r := by
      rw [hrate]
      unfold offerMRS rate
      rw [div_lt_div_iff₀ (by positivity) hDB]
      have : F.denom h.Y1 b1 ^ 2 ≤ F.denom h.Y1 c1 ^ 2 := by nlinarith
      have h6 : F.β * F.Y1 * F.denom h.Y1 b1 < F.denom h.Y1 b1 ^ 2 := by nlinarith
      have h7 := mul_le_mul_of_nonneg_left this hY2s.le
      have h8 := mul_lt_mul_of_pos_left h6 hY2s
      linarith
    have hoC : b2 ≤ F.offer h.Y1 h.Y2 c1 := by
      rw [hb2]
      rcases hle.lt_or_eq with hlt | heq
      · exact (F.offer_strictAntiOn h.Y1 h.Y2 (hdom _ hD) (hdom _ hDB) hlt).le
      · rw [heq]
    have h1 : u' b1 ≤ u' c1 := deriv_anti hu hc1 hle
    have h2 : u' (F.offer h.Y1 h.Y2 c1) ≤ u' b2 := deriv_anti hu hb2pos hoC
    have hpb := hpos _ hb2pos
    have h3 : h.β * u' (F.offer h.Y1 h.Y2 c1) * offerMRS F h.Y1 c1 < h.β * u' b2 * (1 + r) := by
      calc h.β * u' (F.offer h.Y1 h.Y2 c1) * offerMRS F h.Y1 c1
          ≤ h.β * u' b2 * offerMRS F h.Y1 c1 :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hβ.le) hm0
        _ < h.β * u' b2 * (1 + r) := mul_lt_mul_of_pos_left hm (by positivity)
    nlinarith
  · by_contra hle
    push Not at hle
    have hDc : F.denom h.Y1 c1 ≤ F.β * F.Y1 := by unfold denom; nlinarith
    have hm : F.autarkyGross ≤ offerMRS F h.Y1 c1 := by
      unfold offerMRS Foreign.autarkyGross
      rw [div_le_div_iff₀ hc0 (by positivity)]
      have : F.denom h.Y1 c1 ^ 2 ≤ (F.β * F.Y1) ^ 2 := by nlinarith
      nlinarith
    have hoY : F.offer h.Y1 h.Y2 c1 ≤ F.offer h.Y1 h.Y2 h.Y1 := by
      rcases hle.lt_or_eq with hlt | heq
      · have hA' : 0 < F.denom h.Y1 h.Y1 := by simpa [denom] using hc0
        exact (F.offer_strictAntiOn h.Y1 h.Y2 (hdom _ hA') (hdom _ hD) hlt).le
      · rw [heq]
    rw [offer_endowment] at hoY
    have h1 : u' c1 ≤ u' h.Y1 := deriv_anti hu h.Y1_pos hle
    have h2 : u' h.Y2 ≤ u' (F.offer h.Y1 h.Y2 c1) := deriv_anti hu hc2 hoY
    have hpY := hpos _ h.Y2_pos
    rw [div_lt_iff₀ (by positivity)] at hA
    have h3 : h.β * u' h.Y2 * F.autarkyGross ≤
        h.β * u' (F.offer h.Y1 h.Y2 c1) * offerMRS F h.Y1 c1 := by
      calc h.β * u' h.Y2 * F.autarkyGross ≤ h.β * u' h.Y2 * offerMRS F h.Y1 c1 :=
            mul_le_mul_of_nonneg_left hm (by positivity)
        _ ≤ h.β * u' (F.offer h.Y1 h.Y2 c1) * offerMRS F h.Y1 c1 :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h2 hβ.le) hm0
    nlinarith

/-- **Footnote 19, the tax**: if `r^A < r^{A*}` the optimal wedge is negative, `τ < 0`:
residents' gross return on lending, `1 + r^τ + τ`, is below the world rate, i.e. foreign lending
is taxed. -/
theorem optimalTax_neg {h : Household} {F : Foreign} {u' : ℝ → ℝ}
    (hu : ∀ c, 0 < c → HasDerivAt h.u (u' c) c) (hpos : ∀ c, 0 < c → 0 < u' c)
    (hA : u' h.Y1 / (h.β * u' h.Y2) < F.autarkyGross) {r b1 b2 c1 : ℝ}
    (hB : IsLaissezFaire h F r b1 b2) (hC : IsPlannerOptimal h F c1) :
    optimalTax F h.Y1 c1 < 0 := by
  have h1 := (planner_between_lend hu hpos hA hB hC).2
  have hD := hC.1.2.1
  rw [optimalTax_eq F hD.ne']
  have := F.β_pos
  have := F.Y2_pos
  exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by positivity) (by linarith))
    (by positivity)

/-! ### Exercise 8: general utility and an ad valorem tax (O&R pp. 57–58) -/

/-- **The import-elasticity identity** (O&R Appendix 1A, p. 54): with Foreign's date-2 imports
`IM₂*(R) = R · D(R)`, where `D(R)` is Home borrowing (= Foreign saving) at gross rate `R`, the
elasticity `ζ* = R IM₂*'(R)/IM₂*(R)` satisfies `ζ* − 1 = R D'(R)/D(R)`, i.e.
`D' = D (ζ* − 1)/R`. -/
theorem elasticity_sub_one {Dfn IM : ℝ → ℝ} {R D' IM' : ℝ} (hR : R ≠ 0)
    (hD : HasDerivAt Dfn D' R) (hIMdef : ∀ x, IM x = x * Dfn x) (hIM : HasDerivAt IM IM' R)
    (hD0 : Dfn R ≠ 0) :
    R * IM' / IM R - 1 = R * D' / Dfn R := by
  have hfun : IM = fun x => x * Dfn x := funext hIMdef
  have h2 : HasDerivAt IM (1 * Dfn R + R * D') R := by
    rw [hfun]; exact (hasDerivAt_id' R).mul hD
  rw [hIM.unique h2, hIMdef]
  field_simp
  ring

/-- **Exercise 8(a)**: optimal ad valorem borrowing tax. Home's planner maximises a general
differentiable `U(C₁, C₂)` along the offer curve `C₂ = Y₂ − ρ(C₁)(C₁ − Y₁)`, where the world
gross rate `ρ(C₁)` inverts Home borrowing `D(ρ(C₁)) = C₁ − Y₁`. If residents face
`(1 + τ) ρ(C₁)` and choose C, so `(1 + τ) ρ = U₁/U₂`, then `τ (ζ* − 1) = 1`, i.e.
`τ = 1/(ζ* − 1)`, with `ζ*` Foreign's import elasticity at the optimum. -/
theorem ex8_optimal_tax {U : ℝ × ℝ → ℝ} {Dfn IM ρ : ℝ → ℝ} {U1 U2 D' IM' ρ' Y1 Y2 c1 τ : ℝ}
    (hρ : HasDerivAt ρ ρ' c1) (hD : HasDerivAt Dfn D' (ρ c1))
    (hinv : ∀ᶠ s in 𝓝 c1, Dfn (ρ s) = s - Y1)
    (hIMdef : ∀ x, IM x = x * Dfn x) (hIM : HasDerivAt IM IM' (ρ c1))
    (hU : HasFDerivAt U (U1 • ContinuousLinearMap.fst ℝ ℝ ℝ + U2 • ContinuousLinearMap.snd ℝ ℝ ℝ)
      (c1, Y2 - ρ c1 * (c1 - Y1)))
    (hmax : IsLocalMax (fun s => U (s, Y2 - ρ s * (s - Y1))) c1)
    (hR : 0 < ρ c1) (hU2 : U2 ≠ 0) (hne : c1 ≠ Y1) (htax : (1 + τ) * ρ c1 = U1 / U2) :
    τ * (ρ c1 * IM' / IM (ρ c1) - 1) = 1 ∧ τ = 1 / (ρ c1 * IM' / IM (ρ c1) - 1) := by
  -- the rate responds to borrowing: `D'(ρ) ρ' = 1`
  have hDρ : HasDerivAt (fun s => Dfn (ρ s)) (D' * ρ') c1 := hD.comp c1 hρ
  have hlin : HasDerivAt (fun s => Dfn (ρ s)) 1 c1 :=
    ((hasDerivAt_id' c1).sub_const Y1).congr_of_eventuallyEq hinv
  have h1 : D' * ρ' = 1 := hDρ.unique hlin
  have hD0 : Dfn (ρ c1) = c1 - Y1 := hinv.self_of_nhds
  have hsub : c1 - Y1 ≠ 0 := sub_ne_zero.2 hne
  -- the planner's first-order condition along the offer curve
  have hf : HasDerivAt (fun s => Y2 - ρ s * (s - Y1)) (-(ρ' * (c1 - Y1) + ρ c1 * 1)) c1 :=
    (hρ.mul ((hasDerivAt_id' c1).sub_const Y1)).const_sub Y2
  have hγ : HasDerivAt (fun s => (s, Y2 - ρ s * (s - Y1)))
      ((1 : ℝ), -(ρ' * (c1 - Y1) + ρ c1 * 1)) c1 := (hasDerivAt_id' c1).prodMk hf
  have hcomp := hU.comp_hasDerivAt c1 hγ
  have hfoc := hmax.hasDerivAt_eq_zero hcomp
  have hfoc' : U1 * 1 + U2 * -(ρ' * (c1 - Y1) + ρ c1 * 1) = 0 := by simpa using hfoc
  have hU1 : U1 = U2 * (ρ' * (c1 - Y1) + ρ c1) := by linarith
  rw [hU1, mul_div_cancel_left₀ _ hU2] at htax
  have hτ : τ * ρ c1 = ρ' * (c1 - Y1) := by linarith
  have hζ := elasticity_sub_one hR.ne' hD hIMdef hIM (hD0 ▸ hsub)
  rw [hζ, hD0]
  have key : τ * (ρ c1 * D' / (c1 - Y1)) = 1 := by
    field_simp
    linear_combination D' * hτ + (c1 - Y1) * h1
  exact ⟨key, eq_one_div_of_mul_eq_one_left key⟩

/-- **Exercise 8(b)**: at the optimum `ζ* > 1`, provided Foreign's import demand is not
downward-sloping (`ζ* ≥ 0`) and both marginal utilities are positive. The first-order conditions
alone only give `ζ* > 1` or `ζ* < 0`. -/
theorem ex8_elasticity_gt_one {U : ℝ × ℝ → ℝ} {Dfn IM ρ : ℝ → ℝ}
    {U1 U2 D' IM' ρ' Y1 Y2 c1 τ : ℝ}
    (hρ : HasDerivAt ρ ρ' c1) (hD : HasDerivAt Dfn D' (ρ c1))
    (hinv : ∀ᶠ s in 𝓝 c1, Dfn (ρ s) = s - Y1)
    (hIMdef : ∀ x, IM x = x * Dfn x) (hIM : HasDerivAt IM IM' (ρ c1))
    (hU : HasFDerivAt U (U1 • ContinuousLinearMap.fst ℝ ℝ ℝ + U2 • ContinuousLinearMap.snd ℝ ℝ ℝ)
      (c1, Y2 - ρ c1 * (c1 - Y1)))
    (hmax : IsLocalMax (fun s => U (s, Y2 - ρ s * (s - Y1))) c1)
    (hR : 0 < ρ c1) (hU1 : 0 < U1) (hU2 : 0 < U2) (hne : c1 ≠ Y1)
    (htax : (1 + τ) * ρ c1 = U1 / U2) (hζ : 0 ≤ ρ c1 * IM' / IM (ρ c1)) :
    1 < ρ c1 * IM' / IM (ρ c1) := by
  have key := (ex8_optimal_tax hρ hD hinv hIMdef hIM hU hmax hR hU2.ne' hne htax).1
  have h1τ : 0 < 1 + τ := by
    have : 0 < (1 + τ) * ρ c1 := by rw [htax]; positivity
    exact pos_of_mul_pos_left this hR.le
  set ζ := ρ c1 * IM' / IM (ρ c1)
  by_contra hle
  push Not at hle
  have hz : ζ = 0 := by nlinarith [mul_nonneg h1τ.le (sub_nonneg.2 hle)]
  rw [hz] at key
  linarith

/-- **Exercise 8(b), supply-side version**: if Home borrows at the optimum and Foreign's saving
schedule slopes up there (`D' > 0`), then `ζ* > 1`, since `ζ* − 1 = R D'/D`. -/
theorem ex8_elasticity_gt_one_of_supply {Dfn IM : ℝ → ℝ} {R D' IM' : ℝ} (hR : 0 < R)
    (hD : HasDerivAt Dfn D' R) (hIMdef : ∀ x, IM x = x * Dfn x) (hIM : HasDerivAt IM IM' R)
    (hborrow : 0 < Dfn R) (hD' : 0 < D') :
    1 < R * IM' / IM R := by
  have := elasticity_sub_one hR.ne' hD hIMdef hIM hborrow.ne'
  have : 0 < R * D' / Dfn R := by positivity
  linarith

end ObstfeldRogoff.IntertemporalTrade.OptimalTax
