/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StickyPriceModels.NontradablesModel
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Order.IntermediateValue

/-!
# Overshooting with preset nontradables prices: exact nonlinear results

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §10.2.4,
pp. 692–694, and end-of-chapter Exercise 2, p. 713. In the small open economy of
`NontradablesModel`, nontradables prices are preset one period in advance and an unanticipated
permanent money shock `M_1 = μ M_0` hits at date 1. The book log-linearises and obtains (99):
`p_T = e = [β + (1−β)ε] m / [β + (1−β)(1 − γ + γε)]`, so the exchange rate overshoots iff
`ε > 1`.

This file proves everything EXACTLY in the nonlinear model.

* With `x := P_{T,1}/P_{T,0}`, the date-1 money-demand equation (92), long-run neutrality
  (from `NontradablesModel.steadyState_unique`) and the preset `P_N` reduce to
  `μ^ε (1 − βx/μ) = (1−β) x^{1−γ+γε}`, which has a UNIQUE solution, and it lies in `(0, μ/β)`.
* Exact overshooting: for `μ > 1`, `x > μ ⟺ ε > 1`, `x = μ ⟺ ε = 1`, `x < μ ⟺ ε < 1`
  (reversed for `μ < 1`). Also `x > 1`, real balances rise strictly, and `C_N = y_N` rise by the
  factor `x`.
* (99) is the DERIVATIVE at `μ = 1` of the implicitly defined solution `x(μ)` (via the 1-D
  inverse function theorem), and (96)–(99) are verified as linear algebra and as derivatives.
* The whole sticky-price path is a genuine infinite-horizon equilibrium (household optimality
  with the preset price at date 1, via the concave-Lagrangian sufficiency theorem), IF AND ONLY
  IF `x` solves the impact equation and `x² ≤ θ/(θ−1)` (preset price at least ex post marginal
  cost: the exact meaning of "output is demand-determined").
* T29 (p. 694, "unambiguously improves welfare"): the exact gain in lifetime utility is
  `(1−γ)[log x − ((θ−1)/(2θ))(x² − 1)]` plus the strictly positive real-balance gain, positive on
  the whole demand-determined range; its derivative at `μ = 1` is `(1−γ)x'(1)/θ`.
* Exercise 2 (the real exchange rate `Q = 𝓔P^*/P` is never defined in the book; defined here):
  exact real interest parity `1 + r^C_{t+1} = (1+r) Q_{t+1}/Q_t`; on impact `Q_1/Q_0 = x^{1−γ} > 1`
  (real depreciation) and `r^C_2 < r`, for every `ε > 0`.
-/

namespace ObstfeldRogoff.StickyPriceModels.NontradablesOvershooting

open Real Filter Topology Finset
open ObstfeldRogoff.StickyPriceModels.NontradablesModel

/-! ## The exact impact equation -/

/-- The elasticity `1 − γ + γε` of the right side of the impact equation (O&R (99)). -/
noncomputable def expo (γ ε : ℝ) : ℝ := 1 - γ + γ * ε

/-- The impact equation `F(μ, x) = μ^ε (1 − βx/μ) − (1−β) x^{1−γ+γε}` whose zero is the impact
response `x = P_{T,1}/P_{T,0}` (O&R (92) at dates 0 and 1, pp. 692–693). -/
noncomputable def impactGap (β γ ε μ x : ℝ) : ℝ :=
  μ ^ ε * (1 - β * x / μ) - (1 - β) * x ^ expo γ ε

/-- `1 − γ + γε > 0` (O&R (99)). -/
theorem expo_pos {γ ε : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hε : 0 < ε) : 0 < expo γ ε := by
  unfold expo; nlinarith

/-- `ε > 1−γ+γε ⟺ ε > 1` for `γ < 1` (the overshooting comparison, O&R p. 693). -/
theorem expo_lt_iff {γ ε : ℝ} (hγ1 : γ < 1) : expo γ ε < ε ↔ 1 < ε := by
  unfold expo
  constructor <;> intro h <;> nlinarith

/-- The impact equation is strictly decreasing in `x ≥ 0` (O&R pp. 692–693). -/
theorem impactGap_strictAntiOn {β γ ε μ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hγ0 : 0 < γ)
    (hγ1 : γ < 1) (hε : 0 < ε) (hμ : 0 < μ) :
    StrictAntiOn (impactGap β γ ε μ) (Set.Ici 0) := by
  intro x1 hx1 x2 hx2 hlt
  simp only [Set.mem_Ici] at hx1 hx2
  unfold impactGap
  have ha := expo_pos hγ0 hγ1 hε
  have h1 : x1 ^ expo γ ε ≤ x2 ^ expo γ ε := rpow_le_rpow hx1 hlt.le ha.le
  have h2 : β * x1 / μ < β * x2 / μ := by
    apply div_lt_div_of_pos_right _ hμ; nlinarith
  have hme : 0 < μ ^ ε := rpow_pos_of_pos hμ ε
  nlinarith

/-- EXISTENCE AND UNIQUENESS of the impact response (O&R (99), exact version): for every `μ > 0`
there is exactly one `x > 0` with `F(μ, x) = 0`, and it satisfies `x < μ/β` (a positive nominal
interest rate at date 1). -/
theorem impact_exists_unique {β γ ε μ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hγ0 : 0 < γ)
    (hγ1 : γ < 1) (hε : 0 < ε) (hμ : 0 < μ) :
    ∃ x, 0 < x ∧ x < μ / β ∧ impactGap β γ ε μ x = 0 ∧
      ∀ y, 0 < y → impactGap β γ ε μ y = 0 → y = x := by
  have ha := expo_pos hγ0 hγ1 hε
  have hb : 0 < μ / β := div_pos hμ hβ
  have hcont : ContinuousOn (impactGap β γ ε μ) (Set.Icc 0 (μ / β)) := by
    unfold impactGap
    exact (continuous_const.mul (continuous_const.sub
      ((continuous_const.mul continuous_id).div_const μ))).sub
      (continuous_const.mul (continuous_rpow_const ha.le)) |>.continuousOn
  have h0 : impactGap β γ ε μ 0 = μ ^ ε := by
    simp [impactGap, zero_rpow ha.ne']
  have hend : impactGap β γ ε μ (μ / β) = -((1 - β) * (μ / β) ^ expo γ ε) := by
    unfold impactGap
    rw [show β * (μ / β) / μ = 1 by field_simp]; ring
  have hmem : (0 : ℝ) ∈ Set.Ioo (impactGap β γ ε μ (μ / β)) (impactGap β γ ε μ 0) := by
    rw [h0, hend]
    constructor
    · have : 0 < (1 - β) * (μ / β) ^ expo γ ε :=
        mul_pos (by linarith) (rpow_pos_of_pos hb _)
      linarith
    · exact rpow_pos_of_pos hμ ε
  obtain ⟨x, ⟨hx0, hxb⟩, hx⟩ := intermediate_value_Ioo' hb.le hcont hmem
  refine ⟨x, hx0, hxb, hx, fun y hy hy0 => ?_⟩
  by_contra hne
  have hanti := impactGap_strictAntiOn hβ hβ1 hγ0 hγ1 hε hμ
  rcases lt_or_gt_of_ne hne with h | h
  · have := hanti (Set.mem_Ici.mpr hy.le) (Set.mem_Ici.mpr hx0.le) h; linarith
  · have := hanti (Set.mem_Ici.mpr hx0.le) (Set.mem_Ici.mpr hy.le) h; linarith

/-- Any positive root of the impact equation is below `μ/β` (O&R (92) needs `1 − βx/μ > 0`). -/
theorem root_lt {β γ ε μ x : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hε : 0 < ε) (hμ : 0 < μ) (hx : 0 < x) (hF : impactGap β γ ε μ x = 0) : x < μ / β := by
  obtain ⟨z, hz0, hzb, _, huniq⟩ := impact_exists_unique hβ hβ1 hγ0 hγ1 hε hμ
  rw [huniq x hx hF]; exact hzb

/-- The value of the impact equation at `x = μ` (no overshooting):
`F(μ, μ) = (1−β)(μ^ε − μ^{1−γ+γε})` (O&R p. 693). -/
theorem impactGap_at_mu {β γ ε μ : ℝ} (hμ : 0 < μ) :
    impactGap β γ ε μ μ = (1 - β) * (μ ^ ε - μ ^ expo γ ε) := by
  unfold impactGap
  rw [show β * μ / μ = β by field_simp]; ring

/-- EXACT OVERSHOOTING (O&R (99) and p. 693, nonlinear version): for a monetary expansion
`μ > 1`, the tradables price (the exchange rate) overshoots its new long-run level `μ` IF AND
ONLY IF `ε > 1`; it moves one for one iff `ε = 1`; it undershoots iff `ε < 1`. -/
theorem overshoot_iff {β γ ε μ x : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hε : 0 < ε) (hμ : 1 < μ) (hx : 0 < x) (hF : impactGap β γ ε μ x = 0) :
    (μ < x ↔ 1 < ε) ∧ (x = μ ↔ ε = 1) ∧ (x < μ ↔ ε < 1) := by
  have hμ0 : 0 < μ := by linarith
  have hanti := impactGap_strictAntiOn hβ hβ1 hγ0 hγ1 hε hμ0
  have hFμ := impactGap_at_mu (β := β) (γ := γ) (ε := ε) hμ0
  have hb1 : 0 < 1 - β := by linarith
  have key1 : μ < x ↔ 0 < impactGap β γ ε μ μ := by
    constructor
    · intro h; have := hanti (Set.mem_Ici.mpr hμ0.le) (Set.mem_Ici.mpr hx.le) h; linarith
    · intro h; by_contra hle; push Not at hle
      rcases eq_or_lt_of_le hle with he | hlt
      · rw [he] at hF; linarith
      · have := hanti (Set.mem_Ici.mpr hx.le) (Set.mem_Ici.mpr hμ0.le) hlt; linarith
  have key2 : x < μ ↔ impactGap β γ ε μ μ < 0 := by
    constructor
    · intro h; have := hanti (Set.mem_Ici.mpr hx.le) (Set.mem_Ici.mpr hμ0.le) h; linarith
    · intro h; by_contra hle; push Not at hle
      rcases eq_or_lt_of_le hle with he | hlt
      · rw [← he] at hF; linarith
      · have := hanti (Set.mem_Ici.mpr hμ0.le) (Set.mem_Ici.mpr hx.le) hlt; linarith
  have hcmp1 : 0 < impactGap β γ ε μ μ ↔ 1 < ε := by
    rw [hFμ, ← expo_lt_iff hγ1, mul_pos_iff_of_pos_left hb1, sub_pos,
      rpow_lt_rpow_left_iff hμ]
  have hneg : ∀ d : ℝ, (1 - β) * d < 0 ↔ d < 0 := fun d =>
    ⟨fun h => by by_contra hc; push Not at hc; nlinarith [mul_nonneg hb1.le hc],
      fun h => mul_neg_of_pos_of_neg hb1 h⟩
  have hcmp2 : impactGap β γ ε μ μ < 0 ↔ ε < 1 := by
    rw [hFμ, hneg, sub_neg, rpow_lt_rpow_left_iff hμ]
    unfold expo
    constructor <;> intro h <;> nlinarith
  refine ⟨key1.trans hcmp1, ?_, key2.trans hcmp2⟩
  constructor
  · intro he
    rcases lt_trichotomy ε 1 with h | h | h
    · have := (key2.trans hcmp2).mpr h; linarith
    · exact h
    · have := (key1.trans hcmp1).mpr h; linarith
  · intro he
    rcases lt_trichotomy x μ with h | h | h
    · have := (key2.trans hcmp2).mp h; linarith
    · exact h
    · have := (key1.trans hcmp1).mp h; linarith

/-- EXACT OVERSHOOTING for a monetary CONTRACTION `0 < μ < 1` (the mirror image of (99)): the
tradables price falls below its new long-run level (`x < μ`) iff `ε > 1`. -/
theorem overshoot_iff_of_lt_one {β γ ε μ x : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hγ0 : 0 < γ)
    (hγ1 : γ < 1) (hε : 0 < ε) (hμ0 : 0 < μ) (hμ : μ < 1) (hx : 0 < x)
    (hF : impactGap β γ ε μ x = 0) : x < μ ↔ 1 < ε := by
  have hanti := impactGap_strictAntiOn hβ hβ1 hγ0 hγ1 hε hμ0
  have hFμ := impactGap_at_mu (β := β) (γ := γ) (ε := ε) hμ0
  have hb1 : 0 < 1 - β := by linarith
  have key : x < μ ↔ impactGap β γ ε μ μ < 0 := by
    constructor
    · intro h; have := hanti (Set.mem_Ici.mpr hx.le) (Set.mem_Ici.mpr hμ0.le) h; linarith
    · intro h; by_contra hle; push Not at hle
      rcases eq_or_lt_of_le hle with he | hlt
      · rw [← he] at hF; linarith
      · have := hanti (Set.mem_Ici.mpr hμ0.le) (Set.mem_Ici.mpr hx.le) hlt; linarith
  have hneg : ∀ d : ℝ, (1 - β) * d < 0 ↔ d < 0 := fun d =>
    ⟨fun h => by by_contra hc; push Not at hc; nlinarith [mul_nonneg hb1.le hc],
      fun h => mul_neg_of_pos_of_neg hb1 h⟩
  rw [key, hFμ, hneg, sub_neg, rpow_lt_rpow_left_iff_of_base_lt_one hμ0 hμ]
  unfold expo
  constructor <;> intro h <;> nlinarith


/-- For a monetary expansion `μ > 1` the tradables price rises: `x > 1` (O&R p. 693). -/
theorem one_lt_root {β γ ε μ x : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hε : 0 < ε) (hμ : 1 < μ) (hx : 0 < x) (hF : impactGap β γ ε μ x = 0) : 1 < x := by
  have hμ0 : 0 < μ := by linarith
  -- `φ(ν) = ν^ε − β ν^{ε−1}` is strictly increasing on `[1, ∞)`
  set φ : ℝ → ℝ := fun ν => ν ^ ε - β * ν ^ (ε - 1) with hφ
  have hφd : ∀ ν, 0 < ν → HasDerivAt φ (ε * ν ^ (ε - 1) - β * ((ε - 1) * ν ^ (ε - 1 - 1))) ν :=
    fun ν hν => (hasDerivAt_rpow_const (Or.inl hν.ne')).sub
      ((hasDerivAt_rpow_const (p := ε - 1) (Or.inl hν.ne')).const_mul β)
  have hmono : StrictMonoOn φ (Set.Ici 1) := by
    refine strictMonoOn_of_deriv_pos (convex_Ici 1) ?_ ?_
    · intro ν hν
      exact (hφd ν (by simp only [Set.mem_Ici] at hν; linarith)).continuousAt.continuousWithinAt
    · intro ν hν
      rw [interior_Ici] at hν
      simp only [Set.mem_Ioi] at hν
      have hν0 : 0 < ν := by linarith
      rw [(hφd ν hν0).deriv]
      have hp : 0 < ν ^ (ε - 1 - 1) := rpow_pos_of_pos hν0 _
      have e : ν ^ (ε - 1) = ν * ν ^ (ε - 1 - 1) := by
        rw [rpow_sub_one hν0.ne' (ε - 1)]; field_simp
      rw [e]
      rcases le_or_gt 1 ε with h | h
      · have : 0 < ε * ν - β * (ε - 1) := by nlinarith
        nlinarith
      · have : 0 < ε * ν - β * (ε - 1) := by nlinarith
        nlinarith
  have hφ1 : φ 1 < φ μ := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hμ.le) hμ
  simp only [hφ, one_rpow] at hφ1
  have hF1 : 0 < impactGap β γ ε μ 1 := by
    unfold impactGap
    rw [one_rpow]
    have e : μ ^ ε * (1 - β * 1 / μ) = μ ^ ε - β * μ ^ (ε - 1) := by
      rw [rpow_sub_one hμ0.ne']; field_simp
    rw [e]; linarith
  by_contra hle
  push Not at hle
  rcases eq_or_lt_of_le hle with he | hlt
  · rw [he] at hF; linarith
  · have := impactGap_strictAntiOn hβ hβ1 hγ0 hγ1 hε hμ0 (Set.mem_Ici.mpr hx.le)
      (Set.mem_Ici.mpr zero_le_one) hlt
    linarith

/-- Real balances rise strictly on impact (O&R p. 694, "real balances rise temporarily"):
`M_1/P_1 = μ M_0/(x^γ P_0) > M_0/P_0`, i.e. `μ/x^γ > 1`, for every `ε > 0` and `μ > 1`. -/
theorem realBalances_rise {β γ ε μ x : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hγ0 : 0 < γ)
    (hγ1 : γ < 1) (hε : 0 < ε) (hμ : 1 < μ) (hx : 0 < x) (hF : impactGap β γ ε μ x = 0) :
    1 < μ / x ^ γ := by
  have hμ0 : 0 < μ := by linarith
  have hxg : 0 < x ^ γ := rpow_pos_of_pos hx γ
  rw [one_lt_div hxg]
  rcases lt_or_ge x μ with h | h
  · calc x ^ γ < μ ^ γ := rpow_lt_rpow hx.le h hγ0
      _ < μ ^ (1 : ℝ) := rpow_lt_rpow_of_exponent_lt hμ hγ1
      _ = μ := rpow_one μ
  · have hx1 : 1 < x := lt_of_lt_of_le hμ h
    have hb : 0 < 1 - β * x / μ := by
      have := root_lt hβ hβ1 hγ0 hγ1 hε hμ0 hx hF
      rw [sub_pos, div_lt_one hμ0]
      calc β * x < β * (μ / β) := by nlinarith
        _ = μ := by field_simp
    unfold impactGap expo at hF
    have hsplit : x ^ (1 - γ + γ * ε) = x ^ (1 - γ) * (x ^ γ) ^ ε := by
      rw [← rpow_mul hx.le, ← rpow_add hx]
    rw [hsplit] at hF
    have hx1g : 1 < x ^ (1 - γ) := one_lt_rpow hx1 (by linarith)
    have hkey : (x ^ γ) ^ ε < μ ^ ε := by
      have h2 : 1 - β * x / μ ≤ 1 - β := by
        have : β ≤ β * x / μ := by rw [le_div_iff₀ hμ0]; nlinarith
        linarith
      have hxe : 0 < (x ^ γ) ^ ε := rpow_pos_of_pos hxg ε
      have h3 : (1 - β) * (x ^ γ) ^ ε < (1 - β) * x ^ (1 - γ) * (x ^ γ) ^ ε := by
        have : 0 < (1 - β) * (x ^ γ) ^ ε := mul_pos (by linarith) hxe
        nlinarith
      have h4 : (1 - β) * x ^ (1 - γ) * (x ^ γ) ^ ε = μ ^ ε * (1 - β * x / μ) := by linarith
      have h5 : (1 - β * x / μ) * (x ^ γ) ^ ε ≤ (1 - β) * (x ^ γ) ^ ε :=
        mul_le_mul_of_nonneg_right h2 hxe.le
      have h6 : (1 - β * x / μ) * (x ^ γ) ^ ε < (1 - β * x / μ) * μ ^ ε := by linarith
      exact lt_of_mul_lt_mul_left h6 hb.le
    exact (rpow_lt_rpow_iff hxg.le hμ0.le hε).mp hkey

/-! ## (99) as the derivative of the exact impact response -/

/-- The overshooting ratio map `H(t) = (1−β) t^a / (1−βt)`: `x = μt` solves the impact equation
iff `H(t) = μ^{(ε−1)(1−γ)}` (O&R (99), exact). -/
noncomputable def ratioMap (β a t : ℝ) : ℝ := (1 - β) * t ^ a / (1 - β * t)

/-- Rescaling the impact equation by `x = μt` (O&R p. 693):
`F(μ, μt) = μ^ε(1−βt)(1 − μ^{a−ε} H(t))`. -/
theorem impactGap_scaled {β γ ε μ t : ℝ} (hμ : 0 < μ) (ht : 0 < t) (hβt : β * t < 1) :
    impactGap β γ ε μ (μ * t)
      = μ ^ ε * (1 - β * t) * (1 - μ ^ (expo γ ε - ε) * ratioMap β (expo γ ε) t) := by
  unfold impactGap ratioMap
  have hb : (1 : ℝ) - β * t ≠ 0 := by linarith
  rw [mul_rpow hμ.le ht.le, rpow_sub hμ]
  have : 0 < μ ^ ε := rpow_pos_of_pos hμ ε
  field_simp

/-- `H(1) = 1` (O&R (99): no overshooting when `μ = 1`). -/
theorem ratioMap_one {β a : ℝ} (hβ1 : β < 1) : ratioMap β a 1 = 1 := by
  unfold ratioMap
  rw [one_rpow, mul_one, mul_one]
  exact div_self (by linarith)

/-- The strict derivative of `H` at `1` is `(β + (1−β)a)/(1−β)` (O&R (99)). -/
theorem hasStrictDerivAt_ratioMap {β a : ℝ} (hβ1 : β < 1) :
    HasStrictDerivAt (ratioMap β a) ((β + (1 - β) * a) / (1 - β)) 1 := by
  have hb : (1 : ℝ) - β * 1 ≠ 0 := by linarith
  have h1 := (hasStrictDerivAt_rpow_const_of_ne (one_ne_zero) a).const_mul (1 - β)
  have h2 := ((hasStrictDerivAt_id (1 : ℝ)).const_mul β).const_sub 1
  have h3 := h1.div h2 hb
  have e : ratioMap β a = (fun y => (1 - β) * y ^ a) / fun x => 1 - β * id x := by
    funext t; simp [ratioMap]
  rw [e]
  convert h3 using 1
  simp only [one_rpow, id]
  have : (1 : ℝ) - β ≠ 0 := by linarith
  field_simp
  ring

/-- (99) IS THE DERIVATIVE of the exact impact response (O&R (99), p. 693): if `X(μ)` is a
positive root of the impact equation for every `μ` near `1`, then
`X'(1) = [β + (1−β)ε]/[β + (1−β)(1−γ+γε)]`. Proved with the 1-D inverse function theorem
applied to `H`, and uniqueness of the root. -/
theorem hasDerivAt_impact {β γ ε : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hγ0 : 0 < γ)
    (hγ1 : γ < 1) (hε : 0 < ε) {X : ℝ → ℝ}
    (hX : ∀ᶠ μ in 𝓝 1, 0 < X μ ∧ impactGap β γ ε μ (X μ) = 0) :
    HasDerivAt X ((β + (1 - β) * ε) / (β + (1 - β) * expo γ ε)) 1 := by
  set a := expo γ ε with ha_def
  have ha := expo_pos hγ0 hγ1 hε
  set c := ε - a with hc
  set Hd := (β + (1 - β) * a) / (1 - β) with hHd_def
  have hb1 : 0 < 1 - β := by linarith
  have hHd : Hd ≠ 0 := by
    have : 0 < β + (1 - β) * a := by positivity
    exact (div_pos this hb1).ne'
  have hH := hasStrictDerivAt_ratioMap (a := a) hβ1
  set L := HasStrictDerivAt.localInverse (ratioMap β a) Hd 1 hH hHd
  have hH1 : ratioMap β a 1 = 1 := ratioMap_one hβ1
  have hL : HasStrictDerivAt L Hd⁻¹ (ratioMap β a 1) := hH.to_localInverse hHd
  have hleft := hH.eventually_left_inverse hHd
  have hright := hH.eventually_right_inverse hHd
  have hL1 : L 1 = 1 := by
    have := hleft.self_of_nhds; rw [hH1] at this; exact this
  rw [hH1] at hL hright
  -- the power map `μ ↦ μ^c`
  have hpw : HasDerivAt (fun μ : ℝ => μ ^ c) c 1 := by
    have := hasDerivAt_rpow_const (x := (1 : ℝ)) (p := c) (Or.inl one_ne_zero)
    simpa using this
  have hpt : Tendsto (fun μ : ℝ => μ ^ c) (𝓝 1) (𝓝 1) := by
    have := hpw.continuousAt.tendsto; simpa using this
  have hLt : Tendsto (fun μ : ℝ => L (μ ^ c)) (𝓝 1) (𝓝 1) := by
    have := hL.hasDerivAt.continuousAt.tendsto.comp hpt
    rw [hL1] at this; exact this
  have hIoo : Set.Ioo 0 (1 / β) ∈ 𝓝 (1 : ℝ) := by
    apply Ioo_mem_nhds one_pos
    rw [lt_div_iff₀ hβ]; linarith
  -- the explicit solution `Y μ = μ L(μ^c)`
  set Y : ℝ → ℝ := fun μ => μ * L (μ ^ c)
  have hXY : X =ᶠ[𝓝 1] Y := by
    filter_upwards [hX, hpt.eventually hright, hLt.eventually hIoo,
      Ioi_mem_nhds (zero_lt_one' ℝ)] with μ hXμ hR hI hμ
    obtain ⟨hI0, hI1⟩ := hI
    simp only [Set.mem_Ioi] at hμ
    have hβt : β * L (μ ^ c) < 1 := by
      rw [lt_div_iff₀ hβ] at hI1; linarith
    have hYroot : impactGap β γ ε μ (Y μ) = 0 := by
      simp only [Y]
      rw [impactGap_scaled hμ hI0 hβt, hR, ← rpow_add hμ,
        show a - ε + c = 0 by rw [hc]; ring, rpow_zero]
      ring
    have hY0 : 0 < Y μ := mul_pos hμ hI0
    by_contra hne
    have hanti := impactGap_strictAntiOn hβ hβ1 hγ0 hγ1 hε hμ
    rcases lt_or_gt_of_ne hne with h | h
    · have := hanti (Set.mem_Ici.mpr hXμ.1.le) (Set.mem_Ici.mpr hY0.le) h; linarith [hXμ.2]
    · have := hanti (Set.mem_Ici.mpr hY0.le) (Set.mem_Ici.mpr hXμ.1.le) h; linarith [hXμ.2]
  have hLat : HasDerivAt L Hd⁻¹ ((fun μ : ℝ => μ ^ c) 1) := by
    simp only [one_rpow]; exact hL.hasDerivAt
  have hcomp := hLat.comp (1 : ℝ) hpw
  have hY : HasDerivAt Y (1 * L ((1 : ℝ) ^ c) + 1 * (Hd⁻¹ * c)) 1 := by
    have := (hasDerivAt_id' (1 : ℝ)).mul hcomp
    convert this using 1 <;> rfl
  have hfin := hY.congr_of_eventuallyEq hXY
  convert hfin using 1
  rw [one_rpow, hL1, hHd_def, hc, ha_def]
  have : 0 < β + (1 - β) * expo γ ε := by positivity
  field_simp
  ring

/-- (99) in logarithms (O&R (99), `p_T = e`): `d log x / d log μ = [β+(1−β)ε]/[β+(1−β)(1−γ+γε)]`
at `μ = 1`. -/
theorem hasDerivAt_log_impact {β γ ε : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hγ0 : 0 < γ)
    (hγ1 : γ < 1) (hε : 0 < ε) {X : ℝ → ℝ}
    (hX : ∀ᶠ μ in 𝓝 1, 0 < X μ ∧ impactGap β γ ε μ (X μ) = 0) (hX1 : X 1 = 1) :
    HasDerivAt (fun m => log (X (exp m))) ((β + (1 - β) * ε) / (β + (1 - β) * expo γ ε)) 0 := by
  have hd := hasDerivAt_impact hβ hβ1 hγ0 hγ1 hε hX
  have hd' : HasDerivAt X ((β + (1 - β) * ε) / (β + (1 - β) * expo γ ε)) (exp 0) := by
    rw [exp_zero]; exact hd
  have h1 := (hd'.comp 0 (hasDerivAt_exp 0)).log (by simp [hX1])
  convert h1 using 1 <;> first | rfl | simp [hX1]

/-- The coefficient in (99) exceeds one iff `ε > 1` (overshooting, O&R p. 693). -/
theorem coef99_gt_one_iff {β γ ε : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hε : 0 < ε) :
    1 < (β + (1 - β) * ε) / (β + (1 - β) * expo γ ε) ↔ 1 < ε := by
  have ha := expo_pos hγ0 hγ1 hε
  have hden : 0 < β + (1 - β) * expo γ ε := by
    have : 0 < 1 - β := by linarith
    positivity
  rw [one_lt_div hden, ← expo_lt_iff hγ1]
  have : 0 < 1 - β := by linarith
  constructor <;> intro h <;> nlinarith

/-- The log-linear system (96)–(98) implies (99) (O&R pp. 693): with `p = γ p_T` (97) and
`p̄_T = m` (98), `ε(m − p) = p_T − p + (β/(1−β))(p_T − p̄_T)` (96) holds IFF
`p_T = [β + (1−β)ε] m / [β + (1−β)(1 − γ + γε)]` (99). -/
theorem loglinear_99 {β γ ε m pT : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hε : 0 < ε) :
    ε * (m - γ * pT) = pT - γ * pT + β / (1 - β) * (pT - m) ↔
      pT = (β + (1 - β) * ε) * m / (β + (1 - β) * expo γ ε) := by
  have ha := expo_pos hγ0 hγ1 hε
  have hb : 0 < 1 - β := by linarith
  have hden : 0 < β + (1 - β) * expo γ ε := by positivity
  unfold expo at hden ⊢
  constructor
  · intro h
    field_simp at h
    rw [eq_div_iff hden.ne']
    linear_combination -h
  · intro h
    have h' := (eq_div_iff hden.ne').mp h
    have : (1 : ℝ) - β ≠ 0 := hb.ne'
    field_simp
    linear_combination -h'

/-- (96) is the derivative of the exact log money-demand equation (O&R (96), fn 23). On the
impact path the exact equation (92), relative to the initial steady state, reads
`Φ(m, u) = ε(m − γu) − (1−γ)u + log(1 − βe^{u−m}) − log(1−β) = 0` with `m = log μ`,
`u = log x`. Its derivative in `m` at `(0,0)` is `ε + β/(1−β)`. -/
theorem hasDerivAt_logMoneyDemand_m {β ε : ℝ} (hβ1 : β < 1) :
    HasDerivAt (fun m => ε * m + log (1 - β * exp (-m)) - log (1 - β)) (ε + β / (1 - β)) 0 := by
  have hb : (1 : ℝ) - β * exp (-0) ≠ 0 := by simp; linarith
  have h1 := ((hasDerivAt_neg (0 : ℝ)).exp.const_mul β).const_sub 1
  have h2 := h1.log hb
  have h3 := (((hasDerivAt_id (0 : ℝ)).const_mul ε).add h2).sub_const (log (1 - β))
  convert h3 using 1
  · rfl
  · simp only [neg_zero, exp_zero, mul_one]
    have : (1 : ℝ) - β ≠ 0 := by linarith
    field_simp

/-- (96), derivative in `u` (O&R (96)): `Φ(0, u)` has derivative
`−(εγ + 1 − γ + β/(1−β))` at `u = 0`; together with the derivative in `m`, the linearisation
`(ε + β/(1−β))m = (εγ + 1 − γ + β/(1−β))u` is exactly (96) with (97)–(98). -/
theorem hasDerivAt_logMoneyDemand_u {β γ ε : ℝ} (hβ1 : β < 1) :
    HasDerivAt (fun u => -(ε * γ + (1 - γ)) * u + log (1 - β * exp u) - log (1 - β))
      (-(ε * γ + (1 - γ) + β / (1 - β))) 0 := by
  have hb : (1 : ℝ) - β * exp 0 ≠ 0 := by simp; linarith
  have h1 := ((hasDerivAt_exp (0 : ℝ)).const_mul β).const_sub 1
  have h2 := h1.log hb
  have h3 := (((hasDerivAt_id (0 : ℝ)).const_mul (-(ε * γ + (1 - γ)))).add h2).sub_const
    (log (1 - β))
  convert h3 using 1
  · rfl
  · simp only [exp_zero, mul_one]
    have : (1 : ℝ) - β ≠ 0 := by linarith
    field_simp
    ring


/-! ## The sticky-price equilibrium path -/

/-- Homogeneity of the price index (83): `P(aP_T, bP_N) = a^γ b^{1−γ} P(P_T, P_N)`. -/
theorem cpi_scale {γ a b PT PN : ℝ} (ha : 0 < a) (hb : 0 < b) (hT : 0 < PT) (hN : 0 < PN) :
    cpi γ (a * PT) (b * PN) = a ^ γ * b ^ (1 - γ) * cpi γ PT PN := by
  unfold cpi
  rw [mul_rpow ha.le hT.le, mul_rpow hb.le hN.le]
  ring

/-- The pre-shock steady-state tradables price given `M_0` (O&R §10.2.3, from
`NontradablesModel.steadyState_unique`). -/
noncomputable def pT0 (E : Economy) (M0 : ℝ) : ℝ := M0 / (realMoneyBar E * cpiRatio E)

/-- The pre-shock (and preset) nontradables price `P_{N,0} = (P_N/P_T)‾ P_{T,0}` (O&R p. 692). -/
noncomputable def pN0 (E : Economy) (M0 : ℝ) : ℝ := relPriceBar E * pT0 E M0

/-- `P_{T,0} > 0` (O&R p. 692). -/
theorem pT0_pos {E : Economy} (hE : E.Valid) {M0 : ℝ} (hM0 : 0 < M0) : 0 < pT0 E M0 := by
  have := realMoneyBar_pos hE; have := cpiRatio_pos hE
  unfold pT0; positivity

/-- `P_{N,0} > 0` (O&R p. 692). -/
theorem pN0_pos {E : Economy} (hE : E.Valid) {M0 : ℝ} (hM0 : 0 < M0) : 0 < pN0 E M0 :=
  mul_pos (relPriceBar_pos hE) (pT0_pos hE hM0)

/-- LONG-RUN NEUTRALITY (98), p. 693: the steady-state price level is proportional to money,
`P̄_T(μM_0) = μ P̄_T(M_0)` and likewise `P̄_N` (uniqueness from
`NontradablesModel.steadyState_unique`). -/
theorem longRun_neutral (E : Economy) (M0 μ : ℝ) :
    pT0 E (μ * M0) = μ * pT0 E M0 ∧ pN0 E (μ * M0) = μ * pN0 E M0 := by
  unfold pN0 pT0; constructor <;> ring

/-- The pre-shock consumer price index `P̄_0 = P_{T,0} (P/P_T)‾ = M_0/(M/P)‾` (O&R p. 692). -/
theorem cpi_initial {E : Economy} (hE : E.Valid) {M0 : ℝ} (hM0 : 0 < M0) :
    cpi E.γ (pT0 E M0) (pN0 E M0) = pT0 E M0 * cpiRatio E := by
  have hT := pT0_pos hE hM0
  rw [cpi_eq_mul hT (pN0_pos hE hM0)]
  unfold pN0; rw [mul_div_cancel_right₀ _ hT.ne']; rfl

/-- `((M/P)‾)^{−ε} = γ (P/P_T)‾ (1−β)/(χ ȳ_T)` (O&R (92) in the steady state). -/
theorem realMoneyBar_rpow_neg {E : Economy} (hE : E.Valid) :
    realMoneyBar E ^ (-E.ε) = E.γ * cpiRatio E * (1 - E.β) / (E.χ * E.yT) := by
  have hcr := cpiRatio_pos hE
  obtain ⟨_, hβ1, _, hγ0, _, hχ, hε, _, _, hyT⟩ := hE
  unfold realMoneyBar
  have hb : 0 < 1 - E.β := by linarith
  have hpos : 0 ≤ E.χ / E.γ * (E.yT / cpiRatio E) / (1 - E.β) := by positivity
  rw [← rpow_mul hpos, show 1 / E.ε * -E.ε = -1 by field_simp, rpow_neg_one]
  field_simp

/-- The price paths after an unanticipated permanent money shock `M = μM_0` at book date 1
(Lean date 0): `P_T = xP_{T,0}` then `μP_{T,0}`; `P_N` preset at `P_{N,0}` then `μP_{N,0}`;
aggregate nontradables demand `xȳ_N` then `ȳ_N`; seignorage rebated (O&R §10.2.4, pp. 692–693).
-/
noncomputable def shockPrices (E : Economy) (M0 μ x : ℝ) : Prices :=
  ⟨fun t => if t = 0 then x * pT0 E M0 else μ * pT0 E M0,
    fun t => if t = 0 then pN0 E M0 else μ * pN0 E M0,
    fun t => if t = 0 then x * ybarN E else ybarN E,
    fun t => if t = 0 then -(μ * M0 - M0) / (x * pT0 E M0) else 0⟩

/-- The allocation on the shock path: `C_T = ȳ_T` always, `C_N = y_N = xȳ_N` on impact (95) and
`ȳ_N` afterwards, money `μM_0` (O&R (94)–(95), p. 693). -/
noncomputable def shockChoice (E : Economy) (M0 μ x : ℝ) : ℕ → Choice :=
  fun t => if t = 0 then ⟨E.yT, x * ybarN E, μ * M0, x * ybarN E⟩
    else ⟨E.yT, ybarN E, μ * M0, ybarN E⟩

/-- Net resources with the nontradables price PRESET at date 0: each producer sells `y` at the
common preset price `P_N`, so real revenue is `(P_N/P_T) y` (O&R p. 692). -/
noncomputable def stickyNetRes (E : Economy) (Q : Prices) (t : ℕ) (c : Choice) : ℝ :=
  if t = 0 then E.yT - Q.τ 0 + relPrice Q 0 * c.y - relPrice Q 0 * c.cN - c.cT
    - c.money * userCost E.r Q 0
  else netRes E Q t c

/-- Admissible choices with a preset price at date 0: at the common preset price demand is
`C^A_N` (CES demand at `p_N = P_N`), and a producer may sell any quantity up to demand
(O&R p. 692, "output is demand determined"). -/
def stickySet (Q : Prices) (t : ℕ) : Set Choice :=
  if t = 0 then {c | c ∈ posChoice ∧ c.y ≤ Q.CA 0} else posChoice

/-- Household optimality with the nontradables price preset at date 0 (O&R §10.2.4). -/
def StickyOptimal (E : Economy) (Q : Prices) (B0 Mm1 : ℝ) (c : ℕ → Choice) : Prop :=
  IsOptimal E.β E.r (initWealth E Q B0 Mm1) (periodU E Q) (stickyNetRes E Q) (stickySet Q) c

/-- A symmetric equilibrium with the preset price at date 0 (O&R §10.2.4): households optimise,
`y_N = C_N = C^A_N`, the money market clears and seignorage is rebated (85). -/
def IsStickyEquilibrium (E : Economy) (Q : Prices) (B0 Mm1 : ℝ) (M : ℕ → ℝ)
    (c : ℕ → Choice) : Prop :=
  StickyOptimal E Q B0 Mm1 c ∧ (∀ t, (c t).y = (c t).cN ∧ Q.CA t = (c t).cN) ∧
    (∀ t, (c t).money = M t) ∧ ∀ t, Q.τ t = -(M t - moneyPrev Mm1 c t) / Q.PT t

/-- The user cost of money on the shock path: `(1 − βx/μ)/(xP_{T,0})` on impact and
`(1−β)/(μP_{T,0})` afterwards (O&R (92)). -/
theorem shock_userCost {E : Economy} (hE : E.Valid) (hβr : E.β * (1 + E.r) = 1) {M0 μ x : ℝ}
    (hM0 : 0 < M0) (hμ : 0 < μ) (hx : 0 < x) :
    userCost E.r (shockPrices E M0 μ x) 0 = (1 - E.β * x / μ) / (x * pT0 E M0) ∧
      ∀ t, t ≠ 0 → userCost E.r (shockPrices E M0 μ x) t = (1 - E.β) / (μ * pT0 E M0) := by
  have hT := pT0_pos hE hM0
  obtain ⟨_, _, hr, _, _, _, _, _, _, _⟩ := hE
  have hinv : 1 / (1 + E.r) = E.β := by field_simp; linarith
  refine ⟨?_, fun t ht => ?_⟩
  · simp only [userCost, shockPrices, ↓reduceIte, Nat.add_one_ne_zero]
    have : 1 / ((1 + E.r) * (μ * pT0 E M0)) = E.β / (μ * pT0 E M0) := by
      rw [← hinv]; field_simp
    rw [this]; field_simp
  · simp only [userCost, shockPrices, ht, ↓reduceIte, Nat.add_one_ne_zero]
    have : 1 / ((1 + E.r) * (μ * pT0 E M0)) = E.β / (μ * pT0 E M0) := by
      rw [← hinv]; field_simp
    rw [this]; field_simp

/-- The impact CPI `P_1 = x^γ P̄_0` (O&R (97): `p = γ p_T`, exactly), and `P_t = μP̄_0` later. -/
theorem shock_cpi {E : Economy} (hE : E.Valid) {M0 μ x : ℝ} (hM0 : 0 < M0) (hμ : 0 < μ)
    (hx : 0 < x) :
    cpiAt E (shockPrices E M0 μ x) 0 = x ^ E.γ * (pT0 E M0 * cpiRatio E) ∧
      ∀ t, t ≠ 0 → cpiAt E (shockPrices E M0 μ x) t = μ * (pT0 E M0 * cpiRatio E) := by
  have hT := pT0_pos hE hM0
  have hN := pN0_pos hE hM0
  refine ⟨?_, fun t ht => ?_⟩
  · simp only [cpiAt, shockPrices, ↓reduceIte]
    rw [show pN0 E M0 = 1 * pN0 E M0 by ring, cpi_scale hx one_pos hT hN, one_rpow,
      mul_one, cpi_initial hE hM0]
  · simp only [cpiAt, shockPrices, ht, ↓reduceIte]
    rw [cpi_scale hμ hμ hT hN, ← rpow_add hμ, show E.γ + (1 - E.γ) = 1 by ring, rpow_one,
      cpi_initial hE hM0]

/-- The shock-path prices are admissible whenever `x < μ/β` (positive nominal interest on
impact; O&R (92)). -/
theorem shockPrices_valid {E : Economy} (hE : E.Valid) (hβr : E.β * (1 + E.r) = 1)
    {M0 μ x : ℝ} (hM0 : 0 < M0) (hμ : 0 < μ) (hx : 0 < x) (hxb : x < μ / E.β) :
    (shockPrices E M0 μ x).Valid E.r := by
  have hT := pT0_pos hE hM0
  have hN := pN0_pos hE hM0
  have hy := ybarN_pos hE
  obtain ⟨hu0, hu⟩ := shock_userCost hE hβr hM0 hμ hx
  have hβ := hE.1
  have hβ1 := hE.2.1
  intro t
  by_cases ht : t = 0
  · subst ht
    refine ⟨by simp only [shockPrices, ↓reduceIte]; positivity,
      by simp only [shockPrices, ↓reduceIte]; positivity,
      by simp only [shockPrices, ↓reduceIte]; positivity, ?_⟩
    rw [hu0]
    apply div_pos _ (by positivity)
    rw [sub_pos, div_lt_one hμ]
    rw [lt_div_iff₀ hβ] at hxb; linarith
  · refine ⟨by simp only [shockPrices, ht, ↓reduceIte]; positivity,
      by simp only [shockPrices, ht, ↓reduceIte]; positivity,
      by simp only [shockPrices, ht, ↓reduceIte]; positivity, ?_⟩
    rw [hu t ht]
    exact div_pos (by linarith) (by positivity)


/-- `M_0/P̄_0 = (M/P)‾`: the pre-shock real balances (O&R (92)). -/
theorem M0_div_cpi {E : Economy} (hE : E.Valid) {M0 : ℝ} (hM0 : 0 < M0) :
    M0 / (pT0 E M0 * cpiRatio E) = realMoneyBar E := by
  have := realMoneyBar_pos hE; have := cpiRatio_pos hE
  unfold pT0; field_simp

/-- THE IMPACT MONEY-DEMAND CONDITION IS THE IMPACT EQUATION (O&R (92) at date 1 with `P_N`
preset, `C_T = ȳ_T` and `P_{T,2} = μP_{T,0}`): the money first-order condition on impact holds IFF
`μ^ε(1 − βx/μ) = (1−β)x^{1−γ+γε}`. -/
theorem shock_moneyFOC0_iff {E : Economy} (hE : E.Valid) (hβr : E.β * (1 + E.r) = 1)
    {M0 μ x : ℝ} (hM0 : 0 < M0) (hμ : 0 < μ) (hx : 0 < x) :
    E.χ * (μ * M0 / cpiAt E (shockPrices E M0 μ x) 0) ^ (-E.ε)
        / cpiAt E (shockPrices E M0 μ x) 0
      = E.γ / E.yT * userCost E.r (shockPrices E M0 μ x) 0 ↔
      impactGap E.β E.γ E.ε μ x = 0 := by
  have hT := pT0_pos hE hM0
  have hcr := cpiRatio_pos hE
  have hmb := realMoneyBar_pos hE
  have hmneg := realMoneyBar_rpow_neg hE
  have hmd := M0_div_cpi hE hM0
  obtain ⟨hu0, _⟩ := shock_userCost hE hβr hM0 hμ hx
  obtain ⟨hP0, _⟩ := shock_cpi hE hM0 hμ hx
  obtain ⟨_, _, _, hγ0, _, hχ, hε, _, _, hyT⟩ := hE
  rw [hu0, hP0]
  set u := x ^ E.γ with hu
  have hu0' : 0 < u := rpow_pos_of_pos hx _
  have hμe : 0 < μ ^ E.ε := rpow_pos_of_pos hμ _
  have hrb : μ * M0 / (u * (pT0 E M0 * cpiRatio E)) = μ * realMoneyBar E / u := by
    rw [← hmd]; field_simp
  rw [hrb]
  have hpow : (μ * realMoneyBar E / u) ^ (-E.ε)
      = u ^ E.ε / μ ^ E.ε * realMoneyBar E ^ (-E.ε) := by
    rw [div_rpow (by positivity) hu0'.le, mul_rpow hμ.le hmb.le]
    simp only [rpow_neg hu0'.le, rpow_neg hμ.le]
    field_simp
  rw [hpow, hmneg]
  have hxa : x ^ expo E.γ E.ε = x / u * u ^ E.ε := by
    unfold expo
    rw [hu, ← rpow_mul hx.le, show 1 - E.γ + E.γ * E.ε = 1 - E.γ + E.γ * E.ε by rfl,
      rpow_add hx, rpow_sub hx, rpow_one]
  set K := E.γ / (E.yT * x * pT0 E M0 * μ ^ E.ε) with hK
  have hKpos : 0 < K := by positivity
  have hL : E.χ * (u ^ E.ε / μ ^ E.ε * (E.γ * cpiRatio E * (1 - E.β) / (E.χ * E.yT)))
      / (u * (pT0 E M0 * cpiRatio E)) = K * ((1 - E.β) * x ^ expo E.γ E.ε) := by
    rw [hxa, hK]; field_simp
  have hR : E.γ / E.yT * ((1 - E.β * x / μ) / (x * pT0 E M0))
      = K * (μ ^ E.ε * (1 - E.β * x / μ)) := by
    rw [hK]; field_simp
  rw [hL, hR]
  unfold impactGap
  constructor
  · intro h
    have := mul_left_cancel₀ hKpos.ne' h
    linarith
  · intro h
    congr 1; linarith

/-- The date-0 Lagrangian inequality with the price PRESET (O&R §10.2.4): if (89) and the money
condition hold and the preset price is at least ex post marginal cost,
`κ y_N ≤ (γ/C_T)(P_N/P_T)`, then selling the full demand maximises the date-0 Lagrangian over
all admissible choices (including rationing, `y ≤ C^A_N`). -/
theorem stickyLagrangian_le {E : Economy} (hE : E.Valid) (Q : Prices)
    (hQ0 : 0 < Q.PT 0 ∧ 0 < Q.PN 0 ∧ 0 < Q.CA 0 ∧ 0 < userCost E.r Q 0) {c y : Choice}
    (hc : c ∈ posChoice) (hy : y ∈ stickySet Q 0) (hcy : c.y = Q.CA 0)
    (hN : (1 - E.γ) / c.cN = E.γ / c.cT * relPrice Q 0)
    (hM : E.χ * (c.money / cpiAt E Q 0) ^ (-E.ε) / cpiAt E Q 0
      = E.γ / c.cT * userCost E.r Q 0)
    (hMC : E.κ * c.y ≤ E.γ / c.cT * relPrice Q 0) :
    periodU E Q 0 y + E.γ / c.cT * stickyNetRes E Q 0 y
      ≤ periodU E Q 0 c + E.γ / c.cT * stickyNetRes E Q 0 c := by
  obtain ⟨_, _, _, hγ0, hγ1, hχ, hε, hκ, _, _⟩ := hE
  obtain ⟨hT, hPN, hA, _⟩ := hQ0
  obtain ⟨ha, hb, hn, hq⟩ := hc
  simp only [stickySet, ↓reduceIte, Set.mem_ofPred_eq] at hy
  obtain ⟨⟨ha', hb', hn', hq'⟩, hyle⟩ := hy
  have hP : 0 < cpiAt E Q 0 := cpi_pos hγ0 hγ1 hT hPN
  set lam := E.γ / c.cT with hlam
  set ρ := relPrice Q 0
  set P := cpiAt E Q 0
  have hA' := log_tangent hγ0.le ha' ha
  have hB' := log_tangent (k := 1 - E.γ) (by linarith) hb' hb
  have hBr : (1 - E.γ) / c.cN = lam * ρ := hN
  have hC' := moneyU_le_tangent hχ.le hε (div_pos hn hP) (div_pos hn' hP) (χ := E.χ)
  have hCr : E.χ * (c.money / P) ^ (-E.ε) * (y.money / P - c.money / P)
      = lam * userCost E.r Q 0 * (y.money - c.money) := by
    rw [← hM]; field_simp
  have hD : -(E.κ / 2) * y.y ^ 2 + lam * ρ * y.y ≤ -(E.κ / 2) * c.y ^ 2 + lam * ρ * c.y := by
    have h1 : y.y ≤ c.y := hcy ▸ hyle
    have e : (-(E.κ / 2) * c.y ^ 2 + lam * ρ * c.y) - (-(E.κ / 2) * y.y ^ 2 + lam * ρ * y.y)
        = (c.y - y.y) * (lam * ρ - E.κ / 2 * (c.y + y.y)) := by ring
    have h2 : 0 ≤ lam * ρ - E.κ / 2 * (c.y + y.y) := by nlinarith
    nlinarith [mul_nonneg (sub_nonneg.mpr h1) h2]
  simp only [periodU, stickyNetRes, ↓reduceIte]
  rw [hBr] at hB'
  have e1 : (1 - E.γ) / c.cN * y.cN = lam * ρ * y.cN := by rw [hBr]
  have e2 : (1 - E.γ) / c.cN * c.cN = lam * ρ * c.cN := by rw [hBr]
  linarith [hA', hB', hC', hCr, hD, e1, e2]

/-- On the shock path the preset price is at least ex post marginal cost IFF
`x² ≤ θ/(θ−1)` (O&R p. 674, p. 692: the exact range in which output is demand-determined). -/
theorem shock_markup_iff {E : Economy} (hE : E.Valid) {M0 μ x : ℝ} (hM0 : 0 < M0) (hx : 0 < x) :
    E.κ * (x * ybarN E) ≤ E.γ / E.yT * relPrice (shockPrices E M0 μ x) 0 ↔
      x ^ 2 ≤ E.θ / (E.θ - 1) := by
  have hT := pT0_pos hE hM0
  have hy := ybarN_pos hE
  have hk := kappa_mul_ybarN_sq hE
  obtain ⟨_, _, _, hγ0, hγ1, _, _, hκ, hθ, hyT⟩ := hE
  have e : E.γ / E.yT * relPrice (shockPrices E M0 μ x) 0 = (1 - E.γ) / (x * ybarN E) := by
    simp only [relPrice, shockPrices, ↓reduceIte, pN0, relPriceBar]
    field_simp
  rw [e, le_div_iff₀ (by positivity : 0 < x * ybarN E),
    le_div_iff₀ (by linarith : 0 < E.θ - 1)]
  have e2 : E.κ * (x * ybarN E) * (x * ybarN E) = x ^ 2 * ((E.θ - 1) * (1 - E.γ) / E.θ) := by
    rw [← hk]; ring
  rw [e2]
  have h1 : 0 < 1 - E.γ := by linarith
  have h2 : 0 < E.θ := by linarith
  have e3 : x ^ 2 * ((E.θ - 1) * (1 - E.γ) / E.θ) = (x ^ 2 * (E.θ - 1)) * (1 - E.γ) / E.θ := by
    ring
  rw [e3, div_le_iff₀ h2]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith


/-- With `β(1+r) = 1` the market discount factor is `β^t` (O&R p. 690). -/
theorem disc_eq_pow {E : Economy} (hβr : E.β * (1 + E.r) = 1) (t : ℕ) : disc E.r t = E.β ^ t := by
  have hb : E.β = (1 + E.r)⁻¹ := by
    have h : (1 + E.r) ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hβr; exact zero_ne_one hβr
    field_simp; linarith
  simp [disc, hb, inv_pow]

/-- The intratemporal condition (89) on the shock path, at every date (O&R (95)). -/
theorem shock_intra {E : Economy} (hE : E.Valid) {M0 μ x : ℝ} (hM0 : 0 < M0) (hμ : 0 < μ)
    (hx : 0 < x) (t : ℕ) :
    (1 - E.γ) / (shockChoice E M0 μ x t).cN
      = E.γ / (shockChoice E M0 μ x t).cT * relPrice (shockPrices E M0 μ x) t := by
  have hT := pT0_pos hE hM0
  have hy := ybarN_pos hE
  obtain ⟨_, _, _, hγ0, hγ1, _, _, _, _, hyT⟩ := hE
  by_cases ht : t = 0
  · subst ht
    simp only [shockChoice, shockPrices, relPrice, ↓reduceIte, pN0, relPriceBar]
    field_simp
  · simp only [shockChoice, shockPrices, relPrice, ht, ↓reduceIte, pN0, relPriceBar]
    field_simp

/-- The money condition on the shock path after impact (the new steady state), O&R (92). -/
theorem shock_money_later {E : Economy} (hE : E.Valid) (hβr : E.β * (1 + E.r) = 1)
    {M0 μ x : ℝ} (hM0 : 0 < M0) (hμ : 0 < μ) (hx : 0 < x) {t : ℕ} (ht : t ≠ 0) :
    E.χ * ((shockChoice E M0 μ x t).money / cpiAt E (shockPrices E M0 μ x) t) ^ (-E.ε)
        / cpiAt E (shockPrices E M0 μ x) t
      = E.γ / (shockChoice E M0 μ x t).cT * userCost E.r (shockPrices E M0 μ x) t := by
  have hT := pT0_pos hE hM0
  have hcr := cpiRatio_pos hE
  have hmneg := realMoneyBar_rpow_neg hE
  have hmd := M0_div_cpi hE hM0
  obtain ⟨_, hu⟩ := shock_userCost hE hβr hM0 hμ hx
  obtain ⟨_, hP⟩ := shock_cpi hE hM0 hμ hx
  obtain ⟨_, _, _, hγ0, _, hχ, _, _, _, hyT⟩ := hE
  rw [hu t ht, hP t ht]
  simp only [shockChoice, ht, ↓reduceIte]
  rw [show μ * M0 / (μ * (pT0 E M0 * cpiRatio E)) = M0 / (pT0 E M0 * cpiRatio E) by
    field_simp, hmd, hmneg]
  field_simp

/-- The output condition on the shock path after impact (the new steady state), O&R (90). -/
theorem shock_labour_later {E : Economy} (hE : E.Valid) {M0 μ x : ℝ} (hM0 : 0 < M0)
    (hμ : 0 < μ) {t : ℕ} (ht : t ≠ 0) :
    E.κ * (shockChoice E M0 μ x t).y = E.γ / (shockChoice E M0 μ x t).cT
      * relPrice (shockPrices E M0 μ x) t * ((E.θ - 1) / E.θ *
        ((shockChoice E M0 μ x t).y ^ ((E.θ - 1) / E.θ - 1)
          * (shockPrices E M0 μ x).CA t ^ (1 / E.θ))) := by
  have hT := pT0_pos hE hM0
  have hy := ybarN_pos hE
  have hk := kappa_mul_ybarN_sq hE
  obtain ⟨_, _, _, hγ0, hγ1, _, _, _, hθ, hyT⟩ := hE
  simp only [shockChoice, shockPrices, relPrice, ht, ↓reduceIte, pN0]
  rw [← rpow_add hy, show (E.θ - 1) / E.θ - 1 + 1 / E.θ = 0 by field_simp; ring, rpow_zero,
    mul_one, show μ * (relPriceBar E * pT0 E M0) / (μ * pT0 E M0) = relPriceBar E by
      field_simp]
  unfold relPriceBar
  field_simp at hk ⊢
  linarith

/-- Wealth on the shock path: `A_t = M_0/P_{T,0}` for every `t ≥ 1` (bonds stay zero; O&R (91)). -/
theorem shock_wealth {E : Economy} (hE : E.Valid) (hβr : E.β * (1 + E.r) = 1) {M0 μ x : ℝ}
    (hM0 : 0 < M0) (hμ : 0 < μ) (hx : 0 < x) {t : ℕ} (ht : 1 ≤ t) :
    wealth E.r (initWealth E (shockPrices E M0 μ x) 0 M0) (stickyNetRes E (shockPrices E M0 μ x))
      (shockChoice E M0 μ x) t = M0 / pT0 E M0 := by
  have hT := pT0_pos hE hM0
  have hy := ybarN_pos hE
  obtain ⟨hu0, hu⟩ := shock_userCost hE hβr hM0 hμ hx
  have hr := hE.2.2.1
  have hθ := hE.2.2.2.2.2.2.2.2.1
  induction t, ht using Nat.le_induction with
  | base =>
    have e : initWealth E (shockPrices E M0 μ x) 0 M0
        + stickyNetRes E (shockPrices E M0 μ x) 0 (shockChoice E M0 μ x 0)
        = E.β * (M0 / pT0 E M0) := by
      simp only [initWealth, stickyNetRes, ↓reduceIte]
      rw [hu0]
      simp only [shockChoice, shockPrices, relPrice, ↓reduceIte]
      field_simp
      ring
    change (1 + E.r) * (initWealth E (shockPrices E M0 μ x) 0 M0
      + stickyNetRes E (shockPrices E M0 μ x) 0 (shockChoice E M0 μ x 0)) = _
    rw [e, ← mul_assoc, mul_comm (1 + E.r), hβr, one_mul]
  | succ t ht ih =>
    have ht0 : t ≠ 0 := by omega
    rw [wealth, ih]
    have e : M0 / pT0 E M0 + stickyNetRes E (shockPrices E M0 μ x) t (shockChoice E M0 μ x t)
        = E.β * (M0 / pT0 E M0) := by
      simp only [stickyNetRes, ht0, ↓reduceIte, netRes]
      rw [hu t ht0]
      simp only [shockChoice, ht0, ↓reduceIte]
      rw [realRevenue_symm E (shockPrices E M0 μ x) t (by linarith) hy
        (by simp [shockPrices, ht0])]
      simp only [shockPrices, ht0, ↓reduceIte]
      field_simp
      ring
    rw [e, ← mul_assoc, mul_comm (1 + E.r), hβr, one_mul]

/-- EXISTENCE OF THE STICKY-PRICE EQUILIBRIUM (O&R §10.2.4, pp. 692–693, exact): if `x` solves
the impact equation and `x² ≤ θ/(θ−1)`, the shock path — `P_{T,1} = xP_{T,0}`, `P_N` preset,
`C_N = y_N = xȳ_N`, and the new steady state `μ×` the old one from date 2 — is a genuine
infinite-horizon equilibrium: households optimise over ALL plans (including rationing at the
preset price) subject to no-Ponzi, markets clear and seignorage is rebated. -/
theorem shock_isStickyEquilibrium {E : Economy} (hE : E.Valid) (hβr : E.β * (1 + E.r) = 1)
    {M0 μ x : ℝ} (hM0 : 0 < M0) (hμ : 0 < μ) (hx : 0 < x)
    (hF : impactGap E.β E.γ E.ε μ x = 0) (hdd : x ^ 2 ≤ E.θ / (E.θ - 1)) :
    (shockPrices E M0 μ x).Valid E.r ∧
      IsStickyEquilibrium E (shockPrices E M0 μ x) 0 M0 (fun _ => μ * M0)
        (shockChoice E M0 μ x) := by
  have hE' := hE
  obtain ⟨hβ, hβ1, hr, hγ0, hγ1, hχ, hε, hκ, hθ, hyT⟩ := hE'
  have hr0 : 0 < E.r := by nlinarith
  have hT := pT0_pos hE hM0
  have hy := ybarN_pos hE
  have hxb := root_lt hβ hβ1 hγ0 hγ1 hε hμ hx hF
  have hQ := shockPrices_valid hE hβr hM0 hμ hx hxb
  set Q := shockPrices E M0 μ x with hQdef
  set c := shockChoice E M0 μ x with hcdef
  have hc : ∀ t, c t ∈ posChoice := by
    intro t
    by_cases ht : t = 0
    · subst ht; simp only [c, shockChoice, ↓reduceIte]
      exact ⟨hyT, by positivity, by positivity, by positivity⟩
    · simp only [c, shockChoice, ht, ↓reduceIte]
      exact ⟨hyT, hy, by positivity, hy⟩
  have hadm : ∀ t, c t ∈ stickySet Q t := by
    intro t
    by_cases ht : t = 0
    · subst ht
      simp only [stickySet, ↓reduceIte, Set.mem_ofPred_eq]
      refine ⟨hc 0, ?_⟩
      simp [c, shockChoice, Q, shockPrices]
    · simp only [stickySet, ht, ↓reduceIte]; exact hc t
  -- summability
  have hsum : Summable fun t => E.β ^ t * periodU E Q t (c t) := by
    have hconst : ∀ t ∉ ({0} : Finset ℕ), E.β ^ t * periodU E Q t (c t)
        = E.β ^ t * periodU E Q 1 (c 1) := by
      intro t ht
      have ht0 : t ≠ 0 := by simpa using ht
      simp only [periodU, cpiAt, c, Q, shockChoice, shockPrices, ht0, ↓reduceIte,
        Nat.one_ne_zero]
    exact (tsum_eq_add_of_eq_off
      ((summable_geometric_of_lt_one hβ.le hβ1).mul_right (periodU E Q 1 (c 1))) {0}
      hconst).1
  -- wealth, no-Ponzi, transversality
  have hdw : Tendsto (fun T => disc E.r T
      * wealth E.r (initWealth E Q 0 M0) (stickyNetRes E Q) c T) atTop (𝓝 0) := by
    have h0 : Tendsto (fun T => disc E.r T * (M0 / pT0 E M0)) atTop (𝓝 0) := by
      simpa using (tendsto_disc hr0).mul_const (M0 / pT0 E M0)
    refine h0.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with T hT1
    rw [shock_wealth hE hβr hM0 hμ hx hT1]
  have hnp : NoPonzi E.r (wealth E.r (initWealth E Q 0 M0) (stickyNetRes E Q) c) :=
    fun δ hδ => (hdw.eventually (lt_mem_nhds (by linarith : -δ < 0))).mono fun _ h => h.le
  have htv : LiminfNonpos E.r (wealth E.r (initWealth E Q 0 M0) (stickyNetRes E Q) c) :=
    fun δ hδ => (hdw.eventually (gt_mem_nhds hδ)).frequently.mono fun _ h => h.le
  -- the saddle condition
  have hsad : ∀ t, ∀ y ∈ stickySet Q t, E.β ^ t * periodU E Q t y
      + E.γ / E.yT * (disc E.r t * stickyNetRes E Q t y)
      ≤ E.β ^ t * periodU E Q t (c t) + E.γ / E.yT * (disc E.r t * stickyNetRes E Q t (c t)) := by
    intro t y hyS
    rw [disc_eq_pow hβr]
    have hβt : 0 ≤ E.β ^ t := pow_nonneg hβ.le t
    have hcT : (c t).cT = E.yT := by
      by_cases ht : t = 0
      · subst ht; simp [c, shockChoice]
      · simp [c, shockChoice, ht]
    have key : periodU E Q t y + E.γ / E.yT * stickyNetRes E Q t y
        ≤ periodU E Q t (c t) + E.γ / E.yT * stickyNetRes E Q t (c t) := by
      by_cases ht : t = 0
      · subst ht
        have h1 := stickyLagrangian_le hE Q (hQ 0) (hc 0) hyS
          (by simp [c, shockChoice, Q, shockPrices]) (shock_intra hE hM0 hμ hx 0)
          (by
            have := (shock_moneyFOC0_iff hE hβr hM0 hμ hx).mpr hF
            simpa [c, shockChoice, Q] using this)
          (by
            have := (shock_markup_iff hE (μ := μ) hM0 hx).mpr hdd
            simpa [c, shockChoice, Q] using this)
        rw [hcT] at h1
        exact h1
      · have hyS' : y ∈ posChoice := by simpa [stickySet, ht] using hyS
        have h1 := periodLagrangian_le E Q hE hQ t (hc t) hyS' (shock_intra hE hM0 hμ hx t)
          (shock_money_later hE hβr hM0 hμ hx ht) (shock_labour_later hE hM0 hμ ht)
        rw [hcT] at h1
        simpa [stickyNetRes, ht] using h1
    have := mul_le_mul_of_nonneg_left key hβt
    nlinarith
  refine ⟨hQ, isOptimal_of_saddle (μ0 := E.γ / E.yT) hr (div_pos hγ0 hyT).le hadm hsum hnp htv
    hsad, ?_, ?_, ?_⟩
  · intro t
    by_cases ht : t = 0
    · subst ht; simp [c, shockChoice, Q, shockPrices]
    · simp [c, shockChoice, Q, shockPrices, ht]
  · intro t
    by_cases ht : t = 0
    · subst ht; simp [c, shockChoice]
    · simp [c, shockChoice, ht]
  · intro t
    by_cases ht : t = 0
    · subst ht; simp [Q, shockPrices, moneyPrev]
    · obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ht
      by_cases hs : s = 0 <;> simp [Q, shockPrices, moneyPrev, c, shockChoice, hs]


/-- A single-date perturbation that keeps net resources weakly higher cannot raise date-`t`
utility at an optimum, for ANY infinite-horizon problem (O&R §10.2.2; generic form of
`NontradablesModel.isLocalMax_of_perturb`), stated on a set `s` of perturbation sizes. -/
theorem perturb_le_gen {X : Type*} {β r A0 : ℝ} (hr : 0 < 1 + r) (hβ : 0 < β)
    {U h : ℕ → X → ℝ} {D : ℕ → Set X} {c : ℕ → X} (hopt : IsOptimal β r A0 U h D c) (t : ℕ)
    (g : ℝ → X) {η : ℝ} (hη : g η ∈ D t) (hres : h t (c t) ≤ h t (g η)) :
    U t (g η) ≤ U t (c t) := by
  set x' : ℕ → X := Function.update c t (g η)
  have hS : ∀ s ∉ ({t} : Finset ℕ), x' s = c s := by
    intro s hs
    simp only [Finset.mem_singleton] at hs
    simp [x', Function.update_of_ne hs]
  have hx' : ∀ s, x' s ∈ D s := by
    intro s
    by_cases hs : s = t
    · subst hs; simpa [x'] using hη
    · rw [hS s (by simpa using hs)]; exact hopt.1 s
  have hpv : 0 ≤ ∑ s ∈ ({t} : Finset ℕ), disc r s * (h s (x' s) - h s (c s)) := by
    simp only [Finset.sum_singleton, x', Function.update_self]
    exact mul_nonneg (disc_pos hr t).le (by linarith)
  have hh := perturb_utility_le_of_pv hr hopt hx' hS hpv
  simp only [Finset.sum_singleton, x', Function.update_self] at hh
  have hβt : 0 < β ^ t := pow_pos hβ t
  nlinarith

/-- NECESSITY (O&R §10.2.4): if the shock path is a sticky-price equilibrium, then `x` solves the
impact equation `μ^ε(1 − βx/μ) = (1−β)x^{1−γ+γε}` (necessity of the money condition on
impact) AND `x² ≤ θ/(θ−1)` (a producer would ration at a preset price below marginal cost). -/
theorem shock_necessary {E : Economy} (hE : E.Valid) (hβr : E.β * (1 + E.r) = 1)
    {M0 μ x : ℝ} (hM0 : 0 < M0) (hμ : 0 < μ) (hx : 0 < x)
    (hQ : (shockPrices E M0 μ x).Valid E.r)
    (heq : IsStickyEquilibrium E (shockPrices E M0 μ x) 0 M0 (fun _ => μ * M0)
      (shockChoice E M0 μ x)) :
    impactGap E.β E.γ E.ε μ x = 0 ∧ x ^ 2 ≤ E.θ / (E.θ - 1) := by
  have hE' := hE
  obtain ⟨hβ, hβ1, hr, hγ0, hγ1, hχ, hε, hκ, hθ, hyT⟩ := hE'
  have hopt := heq.1
  have hy := ybarN_pos hE
  have hT := pT0_pos hE hM0
  set Q := shockPrices E M0 μ x with hQdef
  obtain ⟨hPT, hPN, hCA, hu⟩ := hQ 0
  have hP : 0 < cpiAt E Q 0 := cpi_pos hγ0 hγ1 hPT hPN
  set ι := userCost E.r Q 0
  set P := cpiAt E Q 0
  set ρ := relPrice Q 0
  have hρ : 0 < ρ := div_pos hPN hPT
  have hc0 : shockChoice E M0 μ x 0 = ⟨E.yT, x * ybarN E, μ * M0, x * ybarN E⟩ := by
    simp [shockChoice]
  have hCA0 : Q.CA 0 = x * ybarN E := by simp [Q, shockPrices]
  refine ⟨?_, ?_⟩
  · -- the money perturbation on impact
    set g : ℝ → Choice := fun η => ⟨E.yT - ι * η, x * ybarN E, μ * M0 + η, x * ybarN E⟩
    have hmax : IsLocalMax (fun η => periodU E Q 0 (g η)) 0 := by
      have h1 : ∀ᶠ η in 𝓝 (0 : ℝ), 0 < E.yT - ι * η :=
        (continuous_const.sub (continuous_const.mul continuous_id)).continuousAt.eventually
          (lt_mem_nhds (by simpa using hyT))
      have h2 : ∀ᶠ η in 𝓝 (0 : ℝ), 0 < μ * M0 + η :=
        (continuous_const.add continuous_id).continuousAt.eventually
          (lt_mem_nhds (by simpa using mul_pos hμ hM0))
      filter_upwards [h1, h2] with η e1 e2
      have hmem : g η ∈ stickySet Q 0 := by
        simp only [stickySet, ↓reduceIte, Set.mem_ofPred_eq, g, hCA0]
        exact ⟨⟨e1, by positivity, e2, by positivity⟩, le_rfl⟩
      have hres : stickyNetRes E Q 0 (shockChoice E M0 μ x 0) ≤ stickyNetRes E Q 0 (g η) := by
        rw [hc0]; simp only [stickyNetRes, ↓reduceIte, g]; linarith
      have := perturb_le_gen hr hβ hopt 0 g hmem hres
      rw [hc0] at this
      have hg0 : g 0 = ⟨E.yT, x * ybarN E, μ * M0, x * ybarN E⟩ := by simp [g]
      simp only [hg0]
      exact this
    have hfun : (fun η => periodU E Q 0 (g η)) = fun η =>
        E.γ * log (E.yT - ι * η) + moneyU E.χ E.ε ((μ * M0 + η) / P)
          + ((1 - E.γ) * log (x * ybarN E) - E.κ / 2 * (x * ybarN E) ^ 2) := by
      funext η; simp only [periodU, g]; ring
    have hd1 : HasDerivAt (fun η => E.yT - ι * η) (-ι) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).const_mul ι).const_sub E.yT
    have hd2 : HasDerivAt (fun η => (μ * M0 + η) / P) (1 / P) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).const_add (μ * M0)).div_const P
    have hm : HasDerivAt (fun η => moneyU E.χ E.ε ((μ * M0 + η) / P))
        (E.χ * ((μ * M0) / P) ^ (-E.ε) * (1 / P)) 0 := by
      have := (hasDerivAt_moneyU E.χ E.ε (z := (μ * M0 + 0) / P)
        (by simpa using div_pos (mul_pos hμ hM0) hP)).comp (0 : ℝ) hd2
      convert this using 1 <;> first | rfl | simp
    have hd : HasDerivAt (fun η => periodU E Q 0 (g η))
        (E.γ * (-ι / E.yT) + E.χ * ((μ * M0) / P) ^ (-E.ε) * (1 / P)) 0 := by
      rw [hfun]
      have e1 := (hd1.log (by simpa using hyT.ne')).const_mul E.γ
      simp only [mul_zero, sub_zero] at e1
      exact (e1.add hm).add_const _
    have h0 := hmax.hasDerivAt_eq_zero hd
    have hfoc : E.χ * (μ * M0 / P) ^ (-E.ε) / P = E.γ / E.yT * ι := by
      field_simp at h0 ⊢; linarith
    exact (shock_moneyFOC0_iff hE hβr hM0 hμ hx).mp hfoc
  · -- cutting output at the preset price is always feasible
    set g : ℝ → Choice := fun η => ⟨E.yT + ρ * η, x * ybarN E, μ * M0, x * ybarN E + η⟩
    have hmaxOn : IsLocalMaxOn (fun η => periodU E Q 0 (g η)) (Set.Iic 0) 0 := by
      have h1 : ∀ᶠ η in 𝓝 (0 : ℝ), 0 < E.yT + ρ * η :=
        (continuous_const.add (continuous_const.mul continuous_id)).continuousAt.eventually
          (lt_mem_nhds (by simpa using hyT))
      have h2 : ∀ᶠ η in 𝓝 (0 : ℝ), 0 < x * ybarN E + η :=
        (continuous_const.add continuous_id).continuousAt.eventually
          (lt_mem_nhds (by simpa using mul_pos hx hy))
      have h12 := (h1.and h2)
      filter_upwards [nhdsWithin_le_nhds h12, self_mem_nhdsWithin] with η ⟨e1, e2⟩ e3
      simp only [Set.mem_Iic] at e3
      have hmem : g η ∈ stickySet Q 0 := by
        simp only [stickySet, ↓reduceIte, Set.mem_ofPred_eq, g, hCA0]
        exact ⟨⟨e1, by positivity, by positivity, e2⟩, by linarith⟩
      have hres : stickyNetRes E Q 0 (shockChoice E M0 μ x 0) ≤ stickyNetRes E Q 0 (g η) := by
        rw [hc0]; simp only [stickyNetRes, ↓reduceIte, g]; linarith
      have := perturb_le_gen hr hβ hopt 0 g hmem hres
      rw [hc0] at this
      have hg0 : g 0 = ⟨E.yT, x * ybarN E, μ * M0, x * ybarN E⟩ := by simp [g]
      simp only [hg0]
      exact this
    have hfun : (fun η => periodU E Q 0 (g η)) = fun η =>
        E.γ * log (E.yT + ρ * η) - E.κ / 2 * (x * ybarN E + η) ^ 2
          + ((1 - E.γ) * log (x * ybarN E) + moneyU E.χ E.ε (μ * M0 / P)) := by
      funext η; simp only [periodU, g]; ring
    have hd1 : HasDerivAt (fun η => E.yT + ρ * η) ρ 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).const_mul ρ).const_add E.yT
    have hsq : HasDerivAt (fun η => (x * ybarN E + η) ^ 2) (2 * (x * ybarN E)) 0 := by
      have := (hasDerivAt_pow 2 (x * ybarN E + 0)).comp (0 : ℝ)
        ((hasDerivAt_id (0 : ℝ)).const_add (x * ybarN E))
      convert this using 1 <;> first | rfl | simp
    have hd : HasDerivAt (fun η => periodU E Q 0 (g η))
        (E.γ * (ρ / E.yT) - E.κ / 2 * (2 * (x * ybarN E))) 0 := by
      rw [hfun]
      have e1 := (hd1.log (by simpa using hyT.ne')).const_mul E.γ
      simp only [mul_zero, add_zero] at e1
      exact (e1.sub (hsq.const_mul (E.κ / 2))).add_const _
    have hcone : (-1 : ℝ) ∈ posTangentConeAt (Set.Iic (0 : ℝ)) 0 :=
      mem_posTangentConeAt_of_segment_subset
        ((convex_Iic (0 : ℝ)).segment_subset (by simp) (by norm_num))
    have hnp := hmaxOn.hasFDerivWithinAt_nonpos hd.hasFDerivAt.hasFDerivWithinAt hcone
    have hnp' : -(E.γ * (ρ / E.yT) - E.κ / 2 * (2 * (x * ybarN E))) ≤ 0 := by
      simpa using hnp
    have hMC : E.κ * (x * ybarN E) ≤ E.γ / E.yT * ρ := by
      have : E.γ * (ρ / E.yT) = E.γ / E.yT * ρ := by ring
      linarith
    exact (shock_markup_iff hE hM0 hx).mp hMC

/-- EXACT CHARACTERISATION (O&R §10.2.4): the shock path is a sticky-price equilibrium IF AND
ONLY IF `x` solves the impact equation and `x² ≤ θ/(θ−1)`. In particular the impact response is
UNIQUE, and it exists iff the unique root of the impact equation lies in the demand-determined
range. -/
theorem shock_equilibrium_iff {E : Economy} (hE : E.Valid) (hβr : E.β * (1 + E.r) = 1)
    {M0 μ x : ℝ} (hM0 : 0 < M0) (hμ : 0 < μ) (hx : 0 < x) :
    ((shockPrices E M0 μ x).Valid E.r ∧
      IsStickyEquilibrium E (shockPrices E M0 μ x) 0 M0 (fun _ => μ * M0)
        (shockChoice E M0 μ x)) ↔
      impactGap E.β E.γ E.ε μ x = 0 ∧ x ^ 2 ≤ E.θ / (E.θ - 1) :=
  ⟨fun ⟨hQ, heq⟩ => shock_necessary hE hβr hM0 hμ hx hQ heq,
    fun ⟨hF, hdd⟩ => shock_isStickyEquilibrium hE hβr hM0 hμ hx hF hdd⟩


/-- "SMALL SHOCKS" MADE PRECISE (O&R pp. 674, 692): for every permanent money shock `μ` close
enough to `1` the sticky-price equilibrium EXISTS (the unique impact response satisfies
`x² < θ/(θ−1)`), and it is unique by `shock_equilibrium_iff`. -/
theorem shock_equilibrium_exists_near_one {E : Economy} (hE : E.Valid)
    (hβr : E.β * (1 + E.r) = 1) {M0 : ℝ} (hM0 : 0 < M0) :
    ∀ᶠ μ in 𝓝 (1 : ℝ), ∃ x, 0 < x ∧ impactGap E.β E.γ E.ε μ x = 0 ∧
      (shockPrices E M0 μ x).Valid E.r ∧
      IsStickyEquilibrium E (shockPrices E M0 μ x) 0 M0 (fun _ => μ * M0)
        (shockChoice E M0 μ x) := by
  have hE' := hE
  obtain ⟨hβ, hβ1, _, hγ0, hγ1, _, hε, _, hθ, _⟩ := hE'
  set xm := sqrt (E.θ / (E.θ - 1)) with hxm
  have hq : 1 < E.θ / (E.θ - 1) := by rw [one_lt_div (by linarith)]; linarith
  have hxm1 : 1 < xm := by
    rw [hxm, lt_sqrt zero_le_one]; simpa using hq
  have hxm0 : 0 < xm := by linarith
  have hF1 : impactGap E.β E.γ E.ε 1 xm < 0 := by
    have h1 : impactGap E.β E.γ E.ε 1 1 = 0 := by rw [impactGap_at_mu one_pos]; simp
    have := impactGap_strictAntiOn hβ hβ1 hγ0 hγ1 hε one_pos (Set.mem_Ici.mpr zero_le_one)
      (Set.mem_Ici.mpr hxm0.le) hxm1
    linarith
  have hcont : ContinuousAt (fun μ => impactGap E.β E.γ E.ε μ xm) 1 := by
    unfold impactGap
    exact ((continuousAt_rpow_const 1 E.ε (Or.inl one_ne_zero)).mul (continuousAt_const.sub
      (continuousAt_const.div continuousAt_id one_ne_zero))).sub continuousAt_const
  filter_upwards [hcont.eventually (gt_mem_nhds hF1), Ioi_mem_nhds (zero_lt_one' ℝ)]
    with μ hFμ hμ
  simp only [Set.mem_Ioi] at hμ
  obtain ⟨x, hx0, _, hx, _⟩ := impact_exists_unique hβ hβ1 hγ0 hγ1 hε hμ
  have hxlt : x < xm := by
    by_contra hle; push Not at hle
    rcases eq_or_lt_of_le hle with he | hlt
    · rw [← he] at hx; linarith
    · have := impactGap_strictAntiOn hβ hβ1 hγ0 hγ1 hε hμ (Set.mem_Ici.mpr hxm0.le)
        (Set.mem_Ici.mpr hx0.le) hlt
      linarith
  have hdd : x ^ 2 ≤ E.θ / (E.θ - 1) := by
    have : x ^ 2 < xm ^ 2 := by nlinarith
    rw [hxm, sq_sqrt (by linarith)] at this
    exact this.le
  obtain ⟨hQ, heq⟩ := shock_isStickyEquilibrium hE hβr hM0 hμ hx0 hx hdd
  exact ⟨x, hx0, hx, hQ, heq⟩

/-! ## Positive consequences: exchange rate and nontradables output -/

/-- The nominal exchange rate `𝓔 = P_T/P_T^*` with `P_T^*` constant (law of one price,
O&R (83) and p. 693: `p_T = e`). -/
noncomputable def exchangeRate (PTstar PT : ℝ) : ℝ := PT / PTstar

/-- On the shock path `𝓔_1/𝓔_0 = x` and `𝓔_t/𝓔_0 = μ` from date 2 (O&R p. 693, `p_T = e`). -/
theorem shock_exchangeRate {E : Economy} (hE : E.Valid) {M0 μ x PTstar : ℝ} (hM0 : 0 < M0)
    (hs : 0 < PTstar) :
    exchangeRate PTstar ((shockPrices E M0 μ x).PT 0) / exchangeRate PTstar (pT0 E M0) = x ∧
      ∀ t, t ≠ 0 → exchangeRate PTstar ((shockPrices E M0 μ x).PT t)
        / exchangeRate PTstar (pT0 E M0) = μ := by
  have hT := pT0_pos hE hM0
  refine ⟨?_, fun t ht => ?_⟩
  · simp only [exchangeRate, shockPrices, ↓reduceIte]; field_simp
  · simp only [exchangeRate, shockPrices, ht, ↓reduceIte]; field_simp

/-- EXCHANGE-RATE OVERSHOOTING IN EQUILIBRIUM (O&R (99), p. 693, exact): on any sticky-price
equilibrium path after a permanent monetary expansion `μ > 1`, the exchange rate jumps above its
new long-run level (`𝓔_1 > 𝓔̄ = μ𝓔_0`) IF AND ONLY IF `ε > 1`. -/
theorem exchangeRate_overshoots_iff {E : Economy} (hE : E.Valid) (hβr : E.β * (1 + E.r) = 1)
    {M0 μ x PTstar : ℝ} (hM0 : 0 < M0) (hμ : 1 < μ) (hx : 0 < x) (hs : 0 < PTstar)
    (hQ : (shockPrices E M0 μ x).Valid E.r)
    (heq : IsStickyEquilibrium E (shockPrices E M0 μ x) 0 M0 (fun _ => μ * M0)
      (shockChoice E M0 μ x)) :
    exchangeRate PTstar ((shockPrices E M0 μ x).PT 1)
        < exchangeRate PTstar ((shockPrices E M0 μ x).PT 0) ↔ 1 < E.ε := by
  have hμ0 : 0 < μ := by linarith
  have hT := pT0_pos hE hM0
  obtain ⟨hF, _⟩ := shock_necessary hE hβr hM0 hμ0 hx hQ heq
  obtain ⟨hβ, hβ1, _, hγ0, hγ1, _, hε, _, _, _⟩ := hE
  have h := (overshoot_iff hβ hβ1 hγ0 hγ1 hε hμ hx hF).1
  simp only [exchangeRate, shockPrices, Nat.one_ne_zero, ↓reduceIte]
  rw [div_lt_div_iff_of_pos_right hs, mul_lt_mul_iff_left₀ hT]
  exact h

/-- (95), p. 693: on impact nontradables consumption and output rise by the factor `x > 1`
(`C_N = y_N = xȳ_N`), and tradables consumption is unchanged (O&R (91)). -/
theorem shock_output_rises {E : Economy} (hE : E.Valid) {M0 μ x : ℝ} (hβ : 0 < E.β)
    (hβ1 : E.β < 1) (hμ : 1 < μ) (hx : 0 < x) (hF : impactGap E.β E.γ E.ε μ x = 0) :
    (shockChoice E M0 μ x 0).cN = x * ybarN E ∧ (shockChoice E M0 μ x 0).y = x * ybarN E ∧
      ybarN E < (shockChoice E M0 μ x 0).y ∧ (shockChoice E M0 μ x 0).cT = E.yT := by
  have hy := ybarN_pos hE
  obtain ⟨_, _, _, hγ0, hγ1, _, hε, _, _, _⟩ := hE
  have hx1 := one_lt_root hβ hβ1 hγ0 hγ1 hε hμ hx hF
  exact ⟨by simp [shockChoice], by simp [shockChoice],
    by simp only [shockChoice, ↓reduceIte]; nlinarith, by simp [shockChoice]⟩

/-- (95), p. 693, exactly: on impact `y_N = C_N = ((1−γ)/γ)(P_{T,1}/P̄_{N,0}) ȳ_T`, with the
nontradables price preset at its pre-shock level. -/
theorem shock_95 {E : Economy} (hE : E.Valid) {M0 μ x : ℝ} (hM0 : 0 < M0) :
    (shockChoice E M0 μ x 0).cN
      = (1 - E.γ) / E.γ * ((shockPrices E M0 μ x).PT 0 / (shockPrices E M0 μ x).PN 0) * E.yT ∧
      (shockChoice E M0 μ x 0).y = (shockChoice E M0 μ x 0).cN := by
  have hT := pT0_pos hE hM0
  have hy := ybarN_pos hE
  obtain ⟨_, _, _, hγ0, hγ1, _, _, _, _, hyT⟩ := hE
  refine ⟨?_, by simp [shockChoice]⟩
  simp only [shockChoice, shockPrices, ↓reduceIte, pN0, relPriceBar]
  have : (1 : ℝ) - E.γ ≠ 0 := by linarith
  field_simp

/-! ## Welfare (p. 694) -/

/-- The real-utility gain on impact, `(1−γ)[log x − ((θ−1)/(2θ))(x² − 1)]` (O&R p. 694). -/
noncomputable def realGain (θ γ x : ℝ) : ℝ := (1 - γ) * (log x - (θ - 1) / (2 * θ) * (x ^ 2 - 1))

/-- The real-utility gain is strictly positive on the whole demand-determined range
`1 < x ≤ (θ/(θ−1))^{1/2}` (O&R p. 694, exact). -/
theorem realGain_pos {θ γ x : ℝ} (hθ : 1 < θ) (hγ1 : γ < 1) (hx : 1 < x)
    (hdd : x ^ 2 ≤ θ / (θ - 1)) : 0 < realGain θ γ x := by
  unfold realGain
  apply mul_pos (by linarith)
  have hx2 : 1 < x ^ 2 := by nlinarith
  have hx0 : 0 < x := by linarith
  -- `log x = log(x²)/2 > (1 − 1/x²)/2 ≥ ((θ−1)/θ)(x² − 1)/2`
  have hlog : log (x ^ 2) = 2 * log x := by
    rw [show x ^ 2 = x ^ (2 : ℕ) by rfl, log_pow]; norm_num
  have hstrict : 1 - 1 / x ^ 2 < log (x ^ 2) := by
    have h := log_lt_sub_one_of_pos (by positivity : 0 < 1 / x ^ 2) (by
      intro h; field_simp at h; linarith)
    rw [one_div, log_inv] at h
    rw [one_div]; linarith
  have hb : (θ - 1) / θ * (x ^ 2 - 1) ≤ 1 - 1 / x ^ 2 := by
    have h1 : (θ - 1) / θ ≤ 1 / x ^ 2 := by
      rw [div_le_div_iff₀ (by linarith) (by positivity)]
      rw [le_div_iff₀ (by linarith)] at hdd
      linarith
    have : 1 - 1 / x ^ 2 = 1 / x ^ 2 * (x ^ 2 - 1) := by field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_right h1 (by linarith)
  have e : (θ - 1) / (2 * θ) * (x ^ 2 - 1) = ((θ - 1) / θ * (x ^ 2 - 1)) / 2 := by
    field_simp
  rw [e]
  linarith

/-- Period utility on the shock path after impact equals the pre-shock period utility
(O&R p. 694: "later periods are unchanged", money being neutral from date 2). -/
theorem shock_periodU_later {E : Economy} (hE : E.Valid) {M0 μ x : ℝ} (hM0 : 0 < M0)
    (hμ : 0 < μ) (hx : 0 < x) {t : ℕ} (ht : t ≠ 0) (s : ℕ) :
    periodU E (shockPrices E M0 μ x) t (shockChoice E M0 μ x t)
      = periodU E (steadyPrices E M0) s (steadyChoice E M0 s) := by
  obtain ⟨_, hP⟩ := shock_cpi hE hM0 hμ hx
  have hPs : cpiAt E (steadyPrices E M0) s = pT0 E M0 * cpiRatio E := by
    simp only [cpiAt, steadyPrices]
    exact cpi_initial hE hM0
  unfold periodU
  rw [hP t ht, hPs]
  simp only [shockChoice, steadyChoice, ht, ↓reduceIte]
  rw [show μ * M0 / (μ * (pT0 E M0 * cpiRatio E)) = M0 / (pT0 E M0 * cpiRatio E) by
    field_simp]

/-- THE EXACT WELFARE GAIN (O&R p. 694, T29): lifetime utility from the shock date on the
sticky-price path minus that on the no-shock path equals
`(1−γ)[log x − ((θ−1)/(2θ))(x² − 1)] + [v((μ/x^γ)(M/P)‾) − v((M/P)‾)]`: only the impact period
differs (genuine infinite-horizon sums). -/
theorem welfare_gain_eq {E : Economy} (hE : E.Valid) {M0 μ x : ℝ} (hM0 : 0 < M0) (hμ : 0 < μ)
    (hx : 0 < x) :
    Summable (fun t => E.β ^ t * periodU E (steadyPrices E M0) t (steadyChoice E M0 t)) ∧
    Summable (fun t => E.β ^ t * periodU E (shockPrices E M0 μ x) t (shockChoice E M0 μ x t)) ∧
    ∑' t, E.β ^ t * periodU E (shockPrices E M0 μ x) t (shockChoice E M0 μ x t)
      - ∑' t, E.β ^ t * periodU E (steadyPrices E M0) t (steadyChoice E M0 t)
      = realGain E.θ E.γ x + (moneyU E.χ E.ε (μ / x ^ E.γ * realMoneyBar E)
          - moneyU E.χ E.ε (realMoneyBar E)) := by
  have hy := ybarN_pos hE
  have hk := kappa_mul_ybarN_sq hE
  have hmd := M0_div_cpi hE hM0
  obtain ⟨hP0, _⟩ := shock_cpi hE hM0 hμ hx
  have hβ := hE.1
  have hβ1 := hE.2.1
  have hθ := hE.2.2.2.2.2.2.2.2.1
  set ub := periodU E (steadyPrices E M0) 0 (steadyChoice E M0 0)
  have hbase : (fun t => E.β ^ t * periodU E (steadyPrices E M0) t (steadyChoice E M0 t))
      = fun t => E.β ^ t * ub := by funext t; rfl
  have hsb : Summable fun t => E.β ^ t * ub :=
    (summable_geometric_of_lt_one hβ.le hβ1).mul_right ub
  have hoff : ∀ t ∉ ({0} : Finset ℕ),
      E.β ^ t * periodU E (shockPrices E M0 μ x) t (shockChoice E M0 μ x t) = E.β ^ t * ub := by
    intro t ht
    have ht0 : t ≠ 0 := by simpa using ht
    rw [shock_periodU_later hE hM0 hμ hx ht0 0]
  obtain ⟨hss, htsum⟩ := tsum_eq_add_of_eq_off hsb {0} hoff
  refine ⟨hbase ▸ hsb, hss, ?_⟩
  rw [hbase, htsum, Finset.sum_singleton, pow_zero, one_mul, one_mul, add_sub_cancel_left]
  have hPs : cpiAt E (steadyPrices E M0) 0 = pT0 E M0 * cpiRatio E := by
    simp only [cpiAt, steadyPrices]; exact cpi_initial hE hM0
  simp only [ub, periodU, hP0, hPs, shockChoice, steadyChoice, ↓reduceIte]
  rw [hmd, show μ * M0 / (x ^ E.γ * (pT0 E M0 * cpiRatio E))
      = μ / x ^ E.γ * (M0 / (pT0 E M0 * cpiRatio E)) by field_simp, hmd,
    log_mul hx.ne' hy.ne']
  unfold realGain
  have e : E.κ / 2 * (x * ybarN E) ^ 2 - E.κ / 2 * ybarN E ^ 2
      = (E.θ - 1) * (1 - E.γ) / E.θ / 2 * (x ^ 2 - 1) := by
    rw [← hk]; ring
  field_simp at e ⊢
  linear_combination (-1 : ℝ) * e

/-- A MONEY SHOCK UNAMBIGUOUSLY IMPROVES WELFARE (O&R p. 694, exact): for a permanent expansion
`μ > 1` whose impact response is demand-determined (`x² ≤ θ/(θ−1)`), lifetime utility on the
sticky-price path strictly exceeds that on the no-shock path — both the real-utility gain and
the real-balance gain are strictly positive. -/
theorem welfare_gain_pos {E : Economy} (hE : E.Valid) {M0 μ x : ℝ} (hM0 : 0 < M0) (hμ : 1 < μ)
    (hx : 0 < x) (hF : impactGap E.β E.γ E.ε μ x = 0) (hdd : x ^ 2 ≤ E.θ / (E.θ - 1)) :
    ∑' t, E.β ^ t * periodU E (steadyPrices E M0) t (steadyChoice E M0 t)
      < ∑' t, E.β ^ t * periodU E (shockPrices E M0 μ x) t (shockChoice E M0 μ x t) := by
  have hμ0 : 0 < μ := by linarith
  obtain ⟨_, _, heqn⟩ := welfare_gain_eq hE hM0 hμ0 hx
  have hmb := realMoneyBar_pos hE
  obtain ⟨hβ, hβ1, _, hγ0, hγ1, hχ, hε, _, hθ, _⟩ := hE
  have hx1 := one_lt_root hβ hβ1 hγ0 hγ1 hε hμ hx hF
  have hr := realGain_pos hθ hγ1 hx1 hdd
  have hrb := realBalances_rise hβ hβ1 hγ0 hγ1 hε hμ hx hF
  have hm : moneyU E.χ E.ε (realMoneyBar E) < moneyU E.χ E.ε (μ / x ^ E.γ * realMoneyBar E) :=
    moneyU_strictMonoOn hχ (Set.mem_Ioi.mpr hmb) (Set.mem_Ioi.mpr (by positivity))
      (by nlinarith)
  linarith

/-- First-order welfare (O&R p. 694): the derivative of the real-utility gain at `μ = 1` is
`(1−γ)/θ` times the (99) coefficient, i.e. `dU^R = (1−γ) p_T/θ > 0`. -/
theorem hasDerivAt_realGain {β γ ε θ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hγ0 : 0 < γ)
    (hγ1 : γ < 1) (hε : 0 < ε) (hθ : 1 < θ) {X : ℝ → ℝ}
    (hX : ∀ᶠ μ in 𝓝 1, 0 < X μ ∧ impactGap β γ ε μ (X μ) = 0) :
    HasDerivAt (fun μ => realGain θ γ (X μ))
      ((1 - γ) / θ * ((β + (1 - β) * ε) / (β + (1 - β) * expo γ ε))) 1 := by
  have hd := hasDerivAt_impact hβ hβ1 hγ0 hγ1 hε hX
  have hX1 : X 1 = 1 := by
    obtain ⟨z, _, _, _, huniq⟩ := impact_exists_unique hβ hβ1 hγ0 hγ1 hε one_pos
    have h1 : impactGap β γ ε 1 1 = 0 := by
      rw [impactGap_at_mu one_pos]; simp
    rw [huniq (X 1) hX.self_of_nhds.1 hX.self_of_nhds.2, huniq 1 one_pos h1]
  set k := (β + (1 - β) * ε) / (β + (1 - β) * expo γ ε)
  have hlog := hd.log (by rw [hX1]; exact one_ne_zero)
  have hsq := hd.pow 2
  have h := ((hlog.sub ((hsq.sub_const 1).const_mul ((θ - 1) / (2 * θ))))).const_mul (1 - γ)
  have e : (fun μ => realGain θ γ (X μ))
      = fun μ => (1 - γ) * (log (X μ) - (θ - 1) / (2 * θ) * (X μ ^ 2 - 1)) := rfl
  rw [e]
  convert h using 1
  · rw [hX1]
    have : θ ≠ 0 := by linarith
    field_simp
    ring

/-! ## Exercise 2: the real exchange rate and the real interest rate (p. 713) -/

/-- The real exchange rate `Q = 𝓔P^*/P` with `𝓔 = P_T/P_T^*` and the foreign CPI `P^*`
constant (the book never defines it in §10.2; O&R Ex. 2, p. 713). -/
noncomputable def realExchangeRate (PTstar Pstar PT P : ℝ) : ℝ := PT / PTstar * Pstar / P

/-- The gross consumption-based real interest rate `1 + r^C_{t+1} = (1+i_{t+1})P_t/P_{t+1}`,
with interest parity `1 + i_{t+1} = (1+r)P_{T,t+1}/P_{T,t}` (O&R Ex. 2, p. 713). -/
noncomputable def grossRealRate (r PT PT' P P' : ℝ) : ℝ := (1 + r) * (PT' / PT) * (P / P')

/-- EXACT REAL INTEREST PARITY (O&R Ex. 2): `1 + r^C_{t+1} = (1+r) Q_{t+1}/Q_t`, for any positive
price paths. -/
theorem real_interest_parity {r PTstar Pstar PT PT' P P' : ℝ} (hs : 0 < PTstar)
    (hps : 0 < Pstar) (hT : 0 < PT) (hP : 0 < P) (hP' : 0 < P') :
    grossRealRate r PT PT' P P'
      = (1 + r) * (realExchangeRate PTstar Pstar PT' P' / realExchangeRate PTstar Pstar PT P) := by
  unfold grossRealRate realExchangeRate
  field_simp

/-- EXERCISE 2 ANSWERED EXACTLY (O&R p. 713): on the sticky-price path after a permanent
expansion `μ > 1`, for EVERY `ε > 0`, the real exchange rate depreciates on impact,
`Q_1/Q_0 = x^{1−γ} > 1`, returns to `Q_0` from date 2, and the consumption-based real interest
rate between dates 1 and 2 falls below `r`: `1 + r^C_2 = (1+r) x^{−(1−γ)} < 1 + r`. In logs,
`log(1 + r^C_2) − log(1+r) = −log(Q_1/Q_0)` (coefficient exactly one): the Dornbusch-type
co-movement holds without any need for overshooting. -/
theorem ex2_real_depreciation {E : Economy} (hE : E.Valid) {M0 μ x PTstar Pstar : ℝ}
    (hM0 : 0 < M0) (hμ : 1 < μ) (hx : 0 < x) (hF : impactGap E.β E.γ E.ε μ x = 0)
    (hs : 0 < PTstar) (hps : 0 < Pstar) :
    realExchangeRate PTstar Pstar ((shockPrices E M0 μ x).PT 0) (cpiAt E (shockPrices E M0 μ x) 0)
        / realExchangeRate PTstar Pstar (pT0 E M0) (pT0 E M0 * cpiRatio E) = x ^ (1 - E.γ) ∧
      1 < x ^ (1 - E.γ) ∧
      realExchangeRate PTstar Pstar ((shockPrices E M0 μ x).PT 1)
        (cpiAt E (shockPrices E M0 μ x) 1)
        = realExchangeRate PTstar Pstar (pT0 E M0) (pT0 E M0 * cpiRatio E) ∧
      grossRealRate E.r ((shockPrices E M0 μ x).PT 0) ((shockPrices E M0 μ x).PT 1)
          (cpiAt E (shockPrices E M0 μ x) 0) (cpiAt E (shockPrices E M0 μ x) 1)
        = (1 + E.r) * (x ^ (1 - E.γ))⁻¹ ∧
      grossRealRate E.r ((shockPrices E M0 μ x).PT 0) ((shockPrices E M0 μ x).PT 1)
          (cpiAt E (shockPrices E M0 μ x) 0) (cpiAt E (shockPrices E M0 μ x) 1) < 1 + E.r := by
  have hμ0 : 0 < μ := by linarith
  have hT := pT0_pos hE hM0
  have hcr := cpiRatio_pos hE
  obtain ⟨hP0, hP⟩ := shock_cpi hE hM0 hμ0 hx
  have hr := hE.2.2.1
  obtain ⟨hβ, hβ1, _, hγ0, hγ1, _, hε, _, _, _⟩ := hE
  have hx1 := one_lt_root hβ hβ1 hγ0 hγ1 hε hμ hx hF
  have hxg : 0 < x ^ E.γ := rpow_pos_of_pos hx _
  have hsplit : x ^ (1 - E.γ) = x / x ^ E.γ := by rw [rpow_sub hx, rpow_one]
  have hq1 : 1 < x ^ (1 - E.γ) := one_lt_rpow hx1 (by linarith)
  have hP1 := hP 1 Nat.one_ne_zero
  have hPT0 : (shockPrices E M0 μ x).PT 0 = x * pT0 E M0 := by simp [shockPrices]
  have hPT1 : (shockPrices E M0 μ x).PT 1 = μ * pT0 E M0 := by simp [shockPrices]
  have hgr : grossRealRate E.r ((shockPrices E M0 μ x).PT 0) ((shockPrices E M0 μ x).PT 1)
      (cpiAt E (shockPrices E M0 μ x) 0) (cpiAt E (shockPrices E M0 μ x) 1)
      = (1 + E.r) * (x ^ (1 - E.γ))⁻¹ := by
    rw [hP0, hP1, hPT0, hPT1, hsplit]
    unfold grossRealRate
    field_simp
  refine ⟨?_, hq1, ?_, hgr, ?_⟩
  · rw [hP0, hPT0, hsplit]
    unfold realExchangeRate
    field_simp
  · rw [hP1, hPT1]
    unfold realExchangeRate
    field_simp
  · rw [hgr]
    have : (x ^ (1 - E.γ))⁻¹ < 1 := inv_lt_one_of_one_lt₀ hq1
    nlinarith

/-- Exercise 2 in logs (O&R p. 713): `log(1 + r^C_2) − log(1 + r) = −(1−γ) log x
= −log(Q_1/Q_0)`, exactly. -/
theorem ex2_log_parity {r γ x : ℝ} (hr : 0 < 1 + r) (hx : 0 < x) :
    log ((1 + r) * (x ^ (1 - γ))⁻¹) - log (1 + r) = -((1 - γ) * log x) := by
  rw [log_mul hr.ne' (by positivity), log_inv, log_rpow hx]
  ring

/-- Exercise 2 to first order (O&R p. 713): `q = (1−γ) p_T`, i.e. the impact real-depreciation
factor `x(μ)^{1−γ}` has derivative `(1−γ)` times the (99) coefficient at `μ = 1`. -/
theorem hasDerivAt_realDepreciation {β γ ε : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hγ0 : 0 < γ)
    (hγ1 : γ < 1) (hε : 0 < ε) {X : ℝ → ℝ}
    (hX : ∀ᶠ μ in 𝓝 1, 0 < X μ ∧ impactGap β γ ε μ (X μ) = 0) :
    HasDerivAt (fun μ => X μ ^ (1 - γ))
      ((1 - γ) * ((β + (1 - β) * ε) / (β + (1 - β) * expo γ ε))) 1 := by
  have hd := hasDerivAt_impact hβ hβ1 hγ0 hγ1 hε hX
  have hX1 : X 1 = 1 := by
    obtain ⟨z, _, _, _, huniq⟩ := impact_exists_unique hβ hβ1 hγ0 hγ1 hε one_pos
    have h1 : impactGap β γ ε 1 1 = 0 := by
      rw [impactGap_at_mu one_pos]; simp
    rw [huniq (X 1) hX.self_of_nhds.1 hX.self_of_nhds.2, huniq 1 one_pos h1]
  have h := hd.rpow_const (p := 1 - γ) (Or.inl (by rw [hX1]; exact one_ne_zero))
  convert h using 1
  rw [hX1, one_rpow]; ring

/-- The internal real exchange rate `P_T/P_N` also rises by the factor `x` on impact and returns
to its initial value from date 2 (O&R Ex. 2: the sign conclusions coincide). -/
theorem ex2_internal_real_rate {E : Economy} (hE : E.Valid) {M0 μ x : ℝ} (hM0 : 0 < M0)
    (hμ : 0 < μ) :
    (shockPrices E M0 μ x).PT 0 / (shockPrices E M0 μ x).PN 0 = x * (pT0 E M0 / pN0 E M0) ∧
      (shockPrices E M0 μ x).PT 1 / (shockPrices E M0 μ x).PN 1 = pT0 E M0 / pN0 E M0 := by
  have hN := pN0_pos hE hM0
  refine ⟨?_, ?_⟩
  · simp only [shockPrices, ↓reduceIte]; ring
  · simp only [shockPrices, Nat.one_ne_zero, ↓reduceIte]; field_simp

end ObstfeldRogoff.StickyPriceModels.NontradablesOvershooting
