/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Topology.Order.IntermediateValue

/-!
# The two-period consumer

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*,
§1.1, pp. 1–14, and Exercise 1. A household with endowments `Y₁, Y₂ > 0` and
utility `u(C₁) + β u(C₂)` (O&R (1.1)) faces the world interest rate `r`.

The budget set O&R (1.2) is written in the equivalent multiplied-through form
`C₂ ≤ Y₂ + (1 + r)(Y₁ − C₁)`; `feasible_iff_budget` records the equivalence.
The book states the budget as an equality; we allow slack and prove that it
binds at an optimum (`optimal_binds`).

Strict monotonicity and strict concavity of `u` give that the budget binds and
the optimum is unique. With a derivative `u' > 0`, the Euler equation (1.3) is
necessary and sufficient, consumption is flat when `β(1 + r) = 1` (1.5) and
tilts otherwise (p. 4), and an optimum exists under the Inada condition of
footnote 1. Exercise 1 treats a general differentiable `U(C₁, C₂)`: the Euler
condition and the envelope formula for the value function.

The autarky rate and the gains from trade are in `AutarkyGains`.
-/

namespace ObstfeldRogoff.IntertemporalTrade.Consumer

open Set Filter Topology

/-- The tangent line of a concave function lies weakly above its graph. -/
theorem concave_le_tangent {f : ℝ → ℝ} {S : Set ℝ} (hf : ConcaveOn ℝ S f) {x y d : ℝ}
    (hx : x ∈ S) (hy : y ∈ S) (hd : HasDerivAt f d x) : f y ≤ f x + d * (y - x) := by
  rcases lt_trichotomy y x with hyx | rfl | hxy
  · have h := hf.le_slope_of_hasDerivAt hy hx hyx hd
    rw [slope_def_field, le_div_iff₀ (by linarith)] at h
    linarith
  · simp
  · have h := hf.slope_le_of_hasDerivAt hx hy hxy hd
    rw [slope_def_field, div_le_iff₀ (by linarith)] at h
    linarith

/-- The derivative of a strictly concave function is strictly decreasing. -/
theorem deriv_lt_of_strictConcave {f : ℝ → ℝ} {S : Set ℝ} (hf : StrictConcaveOn ℝ S f)
    {x y dx dy : ℝ} (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y) (hdx : HasDerivAt f dx x)
    (hdy : HasDerivAt f dy y) : dy < dx :=
  (hf.lt_slope_of_hasDerivAt hx hy hxy hdy).trans (hf.slope_lt_of_hasDerivAt hx hy hxy hdx)

/-- A two-period household: utility `u(C₁) + β u(C₂)` with `u` strictly increasing and
strictly concave on `(0, ∞)`, `β > 0`, and positive endowments (O&R (1.1), p. 1–2). -/
structure Household where
  u : ℝ → ℝ
  β : ℝ
  Y1 : ℝ
  Y2 : ℝ
  β_pos : 0 < β
  Y1_pos : 0 < Y1
  Y2_pos : 0 < Y2
  mono : StrictMonoOn u (Ioi 0)
  concave : StrictConcaveOn ℝ (Ioi 0) u

namespace Household

variable (h : Household)

/-- Lifetime utility `U = u(C₁) + β u(C₂)`, O&R (1.1). -/
def utility (c1 c2 : ℝ) : ℝ := h.u c1 + h.β * h.u c2

/-- The budget set at world rate `r`: positive consumption and `C₂ ≤ Y₂ + (1 + r)(Y₁ − C₁)`. -/
def Feasible (r c1 c2 : ℝ) : Prop :=
  0 < c1 ∧ 0 < c2 ∧ c2 ≤ h.Y2 + (1 + r) * (h.Y1 - c1)

/-- `(c₁, c₂)` maximises lifetime utility over the budget set at rate `r`. -/
def IsOptimal (r c1 c2 : ℝ) : Prop :=
  h.Feasible r c1 c2 ∧ ∀ d1 d2, h.Feasible r d1 d2 → h.utility d1 d2 ≤ h.utility c1 c2

/-- The multiplied-through budget constraint is O&R (1.2) when `1 + r > 0`. -/
theorem feasible_iff_budget {r c1 c2 : ℝ} (hr : 0 < 1 + r) (hc1 : 0 < c1) (hc2 : 0 < c2) :
    h.Feasible r c1 c2 ↔ c1 + c2 / (1 + r) ≤ h.Y1 + h.Y2 / (1 + r) := by
  unfold Feasible
  simp only [hc1, hc2, true_and]
  rw [← sub_nonneg, ← sub_nonneg (a := h.Y1 + h.Y2 / (1 + r))]
  have e : h.Y1 + h.Y2 / (1 + r) - (c1 + c2 / (1 + r)) =
      (h.Y2 + (1 + r) * (h.Y1 - c1) - c2) / (1 + r) := by
    field_simp
    ring
  rw [e, div_nonneg_iff]
  constructor
  · intro hn
    exact Or.inl ⟨hn, hr.le⟩
  · rintro (⟨hn, -⟩ | ⟨-, hn⟩)
    · exact hn
    · linarith

/-- The endowment is always affordable. -/
theorem endowment_feasible (r : ℝ) : h.Feasible r h.Y1 h.Y2 :=
  ⟨h.Y1_pos, h.Y2_pos, by simp⟩

/-- Utility is strictly increasing in second-period consumption. -/
theorem utility_lt_utility_of_lt {c1 c2 d2 : ℝ} (hc2 : 0 < c2) (hlt : c2 < d2) :
    h.utility c1 c2 < h.utility c1 d2 := by
  have := h.mono (mem_Ioi.2 hc2) (mem_Ioi.2 (hc2.trans hlt)) hlt
  unfold utility
  nlinarith [h.β_pos]

/-- The budget constraint binds at an optimum: `C₂ = Y₂ + (1 + r)(Y₁ − C₁)`. -/
theorem optimal_binds {r c1 c2 : ℝ} (ho : h.IsOptimal r c1 c2) :
    c2 = h.Y2 + (1 + r) * (h.Y1 - c1) := by
  obtain ⟨⟨hc1, hc2, hb⟩, hmax⟩ := ho
  by_contra hne
  have hlt : c2 < h.Y2 + (1 + r) * (h.Y1 - c1) := lt_of_le_of_ne hb hne
  have hf : h.Feasible r c1 (h.Y2 + (1 + r) * (h.Y1 - c1)) := ⟨hc1, hc2.trans hlt, le_rfl⟩
  exact absurd (hmax _ _ hf) (not_le.2 (h.utility_lt_utility_of_lt hc2 hlt))

/-- The optimum is unique (strict concavity of `u`). -/
theorem optimal_unique {r c1 c2 d1 d2 : ℝ} (hc : h.IsOptimal r c1 c2)
    (hd : h.IsOptimal r d1 d2) : c1 = d1 ∧ c2 = d2 := by
  have bc := h.optimal_binds hc
  have bd := h.optimal_binds hd
  by_cases h1 : c1 = d1
  · refine ⟨h1, ?_⟩
    rw [bc, bd, h1]
  exfalso
  obtain ⟨⟨hc1, hc2, -⟩, hcmax⟩ := hc
  obtain ⟨⟨hd1, hd2, -⟩, hdmax⟩ := hd
  have hm : h.Feasible r ((c1 + d1) / 2) ((c2 + d2) / 2) :=
    ⟨by linarith, by linarith, by rw [bc, bd]; linarith⟩
  have huc := h.concave.2 (mem_Ioi.2 hc1) (mem_Ioi.2 hd1) h1 (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
  have hu2 := h.concave.concaveOn.2 (mem_Ioi.2 hc2) (mem_Ioi.2 hd2)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at huc hu2
  have e1 : 1 / 2 * c1 + 1 / 2 * d1 = (c1 + d1) / 2 := by ring
  have e2 : 1 / 2 * c2 + 1 / 2 * d2 = (c2 + d2) / 2 := by ring
  rw [e1] at huc
  rw [e2] at hu2
  have hcd := hcmax d1 d2 ⟨hd1, hd2, by rw [bd]⟩
  have hdc := hdmax c1 c2 ⟨hc1, hc2, by rw [bc]⟩
  have hmc := hcmax _ _ hm
  unfold utility at hcd hdc hmc
  nlinarith [h.β_pos]

/-! ### Differentiable utility -/

variable {u' : ℝ → ℝ}

/-- The objective along the budget line, `t ↦ u(t) + β u(Y₂ + (1 + r)(Y₁ − t))`, has
derivative `u'(t) − (1 + r) β u'(C₂)`. -/
theorem hasDerivAt_budgetLine (hu : ∀ c, 0 < c → HasDerivAt h.u (u' c) c) {r t : ℝ}
    (ht : 0 < t) (ht2 : 0 < h.Y2 + (1 + r) * (h.Y1 - t)) :
    HasDerivAt (fun s => h.utility s (h.Y2 + (1 + r) * (h.Y1 - s)))
      (u' t - (1 + r) * h.β * u' (h.Y2 + (1 + r) * (h.Y1 - t))) t := by
  have hin : HasDerivAt (fun s => h.Y2 + (1 + r) * (h.Y1 - s)) ((1 + r) * (-1)) t :=
    (((hasDerivAt_id t).const_sub h.Y1).const_mul (1 + r)).const_add h.Y2
  have h2 : HasDerivAt (fun s => h.β * h.u (h.Y2 + (1 + r) * (h.Y1 - s)))
      (h.β * (u' (h.Y2 + (1 + r) * (h.Y1 - t)) * ((1 + r) * (-1)))) t :=
    ((hu _ ht2).comp t hin).const_mul h.β
  exact ((hu t ht).add h2).congr_deriv (by ring)

/-- **Euler equation** O&R (1.3), p. 3: at an optimum, `u'(C₁) = (1 + r) β u'(C₂)`. -/
theorem euler_of_optimal (hu : ∀ c, 0 < c → HasDerivAt h.u (u' c) c) {r c1 c2 : ℝ}
    (ho : h.IsOptimal r c1 c2) : u' c1 = (1 + r) * h.β * u' c2 := by
  have hb := h.optimal_binds ho
  obtain ⟨⟨hc1, hc2, -⟩, hmax⟩ := ho
  rw [hb] at hc2 hmax ⊢
  have hcont : Continuous fun s => h.Y2 + (1 + r) * (h.Y1 - s) := by fun_prop
  have hev1 : ∀ᶠ s in 𝓝 c1, 0 < s := Ioi_mem_nhds hc1
  have hev2 : ∀ᶠ s in 𝓝 c1, 0 < h.Y2 + (1 + r) * (h.Y1 - s) :=
    (hcont.tendsto c1).eventually (lt_mem_nhds hc2)
  have hloc : IsLocalMax (fun s => h.utility s (h.Y2 + (1 + r) * (h.Y1 - s))) c1 := by
    filter_upwards [hev1, hev2] with s hs1 hs2
    exact hmax s _ ⟨hs1, hs2, le_rfl⟩
  have := hloc.hasDerivAt_eq_zero (h.hasDerivAt_budgetLine hu hc1 hc2)
  linarith

/-- **Sufficiency of the Euler equation**: a positive plan on the budget line satisfying
(1.3) is optimal. -/
theorem optimal_of_euler (hu : ∀ c, 0 < c → HasDerivAt h.u (u' c) c)
    (hpos : ∀ c, 0 < c → 0 < u' c) {r c1 c2 : ℝ} (hc1 : 0 < c1) (hc2 : 0 < c2)
    (hb : c2 = h.Y2 + (1 + r) * (h.Y1 - c1)) (he : u' c1 = (1 + r) * h.β * u' c2) :
    h.IsOptimal r c1 c2 := by
  refine ⟨⟨hc1, hc2, hb.le⟩, fun d1 d2 ⟨hd1, hd2, hdb⟩ => ?_⟩
  have t1 := concave_le_tangent h.concave.concaveOn (mem_Ioi.2 hc1) (mem_Ioi.2 hd1) (hu c1 hc1)
  have t2 := concave_le_tangent h.concave.concaveOn (mem_Ioi.2 hc2) (mem_Ioi.2 hd2) (hu c2 hc2)
  have hp2 := hpos c2 hc2
  have hβ := h.β_pos
  have key : h.β * u' c2 * (d2 - c2) ≤ - (u' c1 * (d1 - c1)) := by
    rw [he]
    have hd : d2 - c2 ≤ -((1 + r) * (d1 - c1)) := by rw [hb]; linarith
    have hnn : 0 ≤ h.β * u' c2 := by positivity
    nlinarith
  unfold utility
  nlinarith

/-- The Euler equation characterises the optimum. -/
theorem isOptimal_iff_euler (hu : ∀ c, 0 < c → HasDerivAt h.u (u' c) c)
    (hpos : ∀ c, 0 < c → 0 < u' c) {r c1 c2 : ℝ} :
    h.IsOptimal r c1 c2 ↔ 0 < c1 ∧ 0 < c2 ∧ c2 = h.Y2 + (1 + r) * (h.Y1 - c1) ∧
      u' c1 = (1 + r) * h.β * u' c2 :=
  ⟨fun ho => ⟨ho.1.1, ho.1.2.1, h.optimal_binds ho, h.euler_of_optimal hu ho⟩,
    fun ⟨hc1, hc2, hb, he⟩ => h.optimal_of_euler hu hpos hc1 hc2 hb he⟩

/-- **Flat consumption** O&R (1.5), p. 3: if `β(1 + r) = 1` then `C₁ = C₂`. -/
theorem flat_of_beta_mul_eq_one (hu : ∀ c, 0 < c → HasDerivAt h.u (u' c) c) {r c1 c2 : ℝ}
    (hβr : h.β * (1 + r) = 1) (ho : h.IsOptimal r c1 c2) : c1 = c2 := by
  have he := h.euler_of_optimal hu ho
  have he' : u' c1 = u' c2 := by rw [he]; linear_combination u' c2 * hβr
  obtain ⟨⟨hc1, hc2, -⟩, -⟩ := ho
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact absurd he' (deriv_lt_of_strictConcave h.concave (mem_Ioi.2 hc1) (mem_Ioi.2 hc2)
      hlt (hu c1 hc1) (hu c2 hc2)).ne'
  · exact absurd he' (deriv_lt_of_strictConcave h.concave (mem_Ioi.2 hc2) (mem_Ioi.2 hc1)
      hlt (hu c2 hc2) (hu c1 hc1)).ne

/-- The flat consumption level O&R (1.5): `C̄ = ((1 + r) Y₁ + Y₂)/(2 + r)`. -/
theorem flat_level (hu : ∀ c, 0 < c → HasDerivAt h.u (u' c) c) {r c1 c2 : ℝ}
    (hr : 0 < 1 + r) (hβr : h.β * (1 + r) = 1) (ho : h.IsOptimal r c1 c2) :
    c1 = ((1 + r) * h.Y1 + h.Y2) / (2 + r) ∧ c2 = ((1 + r) * h.Y1 + h.Y2) / (2 + r) := by
  have hflat := h.flat_of_beta_mul_eq_one hu hβr ho
  have hb := h.optimal_binds ho
  have h2r : (2 + r) ≠ 0 := by linarith
  have hc1 : c1 = ((1 + r) * h.Y1 + h.Y2) / (2 + r) := by
    field_simp
    linarith
  exact ⟨hc1, hflat ▸ hc1⟩

/-- **Consumption tilt** (O&R p. 4): if `β(1 + r) > 1`, consumption rises, `C₁ < C₂`. -/
theorem tilt_up (hu : ∀ c, 0 < c → HasDerivAt h.u (u' c) c) (hpos : ∀ c, 0 < c → 0 < u' c)
    {r c1 c2 : ℝ} (hβr : 1 < h.β * (1 + r)) (ho : h.IsOptimal r c1 c2) : c1 < c2 := by
  have he := h.euler_of_optimal hu ho
  obtain ⟨⟨hc1, hc2, -⟩, -⟩ := ho
  have hp := hpos c2 hc2
  have hgt : u' c2 < u' c1 := by rw [he]; nlinarith
  by_contra hle
  push Not at hle
  rcases hle.lt_or_eq with hlt | heq
  · exact absurd hgt (deriv_lt_of_strictConcave h.concave (mem_Ioi.2 hc2) (mem_Ioi.2 hc1)
      hlt (hu c2 hc2) (hu c1 hc1)).not_gt
  · exact absurd hgt (by rw [heq]; exact lt_irrefl _)

/-- **Consumption tilt** (O&R p. 4): if `β(1 + r) < 1`, consumption falls, `C₂ < C₁`. -/
theorem tilt_down (hu : ∀ c, 0 < c → HasDerivAt h.u (u' c) c) (hpos : ∀ c, 0 < c → 0 < u' c)
    {r c1 c2 : ℝ} (hβr : h.β * (1 + r) < 1) (ho : h.IsOptimal r c1 c2) : c2 < c1 := by
  have he := h.euler_of_optimal hu ho
  obtain ⟨⟨hc1, hc2, -⟩, -⟩ := ho
  have hp := hpos c2 hc2
  have hlt' : u' c1 < u' c2 := by rw [he]; nlinarith
  by_contra hle
  push Not at hle
  rcases hle.lt_or_eq with hlt | heq
  · exact absurd hlt' (deriv_lt_of_strictConcave h.concave (mem_Ioi.2 hc1) (mem_Ioi.2 hc2)
      hlt (hu c1 hc1) (hu c2 hc2)).not_gt
  · exact absurd hlt' (by rw [heq]; exact lt_irrefl _)

/-- **Existence under the Inada condition** (O&R footnote 1): if `u'` is continuous, positive
and `u'(c) → ∞` as `c → 0⁺`, the household has an optimum at every `r > −1`. -/
theorem exists_optimal (hu : ∀ c, 0 < c → HasDerivAt h.u (u' c) c)
    (hpos : ∀ c, 0 < c → 0 < u' c) (hcont : ContinuousOn u' (Ioi 0))
    (hinada : Tendsto u' (𝓝[>] 0) atTop) {r : ℝ} (hr : 0 < 1 + r) :
    ∃ c1 c2, h.IsOptimal r c1 c2 := by
  set k := (1 + r) * h.β with hk
  have hkpos : 0 < k := mul_pos hr h.β_pos
  -- the Euler residual along the budget line
  set φ : ℝ → ℝ := fun t => u' t - k * u' (h.Y2 + (1 + r) * (h.Y1 - t)) with hφ
  -- u' is strictly decreasing on (0, ∞)
  have anti : ∀ x y, 0 < x → x < y → u' y < u' x := fun x y hx hxy =>
    deriv_lt_of_strictConcave h.concave (mem_Ioi.2 hx) (mem_Ioi.2 (hx.trans hxy)) hxy
      (hu x hx) (hu y (hx.trans hxy))
  -- a small a ≤ Y₁ with φ a > 0
  have hev : ∀ᶠ t in 𝓝[>] (0 : ℝ), k * u' h.Y2 < u' t ∧ t < h.Y1 :=
    (hinada.eventually (eventually_gt_atTop _)).and
      (nhdsWithin_le_nhds (Iio_mem_nhds h.Y1_pos))
  have hev0 : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t := self_mem_nhdsWithin
  obtain ⟨a, ⟨ha, haY⟩, ha0⟩ := (hev.and hev0).exists
  have hc2a : h.Y2 < h.Y2 + (1 + r) * (h.Y1 - a) := by nlinarith
  have hφa : 0 < φ a := by
    have := anti _ _ h.Y2_pos hc2a
    simp only [hφ]
    nlinarith
  -- a small second-period level s < Y₂ with k u'(s) > u'(Y₁), and b with C₂(b) = s
  have hev' : ∀ᶠ t in 𝓝[>] (0 : ℝ), u' h.Y1 / k < u' t ∧ t < h.Y2 :=
    (hinada.eventually (eventually_gt_atTop _)).and
      (nhdsWithin_le_nhds (Iio_mem_nhds h.Y2_pos))
  obtain ⟨s, ⟨hs, hsY⟩, hs0⟩ := (hev'.and hev0).exists
  set b := h.Y1 + (h.Y2 - s) / (1 + r) with hbdef
  have hbY : h.Y1 < b := by
    have : 0 < (h.Y2 - s) / (1 + r) := div_pos (by linarith) hr
    linarith
  have hc2b : h.Y2 + (1 + r) * (h.Y1 - b) = s := by
    rw [hbdef]
    field_simp
    ring
  have hφb : φ b < 0 := by
    have h1 := anti _ _ h.Y1_pos hbY
    have h2 : u' h.Y1 < k * u' s := by rwa [div_lt_iff₀' hkpos] at hs
    simp only [hφ, hc2b]
    linarith
  have hab : a ≤ b := by linarith
  -- φ is continuous on [a, b]
  have hφcont : ContinuousOn φ (Icc a b) := by
    have hlin : Continuous fun t => h.Y2 + (1 + r) * (h.Y1 - t) := by fun_prop
    refine (hcont.mono fun t ht => ?_).sub (continuousOn_const.mul
      (hcont.comp hlin.continuousOn fun t ht => ?_))
    · exact mem_Ioi.2 (ha0.trans_le ht.1)
    · have : h.Y2 + (1 + r) * (h.Y1 - b) ≤ h.Y2 + (1 + r) * (h.Y1 - t) := by nlinarith [ht.2]
      exact mem_Ioi.2 (by linarith)
  obtain ⟨c, hc, hφc⟩ := intermediate_value_Icc' hab hφcont ⟨hφb.le, hφa.le⟩
  have hc0 : 0 < c := ha0.trans_le hc.1
  have hc2 : 0 < h.Y2 + (1 + r) * (h.Y1 - c) := by
    have : h.Y2 + (1 + r) * (h.Y1 - b) ≤ h.Y2 + (1 + r) * (h.Y1 - c) := by nlinarith [hc.2]
    linarith
  refine ⟨c, _, h.optimal_of_euler hu hpos hc0 hc2 rfl ?_⟩
  simp only [hφ] at hφc
  linarith

end Household

/-! ### Exercise 1: general utility `U(C₁, C₂)` (O&R p. 54) -/

/-- **Exercise 1(a)**: for a differentiable `U` with partial derivatives `U₁, U₂` at a positive
optimum on the budget line, `U₁ = (1 + r) U₂`. -/
theorem euler_general {U : ℝ × ℝ → ℝ} {U1 U2 r Y1 Y2 c1 : ℝ}
    (hU : HasFDerivAt U (U1 • ContinuousLinearMap.fst ℝ ℝ ℝ + U2 • ContinuousLinearMap.snd ℝ ℝ ℝ)
      (c1, Y2 + (1 + r) * (Y1 - c1)))
    (hc1 : 0 < c1) (hc2 : 0 < Y2 + (1 + r) * (Y1 - c1))
    (hmax : ∀ d1 d2, 0 < d1 → 0 < d2 → d2 ≤ Y2 + (1 + r) * (Y1 - d1) →
      U (d1, d2) ≤ U (c1, Y2 + (1 + r) * (Y1 - c1))) :
    U1 = (1 + r) * U2 := by
  have hγ : HasDerivAt (fun t => (t, Y2 + (1 + r) * (Y1 - t))) ((1 : ℝ), (1 + r) * (-1)) c1 :=
    (hasDerivAt_id c1).prodMk ((((hasDerivAt_id c1).const_sub Y1).const_mul (1 + r)).const_add Y2)
  have hd := hU.comp_hasDerivAt c1 hγ
  have hcont : Continuous fun s => Y2 + (1 + r) * (Y1 - s) := by fun_prop
  have hloc : IsLocalMax (fun t => U (t, Y2 + (1 + r) * (Y1 - t))) c1 := by
    filter_upwards [Ioi_mem_nhds hc1, (hcont.tendsto c1).eventually (lt_mem_nhds hc2)]
      with s hs1 hs2
    exact hmax s _ hs1 hs2 le_rfl
  have := hloc.hasDerivAt_eq_zero hd
  simp at this
  linarith

/-- **Exercise 1(b), envelope theorem**: if the value function `V` is differentiable at `r`, then
`V'(r) = U₂ (Y₁ − C₁)`. `V` is any function bounding utility on every budget set and attained
by the optimum at `r`; differentiability of `V` is a hypothesis. -/
theorem envelope_general {U : ℝ × ℝ → ℝ} {V : ℝ → ℝ} {U1 U2 V' r Y1 Y2 c1 : ℝ}
    (hU : HasFDerivAt U (U1 • ContinuousLinearMap.fst ℝ ℝ ℝ + U2 • ContinuousLinearMap.snd ℝ ℝ ℝ)
      (c1, Y2 + (1 + r) * (Y1 - c1)))
    (hc1 : 0 < c1) (hc2 : 0 < Y2 + (1 + r) * (Y1 - c1))
    (hV : ∀ s d1 d2, 0 < d1 → 0 < d2 → d2 ≤ Y2 + (1 + s) * (Y1 - d1) → U (d1, d2) ≤ V s)
    (hVr : V r = U (c1, Y2 + (1 + r) * (Y1 - c1))) (hV' : HasDerivAt V V' r) :
    V' = U2 * (Y1 - c1) := by
  have h2 : HasDerivAt (fun s : ℝ => Y2 + (1 + s) * (Y1 - c1)) (Y1 - c1) r := by
    have := (((hasDerivAt_id r).const_add 1).mul_const (Y1 - c1)).const_add Y2
    simpa using this
  have h1 : HasDerivAt (fun _ : ℝ => c1) 0 r := hasDerivAt_const r c1
  have hγ : HasDerivAt (fun s => (c1, Y2 + (1 + s) * (Y1 - c1))) ((0 : ℝ), Y1 - c1) r :=
    h1.prodMk h2
  have hd := hU.comp_hasDerivAt r hγ
  have hcont : Continuous fun s => Y2 + (1 + s) * (Y1 - c1) := by fun_prop
  have hloc : IsLocalMin (fun s => V s - U (c1, Y2 + (1 + s) * (Y1 - c1))) r := by
    filter_upwards [(hcont.tendsto r).eventually (lt_mem_nhds hc2)] with s hs
    simp only [hVr, sub_self]
    exact sub_nonneg.2 (hV s c1 _ hc1 hs le_rfl)
  have := hloc.hasDerivAt_eq_zero (hV'.sub hd)
  simp at this
  linarith

/-- **Exercise 1(d)**: a change `dr` in the world rate is welfare-equivalent to a change in
date-1 wealth of `r̂ (Y₁ − C₁)`, where `r̂ = dr/(1 + r)`, valued at the marginal utility `U₁`. -/
theorem welfare_equivalent_wealth {U1 U2 r Y1 c1 dr : ℝ} (hr : 0 < 1 + r)
    (he : U1 = (1 + r) * U2) :
    U2 * (Y1 - c1) * dr = U1 * ((Y1 - c1) * (dr / (1 + r))) := by
  rw [he]
  field_simp

end ObstfeldRogoff.IntertemporalTrade.Consumer
