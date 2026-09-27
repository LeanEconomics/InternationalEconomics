import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.Prod
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Calculus.Deriv.Add
set_option autoImplicit false

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

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

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

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

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Autarky rates and the gains from intertemporal trade

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*,
§1.1.4–1.1.5, pp. 8–11. The book argues these results from Figure 1.1. Here the
first group is proved by revealed preference, using only strict monotonicity
and strict concavity of `u`:
* gains from trade (p. 8, p. 10): `utility_endowment_le`, `utility_endowment_lt`;
* the saving-sign lemma behind the pattern of trade (pp. 9–10): a country lends
  when the world rate exceeds its autarky rate, `saving_nonneg_of_autarky_lt`;
* welfare rises with the distance between the world and autarky rates (p. 10):
  `utility_mono_of_autarky_le`, `utility_anti_of_le_autarky`.

With a derivative `u' > 0`, the autarky rate is characterised by O&R (1.7) and is
unique, the saving and welfare results become strict, and the autarky rate
has the comparative statics of p. 10.
-/

namespace ObstfeldRogoff.IntertemporalTrade.Consumer

open Set

namespace Household

variable (h : Household)

/-- `rA` is an autarky rate: at `rA` the household chooses to consume its endowment
(O&R p. 9). -/
def IsAutarkyRate (rA : ℝ) : Prop := h.IsOptimal rA h.Y1 h.Y2

/-- **Gains from trade** (O&R Figure 1.1, p. 8): the optimum is at least as good as autarky. -/
theorem utility_endowment_le {r c1 c2 : ℝ} (ho : h.IsOptimal r c1 c2) :
    h.utility h.Y1 h.Y2 ≤ h.utility c1 c2 :=
  ho.2 _ _ (h.endowment_feasible r)

/-- **Strict gains from trade** (O&R p. 10): if the household trades at all, it is strictly
better off than in autarky. -/
theorem utility_endowment_lt {r c1 c2 : ℝ} (ho : h.IsOptimal r c1 c2) (hne : c1 ≠ h.Y1) :
    h.utility h.Y1 h.Y2 < h.utility c1 c2 := by
  refine lt_of_le_of_ne (h.utility_endowment_le ho) fun heq => hne ?_
  have hY : h.IsOptimal r h.Y1 h.Y2 :=
    ⟨h.endowment_feasible r, fun d1 d2 hd => heq ▸ ho.2 d1 d2 hd⟩
  exact (h.optimal_unique ho hY).1

/-- A plan feasible at `r` that attains the maximal utility at `r` is optimal at `r`. -/
theorem isOptimal_of_utility_eq {r c1 c2 d1 d2 : ℝ} (hd : h.IsOptimal r d1 d2)
    (hc : h.Feasible r c1 c2) (heq : h.utility d1 d2 ≤ h.utility c1 c2) :
    h.IsOptimal r c1 c2 :=
  ⟨hc, fun e1 e2 he => (hd.2 e1 e2 he).trans heq⟩

/-- **Saving-sign lemma** (O&R pp. 9–10): at a world rate above the autarky rate the
household does not borrow, `C₁ ≤ Y₁`. Revealed preference; no derivatives. -/
theorem saving_nonneg_of_autarky_lt {rA r c1 c2 : ℝ} (hA : h.IsAutarkyRate rA)
    (hlt : rA < r) (ho : h.IsOptimal r c1 c2) : c1 ≤ h.Y1 := by
  by_contra hgt
  push Not at hgt
  have hb := h.optimal_binds ho
  have hslack : c2 < h.Y2 + (1 + rA) * (h.Y1 - c1) := by rw [hb]; nlinarith
  have hfA : h.Feasible rA c1 c2 := ⟨ho.1.1, ho.1.2.1, hslack.le⟩
  have hoA : h.IsOptimal rA c1 c2 :=
    h.isOptimal_of_utility_eq hA hfA (h.utility_endowment_le ho)
  exact absurd (h.optimal_binds hoA) hslack.ne

/-- **Saving-sign lemma**, borrowing side: at a world rate below the autarky rate the
household does not lend, `Y₁ ≤ C₁`. -/
theorem saving_nonpos_of_lt_autarky {rA r c1 c2 : ℝ} (hA : h.IsAutarkyRate rA)
    (hlt : r < rA) (ho : h.IsOptimal r c1 c2) : h.Y1 ≤ c1 := by
  by_contra hgt
  push Not at hgt
  have hb := h.optimal_binds ho
  have hslack : c2 < h.Y2 + (1 + rA) * (h.Y1 - c1) := by rw [hb]; nlinarith
  have hfA : h.Feasible rA c1 c2 := ⟨ho.1.1, ho.1.2.1, hslack.le⟩
  have hoA : h.IsOptimal rA c1 c2 :=
    h.isOptimal_of_utility_eq hA hfA (h.utility_endowment_le ho)
  exact absurd (h.optimal_binds hoA) hslack.ne

/-- At the autarky rate itself the household consumes its endowment. -/
theorem optimal_at_autarky {rA c1 c2 : ℝ} (hA : h.IsAutarkyRate rA)
    (ho : h.IsOptimal rA c1 c2) : c1 = h.Y1 ∧ c2 = h.Y2 :=
  h.optimal_unique ho hA

/-- **Welfare and the world rate, lenders** (O&R p. 10): above the autarky rate, utility is
nondecreasing in `r`. -/
theorem utility_mono_of_autarky_le {rA r r' c1 c2 d1 d2 : ℝ} (hA : h.IsAutarkyRate rA)
    (hr : rA ≤ r) (hrr : r ≤ r') (hc : h.IsOptimal r c1 c2) (hd : h.IsOptimal r' d1 d2) :
    h.utility c1 c2 ≤ h.utility d1 d2 := by
  have hs : c1 ≤ h.Y1 := by
    rcases hr.lt_or_eq with hlt | rfl
    · exact h.saving_nonneg_of_autarky_lt hA hlt hc
    · exact (h.optimal_at_autarky hA hc).1.le
  have hb := h.optimal_binds hc
  exact hd.2 c1 c2 ⟨hc.1.1, hc.1.2.1, by rw [hb]; nlinarith⟩

/-- **Welfare and the world rate, borrowers** (O&R p. 10): below the autarky rate, utility is
nonincreasing in `r`. -/
theorem utility_anti_of_le_autarky {rA r r' c1 c2 d1 d2 : ℝ} (hA : h.IsAutarkyRate rA)
    (hr : r' ≤ rA) (hrr : r ≤ r') (hc : h.IsOptimal r c1 c2) (hd : h.IsOptimal r' d1 d2) :
    h.utility d1 d2 ≤ h.utility c1 c2 := by
  have hs : h.Y1 ≤ d1 := by
    rcases hr.lt_or_eq with hlt | rfl
    · exact h.saving_nonpos_of_lt_autarky hA hlt hd
    · exact (h.optimal_at_autarky hA hd).1.ge
  have hb := h.optimal_binds hd
  exact hc.2 d1 d2 ⟨hd.1.1, hd.1.2.1, by rw [hb]; nlinarith⟩

/-- Strict welfare gain for a lender: if the household strictly lends at `r` (`C₁ < Y₁`), a
higher world rate makes it strictly better off. -/
theorem utility_lt_of_lends {r r' c1 c2 d1 d2 : ℝ} (hrr : r < r') (hc : h.IsOptimal r c1 c2)
    (hs : c1 < h.Y1) (hd : h.IsOptimal r' d1 d2) : h.utility c1 c2 < h.utility d1 d2 := by
  have hb := h.optimal_binds hc
  have hslack : c2 < h.Y2 + (1 + r') * (h.Y1 - c1) := by rw [hb]; nlinarith
  have hf : h.Feasible r' c1 c2 := ⟨hc.1.1, hc.1.2.1, hslack.le⟩
  refine lt_of_le_of_ne (hd.2 c1 c2 hf) fun heq => ?_
  have ho := h.isOptimal_of_utility_eq hd hf heq.ge
  exact absurd (h.optimal_binds ho) hslack.ne

/-- Strict welfare loss for a borrower: if the household strictly borrows at `r'`
(`Y₁ < C₁`), a lower world rate makes it strictly better off. -/
theorem utility_lt_of_borrows {r r' c1 c2 d1 d2 : ℝ} (hrr : r < r') (hc : h.IsOptimal r c1 c2)
    (hd : h.IsOptimal r' d1 d2) (hs : h.Y1 < d1) : h.utility d1 d2 < h.utility c1 c2 := by
  have hb := h.optimal_binds hd
  have hslack : d2 < h.Y2 + (1 + r) * (h.Y1 - d1) := by rw [hb]; nlinarith
  have hf : h.Feasible r d1 d2 := ⟨hd.1.1, hd.1.2.1, hslack.le⟩
  refine lt_of_le_of_ne (hc.2 d1 d2 hf) fun heq => ?_
  have ho := h.isOptimal_of_utility_eq hc hf heq.ge
  exact absurd (h.optimal_binds ho) hslack.ne

/-! ### Differentiable utility -/

variable {u' : ℝ → ℝ}

/-- **The autarky interest rate** O&R (1.7), p. 9: `rA` is an autarky rate iff
`β u'(Y₂)/u'(Y₁) = 1/(1 + rA)`. -/
theorem isAutarkyRate_iff (hu : ∀ c, 0 < c → HasDerivAt h.u (u' c) c)
    (hpos : ∀ c, 0 < c → 0 < u' c) {rA : ℝ} (hr : 0 < 1 + rA) :
    h.IsAutarkyRate rA ↔ h.β * u' h.Y2 / u' h.Y1 = 1 / (1 + rA) := by
  have h1 := hpos _ h.Y1_pos
  have h2 := hpos _ h.Y2_pos
  unfold IsAutarkyRate
  rw [h.isOptimal_iff_euler hu hpos, div_eq_div_iff h1.ne' hr.ne']
  constructor
  · rintro ⟨-, -, -, he⟩
    linarith
  · intro he
    exact ⟨h.Y1_pos, h.Y2_pos, by ring, by linarith⟩

/-- The autarky rate is unique. -/
theorem autarkyRate_unique (hu : ∀ c, 0 < c → HasDerivAt h.u (u' c) c)
    (hpos : ∀ c, 0 < c → 0 < u' c) {rA rB : ℝ} (hA : h.IsAutarkyRate rA)
    (hB : h.IsAutarkyRate rB) : rA = rB := by
  have eA := h.euler_of_optimal hu hA
  have eB := h.euler_of_optimal hu hB
  have := mul_pos h.β_pos (hpos _ h.Y2_pos)
  nlinarith

/-- **Strict saving sign** (O&R pp. 9–10): with differentiable utility, a world rate strictly
above the autarky rate makes the household a strict lender, `C₁ < Y₁`. -/
theorem saving_pos_of_autarky_lt (hu : ∀ c, 0 < c → HasDerivAt h.u (u' c) c)
    (hpos : ∀ c, 0 < c → 0 < u' c) {rA r c1 c2 : ℝ} (hA : h.IsAutarkyRate rA)
    (hlt : rA < r) (ho : h.IsOptimal r c1 c2) : c1 < h.Y1 := by
  refine lt_of_le_of_ne (h.saving_nonneg_of_autarky_lt hA hlt ho) fun heq => ?_
  have hb := h.optimal_binds ho
  rw [heq, sub_self, mul_zero, add_zero] at hb
  rw [heq, hb] at ho
  exact hlt.ne (h.autarkyRate_unique hu hpos hA ho)

/-- **Strict saving sign**, borrowing side: below the autarky rate, `Y₁ < C₁`. -/
theorem saving_neg_of_lt_autarky (hu : ∀ c, 0 < c → HasDerivAt h.u (u' c) c)
    (hpos : ∀ c, 0 < c → 0 < u' c) {rA r c1 c2 : ℝ} (hA : h.IsAutarkyRate rA)
    (hlt : r < rA) (ho : h.IsOptimal r c1 c2) : h.Y1 < c1 := by
  refine lt_of_le_of_ne (h.saving_nonpos_of_lt_autarky hA hlt ho) fun heq => ?_
  have hb := h.optimal_binds ho
  rw [← heq, sub_self, mul_zero, add_zero] at hb
  rw [← heq, hb] at ho
  exact hlt.ne (h.autarkyRate_unique hu hpos ho hA)

/-- **Welfare strictly increasing above the autarky rate** (O&R p. 10: "the greater the
difference, the greater the gain"). -/
theorem utility_strictMono_of_autarky_le (hu : ∀ c, 0 < c → HasDerivAt h.u (u' c) c)
    (hpos : ∀ c, 0 < c → 0 < u' c) {rA r r' c1 c2 d1 d2 : ℝ} (hA : h.IsAutarkyRate rA)
    (hr : rA ≤ r) (hrr : r < r') (hc : h.IsOptimal r c1 c2) (hd : h.IsOptimal r' d1 d2) :
    h.utility c1 c2 < h.utility d1 d2 := by
  rcases hr.lt_or_eq with hlt | rfl
  · exact h.utility_lt_of_lends hrr hc (h.saving_pos_of_autarky_lt hu hpos hA hlt hc) hd
  · obtain ⟨e1, e2⟩ := h.optimal_at_autarky hA hc
    rw [e1, e2]
    exact h.utility_endowment_lt hd (h.saving_pos_of_autarky_lt hu hpos hA hrr hd).ne

/-- **Welfare strictly decreasing below the autarky rate** (O&R p. 10). -/
theorem utility_strictAnti_of_le_autarky (hu : ∀ c, 0 < c → HasDerivAt h.u (u' c) c)
    (hpos : ∀ c, 0 < c → 0 < u' c) {rA r r' c1 c2 d1 d2 : ℝ} (hA : h.IsAutarkyRate rA)
    (hr : r' ≤ rA) (hrr : r < r') (hc : h.IsOptimal r c1 c2) (hd : h.IsOptimal r' d1 d2) :
    h.utility d1 d2 < h.utility c1 c2 := by
  rcases hr.lt_or_eq with hlt | rfl
  · exact h.utility_lt_of_borrows hrr hc hd (h.saving_neg_of_lt_autarky hu hpos hA hlt hd)
  · obtain ⟨e1, e2⟩ := h.optimal_at_autarky hA hd
    rw [e1, e2]
    exact h.utility_endowment_lt hc (h.saving_neg_of_lt_autarky hu hpos hA hrr hc).ne'

end Household

/-! ### Comparative statics of the autarky rate (O&R p. 10) -/

/-- The autarky gross rate `1 + rA = u'(Y₁)/(β u'(Y₂))`, from O&R (1.7). -/
noncomputable def autarkyGross (u' : ℝ → ℝ) (β Y1 Y2 : ℝ) : ℝ := u' Y1 / (β * u' Y2)

/-- The autarky rate falls when first-period output rises. -/
theorem autarkyGross_anti_Y1 {u' : ℝ → ℝ} (hanti : StrictAntiOn u' (Ioi 0))
    (hpos : ∀ c, 0 < c → 0 < u' c) {β Y1 Y1' Y2 : ℝ} (hβ : 0 < β) (hY1 : 0 < Y1)
    (hY2 : 0 < Y2) (hlt : Y1 < Y1') :
    autarkyGross u' β Y1' Y2 < autarkyGross u' β Y1 Y2 :=
  div_lt_div_of_pos_right (hanti (mem_Ioi.2 hY1) (mem_Ioi.2 (hY1.trans hlt)) hlt)
    (mul_pos hβ (hpos _ hY2))

/-- The autarky rate rises when second-period output rises. -/
theorem autarkyGross_mono_Y2 {u' : ℝ → ℝ} (hanti : StrictAntiOn u' (Ioi 0))
    (hpos : ∀ c, 0 < c → 0 < u' c) {β Y1 Y2 Y2' : ℝ} (hβ : 0 < β) (hY1 : 0 < Y1)
    (hY2 : 0 < Y2) (hlt : Y2 < Y2') :
    autarkyGross u' β Y1 Y2 < autarkyGross u' β Y1 Y2' := by
  unfold autarkyGross
  have h1 := hpos _ hY1
  have h2 := hpos _ (hY2.trans hlt)
  exact div_lt_div_of_pos_left h1 (mul_pos hβ h2)
    (mul_lt_mul_of_pos_left (hanti (mem_Ioi.2 hY2) (mem_Ioi.2 (hY2.trans hlt)) hlt) hβ)

/-- The autarky rate falls when the household becomes more patient (higher `β`). -/
theorem autarkyGross_anti_beta {u' : ℝ → ℝ} (hpos : ∀ c, 0 < c → 0 < u' c)
    {β β' Y1 Y2 : ℝ} (hβ : 0 < β) (hY1 : 0 < Y1) (hY2 : 0 < Y2) (hlt : β < β') :
    autarkyGross u' β' Y1 Y2 < autarkyGross u' β Y1 Y2 := by
  unfold autarkyGross
  have h2 := hpos _ hY2
  exact div_lt_div_of_pos_left (hpos _ hY1) (mul_pos hβ h2)
    (mul_lt_mul_of_pos_right hlt h2)

end ObstfeldRogoff.IntertemporalTrade.Consumer

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

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

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

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

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Isoelastic utility and the interest-rate response of consumption

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*,
§1.3.2 (pp. 28–31) and Chapter 1 exercises 3, 4 and 7 (pp. 55–57).
-/

namespace ObstfeldRogoff.IntertemporalTrade.Isoelastic

open Real Filter Topology Set

/-- The elasticity of intertemporal substitution, O&R (1.21), p. 28:
`σ(C) = −u'(C) / (C u''(C))`. -/
noncomputable def eis (u : ℝ → ℝ) (C : ℝ) : ℝ :=
  -deriv u C / (C * deriv (deriv u) C)

/-- The isoelastic period utility, O&R (1.22), p. 28: `C^{1−1/σ}/(1−1/σ)`,
replaced by its limit `log C` when `σ = 1`. -/
noncomputable def isoU (σ : ℝ) (C : ℝ) : ℝ :=
  if σ = 1 then Real.log C else C ^ (1 - 1 / σ) / (1 - 1 / σ)

/-- Marginal utility of the isoelastic class, O&R p. 30: `u'(C) = C^{−1/σ}` for `C > 0`
(including the log case `σ = 1`). -/
theorem hasDerivAt_isoU (σ : ℝ) {C : ℝ} (hC : 0 < C) :
    HasDerivAt (isoU σ) (C ^ (-1 / σ)) C := by
  by_cases hσ : σ = 1
  · subst hσ
    have h : C ^ (-1 / (1 : ℝ)) = C⁻¹ := by
      rw [div_one, Real.rpow_neg_one]
    rw [h]
    have hf : isoU 1 = Real.log := by
      funext x
      simp [isoU]
    rw [hf]
    exact Real.hasDerivAt_log hC.ne'
  · have hk : (1 : ℝ) - 1 / σ ≠ 0 := by
      intro h
      apply hσ
      have hs : σ ≠ 0 := by
        rintro rfl
        simp at h
      field_simp at h
      linarith
    have hf : isoU σ = fun x => x ^ (1 - 1 / σ) / (1 - 1 / σ) := by
      funext x
      simp [isoU, hσ]
    rw [hf]
    have hd := (Real.hasDerivAt_rpow_const (p := 1 - 1 / σ) (Or.inl hC.ne')).div_const
      (1 - 1 / σ)
    convert hd using 1
    rw [mul_div_cancel_left₀ _ hk]
    congr 1
    ring

/-- On `(0, ∞)` the derivative of the isoelastic utility is `C ↦ C^{−1/σ}`. -/
theorem deriv_isoU_eventuallyEq (σ : ℝ) {C : ℝ} (hC : 0 < C) :
    deriv (isoU σ) =ᶠ[𝓝 C] fun x => x ^ (-1 / σ) := by
  filter_upwards [Ioi_mem_nhds hC] with x hx
  exact (hasDerivAt_isoU σ hx).deriv

/-- Curvature of the isoelastic class: `u''(C) = −(1/σ) C^{−1/σ−1}` for `C > 0`. -/
theorem deriv_deriv_isoU (σ : ℝ) {C : ℝ} (hC : 0 < C) :
    deriv (deriv (isoU σ)) C = -1 / σ * C ^ (-1 / σ - 1) := by
  rw [(deriv_isoU_eventuallyEq σ hC).deriv_eq]
  exact (Real.hasDerivAt_rpow_const (p := -1 / σ) (Or.inl hC.ne')).deriv

/-- The isoelastic class has constant elasticity of intertemporal substitution `σ`,
O&R (1.21)–(1.22), p. 28. -/
theorem eis_isoU {σ : ℝ} (hσ : 0 < σ) {C : ℝ} (hC : 0 < C) : eis (isoU σ) C = σ := by
  unfold eis
  rw [deriv_deriv_isoU σ hC, (hasDerivAt_isoU σ hC).deriv,
    Real.rpow_sub_one hC.ne']
  have hp : 0 < C ^ (-1 / σ) := Real.rpow_pos_of_pos hC _
  field_simp

/-- O&R footnote 14, p. 28: the normalised isoelastic utility `(C^{1−1/σ} − 1)/(1 − 1/σ)`
converges to `log C` as `σ → 1`. -/
theorem tendsto_normalised_isoU_log {C : ℝ} (hC : 0 < C) :
    Tendsto (fun σ : ℝ => (C ^ (1 - 1 / σ) - 1) / (1 - 1 / σ)) (𝓝[≠] 1)
      (𝓝 (Real.log C)) := by
  -- the slope of `t ↦ C^t` at `t = 0` tends to its derivative `log C`
  have hd : HasDerivAt (fun t : ℝ => C ^ t) (C ^ (0 : ℝ) * Real.log C) 0 :=
    (Real.hasStrictDerivAt_const_rpow hC 0).hasDerivAt
  rw [Real.rpow_zero, one_mul] at hd
  have hs := hd.tendsto_slope_zero
  simp only [zero_add, Real.rpow_zero, smul_eq_mul] at hs
  -- `σ ↦ 1 − 1/σ` maps a punctured neighbourhood of `1` into one of `0`
  have hcont : Tendsto (fun σ : ℝ => 1 - 1 / σ) (𝓝[≠] 1) (𝓝 0) := by
    have : Tendsto (fun σ : ℝ => 1 - 1 / σ) (𝓝 1) (𝓝 (1 - 1 / 1)) :=
      (continuousAt_const.sub (continuousAt_const.div continuousAt_id one_ne_zero))
    rw [div_one, sub_self] at this
    exact this.mono_left nhdsWithin_le_nhds
  have hne : ∀ᶠ σ : ℝ in 𝓝[≠] 1, 1 - 1 / σ ∈ ({0}ᶜ : Set ℝ) := by
    filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Ioi_mem_nhds one_pos)]
      with σ hσ hpos
    simp only [mem_compl_iff, mem_singleton_iff] at hσ ⊢
    intro h
    apply hσ
    have : (σ : ℝ) ≠ 0 := (show (0 : ℝ) < σ from hpos).ne'
    field_simp at h
    linarith
  have hmap := hs.comp (tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hcont hne)
  refine hmap.congr' ?_
  filter_upwards with σ
  simp only [Function.comp_apply]
  ring

/-- Converse of (1.22), O&R p. 28: if `u` is twice differentiable on `(0, ∞)` with constant
elasticity of intertemporal substitution `σ > 0`, then `u` is an affine transformation
`a · isoU σ + b` of the isoelastic utility. -/
theorem eq_affine_isoU_of_eis_const {σ : ℝ} (hσ : 0 < σ) {u : ℝ → ℝ}
    (hu : DifferentiableOn ℝ u (Ioi 0)) (hu' : DifferentiableOn ℝ (deriv u) (Ioi 0))
    (heis : ∀ C, 0 < C → eis u C = σ) :
    ∃ a b : ℝ, ∀ C, 0 < C → u C = a * isoU σ C + b := by
  -- Step 1: `C u''(C) = −u'(C)/σ` on `(0, ∞)`
  have hode : ∀ C, 0 < C → C * deriv (deriv u) C = -deriv u C / σ := by
    intro C hC
    have h := heis C hC
    unfold eis at h
    have hden : C * deriv (deriv u) C ≠ 0 := by
      intro h0
      rw [h0, div_zero] at h
      exact hσ.ne h
    rw [div_eq_iff hden] at h
    rw [eq_div_iff hσ.ne']
    linarith
  -- Step 2: `h(C) = u'(C) C^{1/σ}` has zero derivative, hence is constant
  have hconst : ∃ a, ∀ C ∈ Ioi (0 : ℝ), deriv u C * C ^ (1 / σ) = a := by
    apply isOpen_Ioi.exists_is_const_of_deriv_eq_zero (convex_Ioi 0).isPreconnected
    · intro x hx
      exact ((hu' x hx).mul ((Real.hasDerivAt_rpow_const (p := 1 / σ)
        (Or.inl (ne_of_gt hx))).differentiableAt.differentiableWithinAt))
    · intro x hx
      have hx0 : (0 : ℝ) < x := hx
      have hd1 : HasDerivAt (deriv u) (deriv (deriv u) x) x :=
        ((hu' x hx).differentiableAt (isOpen_Ioi.mem_nhds hx)).hasDerivAt
      have hd2 := Real.hasDerivAt_rpow_const (p := 1 / σ) (Or.inl hx0.ne')
      have hd3 : HasDerivAt (fun y => deriv u y * y ^ (1 / σ))
          (deriv (deriv u) x * x ^ (1 / σ) + deriv u x * (1 / σ * x ^ (1 / σ - 1))) x :=
        hd1.mul hd2
      rw [hd3.deriv]
      have hx1 : x ^ (1 / σ - 1) = x ^ (1 / σ) / x := Real.rpow_sub_one hx0.ne' _
      rw [hx1, Pi.zero_apply]
      have hode' := hode x hx0
      have hxne : x ≠ 0 := hx0.ne'
      field_simp
      field_simp at hode'
      linear_combination x ^ (1 / σ) * hode'
  obtain ⟨a, ha⟩ := hconst
  -- Step 3: so `u' = a · (isoU σ)'`, hence `u − a · isoU σ` is constant
  have hderiv : EqOn (deriv u) (deriv (fun C => a * isoU σ C)) (Ioi 0) := by
    intro x hx
    have hx0 : (0 : ℝ) < x := hx
    rw [((hasDerivAt_isoU σ hx0).const_mul a).deriv, ← ha x hx]
    rw [mul_assoc, ← Real.rpow_add hx0]
    have : 1 / σ + -1 / σ = 0 := by ring
    rw [this, Real.rpow_zero, mul_one]
  have hdiff : DifferentiableOn ℝ (fun C => a * isoU σ C) (Ioi 0) := fun x hx =>
    ((hasDerivAt_isoU σ hx).const_mul a).differentiableAt.differentiableWithinAt
  obtain ⟨b, hb⟩ := isOpen_Ioi.exists_eq_add_of_deriv_eq (convex_Ioi 0).isPreconnected
    hu hdiff hderiv
  exact ⟨a, b, fun C hC => hb hC⟩

/-! ## Closed-form consumption with isoelastic utility (O&R §1.3.2.3, p. 30) -/

/-- Euler equation (1.3) for isoelastic utility, `C₁^{−1/σ} = (1+r)β C₂^{−1/σ}`, is equivalent
to the consumption growth rule O&R (1.25), p. 30: `C₂ = (1+r)^σ β^σ C₁` (positive consumption). -/
theorem euler_iff_growth {σ β r C1 C2 : ℝ} (hσ : 0 < σ) (hβ : 0 < β) (hr : 0 < 1 + r)
    (hC1 : 0 < C1) (hC2 : 0 < C2) :
    C1 ^ (-1 / σ) = (1 + r) * β * C2 ^ (-1 / σ) ↔ C2 = (1 + r) ^ σ * β ^ σ * C1 := by
  -- the growth rule implies the Euler equation
  have key : ∀ D, D = (1 + r) ^ σ * β ^ σ * C1 → C1 ^ (-1 / σ) = (1 + r) * β * D ^ (-1 / σ) := by
    intro D hD
    have hP : (0 : ℝ) ≤ (1 + r) ^ σ := (Real.rpow_pos_of_pos hr σ).le
    have hB : (0 : ℝ) ≤ β ^ σ := (Real.rpow_pos_of_pos hβ σ).le
    rw [hD, Real.mul_rpow (mul_nonneg hP hB) hC1.le, Real.mul_rpow hP hB,
      ← Real.rpow_mul hr.le, ← Real.rpow_mul hβ.le]
    have he : σ * (-1 / σ) = -1 := by field_simp
    rw [he, Real.rpow_neg_one, Real.rpow_neg_one]
    field_simp
  constructor
  · intro h
    have h2 := key _ rfl
    have hk : (0 : ℝ) < (1 + r) * β := by positivity
    have heq : C2 ^ (-1 / σ) = ((1 + r) ^ σ * β ^ σ * C1) ^ (-1 / σ) := by
      have := h.symm.trans h2
      exact mul_left_cancel₀ hk.ne' this
    have hne : (-1 / σ : ℝ) ≠ 0 := by
      have : (0 : ℝ) < 1 / σ := by positivity
      intro h0
      linarith [show -1 / σ = -(1 / σ) by ring]
    exact Real.rpow_left_injOn hne (show (0 : ℝ) ≤ C2 from hC2.le)
      (show (0 : ℝ) ≤ (1 + r) ^ σ * β ^ σ * C1 by positivity) heq
  · exact key C2

/-- Isoelastic date-1 consumption function O&R (1.26), p. 30, as a function of `r`:
`C₁(r) = (Y₁ + Y₂/(1+r)) / (1 + (1+r)^{σ−1} β^σ)`. -/
noncomputable def consC1 (σ β Y1 Y2 r : ℝ) : ℝ :=
  (Y1 + Y2 / (1 + r)) / (1 + (1 + r) ^ (σ - 1) * β ^ σ)

/-- Isoelastic date-2 consumption, O&R (1.25), p. 30: `C₂(r) = (1+r)^σ β^σ C₁(r)`. -/
noncomputable def consC2 (σ β Y1 Y2 r : ℝ) : ℝ :=
  (1 + r) ^ σ * β ^ σ * consC1 σ β Y1 Y2 r

/-- O&R (1.25)–(1.26), p. 30: for positive consumption, the Euler equation plus the budget
constraint (1.2) hold exactly when `C₁` is given by (1.26) and `C₂` by (1.25). -/
theorem euler_budget_iff_closed_form {σ β r Y1 Y2 C1 C2 : ℝ} (hσ : 0 < σ) (hβ : 0 < β)
    (hr : 0 < 1 + r) (hC1 : 0 < C1) (hC2 : 0 < C2) :
    (C1 ^ (-1 / σ) = (1 + r) * β * C2 ^ (-1 / σ) ∧ C1 + C2 / (1 + r) = Y1 + Y2 / (1 + r)) ↔
      (C1 = consC1 σ β Y1 Y2 r ∧ C2 = consC2 σ β Y1 Y2 r) := by
  rw [euler_iff_growth hσ hβ hr hC1 hC2]
  have hg : (1 + r) ^ (σ - 1) = (1 + r) ^ σ / (1 + r) := Real.rpow_sub_one hr.ne' σ
  have hP : 0 < (1 + r) ^ σ := Real.rpow_pos_of_pos hr σ
  have hB : 0 < β ^ σ := Real.rpow_pos_of_pos hβ σ
  have hden : 0 < 1 + (1 + r) ^ σ / (1 + r) * β ^ σ := by positivity
  unfold consC2 consC1
  rw [hg]
  constructor
  · rintro ⟨hgr, hb⟩
    have h1 : C1 = (Y1 + Y2 / (1 + r)) / (1 + (1 + r) ^ σ / (1 + r) * β ^ σ) := by
      rw [eq_div_iff hden.ne', ← hb, hgr]
      field_simp
    exact ⟨h1, by rw [← h1]; exact hgr⟩
  · rintro ⟨h1, h2⟩
    rw [← h1] at h2
    refine ⟨h2, ?_⟩
    rw [h2, h1]
    field_simp

/-- O&R (1.20)–(1.21), p. 28: with constant EIS the log consumption ratio is
`log(C₂/C₁) = σ log(1+r) + σ log β`, so `d log(C₂/C₁) = σ d log(1+r)`. -/
theorem log_growth_isoelastic {σ β r C1 C2 : ℝ} (hβ : 0 < β) (hr : 0 < 1 + r)
    (hC1 : 0 < C1) (hgr : C2 = (1 + r) ^ σ * β ^ σ * C1) :
    Real.log (C2 / C1) = σ * Real.log (1 + r) + σ * Real.log β := by
  rw [hgr, mul_div_assoc, div_self hC1.ne', mul_one,
    Real.log_mul (Real.rpow_pos_of_pos hr σ).ne' (Real.rpow_pos_of_pos hβ σ).ne',
    Real.log_rpow hr, Real.log_rpow hβ]

/-- Log case of (1.26), O&R p. 30 and exercise 2(a), p. 55: with `u = log`, the Euler equation
`1/C₁ = (1+r)β/C₂` plus the budget give `C₁ = (Y₁ + Y₂/(1+r))/(1+β)` and `C₂ = (1+r)βC₁`. -/
theorem log_euler_budget_iff {β r Y1 Y2 C1 C2 : ℝ} (hβ : 0 < β) (hr : 0 < 1 + r)
    (hC1 : 0 < C1) (hC2 : 0 < C2) :
    (1 / C1 = (1 + r) * β / C2 ∧ C1 + C2 / (1 + r) = Y1 + Y2 / (1 + r)) ↔
      (C1 = (Y1 + Y2 / (1 + r)) / (1 + β) ∧ C2 = (1 + r) * β * C1) := by
  have hgr : 1 / C1 = (1 + r) * β / C2 ↔ C2 = (1 + r) * β * C1 := by
    rw [div_eq_div_iff hC1.ne' hC2.ne']
    constructor <;> intro h <;> linarith
  rw [hgr]
  constructor
  · rintro ⟨h2, hb⟩
    refine ⟨?_, h2⟩
    rw [eq_div_iff (by positivity : (1 : ℝ) + β ≠ 0), ← hb, h2]
    field_simp
  · rintro ⟨h1, h2⟩
    refine ⟨h2, ?_⟩
    rw [h2, h1]
    field_simp

/-- O&R p. 30: in the log case the consumption function (1.26) is `(Y₁ + Y₂/(1+r))/(1+β)`,
so the date-1 spending share of lifetime income is `1/(1+β)` whatever `r`. -/
theorem consC1_log (β Y1 Y2 r : ℝ) :
    consC1 1 β Y1 Y2 r = (Y1 + Y2 / (1 + r)) / (1 + β) := by
  simp [consC1]

/-- O&R exercise 2(a), p. 55: with log utility, the date-2 spending share of lifetime income
is `β/(1+β)`: `(C₂/(1+r)) = β/(1+β) · (Y₁ + Y₂/(1+r))`. -/
theorem consC2_log_share {β : ℝ} (Y1 Y2 : ℝ) {r : ℝ} (hr : 0 < 1 + r) :
    consC2 1 β Y1 Y2 r / (1 + r) = β / (1 + β) * (Y1 + Y2 / (1 + r)) := by
  simp only [consC2, consC1_log, Real.rpow_one]
  field_simp

/-! ## The interest-rate response of date-1 consumption (O&R §1.3.2.2, p. 29) -/

/-- O&R (1.24), p. 29: the derivative of the isoelastic consumption function (1.26) is
`dC₁/dr = [(Y₁ − C₁) − σC₂/(1+r)] / [1 + r + C₂/C₁]`
(stated for positive lifetime wealth, so that `C₁ > 0`). -/
theorem hasDerivAt_consC1 {σ β Y1 Y2 r : ℝ} (hβ : 0 < β) (hr : 0 < 1 + r)
    (hW : 0 < Y1 + Y2 / (1 + r)) :
    HasDerivAt (consC1 σ β Y1 Y2)
      (((Y1 - consC1 σ β Y1 Y2 r) - σ * consC2 σ β Y1 Y2 r / (1 + r)) /
        (1 + r + consC2 σ β Y1 Y2 r / consC1 σ β Y1 Y2 r)) r := by
  have hP : 0 < (1 + r) ^ σ := Real.rpow_pos_of_pos hr σ
  have hB : 0 < β ^ σ := Real.rpow_pos_of_pos hβ σ
  have hg1 : (1 + r) ^ (σ - 1) = (1 + r) ^ σ / (1 + r) := Real.rpow_sub_one hr.ne' σ
  have hg2 : (1 + r) ^ (σ - 1 - 1) = (1 + r) ^ σ / (1 + r) ^ 2 := by
    rw [Real.rpow_sub_one hr.ne', hg1, div_div, ← sq]
  have hden : 0 < 1 + (1 + r) ^ (σ - 1) * β ^ σ := by rw [hg1]; positivity
  -- differentiate numerator and denominator
  have hWd : HasDerivAt (fun x => Y1 + Y2 / (1 + x))
      ((0 * (1 + r) - Y2 * 1) / (1 + r) ^ 2) r := by
    have h1 : HasDerivAt (fun x : ℝ => 1 + x) 1 r := (hasDerivAt_id r).const_add 1
    exact ((hasDerivAt_const r Y2).div h1 hr.ne').const_add Y1
  have hDd : HasDerivAt (fun x => 1 + (1 + x) ^ (σ - 1) * β ^ σ)
      (1 * (σ - 1) * (1 + r) ^ (σ - 1 - 1) * β ^ σ) r := by
    have h1 : HasDerivAt (fun x : ℝ => 1 + x) 1 r := (hasDerivAt_id r).const_add 1
    exact ((h1.rpow_const (p := σ - 1) (Or.inl hr.ne')).mul_const (β ^ σ)).const_add 1
  have hd := hWd.div hDd hden.ne'
  have hC1ne : consC1 σ β Y1 Y2 r ≠ 0 := div_ne_zero hW.ne' hden.ne'
  have hratio : consC2 σ β Y1 Y2 r / consC1 σ β Y1 Y2 r = (1 + r) ^ σ * β ^ σ := by
    unfold consC2
    field_simp
  rw [hratio]
  have hd' : HasDerivAt (consC1 σ β Y1 Y2) _ r := hd
  convert hd' using 1
  unfold consC2 consC1
  rw [hg2, hg1]
  rw [hg1] at hden
  field_simp
  ring

/-- O&R p. 29: for a date-1 borrower (`C₁ ≥ Y₁`) date-1 consumption falls when the interest
rate rises, `dC₁/dr < 0` (substitution and terms-of-trade effects reinforce). -/
theorem deriv_consC1_neg_of_borrower {σ β Y1 Y2 r : ℝ} (hσ : 0 < σ) (hβ : 0 < β)
    (hr : 0 < 1 + r) (hW : 0 < Y1 + Y2 / (1 + r)) (hborrow : Y1 ≤ consC1 σ β Y1 Y2 r) :
    deriv (consC1 σ β Y1 Y2) r < 0 := by
  rw [(hasDerivAt_consC1 hβ hr hW).deriv]
  have hP : 0 < (1 + r) ^ σ := Real.rpow_pos_of_pos hr σ
  have hB : 0 < β ^ σ := Real.rpow_pos_of_pos hβ σ
  have hden : 0 < 1 + (1 + r) ^ (σ - 1) * β ^ σ := by
    rw [Real.rpow_sub_one hr.ne' σ]; positivity
  have hC1 : 0 < consC1 σ β Y1 Y2 r := div_pos hW hden
  have hC2 : 0 < consC2 σ β Y1 Y2 r := by unfold consC2; positivity
  apply div_neg_of_neg_of_pos
  · have : 0 < σ * consC2 σ β Y1 Y2 r / (1 + r) := by positivity
    linarith
  · positivity

/-- O&R (1.23), p. 29, for a general period utility: suppose `C₁(r)` is differentiable at `r₀`
and satisfies the Euler equation `u'(C₁) = (1+r)βu'((1+r)(Y₁ − C₁) + Y₂)` identically near
`r₀` (budget substituted in, `B₁ = 0`). If `u'` has derivative `u''` at the two consumption
levels and the denominator is nonzero, then `dC₁/dr` is given by (1.23). -/
theorem dC1_dr_general {up upp C1 : ℝ → ℝ} {r0 d β Y1 Y2 : ℝ}
    (hup1 : HasDerivAt up (upp (C1 r0)) (C1 r0))
    (hup2 : HasDerivAt up (upp ((1 + r0) * (Y1 - C1 r0) + Y2)) ((1 + r0) * (Y1 - C1 r0) + Y2))
    (hC1 : HasDerivAt C1 d r0)
    (heuler : ∀ᶠ r in 𝓝 r0, up (C1 r) = (1 + r) * β * up ((1 + r) * (Y1 - C1 r) + Y2))
    (hden : upp (C1 r0) + β * (1 + r0) ^ 2 * upp ((1 + r0) * (Y1 - C1 r0) + Y2) ≠ 0) :
    d = (β * up ((1 + r0) * (Y1 - C1 r0) + Y2) +
          β * (1 + r0) * upp ((1 + r0) * (Y1 - C1 r0) + Y2) * (Y1 - C1 r0)) /
        (upp (C1 r0) + β * (1 + r0) ^ 2 * upp ((1 + r0) * (Y1 - C1 r0) + Y2)) := by
  set c2 := (1 + r0) * (Y1 - C1 r0) + Y2 with hc2
  have hL : HasDerivAt (fun r => up (C1 r)) (upp (C1 r0) * d) r0 := hup1.comp r0 hC1
  have hg : HasDerivAt (fun r => (1 + r) * (Y1 - C1 r) + Y2)
      (1 * (Y1 - C1 r0) + (1 + r0) * (0 - d)) r0 :=
    ((((hasDerivAt_id r0).const_add 1).mul ((hasDerivAt_const r0 Y1).sub hC1)).add_const Y2)
  have hR : HasDerivAt (fun r => (1 + r) * β * up ((1 + r) * (Y1 - C1 r) + Y2))
      ((1 * β) * up c2 + (1 + r0) * β * (upp c2 * (1 * (Y1 - C1 r0) + (1 + r0) * (0 - d))))
      r0 :=
    (((hasDerivAt_id r0).const_add 1).mul_const β).mul (hup2.comp r0 hg)
  have huniq := hL.unique (hR.congr_of_eventuallyEq heuler)
  rw [eq_div_iff hden]
  linear_combination huniq

/-- O&R p. 29: for isoelastic utility (`u' = C^{−1/σ}`, `u'' = −(1/σ)C^{−1/σ−1}`) and
consumption satisfying the Euler equation, the general formula (1.23) reduces to (1.24). -/
theorem general_formula_eq_isoelastic {σ β r Y1 C1 C2 : ℝ} (hσ : 0 < σ) (hβ : 0 < β)
    (hr : 0 < 1 + r) (hC1 : 0 < C1) (hC2 : 0 < C2)
    (heuler : C1 ^ (-1 / σ) = (1 + r) * β * C2 ^ (-1 / σ)) :
    (β * C2 ^ (-1 / σ) + β * (1 + r) * (-1 / σ * C2 ^ (-1 / σ - 1)) * (Y1 - C1)) /
        (-1 / σ * C1 ^ (-1 / σ - 1) + β * (1 + r) ^ 2 * (-1 / σ * C2 ^ (-1 / σ - 1))) =
      ((Y1 - C1) - σ * C2 / (1 + r)) / (1 + r + C2 / C1) := by
  rw [Real.rpow_sub_one hC1.ne', Real.rpow_sub_one hC2.ne', heuler]
  have hb : 0 < C2 ^ (-1 / σ) := Real.rpow_pos_of_pos hC2 _
  have hden : 0 < 1 + r + C2 / C1 := by positivity
  rw [div_eq_div_iff (by
      have : 0 < 1 / σ * ((1 + r) * β * C2 ^ (-1 / σ) / C1) +
          β * (1 + r) ^ 2 * (1 / σ * (C2 ^ (-1 / σ) / C2)) := by positivity
      intro h0
      linarith [show -1 / σ * ((1 + r) * β * C2 ^ (-1 / σ) / C1) +
          β * (1 + r) ^ 2 * (-1 / σ * (C2 ^ (-1 / σ) / C2)) = -(1 / σ * ((1 + r) * β *
          C2 ^ (-1 / σ) / C1) + β * (1 + r) ^ 2 * (1 / σ * (C2 ^ (-1 / σ) / C2))) by ring])
    hden.ne']
  field_simp
  ring

/-! ## Exercise 3: adding investment (O&R pp. 55–56) -/

/-- O&R exercise 3(a), p. 55: with `Y₂ = A₂K₂^α` (`0 < α < 1`), the investment condition
`A₂αK₂^{α−1} = r` holds exactly when `K₂ = (αA₂/r)^{1/(1−α)}` (for `r > 0`, `K₂ > 0`). -/
theorem ex3_capital_iff {α A2 r K2 : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hA : 0 < A2) (hr : 0 < r)
    (hK : 0 < K2) :
    A2 * α * K2 ^ (α - 1) = r ↔ K2 = (α * A2 / r) ^ (1 / (1 - α)) := by
  have hx : 0 < α * A2 / r := by positivity
  have h1α : (1 : ℝ) - α ≠ 0 := by linarith
  have key : A2 * α * ((α * A2 / r) ^ (1 / (1 - α))) ^ (α - 1) = r := by
    rw [← Real.rpow_mul hx.le]
    have he : 1 / (1 - α) * (α - 1) = -1 := by field_simp; ring
    rw [he, Real.rpow_neg_one]
    field_simp
  constructor
  · intro h
    have hne : α - 1 ≠ 0 := by linarith
    have heq : K2 ^ (α - 1) = ((α * A2 / r) ^ (1 / (1 - α))) ^ (α - 1) := by
      have hc : A2 * α ≠ 0 := by positivity
      exact mul_left_cancel₀ hc (h.trans key.symm)
    exact Real.rpow_left_injOn hne (show (0 : ℝ) ≤ K2 from hK.le)
      (show (0 : ℝ) ≤ (α * A2 / r) ^ (1 / (1 - α)) by positivity) heq
  · rintro rfl
    exact key

/-- O&R exercise 3(d), p. 56: with log utility, investment `I₁ = K₂ − K₁`, `I₂ = −K₂`
(capital consumed at the end) and optimal `K₂` from 3(a), the consumption function of
3(c), `C₁ = [Y₁ − I₁ + (Y₂ − I₂)/(1+r)]/(1+β)`, equals
`[K₁ + Y₁ + (1−α)/(1+r) · (α/r)^{α/(1−α)} A₂^{1/(1−α)}]/(1+β)`. -/
theorem ex3_consumption {α A2 r K1 K2 Y1 β : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hA : 0 < A2)
    (hr : 0 < r) (hK2 : K2 = (α * A2 / r) ^ (1 / (1 - α))) :
    (Y1 - (K2 - K1) + (A2 * K2 ^ α - (-K2)) / (1 + r)) / (1 + β) =
      (K1 + Y1 + (1 - α) / (1 + r) * (α / r) ^ (α / (1 - α)) * A2 ^ (1 / (1 - α))) /
        (1 + β) := by
  have hK : 0 < K2 := by rw [hK2]; positivity
  have h1α : (1 : ℝ) - α ≠ 0 := by linarith
  -- the investment condition, `r K₂ = α A₂ K₂^α`
  have hfoc := (ex3_capital_iff hα0 hα1 hA hr hK).mpr hK2
  rw [Real.rpow_sub_one hK.ne'] at hfoc
  have hrK : r * K2 = α * (A2 * K2 ^ α) := by
    rw [← hfoc]
    field_simp
  -- output: `A₂ K₂^α = (α/r)^{α/(1−α)} A₂^{1/(1−α)}`
  have hY : A2 * K2 ^ α = (α / r) ^ (α / (1 - α)) * A2 ^ (1 / (1 - α)) := by
    rw [hK2, ← Real.rpow_mul (by positivity), show α * A2 / r = α / r * A2 by ring,
      Real.mul_rpow (by positivity) hA.le]
    have he2 : 1 / (1 - α) * α = α / (1 - α) := by ring
    have hA' : A2 ^ (1 / (1 - α)) = A2 * A2 ^ (α / (1 - α)) := by
      rw [show 1 / (1 - α) = 1 + α / (1 - α) by field_simp; ring, Real.rpow_add hA,
        Real.rpow_one]
    rw [he2, hA']
    ring
  rw [show (1 - α) / (1 + r) * (α / r) ^ (α / (1 - α)) * A2 ^ (1 / (1 - α)) =
    (1 - α) / (1 + r) * ((α / r) ^ (α / (1 - α)) * A2 ^ (1 / (1 - α))) by ring, ← hY]
  congr 1
  have hr1 : (1 : ℝ) + r ≠ 0 := by linarith
  field_simp
  linear_combination -hrK

/-! ## Exercise 4: zero intertemporal substitutability, `σ → 0` (O&R p. 56) -/

/-- O&R exercise 4(a), p. 56: as `σ → 0` the Euler ratio `C₂/C₁ = (1+r)^σ β^σ` of (1.25)
tends to `1` (flat consumption, whatever `r`). -/
theorem ex4_growth_tendsto_one {β r : ℝ} (hβ : 0 < β) (hr : 0 < 1 + r) :
    Tendsto (fun σ : ℝ => (1 + r) ^ σ * β ^ σ) (𝓝 0) (𝓝 1) := by
  have h := (Real.continuousAt_const_rpow (b := 0) hr.ne').tendsto.mul
    (Real.continuousAt_const_rpow (b := 0) hβ.ne').tendsto
  simpa using h

/-- O&R exercise 4(b), p. 56: as `σ → 0` the consumption function (1.26) tends to
`C₁ = ((1+r)/(2+r)) Y₁ + (1/(2+r)) Y₂`. -/
theorem ex4_consC1_tendsto {β Y1 Y2 r : ℝ} (hβ : 0 < β) (hr : 0 < 1 + r) :
    Tendsto (fun σ : ℝ => consC1 σ β Y1 Y2 r) (𝓝 0)
      (𝓝 ((1 + r) / (2 + r) * Y1 + 1 / (2 + r) * Y2)) := by
  have hg : Tendsto (fun σ : ℝ => (1 + r) ^ (σ - 1)) (𝓝 0) (𝓝 ((1 + r) ^ ((0 : ℝ) - 1))) :=
    (Real.continuousAt_const_rpow (b := 0 - 1) hr.ne').tendsto.comp
      (tendsto_id.sub tendsto_const_nhds)
  have hb : Tendsto (fun σ : ℝ => β ^ σ) (𝓝 0) (𝓝 (β ^ (0 : ℝ))) :=
    (Real.continuousAt_const_rpow (b := 0) hβ.ne').tendsto
  have hden : (1 : ℝ) + (1 + r) ^ ((0 : ℝ) - 1) * β ^ (0 : ℝ) ≠ 0 := by
    have : 0 < (1 + r) ^ ((0 : ℝ) - 1) * β ^ (0 : ℝ) := by positivity
    linarith
  have h := (tendsto_const_nhds (x := Y1 + Y2 / (1 + r))).div
    (tendsto_const_nhds.add (hg.mul hb)) hden
  unfold consC1
  convert h using 2
  rw [zero_sub, Real.rpow_neg_one, Real.rpow_zero, mul_one]
  have h2 : (2 : ℝ) + r ≠ 0 := by linarith
  field_simp
  ring

/-- O&R exercise 4(b), p. 56: with the `σ → 0` consumption function and the current-account
identity `C₂ = (1+r)(Y₁ − C₁) + Y₂`, consumption is flat, `C₂ = C₁`. -/
theorem ex4_flat {r Y1 Y2 C1 C2 : ℝ} (hr : 0 < 1 + r)
    (hC1 : C1 = (1 + r) / (2 + r) * Y1 + 1 / (2 + r) * Y2)
    (hCA : C2 = (1 + r) * (Y1 - C1) + Y2) : C2 = C1 := by
  have h2 : (2 : ℝ) + r ≠ 0 := by linarith
  rw [hCA, hC1]
  field_simp
  ring

/-- O&R exercise 4(c), p. 56: the `σ → 0` consumption function has
`dC₁/dr = (Y₁ − Y₂)/(2+r)²`. -/
theorem ex4_hasDerivAt {r : ℝ} (Y1 Y2 : ℝ) (hr : 0 < 1 + r) :
    HasDerivAt (fun x : ℝ => (1 + x) / (2 + x) * Y1 + 1 / (2 + x) * Y2)
      ((Y1 - Y2) / (2 + r) ^ 2) r := by
  have h2 : (2 : ℝ) + r ≠ 0 := by linarith
  have hA : HasDerivAt (fun x : ℝ => 1 + x) 1 r := (hasDerivAt_id r).const_add 1
  have hB : HasDerivAt (fun x : ℝ => 2 + x) 1 r := (hasDerivAt_id r).const_add 2
  have h := ((hA.div hB h2).mul_const Y1).add (((hasDerivAt_const r 1).div hB h2).mul_const Y2)
  convert h using 1
  field_simp
  ring

/-- O&R exercise 4(d), p. 56: with lifetime utility
`(C₁^{1−1/σ} + β^{1/σ} C₂^{1−1/σ})/(1−1/σ)` the Euler equation
`C₁^{−1/σ} = (1+r) β^{1/σ} C₂^{−1/σ}` is equivalent to `C₂ = (1+r)^σ β C₁`. -/
theorem ex4d_euler_iff {σ β r C1 C2 : ℝ} (hσ : 0 < σ) (hβ : 0 < β) (hr : 0 < 1 + r)
    (hC1 : 0 < C1) (hC2 : 0 < C2) :
    C1 ^ (-1 / σ) = (1 + r) * β ^ (1 / σ) * C2 ^ (-1 / σ) ↔ C2 = (1 + r) ^ σ * β * C1 := by
  rw [euler_iff_growth hσ (Real.rpow_pos_of_pos hβ _) hr hC1 hC2, ← Real.rpow_mul hβ.le]
  have he : 1 / σ * σ = 1 := by field_simp
  rw [he, Real.rpow_one]

/-- O&R exercise 4(d), p. 56: under the utility of 4(d), as `σ → 0` the consumption ratio
`C₂/C₁ = (1+r)^σ β` tends to `β`, the Leontief pattern `C₂ = βC₁` of `min{βC₁, C₂}`. -/
theorem ex4d_ratio_tendsto {β r : ℝ} (hr : 0 < 1 + r) :
    Tendsto (fun σ : ℝ => (1 + r) ^ σ * β) (𝓝 0) (𝓝 β) := by
  have h := ((Real.continuousAt_const_rpow (b := 0) hr.ne').tendsto).mul_const β
  simpa using h

/-! ## Exercise 7: exponential (CARA) period utility (O&R p. 57) -/

/-- O&R exercise 7(a), p. 57: with `u(C) = −γ e^{−C/γ}` (so `u'(C) = e^{−C/γ}`) and
`R = 1/(1+r)`, the Euler equation `u'(C₁) = (1/R) β u'(C₂)` is equivalent to
`C₂ = C₁ + γ log(β/R)`. -/
theorem ex7_euler_iff {γ β R C1 C2 : ℝ} (hγ : 0 < γ) (hβ : 0 < β) (hR : 0 < R) :
    Real.exp (-C1 / γ) = 1 / R * β * Real.exp (-C2 / γ) ↔
      C2 = C1 + γ * Real.log (β / R) := by
  have hk : 1 / R * β = Real.exp (Real.log (β / R)) := by
    rw [Real.exp_log (div_pos hβ hR)]
    ring
  rw [hk, ← Real.exp_add, Real.exp_eq_exp]
  constructor
  · intro h
    field_simp at h
    linarith
  · intro h
    rw [h]
    field_simp
    ring

/-- The CARA consumption function of O&R exercise 7(b), p. 57:
`C₁ = [W₁ − Rγ log(β/R)]/(1+R)` with `W₁ = Y₁ + RY₂`. -/
noncomputable def caraC1 (γ β Y1 Y2 R : ℝ) : ℝ :=
  (Y1 + R * Y2 - R * γ * Real.log (β / R)) / (1 + R)

/-- O&R exercise 7(b), p. 57: the Euler equation plus the budget `C₁ + RC₂ = Y₁ + RY₂`
hold exactly when `C₁ = [W₁ − Rγ log(β/R)]/(1+R)` and `C₂ = C₁ + γ log(β/R)`. -/
theorem ex7_euler_budget_iff {γ β R Y1 Y2 C1 C2 : ℝ} (hγ : 0 < γ) (hβ : 0 < β) (hR : 0 < R) :
    (Real.exp (-C1 / γ) = 1 / R * β * Real.exp (-C2 / γ) ∧ C1 + R * C2 = Y1 + R * Y2) ↔
      (C1 = caraC1 γ β Y1 Y2 R ∧ C2 = C1 + γ * Real.log (β / R)) := by
  rw [ex7_euler_iff hγ hβ hR]
  unfold caraC1
  constructor
  · rintro ⟨h2, hb⟩
    refine ⟨?_, h2⟩
    rw [eq_div_iff (by linarith : (1 : ℝ) + R ≠ 0)]
    rw [h2] at hb
    linarith
  · rintro ⟨h1, h2⟩
    refine ⟨h2, ?_⟩
    rw [h2, h1]
    field_simp
    ring

/-- O&R exercise 7(c), p. 57: differentiating the CARA consumption function (including
`W₁ = Y₁ + RY₂`) gives
`dC₁/dR = −C₁/(1+R) + Y₂/(1+R) + γ/(1+R) · [1 − log(β/R)]`. -/
theorem ex7_hasDerivAt {γ β Y1 Y2 R : ℝ} (hβ : 0 < β) (hR : 0 < R) :
    HasDerivAt (caraC1 γ β Y1 Y2)
      (-caraC1 γ β Y1 Y2 R / (1 + R) + Y2 / (1 + R) +
        γ / (1 + R) * (1 - Real.log (β / R))) R := by
  have h1R : (1 : ℝ) + R ≠ 0 := by linarith
  -- on `R > 0`, `log(β/R) = log β − log R`
  have hev : (fun x => (Y1 + x * Y2 - x * γ * (Real.log β - Real.log x)) / (1 + x))
      =ᶠ[𝓝 R] caraC1 γ β Y1 Y2 := by
    filter_upwards [Ioi_mem_nhds hR] with x hx
    unfold caraC1
    rw [Real.log_div hβ.ne' (ne_of_gt hx)]
  have hlog : HasDerivAt (fun x => Real.log β - Real.log x) (0 - R⁻¹) R :=
    (hasDerivAt_const R _).sub (Real.hasDerivAt_log hR.ne')
  have hN : HasDerivAt (fun x => Y1 + x * Y2 - x * γ * (Real.log β - Real.log x))
      (1 * Y2 - (1 * γ * (Real.log β - Real.log R) + R * γ * (0 - R⁻¹))) R :=
    (((hasDerivAt_id R).mul_const Y2).const_add Y1).sub
      (((hasDerivAt_id R).mul_const γ).mul hlog)
  have hD : HasDerivAt (fun x : ℝ => 1 + x) 1 R := (hasDerivAt_id R).const_add 1
  have h := (hN.div hD h1R).congr_of_eventuallyEq hev.symm
  convert h using 1
  unfold caraC1
  rw [Real.log_div hβ.ne' hR.ne']
  field_simp
  ring

/-- O&R exercise 7(d), p. 57: for `u(C) = −γ e^{−C/γ}` the inverse elasticity of marginal
utility is not constant: `σ(C) = −u'(C)/(C u''(C)) = γ/C`. -/
theorem ex7_eis {γ : ℝ} (hγ : 0 < γ) (C : ℝ) :
    eis (fun c => -γ * Real.exp (-c / γ)) C = γ / C := by
  have h1 : ∀ x, HasDerivAt (fun c => -γ * Real.exp (-c / γ)) (Real.exp (-x / γ)) x := by
    intro x
    have hin : HasDerivAt (fun c : ℝ => -c / γ) (-1 / γ) x :=
      ((hasDerivAt_id x).neg.div_const γ).congr_deriv (by simp [neg_div])
    convert (hin.exp).const_mul (-γ) using 1
    field_simp
  have hd : deriv (fun c => -γ * Real.exp (-c / γ)) = fun x => Real.exp (-x / γ) := by
    funext x
    exact (h1 x).deriv
  have h2 : HasDerivAt (fun x => Real.exp (-x / γ)) (Real.exp (-C / γ) * (-1 / γ)) C :=
    (((hasDerivAt_id C).neg.div_const γ).congr_deriv (by simp [neg_div])).exp
  unfold eis
  rw [hd, h2.deriv]
  have he : 0 < Real.exp (-C / γ) := Real.exp_pos _
  by_cases hC : C = 0
  · simp [hC]
  field_simp

/-- O&R exercise 7(e), p. 57: with `C₂ = C₁ + γ log(β/R) ≠ 0` the derivative of 7(c) can be
written `dC₁/dR = σ(C₂)C₂/(1+R) − C₂/(1+R) + Y₂/(1+R)`, where `σ` is the CARA inverse
elasticity of 7(d). -/
theorem ex7_hasDerivAt_eis {γ β Y1 Y2 R : ℝ} (hγ : 0 < γ) (hβ : 0 < β) (hR : 0 < R)
    (hC2 : caraC1 γ β Y1 Y2 R + γ * Real.log (β / R) ≠ 0) :
    HasDerivAt (caraC1 γ β Y1 Y2)
      (eis (fun c => -γ * Real.exp (-c / γ)) (caraC1 γ β Y1 Y2 R + γ * Real.log (β / R)) *
          (caraC1 γ β Y1 Y2 R + γ * Real.log (β / R)) / (1 + R) -
        (caraC1 γ β Y1 Y2 R + γ * Real.log (β / R)) / (1 + R) + Y2 / (1 + R)) R := by
  convert ex7_hasDerivAt (γ := γ) (Y1 := Y1) (Y2 := Y2) hβ hR using 1
  rw [ex7_eis hγ, div_mul_cancel₀ _ hC2]
  have h1R : (1 : ℝ) + R ≠ 0 := by linarith
  field_simp
  ring

end ObstfeldRogoff.IntertemporalTrade.Isoelastic

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The two-country world equilibrium

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*,
§1.3, pp. 23–38, and Exercises 2 and 5. Two endowment economies, Home and
Foreign, trade date-1 for date-2 output at a common world rate `r`.

* **Walras's law** (p. 23): if the date-1 market clears, so does the date-2 market.
* **The world rate lies strictly between the two autarky rates** (p. 23), and the
  country with the lower autarky rate lends. The book shows this in Figure 1.5
  assuming upward-sloping saving curves; here it follows from the saving-sign
  lemma with no assumption on the slope of saving.
* **Existence** of an equilibrium. Optimal consumption is continuous in `r`
  (`continuousAt_optimal_c1`), and world excess demand changes sign between the
  two autarky rates, so the intermediate value theorem applies.
* **The first welfare theorem** (p. 33): the equilibrium allocation is Pareto optimal.
* **Log utility** (Exercises 2 and 5): the closed-form world rate is the mediant
  of the two autarky gross rates, the saving function, the welfare derivative
  `dU/dr = β(r − rA)/[(1 + r)((1 + r) + β(1 + rA))]`, and the comparative statics
  of the world rate in the four endowments.
* **Blanchard–Summers** (pp. 36–38): with Cobb–Douglas technology the saving curve
  shifts up by more than the investment curve, `(1 + r)/(1 + α/r) > r ⇔ α < 1`.

Uniqueness of equilibrium is not claimed: the book notes on p. 30 that it can fail.
-/

namespace ObstfeldRogoff.IntertemporalTrade.WorldEquilibrium

open Set Filter Topology Consumer

/-- An equilibrium of the two-country endowment world at rate `r` (O&R (1.19), p. 23): both
countries choose optimally and the date-1 goods market clears. -/
def IsEquilibrium (h hs : Household) (r c1 c2 s1 s2 : ℝ) : Prop :=
  h.IsOptimal r c1 c2 ∧ hs.IsOptimal r s1 s2 ∧ c1 + s1 = h.Y1 + hs.Y1

/-- **Walras's law** (O&R p. 23): in equilibrium the date-2 market clears too. -/
theorem walras_law {h hs : Household} {r c1 c2 s1 s2 : ℝ}
    (he : IsEquilibrium h hs r c1 c2 s1 s2) : c2 + s2 = h.Y2 + hs.Y2 := by
  obtain ⟨ho, hos, hc⟩ := he
  rw [h.optimal_binds ho, hs.optimal_binds hos]
  linear_combination (1 + r) * (-hc)

/-- **The world rate lies strictly between the autarky rates** (O&R p. 23, Figure 1.5). -/
theorem rate_between_autarky {h hs : Household} {u' us' : ℝ → ℝ}
    (hu : ∀ c, 0 < c → HasDerivAt h.u (u' c) c) (hpos : ∀ c, 0 < c → 0 < u' c)
    (hus : ∀ c, 0 < c → HasDerivAt hs.u (us' c) c) (hposs : ∀ c, 0 < c → 0 < us' c)
    {rA rAs r c1 c2 s1 s2 : ℝ} (hA : h.IsAutarkyRate rA) (hAs : hs.IsAutarkyRate rAs)
    (hlt : rA < rAs) (he : IsEquilibrium h hs r c1 c2 s1 s2) : rA < r ∧ r < rAs := by
  obtain ⟨ho, hos, hc⟩ := he
  constructor
  · by_contra hle
    push Not at hle
    have h1 : h.Y1 ≤ c1 := by
      rcases hle.lt_or_eq with hl | rfl
      · exact (h.saving_neg_of_lt_autarky hu hpos hA hl ho).le
      · exact (h.optimal_at_autarky hA ho).1.ge
    have h2 := hs.saving_neg_of_lt_autarky hus hposs hAs (hle.trans_lt hlt) hos
    linarith
  · by_contra hle
    push Not at hle
    have h1 : s1 ≤ hs.Y1 := by
      rcases hle.lt_or_eq with hl | rfl
      · exact (hs.saving_pos_of_autarky_lt hus hposs hAs hl hos).le
      · exact (hs.optimal_at_autarky hAs hos).1.le
    have h2 := h.saving_pos_of_autarky_lt hu hpos hA (hlt.trans_le hle) ho
    linarith

/-- **Pattern of trade** (O&R pp. 23–24): the country with the lower autarky rate lends on
date 1 and the other borrows. -/
theorem trade_pattern {h hs : Household} {u' us' : ℝ → ℝ}
    (hu : ∀ c, 0 < c → HasDerivAt h.u (u' c) c) (hpos : ∀ c, 0 < c → 0 < u' c)
    (hus : ∀ c, 0 < c → HasDerivAt hs.u (us' c) c) (hposs : ∀ c, 0 < c → 0 < us' c)
    {rA rAs r c1 c2 s1 s2 : ℝ} (hA : h.IsAutarkyRate rA) (hAs : hs.IsAutarkyRate rAs)
    (hlt : rA < rAs) (he : IsEquilibrium h hs r c1 c2 s1 s2) : c1 < h.Y1 ∧ hs.Y1 < s1 := by
  obtain ⟨h1, h2⟩ := rate_between_autarky hu hpos hus hposs hA hAs hlt he
  exact ⟨h.saving_pos_of_autarky_lt hu hpos hA h1 he.1,
    hs.saving_neg_of_lt_autarky hus hposs hAs h2 he.2.1⟩

/-- **Optimal consumption is continuous in the world rate.** If `c₁(r), c₂(r)` is optimal for
all `r` near `r₀ > −1` and `u'` is continuous, then `c₁` is continuous at `r₀`. -/
theorem continuousAt_optimal_c1 (h : Household) {u' : ℝ → ℝ}
    (hu : ∀ c, 0 < c → HasDerivAt h.u (u' c) c) (hcont : ContinuousOn u' (Ioi 0))
    {c1 c2 : ℝ → ℝ} {r0 : ℝ} (hr0 : 0 < 1 + r0)
    (hopt : ∀ᶠ r in 𝓝 r0, h.IsOptimal r (c1 r) (c2 r)) : ContinuousAt c1 r0 := by
  -- u' is strictly decreasing
  have anti : ∀ x y, 0 < x → x < y → u' y < u' x := fun x y hx hxy =>
    deriv_lt_of_strictConcave h.concave (mem_Ioi.2 hx) (mem_Ioi.2 (hx.trans hxy)) hxy
      (hu x hx) (hu y (hx.trans hxy))
  have anti' : ∀ x y, 0 < x → x ≤ y → u' y ≤ u' x := fun x y hx hxy => by
    rcases hxy.lt_or_eq with hl | rfl
    · exact (anti x y hx hl).le
    · exact le_rfl
  set g : ℝ → ℝ → ℝ := fun r t => h.Y2 + (1 + r) * (h.Y1 - t) with hg
  set ψ : ℝ → ℝ → ℝ := fun r t => u' t - (1 + r) * h.β * u' (g r t) with hψ
  -- ψ r t is continuous in r wherever g r₀ t > 0
  have hψcont : ∀ t, 0 < g r0 t → ContinuousAt (fun r => ψ r t) r0 := by
    intro t ht
    have hgc : ContinuousAt (fun r => g r t) r0 := by simp only [hg]; fun_prop
    have hu'c : ContinuousAt u' (g r0 t) := hcont.continuousAt (Ioi_mem_nhds ht)
    exact continuousAt_const.sub (((continuousAt_const.add continuousAt_id).mul
      continuousAt_const).mul (hu'c.comp (f := fun r => g r t) hgc))
  have hgcont : ∀ t, ContinuousAt (fun r => g r t) r0 := fun t => by simp only [hg]; fun_prop
  have hev1 : ∀ᶠ r in 𝓝 r0, 0 < 1 + r :=
    (continuousAt_const.add continuousAt_id).eventually (lt_mem_nhds hr0)
  have ho0 : h.IsOptimal r0 (c1 r0) (c2 r0) := hopt.self_of_nhds
  have ha := ho0.1.1
  have hb := ho0.1.2.1
  have hbind0 := h.optimal_binds ho0
  have heul0 := h.euler_of_optimal hu ho0
  -- the Euler residual is zero at every nearby optimum
  have euler_at : ∀ r x y, h.IsOptimal r x y → ψ r x = 0 := fun r x y ho => by
    have e := h.euler_of_optimal hu ho
    have b := h.optimal_binds ho
    simp only [hψ, hg, ← b]
    linarith
  refine tendsto_order.2 ⟨fun l hl => ?_, fun m hm => ?_⟩
  · -- lower bound
    set t := max l (c1 r0 / 2) with ht
    have ht0 : 0 < t := lt_max_of_lt_right (by linarith)
    have hta : t < c1 r0 := max_lt hl (by linarith)
    have hgt : c2 r0 < g r0 t := by simp only [hg]; rw [hbind0]; nlinarith
    have hψt : 0 < ψ r0 t := by
      have h1 := anti _ _ ht0 hta
      have h2 := anti _ _ hb hgt
      simp only [hψ]
      have : (1 + r0) * h.β * u' (g r0 t) < (1 + r0) * h.β * u' (c2 r0) :=
        mul_lt_mul_of_pos_left h2 (mul_pos hr0 h.β_pos)
      linarith
    have hevψ : ∀ᶠ r in 𝓝 r0, 0 < ψ r t :=
      (hψcont t (hb.trans hgt)).eventually (lt_mem_nhds hψt)
    have hevg : ∀ᶠ r in 𝓝 r0, 0 < g r t := (hgcont t).eventually (lt_mem_nhds (hb.trans hgt))
    filter_upwards [hopt, hevψ, hevg, hev1] with r hor hψr hgr hr1
    refine lt_of_le_of_lt (le_max_left l (c1 r0 / 2)) ?_
    by_contra hle
    push Not at hle
    have hx := hor.1.1
    have hbr := h.optimal_binds hor
    have hy : g r t ≤ c2 r := by simp only [hg]; rw [hbr]; nlinarith
    have h1 := anti' _ _ hx hle
    have h2 := anti' _ _ hgr hy
    have e := euler_at r _ _ hor
    have hgc : g r (c1 r) = c2 r := by simp only [hg]; rw [hbr]
    simp only [hψ] at e hψr
    rw [hgc] at e
    try rw [← ht] at h1
    have : (1 + r) * h.β * u' (c2 r) ≤ (1 + r) * h.β * u' (g r t) :=
      mul_le_mul_of_nonneg_left h2 (mul_pos hr1 h.β_pos).le
    linarith
  · -- upper bound
    set T := c1 r0 + c2 r0 / (1 + r0) with hT
    have haT : c1 r0 < T := by
      have : 0 < c2 r0 / (1 + r0) := div_pos hb hr0
      linarith
    set t := min m ((c1 r0 + T) / 2) with ht
    have hat : c1 r0 < t := lt_min hm (by linarith)
    have htT : t < T := min_lt_of_right_lt (by linarith)
    have hg0 : 0 < g r0 t := by
      simp only [hg]
      have e : c2 r0 = (1 + r0) * (T - c1 r0) := by rw [hT]; field_simp; ring
      rw [hbind0] at e
      nlinarith
    have hlt : g r0 t < c2 r0 := by simp only [hg]; rw [hbind0]; nlinarith
    have hψt : ψ r0 t < 0 := by
      have h1 := anti _ _ ha hat
      have h2 := anti _ _ hg0 hlt
      simp only [hψ]
      have : (1 + r0) * h.β * u' (c2 r0) < (1 + r0) * h.β * u' (g r0 t) :=
        mul_lt_mul_of_pos_left h2 (mul_pos hr0 h.β_pos)
      linarith
    have hevψ : ∀ᶠ r in 𝓝 r0, ψ r t < 0 := (hψcont t hg0).eventually (gt_mem_nhds hψt)
    have hevg : ∀ᶠ r in 𝓝 r0, 0 < g r t := (hgcont t).eventually (lt_mem_nhds hg0)
    filter_upwards [hopt, hevψ, hevg, hev1] with r hor hψr hgr hr1
    refine lt_of_lt_of_le ?_ (min_le_left m ((c1 r0 + T) / 2))
    by_contra hle
    push Not at hle
    have hbr := h.optimal_binds hor
    have hy : c2 r ≤ g r t := by simp only [hg]; rw [hbr]; nlinarith
    have h1 := anti' _ _ (ha.trans hat) hle
    have h2 := anti' _ _ hor.1.2.1 hy
    have e := euler_at r _ _ hor
    have hgc : g r (c1 r) = c2 r := by simp only [hg]; rw [hbr]
    simp only [hψ] at e hψr
    rw [hgc] at e
    try rw [← ht] at h1
    have : (1 + r) * h.β * u' (g r t) ≤ (1 + r) * h.β * u' (c2 r) :=
      mul_le_mul_of_nonneg_left h2 (mul_pos hr1 h.β_pos).le
    linarith

/-- The autarky rate exists: `1 + rA = u'(Y₁)/(β u'(Y₂))` (O&R (1.7)). -/
theorem exists_autarkyRate (h : Household) {u' : ℝ → ℝ}
    (hu : ∀ c, 0 < c → HasDerivAt h.u (u' c) c) (hpos : ∀ c, 0 < c → 0 < u' c) :
    ∃ rA, 0 < 1 + rA ∧ h.IsAutarkyRate rA := by
  have h1 := hpos _ h.Y1_pos
  have h2 := hpos _ h.Y2_pos
  have hq : 0 < u' h.Y1 / (h.β * u' h.Y2) := div_pos h1 (mul_pos h.β_pos h2)
  have hr : 0 < 1 + (u' h.Y1 / (h.β * u' h.Y2) - 1) := by linarith
  refine ⟨u' h.Y1 / (h.β * u' h.Y2) - 1, hr, (h.isAutarkyRate_iff hu hpos hr).2 ?_⟩
  have hβ := h.β_pos.ne'
  have h1' := h1.ne'
  have h2' := h2.ne'
  rw [add_sub_cancel, one_div_div]

/-- A selection of optimal plans, one for every `r > −1`. -/
theorem exists_optimal_selection (h : Household) {u' : ℝ → ℝ}
    (hu : ∀ c, 0 < c → HasDerivAt h.u (u' c) c) (hpos : ∀ c, 0 < c → 0 < u' c)
    (hcont : ContinuousOn u' (Ioi 0)) (hinada : Tendsto u' (𝓝[>] 0) atTop) :
    ∃ f : ℝ → ℝ × ℝ, ∀ r, 0 < 1 + r → h.IsOptimal r (f r).1 (f r).2 := by
  have hsel : ∀ r, ∃ p : ℝ × ℝ, 0 < 1 + r → h.IsOptimal r p.1 p.2 := fun r => by
    by_cases hr : 0 < 1 + r
    · obtain ⟨c1, c2, ho⟩ := h.exists_optimal hu hpos hcont hinada hr
      exact ⟨(c1, c2), fun _ => ho⟩
    · exact ⟨(0, 0), fun h' => absurd h' hr⟩
  choose f hf using hsel
  exact ⟨f, hf⟩

/-- Existence of equilibrium when Home's autarky rate is weakly below Foreign's: world excess
demand is positive at `rA` and negative at `rA*`, and continuous in between. -/
theorem exists_equilibrium_of_le {h hs : Household} {u' us' : ℝ → ℝ}
    (hu : ∀ c, 0 < c → HasDerivAt h.u (u' c) c) (hpos : ∀ c, 0 < c → 0 < u' c)
    (hcont : ContinuousOn u' (Ioi 0)) (hinada : Tendsto u' (𝓝[>] 0) atTop)
    (hus : ∀ c, 0 < c → HasDerivAt hs.u (us' c) c) (hposs : ∀ c, 0 < c → 0 < us' c)
    (hconts : ContinuousOn us' (Ioi 0)) (hinadas : Tendsto us' (𝓝[>] 0) atTop)
    {rA rAs : ℝ} (hr : 0 < 1 + rA) (hA : h.IsAutarkyRate rA) (hAs : hs.IsAutarkyRate rAs)
    (hle : rA ≤ rAs) : ∃ r c1 c2 s1 s2, IsEquilibrium h hs r c1 c2 s1 s2 := by
  rcases hle.lt_or_eq with hlt | rfl
  swap
  · exact ⟨rA, h.Y1, h.Y2, hs.Y1, hs.Y2, hA, hAs, rfl⟩
  obtain ⟨f, hf⟩ := exists_optimal_selection h hu hpos hcont hinada
  obtain ⟨fs, hfs⟩ := exists_optimal_selection hs hus hposs hconts hinadas
  set z : ℝ → ℝ := fun r => (f r).1 + (fs r).1 - (h.Y1 + hs.Y1) with hz
  have hzc : ContinuousOn z (Icc rA rAs) := by
    intro r hri
    have hr1 : 0 < 1 + r := by linarith [hri.1]
    have hev : ∀ᶠ r' in 𝓝 r, 0 < 1 + r' :=
      (continuousAt_const.add continuousAt_id).eventually (lt_mem_nhds hr1)
    have c1 := continuousAt_optimal_c1 h hu hcont hr1 (hev.mono fun r' h' => hf r' h')
    have c2 := continuousAt_optimal_c1 hs hus hconts hr1 (hev.mono fun r' h' => hfs r' h')
    exact ((c1.add c2).sub continuousAt_const).continuousWithinAt
  have hrs : 0 < 1 + rAs := by linarith
  have hza : 0 < z rA := by
    have e1 := (h.optimal_at_autarky hA (hf rA hr)).1
    have e2 := hs.saving_neg_of_lt_autarky hus hposs hAs hlt (hfs rA hr)
    simp only [hz]
    linarith
  have hzb : z rAs < 0 := by
    have e1 := h.saving_pos_of_autarky_lt hu hpos hA hlt (hf rAs hrs)
    have e2 := (hs.optimal_at_autarky hAs (hfs rAs hrs)).1
    simp only [hz]
    linarith
  obtain ⟨r, hri, hzr⟩ := intermediate_value_Icc' hlt.le hzc ⟨hzb.le, hza.le⟩
  have hr1 : 0 < 1 + r := by linarith [hri.1]
  refine ⟨r, (f r).1, (f r).2, (fs r).1, (fs r).2, hf r hr1, hfs r hr1, ?_⟩
  simp only [hz] at hzr
  linarith

/-- **Existence of a world equilibrium**: two households with continuous, positive marginal
utility satisfying the Inada condition have an equilibrium world interest rate. -/
theorem exists_equilibrium {h hs : Household} {u' us' : ℝ → ℝ}
    (hu : ∀ c, 0 < c → HasDerivAt h.u (u' c) c) (hpos : ∀ c, 0 < c → 0 < u' c)
    (hcont : ContinuousOn u' (Ioi 0)) (hinada : Tendsto u' (𝓝[>] 0) atTop)
    (hus : ∀ c, 0 < c → HasDerivAt hs.u (us' c) c) (hposs : ∀ c, 0 < c → 0 < us' c)
    (hconts : ContinuousOn us' (Ioi 0)) (hinadas : Tendsto us' (𝓝[>] 0) atTop) :
    ∃ r c1 c2 s1 s2, IsEquilibrium h hs r c1 c2 s1 s2 := by
  obtain ⟨rA, hr, hA⟩ := exists_autarkyRate h hu hpos
  obtain ⟨rAs, hrs, hAs⟩ := exists_autarkyRate hs hus hposs
  rcases le_total rA rAs with hle | hle
  · exact exists_equilibrium_of_le hu hpos hcont hinada hus hposs hconts hinadas hr hA hAs hle
  · obtain ⟨r, s1, s2, c1, c2, hos, ho, hc⟩ :=
      exists_equilibrium_of_le hus hposs hconts hinadas hu hpos hcont hinada hrs hAs hA hle
    exact ⟨r, c1, c2, s1, s2, ho, hos, by linarith⟩

/-- A bundle at least as good as the optimum costs at least the household's wealth. -/
theorem cost_ge_of_utility_ge (h : Household) {r c1 c2 d1 d2 : ℝ} (ho : h.IsOptimal r c1 c2)
    (hd1 : 0 < d1) (hd2 : 0 < d2) (hU : h.utility c1 c2 ≤ h.utility d1 d2) :
    h.Y2 + (1 + r) * (h.Y1 - d1) ≤ d2 := by
  by_contra hlt
  push Not at hlt
  have h1 := ho.2 d1 _ ⟨hd1, hd2.trans hlt, le_rfl⟩
  have h2 := h.utility_lt_utility_of_lt (c1 := d1) hd2 hlt
  linarith

/-- A bundle strictly better than the optimum costs strictly more than the household's wealth. -/
theorem cost_gt_of_utility_gt (h : Household) {r c1 c2 d1 d2 : ℝ} (ho : h.IsOptimal r c1 c2)
    (hd1 : 0 < d1) (hd2 : 0 < d2) (hU : h.utility c1 c2 < h.utility d1 d2) :
    h.Y2 + (1 + r) * (h.Y1 - d1) < d2 := by
  by_contra hle
  push Not at hle
  linarith [ho.2 d1 d2 ⟨hd1, hd2, hle⟩]

/-- **The first welfare theorem** (O&R p. 33): no feasible allocation makes one country better
off without making the other worse off. -/
theorem first_welfare_theorem {h hs : Household} {r c1 c2 s1 s2 d1 d2 e1 e2 : ℝ}
    (hr : 0 < 1 + r) (he : IsEquilibrium h hs r c1 c2 s1 s2) (hd1 : 0 < d1) (hd2 : 0 < d2)
    (he1 : 0 < e1) (he2 : 0 < e2) (hres1 : d1 + e1 ≤ h.Y1 + hs.Y1)
    (hres2 : d2 + e2 ≤ h.Y2 + hs.Y2) (hU : h.utility c1 c2 ≤ h.utility d1 d2)
    (hUs : hs.utility s1 s2 ≤ hs.utility e1 e2) :
    h.utility c1 c2 = h.utility d1 d2 ∧ hs.utility s1 s2 = hs.utility e1 e2 := by
  obtain ⟨ho, hos, -⟩ := he
  have wd := cost_ge_of_utility_ge h ho hd1 hd2 hU
  have we := cost_ge_of_utility_ge hs hos he1 he2 hUs
  have hsum : 0 ≤ (1 + r) * (h.Y1 + hs.Y1 - d1 - e1) := mul_nonneg hr.le (by linarith)
  constructor
  · by_contra hne
    have := cost_gt_of_utility_gt h ho hd1 hd2 (lt_of_le_of_ne hU hne)
    nlinarith
  · by_contra hne
    have := cost_gt_of_utility_gt hs hos he1 he2 (lt_of_le_of_ne hUs hne)
    nlinarith

/-! ### Log utility: Exercises 2 and 5 (O&R pp. 55–56) -/

/-- Log-utility date-1 consumption, `C₁ = (Y₁ + Y₂/(1 + r))/(1 + β)` (Exercise 2(a)). -/
noncomputable def logC1 (β Y1 Y2 r : ℝ) : ℝ := (Y1 + Y2 / (1 + r)) / (1 + β)

/-- **Exercise 2(b)**: log-utility saving, `S₁ = βY₁/(1 + β) − Y₂/((1 + β)(1 + r))`. -/
theorem log_saving {β Y1 Y2 r : ℝ} (hβ : 0 < β) (hr : 0 < 1 + r) :
    Y1 - logC1 β Y1 Y2 r = β / (1 + β) * Y1 - Y2 / ((1 + β) * (1 + r)) := by
  have : (1 + β) ≠ 0 := by linarith
  unfold logC1
  field_simp
  ring

/-- **Exercise 2(c)**: the world market clears iff
`1 + r = [Y₂/(1 + β) + Y₂*/(1 + β*)]/[βY₁/(1 + β) + β*Y₁*/(1 + β*)]`. -/
theorem log_equilibrium_iff {β βs Y1 Y2 Y1s Y2s r : ℝ} (hβ : 0 < β) (hβs : 0 < βs)
    (hY1 : 0 < Y1) (hY1s : 0 < Y1s) (hr : 0 < 1 + r) :
    logC1 β Y1 Y2 r + logC1 βs Y1s Y2s r = Y1 + Y1s ↔
      1 + r = (Y2 / (1 + β) + Y2s / (1 + βs)) / (β * Y1 / (1 + β) + βs * Y1s / (1 + βs)) := by
  have h1 : (1 + β) ≠ 0 := by linarith
  have h2 : (1 + βs) ≠ 0 := by linarith
  have hB : 0 < β * Y1 / (1 + β) + βs * Y1s / (1 + βs) := by positivity
  have key : logC1 β Y1 Y2 r + logC1 βs Y1s Y2s r - (Y1 + Y1s) =
      (Y2 / (1 + β) + Y2s / (1 + βs)) / (1 + r) -
        (β * Y1 / (1 + β) + βs * Y1s / (1 + βs)) := by
    unfold logC1
    field_simp
    ring
  rw [eq_div_iff hB.ne']
  constructor
  · intro heq
    have hk : (Y2 / (1 + β) + Y2s / (1 + βs)) / (1 + r) =
        β * Y1 / (1 + β) + βs * Y1s / (1 + βs) := by linarith
    rw [div_eq_iff hr.ne'] at hk
    linarith
  · intro heq
    have hk : (Y2 / (1 + β) + Y2s / (1 + βs)) / (1 + r) =
        β * Y1 / (1 + β) + βs * Y1s / (1 + βs) := by
      rw [div_eq_iff hr.ne']
      linarith
    linarith

/-- The mediant of two fractions lies strictly between them. -/
theorem mediant_between {a b c d : ℝ} (hb : 0 < b) (hd : 0 < d) (h : a / b < c / d) :
    a / b < (a + c) / (b + d) ∧ (a + c) / (b + d) < c / d := by
  rw [div_lt_div_iff₀ hb hd] at h
  constructor
  · rw [div_lt_div_iff₀ hb (by linarith)]
    nlinarith
  · rw [div_lt_div_iff₀ (by linarith) hd]
    nlinarith

/-- **Exercise 2(d)**: the log-utility world gross rate lies strictly between the two autarky
gross rates `Y₂/(βY₁)` and `Y₂*/(β*Y₁*)`. -/
theorem log_rate_between {β βs Y1 Y2 Y1s Y2s : ℝ} (hβ : 0 < β) (hβs : 0 < βs)
    (hY1 : 0 < Y1) (hY1s : 0 < Y1s) (hlt : Y2 / (β * Y1) < Y2s / (βs * Y1s)) :
    Y2 / (β * Y1) < (Y2 / (1 + β) + Y2s / (1 + βs)) / (β * Y1 / (1 + β) + βs * Y1s / (1 + βs))
    ∧ (Y2 / (1 + β) + Y2s / (1 + βs)) / (β * Y1 / (1 + β) + βs * Y1s / (1 + βs)) <
      Y2s / (βs * Y1s) := by
  have h1 : (1 + β) ≠ 0 := by linarith
  have h2 : (1 + βs) ≠ 0 := by linarith
  have ea : Y2 / (1 + β) / (β * Y1 / (1 + β)) = Y2 / (β * Y1) := by field_simp
  have ec : Y2s / (1 + βs) / (βs * Y1s / (1 + βs)) = Y2s / (βs * Y1s) := by field_simp
  have hm := mediant_between (a := Y2 / (1 + β)) (c := Y2s / (1 + βs))
    (by positivity : 0 < β * Y1 / (1 + β)) (by positivity : 0 < βs * Y1s / (1 + βs))
    (by rw [ea, ec]; exact hlt)
  rw [ea, ec] at hm
  exact hm

/-- Log-utility lifetime welfare as a function of the world rate (Exercise 2(f)). -/
noncomputable def logWelfare (β Y1 Y2 r : ℝ) : ℝ :=
  Real.log (logC1 β Y1 Y2 r) + β * Real.log ((1 + r) * β * logC1 β Y1 Y2 r)

/-- **Exercise 2(f)**: `dU/dr = β(r − rA)/[(1 + r)((1 + r) + β(1 + rA))]` where
`1 + rA = Y₂/(βY₁)` is the autarky gross rate. Welfare rises with `r` iff `r > rA`. -/
theorem hasDerivAt_logWelfare {β Y1 Y2 r rA : ℝ} (hβ : 0 < β) (hY1 : 0 < Y1) (hY2 : 0 < Y2)
    (hr : 0 < 1 + r) (hrA : 1 + rA = Y2 / (β * Y1)) :
    HasDerivAt (logWelfare β Y1 Y2)
      (β / (1 + r) * ((r - rA) / ((1 + r) + β * (1 + rA)))) r := by
  have h1b : (0 : ℝ) < 1 + β := by linarith
  have hW : 0 < Y1 + Y2 / (1 + r) := by positivity
  have hC : 0 < logC1 β Y1 Y2 r := div_pos hW h1b
  have hd1 : HasDerivAt (fun s : ℝ => 1 + s) 1 r := (hasDerivAt_id r).const_add 1
  have hdW : HasDerivAt (fun s => Y1 + Y2 / (1 + s)) (-(Y2 * 1) / (1 + r) ^ 2) r := by
    have := (hasDerivAt_const r Y2).div hd1 hr.ne'
    simpa using this.const_add Y1
  have hdC : HasDerivAt (logC1 β Y1 Y2) (-(Y2 * 1) / (1 + r) ^ 2 / (1 + β)) r :=
    hdW.div_const (1 + β)
  have hdC2 : HasDerivAt (fun s => (1 + s) * β * logC1 β Y1 Y2 s)
      (1 * β * logC1 β Y1 Y2 r + (1 + r) * β * (-(Y2 * 1) / (1 + r) ^ 2 / (1 + β))) r :=
    (hd1.mul_const β).mul hdC
  have hC2 : 0 < (1 + r) * β * logC1 β Y1 Y2 r := by positivity
  have := (hdC.log hC.ne').add ((hdC2.log hC2.ne').const_mul β)
  refine this.congr_deriv ?_
  have hβ1 : (1 + rA) = Y2 / (β * Y1) := hrA
  have hden : 0 < (1 + r) + β * (1 + rA) := by rw [hrA]; positivity
  have hY : Y2 = β * Y1 * (1 + rA) := by rw [hrA]; field_simp
  unfold logC1
  rw [hβ1]
  field_simp
  linear_combination (-1 : ℝ) * hY

/-- The log-utility world gross rate from Exercise 2(c). -/
noncomputable def logGrossRate (β βs Y1 Y2 Y1s Y2s : ℝ) : ℝ :=
  (Y2 / (1 + β) + Y2s / (1 + βs)) / (β * Y1 / (1 + β) + βs * Y1s / (1 + βs))

/-- **Exercise 5 (log utility)**: a rise in Home's date-1 output lowers the world rate. -/
theorem logGrossRate_anti_Y1 {β βs Y2 Y1s Y2s : ℝ} (hβ : 0 < β) (hβs : 0 < βs)
    (hY2 : 0 < Y2) (hY1s : 0 < Y1s) (hY2s : 0 < Y2s) :
    StrictAntiOn (fun Y1 => logGrossRate β βs Y1 Y2 Y1s Y2s) (Ioi 0) := by
  intro a ha b hb hab
  have ha' : (0 : ℝ) < a := ha
  unfold logGrossRate
  apply div_lt_div_of_pos_left (by positivity) (by positivity)
  have : β * a / (1 + β) < β * b / (1 + β) :=
    div_lt_div_of_pos_right (mul_lt_mul_of_pos_left hab hβ) (by linarith)
  linarith

/-- **Exercise 5 (log utility)**: a rise in Home's date-2 output raises the world rate. -/
theorem logGrossRate_mono_Y2 {β βs Y1 Y1s Y2s : ℝ} (hβ : 0 < β) (hβs : 0 < βs)
    (hY1 : 0 < Y1) (hY1s : 0 < Y1s) :
    StrictMono (fun Y2 => logGrossRate β βs Y1 Y2 Y1s Y2s) := by
  intro a b hab
  unfold logGrossRate
  apply div_lt_div_of_pos_right _ (by positivity)
  have : a / (1 + β) < b / (1 + β) := div_lt_div_of_pos_right hab (by linarith)
  linarith

/-- The world rate is symmetric in the two countries. -/
theorem logGrossRate_comm (β βs Y1 Y2 Y1s Y2s : ℝ) :
    logGrossRate β βs Y1 Y2 Y1s Y2s = logGrossRate βs β Y1s Y2s Y1 Y2 := by
  unfold logGrossRate
  rw [add_comm (Y2 / (1 + β)), add_comm (β * Y1 / (1 + β))]

/-- **Exercise 5 (log utility)**: a rise in Foreign's date-1 output lowers the world rate. -/
theorem logGrossRate_anti_Y1s {β βs Y1 Y2 Y2s : ℝ} (hβ : 0 < β) (hβs : 0 < βs)
    (hY1 : 0 < Y1) (hY2 : 0 < Y2) (hY2s : 0 < Y2s) :
    StrictAntiOn (fun Y1s => logGrossRate β βs Y1 Y2 Y1s Y2s) (Ioi 0) := by
  simp only [logGrossRate_comm β βs Y1 Y2]
  exact logGrossRate_anti_Y1 hβs hβ hY2s hY1 hY2

/-- **Exercise 5 (log utility)**: a rise in Foreign's date-2 output raises the world rate. -/
theorem logGrossRate_mono_Y2s {β βs Y1 Y2 Y1s : ℝ} (hβ : 0 < β) (hβs : 0 < βs)
    (hY1 : 0 < Y1) (hY1s : 0 < Y1s) :
    StrictMono (fun Y2s => logGrossRate β βs Y1 Y2 Y1s Y2s) := by
  simp only [logGrossRate_comm β βs Y1 Y2]
  exact logGrossRate_mono_Y2 hβs hβ hY1s hY1

/-! ### Investment and productivity (O&R pp. 31–38) -/

/-- **Investment responds to productivity** (O&R p. 34): along a path `K₂(A₂)` with
`A₂ F'(K₂) = r` at a constant `r`, `dK₂/dA₂ = −F'(K₂)/(A₂ F''(K₂))`. -/
theorem hasDerivAt_capital_productivity {F' K : ℝ → ℝ} {A r dK dF : ℝ}
    (hK : HasDerivAt K dK A) (hF : HasDerivAt F' dF (K A))
    (hid : ∀ᶠ a in 𝓝 A, a * F' (K a) = r) (hA : A ≠ 0) (hdF : dF ≠ 0) :
    dK = -F' (K A) / (A * dF) := by
  have hd : HasDerivAt (fun a => a * F' (K a)) (1 * F' (K A) + A * (dF * dK)) A :=
    (hasDerivAt_id A).mul (hF.comp A hK)
  have hc : HasDerivAt (fun a => a * F' (K a)) 0 A :=
    (hasDerivAt_const A r).congr_of_eventuallyEq hid
  have := hd.unique hc
  field_simp
  linarith

/-- With `F' > 0` and `F'' < 0`, higher productivity raises investment at a given world
rate (O&R p. 34). -/
theorem capital_increasing_in_productivity {F' K : ℝ → ℝ} {A r dK dF : ℝ}
    (hK : HasDerivAt K dK A) (hF : HasDerivAt F' dF (K A))
    (hid : ∀ᶠ a in 𝓝 A, a * F' (K a) = r) (hA : 0 < A) (hF'pos : 0 < F' (K A))
    (hdF : dF < 0) : 0 < dK := by
  rw [hasDerivAt_capital_productivity hK hF hid hA.ne' hdF.ne]
  exact div_pos_of_neg_of_neg (by linarith) (mul_neg_of_pos_of_neg hA hdF)

/-- **Blanchard–Summers** (O&R pp. 36–38): with `Y = A K^α`, a productivity rise shifts the
world saving curve up by `(1 + r)/(1 + α/r) · Â₂` and the investment curve by `r · Â₂`; the
saving shift is larger iff `α < 1`, so world investment falls. -/
theorem blanchard_summers {r α : ℝ} (hr : 0 < r) (hα : 0 < α) :
    r < (1 + r) / (1 + α / r) ↔ α < 1 := by
  have e : (1 + r) / (1 + α / r) = (1 + r) * r / (r + α) := by field_simp
  rw [e, lt_div_iff₀ (by linarith)]
  constructor <;> intro h <;> nlinarith

end ObstfeldRogoff.IntertemporalTrade.WorldEquilibrium

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Real interest rates and consumption in detail: the dual approach

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §1.3.4
"Real Interest Rates and Consumption in Detail", pp. 39–42. Prices are measured by the market
discount factor `R = 1/(1+r)`, the price of date-2 consumption in date-1 units.

* `ExpenditureSystem` packages a lifetime utility `V(C₁, C₂)` (not assumed additive), an
  expenditure function `E(R, U)` and Hicksian demands, through the minimisation property only.
* Shephard's lemma (1.27) is proved from the minimisation property by the envelope (local
  minimum) argument of footnote 18; the welfare effect (1.28), the Slutsky equation (1.30) and
  the total-effect decomposition (1.31) follow by the chain rule from the budget identity and
  the duality identity (1.29).
* §1.3.4.4 (p. 42): for isoelastic additive utility we construct the expenditure system
  explicitly (proving the Hicksian bundle really is cost-minimising), verify Shephard's lemma,
  the duality identity and the Slutsky equation in closed form, and show the p. 42 formula for
  `dC₁/dR` is equivalent to (1.24) of p. 29.
-/

namespace ObstfeldRogoff.IntertemporalTrade.Duality

open Filter Topology

/-- The dual description of the two-period consumer, O&R §1.3.4.1, p. 39. `V C₁ C₂` is lifetime
utility (any function, additivity is not assumed), `Uset` the attainable utility levels,
`E R U` the expenditure function and `C1H`, `C2H` the Hicksian demands. The fields say exactly
that the Hicksian bundle is positive, attains `U`, costs `E R U`, and that no positive bundle
attaining `U` costs less: `E R U = min {C₁ + R C₂ : V C₁ C₂ ≥ U}` for every price `R > 0`. -/
structure ExpenditureSystem where
  V : ℝ → ℝ → ℝ
  Uset : Set ℝ
  E : ℝ → ℝ → ℝ
  C1H : ℝ → ℝ → ℝ
  C2H : ℝ → ℝ → ℝ
  le_cost : ∀ R U C1 C2, 0 < R → U ∈ Uset → 0 < C1 → 0 < C2 → U ≤ V C1 C2 →
    E R U ≤ C1 + R * C2
  C1H_pos : ∀ R U, 0 < R → U ∈ Uset → 0 < C1H R U
  C2H_pos : ∀ R U, 0 < R → U ∈ Uset → 0 < C2H R U
  attains : ∀ R U, 0 < R → U ∈ Uset → U ≤ V (C1H R U) (C2H R U)
  cost_eq : ∀ R U, 0 < R → U ∈ Uset → E R U = C1H R U + R * C2H R U

/-- Chain rule along a path, the calculus behind O&R (1.28) and (1.30)–(1.31), pp. 40–41: if
`F` has partial derivatives `a`, `b` (jointly, i.e. Fréchet) at `(x, g x)` and `g` has
derivative `g'`, then `t ↦ F (t, g t)` has derivative `a + b g'`. -/
theorem hasDerivAt_along_path {F : ℝ × ℝ → ℝ} {g : ℝ → ℝ} {a b g' x : ℝ}
    (hF : HasFDerivAt F (a • ContinuousLinearMap.fst ℝ ℝ ℝ + b • ContinuousLinearMap.snd ℝ ℝ ℝ)
      (x, g x))
    (hg : HasDerivAt g g' x) :
    HasDerivAt (fun t => F (t, g t)) (a + b * g') x := by
  have hp : HasDerivAt (fun t => (t, g t)) ((1 : ℝ), g') x := (hasDerivAt_id x).prodMk hg
  have h := hF.comp_hasDerivAt x hp
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul, mul_one] at h
  exact h

namespace ExpenditureSystem

/-- Envelope inequality of O&R fn. 18, p. 39: the Hicksian bundle chosen at price `R` still
attains `U` at any other price `R' > 0`, so `E(R', U) ≤ C₁ᴴ(R, U) + R' C₂ᴴ(R, U)`, with
equality at `R' = R`. -/
theorem E_le_hicksian_cost (s : ExpenditureSystem) {R R' U : ℝ} (hR : 0 < R) (hR' : 0 < R')
    (hU : U ∈ s.Uset) : s.E R' U ≤ s.C1H R U + R' * s.C2H R U :=
  s.le_cost R' U _ _ hR' hU (s.C1H_pos R U hR hU) (s.C2H_pos R U hR hU) (s.attains R U hR hU)

/-- Shephard's lemma, O&R (1.27), p. 39: if the expenditure function is differentiable in `R`,
its derivative is the Hicksian demand for date-2 consumption, `E_R(R, U) = C₂ᴴ(R, U)`.
Proof as in fn. 18 (an envelope theorem): `R' ↦ C₁ᴴ(R,U) + R' C₂ᴴ(R,U) − E(R', U)` is
nonnegative near `R` and zero at `R`, so it has a local minimum there. -/
theorem shephard (s : ExpenditureSystem) {R U e : ℝ} (hR : 0 < R) (hU : U ∈ s.Uset)
    (hE : HasDerivAt (fun R' => s.E R' U) e R) : e = s.C2H R U := by
  have hmin : IsLocalMin (fun R' => s.C1H R U + R' * s.C2H R U - s.E R' U) R := by
    filter_upwards [Ioi_mem_nhds hR] with R' hR'
    have h1 := s.E_le_hicksian_cost hR hR' hU
    have h2 := s.cost_eq R U hR hU
    linarith
  have hd : HasDerivAt (fun R' => s.C1H R U + R' * s.C2H R U - s.E R' U)
      (s.C2H R U - e) R := by
    have := (((hasDerivAt_id R).mul_const (s.C2H R U)).const_add (s.C1H R U)).sub hE
    rw [one_mul] at this
    exact this
  have := hmin.hasDerivAt_eq_zero hd
  linarith

/-- O&R p. 39, after (1.27): Shephard's lemma and the budget identity give the Hicksian demand
for date-1 consumption, `C₁ᴴ(R, U) = E(R, U) − R E_R(R, U)`. -/
theorem C1H_eq_E_sub (s : ExpenditureSystem) {R U e : ℝ} (hR : 0 < R) (hU : U ∈ s.Uset)
    (hE : HasDerivAt (fun R' => s.E R' U) e R) : s.C1H R U = s.E R U - R * e := by
  rw [s.shephard hR hU hE, s.cost_eq R U hR hU]
  ring

/-- O&R fn. 18, p. 39: differentiating `C₁ᴴ + R C₂ᴴ = E` in `R` at fixed utility. If the Hicksian
demands have `R`-derivatives `a`, `b`, then `E` is differentiable in `R` with derivative
`a + R b + C₂ᴴ`. -/
theorem hasDerivAt_E_of_hicksian (s : ExpenditureSystem) {R U a b : ℝ} (hR : 0 < R)
    (hU : U ∈ s.Uset) (ha : HasDerivAt (fun R' => s.C1H R' U) a R)
    (hb : HasDerivAt (fun R' => s.C2H R' U) b R) :
    HasDerivAt (fun R' => s.E R' U) (a + R * b + s.C2H R U) R := by
  have h := ha.add ((hasDerivAt_id R).mul hb)
  have hev : (fun R' => s.E R' U) =ᶠ[𝓝 R] fun R' => s.C1H R' U + id R' * s.C2H R' U := by
    filter_upwards [Ioi_mem_nhds hR] with R' hR'
    exact s.cost_eq R' U hR' hU
  refine (h.congr_of_eventuallyEq hev).congr_deriv ?_
  simp only [id]
  ring

/-- O&R fn. 18, p. 39: along a fixed indifference curve `∂C₁ᴴ/∂R + R ∂C₂ᴴ/∂R = 0`, i.e. the
slope `(∂C₁ᴴ/∂R)/(∂C₂ᴴ/∂R)` equals `−R`, minus the marginal rate of substitution. -/
theorem hicksian_tangency (s : ExpenditureSystem) {R U a b : ℝ} (hR : 0 < R)
    (hU : U ∈ s.Uset) (ha : HasDerivAt (fun R' => s.C1H R' U) a R)
    (hb : HasDerivAt (fun R' => s.C2H R' U) b R) : a + R * b = 0 := by
  have := s.shephard hR hU (s.hasDerivAt_E_of_hicksian hR hU ha hb)
  linarith

/-- O&R (1.28), p. 40, the income-cum-wealth effect of an interest-rate change. Suppose the
utility level `Upath R'` of the maximising consumer satisfies `E(R', U(R')) = Y₁ + R' Y₂` near
`R`, `E` is (jointly) differentiable at `(R, U(R))` with partials `E_R`, `E_U`, and `U` is
differentiable at `R`. Then `E_U · dU/dR = Y₂ − C₂ᴴ(R, U)`. -/
theorem welfare_effect (s : ExpenditureSystem) {Upath : ℝ → ℝ} {R eR eU u' Y1 Y2 : ℝ}
    (hR : 0 < R) (hU : Upath R ∈ s.Uset)
    (hE : HasFDerivAt (fun p : ℝ × ℝ => s.E p.1 p.2)
      (eR • ContinuousLinearMap.fst ℝ ℝ ℝ + eU • ContinuousLinearMap.snd ℝ ℝ ℝ) (R, Upath R))
    (hUd : HasDerivAt Upath u' R)
    (hbud : ∀ᶠ R' in 𝓝 R, s.E R' (Upath R') = Y1 + R' * Y2) :
    eU * u' = Y2 - s.C2H R (Upath R) := by
  have h1 := hasDerivAt_along_path hE hUd
  have h2 : HasDerivAt (fun R' => Y1 + R' * Y2) (eR + eU * u') R :=
    h1.congr_of_eventuallyEq (hbud.mono fun R' h => h.symm)
  have h3 : HasDerivAt (fun R' => Y1 + R' * Y2) Y2 R := by
    simpa using ((hasDerivAt_id R).mul_const Y2).const_add Y1
  have h4 := h2.unique h3
  have hpart : HasDerivAt (fun R' => s.E R' (Upath R)) eR R := by
    simpa using hasDerivAt_along_path (g := fun _ => Upath R) hE (hasDerivAt_const R _)
  have h5 := s.shephard hR hU hpart
  rw [← h5]
  linarith

/-- O&R p. 40, after (1.28): when the marginal expenditure cost of utility is positive
(`E_U > 0`), a rise in `R` (a fall in `r`) raises lifetime utility exactly when `Y₂ > C₂`, i.e.
when the country repays on date 2 debts incurred through a date-1 current-account deficit. -/
theorem welfare_rises_iff (s : ExpenditureSystem) {Upath : ℝ → ℝ} {R eR eU u' Y1 Y2 : ℝ}
    (hR : 0 < R) (hU : Upath R ∈ s.Uset)
    (hE : HasFDerivAt (fun p : ℝ × ℝ => s.E p.1 p.2)
      (eR • ContinuousLinearMap.fst ℝ ℝ ℝ + eU • ContinuousLinearMap.snd ℝ ℝ ℝ) (R, Upath R))
    (hUd : HasDerivAt Upath u' R)
    (hbud : ∀ᶠ R' in 𝓝 R, s.E R' (Upath R') = Y1 + R' * Y2) (heU : 0 < eU) :
    0 < u' ↔ s.C2H R (Upath R) < Y2 := by
  have h := s.welfare_effect hR hU hE hUd hbud
  constructor
  · intro hu
    have : 0 < eU * u' := mul_pos heU hu
    linarith
  · intro hc
    have : 0 < eU * u' := by linarith
    exact pos_of_mul_pos_right this heU.le

/-- The Slutsky decomposition, O&R (1.30), p. 41. Let `C1M R W` be Marshallian date-1 demand,
(jointly) differentiable at `(R, E(R,U))` with partials `∂C₁/∂R`, `∂C₁/∂W`; suppose the duality
identity (1.29) `C₁(R', E(R', U)) = C₁ᴴ(R', U)` holds for `R' > 0`, and `E`, `C₁ᴴ` are
differentiable in `R`. Then `∂C₁/∂R = ∂C₁ᴴ/∂R − (∂C₁/∂W) C₂ᴴ`. -/
theorem slutsky (s : ExpenditureSystem) {C1M : ℝ → ℝ → ℝ} {R U e h mR mW : ℝ}
    (hR : 0 < R) (hU : U ∈ s.Uset)
    (hM : HasFDerivAt (fun p : ℝ × ℝ => C1M p.1 p.2)
      (mR • ContinuousLinearMap.fst ℝ ℝ ℝ + mW • ContinuousLinearMap.snd ℝ ℝ ℝ) (R, s.E R U))
    (hE : HasDerivAt (fun R' => s.E R' U) e R)
    (hH : HasDerivAt (fun R' => s.C1H R' U) h R)
    (hdual : ∀ R', 0 < R' → C1M R' (s.E R' U) = s.C1H R' U) :
    mR = h - mW * s.C2H R U := by
  have h1 := hasDerivAt_along_path (g := fun R' => s.E R' U) hM hE
  have h2 : HasDerivAt (fun R' => s.C1H R' U) (mR + mW * e) R := by
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hR] with R' hR'
    exact (hdual R' hR').symm
  have h3 := h2.unique hH
  rw [← s.shephard hR hU hE]
  linarith

/-- The total effect of the interest rate, O&R (1.31), p. 41: with wealth `W₁ = Y₁ + R Y₂`
and `U` the attained utility (`E(R, U) = Y₁ + R Y₂`), under the hypotheses of `slutsky`,
`dC₁/dR = ∂C₁ᴴ/∂R + (∂C₁/∂W)(Y₂ − C₂)`: substitution effect plus the consumption effect of the
wealth-minus-income (terms-of-trade) change. -/
theorem total_effect (s : ExpenditureSystem) {C1M : ℝ → ℝ → ℝ} {R U e h mR mW Y1 Y2 : ℝ}
    (hR : 0 < R) (hU : U ∈ s.Uset) (hW : s.E R U = Y1 + R * Y2)
    (hM : HasFDerivAt (fun p : ℝ × ℝ => C1M p.1 p.2)
      (mR • ContinuousLinearMap.fst ℝ ℝ ℝ + mW • ContinuousLinearMap.snd ℝ ℝ ℝ) (R, s.E R U))
    (hE : HasDerivAt (fun R' => s.E R' U) e R)
    (hH : HasDerivAt (fun R' => s.C1H R' U) h R)
    (hdual : ∀ R', 0 < R' → C1M R' (s.E R' U) = s.C1H R' U) :
    HasDerivAt (fun R' => C1M R' (Y1 + R' * Y2)) (h + mW * (Y2 - s.C2H R U)) R := by
  have hsl := s.slutsky hR hU hM hE hH hdual
  have hg : HasDerivAt (fun R' => Y1 + R' * Y2) Y2 R := by
    simpa using ((hasDerivAt_id R).mul_const Y2).const_add Y1
  rw [hW] at hM
  have h1 := hasDerivAt_along_path (g := fun R' => Y1 + R' * Y2) hM hg
  convert h1 using 1
  rw [hsl]
  ring

end ExpenditureSystem

/-! ## The isoelastic intertemporally additive case (O&R §1.3.4.4, p. 42) -/

namespace Iso

/-- Isoelastic period utility O&R (1.22), p. 28, `u(C) = C^{1−1/σ}/(1 − 1/σ)` (for `σ ≠ 1`; the
Hicksian formula of p. 42 has exponent `σ/(σ−1)`, so the log case is excluded there). -/
noncomputable def u (σ C : ℝ) : ℝ := C ^ (1 - 1 / σ) / (1 - 1 / σ)

/-- The common denominator of O&R p. 42 (and of (1.26), p. 30), `1 + β^σ R^{1−σ}`. -/
noncomputable def D (σ β R : ℝ) : ℝ := 1 + β ^ σ * R ^ (1 - σ)

/-- Hicksian date-1 demand, O&R p. 42: `C₁ᴴ(R, U) = [(1 − 1/σ) U / (1 + β^σ R^{1−σ})]^{σ/(σ−1)}`. -/
noncomputable def C1H (σ β R U : ℝ) : ℝ := ((1 - 1 / σ) * U / D σ β R) ^ (σ / (σ - 1))

/-- Hicksian date-2 demand, from the Euler equation (1.25), p. 30, in terms of `R = 1/(1+r)`:
`C₂ᴴ = β^σ R^{−σ} C₁ᴴ`. -/
noncomputable def C2H (σ β R U : ℝ) : ℝ := β ^ σ * R ^ (-σ) * C1H σ β R U

/-- The isoelastic expenditure function, O&R §1.3.4.1, p. 39, in closed form:
`E(R, U) = (1 + β^σ R^{1−σ}) C₁ᴴ(R, U)`. -/
noncomputable def E (σ β R U : ℝ) : ℝ := D σ β R * C1H σ β R U

/-- Marshallian date-1 demand, O&R p. 40: `C₁(R, W₁) = W₁ / (1 + β^σ R^{1−σ})`. -/
noncomputable def C1M (σ β R W : ℝ) : ℝ := W / D σ β R

/-- Marshallian date-2 demand, from (1.25), p. 30: `C₂(R, W₁) = β^σ R^{−σ} C₁(R, W₁)`. -/
noncomputable def C2M (σ β R W : ℝ) : ℝ := β ^ σ * R ^ (-σ) * C1M σ β R W

/-- The denominator `1 + β^σ R^{1−σ}` of O&R p. 42 is positive. -/
theorem D_pos (σ : ℝ) {β R : ℝ} (hβ : 0 < β) (hR : 0 < R) : 0 < D σ β R := by
  unfold D
  have := Real.rpow_pos_of_pos hβ σ
  have := Real.rpow_pos_of_pos hR (1 - σ)
  positivity

/-- `R · R^{−σ} = R^{1−σ}`, used throughout O&R p. 42. -/
theorem mul_rpow_neg {R : ℝ} (σ : ℝ) (hR : 0 < R) : R * R ^ (-σ) = R ^ (1 - σ) := by
  rw [sub_eq_add_neg, Real.rpow_add hR, Real.rpow_one]

/-- Bernoulli-type tangent inequality behind strict concavity of the isoelastic utility:
for `p < 1`, `p ≠ 0` and `t > 0`, `t^p / p ≤ 1/p + (t − 1)`. -/
theorem rpow_div_le_tangent {p t : ℝ} (hp1 : p < 1) (hp0 : p ≠ 0) (ht : 0 < t) :
    t ^ p / p ≤ 1 / p + (t - 1) := by
  rcases lt_or_gt_of_ne hp0 with hneg | hpos
  · -- `p < 0`: weighted AM–GM with weights `1/(1−p)`, `−p/(1−p)` on `t^p` and `t`.
    have hq : 0 < 1 - p := by linarith
    have hw1 : 0 ≤ 1 / (1 - p) := by positivity
    have hw2 : 0 ≤ -p / (1 - p) := div_nonneg (by linarith) hq.le
    have hamgm := Real.geom_mean_le_arith_mean2_weighted hw1 hw2
      (Real.rpow_pos_of_pos ht p).le ht.le (by field_simp; ring)
    rw [← Real.rpow_mul ht.le, ← Real.rpow_add ht,
      show p * (1 / (1 - p)) + -p / (1 - p) = 0 by field_simp; ring, Real.rpow_zero] at hamgm
    have h2 : 1 - p ≤ t ^ p - p * t := by
      have := mul_le_mul_of_nonneg_left hamgm hq.le
      rw [mul_one] at this
      convert this using 1
      field_simp
      ring
    rw [div_le_iff_of_neg hneg]
    have : (1 / p + (t - 1)) * p = 1 + p * t - p := by field_simp; ring
    rw [this]
    linarith
  · have h := rpow_one_add_le_one_add_mul_self (show (-1 : ℝ) ≤ t - 1 by linarith)
      hpos.le hp1.le
    rw [add_sub_cancel] at h
    rw [div_le_iff₀ hpos]
    have : (1 / p + (t - 1)) * p = 1 + p * (t - 1) := by field_simp
    rw [this]
    exact h

/-- Strict concavity of isoelastic utility in tangent form, for `σ > 0`, `σ ≠ 1`: for
`x, y > 0`, `u(x) ≤ u(y) + u'(y)(x − y)` with `u'(y) = y^{−1/σ}` (O&R p. 30). -/
theorem u_le_tangent {σ x y : ℝ} (hσ : 0 < σ) (hσ1 : σ ≠ 1) (hx : 0 < x) (hy : 0 < y) :
    u σ x ≤ u σ y + y ^ (-1 / σ) * (x - y) := by
  set p := 1 - 1 / σ with hpdef
  have hp1 : p < 1 := by
    have : 0 < 1 / σ := by positivity
    linarith
  have hp0 : p ≠ 0 := by
    intro h
    have h1 : (1 : ℝ) / σ = 1 := by linarith
    exact hσ1 ((div_eq_one_iff_eq hσ.ne').mp h1).symm
  have ht : 0 < x / y := div_pos hx hy
  have key := rpow_div_le_tangent hp1 hp0 ht
  have hxy : x = x / y * y := by field_simp
  have hyp : 0 < y ^ p := Real.rpow_pos_of_pos hy p
  have hexp : y ^ (-1 / σ) = y ^ p / y := by
    rw [← Real.rpow_sub_one hy.ne']
    congr 1
    rw [hpdef]
    ring
  unfold u
  rw [← hpdef, hexp]
  conv_lhs => rw [hxy, Real.mul_rpow ht.le hy.le]
  have := mul_le_mul_of_nonneg_left key hyp.le
  calc (x / y) ^ p * y ^ p / p = y ^ p * ((x / y) ^ p / p) := by ring
    _ ≤ y ^ p * (1 / p + (x / y - 1)) := this
    _ = y ^ p / p + y ^ p / y * (x - y) := by field_simp

/-- The Hicksian demands are positive. -/
theorem C1H_pos {σ β R U : ℝ} (hβ : 0 < β) (hR : 0 < R) (hU : 0 < (1 - 1 / σ) * U) :
    0 < C1H σ β R U :=
  Real.rpow_pos_of_pos (div_pos hU (D_pos σ hβ hR)) _

/-- The date-2 Hicksian demand is positive. -/
theorem C2H_pos {σ β R U : ℝ} (hβ : 0 < β) (hR : 0 < R) (hU : 0 < (1 - 1 / σ) * U) :
    0 < C2H σ β R U := by
  unfold C2H
  have := Real.rpow_pos_of_pos hβ σ
  have := Real.rpow_pos_of_pos hR (-σ)
  have := C1H_pos (σ := σ) hβ hR hU
  positivity

/-- O&R p. 42: `(C₁ᴴ)^{1−1/σ} = (1 − 1/σ) U / (1 + β^σ R^{1−σ})`. -/
theorem C1H_rpow {σ β R U : ℝ} (hσ : 0 < σ) (hσ1 : σ ≠ 1) (hβ : 0 < β) (hR : 0 < R)
    (hU : 0 < (1 - 1 / σ) * U) :
    C1H σ β R U ^ (1 - 1 / σ) = (1 - 1 / σ) * U / D σ β R := by
  unfold C1H
  have hs : σ - 1 ≠ 0 := sub_ne_zero.mpr hσ1
  rw [← Real.rpow_mul (div_pos hU (D_pos σ hβ hR)).le,
    show σ / (σ - 1) * (1 - 1 / σ) = 1 by field_simp, Real.rpow_one]

/-- O&R p. 42: the Hicksian bundle attains exactly the utility level `U`,
`u(C₁ᴴ) + β u(C₂ᴴ) = U` (for `U` of the sign of `1 − 1/σ`, as utilities of positive
consumption are). -/
theorem utility_hicksian {σ β R U : ℝ} (hσ : 0 < σ) (hσ1 : σ ≠ 1) (hβ : 0 < β) (hR : 0 < R)
    (hU : 0 < (1 - 1 / σ) * U) :
    u σ (C1H σ β R U) + β * u σ (C2H σ β R U) = U := by
  have hp0 : 1 - 1 / σ ≠ 0 := by
    intro h
    apply hσ1
    field_simp at h
    linarith
  have hB := Real.rpow_pos_of_pos hβ σ
  have hRs := Real.rpow_pos_of_pos hR (-σ)
  have hC := C1H_pos (σ := σ) hβ hR hU
  have hD := D_pos σ hβ hR
  unfold u C2H
  rw [Real.mul_rpow (by positivity) hC.le, Real.mul_rpow hB.le hRs.le,
    ← Real.rpow_mul hβ.le, ← Real.rpow_mul hR.le, C1H_rpow hσ hσ1 hβ hR hU,
    show σ * (1 - 1 / σ) = σ - 1 by field_simp,
    (show -σ * (1 - 1 / σ) = 1 - σ by field_simp; ring), Real.rpow_sub_one hβ.ne']
  unfold D at hD ⊢
  field_simp

/-- Euler condition at the Hicksian bundle, O&R (1.25), p. 30: `β u'(C₂ᴴ) = R u'(C₁ᴴ)`. -/
theorem euler_hicksian {σ β R U : ℝ} (hσ : 0 < σ) (hβ : 0 < β) (hR : 0 < R)
    (hU : 0 < (1 - 1 / σ) * U) :
    β * C2H σ β R U ^ (-1 / σ) = R * C1H σ β R U ^ (-1 / σ) := by
  have hB := Real.rpow_pos_of_pos hβ σ
  have hRs := Real.rpow_pos_of_pos hR (-σ)
  have hC := C1H_pos (σ := σ) hβ hR hU
  unfold C2H
  rw [Real.mul_rpow (by positivity) hC.le, Real.mul_rpow hB.le hRs.le,
    ← Real.rpow_mul hβ.le, ← Real.rpow_mul hR.le,
    show σ * (-1 / σ) = -1 by field_simp, show -σ * (-1 / σ) = 1 by field_simp,
    Real.rpow_neg_one, Real.rpow_one]
  field_simp

/-- The budget identity for the Hicksian bundle, O&R fn. 18, p. 39:
`C₁ᴴ + R C₂ᴴ = E(R, U)`. -/
theorem cost_hicksian (σ β R U : ℝ) (hR : 0 < R) :
    E σ β R U = C1H σ β R U + R * C2H σ β R U := by
  unfold E C2H D
  rw [← mul_rpow_neg σ hR]
  ring

/-- Cost minimisation, O&R §1.3.4.1, p. 39: every positive bundle giving lifetime utility at
least `U` costs at least `E(R, U)`. (Tangent inequality for the concave `u` plus the Euler
condition at the Hicksian bundle.) -/
theorem le_cost {σ β R U C1 C2 : ℝ} (hσ : 0 < σ) (hσ1 : σ ≠ 1) (hβ : 0 < β) (hR : 0 < R)
    (hU : 0 < (1 - 1 / σ) * U) (hC1 : 0 < C1) (hC2 : 0 < C2)
    (hUle : U ≤ u σ C1 + β * u σ C2) : E σ β R U ≤ C1 + R * C2 := by
  have ha := C1H_pos (σ := σ) hβ hR hU
  have hb := C2H_pos (σ := σ) hβ hR hU
  have t1 := u_le_tangent hσ hσ1 hC1 ha
  have t2 := u_le_tangent hσ hσ1 hC2 hb
  have hut := utility_hicksian hσ hσ1 hβ hR hU
  have heu := euler_hicksian hσ hβ hR hU
  have hm : 0 < C1H σ β R U ^ (-1 / σ) := Real.rpow_pos_of_pos ha _
  rw [cost_hicksian σ β R U hR]
  have h3 : 0 ≤ C1H σ β R U ^ (-1 / σ) *
      ((C1 + R * C2) - (C1H σ β R U + R * C2H σ β R U)) := by
    have := mul_le_mul_of_nonneg_left t2 hβ.le
    nlinarith
  linarith [(mul_nonneg_iff_of_pos_left hm).mp h3]

/-- The isoelastic additive consumer as an `ExpenditureSystem`, O&R §1.3.4.4, p. 42:
`V(C₁, C₂) = u(C₁) + β u(C₂)`, attainable levels `U` with `(1 − 1/σ) U > 0`, and the closed
forms above. -/
noncomputable def system {σ β : ℝ} (hσ : 0 < σ) (hσ1 : σ ≠ 1) (hβ : 0 < β) :
    ExpenditureSystem where
  V C1 C2 := u σ C1 + β * u σ C2
  Uset := {U | 0 < (1 - 1 / σ) * U}
  E := E σ β
  C1H := C1H σ β
  C2H := C2H σ β
  le_cost _ _ _ _ hR hU hC1 hC2 hle := le_cost hσ hσ1 hβ hR hU hC1 hC2 hle
  C1H_pos _ _ hR hU := C1H_pos hβ hR hU
  C2H_pos _ _ hR hU := C2H_pos hβ hR hU
  attains _ _ hR hU := (utility_hicksian hσ hσ1 hβ hR hU).ge
  cost_eq R U hR _ := cost_hicksian σ β R U hR

/-- The price derivative of the denominator of O&R p. 42:
`d/dR (1 + β^σ R^{1−σ}) = β^σ (1 − σ) R^{−σ}`. -/
theorem hasDerivAt_D (σ β : ℝ) {R : ℝ} (hR : 0 < R) :
    HasDerivAt (fun R' => D σ β R') (β ^ σ * ((1 - σ) * R ^ (-σ))) R := by
  have h := ((Real.hasDerivAt_rpow_const (p := 1 - σ) (Or.inl hR.ne')).const_mul
    (β ^ σ)).const_add 1
  rw [show (1 : ℝ) - σ - 1 = -σ by ring] at h
  exact h

/-- The Hicksian substitution effect, O&R p. 42 (first term of the decomposition):
`∂C₁ᴴ/∂R = σ β^σ R^{−σ} C₁ᴴ / (1 + β^σ R^{1−σ})`. -/
theorem hasDerivAt_C1H {σ β R U : ℝ} (hσ : 0 < σ) (hσ1 : σ ≠ 1) (hβ : 0 < β) (hR : 0 < R)
    (hU : 0 < (1 - 1 / σ) * U) :
    HasDerivAt (fun R' => C1H σ β R' U)
      (σ * β ^ σ * R ^ (-σ) * C1H σ β R U / D σ β R) R := by
  have hD := D_pos σ hβ hR
  have hs : σ - 1 ≠ 0 := sub_ne_zero.mpr hσ1
  have hk : 0 < (1 - 1 / σ) * U / D σ β R := div_pos hU hD
  have h := ((hasDerivAt_const R ((1 - 1 / σ) * U)).div (hasDerivAt_D σ β hR)
    hD.ne').rpow_const (p := σ / (σ - 1)) (Or.inl hk.ne')
  convert h using 1
  · rfl
  unfold C1H
  simp only [Pi.div_apply]
  rw [Real.rpow_sub_one hk.ne']
  have hU0 : U ≠ 0 := by
    rintro rfl
    simp at hU
  have hσ0 : σ ≠ 0 := hσ.ne'
  generalize ((1 - 1 / σ) * U / D σ β R) ^ (σ / (σ - 1)) = K
  field_simp
  ring

/-- Shephard's lemma (1.27), p. 39, verified in closed form for isoelastic utility:
`∂E/∂R = C₂ᴴ = β^σ R^{−σ} C₁ᴴ`. -/
theorem shephard_iso {σ β R U : ℝ} (hσ : 0 < σ) (hσ1 : σ ≠ 1) (hβ : 0 < β) (hR : 0 < R)
    (hU : 0 < (1 - 1 / σ) * U) :
    HasDerivAt (fun R' => E σ β R' U) (C2H σ β R U) R := by
  have hD := D_pos σ hβ hR
  have h := (hasDerivAt_D σ β hR).mul (hasDerivAt_C1H hσ hσ1 hβ hR hU)
  convert h using 1
  · rfl
  unfold C2H
  field_simp
  ring

/-- The abstract Shephard lemma applied to the isoelastic `system` returns the closed form:
`C₁ᴴ = E − R E_R` holds for isoelastic utility (O&R p. 39). -/
theorem C1H_eq_E_sub_iso {σ β R U : ℝ} (hσ : 0 < σ) (hσ1 : σ ≠ 1) (hβ : 0 < β) (hR : 0 < R)
    (hU : 0 < (1 - 1 / σ) * U) :
    C1H σ β R U = E σ β R U - R * C2H σ β R U :=
  (system hσ hσ1 hβ).C1H_eq_E_sub (U := U) hR hU (shephard_iso hσ hσ1 hβ hR hU)

/-- The duality identity O&R (1.29), p. 41, in closed form: Marshallian demand at wealth
`E(R, U)` is Hicksian demand at utility `U`, `C₁(R, E(R, U)) = C₁ᴴ(R, U)`. -/
theorem duality_identity_iso (σ : ℝ) {β R U : ℝ} (hβ : 0 < β) (hR : 0 < R) :
    C1M σ β R (E σ β R U) = C1H σ β R U := by
  have hD := D_pos σ hβ hR
  unfold C1M E
  field_simp

/-- The Marshallian demands of O&R p. 40 exhaust wealth, `C₁ + R C₂ = W₁`. -/
theorem marshallian_budget (σ : ℝ) {β R W : ℝ} (hβ : 0 < β) (hR : 0 < R) :
    C1M σ β R W + R * C2M σ β R W = W := by
  have hD := D_pos σ hβ hR
  unfold C2M C1M
  have e : R * (β ^ σ * R ^ (-σ) * (W / D σ β R)) = β ^ σ * (R * R ^ (-σ)) * W / D σ β R := by
    ring
  rw [e, mul_rpow_neg σ hR]
  unfold D at hD ⊢
  field_simp

/-- The Marshallian demand of O&R p. 40 is the consumption function (1.26), p. 30, once
`R = 1/(1+r)`: `W / (1 + β^σ R^{1−σ}) = W / (1 + (1+r)^{σ−1} β^σ)`. -/
theorem C1M_eq_eq26 (σ β W : ℝ) {r : ℝ} (hr : 0 < 1 + r) :
    C1M σ β (1 / (1 + r)) W = W / (1 + (1 + r) ^ (σ - 1) * β ^ σ) := by
  unfold C1M D
  rw [one_div, Real.inv_rpow hr.le, ← Real.rpow_neg hr.le, neg_sub, mul_comm]

/-- Price partial of Marshallian demand at fixed wealth, O&R p. 41:
`∂C₁/∂R = (σ − 1) β^σ R^{−σ} C₁ / (1 + β^σ R^{1−σ})`. -/
theorem hasDerivAt_C1M_R (σ : ℝ) {β R W : ℝ} (hβ : 0 < β) (hR : 0 < R) :
    HasDerivAt (fun R' => C1M σ β R' W)
      ((σ - 1) * β ^ σ * R ^ (-σ) * C1M σ β R W / D σ β R) R := by
  have hD := D_pos σ hβ hR
  have h := (hasDerivAt_const R W).div (hasDerivAt_D σ β hR) hD.ne'
  convert h using 1
  · rfl
  unfold C1M
  field_simp
  ring

/-- Wealth partial of Marshallian demand, O&R p. 41: `∂C₁/∂W₁ = 1 / (1 + β^σ R^{1−σ})`. -/
theorem hasDerivAt_C1M_W (σ : ℝ) {β R W : ℝ} :
    HasDerivAt (fun W' => C1M σ β R W') (1 / D σ β R) W := by
  have h := (hasDerivAt_id W).div_const (D σ β R)
  convert h using 1
  rfl

/-- The Slutsky equation O&R (1.30), p. 41, verified in closed form: at wealth `W₁ = E(R, U)`,
`∂C₁/∂R = ∂C₁ᴴ/∂R − (∂C₁/∂W₁) C₂ᴴ`, with the partials of `hasDerivAt_C1H` and
`hasDerivAt_C1M_W`. -/
theorem slutsky_iso {σ β R U : ℝ} (hβ : 0 < β) (hR : 0 < R) :
    HasDerivAt (fun R' => C1M σ β R' (E σ β R U))
      (σ * β ^ σ * R ^ (-σ) * C1H σ β R U / D σ β R - 1 / D σ β R * C2H σ β R U) R := by
  have h := hasDerivAt_C1M_R σ (W := E σ β R U) hβ hR
  rw [duality_identity_iso σ hβ hR] at h
  convert h using 1
  unfold C2H
  ring

/-- The decomposition (1.31) in the isoelastic case, O&R p. 42 (first display): with
`W₁ = Y₁ + R Y₂`, `C₁ = C₁(R, W₁)` and `C₂ = C₂(R, W₁)`,
`dC₁/dR = σ β^σ R^{−σ} C₁ / (1 + β^σ R^{1−σ}) + (Y₂ − C₂) / (1 + β^σ R^{1−σ})`
(substitution effect plus wealth-minus-income effect). -/
theorem hasDerivAt_C1_total {σ β R Y1 Y2 : ℝ} (hβ : 0 < β) (hR : 0 < R) :
    HasDerivAt (fun R' => C1M σ β R' (Y1 + R' * Y2))
      (σ * β ^ σ * R ^ (-σ) * C1M σ β R (Y1 + R * Y2) / D σ β R +
        (Y2 - C2M σ β R (Y1 + R * Y2)) / D σ β R) R := by
  have hD := D_pos σ hβ hR
  have h := (((hasDerivAt_id R).mul_const Y2).const_add Y1).div (hasDerivAt_D σ β hR) hD.ne'
  convert h using 1
  · rfl
  unfold C2M C1M
  simp only [id]
  field_simp
  ring

/-- O&R p. 42 (second display), after applying the Euler equation (1.25):
`dC₁/dR = (σ − 1) β^σ R^{−σ} C₁ / (1 + β^σ R^{1−σ}) + Y₂ / (1 + β^σ R^{1−σ})`, so the sign of
`σ − 1` decides whether substitution or income effect dominates. -/
theorem hasDerivAt_C1_total_euler {σ β R Y1 Y2 : ℝ} (hβ : 0 < β) (hR : 0 < R) :
    HasDerivAt (fun R' => C1M σ β R' (Y1 + R' * Y2))
      ((σ - 1) * β ^ σ * R ^ (-σ) * C1M σ β R (Y1 + R * Y2) / D σ β R +
        Y2 / D σ β R) R := by
  refine (hasDerivAt_C1_total hβ hR).congr_deriv ?_
  unfold C2M
  ring

/-- O&R p. 42: the `R`-form of the interest-rate effect is equivalent to (1.24), p. 29. Writing
date-1 consumption as a function of `r` through `R = 1/(1+r)` (so `dR/dr = −R²`), with
`C₂ = (1+r)^σ β^σ C₁` from (1.25), the derivative is
`dC₁/dr = [(Y₁ − C₁) − σ C₂/(1+r)] / [1 + r + C₂/C₁]` whenever lifetime wealth is positive. -/
theorem hasDerivAt_C1_r_eq24 {σ β Y1 Y2 r C1 C2 : ℝ} (hβ : 0 < β) (hr : 0 < 1 + r)
    (hW : 0 < Y1 + Y2 / (1 + r))
    (hC1 : C1 = C1M σ β (1 / (1 + r)) (Y1 + 1 / (1 + r) * Y2))
    (hC2 : C2 = (1 + r) ^ σ * β ^ σ * C1) :
    HasDerivAt (fun r' => C1M σ β (1 / (1 + r')) (Y1 + 1 / (1 + r') * Y2))
      (((Y1 - C1) - σ * C2 / (1 + r)) / (1 + r + C2 / C1)) r := by
  have hR : 0 < 1 / (1 + r) := by positivity
  have hF := hasDerivAt_C1_total_euler (σ := σ) (Y1 := Y1) (Y2 := Y2) hβ hR
  have hg : HasDerivAt (fun r' => 1 / (1 + r')) (-1 / (1 + r) ^ 2) r := by
    have := (hasDerivAt_const r (1 : ℝ)).div ((hasDerivAt_id r).const_add 1) hr.ne'
    convert this using 1
    · rfl
    simp only [id]
    ring
  have h := hF.comp r hg
  have hA : (1 / (1 + r)) ^ (-σ) = (1 + r) ^ σ := by
    rw [one_div, Real.inv_rpow hr.le, Real.rpow_neg hr.le, inv_inv]
  have hB : (1 / (1 + r)) ^ (1 - σ) = (1 + r) ^ σ / (1 + r) := by
    rw [one_div, Real.inv_rpow hr.le, ← Real.rpow_neg hr.le, neg_sub,
      Real.rpow_sub_one hr.ne']
  have hP := Real.rpow_pos_of_pos hr σ
  have hBs := Real.rpow_pos_of_pos hβ σ
  have hDp : 0 < 1 + β ^ σ * ((1 + r) ^ σ / (1 + r)) := by positivity
  have hC1pos : 0 < C1 := by
    rw [hC1]
    unfold C1M D
    rw [hB]
    have : Y1 + 1 / (1 + r) * Y2 = Y1 + Y2 / (1 + r) := by ring
    rw [this]
    positivity
  have hratio : C2 / C1 = (1 + r) ^ σ * β ^ σ := by
    rw [hC2]
    field_simp
  convert h using 1
  · rfl
  rw [hratio, hC2]
  rw [hC1]
  unfold C1M D
  rw [hA, hB]
  field_simp
  ring

/-- Joint (Fréchet) differentiability of isoelastic Marshallian demand `C₁(R, W₁) = W₁/D(R)`,
with partials `∂C₁/∂R = (σ − 1) β^σ R^{−σ} C₁/D` and `∂C₁/∂W₁ = 1/D` (O&R p. 41). -/
theorem hasFDerivAt_C1M (σ : ℝ) {β R W : ℝ} (hβ : 0 < β) (hR : 0 < R) :
    HasFDerivAt (fun p : ℝ × ℝ => C1M σ β p.1 p.2)
      (((σ - 1) * β ^ σ * R ^ (-σ) * C1M σ β R W / D σ β R) • ContinuousLinearMap.fst ℝ ℝ ℝ +
        (1 / D σ β R) • ContinuousLinearMap.snd ℝ ℝ ℝ) (R, W) := by
  have hD := D_pos σ hβ hR
  have hinv := ((hasDerivAt_D σ β hR).inv hD.ne').hasFDerivAt.comp (R, W)
    (hasFDerivAt_fst (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := (R, W)))
  have h := (hasFDerivAt_snd (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := (R, W))).mul hinv
  convert h using 1
  · funext q
    simp [C1M, div_eq_mul_inv]
  · ext
    · simp [C1M]
      field_simp
      ring
    · simp

/-- The abstract decomposition `ExpenditureSystem.total_effect` (O&R (1.31), p. 41) applied to the
isoelastic `system`: at the utility level `U` with `E(R, U) = Y₁ + R Y₂`,
`dC₁/dR = ∂C₁ᴴ/∂R + (∂C₁/∂W₁)(Y₂ − C₂ᴴ)`, with the closed-form partials of p. 42. -/
theorem total_effect_iso {σ β R U Y1 Y2 : ℝ} (hσ : 0 < σ) (hσ1 : σ ≠ 1) (hβ : 0 < β)
    (hR : 0 < R) (hU : 0 < (1 - 1 / σ) * U) (hW : E σ β R U = Y1 + R * Y2) :
    HasDerivAt (fun R' => C1M σ β R' (Y1 + R' * Y2))
      (σ * β ^ σ * R ^ (-σ) * C1H σ β R U / D σ β R +
        1 / D σ β R * (Y2 - C2H σ β R U)) R :=
  (system hσ hσ1 hβ).total_effect (U := U) hR hU hW (hasFDerivAt_C1M σ hβ hR)
    (shephard_iso hσ hσ1 hβ hR hU) (hasDerivAt_C1H hσ hσ1 hβ hR hU)
    (fun _ hR' => duality_identity_iso σ hβ hR')

end Iso

end ObstfeldRogoff.IntertemporalTrade.Duality

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

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

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# International labour movements

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*,
§1.5, pp. 45–51. A small country with no international borrowing or lending
(`K₁ = 0`, exogenous `Y₁`) but free trade in labour services at a given world
wage `w`. Output on date 2 is `F(K₂, L₂)` with constant returns (1.33); the
resident supplies `Lᴴ` inelastically, while employment `L₂` may differ.

Contents:
* constant-returns facts (1.34)–(1.36): Euler's theorem from homogeneity, and the
  intensive-form marginal products `F_K = f'(k)`, `F_L = f(k) − f'(k) k`;
* the first-order conditions (1.37)–(1.38), p. 48;
* the factor-price frontier, p. 48: `k'(w) = −1/(k f''(k)) > 0`, `r'(w) = −1/k(w) < 0`;
* the GNP and GDP lines and the autarky PPF, pp. 49–50, including the gains-from-trade
  inequality (GNP line weakly above the PPF, touching only at `B`);
* the pattern of labour trade, p. 50: `wᴬ > w` implies labour imports, `wᴬ < w` exports;
* comparative statics of the autarky wage, p. 50.

Throughout, the intensive production function `f` is strictly concave and twice
differentiable on `k > 0` (the book's implicit assumptions); the Inada condition of
footnote 23 is replaced by explicit interiority hypotheses.
-/

namespace ObstfeldRogoff.IntertemporalTrade.LabourMobility

open Set Filter Topology

/-! ## Constant returns to scale, O&R (1.33)–(1.36), pp. 46–47 -/

/-- Euler's theorem, O&R (1.34), p. 47 and footnote 21: if `F` is homogeneous of degree one,
`F(ξK, ξL) = ξ F(K, L)` for `ξ > 0`, and differentiable at `(K, L)` with partial derivatives
`F_K`, `F_L`, then `F(K, L) = F_K K + F_L L`. -/
theorem euler_of_homogeneous {F : ℝ → ℝ → ℝ} {K L FK FL : ℝ}
    (hhom : ∀ ξ : ℝ, 0 < ξ → F (ξ * K) (ξ * L) = ξ * F K L)
    (hF : HasFDerivAt (fun p : ℝ × ℝ => F p.1 p.2)
      (FK • ContinuousLinearMap.fst ℝ ℝ ℝ + FL • ContinuousLinearMap.snd ℝ ℝ ℝ) (K, L)) :
    F K L = FK * K + FL * L := by
  have hpath : HasDerivAt (fun ξ : ℝ => (ξ * K, ξ * L)) (K, L) 1 :=
    (hasDerivAt_mul_const K).prodMk (hasDerivAt_mul_const L)
  have hF' : HasFDerivAt (fun p : ℝ × ℝ => F p.1 p.2)
      (FK • ContinuousLinearMap.fst ℝ ℝ ℝ + FL • ContinuousLinearMap.snd ℝ ℝ ℝ)
      ((fun ξ : ℝ => (ξ * K, ξ * L)) 1) := by
    simpa using hF
  have h1 := hF'.comp_hasDerivAt (1 : ℝ) hpath
  have hev : (fun ξ : ℝ => F (ξ * K) (ξ * L)) =ᶠ[𝓝 1] fun ξ => ξ * F K L := by
    filter_upwards [lt_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with ξ hξ
    exact hhom ξ hξ
  have h2 : HasDerivAt (fun ξ : ℝ => F (ξ * K) (ξ * L)) (F K L) 1 :=
    (hasDerivAt_mul_const (F K L)).congr_of_eventuallyEq hev
  have h := h1.unique h2
  simp at h
  linarith

/-- The constant-returns production function written through its intensive form,
`F(K, L) = L f(K/L)`, O&R p. 47. -/
noncomputable def prod (f : ℝ → ℝ) (K L : ℝ) : ℝ := L * f (K / L)

/-- The intensive-form production function is homogeneous of degree one, O&R p. 46. -/
theorem prod_homogeneous (f : ℝ → ℝ) {K L ξ : ℝ} (hξ : 0 < ξ) :
    prod f (ξ * K) (ξ * L) = ξ * prod f K L := by
  unfold prod
  rw [mul_div_mul_left K L hξ.ne']
  ring

/-- Marginal product of capital, O&R (1.35), p. 47: `F_K(K, L) = f'(k)`, `k = K/L`. -/
theorem hasDerivAt_prod_capital {f : ℝ → ℝ} {f'k K L : ℝ} (hL : 0 < L)
    (hf : HasDerivAt f f'k (K / L)) :
    HasDerivAt (fun K => prod f K L) f'k K := by
  have hdiv : HasDerivAt (fun K : ℝ => K / L) (1 / L) K := (hasDerivAt_id K).div_const L
  have h := (hf.comp K hdiv).const_mul L
  exact h.congr_deriv (by field_simp)

/-- Marginal product of labour, O&R (1.36), p. 47: `F_L(K, L) = f(k) − f'(k) k`, `k = K/L`. -/
theorem hasDerivAt_prod_labour {f : ℝ → ℝ} {f'k K L : ℝ} (hL : 0 < L)
    (hf : HasDerivAt f f'k (K / L)) :
    HasDerivAt (fun L => prod f K L) (f (K / L) - f'k * (K / L)) L := by
  have hdiv : HasDerivAt (fun L : ℝ => K / L) (-(K / L ^ 2)) L := by
    have := (hasDerivAt_inv hL.ne').const_mul K
    convert this using 1
    · ext x
      ring
    · ring
  have h := (hasDerivAt_id L).mul (hf.comp L hdiv)
  exact h.congr_deriv (by simp only [id, Function.comp_apply]; field_simp; ring)

/-- Euler's theorem in intensive form, O&R (1.34)–(1.36), p. 47:
`F(K, L) = f'(k) K + (f(k) − f'(k) k) L` with `k = K/L`. -/
theorem prod_eq_euler (f : ℝ → ℝ) (f'k : ℝ) {K L : ℝ} (hL : 0 < L) :
    prod f K L = f'k * K + (f (K / L) - f'k * (K / L)) * L := by
  unfold prod
  field_simp
  ring

/-! ## The household problem and its first-order conditions, O&R p. 48 -/

/-- Date-2 consumption, O&R p. 48: `C₂ = L₂ f(K₂/L₂) − w (L₂ − Lᴴ) + K₂`. -/
noncomputable def consumption2 (f : ℝ → ℝ) (w LH K2 L2 : ℝ) : ℝ :=
  prod f K2 L2 - w * (L2 - LH) + K2

/-- Lifetime utility after substituting both constraints, O&R p. 48:
`u(Y₁ − K₂) + β u(L₂ f(K₂/L₂) − w (L₂ − Lᴴ) + K₂)`. -/
noncomputable def lifetimeUtility (u f : ℝ → ℝ) (β Y1 w LH K2 L2 : ℝ) : ℝ :=
  u (Y1 - K2) + β * u (consumption2 f w LH K2 L2)

/-- Derivative of lifetime utility with respect to `K₂`, O&R p. 48:
`−u'(C₁) + β u'(C₂)(1 + f'(k₂))`. -/
theorem hasDerivAt_lifetimeUtility_capital {u f : ℝ → ℝ} {u'1 u'2 f'k β Y1 w LH K2 L2 : ℝ}
    (hL : 0 < L2) (hu1 : HasDerivAt u u'1 (Y1 - K2))
    (hu2 : HasDerivAt u u'2 (consumption2 f w LH K2 L2))
    (hf : HasDerivAt f f'k (K2 / L2)) :
    HasDerivAt (fun K => lifetimeUtility u f β Y1 w LH K L2)
      (-u'1 + β * (u'2 * (1 + f'k))) K2 := by
  have hC1 : HasDerivAt (fun K : ℝ => Y1 - K) (-1) K2 := by
    simpa using (hasDerivAt_id K2).const_sub Y1
  have hC2 : HasDerivAt (fun K => consumption2 f w LH K L2) (f'k + 1) K2 :=
    ((hasDerivAt_prod_capital hL hf).sub_const (w * (L2 - LH))).add (hasDerivAt_id K2)
  have h := (hu1.comp (h := fun K : ℝ => Y1 - K) K2 hC1).add
    ((hu2.comp (h := fun K => consumption2 f w LH K L2) K2 hC2).const_mul β)
  exact h.congr_deriv (by ring)

/-- Derivative of lifetime utility with respect to `L₂`, O&R p. 48:
`β u'(C₂)(f(k₂) − f'(k₂) k₂ − w)`. -/
theorem hasDerivAt_lifetimeUtility_labour {u f : ℝ → ℝ} {u'2 f'k β Y1 w LH K2 L2 : ℝ}
    (hL : 0 < L2) (hu2 : HasDerivAt u u'2 (consumption2 f w LH K2 L2))
    (hf : HasDerivAt f f'k (K2 / L2)) :
    HasDerivAt (fun L => lifetimeUtility u f β Y1 w LH K2 L)
      (β * (u'2 * (f (K2 / L2) - f'k * (K2 / L2) - w))) L2 := by
  have hw : HasDerivAt (fun L : ℝ => w * (L - LH)) w L2 := by
    simpa using ((hasDerivAt_id L2).sub_const LH).const_mul w
  have hC2 : HasDerivAt (fun L => consumption2 f w LH K2 L)
      (f (K2 / L2) - f'k * (K2 / L2) - w) L2 :=
    ((hasDerivAt_prod_labour hL hf).sub hw).add_const K2
  have h := (hasDerivAt_const L2 (u (Y1 - K2))).add
    ((hu2.comp (h := fun L => consumption2 f w LH K2 L) L2 hC2).const_mul β)
  exact h.congr_deriv (by ring)

/-- The consumption Euler equation, O&R (1.37), p. 48: at an interior optimum in `K₂`,
`u'(C₁) = β [1 + f'(k₂)] u'(C₂)`. -/
theorem euler_equation {u f : ℝ → ℝ} {u'1 u'2 f'k β Y1 w LH K2 L2 : ℝ}
    (hL : 0 < L2) (hu1 : HasDerivAt u u'1 (Y1 - K2))
    (hu2 : HasDerivAt u u'2 (consumption2 f w LH K2 L2))
    (hf : HasDerivAt f f'k (K2 / L2))
    (hmax : IsLocalMax (fun K => lifetimeUtility u f β Y1 w LH K L2) K2) :
    u'1 = β * (1 + f'k) * u'2 := by
  have h := hmax.hasDerivAt_eq_zero (hasDerivAt_lifetimeUtility_capital hL hu1 hu2 hf)
  linarith

/-- Optimal hiring, O&R (1.38), p. 48: at an interior optimum in `L₂`, with `β u'(C₂) ≠ 0`,
the world wage equals the marginal product of labour, `w = f(k₂) − f'(k₂) k₂`. -/
theorem wage_eq_marginal_product {u f : ℝ → ℝ} {u'2 f'k β Y1 w LH K2 L2 : ℝ}
    (hL : 0 < L2) (hu2 : HasDerivAt u u'2 (consumption2 f w LH K2 L2))
    (hf : HasDerivAt f f'k (K2 / L2)) (hβu : β * u'2 ≠ 0)
    (hmax : IsLocalMax (fun L => lifetimeUtility u f β Y1 w LH K2 L) L2) :
    w = f (K2 / L2) - f'k * (K2 / L2) := by
  have h := hmax.hasDerivAt_eq_zero (hasDerivAt_lifetimeUtility_labour (β := β) (Y1 := Y1)
    hL hu2 hf)
  rw [← mul_assoc] at h
  have := (mul_eq_zero.mp h).resolve_left hβu
  linarith

/-! ## Technology: a strictly concave, twice-differentiable intensive form, O&R pp. 47–48 -/

/-- The intensive production function `f(k) = F(k, 1)` of O&R (1.35), p. 47, with its first
and second derivatives. The book's implicit assumptions are made explicit: `f` is continuous on
`k ≥ 0`, twice differentiable on `k > 0`, and strictly concave there (`f'' < 0`). -/
structure Technology where
  f : ℝ → ℝ
  f' : ℝ → ℝ
  f'' : ℝ → ℝ
  continuousOn_f : ContinuousOn f (Ici 0)
  hasDerivAt_f : ∀ k : ℝ, 0 < k → HasDerivAt f (f' k) k
  hasDerivAt_f' : ∀ k : ℝ, 0 < k → HasDerivAt f' (f'' k) k
  f''_neg : ∀ k : ℝ, 0 < k → f'' k < 0

namespace Technology

variable (T : Technology)

/-- Diminishing marginal product of capital (O&R p. 48): `f'` is strictly decreasing on
`k > 0`. -/
theorem f'_strictAntiOn : StrictAntiOn T.f' (Ioi 0) := by
  refine strictAntiOn_of_hasDerivWithinAt_neg (convex_Ioi 0)
    (fun x hx => (T.hasDerivAt_f' x hx).continuousAt.continuousWithinAt) (fun x hx => ?_)
    (fun x hx => T.f''_neg x (by rwa [interior_Ioi] at hx))
  rw [interior_Ioi] at hx ⊢
  exact (T.hasDerivAt_f' x hx).hasDerivWithinAt

/-- Strict concavity as a strict supporting-line inequality (used for O&R pp. 49–50):
for `x ≥ 0`, `y > 0`, `x ≠ y`, `f(x) < f(y) + f'(y)(x − y)`. -/
theorem f_lt_tangent {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) (hxy : x ≠ y) :
    T.f x < T.f y + T.f' y * (x - y) := by
  rcases lt_or_gt_of_ne hxy with h | h
  · obtain ⟨c, hc, hcs⟩ := exists_hasDerivAt_eq_slope T.f T.f' h
      (T.continuousOn_f.mono fun z hz => le_trans hx hz.1)
      (fun z hz => T.hasDerivAt_f z (lt_of_le_of_lt hx hz.1))
    have hc0 : 0 < c := lt_of_le_of_lt hx hc.1
    have hlt : T.f' y < T.f' c := T.f'_strictAntiOn hc0 hy hc.2
    have hyx : 0 < y - x := sub_pos.2 h
    rw [eq_div_iff hyx.ne'] at hcs
    have := mul_lt_mul_of_pos_right hlt hyx
    linarith
  · obtain ⟨c, hc, hcs⟩ := exists_hasDerivAt_eq_slope T.f T.f' h
      (T.continuousOn_f.mono fun z hz => le_trans hy.le hz.1)
      (fun z hz => T.hasDerivAt_f z (lt_trans hy hz.1))
    have hc0 : 0 < c := lt_trans hy hc.1
    have hlt : T.f' c < T.f' y := T.f'_strictAntiOn hy hc0 hc.1
    have hxy' : 0 < x - y := sub_pos.2 h
    rw [eq_div_iff hxy'.ne'] at hcs
    have := mul_lt_mul_of_pos_right hlt hxy'
    linarith

/-- Weak supporting-line inequality: for `x ≥ 0`, `y > 0`, `f(x) ≤ f(y) + f'(y)(x − y)`. -/
theorem f_le_tangent {x y : ℝ} (hx : 0 ≤ x) (hy : 0 < y) :
    T.f x ≤ T.f y + T.f' y * (x - y) := by
  rcases eq_or_ne x y with h | h
  · subst h
    simp
  · exact (T.f_lt_tangent hx hy h).le

/-- The marginal product of labour as a function of the capital-labour ratio,
`k ↦ f(k) − f'(k) k`, O&R (1.36), p. 47 and (1.38), p. 48. -/
def wage (k : ℝ) : ℝ := T.f k - T.f' k * k

/-- Derivative of the wage map, O&R p. 48: `d/dk [f(k) − f'(k) k] = −k f''(k)`. -/
theorem hasDerivAt_wage {k : ℝ} (hk : 0 < k) :
    HasDerivAt T.wage (-(k * T.f'' k)) k := by
  have h := (T.hasDerivAt_f k hk).sub ((T.hasDerivAt_f' k hk).mul (hasDerivAt_id k))
  exact h.congr_deriv (by simp only [id]; ring)

/-- The wage map is strictly increasing on `k > 0` (its derivative `−k f''(k)` is positive),
O&R p. 48; hence (1.38) pins down `k₂` uniquely. -/
theorem wage_strictMonoOn : StrictMonoOn T.wage (Ioi 0) := by
  refine strictMonoOn_of_hasDerivWithinAt_pos (f' := fun k => -(k * T.f'' k)) (convex_Ioi 0)
    (fun x hx => (T.hasDerivAt_wage hx).continuousAt.continuousWithinAt) (fun x hx => ?_)
    (fun x hx => ?_)
  · rw [interior_Ioi] at hx ⊢
    exact (T.hasDerivAt_wage hx).hasDerivWithinAt
  · rw [interior_Ioi] at hx
    exact neg_pos.2 (mul_neg_of_pos_of_neg hx (T.f''_neg x hx))

/-- The set of world wages attainable on the factor-price frontier, `{f(k) − f'(k) k : k > 0}`
(O&R p. 48). -/
def wageRange : Set ℝ := T.wage '' Ioi 0

/-- The capital-labour ratio `k(w)` solving `w = f(k) − f'(k) k`, O&R p. 48 (the inverse of the
wage map on `k > 0`). -/
noncomputable def kOf (w : ℝ) : ℝ := Function.invFunOn T.wage (Ioi 0) w

/-- The domestic interest rate on the factor-price frontier, `r(w) = f'(k(w))`, O&R p. 48. -/
noncomputable def rOf (w : ℝ) : ℝ := T.f' (T.kOf w)

/-- `k(w) > 0` on the frontier, O&R p. 48. -/
theorem kOf_pos {w : ℝ} (hw : w ∈ T.wageRange) : 0 < T.kOf w :=
  Function.invFunOn_mem hw

/-- `k(w)` solves the optimal-hiring condition (1.38), O&R p. 48: `f(k(w)) − f'(k(w)) k(w) = w`.
-/
theorem wage_kOf {w : ℝ} (hw : w ∈ T.wageRange) : T.wage (T.kOf w) = w :=
  Function.invFunOn_eq hw

/-- `k(·)` inverts the wage map: `k(f(k) − f'(k)k) = k` for `k > 0`, O&R p. 48. -/
theorem kOf_wage {k : ℝ} (hk : 0 < k) : T.kOf (T.wage k) = k :=
  T.wage_strictMonoOn.injOn (T.kOf_pos ⟨k, hk, rfl⟩) hk (T.wage_kOf ⟨k, hk, rfl⟩)

/-- A rise in the world wage raises the optimal capital intensity, O&R p. 48:
`k(w)` is strictly increasing on the frontier. -/
theorem kOf_strictMonoOn : StrictMonoOn T.kOf T.wageRange := by
  intro a ha b hb hab
  rw [← T.wage_kOf ha, ← T.wage_kOf hb] at hab
  exact (T.wage_strictMonoOn.lt_iff_lt (T.kOf_pos ha) (T.kOf_pos hb)).mp hab

/-- The factor-price frontier slopes down, O&R p. 48: `r(w)` is strictly decreasing. -/
theorem rOf_strictAntiOn : StrictAntiOn T.rOf T.wageRange :=
  fun _ ha _ hb hab => T.f'_strictAntiOn (T.kOf_pos ha) (T.kOf_pos hb)
    (T.kOf_strictMonoOn ha hb hab)

/-- `k(w)` is continuous at interior points of the frontier (O&R p. 48). -/
theorem continuousAt_kOf {w : ℝ} (hW : T.wageRange ∈ 𝓝 w) : ContinuousAt T.kOf w :=
  T.kOf_strictMonoOn.continuousAt_of_image_mem_nhds hW
    (mem_of_superset (Ioi_mem_nhds (T.kOf_pos (mem_of_mem_nhds hW)))
      fun k hk => ⟨T.wage k, ⟨k, hk, rfl⟩, T.kOf_wage hk⟩)

/-- Slope of `k(w)`, O&R p. 48: `k'(w) = −1/(k(w) f''(k(w)))`. -/
theorem hasDerivAt_kOf {w : ℝ} (hW : T.wageRange ∈ 𝓝 w) :
    HasDerivAt T.kOf (-1 / (T.kOf w * T.f'' (T.kOf w))) w := by
  have hk := T.kOf_pos (mem_of_mem_nhds hW)
  have hne : -(T.kOf w * T.f'' (T.kOf w)) ≠ 0 :=
    neg_ne_zero.2 (mul_neg_of_pos_of_neg hk (T.f''_neg _ hk)).ne
  have h := HasDerivAt.of_local_left_inverse (T.continuousAt_kOf hW) (T.hasDerivAt_wage hk) hne
    (by filter_upwards [hW] with y hy using T.wage_kOf hy)
  exact h.congr_deriv (by rw [inv_neg, neg_div, one_div])

/-- The slope `k'(w) = −1/(k f''(k))` is positive, O&R p. 48. -/
theorem kOf_slope_pos {w : ℝ} (hw : w ∈ T.wageRange) :
    0 < -1 / (T.kOf w * T.f'' (T.kOf w)) :=
  div_pos_of_neg_of_neg (by norm_num)
    (mul_neg_of_pos_of_neg (T.kOf_pos hw) (T.f''_neg _ (T.kOf_pos hw)))

/-- Slope of the factor-price frontier, O&R p. 48: `r'(w) = f''(k(w)) k'(w) = −1/k(w) < 0`. -/
theorem hasDerivAt_rOf {w : ℝ} (hW : T.wageRange ∈ 𝓝 w) :
    HasDerivAt T.rOf (-1 / T.kOf w) w := by
  have hk := T.kOf_pos (mem_of_mem_nhds hW)
  have hf'' := (T.f''_neg _ hk).ne
  exact ((T.hasDerivAt_f' _ hk).comp w (T.hasDerivAt_kOf hW)).congr_deriv (by field_simp)

/-! ## Zero profits on the factor-price frontier, O&R (1.34) and pp. 49–50 -/

/-- Euler's theorem with factor prices, O&R (1.34)–(1.36): for `L > 0`,
`F(K, L) = f'(k) K + (f(k) − f'(k) k) L`, `k = K/L`. -/
theorem prod_eq_factor_payments {K L : ℝ} (hL : 0 < L) :
    prod T.f K L = T.f' (K / L) * K + T.wage (K / L) * L :=
  prod_eq_euler T.f (T.f' (K / L)) hL

/-- The CRS profit inequality behind the gains from trade, O&R pp. 49–50: at factor prices
`(f'(k*), f(k*) − f'(k*)k*)`, `F(K, L) ≤ f'(k*) K + w(k*) L` for all `K ≥ 0`, `L > 0`. -/
theorem prod_le_factor_payments {ks K L : ℝ} (hks : 0 < ks) (hK : 0 ≤ K) (hL : 0 < L) :
    prod T.f K L ≤ T.f' ks * K + T.wage ks * L := by
  have h := mul_le_mul_of_nonneg_left (T.f_le_tangent (div_nonneg hK hL.le) hks) hL.le
  have he : L * (T.f ks + T.f' ks * (K / L - ks)) = T.f' ks * K + T.wage ks * L := by
    unfold wage
    field_simp
    ring
  unfold prod
  linarith

/-- Strict version of the profit inequality: `F(K, L) < f'(k*) K + w(k*) L` unless
`K = k* L` (O&R p. 50: the GNP line touches the PPF only at `B`). -/
theorem prod_lt_factor_payments {ks K L : ℝ} (hks : 0 < ks) (hK : 0 ≤ K) (hL : 0 < L)
    (hne : K ≠ ks * L) : prod T.f K L < T.f' ks * K + T.wage ks * L := by
  have hne' : K / L ≠ ks := fun h => hne ((div_eq_iff hL.ne').mp h)
  have h := mul_lt_mul_of_pos_left (T.f_lt_tangent (div_nonneg hK hL.le) hks hne') hL
  have he : L * (T.f ks + T.f' ks * (K / L - ks)) = T.f' ks * K + T.wage ks * L := by
    unfold wage
    field_simp
    ring
  unfold prod
  linarith

/-- Zero profits on the frontier, O&R p. 49: `F(K, L) − r(w) K − w L ≤ 0` for `K ≥ 0`,
`L > 0`. -/
theorem profit_nonpos {w K L : ℝ} (hw : w ∈ T.wageRange) (hK : 0 ≤ K) (hL : 0 < L) :
    prod T.f K L - T.rOf w * K - w * L ≤ 0 := by
  have h := T.prod_le_factor_payments (T.kOf_pos hw) hK hL
  rw [T.wage_kOf hw] at h
  unfold rOf
  linarith

/-- Profits are exactly zero iff the firm uses the frontier capital-labour ratio,
`K = k(w) L` (O&R p. 49). -/
theorem profit_eq_zero_iff {w K L : ℝ} (hw : w ∈ T.wageRange) (hK : 0 ≤ K) (hL : 0 < L) :
    prod T.f K L - T.rOf w * K - w * L = 0 ↔ K = T.kOf w * L := by
  constructor
  · intro h
    by_contra hne
    have h' := T.prod_lt_factor_payments (T.kOf_pos hw) hK hL hne
    rw [T.wage_kOf hw] at h'
    unfold rOf at h
    linarith
  · intro h
    have he := T.prod_eq_factor_payments (K := K) hL
    rw [h, mul_div_cancel_right₀ _ hL.ne', T.wage_kOf hw] at he
    rw [h]
    unfold rOf
    linarith

/-! ## The GNP line, the GDP line and the autarky PPF, O&R pp. 48–50 -/

/-- With free labour trade, date-2 consumption lies on or below the GNP line, O&R pp. 48–49:
`C₂(K₂, L₂) ≤ [1 + r(w)] K₂ + w Lᴴ` for every hiring choice `L₂ > 0`. -/
theorem consumption2_le_gnp {w LH K2 L2 : ℝ} (hw : w ∈ T.wageRange) (hK : 0 ≤ K2)
    (hL : 0 < L2) : consumption2 T.f w LH K2 L2 ≤ (1 + T.rOf w) * K2 + w * LH := by
  have h := T.profit_nonpos hw hK hL
  unfold consumption2
  linarith

/-- Date-2 consumption reaches the GNP line exactly under optimal hiring `K₂ = k(w) L₂`,
O&R (1.38) and p. 49. -/
theorem consumption2_eq_gnp_iff {w LH K2 L2 : ℝ} (hw : w ∈ T.wageRange) (hK : 0 ≤ K2)
    (hL : 0 < L2) :
    consumption2 T.f w LH K2 L2 = (1 + T.rOf w) * K2 + w * LH ↔ K2 = T.kOf w * L2 := by
  rw [← T.profit_eq_zero_iff hw hK hL]
  unfold consumption2
  constructor <;> intro h <;> linarith

/-- The autarky production possibility frontier, O&R p. 49: `C₂ = F(Y₁ − C₁, Lᴴ) + Y₁ − C₁`. -/
noncomputable def ppf (Y1 LH C1 : ℝ) : ℝ := prod T.f (Y1 - C1) LH + (Y1 - C1)

/-- The GNP line, O&R p. 49: `C₂ = [1 + r(w)](Y₁ − C₁) + w Lᴴ`. -/
noncomputable def gnpLine (w Y1 LH C1 : ℝ) : ℝ := (1 + T.rOf w) * (Y1 - C1) + w * LH

/-- The GDP line, O&R p. 50: `Y₂ + K₂ = [1 + r(w) + w/k(w)](Y₁ − C₁)`. -/
noncomputable def gdpLine (w Y1 C1 : ℝ) : ℝ := (1 + T.rOf w + w / T.kOf w) * (Y1 - C1)

/-- Gains from trade, O&R p. 50: the GNP line lies weakly above the autarky PPF,
for all `C₁ ≤ Y₁`. -/
theorem ppf_le_gnpLine {w Y1 LH C1 : ℝ} (hw : w ∈ T.wageRange) (hC1 : C1 ≤ Y1)
    (hLH : 0 < LH) : T.ppf Y1 LH C1 ≤ T.gnpLine w Y1 LH C1 := by
  have h := T.profit_nonpos hw (sub_nonneg.2 hC1) hLH
  unfold ppf gnpLine
  linarith

/-- The GNP line touches the autarky PPF only at point `B`, where `K₂ = Y₁ − C₁ = k(w) Lᴴ`
(O&R pp. 49–50). -/
theorem ppf_eq_gnpLine_iff {w Y1 LH C1 : ℝ} (hw : w ∈ T.wageRange) (hC1 : C1 ≤ Y1)
    (hLH : 0 < LH) : T.ppf Y1 LH C1 = T.gnpLine w Y1 LH C1 ↔ Y1 - C1 = T.kOf w * LH := by
  rw [← T.profit_eq_zero_iff hw (sub_nonneg.2 hC1) hLH]
  unfold ppf gnpLine
  constructor <;> intro h <;> linarith

/-- Slope of the autarky PPF, O&R p. 49: `−(1 + F_K(Y₁ − C₁, Lᴴ))` for `C₁ < Y₁`. -/
theorem hasDerivAt_ppf {Y1 LH C1 : ℝ} (hC1 : C1 < Y1) (hLH : 0 < LH) :
    HasDerivAt (fun c => T.ppf Y1 LH c) (-(1 + T.f' ((Y1 - C1) / LH))) C1 := by
  have hK : HasDerivAt (fun c : ℝ => Y1 - c) (-1) C1 := by
    simpa using (hasDerivAt_id C1).const_sub Y1
  have hF := hasDerivAt_prod_capital hLH
    (T.hasDerivAt_f _ (div_pos (sub_pos.2 hC1) hLH))
  have h := (hF.comp (h := fun c : ℝ => Y1 - c) C1 hK).add hK
  exact h.congr_deriv (by ring)

/-- At point `B` the GNP line is tangent to the autarky PPF, O&R p. 49: when
`Y₁ − C₁ = k(w) Lᴴ` the PPF has slope `−(1 + r(w))`, the slope of the GNP line. -/
theorem ppf_tangent_at_B {w Y1 LH C1 : ℝ} (hw : w ∈ T.wageRange) (hLH : 0 < LH)
    (hB : Y1 - C1 = T.kOf w * LH) :
    HasDerivAt (fun c => T.ppf Y1 LH c) (-(1 + T.rOf w)) C1 := by
  have hC1 : C1 < Y1 := by nlinarith [T.kOf_pos hw]
  have h := T.hasDerivAt_ppf hC1 hLH
  rwa [hB, mul_div_cancel_right₀ _ hLH.ne'] at h

/-- The GDP line, O&R p. 50: with employment `L₂ = K₂/k(w)` and `K₂ = Y₁ − C₁ > 0`,
`F(K₂, L₂) + K₂ = [1 + r(w) + w/k(w)](Y₁ − C₁)`. -/
theorem gdpLine_eq {w Y1 C1 : ℝ} (hw : w ∈ T.wageRange) (hK : 0 < Y1 - C1) :
    prod T.f (Y1 - C1) ((Y1 - C1) / T.kOf w) + (Y1 - C1) = T.gdpLine w Y1 C1 := by
  have hk := T.kOf_pos hw
  have hwk := T.wage_kOf hw
  unfold prod gdpLine rOf
  rw [div_div_cancel₀ hK.ne']
  set k := T.kOf w
  unfold wage at hwk
  rw [← hwk]
  field_simp
  ring

/-- GDP minus GNP equals net wage payments to foreign workers, O&R p. 50:
`gdp − gnp = w (L₂ − Lᴴ)` with `L₂ = (Y₁ − C₁)/k(w)`. -/
theorem gdpLine_sub_gnpLine (w Y1 LH C1 : ℝ) :
    T.gdpLine w Y1 C1 - T.gnpLine w Y1 LH C1 = w * ((Y1 - C1) / T.kOf w - LH) := by
  unfold gdpLine gnpLine
  ring

/-- The GDP line is steeper than the GNP line, O&R p. 50: for `w > 0`, GDP exceeds GNP
exactly when investment exceeds its level at `B`, `Y₁ − C₁ > k(w) Lᴴ`. -/
theorem gnpLine_lt_gdpLine_iff {w Y1 LH C1 : ℝ} (hw : w ∈ T.wageRange) (hwpos : 0 < w) :
    T.gnpLine w Y1 LH C1 < T.gdpLine w Y1 C1 ↔ T.kOf w * LH < Y1 - C1 := by
  have h := T.gdpLine_sub_gnpLine w Y1 LH C1
  have hk := T.kOf_pos hw
  rw [← sub_pos, h, mul_pos_iff_of_pos_left hwpos, sub_pos, lt_div_iff₀ hk, mul_comm]

/-! ## The pattern of labour trade, O&R p. 50

The autarky equilibrium `A` solves the Euler equation with `L₂ = Lᴴ`,
`u'(Y₁ − Kᴬ) = β[1 + f'(Kᴬ/Lᴴ)] u'(F(Kᴬ, Lᴴ) + Kᴬ)`; the trade equilibrium solves (1.37)
on the GNP line, `u'(Y₁ − Kᵀ) = β[1 + r(w)] u'([1 + r(w)]Kᵀ + w Lᴴ)`, with employment
`L₂ = Kᵀ/k(w)` from (1.38). Strict concavity of `u` enters as `u'` strictly decreasing
and positive. -/

/-- The autarky wage `wᴬ = F_L(Kᴬ, Lᴴ) = f(kᴬ) − f'(kᴬ) kᴬ`, `kᴬ = Kᴬ/Lᴴ`, O&R p. 50. -/
noncomputable def autarkyWage (KA LH : ℝ) : ℝ := T.wage (KA / LH)

/-- An interior Euler equation `u'(C₁) = β X u'(C₂)` with `u' > 0`, `β > 0` forces the gross
return `X` to be positive (used for `1 + f'(k)` at the optima of O&R p. 50). -/
theorem gross_return_pos_of_euler {u' : ℝ → ℝ} {β X C1 C2 : ℝ} (hβ : 0 < β)
    (h1 : 0 < u' C1) (h2 : 0 < u' C2) (hfoc : u' C1 = β * X * u' C2) : 0 < X := by
  by_contra hn
  push Not at hn
  nlinarith [mul_pos hβ h2]

/-- Labour imports, O&R p. 50: if the autarky wage exceeds the world wage, `wᴬ > w`, then
at the trade equilibrium the country employs more labour than it owns, `L₂ = Kᵀ/k(w) > Lᴴ`. -/
theorem labour_imports_of_autarkyWage_gt {u' : ℝ → ℝ}
    (hu'anti : ∀ x y, 0 < x → x < y → u' y < u' x) (hu'pos : ∀ x, 0 < x → 0 < u' x)
    {β Y1 w LH KA KT : ℝ} (hβ : 0 < β) (hLH : 0 < LH) (hKA : 0 < KA)
    (hw : w ∈ T.wageRange) (hC1A : 0 < Y1 - KA) (hC2A : 0 < prod T.f KA LH + KA)
    (hC1T : 0 < Y1 - KT) (hC2T : 0 < (1 + T.rOf w) * KT + w * LH)
    (hfocA : u' (Y1 - KA) = β * (1 + T.f' (KA / LH)) * u' (prod T.f KA LH + KA))
    (hfocT : u' (Y1 - KT) = β * (1 + T.rOf w) * u' ((1 + T.rOf w) * KT + w * LH))
    (hgt : w < T.autarkyWage KA LH) : LH < KT / T.kOf w := by
  have hkB := T.kOf_pos hw
  have hwB := T.wage_kOf hw
  have hkA : 0 < KA / LH := div_pos hKA hLH
  have hk : T.kOf w < KA / LH := by
    rw [← T.wage_strictMonoOn.lt_iff_lt hkB hkA, hwB]
    exact hgt
  have hKB : T.kOf w * LH < KA := (lt_div_iff₀ hLH).mp hk
  have hA := gross_return_pos_of_euler hβ (hu'pos _ hC1A) (hu'pos _ hC2A) hfocA
  have hr := gross_return_pos_of_euler hβ (hu'pos _ hC1T) (hu'pos _ hC2T) hfocT
  have hrA : T.f' (KA / LH) < T.rOf w := T.f'_strictAntiOn hkB hkA hk
  rw [lt_div_iff₀ hkB]
  by_contra hcon
  push Not at hcon
  have hu1 : u' (Y1 - KT) < u' (Y1 - KA) := hu'anti _ _ hC1A (by linarith)
  -- `C₂ᵀ ≤ ppf(B) < C₂ᴬ`
  have hB := T.prod_eq_factor_payments (K := T.kOf w * LH) hLH
  rw [mul_div_cancel_right₀ _ hLH.ne', hwB] at hB
  have hBA := T.prod_le_factor_payments hkA (mul_pos hkB hLH).le hLH (K := T.kOf w * LH)
  have hAA := T.prod_eq_factor_payments (K := KA) hLH
  have h1 : (1 + T.rOf w) * KT ≤ (1 + T.rOf w) * (T.kOf w * LH) :=
    mul_le_mul_of_nonneg_left (by linarith) hr.le
  have h2 : (1 + T.f' (KA / LH)) * (T.kOf w * LH) < (1 + T.f' (KA / LH)) * KA :=
    mul_lt_mul_of_pos_left hKB hA
  have hC2 : (1 + T.rOf w) * KT + w * LH < prod T.f KA LH + KA := by
    unfold rOf at h1 ⊢
    linarith
  have hu2 : u' (prod T.f KA LH + KA) < u' ((1 + T.rOf w) * KT + w * LH) :=
    hu'anti _ _ hC2T hC2
  have h3 : (1 + T.f' (KA / LH)) * u' (prod T.f KA LH + KA) <
      (1 + T.rOf w) * u' ((1 + T.rOf w) * KT + w * LH) :=
    mul_lt_mul'' (by linarith) hu2 hA.le (hu'pos _ hC2A).le
  have h4 := mul_lt_mul_of_pos_left h3 hβ
  rw [← mul_assoc, ← mul_assoc, ← hfocA, ← hfocT] at h4
  linarith

/-- Labour exports, O&R p. 50: if the autarky wage is below the world wage, `wᴬ < w`, then at
the trade equilibrium the country employs less labour than it owns, `L₂ = Kᵀ/k(w) < Lᴴ`. -/
theorem labour_exports_of_autarkyWage_lt {u' : ℝ → ℝ}
    (hu'anti : ∀ x y, 0 < x → x < y → u' y < u' x) (hu'pos : ∀ x, 0 < x → 0 < u' x)
    {β Y1 w LH KA KT : ℝ} (hβ : 0 < β) (hLH : 0 < LH) (hKA : 0 < KA)
    (hw : w ∈ T.wageRange) (hC1A : 0 < Y1 - KA) (hC2A : 0 < prod T.f KA LH + KA)
    (hC1T : 0 < Y1 - KT) (hC2T : 0 < (1 + T.rOf w) * KT + w * LH)
    (hfocA : u' (Y1 - KA) = β * (1 + T.f' (KA / LH)) * u' (prod T.f KA LH + KA))
    (hfocT : u' (Y1 - KT) = β * (1 + T.rOf w) * u' ((1 + T.rOf w) * KT + w * LH))
    (hlt : T.autarkyWage KA LH < w) : KT / T.kOf w < LH := by
  have hkB := T.kOf_pos hw
  have hwB := T.wage_kOf hw
  have hkA : 0 < KA / LH := div_pos hKA hLH
  have hk : KA / LH < T.kOf w := by
    rw [← T.wage_strictMonoOn.lt_iff_lt hkA hkB, hwB]
    exact hlt
  have hKB : KA < T.kOf w * LH := (div_lt_iff₀ hLH).mp hk
  have hA := gross_return_pos_of_euler hβ (hu'pos _ hC1A) (hu'pos _ hC2A) hfocA
  have hr := gross_return_pos_of_euler hβ (hu'pos _ hC1T) (hu'pos _ hC2T) hfocT
  have hrA : T.rOf w < T.f' (KA / LH) := T.f'_strictAntiOn hkA hkB hk
  rw [div_lt_iff₀ hkB]
  by_contra hcon
  push Not at hcon
  have hu1 : u' (Y1 - KA) < u' (Y1 - KT) := hu'anti _ _ hC1T (by linarith)
  -- `C₂ᴬ ≤ gnp(Kᴬ) < gnp(Kᵀ) = C₂ᵀ`
  have hAB := T.prod_le_factor_payments hkB hKA.le hLH (K := KA)
  rw [hwB] at hAB
  have h1 : (1 + T.rOf w) * KA < (1 + T.rOf w) * KT :=
    mul_lt_mul_of_pos_left (by linarith) hr
  have hC2 : prod T.f KA LH + KA < (1 + T.rOf w) * KT + w * LH := by
    unfold rOf at h1 ⊢
    linarith
  have hu2 : u' ((1 + T.rOf w) * KT + w * LH) < u' (prod T.f KA LH + KA) :=
    hu'anti _ _ hC2A hC2
  have h3 : (1 + T.rOf w) * u' ((1 + T.rOf w) * KT + w * LH) <
      (1 + T.f' (KA / LH)) * u' (prod T.f KA LH + KA) :=
    mul_lt_mul'' (by linarith) hu2 hr.le (hu'pos _ hC2T).le
  have h4 := mul_lt_mul_of_pos_left h3 hβ
  rw [← mul_assoc, ← mul_assoc, ← hfocA, ← hfocT] at h4
  linarith

/-! ## Comparative statics of the autarky wage, O&R p. 50 -/

/-- Literal reading of O&R p. 50 ("countries that save more ... have higher autarky wages"):
for given `Lᴴ`, the autarky wage is strictly increasing in autarky saving `Kᴬ = Y₁ − C₁ᴬ`. -/
theorem autarkyWage_lt_of_saving_lt {LH KA KA' : ℝ} (hLH : 0 < LH) (hKA : 0 < KA)
    (hlt : KA < KA') : T.autarkyWage KA LH < T.autarkyWage KA' LH :=
  T.wage_strictMonoOn (div_pos hKA hLH) (div_pos (hKA.trans hlt) hLH)
    (div_lt_div_of_pos_right hlt hLH)

/-- A larger labour endowment lowers the autarky wage, O&R p. 50: if `Kᴬ` and `Kᴬ'` solve the
autarky Euler equation with endowments `Lᴴ < Lᴴ'` (same `Y₁`, `β`), then `wᴬ' < wᴬ`. -/
theorem autarkyWage_anti_labour {u' : ℝ → ℝ}
    (hu'anti : ∀ x y, 0 < x → x < y → u' y < u' x) (hu'pos : ∀ x, 0 < x → 0 < u' x)
    {β Y1 LH LH' KA KA' : ℝ} (hβ : 0 < β) (hLH : 0 < LH) (hLH' : LH < LH')
    (hKA : 0 < KA) (hKA' : 0 < KA') (hC2 : 0 < prod T.f KA LH + KA)
    (hC1' : 0 < Y1 - KA') (hC2' : 0 < prod T.f KA' LH' + KA')
    (hfoc : u' (Y1 - KA) = β * (1 + T.f' (KA / LH)) * u' (prod T.f KA LH + KA))
    (hfoc' : u' (Y1 - KA') = β * (1 + T.f' (KA' / LH')) * u' (prod T.f KA' LH' + KA')) :
    T.autarkyWage KA' LH' < T.autarkyWage KA LH := by
  have hLH'0 : 0 < LH' := hLH.trans hLH'
  have hk : 0 < KA / LH := div_pos hKA hLH
  have hk' : 0 < KA' / LH' := div_pos hKA' hLH'0
  refine T.wage_strictMonoOn hk' hk ?_
  by_contra hcon
  push Not at hcon
  have hA' := gross_return_pos_of_euler hβ (hu'pos _ hC1') (hu'pos _ hC2') hfoc'
  set k := KA / LH with hkdef
  set k' := KA' / LH' with hk'def
  have hKAe : KA = k * LH := by rw [hkdef]; field_simp
  have hKA'e : KA' = k' * LH' := by rw [hk'def]; field_simp
  have hC2e : prod T.f KA LH + KA = LH * (T.f k + k) := by
    unfold prod
    rw [← hkdef, hKAe]
    ring
  have hC2e' : prod T.f KA' LH' + KA' = LH' * (T.f k' + k') := by
    unfold prod
    rw [← hk'def, hKA'e]
    ring
  -- more saving: `Kᴬ < Kᴬ'`
  have hK : KA < KA' := by
    rw [hKAe, hKA'e]
    nlinarith
  have hu1 : u' (Y1 - KA) < u' (Y1 - KA') := hu'anti _ _ hC1' (by linarith)
  -- more date-2 consumption: `C₂ < C₂'`
  have htan := T.f_le_tangent hk.le hk'
  have hmono : T.f k + k ≤ T.f k' + k' := by nlinarith
  have hpos : 0 < T.f k + k := by
    rw [hC2e] at hC2
    exact pos_of_mul_pos_right hC2 hLH.le
  have hC : prod T.f KA LH + KA < prod T.f KA' LH' + KA' := by
    rw [hC2e, hC2e']
    nlinarith
  have hu2 : u' (prod T.f KA' LH' + KA') < u' (prod T.f KA LH + KA) := hu'anti _ _ hC2 hC
  have hf' : T.f' k' ≤ T.f' k := T.f'_strictAntiOn.antitoneOn hk hk' hcon
  have h3 : (1 + T.f' k') * u' (prod T.f KA' LH' + KA') <
      (1 + T.f' k) * u' (prod T.f KA LH + KA) :=
    mul_lt_mul' (by linarith) hu2 (hu'pos _ hC2').le (by linarith)
  have h4 := mul_lt_mul_of_pos_left h3 hβ
  rw [← mul_assoc, ← mul_assoc, ← hfoc, ← hfoc'] at h4
  linarith

/-- Higher saving propensity raises the autarky wage, O&R p. 50: if `Kᴬ` solves the autarky
Euler equation at `(Y₁, β)` and `Kᴬ'` at `(Y₁', β')` with `Y₁ ≤ Y₁'`, `β ≤ β'`, one strictly
(same `Lᴴ`), then autarky saving and hence the autarky wage are strictly higher, `wᴬ < wᴬ'`. -/
theorem autarkyWage_lt_of_more_saving {u' : ℝ → ℝ}
    (hu'anti : ∀ x y, 0 < x → x < y → u' y < u' x) (hu'pos : ∀ x, 0 < x → 0 < u' x)
    {β β' Y1 Y1' LH KA KA' : ℝ} (hβ : 0 < β) (hββ : β ≤ β') (hYY : Y1 ≤ Y1')
    (hstrict : Y1 < Y1' ∨ β < β') (hLH : 0 < LH) (hKA : 0 < KA) (hKA' : 0 < KA')
    (hC1 : 0 < Y1 - KA) (hC2 : 0 < prod T.f KA LH + KA)
    (hC2' : 0 < prod T.f KA' LH + KA')
    (hfoc : u' (Y1 - KA) = β * (1 + T.f' (KA / LH)) * u' (prod T.f KA LH + KA))
    (hfoc' : u' (Y1' - KA') = β' * (1 + T.f' (KA' / LH)) * u' (prod T.f KA' LH + KA')) :
    T.autarkyWage KA LH < T.autarkyWage KA' LH := by
  have hk : 0 < KA / LH := div_pos hKA hLH
  have hk' : 0 < KA' / LH := div_pos hKA' hLH
  refine T.wage_strictMonoOn hk hk' ?_
  by_contra hcon
  push Not at hcon
  have hA := gross_return_pos_of_euler hβ (hu'pos _ hC1) (hu'pos _ hC2) hfoc
  set k := KA / LH with hkdef
  set k' := KA' / LH with hk'def
  have hKAe : KA = k * LH := by rw [hkdef]; field_simp
  have hKA'e : KA' = k' * LH := by rw [hk'def]; field_simp
  have hC2e : prod T.f KA LH + KA = LH * (T.f k + k) := by
    unfold prod
    rw [← hkdef, hKAe]
    ring
  have hC2e' : prod T.f KA' LH + KA' = LH * (T.f k' + k') := by
    unfold prod
    rw [← hk'def, hKA'e]
    ring
  have hK : KA' ≤ KA := by
    rw [hKAe, hKA'e]
    exact mul_le_mul_of_nonneg_right hcon hLH.le
  -- date-1 consumption weakly higher, so `u'(C₁') ≤ u'(C₁)`
  have hC1le : Y1 - KA ≤ Y1' - KA' := by linarith
  have hu1 : u' (Y1' - KA') ≤ u' (Y1 - KA) := by
    rcases hC1le.eq_or_lt with h | h
    · rw [h]
    · exact (hu'anti _ _ hC1 h).le
  -- date-2 consumption weakly lower, so `u'(C₂) ≤ u'(C₂')`
  have htan := T.f_le_tangent hk'.le hk
  have hmono : T.f k' + k' ≤ T.f k + k := by nlinarith
  have hC : prod T.f KA' LH + KA' ≤ prod T.f KA LH + KA := by
    rw [hC2e, hC2e']
    exact mul_le_mul_of_nonneg_left hmono hLH.le
  have hu2 : u' (prod T.f KA LH + KA) ≤ u' (prod T.f KA' LH + KA') := by
    rcases hC.eq_or_lt with h | h
    · rw [h]
    · exact (hu'anti _ _ hC2' h).le
  have hf' : T.f' k ≤ T.f' k' := T.f'_strictAntiOn.antitoneOn hk' hk hcon
  have h3 : (1 + T.f' k) * u' (prod T.f KA LH + KA) ≤
      (1 + T.f' k') * u' (prod T.f KA' LH + KA') :=
    mul_le_mul (by linarith) hu2 (hu'pos _ hC2).le (by linarith)
  have hX : 0 < (1 + T.f' k) * u' (prod T.f KA LH + KA) := mul_pos hA (hu'pos _ hC2)
  rcases hstrict with hY | hb
  · have h4 := mul_le_mul hββ h3 hX.le (hβ.trans_le hββ).le
    rw [← mul_assoc, ← mul_assoc, ← hfoc, ← hfoc'] at h4
    have : u' (Y1' - KA') < u' (Y1 - KA) := hu'anti _ _ hC1 (by linarith)
    linarith
  · have h4 := mul_lt_mul hb h3 hX (hβ.trans hb).le
    rw [← mul_assoc, ← mul_assoc, ← hfoc, ← hfoc'] at h4
    linarith

/-- Under free labour trade a larger labour endowment raises net labour exports,
O&R p. 50: with `w > 0`, if `Kᵀ` and `Kᵀ'` solve (1.37) on the GNP line for `Lᴴ < Lᴴ'`,
then `Lᴴ − Kᵀ/k(w) < Lᴴ' − Kᵀ'/k(w)`. -/
theorem netLabourExports_lt_of_labour_lt {u' : ℝ → ℝ}
    (hu'anti : ∀ x y, 0 < x → x < y → u' y < u' x) (hu'pos : ∀ x, 0 < x → 0 < u' x)
    {β Y1 w LH LH' KT KT' : ℝ} (hβ : 0 < β) (hw : w ∈ T.wageRange) (hwpos : 0 < w)
    (hLH : LH < LH') (hC1T : 0 < Y1 - KT) (hC2T : 0 < (1 + T.rOf w) * KT + w * LH)
    (hC1T' : 0 < Y1 - KT')
    (hfocT : u' (Y1 - KT) = β * (1 + T.rOf w) * u' ((1 + T.rOf w) * KT + w * LH))
    (hfocT' : u' (Y1 - KT') = β * (1 + T.rOf w) * u' ((1 + T.rOf w) * KT' + w * LH')) :
    LH - KT / T.kOf w < LH' - KT' / T.kOf w := by
  have hkB := T.kOf_pos hw
  have hr := gross_return_pos_of_euler hβ (hu'pos _ hC1T) (hu'pos _ hC2T) hfocT
  have hK : KT' < KT := by
    by_contra hcon
    push Not at hcon
    have hu1 : u' (Y1 - KT) ≤ u' (Y1 - KT') := by
      rcases hcon.eq_or_lt with h | h
      · rw [h]
      · exact (hu'anti _ _ hC1T' (by linarith)).le
    have hC : (1 + T.rOf w) * KT + w * LH < (1 + T.rOf w) * KT' + w * LH' := by
      nlinarith
    have hu2 := hu'anti _ _ hC2T hC
    have h4 := mul_lt_mul_of_pos_left hu2 (mul_pos hβ hr)
    rw [← hfocT, ← hfocT'] at h4
    linarith
  have := div_lt_div_of_pos_right hK hkB
  linarith

end Technology

end ObstfeldRogoff.IntertemporalTrade.LabourMobility

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Walrasian stability and the Marshall–Lerner condition

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*,
Appendix 1A, pp. 53–54. The world market for date-1 output is Walras-stable when
world excess saving rises with the interest rate (O&R (1.39)). Written with
date-1 Home imports `IM₁ = C₁ + I₁ − Y₁` and date-2 Foreign imports
`IM₂* = C₂* + I₂* − Y₂*`, it becomes O&R (1.40): the value of Foreign's date-2
imports in date-1 units, net of Home's date-1 imports, rises with `r`.

At an equilibrium where Home imports on date 1, (1.40) holds if and only if the
import elasticities `ζ = −(1 + r) IM₁'/IM₁` and `ζ* = (1 + r) IM₂*'/IM₂*` sum to
more than one: the **Marshall–Lerner condition** O&R (1.41).
-/

namespace ObstfeldRogoff.IntertemporalTrade.Stability

/-- Home's date-1 import elasticity with respect to the gross interest rate (O&R p. 54). -/
noncomputable def zeta (r IM1 dIM1 : ℝ) : ℝ := -(1 + r) * dIM1 / IM1

/-- Foreign's date-2 import elasticity with respect to the gross interest rate (O&R p. 54). -/
noncomputable def zetaStar (r IM2s dIM2s : ℝ) : ℝ := (1 + r) * dIM2s / IM2s

/-- The derivative of `IM₂*(r)/(1 + r) − IM₁(r)`, the left side of O&R (1.40). -/
theorem hasDerivAt_netImports {IM1 IM2s : ℝ → ℝ} {r dIM1 dIM2s : ℝ} (hr : 0 < 1 + r)
    (h1 : HasDerivAt IM1 dIM1 r) (h2 : HasDerivAt IM2s dIM2s r) :
    HasDerivAt (fun s => IM2s s / (1 + s) - IM1 s)
      (dIM2s / (1 + r) - IM2s r / (1 + r) ^ 2 - dIM1) r := by
  have hd : HasDerivAt (fun s : ℝ => 1 + s) 1 r := (hasDerivAt_id r).const_add 1
  have h3 : HasDerivAt (fun s => IM2s s / (1 + s))
      ((dIM2s * (1 + r) - IM2s r * 1) / (1 + r) ^ 2) r := h2.div hd hr.ne'
  refine HasDerivAt.congr_deriv (HasDerivAt.sub h3 h1) ?_
  field_simp

/-- **(1.39) ⇔ (1.40)**: if Home's saving minus investment is `−IM₁` and Foreign's is
`IM₂*/(1 + r)` (its budget constraint), world excess saving and the net-import expression
have the same derivative. -/
theorem worldExcessSaving_eq {S I Ss Is IM1 IM2s : ℝ → ℝ}
    (hH : ∀ s, S s - I s = -IM1 s) (hF : ∀ s, Ss s - Is s = IM2s s / (1 + s)) :
    (fun s => S s + Ss s - I s - Is s) = fun s => IM2s s / (1 + s) - IM1 s := by
  funext s
  linarith [hH s, hF s]

/-- **The Marshall–Lerner condition** O&R (1.41), p. 54: at an equilibrium with
`IM₁ = IM₂*/(1 + r) > 0`, the stability condition (1.40) holds iff `ζ + ζ* > 1`. -/
theorem marshall_lerner {r IM1 IM2s dIM1 dIM2s : ℝ} (hr : 0 < 1 + r) (hIM : 0 < IM1)
    (heq : IM1 = IM2s / (1 + r)) :
    0 < dIM2s / (1 + r) - IM2s / (1 + r) ^ 2 - dIM1 ↔
      1 < zeta r IM1 dIM1 + zetaStar r IM2s dIM2s := by
  have hIM2 : IM2s = (1 + r) * IM1 := by rw [heq]; field_simp
  have hIM2pos : 0 < IM2s := by rw [hIM2]; positivity
  unfold zeta zetaStar
  have key : dIM2s / (1 + r) - IM2s / (1 + r) ^ 2 - dIM1 =
      (IM1 / (1 + r)) * (-(1 + r) * dIM1 / IM1 + (1 + r) * dIM2s / IM2s - 1) := by
    rw [hIM2]
    field_simp
    ring
  rw [key]
  constructor
  · intro hpos
    have := (pos_iff_pos_of_mul_pos hpos).1 (div_pos hIM hr)
    linarith
  · intro hml
    exact mul_pos (div_pos hIM hr) (by linarith)

/-- **Stability via Marshall–Lerner**: combining (1.39) ⇔ (1.40) with (1.41), world excess
saving is increasing at the equilibrium iff `ζ + ζ* > 1`. -/
theorem stable_iff_marshall_lerner {S I Ss Is IM1 IM2s : ℝ → ℝ} {r dIM1 dIM2s : ℝ}
    (hr : 0 < 1 + r) (hH : ∀ s, S s - I s = -IM1 s)
    (hF : ∀ s, Ss s - Is s = IM2s s / (1 + s)) (h1 : HasDerivAt IM1 dIM1 r)
    (h2 : HasDerivAt IM2s dIM2s r) (hIM : 0 < IM1 r) (heq : IM1 r = IM2s r / (1 + r)) :
    HasDerivAt (fun s => S s + Ss s - I s - Is s)
        (dIM2s / (1 + r) - IM2s r / (1 + r) ^ 2 - dIM1) r ∧
      (0 < dIM2s / (1 + r) - IM2s r / (1 + r) ^ 2 - dIM1 ↔
        1 < zeta r (IM1 r) dIM1 + zetaStar r (IM2s r) dIM2s) := by
  refine ⟨?_, marshall_lerner hr hIM heq⟩
  rw [worldExcessSaving_eq hH hF]
  exact hasDerivAt_netImports hr h1 h2

/-- The numerator and denominator of O&R (1.23) at a zero current account (`C₁ = Y₁`):
with `u' > 0` and `u'' < 0`, `dC₁/dr = βu'(C₂)/[u''(C₁) + β(1 + r)²u''(C₂)] < 0`. -/
theorem dC1_neg_of_zero_ca {β r du2 d2u1 d2u2 Y1 C1 : ℝ} (hβ : 0 < β) (hdu : 0 < du2)
    (h1 : d2u1 < 0) (h2 : d2u2 < 0) (hca : C1 = Y1) :
    (β * du2 + β * (1 + r) * d2u2 * (Y1 - C1)) / (d2u1 + β * (1 + r) ^ 2 * d2u2) < 0 := by
  rw [hca, sub_self, mul_zero, add_zero]
  have : β * (1 + r) ^ 2 * d2u2 ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) h2.le
  exact div_neg_of_pos_of_neg (mul_pos hβ hdu) (by linarith)

/-- **Zero-current-account equilibria are stable** (O&R p. 53): if both countries' saving
rises with `r` (as (1.23) gives at `C₁ = Y₁`, see `dC1_neg_of_zero_ca`) and investment
does not, world excess saving is strictly increasing, i.e. (1.39) holds. -/
theorem stable_of_saving_increasing {dS dSs dI dIs : ℝ} (hS : 0 < dS) (hSs : 0 < dSs)
    (hI : dI ≤ 0) (hIs : dIs ≤ 0) : 0 < dS + dSs - dI - dIs := by
  linarith

end ObstfeldRogoff.IntertemporalTrade.Stability

set_option linter.style.longLine false
#print axioms ObstfeldRogoff.IntertemporalTrade.Economy
#print axioms ObstfeldRogoff.IntertemporalTrade.Economy.mk
#print axioms ObstfeldRogoff.IntertemporalTrade.Economy.r
#print axioms ObstfeldRogoff.IntertemporalTrade.Economy.Y1
#print axioms ObstfeldRogoff.IntertemporalTrade.Economy.Y2
#print axioms ObstfeldRogoff.IntertemporalTrade.Economy.one_add_r_pos
#print axioms ObstfeldRogoff.IntertemporalTrade.Economy.Budget
#print axioms ObstfeldRogoff.IntertemporalTrade.Economy.ca1
#print axioms ObstfeldRogoff.IntertemporalTrade.Economy.ca2
#print axioms ObstfeldRogoff.IntertemporalTrade.Economy.budget_iff
#print axioms ObstfeldRogoff.IntertemporalTrade.Economy.ca1_add_ca2
#print axioms ObstfeldRogoff.IntertemporalTrade.Consumer.concave_le_tangent
#print axioms ObstfeldRogoff.IntertemporalTrade.Consumer.deriv_lt_of_strictConcave
#print axioms ObstfeldRogoff.IntertemporalTrade.Consumer.Household
#print axioms ObstfeldRogoff.IntertemporalTrade.Consumer.Household.mk
#print axioms ObstfeldRogoff.IntertemporalTrade.Consumer.Household.u
#print axioms ObstfeldRogoff.IntertemporalTrade.Consumer.Household.β
#print axioms ObstfeldRogoff.IntertemporalTrade.Consumer.Household.Y1
#print axioms ObstfeldRogoff.IntertemporalTrade.Consumer.Household.Y2
#print axioms ObstfeldRogoff.IntertemporalTrade.Consumer.Household.β_pos
#print axioms ObstfeldRogoff.IntertemporalTrade.Consumer.Household.Y1_pos
#print axioms ObstfeldRogoff.IntertemporalTrade.Consumer.Household.Y2_pos
#print axioms ObstfeldRogoff.IntertemporalTrade.Consumer.Household.mono
#print axioms ObstfeldRogoff.IntertemporalTrade.Consumer.Household.concave
#print axioms ObstfeldRogoff.IntertemporalTrade.Consumer.Household.utility
#print axioms ObstfeldRogoff.IntertemporalTrade.Consumer.Household.Feasible
#print axioms ObstfeldRogoff.IntertemporalTrade.Consumer.Household.IsOptimal
#print axioms ObstfeldRogoff.IntertemporalTrade.Consumer.Household.feasible_iff_budget
#print axioms ObstfeldRogoff.IntertemporalTrade.Consumer.Household.endowment_feasible
#print axioms ObstfeldRogoff.IntertemporalTrade.Consumer.Household.utility_lt_utility_of_lt
#print axioms ObstfeldRogoff.IntertemporalTrade.Consumer.Household.optimal_binds
#print axioms ObstfeldRogoff.IntertemporalTrade.Consumer.Household.optimal_unique
#print axioms ObstfeldRogoff.IntertemporalTrade.Consumer.Household.hasDerivAt_budgetLine
#print axioms ObstfeldRogoff.IntertemporalTrade.Consumer.Household.euler_of_optimal
#print axioms ObstfeldRogoff.IntertemporalTrade.Consumer.Household.optimal_of_euler
#print axioms ObstfeldRogoff.IntertemporalTrade.Consumer.Household.isOptimal_iff_euler
#print axioms ObstfeldRogoff.IntertemporalTrade.Consumer.Household.flat_of_beta_mul_eq_one
#print axioms ObstfeldRogoff.IntertemporalTrade.Consumer.Household.flat_level
#print axioms ObstfeldRogoff.IntertemporalTrade.Consumer.Household.tilt_up
#print axioms ObstfeldRogoff.IntertemporalTrade.Consumer.Household.tilt_down
#print axioms ObstfeldRogoff.IntertemporalTrade.Consumer.Household.exists_optimal
#print axioms ObstfeldRogoff.IntertemporalTrade.Consumer.euler_general
#print axioms ObstfeldRogoff.IntertemporalTrade.Consumer.envelope_general
#print axioms ObstfeldRogoff.IntertemporalTrade.Consumer.welfare_equivalent_wealth
#print axioms ObstfeldRogoff.IntertemporalTrade.Consumer.Household.IsAutarkyRate
#print axioms ObstfeldRogoff.IntertemporalTrade.Consumer.Household.utility_endowment_le
#print axioms ObstfeldRogoff.IntertemporalTrade.Consumer.Household.utility_endowment_lt
#print axioms ObstfeldRogoff.IntertemporalTrade.Consumer.Household.isOptimal_of_utility_eq
#print axioms ObstfeldRogoff.IntertemporalTrade.Consumer.Household.saving_nonneg_of_autarky_lt
#print axioms ObstfeldRogoff.IntertemporalTrade.Consumer.Household.saving_nonpos_of_lt_autarky
#print axioms ObstfeldRogoff.IntertemporalTrade.Consumer.Household.optimal_at_autarky
#print axioms ObstfeldRogoff.IntertemporalTrade.Consumer.Household.utility_mono_of_autarky_le
#print axioms ObstfeldRogoff.IntertemporalTrade.Consumer.Household.utility_anti_of_le_autarky
#print axioms ObstfeldRogoff.IntertemporalTrade.Consumer.Household.utility_lt_of_lends
#print axioms ObstfeldRogoff.IntertemporalTrade.Consumer.Household.utility_lt_of_borrows
#print axioms ObstfeldRogoff.IntertemporalTrade.Consumer.Household.isAutarkyRate_iff
#print axioms ObstfeldRogoff.IntertemporalTrade.Consumer.Household.autarkyRate_unique
#print axioms ObstfeldRogoff.IntertemporalTrade.Consumer.Household.saving_pos_of_autarky_lt
#print axioms ObstfeldRogoff.IntertemporalTrade.Consumer.Household.saving_neg_of_lt_autarky
#print axioms ObstfeldRogoff.IntertemporalTrade.Consumer.Household.utility_strictMono_of_autarky_le
#print axioms ObstfeldRogoff.IntertemporalTrade.Consumer.Household.utility_strictAnti_of_le_autarky
#print axioms ObstfeldRogoff.IntertemporalTrade.Consumer.autarkyGross
#print axioms ObstfeldRogoff.IntertemporalTrade.Consumer.autarkyGross_anti_Y1
#print axioms ObstfeldRogoff.IntertemporalTrade.Consumer.autarkyGross_mono_Y2
#print axioms ObstfeldRogoff.IntertemporalTrade.Consumer.autarkyGross_anti_beta
#print axioms ObstfeldRogoff.IntertemporalTrade.CurrentAccount.gnp_sub_gdp
#print axioms ObstfeldRogoff.IntertemporalTrade.CurrentAccount.ca2_eq_neg_ca1
#print axioms ObstfeldRogoff.IntertemporalTrade.CurrentAccount.caG1
#print axioms ObstfeldRogoff.IntertemporalTrade.CurrentAccount.caG2
#print axioms ObstfeldRogoff.IntertemporalTrade.CurrentAccount.budgetG_iff
#print axioms ObstfeldRogoff.IntertemporalTrade.CurrentAccount.caG1_add_caG2
#print axioms ObstfeldRogoff.IntertemporalTrade.CurrentAccount.caG1_of_flat
#print axioms ObstfeldRogoff.IntertemporalTrade.CurrentAccount.flat_level_G
#print axioms ObstfeldRogoff.IntertemporalTrade.CurrentAccount.flatCA1
#print axioms ObstfeldRogoff.IntertemporalTrade.CurrentAccount.flatCA1_permanent
#print axioms ObstfeldRogoff.IntertemporalTrade.CurrentAccount.flatCA1_strictMono_Y1
#print axioms ObstfeldRogoff.IntertemporalTrade.CurrentAccount.flatCA1_strictAnti_Y2
#print axioms ObstfeldRogoff.IntertemporalTrade.CurrentAccount.ca1_of_optimal
#print axioms ObstfeldRogoff.IntertemporalTrade.CurrentAccount.temporary_government_deficit
#print axioms ObstfeldRogoff.IntertemporalTrade.CurrentAccount.permanent_government_balanced
#print axioms ObstfeldRogoff.IntertemporalTrade.Investment.currentAccount
#print axioms ObstfeldRogoff.IntertemporalTrade.Investment.saving
#print axioms ObstfeldRogoff.IntertemporalTrade.Investment.currentAccount_eq_saving_sub_investment
#print axioms ObstfeldRogoff.IntertemporalTrade.Investment.nfa_change_iff_wealth_change
#print axioms ObstfeldRogoff.IntertemporalTrade.Investment.intertemporal_budget_iff
#print axioms ObstfeldRogoff.IntertemporalTrade.Investment.consumption2
#print axioms ObstfeldRogoff.IntertemporalTrade.Investment.utility
#print axioms ObstfeldRogoff.IntertemporalTrade.Investment.budget_iff_consumption2
#print axioms ObstfeldRogoff.IntertemporalTrade.Investment.IsOptimal
#print axioms ObstfeldRogoff.IntertemporalTrade.Investment.pvNetOutput
#print axioms ObstfeldRogoff.IntertemporalTrade.Investment.pvNetOutput_eq
#print axioms ObstfeldRogoff.IntertemporalTrade.Investment.consumption2_eq_pv
#print axioms ObstfeldRogoff.IntertemporalTrade.Investment.fisher_separation
#print axioms ObstfeldRogoff.IntertemporalTrade.Investment.fisher_separation_pv
#print axioms ObstfeldRogoff.IntertemporalTrade.Investment.profit_maximizer_unique
#print axioms ObstfeldRogoff.IntertemporalTrade.Investment.fisher_separation_independent
#print axioms ObstfeldRogoff.IntertemporalTrade.Investment.no_crowding_out
#print axioms ObstfeldRogoff.IntertemporalTrade.Investment.capital_foc
#print axioms ObstfeldRogoff.IntertemporalTrade.Investment.profit_max_of_deriv_eq
#print axioms ObstfeldRogoff.IntertemporalTrade.Investment.optimal_capital_eq_of_deriv
#print axioms ObstfeldRogoff.IntertemporalTrade.Investment.consumption_foc
#print axioms ObstfeldRogoff.IntertemporalTrade.Investment.ppf
#print axioms ObstfeldRogoff.IntertemporalTrade.Investment.ppf_no_government
#print axioms ObstfeldRogoff.IntertemporalTrade.Investment.consumption2_autarky
#print axioms ObstfeldRogoff.IntertemporalTrade.Investment.autarky_market_clearing
#print axioms ObstfeldRogoff.IntertemporalTrade.Investment.ppf_horizontal_intercept
#print axioms ObstfeldRogoff.IntertemporalTrade.Investment.ppf_vertical_intercept
#print axioms ObstfeldRogoff.IntertemporalTrade.Investment.ppf_shift
#print axioms ObstfeldRogoff.IntertemporalTrade.Investment.ppf_hasDerivAt
#print axioms ObstfeldRogoff.IntertemporalTrade.Investment.ppf_slope_hasDerivAt
#print axioms ObstfeldRogoff.IntertemporalTrade.Investment.ppf_strictConcaveOn
#print axioms ObstfeldRogoff.IntertemporalTrade.Investment.autarky_tangency
#print axioms ObstfeldRogoff.IntertemporalTrade.Investment.gains_from_trade
#print axioms ObstfeldRogoff.IntertemporalTrade.Investment.wealth
#print axioms ObstfeldRogoff.IntertemporalTrade.Investment.consumption2_budget
#print axioms ObstfeldRogoff.IntertemporalTrade.Investment.optimum_solves_wealth_problem
#print axioms ObstfeldRogoff.IntertemporalTrade.Investment.ca1
#print axioms ObstfeldRogoff.IntertemporalTrade.Investment.ca1_eq_currentAccount
#print axioms ObstfeldRogoff.IntertemporalTrade.Investment.consumption_smoothing
#print axioms ObstfeldRogoff.IntertemporalTrade.Investment.ca1_strictAnti_G1
#print axioms ObstfeldRogoff.IntertemporalTrade.Investment.temporary_G1_deficit
#print axioms ObstfeldRogoff.IntertemporalTrade.Investment.ca1_strictMono_G2
#print axioms ObstfeldRogoff.IntertemporalTrade.Investment.future_G2_surplus
#print axioms ObstfeldRogoff.IntertemporalTrade.Isoelastic.eis
#print axioms ObstfeldRogoff.IntertemporalTrade.Isoelastic.isoU
#print axioms ObstfeldRogoff.IntertemporalTrade.Isoelastic.hasDerivAt_isoU
#print axioms ObstfeldRogoff.IntertemporalTrade.Isoelastic.deriv_isoU_eventuallyEq
#print axioms ObstfeldRogoff.IntertemporalTrade.Isoelastic.deriv_deriv_isoU
#print axioms ObstfeldRogoff.IntertemporalTrade.Isoelastic.eis_isoU
#print axioms ObstfeldRogoff.IntertemporalTrade.Isoelastic.tendsto_normalised_isoU_log
#print axioms ObstfeldRogoff.IntertemporalTrade.Isoelastic.eq_affine_isoU_of_eis_const
#print axioms ObstfeldRogoff.IntertemporalTrade.Isoelastic.euler_iff_growth
#print axioms ObstfeldRogoff.IntertemporalTrade.Isoelastic.consC1
#print axioms ObstfeldRogoff.IntertemporalTrade.Isoelastic.consC2
#print axioms ObstfeldRogoff.IntertemporalTrade.Isoelastic.euler_budget_iff_closed_form
#print axioms ObstfeldRogoff.IntertemporalTrade.Isoelastic.log_growth_isoelastic
#print axioms ObstfeldRogoff.IntertemporalTrade.Isoelastic.log_euler_budget_iff
#print axioms ObstfeldRogoff.IntertemporalTrade.Isoelastic.consC1_log
#print axioms ObstfeldRogoff.IntertemporalTrade.Isoelastic.consC2_log_share
#print axioms ObstfeldRogoff.IntertemporalTrade.Isoelastic.hasDerivAt_consC1
#print axioms ObstfeldRogoff.IntertemporalTrade.Isoelastic.deriv_consC1_neg_of_borrower
#print axioms ObstfeldRogoff.IntertemporalTrade.Isoelastic.dC1_dr_general
#print axioms ObstfeldRogoff.IntertemporalTrade.Isoelastic.general_formula_eq_isoelastic
#print axioms ObstfeldRogoff.IntertemporalTrade.Isoelastic.ex3_capital_iff
#print axioms ObstfeldRogoff.IntertemporalTrade.Isoelastic.ex3_consumption
#print axioms ObstfeldRogoff.IntertemporalTrade.Isoelastic.ex4_growth_tendsto_one
#print axioms ObstfeldRogoff.IntertemporalTrade.Isoelastic.ex4_consC1_tendsto
#print axioms ObstfeldRogoff.IntertemporalTrade.Isoelastic.ex4_flat
#print axioms ObstfeldRogoff.IntertemporalTrade.Isoelastic.ex4_hasDerivAt
#print axioms ObstfeldRogoff.IntertemporalTrade.Isoelastic.ex4d_euler_iff
#print axioms ObstfeldRogoff.IntertemporalTrade.Isoelastic.ex4d_ratio_tendsto
#print axioms ObstfeldRogoff.IntertemporalTrade.Isoelastic.ex7_euler_iff
#print axioms ObstfeldRogoff.IntertemporalTrade.Isoelastic.caraC1
#print axioms ObstfeldRogoff.IntertemporalTrade.Isoelastic.ex7_euler_budget_iff
#print axioms ObstfeldRogoff.IntertemporalTrade.Isoelastic.ex7_hasDerivAt
#print axioms ObstfeldRogoff.IntertemporalTrade.Isoelastic.ex7_eis
#print axioms ObstfeldRogoff.IntertemporalTrade.Isoelastic.ex7_hasDerivAt_eis
#print axioms ObstfeldRogoff.IntertemporalTrade.WorldEquilibrium.IsEquilibrium
#print axioms ObstfeldRogoff.IntertemporalTrade.WorldEquilibrium.walras_law
#print axioms ObstfeldRogoff.IntertemporalTrade.WorldEquilibrium.rate_between_autarky
#print axioms ObstfeldRogoff.IntertemporalTrade.WorldEquilibrium.trade_pattern
#print axioms ObstfeldRogoff.IntertemporalTrade.WorldEquilibrium.continuousAt_optimal_c1
#print axioms ObstfeldRogoff.IntertemporalTrade.WorldEquilibrium.exists_autarkyRate
#print axioms ObstfeldRogoff.IntertemporalTrade.WorldEquilibrium.exists_optimal_selection
#print axioms ObstfeldRogoff.IntertemporalTrade.WorldEquilibrium.exists_equilibrium_of_le
#print axioms ObstfeldRogoff.IntertemporalTrade.WorldEquilibrium.exists_equilibrium
#print axioms ObstfeldRogoff.IntertemporalTrade.WorldEquilibrium.cost_ge_of_utility_ge
#print axioms ObstfeldRogoff.IntertemporalTrade.WorldEquilibrium.cost_gt_of_utility_gt
#print axioms ObstfeldRogoff.IntertemporalTrade.WorldEquilibrium.first_welfare_theorem
#print axioms ObstfeldRogoff.IntertemporalTrade.WorldEquilibrium.logC1
#print axioms ObstfeldRogoff.IntertemporalTrade.WorldEquilibrium.log_saving
#print axioms ObstfeldRogoff.IntertemporalTrade.WorldEquilibrium.log_equilibrium_iff
#print axioms ObstfeldRogoff.IntertemporalTrade.WorldEquilibrium.mediant_between
#print axioms ObstfeldRogoff.IntertemporalTrade.WorldEquilibrium.log_rate_between
#print axioms ObstfeldRogoff.IntertemporalTrade.WorldEquilibrium.logWelfare
#print axioms ObstfeldRogoff.IntertemporalTrade.WorldEquilibrium.hasDerivAt_logWelfare
#print axioms ObstfeldRogoff.IntertemporalTrade.WorldEquilibrium.logGrossRate
#print axioms ObstfeldRogoff.IntertemporalTrade.WorldEquilibrium.logGrossRate_anti_Y1
#print axioms ObstfeldRogoff.IntertemporalTrade.WorldEquilibrium.logGrossRate_mono_Y2
#print axioms ObstfeldRogoff.IntertemporalTrade.WorldEquilibrium.logGrossRate_comm
#print axioms ObstfeldRogoff.IntertemporalTrade.WorldEquilibrium.logGrossRate_anti_Y1s
#print axioms ObstfeldRogoff.IntertemporalTrade.WorldEquilibrium.logGrossRate_mono_Y2s
#print axioms ObstfeldRogoff.IntertemporalTrade.WorldEquilibrium.hasDerivAt_capital_productivity
#print axioms ObstfeldRogoff.IntertemporalTrade.WorldEquilibrium.capital_increasing_in_productivity
#print axioms ObstfeldRogoff.IntertemporalTrade.WorldEquilibrium.blanchard_summers
#print axioms ObstfeldRogoff.IntertemporalTrade.Duality.ExpenditureSystem
#print axioms ObstfeldRogoff.IntertemporalTrade.Duality.ExpenditureSystem.mk
#print axioms ObstfeldRogoff.IntertemporalTrade.Duality.ExpenditureSystem.V
#print axioms ObstfeldRogoff.IntertemporalTrade.Duality.ExpenditureSystem.Uset
#print axioms ObstfeldRogoff.IntertemporalTrade.Duality.ExpenditureSystem.E
#print axioms ObstfeldRogoff.IntertemporalTrade.Duality.ExpenditureSystem.C1H
#print axioms ObstfeldRogoff.IntertemporalTrade.Duality.ExpenditureSystem.C2H
#print axioms ObstfeldRogoff.IntertemporalTrade.Duality.ExpenditureSystem.le_cost
#print axioms ObstfeldRogoff.IntertemporalTrade.Duality.ExpenditureSystem.C1H_pos
#print axioms ObstfeldRogoff.IntertemporalTrade.Duality.ExpenditureSystem.C2H_pos
#print axioms ObstfeldRogoff.IntertemporalTrade.Duality.ExpenditureSystem.attains
#print axioms ObstfeldRogoff.IntertemporalTrade.Duality.ExpenditureSystem.cost_eq
#print axioms ObstfeldRogoff.IntertemporalTrade.Duality.hasDerivAt_along_path
#print axioms ObstfeldRogoff.IntertemporalTrade.Duality.ExpenditureSystem.E_le_hicksian_cost
#print axioms ObstfeldRogoff.IntertemporalTrade.Duality.ExpenditureSystem.shephard
#print axioms ObstfeldRogoff.IntertemporalTrade.Duality.ExpenditureSystem.C1H_eq_E_sub
#print axioms ObstfeldRogoff.IntertemporalTrade.Duality.ExpenditureSystem.hasDerivAt_E_of_hicksian
#print axioms ObstfeldRogoff.IntertemporalTrade.Duality.ExpenditureSystem.hicksian_tangency
#print axioms ObstfeldRogoff.IntertemporalTrade.Duality.ExpenditureSystem.welfare_effect
#print axioms ObstfeldRogoff.IntertemporalTrade.Duality.ExpenditureSystem.welfare_rises_iff
#print axioms ObstfeldRogoff.IntertemporalTrade.Duality.ExpenditureSystem.slutsky
#print axioms ObstfeldRogoff.IntertemporalTrade.Duality.ExpenditureSystem.total_effect
#print axioms ObstfeldRogoff.IntertemporalTrade.Duality.Iso.u
#print axioms ObstfeldRogoff.IntertemporalTrade.Duality.Iso.D
#print axioms ObstfeldRogoff.IntertemporalTrade.Duality.Iso.C1H
#print axioms ObstfeldRogoff.IntertemporalTrade.Duality.Iso.C2H
#print axioms ObstfeldRogoff.IntertemporalTrade.Duality.Iso.E
#print axioms ObstfeldRogoff.IntertemporalTrade.Duality.Iso.C1M
#print axioms ObstfeldRogoff.IntertemporalTrade.Duality.Iso.C2M
#print axioms ObstfeldRogoff.IntertemporalTrade.Duality.Iso.D_pos
#print axioms ObstfeldRogoff.IntertemporalTrade.Duality.Iso.mul_rpow_neg
#print axioms ObstfeldRogoff.IntertemporalTrade.Duality.Iso.rpow_div_le_tangent
#print axioms ObstfeldRogoff.IntertemporalTrade.Duality.Iso.u_le_tangent
#print axioms ObstfeldRogoff.IntertemporalTrade.Duality.Iso.C1H_pos
#print axioms ObstfeldRogoff.IntertemporalTrade.Duality.Iso.C2H_pos
#print axioms ObstfeldRogoff.IntertemporalTrade.Duality.Iso.C1H_rpow
#print axioms ObstfeldRogoff.IntertemporalTrade.Duality.Iso.utility_hicksian
#print axioms ObstfeldRogoff.IntertemporalTrade.Duality.Iso.euler_hicksian
#print axioms ObstfeldRogoff.IntertemporalTrade.Duality.Iso.cost_hicksian
#print axioms ObstfeldRogoff.IntertemporalTrade.Duality.Iso.le_cost
#print axioms ObstfeldRogoff.IntertemporalTrade.Duality.Iso.system
#print axioms ObstfeldRogoff.IntertemporalTrade.Duality.Iso.hasDerivAt_D
#print axioms ObstfeldRogoff.IntertemporalTrade.Duality.Iso.hasDerivAt_C1H
#print axioms ObstfeldRogoff.IntertemporalTrade.Duality.Iso.shephard_iso
#print axioms ObstfeldRogoff.IntertemporalTrade.Duality.Iso.C1H_eq_E_sub_iso
#print axioms ObstfeldRogoff.IntertemporalTrade.Duality.Iso.duality_identity_iso
#print axioms ObstfeldRogoff.IntertemporalTrade.Duality.Iso.marshallian_budget
#print axioms ObstfeldRogoff.IntertemporalTrade.Duality.Iso.C1M_eq_eq26
#print axioms ObstfeldRogoff.IntertemporalTrade.Duality.Iso.hasDerivAt_C1M_R
#print axioms ObstfeldRogoff.IntertemporalTrade.Duality.Iso.hasDerivAt_C1M_W
#print axioms ObstfeldRogoff.IntertemporalTrade.Duality.Iso.slutsky_iso
#print axioms ObstfeldRogoff.IntertemporalTrade.Duality.Iso.hasDerivAt_C1_total
#print axioms ObstfeldRogoff.IntertemporalTrade.Duality.Iso.hasDerivAt_C1_total_euler
#print axioms ObstfeldRogoff.IntertemporalTrade.Duality.Iso.hasDerivAt_C1_r_eq24
#print axioms ObstfeldRogoff.IntertemporalTrade.Duality.Iso.hasFDerivAt_C1M
#print axioms ObstfeldRogoff.IntertemporalTrade.Duality.Iso.total_effect_iso
#print axioms ObstfeldRogoff.IntertemporalTrade.OptimalTax.Foreign
#print axioms ObstfeldRogoff.IntertemporalTrade.OptimalTax.Foreign.mk
#print axioms ObstfeldRogoff.IntertemporalTrade.OptimalTax.Foreign.β
#print axioms ObstfeldRogoff.IntertemporalTrade.OptimalTax.Foreign.Y1
#print axioms ObstfeldRogoff.IntertemporalTrade.OptimalTax.Foreign.Y2
#print axioms ObstfeldRogoff.IntertemporalTrade.OptimalTax.Foreign.β_pos
#print axioms ObstfeldRogoff.IntertemporalTrade.OptimalTax.Foreign.Y1_pos
#print axioms ObstfeldRogoff.IntertemporalTrade.OptimalTax.Foreign.Y2_pos
#print axioms ObstfeldRogoff.IntertemporalTrade.OptimalTax.Foreign.saving
#print axioms ObstfeldRogoff.IntertemporalTrade.OptimalTax.Foreign.autarkyGross
#print axioms ObstfeldRogoff.IntertemporalTrade.OptimalTax.Foreign.household
#print axioms ObstfeldRogoff.IntertemporalTrade.OptimalTax.Foreign.household_optimal
#print axioms ObstfeldRogoff.IntertemporalTrade.OptimalTax.Foreign.saving_pos_iff
#print axioms ObstfeldRogoff.IntertemporalTrade.OptimalTax.Foreign.denom
#print axioms ObstfeldRogoff.IntertemporalTrade.OptimalTax.Foreign.rate
#print axioms ObstfeldRogoff.IntertemporalTrade.OptimalTax.Foreign.offer
#print axioms ObstfeldRogoff.IntertemporalTrade.OptimalTax.Foreign.market_clearing_iff
#print axioms ObstfeldRogoff.IntertemporalTrade.OptimalTax.Foreign.denom_pos_of_clearing
#print axioms ObstfeldRogoff.IntertemporalTrade.OptimalTax.Foreign.offer_eq_budget
#print axioms ObstfeldRogoff.IntertemporalTrade.OptimalTax.Foreign.offer_endowment
#print axioms ObstfeldRogoff.IntertemporalTrade.OptimalTax.Foreign.rate_endowment
#print axioms ObstfeldRogoff.IntertemporalTrade.OptimalTax.Foreign.hasDerivAt_offer
#print axioms ObstfeldRogoff.IntertemporalTrade.OptimalTax.Foreign.offer_slope_endowment
#print axioms ObstfeldRogoff.IntertemporalTrade.OptimalTax.Foreign.offer_eq_alt
#print axioms ObstfeldRogoff.IntertemporalTrade.OptimalTax.Foreign.convex_denom_pos
#print axioms ObstfeldRogoff.IntertemporalTrade.OptimalTax.Foreign.offer_strictConcaveOn
#print axioms ObstfeldRogoff.IntertemporalTrade.OptimalTax.Foreign.offer_strictAntiOn
#print axioms ObstfeldRogoff.IntertemporalTrade.OptimalTax.Foreign.rate_strictMonoOn
#print axioms ObstfeldRogoff.IntertemporalTrade.OptimalTax.IsLaissezFaire
#print axioms ObstfeldRogoff.IntertemporalTrade.OptimalTax.laissezFaire_on_offer
#print axioms ObstfeldRogoff.IntertemporalTrade.OptimalTax.deriv_anti
#print axioms ObstfeldRogoff.IntertemporalTrade.OptimalTax.laissezFaire_borrows
#print axioms ObstfeldRogoff.IntertemporalTrade.OptimalTax.laissezFaire_rate_gt
#print axioms ObstfeldRogoff.IntertemporalTrade.OptimalTax.offer_above_laissezFaire_line
#print axioms ObstfeldRogoff.IntertemporalTrade.OptimalTax.PlannerFeasible
#print axioms ObstfeldRogoff.IntertemporalTrade.OptimalTax.IsPlannerOptimal
#print axioms ObstfeldRogoff.IntertemporalTrade.OptimalTax.offerMRS
#print axioms ObstfeldRogoff.IntertemporalTrade.OptimalTax.hasDerivAt_utility_offer
#print axioms ObstfeldRogoff.IntertemporalTrade.OptimalTax.planner_tangency
#print axioms ObstfeldRogoff.IntertemporalTrade.OptimalTax.plannerOptimal_of_tangency
#print axioms ObstfeldRogoff.IntertemporalTrade.OptimalTax.planner_between
#print axioms ObstfeldRogoff.IntertemporalTrade.OptimalTax.rate_ordering
#print axioms ObstfeldRogoff.IntertemporalTrade.OptimalTax.optimalTax
#print axioms ObstfeldRogoff.IntertemporalTrade.OptimalTax.optimalTax_eq
#print axioms ObstfeldRogoff.IntertemporalTrade.OptimalTax.optimalTax_pos
#print axioms ObstfeldRogoff.IntertemporalTrade.OptimalTax.ResidentOptimal
#print axioms ObstfeldRogoff.IntertemporalTrade.OptimalTax.tax_decentralises
#print axioms ObstfeldRogoff.IntertemporalTrade.OptimalTax.home_gains
#print axioms ObstfeldRogoff.IntertemporalTrade.OptimalTax.utility_lt_of_lender
#print axioms ObstfeldRogoff.IntertemporalTrade.OptimalTax.foreign_loses
#print axioms ObstfeldRogoff.IntertemporalTrade.OptimalTax.eventually_gt_of_hasDerivAt_pos
#print axioms ObstfeldRogoff.IntertemporalTrade.OptimalTax.exists_pareto_improvement
#print axioms ObstfeldRogoff.IntertemporalTrade.OptimalTax.foreign_mrs
#print axioms ObstfeldRogoff.IntertemporalTrade.OptimalTax.tax_equilibrium_pareto_inefficient
#print axioms ObstfeldRogoff.IntertemporalTrade.OptimalTax.small_country_zero_tax
#print axioms ObstfeldRogoff.IntertemporalTrade.OptimalTax.Foreign.scale
#print axioms ObstfeldRogoff.IntertemporalTrade.OptimalTax.Foreign.autarkyGross_scale
#print axioms ObstfeldRogoff.IntertemporalTrade.OptimalTax.Foreign.tendsto_denom_scale
#print axioms ObstfeldRogoff.IntertemporalTrade.OptimalTax.Foreign.tendsto_rate_scale
#print axioms ObstfeldRogoff.IntertemporalTrade.OptimalTax.Foreign.tendsto_optimalTax_scale
#print axioms ObstfeldRogoff.IntertemporalTrade.OptimalTax.Foreign.saving_neg_iff
#print axioms ObstfeldRogoff.IntertemporalTrade.OptimalTax.laissezFaire_lends
#print axioms ObstfeldRogoff.IntertemporalTrade.OptimalTax.planner_between_lend
#print axioms ObstfeldRogoff.IntertemporalTrade.OptimalTax.optimalTax_neg
#print axioms ObstfeldRogoff.IntertemporalTrade.OptimalTax.elasticity_sub_one
#print axioms ObstfeldRogoff.IntertemporalTrade.OptimalTax.ex8_optimal_tax
#print axioms ObstfeldRogoff.IntertemporalTrade.OptimalTax.ex8_elasticity_gt_one
#print axioms ObstfeldRogoff.IntertemporalTrade.OptimalTax.ex8_elasticity_gt_one_of_supply
#print axioms ObstfeldRogoff.IntertemporalTrade.LabourMobility.euler_of_homogeneous
#print axioms ObstfeldRogoff.IntertemporalTrade.LabourMobility.prod
#print axioms ObstfeldRogoff.IntertemporalTrade.LabourMobility.prod_homogeneous
#print axioms ObstfeldRogoff.IntertemporalTrade.LabourMobility.hasDerivAt_prod_capital
#print axioms ObstfeldRogoff.IntertemporalTrade.LabourMobility.hasDerivAt_prod_labour
#print axioms ObstfeldRogoff.IntertemporalTrade.LabourMobility.prod_eq_euler
#print axioms ObstfeldRogoff.IntertemporalTrade.LabourMobility.consumption2
#print axioms ObstfeldRogoff.IntertemporalTrade.LabourMobility.lifetimeUtility
#print axioms ObstfeldRogoff.IntertemporalTrade.LabourMobility.hasDerivAt_lifetimeUtility_capital
#print axioms ObstfeldRogoff.IntertemporalTrade.LabourMobility.hasDerivAt_lifetimeUtility_labour
#print axioms ObstfeldRogoff.IntertemporalTrade.LabourMobility.euler_equation
#print axioms ObstfeldRogoff.IntertemporalTrade.LabourMobility.wage_eq_marginal_product
#print axioms ObstfeldRogoff.IntertemporalTrade.LabourMobility.Technology
#print axioms ObstfeldRogoff.IntertemporalTrade.LabourMobility.Technology.mk
#print axioms ObstfeldRogoff.IntertemporalTrade.LabourMobility.Technology.f
#print axioms ObstfeldRogoff.IntertemporalTrade.LabourMobility.Technology.f'
#print axioms ObstfeldRogoff.IntertemporalTrade.LabourMobility.Technology.f''
#print axioms ObstfeldRogoff.IntertemporalTrade.LabourMobility.Technology.continuousOn_f
#print axioms ObstfeldRogoff.IntertemporalTrade.LabourMobility.Technology.hasDerivAt_f
#print axioms ObstfeldRogoff.IntertemporalTrade.LabourMobility.Technology.hasDerivAt_f'
#print axioms ObstfeldRogoff.IntertemporalTrade.LabourMobility.Technology.f''_neg
#print axioms ObstfeldRogoff.IntertemporalTrade.LabourMobility.Technology.f'_strictAntiOn
#print axioms ObstfeldRogoff.IntertemporalTrade.LabourMobility.Technology.f_lt_tangent
#print axioms ObstfeldRogoff.IntertemporalTrade.LabourMobility.Technology.f_le_tangent
#print axioms ObstfeldRogoff.IntertemporalTrade.LabourMobility.Technology.wage
#print axioms ObstfeldRogoff.IntertemporalTrade.LabourMobility.Technology.hasDerivAt_wage
#print axioms ObstfeldRogoff.IntertemporalTrade.LabourMobility.Technology.wage_strictMonoOn
#print axioms ObstfeldRogoff.IntertemporalTrade.LabourMobility.Technology.wageRange
#print axioms ObstfeldRogoff.IntertemporalTrade.LabourMobility.Technology.kOf
#print axioms ObstfeldRogoff.IntertemporalTrade.LabourMobility.Technology.rOf
#print axioms ObstfeldRogoff.IntertemporalTrade.LabourMobility.Technology.kOf_pos
#print axioms ObstfeldRogoff.IntertemporalTrade.LabourMobility.Technology.wage_kOf
#print axioms ObstfeldRogoff.IntertemporalTrade.LabourMobility.Technology.kOf_wage
#print axioms ObstfeldRogoff.IntertemporalTrade.LabourMobility.Technology.kOf_strictMonoOn
#print axioms ObstfeldRogoff.IntertemporalTrade.LabourMobility.Technology.rOf_strictAntiOn
#print axioms ObstfeldRogoff.IntertemporalTrade.LabourMobility.Technology.continuousAt_kOf
#print axioms ObstfeldRogoff.IntertemporalTrade.LabourMobility.Technology.hasDerivAt_kOf
#print axioms ObstfeldRogoff.IntertemporalTrade.LabourMobility.Technology.kOf_slope_pos
#print axioms ObstfeldRogoff.IntertemporalTrade.LabourMobility.Technology.hasDerivAt_rOf
#print axioms ObstfeldRogoff.IntertemporalTrade.LabourMobility.Technology.prod_eq_factor_payments
#print axioms ObstfeldRogoff.IntertemporalTrade.LabourMobility.Technology.prod_le_factor_payments
#print axioms ObstfeldRogoff.IntertemporalTrade.LabourMobility.Technology.prod_lt_factor_payments
#print axioms ObstfeldRogoff.IntertemporalTrade.LabourMobility.Technology.profit_nonpos
#print axioms ObstfeldRogoff.IntertemporalTrade.LabourMobility.Technology.profit_eq_zero_iff
#print axioms ObstfeldRogoff.IntertemporalTrade.LabourMobility.Technology.consumption2_le_gnp
#print axioms ObstfeldRogoff.IntertemporalTrade.LabourMobility.Technology.consumption2_eq_gnp_iff
#print axioms ObstfeldRogoff.IntertemporalTrade.LabourMobility.Technology.ppf
#print axioms ObstfeldRogoff.IntertemporalTrade.LabourMobility.Technology.gnpLine
#print axioms ObstfeldRogoff.IntertemporalTrade.LabourMobility.Technology.gdpLine
#print axioms ObstfeldRogoff.IntertemporalTrade.LabourMobility.Technology.ppf_le_gnpLine
#print axioms ObstfeldRogoff.IntertemporalTrade.LabourMobility.Technology.ppf_eq_gnpLine_iff
#print axioms ObstfeldRogoff.IntertemporalTrade.LabourMobility.Technology.hasDerivAt_ppf
#print axioms ObstfeldRogoff.IntertemporalTrade.LabourMobility.Technology.ppf_tangent_at_B
#print axioms ObstfeldRogoff.IntertemporalTrade.LabourMobility.Technology.gdpLine_eq
#print axioms ObstfeldRogoff.IntertemporalTrade.LabourMobility.Technology.gdpLine_sub_gnpLine
#print axioms ObstfeldRogoff.IntertemporalTrade.LabourMobility.Technology.gnpLine_lt_gdpLine_iff
#print axioms ObstfeldRogoff.IntertemporalTrade.LabourMobility.Technology.autarkyWage
#print axioms ObstfeldRogoff.IntertemporalTrade.LabourMobility.Technology.gross_return_pos_of_euler
#print axioms ObstfeldRogoff.IntertemporalTrade.LabourMobility.Technology.labour_imports_of_autarkyWage_gt
#print axioms ObstfeldRogoff.IntertemporalTrade.LabourMobility.Technology.labour_exports_of_autarkyWage_lt
#print axioms ObstfeldRogoff.IntertemporalTrade.LabourMobility.Technology.autarkyWage_lt_of_saving_lt
#print axioms ObstfeldRogoff.IntertemporalTrade.LabourMobility.Technology.autarkyWage_anti_labour
#print axioms ObstfeldRogoff.IntertemporalTrade.LabourMobility.Technology.autarkyWage_lt_of_more_saving
#print axioms ObstfeldRogoff.IntertemporalTrade.LabourMobility.Technology.netLabourExports_lt_of_labour_lt
#print axioms ObstfeldRogoff.IntertemporalTrade.Stability.zeta
#print axioms ObstfeldRogoff.IntertemporalTrade.Stability.zetaStar
#print axioms ObstfeldRogoff.IntertemporalTrade.Stability.hasDerivAt_netImports
#print axioms ObstfeldRogoff.IntertemporalTrade.Stability.worldExcessSaving_eq
#print axioms ObstfeldRogoff.IntertemporalTrade.Stability.marshall_lerner
#print axioms ObstfeldRogoff.IntertemporalTrade.Stability.stable_iff_marshall_lerner
#print axioms ObstfeldRogoff.IntertemporalTrade.Stability.dC1_neg_of_zero_ca
#print axioms ObstfeldRogoff.IntertemporalTrade.Stability.stable_of_saving_increasing
