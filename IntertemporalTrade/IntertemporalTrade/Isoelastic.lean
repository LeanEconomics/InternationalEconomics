/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Tactic.FieldSimp

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
