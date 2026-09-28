/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Convergence in an overlapping-generations model with credit constraints

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §7.2.2.3
(pp. 469–473) and Exercise 2 (p. 512).

* **The young saver's problem (53)–(56)**, with the constraint `k_{t+1} ≥ 0` that O&R leave
  out made explicit. The optimum is solved in all three cases:
  - `r^D > r`: the borrowing constraint binds, and (57) is the unique optimum;
  - `r^D = r`: the portfolio is indeterminate;
  - `r^D < r`: nothing is invested at home.

  We also prove the Kuhn–Tucker conclusions of fn 29. Without `k ≥ 0` the problem is
  unbounded when `r^D < r`, and with it every equilibrium has `r^D ≥ r`.
* **Equilibrium with full depreciation (58).** Given `k_t`, the equilibrium `k_{t+1}` exists,
  is unique, and equals `min(k̄^U, ψ(k_t))`, where `ψ(k)` is the unique root of the implicit
  equation (58), `x = k^α(P + Q x^{1-α})`. This is proved from the young's optimality
  conditions.
* **Dynamics.** The equilibrium map `Φ` is increasing and `Φ(k)/k` is strictly decreasing,
  so every equilibrium path converges monotonically to `k*`. Here `k* = k̄^D` (59) if the
  non-convergence condition (60) holds and `k* = k̄^U` otherwise. The domestic rate then
  converges to a limit strictly above `r` (under (60)) or equal to `r`.
* **The exact version of (60) and fn 31.** (60) holds iff `D > 0` and `k̄^D < k̄^U`. (59) is
  a steady state only when `D > 0`.
* **Further results.** One-period convergence (Case 3), Case 1, monotonicity in `η`, and the
  reduction at `η = 0` to Solow with `s = (1-α)β/(1+β)`.
* **Exercise 2** (reading `y = A k^α`). After a productivity rise from `r^A = r`, (60) fails
  for every `η ≥ 0`, so the economy always returns to `r^D = r`. It does so in one period iff
  `1 + η(1+β)/β ≥ A^{α/(1-α)}`, and otherwise converges monotonically.

* **General depreciation `0 < δ ≤ 1`.** The constrained equation becomes
  `J(x) = xR^D(x) - wBR^D(x) = wC`, with `J` strictly increasing, so the equilibrium map
  exists, is unique and is `min(k̄^U, ψ_δ(w(k)))`. The growth factor `ψ_δ/k` falls with `k`.
  The steady state exists and is unique, but has no closed form when `δ < 1`. Every
  equilibrium path converges monotonically to it; (60) keeps its form, and Case 3 carries
  over. `δ = 1` is needed only for the closed forms (58)–(59).

The two-country claim on p. 473 ("one can show") is not formalised: it needs a separate
two-country general-equilibrium model that the book does not specify.
-/

namespace ObstfeldRogoff.GlobalGrowth.BorrowingConstrainedOLG

open Filter Topology

/-! ## The domestic interest rate (52) -/

/-- **The domestic interest rate** O&R (52), p. 470: with `y = A k^α` and depreciation `δ`,
the net marginal product of capital is `r^D = αA k^{α-1} - δ`. -/
theorem domestic_rate {A α δ k : ℝ} (hk : 0 < k) :
    HasDerivAt (fun x => A * x ^ α - δ * x) (α * A * k ^ (α - 1) - δ) k := by
  have h : HasDerivAt (fun x => A * x ^ α - δ * x) (A * (α * k ^ (α - 1)) - δ * 1) k :=
    ((Real.hasDerivAt_rpow_const (p := α) (Or.inl hk.ne')).const_mul A).sub
      ((hasDerivAt_id k).const_mul δ)
  convert h using 1
  ring

/-! ## The young saver's problem (53)–(56), with `k_{t+1} ≥ 0` made explicit -/

/-- A **feasible plan of the young** (O&R (53)–(55)): consumption `c^Y > 0`, domestic capital
`k ≥ 0` (a constraint O&R leave implicit), foreign assets `b ≥ -ηw` (55), the first-period
budget `k + b = w - c^Y` (53), and positive old-age consumption
`c^O = R^D k + R b > 0` (54), with gross rates `R^D = 1 + r^D`, `R = 1 + r`. -/
structure Feasible (w η RD R cY k b : ℝ) : Prop where
  posY : 0 < cY
  kNonneg : 0 ≤ k
  borrow : -(η * w) ≤ b
  budget : k + b = w - cY
  posO : 0 < RD * k + R * b

/-- Lifetime utility `log c^Y + β log c^O` of the young (O&R p. 470). -/
noncomputable def utility (β RD R cY k b : ℝ) : ℝ := Real.log cY + β * Real.log (RD * k + R * b)

/-- An **optimal plan** of the young: feasible, and at least as good as every feasible plan. -/
def IsOptimal (β w η RD R cY k b : ℝ) : Prop :=
  Feasible w η RD R cY k b ∧
    ∀ cY' k' b', Feasible w η RD R cY' k' b' → utility β RD R cY' k' b' ≤ utility β RD R cY k b

/-- **The intertemporal budget constraint** O&R (56), p. 470:
`c^Y + c^O/R^D = w - (R^D - R) b / R^D`. -/
theorem intertemporal_budget {w RD R cY k b : ℝ} (hRD : 0 < RD) (hbud : k + b = w - cY) :
    cY + (RD * k + R * b) / RD = w - (RD - R) * b / RD := by
  have : k = w - cY - b := by linarith
  rw [this]
  field_simp
  ring

/-- **The two-period log consumer** (used in all three cases, O&R p. 471): if
`c₁ + c₂/R ≤ W` then `log c₁ + β log c₂ ≤ log(W/(1+β)) + β log(βRW/(1+β))`, with equality
only at `c₁ = W/(1+β)`, `c₂ = βRW/(1+β)` and a binding budget. -/
theorem log_consumer {β R W c₁ c₂ : ℝ} (hβ : 0 < β) (hR : 0 < R) (hW : 0 < W) (hc₁ : 0 < c₁)
    (hc₂ : 0 < c₂) (hbud : c₁ + c₂ / R ≤ W) :
    Real.log c₁ + β * Real.log c₂ ≤
        Real.log (W / (1 + β)) + β * Real.log (β * R * W / (1 + β)) ∧
      (Real.log c₁ + β * Real.log c₂ =
          Real.log (W / (1 + β)) + β * Real.log (β * R * W / (1 + β)) →
        c₁ = W / (1 + β) ∧ c₂ = β * R * W / (1 + β)) := by
  have h1 : 0 < W / (1 + β) := by positivity
  have h2 : 0 < β * R * W / (1 + β) := by positivity
  have l1 := Real.log_le_sub_one_of_pos (div_pos hc₁ h1)
  have l2 := Real.log_le_sub_one_of_pos (div_pos hc₂ h2)
  rw [Real.log_div hc₁.ne' h1.ne'] at l1
  rw [Real.log_div hc₂.ne' h2.ne'] at l2
  have hsum : (c₁ / (W / (1 + β)) - 1) + β * (c₂ / (β * R * W / (1 + β)) - 1) =
      (1 + β) * ((c₁ + c₂ / R) / W - 1) := by
    field_simp
    ring
  have hle : (1 + β) * ((c₁ + c₂ / R) / W - 1) ≤ 0 := by
    apply mul_nonpos_of_nonneg_of_nonpos (by linarith)
    rw [sub_nonpos, div_le_one hW]
    exact hbud
  refine ⟨by nlinarith [mul_le_mul_of_nonneg_left l2 hβ.le], fun heq => ?_⟩
  by_contra hne
  have hstrict : Real.log c₁ - Real.log (W / (1 + β)) +
      β * (Real.log c₂ - Real.log (β * R * W / (1 + β))) <
      (c₁ / (W / (1 + β)) - 1) + β * (c₂ / (β * R * W / (1 + β)) - 1) := by
    by_cases hc1 : c₁ = W / (1 + β)
    · have hc2 : c₂ ≠ β * R * W / (1 + β) := fun h => hne ⟨hc1, h⟩
      have hx : c₂ / (β * R * W / (1 + β)) ≠ 1 := by
        rw [Ne, div_eq_one_iff_eq h2.ne']
        exact hc2
      have l2' := Real.log_lt_sub_one_of_pos (div_pos hc₂ h2) hx
      rw [Real.log_div hc₂.ne' h2.ne'] at l2'
      nlinarith [mul_lt_mul_of_pos_left l2' hβ]
    · have hx : c₁ / (W / (1 + β)) ≠ 1 := by
        rw [Ne, div_eq_one_iff_eq h1.ne']
        exact hc1
      have l1' := Real.log_lt_sub_one_of_pos (div_pos hc₁ h1) hx
      rw [Real.log_div hc₁.ne' h1.ne'] at l1'
      nlinarith [mul_le_mul_of_nonneg_left l2 hβ.le]
  linarith

/-- The optimal plan when the constraint binds (O&R Case 2, p. 471): lifetime income
`W = w + (R^D - R)ηw/R^D`, `c^Y = W/(1+β)`, `b = -ηw`, and domestic capital
`k = w - c^Y + ηw`, which is O&R (57). -/
theorem binding_plan_eq_57 {β w η RD R : ℝ} (hβ : 0 < β) (hRD : 0 < RD) :
    w - (w + (RD - R) * (η * w) / RD) / (1 + β) + η * w =
      (β * (1 + η) / (1 + β) + R * η / ((1 + β) * RD)) * w := by
  have : (1 + β) ≠ 0 := by linarith
  field_simp
  ring

/-- **Case 2: `r^D > r`, the borrowing constraint binds** (O&R p. 471, fn 29). The unique
optimal plan borrows the maximum `b = -ηw`, consumes `c^Y = W/(1+β)` with
`W = w + (R^D - R)ηw/R^D`, and invests `k = w - c^Y + ηw > 0` at home (O&R (57)). -/
theorem optimal_binding {β w η RD R : ℝ} (hβ : 0 < β) (hw : 0 < w) (hη : 0 ≤ η)
    (hR : 0 < R) (hRDR : R < RD) :
    let W := w + (RD - R) * (η * w) / RD
    IsOptimal β w η RD R (W / (1 + β)) (w - W / (1 + β) + η * w) (-(η * w)) ∧
      ∀ cY k b, IsOptimal β w η RD R cY k b →
        cY = W / (1 + β) ∧ k = w - W / (1 + β) + η * w ∧ b = -(η * w) := by
  intro W
  have hRD : 0 < RD := by linarith
  have hW : 0 < W := by
    have : 0 ≤ (RD - R) * (η * w) / RD :=
      div_nonneg (mul_nonneg (by linarith) (mul_nonneg hη hw.le)) hRD.le
    linarith
  have hWle : W ≤ w * (1 + η) := by
    have : (RD - R) * (η * w) / RD ≤ η * w := by
      rw [div_le_iff₀ hRD]
      have := mul_nonneg hη hw.le
      nlinarith
    linarith
  have hk : 0 < w - W / (1 + β) + η * w := by
    have : W / (1 + β) < w * (1 + η) := by
      rw [div_lt_iff₀ (by linarith)]
      nlinarith
    linarith
  have hcO : RD * (w - W / (1 + β) + η * w) + R * -(η * w) = β * RD * W / (1 + β) := by
    simp only [W]
    field_simp
    ring
  have hfeas : Feasible w η RD R (W / (1 + β)) (w - W / (1 + β) + η * w) (-(η * w)) :=
    ⟨by positivity, hk.le, le_rfl, by ring, by rw [hcO]; positivity⟩
  -- every feasible plan has lifetime income at most `W`
  have hbound : ∀ cY k b, Feasible w η RD R cY k b →
      cY + (RD * k + R * b) / RD ≤ W ∧ (b ≠ -(η * w) → cY + (RD * k + R * b) / RD < W) := by
    intro cY k b hf
    rw [intertemporal_budget hRD hf.budget]
    have hb := hf.borrow
    constructor
    · have : -((RD - R) * b / RD) ≤ (RD - R) * (η * w) / RD := by
        rw [neg_div', div_le_div_iff_of_pos_right hRD]
        nlinarith
      simp only [W]
      linarith
    · intro hne
      have hlt : -(η * w) < b := lt_of_le_of_ne hb (Ne.symm hne)
      have : -((RD - R) * b / RD) < (RD - R) * (η * w) / RD := by
        rw [neg_div', div_lt_div_iff_of_pos_right hRD]
        nlinarith
      simp only [W]
      linarith
  have hopt : ∀ cY k b, Feasible w η RD R cY k b →
      utility β RD R cY k b ≤ utility β RD R (W / (1 + β)) (w - W / (1 + β) + η * w)
        (-(η * w)) ∧
      (utility β RD R cY k b = utility β RD R (W / (1 + β)) (w - W / (1 + β) + η * w)
        (-(η * w)) → cY = W / (1 + β) ∧ k = w - W / (1 + β) + η * w ∧ b = -(η * w)) := by
    intro cY k b hf
    obtain ⟨hle, hlt⟩ := hbound cY k b hf
    obtain ⟨hu, heq⟩ := log_consumer hβ hRD hW hf.posY hf.posO hle
    unfold utility
    rw [hcO]
    refine ⟨hu, fun h => ?_⟩
    obtain ⟨h1, h2⟩ := heq h
    have hb : b = -(η * w) := by
      by_contra hne
      have := hlt hne
      rw [h1, h2] at this
      have e : W / (1 + β) + β * RD * W / (1 + β) / RD = W := by
        field_simp
      linarith
    refine ⟨h1, ?_, hb⟩
    have := hf.budget
    linarith
  refine ⟨⟨hfeas, fun cY k b hf => (hopt cY k b hf).1⟩, fun cY k b ho => ?_⟩
  exact (hopt cY k b ho.1).2 (le_antisymm (hopt cY k b ho.1).1 (ho.2 _ _ _ hfeas))

/-- **Case `r^D = r`** (O&R p. 470): the young consume `w/(1+β)` and are indifferent among
all portfolios; any split `k + b = βw/(1+β)` with `k ≥ 0` and `b ≥ -ηw` is optimal. -/
theorem optimal_equal {β w η R k b : ℝ} (hβ : 0 < β) (hw : 0 < w) (hR : 0 < R) (hk : 0 ≤ k)
    (hb : -(η * w) ≤ b) (hsplit : k + b = β * w / (1 + β)) :
    IsOptimal β w η R R (w / (1 + β)) k b := by
  have hcO : R * k + R * b = β * R * w / (1 + β) := by
    rw [← mul_add, hsplit]
    ring
  refine ⟨⟨by positivity, hk, hb, by rw [hsplit]; field_simp; ring, by rw [hcO]; positivity⟩,
    fun cY' k' b' hf => ?_⟩
  have hle : cY' + (R * k' + R * b') / R ≤ w := by
    rw [intertemporal_budget hR hf.budget]
    simp
  have := (log_consumer hβ hR hw hf.posY hf.posO hle).1
  unfold utility
  rw [hcO]
  exact this

/-- **Case `r^D < r`: the young invest nothing at home** (O&R p. 470, made precise with
`k ≥ 0`): the unique optimal plan has `k = 0`, `b = βw/(1+β)`, `c^Y = w/(1+β)`. -/
theorem optimal_lend {β w η RD R : ℝ} (hβ : 0 < β) (hw : 0 < w) (hη : 0 ≤ η) (hRD : 0 < RD)
    (hRDR : RD < R) :
    IsOptimal β w η RD R (w / (1 + β)) 0 (β * w / (1 + β)) ∧
      ∀ cY k b, IsOptimal β w η RD R cY k b →
        cY = w / (1 + β) ∧ k = 0 ∧ b = β * w / (1 + β) := by
  have hR : 0 < R := by linarith
  have hcO : RD * 0 + R * (β * w / (1 + β)) = β * R * w / (1 + β) := by ring
  have hb0 : -(η * w) ≤ β * w / (1 + β) := by
    have : 0 ≤ β * w / (1 + β) := by positivity
    have := mul_nonneg hη hw.le
    linarith
  have hfeas : Feasible w η RD R (w / (1 + β)) 0 (β * w / (1 + β)) :=
    ⟨by positivity, le_rfl, hb0, by field_simp; ring, by rw [hcO]; positivity⟩
  have hkey : ∀ cY k b, Feasible w η RD R cY k b →
      cY + (RD * k + R * b) / R = w - (R - RD) * k / R := by
    intro cY k b hf
    have : b = w - cY - k := by linarith [hf.budget]
    rw [this]
    field_simp
    ring
  have hopt : ∀ cY k b, Feasible w η RD R cY k b →
      utility β RD R cY k b ≤ utility β RD R (w / (1 + β)) 0 (β * w / (1 + β)) ∧
      (utility β RD R cY k b = utility β RD R (w / (1 + β)) 0 (β * w / (1 + β)) →
        cY = w / (1 + β) ∧ k = 0 ∧ b = β * w / (1 + β)) := by
    intro cY k b hf
    have hle : cY + (RD * k + R * b) / R ≤ w := by
      rw [hkey cY k b hf]
      have : 0 ≤ (R - RD) * k / R := div_nonneg (mul_nonneg (by linarith) hf.kNonneg) hR.le
      linarith
    obtain ⟨hu, heq⟩ := log_consumer hβ hR hw hf.posY hf.posO hle
    unfold utility
    rw [hcO]
    refine ⟨hu, fun h => ?_⟩
    obtain ⟨h1, h2⟩ := heq h
    have hk0 : k = 0 := by
      have e := hkey cY k b hf
      rw [h1, h2] at e
      have : (R - RD) * k / R = 0 := by
        field_simp at e
        field_simp
        nlinarith
      rcases (div_eq_zero_iff.mp this) with h | h
      · rcases mul_eq_zero.mp h with h' | h'
        · linarith
        · exact h'
      · linarith
    refine ⟨h1, hk0, ?_⟩
    have := hf.budget
    rw [hk0, h1] at this
    field_simp at this ⊢
    linarith
  refine ⟨⟨hfeas, fun cY k b hf => (hopt cY k b hf).1⟩, fun cY k b ho => ?_⟩
  exact (hopt cY k b ho.1).2 (le_antisymm (hopt cY k b ho.1).1 (ho.2 _ _ _ hfeas))

/-- **Flag (O&R (53)–(55) omit `k ≥ 0`)**: without the nonnegativity of domestic capital and
with `r^D < r`, the young's problem is unbounded — borrowing domestically (`k → -∞`) to lend
abroad yields arbitrarily high utility, so no optimum exists. -/
theorem unbounded_without_k_nonneg {β w η RD R : ℝ} (hβ : 0 < β) (hw : 0 < w) (hη : 0 ≤ η)
    (hRDR : RD < R) (M : ℝ) :
    ∃ cY k b, 0 < cY ∧ -(η * w) ≤ b ∧ k + b = w - cY ∧ 0 < RD * k + R * b ∧
      M < utility β RD R cY k b := by
  set cY := w / 2
  set x := (Real.exp ((|M| + 1 - Real.log cY) / β) + |RD * (w - cY)|) / (R - RD)
  have hx : 0 ≤ x := by positivity
  have hcO : RD * (w - cY - x) + R * x = RD * (w - cY) + (R - RD) * x := by ring
  have hcO' : RD * (w - cY) + (R - RD) * x =
      RD * (w - cY) + (Real.exp ((|M| + 1 - Real.log cY) / β) + |RD * (w - cY)|) := by
    have hne : R - RD ≠ 0 := by linarith
    simp only [x]
    field_simp
  have hge : Real.exp ((|M| + 1 - Real.log cY) / β) ≤ RD * (w - cY) + (R - RD) * x := by
    rw [hcO']
    linarith [neg_abs_le (RD * (w - cY))]
  refine ⟨cY, w - cY - x, x, by positivity, by nlinarith, by ring, by
    rw [hcO]; linarith [Real.exp_pos ((|M| + 1 - Real.log cY) / β)], ?_⟩
  unfold utility
  rw [hcO]
  have hlog : (|M| + 1 - Real.log cY) / β ≤ Real.log (RD * (w - cY) + (R - RD) * x) := by
    rw [Real.le_log_iff_exp_le (by linarith [Real.exp_pos ((|M| + 1 - Real.log cY) / β)])]
    exact hge
  have := mul_le_mul_of_nonneg_left hlog hβ.le
  rw [mul_div_cancel₀ _ hβ.ne'] at this
  linarith [le_abs_self M]

/-- **In equilibrium `r^D ≥ r`** (O&R p. 470, which needs `k ≥ 0` for this): if an optimal
plan of the young invests `k > 0` at home, then `R^D ≥ R`. -/
theorem rate_ge_of_optimal {β w η RD R cY k b : ℝ} (hβ : 0 < β) (hw : 0 < w) (hη : 0 ≤ η)
    (hRD : 0 < RD) (ho : IsOptimal β w η RD R cY k b) (hk : 0 < k) : R ≤ RD := by
  by_contra hlt
  push Not at hlt
  have := ((optimal_lend hβ hw hη hRD hlt).2 cY k b ho).2.1
  linarith

/-- **Kuhn–Tucker, O&R fn 29**: at any optimum with `r^D > r` the constraint binds
(`ηw + b = 0`); at any optimum with `r^D < r` nothing is invested at home. -/
theorem kuhn_tucker {β w η RD R cY k b : ℝ} (hβ : 0 < β) (hw : 0 < w) (hη : 0 ≤ η)
    (hR : 0 < R) (hRD : 0 < RD) (ho : IsOptimal β w η RD R cY k b) :
    (R < RD → η * w + b = 0) ∧ (RD < R → k = 0) := by
  constructor
  · intro h
    have := ((optimal_binding hβ hw hη hR h).2 cY k b ho).2.2
    linarith
  · intro h
    exact ((optimal_lend hβ hw hη hRD h).2 cY k b ho).2.1

/-! ## Equilibrium with full depreciation: the implicit map (57)–(58) -/

/-- The wage of the young, `w_t = (1-α) A k_t^α` (O&R p. 471; productivity `A` for
Exercise 2). -/
noncomputable def wage (A α k : ℝ) : ℝ := (1 - α) * A * k ^ α

/-- Coefficient `P = (1-α)Aβ(1+η)/(1+β)` of the rewritten (58). -/
noncomputable def coefP (A α β η : ℝ) : ℝ := (1 - α) * A * β * (1 + η) / (1 + β)

/-- Coefficient `Q = (1-α)(1+r)η/((1+β)α)` of the rewritten (58). -/
noncomputable def coefQ (α β η r : ℝ) : ℝ := (1 - α) * (1 + r) * η / ((1 + β) * α)

/-- The unconstrained capital stock `k̄^U`, where `r^D = r`: `αA (k̄^U)^{α-1} = 1 + r`. -/
noncomputable def kU (A α r : ℝ) : ℝ := (α * A / (1 + r)) ^ (1 / (1 - α))

/-- `H(x) = x/(P + Q x^{1-α})`: (58) reads `H(k_{t+1}) = k_t^α`. -/
noncomputable def Hmap (P Q α x : ℝ) : ℝ := x / (P + Q * x ^ (1 - α))

/-- **Equilibrium next-period capital** (O&R §7.2.2.3, δ = 1): given `k`, the capital stock `x`
is an equilibrium if some optimal plan of the young at the wage `w(k)` and the domestic rate
`1 + r^D = αA x^{α-1}` invests exactly `x` at home. -/
def EqRel (β η r A α k x : ℝ) : Prop :=
  ∃ cY b, IsOptimal β (wage A α k) η (α * A * x ^ (α - 1)) (1 + r) cY x b


/-- `k̄^U > 0`. -/
theorem kU_pos {A α r : ℝ} (hα : 0 < α) (hA : 0 < A) (hr : 0 < 1 + r) : 0 < kU A α r :=
  Real.rpow_pos_of_pos (by positivity) _

/-- `(k̄^U)^{1-α} = αA/(1+r)`. -/
theorem kU_rpow {A α r : ℝ} (hα : 0 < α) (hα1 : α < 1) (hA : 0 < A) (hr : 0 < 1 + r) :
    kU A α r ^ (1 - α) = α * A / (1 + r) := by
  unfold kU
  rw [← Real.rpow_mul (by positivity), one_div_mul_cancel (by linarith), Real.rpow_one]

/-- At `k̄^U` the domestic and world rates coincide: `αA (k̄^U)^{α-1} = 1 + r`. -/
theorem kU_rate {A α r : ℝ} (hα : 0 < α) (hα1 : α < 1) (hA : 0 < A) (hr : 0 < 1 + r) :
    α * A * kU A α r ^ (α - 1) = 1 + r := by
  rw [show α - 1 = -(1 - α) by ring, Real.rpow_neg (kU_pos hα hA hr).le,
    kU_rpow hα hα1 hA hr, inv_div]
  field_simp

/-- `r^D > r` iff capital is below `k̄^U` (the marginal product is decreasing). -/
theorem rate_gt_iff {A α r x : ℝ} (hα : 0 < α) (hα1 : α < 1) (hA : 0 < A) (hr : 0 < 1 + r)
    (hx : 0 < x) : 1 + r < α * A * x ^ (α - 1) ↔ x < kU A α r := by
  have hU := kU_pos hα hA hr
  rw [← kU_rate hα hα1 hA hr]
  constructor
  · intro h
    by_contra hle
    push Not at hle
    have := Real.rpow_le_rpow_of_nonpos hU hle (by linarith : α - 1 ≤ 0)
    have : α * A * x ^ (α - 1) ≤ α * A * kU A α r ^ (α - 1) :=
      mul_le_mul_of_nonneg_left this (by positivity)
    linarith
  · intro h
    have := Real.rpow_lt_rpow_of_neg hx h (by linarith : α - 1 < 0)
    exact mul_lt_mul_of_pos_left this (by positivity)

/-- `r^D = r` iff `x = k̄^U`. -/
theorem rate_eq_iff {A α r x : ℝ} (hα : 0 < α) (hα1 : α < 1) (hA : 0 < A) (hr : 0 < 1 + r)
    (hx : 0 < x) : α * A * x ^ (α - 1) = 1 + r ↔ x = kU A α r := by
  have hU := kU_pos hα hA hr
  constructor
  · intro h
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · linarith [(rate_gt_iff hα hα1 hA hr hx).mpr hlt]
    · have := Real.rpow_lt_rpow_of_neg hU hgt (by linarith : α - 1 < 0)
      have := mul_lt_mul_of_pos_left this (by positivity : 0 < α * A)
      rw [kU_rate hα hα1 hA hr] at this
      linarith
  · intro h
    rw [h, kU_rate hα hα1 hA hr]

/-- **(57) in terms of `k_{t+1}`: O&R (58) with productivity `A`**: with
`1 + r^D = αA x^{α-1}` and `w = (1-α)Ak^α`, the right side of (57) equals
`k^α (P + Q x^{1-α})`. -/
theorem eq57_eq {A α β η r k x : ℝ} (hα : 0 < α) (hA : 0 < A) (hβ : 0 < β) (hx : 0 < x) :
    (β * (1 + η) / (1 + β) + (1 + r) * η / ((1 + β) * (α * A * x ^ (α - 1)))) *
        wage A α k = k ^ α * (coefP A α β η + coefQ α β η r * x ^ (1 - α)) := by
  unfold wage coefP coefQ
  have hxa : x ^ (α - 1) * x ^ (1 - α) = 1 := by
    rw [← Real.rpow_add hx, show α - 1 + (1 - α) = 0 by ring, Real.rpow_zero]
  have hxp : 0 < x ^ (α - 1) := Real.rpow_pos_of_pos hx _
  have e : x ^ (1 - α) = (x ^ (α - 1))⁻¹ := eq_inv_of_mul_eq_one_right hxa
  rw [e]
  field_simp

/-- `H` is strictly increasing on `(0, ∞)` when `P > 0`, `Q ≥ 0`. -/
theorem Hmap_strictMonoOn {P Q α : ℝ} (hP : 0 < P) (hQ : 0 ≤ Q) (hα : 0 < α) (hα1 : α < 1) :
    StrictMonoOn (Hmap P Q α) (Set.Ioi 0) := by
  intro x hx y hy hxy
  have hx0 : 0 < x := hx
  have hy0 : 0 < y := hy
  unfold Hmap
  have hpx := Real.rpow_pos_of_pos hx0 (1 - α)
  have hpy := Real.rpow_pos_of_pos hy0 (1 - α)
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  have hsx : x = x ^ α * x ^ (1 - α) := by
    rw [← Real.rpow_add hx0, show α + (1 - α) = 1 by ring, Real.rpow_one]
  have hsy : y = y ^ α * y ^ (1 - α) := by
    rw [← Real.rpow_add hy0, show α + (1 - α) = 1 by ring, Real.rpow_one]
  have hα' : x ^ α < y ^ α := Real.rpow_lt_rpow hx0.le hxy hα
  have hcross : x * y ^ (1 - α) ≤ y * x ^ (1 - α) := by
    conv_lhs => rw [hsx]
    conv_rhs => rw [hsy]
    have := mul_pos hpx hpy
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_left hcross hQ]

/-- `H(x) > 0` for `x > 0`. -/
theorem Hmap_pos {P Q α x : ℝ} (hP : 0 < P) (hQ : 0 ≤ Q) (hx : 0 < x) : 0 < Hmap P Q α x := by
  unfold Hmap
  have := Real.rpow_pos_of_pos hx (1 - α)
  positivity

/-- **(58) has a solution**: for every `k > 0` there is `x > 0` with `H(x) = k^α`
(intermediate value theorem; `H(x) ≤ x/P` near 0 and `H(x) ≥ x^α/(P+Q)` for `x ≥ 1`). -/
theorem Hmap_surj {P Q α k : ℝ} (hP : 0 < P) (hQ : 0 ≤ Q) (hα : 0 < α) (hα1 : α < 1)
    (hk : 0 < k) : ∃ x, 0 < x ∧ Hmap P Q α x = k ^ α := by
  have hka := Real.rpow_pos_of_pos hk α
  set a := P * k ^ α / 2 with ha
  set b := max 1 (((P + Q) * k ^ α) ^ (1 / α)) with hb
  have ha0 : 0 < a := by positivity
  have hb1 : 1 ≤ b := le_max_left _ _
  have hb0 : 0 < b := by linarith
  have hHa : Hmap P Q α a ≤ k ^ α := by
    unfold Hmap
    have := Real.rpow_pos_of_pos ha0 (1 - α)
    rw [div_le_iff₀ (by positivity)]
    simp only [ha]
    nlinarith [mul_nonneg hQ this.le]
  have hHb : k ^ α ≤ Hmap P Q α b := by
    unfold Hmap
    have hbp : 1 ≤ b ^ (1 - α) := Real.one_le_rpow hb1 (by linarith)
    have hbpos := Real.rpow_pos_of_pos hb0 (1 - α)
    have hbα : (P + Q) * k ^ α ≤ b ^ α := by
      have h1 : ((P + Q) * k ^ α) ^ (1 / α) ≤ b := le_max_right _ _
      have h2 := Real.rpow_le_rpow (by positivity) h1 hα.le
      rwa [← Real.rpow_mul (by positivity), one_div_mul_cancel hα.ne', Real.rpow_one] at h2
    have hsb : b = b ^ α * b ^ (1 - α) := by
      rw [← Real.rpow_add hb0, show α + (1 - α) = 1 by ring, Real.rpow_one]
    rw [le_div_iff₀ (by positivity)]
    have : P + Q * b ^ (1 - α) ≤ (P + Q) * b ^ (1 - α) := by nlinarith
    calc k ^ α * (P + Q * b ^ (1 - α)) ≤ k ^ α * ((P + Q) * b ^ (1 - α)) :=
          mul_le_mul_of_nonneg_left this hka.le
      _ = (P + Q) * k ^ α * b ^ (1 - α) := by ring
      _ ≤ b ^ α * b ^ (1 - α) := mul_le_mul_of_nonneg_right hbα hbpos.le
      _ = b := hsb.symm
  have hsub : Set.uIcc a b ⊆ Set.Ioi 0 := fun z hz => by
    rcases Set.mem_uIcc.mp hz with ⟨h1, _⟩ | ⟨h1, _⟩
    · exact lt_of_lt_of_le ha0 h1
    · exact lt_of_lt_of_le hb0 h1
  have hcont : ContinuousOn (Hmap P Q α) (Set.uIcc a b) := by
    apply ContinuousOn.div continuousOn_id
    · exact (continuous_const.add (continuous_const.mul
        (continuous_id.rpow_const fun _ => Or.inr (by linarith)))).continuousOn
    · intro z hz
      have := Real.rpow_pos_of_pos (hsub hz) (1 - α)
      have : 0 < P + Q * z ^ (1 - α) := by positivity
      exact this.ne'
  obtain ⟨x, hx, hHx⟩ := intermediate_value_uIcc hcont
    (Set.mem_uIcc.mpr (Or.inl ⟨hHa, hHb⟩))
  exact ⟨x, hsub hx, hHx⟩

/-- The solution of (58): `ψ(k)`, the unique `x > 0` with `H(x) = k^α`. -/
noncomputable def psi (P Q α k : ℝ) : ℝ := by
  classical
  exact if h : ∃ x, 0 < x ∧ Hmap P Q α x = k ^ α then h.choose else 0

/-- `ψ(k) > 0` and `H(ψ(k)) = k^α`. -/
theorem psi_spec {P Q α k : ℝ} (hP : 0 < P) (hQ : 0 ≤ Q) (hα : 0 < α) (hα1 : α < 1)
    (hk : 0 < k) : 0 < psi P Q α k ∧ Hmap P Q α (psi P Q α k) = k ^ α := by
  have h := Hmap_surj hP hQ hα hα1 hk
  unfold psi
  split_ifs
  exact h.choose_spec

/-- **(58) has exactly one positive solution**: any `x > 0` with `H(x) = k^α` is `ψ(k)`. -/
theorem psi_unique {P Q α k x : ℝ} (hP : 0 < P) (hQ : 0 ≤ Q) (hα : 0 < α) (hα1 : α < 1)
    (hk : 0 < k) (hx : 0 < x) (hHx : Hmap P Q α x = k ^ α) : x = psi P Q α k := by
  obtain ⟨hp, hHp⟩ := psi_spec hP hQ hα hα1 hk
  exact (Hmap_strictMonoOn hP hQ hα hα1).injOn hx hp (hHx.trans hHp.symm)

/-- The root equation of (58), `x = k^α(P + Q x^{1-α})`, is `H(x) = k^α`. -/
theorem root_iff {P Q α k x : ℝ} (hP : 0 < P) (hQ : 0 ≤ Q) (hx : 0 < x) :
    x = k ^ α * (P + Q * x ^ (1 - α)) ↔ Hmap P Q α x = k ^ α := by
  unfold Hmap
  have := Real.rpow_pos_of_pos hx (1 - α)
  have hd : 0 < P + Q * x ^ (1 - α) := by positivity
  rw [div_eq_iff hd.ne']

/-- `ψ` is strictly increasing (O&R p. 472: the constrained map is increasing). -/
theorem psi_strictMono {P Q α k₁ k₂ : ℝ} (hP : 0 < P) (hQ : 0 ≤ Q) (hα : 0 < α)
    (hα1 : α < 1) (hk₁ : 0 < k₁) (hk : k₁ < k₂) : psi P Q α k₁ < psi P Q α k₂ := by
  obtain ⟨h1, hH1⟩ := psi_spec hP hQ hα hα1 hk₁
  obtain ⟨h2, hH2⟩ := psi_spec hP hQ hα hα1 (hk₁.trans hk)
  by_contra hle
  push Not at hle
  have := (Hmap_strictMonoOn hP hQ hα hα1).monotoneOn h2 h1 hle
  rw [hH1, hH2] at this
  have := Real.rpow_lt_rpow hk₁.le hk hα
  linarith

/-- The growth factor of the constrained map: `(ψ(k)/k)^α = P ψ(k)^{α-1} + Q`. -/
theorem psi_ratio {P Q α k : ℝ} (hP : 0 < P) (hQ : 0 ≤ Q) (hα : 0 < α) (hα1 : α < 1)
    (hk : 0 < k) :
    (psi P Q α k / k) ^ α = P * psi P Q α k ^ (α - 1) + Q := by
  obtain ⟨hx, hH⟩ := psi_spec hP hQ hα hα1 hk
  set x := psi P Q α k
  have hroot := (root_iff hP hQ hx).mpr hH
  have hka := Real.rpow_pos_of_pos hk α
  have hxa : x ^ (α - 1) * x ^ (1 - α) = 1 := by
    rw [← Real.rpow_add hx, show α - 1 + (1 - α) = 0 by ring, Real.rpow_zero]
  have hxx : x ^ α = x ^ (α - 1) * x := by
    rw [show α = (α - 1) + 1 by ring, Real.rpow_add hx, Real.rpow_one]
    ring_nf
  rw [Real.div_rpow hx.le hk.le, div_eq_iff hka.ne', hxx]
  have h2 : x ^ (α - 1) * x = x ^ (α - 1) * (k ^ α * (P + Q * x ^ (1 - α))) := by
    rw [← hroot]
  linear_combination h2 + (k ^ α * Q) * hxa

/-- **The growth factor falls with capital**: `ψ(k₂)/k₂ < ψ(k₁)/k₁` for `k₁ < k₂`. -/
theorem psi_ratio_anti {P Q α k₁ k₂ : ℝ} (hP : 0 < P) (hQ : 0 ≤ Q) (hα : 0 < α)
    (hα1 : α < 1) (hk₁ : 0 < k₁) (hk : k₁ < k₂) :
    psi P Q α k₂ / k₂ < psi P Q α k₁ / k₁ := by
  have hk₂ : 0 < k₂ := hk₁.trans hk
  have hx1 := (psi_spec hP hQ hα hα1 hk₁).1
  have hx2 := (psi_spec hP hQ hα hα1 hk₂).1
  have hlt := psi_strictMono hP hQ hα hα1 hk₁ hk
  have hpow := Real.rpow_lt_rpow_of_neg hx1 hlt (by linarith : α - 1 < 0)
  have h : (psi P Q α k₂ / k₂) ^ α < (psi P Q α k₁ / k₁) ^ α := by
    rw [psi_ratio hP hQ hα hα1 hk₁, psi_ratio hP hQ hα hα1 hk₂]
    nlinarith
  exact (Real.rpow_lt_rpow_iff (by positivity) (by positivity) hα).mp h

/-- `ψ(k) < k ⟺ P < (1 - Q) k^{1-α}`. -/
theorem psi_lt_self_iff {P Q α k : ℝ} (hP : 0 < P) (hQ : 0 ≤ Q) (hα : 0 < α) (hα1 : α < 1)
    (hk : 0 < k) : psi P Q α k < k ↔ P < (1 - Q) * k ^ (1 - α) := by
  obtain ⟨hx, hH⟩ := psi_spec hP hQ hα hα1 hk
  have hmono := Hmap_strictMonoOn hP hQ hα hα1
  have hkp := Real.rpow_pos_of_pos hk (1 - α)
  have hka := Real.rpow_pos_of_pos hk α
  have hsk : k = k ^ α * k ^ (1 - α) := by
    rw [← Real.rpow_add hk, show α + (1 - α) = 1 by ring, Real.rpow_one]
  have key : k ^ α < Hmap P Q α k ↔ P < (1 - Q) * k ^ (1 - α) := by
    unfold Hmap
    rw [lt_div_iff₀ (by positivity)]
    conv_rhs => rw [show (1 - Q) * k ^ (1 - α) = k ^ (1 - α) - Q * k ^ (1 - α) by ring]
    constructor
    · intro h
      have := lt_of_mul_lt_mul_left (h.trans_eq hsk) hka.le
      linarith
    · intro h
      exact (mul_lt_mul_of_pos_left (by linarith : P + Q * k ^ (1 - α) < k ^ (1 - α))
        hka).trans_eq hsk.symm
  rw [← key, ← hH]
  exact ⟨fun h => hmono hx hk h, fun h => by
    by_contra hge
    push Not at hge
    have := hmono.monotoneOn hk hx hge
    linarith⟩

/-- `ψ(k) = k ⟺ P = (1 - Q) k^{1-α}` (steady states of (58)). -/
theorem psi_eq_self_iff {P Q α k : ℝ} (hP : 0 < P) (hQ : 0 ≤ Q) (hα : 0 < α) (hα1 : α < 1)
    (hk : 0 < k) : psi P Q α k = k ↔ P = (1 - Q) * k ^ (1 - α) := by
  constructor
  · intro h
    obtain ⟨-, hH⟩ := psi_spec hP hQ hα hα1 hk
    rw [h] at hH
    have := (root_iff hP hQ hk).mpr hH
    have hsk : k = k ^ α * k ^ (1 - α) := by
      rw [← Real.rpow_add hk, show α + (1 - α) = 1 by ring, Real.rpow_one]
    have hka := Real.rpow_pos_of_pos hk α
    have : k ^ α * k ^ (1 - α) = k ^ α * (P + Q * k ^ (1 - α)) := by rw [← hsk]; exact this
    have := mul_left_cancel₀ hka.ne' this
    linarith
  · intro h
    symm
    apply psi_unique hP hQ hα hα1 hk hk
    rw [← root_iff hP hQ hk]
    have hsk : k = k ^ α * k ^ (1 - α) := by
      rw [← Real.rpow_add hk, show α + (1 - α) = 1 by ring, Real.rpow_one]
    conv_lhs => rw [hsk]
    congr 1
    linarith

/-- The right side of (57) evaluated at `k̄^U` (where `r^D = r`) is saving plus maximal
borrowing: `k^α(P + Q (k̄^U)^{1-α}) = (β/(1+β) + η) w(k)`. -/
theorem capacity_eq {A α β η r k : ℝ} (hα : 0 < α) (hα1 : α < 1) (hA : 0 < A)
    (hβ : 0 < β) (hr : 0 < 1 + r) :
    k ^ α * (coefP A α β η + coefQ α β η r * kU A α r ^ (1 - α)) =
      (β / (1 + β) + η) * wage A α k := by
  rw [kU_rpow hα hα1 hA hr]
  unfold coefP coefQ wage
  field_simp
  ring

/-- **The constraint is slack iff saving plus maximal borrowing covers `k̄^U`**:
`k̄^U ≤ ψ(k) ⟺ k̄^U ≤ βw(k)/(1+β) + ηw(k)` (the inequality behind (60) and Case 3). -/
theorem kU_le_psi_iff {A α β η r k : ℝ} (hα : 0 < α) (hα1 : α < 1) (hA : 0 < A)
    (hβ : 0 < β) (hη : 0 ≤ η) (hr : 0 < 1 + r) (hk : 0 < k) :
    kU A α r ≤ psi (coefP A α β η) (coefQ α β η r) α k ↔
      kU A α r ≤ (β / (1 + β) + η) * wage A α k := by
  have hP : 0 < coefP A α β η := by
    unfold coefP
    have : 0 < 1 - α := by linarith
    positivity
  have hQ : 0 ≤ coefQ α β η r := by
    unfold coefQ
    have : 0 < 1 - α := by linarith
    positivity
  have hU := kU_pos hα hA hr
  obtain ⟨hx, hH⟩ := psi_spec hP hQ hα hα1 hk
  have hmono := Hmap_strictMonoOn hP hQ hα hα1
  have hd : 0 < coefP A α β η + coefQ α β η r * kU A α r ^ (1 - α) := by
    have := Real.rpow_pos_of_pos hU (1 - α)
    positivity
  have key : Hmap (coefP A α β η) (coefQ α β η r) α (kU A α r) ≤ k ^ α ↔
      kU A α r ≤ (β / (1 + β) + η) * wage A α k := by
    unfold Hmap
    rw [div_le_iff₀ hd, capacity_eq hα hα1 hA hβ hr]
  rw [← key, ← hH]
  exact ⟨fun h => hmono.monotoneOn hU hx h, fun h => by
    by_contra hlt
    push Not at hlt
    have := hmono hx hU hlt
    linarith⟩

/-- **Characterisation of equilibrium** (O&R (57)–(58), δ = 1, made exact): for `k > 0`,
next period's capital `x > 0` is an equilibrium iff `x = min(k̄^U, ψ(k))`. When
`ψ(k) ≥ k̄^U` the borrowing constraint is slack and `r^D = r`; otherwise it binds and
`r^D > r`. -/
theorem eqRel_iff {β η r A α k x : ℝ} (hα : 0 < α) (hα1 : α < 1) (hA : 0 < A) (hβ : 0 < β)
    (hη : 0 ≤ η) (hr : 0 < 1 + r) (hk : 0 < k) (hx : 0 < x) :
    EqRel β η r A α k x ↔ x = min (kU A α r) (psi (coefP A α β η) (coefQ α β η r) α k) := by
  have hP : 0 < coefP A α β η := by
    unfold coefP
    have : 0 < 1 - α := by linarith
    positivity
  have hQ : 0 ≤ coefQ α β η r := by
    unfold coefQ
    have : 0 < 1 - α := by linarith
    positivity
  have hw : 0 < wage A α k := by
    unfold wage
    have : 0 < 1 - α := by linarith
    have := Real.rpow_pos_of_pos hk α
    positivity
  have hRD : 0 < α * A * x ^ (α - 1) := by
    have := Real.rpow_pos_of_pos hx (α - 1)
    positivity
  obtain ⟨hψ, hHψ⟩ := psi_spec hP hQ hα hα1 hk
  constructor
  · rintro ⟨cY, b, ho⟩
    have hge := rate_ge_of_optimal hβ hw hη hRD ho hx
    rcases eq_or_lt_of_le hge with heq | hlt
    · -- `r^D = r`: the constraint is slack
      have hxU : x = kU A α r := (rate_eq_iff hα hα1 hA hr hx).mp heq.symm
      have ho' : IsOptimal β (wage A α k) η (1 + r) (1 + r) cY x b := by rwa [← heq] at ho
      -- compare with the optimal plan `k = 0`
      have hb0 : -(η * wage A α k) ≤ β * wage A α k / (1 + β) := by
        have : 0 ≤ β * wage A α k / (1 + β) := by positivity
        nlinarith [mul_nonneg hη hw.le]
      have hopt0 := optimal_equal (η := η) hβ hw hr le_rfl hb0 (by ring)
      have hu := le_antisymm (hopt0.2 cY x b ho'.1) (ho'.2 _ _ _ hopt0.1)
      have hle : cY + ((1 + r) * x + (1 + r) * b) / (1 + r) ≤ wage A α k := by
        rw [intertemporal_budget hr ho'.1.budget]
        simp
      have hmax := (log_consumer hβ hr hw ho'.1.posY ho'.1.posO hle).2
      have hcO : (1 + r) * 0 + (1 + r) * (β * wage A α k / (1 + β)) =
          β * (1 + r) * wage A α k / (1 + β) := by ring
      unfold utility at hu
      rw [hcO] at hu
      obtain ⟨hc1, -⟩ := hmax hu
      have hbud := ho'.1.budget
      have hbor := ho'.1.borrow
      have hcap : kU A α r ≤ (β / (1 + β) + η) * wage A α k := by
        rw [← hxU]
        rw [hc1] at hbud
        have : x = wage A α k - wage A α k / (1 + β) - b := by linarith
        rw [this]
        have e : wage A α k - wage A α k / (1 + β) = β / (1 + β) * wage A α k := by
          field_simp
          ring
        rw [e]
        nlinarith
      have := (kU_le_psi_iff hα hα1 hA hβ hη hr hk).mpr hcap
      rw [min_eq_left this]
      exact hxU
    · -- `r^D > r`: the constraint binds
      have hxlt : x < kU A α r := (rate_gt_iff hα hα1 hA hr hx).mp hlt
      have huniq := (optimal_binding hβ hw hη (by linarith) hlt).2 cY x b ho
      have h57 := huniq.2.1
      rw [binding_plan_eq_57 hβ hRD, eq57_eq hα hA hβ hx] at h57
      have hxψ := psi_unique hP hQ hα hα1 hk hx ((root_iff hP hQ hx).mp h57)
      rw [← hxψ, min_eq_right hxlt.le]
  · intro hmin
    by_cases hcase : kU A α r ≤ psi (coefP A α β η) (coefQ α β η r) α k
    · rw [min_eq_left hcase] at hmin
      have hcap := (kU_le_psi_iff hα hα1 hA hβ hη hr hk).mp hcase
      have hrate : α * A * x ^ (α - 1) = 1 + r := (rate_eq_iff hα hα1 hA hr hx).mpr hmin
      refine ⟨wage A α k / (1 + β), β * wage A α k / (1 + β) - x, ?_⟩
      rw [hrate]
      apply optimal_equal hβ hw hr hx.le _ (by ring)
      have e : β * wage A α k / (1 + β) = β / (1 + β) * wage A α k := by ring
      rw [e, hmin]
      nlinarith
    · push Not at hcase
      rw [min_eq_right hcase.le] at hmin
      have hlt : 1 + r < α * A * x ^ (α - 1) :=
        (rate_gt_iff hα hα1 hA hr hx).mpr (hmin ▸ hcase)
      obtain ⟨ho, -⟩ := optimal_binding hβ hw hη (by linarith) hlt
      have hHx : Hmap (coefP A α β η) (coefQ α β η r) α x = k ^ α := by rw [hmin]; exact hHψ
      have hkx : wage A α k - (wage A α k + (α * A * x ^ (α - 1) - (1 + r)) *
          (η * wage A α k) / (α * A * x ^ (α - 1))) / (1 + β) + η * wage A α k = x := by
        rw [binding_plan_eq_57 hβ hRD, eq57_eq hα hA hβ hx]
        exact ((root_iff hP hQ hx).mpr hHx).symm
      rw [hkx] at ho
      exact ⟨_, _, ho⟩

/-- The equilibrium map `Φ(k) = min(k̄^U, ψ(k))` (O&R (58) with the switch to `r^D = r`). -/
noncomputable def eqMap (A α β η r k : ℝ) : ℝ :=
  min (kU A α r) (psi (coefP A α β η) (coefQ α β η r) α k)

/-- **The equilibrium path exists and is unique**: for every `k > 0` there is exactly one
equilibrium next-period capital stock, `Φ(k)`. -/
theorem equilibrium_existsUnique {β η r A α k : ℝ} (hα : 0 < α) (hα1 : α < 1) (hA : 0 < A)
    (hβ : 0 < β) (hη : 0 ≤ η) (hr : 0 < 1 + r) (hk : 0 < k) :
    ∃! x, 0 < x ∧ EqRel β η r A α k x := by
  have hP : 0 < coefP A α β η := by
    unfold coefP
    have : 0 < 1 - α := by linarith
    positivity
  have hQ : 0 ≤ coefQ α β η r := by
    unfold coefQ
    have : 0 < 1 - α := by linarith
    positivity
  have hpos : 0 < eqMap A α β η r k :=
    lt_min (kU_pos hα hA hr) (psi_spec hP hQ hα hα1 hk).1
  refine ⟨eqMap A α β η r k, ⟨hpos, (eqRel_iff hα hα1 hA hβ hη hr hk hpos).mpr rfl⟩, ?_⟩
  rintro y ⟨hy, hEq⟩
  exact (eqRel_iff hα hα1 hA hβ hη hr hk hy).mp hEq

/-- Properties of `Φ`: positive, increasing, and `Φ(k)/k` strictly decreasing. -/
theorem eqMap_props {A α β η r : ℝ} (hα : 0 < α) (hα1 : α < 1) (hA : 0 < A) (hβ : 0 < β)
    (hη : 0 ≤ η) (hr : 0 < 1 + r) :
    (∀ k, 0 < k → 0 < eqMap A α β η r k) ∧
      (∀ a b, 0 < a → a ≤ b → eqMap A α β η r a ≤ eqMap A α β η r b) ∧
      (∀ a b, 0 < a → a < b → eqMap A α β η r b / b < eqMap A α β η r a / a) := by
  have hP : 0 < coefP A α β η := by
    unfold coefP
    have : 0 < 1 - α := by linarith
    positivity
  have hQ : 0 ≤ coefQ α β η r := by
    unfold coefQ
    have : 0 < 1 - α := by linarith
    positivity
  have hU := kU_pos hα hA hr
  refine ⟨fun k hk => lt_min hU (psi_spec hP hQ hα hα1 hk).1, fun a b ha hab => ?_,
    fun a b ha hab => ?_⟩
  · unfold eqMap
    rcases eq_or_lt_of_le hab with h | h
    · rw [h]
    · exact min_le_min le_rfl (psi_strictMono hP hQ hα hα1 ha h).le
  · have hb : 0 < b := ha.trans hab
    unfold eqMap
    have h1 := psi_ratio_anti hP hQ hα hα1 ha hab
    have h2 : kU A α r / b < kU A α r / a := div_lt_div_of_pos_left hU ha hab
    rw [← min_div_div_right ha.le]
    apply lt_min
    · calc min (kU A α r) (psi (coefP A α β η) (coefQ α β η r) α b) / b
          ≤ kU A α r / b := div_le_div_of_nonneg_right (min_le_left _ _) hb.le
        _ < kU A α r / a := h2
    · calc min (kU A α r) (psi (coefP A α β η) (coefQ α β η r) α b) / b
          ≤ psi (coefP A α β η) (coefQ α β η r) α b / b :=
            div_le_div_of_nonneg_right (min_le_right _ _) hb.le
        _ < psi (coefP A α β η) (coefQ α β η r) α a / a := h1

/-- **Monotone convergence for maps with a falling growth factor**: if `G > 0` is increasing,
`G(k)/k` is strictly decreasing, and `G(k*) = k*`, then from every `k₀ > 0` the sequence
`k_{t+1} = G(k_t)` converges to `k*`, monotonically (no continuity of `G` needed). -/
theorem monotone_convergence {G : ℝ → ℝ} {ks : ℝ} (hks : 0 < ks)
    (hpos : ∀ k, 0 < k → 0 < G k) (hmono : ∀ a b, 0 < a → a ≤ b → G a ≤ G b)
    (hratio : ∀ a b, 0 < a → a < b → G b / b < G a / a) (hfix : G ks = ks)
    {k : ℕ → ℝ} (h0 : 0 < k 0) (hstep : ∀ t, k (t + 1) = G (k t)) :
    Tendsto k atTop (𝓝 ks) ∧ (k 0 ≤ ks → Monotone k) ∧ (ks ≤ k 0 → Antitone k) := by
  have hk : ∀ t, 0 < k t := by
    intro t
    induction t with
    | zero => exact h0
    | succ t ih => rw [hstep]; exact hpos _ ih
  -- the ratio at `ks` is 1
  have hr1 : ∀ a, 0 < a → a < ks → a < G a := by
    intro a ha hlt
    have := hratio a ks ha hlt
    rw [hfix, div_self hks.ne', lt_div_iff₀ ha, one_mul] at this
    exact this
  have hr2 : ∀ a, ks < a → G a < a := by
    intro a hlt
    have := hratio ks a hks hlt
    rw [hfix, div_self hks.ne', div_lt_iff₀ (hks.trans hlt), one_mul] at this
    exact this
  have up : k 0 ≤ ks → (∀ t, k t ≤ ks) ∧ Monotone k := by
    intro hle
    have hb : ∀ t, k t ≤ ks := by
      intro t
      induction t with
      | zero => exact hle
      | succ t ih => rw [hstep, ← hfix]; exact hmono _ _ (hk t) ih
    refine ⟨hb, monotone_nat_of_le_succ fun t => ?_⟩
    rw [hstep]
    rcases eq_or_lt_of_le (hb t) with h | h
    · rw [h, hfix]
    · exact (hr1 _ (hk t) h).le
  have down : ks ≤ k 0 → (∀ t, ks ≤ k t) ∧ Antitone k := by
    intro hle
    have hb : ∀ t, ks ≤ k t := by
      intro t
      induction t with
      | zero => exact hle
      | succ t ih => rw [hstep, ← hfix]; exact hmono _ _ hks ih
    refine ⟨hb, antitone_nat_of_succ_le fun t => ?_⟩
    rw [hstep]
    rcases eq_or_lt_of_le (hb t) with h | h
    · rw [← h, hfix]
    · exact (hr2 _ h).le
  refine ⟨?_, fun h => (up h).2, fun h => (down h).2⟩
  rcases le_total (k 0) ks with hle | hle
  · obtain ⟨hb, hm⟩ := up hle
    have hbdd : BddAbove (Set.range k) := ⟨ks, by rintro _ ⟨t, rfl⟩; exact hb t⟩
    have hlim := tendsto_atTop_ciSup hm hbdd
    set L := ⨆ t, k t
    have hkL : ∀ t, k t ≤ L := fun t => le_ciSup hbdd t
    have hLks : L ≤ ks := ciSup_le hb
    have hL0 : 0 < L := lt_of_lt_of_le h0 (hkL 0)
    rcases eq_or_lt_of_le hLks with heq | hlt
    · rwa [heq] at hlim
    · exfalso
      set q := G L / L
      have hq : 1 < q := by
        rw [one_lt_div hL0]
        exact hr1 L hL0 hlt
      have hgeo : ∀ t, q ^ t * k 0 ≤ k t := by
        intro t
        induction t with
        | zero => simp
        | succ t ih =>
          have hrat : q ≤ G (k t) / k t := by
            rcases eq_or_lt_of_le (hkL t) with h | h
            · rw [h]
            · exact (hratio _ _ (hk t) h).le
          rw [le_div_iff₀ (hk t)] at hrat
          rw [hstep, pow_succ]
          nlinarith [pow_pos (lt_trans one_pos hq) t]
      obtain ⟨t, ht⟩ := ((tendsto_pow_atTop_atTop_of_one_lt hq).eventually_gt_atTop
        (L / k 0)).exists
      have := hgeo t
      have := hkL t
      rw [div_lt_iff₀ h0] at ht
      linarith
  · obtain ⟨hb, ha⟩ := down hle
    have hbdd : BddBelow (Set.range k) := ⟨ks, by rintro _ ⟨t, rfl⟩; exact hb t⟩
    have hlim := tendsto_atTop_ciInf ha hbdd
    set L := ⨅ t, k t
    have hkL : ∀ t, L ≤ k t := fun t => ciInf_le hbdd t
    have hLks : ks ≤ L := le_ciInf hb
    rcases eq_or_lt_of_le hLks with heq | hlt
    · rwa [← heq] at hlim
    · exfalso
      have hL0 : 0 < L := hks.trans hlt
      set q := G L / L
      have hq : q < 1 := by
        rw [div_lt_one hL0]
        exact hr2 L hlt
      have hq0 : 0 < q := div_pos (hpos L hL0) hL0
      have hgeo : ∀ t, k t ≤ q ^ t * k 0 := by
        intro t
        induction t with
        | zero => simp
        | succ t ih =>
          have hrat : G (k t) / k t ≤ q := by
            rcases eq_or_lt_of_le (hkL t) with h | h
            · rw [← h]
            · exact (hratio _ _ hL0 h).le
          rw [div_le_iff₀ (hk t)] at hrat
          rw [hstep, pow_succ]
          nlinarith [pow_pos hq0 t]
      have hlim0 : Tendsto (fun t => q ^ t * k 0) atTop (𝓝 0) := by
        simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0.le hq).mul_const (k 0)
      obtain ⟨t, ht⟩ := (hlim0.eventually (gt_mem_nhds hL0)).exists
      have := hgeo t
      have := hkL t
      linarith

/-! ## Steady states (59), the convergence condition (60), and dynamics -/

/-- `D = α(1+β) - η(1-α)(1+r)`, the denominator of O&R (59). -/
noncomputable def Dcoef (α β η r : ℝ) : ℝ := α * (1 + β) - η * (1 - α) * (1 + r)

/-- **The constrained steady state** O&R (59), p. 472 (with productivity `A`):
`k̄^D = [αβ(1-α)(1+η)A / (α(1+β) - η(1-α)(1+r))]^{1/(1-α)}`. -/
noncomputable def kD (A α β η r : ℝ) : ℝ :=
  (α * β * (1 - α) * (1 + η) * A / Dcoef α β η r) ^ (1 / (1 - α))

/-- `Q < 1 ⟺ D > 0`. -/
theorem coefQ_lt_one_iff {α β η r : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    coefQ α β η r < 1 ↔ 0 < Dcoef α β η r := by
  unfold coefQ Dcoef
  rw [div_lt_one (by positivity)]
  constructor <;> intro h <;> nlinarith

/-- `(k̄^D)^{1-α} = P/(1 - Q)` when `D > 0`. -/
theorem kD_rpow {A α β η r : ℝ} (hα : 0 < α) (hα1 : α < 1) (hA : 0 < A) (hβ : 0 < β)
    (hη : 0 ≤ η) (hD : 0 < Dcoef α β η r) :
    kD A α β η r ^ (1 - α) = coefP A α β η / (1 - coefQ α β η r) := by
  have h1a : 0 < 1 - α := by linarith
  unfold kD
  rw [← Real.rpow_mul (by unfold Dcoef at hD ⊢; positivity), one_div_mul_cancel h1a.ne',
    Real.rpow_one]
  unfold coefP coefQ
  unfold Dcoef at hD ⊢
  have : (1 - (1 - α) * (1 + r) * η / ((1 + β) * α)) = (α * (1 + β) - η * (1 - α) * (1 + r)) /
      ((1 + β) * α) := by field_simp
  rw [this]
  field_simp

/-- `k̄^D > 0` when `D > 0`. -/
theorem kD_pos {A α β η r : ℝ} (hα : 0 < α) (hα1 : α < 1) (hA : 0 < A) (hβ : 0 < β)
    (hη : 0 ≤ η) (hD : 0 < Dcoef α β η r) : 0 < kD A α β η r := by
  have h1a : 0 < 1 - α := by linarith
  unfold kD
  exact Real.rpow_pos_of_pos (by positivity) _

/-- **Steady states of the constrained map** (O&R (59)): `ψ(k) = k` iff `D > 0` and
`k = k̄^D`. In particular (59) is meaningless when `D ≤ 0`: there is no constrained steady
state. -/
theorem psi_fixed_iff {A α β η r k : ℝ} (hα : 0 < α) (hα1 : α < 1) (hA : 0 < A) (hβ : 0 < β)
    (hη : 0 ≤ η) (hr : 0 < 1 + r) (hk : 0 < k) :
    psi (coefP A α β η) (coefQ α β η r) α k = k ↔ 0 < Dcoef α β η r ∧ k = kD A α β η r := by
  have h1a : 0 < 1 - α := by linarith
  have hP : 0 < coefP A α β η := by unfold coefP; positivity
  have hQ : 0 ≤ coefQ α β η r := by unfold coefQ; positivity
  have hkp := Real.rpow_pos_of_pos hk (1 - α)
  rw [psi_eq_self_iff hP hQ hα hα1 hk]
  constructor
  · intro h
    have hQ1 : 0 < 1 - coefQ α β η r := by
      by_contra hc
      push Not at hc
      nlinarith
    have hD := (coefQ_lt_one_iff (η := η) (r := r) hα hβ).mp (by linarith)
    refine ⟨hD, ?_⟩
    have hkD := kD_pos hα hα1 hA hβ hη hD
    have e : k ^ (1 - α) = kD A α β η r ^ (1 - α) := by
      rw [kD_rpow hα hα1 hA hβ hη hD, eq_div_iff hQ1.ne']
      linarith
    exact le_antisymm ((Real.rpow_le_rpow_iff hk.le hkD.le h1a).mp e.le)
      ((Real.rpow_le_rpow_iff hkD.le hk.le h1a).mp e.ge)
  · rintro ⟨hD, rfl⟩
    have hQ1 : 0 < 1 - coefQ α β η r := by
      have := (coefQ_lt_one_iff (η := η) (r := r) hα hβ).mpr hD
      linarith
    rw [kD_rpow hα hα1 hA hβ hη hD]
    field_simp

/-- **The exact form of O&R (60) and fn 31**: the non-convergence condition
`βw̄/(1+β) + ηw̄ < k̄^U` (with `w̄ = w(k̄^U)`) holds iff `D > 0` and `k̄^D < k̄^U`. -/
theorem cond60_iff {A α β η r : ℝ} (hα : 0 < α) (hα1 : α < 1) (hA : 0 < A) (hβ : 0 < β)
    (hη : 0 ≤ η) (hr : 0 < 1 + r) :
    (β / (1 + β) + η) * wage A α (kU A α r) < kU A α r ↔
      0 < Dcoef α β η r ∧ kD A α β η r < kU A α r := by
  have h1a : 0 < 1 - α := by linarith
  have hP : 0 < coefP A α β η := by unfold coefP; positivity
  have hQ : 0 ≤ coefQ α β η r := by unfold coefQ; positivity
  have hU := kU_pos hα hA hr
  have hUp := Real.rpow_pos_of_pos hU (1 - α)
  have step : (β / (1 + β) + η) * wage A α (kU A α r) < kU A α r ↔
      coefP A α β η < (1 - coefQ α β η r) * kU A α r ^ (1 - α) := by
    rw [← psi_lt_self_iff hP hQ hα hα1 hU, ← not_le, ← not_le,
      kU_le_psi_iff hα hα1 hA hβ hη hr hU]
  rw [step]
  constructor
  · intro h
    have hQ1 : 0 < 1 - coefQ α β η r := by
      by_contra hc
      push Not at hc
      nlinarith
    have hD := (coefQ_lt_one_iff (η := η) (r := r) hα hβ).mp (by linarith)
    refine ⟨hD, ?_⟩
    have hkD := kD_pos hα hα1 hA hβ hη hD
    have : kD A α β η r ^ (1 - α) < kU A α r ^ (1 - α) := by
      rw [kD_rpow hα hα1 hA hβ hη hD, div_lt_iff₀ hQ1]
      linarith
    exact (Real.rpow_lt_rpow_iff hkD.le hU.le h1a).mp this
  · rintro ⟨hD, hlt⟩
    have hQ1 : 0 < 1 - coefQ α β η r := by
      have := (coefQ_lt_one_iff (η := η) (r := r) hα hβ).mpr hD
      linarith
    have hkD := kD_pos hα hα1 hA hβ hη hD
    have := Real.rpow_lt_rpow hkD.le hlt h1a
    rw [kD_rpow hα hα1 hA hβ hη hD, div_lt_iff₀ hQ1] at this
    linarith

/-- **O&R fn 31, made precise**: if (60) holds then `D > 0`; indeed
`D (k̄^U)^{1-α} > αβ(1-α)(1+η)A > 0`. (The book's "positive if the constraint is never slack"
is imprecise: the converse fails, since `D > 0` is compatible with `k̄^D ≥ k̄^U`.) -/
theorem fn31 {A α β η r : ℝ} (hα : 0 < α) (hα1 : α < 1) (hA : 0 < A) (hβ : 0 < β)
    (hη : 0 ≤ η) (hr : 0 < 1 + r)
    (h60 : (β / (1 + β) + η) * wage A α (kU A α r) < kU A α r) :
    0 < Dcoef α β η r ∧
      α * β * (1 - α) * (1 + η) * A < Dcoef α β η r * kU A α r ^ (1 - α) := by
  obtain ⟨hD, hlt⟩ := (cond60_iff hα hα1 hA hβ hη hr).mp h60
  refine ⟨hD, ?_⟩
  have h1a : 0 < 1 - α := by linarith
  have hkD := kD_pos hα hα1 hA hβ hη hD
  have := Real.rpow_lt_rpow hkD.le hlt h1a
  unfold kD at this
  rw [← Real.rpow_mul (by unfold Dcoef at hD ⊢; positivity), one_div_mul_cancel h1a.ne',
    Real.rpow_one, div_lt_iff₀ hD] at this
  linarith

/-- The long-run capital stock: `k̄^D` if (60) holds, else `k̄^U`. -/
noncomputable def kStar (A α β η r : ℝ) : ℝ := by
  classical
  exact if (β / (1 + β) + η) * wage A α (kU A α r) < kU A α r then kD A α β η r else kU A α r

/-- **`k*` is the unique steady state of the equilibrium map** (O&R p. 472). -/
theorem kStar_fixed {A α β η r : ℝ} (hα : 0 < α) (hα1 : α < 1) (hA : 0 < A) (hβ : 0 < β)
    (hη : 0 ≤ η) (hr : 0 < 1 + r) :
    0 < kStar A α β η r ∧ eqMap A α β η r (kStar A α β η r) = kStar A α β η r ∧
      ∀ k, 0 < k → eqMap A α β η r k = k → k = kStar A α β η r := by
  have hU := kU_pos hα hA hr
  have hfix : 0 < kStar A α β η r ∧ eqMap A α β η r (kStar A α β η r) = kStar A α β η r := by
    unfold kStar
    split_ifs with h60
    · obtain ⟨hD, hlt⟩ := (cond60_iff hα hα1 hA hβ hη hr).mp h60
      have hkD := kD_pos hα hα1 hA hβ hη hD
      refine ⟨hkD, ?_⟩
      unfold eqMap
      rw [(psi_fixed_iff hα hα1 hA hβ hη hr hkD).mpr ⟨hD, rfl⟩, min_eq_right hlt.le]
    · refine ⟨hU, ?_⟩
      push Not at h60
      unfold eqMap
      rw [min_eq_left ((kU_le_psi_iff hα hα1 hA hβ hη hr hU).mpr h60)]
  refine ⟨hfix.1, hfix.2, fun k hk hk1 => ?_⟩
  obtain ⟨-, -, hratio⟩ := eqMap_props hα hα1 hA hβ hη hr (η := η)
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have := hratio k _ hk hlt
    rw [hfix.2, hk1, div_self hfix.1.ne', div_self hk.ne'] at this
    exact lt_irrefl _ this
  · have := hratio _ k hfix.1 hgt
    rw [hfix.2, hk1, div_self hfix.1.ne', div_self hk.ne'] at this
    exact lt_irrefl _ this

/-- **Global monotone convergence of every equilibrium path** (O&R pp. 471–472): from any
`k₀ > 0`, the (unique) equilibrium path `k_{t+1}` converges monotonically to `k*`, which is
`k̄^D` when (60) holds and `k̄^U` otherwise. -/
theorem equilibrium_converges {A α β η r : ℝ} {k : ℕ → ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hA : 0 < A) (hβ : 0 < β) (hη : 0 ≤ η) (hr : 0 < 1 + r) (h0 : 0 < k 0)
    (hpos : ∀ t, 0 < k (t + 1)) (heq : ∀ t, EqRel β η r A α (k t) (k (t + 1))) :
    Tendsto k atTop (𝓝 (kStar A α β η r)) ∧
      (k 0 ≤ kStar A α β η r → Monotone k) ∧ (kStar A α β η r ≤ k 0 → Antitone k) := by
  obtain ⟨hGpos, hmono, hratio⟩ := eqMap_props hα hα1 hA hβ hη hr (η := η)
  obtain ⟨hks, hfix, -⟩ := kStar_fixed hα hα1 hA hβ hη hr (η := η)
  have hk : ∀ t, 0 < k t := fun t => by
    cases t with
    | zero => exact h0
    | succ t => exact hpos t
  exact monotone_convergence hks hGpos hmono hratio hfix h0
    fun t => (eqRel_iff hα hα1 hA hβ hη hr (hk t) (hpos t)).mp (heq t)

/-- **Interest rates need not converge** (O&R p. 472): along any equilibrium path the gross
domestic rate `αA k_t^{α-1}` converges to `αA (k*)^{α-1}`; under (60) this limit exceeds the
world rate `1 + r` (a permanent wedge: no absolute convergence), otherwise it equals `1 + r`. -/
theorem rates_converge {A α β η r : ℝ} {k : ℕ → ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hA : 0 < A) (hβ : 0 < β) (hη : 0 ≤ η) (hr : 0 < 1 + r) (h0 : 0 < k 0)
    (hpos : ∀ t, 0 < k (t + 1)) (heq : ∀ t, EqRel β η r A α (k t) (k (t + 1))) :
    Tendsto (fun t => α * A * k t ^ (α - 1)) atTop
        (𝓝 (α * A * kStar A α β η r ^ (α - 1))) ∧
      ((β / (1 + β) + η) * wage A α (kU A α r) < kU A α r →
        1 + r < α * A * kStar A α β η r ^ (α - 1)) ∧
      (¬ (β / (1 + β) + η) * wage A α (kU A α r) < kU A α r →
        α * A * kStar A α β η r ^ (α - 1) = 1 + r) := by
  obtain ⟨hks, -, -⟩ := kStar_fixed hα hα1 hA hβ hη hr (η := η)
  have hlim := (equilibrium_converges hα hα1 hA hβ hη hr h0 hpos heq).1
  refine ⟨((Real.continuousAt_rpow_const _ (α - 1) (Or.inl hks.ne')).tendsto.comp
    hlim).const_mul (α * A), fun h60 => ?_, fun h60 => ?_⟩
  · obtain ⟨hD, hlt⟩ := (cond60_iff hα hα1 hA hβ hη hr).mp h60
    unfold kStar
    simp only [h60, ↓reduceIte]
    exact (rate_gt_iff hα hα1 hA hr (kD_pos hα hα1 hA hβ hη hD)).mpr hlt
  · unfold kStar
    simp only [h60, ↓reduceIte]
    exact kU_rate hα hα1 hA hr

/-- **Case 3: convergence in one period** (O&R p. 472–473): `Φ(k₀) = k̄^U` iff
`βw₀/(1+β) + ηw₀ ≥ k̄^U`. -/
theorem one_period_iff {A α β η r k₀ : ℝ} (hα : 0 < α) (hα1 : α < 1) (hA : 0 < A)
    (hβ : 0 < β) (hη : 0 ≤ η) (hr : 0 < 1 + r) (hk₀ : 0 < k₀) :
    eqMap A α β η r k₀ = kU A α r ↔ kU A α r ≤ (β / (1 + β) + η) * wage A α k₀ := by
  rw [← kU_le_psi_iff hα hα1 hA hβ hη hr hk₀]
  unfold eqMap
  exact min_eq_left_iff

/-- **Case 1** (O&R p. 470–471): if the autarky steady state `k^A`
(`(k^A)^{1-α} = β(1-α)A/(1+β)`) has `r^A < r`, the economy reaches `r^D = r` in one period. -/
theorem case1_one_period {A α β η r kA : ℝ} (hα : 0 < α) (hα1 : α < 1) (hA : 0 < A)
    (hβ : 0 < β) (hη : 0 ≤ η) (hr : 0 < 1 + r) (hkA : 0 < kA)
    (haut : kA ^ (1 - α) = β * (1 - α) * A / (1 + β)) (hrate : α * A * kA ^ (α - 1) < 1 + r) :
    eqMap A α β η r kA = kU A α r := by
  rw [one_period_iff hα hα1 hA hβ hη hr hkA]
  have hUlt : kU A α r < kA := by
    by_contra hle
    push Not at hle
    rcases eq_or_lt_of_le hle with h | h
    · rw [(rate_eq_iff hα hα1 hA hr hkA).mpr h] at hrate
      exact lt_irrefl _ hrate
    · linarith [(rate_gt_iff hα hα1 hA hr hkA).mpr h]
  have hsave : β / (1 + β) * wage A α kA = kA := by
    unfold wage
    have e : kA = kA ^ α * kA ^ (1 - α) := by
      rw [← Real.rpow_add hkA, show α + (1 - α) = 1 by ring, Real.rpow_one]
    conv_rhs => rw [e, haut]
    field_simp
  have : 0 ≤ η * wage A α kA := by
    unfold wage
    have : 0 < 1 - α := by linarith
    have := Real.rpow_pos_of_pos hkA α
    positivity
  nlinarith

/-- **Easier borrowing speeds convergence** (O&R p. 472): the equilibrium map is increasing in
`η`. -/
theorem eqMap_mono_eta {A α β η₁ η₂ r k : ℝ} (hα : 0 < α) (hα1 : α < 1) (hA : 0 < A)
    (hβ : 0 < β) (hη₁ : 0 ≤ η₁) (hη : η₁ ≤ η₂) (hr : 0 < 1 + r) (hk : 0 < k) :
    eqMap A α β η₁ r k ≤ eqMap A α β η₂ r k := by
  have h1a : 0 < 1 - α := by linarith
  have hη₂ : 0 ≤ η₂ := hη₁.trans hη
  have hP1 : 0 < coefP A α β η₁ := by unfold coefP; positivity
  have hQ1 : 0 ≤ coefQ α β η₁ r := by unfold coefQ; positivity
  have hP2 : 0 < coefP A α β η₂ := by unfold coefP; positivity
  have hQ2 : 0 ≤ coefQ α β η₂ r := by unfold coefQ; positivity
  obtain ⟨hx1, hH1⟩ := psi_spec hP1 hQ1 hα hα1 hk
  obtain ⟨hx2, hH2⟩ := psi_spec hP2 hQ2 hα hα1 hk
  have hPle : coefP A α β η₁ ≤ coefP A α β η₂ := by
    unfold coefP
    apply div_le_div_of_nonneg_right _ (by positivity)
    have : 0 ≤ (1 - α) * A * β := by positivity
    nlinarith
  have hQle : coefQ α β η₁ r ≤ coefQ α β η₂ r := by
    unfold coefQ
    apply div_le_div_of_nonneg_right _ (by positivity)
    have : 0 ≤ (1 - α) * (1 + r) := by positivity
    nlinarith
  have hHle : Hmap (coefP A α β η₂) (coefQ α β η₂ r) α (psi (coefP A α β η₂)
      (coefQ α β η₂ r) α k) ≤ Hmap (coefP A α β η₁) (coefQ α β η₁ r) α
      (psi (coefP A α β η₂) (coefQ α β η₂ r) α k) := by
    unfold Hmap
    have := Real.rpow_pos_of_pos hx2 (1 - α)
    apply div_le_div_of_nonneg_left hx2.le (by positivity)
    nlinarith
  have hψ : psi (coefP A α β η₁) (coefQ α β η₁ r) α k ≤
      psi (coefP A α β η₂) (coefQ α β η₂ r) α k := by
    by_contra hlt
    push Not at hlt
    have := Hmap_strictMonoOn hP1 hQ1 hα hα1 hx2 hx1 hlt
    rw [hH1] at this
    rw [hH2] at hHle
    linarith
  unfold eqMap
  exact min_le_min le_rfl hψ

/-- **`η = 0` is the Solow model** (O&R p. 472): with no borrowing, `ψ(k) = s A k^α` with
`s = (1-α)β/(1+β)`, full depreciation and no growth. -/
theorem eta_zero_solow {A α β r k : ℝ} (hα : 0 < α) (hα1 : α < 1) (hA : 0 < A) (hβ : 0 < β)
    (hk : 0 < k) :
    psi (coefP A α β 0) (coefQ α β 0 r) α k = (1 - α) * β / (1 + β) * (A * k ^ α) := by
  have h1a : 0 < 1 - α := by linarith
  have hP : 0 < coefP A α β 0 := by unfold coefP; positivity
  have hQ0 : coefQ α β 0 r = 0 := by unfold coefQ; ring
  have hka := Real.rpow_pos_of_pos hk α
  rw [hQ0]
  symm
  apply psi_unique hP le_rfl hα hα1 hk (by positivity)
  unfold Hmap coefP
  field_simp
  ring

/-! ## Exercise 2: a productivity rise when `r^A = r` -/

/-- Exercise 2 (O&R p. 512; the printed `y_t = A k_t` should read `A k_t^α`). Start at the
autarky steady state `k^A` of the `A = 1` economy with `r^A = r`
(`(k^A)^{1-α} = β(1-α)/(1+β)`, `1 + r = α (k^A)^{α-1}`), and raise productivity to `A > 1`.
Then (a) the new unconstrained stock is `k̄^U = A^{1/(1-α)} k^A`; (b) the non-convergence
condition (60) fails for every `η ≥ 0`, so the economy always returns to `r^D = r` in the
long run (the unique steady state is `k̄^U`); (c) it gets there in one period iff
`1 + η(1+β)/β ≥ A^{α/(1-α)}`. -/
theorem exercise2 {A α β η r kA : ℝ} (hα : 0 < α) (hα1 : α < 1) (hA : 1 < A) (hβ : 0 < β)
    (hη : 0 ≤ η) (hr : 0 < 1 + r) (hkA : 0 < kA)
    (haut : kA ^ (1 - α) = β * (1 - α) / (1 + β)) (hrA : 1 + r = α * kA ^ (α - 1)) :
    kU A α r = A ^ (1 / (1 - α)) * kA ∧
      ¬ (β / (1 + β) + η) * wage A α (kU A α r) < kU A α r ∧
      kStar A α β η r = kU A α r ∧
      (eqMap A α β η r kA = kU A α r ↔ A ^ (α / (1 - α)) ≤ 1 + η * (1 + β) / β) := by
  have hA0 : 0 < A := by linarith
  have h1a : 0 < 1 - α := by linarith
  have hkAm : kA ^ (α - 1) = (1 + β) / (β * (1 - α)) := by
    rw [show α - 1 = -(1 - α) by ring, Real.rpow_neg hkA.le, haut, inv_div]
  have hsplit : kA = kA ^ α * kA ^ (1 - α) := by
    rw [← Real.rpow_add hkA, show α + (1 - α) = 1 by ring, Real.rpow_one]
  -- (a)
  have hU : kU A α r = A ^ (1 / (1 - α)) * kA := by
    unfold kU
    have e : α * A / (1 + r) = A * kA ^ (1 - α) := by
      rw [hrA, show α - 1 = -(1 - α) by ring, Real.rpow_neg hkA.le]
      field_simp
    rw [e, Real.mul_rpow hA0.le (Real.rpow_pos_of_pos hkA _).le, ← Real.rpow_mul hkA.le,
      mul_one_div_cancel h1a.ne', Real.rpow_one]
  have hUpos := kU_pos hα hA0 hr
  -- wage at k̄^U is k̄^U (1+β)/β
  have hwU : wage A α (kU A α r) = kU A α r * ((1 + β) / β) := by
    unfold wage
    have hrate := kU_rate hα hα1 hA0 hr
    have e : kU A α r ^ α = kU A α r ^ (α - 1) * kU A α r := by
      rw [← Real.rpow_add_one hUpos.ne', sub_add_cancel]
    rw [e]
    have : (1 - α) * A * kU A α r ^ (α - 1) = (1 + β) / β := by
      have h2 : A * kU A α r ^ (α - 1) = (1 + r) / α := by
        field_simp
        linarith
      rw [mul_assoc, h2, hrA, hkAm]
      field_simp
    calc (1 - α) * A * (kU A α r ^ (α - 1) * kU A α r)
        = (1 - α) * A * kU A α r ^ (α - 1) * kU A α r := by ring
      _ = kU A α r * ((1 + β) / β) := by rw [this]; ring
  have hnot : ¬ (β / (1 + β) + η) * wage A α (kU A α r) < kU A α r := by
    rw [hwU, not_lt]
    have : (β / (1 + β) + η) * (kU A α r * ((1 + β) / β)) =
        kU A α r * (1 + η * (1 + β) / β) := by field_simp
    rw [this]
    have : 0 ≤ η * (1 + β) / β := by positivity
    nlinarith
  refine ⟨hU, hnot, by unfold kStar; simp only [hnot, ↓reduceIte], ?_⟩
  rw [one_period_iff hα hα1 hA0 hβ hη hr hkA, hU]
  have hwA : wage A α kA = A * kA * ((1 + β) / β) := by
    unfold wage
    have e : kA ^ α = kA ^ (α - 1) * kA := by
      rw [← Real.rpow_add_one hkA.ne', sub_add_cancel]
    rw [e, hkAm]
    field_simp
  rw [hwA]
  have e2 : (β / (1 + β) + η) * (A * kA * ((1 + β) / β)) =
      A * kA * (1 + η * (1 + β) / β) := by field_simp
  rw [e2]
  have hAp : A ^ (1 / (1 - α)) = A ^ (α / (1 - α)) * A := by
    rw [show 1 / (1 - α) = α / (1 - α) + 1 by field_simp; ring, Real.rpow_add hA0,
      Real.rpow_one]
  rw [hAp]
  constructor
  · intro h
    have : A ^ (α / (1 - α)) * (A * kA) ≤ (1 + η * (1 + β) / β) * (A * kA) := by nlinarith
    exact le_of_mul_le_mul_right this (by positivity)
  · intro h
    have := mul_le_mul_of_nonneg_right h (by positivity : 0 ≤ A * kA)
    nlinarith

/-! ## General depreciation `0 < δ ≤ 1` -/

/-- The gross domestic return with depreciation `δ` (O&R (52)): `1 + r^D = αA x^{α-1} + 1 - δ`. -/
noncomputable def rateD (A α δ x : ℝ) : ℝ := α * A * x ^ (α - 1) + 1 - δ

/-- The unconstrained capital stock with depreciation `δ`: `αA (k̄^U)^{α-1} - δ = r`. -/
noncomputable def kUd (A α δ r : ℝ) : ℝ := (α * A / (r + δ)) ^ (1 / (1 - α))

/-- The coefficient `B = β(1+η)/(1+β)` of (57). -/
noncomputable def coefB (β η : ℝ) : ℝ := β * (1 + η) / (1 + β)

/-- The coefficient `C = (1+r)η/(1+β)` of (57). -/
noncomputable def coefC (β η r : ℝ) : ℝ := (1 + r) * η / (1 + β)

/-- (57) multiplied through by `1 + r^D(x)`: `J(x) = x R^D(x) - wB R^D(x)`; (57) reads
`J(x) = wC`. -/
noncomputable def Jmap (A α δ B w x : ℝ) : ℝ := x * rateD A α δ x - w * B * rateD A α δ x

/-- Equilibrium next-period capital with depreciation `δ`: some optimal plan of the young at
wage `w(k)` and gross domestic return `R^D(x)` invests exactly `x`. -/
def EqRelD (β η r A α δ k x : ℝ) : Prop :=
  ∃ cY b, IsOptimal β (wage A α k) η (rateD A α δ x) (1 + r) cY x b

/-- The solution of `J(x) = wC` (the constrained capital stock for wage `w`). -/
noncomputable def psiD (A α δ B C w : ℝ) : ℝ := by
  classical
  exact if h : ∃ x, 0 < x ∧ Jmap A α δ B w x = w * C then h.choose else 0

/-- The equilibrium map with depreciation `δ`: `Φ_δ(k) = min(k̄^U, ψ_δ(w(k)))`. -/
noncomputable def eqMapD (A α β η r δ k : ℝ) : ℝ :=
  min (kUd A α δ r) (psiD A α δ (coefB β η) (coefC β η r) (wage A α k))

/-- `R^D(x) > 0` for `x > 0`, `δ ≤ 1`. -/
theorem rateD_pos {A α δ x : ℝ} (hα : 0 < α) (hA : 0 < A) (hδ1 : δ ≤ 1) (hx : 0 < x) :
    0 < rateD A α δ x := by
  unfold rateD
  have := Real.rpow_pos_of_pos hx (α - 1)
  nlinarith [mul_pos (mul_pos hα hA) this]

/-- `x R^D(x) = αA x^α + (1-δ) x`. -/
theorem mul_rateD {A α δ x : ℝ} (hx : 0 < x) :
    x * rateD A α δ x = α * A * x ^ α + (1 - δ) * x := by
  unfold rateD
  have : x ^ (α - 1) * x = x ^ α := by rw [← Real.rpow_add_one hx.ne', sub_add_cancel]
  linear_combination (α * A) * this

/-- `k̄^U > 0` (for `r + δ > 0`). -/
theorem kUd_pos {A α δ r : ℝ} (hα : 0 < α) (hA : 0 < A) (hrd : 0 < r + δ) : 0 < kUd A α δ r :=
  Real.rpow_pos_of_pos (by positivity) _

/-- At `k̄^U` the domestic return equals the world return: `R^D(k̄^U) = 1 + r`. -/
theorem kUd_rate {A α δ r : ℝ} (hα : 0 < α) (hα1 : α < 1) (hA : 0 < A) (hrd : 0 < r + δ) :
    rateD A α δ (kUd A α δ r) = 1 + r := by
  have hU := kUd_pos hα hA hrd
  have hp : kUd A α δ r ^ (1 - α) = α * A / (r + δ) := by
    unfold kUd
    rw [← Real.rpow_mul (by positivity), one_div_mul_cancel (by linarith), Real.rpow_one]
  unfold rateD
  rw [show α - 1 = -(1 - α) by ring, Real.rpow_neg hU.le, hp, inv_div]
  field_simp
  ring

/-- `r^D > r` iff `x < k̄^U`. -/
theorem rateD_gt_iff {A α δ r x : ℝ} (hα : 0 < α) (hα1 : α < 1) (hA : 0 < A)
    (hrd : 0 < r + δ) (hx : 0 < x) : 1 + r < rateD A α δ x ↔ x < kUd A α δ r := by
  have hU := kUd_pos hα hA hrd
  rw [← kUd_rate hα hα1 hA hrd]
  unfold rateD
  constructor
  · intro h
    by_contra hle
    push Not at hle
    have := Real.rpow_le_rpow_of_nonpos hU hle (by linarith : α - 1 ≤ 0)
    have := mul_le_mul_of_nonneg_left this (by positivity : (0 : ℝ) ≤ α * A)
    linarith
  · intro h
    have := Real.rpow_lt_rpow_of_neg hx h (by linarith : α - 1 < 0)
    have := mul_lt_mul_of_pos_left this (by positivity : (0 : ℝ) < α * A)
    linarith

/-- `r^D = r` iff `x = k̄^U`. -/
theorem rateD_eq_iff {A α δ r x : ℝ} (hα : 0 < α) (hα1 : α < 1) (hA : 0 < A)
    (hrd : 0 < r + δ) (hx : 0 < x) : rateD A α δ x = 1 + r ↔ x = kUd A α δ r := by
  have hU := kUd_pos hα hA hrd
  constructor
  · intro h
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · linarith [(rateD_gt_iff hα hα1 hA hrd hx).mpr hlt]
    · have := Real.rpow_lt_rpow_of_neg hU hgt (by linarith : α - 1 < 0)
      have := mul_lt_mul_of_pos_left this (by positivity : (0 : ℝ) < α * A)
      have hk := kUd_rate hα hα1 hA hrd
      unfold rateD at h hk
      linarith
  · intro h
    rw [h, kUd_rate hα hα1 hA hrd]

/-- `J` is strictly increasing on `(0, ∞)` (for `w, B ≥ 0`, `δ ≤ 1`): `xR^D(x)` rises and
`R^D` falls. This is what makes the general-`δ` map well defined. -/
theorem Jmap_strictMonoOn {A α δ B w : ℝ} (hα : 0 < α) (hα1 : α < 1) (hA : 0 < A) (hδ1 : δ ≤ 1)
    (hB : 0 ≤ B) (hw : 0 ≤ w) : StrictMonoOn (Jmap A α δ B w) (Set.Ioi 0) := by
  intro x hx y hy hxy
  have hx0 : 0 < x := hx
  have hy0 : 0 < y := hy
  unfold Jmap
  rw [mul_rateD hx0, mul_rateD hy0]
  have h1 : x ^ α < y ^ α := Real.rpow_lt_rpow hx0.le hxy hα
  have h2 : rateD A α δ y ≤ rateD A α δ x := by
    unfold rateD
    have := Real.rpow_le_rpow_of_nonpos hx0 hxy.le (by linarith : α - 1 ≤ 0)
    nlinarith [mul_pos hα hA]
  have h3 := mul_le_mul_of_nonneg_left h2 (mul_nonneg hw hB)
  nlinarith [mul_pos hα hA]

/-- **(57) with depreciation `δ`**: `x = (B + (1+r)η/((1+β)R^D(x))) w` iff `J(x) = wC`. -/
theorem root57D_iff {A α δ β η r w x : ℝ} (hα : 0 < α) (hA : 0 < A) (hδ1 : δ ≤ 1)
    (hβ : 0 < β) (hx : 0 < x) :
    x = (β * (1 + η) / (1 + β) + (1 + r) * η / ((1 + β) * rateD A α δ x)) * w ↔
      Jmap A α δ (coefB β η) w x = w * coefC β η r := by
  have hR := rateD_pos hα hA hδ1 hx (δ := δ)
  unfold Jmap coefB coefC
  set R := rateD A α δ x
  have hb : (1 + β) ≠ 0 := by linarith
  constructor
  · intro h
    rw [h]
    field_simp
    ring
  · intro h
    field_simp at h ⊢
    linarith

/-- **The constrained equation has a solution** for every wage `w > 0` (`B > 0`, `C ≥ 0`):
`J(wB) = 0 ≤ wC`, and `J(x) ≥ αAx^α/2` for `x ≥ 2wB`. -/
theorem Jmap_surj {A α δ B C w : ℝ} (hα : 0 < α) (hA : 0 < A) (hδ1 : δ ≤ 1)
    (hB : 0 < B) (hC : 0 ≤ C) (hw : 0 < w) :
    ∃ x, w * B ≤ x ∧ Jmap A α δ B w x = w * C := by
  set a := w * B with ha
  have ha0 : 0 < a := by positivity
  set b := max (2 * a) ((2 * (w * C) / (α * A)) ^ (1 / α)) with hb
  have hab : a ≤ b := le_trans (by linarith) (le_max_left _ _)
  have hb0 : 0 < b := lt_of_lt_of_le ha0 hab
  have hJa : Jmap A α δ B w a = 0 := by unfold Jmap; rw [ha]; ring
  have hJb : w * C ≤ Jmap A α δ B w b := by
    have h2a : 2 * a ≤ b := le_max_left _ _
    have hbα : 2 * (w * C) / (α * A) ≤ b ^ α := by
      have h1 : (2 * (w * C) / (α * A)) ^ (1 / α) ≤ b := le_max_right _ _
      have h2 := Real.rpow_le_rpow (by positivity) h1 hα.le
      rwa [← Real.rpow_mul (by positivity), one_div_mul_cancel hα.ne', Real.rpow_one] at h2
    have hR : α * A * b ^ (α - 1) ≤ rateD A α δ b := by unfold rateD; linarith
    have hbb : b ^ (α - 1) * b = b ^ α := by rw [← Real.rpow_add_one hb0.ne', sub_add_cancel]
    have hpos := Real.rpow_pos_of_pos hb0 (α - 1)
    unfold Jmap
    have e : b * rateD A α δ b - w * B * rateD A α δ b = (b - a) * rateD A α δ b := by
      rw [ha]; ring
    rw [e]
    have hba : b / 2 ≤ b - a := by linarith
    have : (b - a) * rateD A α δ b ≥ b / 2 * (α * A * b ^ (α - 1)) :=
      mul_le_mul hba hR (by positivity) (by linarith)
    have : b / 2 * (α * A * b ^ (α - 1)) = α * A * b ^ α / 2 := by rw [← hbb]; ring
    have : w * C ≤ α * A * b ^ α / 2 := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < α * A)] at hbα
      linarith
    linarith
  have hsub : Set.Icc a b ⊆ Set.Ioi 0 := fun z hz => lt_of_lt_of_le ha0 hz.1
  have hcont : ContinuousOn (Jmap A α δ B w) (Set.Icc a b) := by
    have hR : ContinuousOn (rateD A α δ) (Set.Icc a b) := by
      unfold rateD
      apply ContinuousOn.sub _ continuousOn_const
      apply ContinuousOn.add _ continuousOn_const
      apply ContinuousOn.mul continuousOn_const
      exact fun z hz => (Real.continuousAt_rpow_const z (α - 1)
        (Or.inl (hsub hz).ne')).continuousWithinAt
    unfold Jmap
    exact (continuousOn_id.mul hR).sub (continuousOn_const.mul hR)
  obtain ⟨x, hx, hJx⟩ := intermediate_value_Icc hab hcont
    ⟨by rw [hJa]; positivity, hJb⟩
  exact ⟨x, hx.1, hJx⟩

/-- `ψ_δ(w) ≥ wB > 0` and `J(ψ_δ(w)) = wC`. -/
theorem psiD_spec {A α δ B C w : ℝ} (hα : 0 < α) (hα1 : α < 1) (hA : 0 < A) (hδ1 : δ ≤ 1)
    (hB : 0 < B) (hC : 0 ≤ C) (hw : 0 < w) :
    w * B ≤ psiD A α δ B C w ∧ 0 < psiD A α δ B C w ∧
      Jmap A α δ B w (psiD A α δ B C w) = w * C := by
  obtain ⟨x, hx, hJ⟩ := Jmap_surj hα hA hδ1 hB hC hw
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx
  have h : ∃ x, 0 < x ∧ Jmap A α δ B w x = w * C := ⟨x, hx0, hJ⟩
  have hspec : 0 < psiD A α δ B C w ∧ Jmap A α δ B w (psiD A α δ B C w) = w * C := by
    unfold psiD
    split_ifs
    exact h.choose_spec
  have hmono := Jmap_strictMonoOn hα hα1 hA hδ1 hB.le hw.le (δ := δ)
  refine ⟨?_, hspec.1, hspec.2⟩
  by_contra hlt
  push Not at hlt
  have hwB : 0 < w * B := by positivity
  have := hmono hspec.1 hwB hlt
  have hJwB : Jmap A α δ B w (w * B) = 0 := by unfold Jmap; ring
  rw [hspec.2, hJwB] at this
  nlinarith [mul_nonneg hw.le hC]

/-- Uniqueness of the constrained solution. -/
theorem psiD_unique {A α δ B C w x : ℝ} (hα : 0 < α) (hα1 : α < 1) (hA : 0 < A)
    (hδ1 : δ ≤ 1) (hB : 0 < B) (hC : 0 ≤ C) (hw : 0 < w) (hx : 0 < x)
    (hJ : Jmap A α δ B w x = w * C) : x = psiD A α δ B C w := by
  obtain ⟨-, hp, hJp⟩ := psiD_spec hα hα1 hA hδ1 hB hC hw (δ := δ)
  exact (Jmap_strictMonoOn hα hα1 hA hδ1 hB.le hw.le).injOn hx hp (hJ.trans hJp.symm)

/-- `ψ_δ` is strictly increasing in the wage. -/
theorem psiD_strictMono {A α δ B C w₁ w₂ : ℝ} (hα : 0 < α) (hα1 : α < 1) (hA : 0 < A)
    (hδ1 : δ ≤ 1) (hB : 0 < B) (hC : 0 ≤ C) (hw₁ : 0 < w₁) (hw : w₁ < w₂) :
    psiD A α δ B C w₁ < psiD A α δ B C w₂ := by
  have hw₂ : 0 < w₂ := hw₁.trans hw
  obtain ⟨-, h1, hJ1⟩ := psiD_spec hα hα1 hA hδ1 hB hC hw₁ (δ := δ)
  obtain ⟨-, h2, hJ2⟩ := psiD_spec hα hα1 hA hδ1 hB hC hw₂ (δ := δ)
  by_contra hle
  push Not at hle
  have hm := (Jmap_strictMonoOn hα hα1 hA hδ1 hB.le hw₂.le (δ := δ)).monotoneOn h2 h1 hle
  have hR := rateD_pos hα hA hδ1 h1 (δ := δ)
  unfold Jmap at hm hJ1 hJ2
  have : w₁ * B * rateD A α δ (psiD A α δ B C w₁) < w₂ * B * rateD A α δ (psiD A α δ B C w₁) :=
    mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_right hw hB) hR
  nlinarith [mul_le_mul_of_nonneg_right hw.le hC]

/-- **The growth factor falls with capital (general `δ`)**: for `k₁ < k₂`,
`ψ_δ(w(k₂))/k₂ < ψ_δ(w(k₁))/k₁`. Proof: with `λ = k₂/k₁ > 1`, `J_{w(k₂)}(λψ₁)` exceeds its
target by `(λ - λ^α)(1-δ)ψ₁ + (λ^α - λ^{2α-1})w₁BαAψ₁^{α-1} > 0`. -/
theorem psiD_ratio_anti {A α δ B C k₁ k₂ : ℝ} (hα : 0 < α) (hα1 : α < 1) (hA : 0 < A)
    (hδ1 : δ ≤ 1) (hB : 0 < B) (hC : 0 ≤ C) (hk₁ : 0 < k₁) (hk : k₁ < k₂) :
    psiD A α δ B C (wage A α k₂) / k₂ < psiD A α δ B C (wage A α k₁) / k₁ := by
  have h1a : 0 < 1 - α := by linarith
  have hk₂ : 0 < k₂ := hk₁.trans hk
  set lam := k₂ / k₁ with hlam
  have hl1 : 1 < lam := by rw [hlam, one_lt_div hk₁]; exact hk
  have hl0 : 0 < lam := by linarith
  have hw₁ : 0 < wage A α k₁ := by unfold wage; have := Real.rpow_pos_of_pos hk₁ α; positivity
  have hw₂ : 0 < wage A α k₂ := by unfold wage; have := Real.rpow_pos_of_pos hk₂ α; positivity
  have hwl : wage A α k₂ = lam ^ α * wage A α k₁ := by
    unfold wage
    rw [show k₂ = lam * k₁ by rw [hlam]; field_simp, Real.mul_rpow hl0.le hk₁.le]
    ring
  obtain ⟨-, hx1, hJ1⟩ := psiD_spec hα hα1 hA hδ1 hB hC hw₁ (δ := δ)
  set x₁ := psiD A α δ B C (wage A α k₁)
  set w₁ := wage A α k₁
  obtain ⟨-, hx2, hJ2⟩ := psiD_spec hα hα1 hA hδ1 hB hC hw₂ (δ := δ)
  -- evaluate J_{w₂} at λx₁
  have hlx : 0 < lam * x₁ := by positivity
  have hpa : (lam * x₁) ^ α = lam ^ α * x₁ ^ α := Real.mul_rpow hl0.le hx1.le
  have hpb : (lam * x₁) ^ (α - 1) = lam ^ (α - 1) * x₁ ^ (α - 1) := Real.mul_rpow hl0.le hx1.le
  have hl2 : lam ^ α * lam ^ (α - 1) = lam ^ (2 * α - 1) := by
    rw [← Real.rpow_add hl0]; ring_nf
  have hg1 : lam ^ α < lam := by
    have := Real.rpow_lt_rpow_of_exponent_lt hl1 hα1
    rwa [Real.rpow_one] at this
  have hg2 : lam ^ (2 * α - 1) < lam ^ α := Real.rpow_lt_rpow_of_exponent_lt hl1 (by linarith)
  have hxp := Real.rpow_pos_of_pos hx1 (α - 1)
  have key : wage A α k₂ * C < Jmap A α δ B (wage A α k₂) (lam * x₁) := by
    have e1 : Jmap A α δ B (wage A α k₂) (lam * x₁) = α * A * (lam * x₁) ^ α +
        (1 - δ) * (lam * x₁) - wage A α k₂ * B * rateD A α δ (lam * x₁) := by
      unfold Jmap
      rw [mul_rateD hlx]
    have e0 : w₁ * C = α * A * x₁ ^ α + (1 - δ) * x₁ - w₁ * B * rateD A α δ x₁ := by
      rw [← hJ1]
      unfold Jmap
      rw [mul_rateD hx1]
    rw [e1, hwl, hpa]
    unfold rateD at e0 ⊢
    rw [hpb]
    have hdiff : α * A * (lam ^ α * x₁ ^ α) + (1 - δ) * (lam * x₁) - lam ^ α * w₁ * B *
        (α * A * (lam ^ (α - 1) * x₁ ^ (α - 1)) + 1 - δ) - lam ^ α * w₁ * C =
        (lam - lam ^ α) * (1 - δ) * x₁ +
          (lam ^ α - lam ^ α * lam ^ (α - 1)) * (w₁ * B * (α * A * x₁ ^ (α - 1))) := by
      linear_combination (-lam ^ α) * e0
    rw [hl2] at hdiff
    have t1 : 0 ≤ (lam - lam ^ α) * (1 - δ) * x₁ :=
      mul_nonneg (mul_nonneg (by linarith) (by linarith)) hx1.le
    have t2 : 0 < (lam ^ α - lam ^ (2 * α - 1)) * (w₁ * B * (α * A * x₁ ^ (α - 1))) :=
      mul_pos (by linarith) (by positivity)
    linarith
  have hlt : psiD A α δ B C (wage A α k₂) < lam * x₁ := by
    by_contra hge
    push Not at hge
    have := (Jmap_strictMonoOn hα hα1 hA hδ1 hB.le hw₂.le (δ := δ)).monotoneOn hlx hx2 hge
    rw [hJ2] at this
    linarith
  rw [div_lt_div_iff₀ hk₂ hk₁]
  calc psiD A α δ B C (wage A α k₂) * k₁ < lam * x₁ * k₁ := mul_lt_mul_of_pos_right hlt hk₁
    _ = x₁ * k₂ := by rw [hlam]; field_simp

/-- **Slack iff capacity** (general `δ`): `k̄^U ≤ ψ_δ(w) ⟺ k̄^U ≤ βw/(1+β) + ηw`. -/
theorem kUd_le_psiD_iff {A α δ β η r w : ℝ} (hα : 0 < α) (hα1 : α < 1) (hA : 0 < A)
    (hδ1 : δ ≤ 1) (hβ : 0 < β) (hη : 0 ≤ η) (hr : 0 < 1 + r) (hrd : 0 < r + δ) (hw : 0 < w) :
    kUd A α δ r ≤ psiD A α δ (coefB β η) (coefC β η r) w ↔
      kUd A α δ r ≤ (β / (1 + β) + η) * w := by
  have hB : 0 < coefB β η := by unfold coefB; positivity
  have hC : 0 ≤ coefC β η r := by unfold coefC; positivity
  have hU := kUd_pos hα hA hrd
  obtain ⟨-, hx, hJ⟩ := psiD_spec hα hα1 hA hδ1 hB hC hw (δ := δ)
  have hmono := Jmap_strictMonoOn hα hα1 hA hδ1 hB.le hw.le (δ := δ)
  have key : Jmap A α δ (coefB β η) w (kUd A α δ r) ≤ w * coefC β η r ↔
      kUd A α δ r ≤ (β / (1 + β) + η) * w := by
    unfold Jmap
    rw [kUd_rate hα hα1 hA hrd]
    unfold coefB coefC
    constructor
    · intro h
      have e : (β / (1 + β) + η) * w = w * (β * (1 + η) / (1 + β)) +
          w * ((1 + r) * η / (1 + β)) / (1 + r) := by field_simp; ring
      rw [e, ← sub_le_iff_le_add', le_div_iff₀ hr]
      linarith
    · intro h
      have e : (β / (1 + β) + η) * w = w * (β * (1 + η) / (1 + β)) +
          w * ((1 + r) * η / (1 + β)) / (1 + r) := by field_simp; ring
      rw [e, ← sub_le_iff_le_add', le_div_iff₀ hr] at h
      linarith
  rw [← key, ← hJ]
  exact ⟨fun h => hmono.monotoneOn hU hx h, fun h => by
    by_contra hlt
    push Not at hlt
    have := hmono hx hU hlt
    linarith⟩

/-- **Characterisation of equilibrium with depreciation `δ`**: for `k > 0`, next period's
capital `x > 0` is an equilibrium iff `x = min(k̄^U, ψ_δ(w(k)))`. -/
theorem eqRelD_iff {β η r A α δ k x : ℝ} (hα : 0 < α) (hα1 : α < 1) (hA : 0 < A)
    (hβ : 0 < β) (hη : 0 ≤ η) (hδ1 : δ ≤ 1) (hr : 0 < 1 + r) (hrd : 0 < r + δ) (hk : 0 < k)
    (hx : 0 < x) :
    EqRelD β η r A α δ k x ↔ x = eqMapD A α β η r δ k := by
  have hB : 0 < coefB β η := by unfold coefB; positivity
  have hC : 0 ≤ coefC β η r := by unfold coefC; positivity
  have hw : 0 < wage A α k := by
    unfold wage
    have : 0 < 1 - α := by linarith
    have := Real.rpow_pos_of_pos hk α
    positivity
  have hRD := rateD_pos hα hA hδ1 hx (δ := δ)
  obtain ⟨-, hψ, hJψ⟩ := psiD_spec hα hα1 hA hδ1 hB hC hw (δ := δ)
  unfold eqMapD
  constructor
  · rintro ⟨cY, b, ho⟩
    have hge := rate_ge_of_optimal hβ hw hη hRD ho hx
    rcases eq_or_lt_of_le hge with heq | hlt
    · have hxU : x = kUd A α δ r := (rateD_eq_iff hα hα1 hA hrd hx).mp heq.symm
      have ho' : IsOptimal β (wage A α k) η (1 + r) (1 + r) cY x b := by rwa [← heq] at ho
      have hb0 : -(η * wage A α k) ≤ β * wage A α k / (1 + β) := by
        have : 0 ≤ β * wage A α k / (1 + β) := by positivity
        nlinarith [mul_nonneg hη hw.le]
      have hopt0 := optimal_equal (η := η) hβ hw hr le_rfl hb0 (by ring)
      have hu := le_antisymm (hopt0.2 cY x b ho'.1) (ho'.2 _ _ _ hopt0.1)
      have hle : cY + ((1 + r) * x + (1 + r) * b) / (1 + r) ≤ wage A α k := by
        rw [intertemporal_budget hr ho'.1.budget]
        simp
      have hmax := (log_consumer hβ hr hw ho'.1.posY ho'.1.posO hle).2
      have hcO : (1 + r) * 0 + (1 + r) * (β * wage A α k / (1 + β)) =
          β * (1 + r) * wage A α k / (1 + β) := by ring
      unfold utility at hu
      rw [hcO] at hu
      obtain ⟨hc1, -⟩ := hmax hu
      have hbud := ho'.1.budget
      have hbor := ho'.1.borrow
      have hcap : kUd A α δ r ≤ (β / (1 + β) + η) * wage A α k := by
        rw [← hxU]
        rw [hc1] at hbud
        have : x = wage A α k - wage A α k / (1 + β) - b := by linarith
        rw [this]
        have e : wage A α k - wage A α k / (1 + β) = β / (1 + β) * wage A α k := by
          field_simp
          ring
        rw [e]
        nlinarith
      have := (kUd_le_psiD_iff hα hα1 hA hδ1 hβ hη hr hrd hw).mpr hcap
      rw [min_eq_left this]
      exact hxU
    · have hxlt : x < kUd A α δ r := (rateD_gt_iff hα hα1 hA hrd hx).mp hlt
      have huniq := (optimal_binding hβ hw hη (by linarith) hlt).2 cY x b ho
      have h57 := huniq.2.1
      rw [binding_plan_eq_57 hβ hRD] at h57
      have hxψ := psiD_unique hα hα1 hA hδ1 hB hC hw hx ((root57D_iff hα hA hδ1 hβ hx).mp h57)
      rw [← hxψ, min_eq_right hxlt.le]
  · intro hmin
    by_cases hcase : kUd A α δ r ≤ psiD A α δ (coefB β η) (coefC β η r) (wage A α k)
    · rw [min_eq_left hcase] at hmin
      have hcap := (kUd_le_psiD_iff hα hα1 hA hδ1 hβ hη hr hrd hw).mp hcase
      have hrate : rateD A α δ x = 1 + r := (rateD_eq_iff hα hα1 hA hrd hx).mpr hmin
      refine ⟨wage A α k / (1 + β), β * wage A α k / (1 + β) - x, ?_⟩
      rw [hrate]
      apply optimal_equal hβ hw hr hx.le _ (by ring)
      have e : β * wage A α k / (1 + β) = β / (1 + β) * wage A α k := by ring
      rw [e, hmin]
      nlinarith
    · push Not at hcase
      rw [min_eq_right hcase.le] at hmin
      have hlt : 1 + r < rateD A α δ x :=
        (rateD_gt_iff hα hα1 hA hrd hx).mpr (hmin ▸ hcase)
      obtain ⟨ho, -⟩ := optimal_binding hβ hw hη (by linarith) hlt
      have hJx : Jmap A α δ (coefB β η) (wage A α k) x = wage A α k * coefC β η r := by
        rw [hmin]
        exact hJψ
      have hkx : wage A α k - (wage A α k + (rateD A α δ x - (1 + r)) *
          (η * wage A α k) / rateD A α δ x) / (1 + β) + η * wage A α k = x := by
        rw [binding_plan_eq_57 hβ hRD]
        exact ((root57D_iff hα hA hδ1 hβ hx).mpr hJx).symm
      rw [hkx] at ho
      exact ⟨_, _, ho⟩

/-- Properties of `Φ_δ`: positive, increasing, and `Φ_δ(k)/k` strictly decreasing. -/
theorem eqMapD_props {A α β η r δ : ℝ} (hα : 0 < α) (hα1 : α < 1) (hA : 0 < A) (hβ : 0 < β)
    (hη : 0 ≤ η) (hδ1 : δ ≤ 1) (hr : 0 < 1 + r) (hrd : 0 < r + δ) :
    (∀ k, 0 < k → 0 < eqMapD A α β η r δ k) ∧
      (∀ a b, 0 < a → a ≤ b → eqMapD A α β η r δ a ≤ eqMapD A α β η r δ b) ∧
      (∀ a b, 0 < a → a < b → eqMapD A α β η r δ b / b < eqMapD A α β η r δ a / a) := by
  have hB : 0 < coefB β η := by unfold coefB; positivity
  have hC : 0 ≤ coefC β η r := by unfold coefC; positivity
  have hU := kUd_pos hα hA hrd
  have hwpos : ∀ k, 0 < k → 0 < wage A α k := fun k hk => by
    unfold wage
    have : 0 < 1 - α := by linarith
    have := Real.rpow_pos_of_pos hk α
    positivity
  refine ⟨fun k hk => lt_min hU (psiD_spec hα hα1 hA hδ1 hB hC (hwpos k hk) (δ := δ)).2.1,
    fun a b ha hab => ?_, fun a b ha hab => ?_⟩
  · unfold eqMapD
    rcases eq_or_lt_of_le hab with h | h
    · rw [h]
    · have hw : wage A α a < wage A α b := by
        unfold wage
        have := Real.rpow_lt_rpow ha.le h hα
        have : 0 < (1 - α) * A := by
          have : 0 < 1 - α := by linarith
          positivity
        nlinarith
      exact min_le_min le_rfl (psiD_strictMono hα hα1 hA hδ1 hB hC (hwpos a ha) hw).le
  · have hb : 0 < b := ha.trans hab
    unfold eqMapD
    have h1 := psiD_ratio_anti hα hα1 hA hδ1 hB hC ha hab (δ := δ)
    have h2 : kUd A α δ r / b < kUd A α δ r / a := div_lt_div_of_pos_left hU ha hab
    rw [← min_div_div_right ha.le]
    apply lt_min
    · calc _ ≤ kUd A α δ r / b := div_le_div_of_nonneg_right (min_le_left _ _) hb.le
        _ < _ := h2
    · calc _ ≤ psiD A α δ (coefB β η) (coefC β η r) (wage A α b) / b :=
            div_le_div_of_nonneg_right (min_le_right _ _) hb.le
        _ < _ := h1

/-- An increasing function with a decreasing growth factor is continuous on `(0, ∞)`:
`f(k) min(1, k'/k) ≤ f(k') ≤ f(k) max(1, k'/k)`. -/
theorem continuousOn_of_mono_ratio {f : ℝ → ℝ} (hpos : ∀ k, 0 < k → 0 < f k)
    (hmono : ∀ a b, 0 < a → a ≤ b → f a ≤ f b)
    (hratio : ∀ a b, 0 < a → a < b → f b / b < f a / a) : ContinuousOn f (Set.Ioi 0) := by
  intro k hk
  have hk0 : 0 < k := hk
  apply ContinuousAt.continuousWithinAt
  have hlow : ∀ k', 0 < k' → f k * min 1 (k' / k) ≤ f k' := by
    intro k' hk'
    rcases le_or_gt k k' with h | h
    · have := hmono k k' hk0 h
      have := hpos k hk0
      nlinarith [min_le_left 1 (k' / k)]
    · have hr := hratio k' k hk' h
      rw [div_lt_div_iff₀ hk0 hk'] at hr
      have : f k * (k' / k) ≤ f k' := by
        rw [mul_div_assoc', div_le_iff₀ hk0]
        linarith
      have := hpos k hk0
      nlinarith [min_le_right 1 (k' / k)]
  have hup : ∀ k', 0 < k' → f k' ≤ f k * max 1 (k' / k) := by
    intro k' hk'
    rcases le_or_gt k k' with h | h
    · rcases eq_or_lt_of_le h with he | hlt
      · rw [← he, div_self hk0.ne', max_self, mul_one]
      · have hr := hratio k k' hk0 hlt
        rw [div_lt_div_iff₀ hk' hk0] at hr
        have : f k' ≤ f k * (k' / k) := by
          rw [mul_div_assoc', le_div_iff₀ hk0]
          linarith
        have := hpos k hk0
        nlinarith [le_max_right 1 (k' / k)]
    · have := hmono k' k hk' h.le
      have := hpos k hk0
      nlinarith [le_max_left 1 (k' / k)]
  have hc1 : Tendsto (fun k' => f k * min 1 (k' / k)) (𝓝 k) (𝓝 (f k)) := by
    have : Tendsto (fun k' => f k * min 1 (k' / k)) (𝓝 k) (𝓝 (f k * min 1 (k / k))) :=
      (continuous_const.mul (continuous_const.min (continuous_id.div_const k))).tendsto k
    rwa [div_self hk0.ne', min_self, mul_one] at this
  have hc2 : Tendsto (fun k' => f k * max 1 (k' / k)) (𝓝 k) (𝓝 (f k)) := by
    have : Tendsto (fun k' => f k * max 1 (k' / k)) (𝓝 k) (𝓝 (f k * max 1 (k / k))) :=
      (continuous_const.mul (continuous_const.max (continuous_id.div_const k))).tendsto k
    rwa [div_self hk0.ne', max_self, mul_one] at this
  have hev : ∀ᶠ k' in 𝓝 k, 0 < k' := lt_mem_nhds hk0
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hc1 hc2
    (hev.mono fun k' hk' => hlow k' hk') (hev.mono fun k' hk' => hup k' hk')

/-- **A steady state exists and is unique (general `δ`)**: there is exactly one `k* > 0`
with `Φ_δ(k*) = k*`. If `βw̄/(1+β) + ηw̄ ≥ k̄^U` (`w̄ = w(k̄^U)`, (60) fails) then
`k* = k̄^U`; otherwise `k* < k̄^U` solves the constrained equation, and `r^D > r` there. -/
theorem steadyD_existsUnique {A α β η r δ : ℝ} (hα : 0 < α) (hα1 : α < 1) (hA : 0 < A)
    (hβ : 0 < β) (hη : 0 ≤ η) (hδ1 : δ ≤ 1) (hr : 0 < 1 + r) (hrd : 0 < r + δ) :
    (∃! ks, 0 < ks ∧ eqMapD A α β η r δ ks = ks) ∧
      ((β / (1 + β) + η) * wage A α (kUd A α δ r) < kUd A α δ r →
        ∃ ks, 0 < ks ∧ ks < kUd A α δ r ∧ eqMapD A α β η r δ ks = ks ∧
          1 + r < rateD A α δ ks) ∧
      (¬ (β / (1 + β) + η) * wage A α (kUd A α δ r) < kUd A α δ r →
        eqMapD A α β η r δ (kUd A α δ r) = kUd A α δ r) := by
  have hB : 0 < coefB β η := by unfold coefB; positivity
  have hC : 0 ≤ coefC β η r := by unfold coefC; positivity
  have h1a : 0 < 1 - α := by linarith
  have hU := kUd_pos hα hA hrd
  obtain ⟨hGpos, hmono, hratio⟩ := eqMapD_props hα hα1 hA hβ hη hδ1 hr hrd (δ := δ)
  have hwpos : ∀ k, 0 < k → 0 < wage A α k := fun k hk => by
    unfold wage
    have := Real.rpow_pos_of_pos hk α
    positivity
  set ψ : ℝ → ℝ := fun k => psiD A α δ (coefB β η) (coefC β η r) (wage A α k) with hψdef
  have hψpos : ∀ k, 0 < k → 0 < ψ k := fun k hk =>
    (psiD_spec hα hα1 hA hδ1 hB hC (hwpos k hk) (δ := δ)).2.1
  have hψmono : ∀ a b, 0 < a → a ≤ b → ψ a ≤ ψ b := by
    intro a b ha hab
    rcases eq_or_lt_of_le hab with h | h
    · rw [h]
    · have hw : wage A α a < wage A α b := by
        unfold wage
        have := Real.rpow_lt_rpow ha.le h hα
        nlinarith [mul_pos h1a hA]
      exact (psiD_strictMono hα hα1 hA hδ1 hB hC (hwpos a ha) hw).le
  have hψratio : ∀ a b, 0 < a → a < b → ψ b / b < ψ a / a :=
    fun a b ha hab => psiD_ratio_anti hα hα1 hA hδ1 hB hC ha hab (δ := δ)
  have hψcont := continuousOn_of_mono_ratio hψpos hψmono hψratio
  have huniq : ∀ k₁ k₂, 0 < k₁ → 0 < k₂ → eqMapD A α β η r δ k₁ = k₁ →
      eqMapD A α β η r δ k₂ = k₂ → k₁ = k₂ := by
    intro k₁ k₂ h1 h2 e1 e2
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have := hratio k₁ k₂ h1 hlt
      rw [e1, e2, div_self h1.ne', div_self h2.ne'] at this
      exact lt_irrefl _ this
    · have := hratio k₂ k₁ h2 hgt
      rw [e1, e2, div_self h1.ne', div_self h2.ne'] at this
      exact lt_irrefl _ this
  have hslack : ¬ (β / (1 + β) + η) * wage A α (kUd A α δ r) < kUd A α δ r →
      eqMapD A α β η r δ (kUd A α δ r) = kUd A α δ r := by
    intro h
    push Not at h
    unfold eqMapD
    rw [min_eq_left ((kUd_le_psiD_iff hα hα1 hA hδ1 hβ hη hr hrd (hwpos _ hU)).mpr h)]
  have hcons : (β / (1 + β) + η) * wage A α (kUd A α δ r) < kUd A α δ r →
      ∃ ks, 0 < ks ∧ ks < kUd A α δ r ∧ eqMapD A α β η r δ ks = ks ∧
        1 + r < rateD A α δ ks := by
    intro h60
    have hψU : ψ (kUd A α δ r) < kUd A α δ r := by
      by_contra hge
      push Not at hge
      have := (kUd_le_psiD_iff hα hα1 hA hδ1 hβ hη hr hrd (hwpos _ hU)).mp hge
      linarith
    -- a small k₀ with ψ(k₀) > k₀
    set m := (1 - α) * A * coefB β η with hm
    have hm0 : 0 < m := by positivity
    set k₀ := min (kUd A α δ r / 2) ((m / 2) ^ (1 / (1 - α))) with hk₀
    have hk₀pos : 0 < k₀ := lt_min (by positivity) (Real.rpow_pos_of_pos (by positivity) _)
    have hk₀U : k₀ < kUd A α δ r := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have hk₀p : k₀ ^ (1 - α) ≤ m / 2 := by
      have h1 : k₀ ≤ (m / 2) ^ (1 / (1 - α)) := min_le_right _ _
      have h2 := Real.rpow_le_rpow hk₀pos.le h1 h1a.le
      rwa [← Real.rpow_mul (by positivity), one_div_mul_cancel h1a.ne', Real.rpow_one] at h2
    have hψk₀ : k₀ < ψ k₀ := by
      have hlow := (psiD_spec hα hα1 hA hδ1 hB hC (hwpos k₀ hk₀pos) (δ := δ)).1
      have hs : k₀ = k₀ ^ α * k₀ ^ (1 - α) := by
        rw [← Real.rpow_add hk₀pos, show α + (1 - α) = 1 by ring, Real.rpow_one]
      have hka := Real.rpow_pos_of_pos hk₀pos α
      have : k₀ < wage A α k₀ * coefB β η := by
        unfold wage
        calc k₀ = k₀ ^ α * k₀ ^ (1 - α) := hs
          _ ≤ k₀ ^ α * (m / 2) := mul_le_mul_of_nonneg_left hk₀p hka.le
          _ < k₀ ^ α * m := by nlinarith
          _ = (1 - α) * A * k₀ ^ α * coefB β η := by rw [hm]; ring
      exact lt_of_lt_of_le this hlow
    have hcont : ContinuousOn (fun k => ψ k - k) (Set.Icc k₀ (kUd A α δ r)) :=
      (hψcont.mono fun z hz => lt_of_lt_of_le hk₀pos hz.1).sub continuousOn_id
    obtain ⟨ks, hks, hks0⟩ := intermediate_value_Icc' hk₀U.le hcont
      ⟨show ψ (kUd A α δ r) - kUd A α δ r ≤ 0 by linarith,
        show (0 : ℝ) ≤ ψ k₀ - k₀ by linarith⟩
    simp only at hks0
    have hksU : ks < kUd A α δ r := by
      rcases eq_or_lt_of_le hks.2 with h | h
      · rw [h] at hks0
        linarith
      · exact h
    have hks0' : 0 < ks := lt_of_lt_of_le hk₀pos hks.1
    refine ⟨ks, hks0', hksU, ?_, (rateD_gt_iff hα hα1 hA hrd hks0').mpr hksU⟩
    unfold eqMapD
    have : ψ ks = ks := by linarith
    rw [show psiD A α δ (coefB β η) (coefC β η r) (wage A α ks) = ks from this,
      min_eq_right hksU.le]
  refine ⟨?_, hcons, hslack⟩
  by_cases h60 : (β / (1 + β) + η) * wage A α (kUd A α δ r) < kUd A α δ r
  · obtain ⟨ks, hks, -, hfix, -⟩ := hcons h60
    exact ⟨ks, ⟨hks, hfix⟩, fun y hy => huniq y ks hy.1 hks hy.2 hfix⟩
  · exact ⟨kUd A α δ r, ⟨hU, hslack h60⟩, fun y hy => huniq y _ hy.1 hU hy.2 (hslack h60)⟩

/-- **Global monotone convergence with depreciation `δ ∈ (0, 1]`** (extending O&R's
`δ = 1` analysis, p. 471): every equilibrium path from `k₀ > 0` converges monotonically to
the unique steady state `k*`. When (60) holds, `k* < k̄^U` and the domestic rate stays
above `r` in the limit. -/
theorem equilibriumD_converges {A α β η r δ : ℝ} {k : ℕ → ℝ} (hα : 0 < α) (hα1 : α < 1)
    (hA : 0 < A) (hβ : 0 < β) (hη : 0 ≤ η) (hδ1 : δ ≤ 1) (hr : 0 < 1 + r) (hrd : 0 < r + δ)
    (h0 : 0 < k 0) (hpos : ∀ t, 0 < k (t + 1))
    (heq : ∀ t, EqRelD β η r A α δ (k t) (k (t + 1))) :
    ∃ ks, 0 < ks ∧ eqMapD A α β η r δ ks = ks ∧ Tendsto k atTop (𝓝 ks) ∧
      (k 0 ≤ ks → Monotone k) ∧ (ks ≤ k 0 → Antitone k) := by
  obtain ⟨hGpos, hmono, hratio⟩ := eqMapD_props hα hα1 hA hβ hη hδ1 hr hrd (δ := δ)
  obtain ⟨ks, ⟨hks, hfix⟩, -⟩ := (steadyD_existsUnique hα hα1 hA hβ hη hδ1 hr hrd (δ := δ)).1
  have hk : ∀ t, 0 < k t := fun t => by
    cases t with
    | zero => exact h0
    | succ t => exact hpos t
  obtain ⟨hlim, hm, ha⟩ := monotone_convergence hks hGpos hmono hratio hfix h0
    fun t => (eqRelD_iff hα hα1 hA hβ hη hδ1 hr hrd (hk t) (hpos t)).mp (heq t)
  exact ⟨ks, hks, hfix, hlim, hm, ha⟩

/-- **The equilibrium path with depreciation `δ` exists and is unique**. -/
theorem equilibriumD_existsUnique {β η r A α δ k : ℝ} (hα : 0 < α) (hα1 : α < 1) (hA : 0 < A)
    (hβ : 0 < β) (hη : 0 ≤ η) (hδ1 : δ ≤ 1) (hr : 0 < 1 + r) (hrd : 0 < r + δ) (hk : 0 < k) :
    ∃! x, 0 < x ∧ EqRelD β η r A α δ k x := by
  obtain ⟨hGpos, -, -⟩ := eqMapD_props hα hα1 hA hβ hη hδ1 hr hrd (δ := δ)
  refine ⟨eqMapD A α β η r δ k, ⟨hGpos k hk,
    (eqRelD_iff hα hα1 hA hβ hη hδ1 hr hrd hk (hGpos k hk)).mpr rfl⟩, ?_⟩
  rintro y ⟨hy, hEq⟩
  exact (eqRelD_iff hα hα1 hA hβ hη hδ1 hr hrd hk hy).mp hEq

/-- **One-period convergence with depreciation `δ`** (Case 3): `Φ_δ(k₀) = k̄^U` iff
`βw₀/(1+β) + ηw₀ ≥ k̄^U`. -/
theorem one_periodD_iff {A α β η r δ k₀ : ℝ} (hα : 0 < α) (hα1 : α < 1) (hA : 0 < A)
    (hβ : 0 < β) (hη : 0 ≤ η) (hδ1 : δ ≤ 1) (hr : 0 < 1 + r) (hrd : 0 < r + δ) (hk₀ : 0 < k₀) :
    eqMapD A α β η r δ k₀ = kUd A α δ r ↔ kUd A α δ r ≤ (β / (1 + β) + η) * wage A α k₀ := by
  have hw : 0 < wage A α k₀ := by
    unfold wage
    have : 0 < 1 - α := by linarith
    have := Real.rpow_pos_of_pos hk₀ α
    positivity
  rw [← kUd_le_psiD_iff hα hα1 hA hδ1 hβ hη hr hrd hw]
  unfold eqMapD
  exact min_eq_left_iff

end ObstfeldRogoff.GlobalGrowth.BorrowingConstrainedOLG
