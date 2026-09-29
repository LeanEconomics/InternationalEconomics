/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StickyPriceModels.Model
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# The small open economy with monopolistic nontradables: the model

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §10.2.1–10.2.3,
pp. 689–692. A small open economy has a constant endowment `ȳ_T` of a homogeneous traded good
priced in world markets (`P_T = 𝓔 P_T^*`, `P_T^*` constant) and a continuum of monopolistically
supplied nontraded goods. Period utility is (82):
`γ log C_T + (1−γ) log C_N + (χ/(1−ε)) (M/P)^{1−ε} − (κ/2) y_N²`, the consumer price index is
the Cobb–Douglas index (83), bonds are denominated in tradables with `β(1+r) = 1`, and seignorage
is rebated lump sum (85).

This file formalises the household problem as a genuine infinite-horizon problem.

* A generic infinite-horizon theory: the wealth recursion `A_{t+1} = (1+r)(A_t + h_t(x_t))`, the
  no-Ponzi condition, the transversality condition, sufficiency of a pointwise saddle condition
  (concave Lagrangian) together with the transversality condition, necessity of optimality under
  finite perturbations, and necessity of the transversality condition.
* The Cobb–Douglas price index (83) as a minimum cost, and the split (89).
* The household problem of (82), (84), (86): the book's budget (84) is equivalent to the wealth
  recursion; the first-order conditions (87)–(90) plus the no-Ponzi and transversality
  conditions are NECESSARY AND SUFFICIENT for optimality (`householdOptimal_iff`).
* Equilibrium: (91) holds exactly for ANY money path under the no-bubble condition; precisely,
  `C_T ≥ ȳ_T` always and `C_T = ȳ_T` iff the discounted real value of money has liminf zero;
  the money-demand equation (92); the unique steady-state output (93); the unique steady-state
  price level given the money supply; and existence (the steady state is an equilibrium).

Implicit hypotheses made explicit: `0 < β < 1`, `β(1+r) = 1`, `0 < γ < 1`, `χ > 0`, `ε > 0`,
`κ > 0`, `θ > 1`, positive prices, and a positive nominal interest rate (a positive user cost of
money, `1/P_{T,t} − 1/((1+r)P_{T,t+1}) > 0`). The book's real-balance term `(χ/(1−ε)) z^{1−ε}` is
read as `χ log z` at `ε = 1` (`moneyU`).
-/

namespace ObstfeldRogoff.StickyPriceModels.NontradablesModel

open Real Filter Topology Finset

/-! ## Tangent inequalities -/

/-- Tangent inequality behind the concavity of `(χ/(1−ε)) z^{1−ε}` and of revenue `y^{(θ−1)/θ}`
(O&R (82), (90), pp. 690–691): for `s ≤ 1`, `s ≠ 0`, `b^s/s ≤ a^s/s + a^{s−1}(b − a)`. -/
theorem rpow_div_le_tangent {s a b : ℝ} (hs0 : s ≠ 0) (hs1 : s ≤ 1) (ha : 0 < a) (hb : 0 < b) :
    b ^ s / s ≤ a ^ s / s + a ^ (s - 1) * (b - a) := by
  have hq : 0 < b / a := div_pos hb ha
  have key : b ^ s = a ^ s * (b / a) ^ s := by
    rw [div_rpow hb.le ha.le]; field_simp
  have hsplit : a ^ (s - 1) * (b - a) = a ^ s * (b / a - 1) := by
    rw [rpow_sub_one ha.ne']; field_simp
  have has : 0 < a ^ s := rpow_pos_of_pos ha s
  rcases lt_or_gt_of_ne hs0 with hneg | hpos
  · have h1 : 1 + s * (b / a - 1) ≤ (b / a) ^ s := by
      have e1 : (b / a) ^ s = exp (log (b / a) * s) := rpow_def_of_pos hq s
      have e2 := add_one_le_exp (log (b / a) * s)
      have e3 : log (b / a) ≤ b / a - 1 := log_le_sub_one_of_pos hq
      have e4 : s * (b / a - 1) ≤ log (b / a) * s := by nlinarith
      rw [e1]; linarith
    have h2 : s * (a ^ (s - 1) * (b - a)) ≤ b ^ s - a ^ s := by
      rw [hsplit, key]; nlinarith [mul_le_mul_of_nonneg_left h1 has.le]
    have h3 : (b ^ s - a ^ s) / s ≤ a ^ (s - 1) * (b - a) := by
      rw [div_le_iff_of_neg hneg]; linarith
    have h4 : (b ^ s - a ^ s) / s = b ^ s / s - a ^ s / s := sub_div _ _ _
    linarith
  · have h1 : (b / a) ^ s ≤ 1 + s * (b / a - 1) := by
      have := rpow_one_add_le_one_add_mul_self (s := b / a - 1) (by linarith) hpos.le hs1
      simpa using this
    have h2 : b ^ s - a ^ s ≤ s * (a ^ (s - 1) * (b - a)) := by
      rw [hsplit, key]; nlinarith [mul_le_mul_of_nonneg_left h1 has.le]
    have h3 : (b ^ s - a ^ s) / s ≤ a ^ (s - 1) * (b - a) := by
      rw [div_le_iff₀ hpos]; linarith
    have h4 : (b ^ s - a ^ s) / s = b ^ s / s - a ^ s / s := sub_div _ _ _
    linarith

/-- Tangent inequality for `y ↦ y^s`, `0 < s ≤ 1` (concavity of monopoly revenue, O&R (90),
p. 691): `b^s ≤ a^s + s a^{s−1}(b − a)`. -/
theorem rpow_le_tangent {s a b : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) (ha : 0 < a) (hb : 0 < b) :
    b ^ s ≤ a ^ s + s * (a ^ (s - 1) * (b - a)) := by
  have h := rpow_div_le_tangent hs0.ne' hs1 ha hb
  have h' := mul_le_mul_of_nonneg_left h hs0.le
  have e1 : s * (b ^ s / s) = b ^ s := by field_simp
  have e2 : s * (a ^ s / s + a ^ (s - 1) * (b - a)) = a ^ s + s * (a ^ (s - 1) * (b - a)) := by
    field_simp
  linarith

/-- Tangent inequality for `k log` (O&R (82), p. 690): with `k ≥ 0`, `a, c > 0`,
`k log a − (k/c) a ≤ k log c − (k/c) c`. -/
theorem log_tangent {k a c : ℝ} (hk : 0 ≤ k) (ha : 0 < a) (hc : 0 < c) :
    k * log a - k / c * a ≤ k * log c - k / c * c := by
  have h1 : log (a / c) ≤ a / c - 1 := log_le_sub_one_of_pos (div_pos ha hc)
  rw [log_div ha.ne' hc.ne'] at h1
  have h2 := mul_le_mul_of_nonneg_left h1 hk
  have e : k * (a / c - 1) = k / c * a - k / c * c := by field_simp
  nlinarith

/-! ## Real balances in utility -/

/-- The real-balance term of (82), p. 690: `(χ/(1−ε)) z^{1−ε}`, read as `χ log z` at `ε = 1`
(the book's log limit). -/
noncomputable def moneyU (χ ε z : ℝ) : ℝ :=
  if ε = 1 then χ * log z else χ / (1 - ε) * z ^ (1 - ε)

/-- The marginal utility of real balances (O&R (88), p. 691) is `χ z^{−ε}`. -/
theorem hasDerivAt_moneyU (χ ε : ℝ) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (moneyU χ ε) (χ * z ^ (-ε)) z := by
  by_cases hε : ε = 1
  · subst hε
    have h := (hasDerivAt_log hz.ne').const_mul χ
    have e : moneyU χ 1 = fun w => χ * log w := by
      funext w; simp [moneyU]
    rw [e, rpow_neg_one]; exact h
  · have h1 : (1 : ℝ) - ε ≠ 0 := sub_ne_zero.mpr (Ne.symm hε)
    have h := (hasDerivAt_rpow_const (p := 1 - ε) (Or.inl hz.ne')).const_mul (χ / (1 - ε))
    have e : moneyU χ ε = fun w => χ / (1 - ε) * w ^ (1 - ε) := by
      funext w; simp [moneyU, hε]
    rw [e]
    convert h using 1
    rw [show (1 : ℝ) - ε - 1 = -ε by ring]; field_simp

/-- Concavity of the real-balance term (O&R (82), `ε > 0`), as a tangent inequality:
`v(b) ≤ v(a) + χ a^{−ε} (b − a)`. -/
theorem moneyU_le_tangent {χ ε a b : ℝ} (hχ : 0 ≤ χ) (hε : 0 < ε) (ha : 0 < a) (hb : 0 < b) :
    moneyU χ ε b ≤ moneyU χ ε a + χ * a ^ (-ε) * (b - a) := by
  by_cases h1 : ε = 1
  · subst h1
    simp only [moneyU, ite_true, rpow_neg_one]
    have := log_tangent hχ hb ha
    have e : χ / a * b - χ / a * a = χ * a⁻¹ * (b - a) := by field_simp
    nlinarith [log_tangent hχ hb ha]
  · have hs0 : (1 : ℝ) - ε ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
    simp only [moneyU, h1, ite_false]
    have ht := rpow_div_le_tangent hs0 (by linarith) ha hb
    have ht' := mul_le_mul_of_nonneg_left ht hχ
    have e1 : χ / (1 - ε) * b ^ (1 - ε) = χ * (b ^ (1 - ε) / (1 - ε)) := by ring
    have e2 : χ / (1 - ε) * a ^ (1 - ε) = χ * (a ^ (1 - ε) / (1 - ε)) := by ring
    rw [e1, e2, show (1 : ℝ) - ε - 1 = -ε by ring] at *
    nlinarith

/-- The real-balance term is strictly increasing for `χ > 0` (O&R (82)). -/
theorem moneyU_strictMonoOn {χ ε : ℝ} (hχ : 0 < χ) :
    StrictMonoOn (moneyU χ ε) (Set.Ioi 0) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioi 0) ?_ ?_
  · intro z hz
    exact (hasDerivAt_moneyU χ ε hz).continuousAt.continuousWithinAt
  · intro z hz
    rw [interior_Ioi] at hz
    rw [(hasDerivAt_moneyU χ ε hz).deriv]
    exact mul_pos hχ (rpow_pos_of_pos hz _)


/-! ## Generic infinite-horizon theory -/

/-- The market discount factor `(1+r)^{−T}` in tradables (O&R §10.2.1, p. 690). -/
noncomputable def disc (r : ℝ) (T : ℕ) : ℝ := ((1 + r) ^ T)⁻¹

/-- Wealth recursion `A_{t+1} = (1+r)(A_t + h_t(x_t))`, where `h_t` is the net real resource
flow of the date-`t` choice (the budget (84) in wealth form, O&R p. 691). -/
noncomputable def wealth {X : Type*} (r A0 : ℝ) (h : ℕ → X → ℝ) (x : ℕ → X) : ℕ → ℝ
  | 0 => A0
  | t + 1 => (1 + r) * (wealth r A0 h x t + h t (x t))

/-- The discount factor is positive (O&R p. 690). -/
theorem disc_pos {r : ℝ} (hr : 0 < 1 + r) (T : ℕ) : 0 < disc r T :=
  inv_pos.mpr (pow_pos hr T)

/-- One-step discounting: `(1+r)^{−(t+1)}(1+r) = (1+r)^{−t}` (O&R p. 690). -/
theorem disc_succ_mul {r : ℝ} (hr : 0 < 1 + r) (t : ℕ) :
    disc r (t + 1) * (1 + r) = disc r t := by
  simp only [disc, pow_succ]
  field_simp

/-- Discounted wealth equals initial wealth plus the present value of net resources
(iterating (84), O&R fn 22 and p. 692). -/
theorem disc_mul_wealth {X : Type*} {r : ℝ} (hr : 0 < 1 + r) (A0 : ℝ) (h : ℕ → X → ℝ)
    (x : ℕ → X) (T : ℕ) :
    disc r T * wealth r A0 h x T = A0 + ∑ t ∈ range T, disc r t * h t (x t) := by
  induction T with
  | zero => simp [disc, wealth]
  | succ T ih =>
    rw [sum_range_succ, ← add_assoc, ← ih]
    have e : disc r (T + 1) * wealth r A0 h x (T + 1)
        = (disc r (T + 1) * (1 + r)) * (wealth r A0 h x T + h T (x T)) := by
      simp only [wealth]; ring
    rw [e, disc_succ_mul hr]; ring

/-- Two plans that agree outside a finite set `S` have discounted wealth differing, after `S`,
by the present value of the net-resource changes on `S` (O&R p. 691, perturbations). -/
theorem disc_mul_wealth_sub {X : Type*} {r : ℝ} (hr : 0 < 1 + r) (A0 : ℝ) (h : ℕ → X → ℝ)
    {x x' : ℕ → X} {S : Finset ℕ} (hS : ∀ t ∉ S, x' t = x t) {T : ℕ}
    (hT : ∀ t ∈ S, t < T) :
    disc r T * wealth r A0 h x' T
      = disc r T * wealth r A0 h x T + ∑ t ∈ S, disc r t * (h t (x' t) - h t (x t)) := by
  rw [disc_mul_wealth hr, disc_mul_wealth hr]
  have hsub : S ⊆ range T := fun t ht => mem_range.mpr (hT t ht)
  have e : ∑ t ∈ range T, disc r t * (h t (x' t) - h t (x t))
      = ∑ t ∈ S, disc r t * (h t (x' t) - h t (x t)) := by
    symm
    apply sum_subset hsub
    intro t _ htS
    rw [hS t htS]; ring
  have e2 : ∑ t ∈ range T, disc r t * h t (x' t)
      = ∑ t ∈ range T, disc r t * h t (x t)
        + ∑ t ∈ range T, disc r t * (h t (x' t) - h t (x t)) := by
    rw [← sum_add_distrib]; congr 1; funext t; ring
  rw [e2, e]; ring

/-- A series changed on a finite set stays summable, and its sum changes by the finite sum of
the changes (used for finite perturbations of lifetime utility (82)). -/
theorem tsum_eq_add_of_eq_off {f g : ℕ → ℝ} (hf : Summable f) (S : Finset ℕ)
    (hS : ∀ t ∉ S, g t = f t) :
    Summable g ∧ ∑' t, g t = ∑' t, f t + ∑ t ∈ S, (g t - f t) := by
  have hd : ∀ t ∉ S, g t - f t = 0 := fun t ht => by rw [hS t ht]; ring
  have hds : Summable fun t => g t - f t := summable_of_ne_finset_zero hd
  have hg : g = fun t => f t + (g t - f t) := by funext t; ring
  have hgs : Summable g := by rw [hg]; exact hf.add hds
  refine ⟨hgs, ?_⟩
  calc ∑' t, g t = ∑' t, (f t + (g t - f t)) := by rw [← hg]
    _ = ∑' t, f t + ∑' t, (g t - f t) := hf.tsum_add hds
    _ = ∑' t, f t + ∑ t ∈ S, (g t - f t) := by rw [tsum_eq_sum hd]

/-- The no-Ponzi condition `liminf (1+r)^{−T} A_T ≥ 0` (O&R (16), p. 666, not stated there;
supplied here), in the robust form `∀ δ > 0, eventually (1+r)^{−T} A_T ≥ −δ`. -/
def NoPonzi (r : ℝ) (A : ℕ → ℝ) : Prop :=
  ∀ δ > 0, ∀ᶠ T in atTop, -δ ≤ disc r T * A T

/-- The transversality condition in its necessary form `liminf (1+r)^{−T} A_T ≤ 0`
(O&R (16), p. 666): discounted wealth is frequently below every `δ > 0`. -/
def LiminfNonpos (r : ℝ) (A : ℕ → ℝ) : Prop :=
  ∀ δ > 0, ∃ᶠ T in atTop, disc r T * A T ≤ δ

/-- Optimality in the infinite-horizon problem (O&R (82) subject to (84)): the plan is admissible,
satisfies no-Ponzi, has summable discounted utility, and weakly beats every such plan. -/
def IsOptimal {X : Type*} (β r A0 : ℝ) (U h : ℕ → X → ℝ) (D : ℕ → Set X) (x : ℕ → X) :
    Prop :=
  (∀ t, x t ∈ D t) ∧ NoPonzi r (wealth r A0 h x) ∧ Summable (fun t => β ^ t * U t (x t)) ∧
    ∀ x' : ℕ → X, (∀ t, x' t ∈ D t) → NoPonzi r (wealth r A0 h x') →
      Summable (fun t => β ^ t * U t (x' t)) →
      ∑' t, β ^ t * U t (x' t) ≤ ∑' t, β ^ t * U t (x t)

/-- A convergent sequence that is frequently above `c` has limit at least `c`. -/
theorem le_of_tendsto_of_frequently {s : ℕ → ℝ} {L c : ℝ} (hs : Tendsto s atTop (𝓝 L))
    (hc : ∃ᶠ T in atTop, c ≤ s T) : c ≤ L := by
  by_contra hlt
  push Not at hlt
  have hev : ∀ᶠ T in atTop, s T < c := hs.eventually (gt_mem_nhds hlt)
  obtain ⟨T, h1, h2⟩ := (hc.and_eventually hev).exists
  linarith

/-- SUFFICIENCY (O&R §10.2.2, the concave-Lagrangian argument): if the plan maximises the
date-`t` Lagrangian `β^t U_t + μ₀(1+r)^{−t} h_t` pointwise over the admissible set, satisfies
no-Ponzi and the transversality condition (liminf form), and has summable utility, it is
optimal. -/
theorem isOptimal_of_saddle {X : Type*} {β r A0 μ0 : ℝ} {U h : ℕ → X → ℝ} {D : ℕ → Set X}
    {x : ℕ → X} (hr : 0 < 1 + r) (hμ : 0 ≤ μ0) (hx : ∀ t, x t ∈ D t)
    (hsum : Summable fun t => β ^ t * U t (x t)) (hnp : NoPonzi r (wealth r A0 h x))
    (htv : LiminfNonpos r (wealth r A0 h x))
    (hsad : ∀ t, ∀ y ∈ D t, β ^ t * U t y + μ0 * (disc r t * h t y)
      ≤ β ^ t * U t (x t) + μ0 * (disc r t * h t (x t))) :
    IsOptimal β r A0 U h D x := by
  refine ⟨hx, hnp, hsum, ?_⟩
  intro x' hx' hnp' hsum'
  set s : ℕ → ℝ := fun T => ∑ t ∈ range T, (β ^ t * U t (x t) - β ^ t * U t (x' t))
  have hlim : Tendsto s atTop
      (𝓝 (∑' t, β ^ t * U t (x t) - ∑' t, β ^ t * U t (x' t))) :=
    (hsum.hasSum.sub hsum'.hasSum).tendsto_sum_nat
  have hbound : ∀ T, μ0 * (disc r T * wealth r A0 h x' T - disc r T * wealth r A0 h x T)
      ≤ s T := by
    intro T
    rw [disc_mul_wealth hr, disc_mul_wealth hr]
    have e : μ0 * (A0 + ∑ t ∈ range T, disc r t * h t (x' t)
        - (A0 + ∑ t ∈ range T, disc r t * h t (x t)))
        = ∑ t ∈ range T, (μ0 * (disc r t * h t (x' t)) - μ0 * (disc r t * h t (x t))) := by
      rw [sum_sub_distrib, ← mul_sum, ← mul_sum]; ring
    rw [e]
    apply sum_le_sum
    intro t _
    have := hsad t (x' t) (hx' t)
    linarith
  have key : ∀ δ > 0, -(2 * μ0 * δ) ≤ ∑' t, β ^ t * U t (x t) - ∑' t, β ^ t * U t (x' t) := by
    intro δ hδ
    apply le_of_tendsto_of_frequently hlim
    refine ((htv δ hδ).and_eventually (hnp' δ hδ)).mono ?_
    intro T ⟨h1, h2⟩
    have := hbound T
    nlinarith
  have hfin : 0 ≤ ∑' t, β ^ t * U t (x t) - ∑' t, β ^ t * U t (x' t) := by
    apply le_of_forall_pos_le_add
    intro ε hε
    have := key (ε / (2 * μ0 + 1)) (by positivity)
    have h3 : 2 * μ0 * (ε / (2 * μ0 + 1)) ≤ ε := by
      rw [← mul_div_assoc, div_le_iff₀ (by positivity)]; nlinarith
    linarith
  linarith

/-- No-Ponzi is preserved by a finite perturbation that does not lower the present value of
net resources (O&R p. 691). -/
theorem noPonzi_of_perturb {X : Type*} {r A0 : ℝ} (hr : 0 < 1 + r) {h : ℕ → X → ℝ}
    {x x' : ℕ → X} {S : Finset ℕ} (hS : ∀ t ∉ S, x' t = x t)
    (hnp : NoPonzi r (wealth r A0 h x))
    (hpv : 0 ≤ ∑ t ∈ S, disc r t * (h t (x' t) - h t (x t))) :
    NoPonzi r (wealth r A0 h x') := by
  intro δ hδ
  filter_upwards [hnp δ hδ, eventually_gt_atTop (S.sup id)] with T h1 h2
  have hT : ∀ t ∈ S, t < T := fun t ht => lt_of_le_of_lt (le_sup (f := id) ht) h2
  rw [disc_mul_wealth_sub hr A0 h hS hT]
  linarith

/-- NECESSITY under finite perturbations (O&R §10.2.2): at an optimum, no admissible plan that
differs on a finite set `S` and satisfies no-Ponzi raises utility. -/
theorem perturb_utility_le {X : Type*} {β r A0 : ℝ} {U h : ℕ → X → ℝ} {D : ℕ → Set X}
    {x x' : ℕ → X} (hopt : IsOptimal β r A0 U h D x) (hx' : ∀ t, x' t ∈ D t) {S : Finset ℕ}
    (hS : ∀ t ∉ S, x' t = x t) (hnp' : NoPonzi r (wealth r A0 h x')) :
    ∑ t ∈ S, (β ^ t * U t (x' t) - β ^ t * U t (x t)) ≤ 0 := by
  obtain ⟨_, _, hsum, hbest⟩ := hopt
  have hS' : ∀ t ∉ S, β ^ t * U t (x' t) = β ^ t * U t (x t) := fun t ht => by rw [hS t ht]
  obtain ⟨hs', he⟩ := tsum_eq_add_of_eq_off hsum S hS'
  have := hbest x' hx' hnp' hs'
  linarith

/-- NECESSITY under finite perturbations, resource form: an admissible finite perturbation that
does not lower the present value of net resources cannot raise utility (O&R §10.2.2). -/
theorem perturb_utility_le_of_pv {X : Type*} {β r A0 : ℝ} (hr : 0 < 1 + r) {U h : ℕ → X → ℝ}
    {D : ℕ → Set X} {x x' : ℕ → X} (hopt : IsOptimal β r A0 U h D x)
    (hx' : ∀ t, x' t ∈ D t) {S : Finset ℕ} (hS : ∀ t ∉ S, x' t = x t)
    (hpv : 0 ≤ ∑ t ∈ S, disc r t * (h t (x' t) - h t (x t))) :
    ∑ t ∈ S, (β ^ t * U t (x' t) - β ^ t * U t (x t)) ≤ 0 :=
  perturb_utility_le hopt hx' hS (noPonzi_of_perturb hr hS hopt.2.1 hpv)

/-- NECESSITY OF THE TRANSVERSALITY CONDITION (O&R (16), p. 666, for the §10.2 problem): under
local non-satiation at date 0, an optimal plan has `liminf (1+r)^{−T} A_T ≤ 0`. -/
theorem liminfNonpos_of_isOptimal {X : Type*} {β r A0 : ℝ} (hr : 0 < 1 + r)
    {U h : ℕ → X → ℝ} {D : ℕ → Set X} {x : ℕ → X} (hopt : IsOptimal β r A0 U h D x)
    (hns : ∀ η > 0, ∃ y ∈ D 0, h 0 (x 0) - η ≤ h 0 y ∧ U 0 (x 0) < U 0 y) :
    LiminfNonpos r (wealth r A0 h x) := by
  intro δ hδ
  by_contra hcon
  rw [not_frequently] at hcon
  obtain ⟨y, hyD, hyh, hyU⟩ := hns δ hδ
  set x' : ℕ → X := Function.update x 0 y
  have hS : ∀ t ∉ ({0} : Finset ℕ), x' t = x t := by
    intro t ht
    simp only [Finset.mem_singleton] at ht
    simp [x', Function.update_of_ne ht]
  have hx' : ∀ t, x' t ∈ D t := by
    intro t
    by_cases ht : t = 0
    · subst ht; simp [x', hyD]
    · rw [hS t (by simpa using ht)]; exact hopt.1 t
  have hnp' : NoPonzi r (wealth r A0 h x') := by
    intro ε hε
    filter_upwards [hcon, eventually_gt_atTop 0] with T h1 h2
    have hT : ∀ t ∈ ({0} : Finset ℕ), t < T := by
      intro t ht; simp only [Finset.mem_singleton] at ht; omega
    rw [disc_mul_wealth_sub hr A0 h hS hT]
    simp only [Finset.sum_singleton, disc, pow_zero, inv_one, one_mul, x',
      Function.update_self]
    push Not at h1
    simp only [disc] at h1
    linarith
  have := perturb_utility_le hopt hx' hS hnp'
  simp [x'] at this
  linarith


/-! ## The Cobb–Douglas consumer price index (83) -/

/-- The consumption-based price index (83), p. 690:
`P = P_T^γ P_N^{1−γ} / (γ^γ (1−γ)^{1−γ})`. -/
noncomputable def cpi (γ PT PN : ℝ) : ℝ :=
  PT ^ γ * PN ^ (1 - γ) / (γ ^ γ * (1 - γ) ^ (1 - γ))

/-- Composite real consumption `C_T^γ C_N^{1−γ}` (O&R p. 690). -/
noncomputable def composite (γ CT CN : ℝ) : ℝ := CT ^ γ * CN ^ (1 - γ)

/-- The price index (83) is positive (O&R p. 690). -/
theorem cpi_pos {γ PT PN : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hT : 0 < PT) (hN : 0 < PN) :
    0 < cpi γ PT PN := by
  unfold cpi
  have : 0 < 1 - γ := by linarith
  positivity

/-- Key identity behind (83): `P · C_T^γ C_N^{1−γ} = (P_T C_T/γ)^γ (P_N C_N/(1−γ))^{1−γ}`. -/
theorem cpi_mul_composite {γ PT PN CT CN : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hT : 0 < PT)
    (hN : 0 < PN) (hCT : 0 < CT) (hCN : 0 < CN) :
    cpi γ PT PN * composite γ CT CN
      = (PT * CT / γ) ^ γ * (PN * CN / (1 - γ)) ^ (1 - γ) := by
  have h1 : 0 < 1 - γ := by linarith
  unfold cpi composite
  rw [div_rpow (by positivity) hγ0.le, div_rpow (by positivity) h1.le,
    mul_rpow hT.le hCT.le, mul_rpow hN.le hCN.le]
  have : 0 < γ ^ γ := rpow_pos_of_pos hγ0 γ
  have : 0 < (1 - γ) ^ (1 - γ) := rpow_pos_of_pos h1 _
  field_simp

/-- Weighted AM–GM in the form used for (83): `a^γ b^{1−γ} ≤ γ a + (1−γ) b`, strictly if
`a ≠ b`. -/
theorem wamgm_le {γ a b : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (ha : 0 < a) (hb : 0 < b) :
    a ^ γ * b ^ (1 - γ) ≤ γ * a + (1 - γ) * b ∧
      (a ≠ b → a ^ γ * b ^ (1 - γ) < γ * a + (1 - γ) * b) := by
  have e : a ^ γ * b ^ (1 - γ) = b * (1 + (a / b - 1)) ^ γ := by
    rw [show 1 + (a / b - 1) = a / b by ring, div_rpow ha.le hb.le, rpow_sub hb, rpow_one]
    have : 0 < b ^ γ := rpow_pos_of_pos hb γ
    field_simp
  have e2 : γ * a + (1 - γ) * b = b * (1 + γ * (a / b - 1)) := by field_simp; ring
  rw [e, e2]
  refine ⟨mul_le_mul_of_nonneg_left
    (rpow_one_add_le_one_add_mul_self (by have := div_pos ha hb; linarith) hγ0.le hγ1.le) hb.le,
    fun hne => mul_lt_mul_of_pos_left (rpow_one_add_lt_one_add_mul_self
      (by have := div_pos ha hb; linarith) ?_ hγ0 hγ1) hb⟩
  intro h0
  apply hne
  have : a / b = 1 := by linarith
  field_simp at this; linarith

/-- (83) is a lower bound on cost: `P · C_T^γ C_N^{1−γ} ≤ P_T C_T + P_N C_N`, with strict
inequality off the Cobb–Douglas split `P_T C_T/γ = P_N C_N/(1−γ)` (O&R p. 690). -/
theorem cpi_mul_composite_le {γ PT PN CT CN : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hT : 0 < PT)
    (hN : 0 < PN) (hCT : 0 < CT) (hCN : 0 < CN) :
    cpi γ PT PN * composite γ CT CN ≤ PT * CT + PN * CN ∧
      (PT * CT / γ ≠ PN * CN / (1 - γ) →
        cpi γ PT PN * composite γ CT CN < PT * CT + PN * CN) := by
  have h1 : 0 < 1 - γ := by linarith
  obtain ⟨hle, hlt⟩ := wamgm_le (a := PT * CT / γ) (b := PN * CN / (1 - γ)) hγ0 hγ1
    (by positivity) (by positivity)
  have e : γ * (PT * CT / γ) + (1 - γ) * (PN * CN / (1 - γ)) = PT * CT + PN * CN := by
    field_simp
  rw [cpi_mul_composite hγ0 hγ1 hT hN hCT hCN, ← e]
  exact ⟨hle, hlt⟩

/-- fn to (83), p. 690: `P` is the minimum money cost of one unit of `C_T^γ C_N^{1−γ}`,
attained EXACTLY at `C_T = γP/P_T`, `C_N = (1−γ)P/P_N` (existence and uniqueness). -/
theorem cpi_isMinCost {γ PT PN : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hT : 0 < PT) (hN : 0 < PN) :
    composite γ (γ * cpi γ PT PN / PT) ((1 - γ) * cpi γ PT PN / PN) = 1 ∧
      PT * (γ * cpi γ PT PN / PT) + PN * ((1 - γ) * cpi γ PT PN / PN) = cpi γ PT PN ∧
      ∀ CT CN, 0 < CT → 0 < CN → composite γ CT CN = 1 →
        cpi γ PT PN ≤ PT * CT + PN * CN ∧
        (PT * CT + PN * CN = cpi γ PT PN →
          CT = γ * cpi γ PT PN / PT ∧ CN = (1 - γ) * cpi γ PT PN / PN) := by
  have h1 : 0 < 1 - γ := by linarith
  have hP := cpi_pos hγ0 hγ1 hT hN
  set P := cpi γ PT PN with hPdef
  have hcomp : composite γ (γ * P / PT) ((1 - γ) * P / PN) = 1 := by
    have hm := cpi_mul_composite (CT := γ * P / PT) (CN := (1 - γ) * P / PN) hγ0 hγ1 hT hN
      (by positivity) (by positivity)
    rw [← hPdef] at hm
    have e1 : PT * (γ * P / PT) / γ = P := by field_simp
    have e2 : PN * ((1 - γ) * P / PN) / (1 - γ) = P := by field_simp
    rw [e1, e2, ← rpow_add hP, show γ + (1 - γ) = 1 by ring, rpow_one] at hm
    have := mul_left_cancel₀ hP.ne' (hm.trans (mul_one P).symm)
    exact this
  refine ⟨hcomp, by field_simp; ring, ?_⟩
  intro CT CN hCT hCN hc
  obtain ⟨hle, hlt⟩ := cpi_mul_composite_le hγ0 hγ1 hT hN hCT hCN
  rw [← hPdef, hc, mul_one] at hle hlt
  refine ⟨hle, fun heq => ?_⟩
  have hsplit : PT * CT / γ = PN * CN / (1 - γ) := by
    by_contra hne; have := hlt hne; linarith
  have hm := cpi_mul_composite hγ0 hγ1 hT hN hCT hCN
  rw [← hPdef, hc, mul_one, ← hsplit, ← rpow_add (by positivity),
    show γ + (1 - γ) = 1 by ring, rpow_one] at hm
  refine ⟨?_, ?_⟩
  · rw [hm]; field_simp
  · have : PN * CN / (1 - γ) = P := by rw [← hsplit, ← hm]
    field_simp at this ⊢; linarith

/-- (89), p. 691, as the Cobb–Douglas split: `P_T C_T/γ = P_N C_N/(1−γ)` iff
`C_N = ((1−γ)/γ)(P_T/P_N) C_T`. -/
theorem split_iff_89 {γ PT PN CT CN : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hN : 0 < PN) :
    PT * CT / γ = PN * CN / (1 - γ) ↔ CN = (1 - γ) / γ * (PT / PN) * CT := by
  have h1 : (1 : ℝ) - γ ≠ 0 := by linarith
  constructor <;> intro h
  · field_simp at h ⊢; linarith
  · rw [h]; field_simp


/-! ## The household problem (82), (84), (86) -/

/-- Parameters of the §10.2 economy (O&R (82)–(86), pp. 690–691). -/
structure Economy where
  β : ℝ
  r : ℝ
  γ : ℝ
  χ : ℝ
  ε : ℝ
  κ : ℝ
  θ : ℝ
  yT : ℝ

/-- The parameter restrictions of §10.2 made explicit (O&R pp. 690–691 and fn 2). -/
def Economy.Valid (E : Economy) : Prop :=
  0 < E.β ∧ E.β < 1 ∧ 0 < 1 + E.r ∧ 0 < E.γ ∧ E.γ < 1 ∧ 0 < E.χ ∧ 0 < E.ε ∧ 0 < E.κ ∧
    1 < E.θ ∧ 0 < E.yT

/-- Exogenous (to the household) paths: `P_{T,t}`, the nontradables index `P_{N,t}`, aggregate
nontradables consumption `C^A_{N,t}` and lump-sum taxes `τ_t` (O&R (84), (86), p. 691). -/
structure Prices where
  PT : ℕ → ℝ
  PN : ℕ → ℝ
  CA : ℕ → ℝ
  τ : ℕ → ℝ

/-- The real user cost of holding one unit of money from `t` to `t+1`, in tradables:
`1/P_{T,t} − 1/((1+r)P_{T,t+1}) = (i_{t+1}/(1+i_{t+1}))/P_{T,t}` (O&R (88), p. 691). -/
noncomputable def userCost (r : ℝ) (Q : Prices) (t : ℕ) : ℝ :=
  1 / Q.PT t - 1 / ((1 + r) * Q.PT (t + 1))

/-- Admissible price paths: positive prices and aggregate demand, and a positive nominal
interest rate (positive user cost of money) (implicit in O&R (92), p. 692). -/
def Prices.Valid (Q : Prices) (r : ℝ) : Prop :=
  ∀ t, 0 < Q.PT t ∧ 0 < Q.PN t ∧ 0 < Q.CA t ∧ 0 < userCost r Q t

/-- A date-`t` choice of the household: `C_T`, `C_N`, end-of-period money `M_t`, and output
`y_N` of its own nontraded good (O&R (82), (84), p. 690–691). -/
structure Choice where
  cT : ℝ
  cN : ℝ
  money : ℝ
  y : ℝ

/-- Admissible choices: all four components positive (O&R (82) needs `C_T, C_N, M > 0`). -/
def posChoice : Set Choice := {c | 0 < c.cT ∧ 0 < c.cN ∧ 0 < c.money ∧ 0 < c.y}

/-- The relative price `P_N/P_T` (O&R (89), p. 691). -/
noncomputable def relPrice (Q : Prices) (t : ℕ) : ℝ := Q.PN t / Q.PT t

/-- The consumer price index at date `t` (83). -/
noncomputable def cpiAt (E : Economy) (Q : Prices) (t : ℕ) : ℝ := cpi E.γ (Q.PT t) (Q.PN t)

/-- Period utility (82), p. 690. -/
noncomputable def periodU (E : Economy) (Q : Prices) (t : ℕ) (c : Choice) : ℝ :=
  E.γ * log c.cT + (1 - E.γ) * log c.cN + moneyU E.χ E.ε (c.money / cpiAt E Q t)
    - E.κ / 2 * c.y ^ 2

/-- The inverse of the demand curve (86): the money price at which `y` units are demanded,
`p_N = P_N (y/C^A_N)^{−1/θ}` (O&R p. 691). -/
noncomputable def invDemand (E : Economy) (Q : Prices) (t : ℕ) (y : ℝ) : ℝ :=
  Q.PN t * (y / Q.CA t) ^ (-1 / E.θ)

/-- Real revenue in tradables, `(P_N/P_T) y^{(θ−1)/θ} (C^A_N)^{1/θ}` (O&R fn 22, p. 691). -/
noncomputable def realRevenue (E : Economy) (Q : Prices) (t : ℕ) (y : ℝ) : ℝ :=
  relPrice Q t * (y ^ ((E.θ - 1) / E.θ) * Q.CA t ^ (1 / E.θ))

/-- Net real resource flow of a date-`t` choice (the budget (84) in tradables with the money
carried to `t+1` valued at its user cost) (O&R p. 691). -/
noncomputable def netRes (E : Economy) (Q : Prices) (t : ℕ) (c : Choice) : ℝ :=
  E.yT - Q.τ t + realRevenue E Q t c.y - relPrice Q t * c.cN - c.cT - c.money * userCost E.r Q t

/-- Initial real wealth `(1+r)B_0 + M_{−1}/P_{T,0}` (O&R (84), p. 691). -/
noncomputable def initWealth (E : Economy) (Q : Prices) (B0 Mm1 : ℝ) : ℝ :=
  (1 + E.r) * B0 + Mm1 / Q.PT 0

/-- Household optimality in the §10.2 problem: maximise (82) subject to (84), (86), no-Ponzi. -/
def HouseholdOptimal (E : Economy) (Q : Prices) (B0 Mm1 : ℝ) (c : ℕ → Choice) : Prop :=
  IsOptimal E.β E.r (initWealth E Q B0 Mm1) (periodU E Q) (netRes E Q) (fun _ => posChoice) c

/-- (86): at the inverse-demand price, CES demand `(p_N/P_N)^{−θ} C^A_N` is exactly `y`. -/
theorem cesDemand_invDemand (E : Economy) (Q : Prices) (t : ℕ) {y : ℝ} (hθ : 0 < E.θ)
    (hN : 0 < Q.PN t) (hA : 0 < Q.CA t) (hy : 0 < y) :
    cesDemand E.θ (invDemand E Q t y) (Q.PN t) (Q.CA t) = y := by
  unfold cesDemand invDemand
  rw [mul_div_cancel_left₀ _ hN.ne', ← rpow_mul (div_pos hy hA).le,
    show -1 / E.θ * -E.θ = 1 by field_simp, rpow_one]
  field_simp

/-- Revenue identity (O&R fn 22, p. 691): `p_N y / P_T = (P_N/P_T) y^{(θ−1)/θ} (C^A_N)^{1/θ}`. -/
theorem invDemand_mul (E : Economy) (Q : Prices) (t : ℕ) {y : ℝ} (hθ : 0 < E.θ)
    (hT : 0 < Q.PT t) (hA : 0 < Q.CA t) (hy : 0 < y) :
    invDemand E Q t y * y / Q.PT t = realRevenue E Q t y := by
  unfold invDemand realRevenue relPrice
  have hs : (E.θ - 1) / E.θ = -(1 / E.θ) + 1 := by field_simp; ring
  rw [hs, rpow_add hy, rpow_one, div_rpow hy.le hA.le, show (-1 / E.θ) = -(1 / E.θ) by ring,
    rpow_neg hA.le, rpow_neg hy.le]
  have : 0 < Q.CA t ^ (1 / E.θ) := rpow_pos_of_pos hA _
  have : 0 < y ^ (1 / E.θ) := rpow_pos_of_pos hy _
  field_simp

/-- Money carried into date `t`: `M_{−1}` at `t = 0`, `M_{t−1}` afterwards (O&R (84)). -/
def moneyPrev (Mm1 : ℝ) (c : ℕ → Choice) : ℕ → ℝ
  | 0 => Mm1
  | t + 1 => (c t).money

/-- The book's period budget constraint (84), p. 691, in money terms, with the monopolist's
price on its demand curve (86). -/
def Budget84 (E : Economy) (Q : Prices) (B : ℕ → ℝ) (Mm1 : ℝ) (c : ℕ → Choice) (t : ℕ) :
    Prop :=
  Q.PT t * B (t + 1) + (c t).money
    = Q.PT t * (1 + E.r) * B t + moneyPrev Mm1 c t + invDemand E Q t (c t).y * (c t).y
      + Q.PT t * E.yT - Q.PN t * (c t).cN - Q.PT t * (c t).cT - Q.PT t * Q.τ t

/-- (84) is EQUIVALENT to the wealth recursion with `A_t = (1+r)B_t + M_{t−1}/P_{T,t}`
(O&R p. 691): the Lean problem is exactly the book's. -/
theorem budget84_iff_wealth (E : Economy) (Q : Prices) (hE : E.Valid) (hQ : Q.Valid E.r)
    {B : ℕ → ℝ} {B0 Mm1 : ℝ} (hB0 : B 0 = B0) {c : ℕ → Choice} (hc : ∀ t, c t ∈ posChoice) :
    (∀ t, Budget84 E Q B Mm1 c t) ↔
      ∀ t, (1 + E.r) * B t + moneyPrev Mm1 c t / Q.PT t
        = wealth E.r (initWealth E Q B0 Mm1) (netRes E Q) c t := by
  obtain ⟨_, _, hr, _, _, _, _, _, hθ, _⟩ := hE
  have hθ0 : 0 < E.θ := by linarith
  set Ah : ℕ → ℝ := fun t => (1 + E.r) * B t + moneyPrev Mm1 c t / Q.PT t with hAh
  have step : ∀ t, Ah (t + 1) - (1 + E.r) * (Ah t + netRes E Q t (c t))
      = (1 + E.r) / Q.PT t * ((Q.PT t * B (t + 1) + (c t).money)
        - (Q.PT t * (1 + E.r) * B t + moneyPrev Mm1 c t + invDemand E Q t (c t).y * (c t).y
          + Q.PT t * E.yT - Q.PN t * (c t).cN - Q.PT t * (c t).cT - Q.PT t * Q.τ t)) := by
    intro t
    obtain ⟨hT, hN, hA, _⟩ := hQ t
    have hT1 := (hQ (t + 1)).1
    have hrev := invDemand_mul E Q t hθ0 hT hA (hc t).2.2.2
    have hrev' : invDemand E Q t (c t).y * (c t).y = Q.PT t * realRevenue E Q t (c t).y := by
      rw [← hrev]; field_simp
    simp only [hAh, netRes, userCost, relPrice, moneyPrev]
    rw [hrev']
    field_simp
    ring
  have hfac : ∀ t, (1 + E.r) / Q.PT t ≠ 0 := fun t => div_ne_zero hr.ne' (hQ t).1.ne'
  constructor
  · intro hb t
    induction t with
    | zero => simp [moneyPrev, wealth, initWealth, hB0]
    | succ t ih =>
      have h1 := step t
      rw [show Q.PT t * B (t + 1) + (c t).money - _ = 0 from sub_eq_zero.mpr (hb t),
        mul_zero, sub_eq_zero] at h1
      change Ah (t + 1) = _
      rw [h1, wealth]
      exact congrArg (fun z => (1 + E.r) * (z + netRes E Q t (c t))) ih
  · intro hw t
    have h1 := step t
    have e1 : Ah (t + 1) = wealth E.r (initWealth E Q B0 Mm1) (netRes E Q) c (t + 1) := hw (t + 1)
    have e0 : Ah t = wealth E.r (initWealth E Q B0 Mm1) (netRes E Q) c t := hw t
    rw [e1, e0, wealth, sub_self] at h1
    have := (mul_eq_zero.mp h1.symm).resolve_left (hfac t)
    exact sub_eq_zero.mp this


/-! ## First-order conditions (87)–(90) -/

/-- The consumption Euler equation for tradables, `γ/C_{T,t} = β(1+r) γ/C_{T,t+1}`; with
`β(1+r) = 1` this is (87), p. 691. -/
def EulerFOC (E : Economy) (c : ℕ → Choice) : Prop :=
  ∀ t, E.γ / (c t).cT = E.β * (1 + E.r) * (E.γ / (c (t + 1)).cT)

/-- The intratemporal condition (89), p. 691: `(1−γ)/C_N = (γ/C_T)(P_N/P_T)`. -/
def IntraFOC (E : Economy) (Q : Prices) (c : ℕ → Choice) : Prop :=
  ∀ t, (1 - E.γ) / (c t).cN = E.γ / (c t).cT * relPrice Q t

/-- The money condition behind (88), p. 691: the marginal utility of money equals the marginal
utility of tradables times the user cost,
`χ (M/P)^{−ε}/P = (γ/C_T)(1/P_{T,t} − 1/((1+r)P_{T,t+1}))`. -/
def MoneyFOC (E : Economy) (Q : Prices) (c : ℕ → Choice) : Prop :=
  ∀ t, E.χ * ((c t).money / cpiAt E Q t) ^ (-E.ε) / cpiAt E Q t
    = E.γ / (c t).cT * userCost E.r Q t

/-- The monopolist's output condition behind (90), p. 691: marginal disutility of effort equals
the marginal utility of marginal revenue, `κ y = (γ/C_T)(P_N/P_T)((θ−1)/θ) y^{−1/θ}(C^A_N)^{1/θ}`.
-/
def LabourFOC (E : Economy) (Q : Prices) (c : ℕ → Choice) : Prop :=
  ∀ t, E.κ * (c t).y = E.γ / (c t).cT * relPrice Q t *
    ((E.θ - 1) / E.θ * ((c t).y ^ ((E.θ - 1) / E.θ - 1) * Q.CA t ^ (1 / E.θ)))

/-- The pointwise Lagrangian inequality (O&R §10.2.2): at a choice satisfying (89), the money
condition and the output condition, with multiplier `λ = γ/C_T`, the date-`t` Lagrangian
`U_t + λ h_t` is maximised over all admissible choices (concavity). -/
theorem periodLagrangian_le (E : Economy) (Q : Prices) (hE : E.Valid) (hQ : Q.Valid E.r)
    (t : ℕ) {c y : Choice} (hc : c ∈ posChoice) (hy : y ∈ posChoice)
    (hN : (1 - E.γ) / c.cN = E.γ / c.cT * relPrice Q t)
    (hM : E.χ * (c.money / cpiAt E Q t) ^ (-E.ε) / cpiAt E Q t
      = E.γ / c.cT * userCost E.r Q t)
    (hL : E.κ * c.y = E.γ / c.cT * relPrice Q t *
      ((E.θ - 1) / E.θ * (c.y ^ ((E.θ - 1) / E.θ - 1) * Q.CA t ^ (1 / E.θ)))) :
    periodU E Q t y + E.γ / c.cT * netRes E Q t y
      ≤ periodU E Q t c + E.γ / c.cT * netRes E Q t c := by
  obtain ⟨_, _, _, hγ0, hγ1, hχ, hε, hκ, hθ, _⟩ := hE
  obtain ⟨hT, hPN, hA, _⟩ := hQ t
  obtain ⟨ha, hb, hn, hq⟩ := hc
  obtain ⟨ha', hb', hn', hq'⟩ := hy
  have hP : 0 < cpiAt E Q t := cpi_pos hγ0 hγ1 hT hPN
  have hρ : 0 < relPrice Q t := div_pos hPN hT
  set lam := E.γ / c.cT with hlam
  set ρ := relPrice Q t
  set P := cpiAt E Q t
  set K := Q.CA t ^ (1 / E.θ)
  set s := (E.θ - 1) / E.θ with hs
  have hK : 0 < K := rpow_pos_of_pos hA _
  have hs0 : 0 < s := div_pos (by linarith) (by linarith)
  have hs1 : s ≤ 1 := by rw [hs, div_le_one (by linarith)]; linarith
  have hlam0 : 0 < lam := div_pos hγ0 ha
  -- (A) tradables
  have hA' := log_tangent hγ0.le ha' ha
  -- (B) nontradables
  have hB' := log_tangent (k := 1 - E.γ) (by linarith) hb' hb
  have hBr : (1 - E.γ) / c.cN = lam * ρ := hN
  -- (C) money
  have hC' := moneyU_le_tangent hχ.le hε (div_pos hn hP) (div_pos hn' hP) (χ := E.χ)
  have hCr : E.χ * (c.money / P) ^ (-E.ε) * (y.money / P - c.money / P)
      = lam * userCost E.r Q t * (y.money - c.money) := by
    rw [← hM]; field_simp
  -- (D) output
  have hD1 := rpow_le_tangent hs0 hs1 hq hq'
  have hD2 : lam * ρ * K * y.y ^ s ≤ lam * ρ * K * c.y ^ s + E.κ * c.y * (y.y - c.y) := by
    have hL' : E.κ * c.y = lam * ρ * K * (s * c.y ^ (s - 1)) := by rw [hL]; ring
    have hpos : 0 ≤ lam * ρ * K := by positivity
    have := mul_le_mul_of_nonneg_left hD1 hpos
    rw [hL']; linarith
  have hD3 : -(E.κ / 2) * y.y ^ 2 ≤ -(E.κ / 2) * c.y ^ 2 - E.κ * c.y * (y.y - c.y) := by
    have hsq : -(E.κ / 2) * y.y ^ 2 - (-(E.κ / 2) * c.y ^ 2 - E.κ * c.y * (y.y - c.y))
        = -(E.κ / 2 * (y.y - c.y) ^ 2) := by ring
    have := mul_nonneg (by linarith : 0 ≤ E.κ / 2) (sq_nonneg (y.y - c.y))
    linarith
  simp only [periodU, netRes, realRevenue]
  rw [hBr] at hB'
  have e1 : (1 - E.γ) / c.cN * y.cN = lam * ρ * y.cN := by rw [hBr]
  have e2 : (1 - E.γ) / c.cN * c.cN = lam * ρ * c.cN := by rw [hBr]
  linarith [hA', hB', hC', hCr, hD2, hD3, e1, e2]

/-- Under the Euler equation, the discounted marginal utility of tradables is a market-discounted
constant: `β^t γ/C_{T,t} = (γ/C_{T,0}) (1+r)^{−t}` (O&R (87)). -/
theorem discounted_mu_of_euler {E : Economy} {c : ℕ → Choice} (hβ : 0 < E.β)
    (hr : 0 < 1 + E.r) (hc : ∀ t, c t ∈ posChoice) (heu : EulerFOC E c) (hγ : 0 < E.γ) (t : ℕ) :
    E.β ^ t * (E.γ / (c t).cT) = E.γ / (c 0).cT * disc E.r t := by
  induction t with
  | zero => simp [disc]
  | succ t ih =>
    have h := heu t
    have ha := (hc (t + 1)).1
    have hnext : E.γ / (c (t + 1)).cT = E.γ / (c t).cT / (E.β * (1 + E.r)) := by
      rw [h]; field_simp
    have e : E.γ / (c 0).cT * disc E.r (t + 1) = (E.γ / (c 0).cT * disc E.r t) / (1 + E.r) := by
      rw [← disc_succ_mul hr t]; field_simp
    rw [hnext, pow_succ, e, ← ih]
    field_simp

/-- SUFFICIENCY (O&R §10.2.2): an admissible plan with summable utility satisfying (87)–(90),
no-Ponzi and the transversality condition (liminf form) is a household optimum. -/
theorem householdOptimal_of_foc {E : Economy} {Q : Prices} (hE : E.Valid) (hQ : Q.Valid E.r)
    {B0 Mm1 : ℝ} {c : ℕ → Choice} (hc : ∀ t, c t ∈ posChoice)
    (hsum : Summable fun t => E.β ^ t * periodU E Q t (c t)) (heu : EulerFOC E c)
    (hN : IntraFOC E Q c) (hM : MoneyFOC E Q c) (hL : LabourFOC E Q c)
    (hnp : NoPonzi E.r (wealth E.r (initWealth E Q B0 Mm1) (netRes E Q) c))
    (htv : LiminfNonpos E.r (wealth E.r (initWealth E Q B0 Mm1) (netRes E Q) c)) :
    HouseholdOptimal E Q B0 Mm1 c := by
  have hE' := hE
  obtain ⟨hβ, _, hr, hγ0, _, _, _, _, _, _⟩ := hE'
  refine isOptimal_of_saddle (μ0 := E.γ / (c 0).cT) hr (div_pos hγ0 (hc 0).1).le hc hsum hnp
    htv ?_
  intro t y hy
  have hl := periodLagrangian_le E Q hE hQ t (hc t) hy (hN t) (hM t) (hL t)
  have hd := discounted_mu_of_euler hβ hr hc heu hγ0 t
  have hβt : 0 ≤ E.β ^ t := pow_nonneg hβ.le t
  have key := mul_le_mul_of_nonneg_left hl hβt
  have e : ∀ z : Choice, E.β ^ t * (periodU E Q t z + E.γ / (c t).cT * netRes E Q t z)
      = E.β ^ t * periodU E Q t z + E.γ / (c 0).cT * (disc E.r t * netRes E Q t z) := by
    intro z
    have h2 : E.γ / (c 0).cT * (disc E.r t * netRes E Q t z)
        = (E.β ^ t * (E.γ / (c t).cT)) * netRes E Q t z := by rw [hd]; ring
    rw [h2]; ring
  rw [e, e] at key
  exact key


/-- A single-date perturbation that keeps net resources weakly higher cannot raise date-`t`
utility at an optimum: `η ↦ U_t(g η)` has a local maximum at `0` (O&R §10.2.2). -/
theorem isLocalMax_of_perturb {E : Economy} {Q : Prices} {B0 Mm1 : ℝ} {c : ℕ → Choice}
    (hr : 0 < 1 + E.r) (hβ : 0 < E.β) (hopt : HouseholdOptimal E Q B0 Mm1 c) (t : ℕ)
    (g : ℝ → Choice) (hg0 : g 0 = c t) (hgpos : ∀ᶠ η in 𝓝 0, g η ∈ posChoice)
    (hgres : ∀ η, netRes E Q t (c t) ≤ netRes E Q t (g η)) :
    IsLocalMax (fun η => periodU E Q t (g η)) 0 := by
  filter_upwards [hgpos] with η hη
  set x' : ℕ → Choice := Function.update c t (g η)
  have hS : ∀ s ∉ ({t} : Finset ℕ), x' s = c s := by
    intro s hs
    simp only [Finset.mem_singleton] at hs
    simp [x', Function.update_of_ne hs]
  have hx' : ∀ s, x' s ∈ posChoice := by
    intro s
    by_cases hs : s = t
    · subst hs; simpa [x'] using hη
    · rw [hS s (by simpa using hs)]; exact hopt.1 s
  have hpv : 0 ≤ ∑ s ∈ ({t} : Finset ℕ),
      disc E.r s * (netRes E Q s (x' s) - netRes E Q s (c s)) := by
    simp only [Finset.sum_singleton, x', Function.update_self]
    exact mul_nonneg (disc_pos hr t).le (by linarith [hgres η])
  have h := perturb_utility_le_of_pv hr hopt hx' hS hpv
  simp only [Finset.sum_singleton, x', Function.update_self] at h
  have hβt : 0 < E.β ^ t := pow_pos hβ t
  simp only [hg0]
  nlinarith

/-- NECESSITY of (89), p. 691, at a household optimum. -/
theorem intraFOC_of_optimal {E : Economy} {Q : Prices} (hE : E.Valid)
    {B0 Mm1 : ℝ} {c : ℕ → Choice} (hopt : HouseholdOptimal E Q B0 Mm1 c) : IntraFOC E Q c := by
  obtain ⟨hβ, _, hr, hγ0, hγ1, _, _, _, _, _⟩ := hE
  intro t
  obtain ⟨ha, hb, hn, hq⟩ := hopt.1 t
  set ρ := relPrice Q t
  set g : ℝ → Choice := fun η =>
    ⟨(c t).cT - ρ * η, (c t).cN + η, (c t).money, (c t).y⟩ with hg
  have hg0 : g 0 = c t := by simp [g]
  have hgpos : ∀ᶠ η in 𝓝 0, g η ∈ posChoice := by
    have h1 : ∀ᶠ η in 𝓝 (0 : ℝ), 0 < (c t).cT - ρ * η :=
      (continuous_const.sub (continuous_const.mul continuous_id)).continuousAt.eventually
        (lt_mem_nhds (by simpa using ha))
    have h2 : ∀ᶠ η in 𝓝 (0 : ℝ), 0 < (c t).cN + η :=
      (continuous_const.add continuous_id).continuousAt.eventually
        (lt_mem_nhds (by simpa using hb))
    filter_upwards [h1, h2] with η e1 e2
    exact ⟨e1, e2, hn, hq⟩
  have hgres : ∀ η, netRes E Q t (c t) ≤ netRes E Q t (g η) := by
    intro η; simp only [netRes, g]; linarith
  have hmax := isLocalMax_of_perturb hr hβ hopt t g hg0 hgpos hgres
  have hfun : (fun η => periodU E Q t (g η)) = fun η =>
      E.γ * log ((c t).cT - ρ * η) + (1 - E.γ) * log ((c t).cN + η)
        + (moneyU E.χ E.ε ((c t).money / cpiAt E Q t) - E.κ / 2 * (c t).y ^ 2) := by
    funext η; simp only [periodU, g]; ring
  have hd1 : HasDerivAt (fun η => (c t).cT - ρ * η) (-ρ) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul ρ).const_sub (c t).cT
  have hd2 : HasDerivAt (fun η => (c t).cN + η) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_add (c t).cN
  have hd : HasDerivAt (fun η => periodU E Q t (g η))
      (E.γ * (-ρ / (c t).cT) + (1 - E.γ) * (1 / (c t).cN)) 0 := by
    rw [hfun]
    have e1 := (hd1.log (by simpa using ha.ne')).const_mul E.γ
    have e2 := (hd2.log (by simpa using hb.ne')).const_mul (1 - E.γ)
    simp only [mul_zero, sub_zero, add_zero] at e1 e2
    exact (e1.add e2).add_const _
  have h0 := hmax.hasDerivAt_eq_zero hd
  field_simp at h0 ⊢
  linarith

/-- NECESSITY of the money condition behind (88), p. 691, at a household optimum. -/
theorem moneyFOC_of_optimal {E : Economy} {Q : Prices} (hE : E.Valid) (hQ : Q.Valid E.r)
    {B0 Mm1 : ℝ} {c : ℕ → Choice} (hopt : HouseholdOptimal E Q B0 Mm1 c) : MoneyFOC E Q c := by
  obtain ⟨hβ, _, hr, hγ0, hγ1, _, _, _, _, _⟩ := hE
  intro t
  obtain ⟨ha, hb, hn, hq⟩ := hopt.1 t
  obtain ⟨hT, hPN, _, _⟩ := hQ t
  have hP : 0 < cpiAt E Q t := cpi_pos hγ0 hγ1 hT hPN
  set ι := userCost E.r Q t
  set P := cpiAt E Q t
  set g : ℝ → Choice := fun η =>
    ⟨(c t).cT - ι * η, (c t).cN, (c t).money + η, (c t).y⟩ with hg
  have hg0 : g 0 = c t := by simp [g]
  have hgpos : ∀ᶠ η in 𝓝 0, g η ∈ posChoice := by
    have h1 : ∀ᶠ η in 𝓝 (0 : ℝ), 0 < (c t).cT - ι * η :=
      (continuous_const.sub (continuous_const.mul continuous_id)).continuousAt.eventually
        (lt_mem_nhds (by simpa using ha))
    have h2 : ∀ᶠ η in 𝓝 (0 : ℝ), 0 < (c t).money + η :=
      (continuous_const.add continuous_id).continuousAt.eventually
        (lt_mem_nhds (by simpa using hn))
    filter_upwards [h1, h2] with η e1 e2
    exact ⟨e1, hb, e2, hq⟩
  have hgres : ∀ η, netRes E Q t (c t) ≤ netRes E Q t (g η) := by
    intro η; simp only [netRes, g]; linarith
  have hmax := isLocalMax_of_perturb hr hβ hopt t g hg0 hgpos hgres
  have hfun : (fun η => periodU E Q t (g η)) = fun η =>
      E.γ * log ((c t).cT - ι * η) + moneyU E.χ E.ε (((c t).money + η) / P)
        + ((1 - E.γ) * log (c t).cN - E.κ / 2 * (c t).y ^ 2) := by
    funext η; simp only [periodU, g]; ring
  have hd1 : HasDerivAt (fun η => (c t).cT - ι * η) (-ι) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul ι).const_sub (c t).cT
  have hd2 : HasDerivAt (fun η => ((c t).money + η) / P) (1 / P) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_add (c t).money).div_const P
  have hm : HasDerivAt (fun η => moneyU E.χ E.ε (((c t).money + η) / P))
      (E.χ * ((c t).money / P) ^ (-E.ε) * (1 / P)) 0 := by
    have := (hasDerivAt_moneyU E.χ E.ε (z := ((c t).money + 0) / P)
      (by simpa using div_pos hn hP)).comp (0 : ℝ) hd2
    convert this using 1 <;> first | rfl | simp
  have hd : HasDerivAt (fun η => periodU E Q t (g η))
      (E.γ * (-ι / (c t).cT) + E.χ * ((c t).money / P) ^ (-E.ε) * (1 / P)) 0 := by
    rw [hfun]
    have e1 := (hd1.log (by simpa using ha.ne')).const_mul E.γ
    simp only [mul_zero, sub_zero] at e1
    exact (e1.add hm).add_const _
  have h0 := hmax.hasDerivAt_eq_zero hd
  have : E.χ * ((c t).money / P) ^ (-E.ε) / P = E.γ / (c t).cT * ι := by
    field_simp at h0 ⊢; linarith
  exact this

/-- NECESSITY of the output condition behind (90), p. 691, at a household optimum. -/
theorem labourFOC_of_optimal {E : Economy} {Q : Prices} (hE : E.Valid)
    {B0 Mm1 : ℝ} {c : ℕ → Choice} (hopt : HouseholdOptimal E Q B0 Mm1 c) : LabourFOC E Q c := by
  obtain ⟨hβ, _, hr, hγ0, hγ1, _, _, _, hθ, _⟩ := hE
  intro t
  obtain ⟨ha, hb, hn, hq⟩ := hopt.1 t
  set R := realRevenue E Q t
  set s := (E.θ - 1) / E.θ
  set K := Q.CA t ^ (1 / E.θ)
  set ρ := relPrice Q t
  have hRd : HasDerivAt R (ρ * (s * (c t).y ^ (s - 1) * K)) (c t).y := by
    have := ((hasDerivAt_rpow_const (p := s) (Or.inl hq.ne')).mul_const K).const_mul ρ
    exact this
  set g : ℝ → Choice := fun η =>
    ⟨(c t).cT + (R ((c t).y + η) - R (c t).y), (c t).cN, (c t).money, (c t).y + η⟩ with hg
  have hg0 : g 0 = c t := by simp [g]
  have hRc : HasDerivAt (fun η => R ((c t).y + η)) (ρ * (s * (c t).y ^ (s - 1) * K)) 0 := by
    have hR0 : HasDerivAt R (ρ * (s * (c t).y ^ (s - 1) * K)) ((c t).y + 0) := by
      simpa using hRd
    have := hR0.comp (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).const_add (c t).y)
    convert this using 1 <;> first | rfl | simp
  have hd1 : HasDerivAt (fun η => (c t).cT + (R ((c t).y + η) - R (c t).y))
      (ρ * (s * (c t).y ^ (s - 1) * K)) 0 := by
    simpa using (hRc.sub_const (R (c t).y)).const_add (c t).cT
  have hgpos : ∀ᶠ η in 𝓝 0, g η ∈ posChoice := by
    have h1 : ∀ᶠ η in 𝓝 (0 : ℝ), 0 < (c t).cT + (R ((c t).y + η) - R (c t).y) :=
      hd1.continuousAt.eventually (lt_mem_nhds (by simpa using ha))
    have h2 : ∀ᶠ η in 𝓝 (0 : ℝ), 0 < (c t).y + η :=
      (continuous_const.add continuous_id).continuousAt.eventually
        (lt_mem_nhds (by simpa using hq))
    filter_upwards [h1, h2] with η e1 e2
    exact ⟨e1, hb, hn, e2⟩
  have hgres : ∀ η, netRes E Q t (c t) ≤ netRes E Q t (g η) := by
    intro η; simp only [netRes, g, R]; linarith
  have hmax := isLocalMax_of_perturb hr hβ hopt t g hg0 hgpos hgres
  have hfun : (fun η => periodU E Q t (g η)) = fun η =>
      E.γ * log ((c t).cT + (R ((c t).y + η) - R (c t).y)) - E.κ / 2 * ((c t).y + η) ^ 2
        + ((1 - E.γ) * log (c t).cN + moneyU E.χ E.ε ((c t).money / cpiAt E Q t)) := by
    funext η; simp only [periodU, g]; ring
  have hsq : HasDerivAt (fun η => ((c t).y + η) ^ 2) (2 * (c t).y) 0 := by
    have := (hasDerivAt_pow 2 ((c t).y + 0)).comp (0 : ℝ)
      ((hasDerivAt_id (0 : ℝ)).const_add (c t).y)
    convert this using 1 <;> first | rfl | simp
  have hd : HasDerivAt (fun η => periodU E Q t (g η))
      (E.γ * (ρ * (s * (c t).y ^ (s - 1) * K) / (c t).cT) - E.κ / 2 * (2 * (c t).y)) 0 := by
    rw [hfun]
    have e1 := (hd1.log (by simpa using ha.ne')).const_mul E.γ
    simp only [sub_self, add_zero] at e1
    exact ((e1.sub (hsq.const_mul (E.κ / 2)))).add_const _
  have h0 := hmax.hasDerivAt_eq_zero hd
  have : E.κ * (c t).y = E.γ / (c t).cT * ρ * (s * ((c t).y ^ (s - 1) * K)) := by
    field_simp at h0 ⊢; linarith
  exact this

/-- NECESSITY of the Euler equation (87), p. 691, at a household optimum (two-date
perturbation shifting tradables consumption from `t+1` to `t`). -/
theorem eulerFOC_of_optimal {E : Economy} {Q : Prices} (hE : E.Valid)
    {B0 Mm1 : ℝ} {c : ℕ → Choice} (hopt : HouseholdOptimal E Q B0 Mm1 c) : EulerFOC E c := by
  obtain ⟨hβ, _, hr, hγ0, _, _, _, _, _, _⟩ := hE
  intro t
  have ha := (hopt.1 t).1
  have ha' := (hopt.1 (t + 1)).1
  have htt : t + 1 ≠ t := Nat.succ_ne_self t
  set x' : ℝ → ℕ → Choice := fun η s =>
    if s = t then ⟨(c t).cT + η, (c t).cN, (c t).money, (c t).y⟩
    else if s = t + 1 then
      ⟨(c (t + 1)).cT - (1 + E.r) * η, (c (t + 1)).cN, (c (t + 1)).money, (c (t + 1)).y⟩
    else c s with hx'
  set f : ℝ → ℝ := fun η => E.β ^ t * (E.γ * log ((c t).cT + η))
    + E.β ^ (t + 1) * (E.γ * log ((c (t + 1)).cT - (1 + E.r) * η)) with hf
  have hloc : IsLocalMax f 0 := by
    have h1 : ∀ᶠ η in 𝓝 (0 : ℝ), 0 < (c t).cT + η :=
      (continuous_const.add continuous_id).continuousAt.eventually
        (lt_mem_nhds (by simpa using ha))
    have h2 : ∀ᶠ η in 𝓝 (0 : ℝ), 0 < (c (t + 1)).cT - (1 + E.r) * η :=
      (continuous_const.sub (continuous_const.mul continuous_id)).continuousAt.eventually
        (lt_mem_nhds (by simpa using ha'))
    filter_upwards [h1, h2] with η e1 e2
    have hS : ∀ s ∉ ({t, t + 1} : Finset ℕ), x' η s = c s := by
      intro s hs
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hs
      simp [x', hs.1, hs.2]
    have hadm : ∀ s, x' η s ∈ posChoice := by
      intro s
      by_cases hs1 : s = t
      · subst hs1; simp only [x', ↓reduceIte]
        exact ⟨e1, (hopt.1 s).2.1, (hopt.1 s).2.2.1, (hopt.1 s).2.2.2⟩
      by_cases hs2 : s = t + 1
      · subst hs2; simp only [x', htt, ↓reduceIte]
        exact ⟨e2, (hopt.1 (t + 1)).2.1, (hopt.1 (t + 1)).2.2.1, (hopt.1 (t + 1)).2.2.2⟩
      rw [hS s (by simp [hs1, hs2])]; exact hopt.1 s
    have hpv : 0 ≤ ∑ s ∈ ({t, t + 1} : Finset ℕ),
        disc E.r s * (netRes E Q s (x' η s) - netRes E Q s (c s)) := by
      rw [Finset.sum_pair htt.symm]
      simp only [x', htt, ↓reduceIte, netRes]
      have := disc_succ_mul hr t
      nlinarith
    have h := perturb_utility_le_of_pv hr hopt hadm hS hpv
    rw [Finset.sum_pair htt.symm] at h
    simp only [x', htt, ↓reduceIte, periodU] at h
    simp only [hf, add_zero, mul_zero, sub_zero]
    linarith
  have hd1 : HasDerivAt (fun η => (c t).cT + η) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_add (c t).cT
  have hd2 : HasDerivAt (fun η => (c (t + 1)).cT - (1 + E.r) * η) (-(1 + E.r)) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul (1 + E.r)).const_sub (c (t + 1)).cT
  have hd : HasDerivAt f (E.β ^ t * (E.γ * (1 / (c t).cT))
      + E.β ^ (t + 1) * (E.γ * (-(1 + E.r) / (c (t + 1)).cT))) 0 := by
    have e1 := ((hd1.log (by simpa using ha.ne')).const_mul E.γ).const_mul (E.β ^ t)
    have e2 := ((hd2.log (by simpa using ha'.ne')).const_mul E.γ).const_mul (E.β ^ (t + 1))
    simp only [add_zero, mul_zero, sub_zero] at e1 e2
    exact e1.add e2
  have h0 := hloc.hasDerivAt_eq_zero hd
  have hβt : 0 < E.β ^ t := pow_pos hβ t
  rw [pow_succ] at h0
  have : E.γ / (c t).cT = E.β * (1 + E.r) * (E.γ / (c (t + 1)).cT) := by
    have h3 : E.β ^ t * (E.γ / (c t).cT - E.β * (1 + E.r) * (E.γ / (c (t + 1)).cT)) = 0 := by
      rw [← h0]; field_simp; ring
    have := (mul_eq_zero.mp h3).resolve_left hβt.ne'
    linarith
  exact this

/-- NECESSITY of the transversality condition (liminf form) at a household optimum (O&R (16)
for the §10.2 problem): raising date-0 tradables consumption is always feasible. -/
theorem liminfNonpos_of_householdOptimal {E : Economy} {Q : Prices} (hE : E.Valid)
    {B0 Mm1 : ℝ} {c : ℕ → Choice} (hopt : HouseholdOptimal E Q B0 Mm1 c) :
    LiminfNonpos E.r (wealth E.r (initWealth E Q B0 Mm1) (netRes E Q) c) := by
  obtain ⟨_, _, hr, hγ0, _, _, _, _, _, _⟩ := hE
  refine liminfNonpos_of_isOptimal hr hopt ?_
  intro η hη
  obtain ⟨ha, hb, hn, hq⟩ := hopt.1 0
  refine ⟨⟨(c 0).cT + η, (c 0).cN, (c 0).money, (c 0).y⟩, ⟨by linarith, hb, hn, hq⟩, ?_, ?_⟩
  · simp only [netRes]; linarith
  · simp only [periodU]
    have := log_lt_log ha (by linarith : (c 0).cT < (c 0).cT + η)
    nlinarith

/-- MAIN THEOREM (O&R §10.2.2, (87)–(90)): an admissible plan is a household optimum IF AND ONLY
IF its utility is summable, it satisfies the first-order conditions (87)–(90), the no-Ponzi
condition and the transversality condition `liminf (1+r)^{−T} A_T ≤ 0`. -/
theorem householdOptimal_iff {E : Economy} {Q : Prices} (hE : E.Valid) (hQ : Q.Valid E.r)
    {B0 Mm1 : ℝ} {c : ℕ → Choice} :
    HouseholdOptimal E Q B0 Mm1 c ↔
      (∀ t, c t ∈ posChoice) ∧ Summable (fun t => E.β ^ t * periodU E Q t (c t)) ∧
      EulerFOC E c ∧ IntraFOC E Q c ∧ MoneyFOC E Q c ∧ LabourFOC E Q c ∧
      NoPonzi E.r (wealth E.r (initWealth E Q B0 Mm1) (netRes E Q) c) ∧
      LiminfNonpos E.r (wealth E.r (initWealth E Q B0 Mm1) (netRes E Q) c) := by
  constructor
  · intro h
    exact ⟨h.1, h.2.2.1, eulerFOC_of_optimal hE h, intraFOC_of_optimal hE h,
      moneyFOC_of_optimal hE hQ h, labourFOC_of_optimal hE h, h.2.1,
      liminfNonpos_of_householdOptimal hE h⟩
  · rintro ⟨hc, hs, he, hn, hm, hl, hnp, htv⟩
    exact householdOptimal_of_foc hE hQ hc hs he hn hm hl hnp htv


/-! ## The book's forms of (88), (90), (92) -/

/-- (88), p. 691, from the money condition and the Euler equation:
`γ/C_{T,t} = χ (P_{T,t}/P_t)(M_t/P_t)^{−ε} + β (P_{T,t}/P_{T,t+1}) γ/C_{T,t+1}`. -/
theorem money_88 {E : Economy} {Q : Prices} (hE : E.Valid) (hQ : Q.Valid E.r)
    {c : ℕ → Choice} (hc : ∀ t, c t ∈ posChoice) (heu : EulerFOC E c) (hM : MoneyFOC E Q c)
    (t : ℕ) :
    E.γ / (c t).cT = E.χ * (Q.PT t / cpiAt E Q t) * ((c t).money / cpiAt E Q t) ^ (-E.ε)
      + E.β * (Q.PT t / Q.PT (t + 1)) * (E.γ / (c (t + 1)).cT) := by
  obtain ⟨_, _, hr, hγ0, hγ1, _, _, _, _, _⟩ := hE
  obtain ⟨hT, hN, _, _⟩ := hQ t
  have hT1 := (hQ (t + 1)).1
  have hP : 0 < cpiAt E Q t := cpi_pos hγ0 hγ1 hT hN
  have h1 := hM t
  have h2 := heu t
  have ha := (hc t).1
  have ha1 := (hc (t + 1)).1
  unfold userCost at h1
  have e : E.χ * (Q.PT t / cpiAt E Q t) * ((c t).money / cpiAt E Q t) ^ (-E.ε)
      = Q.PT t * (E.χ * ((c t).money / cpiAt E Q t) ^ (-E.ε) / cpiAt E Q t) := by
    field_simp
  rw [e, h1]
  have e2 : E.β * (Q.PT t / Q.PT (t + 1)) * (E.γ / (c (t + 1)).cT)
      = E.γ / (c t).cT * (Q.PT t / ((1 + E.r) * Q.PT (t + 1))) := by
    rw [h2]; field_simp
  rw [e2]; field_simp; ring

/-- (90), p. 691, from the intratemporal and output conditions:
`y_N^{(θ+1)/θ} = ((θ−1)(1−γ)/(κθ)) (C^A_N)^{1/θ} / C_N`. -/
theorem labour_90 {E : Economy} {Q : Prices} (hE : E.Valid)
    {c : ℕ → Choice} (hc : ∀ t, c t ∈ posChoice) (hN : IntraFOC E Q c) (hL : LabourFOC E Q c)
    (t : ℕ) :
    (c t).y ^ ((E.θ + 1) / E.θ)
      = (E.θ - 1) * (1 - E.γ) / (E.κ * E.θ) * Q.CA t ^ (1 / E.θ) / (c t).cN := by
  obtain ⟨_, _, _, _, _, _, _, hκ, hθ, _⟩ := hE
  obtain ⟨_, hb, _, hq⟩ := hc t
  have hθ0 : 0 < E.θ := by linarith
  have h1 := hL t
  rw [← mul_assoc, ← hN t] at h1
  have e1 : (c t).y ^ ((E.θ + 1) / E.θ) = (c t).y * (c t).y ^ (1 / E.θ) := by
    rw [show (E.θ + 1) / E.θ = 1 + 1 / E.θ by field_simp, rpow_add hq, rpow_one]
  have e2 : (c t).y ^ ((E.θ - 1) / E.θ - 1) = ((c t).y ^ (1 / E.θ))⁻¹ := by
    rw [show (E.θ - 1) / E.θ - 1 = -(1 / E.θ) by field_simp; ring, rpow_neg hq.le]
  rw [e2] at h1
  have hy1 : 0 < (c t).y ^ (1 / E.θ) := rpow_pos_of_pos hq _
  rw [e1]
  field_simp at h1 ⊢
  linarith

/-- (92), p. 692: with `β(1+r) = 1`, money demand is
`M/P = [(χ/γ) (C_T P_T/P) / (1 − β P_{T,t}/P_{T,t+1})]^{1/ε}`. -/
theorem money_92 {E : Economy} {Q : Prices} (hE : E.Valid) (hβr : E.β * (1 + E.r) = 1)
    (hQ : Q.Valid E.r) {c : ℕ → Choice} (hc : ∀ t, c t ∈ posChoice) (hM : MoneyFOC E Q c)
    (t : ℕ) :
    (c t).money / cpiAt E Q t
      = (E.χ / E.γ * ((c t).cT * Q.PT t / cpiAt E Q t)
          / (1 - E.β * (Q.PT t / Q.PT (t + 1)))) ^ (1 / E.ε) := by
  obtain ⟨hβ, _, hr, hγ0, hγ1, hχ, hε, _, _, _⟩ := hE
  obtain ⟨hT, hN, _, hu⟩ := hQ t
  have hT1 := (hQ (t + 1)).1
  have hP : 0 < cpiAt E Q t := cpi_pos hγ0 hγ1 hT hN
  obtain ⟨ha, _, hn, _⟩ := hc t
  have hm : 0 < (c t).money / cpiAt E Q t := div_pos hn hP
  have hucost : userCost E.r Q t = (1 - E.β * (Q.PT t / Q.PT (t + 1))) / Q.PT t := by
    unfold userCost
    have : 1 / ((1 + E.r) * Q.PT (t + 1)) = E.β / Q.PT (t + 1) := by
      field_simp; linarith
    rw [this]; field_simp
  have hw : 0 < 1 - E.β * (Q.PT t / Q.PT (t + 1)) := by
    have := hu; rw [hucost] at this
    exact (div_pos_iff_of_pos_right hT).mp this
  have h1 := hM t
  rw [hucost] at h1
  set m := (c t).money / cpiAt E Q t
  set w := 1 - E.β * (Q.PT t / Q.PT (t + 1))
  have hA : m ^ (-E.ε) = E.γ / E.χ * (cpiAt E Q t / ((c t).cT * Q.PT t)) * w := by
    field_simp at h1 ⊢; linarith
  have key : m = (m ^ (-E.ε)) ^ (-(1 / E.ε)) := by
    rw [← rpow_mul hm.le, show -E.ε * -(1 / E.ε) = 1 by field_simp, rpow_one]
  rw [key, hA, rpow_neg (by positivity), ← inv_rpow (by positivity)]
  congr 1
  field_simp

/-! ## Equilibrium -/

/-- A symmetric flexible-price equilibrium given the money supply `M` (O&R §10.2.2–10.2.3):
households optimise, every producer sells `y_N = C_N = C^A_N` (symmetry, so `p_N = P_N`), the
money market clears, and seignorage is rebated (85). -/
def IsEquilibrium (E : Economy) (Q : Prices) (B0 Mm1 : ℝ) (M : ℕ → ℝ) (c : ℕ → Choice) :
    Prop :=
  HouseholdOptimal E Q B0 Mm1 c ∧ (∀ t, (c t).y = (c t).cN ∧ Q.CA t = (c t).cN) ∧
    (∀ t, (c t).money = M t) ∧ ∀ t, Q.τ t = -(M t - moneyPrev Mm1 c t) / Q.PT t

/-- Symmetry: when a producer sells `y = C^A_N`, its price equals the index, `p_N = P_N`
(O&R p. 692). -/
theorem invDemand_self (E : Economy) (Q : Prices) (t : ℕ) (hA : 0 < Q.CA t) :
    invDemand E Q t (Q.CA t) = Q.PN t := by
  simp [invDemand, div_self hA.ne']

/-- Net foreign bonds implied by wealth: `B_t = (A_t − M_{t−1}/P_{T,t})/(1+r)` (O&R (84)). -/
noncomputable def bonds (E : Economy) (Q : Prices) (B0 Mm1 : ℝ) (c : ℕ → Choice) (t : ℕ) :
    ℝ :=
  (wealth E.r (initWealth E Q B0 Mm1) (netRes E Q) c t - moneyPrev Mm1 c t / Q.PT t) / (1 + E.r)

/-- The discounted real value of money held into date `T`, `(1+r)^{−T} M_{T−1}/P_{T,T}`; the
book's no-speculative-bubble condition (p. 692) makes it vanish. -/
noncomputable def moneyBubble (E : Economy) (Q : Prices) (Mm1 : ℝ) (c : ℕ → Choice) (T : ℕ) :
    ℝ :=
  disc E.r T * (moneyPrev Mm1 c T / Q.PT T)

/-- In equilibrium, revenue equals the value of nontradables consumption:
`(P_N/P_T) C_N^{(θ−1)/θ} C_N^{1/θ} = (P_N/P_T) C_N` (O&R p. 692). -/
theorem realRevenue_symm (E : Economy) (Q : Prices) (t : ℕ) (hθ : 0 < E.θ) {x : ℝ}
    (hx : 0 < x) (hA : Q.CA t = x) : realRevenue E Q t x = relPrice Q t * x := by
  unfold realRevenue
  rw [hA, ← rpow_add hx, show (E.θ - 1) / E.θ + 1 / E.θ = 1 by field_simp; ring, rpow_one]

/-- The tradables current account in equilibrium (O&R (84)+(85), p. 691–692):
`B_0` as given and `B_{t+1} = (1+r)B_t + ȳ_T − C_{T,t}`: money and seignorage cancel. -/
theorem bonds_recursion {E : Economy} {Q : Prices} (hE : E.Valid) (hQ : Q.Valid E.r)
    {B0 Mm1 : ℝ} {M : ℕ → ℝ} {c : ℕ → Choice} (heq : IsEquilibrium E Q B0 Mm1 M c) :
    bonds E Q B0 Mm1 c 0 = B0 ∧
      ∀ t, bonds E Q B0 Mm1 c (t + 1) = (1 + E.r) * bonds E Q B0 Mm1 c t + E.yT - (c t).cT := by
  obtain ⟨hopt, hsym, hmon, htax⟩ := heq
  obtain ⟨_, _, hr, _, _, _, _, _, hθ, _⟩ := hE
  refine ⟨?_, ?_⟩
  · simp only [bonds, wealth, initWealth, moneyPrev]; field_simp; ring
  · intro t
    obtain ⟨hT, _, _, _⟩ := hQ t
    have hT1 := (hQ (t + 1)).1
    have hcN := (hopt.1 t).2.1
    have hrev := realRevenue_symm E Q t (by linarith) hcN (hsym t).2
    simp only [bonds, wealth, netRes, userCost]
    rw [show moneyPrev Mm1 c (t + 1) = (c t).money from rfl, (hsym t).1, hrev, htax t, hmon t]
    field_simp
    ring

/-- With `β(1+r) = 1`, the Euler equation makes tradables consumption constant, (87). -/
theorem cT_const {E : Economy} {c : ℕ → Choice} (hγ : 0 < E.γ) (hβr : E.β * (1 + E.r) = 1)
    (hc : ∀ t, c t ∈ posChoice) (heu : EulerFOC E c) (t : ℕ) : (c t).cT = (c 0).cT := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have h := heu t
    rw [hβr, one_mul] at h
    have ha := (hc t).1
    have ha1 := (hc (t + 1)).1
    field_simp at h
    rw [← ih]; linarith

/-- Bonds in closed form when `B_0 = 0` and `C_T ≡ c`:
`(1+r)^{−T}(1+r)B_T = (1+r)(ȳ_T − c)(1 − (1+r)^{−T})/r` (O&R p. 692). -/
theorem disc_bonds_closed {E : Economy} {Q : Prices} {B0 Mm1 : ℝ} {c : ℕ → Choice}
    (hr0 : 0 < E.r) (hB : bonds E Q B0 Mm1 c 0 = 0)
    (hrec : ∀ t, bonds E Q B0 Mm1 c (t + 1) = (1 + E.r) * bonds E Q B0 Mm1 c t + E.yT - (c t).cT)
    (hconst : ∀ t, (c t).cT = (c 0).cT) (T : ℕ) :
    disc E.r T * ((1 + E.r) * bonds E Q B0 Mm1 c T)
      = (1 + E.r) * (E.yT - (c 0).cT) * (1 - disc E.r T) / E.r := by
  have hr : 0 < 1 + E.r := by linarith
  induction T with
  | zero => simp [disc, hB]
  | succ T ih =>
    rw [hrec T, hconst T]
    have hd := disc_succ_mul hr T
    have e : disc E.r (T + 1) = disc E.r T / (1 + E.r) := by
      rw [← hd]; field_simp
    rw [e]
    field_simp
    field_simp at ih
    linear_combination (1 + E.r) * ih

/-- The discount factor vanishes: `(1+r)^{−T} → 0` for `r > 0`. -/
theorem tendsto_disc {r : ℝ} (hr0 : 0 < r) : Tendsto (disc r) atTop (𝓝 0) := by
  have h1 : (1 + r)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have h0 : 0 ≤ (1 + r)⁻¹ := by positivity
  have e : disc r = fun n => ((1 + r)⁻¹) ^ n := by funext n; simp [disc, inv_pow]
  rw [e]; exact tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1

/-- A convergent sequence that is frequently below `c` has limit at most `c`. -/
theorem ge_of_tendsto_of_frequently {s : ℕ → ℝ} {L c : ℝ} (hs : Tendsto s atTop (𝓝 L))
    (hc : ∃ᶠ T in atTop, s T ≤ c) : L ≤ c := by
  have := le_of_tendsto_of_frequently (s := fun T => -s T) (L := -L) (c := -c) hs.neg
    (hc.mono fun T h => by linarith)
  linarith

/-- The pieces of discounted wealth in equilibrium: bonds plus the money term (O&R (16)). -/
theorem disc_wealth_split {E : Economy} {Q : Prices} (hr : 0 < 1 + E.r) (B0 Mm1 : ℝ)
    (c : ℕ → Choice) (T : ℕ) :
    disc E.r T * wealth E.r (initWealth E Q B0 Mm1) (netRes E Q) c T
      = disc E.r T * ((1 + E.r) * bonds E Q B0 Mm1 c T) + moneyBubble E Q Mm1 c T := by
  simp only [bonds, moneyBubble]; field_simp; ring

/-- (91), p. 692, FIRST HALF: in any equilibrium with `β(1+r) = 1` and `B_0 = 0`, tradables
consumption is constant and AT LEAST the endowment (the transversality condition rules out
over-saving), for ANY money path. -/
theorem cT_ge_endowment {E : Economy} {Q : Prices} (hE : E.Valid) (hβr : E.β * (1 + E.r) = 1)
    (hQ : Q.Valid E.r) {Mm1 : ℝ} {M : ℕ → ℝ} {c : ℕ → Choice}
    (heq : IsEquilibrium E Q 0 Mm1 M c) (hMm1 : 0 < Mm1) :
    (∀ t, (c t).cT = (c 0).cT) ∧ E.yT ≤ (c 0).cT := by
  have hE' := hE
  obtain ⟨hβ, hβ1, hr, hγ0, _, _, _, _, _, _⟩ := hE'
  have hr0 : 0 < E.r := by nlinarith
  have hopt := heq.1
  have hconst := cT_const hγ0 hβr hopt.1 (eulerFOC_of_optimal hE hopt)
  refine ⟨hconst, ?_⟩
  obtain ⟨hB0, hrec⟩ := bonds_recursion hE hQ heq
  have hcl := disc_bonds_closed hr0 hB0 hrec hconst
  have hlim : Tendsto (fun T => disc E.r T * ((1 + E.r) * bonds E Q 0 Mm1 c T)) atTop
      (𝓝 ((1 + E.r) * (E.yT - (c 0).cT) * (1 - 0) / E.r)) := by
    simp_rw [hcl]
    exact ((tendsto_const_nhds.sub (tendsto_disc hr0)).const_mul _).div_const _
  have hMB : ∀ T, 0 ≤ moneyBubble E Q Mm1 c T := by
    intro T
    unfold moneyBubble
    refine mul_nonneg (disc_pos hr T).le (div_nonneg ?_ (hQ T).1.le)
    cases T with
    | zero => exact hMm1.le
    | succ T => exact (hopt.1 T).2.2.1.le
  have htv := liminfNonpos_of_householdOptimal hE hopt
  have hle : ∀ δ > 0, (1 + E.r) * (E.yT - (c 0).cT) * (1 - 0) / E.r ≤ δ := by
    intro δ hδ
    apply ge_of_tendsto_of_frequently hlim
    refine (htv δ hδ).mono fun T hT => ?_
    rw [disc_wealth_split hr] at hT
    linarith [hMB T]
  have h0 : (1 + E.r) * (E.yT - (c 0).cT) * (1 - 0) / E.r ≤ 0 :=
    le_of_forall_pos_le_add fun δ hδ => by linarith [hle δ hδ]
  rw [sub_zero, mul_one, div_nonpos_iff] at h0
  rcases h0 with ⟨_, h⟩ | ⟨h, _⟩
  · linarith
  · nlinarith

/-- (91), p. 692, EXACT FORM: in any equilibrium with `β(1+r) = 1` and `B_0 = 0`, for ANY money
path, `C_T = ȳ_T` IF AND ONLY IF the discounted real value of money has liminf zero (no
speculative bubble in money). -/
theorem cT_eq_endowment_iff {E : Economy} {Q : Prices} (hE : E.Valid) (hβr : E.β * (1 + E.r) = 1)
    (hQ : Q.Valid E.r) {Mm1 : ℝ} {M : ℕ → ℝ} {c : ℕ → Choice}
    (heq : IsEquilibrium E Q 0 Mm1 M c) (hMm1 : 0 < Mm1) :
    (c 0).cT = E.yT ↔ ∀ δ > 0, ∃ᶠ T in atTop, moneyBubble E Q Mm1 c T ≤ δ := by
  have hE' := hE
  obtain ⟨hβ, hβ1, hr, hγ0, _, _, _, _, _, _⟩ := hE'
  have hr0 : 0 < E.r := by nlinarith
  have hopt := heq.1
  obtain ⟨hconst, hge⟩ := cT_ge_endowment hE hβr hQ heq hMm1
  obtain ⟨hB0, hrec⟩ := bonds_recursion hE hQ heq
  have hcl := disc_bonds_closed hr0 hB0 hrec hconst
  constructor
  · intro hc δ hδ
    have htv := liminfNonpos_of_householdOptimal hE hopt
    refine (htv δ hδ).mono fun T hT => ?_
    rw [disc_wealth_split hr, hcl, hc, sub_self] at hT
    simpa using hT
  · intro hMB
    set L := (1 + E.r) * (E.yT - (c 0).cT) / E.r
    have hlim : Tendsto (fun T => disc E.r T * ((1 + E.r) * bonds E Q 0 Mm1 c T)) atTop
        (𝓝 (L * (1 - 0))) := by
      simp_rw [hcl]
      have := ((tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_disc hr0)).const_mul L
      refine this.congr fun T => ?_
      simp only [L]; ring
    rw [sub_zero, mul_one] at hlim
    have hge' : ∀ δ > 0, -(3 * δ) ≤ L := by
      intro δ hδ
      have hev : ∀ᶠ T in atTop, disc E.r T * ((1 + E.r) * bonds E Q 0 Mm1 c T) < L + δ :=
        hlim.eventually (gt_mem_nhds (by linarith))
      obtain ⟨T, ⟨h1, h2⟩, h3⟩ := (((hMB δ hδ).and_eventually (hopt.2.1 δ hδ)).and_eventually
        hev).exists
      rw [disc_wealth_split hr] at h2
      linarith
    have hL : 0 ≤ L := le_of_forall_pos_le_add fun δ hδ => by
      have := hge' (δ / 3) (by positivity); linarith
    have : (c 0).cT ≤ E.yT := by
      have := div_nonneg_iff.mp hL
      rcases this with ⟨h, _⟩ | ⟨_, h⟩
      · nlinarith
      · linarith
    linarith

/-- (91), p. 692, under the book's no-speculative-bubble condition `(1+r)^{−T} M_{T−1}/P_{T,T} → 0`:
`C_{T,t} = ȳ_T` and `B_t = 0` for all `t` — a balanced current account for ANY money path. -/
theorem balanced_current_account {E : Economy} {Q : Prices} (hE : E.Valid)
    (hβr : E.β * (1 + E.r) = 1) (hQ : Q.Valid E.r) {Mm1 : ℝ} {M : ℕ → ℝ} {c : ℕ → Choice}
    (heq : IsEquilibrium E Q 0 Mm1 M c) (hMm1 : 0 < Mm1)
    (hnb : Tendsto (moneyBubble E Q Mm1 c) atTop (𝓝 0)) :
    ∀ t, (c t).cT = E.yT ∧ bonds E Q 0 Mm1 c t = 0 := by
  obtain ⟨hconst, _⟩ := cT_ge_endowment hE hβr hQ heq hMm1
  have hc0 : (c 0).cT = E.yT := by
    rw [cT_eq_endowment_iff hE hβr hQ heq hMm1]
    intro δ hδ
    exact (hnb.eventually (gt_mem_nhds hδ)).frequently.mono fun _ h => h.le
  obtain ⟨hB0, hrec⟩ := bonds_recursion hE hQ heq
  intro t
  refine ⟨(hconst t).trans hc0, ?_⟩
  induction t with
  | zero => exact hB0
  | succ t ih => rw [hrec t, ih, hconst t, hc0]; ring


/-! ## Steady state (93) and the initial price level -/

/-- Steady-state nontradables output (93), p. 692: `ȳ_N = [(θ−1)(1−γ)/(κθ)]^{1/2}`. -/
noncomputable def ybarN (E : Economy) : ℝ := sqrt ((E.θ - 1) * (1 - E.γ) / (E.κ * E.θ))

/-- `ȳ_N > 0` (O&R (93)). -/
theorem ybarN_pos {E : Economy} (hE : E.Valid) : 0 < ybarN E := by
  obtain ⟨_, _, _, _, hγ1, _, _, hκ, hθ, _⟩ := hE
  unfold ybarN
  apply sqrt_pos.mpr
  apply div_pos (mul_pos (by linarith) (by linarith)) (mul_pos hκ (by linarith))

/-- `κ ȳ_N² = (θ−1)(1−γ)/θ` (O&R (93)). -/
theorem kappa_mul_ybarN_sq {E : Economy} (hE : E.Valid) :
    E.κ * ybarN E ^ 2 = (E.θ - 1) * (1 - E.γ) / E.θ := by
  obtain ⟨_, _, _, _, hγ1, _, _, hκ, hθ, _⟩ := hE
  unfold ybarN
  rw [sq_sqrt (div_nonneg (mul_nonneg (by linarith) (by linarith))
    (mul_nonneg hκ.le (by linarith)))]
  field_simp

/-- (93), p. 692: in ANY symmetric equilibrium, nontradables output and consumption equal `ȳ_N`
at every date (the unique positive solution of (90) with `y_N = C_N = C^A_N`). -/
theorem output_93 {E : Economy} {Q : Prices} (hE : E.Valid) {B0 Mm1 : ℝ} {M : ℕ → ℝ}
    {c : ℕ → Choice} (heq : IsEquilibrium E Q B0 Mm1 M c) (t : ℕ) :
    (c t).y = ybarN E ∧ (c t).cN = ybarN E := by
  have hE' := hE
  obtain ⟨_, _, _, _, hγ1, _, _, hκ, hθ, _⟩ := hE'
  obtain ⟨hopt, hsym, _, _⟩ := heq
  have hc := hopt.1
  have h90 := labour_90 hE hc (intraFOC_of_optimal hE hopt) (labourFOC_of_optimal hE hopt) t
  obtain ⟨hy, hA⟩ := hsym t
  rw [hA, ← hy] at h90
  have hq := (hc t).2.2.2
  set x := (c t).y
  have hθ0 : 0 < E.θ := by linarith
  have e1 : x ^ ((E.θ + 1) / E.θ) = x * x ^ (1 / E.θ) := by
    rw [show (E.θ + 1) / E.θ = 1 + 1 / E.θ by field_simp, rpow_add hq, rpow_one]
  rw [e1] at h90
  have hx1 : 0 < x ^ (1 / E.θ) := rpow_pos_of_pos hq _
  have hsq : x ^ 2 = (E.θ - 1) * (1 - E.γ) / (E.κ * E.θ) := by
    field_simp at h90 ⊢
    nlinarith
  have hxy : x = ybarN E := by
    unfold ybarN; rw [← hsq, sqrt_sq hq.le]
  exact ⟨hxy, hy ▸ hxy⟩

/-- Homogeneity of (83): `P = P_T · P(1, P_N/P_T)` (O&R p. 690). -/
theorem cpi_eq_mul {γ PT PN : ℝ} (hT : 0 < PT) (hN : 0 < PN) :
    cpi γ PT PN = PT * cpi γ 1 (PN / PT) := by
  unfold cpi
  rw [one_rpow, div_rpow hN.le hT.le, rpow_sub hT, rpow_one]
  have : 0 < PT ^ γ := rpow_pos_of_pos hT γ
  field_simp

/-- The steady-state relative price `P_N/P_T = ((1−γ)/γ)(ȳ_T/ȳ_N)` from (89) (O&R p. 692). -/
noncomputable def relPriceBar (E : Economy) : ℝ := (1 - E.γ) / E.γ * (E.yT / ybarN E)

/-- The steady-state ratio `P/P_T = P(1, P_N/P_T)` (O&R (83)). -/
noncomputable def cpiRatio (E : Economy) : ℝ := cpi E.γ 1 (relPriceBar E)

/-- Steady-state real balances from (92) with constant prices:
`M/P = [(χ/γ) ȳ_T (P_T/P)/(1−β)]^{1/ε}` (O&R p. 692). -/
noncomputable def realMoneyBar (E : Economy) : ℝ :=
  (E.χ / E.γ * (E.yT / cpiRatio E) / (1 - E.β)) ^ (1 / E.ε)

/-- The steady-state relative price is positive (O&R p. 692). -/
theorem relPriceBar_pos {E : Economy} (hE : E.Valid) : 0 < relPriceBar E := by
  have h := ybarN_pos hE
  obtain ⟨_, _, _, hγ0, hγ1, _, _, _, _, hy⟩ := hE
  unfold relPriceBar
  have : 0 < 1 - E.γ := by linarith
  positivity

/-- `P/P_T > 0` in the steady state (O&R (83)). -/
theorem cpiRatio_pos {E : Economy} (hE : E.Valid) : 0 < cpiRatio E := by
  have h := relPriceBar_pos hE
  obtain ⟨_, _, _, hγ0, hγ1, _, _, _, _, _⟩ := hE
  exact cpi_pos hγ0 hγ1 one_pos h

/-- Steady-state real balances are positive (O&R (92)). -/
theorem realMoneyBar_pos {E : Economy} (hE : E.Valid) : 0 < realMoneyBar E := by
  have h := cpiRatio_pos hE
  obtain ⟨_, hβ1, _, hγ0, _, hχ, _, _, _, hy⟩ := hE
  unfold realMoneyBar
  have : 0 < 1 - E.β := by linarith
  positivity

/-- UNIQUENESS of the steady state and of the initial price level `P̄_0` given `M̄_0`
(O&R §10.2.3, p. 692): in any equilibrium with constant prices `P_T, P_N`, constant money `M̄`,
`B_0 = 0` and `β(1+r) = 1`, the allocation is `(ȳ_T, ȳ_N, M̄, ȳ_N)` at every date,
`P_N = (P_N/P_T)‾ P_T`, and `P = M̄/(M/P)‾`, `P_T = M̄/((M/P)‾ (P/P_T)‾)` — all proportional to
`M̄` (long-run neutrality, (98)). -/
theorem steadyState_unique {E : Economy} {Q : Prices} (hE : E.Valid) (hβr : E.β * (1 + E.r) = 1)
    (hQ : Q.Valid E.r) {Mbar pT pN : ℝ} (hM0 : 0 < Mbar) {M : ℕ → ℝ} {c : ℕ → Choice}
    (hPT : ∀ t, Q.PT t = pT) (hPN : ∀ t, Q.PN t = pN) (hMt : ∀ t, M t = Mbar)
    (heq : IsEquilibrium E Q 0 Mbar M c) :
    (∀ t, (c t).cT = E.yT ∧ (c t).cN = ybarN E ∧ (c t).money = Mbar ∧ (c t).y = ybarN E) ∧
      pN = relPriceBar E * pT ∧ cpi E.γ pT pN = Mbar / realMoneyBar E ∧
      pT = Mbar / (realMoneyBar E * cpiRatio E) := by
  have hE' := hE
  obtain ⟨hβ, hβ1, hr, hγ0, hγ1, hχ, hε, _, _, hyT⟩ := hE'
  have hr0 : 0 < E.r := by nlinarith
  have hopt := heq.1
  have hc := hopt.1
  have hT : 0 < pT := hPT 0 ▸ (hQ 0).1
  have hN : 0 < pN := hPN 0 ▸ (hQ 0).2.1
  have hmp : ∀ T, moneyPrev Mbar c T = Mbar := by
    intro T; cases T with
    | zero => rfl
    | succ T => simp only [moneyPrev]; rw [heq.2.2.1 T, hMt T]
  have hnb : Tendsto (moneyBubble E Q Mbar c) atTop (𝓝 0) := by
    have e : moneyBubble E Q Mbar c = fun T => disc E.r T * (Mbar / pT) := by
      funext T; simp only [moneyBubble, hmp T, hPT T]
    rw [e]; simpa using (tendsto_disc hr0).mul_const (Mbar / pT)
  have hca := balanced_current_account hE hβr hQ heq hM0 hnb
  have h93 := output_93 hE heq
  have hall : ∀ t, (c t).cT = E.yT ∧ (c t).cN = ybarN E ∧ (c t).money = Mbar ∧
      (c t).y = ybarN E := fun t =>
    ⟨(hca t).1, (h93 t).2, (heq.2.2.1 t).trans (hMt t), (h93 t).1⟩
  have hyb := ybarN_pos hE
  -- (89)
  have hintra := intraFOC_of_optimal hE hopt 0
  rw [(hall 0).1, (hall 0).2.1] at hintra
  simp only [relPrice, hPT, hPN] at hintra
  have hrel : pN = relPriceBar E * pT := by
    unfold relPriceBar; field_simp at hintra ⊢; linarith
  -- (92)
  have h92 := money_92 hE hβr hQ hc (moneyFOC_of_optimal hE hQ hopt) 0
  simp only [cpiAt, hPT, hPN, (hall 0).1, (hall 0).2.2.1] at h92
  have hP : cpi E.γ pT pN = pT * cpiRatio E := by
    rw [cpi_eq_mul hT hN, hrel, mul_div_cancel_right₀ _ hT.ne']; rfl
  have hcr := cpiRatio_pos hE
  have hmb : Mbar / cpi E.γ pT pN = realMoneyBar E := by
    rw [h92, hP, div_self hT.ne', mul_one]
    unfold realMoneyBar
    congr 1
    field_simp
  have hPbar : cpi E.γ pT pN = Mbar / realMoneyBar E := by
    have hPpos : 0 < cpi E.γ pT pN := cpi_pos hγ0 hγ1 hT hN
    have := realMoneyBar_pos hE
    field_simp at hmb ⊢; linarith
  refine ⟨hall, hrel, hPbar, ?_⟩
  rw [hP] at hPbar
  field_simp at hPbar ⊢
  linarith

/-- The steady-state price paths given `M̄` (O&R §10.2.3): `P_T = M̄/((M/P)‾ (P/P_T)‾)`,
`P_N = (P_N/P_T)‾ P_T`, aggregate demand `ȳ_N`, zero taxes. -/
noncomputable def steadyPrices (E : Economy) (Mbar : ℝ) : Prices :=
  ⟨fun _ => Mbar / (realMoneyBar E * cpiRatio E),
    fun _ => relPriceBar E * (Mbar / (realMoneyBar E * cpiRatio E)), fun _ => ybarN E,
    fun _ => 0⟩

/-- The steady-state allocation `(ȳ_T, ȳ_N, M̄, ȳ_N)` (O&R (91), (93)). -/
noncomputable def steadyChoice (E : Economy) (Mbar : ℝ) : ℕ → Choice :=
  fun _ => ⟨E.yT, ybarN E, Mbar, ybarN E⟩

/-- EXISTENCE (O&R §10.2.3, p. 692): for every `M̄ > 0` the steady state IS an equilibrium —
the allocation `(ȳ_T, ȳ_N, M̄, ȳ_N)` is a genuine infinite-horizon household optimum at the
steady-state prices (verified through `householdOptimal_iff`), markets clear and (85) holds. -/
theorem steadyState_isEquilibrium {E : Economy} (hE : E.Valid) (hβr : E.β * (1 + E.r) = 1)
    {Mbar : ℝ} (hM0 : 0 < Mbar) :
    (steadyPrices E Mbar).Valid E.r ∧
      IsEquilibrium E (steadyPrices E Mbar) 0 Mbar (fun _ => Mbar) (steadyChoice E Mbar) := by
  have hE' := hE
  obtain ⟨hβ, hβ1, hr, hγ0, hγ1, hχ, hε, hκ, hθ, hyT⟩ := hE'
  have hr0 : 0 < E.r := by nlinarith
  have hyb := ybarN_pos hE
  have hrel := relPriceBar_pos hE
  have hcr := cpiRatio_pos hE
  have hmb := realMoneyBar_pos hE
  set pT := Mbar / (realMoneyBar E * cpiRatio E) with hpT
  have hT : 0 < pT := by positivity
  set Q := steadyPrices E Mbar
  set c := steadyChoice E Mbar
  have hu : ∀ t, userCost E.r Q t = (1 - E.β) / pT := by
    intro t
    simp only [userCost, Q, steadyPrices]
    rw [← hpT]
    have : 1 / ((1 + E.r) * pT) = E.β / pT := by field_simp; linarith
    rw [this]; field_simp
  have hQ : Q.Valid E.r := by
    intro t
    refine ⟨hT, by simp only [Q, steadyPrices]; positivity, hyb, ?_⟩
    rw [hu t]; exact div_pos (by linarith) hT
  have hPcpi : ∀ t, cpiAt E Q t = pT * cpiRatio E := by
    intro t
    simp only [cpiAt, Q, steadyPrices]
    rw [← hpT, cpi_eq_mul hT (by positivity), mul_div_cancel_right₀ _ hT.ne']
    rfl
  have hc : ∀ t, c t ∈ posChoice := fun _ => ⟨hyT, hyb, hM0, hyb⟩
  have hw : ∀ t, wealth E.r (initWealth E Q 0 Mbar) (netRes E Q) c t = Mbar / pT := by
    intro t
    induction t with
    | zero => simp only [wealth, initWealth, Q, steadyPrices]; rw [← hpT]; ring
    | succ t ih =>
      rw [wealth, ih]
      have hrev : realRevenue E Q t (c t).y = relPrice Q t * (c t).cN :=
        realRevenue_symm E Q t (by linarith) hyb rfl
      simp only [netRes, hrev, hu t]
      simp only [c, steadyChoice, Q, steadyPrices]
      field_simp
      linear_combination Mbar * hβr
  have hdw : Tendsto (fun T => disc E.r T * wealth E.r (initWealth E Q 0 Mbar) (netRes E Q) c T)
      atTop (𝓝 0) := by
    simp_rw [hw]; simpa using (tendsto_disc hr0).mul_const (Mbar / pT)
  have hnp : NoPonzi E.r (wealth E.r (initWealth E Q 0 Mbar) (netRes E Q) c) :=
    fun δ hδ => (hdw.eventually (lt_mem_nhds (by linarith : -δ < 0))).mono fun _ h => h.le
  have htv : LiminfNonpos E.r (wealth E.r (initWealth E Q 0 Mbar) (netRes E Q) c) :=
    fun δ hδ => (hdw.eventually (gt_mem_nhds hδ)).frequently.mono fun _ h => h.le
  have hsum : Summable fun t => E.β ^ t * periodU E Q t (c t) := by
    have e : (fun t => E.β ^ t * periodU E Q t (c t))
        = fun t => E.β ^ t * periodU E Q 0 (c 0) := by
      funext t; rfl
    rw [e]
    exact (summable_geometric_of_lt_one hβ.le hβ1).mul_right _
  have heu : EulerFOC E c := by
    intro t; simp only [c, steadyChoice]; rw [hβr, one_mul]
  have hN : IntraFOC E Q c := by
    intro t
    simp only [c, steadyChoice, relPrice, Q, steadyPrices]
    rw [mul_div_cancel_right₀ _ hT.ne']
    unfold relPriceBar; field_simp
  have hMF : MoneyFOC E Q c := by
    intro t
    simp only [c, steadyChoice]
    rw [hu t, hPcpi t]
    have hmbar : Mbar / (pT * cpiRatio E) = realMoneyBar E := by
      rw [hpT]; field_simp
    rw [hmbar]
    unfold realMoneyBar
    rw [← rpow_mul (by positivity), show 1 / E.ε * -E.ε = -1 by field_simp, rpow_neg_one]
    have : 0 < 1 - E.β := by linarith
    field_simp
  have hL : LabourFOC E Q c := by
    intro t
    simp only [c, steadyChoice, relPrice, Q, steadyPrices]
    rw [mul_div_cancel_right₀ _ hT.ne', ← rpow_add hyb,
      show (E.θ - 1) / E.θ - 1 + 1 / E.θ = 0 by field_simp; ring, rpow_zero, mul_one]
    have hk := kappa_mul_ybarN_sq hE
    unfold relPriceBar
    field_simp at hk ⊢
    linarith
  refine ⟨hQ, householdOptimal_of_foc hE hQ hc hsum heu hN hMF hL hnp htv, ?_, ?_, ?_⟩
  · intro t; exact ⟨rfl, rfl⟩
  · intro t; rfl
  · intro t
    have : moneyPrev Mbar c t = Mbar := by cases t <;> rfl
    simp [this, Q, steadyPrices]

end ObstfeldRogoff.StickyPriceModels.NontradablesModel
