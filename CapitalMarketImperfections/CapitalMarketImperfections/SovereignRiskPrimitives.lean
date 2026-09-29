/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import CapitalMarketImperfections.Model
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Order.Field

/-!
# Primitives for sovereign risk models

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §6.1
(pp. 349–379) and Appendix 6B (pp. 422–425).

Shared machinery for the sovereign-risk chain of modules:

* **States.** Uncertainty is a finite state space with probabilities `π(s)` (the
  `StateSpace` of `Model`); the book's shock `ε` takes the values `ε_1 < ⋯ < ε_N`
  with `π(ε_i) > 0` (p. 354). Strict positivity is added as a hypothesis where needed.
  We prove the expectation is monotone, strictly monotone on a positive-probability
  state, and that a nonnegative variable with zero mean vanishes.
* **Utility.** A period utility `u` on `(0, ∞)` that is differentiable with `u' > 0` and
  strictly concave (the book's standing assumptions, p. 354). We prove the supporting-line
  (Lagrangian) inequality `u(x) ≤ u(y) + u'(y)(x − y)`, strict for `x ≠ y`, which gives
  sufficiency *and* uniqueness in every optimal-contract problem of the chapter without
  a Kuhn–Tucker theorem; monotonicity of `u` and strict monotonicity of `u'`; and
  Jensen's inequality `E u(C) ≤ u(E C)` with its strict form.
* **The clamp lemma.** The optimal contracts of §6.1.1.3, Appendix 6B and Exercise 2 all
  have consumption `C = min(hi, max(c̄, lo))` for pointwise bounds `lo ≤ C ≤ hi` imposed by
  incentive and nonnegativity constraints; `clamp_optimal` shows such a schedule
  maximises `E u(C)` among all schedules within the bounds with no larger mean, uniquely.
* **Intermediate values and geometric sums** used for thresholds and costs of exclusion.
-/

namespace ObstfeldRogoff.CapitalMarketImperfections.SovereignRiskPrimitives

open Finset Set

/-- A period utility function on positive consumption (O&R §6.1.1.1, p. 354): differentiable
with strictly positive marginal utility `du = u'` and strictly concave on `(0, ∞)`. -/
structure Utility where
  u : ℝ → ℝ
  du : ℝ → ℝ
  hasDerivAt : ∀ x, 0 < x → HasDerivAt u (du x) x
  du_pos : ∀ x, 0 < x → 0 < du x
  strictConcave : StrictConcaveOn ℝ (Ioi 0) u

namespace Utility

variable (U : Utility)

/-- The strict supporting-line (Lagrangian) inequality for strictly concave utility,
O&R §6.1.1.3, p. 356: `u(x) < u(y) + u'(y)(x − y)` for positive `x ≠ y`. -/
theorem supporting_line_strict {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (hxy : x ≠ y) :
    U.u x < U.u y + U.du y * (x - y) := by
  rcases lt_or_gt_of_ne hxy with h | h
  · have hs := U.strictConcave.lt_slope_of_hasDerivAt (mem_Ioi.mpr hx) (mem_Ioi.mpr hy) h
      (U.hasDerivAt y hy)
    rw [slope_def_field, lt_div_iff₀ (by linarith)] at hs
    nlinarith
  · have hs := U.strictConcave.slope_lt_of_hasDerivAt (mem_Ioi.mpr hy) (mem_Ioi.mpr hx) h
      (U.hasDerivAt y hy)
    rw [slope_def_field, div_lt_iff₀ (by linarith)] at hs
    nlinarith

/-- The supporting-line inequality `u(x) ≤ u(y) + u'(y)(x − y)` (O&R §6.1.1.3, p. 356). -/
theorem supporting_line {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    U.u x ≤ U.u y + U.du y * (x - y) := by
  rcases eq_or_ne x y with h | h
  · subst h; simp
  · exact (U.supporting_line_strict hx hy h).le

/-- Utility is strictly increasing in consumption (O&R p. 354). -/
theorem strictMonoOn : StrictMonoOn U.u (Ioi 0) := by
  intro x hx y hy hxy
  have h := U.supporting_line_strict hx hy hxy.ne
  have hd := U.du_pos y hy
  have : U.du y * (x - y) < 0 := mul_neg_of_pos_of_neg hd (by linarith)
  linarith

/-- Monotonicity of utility in the form `x ≤ y → u x ≤ u y` (O&R p. 354). -/
theorem mono {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : U.u x ≤ U.u y :=
  U.strictMonoOn.monotoneOn hx (lt_of_lt_of_le hx hxy) hxy

/-- Strict monotonicity in the form `x < y → u x < u y` (O&R p. 354). -/
theorem lt {x y : ℝ} (hx : 0 < x) (hxy : x < y) : U.u x < U.u y :=
  U.strictMonoOn hx (lt_trans hx hxy) hxy

/-- Utility comparisons are consumption comparisons: `u x ≤ u y ↔ x ≤ y` (O&R p. 354). -/
theorem le_iff {x y : ℝ} (hx : 0 < x) (hy : 0 < y) : U.u x ≤ U.u y ↔ x ≤ y :=
  U.strictMonoOn.le_iff_le hx hy

/-- Equal utilities mean equal consumption (O&R p. 354). -/
theorem inj {x y : ℝ} (hx : 0 < x) (hy : 0 < y) (h : U.u x = U.u y) : x = y :=
  U.strictMonoOn.injOn hx hy h

/-- Marginal utility is strictly decreasing, `x < y → u'(y) < u'(x)` (strict concavity,
O&R §6.1.1.3, p. 357). -/
theorem du_strictAnti {x y : ℝ} (hx : 0 < x) (hxy : x < y) : U.du y < U.du x := by
  have hy : 0 < y := lt_trans hx hxy
  have h1 := U.strictConcave.lt_slope_of_hasDerivAt (mem_Ioi.mpr hx) (mem_Ioi.mpr hy) hxy
    (U.hasDerivAt y hy)
  have h2 := U.strictConcave.slope_lt_of_hasDerivAt (mem_Ioi.mpr hx) (mem_Ioi.mpr hy) hxy
    (U.hasDerivAt x hx)
  linarith

/-- Marginal utility is antitone on `(0, ∞)` (O&R §6.1.1.3, p. 357). -/
theorem du_anti {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : U.du y ≤ U.du x := by
  rcases eq_or_lt_of_le hxy with h | h
  · rw [h]
  · exact (U.du_strictAnti hx h).le

/-- Utility is continuous on `(0, ∞)` (it is differentiable there).
(O&R p. 354) -/
theorem continuousOn : ContinuousOn U.u (Ioi 0) := fun x hx =>
  (U.hasDerivAt x hx).continuousAt.continuousWithinAt

/-- Marginal utility is continuous on `(0, ∞)`: this follows from differentiability and
strict concavity alone (O&R p. 354; used for the Euler inequality in §6.1.2.3). The proof
squeezes `u′(y)` between `u′(x)` and a combination of secant slopes that tends to `u′(x)`. -/
theorem du_continuousAt {x : ℝ} (hx : 0 < x) : ContinuousAt U.du x := by
  rw [← continuousWithinAt_compl_self]
  have hs : Filter.Tendsto (slope U.u x) (nhdsWithin x {x}ᶜ) (nhds (U.du x)) :=
    hasDerivAt_iff_tendsto_slope.mp (U.hasDerivAt x hx)
  have hmap : Filter.Tendsto (fun y : ℝ => 2 * y - x) (nhdsWithin x {x}ᶜ) (nhdsWithin x {x}ᶜ) := by
    have hc : Filter.Tendsto (fun y : ℝ => 2 * y - x) (nhds x) (nhds x) := by
      have := ((Filter.tendsto_id (x := nhds x)).const_mul 2).sub_const x
      rw [show 2 * x - x = x by ring] at this
      exact this
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
      (hc.mono_left nhdsWithin_le_nhds) ?_
    filter_upwards [self_mem_nhdsWithin] with y hy
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hy ⊢
    intro h; apply hy; linarith
  set g : ℝ → ℝ := fun y => 2 * slope U.u x (2 * y - x) - slope U.u x y with hg
  have hglim : Filter.Tendsto g (nhdsWithin x {x}ᶜ) (nhds (U.du x)) := by
    have := ((hs.comp hmap).const_mul 2).sub hs
    simpa [hg, two_mul] using this
  -- `g y` is the secant slope over `[y, 2y − x]` (or `[2y − x, y]`)
  have hgid : ∀ y, y ≠ x → g y = slope U.u y (2 * y - x) := by
    intro y hy
    have h1 : y - x ≠ 0 := sub_ne_zero.mpr hy
    have h2 : 2 * y - x - x ≠ 0 := by intro h; apply h1; linarith
    have h3 : 2 * y - x - y ≠ 0 := by intro h; apply h1; linarith
    simp only [hg, slope_def_field]
    field_simp
    ring
  have hnear : ∀ᶠ y in nhdsWithin x {x}ᶜ, 0 < y ∧ 0 < 2 * y - x := by
    apply eventually_nhdsWithin_of_eventually_nhds
    have h1 : ∀ᶠ y in nhds x, x / 2 < y := lt_mem_nhds (by linarith)
    filter_upwards [h1] with y hy
    constructor <;> linarith
  have hbound : ∀ᶠ y in nhdsWithin x {x}ᶜ, |U.du y - U.du x| ≤ |g y - U.du x| := by
    filter_upwards [hnear, self_mem_nhdsWithin] with y hy hyx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hyx
    rw [hgid y hyx]
    rcases lt_or_gt_of_ne hyx with hlt | hgt
    · -- `y < x`: `u′(x) ≤ u′(y) ≤ slope over [2y − x, y]`
      have h1 := U.du_anti hy.1 hlt.le
      have h2 := U.strictConcave.concaveOn.le_slope_of_hasDerivAt (mem_Ioi.mpr hy.2)
        (mem_Ioi.mpr hy.1) (by linarith) (U.hasDerivAt y hy.1)
      rw [slope_comm] at h2
      rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)]
      linarith
    · -- `x < y`: `slope over [y, 2y − x] ≤ u′(y) ≤ u′(x)`
      have h1 := U.du_anti hx hgt.le
      have h2 := U.strictConcave.concaveOn.slope_le_of_hasDerivAt (mem_Ioi.mpr hy.1)
        (mem_Ioi.mpr hy.2) (by linarith) (U.hasDerivAt y hy.1)
      rw [abs_of_nonpos (by linarith), abs_of_nonpos (by linarith)]
      linarith
  have hz : Filter.Tendsto (fun y => |g y - U.du x|) (nhdsWithin x {x}ᶜ) (nhds 0) := by
    have := (hglim.sub_const (U.du x)).abs
    simpa using this
  have hz' := squeeze_zero' (Filter.Eventually.of_forall fun y => abs_nonneg _) hbound hz
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  simpa [Real.norm_eq_abs] using hz'

/-- Marginal utility is continuous on `(0, ∞)` (O&R p. 354). -/
theorem du_continuousOn : ContinuousOn U.du (Ioi 0) := fun _ hx =>
  (U.du_continuousAt hx).continuousWithinAt

end Utility

namespace StateSpaceFacts

variable {S : Type} [Fintype S] (Ω : StateSpace S)

/-- A probability space on finitely many states has at least one state (the
probabilities sum to one, O&R p. 354). -/
theorem nonempty (Ω : StateSpace S) : Nonempty S := by
  by_contra h
  rw [not_nonempty_iff] at h
  have := Ω.prob_sum
  simp at this

/-- Expectation is linear: `E[aX + bY] = a E X + b E Y` (O&R p. 354). -/
theorem expect_linear (a b : ℝ) (X Y : S → ℝ) :
    Ω.expect (fun s => a * X s + b * Y s) = a * Ω.expect X + b * Ω.expect Y := by
  simp only [StateSpace.expect, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1 <;> apply Finset.sum_congr rfl <;> intro s _ <;> ring

/-- Expectation of a difference (O&R p. 354). -/
theorem expect_sub (X Y : S → ℝ) :
    Ω.expect (fun s => X s - Y s) = Ω.expect X - Ω.expect Y := by
  have := expect_linear Ω 1 (-1) X Y
  simp only [one_mul, neg_one_mul, ← sub_eq_add_neg] at this
  exact this

/-- Expectation of `c + X` (O&R p. 354). -/
theorem expect_const_add (c : ℝ) (X : S → ℝ) :
    Ω.expect (fun s => c + X s) = c + Ω.expect X := by
  rw [Ω.expect_add (fun _ => c) X, Ω.expect_const]

/-- Expectation of `c X` (O&R p. 354). -/
theorem expect_const_mul (c : ℝ) (X : S → ℝ) :
    Ω.expect (fun s => c * X s) = c * Ω.expect X := by
  simp only [StateSpace.expect, Finset.mul_sum]
  apply Finset.sum_congr rfl; intro s _; ring

/-- Expectation is monotone (O&R p. 354). -/
theorem expect_mono {X Y : S → ℝ} (h : ∀ s, X s ≤ Y s) : Ω.expect X ≤ Ω.expect Y :=
  Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (h s) (Ω.prob_nonneg s)

/-- Expectation is strictly monotone when the inequality is strict on a state of positive
probability (O&R p. 354). -/
theorem expect_strictMono {X Y : S → ℝ} (h : ∀ s, X s ≤ Y s) {s₀ : S}
    (hp : 0 < Ω.prob s₀) (hs : X s₀ < Y s₀) : Ω.expect X < Ω.expect Y :=
  Finset.sum_lt_sum (fun s _ => mul_le_mul_of_nonneg_left (h s) (Ω.prob_nonneg s))
    ⟨s₀, Finset.mem_univ _, mul_lt_mul_of_pos_left hs hp⟩

/-- A nonnegative random variable with zero mean vanishes in every state of positive
probability (O&R p. 356, used with the zero-profit condition (1)). -/
theorem eq_zero_of_nonneg_of_expect_zero {X : S → ℝ} (hX : ∀ s, 0 ≤ X s)
    (hE : Ω.expect X = 0) {s : S} (hp : 0 < Ω.prob s) : X s = 0 := by
  by_contra hne
  have hlt : (fun _ : S => (0 : ℝ)) s < X s := lt_of_le_of_ne (hX s) (Ne.symm hne)
  have := expect_strictMono Ω hX hp hlt
  rw [Ω.expect_const] at this
  linarith

/-- A nonpositive random variable with zero mean vanishes in every state of positive
probability (O&R p. 365: an incentive-compatible zero-profit contract with `P ≤ 0` is
null). -/
theorem eq_zero_of_nonpos_of_expect_zero {X : S → ℝ} (hX : ∀ s, X s ≤ 0)
    (hE : Ω.expect X = 0) {s : S} (hp : 0 < Ω.prob s) : X s = 0 := by
  have h := eq_zero_of_nonneg_of_expect_zero Ω (X := fun s => -X s) (fun s => by
    linarith [hX s]) (by rw [show (fun s => -X s) = fun s => (-1) * X s from by
      funext s; ring, expect_const_mul, hE]; ring) hp
  linarith

/-- Jensen's inequality for strictly concave utility, O&R (15), p. 365:
`E u(C) ≤ u(E C)` for positive consumption. -/
theorem jensen (U : Utility) {C : S → ℝ} (hC : ∀ s, 0 < C s) :
    Ω.expect (fun s => U.u (C s)) ≤ U.u (Ω.expect C) := by
  have hm : 0 < Ω.expect C := by
    have := nonempty Ω
    have h0 : Ω.expect (fun _ => (0 : ℝ)) ≤ Ω.expect C := expect_mono Ω fun s => (hC s).le
    rw [Ω.expect_const] at h0
    rcases eq_or_lt_of_le h0 with h | h
    · exfalso
      obtain ⟨s₀, hs₀⟩ : ∃ s, 0 < Ω.prob s := by
        by_contra hn
        push Not at hn
        have : ∑ s, Ω.prob s ≤ 0 := Finset.sum_nonpos fun s _ => hn s
        rw [Ω.prob_sum] at this
        linarith
      have := expect_strictMono Ω (X := fun _ => (0 : ℝ)) (fun s => (hC s).le) hs₀ (hC s₀)
      rw [Ω.expect_const] at this
      linarith
    · exact h
  have hle : Ω.expect (fun s => U.u (C s)) ≤
      Ω.expect (fun s => U.u (Ω.expect C) + U.du (Ω.expect C) * (C s - Ω.expect C)) :=
    expect_mono Ω fun s => U.supporting_line (hC s) hm
  have hrhs : Ω.expect (fun s => U.u (Ω.expect C) + U.du (Ω.expect C) * (C s - Ω.expect C))
      = U.u (Ω.expect C) := by
    rw [expect_const_add, expect_const_mul, expect_sub, Ω.expect_const]; ring
  linarith

/-- Strict Jensen, O&R (15), p. 365: if consumption differs from its mean in a state of
positive probability then `E u(C) < u(E C)`. -/
theorem jensen_strict (U : Utility) {C : S → ℝ} (hC : ∀ s, 0 < C s) {s₀ : S}
    (hp : 0 < Ω.prob s₀) (hne : C s₀ ≠ Ω.expect C) :
    Ω.expect (fun s => U.u (C s)) < U.u (Ω.expect C) := by
  have hm : 0 < Ω.expect C := by
    have h0 : Ω.expect (fun _ => (0 : ℝ)) < Ω.expect C :=
      expect_strictMono Ω (fun s => (hC s).le) hp (hC s₀)
    rwa [Ω.expect_const] at h0
  have hlt : Ω.expect (fun s => U.u (C s)) <
      Ω.expect (fun s => U.u (Ω.expect C) + U.du (Ω.expect C) * (C s - Ω.expect C)) :=
    expect_strictMono Ω (fun s => U.supporting_line (hC s) hm) hp
      (U.supporting_line_strict (hC s₀) hm hne)
  have hrhs : Ω.expect (fun s => U.u (Ω.expect C) + U.du (Ω.expect C) * (C s - Ω.expect C))
      = U.u (Ω.expect C) := by
    rw [expect_const_add, expect_const_mul, expect_sub, Ω.expect_const]; ring
  linarith

/-- Continuity of `c ↦ E[max(c, g)]` (used for the thresholds of O&R (7), p. 357, and
(64), p. 424). -/
theorem continuous_expect_max (g : S → ℝ) :
    Continuous fun c => Ω.expect (fun s => max c (g s)) := by
  unfold StateSpace.expect
  fun_prop

/-- **The clamp supergradient inequality** (O&R Appendix 6B, (59)–(62), pp. 423–424):
for `C* = min(hi, max(c̄, lo))` and any positive `C` with `lo ≤ C ≤ hi`,
`E u(C) ≤ E u(C*) + u'(c̄)(E C − E C*)`, strictly if `C ≠ C*` on a state of positive
probability. The multiplier on the resource constraint is `u'(c̄)`. -/
theorem clamp_supergradient (U : Utility) {lo hi C : S → ℝ} {cbar : ℝ} (hc : 0 < cbar)
    (hlo : ∀ s, 0 < lo s) (hlohi : ∀ s, lo s ≤ hi s)
    (hClo : ∀ s, lo s ≤ C s) (hChi : ∀ s, C s ≤ hi s) :
    Ω.expect (fun s => U.u (C s)) ≤
        Ω.expect (fun s => U.u (min (hi s) (max cbar (lo s)))) +
          U.du cbar * (Ω.expect C - Ω.expect (fun s => min (hi s) (max cbar (lo s)))) ∧
      ((∃ s, 0 < Ω.prob s ∧ C s ≠ min (hi s) (max cbar (lo s))) →
        Ω.expect (fun s => U.u (C s)) <
          Ω.expect (fun s => U.u (min (hi s) (max cbar (lo s)))) +
            U.du cbar * (Ω.expect C - Ω.expect (fun s => min (hi s) (max cbar (lo s))))) := by
  set Cs : S → ℝ := fun s => min (hi s) (max cbar (lo s)) with hCs
  have hCpos : ∀ s, 0 < C s := fun s => lt_of_lt_of_le (hlo s) (hClo s)
  have hCspos : ∀ s, 0 < Cs s := fun s =>
    lt_min (lt_of_lt_of_le (hlo s) (hlohi s)) (lt_of_lt_of_le hc (le_max_left _ _))
  -- pointwise: u'(C*)(C − C*) ≤ u'(c̄)(C − C*)
  have hkey : ∀ s, U.du (Cs s) * (C s - Cs s) ≤ U.du cbar * (C s - Cs s) := by
    intro s
    simp only [hCs]
    by_cases h1 : max cbar (lo s) ≤ hi s
    · rw [min_eq_right h1]
      by_cases h2 : lo s ≤ cbar
      · rw [max_eq_left h2]
      · push Not at h2
        rw [max_eq_right h2.le]
        have hd : U.du (lo s) ≤ U.du cbar := U.du_anti hc h2.le
        have : 0 ≤ C s - lo s := by linarith [hClo s]
        nlinarith
    · push Not at h1
      rw [min_eq_left h1.le]
      have hhc : hi s < cbar := by
        rcases le_total cbar (lo s) with h | h
        · rw [max_eq_right h] at h1; linarith [hlohi s]
        · rw [max_eq_left h] at h1; exact h1
      have hd : U.du cbar ≤ U.du (hi s) :=
        U.du_anti (lt_of_lt_of_le (hlo s) (hlohi s)) hhc.le
      have : C s - hi s ≤ 0 := by linarith [hChi s]
      nlinarith
  have hsl : ∀ s, U.u (C s) ≤ U.u (Cs s) + U.du cbar * (C s - Cs s) := fun s =>
    le_trans (U.supporting_line (hCpos s) (hCspos s)) (by linarith [hkey s])
  have hsum : Ω.expect (fun s => U.u (Cs s) + U.du cbar * (C s - Cs s)) =
      Ω.expect (fun s => U.u (Cs s)) + U.du cbar * (Ω.expect C - Ω.expect Cs) := by
    rw [Ω.expect_add, expect_const_mul, expect_sub]
  refine ⟨by rw [← hsum]; exact expect_mono Ω hsl, fun ⟨s, hp, hne⟩ => ?_⟩
  have hlt := expect_strictMono Ω hsl hp (lt_of_lt_of_le
    (U.supporting_line_strict (hCpos s) (hCspos s) hne) (by linarith [hkey s]))
  rw [hsum] at hlt
  exact hlt

/-- **The clamp lemma** (O&R §6.1.1.3, eqs. (4)–(9), pp. 356–358; Appendix 6B (65),
p. 424; Exercise 2, p. 426). Let `lo ≤ hi` be pointwise consumption bounds and
`C* = min(hi, max(c̄, lo))`. Every positive schedule `C` with `lo ≤ C ≤ hi` and
`E C ≤ E C*` has `E u(C) ≤ E u(C*)`, with equality only if `C = C*` on every state of
positive probability. The proof sums the supporting-line inequality at `C*`, using that
`u'` is antitone: this is the Kuhn–Tucker sufficiency argument with multiplier
`μ = u'(c̄)`. -/
theorem clamp_optimal (U : Utility) {lo hi C : S → ℝ} {cbar : ℝ} (hc : 0 < cbar)
    (hlo : ∀ s, 0 < lo s) (hlohi : ∀ s, lo s ≤ hi s)
    (hClo : ∀ s, lo s ≤ C s) (hChi : ∀ s, C s ≤ hi s)
    (hmean : Ω.expect C ≤ Ω.expect (fun s => min (hi s) (max cbar (lo s)))) :
    Ω.expect (fun s => U.u (C s)) ≤
        Ω.expect (fun s => U.u (min (hi s) (max cbar (lo s)))) ∧
      (Ω.expect (fun s => U.u (C s)) =
          Ω.expect (fun s => U.u (min (hi s) (max cbar (lo s)))) →
        ∀ s, 0 < Ω.prob s → C s = min (hi s) (max cbar (lo s))) := by
  set Cs : S → ℝ := fun s => min (hi s) (max cbar (lo s)) with hCs
  have hCpos : ∀ s, 0 < C s := fun s => lt_of_lt_of_le (hlo s) (hClo s)
  have hCspos : ∀ s, 0 < Cs s := fun s =>
    lt_min (lt_of_lt_of_le (hlo s) (hlohi s)) (lt_of_lt_of_le hc (le_max_left _ _))
  -- pointwise: u'(C*)(C − C*) ≤ u'(c̄)(C − C*)
  have hkey : ∀ s, U.du (Cs s) * (C s - Cs s) ≤ U.du cbar * (C s - Cs s) := by
    intro s
    simp only [hCs]
    by_cases h1 : max cbar (lo s) ≤ hi s
    · rw [min_eq_right h1]
      by_cases h2 : lo s ≤ cbar
      · rw [max_eq_left h2]
      · push Not at h2
        rw [max_eq_right h2.le]
        have hd : U.du (lo s) ≤ U.du cbar := U.du_anti hc h2.le
        have : 0 ≤ C s - lo s := by linarith [hClo s]
        nlinarith
    · push Not at h1
      rw [min_eq_left h1.le]
      have hhc : hi s < cbar := by
        rcases le_total cbar (lo s) with h | h
        · rw [max_eq_right h] at h1; linarith [hlohi s]
        · rw [max_eq_left h] at h1; exact h1
      have hd : U.du cbar ≤ U.du (hi s) :=
        U.du_anti (lt_of_lt_of_le (hlo s) (hlohi s)) hhc.le
      have : C s - hi s ≤ 0 := by linarith [hChi s]
      nlinarith
  have hsl : ∀ s, U.u (C s) ≤ U.u (Cs s) + U.du cbar * (C s - Cs s) := fun s =>
    le_trans (U.supporting_line (hCpos s) (hCspos s)) (by linarith [hkey s])
  have hsum : Ω.expect (fun s => U.u (Cs s) + U.du cbar * (C s - Cs s)) =
      Ω.expect (fun s => U.u (Cs s)) + U.du cbar * (Ω.expect C - Ω.expect Cs) := by
    rw [Ω.expect_add, expect_const_mul, expect_sub]
  have hdpos := U.du_pos cbar hc
  have hmain : Ω.expect (fun s => U.u (C s)) ≤
      Ω.expect (fun s => U.u (Cs s)) + U.du cbar * (Ω.expect C - Ω.expect Cs) := by
    rw [← hsum]; exact expect_mono Ω hsl
  have hneg : U.du cbar * (Ω.expect C - Ω.expect Cs) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hdpos.le (by linarith)
  refine ⟨by linarith, fun heq s hp => ?_⟩
  by_contra hne
  have hlt := expect_strictMono Ω hsl hp (lt_of_lt_of_le
    (U.supporting_line_strict (hCpos s) (hCspos s) hne) (by linarith [hkey s]))
  rw [hsum] at hlt
  linarith

/-- Intermediate values for a continuous function on an interval (the existence step for
the thresholds `e` of O&R (7), p. 357, and (64), p. 424). -/
theorem exists_eq_of_continuous {f : ℝ → ℝ} (hf : Continuous f) {a b T : ℝ} (hab : a ≤ b)
    (ha : f a ≤ T) (hb : T ≤ f b) : ∃ c ∈ Icc a b, f c = T :=
  intermediate_value_Icc hab hf.continuousOn ⟨ha, hb⟩

end StateSpaceFacts

/-- The small country's stochastic endowment (O&R §6.1.1.1, p. 354): output
`Y(s) = Ȳ + ε(s)` with a mean-zero shock `ε`, every state of positive probability and
output positive in every state (`Ȳ + ε_1 > 0`). -/
structure Endowment (S : Type) [Fintype S] where
  Ω : StateSpace S
  ε : S → ℝ
  Ybar : ℝ
  prob_pos : ∀ s, 0 < Ω.prob s
  mean_zero : Ω.expect ε = 0
  output_pos : ∀ s, 0 < Ybar + ε s

namespace Endowment

variable {S : Type} [Fintype S] (E : Endowment S)

/-- Output in state `s`, `Y(s) = Ȳ + ε(s)` (O&R p. 354). -/
def Y (s : S) : ℝ := E.Ybar + E.ε s

/-- Expected output is `Ȳ`, O&R p. 355: `Σ π(ε_i) Y_2 = Ȳ`. -/
theorem expect_Y : E.Ω.expect E.Y = E.Ybar := by
  unfold Y
  rw [StateSpaceFacts.expect_const_add, E.mean_zero, add_zero]

/-- Output is positive in every state (O&R p. 354). -/
theorem Y_pos (s : S) : 0 < E.Y s := E.output_pos s

/-- Mean output is positive (O&R p. 354). -/
theorem Ybar_pos : 0 < E.Ybar := by
  have h := StateSpaceFacts.expect_mono E.Ω (X := fun _ => (0 : ℝ)) (fun s => (E.Y_pos s).le)
  rw [E.Ω.expect_const, expect_Y] at h
  rcases eq_or_lt_of_le h with h0 | h0
  · exfalso
    have := StateSpaceFacts.nonempty E.Ω
    obtain ⟨s⟩ := this
    have hlt := StateSpaceFacts.expect_strictMono E.Ω (X := fun _ => (0 : ℝ))
      (fun s => (E.Y_pos s).le) (E.prob_pos s) (E.Y_pos s)
    rw [E.Ω.expect_const, expect_Y] at hlt
    linarith
  · exact h0

end Endowment

namespace Geometric

/-- The present value of a constant flow from next period on,
`Σ_{s ≥ 1} β^s x = β x/(1 − β)` (O&R (15), p. 365). -/
theorem hasSum_geometric_from_one {β : ℝ} (h0 : 0 ≤ β) (h1 : β < 1) (x : ℝ) :
    HasSum (fun n : ℕ => β ^ (n + 1) * x) (β / (1 - β) * x) := by
  have h := (hasSum_geometric_of_lt_one h0 h1).mul_right (β * x)
  have e : (fun n : ℕ => β ^ n * (β * x)) = fun n : ℕ => β ^ (n + 1) * x := by
    funext n; ring
  rw [e] at h
  convert h using 1
  field_simp [show (1 : ℝ) - β ≠ 0 by linarith]

/-- The present value of a constant flow from today on, `Σ_{s ≥ 0} β^s x = x/(1 − β)`
(O&R (11), p. 364). -/
theorem hasSum_geometric_const {β : ℝ} (h0 : 0 ≤ β) (h1 : β < 1) (x : ℝ) :
    HasSum (fun n : ℕ => β ^ n * x) (x / (1 - β)) := by
  have h := (hasSum_geometric_of_lt_one h0 h1).mul_right x
  convert h using 1
  field_simp [show (1 : ℝ) - β ≠ 0 by linarith]

/-- A discounted sequence with bounded terms is summable (O&R (11), p. 364: lifetime
utility is finite when period utility is bounded). -/
theorem summable_of_bounded {β : ℝ} (h0 : 0 ≤ β) (h1 : β < 1) {x : ℕ → ℝ} {M : ℝ}
    (hx : ∀ n, |x n| ≤ M) : Summable fun n => β ^ n * x n := by
  refine Summable.of_norm_bounded (g := fun n => β ^ n * M)
    ((summable_geometric_of_lt_one h0 h1).mul_right M) fun n => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg h0 n)]
  exact mul_le_mul_of_nonneg_left (hx n) (pow_nonneg h0 n)

end Geometric

end ObstfeldRogoff.CapitalMarketImperfections.SovereignRiskPrimitives
