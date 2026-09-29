/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# International monetary policy coordination: Nash versus the planner

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §9.5.5,
pp. 654–657, including the exercise of footnote 42 ("solve for the levels of monetary
growth in both the Nash and planner solutions").

Home and Foreign output gaps are
`y − ȳ = a₁ (Δm − E_{t−1}Δm) + a₂ (Δm* − E_{t−1}Δm*) + ε` and
`y* − ȳ = a₁ (Δm* − E_{t−1}Δm*) + a₂ (Δm − E_{t−1}Δm) + ε*`,
and the losses are `L = (y − ȳ)² + χ (Δm)²`, `L* = (y* − ȳ)² + χ (Δm*)²`, with `χ > 0`.

**Stochastic structure.** The shocks `(ε, ε*)` live on a finite state space with mean zero
(`E_{t−1} ε = E_{t−1} ε* = 0`). Policies are state-contingent money growth rates
`Δm, Δm* : S → ℝ`, chosen after the shock, taking the expectations `E_{t−1}Δm`,
`E_{t−1}Δm*` (formed before the shock) as given; rational expectations require these to
equal the means of the chosen policies (a one-shot-game equilibrium, as in the book).

Main results.
* First-order conditions are necessary and sufficient, both for each country's best
  response and for the planner (the objectives are strictly convex quadratics).
* Expected money growth is zero in both the Nash and the planner solution (no inflation bias
  without a wedge, footnote 42).
* The Nash equilibrium is unique iff `(a₁² + χ)² ≠ a₁² a₂²`, with a closed form; when the
  determinant vanishes equilibria are not unique. The planner's solution always exists, is
  unique, and has a closed form (its determinant is positive).
* With symmetric shocks and weights, Nash responds with coefficient `a₁/(a₁² + a₁a₂ + χ)` and
  the planner with `(a₁ + a₂)/((a₁ + a₂)² + χ)`; the planner responds more strongly iff
  `a₂ > 0` (the difference is exactly `χ a₂` over positive denominators).
* The planner's expected weighted loss never exceeds Nash's, strictly if `a₂ ≠ 0` and a
  shock hits with positive probability.
* With `χ = 0`, both outputs can be stabilised exactly iff `a₁² ≠ a₂²`, and then Nash
  already does so ("two instruments, two targets").
-/

namespace ObstfeldRogoff.NominalRigidities.PolicyCoordination

open Finset

/-- O&R §9.5.5, p. 654: the spillover coefficients `a₁` (own money surprise) and `a₂`
(foreign money surprise) and the weight `χ > 0` on money growth in the loss. -/
structure CoordParams where
  a1 : ℝ
  a2 : ℝ
  χ : ℝ
  χ_pos : 0 < χ

/-- O&R §9.5.5, p. 655: Home and Foreign shocks on a finite state space, with mean zero. -/
structure CoordShocks (S : Type) [Fintype S] where
  prob : S → ℝ
  eps : S → ℝ
  epsF : S → ℝ
  prob_nonneg : ∀ s, 0 ≤ prob s
  prob_sum : ∑ s, prob s = 1
  eps_mean : ∑ s, prob s * eps s = 0
  epsF_mean : ∑ s, prob s * epsF s = 0

variable {S : Type} [Fintype S]

/-- The expectation of a state-contingent variable (O&R §9.5.5). -/
def expect (Sh : CoordShocks S) (f : S → ℝ) : ℝ := ∑ s, Sh.prob s * f s

/-- O&R §9.5.5, p. 654: the Home output gap given expectations `Em, EmF`, money growth
`M, MF` and the Home shock `e`. -/
def homeGap (P : CoordParams) (Em EmF M MF e : ℝ) : ℝ :=
  P.a1 * (M - Em) + P.a2 * (MF - EmF) + e

/-- O&R §9.5.5, p. 655: the Foreign output gap. -/
def foreignGap (P : CoordParams) (Em EmF M MF eF : ℝ) : ℝ :=
  P.a1 * (MF - EmF) + P.a2 * (M - Em) + eF

/-- O&R §9.5.5, p. 655: the Home loss `(y − ȳ)² + χ (Δm)²`. -/
def homeLoss (P : CoordParams) (Em EmF M MF e : ℝ) : ℝ :=
  homeGap P Em EmF M MF e ^ 2 + P.χ * M ^ 2

/-- O&R §9.5.5, p. 655: the Foreign loss `(y* − ȳ)² + χ (Δm*)²`. -/
def foreignLoss (P : CoordParams) (Em EmF M MF eF : ℝ) : ℝ :=
  foreignGap P Em EmF M MF eF ^ 2 + P.χ * MF ^ 2

/-- O&R §9.5.5, p. 656: the planner's objective `x L + (1 − x) L*` (weight `w`). -/
def welfare (P : CoordParams) (w Em EmF M MF e eF : ℝ) : ℝ :=
  w * homeLoss P Em EmF M MF e + (1 - w) * foreignLoss P Em EmF M MF eF

/-- O&R §9.5.5, p. 655: a (one-shot-game) Nash equilibrium in state-contingent money
growth: in every state each country's choice is a best response to the other's, given
rational expectations `E_{t−1}Δm = E M`, `E_{t−1}Δm* = E MF`. -/
def IsNash (P : CoordParams) (Sh : CoordShocks S) (M MF : S → ℝ) : Prop :=
  ∀ s, (∀ x, homeLoss P (expect Sh M) (expect Sh MF) (M s) (MF s) (Sh.eps s) ≤
      homeLoss P (expect Sh M) (expect Sh MF) x (MF s) (Sh.eps s)) ∧
    (∀ x, foreignLoss P (expect Sh M) (expect Sh MF) (M s) (MF s) (Sh.epsF s) ≤
      foreignLoss P (expect Sh M) (expect Sh MF) (M s) x (Sh.epsF s))

/-- O&R §9.5.5, p. 656: the planner's solution with weight `w`: in every state the pair
`(M s, MF s)` minimises `w L + (1 − w) L*`, given rational expectations. -/
def IsPlanner (P : CoordParams) (Sh : CoordShocks S) (w : ℝ) (M MF : S → ℝ) : Prop :=
  ∀ s x xF, welfare P w (expect Sh M) (expect Sh MF) (M s) (MF s) (Sh.eps s) (Sh.epsF s) ≤
    welfare P w (expect Sh M) (expect Sh MF) x xF (Sh.eps s) (Sh.epsF s)

/-! ### Expectation algebra -/

/-- The expectation of an affine combination (O&R §9.5.5 background). -/
theorem expect_affine (Sh : CoordShocks S) (f g k l : S → ℝ) (c1 c2 c3 c4 c5 : ℝ) :
    ∑ s, Sh.prob s * (c1 * f s + c2 * g s + c3 * k s + c4 * l s + c5) =
      c1 * expect Sh f + c2 * expect Sh g + c3 * expect Sh k + c4 * expect Sh l + c5 := by
  unfold expect
  have h : ∀ s, Sh.prob s * (c1 * f s + c2 * g s + c3 * k s + c4 * l s + c5) =
      c1 * (Sh.prob s * f s) + c2 * (Sh.prob s * g s) + c3 * (Sh.prob s * k s) +
        c4 * (Sh.prob s * l s) + c5 * Sh.prob s := fun s => by ring
  rw [Finset.sum_congr rfl fun s _ => h s]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Sh.prob_sum, mul_one]

/-! ### Best responses -/

/-- O&R p. 655: the exact expansion of the Home loss around `x₀`. -/
theorem homeLoss_sub (P : CoordParams) (Em EmF MF e x0 x : ℝ) :
    homeLoss P Em EmF x MF e - homeLoss P Em EmF x0 MF e =
      2 * (x - x0) * (P.a1 * homeGap P Em EmF x0 MF e + P.χ * x0) +
        (P.a1 ^ 2 + P.χ) * (x - x0) ^ 2 := by
  unfold homeLoss homeGap
  ring

/-- O&R p. 655: the exact expansion of the Foreign loss around `x₀`. -/
theorem foreignLoss_sub (P : CoordParams) (Em EmF M eF x0 x : ℝ) :
    foreignLoss P Em EmF M x eF - foreignLoss P Em EmF M x0 eF =
      2 * (x - x0) * (P.a1 * foreignGap P Em EmF M x0 eF + P.χ * x0) +
        (P.a1 ^ 2 + P.χ) * (x - x0) ^ 2 := by
  unfold foreignLoss foreignGap
  ring

/-- O&R p. 655: Home's first-order condition `a₁ (y − ȳ) + χ Δm = 0` is necessary and
sufficient for a best response. -/
theorem home_best_response_iff (P : CoordParams) (Em EmF MF e x0 : ℝ) :
    (∀ x, homeLoss P Em EmF x0 MF e ≤ homeLoss P Em EmF x MF e) ↔
      P.a1 * homeGap P Em EmF x0 MF e + P.χ * x0 = 0 := by
  have hK : 0 < P.a1 ^ 2 + P.χ := by have := P.χ_pos; positivity
  constructor
  · intro h
    by_contra hF
    set F := P.a1 * homeGap P Em EmF x0 MF e + P.χ * x0
    have h1 := homeLoss_sub P Em EmF MF e x0 (x0 - F / (P.a1 ^ 2 + P.χ))
    have h2 := h (x0 - F / (P.a1 ^ 2 + P.χ))
    have h3 : 2 * (x0 - F / (P.a1 ^ 2 + P.χ) - x0) * F +
        (P.a1 ^ 2 + P.χ) * (x0 - F / (P.a1 ^ 2 + P.χ) - x0) ^ 2 =
          -(F ^ 2 / (P.a1 ^ 2 + P.χ)) := by
      field_simp
      ring
    have h4 : 0 < F ^ 2 / (P.a1 ^ 2 + P.χ) := by positivity
    linarith
  · intro hF x
    have h1 := homeLoss_sub P Em EmF MF e x0 x
    rw [hF, mul_zero, zero_add] at h1
    nlinarith [sq_nonneg (x - x0)]

/-- O&R p. 655: Foreign's first-order condition is necessary and sufficient. -/
theorem foreign_best_response_iff (P : CoordParams) (Em EmF M eF x0 : ℝ) :
    (∀ x, foreignLoss P Em EmF M x0 eF ≤ foreignLoss P Em EmF M x eF) ↔
      P.a1 * foreignGap P Em EmF M x0 eF + P.χ * x0 = 0 := by
  have hK : 0 < P.a1 ^ 2 + P.χ := by have := P.χ_pos; positivity
  constructor
  · intro h
    by_contra hF
    set F := P.a1 * foreignGap P Em EmF M x0 eF + P.χ * x0
    have h1 := foreignLoss_sub P Em EmF M eF x0 (x0 - F / (P.a1 ^ 2 + P.χ))
    have h2 := h (x0 - F / (P.a1 ^ 2 + P.χ))
    have h3 : 2 * (x0 - F / (P.a1 ^ 2 + P.χ) - x0) * F +
        (P.a1 ^ 2 + P.χ) * (x0 - F / (P.a1 ^ 2 + P.χ) - x0) ^ 2 =
          -(F ^ 2 / (P.a1 ^ 2 + P.χ)) := by
      field_simp
      ring
    have h4 : 0 < F ^ 2 / (P.a1 ^ 2 + P.χ) := by positivity
    linarith
  · intro hF x
    have h1 := foreignLoss_sub P Em EmF M eF x0 x
    rw [hF, mul_zero, zero_add] at h1
    nlinarith [sq_nonneg (x - x0)]

/-- O&R p. 655: a Nash equilibrium is exactly a profile satisfying both first-order
conditions in every state. -/
theorem nash_iff_foc (P : CoordParams) (Sh : CoordShocks S) (M MF : S → ℝ) :
    IsNash P Sh M MF ↔ ∀ s,
      P.a1 * homeGap P (expect Sh M) (expect Sh MF) (M s) (MF s) (Sh.eps s) + P.χ * M s = 0 ∧
      P.a1 * foreignGap P (expect Sh M) (expect Sh MF) (M s) (MF s) (Sh.epsF s) +
        P.χ * MF s = 0 := by
  unfold IsNash
  simp only [home_best_response_iff, foreign_best_response_iff]

/-- O&R fn 42: in any Nash equilibrium expected money growth is zero in both countries. -/
theorem nash_expect_zero {P : CoordParams} {Sh : CoordShocks S} {M MF : S → ℝ}
    (hN : IsNash P Sh M MF) : expect Sh M = 0 ∧ expect Sh MF = 0 := by
  rw [nash_iff_foc] at hN
  have hχ := P.χ_pos.ne'
  have h1 : ∑ s, Sh.prob s * ((P.a1 ^ 2 + P.χ) * M s + (P.a1 * P.a2) * MF s +
      P.a1 * Sh.eps s + 0 * Sh.epsF s +
        (-(P.a1 * (P.a1 * expect Sh M + P.a2 * expect Sh MF)))) = 0 := by
    refine Finset.sum_eq_zero fun s _ => ?_
    have := (hN s).1
    unfold homeGap at this
    rw [show (P.a1 ^ 2 + P.χ) * M s + (P.a1 * P.a2) * MF s + P.a1 * Sh.eps s + 0 * Sh.epsF s +
      -(P.a1 * (P.a1 * expect Sh M + P.a2 * expect Sh MF)) = 0 by linear_combination this,
      mul_zero]
  have h2 : ∑ s, Sh.prob s * ((P.a1 * P.a2) * M s + (P.a1 ^ 2 + P.χ) * MF s +
      0 * Sh.eps s + P.a1 * Sh.epsF s +
        (-(P.a1 * (P.a1 * expect Sh MF + P.a2 * expect Sh M)))) = 0 := by
    refine Finset.sum_eq_zero fun s _ => ?_
    have := (hN s).2
    unfold foreignGap at this
    rw [show (P.a1 * P.a2) * M s + (P.a1 ^ 2 + P.χ) * MF s + 0 * Sh.eps s + P.a1 * Sh.epsF s +
      -(P.a1 * (P.a1 * expect Sh MF + P.a2 * expect Sh M)) = 0 by linear_combination this,
      mul_zero]
  rw [expect_affine] at h1 h2
  have he : expect Sh Sh.eps = 0 := Sh.eps_mean
  have heF : expect Sh Sh.epsF = 0 := Sh.epsF_mean
  rw [he, heF] at h1 h2
  constructor
  · have : P.χ * expect Sh M = 0 := by linear_combination h1
    exact (mul_eq_zero.mp this).resolve_left hχ
  · have : P.χ * expect Sh MF = 0 := by linear_combination h2
    exact (mul_eq_zero.mp this).resolve_left hχ

/-- O&R p. 655 and fn 42: Nash equilibria are exactly the zero-mean solutions of the linear
system `(a₁² + χ) Δm + a₁a₂ Δm* = −a₁ ε`, `a₁a₂ Δm + (a₁² + χ) Δm* = −a₁ ε*`. -/
theorem nash_iff_system (P : CoordParams) (Sh : CoordShocks S) (M MF : S → ℝ) :
    IsNash P Sh M MF ↔ expect Sh M = 0 ∧ expect Sh MF = 0 ∧ ∀ s,
      (P.a1 ^ 2 + P.χ) * M s + P.a1 * P.a2 * MF s = -(P.a1 * Sh.eps s) ∧
      P.a1 * P.a2 * M s + (P.a1 ^ 2 + P.χ) * MF s = -(P.a1 * Sh.epsF s) := by
  constructor
  · intro hN
    obtain ⟨h0, h0F⟩ := nash_expect_zero hN
    rw [nash_iff_foc] at hN
    refine ⟨h0, h0F, fun s => ?_⟩
    have h1 := (hN s).1
    have h2 := (hN s).2
    unfold homeGap at h1
    unfold foreignGap at h2
    rw [h0, h0F] at h1 h2
    constructor
    · linear_combination h1
    · linear_combination h2
  · rintro ⟨h0, h0F, hs⟩
    rw [nash_iff_foc]
    intro s
    unfold homeGap foreignGap
    rw [h0, h0F]
    constructor
    · linear_combination (hs s).1
    · linear_combination (hs s).2

/-- O&R fn 42: the Nash determinant `(a₁² + χ)² − a₁² a₂²`. -/
def nashDet (P : CoordParams) : ℝ := (P.a1 ^ 2 + P.χ) ^ 2 - (P.a1 * P.a2) ^ 2

/-- O&R fn 42: Home's Nash money growth `−a₁ ((a₁² + χ) ε − a₁a₂ ε*)/det`. -/
noncomputable def nashM (P : CoordParams) (Sh : CoordShocks S) (s : S) : ℝ :=
  -(P.a1 * ((P.a1 ^ 2 + P.χ) * Sh.eps s - P.a1 * P.a2 * Sh.epsF s)) / nashDet P

/-- O&R fn 42: Foreign's Nash money growth `−a₁ ((a₁² + χ) ε* − a₁a₂ ε)/det`. -/
noncomputable def nashMF (P : CoordParams) (Sh : CoordShocks S) (s : S) : ℝ :=
  -(P.a1 * ((P.a1 ^ 2 + P.χ) * Sh.epsF s - P.a1 * P.a2 * Sh.eps s)) / nashDet P

/-- O&R fn 42: the closed form has zero mean. -/
theorem expect_nashM (P : CoordParams) (Sh : CoordShocks S) :
    expect Sh (nashM P Sh) = 0 ∧ expect Sh (nashMF P Sh) = 0 := by
  have he : expect Sh Sh.eps = 0 := Sh.eps_mean
  have heF : expect Sh Sh.epsF = 0 := Sh.epsF_mean
  set c1 := -(P.a1 * (P.a1 ^ 2 + P.χ)) / nashDet P
  set c2 := P.a1 * (P.a1 * P.a2) / nashDet P
  constructor
  · have hs : ∀ s, Sh.prob s * nashM P Sh s = Sh.prob s *
        (c1 * Sh.eps s + c2 * Sh.epsF s + 0 * Sh.eps s + 0 * Sh.eps s + 0) := fun s => by
      unfold nashM
      ring
    unfold expect
    rw [Finset.sum_congr rfl fun s _ => hs s, expect_affine, he, heF]
    ring
  · have hs : ∀ s, Sh.prob s * nashMF P Sh s = Sh.prob s *
        (c1 * Sh.epsF s + c2 * Sh.eps s + 0 * Sh.eps s + 0 * Sh.eps s + 0) := fun s => by
      unfold nashMF
      ring
    unfold expect
    rw [Finset.sum_congr rfl fun s _ => hs s, expect_affine, he, heF]
    ring

/-- O&R fn 42, Nash existence, uniqueness and closed form: when `(a₁² + χ)² ≠ a₁² a₂²` a
profile is a Nash equilibrium iff it equals `(nashM, nashMF)` in every state. -/
theorem nash_iff_closed_form {P : CoordParams} {Sh : CoordShocks S} (hdet : nashDet P ≠ 0)
    (M MF : S → ℝ) :
    IsNash P Sh M MF ↔ ∀ s, M s = nashM P Sh s ∧ MF s = nashMF P Sh s := by
  rw [nash_iff_system]
  constructor
  · rintro ⟨_, _, hs⟩ s
    obtain ⟨h1, h2⟩ := hs s
    unfold nashM nashMF
    unfold nashDet at hdet ⊢
    constructor
    · rw [eq_div_iff hdet]
      linear_combination (P.a1 ^ 2 + P.χ) * h1 - P.a1 * P.a2 * h2
    · rw [eq_div_iff hdet]
      linear_combination (P.a1 ^ 2 + P.χ) * h2 - P.a1 * P.a2 * h1
  · intro hs
    have hM : M = nashM P Sh := funext fun s => (hs s).1
    have hMF : MF = nashMF P Sh := funext fun s => (hs s).2
    subst hM hMF
    refine ⟨(expect_nashM P Sh).1, (expect_nashM P Sh).2, fun s => ?_⟩
    unfold nashM nashMF nashDet
    unfold nashDet at hdet
    constructor
    · rw [mul_div_assoc', mul_div_assoc', ← add_div, div_eq_iff hdet]
      ring
    · rw [mul_div_assoc', mul_div_assoc', ← add_div, div_eq_iff hdet]
      ring

/-- O&R fn 42: the closed form is a Nash equilibrium (existence) when the determinant is
nonzero. -/
theorem nash_exists {P : CoordParams} (Sh : CoordShocks S) (hdet : nashDet P ≠ 0) :
    IsNash P Sh (nashM P Sh) (nashMF P Sh) :=
  (nash_iff_closed_form hdet _ _).mpr fun _ => ⟨rfl, rfl⟩

/-- O&R p. 655, the determinant condition is sharp: if `(a₁² + χ)² = a₁² a₂²` then adding
any zero-mean `g` along the kernel direction `(1, c)`, `c = ±1`, to a Nash equilibrium gives
another Nash equilibrium, so uniqueness fails as soon as a nonzero zero-mean `g` exists. -/
theorem nash_nonunique_of_det_zero {P : CoordParams} {Sh : CoordShocks S}
    (hdet : nashDet P = 0) {M MF : S → ℝ} (hN : IsNash P Sh M MF) {g : S → ℝ}
    (hg : expect Sh g = 0) :
    ∃ c : ℝ, (c = 1 ∨ c = -1) ∧ IsNash P Sh (fun s => M s + g s) (fun s => MF s + c * g s) := by
  rw [nash_iff_system] at hN
  obtain ⟨h0, h0F, hs⟩ := hN
  have hfac : (P.a1 ^ 2 + P.χ - P.a1 * P.a2) * (P.a1 ^ 2 + P.χ + P.a1 * P.a2) = 0 := by
    unfold nashDet at hdet
    linear_combination hdet
  have hEg : ∀ c : ℝ, expect Sh (fun s => MF s + c * g s) = 0 ∧
      expect Sh (fun s => M s + g s) = 0 := by
    intro c
    unfold expect at h0 h0F hg ⊢
    constructor
    · change ∑ s, Sh.prob s * (MF s + c * g s) = 0
      have : ∑ s, Sh.prob s * (MF s + c * g s) =
          ∑ s, Sh.prob s * MF s + c * ∑ s, Sh.prob s * g s := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun s _ => by ring
      rw [this, h0F, hg]
      ring
    · change ∑ s, Sh.prob s * (M s + g s) = 0
      have : ∑ s, Sh.prob s * (M s + g s) = ∑ s, Sh.prob s * M s + ∑ s, Sh.prob s * g s := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun s _ => by ring
      rw [this, h0, hg]
      ring
  rcases mul_eq_zero.mp hfac with hk | hk
  · refine ⟨-1, Or.inr rfl, ?_⟩
    rw [nash_iff_system]
    refine ⟨(hEg (-1)).2, (hEg (-1)).1, fun s => ⟨?_, ?_⟩⟩
    · linear_combination (hs s).1 + g s * hk
    · linear_combination (hs s).2 - g s * hk
  · refine ⟨1, Or.inl rfl, ?_⟩
    rw [nash_iff_system]
    refine ⟨(hEg 1).2, (hEg 1).1, fun s => ⟨?_, ?_⟩⟩
    · linear_combination (hs s).1 + g s * hk
    · linear_combination (hs s).2 + g s * hk

/-! ### The planner -/

/-- O&R p. 656: the planner's first-order condition with respect to `Δm` (divided by 2). -/
def plannerFOC1 (P : CoordParams) (w Em EmF M MF e eF : ℝ) : ℝ :=
  w * (P.a1 * homeGap P Em EmF M MF e + P.χ * M) + (1 - w) * P.a2 * foreignGap P Em EmF M MF eF

/-- O&R p. 656: the planner's first-order condition with respect to `Δm*` (divided by 2). -/
def plannerFOC2 (P : CoordParams) (w Em EmF M MF e eF : ℝ) : ℝ :=
  w * P.a2 * homeGap P Em EmF M MF e + (1 - w) * (P.a1 * foreignGap P Em EmF M MF eF + P.χ * MF)

/-- O&R p. 656: the quadratic part of the planner's objective. -/
def plannerQ (P : CoordParams) (w d dF : ℝ) : ℝ :=
  w * ((P.a1 * d + P.a2 * dF) ^ 2 + P.χ * d ^ 2) +
    (1 - w) * ((P.a2 * d + P.a1 * dF) ^ 2 + P.χ * dF ^ 2)

/-- O&R p. 656: the exact expansion of the planner's objective around `(M, MF)`. -/
theorem welfare_sub (P : CoordParams) (w Em EmF M MF e eF x xF : ℝ) :
    welfare P w Em EmF x xF e eF - welfare P w Em EmF M MF e eF =
      2 * ((x - M) * plannerFOC1 P w Em EmF M MF e eF +
        (xF - MF) * plannerFOC2 P w Em EmF M MF e eF) + plannerQ P w (x - M) (xF - MF) := by
  unfold welfare homeLoss foreignLoss plannerFOC1 plannerFOC2 plannerQ homeGap foreignGap
  ring

/-- O&R p. 656: for `0 < w < 1` the quadratic part is positive definite. -/
theorem plannerQ_pos (P : CoordParams) {w : ℝ} (hw0 : 0 < w) (hw1 : w < 1) {d dF : ℝ}
    (hd : d ≠ 0 ∨ dF ≠ 0) : 0 < plannerQ P w d dF := by
  have hχ := P.χ_pos
  have h1w : 0 < 1 - w := by linarith
  unfold plannerQ
  have h1 : 0 ≤ w * (P.a1 * d + P.a2 * dF) ^ 2 := by positivity
  have h2 : 0 ≤ (1 - w) * (P.a2 * d + P.a1 * dF) ^ 2 := by positivity
  rcases hd with hd | hd
  · have : 0 < w * (P.χ * d ^ 2) := by positivity
    have : 0 ≤ (1 - w) * (P.χ * dF ^ 2) := by positivity
    nlinarith
  · have : 0 ≤ w * (P.χ * d ^ 2) := by positivity
    have : 0 < (1 - w) * (P.χ * dF ^ 2) := by positivity
    nlinarith

/-- O&R p. 656: the planner's first-order conditions are necessary and sufficient for a
state-by-state optimum (for `0 < w < 1`). -/
theorem planner_state_iff (P : CoordParams) {w : ℝ} (hw0 : 0 < w) (hw1 : w < 1)
    (Em EmF M MF e eF : ℝ) :
    (∀ x xF, welfare P w Em EmF M MF e eF ≤ welfare P w Em EmF x xF e eF) ↔
      plannerFOC1 P w Em EmF M MF e eF = 0 ∧ plannerFOC2 P w Em EmF M MF e eF = 0 := by
  constructor
  · intro h
    by_contra hF
    set F1 := plannerFOC1 P w Em EmF M MF e eF
    set F2 := plannerFOC2 P w Em EmF M MF e eF
    have hne : F1 ≠ 0 ∨ F2 ≠ 0 := by
      by_contra h'
      push Not at h'
      exact hF h'
    have hq := plannerQ_pos P hw0 hw1 hne
    have hS : 0 < F1 ^ 2 + F2 ^ 2 := by
      rcases hne with h' | h'
      · have := pow_pos (abs_pos.mpr h') 2
        rw [sq_abs] at this
        nlinarith [sq_nonneg F2]
      · have := pow_pos (abs_pos.mpr h') 2
        rw [sq_abs] at this
        nlinarith [sq_nonneg F1]
    set τ := (F1 ^ 2 + F2 ^ 2) / plannerQ P w F1 F2
    have h1 := welfare_sub P w Em EmF M MF e eF (M - τ * F1) (MF - τ * F2)
    have h2 := h (M - τ * F1) (MF - τ * F2)
    have hQτ : plannerQ P w (M - τ * F1 - M) (MF - τ * F2 - MF) =
        τ ^ 2 * plannerQ P w F1 F2 := by
      unfold plannerQ
      ring
    rw [hQτ] at h1
    have h3 : 2 * ((M - τ * F1 - M) * F1 + (MF - τ * F2 - MF) * F2) +
        τ ^ 2 * plannerQ P w F1 F2 = -((F1 ^ 2 + F2 ^ 2) ^ 2 / plannerQ P w F1 F2) := by
      simp only [τ]
      field_simp
      ring
    have h4 : 0 < (F1 ^ 2 + F2 ^ 2) ^ 2 / plannerQ P w F1 F2 := by positivity
    linarith
  · rintro ⟨h1, h2⟩ x xF
    have h := welfare_sub P w Em EmF M MF e eF x xF
    rw [h1, h2] at h
    have hq : 0 ≤ plannerQ P w (x - M) (xF - MF) := by
      by_cases hd : x - M ≠ 0 ∨ xF - MF ≠ 0
      · exact (plannerQ_pos P hw0 hw1 hd).le
      · push Not at hd
        rw [hd.1, hd.2]
        unfold plannerQ
        simp
    linarith

/-- O&R p. 656: the planner's solution is exactly a profile satisfying both first-order
conditions in every state. -/
theorem planner_iff_foc (P : CoordParams) (Sh : CoordShocks S) {w : ℝ} (hw0 : 0 < w)
    (hw1 : w < 1) (M MF : S → ℝ) :
    IsPlanner P Sh w M MF ↔ ∀ s,
      plannerFOC1 P w (expect Sh M) (expect Sh MF) (M s) (MF s) (Sh.eps s) (Sh.epsF s) = 0 ∧
      plannerFOC2 P w (expect Sh M) (expect Sh MF) (M s) (MF s) (Sh.eps s) (Sh.epsF s) = 0 := by
  unfold IsPlanner
  exact forall_congr' fun s => planner_state_iff P hw0 hw1 _ _ _ _ _ _

/-- O&R fn 42: in the planner's solution expected money growth is zero in both countries. -/
theorem planner_expect_zero {P : CoordParams} {Sh : CoordShocks S} {w : ℝ} (hw0 : 0 < w)
    (hw1 : w < 1) {M MF : S → ℝ} (hP : IsPlanner P Sh w M MF) :
    expect Sh M = 0 ∧ expect Sh MF = 0 := by
  rw [planner_iff_foc P Sh hw0 hw1] at hP
  have hχ := P.χ_pos
  set Em := expect Sh M
  set EmF := expect Sh MF
  have h1 : ∑ s, Sh.prob s * ((w * (P.a1 ^ 2 + P.χ) + (1 - w) * P.a2 ^ 2) * M s +
      (P.a1 * P.a2) * MF s + (w * P.a1) * Sh.eps s + ((1 - w) * P.a2) * Sh.epsF s +
        (-(w * P.a1 * (P.a1 * Em + P.a2 * EmF) + (1 - w) * P.a2 * (P.a1 * EmF + P.a2 * Em)))) =
      0 := by
    refine Finset.sum_eq_zero fun s _ => ?_
    have := (hP s).1
    unfold plannerFOC1 homeGap foreignGap at this
    rw [show (w * (P.a1 ^ 2 + P.χ) + (1 - w) * P.a2 ^ 2) * M s + (P.a1 * P.a2) * MF s +
      (w * P.a1) * Sh.eps s + ((1 - w) * P.a2) * Sh.epsF s +
      (-(w * P.a1 * (P.a1 * Em + P.a2 * EmF) + (1 - w) * P.a2 * (P.a1 * EmF + P.a2 * Em))) = 0
      by linear_combination this, mul_zero]
  have h2 : ∑ s, Sh.prob s * ((P.a1 * P.a2) * M s +
      (w * P.a2 ^ 2 + (1 - w) * (P.a1 ^ 2 + P.χ)) * MF s + (w * P.a2) * Sh.eps s +
        ((1 - w) * P.a1) * Sh.epsF s +
        (-(w * P.a2 * (P.a1 * Em + P.a2 * EmF) + (1 - w) * P.a1 * (P.a1 * EmF + P.a2 * Em)))) =
      0 := by
    refine Finset.sum_eq_zero fun s _ => ?_
    have := (hP s).2
    unfold plannerFOC2 homeGap foreignGap at this
    rw [show (P.a1 * P.a2) * M s + (w * P.a2 ^ 2 + (1 - w) * (P.a1 ^ 2 + P.χ)) * MF s +
      (w * P.a2) * Sh.eps s + ((1 - w) * P.a1) * Sh.epsF s +
      (-(w * P.a2 * (P.a1 * Em + P.a2 * EmF) + (1 - w) * P.a1 * (P.a1 * EmF + P.a2 * Em))) = 0
      by linear_combination this, mul_zero]
  rw [expect_affine] at h1 h2
  have he : expect Sh Sh.eps = 0 := Sh.eps_mean
  have heF : expect Sh Sh.epsF = 0 := Sh.epsF_mean
  rw [he, heF] at h1 h2
  have h1w : 0 < 1 - w := by linarith
  constructor
  · have : (w * P.χ) * Em = 0 := by linear_combination h1
    exact (mul_eq_zero.mp this).resolve_left (by positivity)
  · have : ((1 - w) * P.χ) * EmF = 0 := by linear_combination h2
    exact (mul_eq_zero.mp this).resolve_left (by positivity)

/-- O&R fn 42: the planner's (1,1) coefficient `w (a₁² + χ) + (1 − w) a₂²`. -/
def pH11 (P : CoordParams) (w : ℝ) : ℝ := w * (P.a1 ^ 2 + P.χ) + (1 - w) * P.a2 ^ 2

/-- O&R fn 42: the planner's (2,2) coefficient `w a₂² + (1 − w)(a₁² + χ)`. -/
def pH22 (P : CoordParams) (w : ℝ) : ℝ := w * P.a2 ^ 2 + (1 - w) * (P.a1 ^ 2 + P.χ)

/-- O&R fn 42: the planner's determinant. -/
def plannerDet (P : CoordParams) (w : ℝ) : ℝ := pH11 P w * pH22 P w - (P.a1 * P.a2) ^ 2

/-- O&R fn 42: the planner's determinant is positive for `0 < w < 1` (strict convexity):
it equals `w(1−w)(a₁² − a₂²)² + (1−w)χ(w a₁² + (1−w)a₂²) + wχ(w a₂² + (1−w)a₁²) +
w(1−w)χ²`. -/
theorem plannerDet_pos (P : CoordParams) {w : ℝ} (hw0 : 0 < w) (hw1 : w < 1) :
    0 < plannerDet P w := by
  have hχ := P.χ_pos
  have h1w : 0 < 1 - w := by linarith
  have hid : plannerDet P w = w * (1 - w) * (P.a1 ^ 2 - P.a2 ^ 2) ^ 2 +
      (1 - w) * P.χ * (w * P.a1 ^ 2 + (1 - w) * P.a2 ^ 2) +
      w * P.χ * (w * P.a2 ^ 2 + (1 - w) * P.a1 ^ 2) + w * (1 - w) * P.χ ^ 2 := by
    unfold plannerDet pH11 pH22
    ring
  rw [hid]
  positivity

/-- O&R fn 42: Home's planner money growth `−(H₂₂ r₁ − a₁a₂ r₂)/det` with
`r₁ = w a₁ ε + (1−w) a₂ ε*`, `r₂ = w a₂ ε + (1−w) a₁ ε*`. -/
noncomputable def plannerM (P : CoordParams) (Sh : CoordShocks S) (w : ℝ) (s : S) : ℝ :=
  -(pH22 P w * (w * P.a1 * Sh.eps s + (1 - w) * P.a2 * Sh.epsF s) -
    P.a1 * P.a2 * (w * P.a2 * Sh.eps s + (1 - w) * P.a1 * Sh.epsF s)) / plannerDet P w

/-- O&R fn 42: Foreign's planner money growth `−(H₁₁ r₂ − a₁a₂ r₁)/det`. -/
noncomputable def plannerMF (P : CoordParams) (Sh : CoordShocks S) (w : ℝ) (s : S) : ℝ :=
  -(pH11 P w * (w * P.a2 * Sh.eps s + (1 - w) * P.a1 * Sh.epsF s) -
    P.a1 * P.a2 * (w * P.a1 * Sh.eps s + (1 - w) * P.a2 * Sh.epsF s)) / plannerDet P w

/-- O&R fn 42: the planner's closed form has zero mean. -/
theorem expect_plannerM (P : CoordParams) (Sh : CoordShocks S) (w : ℝ) :
    expect Sh (plannerM P Sh w) = 0 ∧ expect Sh (plannerMF P Sh w) = 0 := by
  have he : expect Sh Sh.eps = 0 := Sh.eps_mean
  have heF : expect Sh Sh.epsF = 0 := Sh.epsF_mean
  constructor
  · have hs : ∀ s, Sh.prob s * plannerM P Sh w s = Sh.prob s *
        ((-(pH22 P w * (w * P.a1) - P.a1 * P.a2 * (w * P.a2)) / plannerDet P w) * Sh.eps s +
          (-(pH22 P w * ((1 - w) * P.a2) - P.a1 * P.a2 * ((1 - w) * P.a1)) / plannerDet P w) *
            Sh.epsF s + 0 * Sh.eps s + 0 * Sh.eps s + 0) := fun s => by
      unfold plannerM
      ring
    unfold expect
    rw [Finset.sum_congr rfl fun s _ => hs s, expect_affine, he, heF]
    ring
  · have hs : ∀ s, Sh.prob s * plannerMF P Sh w s = Sh.prob s *
        ((-(pH11 P w * (w * P.a2) - P.a1 * P.a2 * (w * P.a1)) / plannerDet P w) * Sh.eps s +
          (-(pH11 P w * ((1 - w) * P.a1) - P.a1 * P.a2 * ((1 - w) * P.a2)) / plannerDet P w) *
            Sh.epsF s + 0 * Sh.eps s + 0 * Sh.eps s + 0) := fun s => by
      unfold plannerMF
      ring
    unfold expect
    rw [Finset.sum_congr rfl fun s _ => hs s, expect_affine, he, heF]
    ring

/-- O&R fn 42, the planner's solution exists, is unique and has the closed form
`(plannerM, plannerMF)` (for `0 < w < 1`). -/
theorem planner_iff_closed_form {P : CoordParams} {Sh : CoordShocks S} {w : ℝ} (hw0 : 0 < w)
    (hw1 : w < 1) (M MF : S → ℝ) :
    IsPlanner P Sh w M MF ↔ ∀ s, M s = plannerM P Sh w s ∧ MF s = plannerMF P Sh w s := by
  have hdet := (plannerDet_pos P hw0 hw1).ne'
  have hD' : plannerDet P w = (w * (P.a1 ^ 2 + P.χ) + (1 - w) * P.a2 ^ 2) *
      (w * P.a2 ^ 2 + (1 - w) * (P.a1 ^ 2 + P.χ)) - (P.a1 * P.a2) ^ 2 := rfl
  constructor
  · intro hP s
    obtain ⟨h0, h0F⟩ := planner_expect_zero hw0 hw1 hP
    rw [planner_iff_foc P Sh hw0 hw1] at hP
    have h1 := (hP s).1
    have h2 := (hP s).2
    rw [h0, h0F] at h1 h2
    simp only [plannerFOC1, plannerFOC2, homeGap, foreignGap] at h1 h2
    unfold plannerM plannerMF pH11 pH22
    constructor
    · rw [eq_div_iff hdet, hD']
      linear_combination (w * P.a2 ^ 2 + (1 - w) * (P.a1 ^ 2 + P.χ)) * h1 -
        P.a1 * P.a2 * h2
    · rw [eq_div_iff hdet, hD']
      linear_combination (w * (P.a1 ^ 2 + P.χ) + (1 - w) * P.a2 ^ 2) * h2 -
        P.a1 * P.a2 * h1
  · intro hs
    have hM : M = plannerM P Sh w := funext fun s => (hs s).1
    have hMF : MF = plannerMF P Sh w := funext fun s => (hs s).2
    subst hM hMF
    rw [planner_iff_foc P Sh hw0 hw1]
    intro s
    rw [(expect_plannerM P Sh w).1, (expect_plannerM P Sh w).2]
    have k1 : plannerM P Sh w s * plannerDet P w =
        -((w * P.a2 ^ 2 + (1 - w) * (P.a1 ^ 2 + P.χ)) *
          (w * P.a1 * Sh.eps s + (1 - w) * P.a2 * Sh.epsF s) -
          P.a1 * P.a2 * (w * P.a2 * Sh.eps s + (1 - w) * P.a1 * Sh.epsF s)) := by
      unfold plannerM
      exact div_mul_cancel₀ _ hdet
    have k2 : plannerMF P Sh w s * plannerDet P w =
        -((w * (P.a1 ^ 2 + P.χ) + (1 - w) * P.a2 ^ 2) *
          (w * P.a2 * Sh.eps s + (1 - w) * P.a1 * Sh.epsF s) -
          P.a1 * P.a2 * (w * P.a1 * Sh.eps s + (1 - w) * P.a2 * Sh.epsF s)) := by
      unfold plannerMF
      exact div_mul_cancel₀ _ hdet
    constructor
    · have : plannerFOC1 P w 0 0 (plannerM P Sh w s) (plannerMF P Sh w s) (Sh.eps s)
          (Sh.epsF s) * plannerDet P w = 0 := by
        unfold plannerFOC1 homeGap foreignGap
        linear_combination (w * (P.a1 ^ 2 + P.χ) + (1 - w) * P.a2 ^ 2) * k1 +
          (P.a1 * P.a2) * k2 + (w * P.a1 * Sh.eps s + (1 - w) * P.a2 * Sh.epsF s) * hD'
      exact (mul_eq_zero.mp this).resolve_right hdet
    · have : plannerFOC2 P w 0 0 (plannerM P Sh w s) (plannerMF P Sh w s) (Sh.eps s)
          (Sh.epsF s) * plannerDet P w = 0 := by
        unfold plannerFOC2 homeGap foreignGap
        linear_combination (P.a1 * P.a2) * k1 +
          (w * P.a2 ^ 2 + (1 - w) * (P.a1 ^ 2 + P.χ)) * k2 +
          (w * P.a2 * Sh.eps s + (1 - w) * P.a1 * Sh.epsF s) * hD'
      exact (mul_eq_zero.mp this).resolve_right hdet

/-- O&R fn 42: the closed form is the planner's solution (existence). -/
theorem planner_exists (P : CoordParams) (Sh : CoordShocks S) {w : ℝ} (hw0 : 0 < w)
    (hw1 : w < 1) : IsPlanner P Sh w (plannerM P Sh w) (plannerMF P Sh w) :=
  (planner_iff_closed_form hw0 hw1 _ _).mpr fun _ => ⟨rfl, rfl⟩

/-- O&R p. 656: the planner's and Nash's first-order conditions differ exactly by the
spillover terms `(1 − w) a₂ (y* − ȳ)` and `w a₂ (y − ȳ)`, so they coincide when `a₂ = 0`. -/
theorem plannerFOC_eq_nashFOC (P : CoordParams) (w Em EmF M MF e eF : ℝ) :
    plannerFOC1 P w Em EmF M MF e eF = w * (P.a1 * homeGap P Em EmF M MF e + P.χ * M) +
        (1 - w) * P.a2 * foreignGap P Em EmF M MF eF ∧
      plannerFOC2 P w Em EmF M MF e eF =
        (1 - w) * (P.a1 * foreignGap P Em EmF M MF eF + P.χ * MF) +
          w * P.a2 * homeGap P Em EmF M MF e := by
  unfold plannerFOC1 plannerFOC2
  constructor <;> ring

/-! ### Symmetric shocks: the response coefficients -/

/-- O&R p. 656: the Nash response coefficient with symmetric shocks, `a₁/(a₁² + a₁a₂ + χ)`. -/
noncomputable def nashCoef (P : CoordParams) : ℝ := P.a1 / (P.a1 ^ 2 + P.a1 * P.a2 + P.χ)

/-- O&R p. 656: the planner's response coefficient with symmetric shocks and `w = 1/2`,
`(a₁ + a₂)/((a₁ + a₂)² + χ)`. -/
noncomputable def plannerCoef (P : CoordParams) : ℝ :=
  (P.a1 + P.a2) / ((P.a1 + P.a2) ^ 2 + P.χ)

/-- O&R p. 656: with symmetric shocks `ε* = ε`, the symmetric profile
`Δm = Δm* = −a₁ ε/(a₁² + a₁a₂ + χ)` is a Nash equilibrium. -/
theorem nash_symmetric {P : CoordParams} {Sh : CoordShocks S}
    (hsym : ∀ s, Sh.epsF s = Sh.eps s) (hd : P.a1 ^ 2 + P.a1 * P.a2 + P.χ ≠ 0) :
    IsNash P Sh (fun s => -(nashCoef P * Sh.eps s)) (fun s => -(nashCoef P * Sh.eps s)) := by
  have he : expect Sh (fun s => -(nashCoef P * Sh.eps s)) = 0 := by
    have hs : ∀ s, Sh.prob s * -(nashCoef P * Sh.eps s) = Sh.prob s *
        (-nashCoef P * Sh.eps s + 0 * Sh.eps s + 0 * Sh.eps s + 0 * Sh.eps s + 0) :=
      fun s => by ring
    unfold expect
    rw [Finset.sum_congr rfl fun s _ => hs s, expect_affine]
    have h0 : expect Sh Sh.eps = 0 := Sh.eps_mean
    rw [h0]
    ring
  rw [nash_iff_system]
  refine ⟨he, he, fun s => ?_⟩
  have hx : nashCoef P * (P.a1 ^ 2 + P.a1 * P.a2 + P.χ) = P.a1 := by
    unfold nashCoef
    exact div_mul_cancel₀ _ hd
  rw [hsym s]
  constructor
  · linear_combination (-Sh.eps s) * hx
  · linear_combination (-Sh.eps s) * hx

/-- O&R p. 656: with symmetric shocks and equal weights the planner sets
`Δm = Δm* = −(a₁ + a₂) ε/((a₁ + a₂)² + χ)`. -/
theorem planner_symmetric {P : CoordParams} {Sh : CoordShocks S}
    (hsym : ∀ s, Sh.epsF s = Sh.eps s) :
    IsPlanner P Sh (1 / 2) (fun s => -(plannerCoef P * Sh.eps s))
      (fun s => -(plannerCoef P * Sh.eps s)) := by
  have hχ := P.χ_pos
  have hD : 0 < (P.a1 + P.a2) ^ 2 + P.χ := by positivity
  have he : expect Sh (fun s => -(plannerCoef P * Sh.eps s)) = 0 := by
    have hs : ∀ s, Sh.prob s * -(plannerCoef P * Sh.eps s) = Sh.prob s *
        (-plannerCoef P * Sh.eps s + 0 * Sh.eps s + 0 * Sh.eps s + 0 * Sh.eps s + 0) :=
      fun s => by ring
    unfold expect
    rw [Finset.sum_congr rfl fun s _ => hs s, expect_affine]
    have h0 : expect Sh Sh.eps = 0 := Sh.eps_mean
    rw [h0]
    ring
  rw [planner_iff_foc P Sh (by norm_num) (by norm_num)]
  intro s
  rw [he]
  unfold plannerFOC1 plannerFOC2 homeGap foreignGap plannerCoef
  rw [hsym s]
  constructor
  · field_simp
    ring
  · field_simp
    ring

/-- O&R p. 656: the planner's minus Nash's response coefficient is exactly
`χ a₂/(((a₁ + a₂)² + χ)(a₁² + a₁a₂ + χ))`. -/
theorem plannerCoef_sub_nashCoef (P : CoordParams) (hd : P.a1 ^ 2 + P.a1 * P.a2 + P.χ ≠ 0) :
    plannerCoef P - nashCoef P =
      P.χ * P.a2 / (((P.a1 + P.a2) ^ 2 + P.χ) * (P.a1 ^ 2 + P.a1 * P.a2 + P.χ)) := by
  have hχ := P.χ_pos
  have hD : (P.a1 + P.a2) ^ 2 + P.χ ≠ 0 := by positivity
  unfold plannerCoef nashCoef
  rw [div_sub_div _ _ hD hd]
  congr 1
  ring

/-- O&R p. 656 ("higher or lower levels of monetary expansion"): with `a₁ > 0`,
`a₁ + a₂ > 0`, the planner's response coefficient exceeds Nash's iff `a₂ > 0`, equals it
iff `a₂ = 0`, and is smaller iff `a₂ < 0`. -/
theorem planner_response_compare (P : CoordParams) (ha1 : 0 < P.a1) (ha12 : 0 < P.a1 + P.a2) :
    (nashCoef P < plannerCoef P ↔ 0 < P.a2) ∧ (nashCoef P = plannerCoef P ↔ P.a2 = 0) ∧
      (plannerCoef P < nashCoef P ↔ P.a2 < 0) := by
  have hχ := P.χ_pos
  have hd : 0 < P.a1 ^ 2 + P.a1 * P.a2 + P.χ := by nlinarith
  have hD : 0 < (P.a1 + P.a2) ^ 2 + P.χ := by positivity
  have hdiff := plannerCoef_sub_nashCoef P hd.ne'
  have hpos : 0 < ((P.a1 + P.a2) ^ 2 + P.χ) * (P.a1 ^ 2 + P.a1 * P.a2 + P.χ) := by positivity
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · intro h
      have h1 : 0 < P.χ * P.a2 / (((P.a1 + P.a2) ^ 2 + P.χ) * (P.a1 ^ 2 + P.a1 * P.a2 + P.χ)) := by
        linarith
      have h2 := (div_pos_iff_of_pos_right hpos).mp h1
      exact pos_of_mul_pos_right h2 hχ.le
    · intro h
      have : 0 < P.χ * P.a2 / (((P.a1 + P.a2) ^ 2 + P.χ) * (P.a1 ^ 2 + P.a1 * P.a2 + P.χ)) := by
        positivity
      linarith
  · constructor
    · intro h
      have h1 : P.χ * P.a2 / (((P.a1 + P.a2) ^ 2 + P.χ) * (P.a1 ^ 2 + P.a1 * P.a2 + P.χ)) = 0 := by
        linarith
      rcases div_eq_zero_iff.mp h1 with h2 | h2
      · exact (mul_eq_zero.mp h2).resolve_left hχ.ne'
      · exact absurd h2 hpos.ne'
    · intro h
      rw [h, mul_zero, zero_div] at hdiff
      linarith
  · constructor
    · intro h
      have h1 : P.χ * P.a2 / (((P.a1 + P.a2) ^ 2 + P.χ) * (P.a1 ^ 2 + P.a1 * P.a2 + P.χ)) < 0 := by
        linarith
      have h2 := (div_neg_iff.mp h1)
      rcases h2 with ⟨_, h3⟩ | ⟨h3, _⟩
      · exact absurd h3 (not_lt.mpr hpos.le)
      · by_contra h4
        push Not at h4
        have := mul_nonneg hχ.le h4
        linarith
    · intro h
      have : P.χ * P.a2 / (((P.a1 + P.a2) ^ 2 + P.χ) * (P.a1 ^ 2 + P.a1 * P.a2 + P.χ)) < 0 :=
        div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hχ h) hpos
      linarith

/-! ### Welfare: the planner beats Nash -/

/-- O&R p. 656: the planner's expected objective `E[w L + (1 − w) L*]` of a profile. -/
def expWelfare (P : CoordParams) (Sh : CoordShocks S) (w : ℝ) (M MF : S → ℝ) : ℝ :=
  ∑ s, Sh.prob s *
    welfare P w (expect Sh M) (expect Sh MF) (M s) (MF s) (Sh.eps s) (Sh.epsF s)

/-- O&R p. 656: the planner's expected weighted loss never exceeds that of any Nash
equilibrium. -/
theorem planner_le_nash {P : CoordParams} {Sh : CoordShocks S} {w : ℝ} (hw0 : 0 < w)
    (hw1 : w < 1) {Mp MFp Mn MFn : S → ℝ} (hP : IsPlanner P Sh w Mp MFp)
    (hN : IsNash P Sh Mn MFn) : expWelfare P Sh w Mp MFp ≤ expWelfare P Sh w Mn MFn := by
  obtain ⟨hp0, hpF0⟩ := planner_expect_zero hw0 hw1 hP
  obtain ⟨hn0, hnF0⟩ := nash_expect_zero hN
  unfold expWelfare
  rw [hp0, hpF0, hn0, hnF0]
  refine Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left ?_ (Sh.prob_nonneg s)
  have := hP s (Mn s) (MFn s)
  rw [hp0, hpF0] at this
  exact this

/-- O&R p. 656: the gain from coordination is strict when there are spillovers (`a₂ ≠ 0`)
and some state of positive probability has a nonzero shock. -/
theorem planner_lt_nash {P : CoordParams} {Sh : CoordShocks S} {w : ℝ} (hw0 : 0 < w)
    (hw1 : w < 1) (ha2 : P.a2 ≠ 0) {Mp MFp Mn MFn : S → ℝ} (hP : IsPlanner P Sh w Mp MFp)
    (hN : IsNash P Sh Mn MFn) (s0 : S) (hp : 0 < Sh.prob s0)
    (hshock : Sh.eps s0 ≠ 0 ∨ Sh.epsF s0 ≠ 0) :
    expWelfare P Sh w Mp MFp < expWelfare P Sh w Mn MFn := by
  obtain ⟨hp0, hpF0⟩ := planner_expect_zero hw0 hw1 hP
  obtain ⟨hn0, hnF0⟩ := nash_expect_zero hN
  have hχ := P.χ_pos
  have h1w : 0 < 1 - w := by linarith
  have hle : ∀ s, welfare P w 0 0 (Mp s) (MFp s) (Sh.eps s) (Sh.epsF s) ≤
      welfare P w 0 0 (Mn s) (MFn s) (Sh.eps s) (Sh.epsF s) := by
    intro s
    have := hP s (Mn s) (MFn s)
    rw [hp0, hpF0] at this
    exact this
  have hlt : welfare P w 0 0 (Mp s0) (MFp s0) (Sh.eps s0) (Sh.epsF s0) <
      welfare P w 0 0 (Mn s0) (MFn s0) (Sh.eps s0) (Sh.epsF s0) := by
    refine lt_of_le_of_ne (hle s0) fun heq => ?_
    have hmin : ∀ x xF, welfare P w 0 0 (Mn s0) (MFn s0) (Sh.eps s0) (Sh.epsF s0) ≤
        welfare P w 0 0 x xF (Sh.eps s0) (Sh.epsF s0) := by
      intro x xF
      have := hP s0 x xF
      rw [hp0, hpF0] at this
      linarith
    obtain ⟨hF1, hF2⟩ := (planner_state_iff P hw0 hw1 _ _ _ _ _ _).mp hmin
    have hn := (nash_iff_foc P Sh Mn MFn).mp hN s0
    rw [hn0, hnF0] at hn
    simp only [plannerFOC1, plannerFOC2] at hF1 hF2
    obtain ⟨hn1, hn2⟩ := hn
    set Y := homeGap P 0 0 (Mn s0) (MFn s0) (Sh.eps s0)
    set YF := foreignGap P 0 0 (Mn s0) (MFn s0) (Sh.epsF s0)
    have hYF : YF = 0 := by
      have : ((1 - w) * P.a2) * YF = 0 := by linear_combination hF1 - w * hn1
      exact (mul_eq_zero.mp this).resolve_left (mul_ne_zero h1w.ne' ha2)
    have hY : Y = 0 := by
      have : (w * P.a2) * Y = 0 := by linear_combination hF2 - (1 - w) * hn2
      exact (mul_eq_zero.mp this).resolve_left (mul_ne_zero hw0.ne' ha2)
    have hM : Mn s0 = 0 := by
      have : P.χ * Mn s0 = 0 := by linear_combination hn1 - P.a1 * hY
      exact (mul_eq_zero.mp this).resolve_left hχ.ne'
    have hMF : MFn s0 = 0 := by
      have : P.χ * MFn s0 = 0 := by linear_combination hn2 - P.a1 * hYF
      exact (mul_eq_zero.mp this).resolve_left hχ.ne'
    have he : Sh.eps s0 = 0 := by
      have := hY
      simp only [Y, homeGap, hM, hMF] at this
      linarith
    have heF : Sh.epsF s0 = 0 := by
      have := hYF
      simp only [YF, foreignGap, hM, hMF] at this
      linarith
    rcases hshock with h | h
    · exact h he
    · exact h heF
  unfold expWelfare
  rw [hp0, hpF0, hn0, hnF0]
  exact Finset.sum_lt_sum (fun s _ => mul_le_mul_of_nonneg_left (hle s) (Sh.prob_nonneg s))
    ⟨s0, Finset.mem_univ _, mul_lt_mul_of_pos_left hlt hp⟩

/-! ### No weight on money growth: two instruments, two targets -/

/-- O&R p. 655: with `χ = 0`, both outputs can be stabilised exactly for every pair of shocks
iff `a₁² ≠ a₂²` (the two instruments are linearly independent). -/
theorem two_instruments_iff (a1 a2 : ℝ) :
    (∀ e eF : ℝ, ∃ x xF : ℝ, a1 * x + a2 * xF + e = 0 ∧ a2 * x + a1 * xF + eF = 0) ↔
      a1 ^ 2 ≠ a2 ^ 2 := by
  constructor
  · intro h hsq
    have hfac : (a1 - a2) * (a1 + a2) = 0 := by linear_combination hsq
    rcases mul_eq_zero.mp hfac with h1 | h1
    · obtain ⟨x, xF, hx1, hx2⟩ := h 0 1
      have : a1 = a2 := by linarith
      subst this
      linarith
    · obtain ⟨x, xF, hx1, hx2⟩ := h 1 1
      have : a2 = -a1 := by linarith
      subst this
      linarith
  · intro hsq e eF
    have hd : a1 ^ 2 - a2 ^ 2 ≠ 0 := sub_ne_zero.mpr hsq
    refine ⟨(a2 * eF - a1 * e) / (a1 ^ 2 - a2 ^ 2), (a2 * e - a1 * eF) / (a1 ^ 2 - a2 ^ 2),
      ?_, ?_⟩
    · field_simp
      ring
    · field_simp
      ring

/-- O&R p. 655: with `χ = 0` a country's best response closes its own output gap exactly
(`a₁ ≠ 0`): `x₀` minimises `(a₁ x + c)²` iff `a₁ x₀ + c = 0`. Hence with `χ = 0` every Nash
equilibrium puts both outputs at `ȳ` with zero loss, which no planner can improve on. -/
theorem zero_chi_best_response_iff {a1 : ℝ} (ha1 : a1 ≠ 0) (c x0 : ℝ) :
    (∀ x, (a1 * x0 + c) ^ 2 ≤ (a1 * x + c) ^ 2) ↔ a1 * x0 + c = 0 := by
  constructor
  · intro h
    have h1 := h (-c / a1)
    rw [show a1 * (-c / a1) + c = 0 by field_simp; ring] at h1
    have h2 : (a1 * x0 + c) ^ 2 = 0 := le_antisymm (by simpa using h1) (sq_nonneg _)
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2
  · intro h x
    rw [h]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    exact sq_nonneg _

end ObstfeldRogoff.NominalRigidities.PolicyCoordination
