/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import CapitalMarketImperfections.DirectSanctionsInsurance

/-!
# Risk sharing with default risk and saving; two-sided default; indexed debt

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §6.1.1.6
(p. 362), Appendix 6B (pp. 422–425), eqs. (58)–(66) and footnotes 74–75, and Exercises 1
and 2 of Chapter 6 (pp. 425–426).

**Appendix 6B.** The country maximises `u(C₁) + βE u(C₂)` with `Y₁ = Ȳ`, `β(1 + r) = 1`;
date-2 consumption is `C₂ = Ȳ + ε − P + (1 + r)(Ȳ − C₁)` and a defaulter forfeits its own
foreign assets, so (58) `P ≤ η(Ȳ + ε) + (1 + r)(Ȳ − C₁)`. We prove that the optimum has
`C₂(ε) = max(C₁, (1 − η)(Ȳ + ε))`, where `C₁` is the *unique* solution of
`E max(C₁, (1 − η)Y₂) + (1 + r)C₁ = (2 + r)Ȳ`; it is optimal for every strictly concave
utility and it is the unique optimum. Kuhn–Tucker multipliers satisfying (59)–(61) exist,
(62)–(64) hold, and the schedule is (65). Positive saving `C₁ < Ȳ` holds *iff* (58) binds
in some state, iff full insurance is not incentive compatible — no prudence is needed. With
`η = 0` the country still obtains insurance (§6.1.1.6, p. 362). The uniform example with
`η = 0`: zero profit iff `e² + 2(3 + 2r)ε̄e + ε̄² = 0`, the relevant root is
`e = −ε̄[3 + 2r − √((3 + 2r)² − 1)]`, and in fact `e ∈ (−ε̄/3, 0)` (sharper than the book's
`(−ε̄, 0)`); footnote 75.

**Exercise 1 (two-sided default risk).** The efficient symmetric contract separates state by
state: `P(ε) = clamp(ε, −η(Ȳ − ε), η(Ȳ + ε))`; (a) `C = C* = Ȳ` exactly on `[−e, e]`,
`e = ηȲ/(1 − η)`; (b) outside that range the constraint of the richer country binds.

**Exercise 2 (indexed debt).** With nonnegative payments `P ≥ 0`, `E P = (1 + r)D` and
`P ≤ η(Ȳ + (1 + r)D + ε)`, the optimum is `C = min(X, max(c̄, (1 − η)X))`,
`X = Ȳ + (1 + r)D + ε`, `E C = Ȳ`, with Kuhn–Tucker multipliers. The book's hint
`C(ε_) = X(ε_)` is *not* true in general: when debt service exceeds the worst shock and
sanctions are strong the optimum is full insurance with positive payments in every state.
(b) Indexed debt is never better than pure insurance and is strictly worse whenever the
insurance incentive constraint binds; full insurance needs `η ≥ ε̄/(Ȳ + ε̄)` with insurance
but `η ≥ (ε̄ − ε_)/(Ȳ + ε̄ − ε_)` with indexed debt.
-/

namespace ObstfeldRogoff.CapitalMarketImperfections.SanctionsWithSaving

open Finset Set
open SovereignRiskPrimitives SovereignRiskPrimitives.StateSpaceFacts
open DirectSanctionsInsurance

variable {S : Type} [Fintype S] (E : Endowment S)

/-! ## Appendix 6B -/

/-- Date-2 consumption with saving, O&R Appendix 6B, p. 423:
`C₂(ε) = Ȳ + ε − P(ε) + (1 + r)(Ȳ − C₁)`. -/
def cons2 (r C1 : ℝ) (P : S → ℝ) (s : S) : ℝ := E.Y s - P s + (1 + r) * (E.Ybar - C1)

/-- The incentive constraint with seizable foreign assets, O&R (58), p. 423:
`P(ε) ≤ η(Ȳ + ε) + (1 + r)(Ȳ − C₁)`. -/
def SavingIC (η r C1 : ℝ) (P : S → ℝ) : Prop :=
  ∀ s, P s ≤ η * E.Y s + (1 + r) * (E.Ybar - C1)

/-- Lifetime utility `U₁ = u(C₁) + βE u(C₂)`, O&R Appendix 6B, p. 422. -/
def lifetime (U : Utility) (β r C1 : ℝ) (P : S → ℝ) : ℝ :=
  U.u C1 + β * E.Ω.expect (fun s => U.u (cons2 E r C1 P s))

/-- The equation pinning down `C₁`, O&R Appendix 6B (zero profit (1) with (62)–(64)):
`E max(C₁, (1 − η)(Ȳ + ε)) + (1 + r)C₁ = (2 + r)Ȳ`. -/
def C1Eq (η r c : ℝ) : Prop :=
  E.Ω.expect (fun s => max c (floorCons E η s)) + (1 + r) * c = (2 + r) * E.Ybar

/-- The candidate optimal schedule, O&R (65), p. 424:
`P(ε) = Ȳ + ε − max(C₁, (1 − η)(Ȳ + ε)) + (1 + r)(Ȳ − C₁)`. -/
def optPay (η r c : ℝ) (s : S) : ℝ :=
  E.Y s - max c (floorCons E η s) + (1 + r) * (E.Ybar - c)

/-- The candidate gives `C₂ = max(C₁, (1 − η)(Ȳ + ε))` (O&R (62)–(63), p. 424). -/
theorem cons2_optPay (η r c : ℝ) (s : S) :
    cons2 E r c (optPay E η r c) s = max c (floorCons E η s) := by
  unfold cons2 optPay; ring

/-- Budget: expected date-2 consumption, O&R Appendix 6B:
`E C₂ = Ȳ − E P + (1 + r)(Ȳ − C₁)`. -/
theorem expect_cons2 (r C1 : ℝ) (P : S → ℝ) :
    E.Ω.expect (cons2 E r C1 P) = E.Ybar - E.Ω.expect P + (1 + r) * (E.Ybar - C1) := by
  unfold cons2
  rw [show (fun s => E.Y s - P s + (1 + r) * (E.Ybar - C1)) =
      fun s => (1 + r) * (E.Ybar - C1) + (E.Y s - P s) from funext fun s => by ring,
    expect_const_add, expect_sub, E.expect_Y]
  ring

/-- Existence of `C₁`, O&R (64), p. 424 (intermediate value theorem), with `0 < C₁ ≤ Ȳ`. -/
theorem c1_exists {η r : ℝ} (hη0 : 0 ≤ η) (hη1 : η < 1) (hr : -1 < r) :
    ∃ c, 0 < c ∧ c ≤ E.Ybar ∧ C1Eq E η r c := by
  have hY := E.Ybar_pos
  have hcont : Continuous fun c => E.Ω.expect (fun s => max c (floorCons E η s)) +
      (1 + r) * c := (continuous_expect_max E.Ω _).add (by fun_prop)
  have h0 : E.Ω.expect (fun s => max 0 (floorCons E η s)) + (1 + r) * 0 =
      (1 - η) * E.Ybar := by
    have e : (fun s => max 0 (floorCons E η s)) = floorCons E η := by
      funext s; exact max_eq_right (floorCons_pos E hη1 s).le
    rw [e, expect_floorCons]; ring
  have hYv : (2 + r) * E.Ybar ≤
      E.Ω.expect (fun s => max E.Ybar (floorCons E η s)) + (1 + r) * E.Ybar := by
    have := expect_mono E.Ω (X := fun _ => E.Ybar)
      (Y := fun s => max E.Ybar (floorCons E η s)) fun s => le_max_left _ _
    rw [E.Ω.expect_const] at this; linarith
  obtain ⟨c, hc, hceq⟩ := exists_eq_of_continuous hcont hY.le (a := 0) (T := (2 + r) * E.Ybar)
    (by rw [h0]; nlinarith) hYv
  refine ⟨c, lt_of_le_of_ne hc.1 fun h => ?_, hc.2, hceq⟩
  subst h
  rw [h0] at hceq
  nlinarith

/-- Uniqueness of `C₁`, O&R (64), p. 424: the left side is strictly increasing in `C₁`. -/
theorem c1_unique {η r c₁ c₂ : ℝ} (hr : -1 < r) (h₁ : C1Eq E η r c₁) (h₂ : C1Eq E η r c₂) :
    c₁ = c₂ := by
  have key : ∀ a b, C1Eq E η r a → C1Eq E η r b → a < b → False := by
    intro a b ha hb hab
    have hm := expect_mono E.Ω (X := fun s => max a (floorCons E η s))
      (Y := fun s => max b (floorCons E η s)) fun s => max_le_max hab.le le_rfl
    unfold C1Eq at ha hb
    nlinarith
  rcases lt_trichotomy c₁ c₂ with h | h | h
  · exact (key _ _ h₁ h₂ h).elim
  · exact h
  · exact (key _ _ h₂ h₁ h).elim

/-- Any solution `C₁` of the zero-profit equation is positive and at most `Ȳ`
(O&R Appendix 6B, p. 425: date-1 saving `Ȳ − C₁ ≥ 0`). -/
theorem c1_bounds {η r c : ℝ} (hη0 : 0 ≤ η) (hη1 : η < 1) (hr : -1 < r) (hc : C1Eq E η r c) :
    0 < c ∧ c ≤ E.Ybar := by
  obtain ⟨c', h1, h2, h3⟩ := c1_exists E hη0 hη1 hr
  rw [c1_unique E hr hc h3]; exact ⟨h1, h2⟩

/-- The candidate satisfies the zero-profit condition (1) (O&R Appendix 6B). -/
theorem optPay_zero_profit {η r c : ℝ} (hc : C1Eq E η r c) :
    E.Ω.expect (optPay E η r c) = 0 := by
  unfold optPay
  rw [show (fun s => E.Y s - max c (floorCons E η s) + (1 + r) * (E.Ybar - c)) =
      fun s => (1 + r) * (E.Ybar - c) + (E.Y s - max c (floorCons E η s)) from
      funext fun s => by ring, expect_const_add, expect_sub, E.expect_Y]
  unfold C1Eq at hc
  linarith

/-- The candidate satisfies the incentive constraint (58) (O&R Appendix 6B). -/
theorem optPay_ic (η r c : ℝ) : SavingIC E η r c (optPay E η r c) := by
  intro s
  have := le_max_right c (floorCons E η s)
  unfold optPay floorCons at *
  linarith

/-- **The optimal contract with saving**, O&R Appendix 6B, eqs. (58)–(65),
pp. 423–424. With `β(1 + r) = 1`, `r > −1`, `0 ≤ η < 1` and `C₁` solving the zero-profit
equation, `(C₁, P)` with `P` from (65) satisfies (1) and (58), and every `(C₁', P')` with
`C₁' > 0` satisfying (1) and (58) gives no higher lifetime utility, with equality only if
`C₁' = C₁` and `P' = P`. The optimum is the same for every strictly concave utility. -/
theorem optimal_saving_contract (U : Utility) {β η r c : ℝ} (hβ : β * (1 + r) = 1)
    (hr : -1 < r) (hη0 : 0 ≤ η) (hη1 : η < 1) (hc : C1Eq E η r c) :
    E.Ω.expect (optPay E η r c) = 0 ∧ SavingIC E η r c (optPay E η r c) ∧
      ∀ C1 P, 0 < C1 → E.Ω.expect P = 0 → SavingIC E η r C1 P →
        lifetime E U β r C1 P ≤ lifetime E U β r c (optPay E η r c) ∧
        (lifetime E U β r C1 P = lifetime E U β r c (optPay E η r c) →
          C1 = c ∧ P = optPay E η r c) := by
  refine ⟨optPay_zero_profit E hc, optPay_ic E η r c, fun C1 P hC1 hP hIC => ?_⟩
  have hcpos := (c1_bounds E hη0 hη1 hr hc).1
  have hβpos : 0 < β := by
    rcases lt_or_ge 0 β with h | h
    · exact h
    · nlinarith
  set C2 := cons2 E r C1 P with hC2
  have hlo : ∀ s, floorCons E η s ≤ C2 s := fun s => by
    have := hIC s; simp only [hC2, cons2, floorCons]; linarith
  set hi : S → ℝ := fun s => max (C2 s) (max c (floorCons E η s))
  have hmin : ∀ s, min (hi s) (max c (floorCons E η s)) = max c (floorCons E η s) :=
    fun s => min_eq_right (le_max_right _ _)
  obtain ⟨h1, h2⟩ := clamp_supergradient E.Ω U hcpos (floorCons_pos E hη1)
    (fun s => le_trans (le_max_right c _) (le_max_right _ _)) hlo (fun s => le_max_left _ _)
  have hfu : (fun s => U.u (min (hi s) (max c (floorCons E η s)))) =
      fun s => U.u (cons2 E r c (optPay E η r c) s) :=
    funext fun s => by rw [hmin, cons2_optPay]
  have hfc : (fun s => min (hi s) (max c (floorCons E η s))) =
      cons2 E r c (optPay E η r c) := funext fun s => by rw [hmin, cons2_optPay]
  rw [hfu, hfc] at h1 h2
  have hmeans : E.Ω.expect C2 - E.Ω.expect (cons2 E r c (optPay E η r c)) =
      (1 + r) * (c - C1) := by
    rw [hC2, expect_cons2, expect_cons2, hP, optPay_zero_profit E hc]; ring
  rw [hmeans] at h1 h2
  have hsl1 := U.supporting_line hC1 hcpos
  have hlin : U.du c * (C1 - c) + β * (U.du c * ((1 + r) * (c - C1))) = 0 := by
    have : β * (U.du c * ((1 + r) * (c - C1))) = U.du c * (c - C1) * (β * (1 + r)) := by
      ring
    rw [this, hβ]; ring
  unfold lifetime
  constructor
  · nlinarith
  · intro heq
    have hC1eq : C1 = c := by
      by_contra hne
      have := U.supporting_line_strict hC1 hcpos hne
      nlinarith
    refine ⟨hC1eq, ?_⟩
    funext s
    by_contra hne
    have hne' : C2 s ≠ min (hi s) (max c (floorCons E η s)) := by
      rw [hmin, ← cons2_optPay E η r c s]
      simp only [hC2, cons2, hC1eq]
      intro h; apply hne; linarith
    have := h2 ⟨s, E.prob_pos s, hne'⟩
    nlinarith

/-- **Kuhn–Tucker conditions at the optimum**, O&R (59)–(61), p. 423 (necessity): with
`μ = βu'(C₁)` and `λ(ε) = π(ε)β[u'(C₁) − u'(C₂(ε))] ≥ 0`, (59)
`u'(C₁) = β(1 + r)Σπu'(C₂) + (1 + r)Σλ`, (60) `πβu'(C₂) + λ = μπ` and (61) hold. -/
theorem kuhn_tucker_6B (U : Utility) {β η r c : ℝ} (hβ : β * (1 + r) = 1) (hr : -1 < r)
    (hη0 : 0 ≤ η) (hη1 : η < 1) (hc : C1Eq E η r c) :
    let C2 := cons2 E r c (optPay E η r c)
    let lam : S → ℝ := fun s => E.Ω.prob s * β * (U.du c - U.du (C2 s))
    (0 ≤ β → ∀ s, 0 ≤ lam s) ∧
      U.du c = β * (1 + r) * ∑ s, E.Ω.prob s * U.du (C2 s) + (1 + r) * ∑ s, lam s ∧
      (∀ s, E.Ω.prob s * β * U.du (C2 s) + lam s = β * U.du c * E.Ω.prob s) ∧
      (∀ s, lam s * (η * E.Y s + (1 + r) * (E.Ybar - c) - optPay E η r c s) = 0) := by
  intro C2 lam
  have hcpos := (c1_bounds E hη0 hη1 hr hc).1
  refine ⟨fun hβ0 s => ?_, ?_, fun s => by simp only [lam]; ring, fun s => ?_⟩
  · simp only [lam, C2, cons2_optPay]
    exact mul_nonneg (mul_nonneg (E.Ω.prob_nonneg s) hβ0) (by
      linarith [U.du_anti hcpos (le_max_left c (floorCons E η s))])
  · simp only [lam]
    have e : ∑ s, E.Ω.prob s * β * (U.du c - U.du (C2 s)) =
        β * U.du c * ∑ s, E.Ω.prob s - β * ∑ s, E.Ω.prob s * U.du (C2 s) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro s _; ring
    rw [e, E.Ω.prob_sum]
    have : β * (1 + r) * ∑ s, E.Ω.prob s * U.du (C2 s) +
        (1 + r) * (β * U.du c * 1 - β * ∑ s, E.Ω.prob s * U.du (C2 s)) =
        U.du c * (β * (1 + r)) := by ring
    rw [this, hβ, mul_one]
  · simp only [lam, C2, cons2_optPay]
    rcases le_total (floorCons E η s) c with h | h
    · rw [max_eq_left h]; ring
    · have : η * E.Y s + (1 + r) * (E.Ybar - c) - optPay E η r c s = 0 := by
        unfold optPay; rw [max_eq_right h]; unfold floorCons; ring
      rw [this, mul_zero]

/-- O&R (62), p. 424: in states where (58) is slack, `u'(C₁) = (1 + r)βu'(C₂) = u'(C₂)`,
i.e. consumption is equated across dates. -/
theorem euler_slack (U : Utility) {β η r c : ℝ} (hβ : β * (1 + r) = 1) {s : S}
    (hs : floorCons E η s ≤ c) :
    U.du c = (1 + r) * β * U.du (cons2 E r c (optPay E η r c) s) ∧
      cons2 E r c (optPay E η r c) s = c := by
  rw [cons2_optPay, max_eq_left hs]
  refine ⟨?_, rfl⟩
  rw [show (1 + r) * β = β * (1 + r) by ring, hβ, one_mul]

/-- O&R (63), p. 424: where (58) binds, `P(ε) = η(Ȳ + ε) − (1 + r)(C₁ − Ȳ)` and
`C₂(ε) = (1 − η)(Ȳ + ε)`. -/
theorem binding_arm {η r c : ℝ} {s : S} (hs : c ≤ floorCons E η s) :
    optPay E η r c s = η * E.Y s - (1 + r) * (c - E.Ybar) ∧
      cons2 E r c (optPay E η r c) s = (1 - η) * E.Y s := by
  refine ⟨?_, ?_⟩
  · unfold optPay; rw [max_eq_right hs]; unfold floorCons; ring
  · rw [cons2_optPay, max_eq_right hs]; rfl

/-- The threshold of Appendix 6B, `e = C₁/(1 − η) − Ȳ`, so that (64) `C₁ = (1 − η)(Ȳ + e)`
(O&R p. 424). -/
noncomputable def threshold6B (η c Ybar : ℝ) : ℝ := c / (1 - η) - Ybar

/-- **The schedule (65)**, O&R p. 424: `P(ε) = ε + (2 + r)[ηȲ − (1 − η)e]` for `ε < e`
and `P(ε) = ηε + (2 + r)[ηȲ − (1 + r)(1 − η)e/(2 + r)]` for `ε ≥ e`, where (64)
`C₁ = (1 − η)(Ȳ + e)`. -/
theorem schedule_65 {η r c : ℝ} (hη1 : η < 1) (hr : -1 < r) (s : S) :
    c = (1 - η) * (E.Ybar + threshold6B η c E.Ybar) ∧
    (E.ε s < threshold6B η c E.Ybar → optPay E η r c s =
        E.ε s + (2 + r) * (η * E.Ybar - (1 - η) * threshold6B η c E.Ybar)) ∧
    (threshold6B η c E.Ybar ≤ E.ε s → optPay E η r c s =
        η * E.ε s + (2 + r) * (η * E.Ybar -
          (1 + r) / (2 + r) * ((1 - η) * threshold6B η c E.Ybar))) := by
  have h1 : (0 : ℝ) < 1 - η := by linarith
  have h2 : (2 : ℝ) + r ≠ 0 := by linarith
  have hcb : c = (1 - η) * (E.Ybar + threshold6B η c E.Ybar) := by
    unfold threshold6B; field_simp; ring
  refine ⟨hcb, ?_⟩
  generalize threshold6B η c E.Ybar = t at *
  subst hcb
  unfold optPay floorCons Endowment.Y
  constructor
  · intro h; rw [max_eq_left (by nlinarith)]; ring
  · intro h; rw [max_eq_right (by nlinarith)]; field_simp; ring

/-- **Positive saving iff the constraint binds**, O&R Appendix 6B, p. 424, and §6.1.1.6,
p. 362 (no prudence needed): `C₁ < Ȳ` iff (58) binds in some state, i.e. iff
`C₁ < (1 − η)(Ȳ + ε)` for some `ε`. -/
theorem positive_saving_iff_binding {η r c : ℝ} (hr : -1 < r)
    (hc : C1Eq E η r c) : c < E.Ybar ↔ ∃ s, c < floorCons E η s := by
  constructor
  · intro h
    by_contra hn; push Not at hn
    have e : (fun s => max c (floorCons E η s)) = fun _ => c := funext fun s =>
      max_eq_left (hn s)
    unfold C1Eq at hc; rw [e, E.Ω.expect_const] at hc
    have : (2 + r) * c = (2 + r) * E.Ybar := by linarith
    have := mul_left_cancel₀ (show (2 : ℝ) + r ≠ 0 by linarith) this
    linarith
  · rintro ⟨s, hs⟩
    have hlt := expect_strictMono E.Ω (X := fun _ => c)
      (Y := fun s => max c (floorCons E η s)) (fun t => le_max_left _ _) (E.prob_pos s)
      (lt_of_lt_of_le hs (le_max_right _ _))
    rw [E.Ω.expect_const] at hlt
    unfold C1Eq at hc
    nlinarith

/-- O&R §6.1.1.6, p. 362: the country saves (`C₁ < Ȳ`) iff full insurance with zero
saving is not incentive compatible, i.e. iff `(1 − η)(Ȳ + ε) > Ȳ` for some `ε`. -/
theorem positive_saving_iff {η r c : ℝ} (hη0 : 0 ≤ η) (hη1 : η < 1) (hr : -1 < r)
    (hc : C1Eq E η r c) : c < E.Ybar ↔ ∃ s, E.Ybar < floorCons E η s := by
  constructor
  · intro h
    by_contra hn; push Not at hn
    have hY : C1Eq E η r E.Ybar := by
      unfold C1Eq
      have e : (fun s => max E.Ybar (floorCons E η s)) = fun _ => E.Ybar :=
        funext fun s => max_eq_left (hn s)
      rw [e, E.Ω.expect_const]; ring
    rw [c1_unique E hr hc hY] at h
    exact lt_irrefl _ h
  · rintro ⟨s, hs⟩
    have hb := (c1_bounds E hη0 hη1 hr hc).2
    rcases eq_or_lt_of_le hb with he | he
    · exfalso
      have := (positive_saving_iff_binding E hr hc).mpr
      rw [he] at this
      have h2 := this ⟨s, hs⟩
      exact lt_irrefl _ h2
    · exact he

/-- O&R §6.1.1.6, p. 362, and Appendix 6B, p. 425: "the country can get partial insurance
even when `η = 0`". With no sanctions and a nondegenerate shock, the optimal contract lets
the country consume more than its output in some state. -/
theorem insurance_without_sanctions {r c : ℝ} (hr : -1 < r) (hc : C1Eq E 0 r c)
    (hnd : ∃ s, E.ε s ≠ 0) : ∃ s, E.Y s < cons2 E r c (optPay E 0 r c) s := by
  by_contra hn; push Not at hn
  simp only [cons2_optPay] at hn
  have hfl : ∀ s, floorCons E 0 s = E.Y s := fun s => by simp [floorCons]
  have hmax : ∀ s, max c (floorCons E 0 s) = E.Y s := fun s =>
    le_antisymm (hn s) ((hfl s).symm.le.trans (le_max_right _ _))
  have hcY : ∀ s, c ≤ E.Y s := fun s => by rw [← hmax s]; exact le_max_left _ _
  have hceq : c = E.Ybar := by
    unfold C1Eq at hc
    simp only [hmax] at hc
    rw [E.expect_Y] at hc
    have : (1 + r) * c = (1 + r) * E.Ybar := by linarith
    exact mul_left_cancel₀ (show (1 : ℝ) + r ≠ 0 by linarith) this
  obtain ⟨s, hs⟩ := hnd
  have hnn : ∀ t, 0 ≤ E.ε t := fun t => by
    have := hcY t; rw [hceq] at this; unfold Endowment.Y at this; linarith
  have := eq_zero_of_nonneg_of_expect_zero E.Ω hnn E.mean_zero (E.prob_pos s)
  exact hs this

/-! ### The uniform example with `η = 0` -/

/-- The schedule (66) as a continuous function, O&R p. 424:
`P(x) = min(x − (2 + r)e, −(1 + r)e)`. -/
def schedule66 (r e x : ℝ) : ℝ := min (x - (2 + r) * e) (-(1 + r) * e)

/-- Footnote 75, O&R p. 425: `ε − (2 + r)e < −(1 + r)e` iff `ε < e`, so (66) has the arms
`ε − (2 + r)e` below `e` and `−(1 + r)e` above. -/
theorem footnote_75 (r e x : ℝ) : x - (2 + r) * e < -(1 + r) * e ↔ x < e := by
  constructor <;> intro h <;> linarith

/-- O&R p. 425: with `C₁ = Ȳ + e` (saving `−e`), date-2 consumption under (66) is `Ȳ + e`
for `ε < e` and the autarky level `Ȳ + ε` for `ε ≥ e`. -/
theorem schedule66_consumption (Ybar r e x : ℝ) :
    (x < e → Ybar + x - schedule66 r e x + (1 + r) * (Ybar - (Ybar + e)) = Ybar + e) ∧
      (e ≤ x → Ybar + x - schedule66 r e x + (1 + r) * (Ybar - (Ybar + e)) = Ybar + x) := by
  unfold schedule66
  constructor
  · intro h; rw [min_eq_left (by linarith)]; ring
  · intro h; rw [min_eq_right (by linarith)]; ring

/-- **The zero-profit quadratic with `η = 0`**, O&R p. 425: for `ε ~ U[−ε̄, ε̄]` and
`e ∈ [−ε̄, ε̄]`, `∫ P(ε) dε/(2ε̄) = 0` iff `e² + 2(3 + 2r)ε̄e + ε̄² = 0`. -/
theorem uniform66_zero_profit_iff (r : ℝ) {e ebar : ℝ} (hebar : 0 < ebar)
    (he1 : -ebar ≤ e) (he2 : e ≤ ebar) :
    (∫ x in (-ebar)..ebar, schedule66 r e x / (2 * ebar)) = 0 ↔
      e ^ 2 + 2 * (3 + 2 * r) * ebar * e + ebar ^ 2 = 0 := by
  rw [intervalIntegral.integral_div]
  have hint : ∀ a b, IntervalIntegrable (schedule66 r e) MeasureTheory.volume a b :=
    fun a b => by apply Continuous.intervalIntegrable; unfold schedule66; fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (hint (-ebar) e) (hint e ebar)]
  have hA : ∫ x in (-ebar)..e, schedule66 r e x =
      ∫ x in (-ebar)..e, (-(1 + r) * e + 1 * (x - e)) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le he1] at hx
    unfold schedule66; rw [min_eq_left (by linarith [hx.2])]; ring
  have hB : ∫ x in e..ebar, schedule66 r e x =
      ∫ x in e..ebar, (-(1 + r) * e + 0 * (x - e)) := by
    apply intervalIntegral.integral_congr
    intro x hx
    rw [uIcc_of_le he2] at hx
    unfold schedule66; rw [min_eq_right (by linarith [hx.1])]; ring
  rw [hA, hB, integral_affine, integral_affine]
  have h2 : (2 : ℝ) * ebar ≠ 0 := by positivity
  rw [div_eq_zero_iff, or_iff_left h2]
  constructor <;> intro h <;> nlinarith

/-- The relevant root with `η = 0`, O&R p. 425: `e = −ε̄[3 + 2r − √((3 + 2r)² − 1)]`. -/
noncomputable def threshold66 (r ebar : ℝ) : ℝ :=
  -ebar * (3 + 2 * r - Real.sqrt ((3 + 2 * r) ^ 2 - 1))

/-- **O&R p. 425**, sharpened: for `r ≥ 0` and `ε̄ > 0` the root lies in `(−ε̄/3, 0)`
(the book states only `(−ε̄, 0)`). -/
theorem threshold66_bounds {r ebar : ℝ} (hr : 0 ≤ r) (hebar : 0 < ebar) :
    -ebar / 3 < threshold66 r ebar ∧ threshold66 r ebar < 0 := by
  unfold threshold66
  set k := 3 + 2 * r with hk
  have hk3 : 3 ≤ k := by rw [hk]; linarith
  have hq : 0 ≤ k ^ 2 - 1 := by nlinarith
  have hs := Real.sq_sqrt hq
  have hsn := Real.sqrt_nonneg (k ^ 2 - 1)
  have hslt : Real.sqrt (k ^ 2 - 1) < k := by
    rw [Real.sqrt_lt' (by linarith)]; linarith
  have hspos : 0 < Real.sqrt (k ^ 2 - 1) := Real.sqrt_pos.mpr (by nlinarith)
  -- `(k − √(k²−1))(k + √(k²−1)) = 1`
  have hprod : (k - Real.sqrt (k ^ 2 - 1)) * (k + Real.sqrt (k ^ 2 - 1)) = 1 := by
    nlinarith
  have hpos : 0 < k - Real.sqrt (k ^ 2 - 1) := by linarith
  have hlt3 : k - Real.sqrt (k ^ 2 - 1) < 1 / 3 := by
    have : 3 < k + Real.sqrt (k ^ 2 - 1) := by linarith
    rw [lt_div_iff₀ (by norm_num)]
    nlinarith
  constructor
  · nlinarith
  · nlinarith

/-- **O&R p. 425**: the zero-profit threshold with `η = 0` is the root
`e = −ε̄[3 + 2r − √((3 + 2r)² − 1)]`: for `r ≥ 0`, `ε̄ > 0` and `e ∈ [−ε̄, ε̄]`, the uniform
schedule (66) earns zero expected profit iff `e` equals this root (the other root lies
below `−ε̄`). -/
theorem uniform66_threshold_iff {r e ebar : ℝ} (hr : 0 ≤ r) (hebar : 0 < ebar)
    (he1 : -ebar ≤ e) (he2 : e ≤ ebar) :
    (∫ x in (-ebar)..ebar, schedule66 r e x / (2 * ebar)) = 0 ↔ e = threshold66 r ebar := by
  rw [uniform66_zero_profit_iff r hebar he1 he2]
  unfold threshold66
  set k := 3 + 2 * r with hk
  have hk3 : 3 ≤ k := by rw [hk]; linarith
  have hq : 0 ≤ k ^ 2 - 1 := by nlinarith
  have hs := Real.sq_sqrt hq
  have hsn := Real.sqrt_nonneg (k ^ 2 - 1)
  have hslt : Real.sqrt (k ^ 2 - 1) < k := by
    rw [Real.sqrt_lt' (by linarith)]; linarith
  constructor
  · intro h
    -- factor: (e − e₁)(e − e₂) = 0 with e₂ = −ε̄(k + √(k²−1)) < −ε̄
    have hfac : (e + ebar * (k - Real.sqrt (k ^ 2 - 1))) *
        (e + ebar * (k + Real.sqrt (k ^ 2 - 1))) = 0 := by nlinarith
    rcases mul_eq_zero.mp hfac with h1 | h1
    · linarith
    · exfalso
      have : ebar * (k + Real.sqrt (k ^ 2 - 1)) > ebar := by nlinarith
      linarith
  · intro h; rw [h]; nlinarith

/-! ## Exercise 1: two-sided default risk -/

/-- The efficient two-sided contract of Exercise 1, O&R p. 425: the full-insurance payment
`ε` clamped to the incentive interval `[−η(Ȳ − ε), η(Ȳ + ε)]`. -/
def twoSidedPayment (η Ybar x : ℝ) : ℝ := max (-(η * (Ybar - x))) (min x (η * (Ybar + x)))

/-- **Exercise 1, state by state**, O&R p. 425: with Home output `Ȳ + ε`, Foreign output
`Ȳ − ε` and incentive constraints `P ≤ η(Ȳ + ε)`, `−P ≤ η(Ȳ − ε)`, the clamped payment
maximises `u(C) + u(C*)` over all incentive-compatible payments, uniquely. -/
theorem two_sided_optimal_state (U : Utility) {η Ybar x : ℝ} (hη1 : η < 1)
    (hH : 0 < Ybar + x) (hF : 0 < Ybar - x) {P : ℝ} (hP1 : P ≤ η * (Ybar + x))
    (hP2 : -(η * (Ybar - x)) ≤ P) :
    U.u (Ybar + x - P) + U.u (Ybar - x + P) ≤
        U.u (Ybar + x - twoSidedPayment η Ybar x) + U.u (Ybar - x + twoSidedPayment η Ybar x) ∧
      (U.u (Ybar + x - P) + U.u (Ybar - x + P) =
          U.u (Ybar + x - twoSidedPayment η Ybar x) +
            U.u (Ybar - x + twoSidedPayment η Ybar x) → P = twoSidedPayment η Ybar x) := by
  set Q := twoSidedPayment η Ybar x with hQ
  have hint : -(η * (Ybar - x)) ≤ η * (Ybar + x) := by nlinarith
  have hQ1 : Q ≤ η * (Ybar + x) := by
    simp only [hQ, twoSidedPayment]; exact max_le hint (min_le_right _ _)
  have hQ2 : -(η * (Ybar - x)) ≤ Q := le_max_left _ _
  have hpos : ∀ R, R ≤ η * (Ybar + x) → -(η * (Ybar - x)) ≤ R →
      0 < Ybar + x - R ∧ 0 < Ybar - x + R := fun R h1 h2 =>
    ⟨by nlinarith, by nlinarith⟩
  obtain ⟨hC, hCs⟩ := hpos P hP1 hP2
  obtain ⟨hQC, hQCs⟩ := hpos Q hQ1 hQ2
  -- the coefficient times the deviation is nonpositive
  have hcoef : (U.du (Ybar - x + Q) - U.du (Ybar + x - Q)) * (P - Q) ≤ 0 := by
    by_cases hA : x ≤ η * (Ybar + x)
    · by_cases hB : -(η * (Ybar - x)) ≤ x
      · have : Q = x := by
          simp only [hQ, twoSidedPayment]; rw [min_eq_left hA, max_eq_right hB]
        rw [this]; simp
      · push Not at hB
        have : Q = -(η * (Ybar - x)) := by
          simp only [hQ, twoSidedPayment]
          rw [min_eq_left hA, max_eq_left hB.le]
        have hlt : Ybar + x - Q < Ybar - x + Q := by rw [this]; linarith
        have := U.du_anti hQC hlt.le
        have : 0 ≤ P - Q := by linarith
        nlinarith
    · push Not at hA
      have : Q = η * (Ybar + x) := by
        simp only [hQ, twoSidedPayment]; rw [min_eq_right hA.le, max_eq_right hint]
      have hlt : Ybar - x + Q < Ybar + x - Q := by rw [this]; linarith
      have := U.du_anti hQCs hlt.le
      have : P - Q ≤ 0 := by linarith
      nlinarith
  have h1 := U.supporting_line hC hQC
  have h2 := U.supporting_line hCs hQCs
  have e1 : Ybar + x - P - (Ybar + x - Q) = -(P - Q) := by ring
  have e2 : Ybar - x + P - (Ybar - x + Q) = P - Q := by ring
  rw [e1] at h1; rw [e2] at h2
  refine ⟨by nlinarith, fun heq => ?_⟩
  by_contra hne
  have h1s := U.supporting_line_strict hC hQC (by intro h; apply hne; linarith)
  rw [e1] at h1s
  nlinarith

/-- **Exercise 1(a)**, O&R p. 425: consumption is equalised, `C = C* = Ȳ`, exactly on
`[−e, e]` with `e = ηȲ/(1 − η)`. -/
theorem two_sided_full_range {η Ybar x : ℝ} (hη0 : 0 ≤ η) (hη1 : η < 1) (hY : 0 < Ybar) :
    (Ybar + x - twoSidedPayment η Ybar x = Ybar ∧ Ybar - x + twoSidedPayment η Ybar x = Ybar)
      ↔ (-(η * Ybar / (1 - η)) ≤ x ∧ x ≤ η * Ybar / (1 - η)) := by
  have h1 : (0 : ℝ) < 1 - η := by linarith
  have hA : x ≤ η * Ybar / (1 - η) ↔ x ≤ η * (Ybar + x) := by
    rw [le_div_iff₀ h1]; constructor <;> intro h <;> linarith
  have hB : -(η * Ybar / (1 - η)) ≤ x ↔ -(η * (Ybar - x)) ≤ x := by
    rw [neg_le, le_div_iff₀ h1]; constructor <;> intro h <;> linarith
  rw [hA, hB]
  have hint : -(η * (Ybar - x)) ≤ η * (Ybar + x) := by nlinarith
  unfold twoSidedPayment
  constructor
  · rintro ⟨hQ1, _⟩
    have hQ : max (-(η * (Ybar - x))) (min x (η * (Ybar + x))) = x := by linarith
    have hL := le_max_left (-(η * (Ybar - x))) (min x (η * (Ybar + x)))
    rw [hQ] at hL
    refine ⟨hL, ?_⟩
    by_contra h; push Not at h
    rw [min_eq_right h.le, max_eq_right hint] at hQ
    linarith
  · rintro ⟨hx2, hx1⟩
    rw [min_eq_left hx1, max_eq_right hx2]
    constructor <;> ring

/-- **Exercise 1(b)**, O&R p. 425: for `ε > e` Home's constraint binds:
`C = (1 − η)(Ȳ + ε)` and `C* = (1 + η)Ȳ − (1 − η)ε`. -/
theorem two_sided_high {η Ybar x : ℝ} (hη0 : 0 ≤ η) (hη1 : η < 1) (hY : 0 < Ybar)
    (hx : η * Ybar / (1 - η) < x) :
    Ybar + x - twoSidedPayment η Ybar x = (1 - η) * (Ybar + x) ∧
      Ybar - x + twoSidedPayment η Ybar x = (1 + η) * Ybar - (1 - η) * x := by
  have h1 : (0 : ℝ) < 1 - η := by linarith
  rw [div_lt_iff₀ h1] at hx
  have hA : η * (Ybar + x) ≤ x := by nlinarith
  have hint : -(η * (Ybar - x)) ≤ η * (Ybar + x) := by nlinarith
  unfold twoSidedPayment
  rw [min_eq_right hA, max_eq_right hint]
  constructor <;> ring

/-- **Exercise 1(b)**, O&R p. 425: for `ε < −e` Foreign's constraint binds:
`C = (1 + η)Ȳ + (1 − η)ε` and `C* = (1 − η)(Ȳ − ε)`. -/
theorem two_sided_low {η Ybar x : ℝ} (hη0 : 0 ≤ η) (hη1 : η < 1) (hY : 0 < Ybar)
    (hx : x < -(η * Ybar / (1 - η))) :
    Ybar + x - twoSidedPayment η Ybar x = (1 + η) * Ybar + (1 - η) * x ∧
      Ybar - x + twoSidedPayment η Ybar x = (1 - η) * (Ybar - x) := by
  have h1 : (0 : ℝ) < 1 - η := by linarith
  rw [lt_neg, div_lt_iff₀ h1] at hx
  have hB : x ≤ -(η * (Ybar - x)) := by nlinarith
  have hA : x ≤ η * (Ybar + x) := by nlinarith
  unfold twoSidedPayment
  rw [min_eq_left hA, max_eq_left hB]
  constructor <;> ring

/-- The efficient contract is symmetric, `P(−ε) = −P(ε)` (O&R Exercise 1, p. 425; this
needs `ηȲ ≥ 0`, so that the incentive interval is nonempty). -/
theorem two_sided_symmetric {η Ybar : ℝ} (hη0 : 0 ≤ η) (hY : 0 ≤ Ybar) (x : ℝ) :
    twoSidedPayment η Ybar (-x) = -twoSidedPayment η Ybar x := by
  unfold twoSidedPayment
  rw [show Ybar - -x = Ybar + x by ring, show Ybar + -x = Ybar - x by ring]
  have := mul_nonneg hη0 hY
  simp only [max_def, min_def]
  split_ifs <;> linarith

/-- **Exercise 1, the ex ante problem**, O&R p. 425: over a finite state space, the clamped
schedule maximises `E[u(C) + u(C*)]` among all schedules satisfying both incentive
constraints, uniquely; the problem separates state by state. -/
theorem two_sided_efficient (U : Utility) {η : ℝ} (hη1 : η < 1)
    (hF : ∀ s, 0 < E.Ybar - E.ε s) {P : S → ℝ} (hP1 : ∀ s, P s ≤ η * E.Y s)
    (hP2 : ∀ s, -(η * (E.Ybar - E.ε s)) ≤ P s) :
    E.Ω.expect (fun s => U.u (E.Ybar + E.ε s - P s) + U.u (E.Ybar - E.ε s + P s)) ≤
        E.Ω.expect (fun s => U.u (E.Ybar + E.ε s - twoSidedPayment η E.Ybar (E.ε s)) +
          U.u (E.Ybar - E.ε s + twoSidedPayment η E.Ybar (E.ε s))) ∧
      (E.Ω.expect (fun s => U.u (E.Ybar + E.ε s - P s) + U.u (E.Ybar - E.ε s + P s)) =
          E.Ω.expect (fun s => U.u (E.Ybar + E.ε s - twoSidedPayment η E.Ybar (E.ε s)) +
            U.u (E.Ybar - E.ε s + twoSidedPayment η E.Ybar (E.ε s))) →
        P = fun s => twoSidedPayment η E.Ybar (E.ε s)) := by
  have hpt := fun s => two_sided_optimal_state U hη1 (E.Y_pos s) (hF s) (hP1 s) (hP2 s)
  refine ⟨expect_mono E.Ω fun s => (hpt s).1, fun heq => ?_⟩
  funext s
  by_contra hne
  have hlt : U.u (E.Ybar + E.ε s - P s) + U.u (E.Ybar - E.ε s + P s) <
      U.u (E.Ybar + E.ε s - twoSidedPayment η E.Ybar (E.ε s)) +
        U.u (E.Ybar - E.ε s + twoSidedPayment η E.Ybar (E.ε s)) :=
    lt_of_le_of_ne (hpt s).1 fun h => hne ((hpt s).2 h)
  have := expect_strictMono E.Ω (fun s => (hpt s).1) (E.prob_pos s) hlt
  linarith

/-! ## Exercise 2: indexed debt -/

/-- Resources available for consumption or repayment with indexed debt `D`, O&R
Exercise 2, p. 426: `X(ε) = Ȳ + (1 + r)D + ε`. -/
def resources (r D : ℝ) (s : S) : ℝ := E.Ybar + (1 + r) * D + E.ε s

/-- Feasibility of an indexed-debt schedule, O&R Exercise 2, p. 426: `P ≥ 0`,
`E P = (1 + r)D` and `P ≤ η(Ȳ + (1 + r)D + ε)`. -/
def IndexedFeasible (η r D : ℝ) (P : S → ℝ) : Prop :=
  (∀ s, 0 ≤ P s) ∧ E.Ω.expect P = (1 + r) * D ∧ ∀ s, P s ≤ η * resources E r D s

/-- The candidate consumption under indexed debt, O&R Exercise 2(a):
`C = min(X, max(c̄, (1 − η)X))`. -/
def indexedCons (η r D c : ℝ) (s : S) : ℝ :=
  min (resources E r D s) (max c ((1 - η) * resources E r D s))

/-- Resources are positive (O&R Exercise 2: `D ≥ 0`, `r > −1`, `Ȳ + ε > 0`). -/
theorem resources_pos {r D : ℝ} (hr : -1 < r) (hD : 0 ≤ D) (s : S) :
    0 < resources E r D s := by
  unfold resources
  have := E.Y_pos s; unfold Endowment.Y at this
  nlinarith

/-- Expected resources, `E X = Ȳ + (1 + r)D` (O&R Exercise 2). -/
theorem expect_resources (r D : ℝ) :
    E.Ω.expect (resources E r D) = E.Ybar + (1 + r) * D := by
  unfold resources
  rw [show (fun s => E.Ybar + (1 + r) * D + E.ε s) =
      fun s => (E.Ybar + (1 + r) * D) + E.ε s from rfl, expect_const_add, E.mean_zero,
    add_zero]

/-- **Existence of `c̄` for indexed debt**, O&R Exercise 2(a): if the debt can be serviced
at all, `(1 − η)(1 + r)D ≤ ηȲ` (the maximal expected payment `ηE X` covers `(1 + r)D`),
there is `c̄ > 0` with `E min(X, max(c̄, (1 − η)X)) = Ȳ`. -/
theorem indexed_cbar_exists {η r D : ℝ} (hη0 : 0 ≤ η) (hη1 : η < 1) (hr : -1 < r) (hD : 0 ≤ D)
    (hserv : (1 - η) * ((1 + r) * D) ≤ η * E.Ybar) :
    ∃ c, 0 < c ∧ E.Ω.expect (indexedCons E η r D c) = E.Ybar := by
  have := StateSpaceFacts.nonempty E.Ω
  have hne : (Finset.univ : Finset S).Nonempty := Finset.univ_nonempty
  set lo : S → ℝ := fun s => (1 - η) * resources E r D s
  have hlo : ∀ s, 0 < lo s := fun s => mul_pos (by linarith) (resources_pos E hr hD s)
  set c0 := Finset.univ.inf' hne lo
  have hc0 : 0 < c0 := by
    obtain ⟨s, _, hs⟩ := Finset.exists_mem_eq_inf' hne lo
    simp only [c0]; rw [hs]; exact hlo s
  have hc0le : ∀ s, c0 ≤ lo s := fun s => Finset.inf'_le _ (Finset.mem_univ s)
  set M := E.Ybar + (1 + r) * D + ∑ s, |E.ε s| + c0
  have hXM : ∀ s, resources E r D s ≤ M := fun s => by
    have : E.ε s ≤ ∑ t, |E.ε t| := le_trans (le_abs_self _)
      (Finset.single_le_sum (f := fun t => |E.ε t|) (fun t _ => abs_nonneg _)
        (Finset.mem_univ s))
    simp only [M, resources]; linarith
  have hcont : Continuous fun c => E.Ω.expect (indexedCons E η r D c) := by
    unfold indexedCons StateSpace.expect; fun_prop
  have hlow : E.Ω.expect (indexedCons E η r D c0) ≤ E.Ybar := by
    have e : indexedCons E η r D c0 = lo := funext fun s => by
      unfold indexedCons
      rw [max_eq_right (hc0le s), min_eq_right]
      simp only [lo]; nlinarith [resources_pos E hr hD s]
    rw [e]
    simp only [lo]; rw [expect_const_mul, expect_resources]; nlinarith
  have hhigh : E.Ybar ≤ E.Ω.expect (indexedCons E η r D M) := by
    have e : indexedCons E η r D M = resources E r D := funext fun s => by
      unfold indexedCons
      exact min_eq_left (le_trans (hXM s) (le_max_left _ _))
    rw [e, expect_resources]; nlinarith
  have hc0M : c0 ≤ M := by
    obtain ⟨s, _, hs⟩ := Finset.exists_mem_eq_inf' hne lo
    have := hXM s
    have h2 : lo s ≤ resources E r D s := by
      simp only [lo]; nlinarith [resources_pos E hr hD s]
    simp only [c0]; rw [hs]; linarith
  obtain ⟨c, hc, hceq⟩ := exists_eq_of_continuous hcont hc0M hlow hhigh
  exact ⟨c, lt_of_lt_of_le hc0 hc.1, hceq⟩

/-- **The optimal indexed-debt schedule**, O&R Exercise 2(a), p. 426: with `c̄ > 0` solving
`E min(X, max(c̄, (1 − η)X)) = Ȳ`, the schedule `P = X − C` is feasible, and every feasible
schedule gives no higher expected utility, with equality only for this schedule. Expected
consumption equals `Ȳ`. -/
theorem indexed_optimal (U : Utility) {η r D c : ℝ} (hη0 : 0 ≤ η) (hη1 : η < 1)
    (hr : -1 < r) (hD : 0 ≤ D) (hc : 0 < c)
    (hceq : E.Ω.expect (indexedCons E η r D c) = E.Ybar) :
    IndexedFeasible E η r D (fun s => resources E r D s - indexedCons E η r D c s) ∧
      ∀ P, IndexedFeasible E η r D P →
        E.Ω.expect (fun s => U.u (resources E r D s - P s)) ≤
          E.Ω.expect (fun s => U.u (indexedCons E η r D c s)) ∧
        (E.Ω.expect (fun s => U.u (resources E r D s - P s)) =
            E.Ω.expect (fun s => U.u (indexedCons E η r D c s)) →
          P = fun s => resources E r D s - indexedCons E η r D c s) := by
  have hX := resources_pos E hr hD
  have hlohi : ∀ s, (1 - η) * resources E r D s ≤ resources E r D s := fun s => by
    nlinarith [hX s]
  refine ⟨⟨fun s => ?_, ?_, fun s => ?_⟩, fun P hP => ?_⟩
  · have : indexedCons E η r D c s ≤ resources E r D s := min_le_left _ _
    linarith
  · rw [expect_sub, expect_resources, hceq]; ring
  · have : (1 - η) * resources E r D s ≤ indexedCons E η r D c s :=
      le_min (hlohi s) (le_max_right _ _)
    linarith
  · obtain ⟨hP0, hPm, hPic⟩ := hP
    have hClo : ∀ s, (1 - η) * resources E r D s ≤ resources E r D s - P s := fun s => by
      have := hPic s; linarith
    have hChi : ∀ s, resources E r D s - P s ≤ resources E r D s := fun s => by
      linarith [hP0 s]
    have hmean : E.Ω.expect (fun s => resources E r D s - P s) ≤
        E.Ω.expect (fun s => min (resources E r D s)
          (max c ((1 - η) * resources E r D s))) := by
      rw [expect_sub, expect_resources, hPm]
      have : E.Ω.expect (fun s => min (resources E r D s)
          (max c ((1 - η) * resources E r D s))) = E.Ybar := hceq
      rw [this]; ring_nf; rfl
    obtain ⟨h1, h2⟩ := clamp_optimal E.Ω U hc (fun s => mul_pos (by linarith) (hX s)) hlohi
      hClo hChi hmean
    refine ⟨h1, fun heq => ?_⟩
    funext s
    have := h2 heq s (E.prob_pos s)
    simp only [indexedCons] at this ⊢
    linarith

/-- The three arms of the optimal indexed-debt schedule, O&R Exercise 2(a): `P = 0` where
`X ≤ c̄`; full insurance `C = c̄` where `(1 − η)X ≤ c̄ ≤ X`; `P = ηX` where
`c̄ ≤ (1 − η)X`. -/
theorem indexed_arms {η r D c : ℝ} (hη0 : 0 ≤ η) (hr : -1 < r) (hD : 0 ≤ D) (s : S) :
    (resources E r D s ≤ c → resources E r D s - indexedCons E η r D c s = 0) ∧
      ((1 - η) * resources E r D s ≤ c → c ≤ resources E r D s →
        indexedCons E η r D c s = c) ∧
      (c ≤ (1 - η) * resources E r D s →
        resources E r D s - indexedCons E η r D c s = η * resources E r D s) := by
  have hX := resources_pos E hr hD s
  unfold indexedCons
  refine ⟨fun h => ?_, fun h1 h2 => ?_, fun h => ?_⟩
  · rw [min_eq_left (le_trans h (le_max_left _ _))]; ring
  · rw [max_eq_left h1, min_eq_right h2]
  · rw [max_eq_right h, min_eq_right (by nlinarith)]; ring

/-- **The correct form of the book's hint**, O&R Exercise 2(a): the country pays nothing in
state `ε` iff `X(ε) ≤ c̄`. -/
theorem indexed_zero_payment_iff {η r D c : ℝ} (hη0 : 0 < η) (hr : -1 < r)
    (hD : 0 ≤ D) (s : S) :
    resources E r D s - indexedCons E η r D c s = 0 ↔ resources E r D s ≤ c := by
  have hX := resources_pos E hr hD s
  refine ⟨fun h => ?_, (indexed_arms E hη0.le hr hD s).1⟩
  by_contra hn; push Not at hn
  have hlt : indexedCons E η r D c s < resources E r D s := by
    unfold indexedCons
    apply lt_of_le_of_lt (min_le_right _ _)
    exact max_lt hn (by nlinarith)
  linarith

/-- **The book's hint `C(ε_) = X(ε_)` fails in general** (O&R Exercise 2(a), p. 426). If
debt service exceeds the worst shock (`Ȳ < X(ε)` in every state) while
`(1 − η)X(ε) ≤ Ȳ` everywhere, then `c̄ = Ȳ` solves the mean equation, the optimum is full
insurance `C ≡ Ȳ`, and the country makes a strictly positive payment in *every* state,
including the lowest. -/
theorem indexed_hint_fails {η r D : ℝ} (hlow : ∀ s, (1 - η) * resources E r D s ≤ E.Ybar)
    (hhigh : ∀ s, E.Ybar < resources E r D s) :
    E.Ω.expect (indexedCons E η r D E.Ybar) = E.Ybar ∧
      (∀ s, indexedCons E η r D E.Ybar s = E.Ybar) ∧
      ∀ s, 0 < resources E r D s - indexedCons E η r D E.Ybar s := by
  have hC : ∀ s, indexedCons E η r D E.Ybar s = E.Ybar := fun s => by
    unfold indexedCons; rw [max_eq_left (hlow s), min_eq_right (hhigh s).le]
  refine ⟨?_, hC, fun s => by rw [hC]; linarith [hhigh s]⟩
  rw [show indexedCons E η r D E.Ybar = fun _ => E.Ybar from funext hC, E.Ω.expect_const]

/-- **Kuhn–Tucker multipliers for indexed debt**, O&R Exercise 2(a) (necessity): with
`μ = u'(c̄)`, `λ = π max(0, u'(c̄) − u'(C))` on the incentive constraint and
`ν = π max(0, u'(C) − u'(c̄))` on `P ≥ 0`, `π u'(C) + λ − ν = μπ` and both complementary
slackness conditions hold. -/
theorem indexed_kuhn_tucker (U : Utility) {η r D c : ℝ} (hη0 : 0 ≤ η)
    (hr : -1 < r) (hD : 0 ≤ D) (hc : 0 < c) (s : S) :
    let C := indexedCons E η r D c s
    let lam := E.Ω.prob s * max 0 (U.du c - U.du C)
    let nu := E.Ω.prob s * max 0 (U.du C - U.du c)
    0 ≤ lam ∧ 0 ≤ nu ∧ E.Ω.prob s * U.du C + lam - nu = U.du c * E.Ω.prob s ∧
      lam * (η * resources E r D s - (resources E r D s - C)) = 0 ∧
      nu * (resources E r D s - C) = 0 := by
  intro C lam nu
  have hX := resources_pos E hr hD s
  have hp := E.Ω.prob_nonneg s
  refine ⟨mul_nonneg hp (le_max_left _ _), mul_nonneg hp (le_max_left _ _), ?_, ?_, ?_⟩
  · simp only [lam, nu]
    rcases le_total (U.du c) (U.du C) with h | h
    · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; ring
    · rw [max_eq_right (by linarith), max_eq_left (by linarith)]; ring
  · simp only [lam]
    rcases le_total (U.du c - U.du C) 0 with h | h
    · rw [max_eq_left h]; ring
    · -- `u'(C) < u'(c̄)` forces `C > c̄`, hence `C = (1 − η)X`
      rcases eq_or_lt_of_le h with h0 | h0
      · rw [← h0, max_self]; ring
      have hCc : c < C := by
        by_contra hn; push Not at hn
        have hCpos : 0 < C := lt_min hX (lt_of_lt_of_le hc (le_max_left _ _))
        have := U.du_anti hCpos hn
        linarith
      have hCeq : C = (1 - η) * resources E r D s := by
        simp only [C, indexedCons] at hCc ⊢
        have hm : c < max c ((1 - η) * resources E r D s) :=
          lt_of_lt_of_le hCc (min_le_right _ _)
        have hlo : c < (1 - η) * resources E r D s := by
          rcases le_total c ((1 - η) * resources E r D s) with h' | h'
          · rw [max_eq_right h'] at hm; exact hm
          · rw [max_eq_left h'] at hm; exact absurd hm (lt_irrefl _)
        rw [max_eq_right hlo.le, min_eq_right (by nlinarith)]
      rw [hCeq]; ring
  · simp only [nu]
    rcases le_total (U.du C - U.du c) 0 with h | h
    · rw [max_eq_left h]; ring
    · rcases eq_or_lt_of_le h with h0 | h0
      · rw [← h0, max_self]; ring
      have hCc : C < c := by
        by_contra hn; push Not at hn
        have := U.du_anti hc hn
        linarith
      have hCeq : C = resources E r D s := by
        simp only [C, indexedCons] at hCc ⊢
        rcases le_total (resources E r D s) (max c ((1 - η) * resources E r D s)) with h' | h'
        · rw [min_eq_left h']
        · rw [min_eq_right h'] at hCc
          exact absurd (lt_of_lt_of_le hCc (le_max_left _ _)) (lt_irrefl _)
      rw [hCeq]; ring

/-- **Exercise 2(b): indexed debt is never better than pure insurance**, O&R p. 426. Any
feasible indexed-debt schedule `P` with `D ≥ 0` gives the same consumption as the
insurance schedule `P − (1 + r)D`, which satisfies (1) and (2); hence its expected utility
is at most that of the optimal insurance contract of §6.1.1. -/
theorem indexed_le_insurance (U : Utility) {η r D cbar : ℝ} (hη0 : 0 < η) (hη1 : η < 1)
    (hr : -1 < r) (hD : 0 ≤ D) (hc : CbarEq E η cbar) {P : S → ℝ}
    (hP : IndexedFeasible E η r D P) :
    E.Ω.expect (fun s => U.u (resources E r D s - P s)) ≤
      expectedUtility E U (optPayment E η cbar) := by
  obtain ⟨_, hPm, hPic⟩ := hP
  have hcons : ∀ s, resources E r D s - P s = consumption E (fun t => P t - (1 + r) * D) s :=
    fun s => by unfold resources consumption Endowment.Y; ring
  have hZP : ZeroProfit E (fun t => P t - (1 + r) * D) := by
    unfold ZeroProfit
    rw [show (fun t => P t - (1 + r) * D) = fun t => P t - (fun _ => (1 + r) * D) t from rfl,
      expect_sub, E.Ω.expect_const, hPm, sub_self]
  have hIC : SanctionIC E η (fun t => P t - (1 + r) * D) := fun s => by
    have := hPic s
    unfold resources at this; unfold Endowment.Y
    have h1 : 0 ≤ (1 - η) * ((1 + r) * D) := mul_nonneg (by linarith) (by nlinarith)
    nlinarith
  have := ((optimal_ic_contract E U hη0 hη1 hc).2.2 _ hZP hIC).1
  unfold expectedUtility at this ⊢
  simp only [hcons]
  exact this

/-- **Exercise 2(b): indexed debt is strictly worse** whenever the insurance incentive
constraint binds (some state with `c̄ < (1 − η)(Ȳ + ε)`), O&R p. 426: then no feasible
indexed-debt schedule, for any `D ≥ 0`, attains the optimal insurance value. -/
theorem indexed_strictly_worse (U : Utility) {η r D cbar : ℝ} (hη0 : 0 < η) (hη1 : η < 1)
    (hr : -1 < r) (hD : 0 ≤ D) (hc : CbarEq E η cbar) (hbind : ∃ s, cbar < floorCons E η s)
    {P : S → ℝ} (hP : IndexedFeasible E η r D P) :
    E.Ω.expect (fun s => U.u (resources E r D s - P s)) <
      expectedUtility E U (optPayment E η cbar) := by
  refine lt_of_le_of_ne (indexed_le_insurance E U hη0 hη1 hr hD hc hP) fun heq => ?_
  obtain ⟨hP0, hPm, hPic⟩ := hP
  have hcons : ∀ s, resources E r D s - P s = consumption E (fun t => P t - (1 + r) * D) s :=
    fun s => by unfold resources consumption Endowment.Y; ring
  have hZP : ZeroProfit E (fun t => P t - (1 + r) * D) := by
    unfold ZeroProfit
    rw [show (fun t => P t - (1 + r) * D) = fun t => P t - (fun _ => (1 + r) * D) t from rfl,
      expect_sub, E.Ω.expect_const, hPm, sub_self]
  have hIC : SanctionIC E η (fun t => P t - (1 + r) * D) := fun s => by
    have := hPic s
    unfold resources at this; unfold Endowment.Y
    have h1 : 0 ≤ (1 - η) * ((1 + r) * D) := mul_nonneg (by linarith) (by nlinarith)
    nlinarith
  have heq' : expectedUtility E U (fun t => P t - (1 + r) * D) =
      expectedUtility E U (optPayment E η cbar) := by
    unfold expectedUtility; simp only [← hcons]; exact heq
  have hsame := ((optimal_ic_contract E U hη0 hη1 hc).2.2 _ hZP hIC).2 heq'
  obtain ⟨s, hs⟩ := hbind
  have hPs : P s - (1 + r) * D = η * E.Y s := by
    have := congrFun hsame s
    rw [this]; unfold optPayment; rw [max_eq_right hs.le]; unfold floorCons; ring
  have hic := hPic s
  unfold resources at hic; unfold Endowment.Y at hPs
  have hD0 : (1 + r) * D = 0 := by
    have : (1 - η) * ((1 + r) * D) ≤ 0 := by nlinarith
    have h1 : 0 ≤ (1 + r) * D := by nlinarith
    nlinarith
  have hPz : ∀ t, P t = 0 := fun t =>
    eq_zero_of_nonneg_of_expect_zero E.Ω hP0 (by rw [hPm, hD0]) (E.prob_pos t)
  rw [hPz s, hD0] at hPs
  have := mul_pos hη0 (E.Y_pos s)
  unfold Endowment.Y at this
  linarith

/-- **Full insurance through indexed debt**, O&R Exercise 2(b): some `D ≥ 0` allows a
feasible indexed-debt schedule with constant consumption `Ȳ` iff
`(1 − η)(ε' − ε) ≤ ηȲ` for all states `ε, ε'`, i.e. iff
`η ≥ (ε̄ − ε_)/(Ȳ + ε̄ − ε_)`. -/
theorem indexed_full_insurance_iff {η r : ℝ} (hη1 : η < 1) (hr : -1 < r) :
    (∃ D, 0 ≤ D ∧ IndexedFeasible E η r D (fun s => (1 + r) * D + E.ε s)) ↔
      ∀ s t, (1 - η) * (E.ε t - E.ε s) ≤ η * E.Ybar := by
  constructor
  · rintro ⟨D, _, hP0, _, hPic⟩ s t
    have h1 := hP0 s
    have h2 := hPic t
    unfold resources at h2
    nlinarith
  · intro h
    have := StateSpaceFacts.nonempty E.Ω
    have hne : (Finset.univ : Finset S).Nonempty := Finset.univ_nonempty
    obtain ⟨s₀, _, hs₀⟩ := Finset.exists_min_image Finset.univ E.ε hne
    -- the lowest shock is nonpositive because `E ε = 0`
    have hs0 : E.ε s₀ ≤ 0 := by
      by_contra hn; push Not at hn
      have hpos : ∀ t, 0 ≤ E.ε t := fun t => le_trans hn.le (hs₀ t (Finset.mem_univ t))
      have := eq_zero_of_nonneg_of_expect_zero E.Ω hpos E.mean_zero (E.prob_pos s₀)
      linarith
    refine ⟨-E.ε s₀ / (1 + r), div_nonneg (by linarith) (by linarith), fun t => ?_, ?_,
      fun t => ?_⟩
    · have := hs₀ t (Finset.mem_univ t)
      rw [mul_div_cancel₀ _ (show (1 : ℝ) + r ≠ 0 by linarith)]; linarith
    · rw [show (fun s => (1 + r) * (-E.ε s₀ / (1 + r)) + E.ε s) =
          fun s => (1 + r) * (-E.ε s₀ / (1 + r)) + E.ε s from rfl, expect_const_add,
        E.mean_zero, add_zero]
    · unfold resources
      rw [mul_div_cancel₀ _ (show (1 : ℝ) + r ≠ 0 by linarith)]
      have := h s₀ t
      nlinarith

/-- **Exercise 2(b), the threshold comparison**, O&R p. 426: for `ε_ < 0 < ε̄`, full
insurance by pure insurance needs `η ≥ ε̄/(Ȳ + ε̄)`, strictly less than the
`(ε̄ − ε_)/(Ȳ + ε̄ − ε_)` needed with indexed debt. -/
theorem threshold_comparison {Ybar elow ehigh : ℝ} (hY : 0 < Ybar) (hlow : elow < 0)
    (hhigh : 0 < ehigh) :
    ehigh / (Ybar + ehigh) < (ehigh - elow) / (Ybar + ehigh - elow) := by
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith

end ObstfeldRogoff.CapitalMarketImperfections.SanctionsWithSaving
