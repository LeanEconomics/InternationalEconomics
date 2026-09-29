/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NominalRigidities.BarroGordon
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Reputational equilibria in the Barro–Gordon model

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §9.5.1.4
(pp. 639–641), eqs. (37)–(39) and footnotes 28–29.

The repeated game is modelled on **histories**. A history is the list (newest first) of past
triples `(π, πᵉ, s)` (inflation, expected inflation, shock state). Shocks are iid on a finite
state space `S` with probabilities `p` and `E z = 0`; the deterministic game of (38) is the
case `S = Unit`, `z = 0`. Private expectations are a function `ε` of the history; the
central bank's strategy `σ h s` chooses inflation after seeing the history and the current
shock. The expected present value (37) of the loss from a history `h` is the limit of the
`N`-period expected costs `truncCost N h`, defined recursively over the event tree, which
are nondecreasing in `N` (losses are nonnegative), so every strategy either has a finite
expected present value or an infinite one (`truncCost_tendsto_or_atTop`).

An equilibrium (`IsReputationEqm`) requires rational expectations at **every** history and
optimality of `σ` against **every** alternative strategy at **every** history.

* A general verification theorem: a bounded `W` satisfying the Bellman equality for `σ` and
  the Bellman inequality for all actions is the value of `σ` and a lower bound for every
  strategy (`truncCost_lower`, `tendsto_truncCost_of_bellman_eq`).
* (38)/(39) trigger strategies with an arbitrary target `π̄` (T16–T18): the trigger
  equilibrium exists **iff** `(k − χπ̄)²/(1 + χ) ≤ β/(1 − β)·(k²/χ − χπ̄²)`
  (`trigger_eqm_iff`), i.e. iff `π̄ ∈ [π̲(β), k/χ]` with
  `π̲(β) = k(χ − β(1 + 2χ))/(χ(χ + β))` (`trigger_eqm_iff_bounds`). Zero inflation (with the
  commitment rule `z/(1 + χ)` on the path under shocks) is sustainable iff
  `β ≥ χ/(1 + 2χ)` (`trigger_zero_iff`, `trigger_deterministic_iff` for (38)); negative
  rates iff `β > χ/(1 + 2χ)`; `π̲(β) → −k/χ` as `β → 1`; the one-shot outcome is always an
  equilibrium (p. 641 multiplicity).
* Footnote 29, one-period punishments: exact sustainable set
  `[k(χ − β(1 + χ))/(χ(χ + β(1 + χ))), k/χ]`, which always contains rates below `k/χ`.
* Finite horizon (pp. 640–641, T19): in every subgame-perfect equilibrium of the `T`-period
  game, `πᵉ = k/χ` and `π = k/χ + z/(1 + χ)` at every history (backward induction), and this
  profile is an equilibrium.
-/

namespace ObstfeldRogoff.NominalRigidities.ReputationEquilibria

open Filter Topology
open ObstfeldRogoff.NominalRigidities.BarroGordon

variable {S : Type*} [Fintype S]

/-- O&R §9.5.1.4: a history, the list (newest first) of past `(π, πᵉ, shock state)`. -/
abbrev Hist (S : Type*) := List (ℝ × ℝ × S)

/-- O&R (37), p. 639: the `N`-period expected discounted loss from history `h` when
expectations follow `ε` and the bank follows `σ`, computed recursively over the event tree
of iid shocks. -/
noncomputable def truncCost (p z : S → ℝ) (β χ k : ℝ) (ε : Hist S → ℝ)
    (σ : Hist S → S → ℝ) : ℕ → Hist S → ℝ
  | 0, _ => 0
  | N + 1, h => ∑ s, p s * (bgLoss χ k (σ h s) (ε h) (z s) +
      β * truncCost p z β χ k ε σ N ((σ h s, ε h, s) :: h))

/-- O&R (37): the Bellman operator: expected current loss of the action rule `a` at `h`
plus the discounted continuation value `W`. -/
noncomputable def bellman (p z : S → ℝ) (β χ k : ℝ) (ε : Hist S → ℝ) (W : Hist S → ℝ)
    (h : Hist S) (a : S → ℝ) : ℝ :=
  ∑ s, p s * (bgLoss χ k (a s) (ε h) (z s) + β * W ((a s, ε h, s) :: h))

/-- O&R (37): one step of the recursion is the Bellman operator applied to the shorter
horizon. -/
theorem truncCost_succ (p z : S → ℝ) (β χ k : ℝ) (ε : Hist S → ℝ) (σ : Hist S → S → ℝ)
    (N : ℕ) (h : Hist S) :
    truncCost p z β χ k ε σ (N + 1) h =
      bellman p z β χ k ε (truncCost p z β χ k ε σ N) h (σ h) := rfl

/-- O&R (37): the Bellman operator is an expectation. -/
theorem bellman_eq_expect (p z : S → ℝ) (β χ k : ℝ) (ε W : Hist S → ℝ) (h : Hist S)
    (a : S → ℝ) :
    bellman p z β χ k ε W h a =
      expect p (fun s => bgLoss χ k (a s) (ε h) (z s) + β * W ((a s, ε h, s) :: h)) := rfl

/-- O&R (37): the expected present value of the loss from `h` is `J`: the truncated costs
converge to `J`. -/
def HasExpPV (p z : S → ℝ) (β χ k : ℝ) (ε : Hist S → ℝ) (σ : Hist S → S → ℝ) (h : Hist S)
    (J : ℝ) : Prop :=
  Tendsto (fun N => truncCost p z β χ k ε σ N h) atTop (𝓝 J)

/-- O&R §9.5.1.4 (38)–(39): a reputational equilibrium: expectations are rational at every
history, and at every history the bank's strategy has a finite expected present value of
loss that no alternative strategy beats. -/
def IsReputationEqm (p z : S → ℝ) (β χ k : ℝ) (ε : Hist S → ℝ) (σ : Hist S → S → ℝ) :
    Prop :=
  (∀ h, ε h = expect p (σ h)) ∧
    ∀ h, ∃ J, HasExpPV p z β χ k ε σ h J ∧
      ∀ σ' J', HasExpPV p z β χ k ε σ' h J' → J ≤ J'

/-! ## General theory: monotonicity and verification -/

/-- O&R (37): nonnegative losses make the truncated costs nondecreasing in the horizon. -/
theorem truncCost_le_succ (p z : S → ℝ) (β χ k : ℝ) (hp : ∀ s, 0 ≤ p s) (hβ : 0 ≤ β)
    (hχ : 0 ≤ χ) (ε : Hist S → ℝ) (σ : Hist S → S → ℝ) :
    ∀ N h, truncCost p z β χ k ε σ N h ≤ truncCost p z β χ k ε σ (N + 1) h := by
  intro N
  induction N with
  | zero =>
    intro h
    simp only [truncCost, mul_zero, add_zero]
    exact Finset.sum_nonneg fun s _ =>
      mul_nonneg (hp s) (add_nonneg (sq_nonneg _) (mul_nonneg hχ (sq_nonneg _)))
  | succ N ih =>
    intro h
    rw [truncCost_succ, truncCost_succ (N := N + 1)]
    exact Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left
      (add_le_add_right (mul_le_mul_of_nonneg_left (ih _) hβ) _) (hp s)

/-- O&R (37): every strategy has either a finite expected present value of loss or an
infinite one (monotone convergence). -/
theorem truncCost_tendsto_or_atTop (p z : S → ℝ) (β χ k : ℝ) (hp : ∀ s, 0 ≤ p s)
    (hβ : 0 ≤ β) (hχ : 0 ≤ χ) (ε : Hist S → ℝ) (σ : Hist S → S → ℝ) (h : Hist S) :
    Tendsto (fun N => truncCost p z β χ k ε σ N h) atTop atTop ∨
      ∃ J, HasExpPV p z β χ k ε σ h J :=
  tendsto_atTop_of_monotone
    (monotone_nat_of_le_succ fun N => truncCost_le_succ p z β χ k hp hβ hχ ε σ N h)

/-- O&R (37), verification (lower bound): if `W ≤ W̄` and `W` satisfies the Bellman
inequality for every action rule, then every strategy's `N`-period cost is at least
`W h − βᴺ W̄`. -/
theorem truncCost_lower (p z : S → ℝ) (β χ k : ℝ) (hp : ∀ s, 0 ≤ p s) (h1 : ∑ s, p s = 1)
    (hβ : 0 ≤ β) (ε W : Hist S → ℝ) (Wbar : ℝ) (hW : ∀ h, W h ≤ Wbar)
    (hbell : ∀ h a, W h ≤ bellman p z β χ k ε W h a) (σ : Hist S → S → ℝ) :
    ∀ N h, W h - β ^ N * Wbar ≤ truncCost p z β χ k ε σ N h := by
  intro N
  induction N with
  | zero =>
    intro h
    simp only [pow_zero, one_mul, truncCost]
    linarith [hW h]
  | succ N ih =>
    intro h
    have hb := hbell h (σ h)
    have key : bellman p z β χ k ε W h (σ h) - β ^ (N + 1) * Wbar =
        ∑ s, p s * (bgLoss χ k (σ h s) (ε h) (z s) +
          β * (W ((σ h s, ε h, s) :: h) - β ^ N * Wbar)) := by
      have e : β ^ (N + 1) * Wbar = ∑ s, p s * (β * (β ^ N * Wbar)) := by
        rw [← Finset.sum_mul, h1]
        ring
      rw [e, bellman, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun s _ => by ring
    rw [truncCost_succ]
    have : ∑ s, p s * (bgLoss χ k (σ h s) (ε h) (z s) +
          β * (W ((σ h s, ε h, s) :: h) - β ^ N * Wbar)) ≤
        bellman p z β χ k ε (truncCost p z β χ k ε σ N) h (σ h) :=
      Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left
        (add_le_add_right (mul_le_mul_of_nonneg_left (ih _) hβ) _) (hp s)
    linarith

/-- O&R (37), verification (evaluation): if `|W| ≤ W̄` and `W` satisfies the Bellman equality
for `σ`, then `|truncCost N h − W h| ≤ βᴺ W̄`. -/
theorem truncCost_eval (p z : S → ℝ) (β χ k : ℝ) (hp : ∀ s, 0 ≤ p s) (h1 : ∑ s, p s = 1)
    (hβ : 0 ≤ β) (ε W : Hist S → ℝ) (Wbar : ℝ) (hW : ∀ h, |W h| ≤ Wbar)
    (σ : Hist S → S → ℝ) (heq : ∀ h, bellman p z β χ k ε W h (σ h) = W h) :
    ∀ N h, |truncCost p z β χ k ε σ N h - W h| ≤ β ^ N * Wbar := by
  intro N
  induction N with
  | zero =>
    intro h
    simpa [truncCost] using hW h
  | succ N ih =>
    intro h
    have key : truncCost p z β χ k ε σ (N + 1) h - W h =
        ∑ s, p s * (β * (truncCost p z β χ k ε σ N ((σ h s, ε h, s) :: h) -
          W ((σ h s, ε h, s) :: h))) := by
      rw [truncCost_succ, ← heq h, bellman, bellman, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun s _ => by ring
    rw [key]
    calc |∑ s, p s * (β * (truncCost p z β χ k ε σ N ((σ h s, ε h, s) :: h) -
          W ((σ h s, ε h, s) :: h)))|
        ≤ ∑ s, |p s * (β * (truncCost p z β χ k ε σ N ((σ h s, ε h, s) :: h) -
          W ((σ h s, ε h, s) :: h)))| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ s, p s * (β * (β ^ N * Wbar)) := by
        refine Finset.sum_le_sum fun s _ => ?_
        rw [abs_mul, abs_mul, abs_of_nonneg (hp s), abs_of_nonneg hβ]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (ih _) hβ) (hp s)
      _ = β ^ (N + 1) * Wbar := by
        rw [← Finset.sum_mul, h1]
        ring

/-- O&R (37): a bounded solution of the Bellman equality for `σ` is `σ`'s expected present
value of loss (`0 ≤ β < 1`). -/
theorem tendsto_truncCost_of_bellman_eq (p z : S → ℝ) (β χ k : ℝ) (hp : ∀ s, 0 ≤ p s)
    (h1 : ∑ s, p s = 1) (hβ : 0 ≤ β) (hβ1 : β < 1) (ε W : Hist S → ℝ) (Wbar : ℝ)
    (hW : ∀ h, |W h| ≤ Wbar) (σ : Hist S → S → ℝ)
    (heq : ∀ h, bellman p z β χ k ε W h (σ h) = W h) (h : Hist S) :
    HasExpPV p z β χ k ε σ h (W h) := by
  have hev := truncCost_eval p z β χ k hp h1 hβ ε W Wbar hW σ heq
  have hlim : Tendsto (fun N : ℕ => β ^ N * Wbar) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ hβ1).mul_const Wbar
  have hlo : Tendsto (fun N : ℕ => W h - β ^ N * Wbar) atTop (𝓝 (W h)) := by
    simpa using hlim.const_sub (W h)
  have hhi : Tendsto (fun N : ℕ => W h + β ^ N * Wbar) atTop (𝓝 (W h)) := by
    simpa using hlim.const_add (W h)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hhi (fun N => ?_) (fun N => ?_)
  · have := (abs_le.1 (hev N h)).1
    linarith
  · have := (abs_le.1 (hev N h)).2
    linarith

/-- O&R (37): under the Bellman inequality, no strategy has an expected present value of
loss below `W h` (`0 ≤ β < 1`). -/
theorem le_of_hasExpPV_of_bellman_le (p z : S → ℝ) (β χ k : ℝ) (hp : ∀ s, 0 ≤ p s)
    (h1 : ∑ s, p s = 1) (hβ : 0 ≤ β) (hβ1 : β < 1) (ε W : Hist S → ℝ) (Wbar : ℝ)
    (hW : ∀ h, W h ≤ Wbar) (hbell : ∀ h a, W h ≤ bellman p z β χ k ε W h a)
    (σ : Hist S → S → ℝ) (h : Hist S) (J : ℝ) (hJ : HasExpPV p z β χ k ε σ h J) :
    W h ≤ J := by
  have hlim : Tendsto (fun N : ℕ => β ^ N * Wbar) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ hβ1).mul_const Wbar
  have hlo : Tendsto (fun N : ℕ => W h - β ^ N * Wbar) atTop (𝓝 (W h)) := by
    simpa using hlim.const_sub (W h)
  exact le_of_tendsto_of_tendsto' hlo hJ fun N =>
    truncCost_lower p z β χ k hp h1 hβ ε W Wbar hW hbell σ N h

/-- O&R §9.5.1.4, verification theorem: rational expectations, a bounded `W`, the Bellman
equality for `σ` and the Bellman inequality for all action rules make `(ε, σ)` a
reputational equilibrium. -/
theorem isReputationEqm_of_bellman (p z : S → ℝ) (β χ k : ℝ) (hp : ∀ s, 0 ≤ p s)
    (h1 : ∑ s, p s = 1) (hβ : 0 ≤ β) (hβ1 : β < 1) (ε W : Hist S → ℝ) (Wbar : ℝ)
    (hW : ∀ h, |W h| ≤ Wbar) (σ : Hist S → S → ℝ) (hre : ∀ h, ε h = expect p (σ h))
    (heq : ∀ h, bellman p z β χ k ε W h (σ h) = W h)
    (hbell : ∀ h a, W h ≤ bellman p z β χ k ε W h a) :
    IsReputationEqm p z β χ k ε σ := by
  refine ⟨hre, fun h => ⟨W h,
    tendsto_truncCost_of_bellman_eq p z β χ k hp h1 hβ hβ1 ε W Wbar hW σ heq h,
    fun σ' J' hJ' => ?_⟩⟩
  exact le_of_hasExpPV_of_bellman_le p z β χ k hp h1 hβ hβ1 ε W Wbar
    (fun g => (abs_le.1 (hW g)).2) hbell σ' h J' hJ'

/-- O&R §9.5.1.4: a strategy is not an equilibrium strategy if at some history some
alternative strategy has a strictly smaller expected present value of loss. -/
theorem not_isReputationEqm_of_better (p z : S → ℝ) (β χ k : ℝ) (ε : Hist S → ℝ)
    (σ σ' : Hist S → S → ℝ) (h : Hist S) (J J' : ℝ) (hJ : HasExpPV p z β χ k ε σ h J)
    (hJ' : HasExpPV p z β χ k ε σ' h J') (hlt : J' < J) :
    ¬ IsReputationEqm p z β χ k ε σ := by
  rintro ⟨_, hopt⟩
  obtain ⟨J0, hJ0, hle⟩ := hopt h
  have := tendsto_nhds_unique hJ0 hJ
  have := hle σ' J' hJ'
  linarith

/-! ## One-shot deviations at the initial history -/

/-- O&R p. 640: the strategy that plays the action rule `d` at the empty history and follows
`σ` everywhere else. -/
def rootDev (d : S → ℝ) (σ : Hist S → S → ℝ) : Hist S → S → ℝ
  | [], s => d s
  | x :: t, s => σ (x :: t) s

/-- O&R p. 640: the value function equal to `A` at the empty history and to `W` elsewhere. -/
def rootVal (A : ℝ) (W : Hist S → ℝ) : Hist S → ℝ
  | [] => A
  | x :: t => W (x :: t)

/-- O&R p. 640: if `W` solves the Bellman equality for `σ`, then deviating to `d` at the
empty history and following `σ` afterwards has expected present value `bellman W [] d`. -/
theorem hasExpPV_rootDev (p z : S → ℝ) (β χ k : ℝ) (hp : ∀ s, 0 ≤ p s)
    (h1 : ∑ s, p s = 1) (hβ : 0 ≤ β) (hβ1 : β < 1) (ε W : Hist S → ℝ) (Wbar : ℝ)
    (hW : ∀ h, |W h| ≤ Wbar) (σ : Hist S → S → ℝ)
    (heq : ∀ h, bellman p z β χ k ε W h (σ h) = W h) (d : S → ℝ) :
    HasExpPV p z β χ k ε (rootDev d σ) [] (bellman p z β χ k ε W [] d) := by
  set A := bellman p z β χ k ε W [] d
  have hW' : ∀ h, |rootVal A W h| ≤ Wbar + |A| := by
    intro h
    cases h with
    | nil =>
      simp only [rootVal]
      linarith [abs_nonneg (W []), hW []]
    | cons x t =>
      simp only [rootVal]
      linarith [hW (x :: t), abs_nonneg A]
  have heq' : ∀ h, bellman p z β χ k ε (rootVal A W) h (rootDev d σ h) = rootVal A W h := by
    intro h
    cases h with
    | nil => rfl
    | cons x t => exact heq (x :: t)
  exact tendsto_truncCost_of_bellman_eq p z β χ k hp h1 hβ hβ1 ε (rootVal A W) (Wbar + |A|)
    hW' (rootDev d σ) heq' []

/-! ## Stage losses -/

/-- O&R p. 640: the minimised one-period loss given expectations `e` and shock `zz`,
`χ(k + e + zz)²/(1 + χ)`. -/
noncomputable def minLoss (χ k e zz : ℝ) : ℝ := χ * (k + e + zz) ^ 2 / (1 + χ)

/-- O&R p. 640: every action loses at least `minLoss`. -/
theorem minLoss_le (χ k a e zz : ℝ) (hχ : 0 < 1 + χ) : minLoss χ k e zz ≤ bgLoss χ k a e zz := by
  have := bestResponse_isMin χ k a e zz hχ
  rwa [bgLoss_bestResponse χ k e zz hχ] at this

/-- O&R (39): the on-path loss of the trigger rule with target `π̄`: `π = π̄ + z/(1 + χ)`. -/
noncomputable def onLoss (χ k πbar zz : ℝ) : ℝ := bgLoss χ k (πbar + zz / (1 + χ)) πbar zz

/-- O&R p. 640 and (39): the one-period gain from cheating, `onLoss − minLoss`, is
`(k − χπ̄)²/(1 + χ)`, **independent of the shock** (for `π̄ = 0`, the book's `k²/(1 + χ)`). -/
theorem onLoss_sub_minLoss (χ k πbar zz : ℝ) (hχ : 0 < 1 + χ) :
    onLoss χ k πbar zz - minLoss χ k πbar zz = (k - χ * πbar) ^ 2 / (1 + χ) := by
  unfold onLoss minLoss bgLoss
  field_simp
  ring

/-- O&R (39): the expected on-path loss, `k² + χπ̄² + χσ²/(1 + χ)`. -/
noncomputable def valueOn (χ k σ2 πbar : ℝ) : ℝ := k ^ 2 + χ * πbar ^ 2 + χ * σ2 / (1 + χ)

/-- O&R (39): `E onLoss = k² + χπ̄² + χσ²/(1 + χ)`. -/
theorem expect_onLoss (p z : S → ℝ) (χ k πbar : ℝ) (hχ : 0 < 1 + χ) (h1 : ∑ s, p s = 1)
    (hz : expect p z = 0) :
    expect p (fun s => onLoss χ k πbar (z s)) = valueOn χ k (varZ p z) πbar := by
  unfold expect at hz ⊢
  unfold valueOn varZ expect
  have : ∑ s, p s * onLoss χ k πbar (z s) = ∑ s, (p s * (k ^ 2 + χ * πbar ^ 2) +
      (2 * k * χ + 2 * χ * πbar) / (1 + χ) * (p s * z s) +
        χ / (1 + χ) * (p s * z s ^ 2)) := by
    refine Finset.sum_congr rfl fun s _ => ?_
    unfold onLoss bgLoss
    field_simp
    ring
  rw [this, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
    ← Finset.mul_sum, h1, hz]
  ring

/-- O&R (35), fn 28: at `π̄ = k/χ` the on-path value is the discretionary value `V_D`. -/
theorem valueOn_discretion (χ k σ2 : ℝ) (hχ : 0 < χ) :
    valueOn χ k σ2 (k / χ) = valueDiscretion χ k σ2 := by
  unfold valueOn valueDiscretion
  field_simp

/-- O&R p. 640: the per-period punishment cost `V_D − V_on = k²/χ − χπ̄²` (the book's
`k²/χ` at `π̄ = 0`). -/
theorem valueDiscretion_sub_valueOn (χ k σ2 πbar : ℝ) :
    valueDiscretion χ k σ2 - valueOn χ k σ2 πbar = k ^ 2 / χ - χ * πbar ^ 2 := by
  unfold valueDiscretion valueOn
  ring

/-- O&R fn 28: in the punishment phase the best response to `πᵉ = k/χ` is
`k/χ + z/(1 + χ)`, and its loss is the minimum. -/
theorem onLoss_discretion (χ k zz : ℝ) (hχ : 0 < χ) :
    onLoss χ k (k / χ) zz = minLoss χ k (k / χ) zz := by
  have h := onLoss_sub_minLoss χ k (k / χ) zz (by linarith)
  have : k - χ * (k / χ) = 0 := by field_simp; ring
  rw [this] at h
  simp at h
  linarith

/-- O&R p. 640: the best response to `π̄` coincides with the trigger action iff `k = χπ̄`. -/
theorem bestResponse_eq_onPath_iff (χ k πbar zz : ℝ) (hχ : 0 < 1 + χ) :
    bestResponse χ k πbar zz = πbar + zz / (1 + χ) ↔ k = χ * πbar := by
  unfold bestResponse
  rw [div_eq_iff hχ.ne']
  constructor
  · intro h
    field_simp at h
    linarith
  · intro h
    field_simp
    linarith

/-! ## Infinite-punishment trigger strategies, (38)–(39) -/

/-- O&R (38)–(39): no past period had a surprise, `π = πᵉ + z/(1 + χ)` at every past date. -/
def NoSurprise (χ : ℝ) (z : S → ℝ) (h : Hist S) : Prop :=
  ∀ x ∈ h, x.1 = x.2.1 + z x.2.2 / (1 + χ)

omit [Fintype S] in
/-- O&R (38): the empty history has no surprise. -/
theorem noSurprise_nil (χ : ℝ) (z : S → ℝ) : NoSurprise χ z ([] : Hist S) := by
  simp [NoSurprise]

omit [Fintype S] in
/-- O&R (38): extending a history. -/
theorem noSurprise_cons_iff (χ : ℝ) (z : S → ℝ) (x : ℝ × ℝ × S) (h : Hist S) :
    NoSurprise χ z (x :: h) ↔ x.1 = x.2.1 + z x.2.2 / (1 + χ) ∧ NoSurprise χ z h := by
  simp [NoSurprise]

/-- O&R (38)–(39): trigger expectations with target `π̄`: `π̄` after surprise-free histories,
the one-shot level `k/χ` forever after any surprise. -/
noncomputable def trigExp (χ k πbar : ℝ) (z : S → ℝ) (h : Hist S) : ℝ := by
  classical exact if NoSurprise χ z h then πbar else k / χ

/-- O&R (39), fn 28: the bank's trigger strategy: `π̄ + z/(1 + χ)` after surprise-free
histories, the one-shot best response `k/χ + z/(1 + χ)` in punishment. -/
noncomputable def trigCB (χ k πbar : ℝ) (z : S → ℝ) (h : Hist S) (s : S) : ℝ := by
  classical exact if NoSurprise χ z h then πbar + z s / (1 + χ) else k / χ + z s / (1 + χ)

/-- O&R (38): the value of the trigger profile: `V_on/(1 − β)` or `V_D/(1 − β)`. -/
noncomputable def trigVal (p z : S → ℝ) (β χ k πbar : ℝ) (h : Hist S) : ℝ := by
  classical exact if NoSurprise χ z h then valueOn χ k (varZ p z) πbar / (1 - β)
    else valueOn χ k (varZ p z) (k / χ) / (1 - β)

/-- O&R p. 640: the equilibrium condition `gain ≤ β/(1 − β)·punishment cost`. -/
def TriggerCond (χ k β πbar : ℝ) : Prop :=
  (k - χ * πbar) ^ 2 / (1 + χ) ≤ β / (1 - β) * (k ^ 2 / χ - χ * πbar ^ 2)

omit [Fintype S] in
/-- O&R (38)–(39): expectations after a surprise-free history. -/
theorem trigExp_pos (χ k πbar : ℝ) (z : S → ℝ) (h : Hist S) (hns : NoSurprise χ z h) :
    trigExp χ k πbar z h = πbar := by
  unfold trigExp
  simp [hns]

omit [Fintype S] in
/-- O&R (38)–(39): expectations after a surprise. -/
theorem trigExp_neg (χ k πbar : ℝ) (z : S → ℝ) (h : Hist S) (hns : ¬ NoSurprise χ z h) :
    trigExp χ k πbar z h = k / χ := by
  unfold trigExp
  simp [hns]

omit [Fintype S] in
/-- O&R (39): the bank's play after a surprise-free history. -/
theorem trigCB_pos (χ k πbar : ℝ) (z : S → ℝ) (h : Hist S) (hns : NoSurprise χ z h) (s : S) :
    trigCB χ k πbar z h s = πbar + z s / (1 + χ) := by
  unfold trigCB
  simp [hns]

omit [Fintype S] in
/-- O&R fn 28: the bank's play in punishment. -/
theorem trigCB_neg (χ k πbar : ℝ) (z : S → ℝ) (h : Hist S) (hns : ¬ NoSurprise χ z h)
    (s : S) : trigCB χ k πbar z h s = k / χ + z s / (1 + χ) := by
  unfold trigCB
  simp [hns]

/-- O&R (38): the trigger value after a surprise-free history. -/
theorem trigVal_pos (p z : S → ℝ) (β χ k πbar : ℝ) (h : Hist S) (hns : NoSurprise χ z h) :
    trigVal p z β χ k πbar h = valueOn χ k (varZ p z) πbar / (1 - β) := by
  unfold trigVal
  simp [hns]

/-- O&R (38): the trigger value in punishment. -/
theorem trigVal_neg (p z : S → ℝ) (β χ k πbar : ℝ) (h : Hist S) (hns : ¬ NoSurprise χ z h) :
    trigVal p z β χ k πbar h = valueOn χ k (varZ p z) (k / χ) / (1 - β) := by
  unfold trigVal
  simp [hns]

/-- O&R (39): the rule `c + z/(1 + χ)` has mean `c` (as `E z = 0`). -/
theorem expect_const_add_shock (p z : S → ℝ) (χ c : ℝ) (h1 : ∑ s, p s = 1)
    (hz : expect p z = 0) : expect p (fun s => c + z s / (1 + χ)) = c := by
  have : expect p (fun s => c + z s / (1 + χ)) =
      expect p (fun s => c + (1 / (1 + χ)) * z s) := by
    unfold expect
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [this, expect_add, expect_const p h1, expect_const_mul, hz, mul_zero, add_zero]

/-- Pointwise equal integrands have equal expectations (O&R §9.5.1). -/
theorem expect_congr' (p f g : S → ℝ) (hfg : ∀ s, f s = g s) : expect p f = expect p g := by
  rw [funext hfg]

/-- O&R (38): expectations are rational at every history under the trigger profile. -/
theorem trig_rational (p z : S → ℝ) (χ k πbar : ℝ) (h1 : ∑ s, p s = 1) (hz : expect p z = 0)
    (h : Hist S) : trigExp χ k πbar z h = expect p (trigCB χ k πbar z h) := by
  by_cases hns : NoSurprise χ z h
  · rw [trigExp_pos χ k πbar z h hns, funext (trigCB_pos χ k πbar z h hns),
      expect_const_add_shock p z χ πbar h1 hz]
  · rw [trigExp_neg χ k πbar z h hns, funext (trigCB_neg χ k πbar z h hns),
      expect_const_add_shock p z χ _ h1 hz]

/-- Arithmetic behind O&R p. 640: `V/(1 − β) = V + β·V/(1 − β)`. -/
theorem div_one_sub_eq (V β : ℝ) (hβ1 : β < 1) : V / (1 - β) = V + β * (V / (1 - β)) := by
  have : (1 - β) ≠ 0 := by linarith
  field_simp
  ring

/-- O&R (38)–(39): the trigger value satisfies the Bellman equality for the trigger
strategy at every history. -/
theorem trig_bellman_eq (p z : S → ℝ) (β χ k πbar : ℝ) (hχ : 0 < χ) (hβ1 : β < 1)
    (h1 : ∑ s, p s = 1) (hz : expect p z = 0) (h : Hist S) :
    bellman p z β χ k (trigExp χ k πbar z) (trigVal p z β χ k πbar) h
      (trigCB χ k πbar z h) = trigVal p z β χ k πbar h := by
  have hχ1 : 0 < 1 + χ := by linarith
  rw [bellman_eq_expect]
  by_cases hns : NoSurprise χ z h
  · have hpt : ∀ s, bgLoss χ k (trigCB χ k πbar z h s) (trigExp χ k πbar z h) (z s) +
        β * trigVal p z β χ k πbar ((trigCB χ k πbar z h s, trigExp χ k πbar z h, s) :: h) =
        onLoss χ k πbar (z s) + β * (valueOn χ k (varZ p z) πbar / (1 - β)) := by
      intro s
      have hn : NoSurprise χ z ((πbar + z s / (1 + χ), πbar, s) :: h) :=
        (noSurprise_cons_iff χ z _ h).2 ⟨rfl, hns⟩
      rw [trigCB_pos χ k πbar z h hns, trigExp_pos χ k πbar z h hns,
        trigVal_pos p z β χ k πbar _ hn]
      rfl
    rw [expect_congr' p _ _ hpt, expect_add, expect_onLoss p z χ k πbar hχ1 h1 hz,
      expect_const p h1, trigVal_pos p z β χ k πbar h hns]
    exact (div_one_sub_eq _ β hβ1).symm
  · have hpt : ∀ s, bgLoss χ k (trigCB χ k πbar z h s) (trigExp χ k πbar z h) (z s) +
        β * trigVal p z β χ k πbar ((trigCB χ k πbar z h s, trigExp χ k πbar z h, s) :: h) =
        onLoss χ k (k / χ) (z s) + β * (valueOn χ k (varZ p z) (k / χ) / (1 - β)) := by
      intro s
      have hn : ¬ NoSurprise χ z ((trigCB χ k πbar z h s, trigExp χ k πbar z h, s) :: h) :=
        fun hc => hns ((noSurprise_cons_iff χ z _ h).1 hc).2
      rw [trigVal_neg p z β χ k πbar _ hn, trigCB_neg χ k πbar z h hns,
        trigExp_neg χ k πbar z h hns]
      rfl
    rw [expect_congr' p _ _ hpt, expect_add, expect_onLoss p z χ k (k / χ) hχ1 h1 hz,
      expect_const p h1, trigVal_neg p z β χ k πbar h hns]
    exact (div_one_sub_eq _ β hβ1).symm

/-- O&R p. 640: `β·W_D − β·W_on = β/(1 − β)·(k²/χ − χπ̄²)`. -/
theorem beta_val_diff (p z : S → ℝ) (β χ k πbar : ℝ) (hχ : 0 < χ) (hβ1 : β < 1) :
    β * (valueOn χ k (varZ p z) (k / χ) / (1 - β)) -
      β * (valueOn χ k (varZ p z) πbar / (1 - β)) =
      β / (1 - β) * (k ^ 2 / χ - χ * πbar ^ 2) := by
  have hc2 := valueDiscretion_sub_valueOn χ k (varZ p z) πbar
  rw [← valueOn_discretion χ k (varZ p z) hχ] at hc2
  rw [← hc2]
  have : (1 - β) ≠ 0 := by linarith
  field_simp

/-- O&R p. 640: under the condition `gain ≤ β/(1 − β)·cost`, the trigger value satisfies the
Bellman inequality for every action rule at every history (no deviation plan pays). -/
theorem trig_bellman_le (p z : S → ℝ) (β χ k πbar : ℝ) (hχ : 0 < χ) (hβ1 : β < 1)
    (hp : ∀ s, 0 ≤ p s) (h1 : ∑ s, p s = 1) (hz : expect p z = 0)
    (hcond : TriggerCond χ k β πbar) (h : Hist S) (a : S → ℝ) :
    trigVal p z β χ k πbar h ≤
      bellman p z β χ k (trigExp χ k πbar z) (trigVal p z β χ k πbar) h a := by
  have hχ1 : 0 < 1 + χ := by linarith
  rw [bellman_eq_expect]
  by_cases hns : NoSurprise χ z h
  · have hpt : ∀ s, onLoss χ k πbar (z s) + β * (valueOn χ k (varZ p z) πbar / (1 - β)) ≤
        bgLoss χ k (a s) (trigExp χ k πbar z h) (z s) +
          β * trigVal p z β χ k πbar ((a s, trigExp χ k πbar z h, s) :: h) := by
      intro s
      rw [trigExp_pos χ k πbar z h hns]
      by_cases ha : a s = πbar + z s / (1 + χ)
      · have hn : NoSurprise χ z ((a s, πbar, s) :: h) :=
          (noSurprise_cons_iff χ z _ h).2 ⟨ha, hns⟩
        rw [trigVal_pos p z β χ k πbar _ hn, ha]
        rfl
      · have hn : ¬ NoSurprise χ z ((a s, πbar, s) :: h) := fun hc =>
          ha ((noSurprise_cons_iff χ z _ h).1 hc).1
        rw [trigVal_neg p z β χ k πbar _ hn]
        have hm := minLoss_le χ k (a s) πbar (z s) hχ1
        have hg := onLoss_sub_minLoss χ k πbar (z s) hχ1
        have e := beta_val_diff p z β χ k πbar hχ hβ1
        unfold TriggerCond at hcond
        linarith
    calc trigVal p z β χ k πbar h
        = expect p (fun s => onLoss χ k πbar (z s) +
            β * (valueOn χ k (varZ p z) πbar / (1 - β))) := by
          rw [expect_add, expect_onLoss p z χ k πbar hχ1 h1 hz, expect_const p h1,
            trigVal_pos p z β χ k πbar h hns]
          exact div_one_sub_eq _ β hβ1
      _ ≤ _ := expect_mono p _ _ hp hpt
  · have hpt : ∀ s, onLoss χ k (k / χ) (z s) +
        β * (valueOn χ k (varZ p z) (k / χ) / (1 - β)) ≤
        bgLoss χ k (a s) (trigExp χ k πbar z h) (z s) +
          β * trigVal p z β χ k πbar ((a s, trigExp χ k πbar z h, s) :: h) := by
      intro s
      have hn : ¬ NoSurprise χ z ((a s, trigExp χ k πbar z h, s) :: h) := fun hc =>
        hns ((noSurprise_cons_iff χ z _ h).1 hc).2
      rw [trigVal_neg p z β χ k πbar _ hn, trigExp_neg χ k πbar z h hns,
        onLoss_discretion χ k (z s) hχ]
      linarith [minLoss_le χ k (a s) (k / χ) (z s) hχ1]
    calc trigVal p z β χ k πbar h
        = expect p (fun s => onLoss χ k (k / χ) (z s) +
            β * (valueOn χ k (varZ p z) (k / χ) / (1 - β))) := by
          rw [expect_add, expect_onLoss p z χ k (k / χ) hχ1 h1 hz, expect_const p h1,
            trigVal_neg p z β χ k πbar h hns]
          exact div_one_sub_eq _ β hβ1
      _ ≤ _ := expect_mono p _ _ hp hpt

/-- O&R (38)–(39): the trigger value is bounded. -/
theorem trigVal_abs_le (p z : S → ℝ) (β χ k πbar : ℝ) (h : Hist S) :
    |trigVal p z β χ k πbar h| ≤ |valueOn χ k (varZ p z) πbar / (1 - β)| +
      |valueOn χ k (varZ p z) (k / χ) / (1 - β)| := by
  by_cases hns : NoSurprise χ z h
  · rw [trigVal_pos p z β χ k πbar h hns]
    linarith [abs_nonneg (valueOn χ k (varZ p z) (k / χ) / (1 - β))]
  · rw [trigVal_neg p z β χ k πbar h hns]
    linarith [abs_nonneg (valueOn χ k (varZ p z) πbar / (1 - β))]

/-- O&R p. 640: the value of cheating once at the empty history (best response `d` to
`π̄`) and being punished forever: `V_on − gain + β·V_D/(1 − β)`, provided `k ≠ χπ̄`. -/
theorem trig_rootDev_value (p z : S → ℝ) (β χ k πbar : ℝ) (hχ : 0 < χ) (h1 : ∑ s, p s = 1)
    (hz : expect p z = 0) (hne : k ≠ χ * πbar) :
    bellman p z β χ k (trigExp χ k πbar z) (trigVal p z β χ k πbar) []
        (fun s => bestResponse χ k πbar (z s)) =
      valueOn χ k (varZ p z) πbar - (k - χ * πbar) ^ 2 / (1 + χ) +
        β * (valueOn χ k (varZ p z) (k / χ) / (1 - β)) := by
  have hχ1 : 0 < 1 + χ := by linarith
  rw [bellman_eq_expect, trigExp_pos χ k πbar z [] (noSurprise_nil χ z)]
  have hpt : ∀ s, bgLoss χ k (bestResponse χ k πbar (z s)) πbar (z s) +
      β * trigVal p z β χ k πbar ((bestResponse χ k πbar (z s), πbar, s) :: []) =
      (onLoss χ k πbar (z s) - (k - χ * πbar) ^ 2 / (1 + χ)) +
        β * (valueOn χ k (varZ p z) (k / χ) / (1 - β)) := by
    intro s
    have hn : ¬ NoSurprise χ z ((bestResponse χ k πbar (z s), πbar, s) :: []) := by
      rw [noSurprise_cons_iff]
      rintro ⟨hc2, -⟩
      exact hne ((bestResponse_eq_onPath_iff χ k πbar (z s) hχ1).1 hc2)
    rw [trigVal_neg p z β χ k πbar _ hn, ← onLoss_sub_minLoss χ k πbar (z s) hχ1,
      bgLoss_bestResponse χ k πbar (z s) hχ1, minLoss]
    ring
  rw [expect_congr' p _ _ hpt, expect_add, expect_sub, expect_onLoss p z χ k πbar hχ1 h1 hz,
    expect_const p h1, expect_const p h1]

/-- O&R (38)–(39), pp. 639–641, and T17 (exact form): the trigger profile with target `π̄`
is a reputational equilibrium **iff** the one-period cheating gain `(k − χπ̄)²/(1 + χ)` is at
most the discounted punishment cost `β/(1 − β)·(k²/χ − χπ̄²)`. -/
theorem trigger_eqm_iff (p z : S → ℝ) (β χ k πbar : ℝ) (hχ : 0 < χ) (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) (hp : ∀ s, 0 ≤ p s) (h1 : ∑ s, p s = 1) (hz : expect p z = 0) :
    IsReputationEqm p z β χ k (trigExp χ k πbar z) (trigCB χ k πbar z) ↔
      TriggerCond χ k β πbar := by
  set Wbar := |valueOn χ k (varZ p z) πbar / (1 - β)| +
      |valueOn χ k (varZ p z) (k / χ) / (1 - β)|
  constructor
  · intro heqm
    by_contra hc
    unfold TriggerCond at hc
    push Not at hc
    have hne : k ≠ χ * πbar := by
      intro hk
      have e1 : k - χ * πbar = 0 := by rw [hk]; ring
      have e2 : k ^ 2 / χ - χ * πbar ^ 2 = 0 := by rw [hk]; field_simp; ring
      rw [e1, e2] at hc
      simp at hc
    have hdev := hasExpPV_rootDev p z β χ k hp h1 hβ0 hβ1 (trigExp χ k πbar z)
      (trigVal p z β χ k πbar) Wbar (trigVal_abs_le p z β χ k πbar) (trigCB χ k πbar z)
      (trig_bellman_eq p z β χ k πbar hχ hβ1 h1 hz) (fun s => bestResponse χ k πbar (z s))
    have htrig := tendsto_truncCost_of_bellman_eq p z β χ k hp h1 hβ0 hβ1 (trigExp χ k πbar z)
      (trigVal p z β χ k πbar) Wbar (trigVal_abs_le p z β χ k πbar) (trigCB χ k πbar z)
      (trig_bellman_eq p z β χ k πbar hχ hβ1 h1 hz) []
    refine not_isReputationEqm_of_better p z β χ k _ _ _ [] _ _ htrig hdev ?_ heqm
    rw [trig_rootDev_value p z β χ k πbar hχ h1 hz hne,
      trigVal_pos p z β χ k πbar [] (noSurprise_nil χ z)]
    have e := div_one_sub_eq (valueOn χ k (varZ p z) πbar) β hβ1
    have e2 := beta_val_diff p z β χ k πbar hχ hβ1
    linarith
  · intro hcond
    exact isReputationEqm_of_bellman p z β χ k hp h1 hβ0 hβ1 (trigExp χ k πbar z)
      (trigVal p z β χ k πbar) Wbar (trigVal_abs_le p z β χ k πbar) (trigCB χ k πbar z)
      (trig_rational p z χ k πbar h1 hz) (trig_bellman_eq p z β χ k πbar hχ hβ1 h1 hz)
      (trig_bellman_le p z β χ k πbar hχ hβ1 hp h1 hz hcond)

/-! ## The exact sustainable set (T17) -/

/-- T17: the lowest sustainable trigger target, `π̲(β) = k(χ − β(1 + 2χ))/(χ(χ + β))`. -/
noncomputable def lowerBound (χ k β : ℝ) : ℝ := k * (χ - β * (1 + 2 * χ)) / (χ * (χ + β))

/-- An elementary fact used for T17: if `x₀ < k`, then `(k − x)(x − x₀) ≥ 0 ↔ x₀ ≤ x ≤ k`. -/
theorem between_iff (x x0 k : ℝ) (h : x0 < k) :
    0 ≤ (k - x) * (x - x0) ↔ x0 ≤ x ∧ x ≤ k := by
  constructor
  · intro hx
    by_contra hc
    rcases not_and_or.1 hc with h2 | h2
    · push Not at h2
      nlinarith
    · push Not at h2
      nlinarith
  · rintro ⟨h2, h3⟩
    exact mul_nonneg (by linarith) (by linarith)

/-- O&R p. 641 and fn 29, T17: for `k > 0`, `χ > 0`, `0 < β < 1`, the trigger condition holds
iff `π̲(β) ≤ π̄ ≤ k/χ`: the sustainable set is exactly the interval `[π̲(β), k/χ]`. -/
theorem triggerCond_iff_bounds (χ k β πbar : ℝ) (hχ : 0 < χ) (hk : 0 < k) (hβ0 : 0 < β)
    (hβ1 : β < 1) :
    TriggerCond χ k β πbar ↔ lowerBound χ k β ≤ πbar ∧ πbar ≤ k / χ := by
  have hχ1 : 0 < 1 + χ := by linarith
  have hD : 0 < 1 - β := by linarith
  have hcb : 0 < χ + β := by linarith
  set x0 := k * (χ - β * (1 + 2 * χ)) / (χ + β) with hx0
  have hx0k : x0 < k := by
    rw [hx0, div_lt_iff₀ hcb]
    nlinarith [mul_pos hk hβ0, mul_pos (mul_pos hk hβ0) hχ]
  have key : TriggerCond χ k β πbar ↔ 0 ≤ (k - χ * πbar) * (χ * πbar - x0) := by
    unfold TriggerCond
    have e : β / (1 - β) * (k ^ 2 / χ - χ * πbar ^ 2) - (k - χ * πbar) ^ 2 / (1 + χ) =
        (χ + β) / ((1 - β) * χ * (1 + χ)) * ((k - χ * πbar) * (χ * πbar - x0)) := by
      rw [hx0]
      field_simp
      ring
    have hpos : 0 < (χ + β) / ((1 - β) * χ * (1 + χ)) := by positivity
    constructor
    · intro h
      have : 0 ≤ (χ + β) / ((1 - β) * χ * (1 + χ)) * ((k - χ * πbar) * (χ * πbar - x0)) := by
        linarith
      exact (mul_nonneg_iff_of_pos_left hpos).1 this
    · intro h
      have := mul_nonneg hpos.le h
      linarith
  rw [key, between_iff (χ * πbar) x0 k hx0k]
  have e1 : x0 ≤ χ * πbar ↔ lowerBound χ k β ≤ πbar := by
    unfold lowerBound
    rw [hx0, div_le_iff₀ hcb, div_le_iff₀ (by positivity)]
    constructor <;> intro h <;> nlinarith
  have e2 : χ * πbar ≤ k ↔ πbar ≤ k / χ := by
    rw [le_div_iff₀ hχ, mul_comm]
  rw [e1, e2]

/-- O&R (38)–(39), T17: the trigger equilibrium with target `π̄` exists iff
`π̲(β) ≤ π̄ ≤ k/χ`. -/
theorem trigger_eqm_iff_bounds (p z : S → ℝ) (β χ k πbar : ℝ) (hχ : 0 < χ) (hk : 0 < k)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hp : ∀ s, 0 ≤ p s) (h1 : ∑ s, p s = 1)
    (hz : expect p z = 0) :
    IsReputationEqm p z β χ k (trigExp χ k πbar z) (trigCB χ k πbar z) ↔
      lowerBound χ k β ≤ πbar ∧ πbar ≤ k / χ := by
  rw [trigger_eqm_iff p z β χ k πbar hχ hβ0.le hβ1 hp h1 hz,
    triggerCond_iff_bounds χ k β πbar hχ hk hβ0 hβ1]

/-- O&R p. 640 (38): the zero-inflation trigger equilibrium (with the commitment rule
`z/(1 + χ)` on the path when there are shocks, (39)) exists iff `β ≥ χ/(1 + 2χ)`. -/
theorem trigger_zero_iff (p z : S → ℝ) (β χ k : ℝ) (hχ : 0 < χ) (hk : 0 < k) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hp : ∀ s, 0 ≤ p s) (h1 : ∑ s, p s = 1) (hz : expect p z = 0) :
    IsReputationEqm p z β χ k (trigExp χ k 0 z) (trigCB χ k 0 z) ↔ χ / (1 + 2 * χ) ≤ β := by
  rw [trigger_eqm_iff_bounds p z β χ k 0 hχ hk hβ0 hβ1 hp h1 hz]
  have hk' : (0 : ℝ) ≤ k / χ := by positivity
  simp only [hk', and_true]
  unfold lowerBound
  rw [div_le_iff₀ (by positivity), zero_mul, div_le_iff₀ (by positivity)]
  constructor <;> intro h <;> nlinarith

omit [Fintype S] in
/-- O&R (39): on a surprise-free history the zero-target trigger strategy plays the
commitment rule (36). -/
theorem trigCB_zero_eq_commit (χ k : ℝ) (z : S → ℝ) (h : Hist S) (hns : NoSurprise χ z h) :
    trigCB χ k 0 z h = commitRule χ z := by
  classical
  funext s
  simp [trigCB, hns, commitRule]

/-- O&R p. 640: the book's cost and gain at `π̄ = 0`: gain `k²/(1 + χ)`, per-period
punishment `k²/χ`. -/
theorem book_gain_cost (χ k : ℝ) :
    (k - χ * 0) ^ 2 / (1 + χ) = k ^ 2 / (1 + χ) ∧ k ^ 2 / χ - χ * 0 ^ 2 = k ^ 2 / χ := by
  constructor <;> ring

/-- O&R (38), deterministic version (`S = Unit`, `z = 0`): the zero-inflation trigger
equilibrium exists iff `β ≥ χ/(1 + 2χ)`. -/
theorem trigger_deterministic_iff (β χ k : ℝ) (hχ : 0 < χ) (hk : 0 < k) (hβ0 : 0 < β)
    (hβ1 : β < 1) :
    IsReputationEqm (fun _ : Unit => 1) (fun _ => 0) β χ k (trigExp χ k 0 fun _ => 0)
      (trigCB χ k 0 fun _ => 0) ↔ χ / (1 + 2 * χ) ≤ β :=
  trigger_zero_iff _ _ β χ k hχ hk hβ0 hβ1 (fun _ => zero_le_one) (by simp)
    (by simp [expect])

/-- O&R p. 641: the one-shot outcome `π̄ = k/χ` is always a trigger equilibrium. -/
theorem trigger_oneShot_eqm (p z : S → ℝ) (β χ k : ℝ) (hχ : 0 < χ) (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) (hp : ∀ s, 0 ≤ p s) (h1 : ∑ s, p s = 1) (hz : expect p z = 0) :
    IsReputationEqm p z β χ k (trigExp χ k (k / χ) z) (trigCB χ k (k / χ) z) := by
  rw [trigger_eqm_iff p z β χ k _ hχ hβ0 hβ1 hp h1 hz]
  unfold TriggerCond
  have e1 : k - χ * (k / χ) = 0 := by field_simp; ring
  have e2 : k ^ 2 / χ - χ * (k / χ) ^ 2 = 0 := by field_simp; ring
  rw [e1, e2]
  simp

/-- T17 / fn 29: `π̲(β) < k/χ` for every `β > 0`, so a rate below the one-shot level is
always sustainable. -/
theorem lowerBound_lt (χ k β : ℝ) (hχ : 0 < χ) (hk : 0 < k) (hβ0 : 0 < β) :
    lowerBound χ k β < k / χ := by
  unfold lowerBound
  rw [div_lt_div_iff₀ (by positivity) hχ]
  nlinarith [mul_pos hk hβ0, mul_pos (mul_pos hk hβ0) hχ, mul_pos hχ hχ]

/-- T17: `π̲(β) > −k/χ` for `β < 1`. -/
theorem neg_lt_lowerBound (χ k β : ℝ) (hχ : 0 < χ) (hk : 0 < k) (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    -(k / χ) < lowerBound χ k β := by
  have hcb : 0 < χ + β := by linarith
  have : lowerBound χ k β + k / χ = 2 * k * (1 - β) / (χ + β) := by
    unfold lowerBound
    field_simp
    ring
  have : 0 < 2 * k * (1 - β) / (χ + β) := div_pos (by nlinarith) hcb
  linarith

/-- T17: `π̲(β) → −k/χ` as `β → 1`. -/
theorem lowerBound_tendsto (χ k : ℝ) (hχ : 0 < χ) :
    Tendsto (lowerBound χ k) (𝓝 1) (𝓝 (-(k / χ))) := by
  have hc : ContinuousAt (lowerBound χ k) 1 := by
    unfold lowerBound
    have : χ * (χ + 1) ≠ 0 := by positivity
    fun_prop (disch := assumption)
  have : lowerBound χ k 1 = -(k / χ) := by
    unfold lowerBound
    field_simp
    ring
  rw [← this]
  exact hc.tendsto

/-- O&R p. 641 ("even negative expected inflation rates are sustainable"), T17: some negative
target is sustainable iff `β > χ/(1 + 2χ)`. -/
theorem negative_sustainable_iff (p z : S → ℝ) (β χ k : ℝ) (hχ : 0 < χ) (hk : 0 < k)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hp : ∀ s, 0 ≤ p s) (h1 : ∑ s, p s = 1)
    (hz : expect p z = 0) :
    (∃ πbar < 0, IsReputationEqm p z β χ k (trigExp χ k πbar z) (trigCB χ k πbar z)) ↔
      χ / (1 + 2 * χ) < β := by
  have hlb : lowerBound χ k β < 0 ↔ χ / (1 + 2 * χ) < β := by
    unfold lowerBound
    rw [div_lt_iff₀ (by positivity), zero_mul, div_lt_iff₀ (by positivity)]
    constructor <;> intro h <;> nlinarith
  rw [← hlb]
  constructor
  · rintro ⟨πbar, hneg, heq⟩
    rw [trigger_eqm_iff_bounds p z β χ k πbar hχ hk hβ0 hβ1 hp h1 hz] at heq
    linarith [heq.1]
  · intro h
    refine ⟨lowerBound χ k β, h, ?_⟩
    rw [trigger_eqm_iff_bounds p z β χ k _ hχ hk hβ0 hβ1 hp h1 hz]
    exact ⟨le_rfl, (lowerBound_lt χ k β hχ hk hβ0).le⟩

/-- O&R p. 641 (multiplicity): once zero inflation is sustainable, so is every rate in
`[0, k/χ]` (indeed in `[π̲(β), k/χ]`), including the one-shot rate. -/
theorem trigger_multiplicity (p z : S → ℝ) (β χ k πbar : ℝ) (hχ : 0 < χ) (hk : 0 < k)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hp : ∀ s, 0 ≤ p s) (h1 : ∑ s, p s = 1)
    (hz : expect p z = 0)
    (h0 : IsReputationEqm p z β χ k (trigExp χ k 0 z) (trigCB χ k 0 z))
    (hπ0 : 0 ≤ πbar) (hπ1 : πbar ≤ k / χ) :
    IsReputationEqm p z β χ k (trigExp χ k πbar z) (trigCB χ k πbar z) := by
  rw [trigger_eqm_iff_bounds p z β χ k 0 hχ hk hβ0 hβ1 hp h1 hz] at h0
  rw [trigger_eqm_iff_bounds p z β χ k πbar hχ hk hβ0 hβ1 hp h1 hz]
  exact ⟨h0.1.trans hπ0, hπ1⟩

/-! ## One-period punishments (fn 29) -/

/-- O&R fn 29: the last period had no surprise (vacuous at the initial history). -/
def LastOK (χ : ℝ) (z : S → ℝ) : Hist S → Prop
  | [] => True
  | x :: _ => x.1 = x.2.1 + z x.2.2 / (1 + χ)

/-- O&R fn 29: expectations with a one-period punishment interval. -/
noncomputable def exp1 (χ k πbar : ℝ) (z : S → ℝ) (h : Hist S) : ℝ := by
  classical exact if LastOK χ z h then πbar else k / χ

/-- O&R fn 29: the bank's strategy with one-period punishments. -/
noncomputable def cb1 (χ k πbar : ℝ) (z : S → ℝ) (h : Hist S) (s : S) : ℝ := by
  classical exact if LastOK χ z h then πbar + z s / (1 + χ) else k / χ + z s / (1 + χ)

/-- O&R fn 29: the value of the one-period-punishment profile: `W_N = V_on/(1 − β)` in the
normal state and `W_P = V_D + βW_N` in the punishment state. -/
noncomputable def val1 (p z : S → ℝ) (β χ k πbar : ℝ) (h : Hist S) : ℝ := by
  classical exact if LastOK χ z h then valueOn χ k (varZ p z) πbar / (1 - β)
    else valueOn χ k (varZ p z) (k / χ) + β * (valueOn χ k (varZ p z) πbar / (1 - β))

/-- O&R fn 29: the one-period condition `gain ≤ β·(k²/χ − χπ̄²)`. -/
def OnePeriodCond (χ k β πbar : ℝ) : Prop :=
  (k - χ * πbar) ^ 2 / (1 + χ) ≤ β * (k ^ 2 / χ - χ * πbar ^ 2)

omit [Fintype S] in
/-- O&R fn 29: the last entry of an extended history. -/
theorem lastOK_cons_iff (χ : ℝ) (z : S → ℝ) (a e : ℝ) (s : S) (h : Hist S) :
    LastOK χ z ((a, e, s) :: h) ↔ a = e + z s / (1 + χ) := Iff.rfl

omit [Fintype S] in
/-- O&R fn 29: the initial history counts as normal. -/
theorem lastOK_nil (χ : ℝ) (z : S → ℝ) : LastOK χ z ([] : Hist S) := trivial

omit [Fintype S] in
/-- O&R fn 29: expectations in the normal state. -/
theorem exp1_pos (χ k πbar : ℝ) (z : S → ℝ) (h : Hist S) (hl : LastOK χ z h) :
    exp1 χ k πbar z h = πbar := by
  unfold exp1
  simp [hl]

omit [Fintype S] in
/-- O&R fn 29: expectations in the punishment state. -/
theorem exp1_neg (χ k πbar : ℝ) (z : S → ℝ) (h : Hist S) (hl : ¬ LastOK χ z h) :
    exp1 χ k πbar z h = k / χ := by
  unfold exp1
  simp [hl]

omit [Fintype S] in
/-- O&R fn 29: the bank's play in the normal state. -/
theorem cb1_pos (χ k πbar : ℝ) (z : S → ℝ) (h : Hist S) (hl : LastOK χ z h) (s : S) :
    cb1 χ k πbar z h s = πbar + z s / (1 + χ) := by
  unfold cb1
  simp [hl]

omit [Fintype S] in
/-- O&R fn 29: the bank's play in the punishment state. -/
theorem cb1_neg (χ k πbar : ℝ) (z : S → ℝ) (h : Hist S) (hl : ¬ LastOK χ z h) (s : S) :
    cb1 χ k πbar z h s = k / χ + z s / (1 + χ) := by
  unfold cb1
  simp [hl]

/-- O&R fn 29: the value in the normal state. -/
theorem val1_pos (p z : S → ℝ) (β χ k πbar : ℝ) (h : Hist S) (hl : LastOK χ z h) :
    val1 p z β χ k πbar h = valueOn χ k (varZ p z) πbar / (1 - β) := by
  unfold val1
  simp [hl]

/-- O&R fn 29: the value in the punishment state. -/
theorem val1_neg (p z : S → ℝ) (β χ k πbar : ℝ) (h : Hist S) (hl : ¬ LastOK χ z h) :
    val1 p z β χ k πbar h =
      valueOn χ k (varZ p z) (k / χ) + β * (valueOn χ k (varZ p z) πbar / (1 - β)) := by
  unfold val1
  simp [hl]

/-- O&R fn 29: rational expectations at every history. -/
theorem one_rational (p z : S → ℝ) (χ k πbar : ℝ) (h1 : ∑ s, p s = 1) (hz : expect p z = 0)
    (h : Hist S) : exp1 χ k πbar z h = expect p (cb1 χ k πbar z h) := by
  by_cases hl : LastOK χ z h
  · rw [exp1_pos χ k πbar z h hl, funext (cb1_pos χ k πbar z h hl),
      expect_const_add_shock p z χ πbar h1 hz]
  · rw [exp1_neg χ k πbar z h hl, funext (cb1_neg χ k πbar z h hl),
      expect_const_add_shock p z χ _ h1 hz]

/-- O&R fn 29: the one-period value satisfies the Bellman equality. -/
theorem one_bellman_eq (p z : S → ℝ) (β χ k πbar : ℝ) (hχ : 0 < χ) (hβ1 : β < 1)
    (h1 : ∑ s, p s = 1) (hz : expect p z = 0) (h : Hist S) :
    bellman p z β χ k (exp1 χ k πbar z) (val1 p z β χ k πbar) h (cb1 χ k πbar z h) =
      val1 p z β χ k πbar h := by
  have hχ1 : 0 < 1 + χ := by linarith
  rw [bellman_eq_expect]
  by_cases hl : LastOK χ z h
  · have hpt : ∀ s, bgLoss χ k (cb1 χ k πbar z h s) (exp1 χ k πbar z h) (z s) +
        β * val1 p z β χ k πbar ((cb1 χ k πbar z h s, exp1 χ k πbar z h, s) :: h) =
        onLoss χ k πbar (z s) + β * (valueOn χ k (varZ p z) πbar / (1 - β)) := by
      intro s
      rw [cb1_pos χ k πbar z h hl, exp1_pos χ k πbar z h hl,
        val1_pos p z β χ k πbar _ ((lastOK_cons_iff χ z _ _ s h).2 rfl)]
      rfl
    rw [expect_congr' p _ _ hpt, expect_add, expect_onLoss p z χ k πbar hχ1 h1 hz,
      expect_const p h1, val1_pos p z β χ k πbar h hl]
    exact (div_one_sub_eq _ β hβ1).symm
  · have hpt : ∀ s, bgLoss χ k (cb1 χ k πbar z h s) (exp1 χ k πbar z h) (z s) +
        β * val1 p z β χ k πbar ((cb1 χ k πbar z h s, exp1 χ k πbar z h, s) :: h) =
        onLoss χ k (k / χ) (z s) + β * (valueOn χ k (varZ p z) πbar / (1 - β)) := by
      intro s
      rw [cb1_neg χ k πbar z h hl, exp1_neg χ k πbar z h hl,
        val1_pos p z β χ k πbar _ ((lastOK_cons_iff χ z _ _ s h).2 rfl)]
      rfl
    rw [expect_congr' p _ _ hpt, expect_add, expect_onLoss p z χ k (k / χ) hχ1 h1 hz,
      expect_const p h1, val1_neg p z β χ k πbar h hl]

/-- O&R fn 29: under the one-period condition, the Bellman inequality holds for every
action rule. -/
theorem one_bellman_le (p z : S → ℝ) (β χ k πbar : ℝ) (hχ : 0 < χ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hp : ∀ s, 0 ≤ p s) (h1 : ∑ s, p s = 1) (hz : expect p z = 0)
    (hcond : OnePeriodCond χ k β πbar) (h : Hist S) (a : S → ℝ) :
    val1 p z β χ k πbar h ≤
      bellman p z β χ k (exp1 χ k πbar z) (val1 p z β χ k πbar) h a := by
  have hχ1 : 0 < 1 + χ := by linarith
  have hD : 0 < 1 - β := by linarith
  rw [bellman_eq_expect]
  set VN := valueOn χ k (varZ p z) πbar
  set VD := valueOn χ k (varZ p z) (k / χ)
  have hc2 : VD - VN = k ^ 2 / χ - χ * πbar ^ 2 := by
    have := valueDiscretion_sub_valueOn χ k (varZ p z) πbar
    rwa [← valueOn_discretion χ k (varZ p z) hχ] at this
  have hgain : 0 ≤ (k - χ * πbar) ^ 2 / (1 + χ) := by positivity
  unfold OnePeriodCond at hcond
  have hPN : VD + β * (VN / (1 - β)) - VN / (1 - β) = VD - VN := by
    field_simp
    ring
  have hVDN : 0 ≤ VD - VN := by
    rw [hc2]
    by_contra hneg
    push Not at hneg
    nlinarith
  by_cases hl : LastOK χ z h
  · have hpt : ∀ s, onLoss χ k πbar (z s) + β * (VN / (1 - β)) ≤
        bgLoss χ k (a s) (exp1 χ k πbar z h) (z s) +
          β * val1 p z β χ k πbar ((a s, exp1 χ k πbar z h, s) :: h) := by
      intro s
      rw [exp1_pos χ k πbar z h hl]
      by_cases ha : a s = πbar + z s / (1 + χ)
      · rw [val1_pos p z β χ k πbar _ ((lastOK_cons_iff χ z _ _ s h).2 ha), ha]
        rfl
      · have hn : ¬ LastOK χ z ((a s, πbar, s) :: h) := ha
        rw [val1_neg p z β χ k πbar _ hn]
        have hm := minLoss_le χ k (a s) πbar (z s) hχ1
        have hg := onLoss_sub_minLoss χ k πbar (z s) hχ1
        have : β * (VD + β * (VN / (1 - β))) - β * (VN / (1 - β)) = β * (VD - VN) := by
          rw [← hPN]
          ring
        rw [hc2] at this
        linarith
    calc val1 p z β χ k πbar h
        = expect p (fun s => onLoss χ k πbar (z s) + β * (VN / (1 - β))) := by
          rw [expect_add, expect_onLoss p z χ k πbar hχ1 h1 hz, expect_const p h1,
            val1_pos p z β χ k πbar h hl]
          exact div_one_sub_eq _ β hβ1
      _ ≤ _ := expect_mono p _ _ hp hpt
  · have hpt : ∀ s, onLoss χ k (k / χ) (z s) + β * (VN / (1 - β)) ≤
        bgLoss χ k (a s) (exp1 χ k πbar z h) (z s) +
          β * val1 p z β χ k πbar ((a s, exp1 χ k πbar z h, s) :: h) := by
      intro s
      rw [exp1_neg χ k πbar z h hl, onLoss_discretion χ k (z s) hχ]
      have hm := minLoss_le χ k (a s) (k / χ) (z s) hχ1
      by_cases ha : a s = k / χ + z s / (1 + χ)
      · rw [val1_pos p z β χ k πbar _ ((lastOK_cons_iff χ z _ _ s h).2 ha)]
        linarith
      · have hn : ¬ LastOK χ z ((a s, k / χ, s) :: h) := ha
        rw [val1_neg p z β χ k πbar _ hn]
        have : 0 ≤ β * (VD + β * (VN / (1 - β)) - VN / (1 - β)) := by
          rw [hPN]
          exact mul_nonneg hβ0.le hVDN
        nlinarith
    calc val1 p z β χ k πbar h
        = expect p (fun s => onLoss χ k (k / χ) (z s) + β * (VN / (1 - β))) := by
          rw [expect_add, expect_onLoss p z χ k (k / χ) hχ1 h1 hz, expect_const p h1,
            val1_neg p z β χ k πbar h hl]
      _ ≤ _ := expect_mono p _ _ hp hpt

/-- O&R fn 29: the one-period value is bounded. -/
theorem val1_abs_le (p z : S → ℝ) (β χ k πbar : ℝ) (h : Hist S) :
    |val1 p z β χ k πbar h| ≤ |valueOn χ k (varZ p z) πbar / (1 - β)| +
      |valueOn χ k (varZ p z) (k / χ) + β * (valueOn χ k (varZ p z) πbar / (1 - β))| := by
  by_cases hl : LastOK χ z h
  · rw [val1_pos p z β χ k πbar h hl]
    linarith [abs_nonneg (valueOn χ k (varZ p z) (k / χ) +
      β * (valueOn χ k (varZ p z) πbar / (1 - β)))]
  · rw [val1_neg p z β χ k πbar h hl]
    linarith [abs_nonneg (valueOn χ k (varZ p z) πbar / (1 - β))]

/-- O&R fn 29: cheating once at the empty history, then one period of punishment and back
to normal: value `V_on − gain + β(V_D + β·V_on/(1 − β))`, provided `k ≠ χπ̄`. -/
theorem one_rootDev_value (p z : S → ℝ) (β χ k πbar : ℝ) (hχ : 0 < χ) (h1 : ∑ s, p s = 1)
    (hz : expect p z = 0) (hne : k ≠ χ * πbar) :
    bellman p z β χ k (exp1 χ k πbar z) (val1 p z β χ k πbar) []
        (fun s => bestResponse χ k πbar (z s)) =
      valueOn χ k (varZ p z) πbar - (k - χ * πbar) ^ 2 / (1 + χ) +
        β * (valueOn χ k (varZ p z) (k / χ) + β * (valueOn χ k (varZ p z) πbar / (1 - β))) := by
  have hχ1 : 0 < 1 + χ := by linarith
  rw [bellman_eq_expect, exp1_pos χ k πbar z [] (lastOK_nil χ z)]
  have hpt : ∀ s, bgLoss χ k (bestResponse χ k πbar (z s)) πbar (z s) +
      β * val1 p z β χ k πbar ((bestResponse χ k πbar (z s), πbar, s) :: []) =
      (onLoss χ k πbar (z s) - (k - χ * πbar) ^ 2 / (1 + χ)) +
        β * (valueOn χ k (varZ p z) (k / χ) + β * (valueOn χ k (varZ p z) πbar / (1 - β))) := by
    intro s
    have hn : ¬ LastOK χ z ((bestResponse χ k πbar (z s), πbar, s) :: []) := fun hc2 =>
      hne ((bestResponse_eq_onPath_iff χ k πbar (z s) hχ1).1 hc2)
    rw [val1_neg p z β χ k πbar _ hn, ← onLoss_sub_minLoss χ k πbar (z s) hχ1,
      bgLoss_bestResponse χ k πbar (z s) hχ1, minLoss]
    ring
  rw [expect_congr' p _ _ hpt, expect_add, expect_sub, expect_onLoss p z χ k πbar hχ1 h1 hz,
    expect_const p h1, expect_const p h1]

/-- O&R fn 29 (exact form): with a one-period punishment interval, the profile with target
`π̄` is a reputational equilibrium iff `(k − χπ̄)²/(1 + χ) ≤ β(k²/χ − χπ̄²)`. -/
theorem onePeriod_eqm_iff (p z : S → ℝ) (β χ k πbar : ℝ) (hχ : 0 < χ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hp : ∀ s, 0 ≤ p s) (h1 : ∑ s, p s = 1) (hz : expect p z = 0) :
    IsReputationEqm p z β χ k (exp1 χ k πbar z) (cb1 χ k πbar z) ↔
      OnePeriodCond χ k β πbar := by
  set Wbar := |valueOn χ k (varZ p z) πbar / (1 - β)| +
      |valueOn χ k (varZ p z) (k / χ) + β * (valueOn χ k (varZ p z) πbar / (1 - β))|
  constructor
  · intro heqm
    by_contra hc
    unfold OnePeriodCond at hc
    push Not at hc
    have hne : k ≠ χ * πbar := by
      intro hk
      have e1 : k - χ * πbar = 0 := by rw [hk]; ring
      have e2 : k ^ 2 / χ - χ * πbar ^ 2 = 0 := by rw [hk]; field_simp; ring
      rw [e1, e2] at hc
      simp at hc
    have hdev := hasExpPV_rootDev p z β χ k hp h1 hβ0.le hβ1 (exp1 χ k πbar z)
      (val1 p z β χ k πbar) Wbar (val1_abs_le p z β χ k πbar) (cb1 χ k πbar z)
      (one_bellman_eq p z β χ k πbar hχ hβ1 h1 hz) (fun s => bestResponse χ k πbar (z s))
    have htrig := tendsto_truncCost_of_bellman_eq p z β χ k hp h1 hβ0.le hβ1
      (exp1 χ k πbar z) (val1 p z β χ k πbar) Wbar (val1_abs_le p z β χ k πbar)
      (cb1 χ k πbar z) (one_bellman_eq p z β χ k πbar hχ hβ1 h1 hz) []
    refine not_isReputationEqm_of_better p z β χ k _ _ _ [] _ _ htrig hdev ?_ heqm
    rw [one_rootDev_value p z β χ k πbar hχ h1 hz hne,
      val1_pos p z β χ k πbar [] (lastOK_nil χ z)]
    have hc2 := valueDiscretion_sub_valueOn χ k (varZ p z) πbar
    rw [← valueOn_discretion χ k (varZ p z) hχ] at hc2
    have hD : (1 - β) ≠ 0 := by linarith
    have e : valueOn χ k (varZ p z) πbar / (1 - β) -
        (valueOn χ k (varZ p z) πbar - (k - χ * πbar) ^ 2 / (1 + χ) +
          β * (valueOn χ k (varZ p z) (k / χ) +
            β * (valueOn χ k (varZ p z) πbar / (1 - β)))) =
        (k - χ * πbar) ^ 2 / (1 + χ) - β * (k ^ 2 / χ - χ * πbar ^ 2) := by
      rw [← hc2]
      field_simp
      ring
    linarith
  · intro hcond
    exact isReputationEqm_of_bellman p z β χ k hp h1 hβ0.le hβ1 (exp1 χ k πbar z)
      (val1 p z β χ k πbar) Wbar (val1_abs_le p z β χ k πbar) (cb1 χ k πbar z)
      (one_rational p z χ k πbar h1 hz) (one_bellman_eq p z β χ k πbar hχ hβ1 h1 hz)
      (one_bellman_le p z β χ k πbar hχ hβ0 hβ1 hp h1 hz hcond)

/-- O&R fn 29: the lowest target sustainable with one-period punishments,
`k(χ − β(1 + χ))/(χ(χ + β(1 + χ)))`. -/
noncomputable def lowerBound1 (χ k β : ℝ) : ℝ :=
  k * (χ - β * (1 + χ)) / (χ * (χ + β * (1 + χ)))

/-- O&R fn 29 (exact sustainable set): with one-period punishments the profile with target
`π̄` is an equilibrium iff `lowerBound1 ≤ π̄ ≤ k/χ`. -/
theorem onePeriod_eqm_iff_bounds (p z : S → ℝ) (β χ k πbar : ℝ) (hχ : 0 < χ) (hk : 0 < k)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hp : ∀ s, 0 ≤ p s) (h1 : ∑ s, p s = 1)
    (hz : expect p z = 0) :
    IsReputationEqm p z β χ k (exp1 χ k πbar z) (cb1 χ k πbar z) ↔
      lowerBound1 χ k β ≤ πbar ∧ πbar ≤ k / χ := by
  rw [onePeriod_eqm_iff p z β χ k πbar hχ hβ0 hβ1 hp h1 hz]
  have hχ1 : 0 < 1 + χ := by linarith
  have hcb : 0 < χ + β * (1 + χ) := by positivity
  set x0 := k * (χ - β * (1 + χ)) / (χ + β * (1 + χ)) with hx0
  have hx0k : x0 < k := by
    rw [hx0, div_lt_iff₀ hcb]
    nlinarith [mul_pos hβ0 hχ1]
  have key : OnePeriodCond χ k β πbar ↔ 0 ≤ (k - χ * πbar) * (χ * πbar - x0) := by
    unfold OnePeriodCond
    have e : β * (k ^ 2 / χ - χ * πbar ^ 2) - (k - χ * πbar) ^ 2 / (1 + χ) =
        (χ + β * (1 + χ)) / (χ * (1 + χ)) * ((k - χ * πbar) * (χ * πbar - x0)) := by
      rw [hx0]
      field_simp
      ring
    have hpos : 0 < (χ + β * (1 + χ)) / (χ * (1 + χ)) := by positivity
    constructor
    · intro h
      have : 0 ≤ (χ + β * (1 + χ)) / (χ * (1 + χ)) * ((k - χ * πbar) * (χ * πbar - x0)) := by
        linarith
      exact (mul_nonneg_iff_of_pos_left hpos).1 this
    · intro h
      have := mul_nonneg hpos.le h
      linarith
  rw [key, between_iff (χ * πbar) x0 k hx0k]
  have e1 : x0 ≤ χ * πbar ↔ lowerBound1 χ k β ≤ πbar := by
    unfold lowerBound1
    rw [hx0, div_le_iff₀ hcb, div_le_iff₀ (by positivity)]
    constructor <;> intro h <;> nlinarith
  have e2 : χ * πbar ≤ k ↔ πbar ≤ k / χ := by
    rw [le_div_iff₀ hχ, mul_comm]
  rw [e1, e2]

/-- O&R fn 29: even with a one-period punishment interval, some expected inflation rate
strictly below the one-shot level `k/χ` is always sustainable (`0 < β < 1`). -/
theorem onePeriod_below_oneShot (p z : S → ℝ) (β χ k : ℝ) (hχ : 0 < χ) (hk : 0 < k)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hp : ∀ s, 0 ≤ p s) (h1 : ∑ s, p s = 1)
    (hz : expect p z = 0) :
    ∃ πbar < k / χ, IsReputationEqm p z β χ k (exp1 χ k πbar z) (cb1 χ k πbar z) := by
  have hχ1 : 0 < 1 + χ := by linarith
  have hlt : lowerBound1 χ k β < k / χ := by
    unfold lowerBound1
    rw [div_lt_div_iff₀ (by positivity) hχ]
    nlinarith [mul_pos (mul_pos hk hβ0) hχ1, mul_pos hχ hχ]
  refine ⟨lowerBound1 χ k β, hlt, ?_⟩
  rw [onePeriod_eqm_iff_bounds p z β χ k _ hχ hk hβ0 hβ1 hp h1 hz]
  exact ⟨le_rfl, hlt.le⟩

/-! ## Finite horizon: unravelling (pp. 640–641, T19) -/

/-- O&R pp. 640–641: a subgame-perfect equilibrium of the `T`-period game: at every history
of length `< T`, expectations are rational and `σ` minimises the expected loss over the
remaining `T − length` periods against every alternative strategy. -/
def IsFiniteEqm (p z : S → ℝ) (β χ k : ℝ) (T : ℕ) (ε : Hist S → ℝ) (σ : Hist S → S → ℝ) :
    Prop :=
  ∀ h : Hist S, h.length < T → ε h = expect p (σ h) ∧
    ∀ σ', truncCost p z β χ k ε σ (T - h.length) h ≤ truncCost p z β χ k ε σ' (T - h.length) h

/-- O&R pp. 640–641: the value of `j` periods of one-shot play, `V_D(1 + β + ⋯ + β^{j−1})`. -/
noncomputable def staticVal (p z : S → ℝ) (β χ k : ℝ) (j : ℕ) : ℝ :=
  valueDiscretion χ k (varZ p z) * ∑ i ∈ Finset.range j, β ^ i

/-- O&R pp. 640–641: if play is the one-shot equilibrium at every history of length in
`[len h, len h + j)`, then the `j`-period cost from `h` is `staticVal j`. -/
theorem truncCost_static (p z : S → ℝ) (β χ k : ℝ) (hχ : 0 < χ) (hp : ∀ s, 0 ≤ p s)
    (h1 : ∑ s, p s = 1) (hz : expect p z = 0) (ε : Hist S → ℝ) (σ : Hist S → S → ℝ) :
    ∀ j (h : Hist S), (∀ g : Hist S, h.length ≤ g.length → g.length < h.length + j →
      ε g = k / χ ∧ ∀ s, 0 < p s → σ g s = k / χ + z s / (1 + χ)) →
      truncCost p z β χ k ε σ j h = staticVal p z β χ k j := by
  have hχ1 : 0 < 1 + χ := by linarith
  intro j
  induction j with
  | zero => intro h _; simp [truncCost, staticVal]
  | succ j ih =>
    intro h hst
    obtain ⟨he, hs⟩ := hst h le_rfl (by omega)
    have hcont : ∀ s, truncCost p z β χ k ε σ j ((σ h s, ε h, s) :: h) =
        staticVal p z β χ k j := fun s =>
      ih _ fun g hg1 hg2 => hst g (by simp at hg1; omega) (by simp at hg2; omega)
    rw [truncCost_succ, bellman_eq_expect]
    have : expect p (fun s => bgLoss χ k (σ h s) (ε h) (z s) +
        β * truncCost p z β χ k ε σ j ((σ h s, ε h, s) :: h)) =
        expect p (fun s => onLoss χ k (k / χ) (z s) + β * staticVal p z β χ k j) := by
      refine expect_congr_support p _ _ (fun s hps => ?_) hp
      rw [hcont s, he, hs s hps]
      rfl
    rw [this, expect_add, expect_onLoss p z χ k (k / χ) hχ1 h1 hz, expect_const p h1,
      valueOn_discretion χ k _ hχ]
    unfold staticVal
    rw [Finset.sum_range_succ', pow_zero, Finset.mul_sum, Finset.mul_sum]
    simp only [pow_succ]
    rw [mul_add, mul_one, Finset.mul_sum]
    rw [add_comm]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring

/-- O&R pp. 640–641: with one-shot expectations `k/χ` at every history, no strategy can do
better than `staticVal`. -/
theorem truncCost_ge_static (p z : S → ℝ) (β χ k : ℝ) (hχ : 0 < χ) (hβ : 0 ≤ β)
    (hp : ∀ s, 0 ≤ p s) (h1 : ∑ s, p s = 1) (hz : expect p z = 0) (σ : Hist S → S → ℝ) :
    ∀ j h, staticVal p z β χ k j ≤ truncCost p z β χ k (fun _ => k / χ) σ j h := by
  have hχ1 : 0 < 1 + χ := by linarith
  intro j
  induction j with
  | zero => intro h; simp [truncCost, staticVal]
  | succ j ih =>
    intro h
    rw [truncCost_succ, bellman_eq_expect]
    have hlow : staticVal p z β χ k (j + 1) =
        expect p (fun s => onLoss χ k (k / χ) (z s) + β * staticVal p z β χ k j) := by
      rw [expect_add, expect_onLoss p z χ k (k / χ) hχ1 h1 hz, expect_const p h1,
        valueOn_discretion χ k _ hχ]
      unfold staticVal
      rw [Finset.sum_range_succ', pow_zero, mul_add, mul_one, Finset.mul_sum, Finset.mul_sum,
        Finset.mul_sum, add_comm]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hlow]
    refine expect_mono p _ _ hp fun s => ?_
    have := minLoss_le χ k (σ h s) (k / χ) (z s) hχ1
    rw [← onLoss_discretion χ k (z s) hχ] at this
    have := mul_le_mul_of_nonneg_left (ih ((σ h s, k / χ, s) :: h)) hβ
    linarith

/-- O&R pp. 640–641 (T19, existence): one-shot play `πᵉ = k/χ`, `π = k/χ + z/(1 + χ)` at
every history is a subgame-perfect equilibrium of the `T`-period game. -/
theorem finite_static_eqm (p z : S → ℝ) (β χ k : ℝ) (hχ : 0 < χ) (hβ : 0 ≤ β)
    (hp : ∀ s, 0 ≤ p s) (h1 : ∑ s, p s = 1) (hz : expect p z = 0) (T : ℕ) :
    IsFiniteEqm p z β χ k T (fun _ => k / χ) (fun _ s => k / χ + z s / (1 + χ)) := by
  intro h _
  refine ⟨?_, fun σ' => ?_⟩
  · have : expect p (fun s => k / χ + z s / (1 + χ)) =
        expect p (fun s => k / χ + (1 / (1 + χ)) * z s) := by
      unfold expect
      exact Finset.sum_congr rfl fun s _ => by ring
    rw [this, expect_add, expect_const p h1, expect_const_mul, hz, mul_zero, add_zero]
  · rw [truncCost_static p z β χ k hχ hp h1 hz _ _ _ h fun g _ _ => ⟨rfl, fun _ _ => rfl⟩]
    exact truncCost_ge_static p z β χ k hχ hβ hp h1 hz σ' _ h

/-- O&R pp. 640–641 (T19, uniqueness: the trigger equilibrium unravels): in **every**
subgame-perfect equilibrium of the `T`-period game, at every history with periods left,
`πᵉ = k/χ` and `π = k/χ + z/(1 + χ)` in every state of positive probability. -/
theorem finite_eqm_unique (p z : S → ℝ) (β χ k : ℝ) (hχ : 0 < χ) (hp : ∀ s, 0 ≤ p s)
    (h1 : ∑ s, p s = 1) (hz : expect p z = 0) (T : ℕ) (ε : Hist S → ℝ)
    (σ : Hist S → S → ℝ) (heqm : IsFiniteEqm p z β χ k T ε σ) :
    ∀ h : Hist S, h.length < T →
      ε h = k / χ ∧ ∀ s, 0 < p s → σ h s = k / χ + z s / (1 + χ) := by
  have hχ1 : 0 < 1 + χ := by linarith
  -- `Q m`: the claim holds at every history with at most `m` periods remaining.
  suffices hQ : ∀ m, ∀ g : Hist S, T - m ≤ g.length → g.length < T →
      ε g = k / χ ∧ ∀ s, 0 < p s → σ g s = k / χ + z s / (1 + χ) from
    fun h hh => hQ T h (by omega) hh
  intro m
  induction m with
  | zero => intro g hg1 hg2; omega
  | succ m ih =>
    intro h hh1 hh2
    by_cases hlen : T - m ≤ h.length
    · exact ih h hlen hh2
    have hlenEq : h.length + 1 + m = T := by omega
    have hstat : ∀ g : Hist S, h.length + 1 ≤ g.length → g.length < h.length + 1 + m →
        ε g = k / χ ∧ ∀ s, 0 < p s → σ g s = k / χ + z s / (1 + χ) :=
      fun g hg1 hg2 => ih g (by omega) (by omega)
    obtain ⟨hre, hopt⟩ := heqm h hh2
    have hTm : T - h.length = m + 1 := by omega
    -- the cost of any rule `a` at `h`, followed by `σ`
    have hcost : ∀ a : S → ℝ,
        truncCost p z β χ k ε (fun g s => if g.length = h.length then a s else σ g s)
          (T - h.length) h =
        expect p (fun s => bgLoss χ k (a s) (ε h) (z s) + β * staticVal p z β χ k m) := by
      intro a
      rw [hTm, truncCost_succ, bellman_eq_expect]
      congr 1
      funext s
      simp only [↓reduceIte]
      congr 2
      refine truncCost_static p z β χ k hχ hp h1 hz ε _ m _ fun g hg1 hg2 => ?_
      simp only [List.length_cons] at hg1 hg2
      obtain ⟨he, hs⟩ := hstat g hg1 hg2
      refine ⟨he, fun s' hs' => ?_⟩
      have : g.length ≠ h.length := by omega
      simp only [this, ↓reduceIte]
      exact hs s' hs'
    have hσ : truncCost p z β χ k ε σ (T - h.length) h =
        expect p (fun s => bgLoss χ k (σ h s) (ε h) (z s) + β * staticVal p z β χ k m) := by
      rw [hTm, truncCost_succ, bellman_eq_expect]
      congr 1
      funext s
      congr 2
      refine truncCost_static p z β χ k hχ hp h1 hz ε σ m _ fun g hg1 hg2 => ?_
      simp only [List.length_cons] at hg1 hg2
      exact hstat g hg1 hg2
    have hmin : ∀ a : S → ℝ, expect p (fun s => bgLoss χ k (σ h s) (ε h) (z s)) ≤
        expect p (fun s => bgLoss χ k (a s) (ε h) (z s)) := by
      intro a
      have := hopt (fun g s => if g.length = h.length then a s else σ g s)
      rw [hσ, hcost a, expect_add, expect_add, expect_const p h1] at this
      linarith
    have hbr : ∀ s, 0 < p s → σ h s = bestResponse χ k (ε h) (z s) := by
      intro s0 hs0
      classical
      have hle := hmin (fun s => if s = s0 then bestResponse χ k (ε h) (z s0) else σ h s)
      have hdiff : expect p (fun s => bgLoss χ k (σ h s) (ε h) (z s)) -
          expect p (fun s => bgLoss χ k
            (if s = s0 then bestResponse χ k (ε h) (z s0) else σ h s) (ε h) (z s)) =
          p s0 * (bgLoss χ k (σ h s0) (ε h) (z s0) -
            bgLoss χ k (bestResponse χ k (ε h) (z s0)) (ε h) (z s0)) := by
        rw [← expect_sub]
        unfold expect
        rw [Finset.sum_eq_single s0]
        · simp
        · intro b _ hb
          simp [hb]
        · intro hn
          exact absurd (Finset.mem_univ s0) hn
      have hneg : p s0 * (bgLoss χ k (σ h s0) (ε h) (z s0) -
          bgLoss χ k (bestResponse χ k (ε h) (z s0)) (ε h) (z s0)) ≤ 0 := by linarith
      exact eq_bestResponse_of_le χ k _ _ _ hχ1
        (sub_nonpos.1 (nonpos_of_mul_nonpos_right hneg hs0))
    have hE : expect p (fun s => bestResponse χ k (ε h) (z s)) = (k + ε h) / (1 + χ) := by
      have : expect p (fun s => bestResponse χ k (ε h) (z s)) =
          expect p (fun s => (k + ε h) / (1 + χ) + (1 / (1 + χ)) * z s) := by
        unfold expect bestResponse
        exact Finset.sum_congr rfl fun s _ => by ring
      rw [this, expect_add, expect_const p h1, expect_const_mul, hz, mul_zero, add_zero]
    have h2 : ε h = (k + ε h) / (1 + χ) := by
      rw [← hE]
      exact hre.trans (expect_congr_support p _ _ hbr hp)
    have hpe : ε h = k / χ := by
      rw [eq_div_iff hχ1.ne'] at h2
      rw [eq_div_iff hχ.ne']
      linarith
    refine ⟨hpe, fun s hs => ?_⟩
    rw [hbr s hs, hpe]
    unfold bestResponse
    field_simp
    ring

end ObstfeldRogoff.NominalRigidities.ReputationEquilibria
