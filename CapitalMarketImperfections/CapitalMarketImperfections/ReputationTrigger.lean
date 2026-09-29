/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import CapitalMarketImperfections.SovereignRiskPrimitives
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Topology.MetricSpace.Pseudo.Pi
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.Calculus.LHopital

/-!
# Reputation for repayment: trigger strategies on an event tree

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §6.1.2
(pp. 363–373), eqs. (11)–(21), footnotes 18–25, the Application and Table 6.1
(pp. 366–369), §6.1.3 (pp. 375–377), and Exercise 3(a) (pp. 426–427).

**The repeated game (§6.1.2.1).** Output shocks are i.i.d. over dates on a finite state
space. A date-`n` history is the list of the `n + 1` shocks through date `n`
(`Fin (n + 1) → S`), with probability the product of the one-date probabilities. A
*strategy* of the country is an arbitrary default rule `d n h` on histories; the first date
at which it fires is a stopping time. Before default the country consumes its contract
consumption (utility `v_c(ε)`); at the default date it consumes at most its endowment
(`w ≤ v_d(ε)`, so partial defaults are covered); afterwards it is excluded for ever
(autarky, utility `v_a(ε)`). The payoff is the genuine infinite sum
`Σ_n βⁿ E[u(C_n)]`. We prove the exact stopping-time decomposition
`Payoff(honour) − Payoff(d) = Σ_n βⁿ E[1{first default at n}(Cost − Gain(ε_n))]` and
hence: **no strategy beats honouring iff `Gain(ε) ≤ Cost` in every state**, with
`Cost = β/(1 − β)[E v_c − E v_a]` — the sustainability condition (16) as an iff.

**Full insurance (T7).** `Cost` (15) is the infinite sum of discounted utility losses,
positive by strict Jensen; `Gain` (14) is increasing; (16) holds for all `β` close to 1.

**Finite horizon (p. 365).** With a known last date, the only incentive-compatible sequence
of zero-profit contracts is the null contract (backward induction).

**The lognormal application (pp. 366–369).** With `Y_s = (1 + g)^{s−t}Ȳ exp(ε_s − V/2)`,
CRRA utility and the normal moment-generating identity as a hypothesis we prove the closed
forms for `βŪ` and `βE U^A`, that full insurance is sustainable for every output realisation
iff `1 ≤ β(1 + g)^{1−ρ}exp(ρ(ρ − 1)V/2)` when `ρ > 1`, that it is never sustainable when
`ρ < 1` or `ρ = 1`, the formula for `κ`, that `τ = exp(ρV/2) − 1`, and Table 6.1 as interval
statements — including that for **Venezuela `κ ≈ 4.2` is finite, not "Undefined"**.

**Partial insurance (§6.1.2.2, T10).** For stationary contracts with the incentive constraint
(18): the constraint set is convex; an optimum exists and is unique; the Kuhn–Tucker
conditions (19)–(20) are sufficient; at the optimum consumption is
`max(c̄, u⁻¹(u(Ȳ + ε) − Cost))` with `E C = Ȳ`, derived by a direct perturbation argument;
on the binding arm `0 < ΔP < Δε` and `dP/dε = [u'(C) − u'(Ȳ + ε)]/u'(C) ∈ (0, 1)`. The book's
assertion that partial insurance is always feasible is false in general: with two states and
small `β` only the null contract is incentive compatible.

**General equilibrium (§6.1.3, T13)** and **Exercise 3(a)** are further instances of the same
stopping-time theorem.
-/

namespace ObstfeldRogoff.CapitalMarketImperfections.ReputationTrigger

open Finset Filter Topology
open SovereignRiskPrimitives SovereignRiskPrimitives.StateSpaceFacts

/-! ## Histories of i.i.d. shocks -/

namespace History

variable {S : Type} [Fintype S] (Ω : StateSpace S)

/-- The probability of a history of `k` i.i.d. shocks, the product of the one-date
probabilities (O&R (11), p. 364: `ε_s` i.i.d.). -/
noncomputable def histProb {k : ℕ} (h : Fin k → S) : ℝ := ∏ i, Ω.prob (h i)

/-- The expectation over histories of `k` shocks (O&R (11), p. 364: `E_t`). -/
noncomputable def hexp (k : ℕ) (X : (Fin k → S) → ℝ) : ℝ := ∑ h, histProb Ω h * X h

/-- Appending a shock multiplies the history probability by its probability (i.i.d.).
(O&R (11), p. 364) -/
theorem histProb_snoc {k : ℕ} (g : Fin k → S) (s : S) :
    histProb Ω (Fin.snoc g s : Fin (k + 1) → S) = histProb Ω g * Ω.prob s := by
  unfold histProb
  rw [Fin.prod_univ_castSucc]
  simp [Fin.snoc_castSucc, Fin.snoc_last]

/-- Summing over histories of `k + 1` shocks is summing over the first `k` shocks and the
last one.
(O&R (11), p. 364) -/
theorem sum_snoc {k : ℕ} (f : (Fin (k + 1) → S) → ℝ) :
    ∑ h, f h = ∑ g : Fin k → S, ∑ s, f (Fin.snoc g s : Fin (k + 1) → S) := by
  rw [← (Fin.snocEquiv (fun _ : Fin (k + 1) => S)).sum_comp, Fintype.sum_prod_type,
    Finset.sum_comm]
  rfl

/-- History probabilities are nonnegative.
(O&R (11), p. 364) -/
theorem histProb_nonneg {k : ℕ} (h : Fin k → S) : 0 ≤ histProb Ω h :=
  Finset.prod_nonneg fun i _ => Ω.prob_nonneg (h i)

/-- History probabilities sum to one.
(O&R (11), p. 364) -/
theorem histProb_sum (k : ℕ) : ∑ h : Fin k → S, histProb Ω h = 1 := by
  induction k with
  | zero => simp [histProb]
  | succ k ih =>
    rw [sum_snoc]
    simp only [histProb_snoc, ← Finset.mul_sum, Ω.prob_sum, mul_one]
    exact ih

/-- The expectation over histories of `k + 1` shocks, conditioning on the first `k`.
(O&R (11), p. 364) -/
theorem hexp_succ (k : ℕ) (X : (Fin (k + 1) → S) → ℝ) :
    hexp Ω (k + 1) X =
      hexp Ω k (fun g => Ω.expect (fun s => X (Fin.snoc g s : Fin (k + 1) → S))) := by
  unfold hexp StateSpace.expect
  rw [sum_snoc]
  apply Finset.sum_congr rfl; intro g _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro s _
  rw [histProb_snoc]; ring

/-- Expectation of a constant over histories.
(O&R (11), p. 364) -/
theorem hexp_const (k : ℕ) (c : ℝ) : hexp Ω k (fun _ => c) = c := by
  unfold hexp; rw [← Finset.sum_mul, histProb_sum, one_mul]

/-- Linearity of the expectation over histories.
(O&R (11), p. 364) -/
theorem hexp_linear (k : ℕ) (a b : ℝ) (X Y : (Fin k → S) → ℝ) :
    hexp Ω k (fun h => a * X h + b * Y h) = a * hexp Ω k X + b * hexp Ω k Y := by
  unfold hexp
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro h _; ring

/-- Linear combinations of four variables, pointwise: the expectation of `F` is the same
combination of expectations.
(O&R (11), p. 364) -/
theorem hexp_combo (k : ℕ) (F X Y Z W : (Fin k → S) → ℝ) (a b c e : ℝ)
    (hF : ∀ h, F h = a * X h + b * Y h + c * Z h + e * W h) :
    hexp Ω k F = a * hexp Ω k X + b * hexp Ω k Y + c * hexp Ω k Z + e * hexp Ω k W := by
  unfold hexp
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl; intro h _; rw [hF]; ring

/-- Expectation over histories is monotone.
(O&R (11), p. 364) -/
theorem hexp_mono (k : ℕ) {X Y : (Fin k → S) → ℝ} (hXY : ∀ h, X h ≤ Y h) :
    hexp Ω k X ≤ hexp Ω k Y :=
  Finset.sum_le_sum fun h _ => mul_le_mul_of_nonneg_left (hXY h) (histProb_nonneg Ω h)

/-- A bounded variable has bounded expectation over histories.
(O&R (11), p. 364) -/
theorem abs_hexp_le (k : ℕ) {X : (Fin k → S) → ℝ} {M : ℝ} (hX : ∀ h, |X h| ≤ M) :
    |hexp Ω k X| ≤ M := by
  have h1 : hexp Ω k X ≤ M := by
    have := hexp_mono Ω k (X := X) (Y := fun _ => M) fun h => le_trans (le_abs_self _) (hX h)
    rwa [hexp_const] at this
  have h2 : -M ≤ hexp Ω k X := by
    have := hexp_mono Ω k (X := fun _ => -M) (Y := X) fun h => by
      have := hX h; rw [abs_le] at this; exact this.1
    rwa [hexp_const] at this
  exact abs_le.mpr ⟨h2, h1⟩

/-- **Independence of the current shock** (i.i.d., O&R p. 364): for `A` a function of the
first `k` shocks and `f` of the last, `E[A f] = E[A] E[f]`. -/
theorem hexp_indep (k : ℕ) (A : (Fin k → S) → ℝ) (f : S → ℝ) :
    hexp Ω (k + 1) (fun h => A (Fin.init h) * f (h (Fin.last k))) =
      hexp Ω k A * Ω.expect f := by
  rw [hexp_succ]
  unfold hexp
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl; intro g _
  simp only [Fin.init_snoc, Fin.snoc_last]
  rw [expect_const_mul]; ring

/-- The expectation over one-shock histories is the expectation over states.
(O&R (11), p. 364) -/
theorem hexp_one (X : (Fin 1 → S) → ℝ) :
    hexp Ω 1 X = Ω.expect (fun s => X (fun _ => s)) := by
  rw [hexp_succ]
  unfold hexp
  rw [Fintype.sum_unique]
  simp only [histProb, Finset.univ_eq_empty, Finset.prod_empty, one_mul]
  congr 1

/-- The expectation of a function of the `n₀`-th shock alone (i.i.d., O&R (11), p. 364). -/
theorem hexp_coord (n₀ : ℕ) (f : S → ℝ) :
    ∀ m (hm : n₀ < m), hexp Ω m (fun g : Fin m → S => f (g ⟨n₀, hm⟩)) = Ω.expect f := by
  intro m
  induction m with
  | zero => intro hm; exact absurd hm (Nat.not_lt_zero _)
  | succ m ih =>
    intro hm
    rcases Nat.lt_succ_iff_lt_or_eq.mp hm with h | h
    · have hA := hexp_indep Ω m (fun g : Fin m → S => f (g ⟨n₀, h⟩)) (fun _ => (1 : ℝ))
      rw [Ω.expect_const, mul_one, ih h] at hA
      rw [← hA]
      congr 1; funext g; rw [mul_one]; rfl
    · subst h
      have hA := hexp_indep Ω n₀ (fun _ => (1 : ℝ)) f
      rw [hexp_const, one_mul] at hA
      rw [← hA]
      congr 1; funext g; rw [one_mul]; rfl

/-- Independence of two distinct dates' shocks: for `n₀ < m`,
`E[f(ε_{n₀}) g(ε_m)] = E f · E g` (i.i.d., O&R (11), p. 364). -/
theorem hexp_two_coords (n₀ m : ℕ) (hm : n₀ < m) (f g : S → ℝ) :
    hexp Ω (m + 1) (fun h : Fin (m + 1) → S => f (h ⟨n₀, by omega⟩) * g (h (Fin.last m))) =
      Ω.expect f * Ω.expect g := by
  have hA := hexp_indep Ω m (fun g' : Fin m → S => f (g' ⟨n₀, hm⟩)) g
  rw [hexp_coord Ω n₀ f m hm] at hA
  rw [← hA]
  rfl

end History

open History

/-! ## Stopping-time default strategies and the trigger-strategy theorem -/

namespace Trigger

variable {S : Type}

/-- A default strategy of the country (O&R §6.1.2.1, p. 364): after the `n + 1` shocks
through date `n`, `d n h = true` means "default now (if not already in default)". Any rule on
histories is allowed; its first firing date is a stopping time. -/
abbrev Strategy (S : Type) := (n : ℕ) → (Fin (n + 1) → S) → Bool

/-- Whether the country has defaulted at some date along the history of its first `k`
shocks, i.e. at one of the dates `0, …, k − 1`.
(O&R (14)–(16), pp. 364–365) -/
def defaulted (d : Strategy S) : (k : ℕ) → (Fin k → S) → Bool
  | 0, _ => false
  | k + 1, h => defaulted d k (Fin.init h) || d k h

/-- The event that date `n` is the first default date (the stopping time equals `n`).
(O&R (14)–(16), pp. 364–365) -/
def firstDefault (d : Strategy S) (n : ℕ) (h : Fin (n + 1) → S) : Bool :=
  !defaulted d n (Fin.init h) && d n h

/-- Date-`n` utility on history `h` under strategy `d` (O&R (14)–(15), p. 364): honouring
gives `v_c(ε_n)`; on the default date the country gets `w n h` (at most its endowment
utility `v_d(ε_n)`); after default it is in autarky, `v_a(ε_n)`. -/
def flow (d : Strategy S) (vc va : S → ℝ) (w : (n : ℕ) → (Fin (n + 1) → S) → ℝ) (n : ℕ)
    (h : Fin (n + 1) → S) : ℝ :=
  if defaulted d n (Fin.init h) then va (h (Fin.last n))
  else if d n h then w n h else vc (h (Fin.last n))

/-- The decomposition of the date-`n` flow into honour utility minus the losses from past and
current default.
(O&R (14)–(16), pp. 364–365) -/
theorem flow_eq (d : Strategy S) (vc va : S → ℝ) (w : (n : ℕ) → (Fin (n + 1) → S) → ℝ)
    (n : ℕ) (h : Fin (n + 1) → S) :
    flow d vc va w n h = vc (h (Fin.last n)) -
      (if defaulted d n (Fin.init h) then 1 else 0) *
        (vc (h (Fin.last n)) - va (h (Fin.last n))) -
      (if firstDefault d n h then vc (h (Fin.last n)) - w n h else 0) := by
  unfold flow firstDefault
  cases defaulted d n (Fin.init h) <;> cases d n h <;> simp

variable [Fintype S] (Ω : StateSpace S)

/-- Expected lifetime utility of strategy `d`, O&R (11), p. 364:
`U = E Σ_n βⁿ u(C_n)`, an infinite sum. -/
noncomputable def payoff (β : ℝ) (d : Strategy S) (vc va : S → ℝ)
    (w : (n : ℕ) → (Fin (n + 1) → S) → ℝ) : ℝ :=
  ∑' n, β ^ n * hexp Ω (n + 1) (flow d vc va w n)

/-- The probability of having defaulted before date `n`.
(O&R (14)–(16), pp. 364–365) -/
noncomputable def probDefaulted (d : Strategy S) (n : ℕ) : ℝ :=
  hexp Ω n (fun h => if defaulted d n h then 1 else 0)

/-- The probability that date `n` is the first default date.
(O&R (14)–(16), pp. 364–365) -/
noncomputable def probFirst (d : Strategy S) (n : ℕ) : ℝ :=
  hexp Ω (n + 1) (fun h => if firstDefault d n h then 1 else 0)

/-- The cost of exclusion, O&R (15)/(18): `Cost = β/(1 − β)[E v_c − E v_a]`. -/
noncomputable def cost (β : ℝ) (vc va : S → ℝ) : ℝ :=
  β / (1 - β) * (Ω.expect vc - Ω.expect va)

/-- The probability of default before date `n + 1` is that before date `n` plus that of a
first default at `n`.
(O&R (14)–(16), pp. 364–365) -/
theorem probDefaulted_succ (d : Strategy S) (n : ℕ) :
    probDefaulted Ω d (n + 1) = probDefaulted Ω d n + probFirst Ω d n := by
  unfold probDefaulted probFirst
  have hA := hexp_indep Ω n (fun g => if defaulted d n g then (1 : ℝ) else 0) (fun _ => 1)
  rw [Ω.expect_const, mul_one] at hA
  rw [hexp_combo Ω (n + 1) _ (fun h => (if defaulted d n (Fin.init h) then (1 : ℝ) else 0) * 1)
    (fun h => if firstDefault d n h then (1 : ℝ) else 0) (fun _ => 0) (fun _ => 0) 1 1 0 0
    (fun h => by
      simp only [defaulted, firstDefault]
      by_cases h1 : defaulted d n (Fin.init h) = true <;> by_cases h2 : d n h = true <;>
        simp [h1, h2]), hA]
  ring

/-- No default before date 0.
(O&R (14)–(16), pp. 364–365) -/
theorem probDefaulted_zero (d : Strategy S) : probDefaulted Ω d 0 = 0 := by
  unfold probDefaulted; simp [defaulted, hexp_const]

/-- Probabilities of default lie in `[0, 1]`.
(O&R (14)–(16), pp. 364–365) -/
theorem probDefaulted_mem (d : Strategy S) (n : ℕ) :
    0 ≤ probDefaulted Ω d n ∧ probDefaulted Ω d n ≤ 1 := by
  unfold probDefaulted
  constructor
  · have := hexp_mono Ω n (X := fun _ => (0 : ℝ))
      (Y := fun h => if defaulted d n h then 1 else 0) fun h => by split_ifs <;> norm_num
    rwa [hexp_const] at this
  · have := hexp_mono Ω n (X := fun h => if defaulted d n h then 1 else 0)
      (Y := fun _ => (1 : ℝ)) fun h => by split_ifs <;> norm_num
    rwa [hexp_const] at this

/-- The first-default probabilities are nonnegative.
(O&R (14)–(16), pp. 364–365) -/
theorem probFirst_nonneg (d : Strategy S) (n : ℕ) : 0 ≤ probFirst Ω d n := by
  unfold probFirst
  have := hexp_mono Ω (n + 1) (X := fun _ => (0 : ℝ))
    (Y := fun h => if firstDefault d n h then 1 else 0) fun h => by split_ifs <;> norm_num
  rwa [hexp_const] at this

/-- The partial-sum identity behind the stopping-time decomposition:
`(1 − β)Σ_{n<N} βⁿ Pr(defaulted before n) = βΣ_{n<N} βⁿ Pr(first default at n)
 − β^N Pr(defaulted before N)`.
(O&R (14)–(16), pp. 364–365) -/
theorem partial_sum_identity (d : Strategy S) (β : ℝ) (N : ℕ) :
    (1 - β) * ∑ n ∈ range N, β ^ n * probDefaulted Ω d n =
      β * ∑ n ∈ range N, β ^ n * probFirst Ω d n - β ^ N * probDefaulted Ω d N := by
  induction N with
  | zero => simp [probDefaulted_zero]
  | succ N ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ, probDefaulted_succ, mul_add, ih]
    ring

/-- The cost of exclusion as an infinite sum over dates: `Σ_n βⁿ[c Pr(defaulted before n)
 − Cost Pr(first default at n)] = 0`, i.e. the expected discounted future autarky losses
equal `Cost` times the discounted default probability.
(O&R (14)–(16), pp. 364–365) -/
theorem hasSum_cost_identity (d : Strategy S) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (c : ℝ) :
    HasSum (fun n => β ^ n * (c * probDefaulted Ω d n - β / (1 - β) * c * probFirst Ω d n))
      0 := by
  have h1 : (1 : ℝ) - β ≠ 0 := by linarith
  have hbound : ∀ n, |c * probDefaulted Ω d n - β / (1 - β) * c * probFirst Ω d n| ≤
      |c| + |β / (1 - β) * c| := by
    intro n
    have hf1 : probFirst Ω d n ≤ 1 := by
      have := probDefaulted_mem Ω d (n + 1)
      rw [probDefaulted_succ] at this
      linarith [(probDefaulted_mem Ω d n).1]
    have hG := probDefaulted_mem Ω d n
    have hf0 := probFirst_nonneg Ω d n
    calc |c * probDefaulted Ω d n - β / (1 - β) * c * probFirst Ω d n|
        ≤ |c * probDefaulted Ω d n| + |β / (1 - β) * c * probFirst Ω d n| := abs_sub _ _
      _ = |c| * probDefaulted Ω d n + |β / (1 - β) * c| * probFirst Ω d n := by
          rw [abs_mul, abs_mul, abs_of_nonneg hG.1, abs_of_nonneg hf0]
      _ ≤ |c| * 1 + |β / (1 - β) * c| * 1 := by
          gcongr
          · exact hG.2
      _ = _ := by ring
  have hs := Geometric.summable_of_bounded hβ0 hβ1 hbound
  rw [hs.hasSum_iff_tendsto_nat]
  have hps : ∀ N, ∑ n ∈ range N, β ^ n * (c * probDefaulted Ω d n -
      β / (1 - β) * c * probFirst Ω d n) = -(c / (1 - β)) * (β ^ N * probDefaulted Ω d N) := by
    intro N
    have hid := partial_sum_identity Ω d β N
    have e : ∑ n ∈ range N, β ^ n * (c * probDefaulted Ω d n -
        β / (1 - β) * c * probFirst Ω d n) = c * ∑ n ∈ range N, β ^ n * probDefaulted Ω d n -
        β / (1 - β) * c * ∑ n ∈ range N, β ^ n * probFirst Ω d n := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro n _; ring
    rw [e]
    have hS : ∑ n ∈ range N, β ^ n * probDefaulted Ω d n =
        (β * ∑ n ∈ range N, β ^ n * probFirst Ω d n - β ^ N * probDefaulted Ω d N) /
          (1 - β) := by
      rw [eq_div_iff h1, mul_comm, hid]
    rw [hS]; field_simp; ring
  simp only [hps]
  have hlim : Tendsto (fun N => β ^ N * probDefaulted Ω d N) atTop (𝓝 0) := by
    have hp := tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 hβ1
    refine squeeze_zero (fun N => mul_nonneg (pow_nonneg hβ0 N) (probDefaulted_mem Ω d N).1)
      (fun N => ?_) hp
    calc β ^ N * probDefaulted Ω d N ≤ β ^ N * 1 :=
          mul_le_mul_of_nonneg_left (probDefaulted_mem Ω d N).2 (pow_nonneg hβ0 N)
      _ = β ^ N := mul_one _
  have := hlim.const_mul (-(c / (1 - β)))
  simpa using this

/-- A uniform bound on the absolute values of a function on a finite state space.
(O&R (14)–(16), pp. 364–365) -/
theorem abs_le_sum_abs (v : S → ℝ) (s : S) : |v s| ≤ ∑ t, |v t| :=
  Finset.single_le_sum (f := fun t => |v t|) (fun _ _ => abs_nonneg _) (Finset.mem_univ s)

/-- **The stopping-time decomposition** (O&R (14)–(16), pp. 364–365): for every strategy `d`
and bounded default-date utilities `w`,
`Payoff(d) = E v_c/(1 − β) − Σ_n βⁿ E[1{first default at n}(v_c(ε_n) − w_n + Cost)]`. -/
theorem payoff_decomposition (d : Strategy S) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (vc va : S → ℝ) (w : (n : ℕ) → (Fin (n + 1) → S) → ℝ) {Mw : ℝ}
    (hw : ∀ n h, |w n h| ≤ Mw) :
    Summable (fun n => β ^ n * hexp Ω (n + 1) (fun h => if firstDefault d n h then
      vc (h (Fin.last n)) - w n h + cost Ω β vc va else 0)) ∧
    payoff Ω β d vc va w = Ω.expect vc / (1 - β) -
      ∑' n, β ^ n * hexp Ω (n + 1) (fun h => if firstDefault d n h then
        vc (h (Fin.last n)) - w n h + cost Ω β vc va else 0) := by
  set K := cost Ω β vc va with hK
  set c := Ω.expect vc - Ω.expect va with hc
  set Z : ℕ → ℝ := fun n => hexp Ω (n + 1) (fun h => if firstDefault d n h then
      vc (h (Fin.last n)) - w n h + K else 0) with hZ
  -- boundedness
  have hZb : ∀ n, |Z n| ≤ ∑ t, |vc t| + Mw + |K| := by
    intro n
    apply abs_hexp_le
    intro h
    split_ifs
    · calc |vc (h (Fin.last n)) - w n h + K| ≤ |vc (h (Fin.last n))| + |w n h| + |K| := by
            have := abs_add_le (vc (h (Fin.last n)) - w n h) K
            have := abs_sub (vc (h (Fin.last n))) (w n h)
            linarith
        _ ≤ _ := by linarith [abs_le_sum_abs vc (h (Fin.last n)), hw n h]
    · simp only [abs_zero]
      have := abs_nonneg K
      have : 0 ≤ ∑ t, |vc t| := Finset.sum_nonneg fun t _ => abs_nonneg _
      have := le_trans (abs_nonneg _) (hw n (fun _ => h (Fin.last n)))
      linarith
  have hZs := Geometric.summable_of_bounded hβ0 hβ1 hZb
  refine ⟨hZs, ?_⟩
  -- the flow expectation
  have hflow : ∀ n, hexp Ω (n + 1) (flow d vc va w n) =
      Ω.expect vc - (c * probDefaulted Ω d n - K * probFirst Ω d n) - Z n := by
    intro n
    have hX := hexp_indep Ω n (fun _ => (1 : ℝ)) vc
    rw [hexp_const, one_mul] at hX
    simp only [one_mul] at hX
    have hY := hexp_indep Ω n (fun g => if defaulted d n g then (1 : ℝ) else 0)
      (fun s => vc s - va s)
    beta_reduce at hY
    rw [hexp_combo Ω (n + 1) _ (fun h => vc (h (Fin.last n)))
      (fun h => (if defaulted d n (Fin.init h) then (1 : ℝ) else 0) *
        (vc (h (Fin.last n)) - va (h (Fin.last n))))
      (fun h => if firstDefault d n h then vc (h (Fin.last n)) - w n h + K else 0)
      (fun h => if firstDefault d n h then (1 : ℝ) else 0) 1 (-1) (-1) K
      (fun h => by rw [flow_eq]; split_ifs <;> ring), hX, hY, expect_sub]
    simp only [probDefaulted, probFirst, hZ, hc]
    ring
  have hc_id := hasSum_cost_identity Ω d hβ0 hβ1 c
  have hK' : β / (1 - β) * c = K := by rw [hK, cost]
  simp only [hK'] at hc_id
  have hgeo := Geometric.hasSum_geometric_const hβ0 hβ1 (Ω.expect vc)
  have hsum : HasSum (fun n => β ^ n * hexp Ω (n + 1) (flow d vc va w n))
      (Ω.expect vc / (1 - β) - 0 - ∑' n, β ^ n * Z n) := by
    have := (hgeo.sub hc_id).sub hZs.hasSum
    convert this using 1
    funext n; rw [hflow]; ring
  unfold payoff
  rw [hsum.tsum_eq]; ring

/-- The payoff of honouring for ever (never defaulting) is `E v_c/(1 − β)`
(O&R p. 364: under full insurance `C_s = Ȳ` for ever). -/
theorem payoff_honour {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (vc va : S → ℝ)
    (w : (n : ℕ) → (Fin (n + 1) → S) → ℝ) {Mw : ℝ} (hw : ∀ n h, |w n h| ≤ Mw) :
    payoff Ω β (fun _ _ => false) vc va w = Ω.expect vc / (1 - β) := by
  rw [(payoff_decomposition Ω _ hβ0 hβ1 vc va w hw).2]
  simp [firstDefault, hexp_const]

/-- **The trigger-strategy sustainability theorem**, O&R (14)–(16) and (18), pp. 364–370.
Let every state have positive probability. Honouring the contract is optimal against every
default strategy — every stopping time and every (possibly partial) default-date
consumption `w ≤ v_d` — if and only if `Gain(ε) = v_d(ε) − v_c(ε) ≤ Cost` in every state,
`Cost = β/(1 − β)[E v_c − E v_a]`. -/
theorem trigger_iff {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hpos : ∀ s, 0 < Ω.prob s)
    (vc vd va : S → ℝ) :
    (∀ (d : Strategy S) (w : (n : ℕ) → (Fin (n + 1) → S) → ℝ) (Mw : ℝ),
        (∀ n h, |w n h| ≤ Mw) → (∀ n h, w n h ≤ vd (h (Fin.last n))) →
        payoff Ω β d vc va w ≤ Ω.expect vc / (1 - β)) ↔
      ∀ s, vd s - vc s ≤ cost Ω β vc va := by
  constructor
  · intro H s₀
    by_contra hlt; push Not at hlt
    -- the one-shot deviation: default at date 0 iff the shock is `s₀`
    classical
    let d : Strategy S := fun n h => decide (n = 0) && decide (h 0 = s₀)
    let w : (n : ℕ) → (Fin (n + 1) → S) → ℝ := fun n h => vd (h (Fin.last n))
    have hw : ∀ n h, |w n h| ≤ ∑ t, |vd t| := fun n h => abs_le_sum_abs vd _
    have hH := H d w _ hw (fun n h => le_rfl)
    obtain ⟨hsum, hdec⟩ := payoff_decomposition Ω d hβ0 hβ1 vc va w hw
    have hterm : ∀ n, n ≠ 0 → β ^ n * hexp Ω (n + 1) (fun h => if firstDefault d n h then
        vc (h (Fin.last n)) - w n h + cost Ω β vc va else 0) = 0 := by
      intro n hn
      have : ∀ h : Fin (n + 1) → S, firstDefault d n h = false := fun h => by
        simp [firstDefault, d, hn]
      simp [this, hexp_const]
    rw [tsum_eq_single 0 hterm] at hdec
    have h0 : hexp Ω 1 (fun h => if firstDefault d 0 h then
        vc (h (Fin.last 0)) - w 0 h + cost Ω β vc va else 0) =
        Ω.prob s₀ * (vc s₀ - vd s₀ + cost Ω β vc va) := by
      rw [hexp_one]
      unfold StateSpace.expect
      rw [Finset.sum_eq_single s₀]
      · simp [firstDefault, defaulted, d, w]
      · intro s _ hs
        simp [firstDefault, defaulted, d, hs]
      · simp
    rw [h0, pow_zero, one_mul] at hdec
    have : Ω.prob s₀ * (vc s₀ - vd s₀ + cost Ω β vc va) < 0 :=
      mul_neg_of_pos_of_neg (hpos s₀) (by linarith)
    linarith
  · intro H d w Mw hw hwd
    obtain ⟨_, hdec⟩ := payoff_decomposition Ω d hβ0 hβ1 vc va w hw
    rw [hdec]
    have hnn : 0 ≤ ∑' n, β ^ n * hexp Ω (n + 1) (fun h => if firstDefault d n h then
        vc (h (Fin.last n)) - w n h + cost Ω β vc va else 0) := by
      apply tsum_nonneg; intro n
      apply mul_nonneg (pow_nonneg hβ0 n)
      have := hexp_mono Ω (n + 1) (X := fun _ => (0 : ℝ))
        (Y := fun h => if firstDefault d n h then
          vc (h (Fin.last n)) - w n h + cost Ω β vc va else 0) fun h => by
        split_ifs
        · linarith [H (h (Fin.last n)), hwd n h]
        · exact le_rfl
      rwa [hexp_const] at this
    linarith

end Trigger

open Trigger

/-! ## Full insurance by reputation, §6.1.2.1 -/

namespace FullInsurance

variable {S : Type} [Fintype S] (E : Endowment S) (U : Utility)

/-- The short-run gain from default on full insurance, O&R (14), p. 364:
`Gain(ε) = u(Ȳ + ε) − u(Ȳ)`. -/
noncomputable def gain (s : S) : ℝ := U.u (E.Y s) - U.u E.Ybar

/-- The cost of permanent exclusion, O&R (15), p. 365: `β/(1 − β)[u(Ȳ) − E u(Ȳ + ε)]`. -/
noncomputable def costFI (β : ℝ) : ℝ :=
  β / (1 - β) * (U.u E.Ybar - E.Ω.expect (fun s => U.u (E.Y s)))

/-- O&R p. 364–365: `Cost` is the infinite sum of discounted utility losses from date
`t + 1` on, `Σ_{s ≥ t+1} β^{s−t}u(Ȳ) − Σ_{s ≥ t+1} β^{s−t}E u(Ȳ + ε_s)`, which equals the
closed form (15). -/
theorem costFI_tsum {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    (∑' n : ℕ, β ^ (n + 1) * U.u E.Ybar) -
        ∑' n : ℕ, β ^ (n + 1) * E.Ω.expect (fun s => U.u (E.Y s)) = costFI E U β := by
  rw [(Geometric.hasSum_geometric_from_one hβ0 hβ1 _).tsum_eq,
    (Geometric.hasSum_geometric_from_one hβ0 hβ1 _).tsum_eq, costFI]
  ring

/-- The trigger-strategy cost for full insurance is `costFI` (the utilities `v_c = u(Ȳ)`
and `v_a = u(Ȳ + ε)` of §6.1.2.1).
(O&R (15), p. 365) -/
theorem cost_eq_costFI (β : ℝ) :
    cost E.Ω β (fun _ => U.u E.Ybar) (fun s => U.u (E.Y s)) = costFI E U β := by
  unfold cost costFI; rw [E.Ω.expect_const]

/-- O&R p. 365: because `u` is strictly concave, `u(Ȳ) > E u(Ȳ + ε)` and the penalty for
default is positive whenever the shock is nondegenerate and `0 < β < 1`. -/
theorem costFI_pos {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hnd : ∃ s, E.ε s ≠ 0) :
    0 < costFI E U β := by
  obtain ⟨s, hs⟩ := hnd
  have hj := jensen_strict E.Ω U E.Y_pos (E.prob_pos s) (by
    rw [E.expect_Y]; unfold Endowment.Y; intro h; apply hs; linarith)
  rw [E.expect_Y] at hj
  unfold costFI
  exact mul_pos (div_pos hβ0 (by linarith)) (by linarith)

/-- O&R p. 365: the gain from defaulting is highest when `ε` takes its maximum value: `Gain`
is strictly increasing in `ε`. -/
theorem gain_strictMono {s t : S} (h : E.ε s < E.ε t) : gain E U s < gain E U t := by
  unfold gain
  have := U.lt (E.Y_pos s) (show E.Y s < E.Y t by unfold Endowment.Y; linarith)
  linarith

/-- **Sustainability of full insurance, O&R (16), p. 365, as an iff.** With every state of
positive probability, honouring full insurance beats every default strategy (every stopping
time, partial defaults included) iff `u(Ȳ + ε) − u(Ȳ) ≤ β/(1 − β)[u(Ȳ) − E u(Ȳ + ε)]` in
every state (equivalently at `ε̄`, by `gain_strictMono`). -/
theorem full_insurance_sustainable_iff {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    (∀ (d : Strategy S) (w : (n : ℕ) → (Fin (n + 1) → S) → ℝ) (Mw : ℝ),
        (∀ n h, |w n h| ≤ Mw) → (∀ n h, w n h ≤ U.u (E.Y (h (Fin.last n)))) →
        payoff E.Ω β d (fun _ => U.u E.Ybar) (fun s => U.u (E.Y s)) w ≤
          U.u E.Ybar / (1 - β)) ↔
      ∀ s, gain E U s ≤ costFI E U β := by
  have h := trigger_iff E.Ω hβ0 hβ1 E.prob_pos (fun _ => U.u E.Ybar) (fun s => U.u (E.Y s))
    (fun s => U.u (E.Y s))
  rw [E.Ω.expect_const, cost_eq_costFI] at h
  exact h

/-- O&R p. 365: "the cost in eq. (15) becomes unboundedly large as `β → 1`", so (16) holds for
all `β` close enough to 1: there is `β₀ < 1` such that full insurance is sustainable for every
`β ∈ [β₀, 1)` (for a nondegenerate shock). -/
theorem sustainable_for_beta_near_one (hnd : ∃ s, E.ε s ≠ 0) :
    ∃ β₀, 0 < β₀ ∧ β₀ < 1 ∧ ∀ β, β₀ ≤ β → β < 1 → ∀ s, gain E U s ≤ costFI E U β := by
  set c := U.u E.Ybar - E.Ω.expect (fun s => U.u (E.Y s)) with hc
  have hcpos : 0 < c := by
    obtain ⟨s, hs⟩ := hnd
    have hj := jensen_strict E.Ω U E.Y_pos (E.prob_pos s) (by
      rw [E.expect_Y]; unfold Endowment.Y; intro h; apply hs; linarith)
    rw [E.expect_Y] at hj
    linarith
  set G := ∑ t, |gain E U t| + 1 with hG
  have hGpos : 0 < G := by
    have : 0 ≤ ∑ t, |gain E U t| := Finset.sum_nonneg fun t _ => abs_nonneg _
    linarith
  refine ⟨G / (G + c), div_pos hGpos (by linarith), (div_lt_one (by linarith)).mpr
    (by linarith), fun β hβ hβ1 s => ?_⟩
  have h1 : 0 < 1 - β := by linarith
  have hk : G ≤ β / (1 - β) * c := by
    rw [div_le_iff₀ (by linarith)] at hβ
    rw [div_mul_eq_mul_div, le_div_iff₀ h1]
    nlinarith
  have hgs : gain E U s ≤ G := by
    have := le_trans (le_abs_self _) (abs_le_sum_abs (fun t => gain E U t) s)
    linarith
  unfold costFI
  rw [← hc]
  linarith

/-- The second-order remainder ratio behind footnote 19: if `u′` is differentiable at `Ȳ`
with derivative `u″(Ȳ)`, then
`[u(Ȳ + h) − u(Ȳ) − u′(Ȳ)h]/h² → u″(Ȳ)/2` as `h → 0` (L'Hôpital).
(O&R footnote 19, p. 365) -/
theorem second_order_ratio {d2 : ℝ} (hd2 : HasDerivAt U.du d2 E.Ybar) :
    Tendsto (fun h => (U.u (E.Ybar + h) - U.u E.Ybar - U.du E.Ybar * h) / h ^ 2) (𝓝[≠] 0)
      (𝓝 (d2 / 2)) := by
  have hY := E.Ybar_pos
  have hnear : ∀ᶠ h in 𝓝[≠] (0 : ℝ), 0 < E.Ybar + h := by
    apply eventually_nhdsWithin_of_eventually_nhds
    have : Tendsto (fun h : ℝ => E.Ybar + h) (𝓝 0) (𝓝 E.Ybar) := by
      simpa using (tendsto_const_nhds (x := E.Ybar)).add (tendsto_id (x := 𝓝 (0 : ℝ)))
    exact this.eventually (Ioi_mem_nhds hY)
  apply HasDerivAt.lhopital_zero_nhdsNE (f' := fun h => U.du (E.Ybar + h) - U.du E.Ybar)
    (g' := fun h => 2 * h)
  · filter_upwards [hnear] with h hh
    have h1 := (U.hasDerivAt (E.Ybar + h) hh).comp h ((hasDerivAt_id' h).const_add E.Ybar)
    have h2 : HasDerivAt (fun x : ℝ => U.du E.Ybar * x) (U.du E.Ybar) h := by
      simpa using (hasDerivAt_id h).const_mul (U.du E.Ybar)
    have h1' : HasDerivAt (fun x : ℝ => U.u (E.Ybar + x)) (U.du (E.Ybar + h)) h :=
      h1.congr_deriv (mul_one _)
    exact HasDerivAt.sub (HasDerivAt.sub_const (U.u E.Ybar) h1') h2
  · filter_upwards with h
    simpa using (hasDerivAt_pow 2 h)
  · filter_upwards [self_mem_nhdsWithin] with h hh
    exact mul_ne_zero two_ne_zero hh
  · apply tendsto_nhdsWithin_of_tendsto_nhds
    have hc : ContinuousAt (fun h => U.u (E.Ybar + h) - U.u E.Ybar - U.du E.Ybar * h) 0 := by
      have hu : ContinuousAt (fun h => U.u (E.Ybar + h)) 0 := by
        have := (U.hasDerivAt E.Ybar hY).continuousAt
        have hadd : ContinuousAt (fun h : ℝ => E.Ybar + h) 0 :=
          (continuous_const.add continuous_id).continuousAt
        exact ContinuousAt.comp_of_eq this hadd (by simp)
      exact (hu.sub continuousAt_const).sub (continuousAt_const.mul continuousAt_id)
    simpa using hc.tendsto
  · apply tendsto_nhdsWithin_of_tendsto_nhds
    simpa using ((continuous_pow 2).tendsto (0 : ℝ))
  · have := (hasDerivAt_iff_tendsto_slope_zero.mp hd2).div_const 2
    refine this.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with h hh
    simp only [smul_eq_mul]
    field_simp

/-- **Footnote 19, made exact**, O&R p. 365: the book's second-order approximation
`Cost ≈ −β u″(Ȳ)Var(ε)/(2(1 − β))` is the small-shock limit: scaling the shock to `tε`,
`Cost(t)/t² → −β u″(Ȳ) E ε²/(2(1 − β))` as `t → 0`, where `u″(Ȳ)` is the derivative of `u′`
at `Ȳ`. -/
theorem footnote_19 {β d2 : ℝ} (hβ1 : β < 1) (hd2 : HasDerivAt U.du d2 E.Ybar) :
    Tendsto (fun t => β / (1 - β) *
        (U.u E.Ybar - E.Ω.expect (fun s => U.u (E.Ybar + t * E.ε s))) / t ^ 2) (𝓝[≠] 0)
      (𝓝 (-(β / (2 * (1 - β))) * d2 * E.Ω.expect (fun s => E.ε s ^ 2))) := by
  set f : ℝ → ℝ := fun h => U.u (E.Ybar + h) - U.u E.Ybar - U.du E.Ybar * h with hf
  have hratio := second_order_ratio E U hd2
  -- the per-state limits
  have hstate : ∀ s, Tendsto (fun t => f (t * E.ε s) / t ^ 2) (𝓝[≠] 0)
      (𝓝 (E.ε s ^ 2 * (d2 / 2))) := by
    intro s
    by_cases h0 : E.ε s = 0
    · simp only [h0, mul_zero, hf, add_zero, sub_self, zero_div, ne_eq,
        OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, zero_mul]
      exact tendsto_const_nhds
    · have hmap : Tendsto (fun t : ℝ => t * E.ε s) (𝓝[≠] (0 : ℝ)) (𝓝[≠] (0 : ℝ)) := by
        have hc : Tendsto (fun t : ℝ => t * E.ε s) (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ)) := by
          have := (tendsto_id (x := 𝓝 (0 : ℝ))).mul_const (E.ε s)
          rw [zero_mul] at this
          exact this
        exact tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
          (hc.mono_left nhdsWithin_le_nhds)
          (by filter_upwards [self_mem_nhdsWithin] with t ht; exact mul_ne_zero ht h0)
      have := (hratio.comp hmap).const_mul (E.ε s ^ 2)
      refine this.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with t ht
      simp only [Function.comp, hf]
      have ht' : t ≠ 0 := ht
      field_simp
  have hsum := tendsto_finsetSum (s := Finset.univ) fun s _ => (hstate s).const_mul (E.Ω.prob s)
  have hlim := hsum.const_mul (-(β / (1 - β)))
  have hval : -(β / (1 - β)) * ∑ s, E.Ω.prob s * (E.ε s ^ 2 * (d2 / 2)) =
      -(β / (2 * (1 - β))) * d2 * E.Ω.expect (fun s => E.ε s ^ 2) := by
    unfold StateSpace.expect
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_congr rfl; intro s _
    have : (1 : ℝ) - β ≠ 0 := by linarith
    field_simp
  rw [hval] at hlim
  refine hlim.congr fun t => ?_
  -- the pointwise identity `Σ π f(tε) = E u(Ȳ + tε) − u(Ȳ)`, using `E ε = 0`
  have hid : ∑ s, E.Ω.prob s * f (t * E.ε s) =
      E.Ω.expect (fun s => U.u (E.Ybar + t * E.ε s)) - U.u E.Ybar := by
    have e : ∑ s, E.Ω.prob s * f (t * E.ε s) =
        E.Ω.expect (fun s => U.u (E.Ybar + t * E.ε s)) - U.u E.Ybar * ∑ s, E.Ω.prob s -
          U.du E.Ybar * t * E.Ω.expect E.ε := by
      unfold StateSpace.expect
      simp only [hf]
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro s _; ring
    rw [e, E.Ω.prob_sum, E.mean_zero]; ring
  have e2 : ∑ s, E.Ω.prob s * (f (t * E.ε s) / t ^ 2) =
      (∑ s, E.Ω.prob s * f (t * E.ε s)) / t ^ 2 := by
    rw [Finset.sum_div]; apply Finset.sum_congr rfl; intro s _; ring
  rw [e2, hid]
  ring

end FullInsurance

/-! ## Finite horizon: reputation unravels (p. 365) -/

namespace FiniteHorizon

variable {S : Type} [Fintype S] (E : Endowment S) (U : Utility)

/-- The one-shot incentive constraint at date `n ≤ T` with a known last date `T`
(O&R p. 365): defaulting in state `ε` at date `n` gains `u(Ȳ + ε) − u(Ȳ + ε − P_n(ε))` and
loses the contracts of dates `n + 1, …, T` only. -/
def FiniteIC (β : ℝ) (T : ℕ) (P : ℕ → S → ℝ) (n : ℕ) : Prop :=
  ∀ s, U.u (E.Y s) - U.u (E.Y s - P n s) ≤
    ∑ k ∈ Finset.Ioc n T, β ^ (k - n) *
      (E.Ω.expect (fun t => U.u (E.Y t - P k t)) - E.Ω.expect (fun t => U.u (E.Y t)))

/-- **Finite-horizon unravelling**, O&R p. 365: if the country has a known last date `T`,
the only sequence of zero-profit contracts (13) with positive consumption that is incentive
compatible at every date is the null contract: by backward induction no creditor "will ever
be paid a penny". -/
theorem finite_horizon_unravels {β : ℝ} (T : ℕ) (P : ℕ → S → ℝ)
    (hZP : ∀ n, E.Ω.expect (P n) = 0) (hC : ∀ n s, 0 < E.Y s - P n s)
    (hIC : ∀ n, n ≤ T → FiniteIC E U β T P n) : ∀ n, n ≤ T → P n = 0 := by
  -- strong backward induction on `T − n`
  have key : ∀ m, ∀ n, T - n = m → n ≤ T → P n = 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro n hm hn
      have hfut : ∀ k ∈ Finset.Ioc n T, P k = 0 := fun k hk => by
        rw [Finset.mem_Ioc] at hk
        exact ih (T - k) (by omega) k rfl hk.2
      have hsum : ∑ k ∈ Finset.Ioc n T, β ^ (k - n) *
          (E.Ω.expect (fun t => U.u (E.Y t - P k t)) - E.Ω.expect (fun t => U.u (E.Y t))) =
          0 := by
        apply Finset.sum_eq_zero; intro k hk
        rw [hfut k hk]; simp
      have hle : ∀ s, P n s ≤ 0 := fun s => by
        have := hIC n hn s
        rw [hsum] at this
        by_contra hp; push Not at hp
        have := U.lt (hC n s) (show E.Y s - P n s < E.Y s by linarith)
        linarith
      funext s
      exact eq_zero_of_nonpos_of_expect_zero E.Ω hle (hZP n) (E.prob_pos s)
  exact fun n hn => key (T - n) n rfl hn

/-- Date-`n` utility in the finite-horizon game (O&R p. 365): honouring the date-`n` contract
gives `v_c(n, ε)`; on or after the first default date the country consumes its endowment
(utility `v_a(ε)`). -/
def flowT (d : Strategy S) (vc : ℕ → S → ℝ) (va : S → ℝ) (n : ℕ) (h : Fin (n + 1) → S) : ℝ :=
  if (defaulted d n (Fin.init h) || d n h) then va (h (Fin.last n)) else vc n (h (Fin.last n))

/-- Expected utility over the finite horizon `0, …, T` (O&R p. 365). -/
noncomputable def payoffT (Ω : StateSpace S) (β : ℝ) (T : ℕ) (d : Strategy S)
    (vc : ℕ → S → ℝ) (va : S → ℝ) : ℝ :=
  ∑ n ∈ Finset.range (T + 1), β ^ n * hexp Ω (n + 1) (flowT d vc va n)

/-- The one-shot default rule "default at date `n₀` iff the date-`n₀` shock is `s₀`" has
defaulted within the first `k` shocks iff `k > n₀` and the `n₀`-th shock is `s₀`. (O&R p. 365) -/
theorem defaulted_oneShot {T : Type} [DecidableEq T] (n₀ : ℕ) (s₀ : T) :
    ∀ k (g : Fin k → T),
      defaulted (fun m h => decide (m = n₀) && decide (h (Fin.last m) = s₀)) k g = true ↔
        ∃ hk : n₀ < k, g ⟨n₀, hk⟩ = s₀ := by
  intro k
  induction k with
  | zero => intro g; simp [defaulted]
  | succ k ih =>
    intro g
    simp only [defaulted, Bool.or_eq_true, ih (Fin.init g), Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro (⟨hk, hg⟩ | ⟨rfl, hg⟩)
      · exact ⟨by omega, hg⟩
      · exact ⟨by omega, hg⟩
    · rintro ⟨hk, hg⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with h | h
      · exact Or.inl ⟨h, hg⟩
      · subst h; exact Or.inr ⟨rfl, hg⟩

/-- **The one-shot constraints follow from the finite-horizon game** (O&R p. 365, backward
induction): if honouring is optimal against every default strategy in the finite-horizon
game with contracts `v_c(n, ·)` (all states of positive probability, `β > 0`), then for every
date `n₀ ≤ T` and state `s₀`, `v_a(s₀) − v_c(n₀, s₀) ≤ Σ_{k ∈ (n₀, T]} β^{k−n₀}(E v_c(k) − E v_a)`:
the one-shot deviation "default at `n₀` in state `s₀`" is unprofitable. -/
theorem finite_game_oneshot (Ω : StateSpace S) (hpos : ∀ s, 0 < Ω.prob s) {β : ℝ}
    (hβ : 0 < β) (T : ℕ) (vc : ℕ → S → ℝ) (va : S → ℝ)
    (hopt : ∀ d, payoffT Ω β T d vc va ≤ payoffT Ω β T (fun _ _ => false) vc va) :
    ∀ n₀, n₀ ≤ T → ∀ s₀, va s₀ - vc n₀ s₀ ≤
      ∑ k ∈ Finset.Ioc n₀ T, β ^ (k - n₀) * (Ω.expect (vc k) - Ω.expect va) := by
  classical
  intro n₀ hn₀ s₀
  set d : Strategy S := fun m h => decide (m = n₀) && decide (h (Fin.last m) = s₀) with hd
  have hnever : ∀ k (g : Fin k → S), defaulted (fun _ _ => false : Strategy S) k g = false := by
    intro k; induction k with
    | zero => intro g; rfl
    | succ k ih => intro g; simp [defaulted, ih]
  -- the per-date difference in expected utility
  set A := Ω.prob s₀ * (va s₀ - vc n₀ s₀)
  set B : ℕ → ℝ := fun m => Ω.prob s₀ * (Ω.expect va - Ω.expect (vc m))
  have hdiff : ∀ m, hexp Ω (m + 1) (flowT d vc va m) -
      hexp Ω (m + 1) (flowT (fun _ _ => false) vc va m) =
      if m < n₀ then 0 else if m = n₀ then A else B m := by
    intro m
    have hcond : ∀ h : Fin (m + 1) → S, (defaulted d m (Fin.init h) || d m h) = true ↔
        ∃ hk : n₀ ≤ m, h ⟨n₀, by omega⟩ = s₀ := by
      intro h
      rw [Bool.or_eq_true, defaulted_oneShot n₀ s₀ m (Fin.init h)]
      simp only [hd, Bool.and_eq_true, decide_eq_true_eq]
      constructor
      · rintro (⟨hk, hg⟩ | ⟨rfl, hg⟩)
        · exact ⟨hk.le, hg⟩
        · exact ⟨le_rfl, hg⟩
      · rintro ⟨hk, hg⟩
        rcases lt_or_eq_of_le hk with h' | h'
        · exact Or.inl ⟨h', hg⟩
        · subst h'; exact Or.inr ⟨rfl, hg⟩
    have hfn : ∀ h : Fin (m + 1) → S, flowT (fun _ _ => false) vc va m h =
        vc m (h (Fin.last m)) := by
      intro h; unfold flowT; rw [hnever m (Fin.init h)]; simp
    have hsub : ∀ X Y : (Fin (m + 1) → S) → ℝ, hexp Ω (m + 1) X - hexp Ω (m + 1) Y =
        hexp Ω (m + 1) (fun h => X h - Y h) := by
      intro X Y; unfold hexp; rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro h _; ring
    rw [hsub]
    by_cases h1 : m < n₀
    · simp only [h1, ↓reduceIte]
      have : (fun h => flowT d vc va m h - flowT (fun _ _ => false) vc va m h) = fun _ => 0 := by
        funext h
        have hc : (defaulted d m (Fin.init h) || d m h) = false := by
          by_contra hc
          rw [Bool.not_eq_false] at hc
          obtain ⟨hk, _⟩ := (hcond h).mp hc
          omega
        rw [hfn]; simp [flowT, hc]
      rw [this, hexp_const]
    · simp only [h1, ↓reduceIte]
      by_cases h2 : m = n₀
      · simp only [h2, ↓reduceIte]
        subst h2
        have : (fun h => flowT d vc va m h - flowT (fun _ _ => false) vc va m h) =
            fun h => (fun _ => (1 : ℝ)) (Fin.init h) *
              (fun s => if s = s₀ then va s - vc m s else 0) (h (Fin.last m)) := by
          funext h
          have hl : (⟨m, by omega⟩ : Fin (m + 1)) = Fin.last m := rfl
          by_cases hs : h (Fin.last m) = s₀
          · have hc : (defaulted d m (Fin.init h) || d m h) = true :=
              (hcond h).mpr ⟨le_rfl, by rw [hl]; exact hs⟩
            rw [hfn]; simp [flowT, hc, hs]
          · have hc : (defaulted d m (Fin.init h) || d m h) = false := by
              by_contra hc
              rw [Bool.not_eq_false] at hc
              obtain ⟨_, hg⟩ := (hcond h).mp hc
              exact hs (by rw [hl] at hg; exact hg)
            rw [hfn]; simp [flowT, hc, hs]
        rw [this]
        have hi := hexp_indep Ω m (fun _ => (1 : ℝ))
          (fun s => if s = s₀ then va s - vc m s else 0)
        simp only at hi ⊢
        rw [hi, hexp_const, one_mul]
        unfold StateSpace.expect
        rw [Finset.sum_eq_single s₀ (fun b _ hb => by simp [hb]) (by simp)]
        simp [A]
      · simp only [h2, ↓reduceIte]
        have hlt : n₀ < m := by omega
        have : (fun h => flowT d vc va m h - flowT (fun _ _ => false) vc va m h) =
            fun h : Fin (m + 1) → S => (fun s => if s = s₀ then (1 : ℝ) else 0)
              (h ⟨n₀, by omega⟩) * (fun s => va s - vc m s) (h (Fin.last m)) := by
          funext h
          by_cases hs : h ⟨n₀, by omega⟩ = s₀
          · have hc : (defaulted d m (Fin.init h) || d m h) = true :=
              (hcond h).mpr ⟨hlt.le, hs⟩
            rw [hfn]; simp [flowT, hc, hs]
          · have hc : (defaulted d m (Fin.init h) || d m h) = false := by
              by_contra hc
              rw [Bool.not_eq_false] at hc
              obtain ⟨_, hg⟩ := (hcond h).mp hc
              exact hs hg
            rw [hfn]; simp [flowT, hc, hs]
        rw [this]
        have hi := hexp_two_coords Ω n₀ m hlt (fun s => if s = s₀ then (1 : ℝ) else 0)
          (fun s => va s - vc m s)
        simp only at hi ⊢
        rw [hi, expect_sub]
        unfold StateSpace.expect
        rw [Finset.sum_eq_single s₀ (fun b _ hb => by simp [hb]) (by simp)]
        simp only [↓reduceIte, mul_one, B]
        unfold StateSpace.expect; ring
  -- summing over dates
  have hsum : ∀ T', n₀ ≤ T' → ∑ m ∈ Finset.range (T' + 1), β ^ m *
      (if m < n₀ then 0 else if m = n₀ then A else B m) =
      β ^ n₀ * (A + ∑ k ∈ Finset.Ioc n₀ T', β ^ (k - n₀) * B k) := by
    intro T' hT'
    induction T', hT' using Nat.le_induction with
    | base =>
      rw [Finset.sum_range_succ, Finset.sum_eq_zero (fun m hm => by
        simp only [Finset.mem_range.mp hm, ↓reduceIte]; ring)]
      simp
    | succ T' hT' ih =>
      have h1 : ¬ T' + 1 < n₀ := by omega
      have h2 : T' + 1 ≠ n₀ := by omega
      rw [Finset.sum_range_succ, ih, Finset.sum_Ioc_succ_top hT']
      simp only [h1, h2, ↓reduceIte]
      have : β ^ (T' + 1) = β ^ n₀ * β ^ (T' + 1 - n₀) := by
        rw [← pow_add]; congr 1; omega
      rw [this]; ring
  have hcomp : payoffT Ω β T d vc va - payoffT Ω β T (fun _ _ => false) vc va =
      β ^ n₀ * (A + ∑ k ∈ Finset.Ioc n₀ T, β ^ (k - n₀) * B k) := by
    unfold payoffT
    rw [← Finset.sum_sub_distrib, ← hsum T hn₀]
    apply Finset.sum_congr rfl; intro m _
    rw [← hdiff m]; ring
  have hle := hopt d
  have hβn : 0 < β ^ n₀ := pow_pos hβ n₀
  have h1 : A + ∑ k ∈ Finset.Ioc n₀ T, β ^ (k - n₀) * B k ≤ 0 := by
    by_contra h; push Not at h
    have := mul_pos hβn h
    linarith
  have hB : ∑ k ∈ Finset.Ioc n₀ T, β ^ (k - n₀) * B k = Ω.prob s₀ *
      ∑ k ∈ Finset.Ioc n₀ T, β ^ (k - n₀) * (Ω.expect va - Ω.expect (vc k)) := by
    rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro k _; simp only [B]; ring
  rw [hB] at h1
  have hp := hpos s₀
  have h2 : va s₀ - vc n₀ s₀ + ∑ k ∈ Finset.Ioc n₀ T, β ^ (k - n₀) *
      (Ω.expect va - Ω.expect (vc k)) ≤ 0 := by
    by_contra h; push Not at h
    have := mul_pos hp h
    simp only [A] at h1; nlinarith
  have hneg : ∑ k ∈ Finset.Ioc n₀ T, β ^ (k - n₀) * (Ω.expect va - Ω.expect (vc k)) =
      -∑ k ∈ Finset.Ioc n₀ T, β ^ (k - n₀) * (Ω.expect (vc k) - Ω.expect va) := by
    rw [← Finset.sum_neg_distrib]; apply Finset.sum_congr rfl; intro k _; ring
  rw [hneg] at h2
  linarith

/-- **Unravelling derived from the finite-horizon game**, O&R p. 365: if honouring a sequence
of zero-profit contracts is optimal against every default strategy of the finite-horizon game
(permanent exclusion after default), every contract up to the last date is null. -/
theorem finite_game_unravels {β : ℝ} (hβ : 0 < β) (T : ℕ) (P : ℕ → S → ℝ)
    (hZP : ∀ n, E.Ω.expect (P n) = 0) (hC : ∀ n s, 0 < E.Y s - P n s)
    (hopt : ∀ d, payoffT E.Ω β T d (fun n s => U.u (E.Y s - P n s)) (fun s => U.u (E.Y s)) ≤
      payoffT E.Ω β T (fun _ _ => false) (fun n s => U.u (E.Y s - P n s))
        (fun s => U.u (E.Y s))) :
    ∀ n, n ≤ T → P n = 0 :=
  finite_horizon_unravels E U (β := β) T P hZP hC fun n hn s =>
    finite_game_oneshot E.Ω E.prob_pos hβ T _ _ hopt n hn s

end FiniteHorizon

/-! ## The lognormal application and Table 6.1 (pp. 366–369) -/

namespace Lognormal

/-- Isoelastic period utility, O&R p. 366: `u(C) = C^{1−ρ}/(1 − ρ)`, `ρ > 0`, `ρ ≠ 1`. -/
noncomputable def crra (ρ C : ℝ) : ℝ := C ^ (1 - ρ) / (1 - ρ)

/-- The growth-adjusted discount factor `q = β(1 + g)^{1−ρ}` (O&R p. 367; the book assumes
`q < 1`). -/
noncomputable def qfac (ρ β g : ℝ) : ℝ := β * (1 + g) ^ (1 - ρ)

/-- The variance factor `X = exp(ρ(ρ − 1)V/2)` of O&R p. 368. -/
noncomputable def Xfac (ρ V : ℝ) : ℝ := Real.exp (ρ * (ρ - 1) * V / 2)

/-- Output `n` dates after `t`, O&R p. 366: `Y_{t+n} = (1 + g)^n Ȳ exp(ε − V/2)`. -/
noncomputable def output (g V Ybar : ℝ) (n : ℕ) (ε : ℝ) : ℝ :=
  (1 + g) ^ n * Ybar * Real.exp (ε - V / 2)

/-- Utility of fully insured consumption `(1 + g)^n Ȳ` (O&R p. 367). -/
noncomputable def fullUtil (ρ g Ybar : ℝ) (n : ℕ) : ℝ := crra ρ ((1 + g) ^ n * Ybar)

/-- Expected autarky utility `n` dates ahead, O&R p. 367:
`E u(Y_{t+n}) = ((1 + g)^n Ȳ)^{1−ρ} exp(−(1 − ρ)V/2) E[e^{(1−ρ)ε}]/(1 − ρ)`, where
`Eexp = E[e^{(1−ρ)ε}]` (the constants come out of the expectation, `crra_output`). -/
noncomputable def autarkyExpUtil (ρ g V Ybar Eexp : ℝ) (n : ℕ) : ℝ :=
  ((1 + g) ^ n * Ybar) ^ (1 - ρ) * Real.exp (-(1 - ρ) * V / 2) * Eexp / (1 - ρ)

/-- The cost of exclusion from date `t + 1` on, O&R p. 367:
`β(Ū_{t+1} − E_t U^A_{t+1}) = Σ_{s ≥ t+1} β^{s−t}[u((1 + g)^{s−t}Ȳ) − E_t u(Y_s)]`. -/
noncomputable def costLN (ρ β g V Ybar Eexp : ℝ) : ℝ :=
  ∑' n : ℕ, β ^ (n + 1) *
    (fullUtil ρ g Ybar (n + 1) - autarkyExpUtil ρ g V Ybar Eexp (n + 1))

/-- The date-`t` gain from default on full insurance, O&R p. 367: `u(Y_t) − u(Ȳ)`. -/
noncomputable def gainLN (ρ g V Ybar ε : ℝ) : ℝ := crra ρ (output g V Ybar 0 ε) - crra ρ Ybar

/-- Real powers of a product of positive growth factors (used on p. 367):
`((1 + g)^n Ȳ)^{1−ρ} = ((1 + g)^{1−ρ})^n Ȳ^{1−ρ}`.
(O&R pp. 367–369) -/
theorem growth_rpow {g Ybar : ℝ} (hg : -1 < g) (hY : 0 < Ybar) (ρ : ℝ) (n : ℕ) :
    ((1 + g) ^ n * Ybar) ^ (1 - ρ) = ((1 + g) ^ (1 - ρ)) ^ n * Ybar ^ (1 - ρ) := by
  have h1 : 0 < 1 + g := by linarith
  rw [Real.mul_rpow (pow_nonneg h1.le n) hY.le]
  congr 1
  rw [← Real.rpow_natCast, ← Real.rpow_mul h1.le, ← Real.rpow_natCast, ← Real.rpow_mul h1.le,
    mul_comm]

/-- The linearity step of p. 367: `u(Y_{t+n}) = ((1 + g)^n Ȳ)^{1−ρ} e^{−(1−ρ)V/2}
e^{(1−ρ)ε}/(1 − ρ)`, so `E u(Y_{t+n})` is `autarkyExpUtil` with `Eexp = E e^{(1−ρ)ε}`.
(O&R pp. 367–369) -/
theorem crra_output {g Ybar : ℝ} (hg : -1 < g) (hY : 0 < Ybar) (ρ V : ℝ) (n : ℕ) (ε : ℝ) :
    crra ρ (output g V Ybar n ε) = ((1 + g) ^ n * Ybar) ^ (1 - ρ) *
      Real.exp (-(1 - ρ) * V / 2) * Real.exp ((1 - ρ) * ε) / (1 - ρ) := by
  have h1 : 0 < 1 + g := by linarith
  unfold crra output
  rw [Real.mul_rpow (by positivity) (Real.exp_pos _).le, ← Real.exp_mul, mul_assoc,
    ← Real.exp_add]
  congr 3; ring

/-- Footnote 20 and p. 367: with the normal moment-generating identity
`E e^{(1−ρ)ε} = exp((1 − ρ)²V/2)`, `exp(−(1 − ρ)V/2) E e^{(1−ρ)ε} = exp(−ρ(1 − ρ)V/2)`.
(O&R pp. 367–369) -/
theorem mgf_step (ρ V : ℝ) :
    Real.exp (-(1 - ρ) * V / 2) * Real.exp ((1 - ρ) ^ 2 * V / 2) =
      Real.exp (-(ρ * (1 - ρ) * V / 2)) := by
  rw [← Real.exp_add]; congr 1; ring

/-- **The closed form for `βŪ_{t+1}`**, O&R p. 367: with `0 ≤ q = β(1 + g)^{1−ρ} < 1`,
`Σ_{n ≥ 1} βⁿ u((1 + g)ⁿȲ) = Ȳ^{1−ρ}/(1 − ρ) · q/(1 − q)`. -/
theorem hasSum_betaUbar {ρ β g Ybar : ℝ} (hg : -1 < g) (hY : 0 < Ybar)
    (hq0 : 0 ≤ qfac ρ β g) (hq1 : qfac ρ β g < 1) :
    HasSum (fun n : ℕ => β ^ (n + 1) * fullUtil ρ g Ybar (n + 1))
      (qfac ρ β g / (1 - qfac ρ β g) * (Ybar ^ (1 - ρ) / (1 - ρ))) := by
  have h := Geometric.hasSum_geometric_from_one hq0 hq1 (Ybar ^ (1 - ρ) / (1 - ρ))
  convert h using 1
  funext n
  unfold fullUtil crra qfac
  rw [growth_rpow hg hY, mul_pow]
  ring

/-- **The closed form for `βE_tU^A_{t+1}`**, O&R p. 367: with the moment-generating identity,
`Σ_{n ≥ 1} βⁿ E u(Y_{t+n}) = Ȳ^{1−ρ}/(1 − ρ) · q/(1 − q) · exp(−ρ(1 − ρ)V/2)`. -/
theorem hasSum_betaEUA {ρ β g V Ybar Eexp : ℝ} (hg : -1 < g) (hY : 0 < Ybar)
    (hq0 : 0 ≤ qfac ρ β g) (hq1 : qfac ρ β g < 1)
    (hmgf : Eexp = Real.exp ((1 - ρ) ^ 2 * V / 2)) :
    HasSum (fun n : ℕ => β ^ (n + 1) * autarkyExpUtil ρ g V Ybar Eexp (n + 1))
      (qfac ρ β g / (1 - qfac ρ β g) *
        (Ybar ^ (1 - ρ) / (1 - ρ) * Real.exp (-(ρ * (1 - ρ) * V / 2)))) := by
  have h := Geometric.hasSum_geometric_from_one hq0 hq1
    (Ybar ^ (1 - ρ) / (1 - ρ) * Real.exp (-(ρ * (1 - ρ) * V / 2)))
  convert h using 1
  funext n
  unfold autarkyExpUtil qfac
  rw [growth_rpow hg hY, mul_pow, hmgf, ← mgf_step]
  ring

/-- **The cost of exclusion in closed form**, O&R p. 367:
`β(Ū − EU^A) = Ȳ^{1−ρ}/(1 − ρ) · q/(1 − q) · [1 − exp(−ρ(1 − ρ)V/2)]`. -/
theorem costLN_eq {ρ β g V Ybar Eexp : ℝ} (hg : -1 < g) (hY : 0 < Ybar)
    (hq0 : 0 ≤ qfac ρ β g) (hq1 : qfac ρ β g < 1)
    (hmgf : Eexp = Real.exp ((1 - ρ) ^ 2 * V / 2)) :
    costLN ρ β g V Ybar Eexp = Ybar ^ (1 - ρ) / (1 - ρ) * (qfac ρ β g / (1 - qfac ρ β g)) *
      (1 - Real.exp (-(ρ * (1 - ρ) * V / 2))) := by
  unfold costLN
  have h := (hasSum_betaUbar hg hY hq0 hq1).sub (hasSum_betaEUA (V := V) hg hY hq0 hq1 hmgf)
  rw [show (fun n : ℕ => β ^ (n + 1) * (fullUtil ρ g Ybar (n + 1) -
      autarkyExpUtil ρ g V Ybar Eexp (n + 1))) = fun n : ℕ =>
      β ^ (n + 1) * fullUtil ρ g Ybar (n + 1) -
        β ^ (n + 1) * autarkyExpUtil ρ g V Ybar Eexp (n + 1) from funext fun n => by ring,
    h.tsum_eq]
  ring

/-- O&R p. 367: `βE_tU^A_{t+1} < βŪ_{t+1}`: the cost of exclusion is positive whenever
`ρ ≠ 1`, `V > 0` and `0 < q < 1`. -/
theorem costLN_pos {ρ β g V Ybar Eexp : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≠ 1) (hV : 0 < V)
    (hg : -1 < g) (hY : 0 < Ybar) (hq0 : 0 < qfac ρ β g) (hq1 : qfac ρ β g < 1)
    (hmgf : Eexp = Real.exp ((1 - ρ) ^ 2 * V / 2)) : 0 < costLN ρ β g V Ybar Eexp := by
  rw [costLN_eq hg hY hq0.le hq1 hmgf]
  have hA : 0 < Ybar ^ (1 - ρ) := Real.rpow_pos_of_pos hY _
  have hqq : 0 < qfac ρ β g / (1 - qfac ρ β g) := div_pos hq0 (by linarith)
  rcases lt_or_gt_of_ne hρ1 with h | h
  · have he : Real.exp (-(ρ * (1 - ρ) * V / 2)) < 1 := by
      rw [Real.exp_lt_one_iff]
      have : 0 < ρ * (1 - ρ) * V := by
        apply mul_pos (mul_pos hρ0 (by linarith)) hV
      linarith
    have : 0 < Ybar ^ (1 - ρ) / (1 - ρ) := div_pos hA (by linarith)
    have := mul_pos (mul_pos this hqq) (show 0 < 1 - Real.exp (-(ρ * (1 - ρ) * V / 2)) by
      linarith)
    linarith
  · have he : 1 < Real.exp (-(ρ * (1 - ρ) * V / 2)) := by
      rw [Real.one_lt_exp_iff]
      have : 0 < ρ * (ρ - 1) * V := mul_pos (mul_pos hρ0 (by linarith)) hV
      nlinarith
    have hneg : Ybar ^ (1 - ρ) / (1 - ρ) < 0 := div_neg_of_pos_of_neg hA (by linarith)
    have h2 : 1 - Real.exp (-(ρ * (1 - ρ) * V / 2)) < 0 := by linarith
    have := mul_pos_of_neg_of_neg (mul_neg_of_neg_of_pos hneg hqq) h2
    linarith

/-- The date-`t` gain in exponential form: `u(Ȳe^{ε−V/2}) − u(Ȳ) =
Ȳ^{1−ρ}[e^{(1−ρ)(ε−V/2)} − 1]/(1 − ρ)` (O&R p. 367). -/
theorem gainLN_eq {ρ Ybar : ℝ} (hY : 0 < Ybar) (g V ε : ℝ) :
    gainLN ρ g V Ybar ε =
      Ybar ^ (1 - ρ) * (Real.exp ((1 - ρ) * (ε - V / 2)) - 1) / (1 - ρ) := by
  unfold gainLN crra output
  rw [pow_zero, one_mul, Real.mul_rpow hY.le (Real.exp_pos _).le, ← Real.exp_mul]
  rw [show (ε - V / 2) * (1 - ρ) = (1 - ρ) * (ε - V / 2) by ring]
  ring

/-- **Sustainability of full insurance with `ρ > 1`**, O&R p. 368: exclusion from world
insurance markets supports full insurance for *every* output realisation iff
`1 ≤ β(1 + g)^{1−ρ} exp(ρ(ρ − 1)V/2)`. -/
theorem sustainable_iff_rho_gt_one {ρ β g V Ybar Eexp : ℝ} (hρ : 1 < ρ) (hg : -1 < g)
    (hY : 0 < Ybar) (hq0 : 0 ≤ qfac ρ β g) (hq1 : qfac ρ β g < 1)
    (hmgf : Eexp = Real.exp ((1 - ρ) ^ 2 * V / 2)) :
    (∀ ε : ℝ, gainLN ρ g V Ybar ε ≤ costLN ρ β g V Ybar Eexp) ↔
      1 ≤ qfac ρ β g * Xfac ρ V := by
  have hX : Real.exp (-(ρ * (1 - ρ) * V / 2)) = Xfac ρ V := by
    unfold Xfac; congr 1; ring
  have hc := costLN_eq (V := V) (Eexp := Eexp) hg hY hq0 hq1 hmgf
  rw [hX] at hc
  have hgain : ∀ ε, gainLN ρ g V Ybar ε =
      Ybar ^ (1 - ρ) * (Real.exp ((1 - ρ) * (ε - V / 2)) - 1) / (1 - ρ) :=
    fun ε => gainLN_eq hY g V ε
  simp only [hgain, hc]
  generalize qfac ρ β g = q at hq0 hq1 ⊢
  generalize Xfac ρ V = X
  have hApos : 0 < Ybar ^ (1 - ρ) := Real.rpow_pos_of_pos hY _
  generalize Ybar ^ (1 - ρ) = A at hApos ⊢
  have hm : 0 < ρ - 1 := by linarith
  have h1ρ : (1 : ℝ) - ρ ≠ 0 := by linarith
  have h1q : (0 : ℝ) < 1 - q := by linarith
  -- rewrite both sides with the positive factor `A/(ρ − 1)`
  have hcost : A / (1 - ρ) * (q / (1 - q)) * (1 - X) = A / (ρ - 1) * (q * (X - 1) / (1 - q)) := by
    field_simp; ring
  have hg' : ∀ ε, A * (Real.exp ((1 - ρ) * (ε - V / 2)) - 1) / (1 - ρ) =
      A / (ρ - 1) * (1 - Real.exp ((1 - ρ) * (ε - V / 2))) := by
    intro ε; field_simp; ring
  simp only [hcost, hg']
  have hAm : 0 < A / (ρ - 1) := div_pos hApos hm
  constructor
  · intro H
    by_contra hlt; push Not at hlt
    have hc1 : q * (X - 1) / (1 - q) < 1 := by
      rw [div_lt_one h1q]; linarith
    set δ := 1 - q * (X - 1) / (1 - q) with hδ
    have hδpos : 0 < δ := by linarith
    have hexp : Real.exp ((1 - ρ) * (V / 2 + Real.log δ / (1 - ρ) + 1 - V / 2)) < δ := by
      have : (1 - ρ) * (V / 2 + Real.log δ / (1 - ρ) + 1 - V / 2) = Real.log δ + (1 - ρ) := by
        field_simp; ring
      rw [this, Real.exp_add, Real.exp_log hδpos]
      have : Real.exp (1 - ρ) < 1 := by rw [Real.exp_lt_one_iff]; linarith
      nlinarith
    have h := H (V / 2 + Real.log δ / (1 - ρ) + 1)
    have h2 := mul_lt_mul_of_pos_left (show 1 - δ < 1 - Real.exp ((1 - ρ) *
      (V / 2 + Real.log δ / (1 - ρ) + 1 - V / 2)) by linarith) hAm
    have h3 : 1 - δ = q * (X - 1) / (1 - q) := by rw [hδ]; ring
    rw [h3] at h2
    linarith
  · intro H ε
    have h1 : 1 ≤ q * (X - 1) / (1 - q) := by
      rw [le_div_iff₀ h1q]; linarith
    have h2 : 1 - Real.exp ((1 - ρ) * (ε - V / 2)) < 1 := by
      have := Real.exp_pos ((1 - ρ) * (ε - V / 2)); linarith
    have := mul_lt_mul_of_pos_left h2 hAm
    nlinarith

/-- **With `ρ < 1` full insurance is never sustainable**, O&R p. 367: marginal utility falls off
slowly, so some output realisation makes default profitable. -/
theorem not_sustainable_rho_lt_one {ρ β g V Ybar Eexp : ℝ} (hρ : ρ < 1) (hY : 0 < Ybar) :
    ¬ ∀ ε : ℝ, gainLN ρ g V Ybar ε ≤ costLN ρ β g V Ybar Eexp := by
  intro H
  set A := Ybar ^ (1 - ρ)
  have hApos : 0 < A := Real.rpow_pos_of_pos hY _
  have h1 : 0 < 1 - ρ := by linarith
  set K := costLN ρ β g V Ybar Eexp
  -- choose ε with e^{(1−ρ)(ε − V/2)} > 1 + (1 − ρ)|K|/A
  set T := 1 + (1 - ρ) * |K| / A + 1
  have hT : 0 < T := by have : 0 ≤ (1 - ρ) * |K| / A := by positivity
                        linarith
  set ε := V / 2 + Real.log T / (1 - ρ)
  have he : Real.exp ((1 - ρ) * (ε - V / 2)) = T := by
    have : (1 - ρ) * (ε - V / 2) = Real.log T := by simp only [ε]; field_simp; ring
    rw [this, Real.exp_log hT]
  have := H ε
  rw [gainLN_eq hY, he] at this
  have hK : K ≤ |K| := le_abs_self K
  have : A * (T - 1) / (1 - ρ) = A / (1 - ρ) + |K| := by
    simp only [T]; field_simp; ring
  have : A / (1 - ρ) > 0 := div_pos hApos h1
  linarith

/-- The cost of exclusion with log utility (`ρ = 1`), O&R p. 367: with `E ε = 0`,
`E log Y_{t+n} = log((1 + g)^n Ȳ) − V/2`, so the cost is `Σ_{n ≥ 1} βⁿ V/2 = βV/(2(1 − β))`. -/
noncomputable def costLog (β V : ℝ) : ℝ := ∑' n : ℕ, β ^ (n + 1) * (V / 2)

/-- The closed form of the log cost, `βV/(2(1 − β))` (O&R p. 367, `ρ = 1`). -/
theorem costLog_eq {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (V : ℝ) :
    costLog β V = β / (1 - β) * (V / 2) :=
  (Geometric.hasSum_geometric_from_one hβ0 hβ1 _).tsum_eq

/-- **With log utility full insurance is never sustainable**, O&R p. 367 (`ρ ≤ 1`): the gain
`log(Ȳe^{ε−V/2}) − log Ȳ = ε − V/2` is unbounded. -/
theorem not_sustainable_log {β V Ybar : ℝ} (hY : 0 < Ybar) :
    ¬ ∀ ε : ℝ, Real.log (Ybar * Real.exp (ε - V / 2)) - Real.log Ybar ≤ costLog β V := by
  intro H
  have := H (V / 2 + |costLog β V| + 1)
  rw [Real.log_mul hY.ne' (Real.exp_pos _).ne', Real.log_exp] at this
  have := le_abs_self (costLog β V)
  linarith

/-- The cost of exclusion as a fraction of current mean output, O&R p. 368:
`κ = [(1 − qX)/(1 − q)]^{−1/(ρ−1)} − 1`. -/
noncomputable def kappa (ρ β g V : ℝ) : ℝ :=
  ((1 - qfac ρ β g * Xfac ρ V) / (1 - qfac ρ β g)) ^ (-1 / (ρ - 1)) - 1

/-- **The formula for `κ`**, O&R p. 368: for `ρ > 1` and `0 ≤ q`, `qX < 1`, `κ` solves
`u((1 + κ)Ȳ) − u(Ȳ) = β(Ū_{t+1} − E_tU^A_{t+1})`, and it is the only solution with
`κ > −1`. -/
theorem kappa_iff {ρ β g V Ybar Eexp : ℝ} (hρ : 1 < ρ) (hV : 0 ≤ V) (hg : -1 < g)
    (hY : 0 < Ybar) (hq0 : 0 ≤ qfac ρ β g) (hqX : qfac ρ β g * Xfac ρ V < 1)
    (hmgf : Eexp = Real.exp ((1 - ρ) ^ 2 * V / 2)) (k : ℝ) (hk : -1 < k) :
    crra ρ ((1 + k) * Ybar) - crra ρ Ybar = costLN ρ β g V Ybar Eexp ↔ k = kappa ρ β g V := by
  have hX1 : 1 ≤ Xfac ρ V := by
    unfold Xfac; apply Real.one_le_exp
    have : 0 ≤ ρ * (ρ - 1) := mul_nonneg (by linarith) (by linarith)
    have := mul_nonneg this hV; linarith
  have hq1 : qfac ρ β g < 1 := by nlinarith
  have hX : Real.exp (-(ρ * (1 - ρ) * V / 2)) = Xfac ρ V := by unfold Xfac; congr 1; ring
  have hc := costLN_eq (V := V) (Eexp := Eexp) hg hY hq0 hq1 hmgf
  rw [hX] at hc
  have hk1 : 0 < 1 + k := by linarith
  have e1 : crra ρ ((1 + k) * Ybar) - crra ρ Ybar =
      Ybar ^ (1 - ρ) / (1 - ρ) * ((1 + k) ^ (1 - ρ) - 1) := by
    unfold crra; rw [Real.mul_rpow hk1.le hY.le]; ring
  rw [e1, hc]
  unfold kappa
  generalize qfac ρ β g = q at hq0 hq1 hqX ⊢
  generalize Xfac ρ V = X at hX1 hqX ⊢
  have hA : 0 < Ybar ^ (1 - ρ) := Real.rpow_pos_of_pos hY _
  have h1ρ : (1 : ℝ) - ρ ≠ 0 := by linarith
  have h1q : (0 : ℝ) < 1 - q := by linarith
  have hR : 0 < (1 - q * X) / (1 - q) := div_pos (by linarith) h1q
  have hne : Ybar ^ (1 - ρ) / (1 - ρ) ≠ 0 := div_ne_zero hA.ne' h1ρ
  have hm1 : ρ - 1 ≠ 0 := by linarith
  rw [mul_assoc, mul_right_inj' hne]
  have e3 : q / (1 - q) * (1 - X) = (1 - q * X) / (1 - q) - 1 := by field_simp; ring
  rw [e3]
  constructor
  · intro h
    have h' : (1 + k) ^ (1 - ρ) = (1 - q * X) / (1 - q) := by linarith
    have : 1 + k = ((1 - q * X) / (1 - q)) ^ (-1 / (ρ - 1)) := by
      rw [← h', ← Real.rpow_mul hk1.le]
      rw [show (1 - ρ) * (-1 / (ρ - 1)) = 1 by field_simp; ring, Real.rpow_one]
    linarith
  · intro h
    have : 1 + k = ((1 - q * X) / (1 - q)) ^ (-1 / (ρ - 1)) := by linarith
    rw [this, ← Real.rpow_mul hR.le]
    rw [show -1 / (ρ - 1) * (1 - ρ) = 1 by field_simp; ring, Real.rpow_one]

/-- O&R p. 368: "`Cost/Y → ∞` as `β(1 + g)^{1−ρ}exp[ρ(ρ − 1)V/2] → 1` from below": as the
ratio `R = (1 − qX)/(1 − q)` falls to zero, `R^{−1/(ρ−1)} − 1 → ∞`. -/
theorem kappa_tendsto_top {ρ : ℝ} (hρ : 1 < ρ) :
    Tendsto (fun R : ℝ => R ^ (-1 / (ρ - 1)) - 1) (𝓝[>] 0) atTop := by
  have h : -1 / (ρ - 1) < 0 := div_neg_of_neg_of_pos (by norm_num) (by linarith)
  exact tendsto_atTop_add_const_right _ (-1) (tendsto_rpow_neg_nhdsGT_zero h)

/-- The annuitised cost of consumption variability, O&R p. 368 (and p. 330):
`τ = {exp[(1 − ρ)ρV/2]}^{1/(1−ρ)} − 1`. -/
noncomputable def tau (ρ V : ℝ) : ℝ := Real.exp ((1 - ρ) * ρ * V / 2) ^ (1 / (1 - ρ)) - 1

/-- **`τ = exp(ρV/2) − 1` exactly**, O&R p. 368: the book's unsimplified formula reduces. -/
theorem tau_eq {ρ : ℝ} (hρ : ρ ≠ 1) (V : ℝ) : tau ρ V = Real.exp (ρ * V / 2) - 1 := by
  unfold tau
  rw [← Real.exp_mul]
  congr 2
  have : (1 : ℝ) - ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm hρ)
  field_simp

/-- **`τ` is the proportional consumption increase that compensates for variability**, O&R
p. 368 (p. 330): `τ > −1` solves `(1 + τ)^{1−ρ} exp(−ρ(1 − ρ)V/2) = 1`
(i.e. `E u((1 + τ)Y) = u(E Y)`) iff `τ = exp(ρV/2) − 1`. -/
theorem tau_iff {ρ : ℝ} (hρ : ρ ≠ 1) (V t : ℝ) (ht : -1 < t) :
    (1 + t) ^ (1 - ρ) * Real.exp (-(ρ * (1 - ρ) * V / 2)) = 1 ↔ t = tau ρ V := by
  rw [tau_eq hρ]
  have h1 : 0 < 1 + t := by linarith
  have hne : (1 : ℝ) - ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm hρ)
  have key : (1 + t) ^ (1 - ρ) * Real.exp (-(ρ * (1 - ρ) * V / 2)) =
      Real.exp ((1 - ρ) * (Real.log (1 + t) - ρ * V / 2)) := by
    rw [Real.rpow_def_of_pos h1, ← Real.exp_add]; congr 1; ring
  rw [key, Real.exp_eq_one_iff, mul_eq_zero, or_iff_right hne, sub_eq_zero]
  constructor
  · intro h
    have := congrArg Real.exp h
    rw [Real.exp_log h1] at this
    linarith
  · intro h
    rw [h, add_sub_cancel, Real.log_exp]

/-! ### Table 6.1 (`β = 0.95`, `ρ = 4`) -/

/-- With `ρ = 4`: `(1 + g)^{1−ρ} = 1/(1 + g)³` (O&R Table 6.1). -/
theorem growth_rho_four {g : ℝ} (hg : -1 < g) : (1 + g) ^ ((1 : ℝ) - 4) = 1 / (1 + g) ^ 3 := by
  have h1 : 0 < 1 + g := by linarith
  rw [show (1 : ℝ) - 4 = -(3 : ℕ) by norm_num, Real.rpow_neg h1.le, Real.rpow_natCast,
    one_div]

/-- With `ρ = 4`: `X = exp(6V)` (O&R Table 6.1). -/
theorem Xfac_rho_four (V : ℝ) : Xfac 4 V = Real.exp (6 * V) := by
  unfold Xfac; congr 1; ring

/-- The cube-root step for Table 6.1: for `R > 0` and `c > 0`, `c < R^{−1/3}` iff
`R c³ < 1`.
(O&R pp. 367–369) -/
theorem lt_rpow_neg_third_iff {R c : ℝ} (hR : 0 < R) (hc : 0 < c) :
    c < R ^ (-1 / ((4 : ℝ) - 1)) ↔ R * c ^ 3 < 1 := by
  set y := R ^ (-1 / ((4 : ℝ) - 1))
  have hy : 0 < y := Real.rpow_pos_of_pos hR _
  have hy3 : y ^ 3 = R⁻¹ := by
    simp only [y]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hR.le]
    norm_num
    exact Real.rpow_neg_one R
  constructor
  · intro h
    have : c ^ 3 < y ^ 3 := pow_lt_pow_left₀ h hc.le (by norm_num)
    rw [hy3] at this
    have := mul_lt_mul_of_pos_left this hR
    rwa [mul_inv_cancel₀ hR.ne'] at this
  · intro h
    by_contra hn; push Not at hn
    have : y ^ 3 ≤ c ^ 3 := pow_le_pow_left₀ hy.le hn 3
    rw [hy3] at this
    have := mul_le_mul_of_nonneg_left this hR.le
    rw [mul_inv_cancel₀ hR.ne'] at this
    linarith

/-- The cube-root step for Table 6.1, upper form: for `R > 0` and `c > 0`,
`R^{−1/3} < c` iff `1 < R c³`.
(O&R pp. 367–369) -/
theorem rpow_neg_third_lt_iff {R c : ℝ} (hR : 0 < R) (hc : 0 < c) :
    R ^ (-1 / ((4 : ℝ) - 1)) < c ↔ 1 < R * c ^ 3 := by
  set y := R ^ (-1 / ((4 : ℝ) - 1))
  have hy : 0 < y := Real.rpow_pos_of_pos hR _
  have hy3 : y ^ 3 = R⁻¹ := by
    simp only [y]
    rw [← Real.rpow_natCast, ← Real.rpow_mul hR.le]
    norm_num
    exact Real.rpow_neg_one R
  constructor
  · intro h
    have : y ^ 3 < c ^ 3 := pow_lt_pow_left₀ h hy.le (by norm_num)
    rw [hy3] at this
    have := mul_lt_mul_of_pos_left this hR
    rwa [mul_inv_cancel₀ hR.ne'] at this
  · intro h
    by_contra hn; push Not at hn
    have : c ^ 3 ≤ y ^ 3 := pow_le_pow_left₀ hc.le hn 3
    rw [hy3] at this
    have := mul_le_mul_of_nonneg_left this hR.le
    rw [mul_inv_cancel₀ hR.ne'] at this
    linarith

/-- The interval lemma behind the numerical entries of Table 6.1: bounds `X_lo ≤ X ≤ X_hi`
on `X = exp(6V)` and two rational inequalities give `a < κ < b`.
(O&R pp. 367–369) -/
theorem kappa_between {q X Xlo Xhi a b : ℝ} (hq0 : 0 < q) (hq1 : q < 1) (hXlo : Xlo ≤ X)
    (hXhi : X ≤ Xhi) (hpos : q * Xhi < 1) (ha : -1 < a) (hb : -1 < b)
    (hlo : (1 - q * Xlo) * (1 + a) ^ 3 < 1 - q) (hhi : 1 - q < (1 - q * Xhi) * (1 + b) ^ 3) :
    a < ((1 - q * X) / (1 - q)) ^ (-1 / ((4 : ℝ) - 1)) - 1 ∧
      ((1 - q * X) / (1 - q)) ^ (-1 / ((4 : ℝ) - 1)) - 1 < b := by
  have h1q : 0 < 1 - q := by linarith
  have hqX : q * X ≤ q * Xhi := mul_le_mul_of_nonneg_left hXhi hq0.le
  have hR : 0 < (1 - q * X) / (1 - q) := div_pos (by linarith) h1q
  have ha3 : 0 ≤ (1 + a) ^ 3 := pow_nonneg (by linarith) 3
  have hb3 : 0 ≤ (1 + b) ^ 3 := pow_nonneg (by linarith) 3
  constructor
  · have := (lt_rpow_neg_third_iff hR (show 0 < 1 + a by linarith)).mpr (by
      rw [div_mul_eq_mul_div, div_lt_one h1q]
      have : q * Xlo ≤ q * X := mul_le_mul_of_nonneg_left hXlo hq0.le
      nlinarith)
    linarith
  · have := (rpow_neg_third_lt_iff hR (show 0 < 1 + b by linarith)).mpr (by
      rw [div_mul_eq_mul_div, one_lt_div h1q]
      nlinarith)
    linarith

/-- `κ` for `ρ = 4` in the form used for Table 6.1: `q = β/(1 + g)³`, `X = exp(6σ²)`.
(O&R pp. 367–369) -/
theorem kappa_rho_four {β g σ : ℝ} (hg : -1 < g) :
    kappa 4 β g (σ ^ 2) = ((1 - β / (1 + g) ^ 3 * Real.exp (6 * σ ^ 2)) /
      (1 - β / (1 + g) ^ 3)) ^ (-1 / ((4 : ℝ) - 1)) - 1 := by
  unfold kappa qfac
  rw [growth_rho_four hg, Xfac_rho_four]
  ring_nf

end Lognormal

open Lognormal

namespace Table61

/-- The fifth-order Taylor polynomial of `exp`, used for the interval bounds of Table 6.1.
(O&R Table 6.1, p. 369) -/
noncomputable def T5 (x : ℝ) : ℝ := 1 + x + x ^ 2 / 2 + x ^ 3 / 6 + x ^ 4 / 24

/-- Lower Taylor bound `T5(x) ≤ exp x` for `x ≥ 0`.
(O&R Table 6.1, p. 369) -/
theorem T5_le_exp {x : ℝ} (hx : 0 ≤ x) : T5 x ≤ Real.exp x := by
  have h := Real.sum_le_exp_of_nonneg hx 5
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  unfold T5; norm_num at h; linarith

/-- Upper Taylor bound `exp x ≤ T5(x) + x⁵/100` for `0 ≤ x ≤ 1`.
(O&R Table 6.1, p. 369) -/
theorem exp_le_T5 {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) : Real.exp x ≤ T5 x + x ^ 5 / 100 := by
  have h := Real.exp_bound' hx hx1 (show 0 < 5 by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  unfold T5; norm_num at h; linarith

/-- The entry lemma for the `κ` column of Table 6.1 (`ρ = 4`): with `q = β/(1 + g)³` and
`x = 6σ²`, rational inequalities on the Taylor bounds give `a < κ < b`.
(O&R Table 6.1, p. 369) -/
theorem kappa_entry {β g σ a b : ℝ} (hg : -1 < g) (hx1 : 6 * σ ^ 2 ≤ 1)
    (hq0 : 0 < β / (1 + g) ^ 3) (hq1 : β / (1 + g) ^ 3 < 1)
    (hpos : β / (1 + g) ^ 3 * (T5 (6 * σ ^ 2) + (6 * σ ^ 2) ^ 5 / 100) < 1)
    (ha : -1 < a) (hb : -1 < b)
    (hlo : (1 - β / (1 + g) ^ 3 * T5 (6 * σ ^ 2)) * (1 + a) ^ 3 < 1 - β / (1 + g) ^ 3)
    (hhi : 1 - β / (1 + g) ^ 3 <
      (1 - β / (1 + g) ^ 3 * (T5 (6 * σ ^ 2) + (6 * σ ^ 2) ^ 5 / 100)) * (1 + b) ^ 3) :
    a < kappa 4 β g (σ ^ 2) ∧ kappa 4 β g (σ ^ 2) < b := by
  rw [kappa_rho_four hg]
  have hx : 0 ≤ 6 * σ ^ 2 := by positivity
  exact kappa_between hq0 hq1 (T5_le_exp hx) (exp_le_T5 hx hx1) hpos ha hb hlo hhi

/-- The entry lemma for the `τ` column of Table 6.1 (`ρ = 4`, `τ = exp(2σ²) − 1`).
(O&R Table 6.1, p. 369) -/
theorem tau_entry {σ a b : ℝ} (hx1 : 2 * σ ^ 2 ≤ 1) (hlo : a < T5 (2 * σ ^ 2) - 1)
    (hhi : T5 (2 * σ ^ 2) + (2 * σ ^ 2) ^ 5 / 100 - 1 < b) :
    a < tau 4 (σ ^ 2) ∧ tau 4 (σ ^ 2) < b := by
  rw [tau_eq (by norm_num), show (4 : ℝ) * σ ^ 2 / 2 = 2 * σ ^ 2 by ring]
  have hx : 0 ≤ 2 * σ ^ 2 := by positivity
  exact ⟨by linarith [T5_le_exp hx], by linarith [exp_le_T5 hx hx1]⟩

end Table61

open Table61

/-- Table 6.1, **Argentina** (`g = 0.015`, `σ = 0.099`), O&R p. 369: `κ ∈ (0.35, 0.37)`
(printed 0.36) and `τ ∈ (0.019, 0.021)` (printed 0.020). -/
theorem table_argentina :
    ((0.35 : ℝ) < kappa 4 0.95 0.015 (0.099 ^ 2) ∧ kappa 4 0.95 0.015 (0.099 ^ 2) < 0.37) ∧
      ((0.019 : ℝ) < tau 4 (0.099 ^ 2) ∧ tau 4 (0.099 ^ 2) < 0.021) :=
  ⟨kappa_entry (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [T5]) (by norm_num) (by norm_num) (by norm_num [T5]) (by norm_num [T5]),
    tau_entry (by norm_num) (by norm_num [T5]) (by norm_num [T5])⟩

/-- Table 6.1, **Brazil** (`g = 0.040`, `σ = 0.117`), O&R p. 369: `κ ∈ (0.23, 0.235)` (printed
0.24, which the rounded inputs do not reproduce: `κ < 0.235`) and `τ ∈ (0.0275, 0.028)`
(printed 0.028). -/
theorem table_brazil :
    ((0.23 : ℝ) < kappa 4 0.95 0.040 (0.117 ^ 2) ∧
        kappa 4 0.95 0.040 (0.117 ^ 2) < 0.235) ∧
      ((0.0275 : ℝ) < tau 4 (0.117 ^ 2) ∧ tau 4 (0.117 ^ 2) < 0.028) :=
  ⟨kappa_entry (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [T5]) (by norm_num) (by norm_num) (by norm_num [T5]) (by norm_num [T5]),
    tau_entry (by norm_num) (by norm_num [T5]) (by norm_num [T5])⟩

/-- Table 6.1, **Colombia** (`g = 0.023`, `σ = 0.050`), O&R p. 369: `κ ∈ (0.04, 0.05)` (printed
0.04) and `τ ∈ (0.004, 0.006)` (printed 0.005). -/
theorem table_colombia :
    ((0.04 : ℝ) < kappa 4 0.95 0.023 (0.050 ^ 2) ∧
        kappa 4 0.95 0.023 (0.050 ^ 2) < 0.05) ∧
      ((0.004 : ℝ) < tau 4 (0.050 ^ 2) ∧ tau 4 (0.050 ^ 2) < 0.006) :=
  ⟨kappa_entry (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [T5]) (by norm_num) (by norm_num) (by norm_num [T5]) (by norm_num [T5]),
    tau_entry (by norm_num) (by norm_num [T5]) (by norm_num [T5])⟩

/-- Table 6.1, **Lesotho** (`g = 0.053`, `σ = 0.160`), O&R p. 369: `κ ∈ (0.53, 0.54)` (printed
0.53) and `τ ∈ (0.052, 0.053)` (printed 0.052). -/
theorem table_lesotho :
    ((0.53 : ℝ) < kappa 4 0.95 0.053 (0.160 ^ 2) ∧
        kappa 4 0.95 0.053 (0.160 ^ 2) < 0.54) ∧
      ((0.052 : ℝ) < tau 4 (0.160 ^ 2) ∧ tau 4 (0.160 ^ 2) < 0.053) :=
  ⟨kappa_entry (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [T5]) (by norm_num) (by norm_num) (by norm_num [T5]) (by norm_num [T5]),
    tau_entry (by norm_num) (by norm_num [T5]) (by norm_num [T5])⟩

/-- Table 6.1, **Mexico** (`g = 0.030`, `σ = 0.088`), O&R p. 369: `κ ∈ (0.13, 0.14)` (printed 0.13)
and `τ ∈ (0.015, 0.016)` (printed 0.016). -/
theorem table_mexico :
    ((0.13 : ℝ) < kappa 4 0.95 0.030 (0.088 ^ 2) ∧
        kappa 4 0.95 0.030 (0.088 ^ 2) < 0.14) ∧
      ((0.015 : ℝ) < tau 4 (0.088 ^ 2) ∧ tau 4 (0.088 ^ 2) < 0.016) :=
  ⟨kappa_entry (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [T5]) (by norm_num) (by norm_num) (by norm_num [T5]) (by norm_num [T5]),
    tau_entry (by norm_num) (by norm_num [T5]) (by norm_num [T5])⟩

/-- Table 6.1, **Philippines** (`g = 0.023`, `σ = 0.100`), O&R p. 369: `κ ∈ (0.245, 0.25)` (printed
0.24; the rounded inputs give `κ > 0.245`) and `τ ∈ (0.02, 0.0203)` (printed 0.020). -/
theorem table_philippines :
    ((0.245 : ℝ) < kappa 4 0.95 0.023 (0.100 ^ 2) ∧
        kappa 4 0.95 0.023 (0.100 ^ 2) < 0.25) ∧
      ((0.02 : ℝ) < tau 4 (0.100 ^ 2) ∧ tau 4 (0.100 ^ 2) < 0.0203) :=
  ⟨kappa_entry (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [T5]) (by norm_num) (by norm_num) (by norm_num [T5]) (by norm_num [T5]),
    tau_entry (by norm_num) (by norm_num [T5]) (by norm_num [T5])⟩

/-- Table 6.1, **Thailand** (`g = 0.043`, `σ = 0.081`), O&R p. 369: `κ ∈ (0.079, 0.081)` (printed
0.08) and `τ ∈ (0.013, 0.014)` (printed 0.013). -/
theorem table_thailand :
    ((0.079 : ℝ) < kappa 4 0.95 0.043 (0.081 ^ 2) ∧
        kappa 4 0.95 0.043 (0.081 ^ 2) < 0.081) ∧
      ((0.013 : ℝ) < tau 4 (0.081 ^ 2) ∧ tau 4 (0.081 ^ 2) < 0.014) :=
  ⟨kappa_entry (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [T5]) (by norm_num) (by norm_num) (by norm_num [T5]) (by norm_num [T5]),
    tau_entry (by norm_num) (by norm_num [T5]) (by norm_num [T5])⟩

/-- Table 6.1, **Venezuela** (`g = 0.011`, `σ = 0.118`), O&R p. 369: `κ ∈ (4.2, 4.3)` (printed
"Undefined": in fact **finite**, see `venezuela_qX_lt_one`) and `τ ∈ (0.028, 0.029)` (printed
0.028). -/
theorem table_venezuela :
    ((4.2 : ℝ) < kappa 4 0.95 0.011 (0.118 ^ 2) ∧
        kappa 4 0.95 0.011 (0.118 ^ 2) < 4.3) ∧
      ((0.028 : ℝ) < tau 4 (0.118 ^ 2) ∧ tau 4 (0.118 ^ 2) < 0.029) :=
  ⟨kappa_entry (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [T5]) (by norm_num) (by norm_num) (by norm_num [T5]) (by norm_num [T5]),
    tau_entry (by norm_num) (by norm_num [T5]) (by norm_num [T5])⟩

/-- **The Venezuela correction**, O&R Table 6.1, p. 369. From the rounded inputs
`g = 0.011`, `σ = 0.118` (with `β = 0.95`, `ρ = 4`), `β(1 + g)^{1−ρ}exp[ρ(ρ − 1)V/2] < 1`:
so `κ` is finite (`table_venezuela`: `κ ∈ (4.2, 4.3)`), not "Undefined", and full insurance
is *not* sustainable by reputation for Venezuela either. -/
theorem venezuela_qX_lt_one : qfac 4 0.95 0.011 * Xfac 4 (0.118 ^ 2) < 1 := by
  unfold qfac
  rw [growth_rho_four (by norm_num), Xfac_rho_four]
  have hx : (0 : ℝ) ≤ 6 * 0.118 ^ 2 := by norm_num
  have h := exp_le_T5 hx (by norm_num)
  have hq : (0 : ℝ) < 0.95 * (1 / (1 + 0.011) ^ 3) := by norm_num
  calc 0.95 * (1 / (1 + 0.011) ^ 3) * Real.exp (6 * 0.118 ^ 2)
      ≤ 0.95 * (1 / (1 + 0.011) ^ 3) * (T5 (6 * 0.118 ^ 2) + (6 * 0.118 ^ 2) ^ 5 / 100) :=
        mul_le_mul_of_nonneg_left h hq.le
    _ < 1 := by norm_num [T5]

/-- For Venezuela full insurance is not sustainable for every output realisation (O&R p. 368
claims the opposite): by `sustainable_iff_rho_gt_one` and `venezuela_qX_lt_one`. -/
theorem venezuela_not_sustainable {Ybar : ℝ} (hY : 0 < Ybar) :
    ¬ ∀ ε : ℝ, gainLN 4 0.011 (0.118 ^ 2) Ybar ε ≤
      costLN 4 0.95 0.011 (0.118 ^ 2) Ybar (Real.exp ((1 - 4) ^ 2 * 0.118 ^ 2 / 2)) := by
  have hq : qfac 4 0.95 0.011 = 0.95 * (1 / (1 + 0.011) ^ 3) := by
    unfold qfac; rw [growth_rho_four (by norm_num)]
  rw [sustainable_iff_rho_gt_one (by norm_num) (by norm_num) hY (by rw [hq]; norm_num)
    (by rw [hq]; norm_num) rfl]
  exact not_le.mpr venezuela_qX_lt_one

/-- **The Venezuela entry is rounding-sensitive**, O&R Table 6.1: at `σ = 0.1185` (which
rounds to the printed 0.118 or 0.119) the sustainability index exceeds one, so the verdict
flips between `σ = 0.118` and `σ = 0.1185`. -/
theorem venezuela_flip : 1 < qfac 4 0.95 0.011 * Xfac 4 (0.1185 ^ 2) := by
  unfold qfac
  rw [growth_rho_four (by norm_num), Xfac_rho_four]
  have hx : (0 : ℝ) ≤ 6 * 0.1185 ^ 2 := by norm_num
  have h := T5_le_exp hx
  have hq : (0 : ℝ) < 0.95 * (1 / (1 + 0.011) ^ 3) := by norm_num
  calc (1 : ℝ) < 0.95 * (1 / (1 + 0.011) ^ 3) * T5 (6 * 0.1185 ^ 2) := by norm_num [T5]
    _ ≤ _ := mul_le_mul_of_nonneg_left h hq.le

/-- O&R p. 369: with `β = 0.85` Argentina's cost of reputation loss is `κ ∈ (0.10, 0.11)` of
current GDP (the book: "only 11 percent"; the rounded inputs give about 10.7 percent). -/
theorem argentina_beta_085 :
    (0.10 : ℝ) < kappa 4 0.85 0.015 (0.099 ^ 2) ∧ kappa 4 0.85 0.015 (0.099 ^ 2) < 0.11 :=
  kappa_entry (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [T5]) (by norm_num) (by norm_num) (by norm_num [T5]) (by norm_num [T5])


/-! ## Partial insurance by reputation, §6.1.2.2 -/

namespace PartialInsurance

variable {S : Type} [Fintype S] (E : Endowment S) (U : Utility)

/-- Consumption under a stationary contract, O&R (17), p. 370: `C(ε) = Ȳ + ε − P(ε)`. -/
def cons (P : S → ℝ) (s : S) : ℝ := E.Y s - P s

/-- Expected period utility of a stationary contract, O&R p. 371: `Σ π u(Ȳ + ε − P(ε))`. -/
noncomputable def obj (P : S → ℝ) : ℝ := E.Ω.expect (fun s => U.u (cons E P s))

/-- The cost of exclusion under the contract, O&R p. 370:
`β/(1 − β){E u(Ȳ + ε − P) − E u(Ȳ + ε)}`. -/
noncomputable def repCost (β : ℝ) (P : S → ℝ) : ℝ :=
  β / (1 - β) * (obj E U P - E.Ω.expect (fun s => U.u (E.Y s)))

/-- The reputational incentive constraint (18), O&R p. 370:
`u(Ȳ + ε) − u(Ȳ + ε − P(ε)) ≤ Cost` in every state. -/
def RepIC (β : ℝ) (P : S → ℝ) : Prop := ∀ s, U.u (E.Y s) - U.u (cons E P s) ≤ repCost E U β P

/-- A feasible stationary contract, O&R §6.1.2.2: zero profit (13), positive consumption and
the incentive constraint (18). -/
def Feasible (β : ℝ) (P : S → ℝ) : Prop :=
  E.Ω.expect P = 0 ∧ (∀ s, 0 < cons E P s) ∧ RepIC E U β P

/-- **(18) is the no-profitable-deviation condition of the repeated game**, O&R p. 370: a
stationary contract satisfies (18) iff honouring it beats every default strategy (every
stopping time and every partial default) under permanent exclusion. -/
theorem repIC_iff_no_deviation {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (P : S → ℝ) :
    RepIC E U β P ↔
      ∀ (d : Strategy S) (w : (n : ℕ) → (Fin (n + 1) → S) → ℝ) (Mw : ℝ),
        (∀ n h, |w n h| ≤ Mw) → (∀ n h, w n h ≤ U.u (E.Y (h (Fin.last n)))) →
        payoff E.Ω β d (fun s => U.u (cons E P s)) (fun s => U.u (E.Y s)) w ≤
          obj E U P / (1 - β) := by
  exact (trigger_iff E.Ω hβ0 hβ1 E.prob_pos (fun s => U.u (cons E P s)) (fun s => U.u (E.Y s))
    (fun s => U.u (E.Y s))).symm

/-- The null contract is feasible (O&R p. 370: autarky satisfies (18) trivially). -/
theorem feasible_zero (β : ℝ) : Feasible E U β 0 := by
  refine ⟨by simp [StateSpace.expect], fun s => by simp [cons, E.Y_pos s], fun s => ?_⟩
  simp [repCost, obj, cons]

/-- **The incentive-compatible set is convex**, O&R §6.1.2.2 (the left side of (18) is convex in
`P(ε)`, the right side concave): convex combinations of feasible contracts are feasible. -/
theorem feasible_convex {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {P Q : S → ℝ}
    (hP : Feasible E U β P) (hQ : Feasible E U β Q) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Feasible E U β (fun s => t * P s + (1 - t) * Q s) := by
  obtain ⟨hPz, hPc, hPic⟩ := hP
  obtain ⟨hQz, hQc, hQic⟩ := hQ
  have hcons : ∀ s, cons E (fun s => t * P s + (1 - t) * Q s) s =
      t * cons E P s + (1 - t) * cons E Q s := fun s => by unfold cons; ring
  have hpos : ∀ s, 0 < t * cons E P s + (1 - t) * cons E Q s := fun s => by
    have hm : 0 < min (cons E P s) (cons E Q s) := lt_min (hPc s) (hQc s)
    have h1 : t * min (cons E P s) (cons E Q s) ≤ t * cons E P s :=
      mul_le_mul_of_nonneg_left (min_le_left _ _) ht0
    have h2 : (1 - t) * min (cons E P s) (cons E Q s) ≤ (1 - t) * cons E Q s :=
      mul_le_mul_of_nonneg_left (min_le_right _ _) (by linarith)
    nlinarith
  have hconc : ∀ s, t * U.u (cons E P s) + (1 - t) * U.u (cons E Q s) ≤
      U.u (cons E (fun s => t * P s + (1 - t) * Q s) s) := fun s => by
    rw [hcons]
    have := U.strictConcave.concaveOn.2 (Set.mem_Ioi.mpr (hPc s)) (Set.mem_Ioi.mpr (hQc s))
      ht0 (by linarith : 0 ≤ 1 - t) (by ring)
    simpa [smul_eq_mul] using this
  have hobj : t * obj E U P + (1 - t) * obj E U Q ≤ obj E U (fun s => t * P s + (1 - t) * Q s) := by
    unfold obj
    rw [← expect_linear]
    exact expect_mono E.Ω hconc
  have hk : 0 ≤ β / (1 - β) := div_nonneg hβ0 (by linarith)
  refine ⟨?_, fun s => by rw [hcons]; exact hpos s, fun s => ?_⟩
  · rw [expect_linear, hPz, hQz]; ring
  · have h1 := hPic s
    have h2 := hQic s
    have h3 := hconc s
    unfold repCost at h1 h2 ⊢
    have h4 : t * (U.u (E.Y s) - U.u (cons E P s)) + (1 - t) * (U.u (E.Y s) - U.u (cons E Q s))
        ≤ t * (β / (1 - β) * (obj E U P - E.Ω.expect fun s => U.u (E.Y s))) +
          (1 - t) * (β / (1 - β) * (obj E U Q - E.Ω.expect fun s => U.u (E.Y s))) :=
      add_le_add (mul_le_mul_of_nonneg_left h1 ht0)
        (mul_le_mul_of_nonneg_left h2 (by linarith))
    have h5 : β / (1 - β) * (t * obj E U P + (1 - t) * obj E U Q) ≤
        β / (1 - β) * obj E U (fun s => t * P s + (1 - t) * Q s) :=
      mul_le_mul_of_nonneg_left hobj hk
    nlinarith

/-- **Uniqueness of the optimal contract**, O&R §6.1.2.2: two optimal feasible contracts
coincide (strict concavity and convexity of the feasible set). -/
theorem optimum_unique {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {P Q : S → ℝ}
    (hP : Feasible E U β P) (hQ : Feasible E U β Q)
    (hPopt : ∀ R, Feasible E U β R → obj E U R ≤ obj E U P)
    (hQopt : ∀ R, Feasible E U β R → obj E U R ≤ obj E U Q) : P = Q := by
  have heq : obj E U P = obj E U Q := le_antisymm (hQopt P hP) (hPopt Q hQ)
  funext s
  by_contra hne
  have hM := feasible_convex E U hβ0 hβ1 hP hQ (t := 1 / 2) (by norm_num) (by norm_num)
  have hcP := hP.2.1
  have hcQ := hQ.2.1
  have hpt : ∀ t, 1 / 2 * U.u (cons E P t) + (1 - 1 / 2) * U.u (cons E Q t) ≤
      U.u (cons E (fun s => 1 / 2 * P s + (1 - 1 / 2) * Q s) t) := fun t => by
    have : cons E (fun s => 1 / 2 * P s + (1 - 1 / 2) * Q s) t =
        1 / 2 * cons E P t + (1 - 1 / 2) * cons E Q t := by unfold cons; ring
    rw [this]
    have := U.strictConcave.concaveOn.2 (Set.mem_Ioi.mpr (hcP t)) (Set.mem_Ioi.mpr (hcQ t))
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 - 1 / 2) (by ring)
    simpa [smul_eq_mul] using this
  have hstrict : 1 / 2 * U.u (cons E P s) + (1 - 1 / 2) * U.u (cons E Q s) <
      U.u (cons E (fun s => 1 / 2 * P s + (1 - 1 / 2) * Q s) s) := by
    have : cons E (fun s => 1 / 2 * P s + (1 - 1 / 2) * Q s) s =
        1 / 2 * cons E P s + (1 - 1 / 2) * cons E Q s := by unfold cons; ring
    rw [this]
    have hne' : cons E P s ≠ cons E Q s := by unfold cons; intro h; apply hne; linarith
    have := U.strictConcave.2 (Set.mem_Ioi.mpr (hcP s)) (Set.mem_Ioi.mpr (hcQ s)) hne'
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 - 1 / 2) (by ring)
    simpa [smul_eq_mul] using this
  have hlt := expect_strictMono E.Ω hpt (E.prob_pos s) hstrict
  rw [expect_linear] at hlt
  have := hPopt _ hM
  unfold obj at this heq
  rw [← heq] at hlt
  linarith

/-- Jensen bound on the cost of exclusion: for any zero-profit contract with positive
consumption, `Cost ≤ β/(1 − β)[u(Ȳ) − E u(Ȳ + ε)]` (O&R (15)–(18)). -/
theorem repCost_le {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {P : S → ℝ}
    (hz : E.Ω.expect P = 0) (hc : ∀ s, 0 < cons E P s) :
    repCost E U β P ≤ β / (1 - β) * (U.u E.Ybar - E.Ω.expect (fun s => U.u (E.Y s))) := by
  have hm : E.Ω.expect (cons E P) = E.Ybar := by
    unfold cons; rw [expect_sub, E.expect_Y, hz, sub_zero]
  have hj := jensen E.Ω U hc
  rw [hm] at hj
  unfold repCost obj
  exact mul_le_mul_of_nonneg_left (by linarith) (div_nonneg hβ0 (by linarith))

/-- A consumption floor from utility unbounded below (e.g. log or CRRA with `ρ ≥ 1`): some
`c₀ > 0` has `u(c₀) ≤ u(Ȳ + ε) − β/(1 − β)[u(Ȳ) − E u(Ȳ + ε)]` in every state, i.e. even the
harshest exclusion cannot push incentive-compatible consumption to zero.
(O&R §6.1.2.2, pp. 370–373) -/
theorem floor_of_unbounded_below (β : ℝ) (hbot : ∀ M, ∃ c, 0 < c ∧ U.u c < M) :
    ∃ c₀, 0 < c₀ ∧ ∀ s, U.u c₀ ≤
      U.u (E.Y s) - β / (1 - β) * (U.u E.Ybar - E.Ω.expect (fun s => U.u (E.Y s))) := by
  obtain ⟨c, hc, hcM⟩ := hbot (-(∑ t, |U.u (E.Y t)|) -
    |β / (1 - β) * (U.u E.Ybar - E.Ω.expect (fun s => U.u (E.Y s)))|)
  refine ⟨c, hc, fun s => ?_⟩
  have h1 := Trigger.abs_le_sum_abs (fun t => U.u (E.Y t)) s
  have h2 := neg_abs_le (U.u (E.Y s))
  have h3 := le_abs_self (β / (1 - β) * (U.u E.Ybar - E.Ω.expect (fun s => U.u (E.Y s))))
  linarith

/-- **Existence of an optimal incentive-compatible contract**, O&R §6.1.2.2. Given a
consumption floor `c₀ > 0` (automatic when `u` is unbounded below,
`floor_of_unbounded_below`), the feasible set is compact and nonempty, so the continuous
objective attains its maximum. -/
theorem optimum_exists {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hfloor : ∀ s, U.u c₀ ≤
      U.u (E.Y s) - β / (1 - β) * (U.u E.Ybar - E.Ω.expect (fun s => U.u (E.Y s)))) :
    ∃ P, Feasible E U β P ∧ ∀ Q, Feasible E U β Q → obj E U Q ≤ obj E U P := by
  classical
  set Kmax := β / (1 - β) * (U.u E.Ybar - E.Ω.expect (fun s => U.u (E.Y s))) with hKmax
  have hKmax0 : 0 ≤ Kmax := by
    have := repCost_le E U hβ0 hβ1 (P := 0) (by simp [StateSpace.expect])
      (fun s => by simp [cons, E.Y_pos s])
    have h0 : repCost E U β 0 = 0 := by simp [repCost, obj, cons]
    linarith
  have hYc : ∀ s, c₀ ≤ E.Y s := fun s =>
    (U.le_iff hc₀ (E.Y_pos s)).mp (by linarith [hfloor s])
  -- feasible contracts respect the floor
  have hfl : ∀ P, Feasible E U β P → ∀ s, c₀ ≤ cons E P s := by
    intro P hP s
    have h1 := hP.2.2 s
    have h2 := repCost_le E U hβ0 hβ1 hP.1 hP.2.1
    exact (U.le_iff hc₀ (hP.2.1 s)).mp (by linarith [hfloor s])
  -- the truncated utility
  set ut : ℝ → ℝ := fun x => U.u (max x c₀) with hut
  have hutc : Continuous ut := U.continuousOn.comp_continuous (continuous_id.max continuous_const)
    (fun x => Set.mem_Ioi.mpr (lt_of_lt_of_le hc₀ (le_max_right _ _)))
  have hut_eq : ∀ x, c₀ ≤ x → ut x = U.u x := fun x hx => by simp [hut, max_eq_left hx]
  set objt : (S → ℝ) → ℝ := fun P => ∑ s, E.Ω.prob s * ut (E.Y s - P s) with hobjt
  have hobjtc : Continuous objt := by
    simp only [hobjt]
    exact continuous_finsetSum _ fun s _ =>
      continuous_const.mul (hutc.comp (continuous_const.sub (continuous_apply s)))
  set K : Set (S → ℝ) := {P | ∑ s, E.Ω.prob s * P s = 0} ∩ (⋂ s, {P | c₀ ≤ E.Y s - P s}) ∩
    ⋂ s, {P | U.u (E.Y s) - ut (E.Y s - P s) ≤
      β / (1 - β) * (objt P - E.Ω.expect (fun s => U.u (E.Y s)))} with hK
  have hKfeas : ∀ P, P ∈ K ↔ Feasible E U β P := by
    intro P
    simp only [hK, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨⟨hz, hc⟩, hic⟩
      have hobj : objt P = obj E U P := by
        simp only [hobjt, obj, StateSpace.expect, cons]
        exact Finset.sum_congr rfl fun s _ => by rw [hut_eq (E.Y s - P s) (hc s)]
      refine ⟨hz, fun s => lt_of_lt_of_le hc₀ (hc s), fun s => ?_⟩
      have := hic s
      rw [hut_eq (E.Y s - P s) (hc s), hobj] at this
      exact this
    · intro hP
      have hc := hfl P hP
      have hobj : objt P = obj E U P := by
        simp only [hobjt, obj, StateSpace.expect, cons]
        exact Finset.sum_congr rfl fun s _ => by rw [hut_eq (E.Y s - P s) (hc s)]
      refine ⟨⟨hP.1, hc⟩, fun s => ?_⟩
      rw [hut_eq (E.Y s - P s) (hc s), hobj]
      exact hP.2.2 s
  have hKclosed : IsClosed K := by
    refine ((isClosed_eq ?_ continuous_const).inter (isClosed_iInter fun s =>
      isClosed_le continuous_const (continuous_const.sub (continuous_apply s)))).inter
      (isClosed_iInter fun s => isClosed_le ?_ ?_)
    · exact continuous_finsetSum _ fun s _ => continuous_const.mul (continuous_apply s)
    · exact continuous_const.sub (hutc.comp (continuous_const.sub (continuous_apply s)))
    · exact continuous_const.mul (hobjtc.sub continuous_const)
  set B := ∑ t, |E.Y t|
  have hKsub : K ⊆ Set.pi Set.univ (fun s => Set.Icc (-B / E.Ω.prob s) B) := by
    intro P hP
    have hPf := (hKfeas P).mp hP
    have hc := hfl P hPf
    have hup : ∀ t, P t ≤ B := fun t => by
      have := hc t
      have := Trigger.abs_le_sum_abs E.Y t
      have := le_abs_self (E.Y t)
      unfold cons at *; linarith
    intro s _
    refine ⟨?_, hup s⟩
    rw [div_le_iff₀ (E.prob_pos s)]
    have hz : ∑ t, E.Ω.prob t * P t = 0 := hPf.1
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ s)] at hz
    have hrest : ∑ t ∈ Finset.univ.erase s, E.Ω.prob t * P t ≤ B := by
      calc ∑ t ∈ Finset.univ.erase s, E.Ω.prob t * P t
          ≤ ∑ t ∈ Finset.univ.erase s, E.Ω.prob t * B :=
            Finset.sum_le_sum fun t _ => mul_le_mul_of_nonneg_left (hup t) (E.Ω.prob_nonneg t)
        _ ≤ ∑ t, E.Ω.prob t * B := Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.erase_subset _ _) fun t _ _ =>
              mul_nonneg (E.Ω.prob_nonneg t) (Finset.sum_nonneg fun _ _ => abs_nonneg _)
        _ = B := by rw [← Finset.sum_mul, E.Ω.prob_sum, one_mul]
    nlinarith
  have hKcompact : IsCompact K :=
    (isCompact_univ_pi fun s => isCompact_Icc).of_isClosed_subset hKclosed hKsub
  have hKne : K.Nonempty := ⟨0, (hKfeas 0).mpr (feasible_zero E U β)⟩
  obtain ⟨P, hPK, hPmax⟩ := hKcompact.exists_isMaxOn hKne hobjtc.continuousOn
  have hPf := (hKfeas P).mp hPK
  refine ⟨P, hPf, fun Q hQ => ?_⟩
  have hQK := (hKfeas Q).mpr hQ
  have h := hPmax hQK
  simp only [Set.mem_ofPred_eq] at h
  have eQ : objt Q = obj E U Q := by
    simp only [hobjt, obj, StateSpace.expect, cons]
    exact Finset.sum_congr rfl fun s _ => by rw [hut_eq (E.Y s - Q s) (hfl Q hQ s)]
  have eP : objt P = obj E U P := by
    simp only [hobjt, obj, StateSpace.expect, cons]
    exact Finset.sum_congr rfl fun s _ => by rw [hut_eq (E.Y s - P s) (hfl P hPf s)]
  rw [← eQ, ← eP]; exact h

/-- **Kuhn–Tucker sufficiency**, O&R (19)–(20), p. 371: a feasible contract with multipliers
`μ` and `λ ≥ 0` satisfying (19) `[π + λ + βπΣλ/(1 − β)]u'(C) = μπ` and complementary
slackness (20) is optimal (the feasible set is convex, `feasible_convex`). -/
theorem kuhn_tucker_sufficient {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {P : S → ℝ}
    (hP : Feasible E U β P) (μ : ℝ) (lam : S → ℝ) (hlam : ∀ s, 0 ≤ lam s)
    (h19 : ∀ s, (E.Ω.prob s + lam s + β * E.Ω.prob s * (∑ t, lam t) / (1 - β)) *
      U.du (cons E P s) = μ * E.Ω.prob s)
    (h20 : ∀ s, lam s * (repCost E U β P - U.u (E.Y s) + U.u (cons E P s)) = 0) :
    ∀ Q, Feasible E U β Q → obj E U Q ≤ obj E U P := by
  intro Q hQ
  set L := ∑ t, lam t with hL
  have hL0 : 0 ≤ L := Finset.sum_nonneg fun t _ => hlam t
  set w : S → ℝ := fun s => E.Ω.prob s + lam s + β * E.Ω.prob s * L / (1 - β) with hw
  have hk : 0 ≤ β / (1 - β) := div_nonneg hβ0 (by linarith)
  -- supporting lines
  have hsl : ∀ s, w s * U.u (cons E Q s) ≤ w s * U.u (cons E P s) +
      μ * E.Ω.prob s * (P s - Q s) := fun s => by
    have hws : 0 ≤ w s := by
      simp only [hw]
      have := E.Ω.prob_nonneg s
      have : 0 ≤ β * E.Ω.prob s * L / (1 - β) := by
        apply div_nonneg (mul_nonneg (mul_nonneg hβ0 this) hL0) (by linarith)
      linarith [hlam s]
    have := U.supporting_line (hQ.2.1 s) (hP.2.1 s)
    have e : cons E Q s - cons E P s = P s - Q s := by unfold cons; ring
    rw [e] at this
    have h19s := h19 s
    calc w s * U.u (cons E Q s)
        ≤ w s * (U.u (cons E P s) + U.du (cons E P s) * (P s - Q s)) :=
          mul_le_mul_of_nonneg_left this hws
      _ = w s * U.u (cons E P s) + (w s * U.du (cons E P s)) * (P s - Q s) := by ring
      _ = _ := by rw [show w s * U.du (cons E P s) = μ * E.Ω.prob s from h19s]
  have hsum := Finset.sum_le_sum fun s (_ : s ∈ Finset.univ) => hsl s
  rw [Finset.sum_add_distrib] at hsum
  have hlin : ∑ s, μ * E.Ω.prob s * (P s - Q s) = 0 := by
    have : ∑ s, μ * E.Ω.prob s * (P s - Q s) = μ * (E.Ω.expect P - E.Ω.expect Q) := by
      unfold StateSpace.expect
      rw [mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro s _; ring
    rw [this, hP.1, hQ.1]; ring
  rw [hlin, add_zero] at hsum
  -- expand `Σ w u(C)`
  have hexpand : ∀ R : S → ℝ, ∑ s, w s * U.u (cons E R s) =
      obj E U R + ∑ s, lam s * U.u (cons E R s) + β * L / (1 - β) * obj E U R := by
    intro R
    simp only [hw, obj, StateSpace.expect]
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro s _; ring
  rw [hexpand, hexpand] at hsum
  -- incentive constraints: `λ u(C_Q) ≥ λ (u(Y) − Cost_Q)`, equality for `P`
  have hQl : ∀ s, lam s * (U.u (E.Y s) - repCost E U β Q) ≤ lam s * U.u (cons E Q s) :=
    fun s => mul_le_mul_of_nonneg_left (by linarith [hQ.2.2 s]) (hlam s)
  have hPl : ∀ s, lam s * U.u (cons E P s) = lam s * (U.u (E.Y s) - repCost E U β P) :=
    fun s => by linarith [h20 s]
  have hQs := Finset.sum_le_sum fun s (_ : s ∈ Finset.univ) => hQl s
  rw [Finset.sum_congr rfl fun s _ => hPl s] at hsum
  have eQ : ∑ s, lam s * (U.u (E.Y s) - repCost E U β Q) =
      ∑ s, lam s * U.u (E.Y s) - L * repCost E U β Q := by
    rw [hL, Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro s _; ring
  have eP : ∑ s, lam s * (U.u (E.Y s) - repCost E U β P) =
      ∑ s, lam s * U.u (E.Y s) - L * repCost E U β P := by
    rw [hL, Finset.sum_mul, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro s _; ring
  rw [eQ] at hQs
  rw [eP] at hsum
  unfold repCost at hsum hQs
  have hb : β * L / (1 - β) = L * (β / (1 - β)) := by ring
  rw [hb] at hsum
  nlinarith

/-- Strictly concave utility has strictly decreasing increments: for `0 < x < y` and `d > 0`,
`u(y + d) − u(y) < u(x + d) − u(x)` (used for the binding arm of §6.1.2.2).
(O&R §6.1.2.2, pp. 370–373) -/
theorem increment_strict_anti {x y d : ℝ} (hx : 0 < x) (hxy : x < y) (hd : 0 < d) :
    U.u (y + d) - U.u y < U.u (x + d) - U.u x := by
  have hL : 0 < y + d - x := by linarith
  set θ := d / (y + d - x) with hθ
  have hθ0 : 0 < θ := div_pos hd hL
  have hθ1 : 0 < 1 - θ := by rw [hθ, one_sub_div hL.ne']; exact div_pos (by linarith) hL
  have hy : 0 < y + d := by linarith
  have hne : x ≠ y + d := by linarith
  have h1 := U.strictConcave.2 (Set.mem_Ioi.mpr hx) (Set.mem_Ioi.mpr hy) hne hθ0 hθ1
    (by ring)
  have h2 := U.strictConcave.2 (Set.mem_Ioi.mpr hx) (Set.mem_Ioi.mpr hy) hne hθ1 hθ0
    (by ring)
  simp only [smul_eq_mul] at h1 h2
  have e1 : θ * x + (1 - θ) * (y + d) = y := by
    rw [hθ]; field_simp; ring
  have e2 : (1 - θ) * x + θ * (y + d) = x + d := by
    rw [hθ]; field_simp; ring
  rw [e1] at h1; rw [e2] at h2
  linarith

/-- **The transfer step** (O&R §6.1.2.2, the argument behind (21)): if state `j` is slack in
(18) and consumes strictly more than state `i`, moving consumption from `j` to `i` keeps the
contract feasible and raises expected utility. -/
theorem transfer_improves {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {P : S → ℝ}
    (hP : Feasible E U β P) {i j : S} (hij : i ≠ j) (hC : cons E P i < cons E P j)
    (hslack : U.u (E.Y j) - U.u (cons E P j) < repCost E U β P) :
    ∃ Q, Feasible E U β Q ∧ obj E U P < obj E U Q := by
  classical
  obtain ⟨hz, hc, hic⟩ := hP
  set Ci := cons E P i
  set Cj := cons E P j
  set pi := E.Ω.prob i
  set pj := E.Ω.prob j
  have hpi := E.prob_pos i
  have hpj := E.prob_pos j
  have hCj : 0 < Cj := hc j
  have hCi : 0 < Ci := hc i
  set σ := repCost E U β P - (U.u (E.Y j) - U.u Cj) with hσ
  have hσpos : 0 < σ := by simp only [hσ]; linarith
  have hdu := U.du_pos (Cj / 2) (by linarith)
  set b := min (min (Cj / 2) (σ / (2 * U.du (Cj / 2)))) ((Cj - Ci) / (2 * (1 + pj / pi)))
    with hb
  have hb0 : 0 < b := lt_min (lt_min (by linarith) (div_pos hσpos (by linarith)))
    (div_pos (by linarith) (by have : 0 < pj / pi := div_pos hpj hpi; linarith))
  have hb1 : b ≤ Cj / 2 := le_trans (min_le_left _ _) (min_le_left _ _)
  have hb2 : b ≤ σ / (2 * U.du (Cj / 2)) := le_trans (min_le_left _ _) (min_le_right _ _)
  have hb3 : b ≤ (Cj - Ci) / (2 * (1 + pj / pi)) := min_le_right _ _
  set a := pj * b / pi with ha
  have ha0 : 0 < a := div_pos (mul_pos hpj hb0) hpi
  have hab : Ci + a < Cj - b := by
    have hq : 0 < 1 + pj / pi := by have : 0 < pj / pi := div_pos hpj hpi; linarith
    rw [le_div_iff₀ (by linarith)] at hb3
    have : a = pj / pi * b := by rw [ha]; ring
    rw [this]
    nlinarith
  set Q : S → ℝ := fun s => P s + (if s = i then -a else 0) + (if s = j then b else 0) with hQ
  have hQi : cons E Q i = Ci + a := by
    simp only [Ci, hQ, cons, ↓reduceIte, hij]; ring
  have hQj : cons E Q j = Cj - b := by
    simp only [Cj, hQ, cons, ↓reduceIte, Ne.symm hij]; ring
  have hQo : ∀ s, s ≠ i → s ≠ j → cons E Q s = cons E P s := fun s h1 h2 => by
    simp only [hQ, cons, h1, h2, ↓reduceIte]; ring
  -- zero profit
  have hzQ : E.Ω.expect Q = 0 := by
    have e : E.Ω.expect Q = E.Ω.expect P + ∑ s, E.Ω.prob s * (if s = i then -a else 0) +
        ∑ s, E.Ω.prob s * (if s = j then b else 0) := by
      unfold StateSpace.expect
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro s _; simp only [hQ]; ring
    rw [e, hz]
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    simp only [pi, pj, ha] at *
    field_simp; ring
  -- objective gain
  have hgain : obj E U Q - obj E U P =
      pi * (U.u (Ci + a) - U.u Ci) + pj * (U.u (Cj - b) - U.u Cj) := by
    unfold obj
    rw [← expect_sub]
    unfold StateSpace.expect
    rw [Finset.sum_eq_add i j hij
      (fun c _ hc => by simp only [hQo c hc.1 hc.2, sub_self, mul_zero])
      (fun h => absurd (Finset.mem_univ i) h) (fun h => absurd (Finset.mem_univ j) h)]
    simp only [hQi, hQj]
    rfl
  have hCia : 0 < Ci + a := by linarith
  have hCjb : 0 < Cj - b := by linarith
  have hsi : U.u Ci ≤ U.u (Ci + a) + U.du (Ci + a) * (Ci - (Ci + a)) :=
    U.supporting_line hCi hCia
  have hsj : U.u Cj ≤ U.u (Cj - b) + U.du (Cj - b) * (Cj - (Cj - b)) :=
    U.supporting_line hCj hCjb
  have hdd := U.du_strictAnti hCia hab
  have hobj : obj E U P < obj E U Q := by
    have : 0 < pi * (U.u (Ci + a) - U.u Ci) + pj * (U.u (Cj - b) - U.u Cj) := by
      have hpi' : pi ≠ 0 := hpi.ne'
      have e1 : pi * a = pj * b := by rw [ha]; field_simp
      have h1 : pi * (a * U.du (Ci + a)) ≤ pi * (U.u (Ci + a) - U.u Ci) :=
        mul_le_mul_of_nonneg_left (by nlinarith) hpi.le
      have h2 : pj * (-(b * U.du (Cj - b))) ≤ pj * (U.u (Cj - b) - U.u Cj) :=
        mul_le_mul_of_nonneg_left (by nlinarith) hpj.le
      have h3 : pi * (a * U.du (Ci + a)) + pj * (-(b * U.du (Cj - b))) =
          pj * b * (U.du (Ci + a) - U.du (Cj - b)) := by
        linear_combination U.du (Ci + a) * e1
      have h4 : 0 < pj * b * (U.du (Ci + a) - U.du (Cj - b)) :=
        mul_pos (mul_pos hpj hb0) (by linarith)
      linarith
    linarith
  have hcost : repCost E U β P ≤ repCost E U β Q := by
    unfold repCost
    exact mul_le_mul_of_nonneg_left (by linarith) (div_nonneg hβ0 (by linarith))
  refine ⟨Q, ⟨hzQ, fun s => ?_, fun s => ?_⟩, hobj⟩
  · by_cases h1 : s = i
    · rw [h1, hQi]; exact hCia
    · by_cases h2 : s = j
      · rw [h2, hQj]; exact hCjb
      · rw [hQo s h1 h2]; exact hc s
  · by_cases h1 : s = i
    · rw [h1, hQi]
      have := U.mono hCi (show Ci ≤ Ci + a by linarith)
      linarith [hic i]
    · by_cases h2 : s = j
      · rw [h2, hQj]
        -- `u(C_j) − u(C_j − b) ≤ b u'(C_j − b) ≤ b u'(C_j/2) < σ`
        have hd2 := U.du_anti (show 0 < Cj / 2 by linarith) (show Cj / 2 ≤ Cj - b by linarith)
        have hbd : b * U.du (Cj / 2) < σ := by
          have h2 := (le_div_iff₀ (by linarith : (0 : ℝ) < 2 * U.du (Cj / 2))).mp hb2
          have : 0 < b * U.du (Cj / 2) := mul_pos hb0 hdu
          linarith
        have hmul : U.du (Cj - b) * b ≤ U.du (Cj / 2) * b :=
          mul_le_mul_of_nonneg_right hd2 hb0.le
        have e : Cj - (Cj - b) = b := by ring
        rw [e] at hsj
        have : U.u Cj - U.u (Cj - b) < σ := by linarith
        have hσ' : σ = repCost E U β P - (U.u (E.Y j) - U.u Cj) := hσ
        have := hic j
        linarith
      · rw [hQo s h1 h2]; linarith [hic s]

/-- At an optimum, every state that is slack in (18) has the lowest consumption: for a slack
state `j`, `C(ε_j) ≤ C(ε_i)` for every `i` (O&R p. 372, (21)). -/
theorem slack_minimal {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {P : S → ℝ}
    (hP : Feasible E U β P) (hopt : ∀ Q, Feasible E U β Q → obj E U Q ≤ obj E U P) {j : S}
    (hslack : U.u (E.Y j) - U.u (cons E P j) < repCost E U β P) (i : S) :
    cons E P j ≤ cons E P i := by
  by_contra h; push Not at h
  have hij : i ≠ j := by intro e; rw [e] at h; exact lt_irrefl _ h
  obtain ⟨Q, hQ, hlt⟩ := transfer_improves E U hβ0 hβ1 hP hij h hslack
  exact absurd (hopt Q hQ) (not_le.mpr hlt)

/-- At an optimum the cost of exclusion is nonnegative (the null contract is feasible).
(O&R §6.1.2.2, pp. 370–373) -/
theorem repCost_nonneg_of_opt {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {P : S → ℝ}
    (hopt : ∀ Q, Feasible E U β Q → obj E U Q ≤ obj E U P) : 0 ≤ repCost E U β P := by
  have h := hopt 0 (feasible_zero E U β)
  have h0 : obj E U 0 = E.Ω.expect (fun s => U.u (E.Y s)) := by simp [obj, cons]
  unfold repCost
  exact mul_nonneg (div_nonneg hβ0 (by linarith)) (by linarith)

/-- If (18) binds in every state at an optimum, the optimum is autarky, `P = 0`
(O&R §6.1.2.2). -/
theorem all_binding_autarky {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {P : S → ℝ}
    (hP : Feasible E U β P) (hopt : ∀ Q, Feasible E U β Q → obj E U Q ≤ obj E U P)
    (hbind : ∀ s, U.u (E.Y s) - U.u (cons E P s) = repCost E U β P) : P = 0 := by
  have hK := repCost_nonneg_of_opt E U hβ0 hβ1 hopt
  have hnn : ∀ s, 0 ≤ P s := fun s => by
    have h := hbind s
    have : U.u (cons E P s) ≤ U.u (E.Y s) := by linarith
    have := (U.le_iff (hP.2.1 s) (E.Y_pos s)).mp this
    unfold cons at this; linarith
  funext s
  exact eq_zero_of_nonneg_of_expect_zero E.Ω hnn hP.1 (E.prob_pos s)

/-- **Characterisation of the optimal contract**, O&R (21) and pp. 372–373: at an optimum
with `K = Cost ≥ 0`, there is `c̄ > 0` such that `C(ε) = c̄` where `u(Ȳ + ε) − u(c̄) < K`
(the unconstrained, fully insured low states) and `u(C(ε)) = u(Ȳ + ε) − K` where
`u(Ȳ + ε) − u(c̄) ≥ K` (the binding states); i.e. `C = max(c̄, u⁻¹(u(Ȳ + ε) − K))`.
Expected consumption is `Ȳ`. -/
theorem optimum_characterisation {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {P : S → ℝ}
    (hP : Feasible E U β P) (hopt : ∀ Q, Feasible E U β Q → obj E U Q ≤ obj E U P) :
    0 ≤ repCost E U β P ∧ E.Ω.expect (cons E P) = E.Ybar ∧
      ∃ cbar, 0 < cbar ∧ ∀ s,
        (U.u (E.Y s) - U.u cbar < repCost E U β P → cons E P s = cbar) ∧
        (repCost E U β P ≤ U.u (E.Y s) - U.u cbar →
          U.u (cons E P s) = U.u (E.Y s) - repCost E U β P) := by
  have hK := repCost_nonneg_of_opt E U hβ0 hβ1 hopt
  have hmean : E.Ω.expect (cons E P) = E.Ybar := by
    unfold cons; rw [expect_sub, E.expect_Y, hP.1, sub_zero]
  refine ⟨hK, hmean, ?_⟩
  by_cases hex : ∃ j, U.u (E.Y j) - U.u (cons E P j) < repCost E U β P
  · obtain ⟨j, hj⟩ := hex
    refine ⟨cons E P j, hP.2.1 j, fun s => ⟨fun hs => ?_, fun hs => ?_⟩⟩
    · -- `s` must be slack, hence minimal like `j`
      have hjs := slack_minimal E U hβ0 hβ1 hP hopt hj s
      have hslack : U.u (E.Y s) - U.u (cons E P s) < repCost E U β P := by
        have := U.mono (hP.2.1 j) hjs
        linarith
      exact le_antisymm (slack_minimal E U hβ0 hβ1 hP hopt hslack j) hjs
    · -- `s` must bind
      rcases lt_or_eq_of_le (hP.2.2 s) with hlt | heq
      · have h1 := slack_minimal E U hβ0 hβ1 hP hopt hlt j
        have h2 := slack_minimal E U hβ0 hβ1 hP hopt hj s
        have : cons E P s = cons E P j := le_antisymm h1 h2
        rw [this] at hlt; linarith
      · linarith
  · push Not at hex
    have hbind : ∀ s, U.u (E.Y s) - U.u (cons E P s) = repCost E U β P := fun s =>
      le_antisymm (hP.2.2 s) (hex s)
    have hP0 := all_binding_autarky E U hβ0 hβ1 hP hopt hbind
    have hne := StateSpaceFacts.nonempty E.Ω
    have hK0 : repCost E U β P = 0 := by
      have := hbind hne.some
      rw [hP0] at this ⊢; simp [cons] at this; linarith
    obtain ⟨s₀, _, hs₀⟩ := Finset.exists_min_image Finset.univ E.Y Finset.univ_nonempty
    refine ⟨E.Y s₀, E.Y_pos s₀, fun s => ⟨fun hs => ?_, fun _ => ?_⟩⟩
    · exfalso
      have := U.mono (E.Y_pos s₀) (hs₀ s (Finset.mem_univ s))
      linarith
    · rw [hK0, hP0]; simp [cons]

/-- **The binding arm**, O&R p. 372: across states where (18) binds with `Cost > 0`,
consumption and payments rise with output but payments rise by less than output:
`C(ε_i) < C(ε_j)` and `0 < P(ε_j) − P(ε_i) < ε_j − ε_i` for `ε_i < ε_j` (the discrete form of
`0 < dP/dε < 1`). -/
theorem binding_increments {β : ℝ} {P : S → ℝ} (hc : ∀ s, 0 < cons E P s) {i j : S}
    (hi : U.u (E.Y i) - U.u (cons E P i) = repCost E U β P)
    (hj : U.u (E.Y j) - U.u (cons E P j) = repCost E U β P)
    (hK : 0 < repCost E U β P) (hij : E.ε i < E.ε j) :
    cons E P i < cons E P j ∧ 0 < P j - P i ∧ P j - P i < E.ε j - E.ε i := by
  have hYij : E.Y i < E.Y j := by unfold Endowment.Y; linarith
  have hu : U.u (cons E P j) - U.u (cons E P i) = U.u (E.Y j) - U.u (E.Y i) := by linarith
  have huY := U.lt (E.Y_pos i) hYij
  have hCij : cons E P i < cons E P j := by
    by_contra h; push Not at h
    have := U.mono (hc j) h
    linarith
  have hCiY : cons E P i < E.Y i := by
    by_contra h; push Not at h
    have := U.mono (E.Y_pos i) h
    linarith
  have hlt : cons E P j - cons E P i < E.Y j - E.Y i := by
    by_contra h; push Not at h
    set d := E.Y j - E.Y i
    have hd : 0 < d := by simp only [d]; linarith
    have h1 := U.mono (show 0 < cons E P i + d by linarith [hc i])
      (show cons E P i + d ≤ cons E P j by linarith)
    have h2 := increment_strict_anti U (hc i) hCiY hd
    have e : E.Y i + d = E.Y j := by simp only [d]; ring
    rw [e] at h2
    linarith
  have hd : cons E P j - cons E P i = (E.Y j - E.Y i) - (P j - P i) := by unfold cons; ring
  have hYd : E.Y j - E.Y i = E.ε j - E.ε i := by unfold Endowment.Y; ring
  refine ⟨hCij, by linarith, by linarith⟩

/-- **The slope of the binding arm**, O&R p. 372: if consumption `C` is differentiable at `x`
and (18) binds near `x`, `u(C(z)) = u(Ȳ + z) − K`, then `C'(x) = u'(Ȳ + x)/u'(C(x))` and
`dP/dε = 1 − C'(x) = [u'(C(x)) − u'(Ȳ + x)]/u'(C(x))`, which lies in `(0, 1)` when
`C(x) < Ȳ + x` (the constraint binds only where `P > 0`). -/
theorem binding_slope {C : ℝ → ℝ} {c' x Ybar K : ℝ} (hC : HasDerivAt C c' x)
    (hCpos : 0 < C x) (hY : 0 < Ybar + x)
    (hbind : ∀ᶠ z in 𝓝 x, U.u (C z) = U.u (Ybar + z) - K) :
    c' = U.du (Ybar + x) / U.du (C x) ∧
      1 - c' = (U.du (C x) - U.du (Ybar + x)) / U.du (C x) ∧
      (C x < Ybar + x → 0 < 1 - c' ∧ 1 - c' < 1) := by
  have h1 : HasDerivAt (fun z => U.u (C z)) (U.du (C x) * c') x :=
    (U.hasDerivAt (C x) hCpos).comp x hC
  have h2 : HasDerivAt (fun z => U.u (Ybar + z) - K) (U.du (Ybar + x)) x := by
    have := ((U.hasDerivAt (Ybar + x) hY).comp x ((hasDerivAt_id x).const_add Ybar)).sub_const K
    simpa using this
  have h3 : HasDerivAt (fun z => U.u (C z)) (U.du (Ybar + x)) x :=
    h2.congr_of_eventuallyEq hbind
  have hu := h1.unique h3
  have hd := U.du_pos (C x) hCpos
  have hc' : c' = U.du (Ybar + x) / U.du (C x) := by
    rw [eq_div_iff hd.ne']; linarith
  refine ⟨hc', by rw [hc']; field_simp, fun hlt => ?_⟩
  have hdd := U.du_strictAnti hCpos hlt
  have hdY := U.du_pos _ hY
  rw [hc']
  constructor
  · rw [sub_pos, div_lt_one hd]; exact hdd
  · have : 0 < U.du (Ybar + x) / U.du (C x) := div_pos hdY hd
    linarith

/-- O&R §6.1.2.1–6.1.2.2: when (16) holds, full insurance `P = ε` is feasible and is the
optimal contract (it attains the first-best `u(Ȳ)`). -/
theorem full_insurance_optimal_of_16 {β : ℝ}
    (h16 : ∀ s, U.u (E.Y s) - U.u E.Ybar ≤
      β / (1 - β) * (U.u E.Ybar - E.Ω.expect (fun s => U.u (E.Y s)))) :
    Feasible E U β E.ε ∧ ∀ Q, Feasible E U β Q → obj E U Q ≤ obj E U E.ε := by
  have hcons : ∀ s, cons E E.ε s = E.Ybar := fun s => by simp [cons, Endowment.Y]
  have hobj : obj E U E.ε = U.u E.Ybar := by
    unfold obj; simp only [hcons]; exact E.Ω.expect_const _
  refine ⟨⟨E.mean_zero, fun s => by rw [hcons]; exact E.Ybar_pos, fun s => ?_⟩, fun Q hQ => ?_⟩
  · unfold repCost; rw [hobj, hcons]; exact h16 s
  · rw [hobj]
    have hm : E.Ω.expect (cons E Q) = E.Ybar := by
      unfold cons; rw [expect_sub, E.expect_Y, hQ.1, sub_zero]
    have := jensen E.Ω U hQ.2.1
    rw [hm] at this
    exact this

/-- **Partial insurance need not be feasible** (O&R p. 370 asserts it is): with two states
`Y₀ < Y₁`, if `(1 − β)u'(Y₁) > βπ₁[u'(Y₀) − u'(Y₁)]` (e.g. `β` small), the only contract
satisfying (13) and (18) is the null contract. -/
theorem two_state_autarky (E : Endowment (Fin 2)) (U : Utility) {β : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) (hY : E.Y 0 < E.Y 1)
    (hcond : β * E.Ω.prob 1 * (U.du (E.Y 0) - U.du (E.Y 1)) < (1 - β) * U.du (E.Y 1))
    {P : Fin 2 → ℝ} (hP : Feasible E U β P) : P = 0 := by
  obtain ⟨hz, hc, hic⟩ := hP
  have hp0 := E.prob_pos 0
  have hp1 := E.prob_pos 1
  have hzs : E.Ω.prob 0 * P 0 + E.Ω.prob 1 * P 1 = 0 := by
    unfold StateSpace.expect at hz; rw [Fin.sum_univ_two] at hz; exact hz
  have hk : 0 ≤ β / (1 - β) := div_nonneg hβ0 (by linarith)
  have hcost : repCost E U β P = β / (1 - β) *
      (E.Ω.prob 0 * (U.u (cons E P 0) - U.u (E.Y 0)) +
        E.Ω.prob 1 * (U.u (cons E P 1) - U.u (E.Y 1))) := by
    unfold repCost obj StateSpace.expect; rw [Fin.sum_univ_two, Fin.sum_univ_two]; ring
  have hd01 := U.du_strictAnti (E.Y_pos 0) hY
  have hdu1 := U.du_pos _ (E.Y_pos 1)
  -- supporting lines at output
  have s0 := U.supporting_line (hc 0) (E.Y_pos 0)
  have s1 := U.supporting_line (hc 1) (E.Y_pos 1)
  have e0 : cons E P 0 - E.Y 0 = -P 0 := by unfold cons; ring
  have e1 : cons E P 1 - E.Y 1 = -P 1 := by unfold cons; ring
  rw [e0] at s0; rw [e1] at s1
  have hP1 : P 1 = 0 := by
    rcases lt_trichotomy (P 1) 0 with h | h | h
    · -- then `P 0 > 0` and state 0's constraint fails
      exfalso
      have hP0 : 0 < P 0 := by nlinarith
      have ic0 := hic 0
      rw [hcost] at ic0
      have hr : E.Ω.prob 0 * (U.u (cons E P 0) - U.u (E.Y 0)) +
          E.Ω.prob 1 * (U.u (cons E P 1) - U.u (E.Y 1)) ≤
          E.Ω.prob 0 * P 0 * (U.du (E.Y 1) - U.du (E.Y 0)) := by
        have a0 : E.Ω.prob 0 * (U.u (cons E P 0) - U.u (E.Y 0)) ≤
            E.Ω.prob 0 * (U.du (E.Y 0) * -P 0) :=
          mul_le_mul_of_nonneg_left (by linarith) hp0.le
        have a1 : E.Ω.prob 1 * (U.u (cons E P 1) - U.u (E.Y 1)) ≤
            E.Ω.prob 1 * (U.du (E.Y 1) * -P 1) :=
          mul_le_mul_of_nonneg_left (by linarith) hp1.le
        have : E.Ω.prob 1 * (U.du (E.Y 1) * -P 1) = E.Ω.prob 0 * P 0 * U.du (E.Y 1) := by
          have : E.Ω.prob 1 * P 1 = -(E.Ω.prob 0 * P 0) := by linarith
          calc E.Ω.prob 1 * (U.du (E.Y 1) * -P 1) = -(E.Ω.prob 1 * P 1) * U.du (E.Y 1) := by
                ring
            _ = _ := by rw [this]; ring
        nlinarith
      have hneg : E.Ω.prob 0 * P 0 * (U.du (E.Y 1) - U.du (E.Y 0)) < 0 :=
        mul_neg_of_pos_of_neg (mul_pos hp0 hP0) (by linarith)
      have hlhs : 0 < U.u (E.Y 0) - U.u (cons E P 0) := by
        have := U.du_pos _ (E.Y_pos 0); nlinarith
      have := mul_le_mul_of_nonneg_left hr hk
      nlinarith
    · exact h
    · exfalso
      have ic1 := hic 1
      rw [hcost] at ic1
      have hr : E.Ω.prob 0 * (U.u (cons E P 0) - U.u (E.Y 0)) +
          E.Ω.prob 1 * (U.u (cons E P 1) - U.u (E.Y 1)) ≤
          E.Ω.prob 1 * P 1 * (U.du (E.Y 0) - U.du (E.Y 1)) := by
        have a0 : E.Ω.prob 0 * (U.u (cons E P 0) - U.u (E.Y 0)) ≤
            E.Ω.prob 0 * (U.du (E.Y 0) * -P 0) :=
          mul_le_mul_of_nonneg_left (by linarith) hp0.le
        have a1 : E.Ω.prob 1 * (U.u (cons E P 1) - U.u (E.Y 1)) ≤
            E.Ω.prob 1 * (U.du (E.Y 1) * -P 1) :=
          mul_le_mul_of_nonneg_left (by linarith) hp1.le
        have : E.Ω.prob 0 * (U.du (E.Y 0) * -P 0) = E.Ω.prob 1 * P 1 * U.du (E.Y 0) := by
          have : E.Ω.prob 0 * P 0 = -(E.Ω.prob 1 * P 1) := by linarith
          calc E.Ω.prob 0 * (U.du (E.Y 0) * -P 0) = -(E.Ω.prob 0 * P 0) * U.du (E.Y 0) := by
                ring
            _ = _ := by rw [this]; ring
        nlinarith
      have hlhs : U.du (E.Y 1) * P 1 ≤ U.u (E.Y 1) - U.u (cons E P 1) := by linarith
      have h3 := mul_le_mul_of_nonneg_left hr hk
      -- `u'(Y₁)P₁ ≤ β/(1−β) π₁P₁[u'(Y₀) − u'(Y₁)]`, contradicting `hcond`
      have h4 : U.du (E.Y 1) * P 1 ≤
          β / (1 - β) * (E.Ω.prob 1 * P 1 * (U.du (E.Y 0) - U.du (E.Y 1))) := by linarith
      have h5 : (1 - β) * U.du (E.Y 1) ≤ β * E.Ω.prob 1 * (U.du (E.Y 0) - U.du (E.Y 1)) := by
        have h1b : 0 < 1 - β := by linarith
        rw [div_mul_eq_mul_div, le_div_iff₀ h1b] at h4
        have : P 1 * ((1 - β) * U.du (E.Y 1)) ≤
            P 1 * (β * E.Ω.prob 1 * (U.du (E.Y 0) - U.du (E.Y 1))) := by nlinarith
        exact le_of_mul_le_mul_left this h
      linarith
  have hP0 : P 0 = 0 := by
    rw [hP1, mul_zero, add_zero] at hzs
    exact (mul_eq_zero.mp hzs).resolve_left hp0.ne'
  funext k
  fin_cases k
  · exact hP0
  · exact hP1

/-! ### Kuhn–Tucker necessity and existence without a floor -/

/-- **A Slater point**, O&R §6.1.2.2: for `β > 0`, half of any non-null feasible contract is
feasible with every incentive constraint (18) strictly slack. -/
theorem slater_half {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {P : S → ℝ}
    (hP : Feasible E U β P) (hne : P ≠ 0) :
    Feasible E U β (fun s => 1 / 2 * P s) ∧
      ∀ s, U.u (E.Y s) - U.u (cons E (fun s => 1 / 2 * P s) s) <
        repCost E U β (fun s => 1 / 2 * P s) := by
  have hF := feasible_convex E U hβ0.le hβ1 hP (feasible_zero E U β) (t := 1 / 2)
    (by norm_num) (by norm_num)
  have e : (fun s => 1 / 2 * P s + (1 - 1 / 2) * (0 : S → ℝ) s) = fun s => 1 / 2 * P s := by
    funext s; simp
  rw [e] at hF
  refine ⟨hF, fun s => ?_⟩
  have hcP := hP.2.1
  have hcons : ∀ t, cons E (fun s => 1 / 2 * P s) t = 1 / 2 * cons E P t + 1 / 2 * E.Y t :=
    fun t => by unfold cons; ring
  have hconc : ∀ t, 1 / 2 * U.u (cons E P t) + 1 / 2 * U.u (E.Y t) ≤
      U.u (cons E (fun s => 1 / 2 * P s) t) := fun t => by
    rw [hcons]
    have := U.strictConcave.concaveOn.2 (Set.mem_Ioi.mpr (hcP t)) (Set.mem_Ioi.mpr (E.Y_pos t))
      (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
    simpa [smul_eq_mul] using this
  obtain ⟨j, hj⟩ : ∃ j, P j ≠ 0 := by
    by_contra h; push Not at h; exact hne (funext h)
  have hstrict : 1 / 2 * U.u (cons E P j) + 1 / 2 * U.u (E.Y j) <
      U.u (cons E (fun s => 1 / 2 * P s) j) := by
    rw [hcons]
    have hne' : cons E P j ≠ E.Y j := by unfold cons; intro h; apply hj; linarith
    have := U.strictConcave.2 (Set.mem_Ioi.mpr (hcP j)) (Set.mem_Ioi.mpr (E.Y_pos j)) hne'
      (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num)
    simpa [smul_eq_mul] using this
  have hobj : 1 / 2 * obj E U P + 1 / 2 * E.Ω.expect (fun t => U.u (E.Y t)) <
      obj E U (fun s => 1 / 2 * P s) := by
    unfold obj
    rw [← expect_linear]
    exact expect_strictMono E.Ω hconc (E.prob_pos j) hstrict
  have hk : 0 < β / (1 - β) := div_pos hβ0 (by linarith)
  have hIC := hP.2.2 s
  have hcs := hconc s
  unfold repCost at hIC ⊢
  have := mul_lt_mul_of_pos_left hobj hk
  nlinarith

/-- **Kuhn–Tucker necessity** at every non-null optimum, O&R (19)–(20), p. 371: for
`0 < β < 1` and an optimal feasible contract `P ≠ 0` there are `μ` and multipliers `λ ≥ 0`
satisfying (19) and complementary slackness (20). The constraint qualification is Slater's
condition, which holds away from the null contract (`slater_half`); the multipliers are
constructed explicitly from the characterisation (21). -/
theorem kuhn_tucker_necessary {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {P : S → ℝ}
    (hP : Feasible E U β P) (hopt : ∀ Q, Feasible E U β Q → obj E U Q ≤ obj E U P)
    (hne : P ≠ 0) :
    ∃ μ : ℝ, ∃ lam : S → ℝ, (∀ s, 0 ≤ lam s) ∧
      (∀ s, (E.Ω.prob s + lam s + β * E.Ω.prob s * (∑ t, lam t) / (1 - β)) *
        U.du (cons E P s) = μ * E.Ω.prob s) ∧
      (∀ s, lam s * (repCost E U β P - U.u (E.Y s) + U.u (cons E P s)) = 0) := by
  have h1β : (0 : ℝ) < 1 - β := by linarith
  set k := β / (1 - β) with hk
  have hkpos : 0 < k := div_pos hβ0 h1β
  -- a slack state exists
  obtain ⟨j, hj⟩ : ∃ j, U.u (E.Y j) - U.u (cons E P j) < repCost E U β P := by
    by_contra h; push Not at h
    exact hne (all_binding_autarky E U hβ0.le hβ1 hP hopt fun s => le_antisymm (hP.2.2 s) (h s))
  set cb := cons E P j with hcb
  have hC := hP.2.1
  have hcbpos : 0 < cb := hC j
  have hmin : ∀ s, cb ≤ cons E P s := slack_minimal E U hβ0.le hβ1 hP hopt hj
  have hbindgt : ∀ s, cb < cons E P s →
      U.u (E.Y s) - U.u (cons E P s) = repCost E U β P := by
    intro s hs
    rcases lt_or_eq_of_le (hP.2.2 s) with h | h
    · exact absurd (slack_minimal E U hβ0.le hβ1 hP hopt h j) (not_le.mpr hs)
    · exact h
  have hdupos : ∀ s, 0 < U.du (cons E P s) := fun s => U.du_pos _ (hC s)
  set lam0 : S → ℝ := fun s => E.Ω.prob s * (U.du cb / U.du (cons E P s) - 1) with hlam0
  have hratio : ∀ s, 1 ≤ U.du cb / U.du (cons E P s) := fun s => by
    rw [le_div_iff₀ (hdupos s), one_mul]; exact U.du_anti hcbpos (hmin s)
  have hlam0nn : ∀ s, 0 ≤ lam0 s := fun s =>
    mul_nonneg (E.Ω.prob_nonneg s) (by linarith [hratio s])
  have hlam0pos : ∀ s, 0 < lam0 s → cb < cons E P s := by
    intro s hs
    rcases lt_or_eq_of_le (hmin s) with h | h
    · exact h
    · exfalso; simp only [hlam0] at hs; rw [← h, div_self (hdupos j).ne'] at hs; simp at hs
  set A := ∑ t, lam0 t with hA
  set κ := 1 - k * A with hκ
  have hid : ∀ s, (κ * E.Ω.prob s + lam0 s + k * E.Ω.prob s * A) * U.du (cons E P s) =
      E.Ω.prob s * U.du cb := by
    intro s
    have hd := (hdupos s).ne'
    simp only [hκ, hlam0]
    field_simp
    ring
  -- `κ > 0`
  have hκpos : 0 < κ := by
    by_contra hκ0; push Not at hκ0
    have hApos : 0 < A := by
      by_contra hA0; push Not at hA0
      have : k * A ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hkpos.le hA0
      linarith
    obtain ⟨s₁, hs₁⟩ : ∃ s, 0 < lam0 s := by
      by_contra h; push Not at h
      have : A ≤ 0 := Finset.sum_nonpos fun t _ => h t
      linarith
    obtain ⟨hM, hMs⟩ := slater_half E U hβ0 hβ1 hP hne
    set M : S → ℝ := fun s => 1 / 2 * P s
    set d : S → ℝ := fun s => M s - P s with hd
    set Df := ∑ s, E.Ω.prob s * (U.du (cons E P s) * -d s) with hDf
    set Dg : S → ℝ := fun s => U.du (cons E P s) * d s - k * Df with hDg
    -- `E d = 0`
    have hEd : ∑ s, E.Ω.prob s * d s = 0 := by
      have : ∑ s, E.Ω.prob s * d s = -(1 / 2) * E.Ω.expect P := by
        unfold StateSpace.expect; rw [Finset.mul_sum]
        apply Finset.sum_congr rfl; intro s _; simp only [hd, M]; ring
      rw [this, hP.1, mul_zero]
    -- the identity `κ Df = Σ λ⁰ Dg`
    have hdot : κ * Df = ∑ s, lam0 s * Dg s := by
      have h1 : ∑ s, d s * ((κ * E.Ω.prob s + lam0 s + k * E.Ω.prob s * A) *
          U.du (cons E P s)) = 0 := by
        simp only [hid]
        rw [show (∑ s, d s * (E.Ω.prob s * U.du cb)) = U.du cb * ∑ s, E.Ω.prob s * d s from by
          rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro s _; ring, hEd, mul_zero]
      have eL : ∑ s, d s * ((κ * E.Ω.prob s + lam0 s + k * E.Ω.prob s * A) *
          U.du (cons E P s)) = κ * ∑ s, E.Ω.prob s * U.du (cons E P s) * d s +
          ∑ s, lam0 s * (U.du (cons E P s) * d s) +
          k * A * ∑ s, E.Ω.prob s * U.du (cons E P s) * d s := by
        simp only [Finset.mul_sum]
        rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl; intro s _; ring
      have eDf : Df = -∑ s, E.Ω.prob s * U.du (cons E P s) * d s := by
        simp only [hDf]; rw [← Finset.sum_neg_distrib]
        apply Finset.sum_congr rfl; intro s _; ring
      have eDg : ∑ s, lam0 s * Dg s =
          ∑ s, lam0 s * (U.du (cons E P s) * d s) - A * (k * Df) := by
        rw [hA, Finset.sum_mul, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl; intro s _; simp only [hDg]; ring
      have h2 : ∑ s, d s * ((κ * E.Ω.prob s + lam0 s + k * E.Ω.prob s * A) *
          U.du (cons E P s)) = -(κ * Df) + ∑ s, lam0 s * Dg s := by
        rw [eL, eDg, eDf]; ring
      linarith
    -- convexity of the constraints: `g_s(M) − g_s(P) ≥ Dg_s`
    have hconv : ∀ s, U.u (E.Y s) - U.u (cons E M s) - repCost E U β M -
        (U.u (E.Y s) - U.u (cons E P s) - repCost E U β P) ≥ Dg s := by
      intro s
      have hsl : ∀ t, U.u (cons E M t) ≤
          U.u (cons E P t) + U.du (cons E P t) * (-d t) := fun t => by
        have := U.supporting_line (hM.2.1 t) (hC t)
        have e : cons E M t - cons E P t = -d t := by simp only [cons, hd, M]; ring
        rw [e] at this; exact this
      have hobj : obj E U M - obj E U P ≤ Df := by
        unfold obj StateSpace.expect
        rw [← Finset.sum_sub_distrib]
        apply Finset.sum_le_sum; intro t _
        have := mul_le_mul_of_nonneg_left (hsl t) (E.Ω.prob_nonneg t)
        linarith
      have hrc : repCost E U β M - repCost E U β P ≤ k * Df := by
        unfold repCost
        have := mul_le_mul_of_nonneg_left hobj hkpos.le
        rw [← hk]; nlinarith
      have := hsl s
      simp only [hDg]
      linarith
    have hDgneg : ∀ s, 0 < lam0 s → Dg s < 0 := by
      intro s hs
      have hb := hbindgt s (hlam0pos s hs)
      have hsl := hMs s
      have := hconv s
      linarith
    have hsum_neg : ∑ s, lam0 s * Dg s < 0 := by
      calc ∑ s, lam0 s * Dg s < ∑ s, (0 : ℝ) := by
            apply Finset.sum_lt_sum
            · intro s _
              rcases eq_or_lt_of_le (hlam0nn s) with h | h
              · rw [← h, zero_mul]
              · exact (mul_neg_of_pos_of_neg h (hDgneg s h)).le
            · exact ⟨s₁, Finset.mem_univ _, mul_neg_of_pos_of_neg hs₁ (hDgneg s₁ hs₁)⟩
        _ = 0 := by simp
    rw [← hdot] at hsum_neg
    have hκneg : κ < 0 := by
      rcases eq_or_lt_of_le hκ0 with h | h
      · rw [h, zero_mul] at hsum_neg; exact absurd hsum_neg (lt_irrefl 0)
      · exact h
    have hDfpos : 0 < Df := by
      by_contra h; push Not at h
      have := mul_nonneg_of_nonpos_of_nonpos hκneg.le h
      linarith
    -- moving from `P` towards the Slater point raises the objective
    set φ : ℝ → ℝ := fun t => obj E U (fun s => P s + t * d s) with hφ
    have hφd : HasDerivAt φ Df 0 := by
      have hterm : ∀ s ∈ Finset.univ, HasDerivAt (fun t => E.Ω.prob s *
          U.u (E.Y s - (P s + t * d s))) (E.Ω.prob s * (U.du (cons E P s) * -d s)) 0 := by
        intro s _
        have hin : HasDerivAt (fun t : ℝ => E.Y s - (P s + t * d s)) (-d s) 0 := by
          have := (((hasDerivAt_id (0 : ℝ)).mul_const (d s)).const_add (P s)).const_sub (E.Y s)
          simpa using this
        have hc := HasDerivAt.comp_of_eq 0 (U.hasDerivAt (cons E P s) (hC s)) hin
          (by simp [cons])
        exact hc.const_mul (E.Ω.prob s)
      exact HasDerivAt.fun_sum hterm
    have hev : ∀ᶠ t in nhdsWithin (0 : ℝ) (Set.Ioi 0), 0 < slope φ 0 t := by
      have hs := hasDerivAt_iff_tendsto_slope.mp hφd
      have := (hs.eventually (lt_mem_nhds hDfpos)).filter_mono
        (nhdsWithin_mono _ fun x (hx : x ∈ Set.Ioi (0 : ℝ)) => ne_of_gt hx)
      exact this
    obtain ⟨t, ht, htI⟩ := (hev.and (Ioo_mem_nhdsGT one_pos)).exists
    rw [slope_def_field, sub_zero] at ht
    have hφt : φ 0 < φ t := by
      have := (div_pos_iff.mp ht).resolve_right (by intro h; linarith [htI.1, h.2])
      linarith [this.1]
    have hfeas := feasible_convex E U hβ0.le hβ1 hM hP (t := t) htI.1.le htI.2.le
    have e2 : (fun s => t * M s + (1 - t) * P s) = fun s => P s + t * d s := by
      funext s; simp only [hd, M]; ring
    rw [e2] at hfeas
    have hle := hopt _ hfeas
    have h0 : φ 0 = obj E U P := by simp [hφ]
    have ht' : φ t = obj E U (fun s => P s + t * d s) := rfl
    linarith
  -- the multipliers
  refine ⟨U.du cb / κ, fun s => lam0 s / κ, fun s => div_nonneg (hlam0nn s) hκpos.le,
    fun s => ?_, fun s => ?_⟩
  · have hsum : ∑ t, lam0 t / κ = A / κ := by rw [hA, Finset.sum_div]
    rw [hsum]
    have := hid s
    have hκne := hκpos.ne'
    field_simp
    rw [hk] at this
    field_simp at this
    linarith
  · rcases eq_or_lt_of_le (hlam0nn s) with h | h
    · dsimp only; rw [← h, zero_div, zero_mul]
    · dsimp only
      have hb := hbindgt s (hlam0pos s h)
      rw [show repCost E U β P - U.u (E.Y s) + U.u (cons E P s) = 0 by linarith, mul_zero]

/-- The right boundary of utility unbounded-below-free: if `u ≥ L` on `(0, ∞)` then its
infimum `L₀` satisfies `L₀ ≤ u(a) − a u′(a)` for every `a > 0` (the supporting line at `a`
evaluated at `0`) (O&R §6.1.2.2). -/
theorem inf_le_supporting_at_zero {L₀ : ℝ} (hL₀ : ∀ x, 0 < x → L₀ ≤ U.u x) {a : ℝ}
    (ha : 0 < a) : L₀ ≤ U.u a - a * U.du a := by
  apply le_of_forall_pos_lt_add
  intro δ hδ
  have hd := U.du_pos a ha
  set x := min (a / 2) (δ / (U.du a + 1)) with hx
  have hx0 : 0 < x := lt_min (by linarith) (div_pos hδ (by linarith))
  have hxa : x < a := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hxd : U.du a * x < δ := by
    have h1 : x ≤ δ / (U.du a + 1) := min_le_right _ _
    have h2 : U.du a * (δ / (U.du a + 1)) < δ := by
      rw [mul_div_assoc', div_lt_iff₀ (by linarith)]; nlinarith
    calc U.du a * x ≤ U.du a * (δ / (U.du a + 1)) := mul_le_mul_of_nonneg_left h1 hd.le
      _ < δ := h2
  have hsl := U.supporting_line hx0 ha
  have := hL₀ x hx0
  nlinarith

/-- **Existence of an optimal contract when utility is bounded below**, O&R §6.1.2.2 (no
floor assumption): the problem is maximised over the closure (consumption `≥ 0`, utility
extended continuously to `0`); at the maximiser every state with positive consumption binds
(else a transfer to a zero-consumption state would improve), which forces `P ≥ 0`, hence
`P = 0` by zero profit — so consumption is positive and the maximiser is an optimum. -/
theorem optimum_exists_bounded_below {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {L : ℝ}
    (hL : ∀ x, 0 < x → L ≤ U.u x) :
    ∃ P, Feasible E U β P ∧ ∀ Q, Feasible E U β Q → obj E U Q ≤ obj E U P := by
  classical
  have hk : 0 ≤ β / (1 - β) := div_nonneg hβ0 (by linarith)
  set L₀ := sInf (U.u '' Set.Ioi 0) with hL₀
  have hbdd : BddBelow (U.u '' Set.Ioi 0) := ⟨L, by rintro _ ⟨x, hx, rfl⟩; exact hL x hx⟩
  have hL₀le : ∀ x, 0 < x → L₀ ≤ U.u x := fun x hx => csInf_le hbdd ⟨x, hx, rfl⟩
  set ut : ℝ → ℝ := fun x => if 0 < x then U.u x else L₀ with hut
  have hut_pos : ∀ x, 0 < x → ut x = U.u x := fun x hx => by simp [hut, hx]
  have hut_np : ∀ x, ¬ 0 < x → ut x = L₀ := fun x hx => by simp [hut, hx]
  have hut_mono : Monotone ut := by
    intro x y hxy
    by_cases hx : 0 < x
    · rw [hut_pos x hx, hut_pos y (lt_of_lt_of_le hx hxy)]; exact U.mono hx hxy
    · rw [hut_np x hx]
      by_cases hy : 0 < y
      · rw [hut_pos y hy]; exact hL₀le y hy
      · rw [hut_np y hy]
  have hutc : ContinuousOn ut (Set.Ici 0) := by
    intro x hx
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hx) with h | h
    · subst h
      rw [← Set.Ioi_insert, continuousWithinAt_insert_self, ContinuousWithinAt,
        hut_np 0 (lt_irrefl 0)]
      have := hut_mono.tendsto_nhdsGT 0
      have himg : ut '' Set.Ioi 0 = U.u '' Set.Ioi 0 :=
        Set.image_congr fun y hy => hut_pos y hy
      rw [himg] at this
      exact this
    · have hc : ContinuousAt U.u x := U.continuousOn.continuousAt (Ioi_mem_nhds h)
      refine (hc.congr ?_).continuousWithinAt
      filter_upwards [Ioi_mem_nhds h] with y hy
      rw [hut_pos y hy]
  set v : ℝ → ℝ := fun x => ut (max x 0) with hv
  have hvc : Continuous v := hutc.comp_continuous (continuous_id.max continuous_const)
    fun x => Set.mem_Ici.mpr (le_max_right _ _)
  have hv_pos : ∀ x, 0 < x → v x = U.u x := fun x hx => by
    simp only [hv, max_eq_left hx.le]; exact hut_pos x hx
  have hv_zero : v 0 = L₀ := by simp only [hv, max_self]; exact hut_np 0 (lt_irrefl 0)
  have hv_mono : ∀ x y, 0 ≤ x → x ≤ y → v x ≤ v y := fun x y _ hxy =>
    hut_mono (max_le_max hxy le_rfl)
  have hv_inc : ∀ c a, 0 ≤ c → 0 < a → a * U.du (c + a) ≤ v (c + a) - v c := by
    intro c a hc ha
    rw [hv_pos (c + a) (by linarith)]
    rcases eq_or_lt_of_le hc with h | h
    · subst h; rw [hv_zero, zero_add]
      have := inf_le_supporting_at_zero U hL₀le ha; linarith
    · rw [hv_pos c h]
      have := U.supporting_line h (show 0 < c + a by linarith)
      nlinarith
  set objt : (S → ℝ) → ℝ := fun P => ∑ s, E.Ω.prob s * v (E.Y s - P s) with hobjt
  have hobjtc : Continuous objt := by
    simp only [hobjt]
    exact continuous_finsetSum _ fun s _ =>
      continuous_const.mul (hvc.comp (continuous_const.sub (continuous_apply s)))
  set EuY := E.Ω.expect (fun s => U.u (E.Y s)) with hEuY
  set K : Set (S → ℝ) := {P | ∑ s, E.Ω.prob s * P s = 0} ∩ (⋂ s, {P | 0 ≤ E.Y s - P s}) ∩
    ⋂ s, {P | U.u (E.Y s) - v (E.Y s - P s) ≤ β / (1 - β) * (objt P - EuY)} with hK
  have hobj_eq : ∀ P, (∀ s, 0 < cons E P s) → objt P = obj E U P := fun P hc => by
    simp only [hobjt, obj, StateSpace.expect, cons]
    exact Finset.sum_congr rfl fun s _ => by rw [hv_pos (E.Y s - P s) (hc s)]
  have hfeasK : ∀ P, Feasible E U β P → P ∈ K := by
    intro P hP
    simp only [hK, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
    refine ⟨⟨hP.1, fun s => (hP.2.1 s).le⟩, fun s => ?_⟩
    rw [hv_pos (E.Y s - P s) (hP.2.1 s), hobj_eq P hP.2.1]
    exact hP.2.2 s
  have hKclosed : IsClosed K := by
    refine ((isClosed_eq ?_ continuous_const).inter (isClosed_iInter fun s =>
      isClosed_le continuous_const (continuous_const.sub (continuous_apply s)))).inter
      (isClosed_iInter fun s => isClosed_le ?_ ?_)
    · exact continuous_finsetSum _ fun s _ => continuous_const.mul (continuous_apply s)
    · exact continuous_const.sub (hvc.comp (continuous_const.sub (continuous_apply s)))
    · exact continuous_const.mul (hobjtc.sub continuous_const)
  set B := ∑ t, |E.Y t|
  have hKsub : K ⊆ Set.pi Set.univ (fun s => Set.Icc (-B / E.Ω.prob s) B) := by
    intro P hP
    simp only [hK, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq] at hP
    obtain ⟨⟨hz, hc⟩, _⟩ := hP
    have hup : ∀ t, P t ≤ B := fun t => by
      have := hc t
      have := Trigger.abs_le_sum_abs E.Y t
      have := le_abs_self (E.Y t)
      linarith
    intro s _
    refine ⟨?_, hup s⟩
    rw [div_le_iff₀ (E.prob_pos s)]
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ s)] at hz
    have hrest : ∑ t ∈ Finset.univ.erase s, E.Ω.prob t * P t ≤ B := by
      calc ∑ t ∈ Finset.univ.erase s, E.Ω.prob t * P t
          ≤ ∑ t ∈ Finset.univ.erase s, E.Ω.prob t * B :=
            Finset.sum_le_sum fun t _ => mul_le_mul_of_nonneg_left (hup t) (E.Ω.prob_nonneg t)
        _ ≤ ∑ t, E.Ω.prob t * B := Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.erase_subset _ _) fun t _ _ =>
              mul_nonneg (E.Ω.prob_nonneg t) (Finset.sum_nonneg fun _ _ => abs_nonneg _)
        _ = B := by rw [← Finset.sum_mul, E.Ω.prob_sum, one_mul]
    nlinarith
  have hKcompact : IsCompact K :=
    (isCompact_univ_pi fun s => isCompact_Icc).of_isClosed_subset hKclosed hKsub
  have hKne : K.Nonempty := ⟨0, hfeasK 0 (feasible_zero E U β)⟩
  obtain ⟨P, hPK, hPmax⟩ := hKcompact.exists_isMaxOn hKne hobjtc.continuousOn
  have hmax : ∀ Q ∈ K, objt Q ≤ objt P := fun Q hQ => hPmax hQ
  simp only [hK, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq] at hPK
  obtain ⟨⟨hz, hc0⟩, hic⟩ := hPK
  set Kc := β / (1 - β) * (objt P - EuY) with hKc
  have hobj0 : objt 0 = EuY := hobj_eq 0 (fun s => by simp [cons, E.Y_pos s]) |>.trans (by
    simp [obj, cons, hEuY])
  have hKc0 : 0 ≤ Kc := by
    have := hmax 0 (hfeasK 0 (feasible_zero E U β))
    rw [hobj0] at this
    exact mul_nonneg hk (by linarith)
  -- every consumption is positive
  have hpos : ∀ s, 0 < E.Y s - P s := by
    by_contra hneg; push Not at hneg
    obtain ⟨m, hm⟩ := hneg
    have hm0 : E.Y m - P m = 0 := le_antisymm hm (hc0 m)
    -- states with positive consumption bind
    have hbind : ∀ j, 0 < E.Y j - P j → U.u (E.Y j) - U.u (E.Y j - P j) = Kc := by
      intro j hj
      by_contra hne
      have hslack : U.u (E.Y j) - U.u (E.Y j - P j) < Kc := by
        have := hic j; rw [hv_pos _ hj] at this; exact lt_of_le_of_ne this hne
      have hmj : m ≠ j := by intro h; rw [h] at hm0; linarith
      -- transfer from `j` to `m`
      set Cj := E.Y j - P j
      set pm := E.Ω.prob m
      set pj := E.Ω.prob j
      have hpm := E.prob_pos m
      have hpj := E.prob_pos j
      set σ := Kc - (U.u (E.Y j) - U.u Cj) with hσ
      have hσpos : 0 < σ := by simp only [hσ]; linarith
      have hdu := U.du_pos (Cj / 2) (by linarith)
      set b := min (min (Cj / 2) (σ / (2 * U.du (Cj / 2)))) (Cj / (2 * (1 + pj / pm)))
      have hq : 0 < 1 + pj / pm := by have : 0 < pj / pm := div_pos hpj hpm; linarith
      have hb0 : 0 < b := lt_min (lt_min (by linarith) (div_pos hσpos (by linarith)))
        (div_pos hj (by linarith))
      have hb1 : b ≤ Cj / 2 := le_trans (min_le_left _ _) (min_le_left _ _)
      have hb2 : b ≤ σ / (2 * U.du (Cj / 2)) := le_trans (min_le_left _ _) (min_le_right _ _)
      have hb3 : b ≤ Cj / (2 * (1 + pj / pm)) := min_le_right _ _
      set a := pj * b / pm with ha
      have ha0 : 0 < a := div_pos (mul_pos hpj hb0) hpm
      have hab : a < Cj - b := by
        rw [le_div_iff₀ (by linarith)] at hb3
        have : a = pj / pm * b := by rw [ha]; ring
        rw [this]; nlinarith
      set Q : S → ℝ := fun s => P s + (if s = m then -a else 0) + (if s = j then b else 0)
        with hQ
      have hQm : E.Y m - Q m = a := by
        simp only [hQ, hmj, ↓reduceIte]; linarith
      have hQj : E.Y j - Q j = Cj - b := by
        simp only [hQ, Ne.symm hmj, ↓reduceIte]; ring
      have hQo : ∀ s, s ≠ m → s ≠ j → E.Y s - Q s = E.Y s - P s := fun s h1 h2 => by
        simp only [hQ, h1, h2, ↓reduceIte]; ring
      have hzQ : ∑ s, E.Ω.prob s * Q s = 0 := by
        have e : ∑ s, E.Ω.prob s * Q s = ∑ s, E.Ω.prob s * P s +
            ∑ s, E.Ω.prob s * (if s = m then -a else 0) +
            ∑ s, E.Ω.prob s * (if s = j then b else 0) := by
          rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro s _; simp only [hQ]; ring
        rw [e, hz]
        simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
        simp only [pm, pj, ha] at *
        field_simp; ring
      have hgain : objt Q - objt P =
          pm * (v a - v 0) + pj * (U.u (Cj - b) - U.u Cj) := by
        simp only [hobjt]
        rw [← Finset.sum_sub_distrib]
        rw [Finset.sum_eq_add m j hmj
          (fun c _ hc => by simp only [hQo c hc.1 hc.2, sub_self])
          (fun h => absurd (Finset.mem_univ m) h) (fun h => absurd (Finset.mem_univ j) h)]
        rw [hQm, hQj, hm0, hv_pos _ (by linarith : 0 < Cj - b), hv_pos _ hj]
        ring
      have hCjb : 0 < Cj - b := by linarith
      have hsj : U.u Cj ≤ U.u (Cj - b) + U.du (Cj - b) * (Cj - (Cj - b)) :=
        U.supporting_line hj hCjb
      have hdd := U.du_strictAnti ha0 hab
      have hva := hv_inc 0 a le_rfl ha0
      rw [zero_add] at hva
      have hobjQ : objt P < objt Q := by
        have hpm' : pm ≠ 0 := hpm.ne'
        have e1 : pm * a = pj * b := by rw [ha]; field_simp
        have h1 : pm * (a * U.du a) ≤ pm * (v a - v 0) :=
          mul_le_mul_of_nonneg_left hva hpm.le
        have h2 : pj * (-(b * U.du (Cj - b))) ≤ pj * (U.u (Cj - b) - U.u Cj) :=
          mul_le_mul_of_nonneg_left (by
            have e : Cj - (Cj - b) = b := by ring
            rw [e] at hsj; linarith) hpj.le
        have h3 : pm * (a * U.du a) + pj * (-(b * U.du (Cj - b))) =
            pj * b * (U.du a - U.du (Cj - b)) := by linear_combination U.du a * e1
        have h4 : 0 < pj * b * (U.du a - U.du (Cj - b)) :=
          mul_pos (mul_pos hpj hb0) (by linarith)
        linarith
      have hKQ : Kc ≤ β / (1 - β) * (objt Q - EuY) := by
        simp only [hKc]; exact mul_le_mul_of_nonneg_left (by linarith) hk
      have hQK : Q ∈ K := by
        simp only [hK, Set.mem_inter_iff, Set.mem_iInter, Set.mem_ofPred_eq]
        refine ⟨⟨hzQ, fun s => ?_⟩, fun s => ?_⟩
        · by_cases h1 : s = m
          · rw [h1, hQm]; exact ha0.le
          · by_cases h2 : s = j
            · rw [h2, hQj]; exact hCjb.le
            · rw [hQo s h1 h2]; exact hc0 s
        · by_cases h1 : s = m
          · rw [h1, hQm]
            have := hic m
            have hmono := hv_mono 0 a le_rfl ha0.le
            rw [hm0] at this
            linarith
          · by_cases h2 : s = j
            · rw [h2, hQj, hv_pos _ hCjb]
              have hd2 := U.du_anti (show 0 < Cj / 2 by linarith)
                (show Cj / 2 ≤ Cj - b by linarith)
              have hbd : b * U.du (Cj / 2) < σ := by
                have h2' := (le_div_iff₀ (by linarith : (0 : ℝ) < 2 * U.du (Cj / 2))).mp hb2
                have : 0 < b * U.du (Cj / 2) := mul_pos hb0 hdu
                linarith
              have hmul : U.du (Cj - b) * b ≤ U.du (Cj / 2) * b :=
                mul_le_mul_of_nonneg_right hd2 hb0.le
              have e : Cj - (Cj - b) = b := by ring
              rw [e] at hsj
              have : U.u Cj - U.u (Cj - b) < σ := by linarith
              simp only [hσ] at this
              linarith
            · rw [hQo s h1 h2]; linarith [hic s]
      linarith [hmax Q hQK]
    -- hence all payments are nonnegative, so the contract is null
    have hnn : ∀ s, 0 ≤ P s := by
      intro s
      rcases eq_or_lt_of_le (hc0 s) with h | h
      · linarith [E.Y_pos s]
      · have := hbind s h
        have hle : U.u (E.Y s - P s) ≤ U.u (E.Y s) := by linarith
        have := (U.le_iff h (E.Y_pos s)).mp hle
        linarith
    have hP0 : P m = 0 := eq_zero_of_nonneg_of_expect_zero E.Ω hnn hz (E.prob_pos m)
    rw [hP0] at hm0
    linarith [E.Y_pos m]
  have hcons : ∀ s, 0 < cons E P s := hpos
  have hPf : Feasible E U β P := by
    refine ⟨hz, hcons, fun s => ?_⟩
    have h := hic s
    rw [hv_pos (E.Y s - P s) (hpos s)] at h
    have hKr : Kc = repCost E U β P := by rw [hKc, hobj_eq P hcons]; rfl
    rw [← hKr]; exact h
  refine ⟨P, hPf, fun Q hQ => ?_⟩
  have := hmax Q (hfeasK Q hQ)
  rw [hobj_eq Q hQ.2.1, hobj_eq P hcons] at this
  exact this

/-- **Existence of an optimal incentive-compatible contract**, O&R §6.1.2.2, for every
strictly concave utility and every `β ∈ [0, 1)`: if `u` is unbounded below a consumption floor
exists (`floor_of_unbounded_below`, `optimum_exists`), otherwise `optimum_exists_bounded_below`
applies. -/
theorem optimum_exists_general {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    ∃ P, Feasible E U β P ∧ ∀ Q, Feasible E U β Q → obj E U Q ≤ obj E U P := by
  by_cases hb : ∃ L, ∀ x, 0 < x → L ≤ U.u x
  · obtain ⟨L, hL⟩ := hb
    exact optimum_exists_bounded_below E U hβ0 hβ1 hL
  · push Not at hb
    have hbot : ∀ M, ∃ c, 0 < c ∧ U.u c < M := fun M => by
      obtain ⟨c, hc, hlt⟩ := hb M; exact ⟨c, hc, hlt⟩
    obtain ⟨c₀, hc₀, hfl⟩ := floor_of_unbounded_below E U β hbot
    exact optimum_exists E U hβ0 hβ1 hc₀ hfl

end PartialInsurance


/-! ## Subgame perfection, multiplicity and renegotiation (§6.1.3, pp. 376–377) -/

namespace SubgamePerfection

open PartialInsurance

variable {S : Type} [Fintype S] (E : Endowment S) (U : Utility)

/-- The expected profit of a lender who offers the schedule `P` to a borrower expected to
default whenever it owes (it collects `−P` when `P < 0` and never pays when `P > 0`): the
punishment phase of O&R p. 376. -/
noncomputable def profitVsDefaulter (P : S → ℝ) : ℝ := E.Ω.expect (fun s => min (P s) 0)

/-- O&R p. 376: lending to a defaulter never pays. -/
theorem profitVsDefaulter_nonpos (P : S → ℝ) : profitVsDefaulter E P ≤ 0 := by
  have := expect_mono E.Ω (X := fun s => min (P s) 0) (Y := fun _ => (0 : ℝ))
    fun s => min_le_right _ _
  rwa [E.Ω.expect_const] at this

/-- O&R p. 376: any non-null zero-profit contract offered to a defaulter makes a strict loss,
so not lending is the strict best response in the punishment phase (for creditors, and for the
defaulter itself, which "believes that any potential insurer will default"). -/
theorem profitVsDefaulter_neg {P : S → ℝ} (hzp : E.Ω.expect P = 0) (hne : P ≠ 0) :
    profitVsDefaulter E P < 0 := by
  obtain ⟨s, hs⟩ : ∃ s, P s < 0 := by
    by_contra h; push Not at h
    exact hne (funext fun s => eq_zero_of_nonneg_of_expect_zero E.Ω h hzp (E.prob_pos s))
  have := expect_strictMono E.Ω (X := fun s => min (P s) 0) (Y := fun _ => (0 : ℝ))
    (fun s => min_le_right _ _) (E.prob_pos s) (by simp [hs])
  rw [E.Ω.expect_const] at this
  exact this

/-- O&R p. 376: with no future access to lose, a defaulter's best response to any contract is
to collect what it is owed and pay nothing. -/
theorem defaulter_best_response (P : S → ℝ) (s : S) (h : 0 < E.Y s - P s) :
    U.u (E.Y s - P s) ≤ U.u (E.Y s - min (P s) 0) :=
  U.mono h (by linarith [min_le_left (P s) (0 : ℝ)])

/-- **The trigger profile** (O&R pp. 376–377) for a stationary contract `P`: (i) in the
cooperative phase honouring beats every default strategy of the country; (ii) lenders break
even; (iii) in the punishment phase no lender gains by lending to the defaulter; (iv) in the
punishment phase the defaulter's "always default" is a best response. Since the environment
is i.i.d. and strategies depend only on the phase, these are the conditions for every
subgame. -/
def TriggerSPE (β : ℝ) (P : S → ℝ) : Prop :=
  (∀ (d : Strategy S) (w : (n : ℕ) → (Fin (n + 1) → S) → ℝ) (Mw : ℝ),
      (∀ n h, |w n h| ≤ Mw) → (∀ n h, w n h ≤ U.u (E.Y (h (Fin.last n)))) →
      payoff E.Ω β d (fun s => U.u (cons E P s)) (fun s => U.u (E.Y s)) w ≤
        obj E U P / (1 - β)) ∧
    E.Ω.expect P = 0 ∧ (∀ Q : S → ℝ, profitVsDefaulter E Q ≤ 0) ∧
    (∀ (Q : S → ℝ) (s : S), 0 < E.Y s - Q s → U.u (E.Y s - Q s) ≤ U.u (E.Y s - min (Q s) 0))

/-- **The autarky profile** (O&R p. 377, "including none"): nobody ever lends and every
country always defaults; conditions (iii)–(iv) in every subgame. -/
def AutarkySPE : Prop :=
  (∀ Q : S → ℝ, profitVsDefaulter E Q ≤ 0) ∧
    (∀ (Q : S → ℝ) (s : S), 0 < E.Y s - Q s → U.u (E.Y s - Q s) ≤ U.u (E.Y s - min (Q s) 0))

/-- **Subgame perfection of the trigger profile iff sustainability**, O&R pp. 376–377: for a
zero-profit stationary contract, the trigger profile is subgame perfect iff (18) holds (for
full insurance, iff (16)); the punishments are self-enforcing in every case. -/
theorem triggerSPE_iff {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {P : S → ℝ}
    (hzp : E.Ω.expect P = 0) : TriggerSPE E U β P ↔ RepIC E U β P := by
  rw [repIC_iff_no_deviation E U hβ0 hβ1 P]
  exact ⟨fun h => h.1, fun h => ⟨h, hzp, profitVsDefaulter_nonpos E,
    fun Q s hs => defaulter_best_response E U Q s hs⟩⟩

/-- The autarky profile is always subgame perfect (O&R p. 377). -/
theorem autarkySPE_holds : AutarkySPE E U :=
  ⟨profitVsDefaulter_nonpos E, fun Q s hs => defaulter_best_response E U Q s hs⟩

/-- **Multiplicity**, O&R p. 377: when (16) holds, both the full-insurance trigger profile and
autarky are subgame-perfect equilibria. -/
theorem multiplicity {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (h16 : ∀ s, U.u (E.Y s) - U.u E.Ybar ≤
      β / (1 - β) * (U.u E.Ybar - E.Ω.expect (fun s => U.u (E.Y s)))) :
    TriggerSPE E U β E.ε ∧ AutarkySPE E U :=
  ⟨(triggerSPE_iff E U hβ0 hβ1 E.mean_zero).mpr (full_insurance_optimal_of_16 E U h16).1.2.2,
    autarkySPE_holds E U⟩

/-- **A continuum of equilibria with different degrees of risk sharing**, O&R p. 377: when
(16) holds, the trigger profile with the partial-insurance contract `P = tε` is subgame perfect
for every `t ∈ [0, 1]`. -/
theorem continuum_of_equilibria {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (h16 : ∀ s, U.u (E.Y s) - U.u E.Ybar ≤
      β / (1 - β) * (U.u E.Ybar - E.Ω.expect (fun s => U.u (E.Y s))))
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : TriggerSPE E U β (fun s => t * E.ε s) := by
  have hF := feasible_convex E U hβ0 hβ1 (full_insurance_optimal_of_16 E U h16).1
    (feasible_zero E U β) ht0 ht1
  have e : (fun s => t * E.ε s + (1 - t) * (0 : S → ℝ) s) = fun s => t * E.ε s := by
    funext s; simp
  rw [e] at hF
  exact (triggerSPE_iff E U hβ0 hβ1 hF.1).mpr hF.2.2

/-- Weak renegotiation-proofness (Farrell–Maskin), for a set of continuation payoff vectors
(country, lenders) of subgame-perfect equilibria: no member is strictly Pareto-dominated by
another member (O&R p. 377). -/
def WeaklyRenegotiationProof (vals : Set (ℝ × ℝ)) : Prop :=
  ∀ v ∈ vals, ∀ w ∈ vals, ¬ (v.1 ≤ w.1 ∧ v.2 ≤ w.2 ∧ (v.1 < w.1 ∨ v.2 < w.2))

/-- **Permanent-exclusion punishments are not renegotiation-proof**, O&R p. 377: when (16)
holds and the shock is nondegenerate, the punishment (autarky) continuation, with payoffs
`(E u(Ȳ + ε)/(1 − β), 0)`, is strictly Pareto-dominated by resuming full insurance, with payoffs
`(u(Ȳ)/(1 − β), 0)`; both are equilibrium continuations (`multiplicity`), so the pair is not
weakly renegotiation-proof. -/
theorem exclusion_not_renegotiation_proof {β : ℝ} (hβ1 : β < 1) (hnd : ∃ s, E.ε s ≠ 0) :
    ¬ WeaklyRenegotiationProof ({(E.Ω.expect (fun s => U.u (E.Y s)) / (1 - β), 0),
      (U.u E.Ybar / (1 - β), 0)} : Set (ℝ × ℝ)) := by
  intro h
  obtain ⟨s, hs⟩ := hnd
  have hj := jensen_strict E.Ω U E.Y_pos (E.prob_pos s) (by
    rw [E.expect_Y]; unfold Endowment.Y; intro h'; apply hs; linarith)
  rw [E.expect_Y] at hj
  have hlt : E.Ω.expect (fun s => U.u (E.Y s)) / (1 - β) < U.u E.Ybar / (1 - β) :=
    div_lt_div_of_pos_right hj (by linarith)
  exact h _ (Set.mem_insert _ _) _ (Set.mem_insert_of_mem _ rfl) ⟨hlt.le, le_rfl, Or.inl hlt⟩

end SubgamePerfection

/-! ## A general-equilibrium model of reputation, §6.1.3 -/

namespace GeneralEquilibrium

variable {S W : Type}

/-- The product of two independent finite probability spaces (O&R §6.1.3: the idiosyncratic
shock `ε^j` is independent of the global shock `ω`). -/
noncomputable def prodSpace [Fintype S] [Fintype W] (Ω₁ : StateSpace S) (Ω₂ : StateSpace W) :
    StateSpace (S × W) :=
  ⟨fun p => Ω₁.prob p.1 * Ω₂.prob p.2, fun p => mul_nonneg (Ω₁.prob_nonneg _) (Ω₂.prob_nonneg _),
    by rw [Fintype.sum_prod_type]; simp [← Finset.mul_sum, Ω₂.prob_sum, Ω₁.prob_sum]⟩

/-- Expectation over the product space is the iterated expectation (O&R §6.1.3). -/
theorem prod_expect [Fintype S] [Fintype W] (Ω₁ : StateSpace S) (Ω₂ : StateSpace W)
    (f : S × W → ℝ) :
    (prodSpace Ω₁ Ω₂).expect f = Ω₂.expect (fun w => Ω₁.expect (fun s => f (s, w))) := by
  unfold StateSpace.expect prodSpace
  simp only
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl; intro w _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro s _
  ring

/-- Positive probabilities on both factors give positive product probabilities.
(O&R §6.1.3, p. 376) -/
theorem prod_prob_pos [Fintype S] [Fintype W] (Ω₁ : StateSpace S) (Ω₂ : StateSpace W)
    (h₁ : ∀ s, 0 < Ω₁.prob s)
    (h₂ : ∀ w, 0 < Ω₂.prob w) (p : S × W) : 0 < (prodSpace Ω₁ Ω₂).prob p :=
  mul_pos (h₁ p.1) (h₂ p.2)

variable (U : Utility) (Ybar : ℝ) (ε : S → ℝ) (ω : W → ℝ)

/-- The short-term gain from repudiating first-best insurance, O&R p. 377:
`Gain(ε, ω) = u(Ȳ + ε + ω) − u(Ȳ + ω)`. -/
noncomputable def gainGE (s : S) (w : W) : ℝ := U.u (Ybar + ε s + ω w) - U.u (Ybar + ω w)

/-- The expected future cost of exclusion, O&R p. 377:
`Cost = β/(1 − β)[E u(Ȳ + ω) − E u(Ȳ + ε + ω)]`. -/
noncomputable def costGE [Fintype S] [Fintype W] (Ω₁ : StateSpace S) (Ω₂ : StateSpace W)
    (β : ℝ) : ℝ :=
  β / (1 - β) * ((prodSpace Ω₁ Ω₂).expect (fun p => U.u (Ybar + ω p.2)) -
    (prodSpace Ω₁ Ω₂).expect (fun p => U.u (Ybar + ε p.1 + ω p.2)))

/-- O&R p. 377: the gain from default rises with the country's own shock. -/
theorem gainGE_mono_eps (hpos : ∀ s w, 0 < Ybar + ε s + ω w) {s s' : S} (h : ε s ≤ ε s')
    (w : W) : gainGE U Ybar ε ω s w ≤ gainGE U Ybar ε ω s' w := by
  unfold gainGE
  have := U.mono (hpos s w) (show Ybar + ε s + ω w ≤ Ybar + ε s' + ω w by linarith)
  linarith

/-- O&R p. 377: for a relative boom (`ε ≥ 0`) the gain from default is largest when the world
is in its deepest recession: `Gain(ε, ·)` is antitone in `ω` (strict concavity). -/
theorem gainGE_anti_omega (hW : ∀ w, 0 < Ybar + ω w) {s : S} (hs : 0 ≤ ε s) {w w' : W}
    (h : ω w ≤ ω w') : gainGE U Ybar ε ω s w' ≤ gainGE U Ybar ε ω s w := by
  unfold gainGE
  rcases eq_or_lt_of_le hs with h0 | h0
  · rw [← h0]; simp
  rcases eq_or_lt_of_le h with h1 | h1
  · rw [h1]
  · have := PartialInsurance.increment_strict_anti U (hW w)
      (show Ybar + ω w < Ybar + ω w' by linarith) h0
    have e1 : Ybar + ω w' + ε s = Ybar + ε s + ω w' := by ring
    have e2 : Ybar + ω w + ε s = Ybar + ε s + ω w := by ring
    rw [e1, e2] at this
    linarith

/-- O&R p. 377: the cost of exclusion is positive for `0 < β < 1` and a nondegenerate
idiosyncratic shock, by Jensen's inequality conditional on each `ω`. -/
theorem costGE_pos [Fintype S] [Fintype W] (Ω₁ : StateSpace S) (Ω₂ : StateSpace W)
    (h₁ : ∀ s, 0 < Ω₁.prob s) (hmean : Ω₁.expect ε = 0) (hpos : ∀ s w, 0 < Ybar + ε s + ω w)
    (hnd : ∃ s, ε s ≠ 0) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    0 < costGE U Ybar ε ω Ω₁ Ω₂ β := by
  obtain ⟨s₀, hs₀⟩ := hnd
  have hw : ∀ w, Ω₁.expect (fun s => U.u (Ybar + ε s + ω w)) < U.u (Ybar + ω w) := by
    intro w
    have hm : Ω₁.expect (fun s => Ybar + ε s + ω w) = Ybar + ω w := by
      rw [show (fun s => Ybar + ε s + ω w) = fun s => (Ybar + ω w) + ε s from
        funext fun s => by ring, expect_const_add, hmean, add_zero]
    have := jensen_strict Ω₁ U (C := fun s => Ybar + ε s + ω w) (fun s => hpos s w) (h₁ s₀)
      (by rw [hm]; intro h; apply hs₀; linarith)
    rwa [hm] at this
  have hne := StateSpaceFacts.nonempty Ω₂
  have hsum : (prodSpace Ω₁ Ω₂).expect (fun p => U.u (Ybar + ε p.1 + ω p.2)) <
      (prodSpace Ω₁ Ω₂).expect (fun p => U.u (Ybar + ω p.2)) := by
    rw [prod_expect, prod_expect]
    simp only [Ω₁.expect_const]
    obtain ⟨w₀, hw₀⟩ : ∃ w, 0 < Ω₂.prob w := by
      by_contra hn; push Not at hn
      have : ∑ w, Ω₂.prob w ≤ 0 := Finset.sum_nonpos fun w _ => hn w
      rw [Ω₂.prob_sum] at this; linarith
    exact expect_strictMono Ω₂ (fun w => (hw w).le) hw₀ (hw w₀)
  unfold costGE
  exact mul_pos (div_pos hβ0 (by linarith)) (by linarith)

/-- **The sustainability condition of §6.1.3**, O&R p. 377: with `ε̄` the largest idiosyncratic
shock and `ω_` the deepest world recession, first-best insurance survives every temptation iff
`Gain(ε̄, ω_) ≤ Cost`. -/
theorem ge_condition_iff [Fintype S] (Ω₁ : StateSpace S) (hmean : Ω₁.expect ε = 0)
    (hpos : ∀ s w, 0 < Ybar + ε s + ω w) (hW : ∀ w, 0 < Ybar + ω w) {smax : S} {wmin : W}
    (hsmax : ∀ s, ε s ≤ ε smax) (hwmin : ∀ w, ω wmin ≤ ω w) (K : ℝ) :
    (∀ s w, gainGE U Ybar ε ω s w ≤ K) ↔ gainGE U Ybar ε ω smax wmin ≤ K := by
  have hmax0 : 0 ≤ ε smax := by
    have := expect_mono Ω₁ (X := ε) (Y := fun _ => ε smax) hsmax
    rw [Ω₁.expect_const, hmean] at this; exact this
  refine ⟨fun H => H smax wmin, fun H s w => ?_⟩
  calc gainGE U Ybar ε ω s w ≤ gainGE U Ybar ε ω smax w := gainGE_mono_eps U Ybar ε ω hpos
        (hsmax s) w
    _ ≤ gainGE U Ybar ε ω smax wmin := gainGE_anti_omega U Ybar ε ω hW hmax0 (hwmin w)
    _ ≤ K := H

/-- **The trigger-strategy equilibrium of §6.1.3 as an iff**, O&R pp. 376–377: with
independent i.i.d. shocks `(ε^j, ω)`, honouring the first-best insurance contract beats every
default strategy of country `j` (stopping times, partial defaults) under permanent exclusion
iff `Gain(ε, ω) ≤ Cost` in every state. -/
theorem ge_trigger_iff [Fintype S] [Fintype W] (Ω₁ : StateSpace S) (Ω₂ : StateSpace W)
    (h₁ : ∀ s, 0 < Ω₁.prob s)
    (h₂ : ∀ w, 0 < Ω₂.prob w) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    (∀ (d : Strategy (S × W)) (w : (n : ℕ) → (Fin (n + 1) → S × W) → ℝ) (Mw : ℝ),
        (∀ n h, |w n h| ≤ Mw) →
        (∀ n h, w n h ≤ U.u (Ybar + ε (h (Fin.last n)).1 + ω (h (Fin.last n)).2)) →
        payoff (prodSpace Ω₁ Ω₂) β d (fun p => U.u (Ybar + ω p.2))
          (fun p => U.u (Ybar + ε p.1 + ω p.2)) w ≤
          (prodSpace Ω₁ Ω₂).expect (fun p => U.u (Ybar + ω p.2)) / (1 - β)) ↔
      ∀ s w, gainGE U Ybar ε ω s w ≤ costGE U Ybar ε ω Ω₁ Ω₂ β := by
  refine (trigger_iff (prodSpace Ω₁ Ω₂) hβ0 hβ1 (prod_prob_pos Ω₁ Ω₂ h₁ h₂)
    (fun p => U.u (Ybar + ω p.2)) (fun p => U.u (Ybar + ε p.1 + ω p.2))
    (fun p => U.u (Ybar + ε p.1 + ω p.2))).trans ?_
  constructor
  · intro H s w; exact H (s, w)
  · intro H p; exact H p.1 p.2

/-- O&R p. 377: the condition "can always be met if `β` is close enough to 1". -/
theorem ge_sustainable_near_one [Fintype S] [Fintype W] (Ω₁ : StateSpace S) (Ω₂ : StateSpace W)
    (h₁ : ∀ s, 0 < Ω₁.prob s) (hmean : Ω₁.expect ε = 0) (hpos : ∀ s w, 0 < Ybar + ε s + ω w)
    (hnd : ∃ s, ε s ≠ 0) :
    ∃ β₀, 0 < β₀ ∧ β₀ < 1 ∧ ∀ β, β₀ ≤ β → β < 1 →
      ∀ s w, gainGE U Ybar ε ω s w ≤ costGE U Ybar ε ω Ω₁ Ω₂ β := by
  set c := (prodSpace Ω₁ Ω₂).expect (fun p => U.u (Ybar + ω p.2)) -
    (prodSpace Ω₁ Ω₂).expect (fun p => U.u (Ybar + ε p.1 + ω p.2)) with hc
  have hcpos : 0 < c := by
    have := costGE_pos U Ybar ε ω Ω₁ Ω₂ h₁ hmean hpos hnd (β := 1 / 2) (by norm_num)
      (by norm_num)
    unfold costGE at this
    rw [← hc] at this
    have h2 : (0 : ℝ) < 1 / 2 / (1 - 1 / 2) := by norm_num
    exact pos_of_mul_pos_right this h2.le
  set G := ∑ p : S × W, |gainGE U Ybar ε ω p.1 p.2| + 1 with hG
  have hGpos : 0 < G := by
    have : 0 ≤ ∑ p : S × W, |gainGE U Ybar ε ω p.1 p.2| :=
      Finset.sum_nonneg fun _ _ => abs_nonneg _
    linarith
  refine ⟨G / (G + c), div_pos hGpos (by linarith), (div_lt_one (by linarith)).mpr
    (by linarith), fun β hβ hβ1 s w => ?_⟩
  have h1 : 0 < 1 - β := by linarith
  have hk : G ≤ β / (1 - β) * c := by
    rw [div_le_iff₀ (by linarith)] at hβ
    rw [div_mul_eq_mul_div, le_div_iff₀ h1]
    nlinarith
  have hgs : gainGE U Ybar ε ω s w ≤ G := by
    have := le_trans (le_abs_self _)
      (Trigger.abs_le_sum_abs (fun p : S × W => gainGE U Ybar ε ω p.1 p.2) (s, w))
    linarith
  unfold costGE
  rw [← hc]
  linarith

/-- **Assumption (22) is inconsistent with i.i.d. shocks across finitely many countries**
(O&R p. 376): if `J ≥ 1` countries draw independent shocks from the same finite distribution
(so every joint realisation has positive probability) and `Σ_j ε^j = 0` in every realisation,
then every shock is zero. (The book's setup needs a continuum of countries or exchangeable,
non-independent shocks.) -/
theorem idiosyncratic_sum_zero_degenerate {J : ℕ} (hJ : 0 < J) (ε' : S → ℝ)
    (h : ∀ x : Fin J → S, ∑ j, ε' (x j) = 0) (s : S) : ε' s = 0 := by
  have := h (fun _ => s)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
  have hJ' : (J : ℝ) ≠ 0 := by exact_mod_cast hJ.ne'
  exact (mul_eq_zero.mp this).resolve_left hJ'

end GeneralEquilibrium

/-! ## Exercise 3(a): a reputational equilibrium with investment -/

namespace ReputationInvestment

variable {S : Type} [Fintype S] (Ω : StateSpace S) (U : Utility)

/-- The production-function conditions of Exercise 3, O&R p. 426, in usable form: if
`F' > 1 + r` below `D̃` and `F' = 1 + r` from `D̃` on, then `F(D) − (1 + r)D` is maximised at
`D̃`, strictly below it and constant above it, and `F` is strictly increasing. -/
theorem production_facts {F F' : ℝ → ℝ} {r Dt : ℝ} (hr : -1 < r)
    (hF : ∀ x, HasDerivAt F (F' x) x) (hlo : ∀ x, x < Dt → 1 + r < F' x)
    (hhi : ∀ x, Dt ≤ x → F' x = 1 + r) :
    (∀ D, D < Dt → F D - (1 + r) * D < F Dt - (1 + r) * Dt) ∧
      (∀ D, Dt ≤ D → F D - (1 + r) * D = F Dt - (1 + r) * Dt) ∧ StrictMono F := by
  set g : ℝ → ℝ := fun x => F x - (1 + r) * x with hg
  have hgd : ∀ x, HasDerivAt g (F' x - (1 + r)) x := fun x => by
    have h2 : HasDerivAt (fun y => (1 + r) * y) (1 + r) x := by
      simpa using (hasDerivAt_id x).const_mul (1 + r)
    exact HasDerivAt.sub (hF x) h2
  have hgc : Continuous g := continuous_iff_continuousAt.mpr fun x => (hgd x).continuousAt
  have hmono : StrictMonoOn g (Set.Iic Dt) := by
    apply strictMonoOn_of_deriv_pos (convex_Iic Dt) hgc.continuousOn
    intro x hx
    rw [interior_Iic] at hx
    rw [(hgd x).deriv]; linarith [hlo x hx]
  have hconst : ∀ D, Dt ≤ D → g D = g Dt := by
    intro D hD
    have hdiff : DifferentiableOn ℝ g (interior (Set.Ici Dt)) := fun x _ =>
      (hgd x).differentiableAt.differentiableWithinAt
    have hm := monotoneOn_of_deriv_nonneg (convex_Ici Dt) hgc.continuousOn hdiff (fun x hx => by
      rw [interior_Ici] at hx; rw [(hgd x).deriv, hhi x (le_of_lt hx)]; simp)
    have ha := antitoneOn_of_deriv_nonpos (convex_Ici Dt) hgc.continuousOn hdiff (fun x hx => by
      rw [interior_Ici] at hx; rw [(hgd x).deriv, hhi x (le_of_lt hx)]; simp)
    exact le_antisymm (ha (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hD) hD)
      (hm (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hD) hD)
  refine ⟨fun D hD => hmono (Set.mem_Iic.mpr hD.le) (Set.mem_Iic.mpr le_rfl) hD, hconst, ?_⟩
  apply strictMono_of_deriv_pos
  intro x
  rw [(hF x).deriv]
  by_cases h : x < Dt
  · linarith [hlo x h]
  · rw [hhi x (not_lt.mp h)]; linarith

/-- A one-period repayment contract of Exercise 3, O&R p. 426: borrow `D ≥ 0`, repay
`P(ε) ≥ 0` with `E P = (1 + r)D`; consumption `C = F(D) + ε − P(ε)`. -/
def Feasible3 (F : ℝ → ℝ) (r : ℝ) (ε : S → ℝ) (D : ℝ) (P : S → ℝ) : Prop :=
  0 ≤ D ∧ (∀ s, 0 ≤ P s) ∧ Ω.expect P = (1 + r) * D ∧ ∀ s, 0 < F D + ε s - P s

/-- The first-best consumption level of Exercise 3(a):
`C̄ = F(D̃) − (1 + r)D̃ + E ε`.
(O&R Exercise 3(a), p. 426) -/
def cbar3 (F : ℝ → ℝ) (r Dt : ℝ) (ε : S → ℝ) : ℝ := F Dt - (1 + r) * Dt + Ω.expect ε

/-- **The commitment optimum is bounded by `u(C̄)`**, O&R Exercise 3(a): every feasible
contract gives `E u(C) ≤ u(C̄)` (Jensen and `F(D) − (1 + r)D ≤ F(D̃) − (1 + r)D̃`). -/
theorem commitment_le {F F' : ℝ → ℝ} {r Dt : ℝ} (hr : -1 < r)
    (hF : ∀ x, HasDerivAt F (F' x) x) (hlo : ∀ x, x < Dt → 1 + r < F' x)
    (hhi : ∀ x, Dt ≤ x → F' x = 1 + r) {ε : S → ℝ} {D : ℝ} {P : S → ℝ}
    (hP : Feasible3 Ω F r ε D P) :
    Ω.expect (fun s => U.u (F D + ε s - P s)) ≤ U.u (cbar3 Ω F r Dt ε) := by
  obtain ⟨h1, h2, _⟩ := production_facts hr hF hlo hhi
  obtain ⟨_, _, hm, hc⟩ := hP
  have hEC : Ω.expect (fun s => F D + ε s - P s) = F D - (1 + r) * D + Ω.expect ε := by
    rw [show (fun s => F D + ε s - P s) = fun s => F D + (ε s - P s) from
      funext fun s => by ring, expect_const_add, expect_sub, hm]; ring
  have hle : F D - (1 + r) * D ≤ F Dt - (1 + r) * Dt := by
    by_cases h : D < Dt
    · exact (h1 D h).le
    · exact (h2 D (not_lt.mp h)).le
  have hj := jensen Ω U hc
  rw [hEC] at hj
  have hpos : 0 < F D - (1 + r) * D + Ω.expect ε := by
    rw [← hEC]
    have := StateSpaceFacts.nonempty Ω
    have hle0 := expect_mono Ω (X := fun _ => (0 : ℝ)) (Y := fun s => F D + ε s - P s)
      fun s => (hc s).le
    rw [Ω.expect_const] at hle0
    rcases eq_or_lt_of_le hle0 with he | he
    · exfalso
      obtain ⟨s₀, hs₀⟩ : ∃ s, 0 < Ω.prob s := by
        by_contra hn; push Not at hn
        have : ∑ s, Ω.prob s ≤ 0 := Finset.sum_nonpos fun s _ => hn s
        rw [Ω.prob_sum] at this; linarith
      have := expect_strictMono Ω (X := fun _ => (0 : ℝ)) (fun s => (hc s).le) hs₀ (hc s₀)
      rw [Ω.expect_const] at this; linarith
    · exact he
  exact le_trans hj (U.mono hpos (by unfold cbar3; linarith))

/-- **The optimal commitment contracts**, O&R Exercise 3(a): a contract with loan
`D ≥ D̃` and `(1 + r)D ≥ E ε − ε` in every state, repaying `P(ε) = ε − E ε + (1 + r)D`, is
feasible and gives constant consumption `C̄`; it attains the bound of `commitment_le`. -/
theorem commitment_optimum {F F' : ℝ → ℝ} {r Dt : ℝ} (hr : -1 < r)
    (hF : ∀ x, HasDerivAt F (F' x) x) (hlo : ∀ x, x < Dt → 1 + r < F' x)
    (hhi : ∀ x, Dt ≤ x → F' x = 1 + r) {ε : S → ℝ} (hC : 0 < cbar3 Ω F r Dt ε) {D : ℝ}
    (hD0 : 0 ≤ D) (hD : Dt ≤ D) (hcol : ∀ s, Ω.expect ε - ε s ≤ (1 + r) * D) :
    Feasible3 Ω F r ε D (fun s => ε s - Ω.expect ε + (1 + r) * D) ∧
      ∀ s, F D + ε s - (ε s - Ω.expect ε + (1 + r) * D) = cbar3 Ω F r Dt ε := by
  obtain ⟨_, h2, _⟩ := production_facts hr hF hlo hhi
  have hcons : ∀ s, F D + ε s - (ε s - Ω.expect ε + (1 + r) * D) = cbar3 Ω F r Dt ε := by
    intro s; unfold cbar3; have := h2 D hD; linarith
  refine ⟨⟨hD0, fun s => by linarith [hcol s], ?_, fun s => by rw [hcons]; exact hC⟩, hcons⟩
  rw [show (fun s => ε s - Ω.expect ε + (1 + r) * D) =
      fun s => (-Ω.expect ε + (1 + r) * D) + ε s from funext fun s => by ring,
    expect_const_add]; ring

/-- **Characterisation of the commitment optimum**, O&R Exercise 3(a): a feasible contract
attains `u(C̄)` iff `D ≥ D̃` and `P(ε) = ε − E ε + (1 + r)D` (full insurance); feasibility then
forces `(1 + r)D ≥ E ε − ε` in every state. Every state has positive probability. -/
theorem commitment_optimum_iff {F F' : ℝ → ℝ} {r Dt : ℝ} (hr : -1 < r)
    (hF : ∀ x, HasDerivAt F (F' x) x) (hlo : ∀ x, x < Dt → 1 + r < F' x)
    (hhi : ∀ x, Dt ≤ x → F' x = 1 + r) (hpos : ∀ s, 0 < Ω.prob s) {ε : S → ℝ} {D : ℝ}
    {P : S → ℝ} (hP : Feasible3 Ω F r ε D P) :
    Ω.expect (fun s => U.u (F D + ε s - P s)) = U.u (cbar3 Ω F r Dt ε) ↔
      Dt ≤ D ∧ ∀ s, P s = ε s - Ω.expect ε + (1 + r) * D := by
  obtain ⟨h1, h2, _⟩ := production_facts hr hF hlo hhi
  obtain ⟨hD0, hP0, hm, hc⟩ := hP
  have hEC : Ω.expect (fun s => F D + ε s - P s) = F D - (1 + r) * D + Ω.expect ε := by
    rw [show (fun s => F D + ε s - P s) = fun s => F D + (ε s - P s) from
      funext fun s => by ring, expect_const_add, expect_sub, hm]; ring
  constructor
  · intro heq
    have hj := jensen Ω U hc
    rw [hEC, heq] at hj
    have hECpos : 0 < F D - (1 + r) * D + Ω.expect ε := by
      rw [← hEC]
      have := StateSpaceFacts.nonempty Ω
      obtain ⟨s₀⟩ := this
      have := expect_strictMono Ω (X := fun _ => (0 : ℝ)) (fun s => (hc s).le) (hpos s₀) (hc s₀)
      rw [Ω.expect_const] at this; exact this
    have hCpos : 0 < cbar3 Ω F r Dt ε := by
      unfold cbar3
      by_cases h : D < Dt
      · linarith [h1 D h]
      · linarith [h2 D (not_lt.mp h)]
    have hge := (U.le_iff hCpos hECpos).mp hj
    have hD : Dt ≤ D := by
      by_contra h; push Not at h
      have := h1 D h
      unfold cbar3 at hge; linarith
    refine ⟨hD, fun s => ?_⟩
    -- equality in Jensen forces constant consumption
    by_contra hne
    have hconst : F D + ε s - P s ≠ Ω.expect (fun s => F D + ε s - P s) := by
      rw [hEC]; intro h; apply hne
      have := h2 D hD; unfold cbar3 at *; linarith
    have := jensen_strict Ω U hc (hpos s) hconst
    rw [hEC, heq] at this
    have hle := U.mono hECpos (show F D - (1 + r) * D + Ω.expect ε ≤ cbar3 Ω F r Dt ε by
      unfold cbar3; have := h2 D hD; linarith)
    linarith
  · rintro ⟨hD, hPs⟩
    have hcons : ∀ s, F D + ε s - P s = cbar3 Ω F r Dt ε := by
      intro s; rw [hPs]; unfold cbar3; have := h2 D hD; linarith
    simp only [hcons]
    exact Ω.expect_const _

/-- **Lifetime optimality**, O&R Exercise 3(a): with no saving or lending, any sequence of
feasible one-period contracts gives lifetime utility `Σ βⁿ E u(C_n) ≤ u(C̄)/(1 − β)`, the value of
repeating the commitment optimum. -/
theorem commitment_lifetime_le {F F' : ℝ → ℝ} {r Dt β : ℝ} (hr : -1 < r)
    (hF : ∀ x, HasDerivAt F (F' x) x) (hlo : ∀ x, x < Dt → 1 + r < F' x)
    (hhi : ∀ x, Dt ≤ x → F' x = 1 + r) (hβ0 : 0 ≤ β) (hβ1 : β < 1) {ε : S → ℝ}
    (D : ℕ → ℝ) (P : ℕ → S → ℝ) (hP : ∀ n, Feasible3 Ω F r ε (D n) (P n))
    (hsum : Summable fun n => β ^ n * Ω.expect (fun s => U.u (F (D n) + ε s - P n s))) :
    ∑' n, β ^ n * Ω.expect (fun s => U.u (F (D n) + ε s - P n s)) ≤
      U.u (cbar3 Ω F r Dt ε) / (1 - β) := by
  rw [← (Geometric.hasSum_geometric_const hβ0 hβ1 (U.u (cbar3 Ω F r Dt ε))).tsum_eq]
  exact hsum.tsum_le_tsum (fun n => mul_le_mul_of_nonneg_left
    (commitment_le Ω U hr hF hlo hhi (hP n)) (pow_nonneg hβ0 n))
    (Geometric.hasSum_geometric_const hβ0 hβ1 _).summable

/-- **Enforceability by exclusion**, O&R Exercise 3(a): the commitment optimum with loan `D`
is a trigger-strategy equilibrium (honouring beats every default strategy, where a defaulter
consumes `F(D) + ε` at the default date and the autarky level `F(0) + ε` for ever after) iff
`u(F(D) + ε) − u(C̄) ≤ β/(1 − β)[u(C̄) − E u(F(0) + ε)]` in every state. -/
theorem enforceable_iff {F : ℝ → ℝ} {r Dt β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hpos : ∀ s, 0 < Ω.prob s) {ε : S → ℝ} (D : ℝ) :
    (∀ (d : Strategy S) (w : (n : ℕ) → (Fin (n + 1) → S) → ℝ) (Mw : ℝ),
        (∀ n h, |w n h| ≤ Mw) → (∀ n h, w n h ≤ U.u (F D + ε (h (Fin.last n)))) →
        payoff Ω β d (fun _ => U.u (cbar3 Ω F r Dt ε)) (fun s => U.u (F 0 + ε s)) w ≤
          U.u (cbar3 Ω F r Dt ε) / (1 - β)) ↔
      ∀ s, U.u (F D + ε s) - U.u (cbar3 Ω F r Dt ε) ≤
        β / (1 - β) * (U.u (cbar3 Ω F r Dt ε) - Ω.expect (fun s => U.u (F 0 + ε s))) := by
  have h := trigger_iff Ω hβ0 hβ1 hpos (fun _ => U.u (cbar3 Ω F r Dt ε))
    (fun s => U.u (F D + ε s)) (fun s => U.u (F 0 + ε s))
  rw [Ω.expect_const] at h
  unfold cost at h
  rw [Ω.expect_const] at h
  exact h

/-- **The best enforceable commitment contract**, O&R Exercise 3(a): the temptation to default
rises with the loan (`F` is increasing), so some optimal commitment contract is enforceable by
exclusion iff the one with the smallest admissible loan `D_min = max(D̃, (E ε − ε_)/(1 + r))`
is. -/
theorem exists_enforceable_iff {F F' : ℝ → ℝ} {r Dt : ℝ} (hr : -1 < r)
    (hF : ∀ x, HasDerivAt F (F' x) x) (hlo : ∀ x, x < Dt → 1 + r < F' x)
    (hhi : ∀ x, Dt ≤ x → F' x = 1 + r) (hF0 : 0 ≤ F 0) (hDt : 0 ≤ Dt) {ε : S → ℝ}
    (hε : ∀ s, 0 < ε s) {slow : S} (hslow : ∀ s, ε slow ≤ ε s) (K : ℝ) :
    (∃ D, Dt ≤ D ∧ (∀ s, Ω.expect ε - ε s ≤ (1 + r) * D) ∧
        ∀ s, U.u (F D + ε s) - U.u (cbar3 Ω F r Dt ε) ≤ K) ↔
      ∀ s, U.u (F (max Dt ((Ω.expect ε - ε slow) / (1 + r))) + ε s) -
        U.u (cbar3 Ω F r Dt ε) ≤ K := by
  obtain ⟨_, _, hmono⟩ := production_facts hr hF hlo hhi
  have h1r : 0 < 1 + r := by linarith
  set Dmin := max Dt ((Ω.expect ε - ε slow) / (1 + r))
  constructor
  · rintro ⟨D, hD, hcol, hK⟩ s
    have hDmin : Dmin ≤ D := max_le hD (by rw [div_le_iff₀ h1r]; linarith [hcol slow])
    have hFpos : 0 < F Dmin + ε s := by
      have := hmono.monotone (show 0 ≤ Dmin from le_trans hDt (le_max_left _ _))
      linarith [hε s]
    have := U.mono hFpos (show F Dmin + ε s ≤ F D + ε s by linarith [hmono.monotone hDmin])
    linarith [hK s]
  · intro H
    refine ⟨Dmin, le_max_left _ _, fun s => ?_, H⟩
    have := le_max_right Dt ((Ω.expect ε - ε slow) / (1 + r))
    rw [div_le_iff₀ h1r] at this
    have := hslow s
    nlinarith

/-- **Exercise 3(b): self-financed investment beats the no-investment autarky**, O&R p. 427
with §6.2.2: if the defaulter can finance investment `D̃` out of its own income, its
steady-state autarky consumption `F(D̃) − D̃ + ε` exceeds `F(0) + ε` (for `r > 0`, `D̃ > 0`). -/
theorem selffin_autarky_improves {F F' : ℝ → ℝ} {r Dt : ℝ} (hr : 0 < r)
    (hF : ∀ x, HasDerivAt F (F' x) x) (hlo : ∀ x, x < Dt → 1 + r < F' x)
    (hhi : ∀ x, Dt ≤ x → F' x = 1 + r) (hDt : 0 < Dt) : F 0 < F Dt - Dt := by
  obtain ⟨h1, _, _⟩ := production_facts (by linarith : -1 < r) hF hlo hhi
  have := h1 0 hDt
  nlinarith

/-- **Exercise 3(b): self-financing weakens the punishment**, O&R p. 427: the cost of exclusion
when the defaulter can self-finance, `β/(1 − β)[u(C̄) − E u(F(D̃) − D̃ + ε)]`, is strictly
smaller than without self-financing, `β/(1 − β)[u(C̄) − E u(F(0) + ε)]`. -/
theorem selffin_cost_lt {F F' : ℝ → ℝ} {r Dt β : ℝ} (hr : 0 < r)
    (hF : ∀ x, HasDerivAt F (F' x) x) (hlo : ∀ x, x < Dt → 1 + r < F' x)
    (hhi : ∀ x, Dt ≤ x → F' x = 1 + r) (hDt : 0 < Dt) (hF0 : 0 ≤ F 0) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hpos : ∀ s, 0 < Ω.prob s) {ε : S → ℝ} (hε : ∀ s, 0 < ε s) (Cb : ℝ) :
    β / (1 - β) * (U.u Cb - Ω.expect (fun s => U.u (F Dt - Dt + ε s))) <
      β / (1 - β) * (U.u Cb - Ω.expect (fun s => U.u (F 0 + ε s))) := by
  have hgt := selffin_autarky_improves hr hF hlo hhi hDt
  have := StateSpaceFacts.nonempty Ω
  obtain ⟨s₀⟩ := this
  have hlt := expect_strictMono Ω (X := fun s => U.u (F 0 + ε s))
    (Y := fun s => U.u (F Dt - Dt + ε s))
    (fun s => U.mono (by linarith [hε s]) (by linarith)) (hpos s₀)
    (U.lt (by linarith [hε s₀]) (by linarith))
  exact mul_lt_mul_of_pos_left (by linarith) (div_pos hβ0 (by linarith))

/-- **Exercise 3(b): enforceability when the defaulter can self-finance**, O&R p. 427: the
commitment optimum with loan `D` survives every default strategy in which the defaulter keeps
its output, invests `D̃` itself and thereafter consumes `F(D̃) − D̃ + ε`, iff
`u(F(D) + ε − D̃) − u(C̄) ≤ β/(1 − β)[u(C̄) − E u(F(D̃) − D̃ + ε)]` in every state. -/
theorem selffin_enforceable_iff {F : ℝ → ℝ} {r Dt β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hpos : ∀ s, 0 < Ω.prob s) {ε : S → ℝ} (D : ℝ) :
    (∀ (d : Strategy S) (w : (n : ℕ) → (Fin (n + 1) → S) → ℝ) (Mw : ℝ),
        (∀ n h, |w n h| ≤ Mw) → (∀ n h, w n h ≤ U.u (F D + ε (h (Fin.last n)) - Dt)) →
        payoff Ω β d (fun _ => U.u (cbar3 Ω F r Dt ε)) (fun s => U.u (F Dt - Dt + ε s)) w ≤
          U.u (cbar3 Ω F r Dt ε) / (1 - β)) ↔
      ∀ s, U.u (F D + ε s - Dt) - U.u (cbar3 Ω F r Dt ε) ≤
        β / (1 - β) * (U.u (cbar3 Ω F r Dt ε) - Ω.expect (fun s => U.u (F Dt - Dt + ε s))) := by
  have h := trigger_iff Ω hβ0 hβ1 hpos (fun _ => U.u (cbar3 Ω F r Dt ε))
    (fun s => U.u (F D + ε s - Dt)) (fun s => U.u (F Dt - Dt + ε s))
  rw [Ω.expect_const] at h
  unfold cost at h
  rw [Ω.expect_const] at h
  exact h

/-- **Exercise 3(b): with self-financing, reputation may support no lending at all**, O&R p. 427
and §6.2.2: if self-financed autarky is at least as good on average as the commitment
consumption, `u(C̄) ≤ E u(F(D̃) − D̃ + ε)`, then no commitment contract (`D ≥ D̃`, `r > 0`,
`D̃ > 0`) satisfies the enforceability condition: the temptation in a state with `ε ≥ E ε` is
strictly positive while the cost of exclusion is not. -/
theorem selffin_unenforceable {F F' : ℝ → ℝ} {r Dt β : ℝ} (hr : 0 < r)
    (hF : ∀ x, HasDerivAt F (F' x) x) (hlo : ∀ x, x < Dt → 1 + r < F' x)
    (hhi : ∀ x, Dt ≤ x → F' x = 1 + r) (hDt : 0 < Dt) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {ε : S → ℝ} (hC : 0 < cbar3 Ω F r Dt ε) {D : ℝ} (hD : Dt ≤ D)
    (hmean : U.u (cbar3 Ω F r Dt ε) ≤ Ω.expect (fun s => U.u (F Dt - Dt + ε s))) :
    ¬ ∀ s, U.u (F D + ε s - Dt) - U.u (cbar3 Ω F r Dt ε) ≤
        β / (1 - β) * (U.u (cbar3 Ω F r Dt ε) - Ω.expect (fun s => U.u (F Dt - Dt + ε s))) := by
  intro H
  obtain ⟨_, h2, hmono⟩ := production_facts (by linarith : -1 < r) hF hlo hhi
  have := StateSpaceFacts.nonempty Ω
  obtain ⟨smax, _, hsmax⟩ := Finset.exists_max_image Finset.univ ε Finset.univ_nonempty
  have hmeanle : Ω.expect ε ≤ ε smax := by
    have := expect_mono Ω (X := ε) (Y := fun _ => ε smax) fun s => hsmax s (Finset.mem_univ s)
    rwa [Ω.expect_const] at this
  have hFD : F Dt ≤ F D := hmono.monotone hD
  have hgt : cbar3 Ω F r Dt ε < F D + ε smax - Dt := by
    unfold cbar3; nlinarith
  have hgain := U.lt hC hgt
  have hcost : β / (1 - β) * (U.u (cbar3 Ω F r Dt ε) -
      Ω.expect (fun s => U.u (F Dt - Dt + ε s))) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (div_nonneg hβ0 (by linarith)) (by linarith)
  have := H smax
  linarith

end ReputationInvestment

end ObstfeldRogoff.CapitalMarketImperfections.ReputationTrigger
