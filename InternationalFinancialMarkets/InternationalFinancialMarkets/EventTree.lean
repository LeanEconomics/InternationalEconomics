/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# Event trees, many-period Arrow–Debreu markets and dynamic consistency

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*,
Appendix 5C (pp. 341–343), Appendix 5D (pp. 343–344) and Supplement A to Chapter 5
(pp. 742–744).

**Histories.** One event from a finite set `S` is revealed at each date after date 1. The
date-1 history `h₁` is fixed; a date-`t` history (a continuation of `h₁` through date `t`)
is the list of the `n = t − 1` later events, `h : Fin n → S`. The one-step conditional
probability of event `s` after a history `g` of `k` events is `q k g s`; the conditional
probability `π(h_t | h_1)` is the product of the one-step probabilities along the history
(`histProb`), and `π(h_t | h_m)` is the product over the steps after date `m`
(`condProb`). We prove that the probabilities of all date-`t` histories sum to one and
Bayes' rule, O&R footnote 53.

**Appendix 5C, infinite horizon.** A plan `C : (n : ℕ) → (Fin n → S) → ℝ` assigns consumption
to every history of every date `t = n + 1` (date 1 is `n = 0`). Lifetime expected utility (82)
is the infinite sum `Σ_n β^n Σ_h π(h) u(C n h)` and the budget constraint (83) equates infinite
sums of date-1 values `Σ_n Σ_h P(h) x(h)`, with prices `P(h_t) = R_{1,t} p(h_t|h_1)` in date-1
output; a plan is admissible when these series converge (explicit `Summable` hypotheses). We
prove that the first-order conditions (84) with the budget give a global optimum when `u` is
concave (supporting-line inequality summed with `tsum`), and conversely that an interior optimum
with differentiable `u` satisfies (84) at every history (single-history perturbation); the
bond Euler equation (85) and the analogue of (9) follow. In the CRRA economy, under the primitive
condition that `Σ_t β^{t−1} E[(Y^W)^{−ρ} Y^n]` converges for every country, the prices, the
present-value shares `μ^n` and `C^n = μ^n Y^W` form an equilibrium (first-order conditions,
infinite budget, market clearing, optimality); conversely the first-order conditions and market
clearing force constant shares, and the infinite budget pins down `μ^n`. `R_{1,t}` is given in
closed form. The log case `ρ = 1` is covered too, with the one extra primitive condition that
`Σ_t β^{t−1} E log Y^W` converges (and `β < 1`). Finite-horizon versions of the optimality and
budget results are kept as lemmas.

**Appendix 5D.** Prices in date-1 units `p̃ = p R`; from (86) the date-1 plan satisfies
(88), which by Bayes' rule and the no-arbitrage identity `p̃(h_t|h_1)/p̃(h_2|h_1) = p̃(h_t|h_2)`
(taken as a hypothesis, as in the book's arbitrage argument, which is about the trading
technology rather than a consequence of the model's primitives) is (87). Over the infinite
horizon the continuation of the date-1 plan after any date-2 event with positive probability is
admissible (when its utility series converges absolutely) and optimal for the date-2 problem
with reopened markets (dynamic consistency).

**Supplement A.** (The infinite-horizon consumption–portfolio problem with its Bellman
equation and verification theorem is in `ConsumptionPortfolio`.) Log utility gives the
consumption share `μ = 1 − β`; the CRRA share
recursion `μ_t = (1 + [βE{(1+r°)^{1−ρ} μ_{t+1}^{−ρ}}]^{1/ρ})^{−1}` is equivalent to the
consumption Euler equation, and its i.i.d. fixed point is `μ = 1 − [βE(1+r°)^{1−ρ}]^{1/ρ}`.
-/

namespace ObstfeldRogoff.InternationalFinancialMarkets.EventTree

open Finset

/-- An event tree (O&R Appendix 5C, p. 341): after a history of `k` events `g : Fin k → S`,
the next event is `s` with conditional probability `q k g s`. -/
structure Tree (S : Type) [Fintype S] where
  q : (k : ℕ) → (Fin k → S) → S → ℝ
  q_nonneg : ∀ k g s, 0 ≤ q k g s
  q_sum : ∀ k g, ∑ s, q k g s = 1

variable {S : Type} [Fintype S]

/-- The restriction of a history `h` of `n` events to its first `k ≤ n` events, i.e. the
history through the earlier date `k + 1` (O&R Appendix 5C, p. 341). -/
def restr {n : ℕ} (h : Fin n → S) (k : ℕ) (hk : k ≤ n) : Fin k → S :=
  fun j => h ⟨j, lt_of_lt_of_le j.2 hk⟩

namespace Tree

variable (tr : Tree S)

/-- The one-step conditional probability `π(h_{i+2} | h_{i+1})` of the `i`-th event of the
history `h` given the events before it (O&R Appendix 5C, p. 341); `1` beyond the history. -/
noncomputable def step {n : ℕ} (h : Fin n → S) (i : ℕ) : ℝ :=
  if hi : i < n then tr.q i (restr h i hi.le) (h ⟨i, hi⟩) else 1

/-- The conditional probability `π(h_{n+1} | h_{m+1})` of the history `h` (of `n` events)
given its first `m` events: the product of the one-step probabilities after step `m`
(O&R Appendix 5C, p. 341, and footnote 53, p. 344). -/
noncomputable def condProb {n : ℕ} (h : Fin n → S) (m : ℕ) : ℝ :=
  ∏ i ∈ Ico m n, tr.step h i

/-- The probability `π(h_t | h_1)` of the date-`t` history `h`, `t = n + 1`
(O&R Appendix 5C, p. 341). -/
noncomputable def histProb {n : ℕ} (h : Fin n → S) : ℝ :=
  tr.condProb h 0

/-- One-step probabilities are nonnegative (O&R Appendix 5C, p. 341). -/
theorem step_nonneg {n : ℕ} (h : Fin n → S) (i : ℕ) : 0 ≤ tr.step h i := by
  unfold step
  split_ifs
  · exact tr.q_nonneg _ _ _
  · exact zero_le_one

/-- History probabilities are nonnegative (O&R Appendix 5C, p. 341). -/
theorem histProb_nonneg {n : ℕ} (h : Fin n → S) : 0 ≤ tr.histProb h :=
  by unfold histProb condProb; exact Finset.prod_nonneg fun i _ => tr.step_nonneg h i

/-- Appending an event does not change the earlier one-step probabilities. -/
theorem step_snoc_lt {n : ℕ} (h : Fin n → S) (s : S) {i : ℕ} (hi : i < n) :
    tr.step (Fin.snoc h s : Fin (n + 1) → S) i = tr.step h i := by
  have hi' : i < n + 1 := by omega
  simp only [step, hi, hi', dite_true]
  have h1 : (Fin.snoc h s : Fin (n + 1) → S) ⟨i, hi'⟩ = h ⟨i, hi⟩ := by
    simp [Fin.snoc, hi]
  have h2 : restr (Fin.snoc h s : Fin (n + 1) → S) i hi'.le = restr h i hi.le := by
    funext j
    have hj : (j : ℕ) < n := by omega
    simp [restr, Fin.snoc, hj]
  rw [h1, h2]

/-- The last one-step probability of `snoc h s` is `q n h s`. -/
theorem step_snoc_last {n : ℕ} (h : Fin n → S) (s : S) :
    tr.step (Fin.snoc h s : Fin (n + 1) → S) n = tr.q n h s := by
  have hn : n < n + 1 := by omega
  simp only [step, hn, dite_true]
  have h1 : (Fin.snoc h s : Fin (n + 1) → S) ⟨n, hn⟩ = s := by
    simp [Fin.snoc]
  have h2 : restr (Fin.snoc h s : Fin (n + 1) → S) n hn.le = h := by
    funext j
    have hj : (j : ℕ) < n := j.2
    simp [restr, Fin.snoc, hj]
  rw [h1, h2]

/-- The probabilities of all date-`t` histories sum to one, `Σ_{h_t} π(h_t | h_1) = 1`
(O&R Appendix 5C, p. 341; used for (85), p. 342). -/
theorem histProb_sum_eq_one (n : ℕ) : ∑ h : Fin n → S, tr.histProb h = 1 := by
  induction n with
  | zero => simp [histProb, condProb]
  | succ n ih =>
    rw [← (Fin.snocEquiv (fun _ : Fin (n + 1) => S)).sum_comp]
    rw [Fintype.sum_prod_type]
    rw [Finset.sum_comm]
    have key : ∀ (g : Fin n → S) (s : S),
        tr.histProb (Fin.snoc g s : Fin (n + 1) → S) = tr.histProb g * tr.q n g s := by
      intro g s
      simp only [histProb, condProb, Nat.Ico_zero_eq_range]
      rw [Finset.prod_range_succ, tr.step_snoc_last]
      congr 1
      exact Finset.prod_congr rfl fun i hi => tr.step_snoc_lt g s (Finset.mem_range.mp hi)
    have e : ∀ (g : Fin n → S) (s : S),
        (Fin.snocEquiv fun _ : Fin (n + 1) => S) (s, g) = Fin.snoc g s := fun _ _ => rfl
    simp only [e, key, ← Finset.mul_sum, tr.q_sum, mul_one]
    exact ih

/-- Restricting a history to an earlier date leaves the earlier one-step probabilities
unchanged (O&R Appendix 5C, p. 341). -/
theorem step_restr {n k : ℕ} (h : Fin n → S) (hk : k ≤ n) {i : ℕ} (hi : i < k) :
    tr.step (restr h k hk) i = tr.step h i := by
  have hin : i < n := lt_of_lt_of_le hi hk
  simp only [step, hi, hin, dite_true]
  rfl

/-- The chain rule for conditional probabilities along a history,
`π(h_n | h_m) = π(h_k | h_m) π(h_n | h_k)` for `m ≤ k ≤ n` (O&R footnote 53, p. 344). -/
theorem condProb_chain {n : ℕ} (h : Fin n → S) {m k : ℕ} (hmk : m ≤ k) (hk : k ≤ n) :
    tr.condProb h m = tr.condProb (restr h k hk) m * tr.condProb h k := by
  have e : tr.condProb (restr h k hk) m = ∏ i ∈ Ico m k, tr.step h i :=
    Finset.prod_congr rfl fun i hi => tr.step_restr h hk (Finset.mem_Ico.mp hi).2
  rw [e]
  exact (Finset.prod_Ico_consecutive _ hmk hk).symm

/-- Bayes' rule, O&R footnote 53, p. 344: for a history `h` continuing `h_{t+1}` (its first
`t + 1` events), `π(h | h_{t+1}) = π(h | h_t)/π(h_{t+1} | h_t)` whenever
`π(h_{t+1} | h_t) ≠ 0`. -/
theorem bayes_rule {n : ℕ} (h : Fin n → S) {t : ℕ} (ht : t + 1 ≤ n)
    (hpos : tr.condProb (restr h (t + 1) ht) t ≠ 0) :
    tr.condProb h (t + 1) = tr.condProb h t / tr.condProb (restr h (t + 1) ht) t := by
  rw [eq_div_iff hpos, tr.condProb_chain h (Nat.le_succ t) ht, mul_comm]

/-- The date-2 form of Bayes' rule used in Appendix 5D, O&R p. 344:
`π(h_t | h_1)/π(h_2 | h_1) = π(h_t | h_2)`, where `h_2` is the first event of `h_t`. -/
theorem histProb_div_date2 {n : ℕ} (h : Fin n → S) (hn : 1 ≤ n)
    (hpos : tr.histProb (restr h 1 hn) ≠ 0) :
    tr.histProb h / tr.histProb (restr h 1 hn) = tr.condProb h 1 := by
  rw [div_eq_iff hpos, histProb, histProb, tr.condProb_chain h (Nat.zero_le 1) hn, mul_comm]

/-- The date-2 probability `π(h_2 | h_1)` of the first event of `h` is its first one-step
probability (O&R Appendix 5D, p. 344). -/
theorem histProb_restr_one {n : ℕ} (h : Fin n → S) (hn : 1 ≤ n) :
    tr.histProb (restr h 1 hn) = tr.step h 0 := by
  have e : tr.histProb (restr h 1 hn) = tr.step (restr h 1 hn) 0 := by
    simp [histProb, condProb]
  rw [e, tr.step_restr h hn Nat.zero_lt_one]

/-- Conditional probabilities are nonnegative (O&R Appendix 5C, p. 341). -/
theorem condProb_nonneg {n : ℕ} (h : Fin n → S) (m : ℕ) : 0 ≤ tr.condProb h m :=
  Finset.prod_nonneg fun i _ => tr.step_nonneg h i

/-- The probability of a history extended by one event, `π(h_{t+1}|h_1) = π(h_t|h_1) q(s|h_t)`
where `h_{t+1} = {s} ∪ h_t` (O&R Appendix 5C, p. 341). -/
theorem histProb_snoc {n : ℕ} (h : Fin n → S) (s : S) :
    tr.histProb (Fin.snoc h s : Fin (n + 1) → S) = tr.histProb h * tr.q n h s := by
  simp only [histProb, condProb, Nat.Ico_zero_eq_range]
  rw [Finset.prod_range_succ, tr.step_snoc_last]
  congr 1
  exact Finset.prod_congr rfl fun i hi => tr.step_snoc_lt h s (Finset.mem_range.mp hi)

/-- The date-1 history has probability one, `π(h_1|h_1) = 1` (O&R Appendix 5C, p. 341). -/
theorem histProb_zero (h : Fin 0 → S) : tr.histProb h = 1 := by
  simp [histProb, condProb]

/-- The probability of the date-2 history `{s}` is the first one-step probability
`π(h_2|h_1) = q(s|h_1)` (O&R Appendix 5D, p. 344). -/
theorem histProb_one (s : S) : tr.histProb (fun _ : Fin 1 => s) = tr.q 0 Fin.elim0 s := by
  have e : restr (fun _ : Fin 1 => s) 0 (Nat.zero_le 1) = Fin.elim0 := Subsingleton.elim _ _
  simp [histProb, condProb, step, e]

/-- A date-`t` history's probability factors through its date-2 event,
`π(h_t|h_1) = π(h_2|h_1) π(h_t|h_2)` (O&R Appendix 5D, p. 344, and footnote 53). -/
theorem histProb_eq_first_mul_condProb {m : ℕ} (h : Fin (m + 1) → S) :
    tr.histProb h = tr.q 0 Fin.elim0 (h 0) * tr.condProb h 1 := by
  have e : restr h 0 (Nat.zero_le _) = Fin.elim0 := Subsingleton.elim _ _
  have h1 : tr.histProb (restr h 1 (by omega)) = tr.q 0 Fin.elim0 (h 0) := by
    rw [tr.histProb_restr_one h (by omega)]
    simp only [step, Nat.zero_lt_succ, dite_true, e]
    rfl
  rw [histProb, tr.condProb_chain h (Nat.zero_le 1) (by omega), ← histProb, h1]

end Tree

/-! ## Appendix 5C: individual optimality -/

/-- The supporting-line (tangent) inequality for log utility,
`log y ≤ log x + (1/x)(y − x)` for `x, y > 0`: log is concave (used for O&R Appendix 5C and
Supplement A). -/
theorem log_tangent {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Real.log y ≤ Real.log x + 1 / x * (y - x) := by
  have h := Real.log_le_sub_one_of_pos (div_pos hy hx)
  rw [Real.log_div hy.ne' hx.ne'] at h
  have e : y / x - 1 = 1 / x * (y - x) := by field_simp
  linarith

/-- Sufficiency of the first-order conditions under concavity (O&R Appendix 5C, p. 342, and
Appendix 5D, p. 344). Consider nodes `h ∈ A n` for `n ∈ N`, with nonnegative utility weights
`w` and prices `q` of contingent consumption in units of current consumption. If `u` lies
below its tangent lines with slope `du` (concavity), `du(c₀) ≥ 0`, the plan `(c₀, c)`
satisfies the first-order conditions `q(h) u′(c₀) = w(h) u′(c(h))`, and the plan
`(c₀′, c′)` costs no more, then `(c₀′, c′)` gives no more utility. -/
theorem foc_plan_optimal {H : ℕ → Type} (N : Finset ℕ) (A : (n : ℕ) → Finset (H n))
    (u du : ℝ → ℝ) (htan : ∀ x y, 0 < x → 0 < y → u y ≤ u x + du x * (y - x))
    (w q : (n : ℕ) → H n → ℝ) (hw : ∀ n ∈ N, ∀ h ∈ A n, 0 ≤ w n h)
    {c₀ c₀' : ℝ} {c c' : (n : ℕ) → H n → ℝ} (hc₀ : 0 < c₀) (hc₀' : 0 < c₀')
    (hc : ∀ n ∈ N, ∀ h ∈ A n, 0 < c n h) (hc' : ∀ n ∈ N, ∀ h ∈ A n, 0 < c' n h)
    (hdu : 0 ≤ du c₀)
    (hfoc : ∀ n ∈ N, ∀ h ∈ A n, q n h * du c₀ = w n h * du (c n h))
    (hbud : c₀' + ∑ n ∈ N, ∑ h ∈ A n, q n h * c' n h
      ≤ c₀ + ∑ n ∈ N, ∑ h ∈ A n, q n h * c n h) :
    u c₀' + ∑ n ∈ N, ∑ h ∈ A n, w n h * u (c' n h)
      ≤ u c₀ + ∑ n ∈ N, ∑ h ∈ A n, w n h * u (c n h) := by
  have key : ∀ n ∈ N, ∀ h ∈ A n, w n h * u (c' n h)
      ≤ w n h * u (c n h) + du c₀ * (q n h * c' n h - q n h * c n h) := by
    intro n hn h hh
    have t := htan _ _ (hc n hn h hh) (hc' n hn h hh)
    have t2 := mul_le_mul_of_nonneg_left t (hw n hn h hh)
    have e : du c₀ * (q n h * c' n h - q n h * c n h)
        = w n h * du (c n h) * (c' n h - c n h) := by
      rw [← hfoc n hn h hh]; ring
    rw [e]; nlinarith
  have hsum : ∑ n ∈ N, ∑ h ∈ A n, w n h * u (c' n h)
      ≤ ∑ n ∈ N, ∑ h ∈ A n, w n h * u (c n h)
        + du c₀ * (∑ n ∈ N, ∑ h ∈ A n, q n h * c' n h
          - ∑ n ∈ N, ∑ h ∈ A n, q n h * c n h) := by
    rw [mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun n hn => ?_
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun h hh => ?_
    have := key n hn h hh
    linarith
  have t0 := htan _ _ hc₀ hc₀'
  have hgap : du c₀ * (c₀' - c₀ + (∑ n ∈ N, ∑ h ∈ A n, q n h * c' n h
      - ∑ n ∈ N, ∑ h ∈ A n, q n h * c n h)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hdu (by linarith)
  nlinarith

/-- Finite-horizon lemma (the infinite-horizon statement is `arrowDebreu_optimal_infinite`).
The many-period Arrow–Debreu problem, O&R (82)–(84), pp. 341–342, over a finite horizon
`T` (dates `t = n + 1 ≤ T`): if the plan `(C₁, C)` satisfies the first-order conditions (84)
`R_{1,t} p(h_t|h_1) u′(C₁) = π(h_t|h_1) β^{t−1} u′(C(h_t))` and `u` is concave with
`u′(C₁) ≥ 0`, then every positive plan satisfying the budget constraint (83) (at no greater
cost) gives no more expected utility (82). -/
theorem arrowDebreu_plan_optimal (tr : Tree S) (T : ℕ) (u du : ℝ → ℝ)
    (htan : ∀ x y, 0 < x → 0 < y → u y ≤ u x + du x * (y - x)) {β : ℝ} (hβ : 0 ≤ β)
    (R : ℕ → ℝ) (p : (n : ℕ) → (Fin n → S) → ℝ)
    {C₁ C₁' : ℝ} {C C' : (n : ℕ) → (Fin n → S) → ℝ} (hC₁ : 0 < C₁) (hC₁' : 0 < C₁')
    (hC : ∀ n h, 0 < C n h) (hC' : ∀ n h, 0 < C' n h) (hdu : 0 ≤ du C₁)
    (hfoc : ∀ n ∈ Ico 1 T, ∀ h, R n * p n h * du C₁ = tr.histProb h * β ^ n * du (C n h))
    (hbud : C₁' + ∑ n ∈ Ico 1 T, R n * ∑ h, p n h * C' n h
      ≤ C₁ + ∑ n ∈ Ico 1 T, R n * ∑ h, p n h * C n h) :
    u C₁' + ∑ n ∈ Ico 1 T, β ^ n * ∑ h, tr.histProb h * u (C' n h)
      ≤ u C₁ + ∑ n ∈ Ico 1 T, β ^ n * ∑ h, tr.histProb h * u (C n h) := by
  simp only [Finset.mul_sum, ← mul_assoc] at hbud ⊢
  exact foc_plan_optimal (Ico 1 T) (fun _ => Finset.univ) u du htan
    (fun n h => β ^ n * tr.histProb h) (fun n h => R n * p n h)
    (fun n _ h _ => mul_nonneg (pow_nonneg hβ n) (tr.histProb_nonneg h)) hC₁ hC₁'
    (fun n _ h _ => hC n h) (fun n _ h _ => hC' n h) hdu
    (fun n hn h _ => by rw [hfoc n hn h]; ring) hbud

/-- The noncontingent-bond Euler equation, O&R (85), p. 342: summing the first-order
conditions (84) over date-`t` histories and using `Σ_{h_t} p(h_t|h_1) = 1` gives
`u′(C₁) = (β^{t−1}/R_{1,t}) Σ_{h_t} π(h_t|h_1) u′(C(h_t))`. -/
theorem euler_bond (tr : Tree S) (du : ℝ → ℝ) (β : ℝ) (n : ℕ) {R C₁ : ℝ}
    {p C : (Fin n → S) → ℝ} (hR : R ≠ 0) (hp : ∑ h, p h = 1)
    (hfoc : ∀ h, R * p h * du C₁ = tr.histProb h * β ^ n * du (C h)) :
    du C₁ = β ^ n / R * ∑ h, tr.histProb h * du (C h) := by
  have hs : ∑ h, R * p h * du C₁ = ∑ h, tr.histProb h * β ^ n * du (C h) :=
    Finset.sum_congr rfl fun h _ => hfoc h
  rw [← Finset.sum_mul, ← Finset.mul_sum, hp] at hs
  have e : ∑ h, tr.histProb h * β ^ n * du (C h) = β ^ n * ∑ h, tr.histProb h * du (C h) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun h _ => by ring
  rw [e] at hs
  field_simp
  linarith

/-- The analogue of O&R (9) in Appendix 5C, p. 342: for two date-`t` histories,
`π(h¹)u′(C(h¹))/(π(h²)u′(C(h²))) = p(h¹|h_1)/p(h²|h_1)`, from the first-order conditions (84)
(given `R_{1,t}, u′(C₁), β, p(h²|h_1) ≠ 0`). -/
theorem foc_ratio (tr : Tree S) (du : ℝ → ℝ) (n : ℕ) {β R C₁ : ℝ}
    {p C : (Fin n → S) → ℝ} (hR : R ≠ 0) (hduC : du C₁ ≠ 0) (hβ : β ≠ 0)
    (hfoc : ∀ h, R * p h * du C₁ = tr.histProb h * β ^ n * du (C h))
    (h₁ h₂ : Fin n → S) (hp₂ : p h₂ ≠ 0) :
    tr.histProb h₁ * du (C h₁) / (tr.histProb h₂ * du (C h₂)) = p h₁ / p h₂ := by
  have hb : β ^ n ≠ 0 := pow_ne_zero n hβ
  have e : ∀ h, tr.histProb h * du (C h) = R * p h * du C₁ / β ^ n := by
    intro h
    rw [eq_div_iff hb]
    linarith [hfoc h]
  rw [e h₁, e h₂]
  field_simp

/-! ## Appendix 5C.3: the CRRA equilibrium -/

/-- The normalising sum `Σ_{h_t} π(h_t|h_1) Y^W(h_t)^{−ρ}` (O&R Appendix 5C.3, p. 342). -/
noncomputable def crraMass (tr : Tree S) (ρ : ℝ) (n : ℕ) (Y : (Fin n → S) → ℝ) : ℝ :=
  ∑ h, tr.histProb h * Y h ^ (-ρ)

/-- The equilibrium long-term interest factor, O&R Appendix 5C.3, p. 342:
`R_{1,t} = β^{t−1} Σ_{h_t} π(h_t|h_1) Y^W(h_t)^{−ρ} / (Y^W_1)^{−ρ}`. -/
noncomputable def crraR (tr : Tree S) (β ρ Y₁ : ℝ) (n : ℕ) (Y : (Fin n → S) → ℝ) : ℝ :=
  β ^ n * crraMass tr ρ n Y / Y₁ ^ (-ρ)

/-- The equilibrium history-contingent prices (left as an exercise in O&R Appendix 5C.3,
p. 342): `p(h_t|h_1) = π(h_t|h_1) Y^W(h_t)^{−ρ} / Σ_{h'} π(h'|h_1) Y^W(h')^{−ρ}`. -/
noncomputable def crraPrice (tr : Tree S) (ρ : ℝ) (n : ℕ) (Y : (Fin n → S) → ℝ)
    (h : Fin n → S) : ℝ :=
  tr.histProb h * Y h ^ (-ρ) / crraMass tr ρ n Y

/-- The normalising sum is positive when world output is positive (O&R Appendix 5C.3). -/
theorem crraMass_pos (tr : Tree S) (ρ : ℝ) (n : ℕ) {Y : (Fin n → S) → ℝ}
    (hY : ∀ h, 0 < Y h) : 0 < crraMass tr ρ n Y := by
  have hlt : ∑ _h : Fin n → S, (0 : ℝ) < ∑ h : Fin n → S, tr.histProb h := by
    rw [tr.histProb_sum_eq_one]; simp
  obtain ⟨h₀, -, hh₀⟩ := Finset.exists_lt_of_sum_lt hlt
  exact Finset.sum_pos' (fun h _ => mul_nonneg (tr.histProb_nonneg h)
    (Real.rpow_nonneg (hY h).le _)) ⟨h₀, Finset.mem_univ _,
      mul_pos hh₀ (Real.rpow_pos_of_pos (hY h₀) _)⟩

/-- The CRRA equilibrium prices of date-`t` Arrow–Debreu securities sum to one, the
no-arbitrage condition `Σ_{h_t} p(h_t|h_1) = 1` of O&R Appendix 5C, p. 342. -/
theorem crraPrice_sum (tr : Tree S) (ρ : ℝ) (n : ℕ) {Y : (Fin n → S) → ℝ}
    (hY : ∀ h, 0 < Y h) : ∑ h, crraPrice tr ρ n Y h = 1 := by
  simp only [crraPrice, ← Finset.sum_div]
  exact div_self (crraMass_pos tr ρ n hY).ne'

/-- The CRRA equilibrium of O&R Appendix 5C.3, p. 342: at the prices `crraR`, `crraPrice`
the constant-share plan `C₁ = μY^W_1`, `C(h_t) = μY^W(h_t)` satisfies the first-order
conditions (84) with `u′(C) = C^{−ρ}`, for every country share `μ > 0`. -/
theorem crra_foc (tr : Tree S) (β ρ : ℝ) (n : ℕ) {μ Y₁ : ℝ} {Y : (Fin n → S) → ℝ}
    (hμ : 0 < μ) (hY₁ : 0 < Y₁) (hY : ∀ h, 0 < Y h) (h : Fin n → S) :
    crraR tr β ρ Y₁ n Y * crraPrice tr ρ n Y h * (μ * Y₁) ^ (-ρ)
      = tr.histProb h * β ^ n * (μ * Y h) ^ (-ρ) := by
  have hD := (crraMass_pos tr ρ n hY).ne'
  have hY₁' : Y₁ ^ (-ρ) ≠ 0 := (Real.rpow_pos_of_pos hY₁ _).ne'
  simp only [crraR, crraPrice]
  rw [Real.mul_rpow hμ.le hY₁.le, Real.mul_rpow hμ.le (hY h).le]
  field_simp

/-- Finite-horizon present value (the infinite-horizon one is `dateOneValue`): the value at
date 1 of a history-contingent stream `x` through date `T`, in date-1 output (O&R (83), p. 341):
`x₁ + Σ_t R_{1,t} Σ_{h_t} p(h_t|h_1) x(h_t)`. -/
noncomputable def presentValue (T : ℕ) (R : ℕ → ℝ) (p : (n : ℕ) → (Fin n → S) → ℝ)
    (x₁ : ℝ) (x : (n : ℕ) → (Fin n → S) → ℝ) : ℝ :=
  x₁ + ∑ n ∈ Ico 1 T, R n * ∑ h, p n h * x n h

/-- Finite-horizon lemma (the infinite-horizon statement is part of
`crra_equilibrium_infinite`). The budget constraint (83) at the constant-share plan, O&R
Appendix 5C.3, p. 342: at any prices, if `μ` is country `n`'s share of the date-1 present
value of world output, the plan
`C = μY^W` exactly exhausts country `n`'s present value of endowments. -/
theorem budget_of_share (T : ℕ) (R : ℕ → ℝ) (p : (n : ℕ) → (Fin n → S) → ℝ)
    {Yw₁ Yi₁ : ℝ} {Yw Yi : (n : ℕ) → (Fin n → S) → ℝ}
    (hW : presentValue T R p Yw₁ Yw ≠ 0) :
    presentValue T R p (presentValue T R p Yi₁ Yi / presentValue T R p Yw₁ Yw * Yw₁)
        (fun n h => presentValue T R p Yi₁ Yi / presentValue T R p Yw₁ Yw * Yw n h)
      = presentValue T R p Yi₁ Yi := by
  set μ := presentValue T R p Yi₁ Yi / presentValue T R p Yw₁ Yw with hμ
  have lin : presentValue T R p (μ * Yw₁) (fun n h => μ * Yw n h)
      = μ * presentValue T R p Yw₁ Yw := by
    simp only [presentValue, mul_add, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun n _ => Finset.sum_congr rfl fun h _ => by ring
  rw [lin, hμ, div_mul_cancel₀ _ hW]

/-- Constant consumption shares from the first-order conditions, O&R Appendix 5C.3, p. 342:
if Home and Foreign both satisfy (84) with CRRA marginal utility `C^{−ρ}` (`ρ ≠ 0`) at
common prices, and world markets clear at date 1 and at `h_t`, then
`C(h_t) = μ Y^W(h_t)` with `μ = C₁/Y^W_1` (requires `π(h_t|h_1) > 0`, `β > 0`). -/
theorem crra_constant_share (tr : Tree S) {β ρ : ℝ} (hβ : 0 < β) (hρ : ρ ≠ 0) (n : ℕ)
    {R P C₁ C₁' Y₁ : ℝ} {h : Fin n → S} {Ch Ch' Yh : ℝ}
    (hπ : 0 < tr.histProb h) (hC₁ : 0 < C₁) (hC₁' : 0 < C₁') (hCh : 0 < Ch) (hCh' : 0 < Ch')
    (hfoc : R * P * C₁ ^ (-ρ) = tr.histProb h * β ^ n * Ch ^ (-ρ))
    (hfoc' : R * P * C₁' ^ (-ρ) = tr.histProb h * β ^ n * Ch' ^ (-ρ))
    (hclear₁ : C₁ + C₁' = Y₁) (hclear : Ch + Ch' = Yh) :
    Ch = C₁ / Y₁ * Yh := by
  have hk : 0 < tr.histProb h * β ^ n := mul_pos hπ (pow_pos hβ n)
  have r1 : (Ch / C₁) ^ (-ρ) = R * P / (tr.histProb h * β ^ n) := by
    rw [Real.div_rpow hCh.le hC₁.le, eq_div_iff hk.ne',
      div_mul_eq_mul_div, div_eq_iff (Real.rpow_pos_of_pos hC₁ _).ne']
    linarith
  have r2 : (Ch' / C₁') ^ (-ρ) = R * P / (tr.histProb h * β ^ n) := by
    rw [Real.div_rpow hCh'.le hC₁'.le, eq_div_iff hk.ne',
      div_mul_eq_mul_div, div_eq_iff (Real.rpow_pos_of_pos hC₁' _).ne']
    linarith
  have hg : Ch / C₁ = Ch' / C₁' :=
    (Real.rpow_left_inj (div_pos hCh hC₁).le (div_pos hCh' hC₁').le (neg_ne_zero.mpr hρ)).mp
      (r1.trans r2.symm)
  rw [← hclear₁, ← hclear]
  field_simp at hg ⊢
  nlinarith

/-- The equilibrium long-term interest factor, O&R Appendix 5C.3, p. 342: if the bond Euler
equation (85) holds with CRRA marginal utility at the constant-share allocation `C = μY^W`,
then `R_{1,t} = β^{t−1} Σ π(h_t|h_1) Y^W(h_t)^{−ρ}/(Y^W_1)^{−ρ}`. -/
theorem crra_interest_factor (tr : Tree S) (β ρ : ℝ) (n : ℕ) {R μ Y₁ : ℝ}
    {Y : (Fin n → S) → ℝ} (hR : R ≠ 0) (hμ : 0 < μ) (hY₁ : 0 < Y₁) (hY : ∀ h, 0 < Y h)
    (heuler : (μ * Y₁) ^ (-ρ) = β ^ n / R * ∑ h, tr.histProb h * (μ * Y h) ^ (-ρ)) :
    R = crraR tr β ρ Y₁ n Y := by
  have hm : 0 < μ ^ (-ρ) := Real.rpow_pos_of_pos hμ _
  have hY₁' : 0 < Y₁ ^ (-ρ) := Real.rpow_pos_of_pos hY₁ _
  have e : ∑ h, tr.histProb h * (μ * Y h) ^ (-ρ) = μ ^ (-ρ) * crraMass tr ρ n Y := by
    rw [crraMass, Finset.mul_sum]
    exact Finset.sum_congr rfl fun h _ => by rw [Real.mul_rpow hμ.le (hY h).le]; ring
  rw [e, Real.mul_rpow hμ.le hY₁.le] at heuler
  unfold crraR
  field_simp at heuler ⊢
  nlinarith

/-! ## Appendix 5D: ongoing trade and dynamic consistency -/

/-- O&R (88), p. 344: if the date-1 plan satisfies the first-order conditions (84)/(86) in
date-1 prices `p̃ = pR` at a date-`t` history `h` (`t = m + 2`) and at its date-2 history
`h_2`, then `[p̃(h_t|h_1)/p̃(h_2|h_1)] u′(C(h_2)) = [π(h_t|h_1)/π(h_2|h_1)] β^{t−2} u′(C(h_t))`
(given positive marginal utilities, `β > 0`, `π(h_2|h_1) > 0`). -/
theorem foc_date2_ratio (tr : Tree S) (du : ℝ → ℝ) {β : ℝ} (hβ : 0 < β) {m : ℕ}
    (h : Fin (m + 1) → S) {P₁ Pt C₁ C₂ Ct : ℝ}
    (hπ₂ : 0 < tr.histProb (restr h 1 (by omega))) (hdu₁ : 0 < du C₁) (hdu₂ : 0 < du C₂)
    (hfoc₂ : P₁ * du C₁ = tr.histProb (restr h 1 (by omega)) * β ^ 1 * du C₂)
    (hfoct : Pt * du C₁ = tr.histProb h * β ^ (m + 1) * du Ct) :
    Pt / P₁ * du C₂ = tr.histProb h / tr.histProb (restr h 1 (by omega)) * β ^ m * du Ct := by
  have hP₁ : P₁ = tr.histProb (restr h 1 (by omega)) * β * du C₂ / du C₁ := by
    rw [eq_div_iff hdu₁.ne']; linarith [hfoc₂, pow_one β]
  have hPt : Pt = tr.histProb h * β ^ (m + 1) * du Ct / du C₁ := by
    rw [eq_div_iff hdu₁.ne']; linarith
  rw [hP₁, hPt, pow_succ]
  field_simp

/-- O&R (87), p. 344: with Bayes' rule and the no-arbitrage identity
`p̃(h_t|h_1)/p̃(h_2|h_1) = p̃(h_t|h_2)` (a hypothesis here, the book's arbitrage argument),
equation (88) becomes the date-2 first-order condition
`p̃(h_t|h_2) u′(C(h_2)) = π(h_t|h_2) β^{t−2} u′(C(h_t))`. -/
theorem foc_date2 (tr : Tree S) (du : ℝ → ℝ) {β : ℝ} (hβ : 0 < β) {m : ℕ}
    (h : Fin (m + 1) → S) {P₁ Pt P₂ C₁ C₂ Ct : ℝ}
    (hπ₂ : 0 < tr.histProb (restr h 1 (by omega))) (hdu₁ : 0 < du C₁) (hdu₂ : 0 < du C₂)
    (hfoc₂ : P₁ * du C₁ = tr.histProb (restr h 1 (by omega)) * β ^ 1 * du C₂)
    (hfoct : Pt * du C₁ = tr.histProb h * β ^ (m + 1) * du Ct)
    (harb : Pt / P₁ = P₂) :
    P₂ * du C₂ = tr.condProb h 1 * β ^ m * du Ct := by
  rw [← harb, foc_date2_ratio tr du hβ h hπ₂ hdu₁ hdu₂ hfoc₂ hfoct,
    tr.histProb_div_date2 h (by omega) hπ₂.ne']

/-- Finite-horizon lemma (the infinite-horizon statement is `dynamic_consistency_infinite`).
Dynamic consistency, O&R Appendix 5D, pp. 343–344. Suppose the date-1 plan `(C₁, C)`
satisfies the first-order conditions (84) at date-1 prices `R_{1,t} p(h_t|h_1)` for all dates
`t = n + 1 ≤ T`, and date-2 prices `P₂` (of date-`t` claims, `t = m + 2`, in date-2 output)
obey the no-arbitrage identity `p̃(h_t|h_1)/p̃(h_2|h_1) = p̃(h_t|h_2)`. When the date-2 event is
`s₂` (with `π(h_2|h_1) > 0`) and markets reopen, any positive plan `(c₂′, c′)` affordable
from the contracted positions (the date-2 budget constraint on p. 344) gives no more
date-2 expected utility than the original plan: with concave `u`, the date-1 plan remains
optimal on date 2. -/
theorem dynamic_consistency [DecidableEq S] (tr : Tree S) (T : ℕ) (u du : ℝ → ℝ)
    (htan : ∀ x y, 0 < x → 0 < y → u y ≤ u x + du x * (y - x))
    (hdu : ∀ x, 0 < x → 0 < du x) {β : ℝ} (hβ : 0 < β) (R : ℕ → ℝ)
    (p : (n : ℕ) → (Fin n → S) → ℝ) (P₂ : (m : ℕ) → (Fin (m + 1) → S) → ℝ)
    {C₁ : ℝ} {C : (n : ℕ) → (Fin n → S) → ℝ} (hC₁ : 0 < C₁) (hC : ∀ n h, 0 < C n h)
    (s₂ : S) (hπ₂ : 0 < tr.histProb (fun _ : Fin 1 => s₂))
    (hfoc : ∀ n, 1 ≤ n → n < T → ∀ h,
      R n * p n h * du C₁ = tr.histProb h * β ^ n * du (C n h))
    (harb : ∀ m ∈ Ico 1 (T - 1), ∀ h : Fin (m + 1) → S, h 0 = s₂ →
      R (m + 1) * p (m + 1) h / (R 1 * p 1 (fun _ => s₂)) = P₂ m h)
    {c₂' : ℝ} {c' : (m : ℕ) → (Fin (m + 1) → S) → ℝ} (hc₂' : 0 < c₂')
    (hc' : ∀ m h, 0 < c' m h)
    (hbud : c₂' + ∑ m ∈ Ico 1 (T - 1), ∑ h ∈ univ.filter (fun h : Fin (m + 1) → S => h 0 = s₂),
        P₂ m h * c' m h
      ≤ C 1 (fun _ => s₂) + ∑ m ∈ Ico 1 (T - 1),
        ∑ h ∈ univ.filter (fun h : Fin (m + 1) → S => h 0 = s₂), P₂ m h * C (m + 1) h) :
    u c₂' + ∑ m ∈ Ico 1 (T - 1), ∑ h ∈ univ.filter (fun h : Fin (m + 1) → S => h 0 = s₂),
        β ^ m * tr.condProb h 1 * u (c' m h)
      ≤ u (C 1 (fun _ => s₂)) + ∑ m ∈ Ico 1 (T - 1),
        ∑ h ∈ univ.filter (fun h : Fin (m + 1) → S => h 0 = s₂),
          β ^ m * tr.condProb h 1 * u (C (m + 1) h) := by
  refine foc_plan_optimal (Ico 1 (T - 1))
    (fun m => univ.filter (fun h : Fin (m + 1) → S => h 0 = s₂)) u du htan
    (fun m h => β ^ m * tr.condProb h 1) P₂
    (fun m _ h _ => mul_nonneg (pow_nonneg hβ.le m) (tr.condProb_nonneg h 1))
    (hC 1 _) hc₂' (fun m _ h _ => hC (m + 1) h) (fun m _ h _ => hc' m h)
    (hdu _ (hC 1 _)).le ?_ hbud
  intro m hm h hh
  have hh0 : h 0 = s₂ := (Finset.mem_filter.mp hh).2
  have hmT := Finset.mem_Ico.mp hm
  have hg : restr h 1 (by omega) = fun _ : Fin 1 => s₂ := by
    funext j
    rw [Fin.fin_one_eq_zero j, ← hh0]
    rfl
  have hπ : 0 < tr.histProb (restr h 1 (by omega)) := by rw [hg]; exact hπ₂
  have hf₂ : R 1 * p 1 (fun _ => s₂) * du C₁
      = tr.histProb (restr h 1 (by omega)) * β ^ 1 * du (C 1 (fun _ => s₂)) := by
    rw [hg]; exact hfoc 1 le_rfl (by omega) _
  have key := foc_date2 tr du hβ h hπ (hdu _ hC₁) (hdu _ (hC 1 _)) hf₂
    (hfoc (m + 1) (by omega) (by omega) h) (harb m hm h hh0)
  rw [key]; ring

/-! ## Appendix 5C with the book's infinite horizon

A plan is `C : (n : ℕ) → (Fin n → S) → ℝ` over all dates `t = n + 1`, date 1 being `n = 0`
(the unique empty history). Prices `P n h` are in date-1 output, `P(h_t) = R_{1,t} p(h_t|h_1)`
(the book's `p̃` of Appendix 5D), with `P(h_1) = 1`. -/

/-- A sum over date-`(t+1)` histories is a sum over date-`t` histories and the next event
(O&R Appendix 5C, p. 341: `h_{t+1} = {s_{t+1}} ∪ h_t`). -/
theorem sum_snoc {n : ℕ} (f : (Fin (n + 1) → S) → ℝ) :
    ∑ g, f g = ∑ h : Fin n → S, ∑ s, f (Fin.snoc h s) := by
  rw [← (Fin.snocEquiv (fun _ : Fin (n + 1) => S)).sum_comp, Fintype.sum_prod_type,
    Finset.sum_comm]
  rfl

/-- CRRA utility `u(C) = C^{1−ρ}/(1−ρ)`, O&R Appendix 5C.3, p. 342 (and Supplement A). -/
noncomputable def crraUtil (ρ C : ℝ) : ℝ := C ^ (1 - ρ) / (1 - ρ)

/-- The supporting-line inequality for CRRA utility (concavity), used for O&R Appendix 5C.3
and Supplement A: for `ρ > 0`, `ρ ≠ 1`, `x, y > 0`,
`y^{1−ρ}/(1−ρ) ≤ x^{1−ρ}/(1−ρ) + x^{−ρ}(y − x)`. -/
theorem crra_tangent {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≠ 1) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    crraUtil ρ y ≤ crraUtil ρ x + x ^ (-ρ) * (y - x) := by
  unfold crraUtil
  set t := y / x with ht_def
  have ht : 0 < t := div_pos hy hx
  have hyx : y = x * t := by rw [ht_def]; field_simp
  have hy' : y ^ (1 - ρ) = x ^ (1 - ρ) * t ^ (1 - ρ) := by rw [hyx, Real.mul_rpow hx.le ht.le]
  have hxr : x ^ (-ρ) * (y - x) = x ^ (1 - ρ) * (t - 1) := by
    rw [show (1 : ℝ) - ρ = -ρ + 1 by ring, Real.rpow_add hx, Real.rpow_one, hyx]; ring
  have hxp : 0 < x ^ (1 - ρ) := Real.rpow_pos_of_pos hx _
  rw [hy', hxr]
  have key : t ^ (1 - ρ) / (1 - ρ) ≤ 1 / (1 - ρ) + (t - 1) := by
    rcases lt_or_gt_of_ne hρ1 with h | h
    · have hp : 0 < 1 - ρ := by linarith
      have b := rpow_one_add_le_one_add_mul_self (s := t - 1) (by linarith) hp.le
        (by linarith)
      rw [show 1 + (t - 1) = t by ring] at b
      have e : t ^ (1 - ρ) / (1 - ρ) - (1 / (1 - ρ) + (t - 1))
          = (t ^ (1 - ρ) - (1 + (1 - ρ) * (t - 1))) / (1 - ρ) := by field_simp
      have : (t ^ (1 - ρ) - (1 + (1 - ρ) * (t - 1))) / (1 - ρ) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (by linarith) hp.le
      linarith
    · have hp : 1 - ρ < 0 := by linarith
      have e1 : 1 + (1 - ρ) * Real.log t ≤ t ^ (1 - ρ) := by
        rw [Real.rpow_def_of_pos ht]
        have := Real.add_one_le_exp (Real.log t * (1 - ρ))
        linarith [mul_comm (Real.log t) (1 - ρ)]
      have e2 : Real.log t ≤ t - 1 := Real.log_le_sub_one_of_pos ht
      have e3 : (1 - ρ) * (t - 1) ≤ (1 - ρ) * Real.log t := mul_le_mul_of_nonpos_left e2 hp.le
      have e : t ^ (1 - ρ) / (1 - ρ) - (1 / (1 - ρ) + (t - 1))
          = (t ^ (1 - ρ) - (1 + (1 - ρ) * (t - 1))) / (1 - ρ) := by field_simp
      have : (t ^ (1 - ρ) - (1 + (1 - ρ) * (t - 1))) / (1 - ρ) ≤ 0 :=
        div_nonpos_of_nonneg_of_nonpos (by linarith) hp.le
      linarith
  calc x ^ (1 - ρ) * t ^ (1 - ρ) / (1 - ρ) = x ^ (1 - ρ) * (t ^ (1 - ρ) / (1 - ρ)) := by ring
    _ ≤ x ^ (1 - ρ) * (1 / (1 - ρ) + (t - 1)) := mul_le_mul_of_nonneg_left key hxp.le
    _ = x ^ (1 - ρ) / (1 - ρ) + x ^ (1 - ρ) * (t - 1) := by ring

/-- The date-`t` term of lifetime expected utility (82), O&R p. 341 (`t = n + 1`):
`β^{t−1} Σ_{h_t} π(h_t|h_1) u(C(h_t))`; the date-1 term (`n = 0`) is `u(C₁)`. -/
noncomputable def utilSeries (tr : Tree S) (β : ℝ) (u : ℝ → ℝ)
    (C : (n : ℕ) → (Fin n → S) → ℝ) (n : ℕ) : ℝ :=
  β ^ n * ∑ h, tr.histProb h * u (C n h)

/-- Lifetime expected utility (82), O&R p. 341, over the infinite horizon:
`U₁ = u(C₁) + Σ_{t≥2} β^{t−1} Σ_{h_t} π(h_t|h_1) u(C(h_t))`. It is meaningful for plans whose
series `utilSeries` is summable (admissible plans); results always assume that explicitly. -/
noncomputable def expectedUtility (tr : Tree S) (β : ℝ) (u : ℝ → ℝ)
    (C : (n : ℕ) → (Fin n → S) → ℝ) : ℝ :=
  ∑' n, utilSeries tr β u C n

/-- The date-`t` term `Σ_{h_t} P(h_t) x(h_t)` of the date-1 value of a contingent stream `x`
at date-1 prices `P(h_t) = R_{1,t} p(h_t|h_1)` (O&R (83), p. 341). -/
noncomputable def valueSeries (P x : (n : ℕ) → (Fin n → S) → ℝ) (n : ℕ) : ℝ :=
  ∑ h, P n h * x n h

/-- The date-1 value of a contingent stream `x`, the two sides of the budget constraint (83),
O&R p. 341: `Σ_{t≥1} Σ_{h_t} P(h_t) x(h_t)` (meaningful when `valueSeries` is summable). -/
noncomputable def dateOneValue (P x : (n : ℕ) → (Fin n → S) → ℝ) : ℝ :=
  ∑' n, valueSeries P x n

/-- Lifetime expected utility in the book's form (82), O&R p. 341:
`U₁ = u(C₁) + Σ_{t=2}^∞ β^{t−1} Σ_{h_t} π(h_t|h_1) u(C(h_t))`, for an admissible plan. -/
theorem expectedUtility_eq_book (tr : Tree S) (β : ℝ) (u : ℝ → ℝ)
    (C : (n : ℕ) → (Fin n → S) → ℝ) (hU : Summable (utilSeries tr β u C)) :
    expectedUtility tr β u C = u (C 0 Fin.elim0)
      + ∑' n, β ^ (n + 1) * ∑ h : Fin (n + 1) → S, tr.histProb h * u (C (n + 1) h) := by
  rw [expectedUtility, hU.tsum_eq_zero_add]
  congr 1
  rw [utilSeries, Fintype.sum_unique, tr.histProb_zero, Subsingleton.elim default Fin.elim0]
  ring

/-- The budget constraint's value in the book's form (83), O&R p. 341: with `P(h_1) = 1` and
`P(h_t) = R_{1,t} p(h_t|h_1)`, the date-1 value of `x` is
`x₁ + Σ_{t=2}^∞ R_{1,t} Σ_{h_t} p(h_t|h_1) x(h_t)`. -/
theorem dateOneValue_eq_book (R : ℕ → ℝ) (p P x : (n : ℕ) → (Fin n → S) → ℝ)
    (hP0 : P 0 Fin.elim0 = 1) (hP : ∀ n h, P (n + 1) h = R (n + 1) * p (n + 1) h)
    (hV : Summable (valueSeries P x)) :
    dateOneValue P x = x 0 Fin.elim0 + ∑' n, R (n + 1) * ∑ h, p (n + 1) h * x (n + 1) h := by
  rw [dateOneValue, hV.tsum_eq_zero_add]
  congr 1
  · rw [valueSeries, Fintype.sum_unique, Subsingleton.elim default Fin.elim0, hP0, one_mul]
  · refine tsum_congr fun n => ?_
    rw [valueSeries, Finset.mul_sum]
    exact Finset.sum_congr rfl fun h _ => by rw [hP]; ring

/-- Sufficiency of the first-order conditions over an infinite horizon (O&R Appendix 5C,
pp. 341–342, and Appendix 5D, p. 344): the supporting-line inequality summed with `tsum`.
Dates `n : ℕ` carry finitely many nodes `h ∈ A n` with utility weights `w ≥ 0` and prices `q`.
If `u` lies below its tangent lines of slope `du`, the plan `c` satisfies
`q(h) λ = w(h) u′(c(h))` with multiplier `λ ≥ 0`, both plans have convergent utility and value
series, and `c′` costs no more than `c`, then `c′` gives no more utility. -/
theorem foc_plan_optimal_tsum {H : ℕ → Type} (A : (n : ℕ) → Finset (H n)) (u du : ℝ → ℝ)
    (htan : ∀ x y, 0 < x → 0 < y → u y ≤ u x + du x * (y - x))
    (w q : (n : ℕ) → H n → ℝ) (hw : ∀ n, ∀ h ∈ A n, 0 ≤ w n h) {lam : ℝ} (hlam : 0 ≤ lam)
    {c c' : (n : ℕ) → H n → ℝ} (hc : ∀ n, ∀ h ∈ A n, 0 < c n h)
    (hc' : ∀ n, ∀ h ∈ A n, 0 < c' n h)
    (hfoc : ∀ n, ∀ h ∈ A n, q n h * lam = w n h * du (c n h))
    (hU : Summable fun n => ∑ h ∈ A n, w n h * u (c n h))
    (hU' : Summable fun n => ∑ h ∈ A n, w n h * u (c' n h))
    (hV : Summable fun n => ∑ h ∈ A n, q n h * c n h)
    (hV' : Summable fun n => ∑ h ∈ A n, q n h * c' n h)
    (hbud : ∑' n, ∑ h ∈ A n, q n h * c' n h ≤ ∑' n, ∑ h ∈ A n, q n h * c n h) :
    ∑' n, ∑ h ∈ A n, w n h * u (c' n h) ≤ ∑' n, ∑ h ∈ A n, w n h * u (c n h) := by
  have key : ∀ n, ∑ h ∈ A n, w n h * u (c' n h) ≤ ∑ h ∈ A n, w n h * u (c n h)
      + lam * (∑ h ∈ A n, q n h * c' n h - ∑ h ∈ A n, q n h * c n h) := by
    intro n
    rw [mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun h hh => ?_
    have t := htan _ _ (hc n h hh) (hc' n h hh)
    have t2 := mul_le_mul_of_nonneg_left t (hw n h hh)
    have e : lam * (q n h * c' n h) - lam * (q n h * c n h)
        = w n h * du (c n h) * (c' n h - c n h) := by
      rw [show lam * (q n h * c' n h) - lam * (q n h * c n h)
        = q n h * lam * (c' n h - c n h) by ring, hfoc n h hh]
    rw [e]; nlinarith
  have hR := hU.add ((hV'.sub hV).mul_left lam)
  have h1 := Summable.tsum_le_tsum key hU' hR
  rw [Summable.tsum_add hU ((hV'.sub hV).mul_left lam), Summable.tsum_mul_left lam (hV'.sub hV),
    Summable.tsum_sub hV' hV] at h1
  have hgap : lam * (∑' n, ∑ h ∈ A n, q n h * c' n h - ∑' n, ∑ h ∈ A n, q n h * c n h) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hlam (by linarith)
  linarith

/-- O&R (82)–(84), pp. 341–342, over the book's infinite horizon: if the plan `C` satisfies the
first-order conditions (84), `R_{1,t} p(h_t|h_1) u′(C₁) = π(h_t|h_1) β^{t−1} u′(C(h_t))` (in
date-1 prices `P = R p`, at every date including date 1), exhausts the budget (83), and `u` is
concave with `u′(C₁) ≥ 0`, then every positive admissible plan `C′` (convergent utility and
budget series) satisfying the budget constraint (83) gives no more lifetime expected utility. -/
theorem arrowDebreu_optimal_infinite (tr : Tree S) (u du : ℝ → ℝ)
    (htan : ∀ x y, 0 < x → 0 < y → u y ≤ u x + du x * (y - x)) {β : ℝ} (hβ : 0 ≤ β)
    (P Y : (n : ℕ) → (Fin n → S) → ℝ) {C C' : (n : ℕ) → (Fin n → S) → ℝ}
    (hC : ∀ n h, 0 < C n h) (hC' : ∀ n h, 0 < C' n h) (hdu : 0 ≤ du (C 0 Fin.elim0))
    (hfoc : ∀ n h, P n h * du (C 0 Fin.elim0) = tr.histProb h * β ^ n * du (C n h))
    (hU : Summable (utilSeries tr β u C)) (hU' : Summable (utilSeries tr β u C'))
    (hV : Summable (valueSeries P C)) (hV' : Summable (valueSeries P C'))
    (hbud : dateOneValue P C = dateOneValue P Y) (hbud' : dateOneValue P C' ≤ dateOneValue P Y) :
    expectedUtility tr β u C' ≤ expectedUtility tr β u C := by
  have e : ∀ D : (n : ℕ) → (Fin n → S) → ℝ, utilSeries tr β u D
      = fun n => ∑ h ∈ univ, β ^ n * tr.histProb h * u (D n h) := by
    intro D; funext n
    rw [utilSeries, Finset.mul_sum]
    exact Finset.sum_congr rfl fun h _ => by ring
  unfold expectedUtility
  rw [e C] at hU; rw [e C'] at hU'; rw [e C, e C']
  unfold dateOneValue valueSeries at hbud hbud'
  unfold valueSeries at hV hV'
  exact foc_plan_optimal_tsum (fun _ => univ) u du htan (fun n h => β ^ n * tr.histProb h) P
    (fun n h _ => mul_nonneg (pow_nonneg hβ n) (tr.histProb_nonneg h)) hdu
    (fun n h _ => hC n h) (fun n h _ => hC' n h)
    (fun n h _ => by rw [hfoc n h]; ring) hU hU' hV hV' (by rw [← hbud] at hbud'; exact hbud')

/-- The noncontingent-bond Euler equation (85), O&R p. 342, from the plan's first-order
conditions (84) in date-1 prices: with `R_{1,t} = Σ_{h_t} P(h_t)` (the date-1 price of a sure
unit on date `t`, since `Σ p(h_t|h_1) = 1`), `u′(C₁) = (β^{t−1}/R_{1,t}) E₁ u′(C(h_t))`. -/
theorem euler_bond_plan (tr : Tree S) (du : ℝ → ℝ) (β : ℝ)
    (P C : (n : ℕ) → (Fin n → S) → ℝ)
    (hfoc : ∀ n h, P n h * du (C 0 Fin.elim0) = tr.histProb h * β ^ n * du (C n h))
    (n : ℕ) (hR : ∑ h, P n h ≠ 0) :
    du (C 0 Fin.elim0) = β ^ n / (∑ h, P n h) * ∑ h, tr.histProb h * du (C n h) := by
  have hs : ∑ h, P n h * du (C 0 Fin.elim0) = ∑ h, tr.histProb h * β ^ n * du (C n h) :=
    Finset.sum_congr rfl fun h _ => hfoc n h
  rw [← Finset.sum_mul] at hs
  have e : ∑ h, tr.histProb h * β ^ n * du (C n h) = β ^ n * ∑ h, tr.histProb h * du (C n h) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun h _ => by ring
  rw [e] at hs
  field_simp
  linarith

/-- One unit of consumption at the single date-`(n+1)` history `h` and nothing elsewhere: the
direction of the single-history perturbation behind the necessity of (84), O&R p. 342. -/
noncomputable def histBump [DecidableEq S] (n : ℕ) (h : Fin n → S) :
    (m : ℕ) → (Fin m → S) → ℝ :=
  fun m g => if (⟨m, g⟩ : (k : ℕ) × (Fin k → S)) = ⟨n, h⟩ then 1 else 0

omit [Fintype S] in
/-- The bump at `h` evaluated at a history `g` of the same date (O&R p. 342). -/
theorem histBump_self [DecidableEq S] {n : ℕ} (h g : Fin n → S) :
    histBump n h n g = if g = h then 1 else 0 := by
  simp [histBump]

omit [Fintype S] in
/-- The bump at a date-`(n+1)` history vanishes at every other date (O&R p. 342). -/
theorem histBump_ne [DecidableEq S] {n m : ℕ} (h : Fin n → S) (g : Fin m → S) (hm : m ≠ n) :
    histBump n h m g = 0 := by
  simp [histBump, hm]

/-- The single-history perturbation of a plan (O&R Appendix 5C, p. 342): `ε` more consumption at
the date-`(n+1)` history `h`, paid for by `ε P(h)` less date-1 consumption. -/
noncomputable def perturbPlan [DecidableEq S] (C P : (n : ℕ) → (Fin n → S) → ℝ) (n : ℕ)
    (h : Fin n → S) (ε : ℝ) : (m : ℕ) → (Fin m → S) → ℝ :=
  fun m g => C m g + ε * histBump n h m g - ε * P n h * histBump 0 Fin.elim0 m g

/-- The utility series of the perturbed plan differs from the original in two terms only
(O&R Appendix 5C, p. 342). -/
theorem utilSeries_perturbPlan [DecidableEq S] (tr : Tree S) (β : ℝ) (u : ℝ → ℝ)
    (C P : (n : ℕ) → (Fin n → S) → ℝ) {n : ℕ} (hn : n ≠ 0) (h : Fin n → S) (ε : ℝ) (m : ℕ) :
    utilSeries tr β u (perturbPlan C P n h ε) m = utilSeries tr β u C m
      + (if m = n then β ^ n * (tr.histProb h * (u (C n h + ε) - u (C n h))) else 0)
      + (if m = 0 then u (C 0 Fin.elim0 - ε * P n h) - u (C 0 Fin.elim0) else 0) := by
  by_cases hm0 : m = 0
  · subst hm0
    have hn' : (0 : ℕ) ≠ n := fun e => hn e.symm
    have hb : histBump 0 (Fin.elim0 : Fin 0 → S) 0 Fin.elim0 = 1 := by
      rw [histBump_self]; simp
    simp only [utilSeries, perturbPlan, Fintype.sum_unique, hn', ↓reduceIte,
      histBump_ne h _ hn', hb, tr.histProb_zero, Subsingleton.elim (default : Fin 0 → S) Fin.elim0]
    ring_nf
  · by_cases hmn : m = n
    · subst hmn
      have hs : ∑ g, tr.histProb g * u (C m g + ε * histBump m h m g
            - ε * P m h * histBump 0 Fin.elim0 m g) - ∑ g, tr.histProb g * u (C m g)
          = tr.histProb h * (u (C m h + ε) - u (C m h)) := by
        rw [← Finset.sum_sub_distrib, Finset.sum_eq_single h]
        · simp [histBump_self, histBump_ne _ _ hm0]; ring
        · intro g _ hg
          simp [histBump_self, histBump_ne _ _ hm0, hg]
        · intro hh; exact absurd (Finset.mem_univ h) hh
      simp only [utilSeries, perturbPlan, hm0, ↓reduceIte]
      linear_combination β ^ m * hs
    · simp [utilSeries, perturbPlan, histBump_ne _ _ hmn, histBump_ne _ _ hm0, hmn, hm0]

/-- The date-1 value series of the perturbed plan: `ε P(h)` more at date `n + 1`, `ε P(h)` less at
date 1, when `P(h_1) = 1` (O&R Appendix 5C, p. 342). -/
theorem valueSeries_perturbPlan [DecidableEq S] (C P : (n : ℕ) → (Fin n → S) → ℝ)
    (hP0 : P 0 Fin.elim0 = 1) {n : ℕ} (hn : n ≠ 0) (h : Fin n → S) (ε : ℝ) (m : ℕ) :
    valueSeries P (perturbPlan C P n h ε) m = valueSeries P C m
      + (if m = n then P n h * ε else 0) + (if m = 0 then -(ε * P n h) else 0) := by
  by_cases hm0 : m = 0
  · subst hm0
    have hn' : (0 : ℕ) ≠ n := fun e => hn e.symm
    have hb : histBump 0 (Fin.elim0 : Fin 0 → S) 0 Fin.elim0 = 1 := by
      rw [histBump_self]; simp
    simp only [valueSeries, perturbPlan, Fintype.sum_unique, hn', ↓reduceIte,
      histBump_ne h _ hn', hb, Subsingleton.elim (default : Fin 0 → S) Fin.elim0, hP0]
    ring
  · by_cases hmn : m = n
    · subst hmn
      have hs : ∑ g, P m g * (C m g + ε * histBump m h m g
            - ε * P m h * histBump 0 Fin.elim0 m g) - ∑ g, P m g * C m g = P m h * ε := by
        rw [← Finset.sum_sub_distrib, Finset.sum_eq_single h]
        · simp [histBump_self, histBump_ne _ _ hm0]; ring
        · intro g _ hg
          simp [histBump_self, histBump_ne _ _ hm0, hg]
        · intro hh; exact absurd (Finset.mem_univ h) hh
      simp only [valueSeries, perturbPlan, hm0, ↓reduceIte]
      linear_combination hs
    · simp [valueSeries, perturbPlan, histBump_ne _ _ hmn, histBump_ne _ _ hm0, hmn, hm0]

/-- Necessity of the first-order conditions (84), O&R p. 342, over the infinite horizon. Let
prices be in date-1 output with `P(h_1) = 1`, let `u` be differentiable on `(0, ∞)` with
derivative `du`, and let the positive admissible plan `C` be optimal: it satisfies the budget
(83) and no positive admissible plan satisfying (83) gives more expected utility (82). Then at
every history `R_{1,t} p(h_t|h_1) u′(C₁) = π(h_t|h_1) β^{t−1} u′(C(h_t))`. The proof perturbs
consumption at the single history `h_t` against date-1 consumption, which keeps the plan
admissible (only two terms of each series change) and within the budget. -/
theorem arrowDebreu_foc_necessary (tr : Tree S) (u du : ℝ → ℝ)
    (hu : ∀ x, 0 < x → HasDerivAt u (du x) x) (β : ℝ) (P Y : (n : ℕ) → (Fin n → S) → ℝ)
    (hP0 : P 0 Fin.elim0 = 1) {C : (n : ℕ) → (Fin n → S) → ℝ} (hC : ∀ n h, 0 < C n h)
    (hU : Summable (utilSeries tr β u C)) (hV : Summable (valueSeries P C))
    (hbud : dateOneValue P C ≤ dateOneValue P Y)
    (hopt : ∀ C' : (n : ℕ) → (Fin n → S) → ℝ, (∀ n h, 0 < C' n h) →
      Summable (utilSeries tr β u C') → Summable (valueSeries P C') →
      dateOneValue P C' ≤ dateOneValue P Y → expectedUtility tr β u C' ≤ expectedUtility tr β u C)
    (n : ℕ) (h : Fin n → S) :
    P n h * du (C 0 Fin.elim0) = tr.histProb h * β ^ n * du (C n h) := by
  classical
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    rw [Subsingleton.elim h Fin.elim0, hP0, tr.histProb_zero]; ring
  have hn0 : n ≠ 0 := hn.ne'
  have hsa : ∀ ε : ℝ, Summable (fun m : ℕ =>
      if m = n then β ^ n * (tr.histProb h * (u (C n h + ε) - u (C n h))) else 0) :=
    fun ε => (hasSum_ite_eq n _).summable
  have hsb : ∀ ε : ℝ, Summable (fun m : ℕ =>
      if m = 0 then u (C 0 Fin.elim0 - ε * P n h) - u (C 0 Fin.elim0) else 0) :=
    fun ε => (hasSum_ite_eq 0 _).summable
  have hUe : ∀ ε, utilSeries tr β u (perturbPlan C P n h ε) = fun m => utilSeries tr β u C m
      + (if m = n then β ^ n * (tr.histProb h * (u (C n h + ε) - u (C n h))) else 0)
      + (if m = 0 then u (C 0 Fin.elim0 - ε * P n h) - u (C 0 Fin.elim0) else 0) :=
    fun ε => funext (utilSeries_perturbPlan tr β u C P hn0 h ε)
  have hSU : ∀ ε, Summable (utilSeries tr β u (perturbPlan C P n h ε)) := by
    intro ε; rw [hUe]; exact (hU.add (hsa ε)).add (hsb ε)
  have hEU : ∀ ε, expectedUtility tr β u (perturbPlan C P n h ε) = expectedUtility tr β u C
      + β ^ n * (tr.histProb h * (u (C n h + ε) - u (C n h)))
      + (u (C 0 Fin.elim0 - ε * P n h) - u (C 0 Fin.elim0)) := by
    intro ε; unfold expectedUtility
    rw [hUe, Summable.tsum_add (hU.add (hsa ε)) (hsb ε), Summable.tsum_add hU (hsa ε),
      tsum_ite_eq, tsum_ite_eq]
  have hsc : ∀ ε : ℝ, Summable (fun m : ℕ => if m = n then P n h * ε else 0) :=
    fun ε => (hasSum_ite_eq n _).summable
  have hsd : ∀ ε : ℝ, Summable (fun m : ℕ => if m = 0 then -(ε * P n h) else 0) :=
    fun ε => (hasSum_ite_eq 0 _).summable
  have hVe : ∀ ε, valueSeries P (perturbPlan C P n h ε) = fun m => valueSeries P C m
      + (if m = n then P n h * ε else 0) + (if m = 0 then -(ε * P n h) else 0) :=
    fun ε => funext (valueSeries_perturbPlan C P hP0 hn0 h ε)
  have hSV : ∀ ε, Summable (valueSeries P (perturbPlan C P n h ε)) := by
    intro ε; rw [hVe]; exact (hV.add (hsc ε)).add (hsd ε)
  have hDV : ∀ ε, dateOneValue P (perturbPlan C P n h ε) = dateOneValue P C := by
    intro ε; unfold dateOneValue
    rw [hVe, Summable.tsum_add (hV.add (hsc ε)) (hsd ε), Summable.tsum_add hV (hsc ε),
      tsum_ite_eq, tsum_ite_eq]
    ring
  have hpos : ∀ᶠ ε in nhds (0 : ℝ), 0 < C 0 Fin.elim0 - ε * P n h ∧ 0 < C n h + ε := by
    have c1 : ContinuousAt (fun ε : ℝ => C 0 Fin.elim0 - ε * P n h) 0 := by fun_prop
    have c2 : ContinuousAt (fun ε : ℝ => C n h + ε) 0 := by fun_prop
    exact (c1.eventually (lt_mem_nhds (by simpa using hC 0 Fin.elim0))).and
      (c2.eventually (lt_mem_nhds (by simpa using hC n h)))
  have hmax : IsLocalMax (fun ε => expectedUtility tr β u C
      + β ^ n * (tr.histProb h * (u (C n h + ε) - u (C n h)))
      + (u (C 0 Fin.elim0 - ε * P n h) - u (C 0 Fin.elim0))) 0 := by
    filter_upwards [hpos] with ε hε
    simp only [add_zero, zero_mul, sub_zero, sub_self, mul_zero]
    rw [← hEU ε]
    refine hopt _ ?_ (hSU ε) (hSV ε) (by rw [hDV]; exact hbud)
    intro m g
    by_cases hm0 : m = 0
    · subst hm0
      have hn' : (0 : ℕ) ≠ n := fun e => hn0 e.symm
      obtain rfl : g = Fin.elim0 := Subsingleton.elim _ _
      have hb : histBump 0 (Fin.elim0 : Fin 0 → S) 0 Fin.elim0 = 1 := by
        rw [histBump_self]; simp
      simp only [perturbPlan, histBump_ne h _ hn', hb]
      linarith [hε.1]
    · by_cases hmn : m = n
      · subst hmn
        simp only [perturbPlan, histBump_self, histBump_ne _ _ hm0]
        by_cases hg : g = h
        · subst hg; simp only [↓reduceIte]; linarith [hε.2]
        · simp only [hg, ↓reduceIte]; linarith [hC m g]
      · simp only [perturbPlan, histBump_ne _ _ hmn, histBump_ne _ _ hm0]
        linarith [hC m g]
  have hda : HasDerivAt (fun ε => β ^ n * (tr.histProb h * (u (C n h + ε) - u (C n h))))
      (β ^ n * (tr.histProb h * (du (C n h) * 1))) 0 := by
    have h1 : HasDerivAt (fun ε : ℝ => C n h + ε) 1 0 :=
      HasDerivAt.const_add (C n h) (hasDerivAt_id (0 : ℝ))
    have h2 := HasDerivAt.comp_of_eq 0 (hu _ (hC n h)) h1 (by simp)
    exact HasDerivAt.const_mul (β ^ n)
      (HasDerivAt.const_mul (tr.histProb h) (HasDerivAt.sub_const (u (C n h)) h2))
  have hdb : HasDerivAt (fun ε => u (C 0 Fin.elim0 - ε * P n h) - u (C 0 Fin.elim0))
      (du (C 0 Fin.elim0) * (-P n h)) 0 := by
    have h1 : HasDerivAt (fun ε : ℝ => C 0 Fin.elim0 - ε * P n h) (-P n h) 0 := by
      simpa using HasDerivAt.const_sub (C 0 Fin.elim0)
        (HasDerivAt.mul_const (hasDerivAt_id (0 : ℝ)) (P n h))
    exact HasDerivAt.sub_const _ (HasDerivAt.comp_of_eq 0 (hu _ (hC 0 Fin.elim0)) h1 (by simp))
  have hd := HasDerivAt.add (HasDerivAt.add (hasDerivAt_const (0 : ℝ) (expectedUtility tr β u C))
    hda) hdb
  have h0 := hmax.hasDerivAt_eq_zero hd
  linarith

/-! ### Appendix 5C.3: the CRRA equilibrium of the infinite economy -/

/-- World output `Y^W(h_t) = Σ_n Y^n(h_t)`, summed over countries (O&R Appendix 5C.3, p. 342). -/
noncomputable def worldOutput {ι : Type} [Fintype ι] (Y : ι → (n : ℕ) → (Fin n → S) → ℝ) :
    (n : ℕ) → (Fin n → S) → ℝ :=
  fun n h => ∑ i, Y i n h

/-- CRRA equilibrium prices in date-1 output, O&R Appendix 5C.3, p. 342 (left as an exercise
there): `R_{1,t} p(h_t|h_1) = β^{t−1} π(h_t|h_1) Y^W(h_t)^{−ρ}/(Y^W_1)^{−ρ}`. -/
noncomputable def crraDatePrice (tr : Tree S) (β ρ : ℝ) (Yw : (n : ℕ) → (Fin n → S) → ℝ) :
    (n : ℕ) → (Fin n → S) → ℝ :=
  fun n h => β ^ n * tr.histProb h * Yw n h ^ (-ρ) / Yw 0 Fin.elim0 ^ (-ρ)

/-- Date-1 output is the numeraire at the CRRA prices, `P(h_1) = 1` (O&R Appendix 5C.3). -/
theorem crraDatePrice_zero (tr : Tree S) (β ρ : ℝ) (Yw : (n : ℕ) → (Fin n → S) → ℝ)
    (hY : 0 < Yw 0 Fin.elim0) : crraDatePrice tr β ρ Yw 0 Fin.elim0 = 1 := by
  have := (Real.rpow_pos_of_pos hY (-ρ)).ne'
  simp [crraDatePrice, tr.histProb_zero, this]

/-- The CRRA date-1 prices factor as `R_{1,t} p(h_t|h_1)` with the book's long-term interest
factor `R_{1,t}` (`crraR`) and history prices `p(h_t|h_1)` (`crraPrice`), O&R Appendix 5C.3,
p. 342. -/
theorem crraDatePrice_eq (tr : Tree S) (β ρ : ℝ) (Yw : (n : ℕ) → (Fin n → S) → ℝ)
    (hY : ∀ n h, 0 < Yw n h) (n : ℕ) (h : Fin n → S) :
    crraDatePrice tr β ρ Yw n h
      = crraR tr β ρ (Yw 0 Fin.elim0) n (Yw n) * crraPrice tr ρ n (Yw n) h := by
  have hD := (crraMass_pos tr ρ n (hY n)).ne'
  simp only [crraDatePrice, crraR, crraPrice]
  field_simp

/-- The long-term interest factor in closed form, O&R Appendix 5C.3, p. 342: the date-1 price of
a sure unit on date `t` at the CRRA prices is
`R_{1,t} = β^{t−1} Σ_{h_t} π(h_t|h_1) Y^W(h_t)^{−ρ}/(Y^W_1)^{−ρ}`. -/
theorem crraDatePrice_sum (tr : Tree S) (β ρ : ℝ) (Yw : (n : ℕ) → (Fin n → S) → ℝ) (n : ℕ) :
    ∑ h, crraDatePrice tr β ρ Yw n h = crraR tr β ρ (Yw 0 Fin.elim0) n (Yw n) := by
  simp only [crraDatePrice, crraR, crraMass, Finset.mul_sum, Finset.sum_div]
  exact Finset.sum_congr rfl fun h _ => by ring

/-- The first-order conditions (84) at the CRRA prices, over all dates, O&R Appendix 5C.3,
p. 342: the constant-share plan `C = μY^W` satisfies
`P(h_t) (μY^W_1)^{−ρ} = π(h_t|h_1) β^{t−1} (μY^W(h_t))^{−ρ}` for every `μ > 0`. -/
theorem crra_foc_infinite (tr : Tree S) (β ρ : ℝ) {Yw : (n : ℕ) → (Fin n → S) → ℝ}
    (hY : ∀ n h, 0 < Yw n h) {μ : ℝ} (hμ : 0 < μ) (n : ℕ) (h : Fin n → S) :
    crraDatePrice tr β ρ Yw n h * (μ * Yw 0 Fin.elim0) ^ (-ρ)
      = tr.histProb h * β ^ n * (μ * Yw n h) ^ (-ρ) := by
  have h1 := (Real.rpow_pos_of_pos (hY 0 Fin.elim0) (-ρ)).ne'
  rw [Real.mul_rpow hμ.le (hY 0 Fin.elim0).le, Real.mul_rpow hμ.le (hY n h).le]
  simp only [crraDatePrice]
  field_simp

/-- The date-`t` term of the date-1 value of a stream at the CRRA prices, O&R (83) with
Appendix 5C.3: `β^{t−1} E₁[Y^W(h_t)^{−ρ} x(h_t)]/(Y^W_1)^{−ρ}`. -/
theorem crra_valueSeries (tr : Tree S) (β ρ : ℝ) (Yw x : (n : ℕ) → (Fin n → S) → ℝ) (n : ℕ) :
    valueSeries (crraDatePrice tr β ρ Yw) x n
      = β ^ n * (∑ h, tr.histProb h * (Yw n h ^ (-ρ) * x n h)) / Yw 0 Fin.elim0 ^ (-ρ) := by
  simp only [valueSeries, crraDatePrice, Finset.mul_sum, Finset.sum_div]
  exact Finset.sum_congr rfl fun h _ => by ring

/-- The CRRA equilibrium of the infinite economy, O&R Appendix 5C.3, p. 342. Countries `j`
have positive endowments `Y^j(h_t)`, common CRRA utility (`ρ > 0`, `ρ ≠ 1`) and discount factor
`β > 0`. Primitive condition: for each country the series
`Σ_t β^{t−1} E₁[Y^W(h_t)^{−ρ} Y^j(h_t)]` converges. Then at the prices `crraDatePrice`, with
`μ^j` country `j`'s share of the date-1 present value of world output and `C^j = μ^j Y^W`:
the shares are positive and sum to one; each plan satisfies the first-order conditions (84) at
every history, the infinite budget constraint (83) with equality (the value series converges),
and is admissible (its utility series converges); markets clear at every history; and each
plan is optimal: no positive admissible plan satisfying (83) gives more expected utility. -/
theorem crra_equilibrium_infinite {ι : Type} [Fintype ι] (tr : Tree S) {β ρ : ℝ} (hβ : 0 < β)
    (hρ : 0 < ρ) (hρ1 : ρ ≠ 1) (Y : ι → (n : ℕ) → (Fin n → S) → ℝ)
    (hY : ∀ j n h, 0 < Y j n h)
    (hsum : ∀ j, Summable fun n =>
      β ^ n * ∑ h, tr.histProb h * (worldOutput Y n h ^ (-ρ) * Y j n h))
    (i : ι) :
    let P := crraDatePrice tr β ρ (worldOutput Y)
    let μ := fun j => dateOneValue P (Y j) / dateOneValue P (worldOutput Y)
    let C := fun j (n : ℕ) (h : Fin n → S) => μ j * worldOutput Y n h
    (0 < μ i ∧ ∑ j, μ j = 1) ∧
    (∀ n h, P n h * C i 0 Fin.elim0 ^ (-ρ) = tr.histProb h * β ^ n * C i n h ^ (-ρ)) ∧
    (Summable (valueSeries P (C i)) ∧ dateOneValue P (C i) = dateOneValue P (Y i)) ∧
    (∀ n h, ∑ j, C j n h = worldOutput Y n h) ∧
    Summable (utilSeries tr β (crraUtil ρ) (C i)) ∧
    (∀ C' : (n : ℕ) → (Fin n → S) → ℝ, (∀ n h, 0 < C' n h) →
      Summable (utilSeries tr β (crraUtil ρ) C') → Summable (valueSeries P C') →
      dateOneValue P C' ≤ dateOneValue P (Y i) →
      expectedUtility tr β (crraUtil ρ) C' ≤ expectedUtility tr β (crraUtil ρ) (C i)) := by
  intro P μ C
  set Yw := worldOutput Y with hYw_def
  have hYw : ∀ n h, 0 < Yw n h := fun n h =>
    Finset.sum_pos (fun j _ => hY j n h) ⟨i, Finset.mem_univ i⟩
  have hVs : ∀ j, Summable (valueSeries P (Y j)) := by
    intro j
    have e : valueSeries P (Y j) = fun n =>
        β ^ n * (∑ h, tr.histProb h * (Yw n h ^ (-ρ) * Y j n h)) / Yw 0 Fin.elim0 ^ (-ρ) :=
      funext (crra_valueSeries tr β ρ Yw (Y j))
    rw [e]; exact (hsum j).div_const _
  have hVwe : valueSeries P Yw = fun n => ∑ j, valueSeries P (Y j) n := by
    funext n
    simp only [valueSeries, hYw_def, worldOutput, Finset.mul_sum]
    exact Finset.sum_comm
  have hVw : Summable (valueSeries P Yw) := by
    rw [hVwe]; exact summable_sum fun j _ => hVs j
  have hDw : dateOneValue P Yw = ∑ j, dateOneValue P (Y j) := by
    unfold dateOneValue; rw [hVwe, Summable.tsum_finsetSum fun j _ => hVs j]
  have hP0 : P 0 Fin.elim0 = 1 := crraDatePrice_zero tr β ρ Yw (hYw 0 Fin.elim0)
  have hPnn : ∀ n h, 0 ≤ P n h := fun n h =>
    div_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hβ.le n) (tr.histProb_nonneg h))
      (Real.rpow_nonneg (hYw n h).le _)) (Real.rpow_nonneg (hYw 0 Fin.elim0).le _)
  have hDpos : ∀ x : (n : ℕ) → (Fin n → S) → ℝ, (∀ n h, 0 < x n h) →
      Summable (valueSeries P x) → 0 < dateOneValue P x := by
    intro x hx hs
    refine hs.tsum_pos (fun n => Finset.sum_nonneg fun h _ =>
      mul_nonneg (hPnn n h) (hx n h).le) 0 ?_
    rw [valueSeries, Fintype.sum_unique, Subsingleton.elim default Fin.elim0, hP0, one_mul]
    exact hx 0 Fin.elim0
  have hVwpos : 0 < dateOneValue P Yw := hDpos Yw hYw hVw
  have hμ : ∀ j, 0 < μ j := fun j => div_pos (hDpos (Y j) (hY j) (hVs j)) hVwpos
  have hμsum : ∑ j, μ j = 1 := by
    simp only [μ]
    rw [← Finset.sum_div, ← hDw, div_self hVwpos.ne']
  have hCe : valueSeries P (C i) = fun n => μ i * valueSeries P Yw n := by
    funext n
    simp only [valueSeries, C, Finset.mul_sum]
    exact Finset.sum_congr rfl fun h _ => by ring
  have hVC : Summable (valueSeries P (C i)) := by rw [hCe]; exact hVw.mul_left _
  have hbud : dateOneValue P (C i) = dateOneValue P (Y i) := by
    unfold dateOneValue
    rw [hCe, tsum_mul_left]
    exact div_mul_cancel₀ _ hVwpos.ne'
  have hfoc : ∀ n h, P n h * C i 0 Fin.elim0 ^ (-ρ) = tr.histProb h * β ^ n * C i n h ^ (-ρ) :=
    crra_foc_infinite tr β ρ hYw (hμ i)
  have hUe : utilSeries tr β (crraUtil ρ) (C i) = fun n => μ i ^ (1 - ρ) / (1 - ρ)
      * ∑ j, β ^ n * ∑ h, tr.histProb h * (Yw n h ^ (-ρ) * Y j n h) := by
    funext n
    have e1 : ∑ j, β ^ n * ∑ h, tr.histProb h * (Yw n h ^ (-ρ) * Y j n h)
        = β ^ n * ∑ h, tr.histProb h * Yw n h ^ (1 - ρ) := by
      rw [← Finset.mul_sum, Finset.sum_comm]
      congr 1
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [← Finset.mul_sum, ← Finset.mul_sum, show (1 : ℝ) - ρ = -ρ + 1 by ring,
        Real.rpow_add (hYw n h), Real.rpow_one]
      rfl
    rw [e1]
    simp only [utilSeries, crraUtil, C, Finset.mul_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [Real.mul_rpow (hμ i).le (hYw n h).le]
    ring
  have hU : Summable (utilSeries tr β (crraUtil ρ) (C i)) := by
    rw [hUe]; exact (summable_sum fun j _ => hsum j).mul_left _
  have hC : ∀ n h, 0 < C i n h := fun n h => mul_pos (hμ i) (hYw n h)
  refine ⟨⟨hμ i, hμsum⟩, hfoc, ⟨hVC, hbud⟩, ?_, hU, ?_⟩
  · intro n h
    simp only [C]
    rw [← Finset.sum_mul, hμsum, one_mul]
  · intro C' hC' hU' hV' hbud'
    exact arrowDebreu_optimal_infinite tr (crraUtil ρ) (fun x => x ^ (-ρ))
      (fun x y hx hy => crra_tangent hρ hρ1 hx hy) hβ.le P (Y i) hC hC'
      (Real.rpow_nonneg (hC 0 Fin.elim0).le _) hfoc hU hU' hVC hV' hbud hbud'

/-- Constant consumption shares in the infinite economy, O&R Appendix 5C.3, p. 342: if every
country's plan satisfies the first-order conditions (84) with CRRA marginal utility `C^{−ρ}`
(`ρ ≠ 0`) at common date-1 prices at every history, and world markets clear at every history,
then `C^j(h_t) = μ^j Y^W(h_t)` with the date-1 share `μ^j = C^j_1/Y^W_1`, at every history with
`π(h_t|h_1) > 0` (and `β > 0`). -/
theorem crra_constant_share_infinite {ι : Type} [Fintype ι] (tr : Tree S) {β ρ : ℝ}
    (hβ : 0 < β) (hρ : ρ ≠ 0) (P Yw : (n : ℕ) → (Fin n → S) → ℝ)
    (C : ι → (n : ℕ) → (Fin n → S) → ℝ) (hC : ∀ j n h, 0 < C j n h)
    (hfoc : ∀ j n h, P n h * C j 0 Fin.elim0 ^ (-ρ) = tr.histProb h * β ^ n * C j n h ^ (-ρ))
    (hclear : ∀ n h, ∑ j, C j n h = Yw n h) (i : ι) (n : ℕ) (h : Fin n → S)
    (hπ : 0 < tr.histProb h) :
    C i n h = C i 0 Fin.elim0 / Yw 0 Fin.elim0 * Yw n h := by
  have hk : 0 < tr.histProb h * β ^ n := mul_pos hπ (pow_pos hβ n)
  have ratio : ∀ j, (C j n h / C j 0 Fin.elim0) ^ (-ρ) = P n h / (tr.histProb h * β ^ n) := by
    intro j
    have h0 := hC j 0 Fin.elim0
    rw [Real.div_rpow (hC j n h).le h0.le, eq_div_iff hk.ne',
      div_mul_eq_mul_div, div_eq_iff (Real.rpow_pos_of_pos h0 _).ne']
    linarith [hfoc j n h]
  have hg : ∀ j, C j n h / C j 0 Fin.elim0 = C i n h / C i 0 Fin.elim0 := fun j =>
    (Real.rpow_left_inj (div_pos (hC j n h) (hC j 0 _)).le (div_pos (hC i n h) (hC i 0 _)).le
      (neg_ne_zero.mpr hρ)).mp ((ratio j).trans (ratio i).symm)
  have hY0 : 0 < Yw 0 Fin.elim0 := by
    rw [← hclear]; exact Finset.sum_pos (fun j _ => hC j 0 _) ⟨i, Finset.mem_univ i⟩
  have hYn : Yw n h = C i n h / C i 0 Fin.elim0 * Yw 0 Fin.elim0 := by
    rw [← hclear, ← hclear, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hg j, div_mul_cancel₀ _ (hC j 0 _).ne']
  have := (hC i 0 Fin.elim0).ne'
  rw [hYn]
  field_simp

/-- The share is pinned down by the infinite budget constraint, O&R Appendix 5C.3, p. 342: if the
plan `C = μY^W` exhausts the date-1 value of the endowment `Y` (83), then `μ` is the country's
share of the date-1 present value of world output, `μ = PV(Y)/PV(Y^W)` (given `PV(Y^W) ≠ 0`). -/
theorem crra_share_of_budget (P Y Yw : (n : ℕ) → (Fin n → S) → ℝ) {μ : ℝ}
    (hW : dateOneValue P Yw ≠ 0)
    (hbud : dateOneValue P (fun n h => μ * Yw n h) = dateOneValue P Y) :
    μ = dateOneValue P Y / dateOneValue P Yw := by
  have e : dateOneValue P (fun n h => μ * Yw n h) = μ * dateOneValue P Yw := by
    unfold dateOneValue valueSeries
    rw [← tsum_mul_left]
    refine tsum_congr fun n => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun h _ => by ring
  rw [eq_div_iff hW, ← hbud, e, mul_comm]

/-- The log-utility (`ρ = 1`) equilibrium of the infinite economy, O&R Appendix 5C.3, p. 342
(the limit `ρ → 1` of CRRA utility). Countries `j` have positive endowments and common log
utility with discount factor `0 < β < 1`. The prices are `crraDatePrice` at `ρ = 1`,
`P(h_t) = β^{t−1} π(h_t|h_1) Y^W_1/Y^W(h_t)`. The budget series of every endowment converges
automatically (`Y^j/Y^W ≤ 1` and `β < 1`); the one extra primitive condition, needed exactly for
the equilibrium utility series `Σ β^{t−1}E₁ log(μ^j Y^W)` to converge, is that
`Σ_t β^{t−1} E₁ log Y^W(h_t)` converges. Then, with `μ^j` the present-value share and
`C^j = μ^j Y^W`: the shares are positive and sum to one; each plan satisfies the log first-order
conditions (84) `P(h_t)/C^j_1 = π(h_t|h_1) β^{t−1}/C^j(h_t)`, the infinite budget (83) with
equality, market clearing, admissibility, and optimality against every positive admissible plan
satisfying (83). -/
theorem log_equilibrium_infinite {ι : Type} [Fintype ι] (tr : Tree S) {β : ℝ} (hβ : 0 < β)
    (hβ1 : β < 1) (Y : ι → (n : ℕ) → (Fin n → S) → ℝ) (hY : ∀ j n h, 0 < Y j n h)
    (hlog : Summable fun n => β ^ n * ∑ h, tr.histProb h * Real.log (worldOutput Y n h))
    (i : ι) :
    let P := crraDatePrice tr β 1 (worldOutput Y)
    let μ := fun j => dateOneValue P (Y j) / dateOneValue P (worldOutput Y)
    let C := fun j (n : ℕ) (h : Fin n → S) => μ j * worldOutput Y n h
    (0 < μ i ∧ ∑ j, μ j = 1) ∧
    (∀ n h, P n h * (C i 0 Fin.elim0)⁻¹ = tr.histProb h * β ^ n * (C i n h)⁻¹) ∧
    (Summable (valueSeries P (C i)) ∧ dateOneValue P (C i) = dateOneValue P (Y i)) ∧
    (∀ n h, ∑ j, C j n h = worldOutput Y n h) ∧
    Summable (utilSeries tr β Real.log (C i)) ∧
    (∀ C' : (n : ℕ) → (Fin n → S) → ℝ, (∀ n h, 0 < C' n h) →
      Summable (utilSeries tr β Real.log C') → Summable (valueSeries P C') →
      dateOneValue P C' ≤ dateOneValue P (Y i) →
      expectedUtility tr β Real.log C' ≤ expectedUtility tr β Real.log (C i)) := by
  intro P μ C
  set Yw := worldOutput Y with hYw_def
  have hYw : ∀ n h, 0 < Yw n h := fun n h =>
    Finset.sum_pos (fun j _ => hY j n h) ⟨i, Finset.mem_univ i⟩
  have hP0 : P 0 Fin.elim0 = 1 := crraDatePrice_zero tr β 1 Yw (hYw 0 Fin.elim0)
  have hPnn : ∀ n h, 0 ≤ P n h := fun n h =>
    div_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hβ.le n) (tr.histProb_nonneg h))
      (Real.rpow_nonneg (hYw n h).le _)) (Real.rpow_nonneg (hYw 0 Fin.elim0).le _)
  have hY1 : 0 < Yw 0 Fin.elim0 ^ (-(1 : ℝ)) := Real.rpow_pos_of_pos (hYw 0 Fin.elim0) _
  have hVs : ∀ j, Summable (valueSeries P (Y j)) := by
    intro j
    refine Summable.of_nonneg_of_le (fun n => Finset.sum_nonneg fun h _ =>
      mul_nonneg (hPnn n h) (hY j n h).le) (fun n => ?_)
      ((summable_geometric_of_lt_one hβ.le hβ1).div_const (Yw 0 Fin.elim0 ^ (-(1 : ℝ))))
    rw [crra_valueSeries]
    refine div_le_div_of_nonneg_right ?_ hY1.le
    refine mul_le_of_le_one_right (pow_nonneg hβ.le n) ?_
    calc ∑ h, tr.histProb h * (Yw n h ^ (-(1 : ℝ)) * Y j n h) ≤ ∑ h, tr.histProb h * 1 :=
          Finset.sum_le_sum fun h _ => mul_le_mul_of_nonneg_left (by
            rw [Real.rpow_neg_one, inv_mul_le_one₀ (hYw n h)]
            exact Finset.single_le_sum (f := fun j => Y j n h) (fun j _ => (hY j n h).le)
              (Finset.mem_univ j)) (tr.histProb_nonneg h)
      _ = 1 := by simp [tr.histProb_sum_eq_one]
  have hVwe : valueSeries P Yw = fun n => ∑ j, valueSeries P (Y j) n := by
    funext n
    simp only [valueSeries, hYw_def, worldOutput, Finset.mul_sum]
    exact Finset.sum_comm
  have hVw : Summable (valueSeries P Yw) := by
    rw [hVwe]; exact summable_sum fun j _ => hVs j
  have hDw : dateOneValue P Yw = ∑ j, dateOneValue P (Y j) := by
    unfold dateOneValue; rw [hVwe, Summable.tsum_finsetSum fun j _ => hVs j]
  have hDpos : ∀ x : (n : ℕ) → (Fin n → S) → ℝ, (∀ n h, 0 < x n h) →
      Summable (valueSeries P x) → 0 < dateOneValue P x := by
    intro x hx hs
    refine hs.tsum_pos (fun n => Finset.sum_nonneg fun h _ =>
      mul_nonneg (hPnn n h) (hx n h).le) 0 ?_
    rw [valueSeries, Fintype.sum_unique, Subsingleton.elim default Fin.elim0, hP0, one_mul]
    exact hx 0 Fin.elim0
  have hVwpos : 0 < dateOneValue P Yw := hDpos Yw hYw hVw
  have hμ : ∀ j, 0 < μ j := fun j => div_pos (hDpos (Y j) (hY j) (hVs j)) hVwpos
  have hμsum : ∑ j, μ j = 1 := by
    simp only [μ]
    rw [← Finset.sum_div, ← hDw, div_self hVwpos.ne']
  have hCe : valueSeries P (C i) = fun n => μ i * valueSeries P Yw n := by
    funext n
    simp only [valueSeries, C, Finset.mul_sum]
    exact Finset.sum_congr rfl fun h _ => by ring
  have hVC : Summable (valueSeries P (C i)) := by rw [hCe]; exact hVw.mul_left _
  have hbud : dateOneValue P (C i) = dateOneValue P (Y i) := by
    unfold dateOneValue
    rw [hCe, tsum_mul_left]
    exact div_mul_cancel₀ _ hVwpos.ne'
  have hfoc : ∀ n h, P n h * (C i 0 Fin.elim0)⁻¹ = tr.histProb h * β ^ n * (C i n h)⁻¹ := by
    intro n h
    have := crra_foc_infinite tr β 1 hYw (hμ i) n h
    simp only [Real.rpow_neg_one] at this
    exact this
  have hUe : utilSeries tr β Real.log (C i) = fun n => Real.log (μ i) * β ^ n
      + β ^ n * ∑ h, tr.histProb h * Real.log (Yw n h) := by
    funext n
    have e : ∀ h, Real.log (μ i * worldOutput Y n h) = Real.log (μ i) + Real.log (Yw n h) :=
      fun h => Real.log_mul (hμ i).ne' (hYw n h).ne'
    simp only [utilSeries, C, e, mul_add,
      Finset.sum_add_distrib, ← Finset.sum_mul, tr.histProb_sum_eq_one, one_mul]
    ring
  have hU : Summable (utilSeries tr β Real.log (C i)) := by
    rw [hUe]; exact ((summable_geometric_of_lt_one hβ.le hβ1).mul_left _).add hlog
  have hC : ∀ n h, 0 < C i n h := fun n h => mul_pos (hμ i) (hYw n h)
  refine ⟨⟨hμ i, hμsum⟩, hfoc, ⟨hVC, hbud⟩, ?_, hU, ?_⟩
  · intro n h
    simp only [C]
    rw [← Finset.sum_mul, hμsum, one_mul]
  · intro C' hC' hU' hV' hbud'
    exact arrowDebreu_optimal_infinite tr Real.log (fun x => x⁻¹)
      (fun x y hx hy => by simpa [one_div] using log_tangent hx hy) hβ.le P (Y i) hC hC'
      (inv_nonneg.mpr (hC 0 Fin.elim0).le) hfoc hU hU' hVC hV' hbud hbud'

/-! ### Appendix 5D: dynamic consistency in the infinite economy -/

/-- The date-`(m+2)` term of date-2 expected utility after the date-2 event `s₂`, O&R Appendix
5D, p. 344: `β^{t−2} Σ_{h_t ∈ H_t(h_2)} π(h_t|h_2) u(c(h_t))`, `t = m + 2`, for a plan `c` on
the histories continuing `h_2 = {s₂} ∪ h_1` (date 2 itself is `m = 0`). -/
noncomputable def dateTwoUtilSeries [DecidableEq S] (tr : Tree S) (β : ℝ) (u : ℝ → ℝ) (s₂ : S)
    (c : (m : ℕ) → (Fin (m + 1) → S) → ℝ) (m : ℕ) : ℝ :=
  ∑ h ∈ univ.filter (fun h : Fin (m + 1) → S => h 0 = s₂), β ^ m * tr.condProb h 1 * u (c m h)

/-- The date-`(m+2)` term `Σ_{h_t ∈ H_t(h_2)} p̃(h_t|h_2) c(h_t)` of the date-2 budget
constraint, O&R Appendix 5D, p. 344, with date-2 prices `P₂ = p̃(·|h_2)` in date-2 output. -/
noncomputable def dateTwoValueSeries [DecidableEq S] (s₂ : S)
    (P₂ c : (m : ℕ) → (Fin (m + 1) → S) → ℝ) (m : ℕ) : ℝ :=
  ∑ h ∈ univ.filter (fun h : Fin (m + 1) → S => h 0 = s₂), P₂ m h * c m h

/-- The date-1 plan, continued after the date-2 event `s₂`, is admissible for the date-2
problem (O&R Appendix 5D, p. 344): if it satisfies (84) with `u′ > 0` at date-1 prices, its
budget series converges and its utility series converges absolutely (expected discounted utility
integrable over the event tree), and `π(h_2|h_1) > 0`, then with the no-arbitrage date-2 prices
`p̃(h_t|h_2) = p̃(h_t|h_1)/p̃(h_2|h_1)` its date-2 utility and budget series converge. -/
theorem dateTwo_restriction_admissible [DecidableEq S] (tr : Tree S) (u du : ℝ → ℝ)
    (hdu : ∀ x, 0 < x → 0 < du x) {β : ℝ} (hβ : 0 < β)
    (P : (n : ℕ) → (Fin n → S) → ℝ) (P₂ : (m : ℕ) → (Fin (m + 1) → S) → ℝ)
    {C : (n : ℕ) → (Fin n → S) → ℝ} (hC : ∀ n h, 0 < C n h)
    (hfoc : ∀ n h, P n h * du (C 0 Fin.elim0) = tr.histProb h * β ^ n * du (C n h))
    (hUabs : Summable fun n => β ^ n * ∑ h, tr.histProb h * |u (C n h)|)
    (hV : Summable (valueSeries P C)) (s₂ : S) (hπ₂ : 0 < tr.q 0 Fin.elim0 s₂)
    (harb : ∀ m (h : Fin (m + 1) → S), h 0 = s₂ → P (m + 1) h / P 1 (fun _ => s₂) = P₂ m h) :
    Summable (dateTwoUtilSeries tr β u s₂ fun m h => C (m + 1) h) ∧
      Summable (dateTwoValueSeries s₂ P₂ fun m h => C (m + 1) h) := by
  have hdu1 := hdu _ (hC 0 Fin.elim0)
  have hPnn : ∀ n h, 0 ≤ P n h := by
    intro n h
    have e : P n h = tr.histProb h * β ^ n * du (C n h) / du (C 0 Fin.elim0) := by
      rw [eq_div_iff hdu1.ne']; exact hfoc n h
    rw [e]
    exact div_nonneg (mul_nonneg (mul_nonneg (tr.histProb_nonneg h) (pow_nonneg hβ.le n))
      (hdu _ (hC n h)).le) hdu1.le
  have hP1 : 0 < P 1 (fun _ => s₂) := by
    have e : P 1 (fun _ => s₂)
        = tr.histProb (fun _ : Fin 1 => s₂) * β ^ 1 * du (C 1 fun _ => s₂) / du (C 0 Fin.elim0) :=
      by rw [eq_div_iff hdu1.ne']; exact hfoc 1 _
    rw [e, tr.histProb_one]
    exact div_pos (mul_pos (mul_pos hπ₂ (pow_pos hβ 1)) (hdu _ (hC 1 _))) hdu1
  constructor
  · refine Summable.of_norm_bounded (((summable_nat_add_iff 1).mpr hUabs).div_const
      (β * tr.q 0 Fin.elim0 s₂)) fun m => ?_
    have hk : 0 < β * tr.q 0 Fin.elim0 s₂ := mul_pos hβ hπ₂
    rw [Real.norm_eq_abs, le_div_iff₀ hk]
    refine le_trans (mul_le_mul_of_nonneg_right (Finset.abs_sum_le_sum_abs _ _) hk.le) ?_
    rw [Finset.sum_mul, Finset.mul_sum]
    refine le_trans ?_ (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.filter_subset (fun h : Fin (m + 1) → S => h 0 = s₂) univ)
      fun h _ _ => mul_nonneg (pow_nonneg hβ.le _)
        (mul_nonneg (tr.histProb_nonneg h) (abs_nonneg _)))
    refine le_of_eq (Finset.sum_congr rfl fun h hh => ?_)
    have hh0 : h 0 = s₂ := (Finset.mem_filter.mp hh).2
    rw [abs_mul, abs_mul, abs_of_nonneg (pow_nonneg hβ.le m),
      abs_of_nonneg (tr.condProb_nonneg h 1), tr.histProb_eq_first_mul_condProb, hh0]
    ring
  · refine Summable.of_nonneg_of_le (fun m => Finset.sum_nonneg fun h hh => ?_) (fun m => ?_)
      (((summable_nat_add_iff 1).mpr hV).div_const (P 1 fun _ => s₂))
    · rw [← harb m h (Finset.mem_filter.mp hh).2]
      exact mul_nonneg (div_nonneg (hPnn _ h) hP1.le) (hC _ h).le
    · simp only [dateTwoValueSeries, valueSeries]
      rw [le_div_iff₀ hP1, Finset.sum_mul]
      refine le_trans (le_of_eq (Finset.sum_congr rfl fun h hh => ?_))
        (Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.filter_subset (fun h : Fin (m + 1) → S => h 0 = s₂) univ)
      fun h _ _ => mul_nonneg (hPnn _ h) (hC _ h).le)
      rw [← harb m h (Finset.mem_filter.mp hh).2]
      field_simp

/-- Dynamic consistency over the infinite horizon, O&R Appendix 5D, pp. 343–344. Suppose the
date-1 plan `C` satisfies the first-order conditions (84)/(86) at date-1 prices
`p̃(h_t|h_1) = R_{1,t} p(h_t|h_1)` at every history, `u` is concave with `u′ > 0`, the plan's
budget series converges and its utility series converges absolutely. Markets reopen on date 2
after the event `s₂` (with `π(h_2|h_1) > 0`) at date-2 prices obeying the book's no-arbitrage
identity `p̃(h_t|h_1)/p̃(h_2|h_1) = p̃(h_t|h_2)` (a hypothesis: O&R justify it by an arbitrage
argument, buying a date-`t` claim directly or via a date-2 claim, not by the model's
primitives). Then every positive plan `c′` on the date-2 subtree whose utility and budget
series converge and which satisfies the date-2 budget constraint (p. 344) gives no more date-2
expected utility than the continuation of the date-1 plan: the date-1 plan remains optimal. -/
theorem dynamic_consistency_infinite [DecidableEq S] (tr : Tree S) (u du : ℝ → ℝ)
    (htan : ∀ x y, 0 < x → 0 < y → u y ≤ u x + du x * (y - x))
    (hdu : ∀ x, 0 < x → 0 < du x) {β : ℝ} (hβ : 0 < β)
    (P : (n : ℕ) → (Fin n → S) → ℝ) (P₂ : (m : ℕ) → (Fin (m + 1) → S) → ℝ)
    {C : (n : ℕ) → (Fin n → S) → ℝ} (hC : ∀ n h, 0 < C n h)
    (hfoc : ∀ n h, P n h * du (C 0 Fin.elim0) = tr.histProb h * β ^ n * du (C n h))
    (hUabs : Summable fun n => β ^ n * ∑ h, tr.histProb h * |u (C n h)|)
    (hV : Summable (valueSeries P C)) (s₂ : S) (hπ₂ : 0 < tr.q 0 Fin.elim0 s₂)
    (harb : ∀ m (h : Fin (m + 1) → S), h 0 = s₂ → P (m + 1) h / P 1 (fun _ => s₂) = P₂ m h)
    {c' : (m : ℕ) → (Fin (m + 1) → S) → ℝ}
    (hc' : ∀ m (h : Fin (m + 1) → S), h 0 = s₂ → 0 < c' m h)
    (hU' : Summable (dateTwoUtilSeries tr β u s₂ c'))
    (hV' : Summable (dateTwoValueSeries s₂ P₂ c'))
    (hbud : ∑' m, dateTwoValueSeries s₂ P₂ c' m
      ≤ ∑' m, dateTwoValueSeries s₂ P₂ (fun m h => C (m + 1) h) m) :
    ∑' m, dateTwoUtilSeries tr β u s₂ c' m
      ≤ ∑' m, dateTwoUtilSeries tr β u s₂ (fun m h => C (m + 1) h) m := by
  obtain ⟨hU, hVr⟩ := dateTwo_restriction_admissible tr u du hdu hβ P P₂ hC hfoc hUabs hV s₂
    hπ₂ harb
  have hπ₂' : 0 < tr.histProb (fun _ : Fin 1 => s₂) := by rw [tr.histProb_one]; exact hπ₂
  refine foc_plan_optimal_tsum (fun m => univ.filter (fun h : Fin (m + 1) → S => h 0 = s₂))
    u du htan (fun m h => β ^ m * tr.condProb h 1) P₂
    (fun m h _ => mul_nonneg (pow_nonneg hβ.le m) (tr.condProb_nonneg h 1))
    (hdu _ (hC 1 fun _ => s₂)).le (fun m h _ => hC (m + 1) h)
    (fun m h hh => hc' m h (Finset.mem_filter.mp hh).2) ?_ hU hU' hVr hV' hbud
  intro m h hh
  have hh0 : h 0 = s₂ := (Finset.mem_filter.mp hh).2
  have hg : restr h 1 (by omega) = fun _ : Fin 1 => s₂ := by
    funext j
    rw [Fin.fin_one_eq_zero j, ← hh0]
    rfl
  have hπ : 0 < tr.histProb (restr h 1 (by omega)) := by rw [hg]; exact hπ₂'
  have hf₂ : P 1 (fun _ => s₂) * du (C 0 Fin.elim0)
      = tr.histProb (restr h 1 (by omega)) * β ^ 1 * du (C 1 (fun _ => s₂)) := by
    rw [hg]; exact hfoc 1 _
  have key := foc_date2 tr du hβ h hπ (hdu _ (hC 0 _)) (hdu _ (hC 1 _)) hf₂
    (hfoc (m + 1) h) (harb m h hh0)
  rw [key]; ring

/-! ## Supplement A to Chapter 5: multiperiod portfolio selection -/

/-- Log utility, O&R Supplement A, p. 743: with consumption `C_s = μW_s`, wealth
`W_{t+1} = (1 + r°_{t+1})(W_t − C_t)` and next-period return `r°(s)` in state `s` (probabilities
`π`, `Σπ = 1`, `1 + r°(s) > 0`), the Euler equation `1/C_t = βE_t{(1 + r°_{t+1})/C_{t+1}}` holds
if and only if `μ = 1 − β` (for `0 < μ < 1`, `W_t > 0`), whatever the return distribution. -/
theorem log_share_iff {ι : Type} [Fintype ι] (π r : ι → ℝ) (hπ : ∑ s, π s = 1)
    (hr : ∀ s, 0 < 1 + r s) {β μ W : ℝ} (hμ0 : 0 < μ) (hμ1 : μ < 1) (hW : 0 < W) :
    1 / (μ * W) = β * ∑ s, π s * ((1 + r s) * (1 / (μ * ((1 + r s) * ((1 - μ) * W)))))
      ↔ μ = 1 - β := by
  have h1 : 0 < 1 - μ := by linarith
  have e : ∀ s, π s * ((1 + r s) * (1 / (μ * ((1 + r s) * ((1 - μ) * W)))))
      = π s * (1 / (μ * ((1 - μ) * W))) := by
    intro s
    have := (hr s).ne'
    field_simp
  simp only [e, ← Finset.sum_mul, hπ, one_mul]
  rw [mul_one_div, div_eq_div_iff (by positivity) (by positivity)]
  constructor
  · intro h
    have h2 : (1 - μ) * (μ * W) = β * (μ * W) := by linarith
    have := mul_right_cancel₀ (mul_pos hμ0 hW).ne' h2
    linarith
  · intro h
    rw [h]; ring

/-- The share formula behind O&R's CRRA recursion, Supplement A, p. 744: for `0 < μ < 1`,
`ρ > 0` and `K ≥ 0`, `μ = (1 + K^{1/ρ})^{−1}` if and only if `K = ((1 − μ)/μ)^ρ`. -/
theorem share_formula_iff {μ ρ K : ℝ} (hμ0 : 0 < μ) (hμ1 : μ < 1) (hρ : 0 < ρ)
    (hK : 0 ≤ K) : μ = (1 + K ^ (1 / ρ))⁻¹ ↔ K = ((1 - μ) / μ) ^ ρ := by
  have h1 : 0 < 1 - μ := by linarith
  have hq : 0 ≤ (1 - μ) / μ := (div_pos h1 hμ0).le
  have hKr : 0 ≤ K ^ (1 / ρ) := Real.rpow_nonneg hK _
  constructor
  · intro h
    have e : K ^ (1 / ρ) = (1 - μ) / μ := by
      rw [h]; field_simp; ring
    rw [← e, one_div, Real.rpow_inv_rpow hK hρ.ne']
  · intro h
    have e : K ^ (1 / ρ) = (1 - μ) / μ := by
      rw [h, one_div, Real.rpow_rpow_inv hq hρ.ne']
    rw [e]
    field_simp
    ring

/-- The CRRA consumption-share recursion, O&R Supplement A, p. 744. With `u′(C) = C^{−ρ}`,
`C_t = μ_t W_t`, `C_{t+1}(s) = μ_{t+1}(s) W_{t+1}(s)` and
`W_{t+1}(s) = (1 + r°(s))(1 − μ_t)W_t`, the consumption Euler equation
`C_t^{−ρ} = βE_t{(1 + r°_{t+1}) C_{t+1}^{−ρ}}` holds if and only if
`μ_t = (1 + [βE_t{(1 + r°_{t+1})^{1−ρ} μ_{t+1}^{−ρ}}]^{1/ρ})^{−1}`
(for `0 < μ_t < 1`, `μ_{t+1} > 0`, `W_t > 0`, `1 + r° > 0`, `β ≥ 0`, `π ≥ 0`, `ρ > 0`). -/
theorem crra_share_recursion {ι : Type} [Fintype ι] (π r μ' : ι → ℝ)
    (hπ : ∀ s, 0 ≤ π s) (hr : ∀ s, 0 < 1 + r s) (hμ' : ∀ s, 0 < μ' s) {β ρ μ W : ℝ}
    (hβ : 0 ≤ β) (hρ : 0 < ρ) (hμ0 : 0 < μ) (hμ1 : μ < 1) (hW : 0 < W) :
    (μ * W) ^ (-ρ) = β * ∑ s, π s * ((1 + r s) * (μ' s * ((1 + r s) * (1 - μ) * W)) ^ (-ρ))
      ↔ μ = (1 + (β * ∑ s, π s * ((1 + r s) ^ (1 - ρ) * μ' s ^ (-ρ))) ^ (1 / ρ))⁻¹ := by
  have h1 : 0 < 1 - μ := by linarith
  set E := ∑ s, π s * ((1 + r s) ^ (1 - ρ) * μ' s ^ (-ρ)) with hE
  have hE0 : 0 ≤ E := Finset.sum_nonneg fun s _ =>
    mul_nonneg (hπ s) (mul_nonneg (Real.rpow_nonneg (hr s).le _)
      (Real.rpow_nonneg (hμ' s).le _))
  have e : ∀ s, π s * ((1 + r s) * (μ' s * ((1 + r s) * (1 - μ) * W)) ^ (-ρ))
      = π s * ((1 + r s) ^ (1 - ρ) * μ' s ^ (-ρ)) * ((1 - μ) * W) ^ (-ρ) := by
    intro s
    have hrs := hr s
    rw [show μ' s * ((1 + r s) * (1 - μ) * W) = μ' s * ((1 + r s) * ((1 - μ) * W)) by ring,
      Real.mul_rpow (hμ' s).le (by positivity), Real.mul_rpow hrs.le (by positivity),
      show (1 : ℝ) - ρ = 1 + -ρ by ring, Real.rpow_add hrs, Real.rpow_one]
    ring
  simp only [e, ← Finset.sum_mul]
  rw [← hE, share_formula_iff hμ0 hμ1 hρ (mul_nonneg hβ hE0), Real.mul_rpow hμ0.le hW.le,
    Real.mul_rpow h1.le hW.le, Real.div_rpow h1.le hμ0.le]
  have hWr : 0 < W ^ (-ρ) := Real.rpow_pos_of_pos hW _
  have hμr : 0 < μ ^ ρ := Real.rpow_pos_of_pos hμ0 _
  rw [Real.rpow_neg hμ0.le, Real.rpow_neg h1.le, Real.rpow_neg hW.le]
  have h1r : 0 < (1 - μ) ^ ρ := Real.rpow_pos_of_pos h1 _
  have hWr' : 0 < W ^ ρ := Real.rpow_pos_of_pos hW _
  constructor
  · intro h
    field_simp at h
    rw [eq_div_iff hμr.ne']
    nlinarith
  · intro h
    have e2 : β * (E * (((1 - μ) ^ ρ)⁻¹ * (W ^ ρ)⁻¹)) = β * E * (((1 - μ) ^ ρ)⁻¹ * (W ^ ρ)⁻¹) :=
      by ring
    rw [e2, h]
    field_simp

/-- The i.i.d. fixed point, O&R Supplement A, p. 744: with a constant share `μ_{t+1} = μ`, the
recursion `μ = (1 + [βE{(1 + r°)^{1−ρ} μ^{−ρ}}]^{1/ρ})^{−1}` holds if and only if
`μ = 1 − [βE(1 + r°)^{1−ρ}]^{1/ρ}` (for `0 < μ < 1`, `ρ > 0`, `β ≥ 0`, `π ≥ 0`,
`1 + r° > 0`). So the book's formula is a fixed point, and the only one in `(0, 1)`. -/
theorem crra_iid_share {ι : Type} [Fintype ι] (π r : ι → ℝ) (hπ : ∀ s, 0 ≤ π s)
    (hr : ∀ s, 0 < 1 + r s) {β ρ μ : ℝ} (hβ : 0 ≤ β) (hρ : 0 < ρ) (hμ0 : 0 < μ)
    (hμ1 : μ < 1) :
    μ = (1 + (β * ∑ s, π s * ((1 + r s) ^ (1 - ρ) * μ ^ (-ρ))) ^ (1 / ρ))⁻¹
      ↔ μ = 1 - (β * ∑ s, π s * (1 + r s) ^ (1 - ρ)) ^ (1 / ρ) := by
  set B := β * ∑ s, π s * (1 + r s) ^ (1 - ρ) with hB
  have hB0 : 0 ≤ B := mul_nonneg hβ (Finset.sum_nonneg fun s _ =>
    mul_nonneg (hπ s) (Real.rpow_nonneg (hr s).le _))
  have h1 : 0 < 1 - μ := by linarith
  have eK : β * ∑ s, π s * ((1 + r s) ^ (1 - ρ) * μ ^ (-ρ)) = B * μ ^ (-ρ) := by
    rw [hB, mul_assoc, Finset.sum_mul]
    congr 1
    exact Finset.sum_congr rfl fun s _ => by ring
  have hμr : 0 < μ ^ ρ := Real.rpow_pos_of_pos hμ0 _
  rw [eK, share_formula_iff hμ0 hμ1 hρ (mul_nonneg hB0 (Real.rpow_nonneg hμ0.le _)),
    Real.div_rpow h1.le hμ0.le, Real.rpow_neg hμ0.le]
  constructor
  · intro h
    have hB' : B = (1 - μ) ^ ρ := by
      field_simp at h
      exact h
    rw [hB', one_div, Real.rpow_rpow_inv h1.le hρ.ne']
    ring
  · intro h
    have hb : (1 - μ) = B ^ (1 / ρ) := by linarith
    rw [hb, one_div, Real.rpow_inv_rpow hB0 hρ.ne']
    field_simp

/-- The log case of the i.i.d. share, O&R Supplement A, pp. 743–744: at `ρ = 1` the formula
`1 − [βE(1 + r°)^{1−ρ}]^{1/ρ}` reduces to `1 − β` (given `Σπ = 1`). -/
theorem crra_iid_share_log {ι : Type} [Fintype ι] (π r : ι → ℝ) (hπ : ∑ s, π s = 1)
    (β : ℝ) : 1 - (β * ∑ s, π s * (1 + r s) ^ ((1 : ℝ) - 1)) ^ ((1 : ℝ) / 1) = 1 - β := by
  simp [hπ]

end ObstfeldRogoff.InternationalFinancialMarkets.EventTree
