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

**Appendix 5C.** A finite horizon `T` replaces the book's infinite horizon: the dates after 1
are `t = n + 1`, `n ∈ [1, T)`. We derive the noncontingent-bond Euler equation (85) and the
analogue of (9) from the first-order conditions (84), prove that (84) plus the budget
constraint (83) give a global optimum when `u` is concave (supporting-line inequality),
verify the CRRA equilibrium `C(h_t) = μ Y^W(h_t)` with its prices and long-term interest
factor `R_{1,t}`, and conversely derive the constant shares from the first-order conditions
and market clearing.

**Appendix 5D.** Prices in date-1 units `p̃ = p R`; from (86) the date-1 plan satisfies
(88), which by Bayes' rule and the no-arbitrage identity `p̃(h_t|h_1)/p̃(h_2|h_1) = p̃(h_t|h_2)`
(taken as a hypothesis, as in the book's arbitrage argument) is (87); the old plan is
therefore optimal for the date-2 problem with ongoing trade (dynamic consistency).

**Supplement A.** Log utility gives the consumption share `μ = 1 − β`; the CRRA share
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

/-- The many-period Arrow–Debreu problem, O&R (82)–(84), pp. 341–342, over a finite horizon
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

/-- Present value at date 1 of a history-contingent stream `x`, in date-1 output
(O&R (83), p. 341): `x₁ + Σ_t R_{1,t} Σ_{h_t} p(h_t|h_1) x(h_t)`. -/
noncomputable def presentValue (T : ℕ) (R : ℕ → ℝ) (p : (n : ℕ) → (Fin n → S) → ℝ)
    (x₁ : ℝ) (x : (n : ℕ) → (Fin n → S) → ℝ) : ℝ :=
  x₁ + ∑ n ∈ Ico 1 T, R n * ∑ h, p n h * x n h

/-- The budget constraint (83) at the constant-share plan, O&R Appendix 5C.3, p. 342: at any
prices, if `μ` is country `n`'s share of the date-1 present value of world output, the plan
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

/-- Dynamic consistency, O&R Appendix 5D, pp. 343–344. Suppose the date-1 plan `(C₁, C)`
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
