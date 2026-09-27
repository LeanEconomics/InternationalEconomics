/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import InternationalFinancialMarkets.EventTree
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Infinite-horizon consumption-based asset pricing on an event tree

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §5.4.3
(pp. 315–317), Chapter 5 Exercise 3(a) (pp. 345–346) and Exercise 6 (p. 347).

This module generalises the deterministic `AssetPricing.price_eq_present_value` /
`price_crra_world_output` and the truncated Markov results of `OLGRiskSharing` to a genuinely
stochastic, infinite-horizon economy.

**Uncertainty.** Histories are those of `EventTree` (`h : Fin n → S`, date `t = n + 1`), with
the tree's one-step conditional probabilities `q n h s`. A `TreeProcess` assigns a number to
every history, and `condE tr f k` is the `k`-step conditional expectation `E_t[f_{t+k}]`,
defined one step at a time; we prove the law of iterated expectations and that `condE` is
the sum over continuations weighted by `Tree.condProb` (`condE_eq_sum_condProb`); at the
root it is the sum over histories weighted by `Tree.histProb` (`condE_root_eq_sum_histProb`).

**(57)–(59).** From the Euler equation (57) at every history we prove the `K`-step identity
(price = `K` discounted expected dividends + `β^K` discounted expected price), and under the
book's no-bubble condition the price is the limit of the present-value partial sums (59)
(a genuine `HasSum` when dividends are nonnegative). Conversely, if the series converges at
every history it solves (57); every solution is the series plus a bubble `b` with
`b_t = βE_t[b_{t+1}]`; the price equals the series iff the no-bubble condition holds; and
without that condition prices are not unique (deterministic bubbles `c/β^{t−1}`). The
no-bubble condition is *derived* when `u′(C)V` is bounded and `0 ≤ β < 1`; with `u′(C)Y`
bounded the series converges (proved) and gives the unique bounded price.

**(60)–(61).** Each term splits into a riskless-discounted expectation plus a conditional
covariance with the marginal rate of substitution; `R_{t,s}` is the price of a riskless
discount bond (footnote 44). With CRRA utility and `C = μY^W` the marginal rate of
substitution is `(Y^W_s/Y^W_t)^{−ρ}` (61), and for bounded prices with `Y^W` bounded away
from zero no no-bubble hypothesis is needed. The constant share `C = μY^W` is also derived
from all countries' complete-markets first-order conditions and market clearing
(`price_crra_world_output_derived`).

**Exercise 6 (Lucas 1982).** (a) the finance constraint, feasibility of one-period
portfolio perturbations and the three Euler equations as first-order conditions;
(b) the no-trade equilibrium with `C_X = X/2`, `C_Y = Y/2`, `p = u_Y/u_X`, market clearing
and constant wealth shares; the no-trade plan is optimal over all admissible infinite plans
(concavity plus a transversality property proved from bounded holdings), and with strictly
concave `u` every equilibrium allocation is `(X/2, Y/2)`; (c) on a finite Markov chain
with `β < 1`, the claim prices are the (convergent) expected present values and the
unique stationary — and unique bounded history-dependent — solutions of their Euler
equations; (d) riskless and own-rates of interest, and multi-period bond prices.

**Exercise 3(a).** Quadratic utility discounted at `(1 + r)^{−1}`: the two-period
certainty-equivalent `C₁`, and over an infinite horizon on the tree the permanent-income
rule `C_t = [r/(1 + r)][(1 + r)B_t + Σ_k (1 + r)^{−k}E_t Y_{t+k}]`, derived from the Euler
equation, the budget constraint and the transversality condition; conversely the rule
satisfies the Euler equation and the transversality condition.
-/

namespace ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing

open Finset Filter Topology


variable {S : Type} [Fintype S]

/-- A stochastic process on the event tree (O&R §5.4.3, p. 315): a real number `f n h` at
every date-`(n + 1)` history `h : Fin n → S`. -/
abbrev TreeProcess (S : Type) : Type := (n : ℕ) → (Fin n → S) → ℝ

/-- The `k`-step conditional expectation `E_t[f_{t+k}]` on the event tree (O&R §5.4.3,
p. 316): at the history `h` of `n` events, average `f` over the continuations of `h` by `k`
further events, one step at a time, with the tree's one-step conditional probabilities
`q n h s = π(h, s | h)`. -/
noncomputable def condE (tr : EventTree.Tree S) (f : TreeProcess S) : ℕ → TreeProcess S
  | 0 => f
  | k + 1 => fun n h => ∑ s, tr.q n h s * condE tr f k (n + 1) (Fin.snoc h s)

namespace condE

variable (tr : EventTree.Tree S)

/-- `E_t[f_t] = f_t` (O&R §5.4.3, p. 316). -/
theorem zero_eq (f : TreeProcess S) : condE tr f 0 = f := rfl

/-- The defining recursion: `E_t[f_{t+k+1}] = Σ_s π(s|h) E_{t+1}[f_{t+k+1}](h, s)`
(O&R §5.4.3, p. 316). -/
theorem succ_eq (f : TreeProcess S) (k n : ℕ) (h : Fin n → S) :
    condE tr f (k + 1) n h = ∑ s, tr.q n h s * condE tr f k (n + 1) (Fin.snoc h s) := rfl

/-- The one-step conditional expectation `E_t[f_{t+1}] = Σ_s π(s|h) f(h, s)`
(O&R (57), p. 315). -/
theorem one_eq (f : TreeProcess S) (n : ℕ) (h : Fin n → S) :
    condE tr f 1 n h = ∑ s, tr.q n h s * f (n + 1) (Fin.snoc h s) := rfl

/-- The law of iterated expectations in its one-step form, `E_t[f_{t+k+1}] =
E_t[E_{t+k}[f_{t+k+1}]]` (O&R p. 316). -/
theorem succ_eq_iter (f : TreeProcess S) (k : ℕ) :
    condE tr f (k + 1) = condE tr (condE tr f 1) k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    funext n h
    rw [succ_eq, succ_eq, ih]

/-- The law of iterated expectations, `E_t[f_{t+j+k}] = E_t[E_{t+k}[f_{t+k+j}]]`
(O&R p. 316: "`E_t{E_{t+1}{X}} = E_t{X}`"). -/
theorem add_eq_iter (j : ℕ) : ∀ (f : TreeProcess S) (k : ℕ),
    condE tr f (j + k) = condE tr (condE tr f j) k := by
  induction j with
  | zero => intro f k; simp [zero_eq]
  | succ j ih =>
    intro f k
    rw [show j + 1 + k = (j + k) + 1 by omega, succ_eq_iter, ih, ← succ_eq_iter]

/-- Conditional expectation is additive (O&R p. 316). -/
theorem add_apply (f g : TreeProcess S) (k : ℕ) : ∀ (n : ℕ) (h : Fin n → S),
    condE tr (fun m x => f m x + g m x) k n h = condE tr f k n h + condE tr g k n h := by
  induction k with
  | zero => intro n h; rfl
  | succ k ih =>
    intro n h
    simp only [succ_eq, ih, mul_add, Finset.sum_add_distrib]

/-- Constants pass through conditional expectations (O&R p. 316). -/
theorem smul_apply (c : ℝ) (f : TreeProcess S) (k : ℕ) : ∀ (n : ℕ) (h : Fin n → S),
    condE tr (fun m x => c * f m x) k n h = c * condE tr f k n h := by
  induction k with
  | zero => intro n h; rfl
  | succ k ih =>
    intro n h
    simp only [succ_eq, ih, Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => by ring

/-- Conditional expectation is subtractive (O&R p. 316). -/
theorem sub_apply (f g : TreeProcess S) (k n : ℕ) (h : Fin n → S) :
    condE tr (fun m x => f m x - g m x) k n h = condE tr f k n h - condE tr g k n h := by
  have e : (fun m x => f m x - g m x) = fun m x => f m x + (-1) * g m x := by
    funext m x; ring
  rw [e, add_apply, smul_apply]
  ring

/-- The conditional expectation of a constant is that constant (O&R p. 316). -/
theorem const_apply (c : ℝ) (k : ℕ) : ∀ (n : ℕ) (h : Fin n → S),
    condE tr (fun _ _ => c) k n h = c := by
  induction k with
  | zero => intro n h; rfl
  | succ k ih =>
    intro n h
    simp only [succ_eq, ih, ← Finset.sum_mul, tr.q_sum, one_mul]

/-- Conditional expectation is monotone (O&R p. 316). -/
theorem mono_apply {f g : TreeProcess S} (hfg : ∀ n h, f n h ≤ g n h) (k : ℕ) :
    ∀ (n : ℕ) (h : Fin n → S), condE tr f k n h ≤ condE tr g k n h := by
  induction k with
  | zero => intro n h; exact hfg n h
  | succ k ih =>
    intro n h
    exact Finset.sum_le_sum fun s _ =>
      mul_le_mul_of_nonneg_left (ih _ _) (tr.q_nonneg _ _ _)

/-- A process bounded by `B` in absolute value has conditional expectations bounded by `B`
(O&R p. 316). -/
theorem abs_le_of_bound {f : TreeProcess S} {B : ℝ} (hf : ∀ n h, |f n h| ≤ B) (k n : ℕ)
    (h : Fin n → S) : |condE tr f k n h| ≤ B := by
  rw [_root_.abs_le]
  constructor
  · have := mono_apply tr (f := fun _ _ => -B) (g := f) (fun n h => (abs_le.mp (hf n h)).1) k n h
    rwa [const_apply] at this
  · have := mono_apply tr (f := f) (g := fun _ _ => B) (fun n h => (abs_le.mp (hf n h)).2) k n h
    rwa [const_apply] at this

/-- Nonnegative processes have nonnegative conditional expectations (O&R p. 316). -/
theorem nonneg_apply {f : TreeProcess S} (hf : ∀ n h, 0 ≤ f n h) (k n : ℕ) (h : Fin n → S) :
    0 ≤ condE tr f k n h := by
  have := mono_apply tr (f := fun _ _ => 0) (g := f) hf k n h
  rwa [const_apply] at this

end condE

/-- Appending an event multiplies the conditional probability by its one-step probability,
`π(h, s | h_m) = π(h | h_m)π(s | h)` (O&R Appendix 5C, p. 341, and footnote 53, p. 344). -/
theorem condProb_snoc (tr : EventTree.Tree S) {n : ℕ} (x : Fin n → S) (s : S) {m : ℕ}
    (hm : m ≤ n) :
    tr.condProb (Fin.snoc x s : Fin (n + 1) → S) m = tr.condProb x m * tr.q n x s := by
  unfold EventTree.Tree.condProb
  rw [Finset.prod_Ico_succ_top hm, tr.step_snoc_last]
  congr 1
  exact Finset.prod_congr rfl fun i hi => tr.step_snoc_lt x s (Finset.mem_Ico.mp hi).2

/-- **The recursive conditional expectation is the tree's conditional expectation**
(O&R §5.4.3, p. 316, with the probabilities of Appendix 5C, p. 341): `E_t[f_{t+k}]` at `h`
is the sum over all `k`-event continuations `g` of `π(h ++ g | h) f(h ++ g)`, where
`π(· | h)` is `Tree.condProb`. -/
theorem condE_eq_sum_condProb (tr : EventTree.Tree S) (f : TreeProcess S) (k : ℕ) :
    ∀ (n : ℕ) (h : Fin n → S), condE tr f k n h
      = ∑ g : Fin k → S, tr.condProb (Fin.append h g) n * f (n + k) (Fin.append h g) := by
  induction k generalizing f with
  | zero =>
    intro n h
    rw [Fintype.sum_unique]
    have e : (Fin.append h (default : Fin 0 → S) : Fin (n + 0) → S) = h := by
      funext i
      simp [Fin.append_right_nil]
    simp [e, EventTree.Tree.condProb, condE.zero_eq]
  | succ k ih =>
    intro n h
    rw [condE.succ_eq_iter, ih]
    rw [← (Fin.snocEquiv (fun _ : Fin (k + 1) => S)).sum_comp, Fintype.sum_prod_type,
      Finset.sum_comm]
    refine Finset.sum_congr rfl fun g _ => ?_
    have e : ∀ s : S, (Fin.snocEquiv fun _ : Fin (k + 1) => S) (s, g) = Fin.snoc g s :=
      fun _ => rfl
    simp only [e, Fin.append_snoc, condProb_snoc tr _ _ (Nat.le_add_right n k), condE.one_eq,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => (mul_assoc _ _ _).symm


/-! ## §5.4.3: the Euler equation (57) and forward iteration to (59) -/

/-- The equity Euler equation (57), O&R p. 315, on the event tree: at every history `h`,
`u′(C(h))V(h) = βΣ_s π(s|h) u′(C(h,s))(Y(h,s) + V(h,s))`, where `M = u′(C)` is the marginal
utility process, `Y` the dividend and `V` the ex-dividend price. -/
def EulerEq (tr : EventTree.Tree S) (β : ℝ) (M Y V : TreeProcess S) : Prop :=
  ∀ (n : ℕ) (h : Fin n → S), M n h * V n h =
    β * ∑ s, tr.q n h s * (M (n + 1) (Fin.snoc h s) *
      (Y (n + 1) (Fin.snoc h s) + V (n + 1) (Fin.snoc h s)))

/-- The `K`-term partial sum of marginal-utility-weighted discounted expected dividends in
(59), O&R p. 316: `Σ_{k=1}^{K} β^k E_t[u′(C_{t+k})Y_{t+k}]`. -/
noncomputable def pvPartial (tr : EventTree.Tree S) (β : ℝ) (M Y : TreeProcess S) (K n : ℕ)
    (h : Fin n → S) : ℝ :=
  ∑ k ∈ range K, β ^ (k + 1) * condE tr (fun m g => M m g * Y m g) (k + 1) n h

variable (tr : EventTree.Tree S)

/-- The Euler equation (57) in conditional-expectation form, O&R p. 316:
`u′(C_t)V_t = β(E_t[u′(C_{t+1})Y_{t+1}] + E_t[u′(C_{t+1})V_{t+1}])`. -/
theorem eulerEq_iff (β : ℝ) (M Y V : TreeProcess S) :
    EulerEq tr β M Y V ↔ (fun m g => M m g * V m g) = fun m g =>
      β * (condE tr (fun m g => M m g * Y m g) 1 m g
        + condE tr (fun m g => M m g * V m g) 1 m g) := by
  constructor
  · intro he
    funext n h
    rw [he n h, condE.one_eq, condE.one_eq, ← Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_congr rfl fun s _ => by ring
  · intro he n h
    have := congrFun (congrFun he n) h
    rw [this, condE.one_eq, condE.one_eq, ← Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_congr rfl fun s _ => by ring

/-- **Forward iteration of (57), O&R p. 316** (stochastic, `K` steps): if the Euler equation
holds at every history then, for every horizon `K`,
`u′(C_t)V_t = Σ_{k=1}^{K} β^k E_t[u′(C_{t+k})Y_{t+k}] + β^K E_t[u′(C_{t+K})V_{t+K}]`. -/
theorem mu_price_k_step {β : ℝ} {M Y V : TreeProcess S} (he : EulerEq tr β M Y V) (K : ℕ) :
    ∀ (n : ℕ) (h : Fin n → S), M n h * V n h = pvPartial tr β M Y K n h
      + β ^ K * condE tr (fun m g => M m g * V m g) K n h := by
  have hfun := (eulerEq_iff tr β M Y V).mp he
  induction K with
  | zero => intro n h; simp [pvPartial, condE.zero_eq]
  | succ K ih =>
    intro n h
    have key : condE tr (fun m g => M m g * V m g) K n h
        = β * (condE tr (fun m g => M m g * Y m g) (K + 1) n h
          + condE tr (fun m g => M m g * V m g) (K + 1) n h) := by
      rw [hfun, condE.smul_apply, condE.add_apply, ← condE.succ_eq_iter,
        ← condE.succ_eq_iter, ← hfun]
    rw [ih n h, key, pvPartial, pvPartial, Finset.sum_range_succ]
    ring

/-- **The `K`-step price identity, O&R p. 316**: with `u′(C_t) ≠ 0`, the price is the sum of
the first `K` discounted expected dividends, each valued at the marginal rate of substitution
`β^k u′(C_{t+k})/u′(C_t)`, plus the discounted expected price
`β^K E_t[u′(C_{t+K})V_{t+K}]/u′(C_t)`. -/
theorem price_k_step {β : ℝ} {M Y V : TreeProcess S} (he : EulerEq tr β M Y V) (K n : ℕ)
    (h : Fin n → S) (hM : M n h ≠ 0) :
    V n h = pvPartial tr β M Y K n h / M n h
      + β ^ K * condE tr (fun m g => M m g * V m g) K n h / M n h := by
  rw [← add_div, ← mu_price_k_step tr he K n h]
  field_simp

/-- **O&R (59), p. 316**: under the book's no-bubble condition
`lim_{T→∞} E_t{β^T[u′(C_{t+T})/u′(C_t)]V_{t+T}} = 0`, the price is the infinite sum of
discounted expected dividends,
`V_t = lim_K Σ_{k=1}^{K} β^k E_t[u′(C_{t+k})Y_{t+k}]/u′(C_t)` (the limit of partial sums, as
the book's `Σ_{s=t+1}^∞` means; no summability is assumed). -/
theorem price_eq_series {β : ℝ} {M Y V : TreeProcess S} (he : EulerEq tr β M Y V) (n : ℕ)
    (h : Fin n → S) (hM : M n h ≠ 0)
    (hnb : Tendsto (fun K => β ^ K * condE tr (fun m g => M m g * V m g) K n h / M n h)
      atTop (𝓝 0)) :
    Tendsto (fun K => pvPartial tr β M Y K n h / M n h) atTop (𝓝 (V n h)) := by
  have e : (fun K => pvPartial tr β M Y K n h / M n h) = fun K =>
      V n h - β ^ K * condE tr (fun m g => M m g * V m g) K n h / M n h := by
    funext K
    rw [price_k_step tr he K n h hM]
    ring
  rw [e]
  simpa using (tendsto_const_nhds (x := V n h)).sub hnb

/-- **O&R (59), p. 316, as a sum**: when dividends and marginal utilities are nonnegative
(`u′(C)Y ≥ 0`), `β ≥ 0` and `u′(C_t) > 0`, the no-bubble condition gives
`V_t = Σ_{k≥1} β^k E_t[u′(C_{t+k})Y_{t+k}]/u′(C_t)` as a genuine (absolutely convergent)
series; summability is derived, not assumed. -/
theorem price_hasSum {β : ℝ} (hβ : 0 ≤ β) {M Y V : TreeProcess S} (he : EulerEq tr β M Y V)
    (hD : ∀ m g, 0 ≤ M m g * Y m g) (n : ℕ) (h : Fin n → S) (hM : 0 < M n h)
    (hnb : Tendsto (fun K => β ^ K * condE tr (fun m g => M m g * V m g) K n h / M n h)
      atTop (𝓝 0)) :
    HasSum (fun k => β ^ (k + 1) * condE tr (fun m g => M m g * Y m g) (k + 1) n h / M n h)
      (V n h) := by
  rw [hasSum_iff_tendsto_nat_of_nonneg]
  · have := price_eq_series tr he n h hM.ne' hnb
    simpa [pvPartial, Finset.sum_div] using this
  · intro k
    exact div_nonneg (mul_nonneg (pow_nonneg hβ _) (condE.nonneg_apply tr hD _ _ _)) hM.le

/-- The recursion of the partial sums, O&R p. 316: `P_{K+1}(h) = βΣ_s π(s|h)
[u′(C(h,s))Y(h,s) + P_K(h,s)]`, where `P_K` is `pvPartial` with `K` terms. -/
theorem pvPartial_succ (β : ℝ) (M Y : TreeProcess S) (K n : ℕ) (h : Fin n → S) :
    pvPartial tr β M Y (K + 1) n h = β * ∑ s, tr.q n h s *
      (M (n + 1) (Fin.snoc h s) * Y (n + 1) (Fin.snoc h s)
        + pvPartial tr β M Y K (n + 1) (Fin.snoc h s)) := by
  simp only [pvPartial, Finset.sum_range_succ', condE.succ_eq, Finset.mul_sum, mul_add,
    Finset.sum_add_distrib, condE.zero_eq]
  rw [Finset.sum_comm, add_comm]
  congr 1
  · refine Finset.sum_congr rfl fun s _ => ?_
    ring
  · refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun k _ => ?_
    ring_nf

/-- The limit of the present-value series satisfies the Euler recursion, O&R p. 316: if at
every history the partial sums converge to `F`, then
`F(h) = βΣ_s π(s|h)[u′(C(h,s))Y(h,s) + F(h,s)]`. -/
theorem series_limit_recursion {β : ℝ} {M Y F : TreeProcess S}
    (hF : ∀ n h, Tendsto (fun K => pvPartial tr β M Y K n h) atTop (𝓝 (F n h))) (n : ℕ)
    (h : Fin n → S) :
    F n h = β * ∑ s, tr.q n h s * (M (n + 1) (Fin.snoc h s) * Y (n + 1) (Fin.snoc h s)
      + F (n + 1) (Fin.snoc h s)) := by
  have h1 : Tendsto (fun K => pvPartial tr β M Y (K + 1) n h) atTop (𝓝 (F n h)) :=
    (tendsto_add_atTop_iff_nat 1).mpr (hF n h)
  have h2 : Tendsto (fun K => pvPartial tr β M Y (K + 1) n h) atTop
      (𝓝 (β * ∑ s, tr.q n h s * (M (n + 1) (Fin.snoc h s) * Y (n + 1) (Fin.snoc h s)
        + F (n + 1) (Fin.snoc h s)))) := by
    simp_rw [pvPartial_succ]
    exact tendsto_const_nhds.mul (tendsto_finsetSum _ fun s _ =>
      tendsto_const_nhds.mul (tendsto_const_nhds.add (hF _ _)))
  exact tendsto_nhds_unique h1 h2

/-- **Existence, O&R (59), p. 316, converse**: if the present-value series converges at every
history (to `F`) and marginal utility never vanishes, then `V = F/u′(C)` satisfies the Euler
equation (57) at every history. -/
theorem euler_of_series {β : ℝ} {M Y F : TreeProcess S} (hM : ∀ n h, M n h ≠ 0)
    (hF : ∀ n h, Tendsto (fun K => pvPartial tr β M Y K n h) atTop (𝓝 (F n h))) :
    EulerEq tr β M Y (fun n h => F n h / M n h) := by
  intro n h
  rw [mul_div_cancel₀ _ (hM n h), series_limit_recursion tr hF n h]
  congr 1
  refine Finset.sum_congr rfl fun s _ => ?_
  have := hM (n + 1) (Fin.snoc h s)
  field_simp

/-- **Bubbles are discounted-marginal-utility martingales, O&R p. 316**: if `V` solves the
Euler equation and the present-value series converges to `F` at every history, the bubble
`b = u′(C)V − F` satisfies `b(h) = βΣ_s π(s|h) b(h,s)`, i.e. `β^t u′(C_t)(V_t − F_t/u′(C_t))`
is a martingale. -/
theorem bubble_recursion {β : ℝ} {M Y V F : TreeProcess S} (he : EulerEq tr β M Y V)
    (hF : ∀ n h, Tendsto (fun K => pvPartial tr β M Y K n h) atTop (𝓝 (F n h))) (n : ℕ)
    (h : Fin n → S) :
    M n h * V n h - F n h = β * ∑ s, tr.q n h s *
      (M (n + 1) (Fin.snoc h s) * V (n + 1) (Fin.snoc h s) - F (n + 1) (Fin.snoc h s)) := by
  rw [he n h, series_limit_recursion tr hF n h, ← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  exact Finset.sum_congr rfl fun s _ => by ring

/-- **The bubble term, O&R p. 316**: if `V` solves the Euler equation and the present-value
series converges to `F`, then `β^K E_t[u′(C_{t+K})V_{t+K}] → u′(C_t)V_t − F_t`: the limit in
the no-bubble condition is exactly the bubble component of the price. -/
theorem bubble_tendsto {β : ℝ} {M Y V F : TreeProcess S} (he : EulerEq tr β M Y V)
    (hF : ∀ n h, Tendsto (fun K => pvPartial tr β M Y K n h) atTop (𝓝 (F n h))) (n : ℕ)
    (h : Fin n → S) :
    Tendsto (fun K => β ^ K * condE tr (fun m g => M m g * V m g) K n h) atTop
      (𝓝 (M n h * V n h - F n h)) := by
  have e : (fun K => β ^ K * condE tr (fun m g => M m g * V m g) K n h)
      = fun K => M n h * V n h - pvPartial tr β M Y K n h := by
    funext K
    rw [mu_price_k_step tr he K n h]
    ring
  rw [e]
  exact (tendsto_const_nhds).sub (hF n h)

/-- **Uniqueness iff no bubble, O&R p. 316**: for an Euler solution `V`, with the series
converging to `F` and `u′(C_t) ≠ 0`, the price equals the fundamental `F_t/u′(C_t)` if and
only if the book's no-bubble condition holds at `h`. -/
theorem price_eq_fundamental_iff {β : ℝ} {M Y V F : TreeProcess S} (he : EulerEq tr β M Y V)
    (hF : ∀ n h, Tendsto (fun K => pvPartial tr β M Y K n h) atTop (𝓝 (F n h))) (n : ℕ)
    (h : Fin n → S) (hM : M n h ≠ 0) :
    V n h = F n h / M n h ↔
      Tendsto (fun K => β ^ K * condE tr (fun m g => M m g * V m g) K n h / M n h)
        atTop (𝓝 0) := by
  have hb := (bubble_tendsto tr he hF n h).div_const (M n h)
  constructor
  · intro hV
    have e : (M n h * V n h - F n h) / M n h = 0 := by
      rw [hV]; field_simp; ring
    rwa [e] at hb
  · intro hnb
    have e := tendsto_nhds_unique hb hnb
    rw [div_eq_zero_iff] at e
    rcases e with e | e
    · rw [eq_div_iff hM]; linarith
    · exact absurd e hM

/-- **Uniqueness under no bubbles, O&R p. 316**: two solutions of the Euler equation that
both satisfy the no-bubble condition at `h` (with `u′(C_t) ≠ 0`) have the same price at `h`;
no convergence of the series is assumed (it follows). -/
theorem price_unique_of_noBubble {β : ℝ} {M Y V W : TreeProcess S}
    (hV : EulerEq tr β M Y V) (hW : EulerEq tr β M Y W) (n : ℕ) (h : Fin n → S)
    (hM : M n h ≠ 0)
    (hnV : Tendsto (fun K => β ^ K * condE tr (fun m g => M m g * V m g) K n h / M n h)
      atTop (𝓝 0))
    (hnW : Tendsto (fun K => β ^ K * condE tr (fun m g => M m g * W m g) K n h / M n h)
      atTop (𝓝 0)) :
    V n h = W n h :=
  tendsto_nhds_unique (price_eq_series tr hV n h hM hnV) (price_eq_series tr hW n h hM hnW)

/-- **Adding a bubble, O&R p. 316**: if `V` solves the Euler equation and `b` satisfies the
martingale recursion `b(h) = βΣ_s π(s|h) b(h,s)`, then `V + b/u′(C)` also solves it. -/
theorem euler_add_bubble {β : ℝ} {M Y V : TreeProcess S} (he : EulerEq tr β M Y V)
    (hM : ∀ n h, M n h ≠ 0) (b : TreeProcess S)
    (hb : ∀ n h, b n h = β * ∑ s, tr.q n h s * b (n + 1) (Fin.snoc h s)) :
    EulerEq tr β M Y (fun n h => V n h + b n h / M n h) := by
  intro n h
  have e1 : M n h * (V n h + b n h / M n h) = M n h * V n h + b n h := by
    field_simp [hM n h]
  rw [e1, he n h, hb n h, ← mul_add, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun s _ => ?_
  have := hM (n + 1) (Fin.snoc h s)
  field_simp
  ring

/-- **Without the no-bubble condition prices are not unique, O&R p. 316**: for `β > 0` and
any `c ≠ 0`, the deterministic bubble `b_t = c/β^{t−1}` satisfies the martingale recursion,
so `V + b/u′(C)` is a second Euler solution differing from `V` at every history. -/
theorem euler_nonunique_without_noBubble {β : ℝ} (hβ : 0 < β) {M Y V : TreeProcess S}
    (he : EulerEq tr β M Y V) (hM : ∀ n h, M n h ≠ 0) {c : ℝ} (hc : c ≠ 0) :
    EulerEq tr β M Y (fun n h => V n h + c / β ^ n / M n h) ∧
      ∀ n h, V n h + c / β ^ n / M n h ≠ V n h := by
  refine ⟨euler_add_bubble tr he hM (fun n _ => c / β ^ n) fun n h => ?_, fun n h => ?_⟩
  · rw [← Finset.sum_mul, tr.q_sum, one_mul, pow_succ]
    field_simp
  · have : c / β ^ n / M n h ≠ 0 :=
      div_ne_zero (div_ne_zero hc (pow_ne_zero _ hβ.ne')) (hM n h)
    intro hh
    exact this (by linarith)

/-! ## Deriving the no-bubble condition from primitives -/

/-- **The no-bubble condition from boundedness, O&R p. 316**: if marginal-utility-weighted
prices `u′(C)V` are bounded over the tree and `0 ≤ β < 1`, then
`β^K E_t[u′(C_{t+K})V_{t+K}]/u′(C_t) → 0`. -/
theorem noBubble_of_bounded {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {M V : TreeProcess S}
    {B : ℝ} (hB : ∀ n h, |M n h * V n h| ≤ B) (n : ℕ) (h : Fin n → S) :
    Tendsto (fun K => β ^ K * condE tr (fun m g => M m g * V m g) K n h / M n h) atTop
      (𝓝 0) := by
  have hlim : Tendsto (fun K : ℕ => β ^ K * B / |M n h|) atTop (𝓝 0) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 hβ1).mul_const B).div_const
      |M n h|
  refine squeeze_zero_norm (fun K => ?_) hlim
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_pow, abs_of_nonneg hβ0]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
    (condE.abs_le_of_bound tr hB K n h) (pow_nonneg hβ0 K)) (abs_nonneg _)

/-- **Convergence of the present-value series, O&R (59), p. 316**: if marginal-utility-weighted
dividends `u′(C)Y` are bounded by `B` and `0 ≤ β < 1`, the series
`Σ_{k≥1} β^k E_t[u′(C_{t+k})Y_{t+k}]` is (absolutely) summable at every history. -/
theorem series_summable_of_bounded {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {M Y : TreeProcess S}
    {B : ℝ} (hB : ∀ n h, |M n h * Y n h| ≤ B) (n : ℕ) (h : Fin n → S) :
    Summable (fun k => β ^ (k + 1) * condE tr (fun m g => M m g * Y m g) (k + 1) n h) := by
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hβ0 hβ1).mul_left (β * B))
    fun k => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hβ0]
  calc β ^ (k + 1) * |condE tr (fun m g => M m g * Y m g) (k + 1) n h|
      ≤ β ^ (k + 1) * B :=
        mul_le_mul_of_nonneg_left (condE.abs_le_of_bound tr hB _ n h) (pow_nonneg hβ0 _)
    _ = β * B * β ^ k := by ring

/-- The marginal-utility-weighted fundamental value `F_t = Σ_{k≥1} β^k E_t[u′(C_{t+k})Y_{t+k}]`,
O&R (59), p. 316 (a `tsum`; used only where summability is proved). -/
noncomputable def fundamentalMU (tr : EventTree.Tree S) (β : ℝ) (M Y : TreeProcess S) (n : ℕ)
    (h : Fin n → S) : ℝ :=
  ∑' k, β ^ (k + 1) * condE tr (fun m g => M m g * Y m g) (k + 1) n h

/-- The partial sums converge to the fundamental value when `u′(C)Y` is bounded and
`0 ≤ β < 1` (O&R (59), p. 316). -/
theorem fundamentalMU_tendsto {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {M Y : TreeProcess S}
    {B : ℝ} (hB : ∀ n h, |M n h * Y n h| ≤ B) (n : ℕ) (h : Fin n → S) :
    Tendsto (fun K => pvPartial tr β M Y K n h) atTop (𝓝 (fundamentalMU tr β M Y n h)) :=
  (series_summable_of_bounded tr hβ0 hβ1 hB n h).hasSum.tendsto_sum_nat

/-- The fundamental value is bounded, `|F_t| ≤ βB/(1 − β)`, when `|u′(C)Y| ≤ B` and
`0 ≤ β < 1` (O&R (59), p. 316). -/
theorem fundamentalMU_abs_le {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {M Y : TreeProcess S}
    {B : ℝ} (hB : ∀ n h, |M n h * Y n h| ≤ B) (n : ℕ) (h : Fin n → S) :
    |fundamentalMU tr β M Y n h| ≤ β * B / (1 - β) := by
  have hf := (series_summable_of_bounded tr hβ0 hβ1 hB n h).hasSum
  have hg := (hasSum_geometric_of_lt_one hβ0 hβ1).mul_left (β * B)
  have hle : ∀ k, |β ^ (k + 1) * condE tr (fun m g => M m g * Y m g) (k + 1) n h|
      ≤ β * B * β ^ k := by
    intro k
    rw [abs_mul, abs_pow, abs_of_nonneg hβ0]
    calc β ^ (k + 1) * |condE tr (fun m g => M m g * Y m g) (k + 1) n h|
        ≤ β ^ (k + 1) * B :=
          mul_le_mul_of_nonneg_left (condE.abs_le_of_bound tr hB _ n h) (pow_nonneg hβ0 _)
      _ = β * B * β ^ k := by ring
  rw [div_eq_mul_inv, _root_.abs_le]
  exact ⟨hasSum_le (fun k => by linarith [(_root_.abs_le.mp (hle k)).1]) hg.neg hf,
    hasSum_le (fun k => (_root_.abs_le.mp (hle k)).2) hf hg⟩

/-- **Existence and uniqueness of the bounded price, O&R (57)–(59), p. 316**. Suppose
`0 ≤ β < 1`, marginal utility is positive and `u′(C)Y` is bounded by `B`. Then the series
price `V = F/u′(C)` (with `F` the fundamental value, whose convergence is proved) solves the
Euler equation (57) at every history, `u′(C)V` is bounded by `βB/(1 − β)`, and every Euler
solution with bounded `u′(C)V` equals it: the no-bubble condition is derived from
boundedness. -/
theorem unique_bounded_price {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {M Y : TreeProcess S}
    (hM : ∀ n h, 0 < M n h) {B : ℝ} (hB : ∀ n h, |M n h * Y n h| ≤ B) :
    EulerEq tr β M Y (fun n h => fundamentalMU tr β M Y n h / M n h) ∧
      (∀ n h, |M n h * (fundamentalMU tr β M Y n h / M n h)| ≤ β * B / (1 - β)) ∧
      ∀ V : TreeProcess S, EulerEq tr β M Y V → (∃ B', ∀ n h, |M n h * V n h| ≤ B') →
        V = fun n h => fundamentalMU tr β M Y n h / M n h := by
  refine ⟨euler_of_series tr (fun n h => (hM n h).ne')
    (fundamentalMU_tendsto tr hβ0 hβ1 hB), fun n h => ?_, fun V hV ⟨B', hB'⟩ => ?_⟩
  · rw [mul_div_cancel₀ _ (hM n h).ne']
    exact fundamentalMU_abs_le tr hβ0 hβ1 hB n h
  · funext n h
    exact tendsto_nhds_unique
      (price_eq_series tr hV n h (hM n h).ne' (noBubble_of_bounded tr hβ0 hβ1 hB' n h))
      ((fundamentalMU_tendsto tr hβ0 hβ1 hB n h).div_const _)

/-- **Bounded prices are unique, O&R p. 316**: if `0 ≤ β < 1` and marginal utility lies in
`(0, M̄]`, any two Euler solutions with bounded prices coincide. -/
theorem bounded_prices_unique {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {M Y V W : TreeProcess S}
    {Mbar BV BW : ℝ} (hM : ∀ n h, 0 < M n h) (hMb : ∀ n h, M n h ≤ Mbar)
    (hV : EulerEq tr β M Y V) (hW : EulerEq tr β M Y W) (hBV : ∀ n h, |V n h| ≤ BV)
    (hBW : ∀ n h, |W n h| ≤ BW) : V = W := by
  have bnd : ∀ (Z : TreeProcess S) (BZ : ℝ), (∀ n h, |Z n h| ≤ BZ) →
      ∀ n h, |M n h * Z n h| ≤ Mbar * BZ := by
    intro Z BZ hZ n h
    rw [abs_mul, abs_of_pos (hM n h)]
    exact mul_le_mul (hMb n h) (hZ n h) (abs_nonneg _) ((hM n h).le.trans (hMb n h))
  funext n h
  exact price_unique_of_noBubble tr hV hW n h (hM n h).ne'
    (noBubble_of_bounded tr hβ0 hβ1 (bnd V BV hBV) n h)
    (noBubble_of_bounded tr hβ0 hβ1 (bnd W BW hBW) n h)

/-! ## (60): riskless discounting plus covariance terms -/

/-- The market discount factor (60), O&R p. 317: `R_{t,t+k} = E_t[β^k u′(C_{t+k})/u′(C_t)]`,
the date-`t` price of a unit of date-`t+k` consumption delivered for sure. -/
noncomputable def discountR (tr : EventTree.Tree S) (β : ℝ) (M : TreeProcess S) (k n : ℕ)
    (h : Fin n → S) : ℝ :=
  β ^ k * condE tr M k n h / M n h

/-- The `k`-step conditional covariance `Cov_t(X_{t+k}, Z_{t+k}) = E_t[XZ] − E_t[X]E_t[Z]`
(O&R (59), p. 316). -/
noncomputable def condCov (tr : EventTree.Tree S) (k : ℕ) (X Z : TreeProcess S) (n : ℕ)
    (h : Fin n → S) : ℝ :=
  condE tr (fun m g => X m g * Z m g) k n h - condE tr X k n h * condE tr Z k n h

/-- **One term of (59), O&R pp. 316–317**: the value of the date-`t+k` dividend is its
expectation discounted at the riskless rate plus a covariance with the marginal rate of
substitution,
`E_t[β^k u′(C_{t+k})Y_{t+k}]/u′(C_t) = R_{t,t+k}E_t[Y_{t+k}]
  + Cov_t(β^k u′(C_{t+k})/u′(C_t), Y_{t+k})`. -/
theorem value_term_decomposition (β : ℝ) (M Y : TreeProcess S) (k n : ℕ) (h : Fin n → S) :
    β ^ k * condE tr (fun m g => M m g * Y m g) k n h / M n h
      = discountR tr β M k n h * condE tr Y k n h
        + condCov tr k (fun m g => β ^ k * M m g / M n h) Y n h := by
  have e1 : condE tr (fun m g => β ^ k * M m g / M n h * Y m g) k n h
      = β ^ k / M n h * condE tr (fun m g => M m g * Y m g) k n h := by
    rw [← condE.smul_apply]
    congr 1
    funext m g
    ring
  have e2 : condE tr (fun m g => β ^ k * M m g / M n h) k n h
      = β ^ k / M n h * condE tr M k n h := by
    rw [← condE.smul_apply]
    congr 1
    funext m g
    ring
  rw [condCov, e1, e2, discountR]
  ring

/-- **O&R footnote 44, p. 317**: a riskless `k`-period discount bond (paying one unit after
`k` periods, `b_0 = 1`) priced by the Euler equation
`u′(C_t)b_{k+1,t} = βE_t[u′(C_{t+1})b_{k,t+1}]` has price `R_{t,t+k}` of (60), i.e.
`R_{t,t+k}u′(C_t) = β^k E_t[u′(C_{t+k})]`. -/
theorem bond_price_eq_discountR {β : ℝ} {M : TreeProcess S} (hM : ∀ n h, M n h ≠ 0)
    (b : ℕ → TreeProcess S) (hb0 : ∀ n h, b 0 n h = 1)
    (hb : ∀ k n (h : Fin n → S), M n h * b (k + 1) n h =
      β * ∑ s, tr.q n h s * (M (n + 1) (Fin.snoc h s) * b k (n + 1) (Fin.snoc h s))) :
    ∀ k n h, b k n h = discountR tr β M k n h := by
  intro k
  induction k with
  | zero => intro n h; rw [hb0, discountR, pow_zero, one_mul, condE.zero_eq, div_self (hM n h)]
  | succ k ih =>
    intro n h
    have e : ∀ s, M (n + 1) (Fin.snoc h s) * b k (n + 1) (Fin.snoc h s)
        = β ^ k * condE tr M k (n + 1) (Fin.snoc h s) := by
      intro s
      rw [ih, discountR]
      field_simp [hM (n + 1) (Fin.snoc h s)]
    rw [discountR, eq_div_iff (hM n h), mul_comm, hb]
    simp only [e, condE.succ_eq, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    ring

/-- **O&R (59) second line, p. 316**: under the no-bubble condition the price is the sum of
expected dividends discounted at the riskless market discount factors (60) plus the sum of
the covariance risk adjustments,
`V_t = Σ_{s>t} R_{t,s}E_t[Y_s] + Σ_{s>t} Cov_t(β^{s−t}u′(C_s)/u′(C_t), Y_s)`
(as a limit of partial sums). -/
theorem price_eq_riskless_plus_cov {β : ℝ} {M Y V : TreeProcess S} (he : EulerEq tr β M Y V)
    (n : ℕ) (h : Fin n → S) (hM : M n h ≠ 0)
    (hnb : Tendsto (fun K => β ^ K * condE tr (fun m g => M m g * V m g) K n h / M n h)
      atTop (𝓝 0)) :
    Tendsto (fun K => ∑ k ∈ range K, (discountR tr β M (k + 1) n h * condE tr Y (k + 1) n h
      + condCov tr (k + 1) (fun m g => β ^ (k + 1) * M m g / M n h) Y n h)) atTop
      (𝓝 (V n h)) := by
  have e : (fun K => ∑ k ∈ range K, (discountR tr β M (k + 1) n h * condE tr Y (k + 1) n h
      + condCov tr (k + 1) (fun m g => β ^ (k + 1) * M m g / M n h) Y n h))
      = fun K => pvPartial tr β M Y K n h / M n h := by
    funext K
    rw [pvPartial, Finset.sum_div]
    exact Finset.sum_congr rfl fun k _ => (value_term_decomposition tr β M Y (k + 1) n h).symm
  rw [e]
  exact price_eq_series tr he n h hM hnb

/-! ## (61): CRRA utility and constant consumption shares -/

/-- With CRRA marginal utility `u′(C) = C^{−ρ}` and `C = μY^W` (`μ > 0`, `Y^W > 0`), the
marginal rate of substitution is `(Y^W_{t+k}/Y^W_t)^{−ρ}`, O&R (61), p. 317:
`β^k E_t[u′(C_{t+k})Y_{t+k}]/u′(C_t) = β^k E_t[(Y^W_{t+k}/Y^W_t)^{−ρ}Y_{t+k}]`. -/
theorem crra_value_term {μ ρ : ℝ} (hμ : 0 < μ) {YW : TreeProcess S}
    (hYW : ∀ n h, 0 < YW n h) (β : ℝ) (Y : TreeProcess S) (k n : ℕ) (h : Fin n → S) :
    β ^ k * condE tr (fun m g => (μ * YW m g) ^ (-ρ) * Y m g) k n h / (μ * YW n h) ^ (-ρ)
      = β ^ k * condE tr (fun m g => (YW m g / YW n h) ^ (-ρ) * Y m g) k n h := by
  have hpos : 0 < (μ * YW n h) ^ (-ρ) := Real.rpow_pos_of_pos (mul_pos hμ (hYW n h)) _
  have hpos' : 0 < YW n h ^ (-ρ) := Real.rpow_pos_of_pos (hYW n h) _
  have key : (fun m g => (μ * YW m g) ^ (-ρ) * Y m g)
      = fun m g => (μ * YW n h) ^ (-ρ) * ((YW m g / YW n h) ^ (-ρ) * Y m g) := by
    funext m g
    rw [Real.mul_rpow hμ.le (hYW m g).le, Real.mul_rpow hμ.le (hYW n h).le,
      Real.div_rpow (hYW m g).le (hYW n h).le]
    field_simp
  rw [key, condE.smul_apply]
  field_simp

/-- **O&R (61), p. 317** (stochastic, infinite horizon): with CRRA utility, consumption a
constant share `μ > 0` of world output `Y^W > 0`, the Euler equation (57) at every history and
the no-bubble condition, `V_t = Σ_{s>t} β^{s−t}E_t[(Y^W_s/Y^W_t)^{−ρ}Y_s]`. -/
theorem price_crra_world_output_tree {β μ ρ : ℝ} (hμ : 0 < μ) {YW Y V : TreeProcess S}
    (hYW : ∀ n h, 0 < YW n h) (he : EulerEq tr β (fun m g => (μ * YW m g) ^ (-ρ)) Y V)
    (n : ℕ) (h : Fin n → S)
    (hnb : Tendsto (fun K => β ^ K * condE tr (fun m g => (μ * YW m g) ^ (-ρ) * V m g) K n h
      / (μ * YW n h) ^ (-ρ)) atTop (𝓝 0)) :
    Tendsto (fun K => ∑ k ∈ range K,
      β ^ (k + 1) * condE tr (fun m g => (YW m g / YW n h) ^ (-ρ) * Y m g) (k + 1) n h)
      atTop (𝓝 (V n h)) := by
  have hM : (μ * YW n h) ^ (-ρ) ≠ 0 := (Real.rpow_pos_of_pos (mul_pos hμ (hYW n h)) _).ne'
  have := price_eq_series tr he n h hM hnb
  simp only [pvPartial, Finset.sum_div] at this
  simpa only [crra_value_term tr hμ hYW] using this

/-- **O&R (59)–(60) at a finite horizon, pp. 316–317**: for every horizon `K`, the price is
the sum over the first `K` dates of riskless-discounted expected dividends plus covariance
terms, plus the discounted expected resale value:
`V_t = Σ_{k=1}^{K}[R_{t,t+k}E_t Y_{t+k} + Cov_t(β^k u′(C_{t+k})/u′(C_t), Y_{t+k})]
  + β^K E_t[u′(C_{t+K})V_{t+K}]/u′(C_t)`. -/
theorem price_k_step_riskless_cov {β : ℝ} {M Y V : TreeProcess S} (he : EulerEq tr β M Y V)
    (K n : ℕ) (h : Fin n → S) (hM : M n h ≠ 0) :
    V n h = ∑ k ∈ range K, (discountR tr β M (k + 1) n h * condE tr Y (k + 1) n h
      + condCov tr (k + 1) (fun m g => β ^ (k + 1) * M m g / M n h) Y n h)
      + β ^ K * condE tr (fun m g => M m g * V m g) K n h / M n h := by
  rw [price_k_step tr he K n h hM, pvPartial, Finset.sum_div]
  congr 1
  exact Finset.sum_congr rfl fun k _ => value_term_decomposition tr β M Y (k + 1) n h

/-- **O&R (61), p. 317, with the no-bubble condition derived**: with CRRA utility (`ρ > 0`),
`C = μY^W` (`μ > 0`), world output bounded away from zero (`Y^W ≥ a > 0`) and `0 ≤ β < 1`,
every bounded price process solving the Euler equation (57) satisfies
`V_t = Σ_{s>t} β^{s−t}E_t[(Y^W_s/Y^W_t)^{−ρ}Y_s]`. -/
theorem price_crra_world_output_bounded {β μ ρ a BV : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hμ : 0 < μ) (hρ : 0 < ρ) (ha : 0 < a) {YW Y V : TreeProcess S}
    (hYW : ∀ n h, a ≤ YW n h) (he : EulerEq tr β (fun m g => (μ * YW m g) ^ (-ρ)) Y V)
    (hV : ∀ n h, |V n h| ≤ BV) (n : ℕ) (h : Fin n → S) :
    Tendsto (fun K => ∑ k ∈ range K,
      β ^ (k + 1) * condE tr (fun m g => (YW m g / YW n h) ^ (-ρ) * Y m g) (k + 1) n h)
      atTop (𝓝 (V n h)) := by
  have hYW' : ∀ n h, 0 < YW n h := fun n h => lt_of_lt_of_le ha (hYW n h)
  have hB : ∀ n h, |(μ * YW n h) ^ (-ρ) * V n h| ≤ (μ * a) ^ (-ρ) * BV := by
    intro n h
    rw [abs_mul, abs_of_pos (Real.rpow_pos_of_pos (mul_pos hμ (hYW' n h)) _)]
    exact mul_le_mul (Real.rpow_le_rpow_of_nonpos (mul_pos hμ ha)
      (mul_le_mul_of_nonneg_left (hYW n h) hμ.le) (by linarith)) (hV n h) (abs_nonneg _)
      (Real.rpow_pos_of_pos (mul_pos hμ ha) _).le
  exact price_crra_world_output_tree tr hμ hYW' he n h
    (noBubble_of_bounded tr hβ0 hβ1 hB n h)

/-! ## First-order conditions from one-period portfolio perturbations -/

/-- **Euler equations from a one-period perturbation, O&R (56)–(58), p. 315**. Buying `ε`
more units of an asset at price `a` lowers today's consumption to `c₀ − εa` and raises
consumption in each state `s` tomorrow to `c₁(s) + εz(s)`, where `z` is the asset's payoff
(dividend plus resale price). If the optimal plan is not improved by any small such
perturbation (a local maximum at `ε = 0` of today's utility plus discounted expected utility
tomorrow — implied by optimality of the plan), and the period utilities are differentiable,
then `u′₀ a = βΣ_s π(s) u′₁(s) z(s)`. -/
theorem euler_of_isLocalMax {U0 : ℝ → ℝ} {U1 : S → ℝ → ℝ} {d0 c0 : ℝ} {d1 c1 : S → ℝ}
    (h0 : HasDerivAt U0 d0 c0) (h1 : ∀ s, HasDerivAt (U1 s) (d1 s) (c1 s)) (β : ℝ)
    (π : S → ℝ) (a : ℝ) (z : S → ℝ)
    (hmax : IsLocalMax (fun ε => U0 (c0 - ε * a) + β * ∑ s, π s * U1 s (c1 s + ε * z s)) 0) :
    d0 * a = β * ∑ s, π s * (d1 s * z s) := by
  have hin0 : HasDerivAt (fun ε : ℝ => c0 - ε * a) (-a) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const a).const_sub c0
  have hin1 : ∀ s, HasDerivAt (fun ε : ℝ => c1 s + ε * z s) (z s) 0 := fun s => by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (z s)).const_add (c1 s)
  have hd0 := h0.comp_of_eq 0 hin0 (by simp)
  have hd1 : ∀ s, HasDerivAt (fun ε => π s * U1 s (c1 s + ε * z s)) (π s * (d1 s * z s)) 0 :=
    fun s => ((h1 s).comp_of_eq 0 (hin1 s) (by simp)).const_mul (π s)
  have hd := hd0.add ((HasDerivAt.fun_sum (u := Finset.univ) fun s _ => hd1 s).const_mul β)
  have := hmax.hasDerivAt_eq_zero hd
  linarith

/-! ## Exercise 6: the Lucas (1982) two-good model -/

/-- The finance constraint of Exercise 6(a), O&R p. 347 (the two-risky-asset version of (56),
p. 315): bonds `B′` and shares `x′, y′` of the Home and Foreign output claims bought at the
ex-dividend prices `V_X, V_Y` are paid for by gross bond income `(1 + r)B`, the dividends plus
resale value of the shares `x, y` held (Foreign's dividend is `pY` in units of `X`), less
consumption spending `C_X + pC_Y`. -/
def lucasFinance (r B x y VX VY X Y p CX CY B' x' y' : ℝ) : Prop :=
  B' + x' * VX + y' * VY = (1 + r) * B + x * (X + VX) + y * (p * Y + VY) - CX - p * CY

/-- **Feasible perturbations, Exercise 6(a), O&R p. 347**: if a plan satisfies the finance
constraint today and in some state tomorrow, then buying `ε` more of the Home claim (paid
from today's `X` consumption, resold tomorrow with its dividend), or of the Foreign claim, or
of the bond, gives a plan that again satisfies both constraints, with later holdings
unchanged. -/
theorem lucas_perturbation_feasible {r B x y VX VY X Y p CX CY B' x' y' r' VX' VY' X' Y' p'
    CX' CY' B'' x'' y'' : ℝ} (ht : lucasFinance r B x y VX VY X Y p CX CY B' x' y')
    (ht1 : lucasFinance r' B' x' y' VX' VY' X' Y' p' CX' CY' B'' x'' y'') (ε : ℝ) :
    (lucasFinance r B x y VX VY X Y p (CX - ε * VX) CY B' (x' + ε) y' ∧
      lucasFinance r' B' (x' + ε) y' VX' VY' X' Y' p' (CX' + ε * (X' + VX')) CY' B'' x'' y'')
    ∧ (lucasFinance r B x y VX VY X Y p (CX - ε * VY) CY B' x' (y' + ε) ∧
      lucasFinance r' B' x' (y' + ε) VX' VY' X' Y' p' (CX' + ε * (p' * Y' + VY')) CY' B''
        x'' y'')
    ∧ (lucasFinance r B x y VX VY X Y p (CX - ε * 1) CY (B' + ε) x' y' ∧
      lucasFinance r' (B' + ε) x' y' VX' VY' X' Y' p' (CX' + ε * (1 + r')) CY' B'' x'' y'') := by
  unfold lucasFinance at *
  exact ⟨⟨by linear_combination ht, by linear_combination ht1⟩,
    ⟨by linear_combination ht, by linear_combination ht1⟩,
    ⟨by linear_combination ht, by linear_combination ht1⟩⟩

/-- **Exercise 6(a), O&R p. 347: the three Euler equations**. Let `u_X` be the partial
derivative of `u(C_X, C_Y)` in `C_X`, and let the date-`t+1` states `s` have probabilities
`π(s)`. If the optimal plan cannot be improved by the feasible perturbations of
`lucas_perturbation_feasible` (buying a little more of the Home claim, the Foreign claim or
the bond), then
`u_X(t)V_{X,t} = βE_t[u_X(t+1)(X_{t+1} + V_{X,t+1})]`,
`u_X(t)V_{Y,t} = βE_t[u_X(t+1)(p_{t+1}Y_{t+1} + V_{Y,t+1})]` and
`u_X(t) = (1 + r_{t+1})βE_t[u_X(t+1)]`. -/
theorem lucas_euler_equations (u uX : ℝ → ℝ → ℝ)
    (huX : ∀ a b, HasDerivAt (fun c => u c b) (uX a b) a) (β : ℝ) (π : S → ℝ)
    {CX CY VX VY r' : ℝ} {CX' CY' X' Y' p' VX' VY' : S → ℝ}
    (hmaxX : IsLocalMax (fun ε => u (CX - ε * VX) CY
      + β * ∑ s, π s * u (CX' s + ε * (X' s + VX' s)) (CY' s)) 0)
    (hmaxY : IsLocalMax (fun ε => u (CX - ε * VY) CY
      + β * ∑ s, π s * u (CX' s + ε * (p' s * Y' s + VY' s)) (CY' s)) 0)
    (hmaxB : IsLocalMax (fun ε => u (CX - ε * 1) CY
      + β * ∑ s, π s * u (CX' s + ε * (1 + r')) (CY' s)) 0) :
    uX CX CY * VX = β * ∑ s, π s * (uX (CX' s) (CY' s) * (X' s + VX' s)) ∧
      uX CX CY * VY = β * ∑ s, π s * (uX (CX' s) (CY' s) * (p' s * Y' s + VY' s)) ∧
      uX CX CY = (1 + r') * (β * ∑ s, π s * uX (CX' s) (CY' s)) := by
  refine ⟨euler_of_isLocalMax (huX CX CY) (fun s => huX (CX' s) (CY' s)) β π VX _ hmaxX,
    euler_of_isLocalMax (huX CX CY) (fun s => huX (CX' s) (CY' s)) β π VY _ hmaxY, ?_⟩
  have := euler_of_isLocalMax (U1 := fun s c => u c (CY' s)) (huX CX CY)
    (fun s => huX (CX' s) (CY' s)) β π 1 (fun _ => 1 + r') hmaxB
  rw [mul_one] at this
  rw [this, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun s _ => by ring

/-! ### The endowment state as a finite Markov chain -/

/-- A finite Markov chain for the endowment state, Exercise 6, O&R p. 347: transition
probabilities `P s s′ ≥ 0` with `Σ_{s′} P s s′ = 1`. -/
structure EndowmentChain (S : Type) [Fintype S] where
  P : S → S → ℝ
  P_nonneg : ∀ s s', 0 ≤ P s s'
  P_sum : ∀ s, ∑ s', P s s' = 1

/-- The current state after a history `h` of `n` events started from `s₀` (Exercise 6,
O&R p. 347): the last event of `h`, or `s₀` if `h` is empty. -/
def lastState {T : Type} (s₀ : T) : (n : ℕ) → (Fin n → T) → T
  | 0, _ => s₀
  | n + 1, h => h (Fin.last n)

/-- Appending an event makes it the current state (Exercise 6, O&R p. 347). -/
theorem lastState_snoc {T : Type} (s₀ : T) (n : ℕ) (h : Fin n → T) (s : T) :
    lastState s₀ (n + 1) (Fin.snoc h s : Fin (n + 1) → T) = s := by
  simp [lastState]

namespace EndowmentChain

variable (mc : EndowmentChain S)

/-- The event tree generated by the Markov chain from the initial state `s₀` (Exercise 6,
O&R p. 347): the next event after `h` is `s` with probability `P(current state, s)`. -/
def toTree (s₀ : S) : EventTree.Tree S :=
  ⟨fun n g s => mc.P (lastState s₀ n g) s, fun _ _ _ => mc.P_nonneg _ _, fun _ _ => mc.P_sum _⟩

/-- The one-step probabilities of the chain's tree (Exercise 6, O&R p. 347). -/
theorem toTree_q (s₀ : S) (n : ℕ) (g : Fin n → S) (s : S) :
    (mc.toTree s₀).q n g s = mc.P (lastState s₀ n g) s := rfl

/-- The `k`-step conditional expectation `E[f(s_{t+k}) | s_t = s]` of the chain
(Exercise 6(c), O&R p. 347). -/
noncomputable def mExp : ℕ → (S → ℝ) → S → ℝ
  | 0, f => f
  | k + 1, f => fun s => ∑ s', mc.P s s' * mExp k f s'

/-- On the chain's tree, conditional expectations of functions of the current state are the
chain's `k`-step expectations (Exercise 6(c), O&R p. 347). -/
theorem condE_toTree (s₀ : S) (f : S → ℝ) (k : ℕ) : ∀ (n : ℕ) (h : Fin n → S),
    condE (mc.toTree s₀) (fun n h => f (lastState s₀ n h)) k n h
      = mc.mExp k f (lastState s₀ n h) := by
  induction k with
  | zero => intro n h; rfl
  | succ k ih =>
    intro n h
    rw [condE.succ_eq]
    simp only [ih, lastState_snoc, toTree_q]
    rfl

/-- The marginal-utility-weighted present value `Σ_{k≥1} β^k E[g(s_{t+k}) | s_t = s]`
(Exercise 6(c), O&R p. 347). -/
noncomputable def markovSeries (β : ℝ) (g : S → ℝ) (s : S) : ℝ :=
  ∑' k, β ^ (k + 1) * mc.mExp (k + 1) g s

/-- The stationary claim price `V(s) = Σ_{k≥1} β^k E[m(s_{t+k})D(s_{t+k}) | s]/m(s)` of a
dividend `D` valued with marginal utility `m` (Exercise 6(c), O&R p. 347). -/
noncomputable def markovPrice (β : ℝ) (m D : S → ℝ) (s : S) : ℝ :=
  mc.markovSeries β (fun s => m s * D s) s / m s

end EndowmentChain

/-- On a finite state space every function is bounded, `|f s| ≤ Σ_{s′}|f s′|` (used for
Exercise 6(c), O&R p. 347). -/
theorem abs_le_sum_abs (f : S → ℝ) (s : S) : |f s| ≤ ∑ s', |f s'| :=
  Finset.single_le_sum (fun s' _ => abs_nonneg (f s')) (Finset.mem_univ s)

/-- The chain's tree fundamental value is the stationary series at the current state
(Exercise 6(c), O&R p. 347). -/
theorem fundamentalMU_toTree (mc : EndowmentChain S) (s₀ : S) (β : ℝ) (m D : S → ℝ)
    (n : ℕ) (h : Fin n → S) :
    fundamentalMU (mc.toTree s₀) β (fun n h => m (lastState s₀ n h))
      (fun n h => D (lastState s₀ n h)) n h
      = mc.markovSeries β (fun s => m s * D s) (lastState s₀ n h) := by
  unfold fundamentalMU EndowmentChain.markovSeries
  exact tsum_congr fun k => by rw [← mc.condE_toTree s₀ (fun s => m s * D s) (k + 1) n h]

/-- **Claim prices on a finite Markov chain, Exercise 6(c), O&R p. 347**. Let `0 ≤ β < 1`,
marginal utility `m(s) > 0` and dividend `D(s)` (in units of `X`). Then
(i) the present-value series `Σ_{k≥1} β^k E[m D | s]` converges at every state (proved from
finiteness and `β < 1`, not assumed);
(ii) the stationary price `V(s) = Σ_{k≥1} β^k E[m D | s]/m(s)` solves the Euler equation
`m(s)V(s) = βΣ_{s′}P(s, s′)m(s′)(D(s′) + V(s′))`;
(iii) it is the only stationary solution; and
(iv) on the event tree generated from any initial state, every bounded (possibly
history-dependent) price process solving the Euler equation equals `V` of the current state:
there are no bounded bubbles. -/
theorem markov_price_unique (mc : EndowmentChain S) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (m D : S → ℝ) (hm : ∀ s, 0 < m s) :
    (∀ s, Summable (fun k => β ^ (k + 1) * mc.mExp (k + 1) (fun s => m s * D s) s)) ∧
    (∀ s, m s * mc.markovPrice β m D s
      = β * ∑ s', mc.P s s' * (m s' * (D s' + mc.markovPrice β m D s'))) ∧
    (∀ V : S → ℝ, (∀ s, m s * V s = β * ∑ s', mc.P s s' * (m s' * (D s' + V s'))) →
      V = mc.markovPrice β m D) ∧
    (∀ (s₀ : S) (W : TreeProcess S), EulerEq (mc.toTree s₀) β (fun n h => m (lastState s₀ n h))
      (fun n h => D (lastState s₀ n h)) W → (∃ B, ∀ n h, |W n h| ≤ B) →
      ∀ n h, W n h = mc.markovPrice β m D (lastState s₀ n h)) := by
  have hB : ∀ s₀ : S, ∀ n (h : Fin n → S),
      |m (lastState s₀ n h) * D (lastState s₀ n h)| ≤ ∑ s', |m s' * D s'| :=
    fun s₀ n h => abs_le_sum_abs (fun s => m s * D s) _
  have hM : ∀ s₀ : S, ∀ n (h : Fin n → S), 0 < m (lastState s₀ n h) := fun _ _ _ => hm _
  have U := fun s₀ => unique_bounded_price (mc.toTree s₀) hβ0 hβ1 (hM s₀) (hB s₀)
  have e0 : ∀ s : S, lastState s 0 (Fin.elim0 : Fin 0 → S) = s := fun _ => rfl
  -- the tree solution is the stationary price of the current state
  have hfund : ∀ s₀ n (h : Fin n → S),
      fundamentalMU (mc.toTree s₀) β (fun n h => m (lastState s₀ n h))
        (fun n h => D (lastState s₀ n h)) n h / m (lastState s₀ n h)
        = mc.markovPrice β m D (lastState s₀ n h) := by
    intro s₀ n h
    rw [fundamentalMU_toTree]
    rfl
  have hstat : ∀ V : S → ℝ, (∀ s, m s * V s = β * ∑ s', mc.P s s' * (m s' * (D s' + V s'))) →
      ∀ s₀, EulerEq (mc.toTree s₀) β (fun n h => m (lastState s₀ n h))
        (fun n h => D (lastState s₀ n h)) (fun n h => V (lastState s₀ n h)) := by
    intro V hV s₀ n h
    simp only [hV, lastState_snoc, EndowmentChain.toTree_q]
  refine ⟨fun s => ?_, fun s => ?_, fun V hV => ?_, fun s₀ W hW ⟨BW, hBW⟩ n h => ?_⟩
  · have := series_summable_of_bounded (mc.toTree s) hβ0 hβ1 (hB s) 0 Fin.elim0
    refine this.congr fun k => ?_
    rw [mc.condE_toTree s (fun s => m s * D s) (k + 1) 0 Fin.elim0]
    rfl
  · have E := (U s).1 0 Fin.elim0
    simp only [fundamentalMU_toTree, lastState_snoc, EndowmentChain.toTree_q, e0] at E
    exact E
  · funext s
    have hW := (U s).2.2 (fun n h => V (lastState s n h)) (hstat V hV s)
      ⟨∑ s', |m s' * V s'|, fun n h => abs_le_sum_abs (fun s => m s * V s) _⟩
    have := congrFun (congrFun hW 0) Fin.elim0
    simp only [fundamentalMU_toTree, e0] at this
    exact this
  · have hW' := (U s₀).2.2 W hW ⟨(∑ s', |m s'|) * BW, fun n h => by
      rw [abs_mul]
      exact mul_le_mul (abs_le_sum_abs m _) (hBW n h) (abs_nonneg _)
        (Finset.sum_nonneg fun s' _ => abs_nonneg _)⟩
    rw [hW']
    exact hfund s₀ n h

/-! ### Exercise 6(b)–(d) -/

/-- **Exercise 6(c), O&R p. 347: equilibrium claim prices as expected present values.** Let
`m_X(s) = u_X(X(s)/2, Y(s)/2) > 0` and `m_Y(s) = u_Y(X(s)/2, Y(s)/2)` be the equilibrium
marginal utilities, `p = m_Y/m_X` the relative price of `Y`, and `0 ≤ β < 1`. Then
`V_X(s) = Σ_{k≥1} β^k E[m_X X | s]/m_X(s)` and
`V_Y(s) = Σ_{k≥1} β^k E[m_X pY | s]/m_X(s) = Σ_{k≥1} β^k E[m_Y Y | s]/m_X(s)` (both series
converge) solve the Euler equations of part (a), and each is the unique stationary solution
of its Euler equation (bounded history-dependent solutions are covered by
`markov_price_unique`). -/
theorem lucas_claim_prices_infinite (mc : EndowmentChain S) {β : ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) (mX mY X Y : S → ℝ) (hmX : ∀ s, 0 < mX s) :
    (∀ s, Summable (fun k => β ^ (k + 1) * mc.mExp (k + 1) (fun s => mX s * X s) s)) ∧
    (∀ s, Summable (fun k => β ^ (k + 1) * mc.mExp (k + 1) (fun s => mY s * Y s) s)) ∧
    (∀ s, mc.markovPrice β mX (fun s => mY s / mX s * Y s) s
      = mc.markovSeries β (fun s => mY s * Y s) s / mX s) ∧
    (∀ s, mX s * mc.markovPrice β mX X s
      = β * ∑ s', mc.P s s' * (mX s' * (X s' + mc.markovPrice β mX X s'))) ∧
    (∀ s, mX s * mc.markovPrice β mX (fun s => mY s / mX s * Y s) s
      = β * ∑ s', mc.P s s' * (mX s' * (mY s' / mX s' * Y s'
        + mc.markovPrice β mX (fun s => mY s / mX s * Y s) s'))) ∧
    (∀ V : S → ℝ, (∀ s, mX s * V s = β * ∑ s', mc.P s s' * (mX s' * (X s' + V s'))) →
      V = mc.markovPrice β mX X) ∧
    (∀ V : S → ℝ, (∀ s, mX s * V s
      = β * ∑ s', mc.P s s' * (mX s' * (mY s' / mX s' * Y s' + V s'))) →
      V = mc.markovPrice β mX (fun s => mY s / mX s * Y s)) := by
  have hX := markov_price_unique mc hβ0 hβ1 mX X hmX
  have hY := markov_price_unique mc hβ0 hβ1 mX (fun s => mY s / mX s * Y s) hmX
  have e : (fun s => mX s * (mY s / mX s * Y s)) = fun s => mY s * Y s := by
    funext s
    field_simp [(hmX s).ne']
  refine ⟨hX.1, fun s => ?_, fun s => ?_, hX.2.1, hY.2.1, hX.2.2.1, hY.2.2.1⟩
  · have := hY.1 s
    rwa [e] at this
  · unfold EndowmentChain.markovPrice
    rw [e]

/-- **Exercise 6(b), O&R p. 347: the equilibrium.** With identical tastes and equal pooled
portfolios, consider the no-trade plan in which each country keeps half of each claim
(`x = y = 1/2`), holds no bonds and consumes `C_X = X/2`, `C_Y = Y/2`. At the prices
`p = m_Y/m_X`, `V_X`, `V_Y` of part (c) and the bond rate `1 + r(s) = m_X(s)/(βE[m_X | s])`:
(i) the plan satisfies each country's finance constraint in every state (whatever the
previous interest rate); (ii) goods, share and bond markets clear; (iii) the intratemporal
condition `u_Y = p u_X` holds; (iv) the Euler equations for both claims and the bond hold at
the allocation, for both countries (their marginal utilities coincide); and (v) each country
owns half of world wealth `X + pY + V_X + V_Y` in every state. -/
theorem lucas_equilibrium (mc : EndowmentChain S) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (mX mY X Y : S → ℝ) (hmX : ∀ s, 0 < mX s) (r0 : ℝ) (s : S) :
    lucasFinance r0 0 (1 / 2) (1 / 2) (mc.markovPrice β mX X s)
      (mc.markovPrice β mX (fun s => mY s / mX s * Y s) s) (X s) (Y s) (mY s / mX s)
      (X s / 2) (Y s / 2) 0 (1 / 2) (1 / 2) ∧
    (X s / 2 + X s / 2 = X s ∧ Y s / 2 + Y s / 2 = Y s ∧ (1 : ℝ) / 2 + 1 / 2 = 1) ∧
    mY s = mY s / mX s * mX s ∧
    (mX s * mc.markovPrice β mX X s
      = β * ∑ s', mc.P s s' * (mX s' * (X s' + mc.markovPrice β mX X s'))) ∧
    (mX s * mc.markovPrice β mX (fun s => mY s / mX s * Y s) s
      = β * ∑ s', mc.P s s' * (mX s' * (mY s' / mX s' * Y s'
        + mc.markovPrice β mX (fun s => mY s / mX s * Y s) s'))) ∧
    mX s = mX s / (β * ∑ s', mc.P s s' * mX s') * (β * ∑ s', mc.P s s' * mX s') ∧
    1 / 2 * (X s + mc.markovPrice β mX X s) + 1 / 2 * (mY s / mX s * Y s
      + mc.markovPrice β mX (fun s => mY s / mX s * Y s) s)
      = 1 / 2 * (X s + mY s / mX s * Y s + mc.markovPrice β mX X s
        + mc.markovPrice β mX (fun s => mY s / mX s * Y s) s) := by
  have hc := lucas_claim_prices_infinite mc hβ0.le hβ1 mX mY X Y hmX
  have hE : 0 < β * ∑ s', mc.P s s' * mX s' := by
    refine mul_pos hβ0 ?_
    obtain ⟨s', hs'⟩ : ∃ s', 0 < mc.P s s' := by
      by_contra hcon
      push Not at hcon
      have h1 := mc.P_sum s
      have : ∑ s', mc.P s s' ≤ 0 := Finset.sum_nonpos fun s' _ => hcon s'
      linarith
    exact lt_of_lt_of_le (mul_pos hs' (hmX s'))
      (Finset.single_le_sum (f := fun s' => mc.P s s' * mX s')
        (fun i _ => mul_nonneg (mc.P_nonneg s i) (hmX i).le) (Finset.mem_univ s'))
  refine ⟨?_, ⟨by ring, by ring, by norm_num⟩, ?_, hc.2.2.2.1 s, hc.2.2.2.2.1 s, ?_, by ring⟩
  · unfold lucasFinance
    ring
  · field_simp [(hmX s).ne']
  · exact (div_mul_cancel₀ (mX s) hE.ne').symm

/-- **Exercise 6(d), O&R p. 347: riskless rates.** (i) The date-`t` price `q_X` of one unit
of `X` delivered for sure at `t + 1` is pinned down by its Euler equation
`q_X m_X(s) = βE[m_X | s]`, so `q_X = βE[m_X | s]/m_X(s)`; (ii) a sure unit of `Y` next period
costs `π_Y` units of `X` with `π_Y m_X(s) = βE[m_X p | s]`, so its price in units of current
`Y` is `π_Y/p(s) = βE[m_Y | s]/m_Y(s)`, whose reciprocal is one plus the own-rate of interest
on `Y`; (iii) a `k`-period sure claim on `X` priced by the Euler recursion
`m_X(s)b_{k+1}(s) = βE[m_X b_k | s]`, `b_0 = 1`, costs `β^k E[m_X(s_{t+k}) | s]/m_X(s)`. -/
theorem lucas_riskless_rates (mc : EndowmentChain S) (β : ℝ) (mX mY : S → ℝ)
    (hmX : ∀ s, 0 < mX s) (hmY : ∀ s, 0 < mY s) (s : S) :
    (∀ q : ℝ, q * mX s = β * ∑ s', mc.P s s' * mX s' →
      q = β * (∑ s', mc.P s s' * mX s') / mX s) ∧
    (∀ πY : ℝ, πY * mX s = β * ∑ s', mc.P s s' * (mX s' * (mY s' / mX s')) →
      πY / (mY s / mX s) = β * (∑ s', mc.P s s' * mY s') / mY s) ∧
    (∀ b : ℕ → S → ℝ, (∀ s, b 0 s = 1) →
      (∀ k s, mX s * b (k + 1) s = β * ∑ s', mc.P s s' * (mX s' * b k s')) →
      ∀ k s, b k s = β ^ k * mc.mExp k mX s / mX s) := by
  refine ⟨fun q hq => ?_, fun πY hπ => ?_, fun b hb0 hb => ?_⟩
  · rw [eq_div_iff (hmX s).ne', hq]
  · have e : ∀ s', mX s' * (mY s' / mX s') = mY s' := fun s' => by
      field_simp [(hmX s').ne']
    simp only [e] at hπ
    have h1 := (hmX s).ne'
    have h2 := (hmY s).ne'
    field_simp
    rw [hπ]
  · intro k
    induction k with
    | zero => intro s; rw [hb0, pow_zero, one_mul, EndowmentChain.mExp, div_self (hmX s).ne']
    | succ k ih =>
      intro s
      rw [eq_div_iff (hmX s).ne', mul_comm, hb]
      simp only [ih, EndowmentChain.mExp, Finset.mul_sum]
      refine Finset.sum_congr rfl fun s' _ => ?_
      field_simp [(hmX s').ne']
      ring

/-! ## Exercise 3(a): quadratic utility and certainty equivalence -/

/-- Quadratic period utility `u(C) = C − (a₀/2)C²` of Exercise 3, O&R p. 345. -/
noncomputable def quadU (a0 c : ℝ) : ℝ := c - a0 / 2 * c ^ 2

/-- Marginal utility of quadratic utility, `u′(C) = 1 − a₀C` (Exercise 3, O&R p. 346). -/
theorem quadU_hasDerivAt (a0 c : ℝ) : HasDerivAt (quadU a0) (1 - a0 * c) c := by
  have h := (hasDerivAt_id c).sub ((hasDerivAt_pow 2 c).const_mul (a0 / 2))
  exact h.congr_deriv (by simp; ring)

/-- **The bond Euler equation with quadratic utility, Exercise 3, O&R p. 346**: with utility
discounted at `(1 + r)^{−1}`, if saving `ε` more in the bond (consuming `(1 + r)ε` more in
every state next period) does not improve the plan locally, then
`1 − a₀C₁ = Σ_s π(s)(1 − a₀C₂(s))`. -/
theorem quadratic_euler (π : S → ℝ) {a0 r C1 : ℝ} {C2 : S → ℝ} (hr : 1 + r ≠ 0)
    (hmax : IsLocalMax (fun ε => quadU a0 (C1 - ε * 1)
      + (1 + r)⁻¹ * ∑ s, π s * quadU a0 (C2 s + ε * (1 + r))) 0) :
    1 - a0 * C1 = ∑ s, π s * (1 - a0 * C2 s) := by
  have h := euler_of_isLocalMax (U1 := fun _ => quadU a0) (quadU_hasDerivAt a0 C1)
    (fun s => quadU_hasDerivAt a0 (C2 s)) (1 + r)⁻¹ π 1 (fun _ => 1 + r) hmax
  rw [mul_one] at h
  rw [h, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  field_simp

/-- **Exercise 3(a), O&R p. 346 (two periods)**: with the bond Euler equation and the budget
constraints `C₁ + C₂(s)/(1 + r) = (1 + r)B₁ + Y₁ + Y₂(s)/(1 + r)` (nonnegativity of `C₂`
ignored), optimal date-1 consumption is
`C₁ = [(1 + r)/(2 + r)][(1 + r)B₁ + Y₁ + E₁Y₂/(1 + r)]`: it depends on `Y₂` only through its
mean (certainty equivalence). -/
theorem quadratic_two_period_consumption {π : S → ℝ} (hπ : ∑ s, π s = 1) {a0 r B1 Y1 C1 : ℝ}
    {Y2 C2 : S → ℝ} (ha0 : a0 ≠ 0) (hr : -1 < r)
    (heul : 1 - a0 * C1 = ∑ s, π s * (1 - a0 * C2 s))
    (hbud : ∀ s, C1 + C2 s / (1 + r) = (1 + r) * B1 + Y1 + Y2 s / (1 + r)) :
    C1 = (1 + r) / (2 + r) * ((1 + r) * B1 + Y1 + (∑ s, π s * Y2 s) / (1 + r)) := by
  have hr1 : (1 + r) ≠ 0 := by linarith
  have hr2 : (2 + r) ≠ 0 := by linarith
  have hC2 : ∀ s, C2 s = (1 + r) * ((1 + r) * B1 + Y1 - C1) + Y2 s := by
    intro s
    have := hbud s
    field_simp at this
    linarith
  have hmean : C1 = ∑ s, π s * C2 s := by
    have e : ∑ s, π s * (1 - a0 * C2 s) = 1 - a0 * ∑ s, π s * C2 s := by
      calc ∑ s, π s * (1 - a0 * C2 s) = ∑ s, π s - a0 * ∑ s, π s * C2 s := by
            rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
            exact Finset.sum_congr rfl fun s _ => by ring
        _ = 1 - a0 * ∑ s, π s * C2 s := by rw [hπ]
    rw [e] at heul
    have : a0 * (C1 - ∑ s, π s * C2 s) = 0 := by linarith
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h ha0
    · linarith
  have hsum : ∑ s, π s * C2 s = (1 + r) * ((1 + r) * B1 + Y1 - C1) + ∑ s, π s * Y2 s := by
    simp only [hC2, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hπ, one_mul]
  rw [hsum] at hmean
  field_simp
  linarith

/-- **Consumption is a martingale under quadratic utility, Exercise 3, O&R p. 346** (with
Chapter 2's `β(1 + r) = 1`): the bond Euler equation `1 − a₀C_t = E_t[1 − a₀C_{t+1}]` at every
history, with `a₀ ≠ 0`, gives `E_t[C_{t+k}] = C_t` for every `k`. -/
theorem quadratic_consumption_martingale {a0 : ℝ} (ha0 : a0 ≠ 0) {C : TreeProcess S}
    (heul : ∀ n (h : Fin n → S),
      1 - a0 * C n h = ∑ s, tr.q n h s * (1 - a0 * C (n + 1) (Fin.snoc h s))) :
    ∀ k n h, condE tr C k n h = C n h := by
  have h1 : condE tr C 1 = C := by
    funext n h
    have e : ∑ s, tr.q n h s * (1 - a0 * C (n + 1) (Fin.snoc h s))
        = 1 - a0 * ∑ s, tr.q n h s * C (n + 1) (Fin.snoc h s) := by
      calc ∑ s, tr.q n h s * (1 - a0 * C (n + 1) (Fin.snoc h s))
          = ∑ s, tr.q n h s - a0 * ∑ s, tr.q n h s * C (n + 1) (Fin.snoc h s) := by
            rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
            exact Finset.sum_congr rfl fun s _ => by ring
        _ = 1 - a0 * ∑ s, tr.q n h s * C (n + 1) (Fin.snoc h s) := by rw [tr.q_sum]
    have := heul n h
    rw [e] at this
    have h2 : a0 * (C n h - ∑ s, tr.q n h s * C (n + 1) (Fin.snoc h s)) = 0 := by linarith
    rw [condE.one_eq]
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact absurd h3 ha0
    · linarith
  intro k
  induction k with
  | zero => intro n h; rfl
  | succ k ih => intro n h; rw [condE.succ_eq_iter, h1, ih]

/-- **The `K`-period expected budget constraint, Exercise 3 (Chapter 2 analogue), O&R p. 346**:
if bonds evolve as `B_{t+1} = (1 + r)B_t + Y_t − C_t` (the same in every date-`t+1` state),
then with `ν = 1/(1 + r)`,
`Σ_{k<K} ν^k E_t[C_{t+k}] = (1 + r)B_t + Σ_{k<K} ν^k E_t[Y_{t+k}] − (1 + r)ν^K E_t[B_{t+K}]`. -/
theorem expected_budget_k_step {r : ℝ} (hr : 1 + r ≠ 0) {B Y C : TreeProcess S}
    (hbud : ∀ n (h : Fin n → S) s,
      B (n + 1) (Fin.snoc h s) = (1 + r) * B n h + Y n h - C n h) (K : ℕ) :
    ∀ n h, ∑ k ∈ range K, (1 / (1 + r)) ^ k * condE tr C k n h
      = (1 + r) * B n h + ∑ k ∈ range K, (1 / (1 + r)) ^ k * condE tr Y k n h
        - (1 + r) * (1 / (1 + r)) ^ K * condE tr B K n h := by
  have hB1 : condE tr B 1 = fun m g => (1 + r) * B m g + Y m g - C m g := by
    funext m g
    rw [condE.one_eq]
    simp only [hbud, ← Finset.sum_mul, tr.q_sum, one_mul]
  have hν : (1 + r) * (1 / (1 + r)) = 1 := by field_simp
  induction K with
  | zero => intro n h; simp [condE.zero_eq]
  | succ K ih =>
    intro n h
    have key : condE tr B (K + 1) n h
        = (1 + r) * condE tr B K n h + condE tr Y K n h - condE tr C K n h := by
      rw [condE.succ_eq_iter, hB1, condE.sub_apply, condE.add_apply, condE.smul_apply]
    rw [Finset.sum_range_succ, Finset.sum_range_succ, ih n h, key, pow_succ]
    linear_combination ((1 / (1 + r)) ^ K * ((1 + r) * condE tr B K n h + condE tr Y K n h
      - condE tr C K n h)) * hν

/-- The human-wealth series `Σ_{k≥0} ν^k E_t[Y_{t+k}]` is summable when income is bounded and
`r > 0` (`ν = 1/(1 + r)`), Exercise 3, O&R p. 346. -/
theorem income_series_summable {r : ℝ} (hr : 0 < r) {Y : TreeProcess S} {BY : ℝ}
    (hY : ∀ n h, |Y n h| ≤ BY) (n : ℕ) (h : Fin n → S) :
    Summable (fun k => (1 / (1 + r)) ^ k * condE tr Y k n h) := by
  have hν0 : 0 ≤ 1 / (1 + r) := by positivity
  have hν1 : 1 / (1 + r) < 1 := by rw [div_lt_one (by linarith)]; linarith
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hν0 hν1).mul_right BY)
    fun k => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hν0]
  exact mul_le_mul_of_nonneg_left (condE.abs_le_of_bound tr hY k n h) (pow_nonneg hν0 k)

/-- **Exercise 3(a), infinite horizon, O&R p. 346 (with Chapter 2's formula)**: on the event
tree, with quadratic utility discounted at `(1 + r)^{−1}`, `r > 0`, `a₀ ≠ 0`, bounded income
`Y`, bonds evolving by `B_{t+1} = (1 + r)B_t + Y_t − C_t`, the bond Euler equation at every
history (from `quadratic_euler`) and the intertemporal-budget (transversality) condition
`lim_K (1 + r)^{−K}E_t[B_{t+K}] = 0`, optimal consumption is
`C_t = [r/(1 + r)][(1 + r)B_t + Σ_{k≥0} (1 + r)^{−k}E_t[Y_{t+k}]]`, the certainty-equivalent
permanent-income rule: income uncertainty matters only through conditional means. The
human-wealth series converges (proved). -/
theorem quadratic_infinite_horizon_consumption {r a0 : ℝ} (hr : 0 < r) (ha0 : a0 ≠ 0)
    {B Y C : TreeProcess S} {BY : ℝ} (hY : ∀ n h, |Y n h| ≤ BY)
    (heul : ∀ n (h : Fin n → S),
      1 - a0 * C n h = ∑ s, tr.q n h s * (1 - a0 * C (n + 1) (Fin.snoc h s)))
    (hbud : ∀ n (h : Fin n → S) s,
      B (n + 1) (Fin.snoc h s) = (1 + r) * B n h + Y n h - C n h)
    (htv : ∀ n h, Tendsto (fun K => (1 / (1 + r)) ^ K * condE tr B K n h) atTop (𝓝 0))
    (n : ℕ) (h : Fin n → S) :
    C n h = r / (1 + r) * ((1 + r) * B n h
      + ∑' k, (1 / (1 + r)) ^ k * condE tr Y k n h) := by
  have hr1 : 1 + r ≠ 0 := by linarith
  have hν0 : 0 ≤ 1 / (1 + r) := by positivity
  have hν1 : 1 / (1 + r) < 1 := by rw [div_lt_one (by linarith)]; linarith
  have hmart := quadratic_consumption_martingale tr ha0 heul
  have hk := expected_budget_k_step tr hr1 hbud
  have hC : HasSum (fun k => (1 / (1 + r)) ^ k * condE tr C k n h)
      (C n h * (1 - 1 / (1 + r))⁻¹) := by
    have := (hasSum_geometric_of_lt_one hν0 hν1).mul_left (C n h)
    refine this.congr_fun fun k => ?_
    simp only [hmart]
    ring
  have hL := hC.tendsto_sum_nat
  have hR : Tendsto (fun K => (1 + r) * B n h
      + ∑ k ∈ range K, (1 / (1 + r)) ^ k * condE tr Y k n h
      - (1 + r) * ((1 / (1 + r)) ^ K * condE tr B K n h)) atTop
      (𝓝 ((1 + r) * B n h + ∑' k, (1 / (1 + r)) ^ k * condE tr Y k n h - (1 + r) * 0)) :=
    (tendsto_const_nhds.add (income_series_summable tr hr hY n h).hasSum.tendsto_sum_nat).sub
      (tendsto_const_nhds.mul (htv n h))
  have e : (fun K => ∑ k ∈ range K, (1 / (1 + r)) ^ k * condE tr C k n h) = fun K =>
      (1 + r) * B n h + ∑ k ∈ range K, (1 / (1 + r)) ^ k * condE tr Y k n h
        - (1 + r) * ((1 / (1 + r)) ^ K * condE tr B K n h) := by
    funext K
    rw [hk K n h]
    ring
  rw [e] at hL
  have := tendsto_nhds_unique hL hR
  have h1 : 1 - 1 / (1 + r) = r / (1 + r) := by field_simp; ring
  rw [h1, mul_zero, sub_zero] at this
  rw [← this]
  field_simp [hr.ne']

/-- The recursion of human wealth `H_t = Σ_{k≥0} ν^k E_t[Y_{t+k}]`, Exercise 3, O&R p. 346:
`H(h) = Y(h) + νΣ_s π(s|h) H(h, s)` when income is bounded and `r > 0`. -/
theorem human_wealth_recursion {r : ℝ} (hr : 0 < r) {Y : TreeProcess S} {BY : ℝ}
    (hY : ∀ n h, |Y n h| ≤ BY) (n : ℕ) (h : Fin n → S) :
    ∑' k, (1 / (1 + r)) ^ k * condE tr Y k n h = Y n h + 1 / (1 + r) *
      ∑ s, tr.q n h s * ∑' k, (1 / (1 + r)) ^ k * condE tr Y k (n + 1) (Fin.snoc h s) := by
  rw [(income_series_summable tr hr hY n h).tsum_eq_zero_add]
  simp only [pow_zero, one_mul, condE.zero_eq]
  congr 1
  have hs := fun s => ((income_series_summable tr hr hY (n + 1) (Fin.snoc h s)).hasSum.mul_left
    (tr.q n h s))
  have := (hasSum_sum (s := Finset.univ) fun s _ => hs s).mul_left (1 / (1 + r))
  refine HasSum.tsum_eq (this.congr_fun fun k => ?_)
  rw [condE.succ_eq, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  ring

/-- **Exercise 3(a), infinite horizon: the permanent-income rule is optimal**, O&R p. 346.
With `r > 0`, bounded income, and bonds evolving by `B_{t+1} = (1 + r)B_t + Y_t − C_t` under
the rule `C_t = [r/(1 + r)][(1 + r)B_t + Σ_{k≥0}(1 + r)^{−k}E_t[Y_{t+k}]]`, consumption
satisfies the quadratic-utility bond Euler equation `1 − a₀C_t = E_t[1 − a₀C_{t+1}]` at every
history, and the transversality condition `(1 + r)^{−K}E_t[B_{t+K}] → 0` holds (derived, not
assumed): the rule and the conditions of `quadratic_infinite_horizon_consumption` are
consistent. -/
theorem quadratic_permanent_income_rule {r : ℝ} (hr : 0 < r) (a0 : ℝ) {B Y C : TreeProcess S}
    {BY : ℝ} (hY : ∀ n h, |Y n h| ≤ BY)
    (hC : ∀ n h, C n h = r / (1 + r) * ((1 + r) * B n h
      + ∑' k, (1 / (1 + r)) ^ k * condE tr Y k n h))
    (hbud : ∀ n (h : Fin n → S) s,
      B (n + 1) (Fin.snoc h s) = (1 + r) * B n h + Y n h - C n h) :
    (∀ n (h : Fin n → S),
      1 - a0 * C n h = ∑ s, tr.q n h s * (1 - a0 * C (n + 1) (Fin.snoc h s))) ∧
    ∀ n h, Tendsto (fun K => (1 / (1 + r)) ^ K * condE tr B K n h) atTop (𝓝 0) := by
  have hr1 : 1 + r ≠ 0 := by linarith
  have hν0 : 0 ≤ 1 / (1 + r) := by positivity
  have hν1 : 1 / (1 + r) < 1 := by rw [div_lt_one (by linarith)]; linarith
  have hmart1 : ∀ n (h : Fin n → S), C n h = ∑ s, tr.q n h s * C (n + 1) (Fin.snoc h s) := by
    intro n h
    have hs : ∀ s, tr.q n h s * C (n + 1) (Fin.snoc h s)
        = r / (1 + r) * ((1 + r) * ((1 + r) * B n h + Y n h - C n h)) * tr.q n h s
          + r / (1 + r) * (tr.q n h s
            * ∑' k, (1 / (1 + r)) ^ k * condE tr Y k (n + 1) (Fin.snoc h s)) := by
      intro s
      rw [hC (n + 1), hbud]
      ring
    rw [Finset.sum_congr rfl fun s _ => hs s, Finset.sum_add_distrib, ← Finset.mul_sum,
      ← Finset.mul_sum, tr.q_sum]
    have hsumH : ∑ s, tr.q n h s * ∑' k, (1 / (1 + r)) ^ k * condE tr Y k (n + 1) (Fin.snoc h s)
        = (1 + r) * (∑' k, (1 / (1 + r)) ^ k * condE tr Y k n h - Y n h) := by
      rw [human_wealth_recursion tr hr hY n h]
      field_simp
      ring
    rw [hsumH, hC n h]
    field_simp
    ring
  have hmart : ∀ k n h, condE tr C k n h = C n h := by
    have h1 : condE tr C 1 = C := by
      funext n h
      rw [condE.one_eq, ← hmart1]
    intro k
    induction k with
    | zero => intro n h; rfl
    | succ k ih => intro n h; rw [condE.succ_eq_iter, h1, ih]
  refine ⟨fun n h => ?_, fun n h => ?_⟩
  · have e : ∑ s, tr.q n h s * (1 - a0 * C (n + 1) (Fin.snoc h s))
        = 1 - a0 * ∑ s, tr.q n h s * C (n + 1) (Fin.snoc h s) := by
      calc ∑ s, tr.q n h s * (1 - a0 * C (n + 1) (Fin.snoc h s))
          = ∑ s, tr.q n h s - a0 * ∑ s, tr.q n h s * C (n + 1) (Fin.snoc h s) := by
            rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
            exact Finset.sum_congr rfl fun s _ => by ring
        _ = 1 - a0 * ∑ s, tr.q n h s * C (n + 1) (Fin.snoc h s) := by rw [tr.q_sum]
    rw [e, ← hmart1]
  · have hk := expected_budget_k_step tr hr1 hbud
    have e : (fun K => (1 / (1 + r)) ^ K * condE tr B K n h) = fun K =>
        ((1 + r) * B n h + ∑ k ∈ range K, (1 / (1 + r)) ^ k * condE tr Y k n h
          - C n h * ∑ k ∈ range K, (1 / (1 + r)) ^ k) / (1 + r) := by
      funext K
      have := hk K n h
      simp only [hmart] at this
      have e2 : ∑ k ∈ range K, (1 / (1 + r)) ^ k * C n h
          = C n h * ∑ k ∈ range K, (1 / (1 + r)) ^ k := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
      rw [e2] at this
      field_simp
      linarith
    rw [e]
    have hlim : Tendsto (fun K => ((1 + r) * B n h
        + ∑ k ∈ range K, (1 / (1 + r)) ^ k * condE tr Y k n h
        - C n h * ∑ k ∈ range K, (1 / (1 + r)) ^ k) / (1 + r)) atTop
        (𝓝 (((1 + r) * B n h + ∑' k, (1 / (1 + r)) ^ k * condE tr Y k n h
          - C n h * (1 - 1 / (1 + r))⁻¹) / (1 + r))) :=
      ((tendsto_const_nhds.add (income_series_summable tr hr hY n h).hasSum.tendsto_sum_nat).sub
        (tendsto_const_nhds.mul
          (hasSum_geometric_of_lt_one hν0 hν1).tendsto_sum_nat)).div_const _
    have hz : ((1 + r) * B n h + ∑' k, (1 / (1 + r)) ^ k * condE tr Y k n h
        - C n h * (1 - 1 / (1 + r))⁻¹) / (1 + r) = 0 := by
      rw [hC n h]
      have h1 : 1 - 1 / (1 + r) = r / (1 + r) := by field_simp; ring
      rw [h1]
      field_simp [hr.ne']
      ring
    rwa [hz] at hlim

/-! ## Unconditional expectations at the root -/

/-- **Unconditional expectations, O&R §5.4.3 (p. 316) with Appendix 5C (p. 341)**: at the
date-1 history the `k`-step expectation is `E_1[f_{k+1}] = Σ_{h_{k+1}} π(h_{k+1} | h_1)
f(h_{k+1})`, the sum over date-`(k + 1)` histories weighted by `Tree.histProb`. -/
theorem condE_root_eq_sum_histProb (tr : EventTree.Tree S) (f : TreeProcess S) (k : ℕ)
    (h0 : Fin 0 → S) : condE tr f k 0 h0 = ∑ g : Fin k → S, tr.histProb g * f k g := by
  induction k generalizing f with
  | zero =>
    rw [Fintype.sum_unique, Subsingleton.elim h0 default]
    simp [EventTree.Tree.histProb, EventTree.Tree.condProb, condE.zero_eq]
  | succ k ih =>
    rw [condE.succ_eq_iter, ih]
    rw [← (Fin.snocEquiv (fun _ : Fin (k + 1) => S)).sum_comp, Fintype.sum_prod_type,
      Finset.sum_comm]
    refine Finset.sum_congr rfl fun g _ => ?_
    have e : ∀ s : S, (Fin.snocEquiv fun _ : Fin (k + 1) => S) (s, g) = Fin.snoc g s :=
      fun _ => rfl
    simp only [e, EventTree.Tree.histProb, condProb_snoc tr _ _ (Nat.zero_le k), condE.one_eq,
      Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => (mul_assoc _ _ _).symm

/-! ## (61) with the constant consumption share derived -/

/-- **O&R (61), p. 317, with `C = μY^W` derived.** Let countries `j ∈ ι` have CRRA marginal
utility `C^{−ρ}` (`ρ ≠ 0`), `β > 0`, positive consumption, and satisfy the complete-markets
first-order conditions (84) in date-1 prices `P(h)`,
`P(h)C_j(h_1)^{−ρ} = π(h | h_1)β^{t−1}C_j(h)^{−ρ}`, at every history, with world market clearing
`Σ_j C_j = Y^W`, and let every history have positive probability. Then country `i`'s
consumption share is constant, `C_i = μY^W` with `μ = C_i(h_1)/Y^W(h_1)`
(`EventTree.crra_constant_share_infinite`), and any claim price `V` satisfying `i`'s Euler
equation (57) and the no-bubble condition obeys (61):
`V_t = Σ_{s>t} β^{s−t}E_t[(Y^W_s/Y^W_t)^{−ρ}Y_s]`. -/
theorem price_crra_world_output_derived {ι : Type} [Fintype ι] (tr : EventTree.Tree S)
    {β ρ : ℝ} (hβ : 0 < β) (hρ : ρ ≠ 0) (P YW : TreeProcess S) (C : ι → TreeProcess S)
    (hC : ∀ j n h, 0 < C j n h)
    (hfoc : ∀ j n h, P n h * C j 0 Fin.elim0 ^ (-ρ) = tr.histProb h * β ^ n * C j n h ^ (-ρ))
    (hclear : ∀ n h, ∑ j, C j n h = YW n h) (hπ : ∀ n (h : Fin n → S), 0 < tr.histProb h)
    (i : ι) {Y V : TreeProcess S} (he : EulerEq tr β (fun m g => C i m g ^ (-ρ)) Y V)
    (n : ℕ) (h : Fin n → S)
    (hnb : Tendsto (fun K => β ^ K * condE tr (fun m g => C i m g ^ (-ρ) * V m g) K n h
      / C i n h ^ (-ρ)) atTop (𝓝 0)) :
    Tendsto (fun K => ∑ k ∈ range K,
      β ^ (k + 1) * condE tr (fun m g => (YW m g / YW n h) ^ (-ρ) * Y m g) (k + 1) n h)
      atTop (𝓝 (V n h)) := by
  have hYW : ∀ n h, 0 < YW n h := fun n h => by
    rw [← hclear n h]
    exact Finset.sum_pos (fun j _ => hC j n h) ⟨i, Finset.mem_univ i⟩
  obtain ⟨μ, hμ⟩ : ∃ μ, μ = C i 0 Fin.elim0 / YW 0 Fin.elim0 := ⟨_, rfl⟩
  have hμpos : 0 < μ := hμ ▸ div_pos (hC i 0 _) (hYW 0 _)
  have hshare : ∀ m (g : Fin m → S), C i m g = μ * YW m g := fun m g => by
    rw [hμ]
    exact EventTree.crra_constant_share_infinite tr hβ hρ P YW C hC hfoc hclear i m g (hπ m g)
  simp only [hshare] at he hnb
  exact price_crra_world_output_tree tr hμpos hYW he n h hnb

/-! ## Exercise 6(b): global optimality and uniqueness of the no-trade allocation -/

/-- **The present value of a plan, O&R (56)–(59), p. 316**: if the cost `A` of the portfolio
chosen at each history and the spending `e` satisfy the pricing identity
`M_tA_t = βE_t[M_{t+1}(e_{t+1} + A_{t+1})]` (the Euler equation with `e` as dividend), then
`Σ_{k≤T} β^k E_t[M_{t+k}e_{t+k}] = M_t(A_t + e_t) − β^T E_t[M_{t+T}A_{t+T}]`. -/
theorem plan_value_identity {β : ℝ} {M e A : TreeProcess S} (he : EulerEq tr β M e A)
    (T n : ℕ) (h : Fin n → S) :
    ∑ k ∈ range (T + 1), β ^ k * condE tr (fun m g => M m g * e m g) k n h
      = M n h * (A n h + e n h) - β ^ T * condE tr (fun m g => M m g * A m g) T n h := by
  have hk := mu_price_k_step tr he T n h
  rw [pvPartial] at hk
  rw [Finset.sum_range_succ']
  simp only [pow_zero, one_mul, condE.zero_eq]
  linarith

/-- Discounted expectations of a bounded process are summable (`0 ≤ β < 1`), O&R (55),
p. 315: `Σ_t β^t E_1[f_t]` converges when `|f| ≤ K`. -/
theorem summable_discounted_condE {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) {f : TreeProcess S}
    {K : ℝ} (hf : ∀ n h, |f n h| ≤ K) (n : ℕ) (h : Fin n → S) :
    Summable (fun k => β ^ k * condE tr f k n h) := by
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hβ0 hβ1).mul_right K)
    fun k => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hβ0]
  exact mul_le_mul_of_nonneg_left (condE.abs_le_of_bound tr hf k n h) (pow_nonneg hβ0 k)

/-- Expectations of a positive function under the chain are positive (Exercise 6,
O&R p. 347): `Σ_{s′} P(s, s′) f(s′) > 0` when `f > 0`. -/
theorem chain_expect_pos (mc : EndowmentChain S) {f : S → ℝ} (hf : ∀ s, 0 < f s) (s : S) :
    0 < ∑ s', mc.P s s' * f s' := by
  obtain ⟨s', hs'⟩ : ∃ s', 0 < mc.P s s' := by
    by_contra hcon
    push Not at hcon
    have h1 := mc.P_sum s
    have : ∑ s', mc.P s s' ≤ 0 := Finset.sum_nonpos fun s' _ => hcon s'
    linarith
  exact lt_of_lt_of_le (mul_pos hs' (hf s'))
    (Finset.single_le_sum (f := fun s' => mc.P s s' * f s')
      (fun i _ => mul_nonneg (mc.P_nonneg s i) (hf i).le) (Finset.mem_univ s'))

/-- A consumption–portfolio plan for one country in the Lucas model, Exercise 6, O&R p. 347:
at each history, consumption of `X` and `Y`, and the holdings of the Home claim, the Foreign
claim and bonds carried to the next date. -/
structure LucasPlan (S : Type) where
  cX : TreeProcess S
  cY : TreeProcess S
  x : TreeProcess S
  y : TreeProcess S
  B : TreeProcess S

/-- The admissible plans of Exercise 6(b), O&R p. 347, on the event tree of the endowment
chain from `s₀`: positive consumption; the finance constraint (56) at date 1 starting from the
pooled half portfolios and no bonds, and at every later history (the bond bought in state
`σ` pays `1 + r(σ)`); bounded holdings (the standard admissibility restriction, which rules
out Ponzi schemes); and a convergent expected-utility series. Prices `V_X, V_Y, p` and
the bond rate are functions of the current state. -/
def LucasAdmissible (mc : EndowmentChain S) (s₀ : S) (β : ℝ) (u : ℝ → ℝ → ℝ)
    (X Y VX VY p r : S → ℝ) (pl : LucasPlan S) : Prop :=
  (∀ n h, 0 < pl.cX n h ∧ 0 < pl.cY n h) ∧
  lucasFinance 0 0 (1 / 2) (1 / 2) (VX s₀) (VY s₀) (X s₀) (Y s₀) (p s₀) (pl.cX 0 Fin.elim0)
    (pl.cY 0 Fin.elim0) (pl.B 0 Fin.elim0) (pl.x 0 Fin.elim0) (pl.y 0 Fin.elim0) ∧
  (∀ n (h : Fin n → S) s, lucasFinance (r (lastState s₀ n h)) (pl.B n h) (pl.x n h)
    (pl.y n h) (VX s) (VY s) (X s) (Y s) (p s) (pl.cX (n + 1) (Fin.snoc h s))
    (pl.cY (n + 1) (Fin.snoc h s)) (pl.B (n + 1) (Fin.snoc h s)) (pl.x (n + 1) (Fin.snoc h s))
    (pl.y (n + 1) (Fin.snoc h s))) ∧
  (∃ K, ∀ n h, |pl.x n h| ≤ K ∧ |pl.y n h| ≤ K ∧ |pl.B n h| ≤ K) ∧
  Summable (fun n => β ^ n *
    condE (mc.toTree s₀) (fun m g => u (pl.cX m g) (pl.cY m g)) n 0 Fin.elim0)

/-- Expected lifetime utility (55), O&R p. 315, of a plan:
`U_1 = Σ_t β^{t−1}E_1[u(C_{X,t}, C_{Y,t})]`. -/
noncomputable def lucasUtility (mc : EndowmentChain S) (s₀ : S) (β : ℝ) (u : ℝ → ℝ → ℝ)
    (pl : LucasPlan S) : ℝ :=
  ∑' n, β ^ n * condE (mc.toTree s₀) (fun m g => u (pl.cX m g) (pl.cY m g)) n 0 Fin.elim0

/-- The no-trade plan of Exercise 6(b), O&R p. 347: consume `X/2`, `Y/2`, keep half of each
claim and hold no bonds. -/
noncomputable def lucasNoTrade (s₀ : S) (X Y : S → ℝ) : LucasPlan S :=
  ⟨fun n h => X (lastState s₀ n h) / 2, fun n h => Y (lastState s₀ n h) / 2,
    fun _ _ => 1 / 2, fun _ _ => 1 / 2, fun _ _ => 0⟩

/-- **The pricing identity for any admissible plan, Exercise 6(b), O&R p. 347**: if the
claim prices and bond rate satisfy the stationary Euler equations of part (a) with
marginal utility `m_X`, then along any plan satisfying the finance constraints, the cost
`A = B + xV_X + yV_Y` of the portfolio chosen and spending `e = C_X + pC_Y` satisfy
`m_X A_t = βE_t[m_X(e_{t+1} + A_{t+1})]`. -/
theorem lucas_plan_euler (mc : EndowmentChain S) (s₀ : S) (β : ℝ) (u : ℝ → ℝ → ℝ)
    {X Y VX VY p r mX : S → ℝ}
    (hEX : ∀ s, mX s * VX s = β * ∑ s', mc.P s s' * (mX s' * (X s' + VX s')))
    (hEY : ∀ s, mX s * VY s = β * ∑ s', mc.P s s' * (mX s' * (p s' * Y s' + VY s')))
    (hEB : ∀ s, mX s = (1 + r s) * (β * ∑ s', mc.P s s' * mX s'))
    {pl : LucasPlan S} (hpl : LucasAdmissible mc s₀ β u X Y VX VY p r pl) :
    EulerEq (mc.toTree s₀) β (fun n h => mX (lastState s₀ n h))
      (fun n h => pl.cX n h + p (lastState s₀ n h) * pl.cY n h)
      (fun n h => pl.B n h + pl.x n h * VX (lastState s₀ n h)
        + pl.y n h * VY (lastState s₀ n h)) := by
  intro n h
  simp only [EndowmentChain.toTree_q, lastState_snoc]
  have hpay : ∀ s, pl.cX (n + 1) (Fin.snoc h s) + p s * pl.cY (n + 1) (Fin.snoc h s)
      + (pl.B (n + 1) (Fin.snoc h s) + pl.x (n + 1) (Fin.snoc h s) * VX s
        + pl.y (n + 1) (Fin.snoc h s) * VY s)
      = (1 + r (lastState s₀ n h)) * pl.B n h + pl.x n h * (X s + VX s)
        + pl.y n h * (p s * Y s + VY s) := by
    intro s
    have := hpl.2.2.1 n h s
    unfold lucasFinance at this
    linarith
  simp only [hpay]
  have hsplit : ∑ s, mc.P (lastState s₀ n h) s * (mX s * ((1 + r (lastState s₀ n h))
      * pl.B n h + pl.x n h * (X s + VX s) + pl.y n h * (p s * Y s + VY s)))
      = (1 + r (lastState s₀ n h)) * pl.B n h * ∑ s, mc.P (lastState s₀ n h) s * mX s
        + pl.x n h * ∑ s, mc.P (lastState s₀ n h) s * (mX s * (X s + VX s))
        + pl.y n h * ∑ s, mc.P (lastState s₀ n h) s * (mX s * (p s * Y s + VY s)) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [hsplit]
  linear_combination pl.B n h * hEB (lastState s₀ n h) + pl.x n h * hEX (lastState s₀ n h)
    + pl.y n h * hEY (lastState s₀ n h)

/-- **Exercise 6(b), O&R p. 347: the no-trade allocation is optimal over all admissible
infinite plans.** Let `0 < β < 1`, `X, Y > 0`, `u` concave with partial derivatives
`u_X, u_Y` in the supporting-hyperplane sense, `m_X = u_X(X/2, Y/2) > 0`,
`m_Y = u_Y(X/2, Y/2)`, `p = m_Y/m_X`, `V_X, V_Y` the claim prices of part (c) and
`1 + r = m_X/(βE[m_X])`. Then the no-trade plan is admissible and gives each country at least
the expected utility of every admissible plan (finance constraints each period, bounded
holdings, convergent utility). The transversality property
`β^T E_1[m_X(A*_T − A_T)] → 0` is proved from boundedness of prices and holdings. -/
theorem lucas_noTrade_optimal (mc : EndowmentChain S) (s₀ : S) {β : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (u uX uY : ℝ → ℝ → ℝ) {X Y mX mY p VX VY r : S → ℝ}
    (hX : ∀ s, 0 < X s) (hY : ∀ s, 0 < Y s)
    (htan : ∀ a b a' b', 0 < a → 0 < b → 0 < a' → 0 < b' →
      u a' b' ≤ u a b + uX a b * (a' - a) + uY a b * (b' - b))
    (hmX : ∀ s, mX s = uX (X s / 2) (Y s / 2)) (hmY : ∀ s, mY s = uY (X s / 2) (Y s / 2))
    (hmXpos : ∀ s, 0 < mX s) (hp : ∀ s, p s = mY s / mX s)
    (hVX : VX = mc.markovPrice β mX X) (hVY : VY = mc.markovPrice β mX (fun s => p s * Y s))
    (hr : ∀ s, 1 + r s = mX s / (β * ∑ s', mc.P s s' * mX s')) :
    LucasAdmissible mc s₀ β u X Y VX VY p r (lucasNoTrade s₀ X Y) ∧
      ∀ pl, LucasAdmissible mc s₀ β u X Y VX VY p r pl →
        lucasUtility mc s₀ β u pl ≤ lucasUtility mc s₀ β u (lucasNoTrade s₀ X Y) := by
  have hEX : ∀ s, mX s * VX s = β * ∑ s', mc.P s s' * (mX s' * (X s' + VX s')) := by
    subst hVX; exact (markov_price_unique mc hβ0.le hβ1 mX X hmXpos).2.1
  have hEY : ∀ s, mX s * VY s = β * ∑ s', mc.P s s' * (mX s' * (p s' * Y s' + VY s')) := by
    subst hVY; exact (markov_price_unique mc hβ0.le hβ1 mX (fun s => p s * Y s) hmXpos).2.1
  have hEB : ∀ s, mX s = (1 + r s) * (β * ∑ s', mc.P s s' * mX s') := fun s => by
    rw [hr s, div_mul_cancel₀ _ (mul_pos hβ0 (chain_expect_pos mc hmXpos s)).ne']
  set tr := mc.toTree s₀ with htr
  -- bounds on state functions
  have bS : ∀ (f : S → ℝ) n (h : Fin n → S), |f (lastState s₀ n h)| ≤ ∑ s', |f s'| :=
    fun f n h => abs_le_sum_abs f _
  set ustar : TreeProcess S := fun m g => u (X (lastState s₀ m g) / 2) (Y (lastState s₀ m g) / 2)
    with hustar
  have hsumStar : Summable (fun n => β ^ n * condE tr ustar n 0 Fin.elim0) :=
    summable_discounted_condE tr hβ0.le hβ1
      (fun n h => bS (fun s => u (X s / 2) (Y s / 2)) n h) 0 Fin.elim0
  have hadm : LucasAdmissible mc s₀ β u X Y VX VY p r (lucasNoTrade s₀ X Y) := by
    refine ⟨fun n h => ⟨by simp [lucasNoTrade, hX], by simp [lucasNoTrade, hY]⟩, ?_, ?_,
      ⟨1 / 2, fun n h => by norm_num [lucasNoTrade]⟩, hsumStar⟩
    · simp only [lucasFinance, lucasNoTrade, lastState]
      ring
    · intro n h s
      simp only [lucasFinance, lucasNoTrade, lastState_snoc]
      ring
  refine ⟨hadm, fun pl hpl => ?_⟩
  obtain ⟨K, hK⟩ := hpl.2.2.2.1
  -- the two pricing identities
  have eP := lucas_plan_euler mc s₀ β u hEX hEY hEB hpl
  have eS := lucas_plan_euler mc s₀ β u hEX hEY hEB hadm
  set M : TreeProcess S := fun n h => mX (lastState s₀ n h) with hM
  set e1 : TreeProcess S := fun n h => pl.cX n h + p (lastState s₀ n h) * pl.cY n h with he1
  set A1 : TreeProcess S := fun n h => pl.B n h + pl.x n h * VX (lastState s₀ n h)
    + pl.y n h * VY (lastState s₀ n h) with hA1
  set e0 : TreeProcess S := fun n h => (lucasNoTrade s₀ X Y).cX n h
    + p (lastState s₀ n h) * (lucasNoTrade s₀ X Y).cY n h with he0
  set A0 : TreeProcess S := fun n h => (lucasNoTrade s₀ X Y).B n h
    + (lucasNoTrade s₀ X Y).x n h * VX (lastState s₀ n h)
    + (lucasNoTrade s₀ X Y).y n h * VY (lastState s₀ n h) with hA0
  -- date-1 wealth is the same
  have hroot : A1 0 Fin.elim0 + e1 0 Fin.elim0 = A0 0 Fin.elim0 + e0 0 Fin.elim0 := by
    have h1 := hpl.2.1
    have h2 := hadm.2.1
    simp only [lucasFinance] at h1 h2
    simp only [hA1, he1, hA0, he0, lastState]
    linarith
  -- concavity, date by date
  have hpt : ∀ m (g : Fin m → S), u (pl.cX m g) (pl.cY m g) - ustar m g
      ≤ M m g * e1 m g - M m g * e0 m g := by
    intro m g
    set σ := lastState s₀ m g
    have t := htan (X σ / 2) (Y σ / 2) (pl.cX m g) (pl.cY m g) (by linarith [hX σ])
      (by linarith [hY σ]) (hpl.1 m g).1 (hpl.1 m g).2
    rw [← hmX σ, ← hmY σ] at t
    have hmY' : mY σ = p σ * mX σ := by rw [hp σ]; field_simp [(hmXpos σ).ne']
    rw [hmY'] at t
    have e : M m g * e1 m g - M m g * e0 m g
        = mX σ * (pl.cX m g - X σ / 2) + p σ * mX σ * (pl.cY m g - Y σ / 2) := by
      simp only [hM, he1, he0, lucasNoTrade]
      ring
    rw [e]
    simp only [hustar]
    linarith
  have hterm : ∀ n, β ^ n * condE tr (fun m g => u (pl.cX m g) (pl.cY m g)) n 0 Fin.elim0
      - β ^ n * condE tr ustar n 0 Fin.elim0
      ≤ β ^ n * condE tr (fun m g => M m g * e1 m g) n 0 Fin.elim0
        - β ^ n * condE tr (fun m g => M m g * e0 m g) n 0 Fin.elim0 := by
    intro n
    rw [← mul_sub, ← mul_sub, ← condE.sub_apply, ← condE.sub_apply]
    exact mul_le_mul_of_nonneg_left (condE.mono_apply tr hpt n 0 Fin.elim0)
      (pow_nonneg hβ0.le n)
  -- transversality from bounded holdings and prices
  set KA : ℝ := (∑ s', |mX s'|) * (K + K * ∑ s', |VX s'| + K * ∑ s', |VY s'|)
    + (∑ s', |mX s'|) * (1 / 2 * ∑ s', |VX s'| + 1 / 2 * ∑ s', |VY s'|) with hKA
  have hbnd : ∀ m (g : Fin m → S), |M m g * A0 m g - M m g * A1 m g| ≤ KA := by
    intro m g
    have hx := (hK m g).1
    have hy := (hK m g).2.1
    have hB := (hK m g).2.2
    have hm := bS mX m g
    have hv := bS VX m g
    have hw := bS VY m g
    have h1 : |M m g * A1 m g| ≤ (∑ s', |mX s'|) * (K + K * ∑ s', |VX s'|
        + K * ∑ s', |VY s'|) := by
      rw [abs_mul]
      refine mul_le_mul hm ?_ (abs_nonneg _) (Finset.sum_nonneg fun _ _ => abs_nonneg _)
      calc |A1 m g| ≤ |pl.B m g| + |pl.x m g| * |VX (lastState s₀ m g)|
            + |pl.y m g| * |VY (lastState s₀ m g)| := by
            simp only [hA1]
            refine (abs_add_le _ _).trans ?_
            rw [abs_mul]
            gcongr
            refine (abs_add_le _ _).trans ?_
            rw [abs_mul]
        _ ≤ K + K * ∑ s', |VX s'| + K * ∑ s', |VY s'| := by
            gcongr
            · exact (abs_nonneg _).trans hx
            · exact (abs_nonneg _).trans hy
    have h0 : |M m g * A0 m g| ≤ (∑ s', |mX s'|) * (1 / 2 * ∑ s', |VX s'|
        + 1 / 2 * ∑ s', |VY s'|) := by
      rw [abs_mul]
      refine mul_le_mul hm ?_ (abs_nonneg _) (Finset.sum_nonneg fun _ _ => abs_nonneg _)
      simp only [hA0, lucasNoTrade, zero_add]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
      gcongr
    calc |M m g * A0 m g - M m g * A1 m g| ≤ |M m g * A0 m g| + |M m g * A1 m g| :=
          abs_sub _ _
      _ ≤ KA := by rw [hKA]; linarith
  have htv : Tendsto (fun T => β ^ T * condE tr (fun m g => M m g * A0 m g
      - M m g * A1 m g) T 0 Fin.elim0) atTop (𝓝 0) := by
    have hlim : Tendsto (fun T : ℕ => β ^ T * KA) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).mul_const KA
    refine squeeze_zero_norm (fun T => ?_) hlim
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_nonneg hβ0.le]
    exact mul_le_mul_of_nonneg_left (condE.abs_le_of_bound tr hbnd T 0 Fin.elim0)
      (pow_nonneg hβ0.le T)
  -- partial sums
  have hpart : ∀ T, ∑ n ∈ range (T + 1), (β ^ n * condE tr
      (fun m g => u (pl.cX m g) (pl.cY m g)) n 0 Fin.elim0
      - β ^ n * condE tr ustar n 0 Fin.elim0)
      ≤ β ^ T * condE tr (fun m g => M m g * A0 m g - M m g * A1 m g) T 0 Fin.elim0 := by
    intro T
    refine (Finset.sum_le_sum fun n _ => hterm n).trans (le_of_eq ?_)
    rw [Finset.sum_sub_distrib, plan_value_identity tr eP, plan_value_identity tr eS,
      condE.sub_apply, hroot]
    ring
  have hL : Tendsto (fun T => ∑ n ∈ range (T + 1), (β ^ n * condE tr
      (fun m g => u (pl.cX m g) (pl.cY m g)) n 0 Fin.elim0
      - β ^ n * condE tr ustar n 0 Fin.elim0)) atTop
      (𝓝 (lucasUtility mc s₀ β u pl - lucasUtility mc s₀ β u (lucasNoTrade s₀ X Y))) :=
    (tendsto_add_atTop_iff_nat 1).mpr (hpl.2.2.2.2.hasSum.sub hsumStar.hasSum).tendsto_sum_nat
  have := le_of_tendsto_of_tendsto' hL htv hpart
  linarith

/-- **Exercise 6(b), O&R p. 347: uniqueness of the equilibrium allocation.** Home and Foreign
have identical tastes `u`, strictly concave in the midpoint sense, and identical initial
portfolios, so they face the same admissible set (for any state-contingent prices `V_X, V_Y,
p` and bond rate `r`). If Home's plan `H` and Foreign's plan `F` are each optimal in that set
and goods markets clear (`C_X^H + C_X^F = X`, `C_Y^H + C_Y^F = Y`), then at every history of
positive probability `C_X = X/2` and `C_Y = Y/2` for both countries. (The average of the two
plans is admissible, consumes `(X/2, Y/2)`, and would otherwise be strictly better.) This is
the dynamic version of `OLGRiskSharing.lucas_allocation`. -/
theorem lucas_allocation_unique (mc : EndowmentChain S) (s₀ : S) {β : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (u : ℝ → ℝ → ℝ) {X Y VX VY p r : S → ℝ}
    (hstrict : ∀ a b a' b', 0 < a → 0 < b → 0 < a' → 0 < b' → (a ≠ a' ∨ b ≠ b') →
      (u a b + u a' b') / 2 < u ((a + a') / 2) ((b + b') / 2))
    {H F : LucasPlan S} (hH : LucasAdmissible mc s₀ β u X Y VX VY p r H)
    (hF : LucasAdmissible mc s₀ β u X Y VX VY p r F)
    (hHopt : ∀ pl, LucasAdmissible mc s₀ β u X Y VX VY p r pl →
      lucasUtility mc s₀ β u pl ≤ lucasUtility mc s₀ β u H)
    (hFopt : ∀ pl, LucasAdmissible mc s₀ β u X Y VX VY p r pl →
      lucasUtility mc s₀ β u pl ≤ lucasUtility mc s₀ β u F)
    (hcX : ∀ n h, H.cX n h + F.cX n h = X (lastState s₀ n h))
    (hcY : ∀ n h, H.cY n h + F.cY n h = Y (lastState s₀ n h))
    (n : ℕ) (h : Fin n → S) (hπ : 0 < (mc.toTree s₀).histProb h) :
    H.cX n h = X (lastState s₀ n h) / 2 ∧ H.cY n h = Y (lastState s₀ n h) / 2 ∧
      F.cX n h = X (lastState s₀ n h) / 2 ∧ F.cY n h = Y (lastState s₀ n h) / 2 := by
  set tr := mc.toTree s₀ with htr
  -- the average plan
  set mid : LucasPlan S := ⟨fun m g => (H.cX m g + F.cX m g) / 2,
    fun m g => (H.cY m g + F.cY m g) / 2, fun m g => (H.x m g + F.x m g) / 2,
    fun m g => (H.y m g + F.y m g) / 2, fun m g => (H.B m g + F.B m g) / 2⟩ with hmid
  set ustar : TreeProcess S := fun m g => u (X (lastState s₀ m g) / 2)
    (Y (lastState s₀ m g) / 2) with hustar
  have hmidu : (fun m g => u (mid.cX m g) (mid.cY m g)) = ustar := by
    funext m g
    simp only [hmid, hustar, hcX, hcY]
  have hsumStar : Summable (fun n => β ^ n * condE tr ustar n 0 Fin.elim0) :=
    summable_discounted_condE tr hβ0.le hβ1
      (fun n h => abs_le_sum_abs (fun s => u (X s / 2) (Y s / 2)) _) 0 Fin.elim0
  obtain ⟨KH, hKH⟩ := hH.2.2.2.1
  obtain ⟨KF, hKF⟩ := hF.2.2.2.1
  have hbd : ∀ a b : ℝ, |a| ≤ KH → |b| ≤ KF → |(a + b) / 2| ≤ (KH + KF) / 2 := by
    intro a b ha hb
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    exact div_le_div_of_nonneg_right ((abs_add_le a b).trans (add_le_add ha hb)) (by norm_num)
  have hadm : LucasAdmissible mc s₀ β u X Y VX VY p r mid := by
    refine ⟨fun m g => ⟨?_, ?_⟩, ?_, fun m g s => ?_, ⟨(KH + KF) / 2, fun m g =>
      ⟨hbd _ _ (hKH m g).1 (hKF m g).1, hbd _ _ (hKH m g).2.1 (hKF m g).2.1,
        hbd _ _ (hKH m g).2.2 (hKF m g).2.2⟩⟩, ?_⟩
    · simp only [hmid]; linarith [(hH.1 m g).1, (hF.1 m g).1]
    · simp only [hmid]; linarith [(hH.1 m g).2, (hF.1 m g).2]
    · have h1 := hH.2.1
      have h2 := hF.2.1
      simp only [lucasFinance, hmid] at h1 h2 ⊢
      linear_combination (h1 + h2) / 2
    · have h1 := hH.2.2.1 m g s
      have h2 := hF.2.2.1 m g s
      simp only [lucasFinance, hmid] at h1 h2 ⊢
      linear_combination (h1 + h2) / 2
    · rw [hmidu]; exact hsumStar
  have hUmid : lucasUtility mc s₀ β u mid = ∑' n, β ^ n * condE tr ustar n 0 Fin.elim0 := by
    unfold lucasUtility
    rw [hmidu]
  have hle1 := hHopt mid hadm
  have hle2 := hHopt F hF
  have hle3 := hFopt H hH
  -- pointwise weak midpoint concavity
  have hweak : ∀ m (g : Fin m → S), 1 / 2 * (u (H.cX m g) (H.cY m g) + u (F.cX m g) (F.cY m g))
      ≤ ustar m g := by
    intro m g
    have e1 : X (lastState s₀ m g) / 2 = (H.cX m g + F.cX m g) / 2 := by rw [hcX]
    have e2 : Y (lastState s₀ m g) / 2 = (H.cY m g + F.cY m g) / 2 := by rw [hcY]
    simp only [hustar, e1, e2]
    by_cases hc : H.cX m g ≠ F.cX m g ∨ H.cY m g ≠ F.cY m g
    · have := hstrict _ _ _ _ (hH.1 m g).1 (hH.1 m g).2 (hF.1 m g).1 (hF.1 m g).2 hc
      linarith
    · push Not at hc
      rw [hc.1, hc.2]
      have a1 : (F.cX m g + F.cX m g) / 2 = F.cX m g := by ring
      have a2 : (F.cY m g + F.cY m g) / 2 = F.cY m g := by ring
      rw [a1, a2]
      linarith
  by_contra hcon
  have hne : H.cX n h ≠ F.cX n h ∨ H.cY n h ≠ F.cY n h := by
    by_contra hc
    push Not at hc
    apply hcon
    have a := hcX n h
    have b := hcY n h
    refine ⟨?_, ?_, ?_, ?_⟩ <;> linarith [hc.1, hc.2]
  set avg : TreeProcess S := fun m g =>
    1 / 2 * (u (H.cX m g) (H.cY m g) + u (F.cX m g) (F.cY m g)) with havg
  have hsumAvg : HasSum (fun k => β ^ k * condE tr avg k 0 Fin.elim0)
      ((lucasUtility mc s₀ β u H + lucasUtility mc s₀ β u F) / 2) := by
    have := (hH.2.2.2.2.hasSum.add hF.2.2.2.2.hasSum).mul_left (1 / 2)
    unfold lucasUtility at this ⊢
    rw [show ∀ a b : ℝ, (a + b) / 2 = 1 / 2 * (a + b) from fun a b => by ring]
    refine this.congr_fun fun k => ?_
    simp only [havg, condE.smul_apply, condE.add_apply]
    ring
  have hlt : (lucasUtility mc s₀ β u H + lucasUtility mc s₀ β u F) / 2
      < ∑' k, β ^ k * condE tr ustar k 0 Fin.elim0 := by
    refine hasSum_lt (i := n) (fun k => mul_le_mul_of_nonneg_left
      (condE.mono_apply tr hweak k 0 Fin.elim0) (pow_nonneg hβ0.le k)) ?_ hsumAvg
      hsumStar.hasSum
    refine mul_lt_mul_of_pos_left ?_ (pow_pos hβ0 n)
    rw [condE_root_eq_sum_histProb, condE_root_eq_sum_histProb, ← sub_pos,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_pos' (fun g _ => ?_) ⟨h, Finset.mem_univ h, ?_⟩
    · rw [← mul_sub]
      exact mul_nonneg (tr.histProb_nonneg g) (sub_nonneg.mpr (hweak n g))
    · rw [← mul_sub]
      refine mul_pos hπ (sub_pos.mpr ?_)
      have e1 : X (lastState s₀ n h) / 2 = (H.cX n h + F.cX n h) / 2 := by rw [hcX]
      have e2 : Y (lastState s₀ n h) / 2 = (H.cY n h + F.cY n h) / 2 := by rw [hcY]
      simp only [hustar, e1, e2]
      have := hstrict _ _ _ _ (hH.1 n h).1 (hH.1 n h).2 (hF.1 n h).1 (hF.1 n h).2 hne
      linarith
  rw [← hUmid] at hlt
  linarith

end ObstfeldRogoff.InternationalFinancialMarkets.InfiniteHorizonPricing
