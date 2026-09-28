/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import CapitalMarketImperfections.ReputationTrigger

/-!
# The significance of reputation: Bulow–Rogoff, collateral, and no sovereign borrowing

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §6.1.2.3
(p. 373), §6.1.2.4 (pp. 373–375) and §6.2.2 (pp. 391–392).

**Bulow–Rogoff (1989b) on a general event tree (T11).** Shocks follow an arbitrary event tree
with finitely many branches (conditional probabilities `q`); the reputation contract calls for
bounded payments `P(h)` at every node; foreign insurers are risk neutral and price a claim
paying `a` at the successors of `h` at `Σ q a/(1 + r)`. `V(h)` is the market value (an infinite
sum) of the obligations after `h`, and `Q(h) = P(h) + V(h)`; we prove the recursion
`V(h) = Σ q Q(h′)/(1 + r)`. If `N = sup Q > 0`, then at a node with `Q(h) > N/(1 + r)` the
country can default and buy fully collateralised claims (never negative, bought with its own
money) paying `N − Q(h′)` at every later node, financed by holdings `N/(1 + r) − V`; this is
self-financing, raises consumption at the default node by `Q(h) − N/(1 + r) > 0` and at every
later node by `rN/(1 + r) > 0`, and hence is strictly preferred under any strictly increasing
utility. Therefore a contract immune to such deviations has `Q ≤ 0` at every node: the
country can never be a net debtor. The stationary corollary is the book's argument: with
per-period zero profit (13) no reputation-based insurance is possible.

**§6.2.2.** In a deterministic economy the same theorem says no sovereign borrowing; and with
exclusion as the only punishment, a country that no longer needs the market (all remaining
payments nonnegative) defaults, so no loan contract is incentive compatible.

**§6.1.2.3 (T12, Worrall's steady state).** With assets `B` that creditors can seize, the
stationary plan `P = ε`, `B` constant, `C = Ȳ + rB` satisfies the budget (12); honouring and
liquidating dominates default in every state iff `(1 + r)B ≥ ε̄`; in the Bulow–Rogoff world the
steady-state package has `Q = ε − (1 + r)B`, so `B ≥ B̄ = ε̄/(1 + r)` is also *necessary*; and
constant consumption `Ȳ + rB` is first best given `B` under actuarially fair complete markets
(`β(1 + r) = 1`). The convergence to `B̄` from below (Worrall 1990), a sketch in the book, is
proved for every optimal plan: at every node whose shock is `ε̄` (and in its whole subtree)
consumption equals `(1 − β)x + βȲ ≥ Ȳ + rB̄`, an optimal plan exists there with assets
constant at `β(x − Ȳ) ≥ B̄`, and the probability (and expected size) of a shortfall below
`Ȳ + rB̄` at date `n` is at most `(1 − π(ε̄))^{n+1} → 0`. For `B₀ ≥ B̄` the stationary plan is
optimal and every optimal plan consumes `Ȳ + rB₀` at every node.
-/

namespace ObstfeldRogoff.CapitalMarketImperfections.BulowRogoff

open Finset Filter Topology
open SovereignRiskPrimitives SovereignRiskPrimitives.StateSpaceFacts

/-- An event tree with finitely many branches (O&R p. 375, "the equilibrium tree"): after a
history of `k` shocks `g`, the next shock is `s` with conditional probability `q k g s`. -/
structure Tree (S : Type) [Fintype S] where
  q : (k : ℕ) → (Fin k → S) → S → ℝ
  q_nonneg : ∀ k g s, 0 ≤ q k g s
  q_sum : ∀ k g, ∑ s, q k g s = 1

namespace Tree

variable {S : Type} [Fintype S] (tr : Tree S)

/-- The i.i.d. tree of a finite state space (the stationary economy of §6.1.2.1).
(O&R §6.1.2.4, pp. 374–375) -/
def iid (Ω : StateSpace S) : Tree S :=
  ⟨fun _ _ s => Ω.prob s, fun _ _ s => Ω.prob_nonneg s, fun _ _ => Ω.prob_sum⟩

/-- The conditional expectation at node `h` (of length `k`) of a node-indexed process `X`,
`j` dates ahead: `ev X 0 k h = X(h)` and `ev X (j+1) k h = Σ_s q(h, s) ev X j (h, s)`.
(O&R §6.1.2.4, pp. 374–375) -/
noncomputable def ev (X : (k : ℕ) → (Fin k → S) → ℝ) : (j : ℕ) → (k : ℕ) → (Fin k → S) → ℝ
  | 0, k, h => X k h
  | j + 1, k, h => ∑ s, tr.q k h s * ev X j (k + 1) (Fin.snoc h s : Fin (k + 1) → S)

/-- Conditional expectations of a bounded process are bounded by the same constant.
(O&R §6.1.2.4, pp. 374–375) -/
theorem abs_ev_le {X : (k : ℕ) → (Fin k → S) → ℝ} {M : ℝ} (hX : ∀ k h, |X k h| ≤ M) :
    ∀ j k h, |tr.ev X j k h| ≤ M := by
  intro j
  induction j with
  | zero => intro k h; exact hX k h
  | succ j ih =>
    intro k h
    simp only [ev]
    calc |∑ s, tr.q k h s * tr.ev X j (k + 1) (Fin.snoc h s : Fin (k + 1) → S)|
        ≤ ∑ s, |tr.q k h s * tr.ev X j (k + 1) (Fin.snoc h s : Fin (k + 1) → S)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ s, tr.q k h s * M := Finset.sum_le_sum fun s _ => by
          rw [abs_mul, abs_of_nonneg (tr.q_nonneg k h s)]
          exact mul_le_mul_of_nonneg_left (ih _ _) (tr.q_nonneg k h s)
      _ = M := by rw [← Finset.sum_mul, tr.q_sum, one_mul]

/-- Conditional expectations are monotone on the subtree: if `X ≤ X'` at every node of length
greater than `k₀`, then `ev X (j + 1) k h ≤ ev X' (j + 1) k h` for every `k ≥ k₀`.
(O&R §6.1.2.4, pp. 374–375) -/
theorem ev_mono_after {X X' : (k : ℕ) → (Fin k → S) → ℝ} {k₀ : ℕ}
    (hle : ∀ k h, k₀ < k → X k h ≤ X' k h) :
    ∀ j k h, k₀ ≤ k → tr.ev X (j + 1) k h ≤ tr.ev X' (j + 1) k h := by
  intro j
  induction j with
  | zero =>
    intro k h hk
    simp only [ev]
    exact Finset.sum_le_sum fun s _ =>
      mul_le_mul_of_nonneg_left (hle _ _ (by omega)) (tr.q_nonneg k h s)
  | succ j ih =>
    intro k h hk
    rw [ev]
    conv_rhs => rw [ev]
    exact Finset.sum_le_sum fun s _ =>
      mul_le_mul_of_nonneg_left (ih _ _ (by omega)) (tr.q_nonneg k h s)

/-- Conditional expectations of a constant process.
(O&R §6.1.2.4, pp. 374–375) -/
theorem ev_const (c : ℝ) : ∀ j k h, tr.ev (fun _ _ => c) j k h = c := by
  intro j
  induction j with
  | zero => intro k h; rfl
  | succ j ih =>
    intro k h
    simp only [ev, ih, ← Finset.sum_mul, tr.q_sum, one_mul]

/-- The market value at node `h` of all obligations *after* `h` (O&R p. 375):
`V(h) = Σ_{j ≥ 1} (1 + r)^{−j} E_h[P_{t+j}]`, an infinite sum. -/
noncomputable def pv (r : ℝ) (P : (k : ℕ) → (Fin k → S) → ℝ) (k : ℕ) (h : Fin k → S) : ℝ :=
  ∑' j : ℕ, ((1 + r)⁻¹) ^ (j + 1) * tr.ev P (j + 1) k h

/-- The market value of the obligations from node `h` on, including the current payment:
`Q(h) = P(h) + V(h)`.
(O&R §6.1.2.4, pp. 374–375) -/
noncomputable def oblig (r : ℝ) (P : (k : ℕ) → (Fin k → S) → ℝ) (k : ℕ) (h : Fin k → S) :
    ℝ :=
  P k h + tr.pv r P k h

/-- The discounted series defining `V` converges for `r > 0` and bounded payments.
(O&R §6.1.2.4, pp. 374–375) -/
theorem summable_pv {r : ℝ} (hr : 0 < r) {P : (k : ℕ) → (Fin k → S) → ℝ} {M : ℝ}
    (hP : ∀ k h, |P k h| ≤ M) (k : ℕ) (h : Fin k → S) :
    Summable fun j : ℕ => ((1 + r)⁻¹) ^ (j + 1) * tr.ev P (j + 1) k h := by
  have hρ0 : 0 ≤ (1 + r)⁻¹ := by positivity
  have hρ1 : (1 + r)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have := Geometric.summable_of_bounded hρ0 hρ1 (x := fun j => (1 + r)⁻¹ * tr.ev P (j + 1) k h)
    (M := M) fun j => by
      rw [abs_mul, abs_of_nonneg hρ0]
      calc (1 + r)⁻¹ * |tr.ev P (j + 1) k h| ≤ 1 * M :=
            mul_le_mul (le_of_lt hρ1) (tr.abs_ev_le hP _ _ _) (abs_nonneg _) zero_le_one
        _ = M := one_mul M
  refine this.congr fun j => ?_
  ring

/-- The market value of future obligations is bounded: `|V(h)| ≤ M/r`.
(O&R §6.1.2.4, pp. 374–375) -/
theorem abs_pv_le {r : ℝ} (hr : 0 < r) {P : (k : ℕ) → (Fin k → S) → ℝ} {M : ℝ}
    (hP : ∀ k h, |P k h| ≤ M) (k : ℕ) (h : Fin k → S) : |tr.pv r P k h| ≤ M / r := by
  have hρ0 : 0 ≤ (1 + r)⁻¹ := by positivity
  have hρ1 : (1 + r)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hs := tr.summable_pv hr hP k h
  have hgeo := Geometric.hasSum_geometric_from_one hρ0 hρ1 M
  have hr0 : r ≠ 0 := hr.ne'
  have hd : (1 : ℝ) - (1 + r)⁻¹ ≠ 0 := by linarith
  have hval : (1 + r)⁻¹ / (1 - (1 + r)⁻¹) * M = M / r := by
    rw [div_mul_eq_mul_div, div_eq_div_iff hd hr0]
    field_simp
    ring
  rw [hval] at hgeo
  have hM : 0 ≤ M := le_trans (abs_nonneg _) (hP 0 Fin.elim0)
  unfold pv
  rw [abs_le]
  constructor
  · have := hgeo.neg.summable.tsum_le_tsum (f := fun j : ℕ => -(((1 + r)⁻¹) ^ (j + 1) * M))
      (g := fun j => ((1 + r)⁻¹) ^ (j + 1) * tr.ev P (j + 1) k h) (fun j => by
        have := (abs_le.mp (tr.abs_ev_le hP (j + 1) k h)).1
        have hp : 0 ≤ ((1 + r)⁻¹) ^ (j + 1) := pow_nonneg hρ0 _
        nlinarith) hs
    rw [hgeo.neg.tsum_eq] at this
    linarith
  · have := hs.tsum_le_tsum (g := fun j : ℕ => ((1 + r)⁻¹) ^ (j + 1) * M) (fun j => by
        have := (abs_le.mp (tr.abs_ev_le hP (j + 1) k h)).2
        exact mul_le_mul_of_nonneg_left this (pow_nonneg hρ0 _)) hgeo.summable
    rw [hgeo.tsum_eq] at this
    exact this

/-- **The recursion for the value of obligations** (O&R p. 375):
`V(h) = Σ_s q(h, s) Q(h, s)/(1 + r)`, i.e. `V(h) = E_h[P(h′) + V(h′)]/(1 + r)`. -/
theorem pv_recursion {r : ℝ} (hr : 0 < r) {P : (k : ℕ) → (Fin k → S) → ℝ} {M : ℝ}
    (hP : ∀ k h, |P k h| ≤ M) (k : ℕ) (h : Fin k → S) :
    tr.pv r P k h =
      (1 + r)⁻¹ * ∑ s, tr.q k h s * tr.oblig r P (k + 1) (Fin.snoc h s : Fin (k + 1) → S) := by
  unfold pv
  simp only [ev]
  set ρ := (1 + r)⁻¹
  -- each child's full value `Σ_j ρ^j ev_j = P + V`
  have hchild : ∀ s, Summable (fun j : ℕ => ρ ^ j * tr.ev P j (k + 1)
      (Fin.snoc h s : Fin (k + 1) → S)) ∧
      ∑' j : ℕ, ρ ^ j * tr.ev P j (k + 1) (Fin.snoc h s : Fin (k + 1) → S) =
        tr.oblig r P (k + 1) (Fin.snoc h s : Fin (k + 1) → S) := by
    intro s
    have hs := tr.summable_pv hr hP (k + 1) (Fin.snoc h s : Fin (k + 1) → S)
    have hs' : Summable (fun j : ℕ => ρ ^ j * tr.ev P j (k + 1)
        (Fin.snoc h s : Fin (k + 1) → S)) := by
      rw [← summable_nat_add_iff 1]
      exact hs
    refine ⟨hs', ?_⟩
    rw [hs'.tsum_eq_zero_add]
    simp only [pow_zero, one_mul, ev]
    rfl
  have e : ∀ j : ℕ, ρ ^ (j + 1) * ∑ s, tr.q k h s * tr.ev P j (k + 1)
      (Fin.snoc h s : Fin (k + 1) → S) =
      ∑ s, ρ * tr.q k h s * (ρ ^ j * tr.ev P j (k + 1) (Fin.snoc h s : Fin (k + 1) → S)) := by
    intro j; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro s _; ring
  simp only [e]
  rw [Summable.tsum_finsetSum (fun s _ => (hchild s).1.mul_left _)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro s _
  rw [(hchild s).1.tsum_mul_left, (hchild s).2]
  ring

/-- The recursion `V(h) = Σ_s q(h, s) Q(h, s)/(1 + r)` whenever the defining series converge
(O&R p. 375; used for growing payments). -/
theorem pv_recursion_of_summable {r : ℝ} {P : (k : ℕ) → (Fin k → S) → ℝ}
    (hs : ∀ k (h : Fin k → S),
      Summable fun j : ℕ => ((1 + r)⁻¹) ^ (j + 1) * tr.ev P (j + 1) k h)
    (k : ℕ) (h : Fin k → S) :
    tr.pv r P k h =
      (1 + r)⁻¹ * ∑ s, tr.q k h s * tr.oblig r P (k + 1) (Fin.snoc h s : Fin (k + 1) → S) := by
  unfold pv
  simp only [ev]
  set ρ := (1 + r)⁻¹
  -- each child's full value `Σ_j ρ^j ev_j = P + V`
  have hchild : ∀ s, Summable (fun j : ℕ => ρ ^ j * tr.ev P j (k + 1)
      (Fin.snoc h s : Fin (k + 1) → S)) ∧
      ∑' j : ℕ, ρ ^ j * tr.ev P j (k + 1) (Fin.snoc h s : Fin (k + 1) → S) =
        tr.oblig r P (k + 1) (Fin.snoc h s : Fin (k + 1) → S) := by
    intro s
    have hs := hs (k + 1) (Fin.snoc h s : Fin (k + 1) → S)
    have hs' : Summable (fun j : ℕ => ρ ^ j * tr.ev P j (k + 1)
        (Fin.snoc h s : Fin (k + 1) → S)) := by
      rw [← summable_nat_add_iff 1]
      exact hs
    refine ⟨hs', ?_⟩
    rw [hs'.tsum_eq_zero_add]
    simp only [pow_zero, one_mul, ev]
    rfl
  have e : ∀ j : ℕ, ρ ^ (j + 1) * ∑ s, tr.q k h s * tr.ev P j (k + 1)
      (Fin.snoc h s : Fin (k + 1) → S) =
      ∑ s, ρ * tr.q k h s * (ρ ^ j * tr.ev P j (k + 1) (Fin.snoc h s : Fin (k + 1) → S)) := by
    intro j; rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro s _; ring
  simp only [e]
  rw [Summable.tsum_finsetSum (fun s _ => (hchild s).1.mul_left _)]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro s _
  rw [(hchild s).1.tsum_mul_left, (hchild s).2]
  ring

/-- The value of obligations is bounded, `|Q| ≤ M + M/r`.
(O&R §6.1.2.4, pp. 374–375) -/
theorem abs_oblig_le {r : ℝ} (hr : 0 < r) {P : (k : ℕ) → (Fin k → S) → ℝ} {M : ℝ}
    (hP : ∀ k h, |P k h| ≤ M) (k : ℕ) (h : Fin k → S) :
    |tr.oblig r P k h| ≤ M + M / r := by
  unfold oblig
  exact le_trans (abs_add_le _ _) (add_le_add (hP k h) (tr.abs_pv_le hr hP k h))

end Tree

/-! ## The Bulow–Rogoff theorem -/

namespace Theorem

variable {S : Type} [Fintype S] (tr : Tree S)

/-- A fully collateralised self-financing deviation (O&R p. 374): after defaulting at node
`h₀`, the country holds `A(h) ≥ 0` in claims at every node, bought at the insurers' price
`A(h) = Σ_s q(h, s) a(h, s)/(1 + r)` for claims paying `a ≥ 0` at the successors. The contract
is **immune** to such deviations if none of them raises consumption weakly at every later node
(`P + a − A ≥ 0`) and strictly at the default node (`P(h₀) − A(h₀) > 0`). -/
def Immune (r : ℝ) (P : (k : ℕ) → (Fin k → S) → ℝ) : Prop :=
  ∀ (A a : (k : ℕ) → (Fin k → S) → ℝ) (k₀ : ℕ) (h₀ : Fin k₀ → S),
    (∀ k h, 0 ≤ a k h) →
    (∀ k h, A k h = (1 + r)⁻¹ * ∑ s, tr.q k h s * a (k + 1) (Fin.snoc h s : Fin (k + 1) → S)) →
    (∀ k (h : Fin k → S) s, 0 ≤ P (k + 1) (Fin.snoc h s : Fin (k + 1) → S) +
      a (k + 1) (Fin.snoc h s : Fin (k + 1) → S) - A (k + 1) (Fin.snoc h s : Fin (k + 1) → S)) →
    P k₀ h₀ - A k₀ h₀ ≤ 0

/-- The supremum `N` of the values of obligations over all nodes.
(O&R §6.1.2.4, pp. 374–375) -/
noncomputable def supOblig (r : ℝ) (P : (k : ℕ) → (Fin k → S) → ℝ) : ℝ :=
  sSup (Set.range fun p : (Σ k, Fin k → S) => tr.oblig r P p.1 p.2)

/-- The values of obligations are bounded above (bounded payments, `r > 0`).
(O&R §6.1.2.4, pp. 374–375) -/
theorem bddAbove_oblig {r : ℝ} (hr : 0 < r) {P : (k : ℕ) → (Fin k → S) → ℝ} {M : ℝ}
    (hP : ∀ k h, |P k h| ≤ M) :
    BddAbove (Set.range fun p : (Σ k, Fin k → S) => tr.oblig r P p.1 p.2) :=
  ⟨M + M / r, by
    rintro _ ⟨p, rfl⟩
    exact le_trans (le_abs_self _) (tr.abs_oblig_le hr hP p.1 p.2)⟩

/-- Every node's obligations are at most the supremum.
(O&R §6.1.2.4, pp. 374–375) -/
theorem oblig_le_sup {r : ℝ} (hr : 0 < r) {P : (k : ℕ) → (Fin k → S) → ℝ} {M : ℝ}
    (hP : ∀ k h, |P k h| ≤ M) (k : ℕ) (h : Fin k → S) :
    tr.oblig r P k h ≤ supOblig tr r P :=
  le_csSup (bddAbove_oblig tr hr hP) ⟨⟨k, h⟩, rfl⟩

/-- **The self-financing deviation** (O&R p. 374; Bulow and Rogoff 1989b), general event tree.
With `N = sup Q > 0` and `K = N/(1 + r)`, the claims `a = N − Q ≥ 0` bought with holdings
`A = K − V ≥ 0` at the insurers' price make consumption rise by exactly `rK` at every node
after the default, and there is a node `h₀` where defaulting raises current consumption by
`Q(h₀) − K > 0`. -/
theorem self_financing_deviation {r : ℝ} (hr : 0 < r) {P : (k : ℕ) → (Fin k → S) → ℝ} {M : ℝ}
    (hP : ∀ k h, |P k h| ≤ M) (hN : 0 < supOblig tr r P) :
    let N := supOblig tr r P
    let K := N / (1 + r)
    let a : (k : ℕ) → (Fin k → S) → ℝ := fun k h => N - tr.oblig r P k h
    let A : (k : ℕ) → (Fin k → S) → ℝ := fun k h => K - tr.pv r P k h
    (∀ k h, 0 ≤ a k h) ∧ (∀ k h, 0 ≤ A k h) ∧
      (∀ k h, A k h = (1 + r)⁻¹ * ∑ s, tr.q k h s * a (k + 1) (Fin.snoc h s : Fin (k + 1) → S)) ∧
      (∀ k (h : Fin k → S) s, P (k + 1) (Fin.snoc h s : Fin (k + 1) → S) +
        a (k + 1) (Fin.snoc h s : Fin (k + 1) → S) - A (k + 1) (Fin.snoc h s : Fin (k + 1) → S) =
          r * K) ∧
      ∃ k₀ h₀, 0 < P k₀ h₀ - A k₀ h₀ := by
  intro N K a A
  have h1r : 0 < 1 + r := by linarith
  have hle := oblig_le_sup tr hr hP
  have hVle : ∀ k h, tr.pv r P k h ≤ K := by
    intro k h
    rw [tr.pv_recursion hr hP]
    have : ∑ s, tr.q k h s * tr.oblig r P (k + 1) (Fin.snoc h s : Fin (k + 1) → S) ≤ N := by
      calc ∑ s, tr.q k h s * tr.oblig r P (k + 1) (Fin.snoc h s : Fin (k + 1) → S)
          ≤ ∑ s, tr.q k h s * N :=
            Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hle _ _) (tr.q_nonneg _ _ _)
        _ = N := by rw [← Finset.sum_mul, tr.q_sum, one_mul]
    have hK : K = (1 + r)⁻¹ * N := by simp only [K]; rw [div_eq_inv_mul]
    rw [hK]
    exact mul_le_mul_of_nonneg_left this (by positivity)
  refine ⟨fun k h => by simp only [a]; linarith [hle k h], fun k h => by
      simp only [A]; linarith [hVle k h], fun k h => ?_, fun k h s => ?_, ?_⟩
  · simp only [A, a]
    rw [tr.pv_recursion hr hP]
    have : ∑ s, tr.q k h s * (N - tr.oblig r P (k + 1) (Fin.snoc h s : Fin (k + 1) → S)) =
        N - ∑ s, tr.q k h s * tr.oblig r P (k + 1) (Fin.snoc h s : Fin (k + 1) → S) := by
      rw [show (fun s => tr.q k h s * (N - tr.oblig r P (k + 1)
          (Fin.snoc h s : Fin (k + 1) → S))) = fun s => tr.q k h s * N -
          tr.q k h s * tr.oblig r P (k + 1) (Fin.snoc h s : Fin (k + 1) → S) from
          funext fun s => by ring, Finset.sum_sub_distrib, ← Finset.sum_mul, tr.q_sum, one_mul]
    rw [this]
    simp only [K]
    rw [div_eq_inv_mul]; ring
  · simp only [A, a, Tree.oblig, K]
    field_simp
    ring
  · have hKN : K < N := by
      simp only [K]; rw [div_lt_iff₀ h1r]; nlinarith
    have : Nonempty ((k : ℕ) × (Fin k → S)) := ⟨⟨0, Fin.elim0⟩⟩
    obtain ⟨_, ⟨p, rfl⟩, hp⟩ := exists_lt_of_lt_csSup (Set.range_nonempty _) hKN
    refine ⟨p.1, p.2, ?_⟩
    simp only [A]
    simp only [Tree.oblig] at hp
    linarith

/-- **The Bulow–Rogoff no-reputation theorem** (O&R §6.1.2.4, pp. 373–375; Bulow and Rogoff
1989b), in the general event-tree form: with `r > 0` and bounded payments, a reputation
contract immune to fully collateralised self-financing deviations has
`Q(h) = P(h) + V(h) ≤ 0` at every node — the market value of the country's remaining
obligations is never positive, so reputation alone supports no net lending to it. -/
theorem bulow_rogoff {r : ℝ} (hr : 0 < r) {P : (k : ℕ) → (Fin k → S) → ℝ} {M : ℝ}
    (hP : ∀ k h, |P k h| ≤ M) (himm : Immune tr r P) :
    ∀ k h, tr.oblig r P k h ≤ 0 := by
  by_contra hne; push Not at hne
  obtain ⟨k, h, hkh⟩ := hne
  have hN : 0 < supOblig tr r P := lt_of_lt_of_le hkh (oblig_le_sup tr hr hP k h)
  obtain ⟨ha, _, hA, hcons, k₀, h₀, hpos⟩ := self_financing_deviation tr hr hP hN
  have hK : 0 ≤ r * (supOblig tr r P / (1 + r)) :=
    mul_nonneg hr.le (div_nonneg hN.le (by linarith))
  have := himm _ _ k₀ h₀ ha hA (fun k h s => by rw [hcons k h s]; exact hK)
  linarith

/-- **The deviation is strictly preferred under any strictly increasing utility** (O&R p. 374:
"the country must come out ahead"). Let honouring consumption `c = Y − P` be bounded between
positive constants, and let `c′` be the deviation consumption from `h₀`: `c′(h₀) = Y(h₀) − A(h₀)`
and `c′ = Y + a − A` afterwards. If `c′ ≥ c` at every later node and `c′(h₀) > c(h₀)`, the
continuation expected utility `Σ_j βʲ E_{h₀} u(c′)` strictly exceeds that of honouring. -/
theorem deviation_preferred (U : Utility) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (c c' : (k : ℕ) → (Fin k → S) → ℝ) {lo hi : ℝ} (hlo : 0 < lo)
    (hc : ∀ k h, lo ≤ c k h ∧ c k h ≤ hi) (hc' : ∀ k h, lo ≤ c' k h ∧ c' k h ≤ hi)
    {k₀ : ℕ} {h₀ : Fin k₀ → S} (hafter : ∀ k h, k₀ < k → c k h ≤ c' k h)
    (hnow : c k₀ h₀ < c' k₀ h₀) :
    ∑' j, β ^ j * tr.ev (fun k h => U.u (c k h)) j k₀ h₀ <
      ∑' j, β ^ j * tr.ev (fun k h => U.u (c' k h)) j k₀ h₀ := by
  have hb : ∀ (d : (k : ℕ) → (Fin k → S) → ℝ), (∀ k h, lo ≤ d k h ∧ d k h ≤ hi) →
      ∀ k h, |U.u (d k h)| ≤ |U.u lo| + |U.u hi| := by
    intro d hd k h
    have h1 := U.mono hlo (hd k h).1
    have h2 := U.mono (lt_of_lt_of_le hlo (hd k h).1) (hd k h).2
    rw [abs_le]
    constructor
    · have := neg_abs_le (U.u lo); have := abs_nonneg (U.u hi); linarith
    · have := le_abs_self (U.u hi); have := abs_nonneg (U.u lo); linarith
  have hs := Geometric.summable_of_bounded hβ0 hβ1
    (fun j => tr.abs_ev_le (hb c hc) j k₀ h₀)
  have hs' := Geometric.summable_of_bounded hβ0 hβ1
    (fun j => tr.abs_ev_le (hb c' hc') j k₀ h₀)
  rw [hs.tsum_eq_zero_add, hs'.tsum_eq_zero_add]
  have h0 : tr.ev (fun k h => U.u (c k h)) 0 k₀ h₀ < tr.ev (fun k h => U.u (c' k h)) 0 k₀ h₀ :=
    U.lt (lt_of_lt_of_le hlo (hc k₀ h₀).1) hnow
  have hrest : ∑' j, β ^ (j + 1) * tr.ev (fun k h => U.u (c k h)) (j + 1) k₀ h₀ ≤
      ∑' j, β ^ (j + 1) * tr.ev (fun k h => U.u (c' k h)) (j + 1) k₀ h₀ := by
    refine ((summable_nat_add_iff 1).mpr hs).tsum_le_tsum (fun j => ?_)
      ((summable_nat_add_iff 1).mpr hs')
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg hβ0 _)
    exact tr.ev_mono_after (fun k h hk => U.mono (lt_of_lt_of_le hlo (hc k h).1)
      (hafter k h hk)) j k₀ h₀ le_rfl
  simp only [pow_zero, one_mul]
  linarith

/-! ### The stationary corollary: the book's version -/

/-- **No reputation-based insurance in the stationary economy** (O&R p. 375): on the i.i.d.
tree, a stationary contract `P(ε)` satisfying the per-period zero-profit condition (13) and
immune to collateralised deviations is the null contract (in every state of positive
probability). -/
theorem stationary_no_reputation (Ω : StateSpace S) (hpos : ∀ s, 0 < Ω.prob s) {r : ℝ}
    (hr : 0 < r) (p : S → ℝ) (hzp : Ω.expect p = 0)
    (himm : Immune (Tree.iid Ω) r (fun k h => if hk : 0 < k then p (h ⟨k - 1, by omega⟩)
      else 0)) :
    p = 0 := by
  set P : (k : ℕ) → (Fin k → S) → ℝ := fun k h => if hk : 0 < k then p (h ⟨k - 1, by omega⟩)
    else 0 with hPdef
  have hPb : ∀ k h, |P k h| ≤ ∑ t, |p t| := by
    intro k h
    simp only [hPdef]
    split_ifs
    · exact ReputationTrigger.Trigger.abs_le_sum_abs p _
    · simp only [abs_zero]; exact Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hchild : ∀ k (h : Fin k → S) s, P (k + 1) (Fin.snoc h s : Fin (k + 1) → S) = p s := by
    intro k h s
    simp only [hPdef, Nat.zero_lt_succ, ↓reduceDIte]
    congr 1
    have : (⟨k + 1 - 1, by omega⟩ : Fin (k + 1)) = Fin.last k := by ext; simp
    rw [this, Fin.snoc_last]
  -- all conditional expectations one or more periods ahead vanish
  have hev : ∀ j k h, (Tree.iid Ω).ev P (j + 1) k h = 0 := by
    intro j
    induction j with
    | zero =>
      intro k h
      simp only [Tree.ev, Tree.iid, hchild]
      exact hzp
    | succ j ih =>
      intro k h
      rw [Tree.ev]
      simp only [ih, mul_zero, Finset.sum_const_zero]
  have hV : ∀ k h, (Tree.iid Ω).pv r P k h = 0 := by
    intro k h; simp [Tree.pv, hev]
  have hQ := bulow_rogoff (Tree.iid Ω) hr hPb himm
  funext s
  have hle : ∀ t, p t ≤ 0 := fun t => by
    have := hQ 1 (Fin.snoc (Fin.elim0 : Fin 0 → S) t : Fin 1 → S)
    simp only [Tree.oblig, hV, add_zero] at this
    rw [hchild 0 Fin.elim0 t] at this
    exact this
  exact eq_zero_of_nonpos_of_expect_zero Ω hle hzp (hpos s)

/-- **Per-period zero profit on a general tree** (O&R p. 375): if insurers break even at every
node, `Σ_s q(h, s) P(h, s) = 0`, then `V ≡ 0` and an immune contract never calls for a positive
payment at any node after the root. -/
theorem node_zero_profit_no_payment {r : ℝ} (hr : 0 < r) {P : (k : ℕ) → (Fin k → S) → ℝ}
    {M : ℝ} (hP : ∀ k h, |P k h| ≤ M)
    (hzp : ∀ k h, ∑ s, tr.q k h s * P (k + 1) (Fin.snoc h s : Fin (k + 1) → S) = 0)
    (himm : Immune tr r P) : ∀ k (h : Fin k → S) s,
      P (k + 1) (Fin.snoc h s : Fin (k + 1) → S) ≤ 0 := by
  have hev : ∀ j k h, tr.ev P (j + 1) k h = 0 := by
    intro j
    induction j with
    | zero => intro k h; simp only [Tree.ev]; exact hzp k h
    | succ j ih =>
      intro k h
      rw [Tree.ev]
      simp only [ih, mul_zero, Finset.sum_const_zero]
  have hV : ∀ k h, tr.pv r P k h = 0 := by intro k h; simp [Tree.pv, hev]
  intro k h s
  have := bulow_rogoff tr hr hP himm (k + 1) (Fin.snoc h s : Fin (k + 1) → S)
  simp only [Tree.oblig, hV, add_zero] at this
  exact this

/-- Incentive compatibility in expected-utility form (O&R p. 374): at no node `h₀` does a
fully collateralised self-financing deviation — any consumption process `c′` that equals
`Y − A` at `h₀` and `Y + a − A` at every later node, with positive bounded values — give a
continuation expected utility `Σ_j βʲ E_{h₀} u(c′)` above that of honouring, `c = Y − P`. -/
def ICUtility (U : Utility) (β r : ℝ) (Y P : (k : ℕ) → (Fin k → S) → ℝ) : Prop :=
  ∀ (A a c' : (k : ℕ) → (Fin k → S) → ℝ) (k₀ : ℕ) (h₀ : Fin k₀ → S),
    (∀ k h, 0 ≤ a k h) →
    (∀ k h, A k h = (1 + r)⁻¹ * ∑ s, tr.q k h s * a (k + 1) (Fin.snoc h s : Fin (k + 1) → S)) →
    (∀ k h, k₀ < k → c' k h = Y k h + a k h - A k h) → c' k₀ h₀ = Y k₀ h₀ - A k₀ h₀ →
    (∃ lo hi, 0 < lo ∧ ∀ k h, lo ≤ c' k h ∧ c' k h ≤ hi) →
    ∑' j, β ^ j * tr.ev (fun k h => U.u (c' k h)) j k₀ h₀ ≤
      ∑' j, β ^ j * tr.ev (fun k h => U.u (Y k h - P k h)) j k₀ h₀

/-- **The Bulow–Rogoff theorem in expected-utility form**, O&R §6.1.2.4, pp. 373–375, as a
single statement: with `r > 0`, bounded payments, honouring consumption `Y − P` between
positive bounds and any strictly increasing (strictly concave) utility, a contract that is
incentive compatible against collateralised self-financing deviations has
`Q(h) = P(h) + V(h) ≤ 0` at every node. -/
theorem bulow_rogoff_expected_utility (U : Utility) {β r : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (hr : 0 < r) {Y P : (k : ℕ) → (Fin k → S) → ℝ} {M lo hi : ℝ} (hP : ∀ k h, |P k h| ≤ M)
    (hlo : 0 < lo) (hc : ∀ k h, lo ≤ Y k h - P k h ∧ Y k h - P k h ≤ hi)
    (hIC : ICUtility tr U β r Y P) : ∀ k h, tr.oblig r P k h ≤ 0 := by
  classical
  by_contra hne; push Not at hne
  obtain ⟨k, h, hkh⟩ := hne
  have hN : 0 < supOblig tr r P := lt_of_lt_of_le hkh (oblig_le_sup tr hr hP k h)
  obtain ⟨ha, hA0, hA, hcons, k₀, h₀, hpos⟩ := self_financing_deviation tr hr hP hN
  set N := supOblig tr r P
  set K := N / (1 + r)
  set a : (k : ℕ) → (Fin k → S) → ℝ := fun k h => N - tr.oblig r P k h
  set A : (k : ℕ) → (Fin k → S) → ℝ := fun k h => K - tr.pv r P k h
  set c : (k : ℕ) → (Fin k → S) → ℝ := fun k h => Y k h - P k h
  set c' : (k : ℕ) → (Fin k → S) → ℝ := fun k h =>
    if k₀ < k then c k h + r * K else if k = k₀ then max (c k h) (Y k h - A k h) else c k h
  have hK0 : 0 ≤ r * K := mul_nonneg hr.le (div_nonneg hN.le (by linarith))
  have hafter : ∀ k h, k₀ < k → c' k h = Y k h + a k h - A k h := by
    intro k h hk
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    simp only [c', hk, ↓reduceIte, c]
    have := hcons k' (Fin.init h) (h (Fin.last k'))
    rw [Fin.snoc_init_self] at this
    linarith
  have hnow : c' k₀ h₀ = Y k₀ h₀ - A k₀ h₀ := by
    simp only [c', lt_irrefl, ↓reduceIte, c]
    exact max_eq_right (by linarith)
  -- bounds
  have hAb : ∀ k h, A k h ≤ K + M / r := fun k h => by
    have := tr.abs_pv_le hr hP k h
    simp only [A]; linarith [neg_abs_le (tr.pv r P k h)]
  have hbd : ∀ k h, lo ≤ c' k h ∧ c' k h ≤ hi + r * K + M + K + M / r := by
    intro k h
    have hc1 := hc k h
    have hMpos : 0 ≤ M := le_trans (abs_nonneg _) (hP k h)
    have hMr : 0 ≤ M / r := div_nonneg hMpos hr.le
    have hK : 0 ≤ K := div_nonneg hN.le (by linarith)
    simp only [c']
    split_ifs
    · simp only [c]; constructor <;> linarith
    · constructor
      · exact le_trans hc1.1 (le_max_left _ _)
      · apply max_le (by simp only [c]; linarith)
        have := hA0 k h
        have hPk := (abs_le.mp (hP k h)).2
        linarith
    · simp only [c]; constructor <;> linarith
  have hle := hIC A a c' k₀ h₀ ha hA hafter hnow
    ⟨lo, hi + r * K + M + K + M / r, hlo, hbd⟩
  have hlt := deviation_preferred tr U hβ0 hβ1 c c' hlo
    (fun k h => ⟨(hc k h).1, by have := hc k h; have := hK0
                                have hMpos : 0 ≤ M := le_trans (abs_nonneg _) (hP k h)
                                have hMr : 0 ≤ M / r := div_nonneg hMpos hr.le
                                have hK : 0 ≤ K := div_nonneg hN.le (by linarith)
                                simp only [c] at *; linarith⟩) hbd
    (fun k h hk => by rw [hafter k h hk]; simp only [c]
                      have := hcons; linarith [show Y k h + a k h - A k h = c k h + r * K from by
                        obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
                        have := hcons k' (Fin.init h) (h (Fin.last k'))
                        rw [Fin.snoc_init_self] at this
                        simp only [c]; linarith])
    (by rw [hnow]; simp only [c]; linarith)
  simp only [c] at hlt
  linarith

end Theorem


/-! ## Bulow–Rogoff with growing payments (p. 375) -/

namespace Growth

variable {S : Type} [Fintype S] (tr : Tree S)

/-- Conditional expectations of a process growing at most geometrically,
`|X(h)| ≤ M wᵏ` at nodes of length `k`, grow at most geometrically (O&R p. 375). -/
theorem abs_ev_le_growth {X : (k : ℕ) → (Fin k → S) → ℝ} {M w : ℝ}
    (hX : ∀ k h, |X k h| ≤ M * w ^ k) : ∀ j k h, |tr.ev X j k h| ≤ M * w ^ (k + j) := by
  intro j
  induction j with
  | zero => intro k h; simp only [Tree.ev, add_zero]; exact hX k h
  | succ j ih =>
    intro k h
    simp only [Tree.ev]
    calc |∑ s, tr.q k h s * tr.ev X j (k + 1) (Fin.snoc h s : Fin (k + 1) → S)|
        ≤ ∑ s, |tr.q k h s * tr.ev X j (k + 1) (Fin.snoc h s : Fin (k + 1) → S)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ s, tr.q k h s * (M * w ^ (k + 1 + j)) := Finset.sum_le_sum fun s _ => by
          rw [abs_mul, abs_of_nonneg (tr.q_nonneg k h s)]
          exact mul_le_mul_of_nonneg_left (ih _ _) (tr.q_nonneg k h s)
      _ = M * w ^ (k + (j + 1)) := by
          rw [← Finset.sum_mul, tr.q_sum, one_mul]; congr 2; omega

/-- With payments growing at a rate below the interest rate (`0 < w < 1 + r`), the market
value of future obligations converges (O&R p. 375: it cannot exceed the value of output). -/
theorem summable_pv_growth {r : ℝ} (hr : 0 < r) {P : (k : ℕ) → (Fin k → S) → ℝ} {M w : ℝ}
    (hw : 0 < w) (hwr : w < 1 + r) (hP : ∀ k h, |P k h| ≤ M * w ^ k) (k : ℕ)
    (h : Fin k → S) :
    Summable fun j : ℕ => ((1 + r)⁻¹) ^ (j + 1) * tr.ev P (j + 1) k h := by
  have h1r : 0 < 1 + r := by linarith
  set ρw := (1 + r)⁻¹ * w with hρw
  have hρw0 : 0 ≤ ρw := by positivity
  have hρw1 : ρw < 1 := by rw [hρw, inv_mul_lt_iff₀ h1r, mul_one]; exact hwr
  have hg := (summable_geometric_of_lt_one hρw0 hρw1).mul_left (M * w ^ k * ρw)
  refine Summable.of_norm_bounded hg fun j => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity)]
  have hb := abs_ev_le_growth tr hP (j + 1) k h
  calc ((1 + r)⁻¹) ^ (j + 1) * |tr.ev P (j + 1) k h|
      ≤ ((1 + r)⁻¹) ^ (j + 1) * (M * w ^ (k + (j + 1))) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
    _ = M * w ^ k * ρw * ρw ^ j := by rw [hρw, mul_pow, pow_add]; ring

/-- The value of future obligations is bounded by `M wᵏ ρw/(1 − ρw)`, `ρ = 1/(1 + r)`.
(O&R p. 375) -/
theorem abs_pv_le_growth {r : ℝ} (hr : 0 < r) {P : (k : ℕ) → (Fin k → S) → ℝ} {M w : ℝ}
    (hw : 0 < w) (hwr : w < 1 + r) (hP : ∀ k h, |P k h| ≤ M * w ^ k) (k : ℕ)
    (h : Fin k → S) :
    |tr.pv r P k h| ≤ M * w ^ k * ((1 + r)⁻¹ * w / (1 - (1 + r)⁻¹ * w)) := by
  have h1r : 0 < 1 + r := by linarith
  set ρw := (1 + r)⁻¹ * w with hρw
  have hρw0 : 0 ≤ ρw := by positivity
  have hρw1 : ρw < 1 := by rw [hρw, inv_mul_lt_iff₀ h1r, mul_one]; exact hwr
  have hs := summable_pv_growth tr hr hw hwr hP k h
  have hgeo := (Geometric.hasSum_geometric_from_one hρw0 hρw1 (M * w ^ k))
  have hbnd : ∀ j : ℕ, |((1 + r)⁻¹) ^ (j + 1) * tr.ev P (j + 1) k h| ≤
      ρw ^ (j + 1) * (M * w ^ k) := by
    intro j
    rw [abs_mul, abs_of_nonneg (by positivity)]
    have hb := abs_ev_le_growth tr hP (j + 1) k h
    calc ((1 + r)⁻¹) ^ (j + 1) * |tr.ev P (j + 1) k h|
        ≤ ((1 + r)⁻¹) ^ (j + 1) * (M * w ^ (k + (j + 1))) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = ρw ^ (j + 1) * (M * w ^ k) := by rw [hρw, mul_pow, pow_add]; ring
  unfold Tree.pv
  rw [abs_le]
  constructor
  · have := hgeo.neg.summable.tsum_le_tsum (f := fun j : ℕ => -(ρw ^ (j + 1) * (M * w ^ k)))
      (g := fun j => ((1 + r)⁻¹) ^ (j + 1) * tr.ev P (j + 1) k h)
      (fun j => by have := (abs_le.mp (hbnd j)).1; linarith) hs
    rw [hgeo.neg.tsum_eq] at this
    have e : -(ρw / (1 - ρw) * (M * w ^ k)) = -(M * w ^ k * (ρw / (1 - ρw))) := by ring
    linarith
  · have := hs.tsum_le_tsum (g := fun j : ℕ => ρw ^ (j + 1) * (M * w ^ k))
      (fun j => (abs_le.mp (hbnd j)).2) hgeo.summable
    rw [hgeo.tsum_eq] at this
    linarith

/-- The supremum of the growth-normalised obligations `Q(h)/wᵏ`. (O&R p. 375) -/
noncomputable def supObligG (r w : ℝ) (P : (k : ℕ) → (Fin k → S) → ℝ) : ℝ :=
  sSup (Set.range fun p : (Σ k, Fin k → S) => tr.oblig r P p.1 p.2 / w ^ p.1)

/-- **Bulow–Rogoff with payments growing at a rate below the interest rate**, O&R p. 375
("in a growing economy, the largest possible reputation payment may be growing over time"):
if `|P(h)| ≤ M wᵏ` at nodes of length `k` with `0 < w < 1 + r` (payments growing at rate
`g = w − 1 < r`, e.g. bounded by a multiple of output that grows more slowly than the interest
rate, so that output has finite market value), a contract immune to collateralised
self-financing deviations has `Q(h) ≤ 0` at every node. -/
theorem bulow_rogoff_growth {r : ℝ} (hr : 0 < r) {P : (k : ℕ) → (Fin k → S) → ℝ} {M w : ℝ}
    (hw : 0 < w) (hwr : w < 1 + r) (hP : ∀ k h, |P k h| ≤ M * w ^ k)
    (himm : Theorem.Immune tr r P) : ∀ k h, tr.oblig r P k h ≤ 0 := by
  classical
  have h1r : 0 < 1 + r := by linarith
  set ρ := (1 + r)⁻¹ with hρ
  have hρpos : 0 < ρ := by positivity
  have hρw : ρ * w < 1 := by rw [hρ, inv_mul_lt_iff₀ h1r, mul_one]; exact hwr
  set cst := M * (1 + ρ * w / (1 - ρ * w))
  have hnorm : ∀ k h, tr.oblig r P k h / w ^ k ≤ cst := by
    intro k h
    have hwk : 0 < w ^ k := pow_pos hw k
    rw [div_le_iff₀ hwk]
    have h1 := le_trans (le_abs_self _) (hP k h)
    have h2 := le_trans (le_abs_self _) (abs_pv_le_growth tr hr hw hwr hP k h)
    unfold Tree.oblig; simp only [cst]; nlinarith
  have hbdd : BddAbove (Set.range fun p : (Σ k, Fin k → S) => tr.oblig r P p.1 p.2 / w ^ p.1) :=
    ⟨cst, by rintro _ ⟨p, rfl⟩; exact hnorm p.1 p.2⟩
  have hle : ∀ k h, tr.oblig r P k h ≤ supObligG tr r w P * w ^ k := by
    intro k h
    have := le_csSup hbdd ⟨⟨k, h⟩, rfl⟩
    rwa [div_le_iff₀ (pow_pos hw k)] at this
  have hrec : ∀ k h, tr.pv r P k h = ρ * ∑ s, tr.q k h s *
      tr.oblig r P (k + 1) (Fin.snoc h s : Fin (k + 1) → S) :=
    tr.pv_recursion_of_summable (summable_pv_growth tr hr hw hwr hP)
  by_contra hne; push Not at hne
  obtain ⟨k, h, hkh⟩ := hne
  set N := supObligG tr r w P with hN
  have hNpos : 0 < N := by
    have := hle k h
    have hwk := pow_pos hw k
    by_contra hn; push Not at hn
    have : N * w ^ k ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hn hwk.le
    linarith
  -- the deviation
  set a : (k : ℕ) → (Fin k → S) → ℝ := fun k h => N * w ^ k - tr.oblig r P k h
  set A : (k : ℕ) → (Fin k → S) → ℝ := fun k h => ρ * N * w ^ (k + 1) - tr.pv r P k h
  have ha : ∀ k h, 0 ≤ a k h := fun k h => by simp only [a]; linarith [hle k h]
  have hA : ∀ k h, A k h = ρ * ∑ s, tr.q k h s * a (k + 1) (Fin.snoc h s : Fin (k + 1) → S) := by
    intro k h
    simp only [A, a]
    rw [hrec k h]
    have : ∑ s, tr.q k h s * (N * w ^ (k + 1) - tr.oblig r P (k + 1)
        (Fin.snoc h s : Fin (k + 1) → S)) = N * w ^ (k + 1) -
        ∑ s, tr.q k h s * tr.oblig r P (k + 1) (Fin.snoc h s : Fin (k + 1) → S) := by
      rw [show (fun s => tr.q k h s * (N * w ^ (k + 1) - tr.oblig r P (k + 1)
          (Fin.snoc h s : Fin (k + 1) → S))) = fun s => tr.q k h s * (N * w ^ (k + 1)) -
          tr.q k h s * tr.oblig r P (k + 1) (Fin.snoc h s : Fin (k + 1) → S) from
          funext fun s => by ring, Finset.sum_sub_distrib, ← Finset.sum_mul, tr.q_sum, one_mul]
    rw [this]; ring
  have hcons : ∀ k (h : Fin k → S) s, 0 ≤ P (k + 1) (Fin.snoc h s : Fin (k + 1) → S) +
      a (k + 1) (Fin.snoc h s : Fin (k + 1) → S) - A (k + 1) (Fin.snoc h s : Fin (k + 1) → S) := by
    intro k h s
    simp only [a, A, Tree.oblig]
    have : 0 ≤ N * w ^ (k + 1) * (1 - ρ * w) :=
      mul_nonneg (mul_nonneg hNpos.le (pow_pos hw _).le) (by linarith)
    have e : w ^ (k + 1 + 1) = w ^ (k + 1) * w := pow_succ w (k + 1)
    rw [e]; nlinarith
  -- a node where default pays
  have hlt : ρ * w * N < N := by nlinarith
  have : Nonempty ((k : ℕ) × (Fin k → S)) := ⟨⟨0, Fin.elim0⟩⟩
  obtain ⟨_, ⟨p, rfl⟩, hp⟩ := exists_lt_of_lt_csSup (Set.range_nonempty _) hlt
  have hwp := pow_pos hw p.1
  simp only at hp
  rw [lt_div_iff₀ hwp] at hp
  have hdev := himm A a p.1 p.2 ha (fun k h => by rw [hA k h]) hcons
  simp only [A, Tree.oblig] at hdev hp
  have e : w ^ (p.1 + 1) = w ^ p.1 * w := pow_succ w p.1
  rw [e] at hdev
  nlinarith

/-- When payments grow at least as fast as the interest rate (`w ≥ 1 + r`), the discounted
series of even the dominating payments `wʲ` diverges, so the market value of obligations used
in the Bulow–Rogoff argument is not defined (the book claims no conclusion in this case).
(O&R p. 375) -/
theorem not_summable_fast_growth {r w : ℝ} (hr : 0 < r) (hw : 1 + r ≤ w) :
    ¬ Summable fun j : ℕ => ((1 + r)⁻¹) ^ (j + 1) * w ^ (j + 1) := by
  intro hs
  have h1r : 0 < 1 + r := by linarith
  have hge : ∀ j : ℕ, 1 ≤ ((1 + r)⁻¹) ^ (j + 1) * w ^ (j + 1) := by
    intro j
    rw [← mul_pow]
    apply one_le_pow₀
    rw [inv_mul_eq_div, le_div_iff₀ h1r, one_mul]; exact hw
  have := hs.tendsto_atTop_zero
  have hev := this.eventually (gt_mem_nhds (show (0 : ℝ) < 1 by norm_num))
  obtain ⟨n, hn⟩ := hev.exists_forall_of_atTop
  have := hn n le_rfl
  linarith [hge n]

end Growth

/-! ## §6.2.2: deterministic economies — no sovereign borrowing -/

namespace Deterministic

/-- The deterministic event tree: one branch at every node (O&R §6.2.2, p. 391). -/
def detTree : Tree Unit := ⟨fun _ _ _ => 1, fun _ _ _ => zero_le_one, fun _ _ => by simp⟩

/-- The deterministic tree has a single branch of probability one.
(O&R §6.2.2, pp. 391–392) -/
theorem detTree_q (k : ℕ) (h : Fin k → Unit) (s : Unit) : detTree.q k h s = 1 := rfl

/-- The market value at date `n` of the remaining obligations of a deterministic contract:
`Q_n = P_n + Σ_{j ≥ 0} (1 + r)^{−(j+1)} P_{n+j+1}`.
(O&R §6.2.2, pp. 391–392) -/
noncomputable def detPV (r : ℝ) (P : ℕ → ℝ) (n : ℕ) : ℝ :=
  P n + ∑' j : ℕ, ((1 + r)⁻¹) ^ (j + 1) * P (n + j + 1)

/-- Conditional expectations on the deterministic tree are the future payments.
(O&R §6.2.2, pp. 391–392) -/
theorem det_ev (P : ℕ → ℝ) : ∀ j k (h : Fin k → Unit),
    detTree.ev (fun k _ => P k) j k h = P (k + j) := by
  intro j
  induction j with
  | zero => intro k h; rfl
  | succ j ih =>
    intro k h
    simp only [Tree.ev, detTree_q, one_mul, Finset.univ_unique, Finset.sum_singleton]
    rw [ih]; congr 1; omega

/-- On the deterministic tree the value of obligations is `detPV`.
(O&R §6.2.2, pp. 391–392) -/
theorem det_oblig (r : ℝ) (P : ℕ → ℝ) (k : ℕ) (h : Fin k → Unit) :
    detTree.oblig r (fun k _ => P k) k h = detPV r P k := by
  simp only [Tree.oblig, Tree.pv, detPV, det_ev]
  congr 1

/-- Immunity to collateralised deviations in a deterministic economy (O&R §6.2.2 with
§6.1.2.4): no plan of nonnegative bond holdings `A_n = a_{n+1}/(1 + r)` (bought, never
borrowed) that raises consumption weakly at every later date and strictly at the default
date. -/
def DetImmune (r : ℝ) (P : ℕ → ℝ) : Prop :=
  ∀ (A a : ℕ → ℝ) (n₀ : ℕ), (∀ n, 0 ≤ a n) → (∀ n, A n = (1 + r)⁻¹ * a (n + 1)) →
    (∀ n, 0 ≤ P (n + 1) + a (n + 1) - A (n + 1)) → P n₀ - A n₀ ≤ 0

/-- Deterministic immunity is immunity on the deterministic tree.
(O&R §6.2.2, pp. 391–392) -/
theorem immune_of_detImmune {r : ℝ} {P : ℕ → ℝ} (h : DetImmune r P) :
    Theorem.Immune detTree r (fun k _ => P k) := by
  intro A a k₀ h₀ ha hA hcons
  have hu : ∀ {k : ℕ} (x y : Fin k → Unit), x = y := fun x y => Subsingleton.elim x y
  have := h (fun n => A n (fun _ => ())) (fun n => a n (fun _ => ())) k₀ (fun n => ha _ _)
    (fun n => by
      rw [hA n (fun _ => ())]
      simp only [detTree_q, one_mul, Finset.univ_unique, Finset.sum_singleton])
    (fun n => by
      have := hcons n (fun _ => ()) ()
      rwa [hu (Fin.snoc (fun _ => ()) () : Fin (n + 1) → Unit) (fun _ => ())] at this)
  rwa [hu h₀ (fun _ => ())]

/-- **No sovereign borrowing** (O&R §6.2.2, p. 392, and §6.1.2.4): with `r > 0` and bounded
payments, a deterministic contract immune to collateralised deviations has `Q_n ≤ 0` at every
date — the country is never a net debtor. -/
theorem no_sovereign_borrowing {r : ℝ} (hr : 0 < r) {P : ℕ → ℝ} {M : ℝ} (hP : ∀ n, |P n| ≤ M)
    (himm : DetImmune r P) : ∀ n, detPV r P n ≤ 0 := by
  intro n
  have := Theorem.bulow_rogoff detTree hr (P := fun k _ => P k) (fun k _ => hP k)
    (immune_of_detImmune himm) n (fun _ => ())
  rwa [det_oblig] at this

/-- **No loan at date 0** (O&R p. 392): if lenders break even, `Q_0 = 0`, an immune
deterministic contract has `P_0 ≥ 0`: the country cannot receive a net inflow. -/
theorem no_loan_inflow {r : ℝ} (hr : 0 < r) {P : ℕ → ℝ} {M : ℝ} (hP : ∀ n, |P n| ≤ M)
    (himm : DetImmune r P) (hbreak : detPV r P 0 = 0) : 0 ≤ P 0 := by
  have h1 := no_sovereign_borrowing hr hP himm 1
  have hrec := detTree.pv_recursion hr (P := fun k _ => P k) (fun k _ => hP k) 0
    (fun _ => ())
  simp only [detTree_q, one_mul, Finset.univ_unique, Finset.sum_singleton] at hrec
  rw [det_oblig] at hrec
  have h0 := det_oblig r P 0 (fun _ => ())
  unfold Tree.oblig at h0
  rw [hrec, hbreak] at h0
  have : 0 ≤ (1 + r)⁻¹ := by positivity
  nlinarith

/-- **Default once the market is no longer needed** (O&R §6.2.2, p. 392): with exclusion as the
only punishment, if all payments from date `T` on are nonnegative and one is positive, default
at `T` (consuming output `Y_n` thereafter) gives strictly higher continuation utility than
honouring (consuming `Y_n − P_n`). -/
theorem default_when_market_unneeded (U : Utility) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (Y P : ℕ → ℝ) {lo hi : ℝ} (hlo : 0 < lo) (hc : ∀ n, lo ≤ Y n - P n) (hY : ∀ n, Y n ≤ hi)
    (T : ℕ) (hnn : ∀ n, T ≤ n → 0 ≤ P n) (hpos : ∃ n, T ≤ n ∧ 0 < P n) :
    ∑' j, β ^ j * U.u (Y (T + j) - P (T + j)) < ∑' j, β ^ j * U.u (Y (T + j)) := by
  obtain ⟨m, hm, hPm⟩ := hpos
  have hb : ∀ x, lo ≤ x → x ≤ hi → |U.u x| ≤ |U.u lo| + |U.u hi| := by
    intro x h1 h2
    have a1 := U.mono hlo h1
    have a2 := U.mono (lt_of_lt_of_le hlo h1) h2
    rw [abs_le]; constructor
    · have := neg_abs_le (U.u lo); have := abs_nonneg (U.u hi); linarith
    · have := le_abs_self (U.u hi); have := abs_nonneg (U.u lo); linarith
  have hs1 := Geometric.summable_of_bounded hβ0.le hβ1
    (x := fun j => U.u (Y (T + j) - P (T + j)))
    (fun j => hb _ (hc _) (by linarith [hY (T + j), hnn (T + j) (by omega)]))
  have hs2 := Geometric.summable_of_bounded hβ0.le hβ1 (x := fun j => U.u (Y (T + j)))
    (fun j => hb _ (by linarith [hc (T + j), hnn (T + j) (by omega)]) (hY _))
  refine hs1.tsum_lt_tsum (i := m - T) (fun j => ?_) ?_ hs2
  · apply mul_le_mul_of_nonneg_left _ (pow_nonneg hβ0.le j)
    exact U.mono (lt_of_lt_of_le hlo (hc _)) (by linarith [hnn (T + j) (by omega)])
  · have he : T + (m - T) = m := by omega
    simp only [he]
    have hlt := U.lt (lt_of_lt_of_le hlo (hc m)) (show Y m - P m < Y m by linarith)
    exact mul_lt_mul_of_pos_left hlt (pow_pos hβ0 _)

/-- **No loan contract is incentive compatible under exclusion alone** (O&R §6.2.2, p. 392): a
deterministic loan (`P_0 < 0`, repayments `P_n ≥ 0` for `n ≥ 1`) on which lenders break even has
some positive repayment, so at date 1 the country strictly prefers to default. -/
theorem loan_defaulted (U : Utility) {β r : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (Y P : ℕ → ℝ) {lo hi : ℝ} (hlo : 0 < lo) (hc : ∀ n, lo ≤ Y n - P n) (hY : ∀ n, Y n ≤ hi)
    (hloan : P 0 < 0) (hrepay : ∀ n, 1 ≤ n → 0 ≤ P n)
    (hbreak : detPV r P 0 = 0) :
    ∑' j, β ^ j * U.u (Y (1 + j) - P (1 + j)) < ∑' j, β ^ j * U.u (Y (1 + j)) := by
  apply default_when_market_unneeded U hβ0 hβ1 Y P hlo hc hY 1 hrepay
  by_contra hn; push Not at hn
  have hz : ∀ j, P (0 + j + 1) = 0 := fun j =>
    le_antisymm (hn _ (by omega)) (hrepay _ (by omega))
  unfold detPV at hbreak
  simp only [hz, mul_zero, tsum_zero, add_zero] at hbreak
  linarith

end Deterministic


/-! ## §6.1.2.3: the collateralised steady state (Worrall 1990) -/

namespace Collateral

variable {S : Type} [Fintype S] (E : Endowment S)

/-- Next-period foreign assets, O&R (12), p. 364: `B′ = (1 + r)B + Ȳ + ε − C − P(ε)`. -/
def nextAssets (r B C P : ℝ) (s : S) : ℝ := (1 + r) * B + E.Y s - C - P

/-- **The steady state satisfies the budget**, O&R p. 373: with full insurance `P = ε` and
consumption `C̄ = Ȳ + rB`, assets stay at `B` in every state. -/
theorem steady_state_budget (r B : ℝ) (s : S) :
    nextAssets E r B (E.Ybar + r * B) (E.ε s) s = B := by
  unfold nextAssets Endowment.Y; ring

/-- **Full collateralisation**, O&R p. 373: honouring the full-insurance payment and then
liquidating all assets leaves at least the defaulter's resources (a defaulter keeps its output
but forfeits its foreign assets `(1 + r)B`) in every state iff `ε ≤ (1 + r)B` in every
state. -/
theorem collateral_dominates_iff (r B : ℝ) :
    (∀ s, E.Y s ≤ E.Y s - E.ε s + (1 + r) * B) ↔ ∀ s, E.ε s ≤ (1 + r) * B := by
  constructor <;> intro h s <;> have := h s <;> linarith

/-- The collateral threshold `B̄ = ε̄/(1 + r)`, O&R p. 373: `ε ≤ (1 + r)B` in every state iff
`B ≥ ε̄/(1 + r)`. -/
theorem collateral_threshold {r B : ℝ} (hr : -1 < r) {smax : S} (hsmax : ∀ s, E.ε s ≤ E.ε smax) :
    (∀ s, E.ε s ≤ (1 + r) * B) ↔ E.ε smax / (1 + r) ≤ B := by
  rw [div_le_iff₀ (by linarith)]
  constructor
  · intro h; linarith [h smax]
  · intro h s; linarith [hsmax s]

/-- The steady-state package as net payments to foreigners on the i.i.d. tree: at every date
after the first, the country pays the insurance premium `ε` and receives interest `rB` on its
foreign assets (O&R p. 373). -/
def packagePayments (r B : ℝ) : (k : ℕ) → (Fin k → S) → ℝ :=
  fun k h => if hk : 0 < k then E.ε (h ⟨k - 1, by omega⟩) - r * B else 0

/-- The package's payment at a successor node.
(O&R §6.1.2.3, p. 373) -/
theorem package_child (r B : ℝ) (k : ℕ) (h : Fin k → S) (s : S) :
    packagePayments E r B (k + 1) (Fin.snoc h s : Fin (k + 1) → S) = E.ε s - r * B := by
  simp only [packagePayments, Nat.zero_lt_succ, ↓reduceDIte]
  have : (⟨k + 1 - 1, by omega⟩ : Fin (k + 1)) = Fin.last k := by ext; simp
  rw [this, Fin.snoc_last]

/-- The package's payments are bounded.
(O&R §6.1.2.3, p. 373) -/
theorem package_bounded (r B : ℝ) :
    ∀ k h, |packagePayments E r B k h| ≤ ∑ t, |E.ε t| + |r * B| := by
  intro k h
  simp only [packagePayments]
  split_ifs
  · exact le_trans (abs_sub _ _) (add_le_add (ReputationTrigger.Trigger.abs_le_sum_abs E.ε _)
      le_rfl)
  · simp only [abs_zero]
    have := abs_nonneg (r * B)
    have : 0 ≤ ∑ t, |E.ε t| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    linarith

/-- **The value of the package's future obligations is `−B`** (O&R p. 373): the country is a
net creditor by exactly its foreign assets, since `E ε = 0` and `Σ_{j ≥ 1} rB/(1 + r)^j = B`. -/
theorem package_pv {r : ℝ} (hr : 0 < r) (B : ℝ) (k : ℕ) (h : Fin k → S) :
    (Tree.iid E.Ω).pv r (packagePayments E r B) k h = -B := by
  have hev : ∀ j k h, (Tree.iid E.Ω).ev (packagePayments E r B) (j + 1) k h = -(r * B) := by
    intro j
    induction j with
    | zero =>
      intro k h
      simp only [Tree.ev, package_child]
      have : ∑ s, (Tree.iid E.Ω).q k h s * (E.ε s - r * B) = E.Ω.expect E.ε - r * B := by
        simp only [Tree.iid, StateSpace.expect, mul_sub, Finset.sum_sub_distrib,
          ← Finset.sum_mul, E.Ω.prob_sum, one_mul]
      rw [this, E.mean_zero]; ring
    | succ j ih =>
      intro k h
      rw [Tree.ev]
      simp only [ih]
      rw [← Finset.sum_mul]
      simp [Tree.iid, E.Ω.prob_sum]
  have hρ0 : 0 ≤ (1 + r)⁻¹ := by positivity
  have hρ1 : (1 + r)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  unfold Tree.pv
  simp only [hev]
  rw [(Geometric.hasSum_geometric_from_one hρ0 hρ1 _).tsum_eq]
  have hd : (1 : ℝ) - (1 + r)⁻¹ ≠ 0 := by linarith
  have h1r : (1 : ℝ) + r ≠ 0 := by linarith
  rw [div_mul_eq_mul_div, div_eq_iff hd]
  field_simp
  ring

/-- The package's obligations at a successor node: `Q = ε − (1 + r)B` (O&R p. 373). -/
theorem package_oblig_child {r : ℝ} (hr : 0 < r) (B : ℝ) (k : ℕ) (h : Fin k → S) (s : S) :
    (Tree.iid E.Ω).oblig r (packagePayments E r B) (k + 1) (Fin.snoc h s : Fin (k + 1) → S) =
      E.ε s - (1 + r) * B := by
  unfold Tree.oblig
  rw [package_child, package_pv E hr]; ring

/-- **Collateral is necessary in a Bulow–Rogoff world** (O&R pp. 373–375): if the country can
default and hold fully collateralised claims, the full-insurance steady state with assets `B`
is immune to such deviations only if `ε ≤ (1 + r)B` in every state, i.e. `B ≥ B̄`. -/
theorem steady_state_requires_collateral {r : ℝ} (hr : 0 < r) (B : ℝ)
    (himm : Theorem.Immune (Tree.iid E.Ω) r (packagePayments E r B)) :
    ∀ s, E.ε s ≤ (1 + r) * B := by
  intro s
  have := Theorem.bulow_rogoff (Tree.iid E.Ω) hr (package_bounded E r B) himm 1
    (Fin.snoc (Fin.elim0 : Fin 0 → S) s : Fin 1 → S)
  rw [package_oblig_child E hr] at this
  linarith

/-- **The steady state is first best given `B`**, O&R p. 373: under actuarially fair complete
markets (`β(1 + r) = 1`), any positive state-contingent consumption plan satisfying the
present-value budget `Σ_n βⁿ E C_n ≤ (1 + r)B + Ȳ/(1 − β)` has lifetime utility at most
`u(Ȳ + rB)/(1 − β)`, the value of the constant plan `C̄ = Ȳ + rB`. -/
theorem steady_state_first_best (U : Utility) {β r B : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hβ : β * (1 + r) = 1) (hB : 0 ≤ B) (C : (n : ℕ) → (Fin (n + 1) → S) → ℝ)
    (hC : ∀ n h, 0 < C n h)
    (hsC : Summable fun n => β ^ n * ReputationTrigger.History.hexp E.Ω (n + 1) (C n))
    (hsU : Summable fun n => β ^ n *
      ReputationTrigger.History.hexp E.Ω (n + 1) (fun h => U.u (C n h)))
    (hbudget : ∑' n, β ^ n * ReputationTrigger.History.hexp E.Ω (n + 1) (C n) ≤
      (1 + r) * B + E.Ybar / (1 - β)) :
    ∑' n, β ^ n * ReputationTrigger.History.hexp E.Ω (n + 1) (fun h => U.u (C n h)) ≤
      U.u (E.Ybar + r * B) / (1 - β) := by
  have hr : 0 < r := by nlinarith
  set Cb := E.Ybar + r * B with hCb
  have hCbpos : 0 < Cb := by have := E.Ybar_pos; nlinarith
  -- supporting line at `C̄`
  have hpt : ∀ n, ReputationTrigger.History.hexp E.Ω (n + 1) (fun h => U.u (C n h)) ≤
      U.u Cb + U.du Cb * (ReputationTrigger.History.hexp E.Ω (n + 1) (C n) - Cb) := by
    intro n
    have := ReputationTrigger.History.hexp_mono E.Ω (n + 1)
      (X := fun h => U.u (C n h)) (Y := fun h => U.u Cb + U.du Cb * (C n h - Cb))
      (fun h => U.supporting_line (hC n h) hCbpos)
    have e := ReputationTrigger.History.hexp_combo E.Ω (n + 1)
      (fun h => U.u Cb + U.du Cb * (C n h - Cb)) (fun _ => 1) (C n) (fun _ => 0) (fun _ => 0)
      (U.u Cb - U.du Cb * Cb) (U.du Cb) 0 0 (fun h => by ring)
    rw [e, ReputationTrigger.History.hexp_const] at this
    linarith
  have hgeo := Geometric.hasSum_geometric_const hβ0.le hβ1 (U.u Cb - U.du Cb * Cb)
  have hrhs : Summable fun n => β ^ n * (U.u Cb + U.du Cb *
      (ReputationTrigger.History.hexp E.Ω (n + 1) (C n) - Cb)) := by
    have := hgeo.summable.add (hsC.mul_left (U.du Cb))
    refine this.congr fun n => ?_
    ring
  have hle := hsU.tsum_le_tsum (fun n => mul_le_mul_of_nonneg_left (hpt n)
    (pow_nonneg hβ0.le n)) hrhs
  have hval : ∑' n, β ^ n * (U.u Cb + U.du Cb *
      (ReputationTrigger.History.hexp E.Ω (n + 1) (C n) - Cb)) =
      (U.u Cb - U.du Cb * Cb) / (1 - β) +
        U.du Cb * ∑' n, β ^ n * ReputationTrigger.History.hexp E.Ω (n + 1) (C n) := by
    rw [← hgeo.tsum_eq, ← hsC.tsum_mul_left, ← hgeo.summable.tsum_add (hsC.mul_left _)]
    apply tsum_congr; intro n; ring
  rw [hval] at hle
  have hdu := U.du_pos Cb hCbpos
  have hbud : (1 + r) * B + E.Ybar / (1 - β) = Cb / (1 - β) := by
    have h1 : (1 : ℝ) - β ≠ 0 := by linarith
    have hr' : 1 + r = 1 / β := by field_simp; linarith
    rw [hCb, hr']
    field_simp
    have : β * r = 1 - β := by linarith
    nlinarith
  rw [hbud] at hbudget
  have := mul_le_mul_of_nonneg_left hbudget hdu.le
  have e2 : (U.u Cb - U.du Cb * Cb) / (1 - β) + U.du Cb * (Cb / (1 - β)) =
      U.u Cb / (1 - β) := by ring
  linarith

/-- The constant steady-state plan `C̄ = Ȳ + rB` exhausts the present-value budget and attains
`u(C̄)/(1 − β)` (O&R p. 373, `β(1 + r) = 1`). -/
theorem steady_state_plan (U : Utility) {β r B : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hβ : β * (1 + r) = 1) :
    ∑' n : ℕ, β ^ n * ReputationTrigger.History.hexp E.Ω (n + 1) (fun _ => E.Ybar + r * B) =
        (1 + r) * B + E.Ybar / (1 - β) ∧
      ∑' n : ℕ, β ^ n * ReputationTrigger.History.hexp E.Ω (n + 1)
        (fun _ => U.u (E.Ybar + r * B)) = U.u (E.Ybar + r * B) / (1 - β) := by
  simp only [ReputationTrigger.History.hexp_const]
  refine ⟨?_, (Geometric.hasSum_geometric_const hβ0.le hβ1 _).tsum_eq⟩
  rw [(Geometric.hasSum_geometric_const hβ0.le hβ1 _).tsum_eq]
  have h1 : (1 : ℝ) - β ≠ 0 := by linarith
  have hr' : r = (1 - β) / β := by field_simp; linarith
  rw [hr']
  field_simp
  ring

end Collateral

/-! ## Exercise 3(c): lending abroad and investment loans -/

namespace InvestmentLending

variable {S : Type}

/-- The Exercise 3 loan package as net payments on the i.i.d. tree (O&R p. 426): at every
date after the first the country repays `p(ε)` on last period's loan and takes a new loan
`D`. -/
def loanPayments (p : S → ℝ) (D : ℝ) : (k : ℕ) → (Fin k → S) → ℝ :=
  fun k h => if hk : 0 < k then p (h ⟨k - 1, by omega⟩) - D else 0

/-- The package's payment at a successor node. (O&R Exercise 3(c), p. 427) -/
theorem loan_child (p : S → ℝ) (D : ℝ) (k : ℕ) (h : Fin k → S) (s : S) :
    loanPayments p D (k + 1) (Fin.snoc h s : Fin (k + 1) → S) = p s - D := by
  simp only [loanPayments, Nat.zero_lt_succ, ↓reduceDIte]
  have : (⟨k + 1 - 1, by omega⟩ : Fin (k + 1)) = Fin.last k := by ext; simp
  rw [this, Fin.snoc_last]

variable [Fintype S] (E : Endowment S)

/-- **Exercise 3(c)**, O&R p. 427 with §6.1.2.4: if the country may lend abroad after
defaulting (hold fully collateralised claims), no reputational investment loan survives:
a stationary package with repayments `p ≥ 0`, `E p = (1 + r)D`, that is immune to
collateralised self-financing deviations has `D ≤ 0`. In particular the commitment optimum
of Exercise 3(a), which needs `D ≥ D̃ > 0`, cannot be sustained. -/
theorem lending_abroad_no_investment_loans {r : ℝ} (hr : 0 < r) (p : S → ℝ) (D : ℝ)
    (hp : ∀ s, 0 ≤ p s) (hzp : E.Ω.expect p = (1 + r) * D)
    (himm : Theorem.Immune (Tree.iid E.Ω) r (loanPayments p D)) : D ≤ 0 := by
  have hbnd : ∀ k h, |loanPayments p D k h| ≤ ∑ t, |p t| + |D| := by
    intro k h
    simp only [loanPayments]
    split_ifs
    · exact le_trans (abs_sub _ _) (add_le_add
        (ReputationTrigger.Trigger.abs_le_sum_abs p _) le_rfl)
    · simp only [abs_zero]
      have := abs_nonneg D
      have : 0 ≤ ∑ t, |p t| := Finset.sum_nonneg fun _ _ => abs_nonneg _
      linarith
  -- future obligations are worth `D`
  have hev : ∀ j k h, (Tree.iid E.Ω).ev (loanPayments p D) (j + 1) k h = r * D := by
    intro j
    induction j with
    | zero =>
      intro k h
      simp only [Tree.ev, loan_child]
      have : ∑ s, (Tree.iid E.Ω).q k h s * (p s - D) = E.Ω.expect p - D := by
        simp only [Tree.iid, StateSpace.expect, mul_sub, Finset.sum_sub_distrib,
          ← Finset.sum_mul, E.Ω.prob_sum, one_mul]
      rw [this, hzp]; ring
    | succ j ih =>
      intro k h
      rw [Tree.ev]
      simp only [ih]
      rw [← Finset.sum_mul]
      simp [Tree.iid, E.Ω.prob_sum]
  have hρ0 : 0 ≤ (1 + r)⁻¹ := by positivity
  have hρ1 : (1 + r)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hpv : ∀ k h, (Tree.iid E.Ω).pv r (loanPayments p D) k h = D := by
    intro k h
    unfold Tree.pv
    simp only [hev]
    rw [(Geometric.hasSum_geometric_from_one hρ0 hρ1 _).tsum_eq]
    have hd : (1 : ℝ) - (1 + r)⁻¹ ≠ 0 := by linarith
    have h1r : (1 : ℝ) + r ≠ 0 := by linarith
    rw [div_mul_eq_mul_div, div_eq_iff hd]
    field_simp
    ring
  have hQ := Theorem.bulow_rogoff (Tree.iid E.Ω) hr hbnd himm
  have hps : ∀ s, p s ≤ 0 := fun s => by
    have := hQ 1 (Fin.snoc (Fin.elim0 : Fin 0 → S) s : Fin 1 → S)
    unfold Tree.oblig at this
    rw [loan_child, hpv] at this
    linarith
  have hp0 : ∀ s, p s = 0 := fun s => le_antisymm (hps s) (hp s)
  have : E.Ω.expect p = 0 := by
    rw [show p = fun _ => 0 from funext hp0, E.Ω.expect_const]
  rw [this] at hzp
  nlinarith

end InvestmentLending


/-! ## Subtrees of an event tree -/

namespace Subtree

variable {S : Type}

/-- Extending a date-`n` node `h` (a history of `n + 1` shocks) by `j` further shocks `k`: the
date-`(n + j)` node `h ⌢ k` (O&R (11), p. 364). -/
def extendD {n : ℕ} (h : Fin (n + 1) → S) : (j : ℕ) → (Fin j → S) → Fin (n + j + 1) → S
  | 0, _ => h
  | j + 1, k => (Fin.snoc (extendD h j (Fin.init k)) (k (Fin.last j)) : Fin (n + j + 1 + 1) → S)

/-- The date-`n` prefix of a date-`m` node, `n ≤ m`. (O&R (11), p. 364) -/
def preN {n m : ℕ} (hm : n ≤ m) (g : Fin (m + 1) → S) : Fin (n + 1) → S :=
  fun i => g ⟨i, by omega⟩

/-- The last `j` shocks of a date-`(n + j)` node. (O&R (11), p. 364) -/
def dropN {n j : ℕ} (g : Fin (n + j + 1) → S) : Fin j → S := fun i => g ⟨n + 1 + i, by omega⟩

/-- The prefix of an extension is the node extended. (O&R (11), p. 364) -/
theorem preN_extendD {n : ℕ} (h : Fin (n + 1) → S) :
    ∀ j (k : Fin j → S), preN (Nat.le_add_right n j) (extendD h j k) = h := by
  intro j
  induction j with
  | zero => intro k; funext i; rfl
  | succ j ih =>
    intro k; funext i
    have := congrFun (ih (Fin.init k)) i
    simp only [preN] at this ⊢
    rw [← this]
    simp only [extendD]
    have e : (⟨i, by omega⟩ : Fin (n + j + 1 + 1)) = Fin.castSucc ⟨i, by omega⟩ := rfl
    rw [e, Fin.snoc_castSucc]

/-- The prefix of the predecessor node is the prefix of the node. (O&R (11), p. 364) -/
theorem preN_init {n m : ℕ} (hm : n ≤ m) (g : Fin (m + 1 + 1) → S) :
    preN hm (Fin.init g) = preN (by omega) g := by
  funext i; rfl

/-- Siblings share their prefixes. (O&R (11), p. 364) -/
theorem preN_snoc {n m : ℕ} (hm : n < m) (g : Fin m → S) (s t : S) :
    preN hm.le (Fin.snoc g s : Fin (m + 1) → S) = preN hm.le (Fin.snoc g t : Fin (m + 1) → S) := by
  funext i
  simp only [preN]
  have e : (⟨i, by omega⟩ : Fin (m + 1)) = Fin.castSucc ⟨i, by omega⟩ := rfl
  rw [e, Fin.snoc_castSucc, Fin.snoc_castSucc]

/-- Every date-`(n + j)` node is the extension of its prefix by its last `j` shocks.
(O&R (11), p. 364) -/
theorem extendD_pre_drop {n : ℕ} :
    ∀ j (g : Fin (n + j + 1) → S), extendD (preN (Nat.le_add_right n j) g) j (dropN g) = g := by
  intro j
  induction j with
  | zero => intro g; funext i; rfl
  | succ j ih =>
    intro g
    have h1 : preN (Nat.le_add_right n (j + 1)) g = preN (Nat.le_add_right n j) (Fin.init g) := by
      funext i; rfl
    have h2 : Fin.init (dropN g) = dropN (Fin.init g) := by funext i; rfl
    simp only [extendD]
    rw [h1, h2, ih (Fin.init g)]
    have h3 : dropN g (Fin.last j) = g (Fin.last (n + j + 1)) := by
      simp only [dropN]; congr 1; ext; simp; omega
    rw [h3, Fin.snoc_init_self]

end Subtree

open Subtree

/-! ## Toward Worrall's convergence claim: the Euler supermartingale

O&R p. 373 sketch (after Worrall 1990): while the incentive constraint binds the country keeps
accumulating foreign assets, "so mean consumption rises over time", until assets reach `B̄`.
We formalise the dynamic economy in which the only enforcement is seizure of the country's
own foreign assets (the Bulow–Rogoff world): i.i.d. shocks, per-period zero-profit insurance
(13), payments bounded by seizable assets `P ≤ (1 + r)B`, nonnegative assets, budget (12).
For **every optimal plan** we prove the Euler inequality at every node
(`u′(C_n) ≥ β(1 + r)E_n u′(C_{n+1})`, in an exact finite-`δ` form and, for continuous `u′`, in
the limit), i.e. marginal utility is a supermartingale when `β(1 + r) = 1`; hence expected
marginal utility is nonincreasing over time and converges. The convergence claim itself is
proved in the next subsection by a direct argument: after the first top shock `ε̄` an optimal
plan is a first-best steady state with consumption at least `Ȳ + rB̄`, so the probability of
still being below the steady state at date `n` is at most `(1 − π(ε̄))^{n+1}`. Existence of an
optimal plan is proved when `B₀ ≥ B̄`; for `B₀ < B̄` it is not proved (see `steady_optimal`). -/

namespace Worrall

variable {S : Type} [Fintype S] (E : Endowment S) (U : Utility)

/-- A dynamic plan (O&R (12), p. 364): consumption `C` and insurance payments `P` at every
date-`n` node (history of `n + 1` shocks), and foreign assets `B` carried into date `n`
(chosen at the date-`(n − 1)` node, a history of `n` shocks). -/
structure Plan (S : Type) where
  C : (n : ℕ) → (Fin (n + 1) → S) → ℝ
  P : (n : ℕ) → (Fin (n + 1) → S) → ℝ
  B : (n : ℕ) → (Fin n → S) → ℝ

/-- Admissible plans with initial assets `B₀` (O&R (12)–(13) with seizable collateral):
the budget, the collateral constraint `P ≤ (1 + r)B`, per-period zero profit, nonnegative
assets, positive consumption and a convergent utility series. -/
def Admissible (β r B₀ : ℝ) (pl : Plan S) : Prop :=
  pl.B 0 (Fin.elim0 : Fin 0 → S) = B₀ ∧
  (∀ n (h : Fin (n + 1) → S), pl.B (n + 1) h =
    (1 + r) * pl.B n (Fin.init h) + E.Y (h (Fin.last n)) - pl.C n h - pl.P n h) ∧
  (∀ n (h : Fin (n + 1) → S), pl.P n h ≤ (1 + r) * pl.B n (Fin.init h)) ∧
  (∀ n (g : Fin n → S), ∑ s, E.Ω.prob s * pl.P n (Fin.snoc g s : Fin (n + 1) → S) = 0) ∧
  (∀ n g, 0 ≤ pl.B n g) ∧ (∀ n h, 0 < pl.C n h) ∧
  Summable (fun n => β ^ n * ReputationTrigger.History.hexp E.Ω (n + 1)
    (fun h => |U.u (pl.C n h)|))

/-- Lifetime expected utility of a plan, O&R (11): `Σ_n βⁿ E u(C_n)`. -/
noncomputable def lifetime (β : ℝ) (pl : Plan S) : ℝ :=
  ∑' n, β ^ n * ReputationTrigger.History.hexp E.Ω (n + 1) (fun h => U.u (pl.C n h))

/-- The expectation over histories is dominated by the expectation of the absolute value.
(O&R (11), p. 364) -/
theorem abs_hexp_le_hexp_abs {k : ℕ} (X : (Fin k → S) → ℝ) :
    |ReputationTrigger.History.hexp E.Ω k X| ≤
      ReputationTrigger.History.hexp E.Ω k (fun h => |X h|) := by
  rw [abs_le]
  constructor
  · have := ReputationTrigger.History.hexp_mono E.Ω k (X := fun h => -|X h|) (Y := X)
      fun h => neg_abs_le (X h)
    have e : ReputationTrigger.History.hexp E.Ω k (fun h => -|X h|) =
        -ReputationTrigger.History.hexp E.Ω k (fun h => |X h|) := by
      have := ReputationTrigger.History.hexp_linear E.Ω k (-1) 0 (fun h => |X h|)
        (fun _ => (0 : ℝ))
      simp only [neg_one_mul, zero_mul, add_zero] at this
      exact this
    linarith
  · exact ReputationTrigger.History.hexp_mono E.Ω k fun h => le_abs_self (X h)

/-- The utility series of an admissible plan converges (O&R (11)). -/
theorem summable_u {β r B₀ : ℝ} {pl : Plan S} (hpl : Admissible E U β r B₀ pl) :
    Summable (fun n => β ^ n * ReputationTrigger.History.hexp E.Ω (n + 1)
      (fun h => U.u (pl.C n h))) := by
  refine Summable.of_norm_bounded hpl.2.2.2.2.2.2.abs fun n => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_mul]
  have hb := abs_hexp_le_hexp_abs E (fun h => U.u (pl.C n h))
  have h0 : 0 ≤ ReputationTrigger.History.hexp E.Ω (n + 1) (fun h => |U.u (pl.C n h)|) :=
    le_trans (abs_nonneg _) hb
  rw [abs_of_nonneg h0]
  exact mul_le_mul_of_nonneg_left hb (abs_nonneg _)

/-- An optimal plan: admissible and at least as good as every admissible plan.
(O&R §6.1.2.3, p. 373) -/
def Optimal (β r B₀ : ℝ) (pl : Plan S) : Prop :=
  Admissible E U β r B₀ pl ∧
    ∀ pl', Admissible E U β r B₀ pl' → lifetime E U β pl' ≤ lifetime E U β pl

/-- The saving perturbation at node `h`: consume `δ` less at `h`, carry `δ` more assets into
the next date, and consume `(1 + r)δ` more at every successor of `h`.
(O&R §6.1.2.3, p. 373) -/
noncomputable def perturb [DecidableEq S] (pl : Plan S) {n : ℕ} (h : Fin (n + 1) → S) (r δ : ℝ) :
    Plan S :=
  ⟨fun m h' => pl.C m h' - (if List.ofFn h' = List.ofFn h then δ else 0) +
      (if List.ofFn (Fin.init h') = List.ofFn h then (1 + r) * δ else 0),
    pl.P,
    fun m g => pl.B m g + (if List.ofFn g = List.ofFn h then δ else 0)⟩

/-- Histories represented as lists are equal only if they have the same length and agree.
(O&R §6.1.2.3, p. 373) -/
theorem ofFn_eq_iff {T : Type} {m n : ℕ} (a : Fin m → T) (b : Fin n → T) :
    List.ofFn a = List.ofFn b → m = n := fun h => by
  have := congrArg List.length h
  simpa using this

/-- The saving perturbation of an admissible plan is admissible (for `0 < δ < C_n(h)`,
`r > −1`).
(O&R §6.1.2.3, p. 373) -/
theorem perturb_admissible [DecidableEq S] {β r B₀ : ℝ} (hr : -1 < r) {pl : Plan S}
    (hpl : Admissible E U β r B₀ pl) {n : ℕ} (h : Fin (n + 1) → S) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ : δ < pl.C n h) : Admissible E U β r B₀ (perturb pl h r δ) := by
  obtain ⟨h0, hbud, hcol, hzp, hB, hC, hsum⟩ := hpl
  have hne0 : ∀ {m : ℕ} (g : Fin m → S), m ≠ n + 1 → List.ofFn g ≠ List.ofFn h :=
    fun g hm he => hm (ofFn_eq_iff g h he)
  -- the utility series differs from the original at dates `n` and `n + 1` only
  have hdiff : ∀ m, m ∉ ({n, n + 1} : Finset ℕ) →
      β ^ m * ReputationTrigger.History.hexp E.Ω (m + 1)
        (fun h' => |U.u ((perturb pl h r δ).C m h')|) =
      β ^ m * ReputationTrigger.History.hexp E.Ω (m + 1) (fun h' => |U.u (pl.C m h')|) := by
    intro m hm
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hm
    congr 2; funext h'
    simp only [perturb, hne0 h' (by omega), hne0 (Fin.init h') (by omega), ↓reduceIte]
    ring_nf
  refine ⟨?_, fun m h'' => ?_, fun m h'' => ?_, hzp, fun m g => ?_, fun m h' => ?_, ?_⟩
  · simp only [perturb, hne0 (Fin.elim0 : Fin 0 → S) (show 0 ≠ n + 1 by omega), ↓reduceIte,
      h0, add_zero]
  · simp only [perturb]
    rw [hbud m h'']
    split_ifs <;> ring
  · simp only [perturb]
    have := hcol m h''
    split_ifs
    · nlinarith
    · linarith
  · simp only [perturb]
    have := hB m g
    split_ifs <;> linarith
  · simp only [perturb]
    have := hC m h'
    by_cases h1 : List.ofFn h' = List.ofFn h
    · have hm := ofFn_eq_iff h' h h1
      have hm' : m = n := by omega
      subst hm'
      have := List.ofFn_injective h1
      subst this
      have hl : List.ofFn (Fin.init h') ≠ List.ofFn h' := fun he => by
        have := ofFn_eq_iff _ _ he; omega
      simp only [hl, ↓reduceIte]
      linarith
    · simp only [h1, ↓reduceIte]
      split_ifs <;> nlinarith
  · have hsd : Summable (fun m => β ^ m * ReputationTrigger.History.hexp E.Ω (m + 1)
        (fun h' => |U.u ((perturb pl h r δ).C m h')|) -
        β ^ m * ReputationTrigger.History.hexp E.Ω (m + 1) (fun h' => |U.u (pl.C m h')|)) :=
      summable_of_ne_finset_zero (s := ({n, n + 1} : Finset ℕ))
        (fun m hm => by rw [hdiff m hm, sub_self])
    exact (hsum.add hsd).congr fun m => by ring

/-- The change in lifetime utility from the saving perturbation, computed exactly:
`βⁿπ(h)[u(C − δ) − u(C)] + β^{n+1}π(h)Σ_s π(s)[u(C′_s + (1 + r)δ) − u(C′_s)]`.
(O&R §6.1.2.3, p. 373) -/
theorem perturb_gain [DecidableEq S] {β r B₀ : ℝ} (hr : -1 < r) {pl : Plan S}
    (hpl : Admissible E U β r B₀ pl) {n : ℕ} (h : Fin (n + 1) → S) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ : δ < pl.C n h) :
    lifetime E U β (perturb pl h r δ) - lifetime E U β pl =
      β ^ n * (ReputationTrigger.History.histProb E.Ω h *
        (U.u (pl.C n h - δ) - U.u (pl.C n h))) +
      β ^ (n + 1) * (ReputationTrigger.History.histProb E.Ω h *
        ∑ s, E.Ω.prob s * (U.u (pl.C (n + 1) (Fin.snoc h s : Fin (n + 2) → S) + (1 + r) * δ) -
          U.u (pl.C (n + 1) (Fin.snoc h s : Fin (n + 2) → S)))) := by
  have hpl' := perturb_admissible E U hr hpl h hδ0 hδ
  have hne0 : ∀ {m : ℕ} (g : Fin m → S), m ≠ n + 1 → List.ofFn g ≠ List.ofFn h :=
    fun g hm he => hm (ofFn_eq_iff g h he)
  set f : ℕ → ℝ := fun m => β ^ m * (ReputationTrigger.History.hexp E.Ω (m + 1)
      (fun h' => U.u ((perturb pl h r δ).C m h')) -
      ReputationTrigger.History.hexp E.Ω (m + 1) (fun h' => U.u (pl.C m h'))) with hf
  have hzero : ∀ m, m ∉ ({n, n + 1} : Finset ℕ) → f m = 0 := by
    intro m hm
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hm
    simp only [hf]
    have : (fun h' => U.u ((perturb pl h r δ).C m h')) = fun h' => U.u (pl.C m h') := by
      funext h'
      simp only [perturb, hne0 h' (by omega), hne0 (Fin.init h') (by omega), ↓reduceIte]
      ring_nf
    rw [this, sub_self, mul_zero]
  have hdiff : lifetime E U β (perturb pl h r δ) - lifetime E U β pl = ∑' m, f m := by
    unfold lifetime
    rw [← ((summable_u E U hpl').hasSum.sub (summable_u E U hpl).hasSum).tsum_eq]
    apply tsum_congr; intro m; simp only [hf]; ring
  rw [hdiff, tsum_eq_sum hzero, Finset.sum_pair (by omega)]
  congr 1
  · -- date `n`: only the node `h` changes
    simp only [hf]
    congr 1
    unfold ReputationTrigger.History.hexp
    rw [← Finset.sum_sub_distrib]
    rw [Finset.sum_eq_single h]
    · simp only [perturb, hne0 (Fin.init h) (show n ≠ n + 1 by omega), ↓reduceIte]
      ring_nf
    · intro b _ hb
      have hb' : List.ofFn b ≠ List.ofFn h := fun he => hb (List.ofFn_injective he)
      simp only [perturb, hb', hne0 (Fin.init b) (show n ≠ n + 1 by omega), ↓reduceIte]
      ring_nf
    · intro hh; exact absurd (Finset.mem_univ h) hh
  · -- date `n + 1`: only the successors of `h` change
    simp only [hf]
    congr 1
    unfold ReputationTrigger.History.hexp
    rw [← Finset.sum_sub_distrib, ReputationTrigger.History.sum_snoc]
    rw [Finset.sum_eq_single h]
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro s _
      simp only [perturb, Fin.init_snoc,
        hne0 (Fin.snoc h s : Fin (n + 2) → S) (show n + 2 ≠ n + 1 by omega), ↓reduceIte,
        ReputationTrigger.History.histProb_snoc]
      ring_nf
    · intro b _ hb
      apply Finset.sum_eq_zero; intro s _
      have hb' : List.ofFn b ≠ List.ofFn h := fun he => hb (List.ofFn_injective he)
      simp only [perturb, Fin.init_snoc,
        hne0 (Fin.snoc b s : Fin (n + 2) → S) (show n + 2 ≠ n + 1 by omega), hb', ↓reduceIte]
      ring_nf
    · intro hh; exact absurd (Finset.mem_univ h) hh

/-- **The Euler inequality along an optimal plan, finite-`δ` form** (O&R p. 373, Worrall's
sketch): at every node `h` of positive probability and every `0 < δ < C_n(h)`,
`β(1 + r)E_h u′(C_{n+1} + (1 + r)δ) ≤ u′(C_n(h) − δ)`. -/
theorem euler_delta {β r B₀ : ℝ} (hβ0 : 0 < β) (hr : -1 < r) {pl : Plan S}
    (hopt : Optimal E U β r B₀ pl) {n : ℕ} (h : Fin (n + 1) → S) {δ : ℝ} (hδ0 : 0 < δ)
    (hδ : δ < pl.C n h) :
    β * (1 + r) * E.Ω.expect (fun s =>
        U.du (pl.C (n + 1) (Fin.snoc h s : Fin (n + 2) → S) + (1 + r) * δ)) ≤
      U.du (pl.C n h - δ) := by
  classical
  obtain ⟨hpl, hmax⟩ := hopt
  have hgain := perturb_gain E U hr hpl h hδ0 hδ
  have hle := hmax _ (perturb_admissible E U hr hpl h hδ0 hδ)
  have hC := hpl.2.2.2.2.2.1
  set p := ReputationTrigger.History.histProb E.Ω h
  have hp : 0 < p := Finset.prod_pos fun i _ => E.prob_pos (h i)
  have hx : 0 < (1 + r) * δ := mul_pos (by linarith) hδ0
  have hCd : 0 < pl.C n h - δ := by linarith
  -- lower bounds from the supporting line
  have h1 : -(δ * U.du (pl.C n h - δ)) ≤ U.u (pl.C n h - δ) - U.u (pl.C n h) := by
    have := U.supporting_line (hC n h) hCd
    have e : pl.C n h - (pl.C n h - δ) = δ := by ring
    rw [e] at this; linarith
  have h2 : ∀ s, (1 + r) * δ *
      U.du (pl.C (n + 1) (Fin.snoc h s : Fin (n + 2) → S) + (1 + r) * δ) ≤
      U.u (pl.C (n + 1) (Fin.snoc h s : Fin (n + 2) → S) + (1 + r) * δ) -
        U.u (pl.C (n + 1) (Fin.snoc h s : Fin (n + 2) → S)) := by
    intro s
    have hc := hC (n + 1) (Fin.snoc h s : Fin (n + 2) → S)
    have := U.supporting_line hc (show 0 < pl.C (n + 1) (Fin.snoc h s : Fin (n + 2) → S) +
      (1 + r) * δ by linarith)
    have e : pl.C (n + 1) (Fin.snoc h s : Fin (n + 2) → S) -
        (pl.C (n + 1) (Fin.snoc h s : Fin (n + 2) → S) + (1 + r) * δ) = -((1 + r) * δ) := by
      ring
    rw [e] at this; linarith
  have h2s : (1 + r) * δ * E.Ω.expect (fun s =>
      U.du (pl.C (n + 1) (Fin.snoc h s : Fin (n + 2) → S) + (1 + r) * δ)) ≤
      ∑ s, E.Ω.prob s * (U.u (pl.C (n + 1) (Fin.snoc h s : Fin (n + 2) → S) + (1 + r) * δ) -
        U.u (pl.C (n + 1) (Fin.snoc h s : Fin (n + 2) → S))) := by
    unfold StateSpace.expect
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun s _ => by
      have := mul_le_mul_of_nonneg_left (h2 s) (E.Ω.prob_nonneg s)
      linarith
  have hβn : 0 < β ^ n := pow_pos hβ0 n
  have key : β ^ n * p * δ * (β * (1 + r) * E.Ω.expect (fun s =>
      U.du (pl.C (n + 1) (Fin.snoc h s : Fin (n + 2) → S) + (1 + r) * δ)) -
        U.du (pl.C n h - δ)) ≤ 0 := by
    have a1 := mul_le_mul_of_nonneg_left h1 (mul_nonneg hβn.le hp.le)
    have a2 := mul_le_mul_of_nonneg_left h2s (mul_nonneg (pow_pos hβ0 (n + 1)).le hp.le)
    have : lifetime E U β (perturb pl h r δ) - lifetime E U β pl ≤ 0 := by linarith
    rw [hgain] at this
    have e : β ^ (n + 1) = β ^ n * β := pow_succ β n
    rw [e] at a2 this
    nlinarith
  have hpos : 0 < β ^ n * p * δ := mul_pos (mul_pos hβn hp) hδ0
  have := (mul_nonpos_iff_pos_imp_nonpos.mp key).1 hpos
  linarith

/-- **The Euler inequality in the limit** (O&R p. 373; marginal utility is continuous,
`Utility.du_continuousOn`): along an optimal plan `β(1 + r)E_h u′(C_{n+1}) ≤ u′(C_n(h))` at
every node; with `β(1 + r) = 1` marginal utility is a supermartingale. -/
theorem euler_supermartingale {β r B₀ : ℝ} (hβ0 : 0 < β) (hr : -1 < r)
    {pl : Plan S} (hopt : Optimal E U β r B₀ pl) {n : ℕ} (h : Fin (n + 1) → S) :
    β * (1 + r) * E.Ω.expect (fun s => U.du (pl.C (n + 1) (Fin.snoc h s : Fin (n + 2) → S))) ≤
      U.du (pl.C n h) := by
  have hC := hopt.1.2.2.2.2.2.1
  have hcat : ∀ x, 0 < x → ContinuousAt U.du x := fun x hx =>
    U.du_continuousOn.continuousAt (Ioi_mem_nhds hx)
  -- both sides are continuous in `δ` at `0`
  have hL : Tendsto (fun δ => β * (1 + r) * E.Ω.expect (fun s =>
      U.du (pl.C (n + 1) (Fin.snoc h s : Fin (n + 2) → S) + (1 + r) * δ))) (𝓝[>] 0)
      (𝓝 (β * (1 + r) * E.Ω.expect (fun s =>
        U.du (pl.C (n + 1) (Fin.snoc h s : Fin (n + 2) → S))))) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds
    apply Tendsto.const_mul
    unfold StateSpace.expect
    apply tendsto_finsetSum; intro s _
    apply Tendsto.const_mul
    have hc := hC (n + 1) (Fin.snoc h s : Fin (n + 2) → S)
    have : Tendsto (fun δ : ℝ => pl.C (n + 1) (Fin.snoc h s : Fin (n + 2) → S) + (1 + r) * δ)
        (𝓝 0) (𝓝 (pl.C (n + 1) (Fin.snoc h s : Fin (n + 2) → S))) := by
      have h' := (tendsto_const_nhds (x := pl.C (n + 1) (Fin.snoc h s : Fin (n + 2) → S))).add
        ((tendsto_const_nhds (x := 1 + r)).mul (tendsto_id (x := 𝓝 (0 : ℝ))))
      rw [mul_zero, add_zero] at h'
      exact h'
    exact (hcat _ hc).tendsto.comp this
  have hR : Tendsto (fun δ => U.du (pl.C n h - δ)) (𝓝[>] 0) (𝓝 (U.du (pl.C n h))) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds
    have : Tendsto (fun δ : ℝ => pl.C n h - δ) (𝓝 0) (𝓝 (pl.C n h)) := by
      have h' := (tendsto_const_nhds (x := pl.C n h)).sub (tendsto_id (x := 𝓝 (0 : ℝ)))
      rw [sub_zero] at h'
      exact h'
    exact (hcat _ (hC n h)).tendsto.comp this
  have hev : ∀ᶠ δ in 𝓝[>] (0 : ℝ), β * (1 + r) * E.Ω.expect (fun s =>
      U.du (pl.C (n + 1) (Fin.snoc h s : Fin (n + 2) → S) + (1 + r) * δ)) ≤
      U.du (pl.C n h - δ) := by
    have hmem : Set.Ioo (0 : ℝ) (pl.C n h) ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT (hC n h)
    filter_upwards [hmem] with δ hδ
    exact euler_delta E U hβ0 hr hopt h hδ.1 hδ.2
  exact le_of_tendsto_of_tendsto hL hR hev

/-- **Expected marginal utility falls over time and converges** along an optimal plan
(O&R p. 373, "mean consumption rises over time", in marginal-utility form): with
`β(1 + r) = 1`, `E u′(C_{n+1}) ≤ E u′(C_n)` for all `n`, and the sequence
converges. -/
theorem expected_marginal_utility_converges {β r B₀ : ℝ} (hβ0 : 0 < β) (hr : -1 < r)
    (hβ : β * (1 + r) = 1) {pl : Plan S}
    (hopt : Optimal E U β r B₀ pl) :
    Antitone (fun n => ReputationTrigger.History.hexp E.Ω (n + 1)
        (fun h => U.du (pl.C n h))) ∧
      ∃ L, Tendsto (fun n => ReputationTrigger.History.hexp E.Ω (n + 1)
        (fun h => U.du (pl.C n h))) atTop (𝓝 L) := by
  have hC := hopt.1.2.2.2.2.2.1
  have hstep : ∀ n, ReputationTrigger.History.hexp E.Ω (n + 2)
      (fun h => U.du (pl.C (n + 1) h)) ≤
      ReputationTrigger.History.hexp E.Ω (n + 1) (fun h => U.du (pl.C n h)) := by
    intro n
    rw [ReputationTrigger.History.hexp_succ]
    apply ReputationTrigger.History.hexp_mono
    intro g
    have := euler_supermartingale E U hβ0 hr hopt g
    rw [hβ, one_mul] at this
    exact this
  have hanti : Antitone (fun n => ReputationTrigger.History.hexp E.Ω (n + 1)
      (fun h => U.du (pl.C n h))) := antitone_nat_of_succ_le hstep
  refine ⟨hanti, _, tendsto_atTop_ciInf hanti ⟨0, ?_⟩⟩
  rintro _ ⟨n, rfl⟩
  have := ReputationTrigger.History.hexp_mono E.Ω (n + 1) (X := fun _ => (0 : ℝ))
    (Y := fun h => U.du (pl.C n h)) (fun h => (U.du_pos _ (hC n h)).le)
  rwa [ReputationTrigger.History.hexp_const] at this

/-! ### Convergence: after the first top shock the plan is a first-best steady state -/

/-- Summing over date-`(n + j)` nodes is summing over date-`n` nodes and their extensions
(i.i.d., O&R (11)). -/
theorem sum_extendD {n : ℕ} : ∀ j (F : (Fin (n + j + 1) → S) → ℝ),
    ∑ g, ReputationTrigger.History.histProb E.Ω g * F g =
      ∑ h : Fin (n + 1) → S, ReputationTrigger.History.histProb E.Ω h *
        ∑ k : Fin j → S, ReputationTrigger.History.histProb E.Ω k * F (extendD h j k) := by
  intro j
  induction j with
  | zero =>
    intro F
    apply Finset.sum_congr rfl; intro h _
    rw [Fintype.sum_unique]
    simp [ReputationTrigger.History.histProb, extendD]
  | succ j ih =>
    intro F
    change ∑ g : Fin (n + j + 1 + 1) → S, _ = _
    rw [ReputationTrigger.History.sum_snoc]
    simp only [ReputationTrigger.History.histProb_snoc]
    have hih := ih (fun g' => ∑ s, E.Ω.prob s * F (Fin.snoc g' s : Fin (n + j + 1 + 1) → S))
    have eL : ∑ g' : Fin (n + j + 1) → S, ∑ s, ReputationTrigger.History.histProb E.Ω g' *
        E.Ω.prob s * F (Fin.snoc g' s : Fin (n + j + 1 + 1) → S) =
        ∑ g' : Fin (n + j + 1) → S, ReputationTrigger.History.histProb E.Ω g' *
          ∑ s, E.Ω.prob s * F (Fin.snoc g' s : Fin (n + j + 1 + 1) → S) := by
      apply Finset.sum_congr rfl; intro g' _; rw [Finset.mul_sum]
      apply Finset.sum_congr rfl; intro s _; ring
    rw [eL, hih]
    apply Finset.sum_congr rfl; intro h _
    congr 1
    rw [ReputationTrigger.History.sum_snoc]
    simp only [ReputationTrigger.History.histProb_snoc, extendD, Fin.init_snoc, Fin.snoc_last]
    apply Finset.sum_congr rfl; intro k' _; rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro s _; ring

/-- The expectation over the subtree of the date-`n` node `h`, `j` dates ahead:
`E_h[F] = Σ_k π(k) F(h ⌢ k)` (O&R (11), p. 364). -/
noncomputable def condE {n : ℕ} (h : Fin (n + 1) → S) (j : ℕ)
    (F : (Fin (n + j + 1) → S) → ℝ) : ℝ :=
  ∑ k : Fin j → S, ReputationTrigger.History.histProb E.Ω k * F (extendD h j k)

/-- Cash on hand at a date-`n` node after the insurance payment: `x = (1 + r)B_n + Y − P_n`
(O&R (12), p. 364). -/
def cash (r : ℝ) (pl : Plan S) {n : ℕ} (h : Fin (n + 1) → S) : ℝ :=
  (1 + r) * pl.B n (Fin.init h) + E.Y (h (Fin.last n)) - pl.P n h

/-- Collateral guarantees cash at least equal to current output (O&R p. 373). -/
theorem output_le_cash {β r B₀ : ℝ} {pl : Plan S} (hpl : Admissible E U β r B₀ pl) {n : ℕ}
    (h : Fin (n + 1) → S) : E.Y (h (Fin.last n)) ≤ cash E r pl h := by
  have := hpl.2.2.1 n h; unfold cash; linarith

/-- The subtree budget, O&R (12): `E_h B_{n+j+2} = (1 + r)E_h B_{n+j+1} + Ȳ − E_h C_{n+j+1}`
(per-period zero profit makes the expected insurance payment vanish). -/
theorem cond_budget {β r B₀ : ℝ} {pl : Plan S} (hpl : Admissible E U β r B₀ pl) {n : ℕ}
    (h : Fin (n + 1) → S) (j : ℕ) :
    condE E h (j + 1) (fun g => pl.B (n + j + 1 + 1) g) =
      (1 + r) * condE E h j (fun g => pl.B (n + j + 1) g) + E.Ybar -
        condE E h (j + 1) (fun g => pl.C (n + j + 1) g) := by
  obtain ⟨_, hbud, _, hzp, _⟩ := hpl
  unfold condE
  rw [ReputationTrigger.History.sum_snoc, ReputationTrigger.History.sum_snoc]
  simp only [ReputationTrigger.History.histProb_snoc, extendD, Fin.init_snoc, Fin.snoc_last]
  have hb : ∀ k' : Fin j → S, ∀ s, pl.B (n + j + 1 + 1)
      (Fin.snoc (extendD h j k') s : Fin (n + j + 1 + 1) → S) =
      (1 + r) * pl.B (n + j + 1) (extendD h j k') + E.Y s -
        pl.C (n + j + 1) (Fin.snoc (extendD h j k') s : Fin (n + j + 1 + 1) → S) -
        pl.P (n + j + 1) (Fin.snoc (extendD h j k') s : Fin (n + j + 1 + 1) → S) := by
    intro k' s
    have := hbud (n + j + 1) (Fin.snoc (extendD h j k') s : Fin (n + j + 1 + 1) → S)
    rw [Fin.init_snoc, Fin.snoc_last] at this
    exact this
  simp only [hb]
  have hY : ∀ k' : Fin j → S, ∑ s, ReputationTrigger.History.histProb E.Ω k' * E.Ω.prob s *
      E.Y s = ReputationTrigger.History.histProb E.Ω k' * E.Ybar := by
    intro k'
    rw [← E.expect_Y]; unfold StateSpace.expect; rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro s _; ring
  have hP : ∀ k' : Fin j → S, ∑ s, ReputationTrigger.History.histProb E.Ω k' * E.Ω.prob s *
      pl.P (n + j + 1) (Fin.snoc (extendD h j k') s : Fin (n + j + 1 + 1) → S) = 0 := by
    intro k'
    have := hzp (n + j + 1) (extendD h j k')
    rw [show (∑ s, ReputationTrigger.History.histProb E.Ω k' * E.Ω.prob s *
      pl.P (n + j + 1) (Fin.snoc (extendD h j k') s : Fin (n + j + 1 + 1) → S)) =
      ReputationTrigger.History.histProb E.Ω k' * ∑ s, E.Ω.prob s *
        pl.P (n + j + 1) (Fin.snoc (extendD h j k') s : Fin (n + j + 1 + 1) → S) from by
      rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro s _; ring, this, mul_zero]
  have hsum1 : ∑ k' : Fin j → S, ReputationTrigger.History.histProb E.Ω k' = 1 :=
    ReputationTrigger.History.histProb_sum E.Ω j
  have e : ∀ k' : Fin j → S, ∑ s, ReputationTrigger.History.histProb E.Ω k' * E.Ω.prob s *
      ((1 + r) * pl.B (n + j + 1) (extendD h j k') + E.Y s -
        pl.C (n + j + 1) (Fin.snoc (extendD h j k') s : Fin (n + j + 1 + 1) → S) -
        pl.P (n + j + 1) (Fin.snoc (extendD h j k') s : Fin (n + j + 1 + 1) → S)) =
      (1 + r) * (ReputationTrigger.History.histProb E.Ω k' * pl.B (n + j + 1) (extendD h j k'))
        + ReputationTrigger.History.histProb E.Ω k' * E.Ybar -
        ∑ s, ReputationTrigger.History.histProb E.Ω k' * E.Ω.prob s *
          pl.C (n + j + 1) (Fin.snoc (extendD h j k') s : Fin (n + j + 1 + 1) → S) := by
    intro k'
    have h1 := hY k'
    have h2 := hP k'
    have h3 : ∑ s, ReputationTrigger.History.histProb E.Ω k' * E.Ω.prob s *
        ((1 + r) * pl.B (n + j + 1) (extendD h j k')) =
        (1 + r) * (ReputationTrigger.History.histProb E.Ω k' *
          pl.B (n + j + 1) (extendD h j k')) := by
      rw [← Finset.sum_mul, ← Finset.mul_sum, E.Ω.prob_sum]; ring
    have hsplit : ∑ s, ReputationTrigger.History.histProb E.Ω k' * E.Ω.prob s *
        ((1 + r) * pl.B (n + j + 1) (extendD h j k') + E.Y s -
          pl.C (n + j + 1) (Fin.snoc (extendD h j k') s : Fin (n + j + 1 + 1) → S) -
          pl.P (n + j + 1) (Fin.snoc (extendD h j k') s : Fin (n + j + 1 + 1) → S)) =
        ∑ s, ReputationTrigger.History.histProb E.Ω k' * E.Ω.prob s *
          ((1 + r) * pl.B (n + j + 1) (extendD h j k')) +
        ∑ s, ReputationTrigger.History.histProb E.Ω k' * E.Ω.prob s * E.Y s -
        ∑ s, ReputationTrigger.History.histProb E.Ω k' * E.Ω.prob s *
          pl.C (n + j + 1) (Fin.snoc (extendD h j k') s : Fin (n + j + 1 + 1) → S) -
        ∑ s, ReputationTrigger.History.histProb E.Ω k' * E.Ω.prob s *
          pl.P (n + j + 1) (Fin.snoc (extendD h j k') s : Fin (n + j + 1 + 1) → S) := by
      rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl; intro s _; ring
    rw [hsplit, h3, h1, h2]; ring
  simp only [e]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul,
    hsum1, one_mul]

/-- The discounted subtree budget (O&R (12) with `β(1 + r) = 1`): for every horizon `J`,
`Σ_{j ≤ J} βʲ E_h C_{n+j} = x + Σ_{j < J} β^{j+1} Ȳ − β^J E_h B_{n+J+1}`. -/
theorem cond_telescope {β r B₀ : ℝ} (hβ : β * (1 + r) = 1) {pl : Plan S}
    (hpl : Admissible E U β r B₀ pl) {n : ℕ} (h : Fin (n + 1) → S) : ∀ J,
    ∑ j ∈ Finset.range (J + 1), β ^ j * condE E h j (fun g => pl.C (n + j) g) =
      cash E r pl h + ∑ j ∈ Finset.range J, β ^ (j + 1) * E.Ybar -
        β ^ J * condE E h J (fun g => pl.B (n + J + 1) g) := by
  intro J
  induction J with
  | zero =>
    simp only [zero_add, Finset.sum_range_one, pow_zero, one_mul, Finset.range_zero,
      Finset.sum_empty, add_zero]
    unfold condE
    rw [Fintype.sum_unique, Fintype.sum_unique]
    simp only [ReputationTrigger.History.histProb, Finset.univ_eq_empty, Finset.prod_empty,
      one_mul, extendD]
    have := hpl.2.1 n h
    change pl.C n h = cash E r pl h - pl.B (n + 1) h
    unfold cash; linarith
  | succ J ih =>
    rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]
    have hb := cond_budget E U hpl h J
    have e1 : condE E h (J + 1) (fun g => pl.C (n + (J + 1)) g) =
        condE E h (J + 1) (fun g => pl.C (n + J + 1) g) := rfl
    have e2 : condE E h (J + 1) (fun g => pl.B (n + (J + 1) + 1) g) =
        condE E h (J + 1) (fun g => pl.B (n + J + 1 + 1) g) := rfl
    rw [e1, e2, hb]
    have : β ^ (J + 1) * (1 + r) = β ^ J := by rw [pow_succ, mul_assoc, hβ, mul_one]
    linear_combination (condE E h J fun g => pl.B (n + J + 1) g) * this

/-- The subtree expectation of a nonnegative variable is nonnegative. (O&R p. 373) -/
theorem condE_nonneg {n : ℕ} (h : Fin (n + 1) → S) (j : ℕ) {F : (Fin (n + j + 1) → S) → ℝ}
    (hF : ∀ g, 0 ≤ F g) : 0 ≤ condE E h j F :=
  Finset.sum_nonneg fun k _ => mul_nonneg (ReputationTrigger.History.histProb_nonneg E.Ω k)
    (hF _)

/-- **The subtree present-value budget** (O&R p. 373): expected discounted consumption from
node `h` on is at most cash on hand plus the value of future output,
`Σ_j βʲ E_h C_{n+j} ≤ x + βȲ/(1 − β)`. -/
theorem cond_consumption_bound {β r B₀ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hβ : β * (1 + r) = 1) {pl : Plan S} (hpl : Admissible E U β r B₀ pl) {n : ℕ}
    (h : Fin (n + 1) → S) :
    Summable (fun j => β ^ j * condE E h j (fun g => pl.C (n + j) g)) ∧
      ∑' j, β ^ j * condE E h j (fun g => pl.C (n + j) g) ≤
        cash E r pl h + β / (1 - β) * E.Ybar := by
  have hY := E.Ybar_pos
  have hcash : 0 ≤ cash E r pl h := le_trans (E.Y_pos _).le (output_le_cash E U hpl h)
  have hnn : ∀ j, 0 ≤ β ^ j * condE E h j (fun g => pl.C (n + j) g) := fun j =>
    mul_nonneg (pow_nonneg hβ0.le j) (condE_nonneg E h j fun g => (hpl.2.2.2.2.2.1 _ g).le)
  have hgeo : ∀ J, ∑ j ∈ Finset.range J, β ^ (j + 1) * E.Ybar ≤ β / (1 - β) * E.Ybar := by
    intro J
    have hs := Geometric.hasSum_geometric_from_one hβ0.le hβ1 E.Ybar
    rw [← hs.tsum_eq]
    exact hs.summable.sum_le_tsum _ fun j _ => mul_nonneg (pow_nonneg hβ0.le _) hY.le
  have hpart : ∀ N, ∑ j ∈ Finset.range N, β ^ j * condE E h j (fun g => pl.C (n + j) g) ≤
      cash E r pl h + β / (1 - β) * E.Ybar := by
    intro N
    rcases N with _ | J
    · simp only [Finset.range_zero, Finset.sum_empty]
      have : 0 ≤ β / (1 - β) * E.Ybar := mul_nonneg (div_nonneg hβ0.le (by linarith)) hY.le
      linarith
    · rw [cond_telescope E U hβ hpl h J]
      have hB : 0 ≤ β ^ J * condE E h J (fun g => pl.B (n + J + 1) g) :=
        mul_nonneg (pow_nonneg hβ0.le J) (condE_nonneg E h J fun g => hpl.2.2.2.2.1 _ g)
      linarith [hgeo J]
  exact ⟨summable_of_sum_range_le hnn hpart, Real.tsum_le_of_sum_range_le hnn hpart⟩

/-- The continuation utility series from any node converges (O&R (11)). -/
theorem cond_utility_summable {β r B₀ : ℝ} (hβ0 : 0 < β) {pl : Plan S}
    (hpl : Admissible E U β r B₀ pl) {n : ℕ} (h : Fin (n + 1) → S) :
    Summable (fun j => β ^ j * condE E h j (fun g => U.u (pl.C (n + j) g))) := by
  have hp : 0 < ReputationTrigger.History.histProb E.Ω h :=
    Finset.prod_pos fun i _ => E.prob_pos (h i)
  have habs := (summable_nat_add_iff n).mpr hpl.2.2.2.2.2.2
  have hbound : ∀ j, ‖β ^ j * condE E h j (fun g => U.u (pl.C (n + j) g))‖ ≤
      (β ^ n * ReputationTrigger.History.histProb E.Ω h)⁻¹ * (β ^ (j + n) *
        ReputationTrigger.History.hexp E.Ω (j + n + 1) (fun g => |U.u (pl.C (j + n) g)|)) := by
    intro j
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0.le j)]
    have h1 : |condE E h j (fun g => U.u (pl.C (n + j) g))| ≤
        condE E h j (fun g => |U.u (pl.C (n + j) g)|) := by
      unfold condE
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) (le_of_eq ?_)
      apply Finset.sum_congr rfl; intro k _
      rw [abs_mul, abs_of_nonneg (ReputationTrigger.History.histProb_nonneg E.Ω k)]
    have h2 : ReputationTrigger.History.histProb E.Ω h *
        condE E h j (fun g => |U.u (pl.C (n + j) g)|) ≤
        ReputationTrigger.History.hexp E.Ω (j + n + 1) (fun g => |U.u (pl.C (j + n) g)|) := by
      have e : ReputationTrigger.History.hexp E.Ω (j + n + 1)
          (fun g => |U.u (pl.C (j + n) g)|) =
          ReputationTrigger.History.hexp E.Ω (n + j + 1)
            (fun g => |U.u (pl.C (n + j) g)|) := by rw [Nat.add_comm j n]
      rw [e]
      unfold ReputationTrigger.History.hexp
      rw [sum_extendD E j]
      unfold condE
      exact Finset.single_le_sum (f := fun h' => ReputationTrigger.History.histProb E.Ω h' *
        ∑ k : Fin j → S, ReputationTrigger.History.histProb E.Ω k *
          |U.u (pl.C (n + j) (extendD h' j k))|)
        (fun h' _ => mul_nonneg (ReputationTrigger.History.histProb_nonneg E.Ω h')
          (Finset.sum_nonneg fun k _ => mul_nonneg
            (ReputationTrigger.History.histProb_nonneg E.Ω k) (abs_nonneg _)))
        (Finset.mem_univ h)
    have hβn := pow_pos hβ0 n
    rw [pow_add, show (β ^ n * ReputationTrigger.History.histProb E.Ω h)⁻¹ *
      (β ^ j * β ^ n * ReputationTrigger.History.hexp E.Ω (j + n + 1)
        (fun g => |U.u (pl.C (j + n) g)|)) = β ^ j * ((ReputationTrigger.History.histProb E.Ω h)⁻¹
          * ReputationTrigger.History.hexp E.Ω (j + n + 1) (fun g => |U.u (pl.C (j + n) g)|))
      from by field_simp]
    apply mul_le_mul_of_nonneg_left _ (pow_nonneg hβ0.le j)
    rw [le_inv_mul_iff₀ hp]
    have := mul_le_mul_of_nonneg_left h1 hp.le
    linarith
  exact Summable.of_norm_bounded ((habs.mul_left _)) hbound

/-- **The subtree first-best bound**, O&R p. 373 (`β(1 + r) = 1`): from any node with cash `x`,
expected discounted utility is at most `u(c∞)/(1 − β)` with `c∞ = (1 − β)x + βȲ`, strictly less
unless consumption equals `c∞` at every node of the subtree. -/
theorem cond_first_best {β r B₀ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hβ : β * (1 + r) = 1)
    {pl : Plan S} (hpl : Admissible E U β r B₀ pl) {n : ℕ} (h : Fin (n + 1) → S) :
    ∑' j, β ^ j * condE E h j (fun g => U.u (pl.C (n + j) g)) ≤
        U.u ((1 - β) * cash E r pl h + β * E.Ybar) / (1 - β) ∧
      ((∃ j k, pl.C (n + j) (extendD h j k) ≠ (1 - β) * cash E r pl h + β * E.Ybar) →
        ∑' j, β ^ j * condE E h j (fun g => U.u (pl.C (n + j) g)) <
          U.u ((1 - β) * cash E r pl h + β * E.Ybar) / (1 - β)) := by
  set x := cash E r pl h with hx
  set c := (1 - β) * x + β * E.Ybar with hc
  have hY := E.Ybar_pos
  have hxpos : 0 < x := lt_of_lt_of_le (E.Y_pos _) (output_le_cash E U hpl h)
  have hcpos : 0 < c := by simp only [hc]; nlinarith
  have hC := hpl.2.2.2.2.2.1
  obtain ⟨hsC, hbC⟩ := cond_consumption_bound E U hβ0 hβ1 hβ hpl h
  have hsU := cond_utility_summable E U hβ0 hpl h
  set d := U.du c
  have hdpos : 0 < d := U.du_pos c hcpos
  have hsum1 : ∀ j, ∑ k : Fin j → S, ReputationTrigger.History.histProb E.Ω k = 1 :=
    ReputationTrigger.History.histProb_sum E.Ω
  -- termwise supporting line
  have hterm : ∀ j, condE E h j (fun g => U.u (pl.C (n + j) g)) ≤
      (U.u c - d * c) + d * condE E h j (fun g => pl.C (n + j) g) := by
    intro j
    unfold condE
    rw [Finset.mul_sum]
    have : U.u c - d * c = ∑ k : Fin j → S, ReputationTrigger.History.histProb E.Ω k *
        (U.u c - d * c) := by rw [← Finset.sum_mul, hsum1, one_mul]
    rw [this, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum; intro k _
    have hsl := U.supporting_line (hC (n + j) (extendD h j k)) hcpos
    have := mul_le_mul_of_nonneg_left hsl (ReputationTrigger.History.histProb_nonneg E.Ω k)
    linarith
  have hgeo := Geometric.hasSum_geometric_const hβ0.le hβ1 (U.u c - d * c)
  have hR : Summable (fun j => β ^ j * ((U.u c - d * c) +
      d * condE E h j (fun g => pl.C (n + j) g))) := by
    have := hgeo.summable.add (hsC.mul_left d)
    refine this.congr fun j => ?_; ring
  have hRval : ∑' j, β ^ j * ((U.u c - d * c) + d * condE E h j (fun g => pl.C (n + j) g)) =
      (U.u c - d * c) / (1 - β) + d * ∑' j, β ^ j * condE E h j (fun g => pl.C (n + j) g) := by
    rw [← hgeo.tsum_eq, ← hsC.tsum_mul_left, ← hgeo.summable.tsum_add (hsC.mul_left d)]
    apply tsum_congr; intro j; ring
  have hbud : x + β / (1 - β) * E.Ybar = c / (1 - β) := by
    have h1β : (1 : ℝ) - β ≠ 0 := by linarith
    simp only [hc]; field_simp
  have hfinal : (U.u c - d * c) / (1 - β) + d * (c / (1 - β)) = U.u c / (1 - β) := by ring
  have hle := hsU.tsum_le_tsum (fun j => mul_le_mul_of_nonneg_left (hterm j)
    (pow_nonneg hβ0.le j)) hR
  rw [hRval] at hle
  have hdb := mul_le_mul_of_nonneg_left hbC hdpos.le
  rw [hbud] at hdb
  refine ⟨by linarith, fun ⟨j₀, k₀, hne⟩ => ?_⟩
  have hstrict : condE E h j₀ (fun g => U.u (pl.C (n + j₀) g)) <
      (U.u c - d * c) + d * condE E h j₀ (fun g => pl.C (n + j₀) g) := by
    unfold condE
    rw [Finset.mul_sum]
    have : U.u c - d * c = ∑ k : Fin j₀ → S, ReputationTrigger.History.histProb E.Ω k *
        (U.u c - d * c) := by rw [← Finset.sum_mul, hsum1, one_mul]
    rw [this, ← Finset.sum_add_distrib]
    apply Finset.sum_lt_sum
    · intro k _
      have hsl := U.supporting_line (hC (n + j₀) (extendD h j₀ k)) hcpos
      have := mul_le_mul_of_nonneg_left hsl (ReputationTrigger.History.histProb_nonneg E.Ω k)
      linarith
    · refine ⟨k₀, Finset.mem_univ _, ?_⟩
      have hsl := U.supporting_line_strict (hC (n + j₀) (extendD h j₀ k₀)) hcpos hne
      have hp : 0 < ReputationTrigger.History.histProb E.Ω k₀ :=
        Finset.prod_pos fun i _ => E.prob_pos (k₀ i)
      have := mul_lt_mul_of_pos_left hsl hp
      linarith
  have hlt := hsU.tsum_lt_tsum (i := j₀) (fun j => mul_le_mul_of_nonneg_left (hterm j)
    (pow_nonneg hβ0.le j)) (mul_lt_mul_of_pos_left hstrict (pow_pos hβ0 j₀)) hR
  rw [hRval] at hlt
  linarith

/-- Consumption of the settled plan: `c` at every node of the subtree of `h`
(O&R p. 373, the steady state). -/
noncomputable def settleC [DecidableEq S] (pl : Plan S) {n : ℕ} (h : Fin (n + 1) → S) (c : ℝ) :
    (m : ℕ) → (Fin (m + 1) → S) → ℝ :=
  fun m g => if hm : n ≤ m then (if preN hm g = h then c else pl.C m g) else pl.C m g

/-- Insurance payments of the settled plan: full insurance `P = ε` strictly below node `h`
(O&R p. 373). -/
noncomputable def settleP [DecidableEq S] (pl : Plan S) {n : ℕ} (h : Fin (n + 1) → S) :
    (m : ℕ) → (Fin (m + 1) → S) → ℝ :=
  fun m g => if hm : n < m then (if preN hm.le g = h then E.ε (g (Fin.last m)) else pl.P m g)
    else pl.P m g

/-- Assets of the settled plan: constant `B′` carried out of every node of the subtree of `h`
(O&R p. 373). -/
noncomputable def settleB [DecidableEq S] (pl : Plan S) {n : ℕ} (h : Fin (n + 1) → S) (B' : ℝ) :
    (m : ℕ) → (Fin m → S) → ℝ
  | 0, g => pl.B 0 g
  | m + 1, g => if hm : n ≤ m then (if preN hm g = h then B' else pl.B (m + 1) g)
      else pl.B (m + 1) g

/-- The plan that follows `pl` outside the subtree of `h` and the first-best steady state
(consumption `c`, assets `B′`, full insurance) inside it (O&R p. 373). -/
noncomputable def settle [DecidableEq S] (pl : Plan S) {n : ℕ} (h : Fin (n + 1) → S)
    (c B' : ℝ) : Plan S :=
  ⟨settleC pl h c, settleP E pl h, settleB pl h B'⟩

/-- **The settled plan is admissible** (O&R p. 373) when the node's cash covers every
full-insurance payment, `ε ≤ x − Ȳ` (collateral), with `c = (1 − β)x + βȲ` and
`B′ = β(x − Ȳ)`, `β(1 + r) = 1`. -/
theorem settle_admissible [DecidableEq S] {β r B₀ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hβ : β * (1 + r) = 1) {pl : Plan S} (hpl : Admissible E U β r B₀ pl) {n : ℕ}
    (h : Fin (n + 1) → S) (hx : ∀ s, E.ε s ≤ cash E r pl h - E.Ybar) :
    Admissible E U β r B₀ (settle E pl h ((1 - β) * cash E r pl h + β * E.Ybar)
      (β * (cash E r pl h - E.Ybar))) := by
  obtain ⟨h0, hbud, hcol, hzp, hB, hC, habs⟩ := hpl
  set x := cash E r pl h with hxdef
  set c := (1 - β) * x + β * E.Ybar with hc
  set B' := β * (x - E.Ybar) with hB'
  have hY := E.Ybar_pos
  have hxpos : 0 < x := by
    have := hcol n h; have := E.Y_pos (h (Fin.last n)); simp only [hxdef, cash]; linarith
  have hcpos : 0 < c := by simp only [hc]; nlinarith
  have hcB : c = E.Ybar + r * B' := by
    simp only [hc, hB']
    have : r * β = 1 - β := by linarith
    nlinarith
  have hBx : B' = x - c := by simp only [hc, hB']; ring
  have hcolB : ∀ s, E.ε s ≤ (1 + r) * B' := fun s => by
    have : (1 + r) * B' = x - E.Ybar := by simp only [hB']; rw [← mul_assoc, mul_comm (1 + r),
      hβ, one_mul]
    rw [this]; exact hx s
  have hB'0 : 0 ≤ B' := by
    have := StateSpaceFacts.nonempty E.Ω
    obtain ⟨sm, _, hsm⟩ := Finset.exists_max_image Finset.univ E.ε Finset.univ_nonempty
    have hmean : E.Ω.expect E.ε ≤ E.ε sm := by
      have := expect_mono E.Ω (X := E.ε) (Y := fun _ => E.ε sm)
        fun s => hsm s (Finset.mem_univ s)
      rwa [E.Ω.expect_const] at this
    rw [E.mean_zero] at hmean
    have := hcolB sm
    have h1r : 0 < 1 + r := by nlinarith
    nlinarith
  have hpre_self : ∀ g : Fin (n + 1) → S, preN (le_refl n) g = g := fun g => by funext i; rfl
  have settleB_le : ∀ m (g : Fin m → S), m ≤ n → settleB pl h B' m g = pl.B m g := by
    intro m g hm
    rcases m with _ | m
    · rfl
    · simp only [settleB, show ¬ n ≤ m by omega, ↓reduceDIte]
  refine ⟨h0, fun m g => ?_, fun m g => ?_, fun m g => ?_, fun m g => ?_, fun m g => ?_, ?_⟩
  · -- budget
    simp only [settle]
    by_cases hm : n ≤ m
    · rcases eq_or_lt_of_le hm with hnm | hnm
      · subst hnm
        rw [settleB_le n (Fin.init g) le_rfl]
        simp only [settleB, settleC, settleP, le_refl, lt_irrefl, ↓reduceDIte, hpre_self]
        by_cases hg : g = h
        · subst hg; simp only [↓reduceIte]; rw [hBx]; simp only [hxdef, cash]; ring
        · simp only [hg, ↓reduceIte]; exact hbud n g
      · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
        have hm' : n ≤ m' := by omega
        simp only [settleB, settleC, settleP, hm, hm', hnm, ↓reduceDIte]
        rw [preN_init hm' g]
        by_cases hg : preN hm g = h
        · have hg' : preN (by omega : n ≤ m' + 1) g = h := hg
          simp only [hg', ↓reduceIte]
          rw [hcB]; unfold Endowment.Y; ring
        · have hg' : ¬ preN (by omega : n ≤ m' + 1) g = h := hg
          simp only [hg', ↓reduceIte]; exact hbud (m' + 1) g
    · have hmn : m ≤ n := by omega
      rw [settleB_le m (Fin.init g) hmn]
      simp only [settleB, settleC, settleP, hm, show ¬ n < m by omega, ↓reduceDIte]
      exact hbud m g
  · -- collateral
    simp only [settle]
    by_cases hm : n < m
    · obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      have hm' : n ≤ m' := by omega
      simp only [settleB, settleP, hm, hm', ↓reduceDIte]
      rw [preN_init hm' g]
      by_cases hg : preN hm.le g = h
      · have hg' : preN (by omega : n ≤ m' + 1) g = h := hg
        simp only [hg', ↓reduceIte]; exact hcolB _
      · have hg' : ¬ preN (by omega : n ≤ m' + 1) g = h := hg
        simp only [hg', ↓reduceIte]; exact hcol (m' + 1) g
    · rw [settleB_le m (Fin.init g) (by omega)]
      simp only [settleP, hm, ↓reduceDIte]
      exact hcol m g
  · -- zero profit
    simp only [settle, settleP]
    by_cases hm : n < m
    · simp only [hm, ↓reduceDIte]
      by_cases hin : ∃ s, preN hm.le (Fin.snoc g s : Fin (m + 1) → S) = h
      · obtain ⟨s₀, hs₀⟩ := hin
        have hall : ∀ s, preN hm.le (Fin.snoc g s : Fin (m + 1) → S) = h := fun s => by
          rw [preN_snoc hm g s s₀]; exact hs₀
        simp only [hall, ↓reduceIte, Fin.snoc_last]
        exact E.mean_zero
      · push Not at hin
        simp only [hin, ↓reduceIte]
        exact hzp m g
    · simp only [hm, ↓reduceDIte]; exact hzp m g
  · -- nonnegative assets
    simp only [settle]
    rcases m with _ | m
    · exact hB 0 g
    · simp only [settleB]
      split_ifs
      · exact hB'0
      · exact hB _ g
      · exact hB _ g
  · -- positive consumption
    simp only [settle, settleC]
    split_ifs
    · exact hcpos
    · exact hC m g
    · exact hC m g
  · -- absolute summability
    have hdom : ∀ m, β ^ m * ReputationTrigger.History.hexp E.Ω (m + 1)
        (fun g => |U.u ((settle E pl h c B').C m g)|) ≤
        β ^ m * ReputationTrigger.History.hexp E.Ω (m + 1) (fun g => |U.u (pl.C m g)|) +
          β ^ m * |U.u c| := by
      intro m
      rw [← mul_add]
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hβ0.le m)
      have := ReputationTrigger.History.hexp_mono E.Ω (m + 1)
        (X := fun g => |U.u ((settle E pl h c B').C m g)|)
        (Y := fun g => |U.u (pl.C m g)| + |U.u c|) fun g => by
          simp only [settle, settleC]
          split_ifs <;> linarith [abs_nonneg (U.u c), abs_nonneg (U.u (pl.C m g))]
      rw [show (fun g => |U.u (pl.C m g)| + |U.u c|) = fun g => 1 * |U.u (pl.C m g)| +
        |U.u c| * (fun _ => (1 : ℝ)) g from funext fun g => by ring,
        ReputationTrigger.History.hexp_linear, ReputationTrigger.History.hexp_const] at this
      linarith
    refine Summable.of_nonneg_of_le (fun m => mul_nonneg (pow_nonneg hβ0.le m)
      (Finset.sum_nonneg fun g _ => mul_nonneg
        (ReputationTrigger.History.histProb_nonneg E.Ω g) (abs_nonneg _))) hdom ?_
    exact habs.add ((summable_geometric_of_lt_one hβ0.le hβ1).mul_right _)

/-- The gain from settling at node `h`, computed exactly (O&R p. 373):
`lifetime(settled) − lifetime(pl) = βⁿ π(h)[u(c)/(1 − β) − Σ_j βʲ E_h u(C_{n+j})]`. -/
theorem settle_gain [DecidableEq S] {β r B₀ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {pl : Plan S}
    (hpl : Admissible E U β r B₀ pl) {n : ℕ} (h : Fin (n + 1) → S) {c B' : ℝ}
    (hpl' : Admissible E U β r B₀ (settle E pl h c B')) :
    lifetime E U β (settle E pl h c B') - lifetime E U β pl =
      β ^ n * ReputationTrigger.History.histProb E.Ω h *
        (U.u c / (1 - β) - ∑' j, β ^ j * condE E h j (fun g => U.u (pl.C (n + j) g))) := by
  set f : ℕ → ℝ := fun m => β ^ m * (ReputationTrigger.History.hexp E.Ω (m + 1)
    (fun g => U.u ((settle E pl h c B').C m g)) -
      ReputationTrigger.History.hexp E.Ω (m + 1) (fun g => U.u (pl.C m g))) with hf
  have hfs : Summable f := by
    have := (summable_u E U hpl').sub (summable_u E U hpl)
    refine this.congr fun m => ?_; simp only [hf]; ring
  have hdiff : lifetime E U β (settle E pl h c B') - lifetime E U β pl = ∑' m, f m := by
    unfold lifetime
    rw [← ((summable_u E U hpl').hasSum.sub (summable_u E U hpl).hasSum).tsum_eq]
    apply tsum_congr; intro m; simp only [hf]; ring
  have hlow : ∀ m, m < n → f m = 0 := by
    intro m hm
    simp only [hf, settle, settleC, show ¬ n ≤ m by omega, ↓reduceDIte, sub_self, mul_zero]
  have hshift : ∀ j, f (j + n) = β ^ n * ReputationTrigger.History.histProb E.Ω h *
      (β ^ j * (U.u c - condE E h j (fun g => U.u (pl.C (n + j) g)))) := by
    intro j
    rw [show j + n = n + j from Nat.add_comm j n]
    simp only [hf]
    have hs1 := sum_extendD E j (fun g => U.u ((settle E pl h c B').C (n + j) g))
    have hs2 := sum_extendD E j (fun g => U.u (pl.C (n + j) g))
    beta_reduce at hs1 hs2
    unfold ReputationTrigger.History.hexp
    beta_reduce
    rw [hs1, hs2]
    have hin : ∀ (h' : Fin (n + 1) → S) (k : Fin j → S),
        U.u ((settle E pl h c B').C (n + j) (extendD h' j k)) - U.u (pl.C (n + j) (extendD h' j k))
          = if h' = h then U.u c - U.u (pl.C (n + j) (extendD h j k)) else 0 := by
      intro h' k
      simp only [settle, settleC, Nat.le_add_right n j, ↓reduceDIte, preN_extendD]
      by_cases hh : h' = h
      · subst hh; simp
      · simp [hh]
    have e : ∀ h' : Fin (n + 1) → S, ReputationTrigger.History.histProb E.Ω h' *
        ∑ k : Fin j → S, ReputationTrigger.History.histProb E.Ω k *
          (U.u ((settle E pl h c B').C (n + j) (extendD h' j k)) -
            U.u (pl.C (n + j) (extendD h' j k))) =
        if h' = h then ReputationTrigger.History.histProb E.Ω h *
          (U.u c - condE E h j (fun g => U.u (pl.C (n + j) g))) else 0 := by
      intro h'
      simp only [hin]
      by_cases hh : h' = h
      · subst hh
        simp only [↓reduceIte]
        unfold condE
        beta_reduce
        congr 1
        simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul,
          ReputationTrigger.History.histProb_sum, one_mul]
      · simp [hh]
    have e2 : ∀ h' : Fin (n + 1) → S, ReputationTrigger.History.histProb E.Ω h' *
        ∑ k : Fin j → S, ReputationTrigger.History.histProb E.Ω k *
          U.u ((settle E pl h c B').C (n + j) (extendD h' j k)) -
        ReputationTrigger.History.histProb E.Ω h' *
        ∑ k : Fin j → S, ReputationTrigger.History.histProb E.Ω k *
          U.u (pl.C (n + j) (extendD h' j k)) =
        ReputationTrigger.History.histProb E.Ω h' *
        ∑ k : Fin j → S, ReputationTrigger.History.histProb E.Ω k *
          (U.u ((settle E pl h c B').C (n + j) (extendD h' j k)) -
            U.u (pl.C (n + j) (extendD h' j k))) := by
      intro h'; rw [← mul_sub, ← Finset.sum_sub_distrib]
      congr 1; apply Finset.sum_congr rfl; intro k _; ring
    rw [← Finset.sum_sub_distrib]
    simp only [e2, e, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
    rw [pow_add]; ring
  rw [hdiff, ← hfs.sum_add_tsum_nat_add n, Finset.sum_eq_zero (fun m hm =>
    hlow m (Finset.mem_range.mp hm)), zero_add]
  simp only [hshift]
  have hsU := cond_utility_summable E U hβ0 hpl h
  have hgeo := Geometric.hasSum_geometric_const hβ0.le hβ1 (U.u c)
  rw [tsum_mul_left]
  congr 1
  rw [show (fun j => β ^ j * (U.u c - condE E h j (fun g => U.u (pl.C (n + j) g)))) =
    fun j => β ^ j * U.u c - β ^ j * condE E h j (fun g => U.u (pl.C (n + j) g)) from
    funext fun j => by ring, hgeo.summable.tsum_sub hsU, hgeo.tsum_eq]

/-- **An optimal plan settles at every node whose cash covers full insurance**, O&R p. 373:
if `ε ≤ x − Ȳ` for every state (e.g. after a top shock), consumption at every node of the
subtree equals `c∞ = (1 − β)x + βȲ`. -/
theorem optimal_settles {β r B₀ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hβ : β * (1 + r) = 1)
    {pl : Plan S} (hopt : Optimal E U β r B₀ pl) {n : ℕ} (h : Fin (n + 1) → S)
    (hx : ∀ s, E.ε s ≤ cash E r pl h - E.Ybar) :
    ∀ j (k : Fin j → S), pl.C (n + j) (extendD h j k) =
      (1 - β) * cash E r pl h + β * E.Ybar := by
  classical
  obtain ⟨hpl, hmax⟩ := hopt
  have hpl' := settle_admissible E U hβ0 hβ1 hβ hpl h hx
  have hgain := settle_gain E U hβ0 hβ1 hpl h hpl'
  have hle := hmax _ hpl'
  have hp : 0 < ReputationTrigger.History.histProb E.Ω h :=
    Finset.prod_pos fun i _ => E.prob_pos (h i)
  have hpos : 0 < β ^ n * ReputationTrigger.History.histProb E.Ω h := mul_pos (pow_pos hβ0 n) hp
  obtain ⟨_, hstrict⟩ := cond_first_best E U hβ0 hβ1 hβ hpl h
  intro j k
  by_contra hne
  have hlt := hstrict ⟨j, k, hne⟩
  have : 0 < β ^ n * ReputationTrigger.History.histProb E.Ω h *
      (U.u ((1 - β) * cash E r pl h + β * E.Ybar) / (1 - β) -
        ∑' j, β ^ j * condE E h j (fun g => U.u (pl.C (n + j) g))) :=
    mul_pos hpos (by linarith)
  linarith

/-- **Worrall's steady state is reached at the first top shock**, O&R p. 373: along an optimal
plan, at every node whose current shock is the largest, `ε̄`, consumption at that node and at
every later node of its subtree equals `c∞ = (1 − β)x + βȲ ≥ Ȳ + rB̄ = Ȳ + (1 − β)ε̄`. -/
theorem optimal_after_top_shock {β r B₀ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hβ : β * (1 + r) = 1) {pl : Plan S} (hopt : Optimal E U β r B₀ pl) {smax : S}
    (hsmax : ∀ s, E.ε s ≤ E.ε smax) {n : ℕ} (h : Fin (n + 1) → S)
    (htop : h (Fin.last n) = smax) :
    (∀ j (k : Fin j → S), pl.C (n + j) (extendD h j k) =
      (1 - β) * cash E r pl h + β * E.Ybar) ∧
      E.Ybar + (1 - β) * E.ε smax ≤ (1 - β) * cash E r pl h + β * E.Ybar := by
  have hcash := output_le_cash E U hopt.1 h
  rw [htop] at hcash
  unfold Endowment.Y at hcash
  refine ⟨optimal_settles E U hβ0 hβ1 hβ hopt h fun s => by linarith [hsmax s], ?_⟩
  nlinarith

/-- **Convergence in probability to the steady state**, O&R p. 373: along an optimal plan the
probability that date-`n` consumption is still below the steady-state level
`C̄ = Ȳ + rB̄ = Ȳ + (1 − β)ε̄` is at most `(1 − π(ε̄))^{n+1}` (no top shock yet), hence tends to
zero. -/
theorem prob_below_steady_state {β r B₀ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hβ : β * (1 + r) = 1) {pl : Plan S} (hopt : Optimal E U β r B₀ pl) {smax : S}
    (hsmax : ∀ s, E.ε s ≤ E.ε smax) (n : ℕ) :
    ReputationTrigger.History.hexp E.Ω (n + 1)
        (fun g => if pl.C n g < E.Ybar + (1 - β) * E.ε smax then 1 else 0) ≤
      (1 - E.Ω.prob smax) ^ (n + 1) := by
  classical
  set f : S → ℝ := fun s => if s = smax then 0 else 1 with hfdef
  have hkey : ∀ m (g : Fin (m + 1) → S) (i : ℕ) (hi : i ≤ m), g ⟨i, by omega⟩ = smax →
      E.Ybar + (1 - β) * E.ε smax ≤ pl.C m g := by
    intro m g i hi hgi
    obtain ⟨j, rfl⟩ : ∃ j, m = i + j := ⟨m - i, by omega⟩
    have htop : preN (Nat.le_add_right i j) g (Fin.last i) = smax := hgi
    obtain ⟨hset, hge⟩ := optimal_after_top_shock E U hβ0 hβ1 hβ hopt hsmax _ htop
    have := hset j (dropN g)
    rw [extendD_pre_drop j g] at this
    rw [this]; exact hge
  have hpt : ∀ g : Fin (n + 1) → S,
      (if pl.C n g < E.Ybar + (1 - β) * E.ε smax then (1 : ℝ) else 0) ≤ ∏ i, f (g i) := by
    intro g
    by_cases hex : ∃ i : Fin (n + 1), g i = smax
    · obtain ⟨i, hi⟩ := hex
      have hprod : ∏ i, f (g i) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hfdef, hi])
      rw [hprod]
      have hge := hkey n g i (Nat.lt_succ_iff.mp i.2) hi
      simp only [not_lt.mpr hge, ↓reduceIte, le_refl]
    · push Not at hex
      have hprod : ∏ i, f (g i) = 1 :=
        Finset.prod_eq_one fun i _ => by simp [hfdef, hex i]
      rw [hprod]
      split_ifs <;> norm_num
  have hmono := ReputationTrigger.History.hexp_mono E.Ω (n + 1) hpt
  refine le_trans hmono (le_of_eq ?_)
  unfold ReputationTrigger.History.hexp ReputationTrigger.History.histProb
  have e : ∀ g : Fin (n + 1) → S, (∏ i, E.Ω.prob (g i)) * ∏ i, f (g i) =
      ∏ i, (E.Ω.prob (g i) * f (g i)) := fun g => (Finset.prod_mul_distrib).symm
  simp only [e]
  rw [show (∑ x : Fin (n + 1) → S, ∏ i, E.Ω.prob (x i) * f (x i)) =
    (∑ s, E.Ω.prob s * f s) ^ (n + 1) from (Fintype.sum_pow (fun s => E.Ω.prob s * f s)
      (n + 1)).symm]
  congr 1
  have h0 : f smax = 0 := by simp [hfdef]
  have h1 : ∀ s ∈ Finset.univ.erase smax, E.Ω.prob s * f s = E.Ω.prob s := fun s hs => by
    have : f s = 1 := by simp [hfdef, Finset.ne_of_mem_erase hs]
    rw [this, mul_one]
  rw [← E.Ω.prob_sum, ← Finset.sum_erase_add _ _ (Finset.mem_univ smax),
    ← Finset.sum_erase_add Finset.univ E.Ω.prob (Finset.mem_univ smax), h0, mul_zero, add_zero,
    add_sub_cancel_right, Finset.sum_congr rfl h1]

/-- The probability of not yet having reached the steady state tends to zero (O&R p. 373,
"consumption thus occupies the steady state `C̄ = Ȳ + rB̄` thereafter"). -/
theorem prob_below_steady_state_tendsto {β r B₀ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hβ : β * (1 + r) = 1) {pl : Plan S} (hopt : Optimal E U β r B₀ pl) {smax : S}
    (hsmax : ∀ s, E.ε s ≤ E.ε smax) :
    Tendsto (fun n => ReputationTrigger.History.hexp E.Ω (n + 1)
      (fun g => if pl.C n g < E.Ybar + (1 - β) * E.ε smax then 1 else 0)) atTop (𝓝 0) := by
  have hp := E.prob_pos smax
  have hp1 : E.Ω.prob smax ≤ 1 := by
    have := Finset.single_le_sum (f := E.Ω.prob) (fun s _ => E.Ω.prob_nonneg s)
      (Finset.mem_univ smax)
    rw [E.Ω.prob_sum] at this; exact this
  have hlim : Tendsto (fun n : ℕ => (1 - E.Ω.prob smax) ^ (n + 1)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) (by linarith)).comp
      (tendsto_add_atTop_nat 1)
  refine squeeze_zero (fun n => ?_) (fun n => prob_below_steady_state E U hβ0 hβ1 hβ hopt hsmax n)
    hlim
  exact Finset.sum_nonneg fun g _ => mul_nonneg
    (ReputationTrigger.History.histProb_nonneg E.Ω g) (by dsimp only; split_ifs <;> norm_num)

/-- **An optimal plan that settles with constant assets `B′ ≥ B̄`**, O&R p. 373: if `pl` is
optimal, so is the plan that switches to the steady state (assets `β(x − Ȳ) ≥ B̄`, consumption
`c∞`, full insurance) at a top-shock node; when the collateral constraint binds there,
`x = Ȳ + ε̄`, these assets are exactly `B̄ = ε̄/(1 + r)` and consumption `Ȳ + rB̄`. -/
theorem settle_optimal [DecidableEq S] {β r B₀ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hβ : β * (1 + r) = 1) {pl : Plan S} (hopt : Optimal E U β r B₀ pl) {smax : S}
    (hsmax : ∀ s, E.ε s ≤ E.ε smax) {n : ℕ} (h : Fin (n + 1) → S)
    (htop : h (Fin.last n) = smax) :
    Optimal E U β r B₀ (settle E pl h ((1 - β) * cash E r pl h + β * E.Ybar)
        (β * (cash E r pl h - E.Ybar))) ∧
      E.ε smax / (1 + r) ≤ β * (cash E r pl h - E.Ybar) ∧
      (cash E r pl h = E.Ybar + E.ε smax →
        β * (cash E r pl h - E.Ybar) = E.ε smax / (1 + r) ∧
        (1 - β) * cash E r pl h + β * E.Ybar = E.Ybar + r * (E.ε smax / (1 + r))) := by
  have hcash := output_le_cash E U hopt.1 h
  rw [htop] at hcash
  unfold Endowment.Y at hcash
  have hx : ∀ s, E.ε s ≤ cash E r pl h - E.Ybar := fun s => by linarith [hsmax s]
  have hpl' := settle_admissible E U hβ0 hβ1 hβ hopt.1 h hx
  have hgain := settle_gain E U hβ0 hβ1 hopt.1 h hpl'
  obtain ⟨hfb, _⟩ := cond_first_best E U hβ0 hβ1 hβ hopt.1 h
  have hp : 0 < ReputationTrigger.History.histProb E.Ω h :=
    Finset.prod_pos fun i _ => E.prob_pos (h i)
  have hge : lifetime E U β pl ≤ lifetime E U β (settle E pl h
      ((1 - β) * cash E r pl h + β * E.Ybar) (β * (cash E r pl h - E.Ybar))) := by
    have := mul_nonneg (mul_pos (pow_pos hβ0 n) hp).le (by linarith : (0 : ℝ) ≤
      U.u ((1 - β) * cash E r pl h + β * E.Ybar) / (1 - β) -
        ∑' j, β ^ j * condE E h j (fun g => U.u (pl.C (n + j) g)))
    linarith
  have h1r : 0 < 1 + r := by nlinarith
  have hβr : β = 1 / (1 + r) := by field_simp; linarith
  refine ⟨⟨hpl', fun pl'' h'' => le_trans (hopt.2 pl'' h'') hge⟩, ?_, fun heq => ?_⟩
  · rw [div_le_iff₀ h1r, hβr]; field_simp; linarith
  · rw [heq, hβr]
    constructor
    · field_simp; ring
    · field_simp; ring

/-- **Expected consumption shortfall vanishes geometrically**, O&R p. 373: along an optimal
plan `E max(C̄ − C_n, 0) ≤ C̄ (1 − π(ε̄))^{n+1}`, `C̄ = Ȳ + (1 − β)ε̄`. -/
theorem shortfall_le {β r B₀ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hβ : β * (1 + r) = 1) {pl : Plan S} (hopt : Optimal E U β r B₀ pl) {smax : S}
    (hsmax : ∀ s, E.ε s ≤ E.ε smax) (n : ℕ) :
    ReputationTrigger.History.hexp E.Ω (n + 1)
        (fun g => max (E.Ybar + (1 - β) * E.ε smax - pl.C n g) 0) ≤
      (E.Ybar + (1 - β) * E.ε smax) * (1 - E.Ω.prob smax) ^ (n + 1) := by
  set Cb := E.Ybar + (1 - β) * E.ε smax with hCb
  have hε : 0 ≤ E.ε smax := by
    have := expect_mono E.Ω (X := E.ε) (Y := fun _ => E.ε smax) hsmax
    rw [E.Ω.expect_const, E.mean_zero] at this; exact this
  have hCb0 : 0 ≤ Cb := by
    have := E.Ybar_pos; simp only [hCb]; nlinarith
  have hpt : ∀ g : Fin (n + 1) → S, max (Cb - pl.C n g) 0 ≤
      Cb * (if pl.C n g < Cb then 1 else 0) + 0 * (fun _ => (0 : ℝ)) g := by
    intro g
    have hC := hopt.1.2.2.2.2.2.1 n g
    by_cases hlt : pl.C n g < Cb
    · simp only [hlt, ↓reduceIte, mul_one, zero_mul, add_zero]
      exact max_le (by linarith) hCb0
    · simp only [hlt, ↓reduceIte, mul_zero, add_zero]
      exact le_of_eq (max_eq_right (by linarith))
  have h1 := ReputationTrigger.History.hexp_mono E.Ω (n + 1) hpt
  rw [ReputationTrigger.History.hexp_linear] at h1
  have h2 := prob_below_steady_state E U hβ0 hβ1 hβ hopt hsmax n
  nlinarith

/-- The expected shortfall from the steady state tends to zero (O&R p. 373). -/
theorem shortfall_tendsto {β r B₀ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hβ : β * (1 + r) = 1) {pl : Plan S} (hopt : Optimal E U β r B₀ pl) {smax : S}
    (hsmax : ∀ s, E.ε s ≤ E.ε smax) :
    Tendsto (fun n => ReputationTrigger.History.hexp E.Ω (n + 1)
      (fun g => max (E.Ybar + (1 - β) * E.ε smax - pl.C n g) 0)) atTop (𝓝 0) := by
  have hp := E.prob_pos smax
  have hp1 : E.Ω.prob smax ≤ 1 := by
    have := Finset.single_le_sum (f := E.Ω.prob) (fun s _ => E.Ω.prob_nonneg s)
      (Finset.mem_univ smax)
    rw [E.Ω.prob_sum] at this; exact this
  have hlim0 : Tendsto (fun n : ℕ => (1 - E.Ω.prob smax) ^ (n + 1)) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by linarith) (by linarith)).comp
      (tendsto_add_atTop_nat 1)
  have hlim : Tendsto (fun n : ℕ => (E.Ybar + (1 - β) * E.ε smax) *
      (1 - E.Ω.prob smax) ^ (n + 1)) atTop (𝓝 0) := by
    have := hlim0.const_mul (E.Ybar + (1 - β) * E.ε smax)
    rw [mul_zero] at this; exact this
  refine squeeze_zero (fun n => ?_) (fun n => shortfall_le E U hβ0 hβ1 hβ hopt hsmax n) hlim
  exact Finset.sum_nonneg fun g _ => mul_nonneg
    (ReputationTrigger.History.histProb_nonneg E.Ω g) (le_max_right _ _)

/-- The stationary full-insurance plan with assets `B₀` (O&R p. 373): consume `Ȳ + rB₀`, pay
`ε` every period, keep assets at `B₀`. -/
def steady (r B₀ : ℝ) : Plan S :=
  ⟨fun _ _ => E.Ybar + r * B₀, fun n h => E.ε (h (Fin.last n)), fun _ _ => B₀⟩

/-- Sums over one-shock histories are expectations over the shock (O&R (11)). -/
theorem sum_one (F : (Fin 1 → S) → ℝ) :
    ∑ h, ReputationTrigger.History.histProb E.Ω h * F h =
      ∑ s, E.Ω.prob s * F (Fin.snoc (Fin.elim0 : Fin 0 → S) s : Fin 1 → S) := by
  rw [ReputationTrigger.History.sum_snoc, Fintype.sum_unique]
  have hd : (default : Fin 0 → S) = Fin.elim0 := Subsingleton.elim _ _
  rw [hd]
  apply Finset.sum_congr rfl
  intro s _
  rw [ReputationTrigger.History.histProb_snoc]
  simp [ReputationTrigger.History.histProb]

/-- **Existence of an optimal plan when `B₀ ≥ B̄`, and uniqueness of its consumption**,
O&R p. 373: if the initial collateral covers every full-insurance payment,
`ε ≤ (1 + r)B₀`, the stationary plan is optimal with lifetime utility
`u(Ȳ + rB₀)/(1 − β)`, and every optimal plan consumes `Ȳ + rB₀` at every node. For
`B₀ < B̄` existence is not proved here: without an Inada condition the constraint `C > 0` can
bind, and with one the plan space still needs a truncation, since admissible wealth can grow at
rate `(1 + r)/min π > 1/β` and lifetime utility is then not upper semicontinuous on it. -/
theorem steady_optimal {β r B₀ : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hβ : β * (1 + r) = 1)
    (hB : ∀ s, E.ε s ≤ (1 + r) * B₀) :
    Optimal E U β r B₀ (steady E r B₀) ∧
      lifetime E U β (steady E r B₀) = U.u (E.Ybar + r * B₀) / (1 - β) ∧
      ∀ pl, Optimal E U β r B₀ pl → ∀ n h, pl.C n h = E.Ybar + r * B₀ := by
  classical
  set c := E.Ybar + r * B₀ with hc
  have hY := E.Ybar_pos
  have h1r : 0 < 1 + r := by nlinarith
  have hr : 0 < r := by nlinarith
  have hB0 : 0 ≤ B₀ := by
    have := StateSpaceFacts.nonempty E.Ω
    obtain ⟨sm, _, hsm⟩ := Finset.exists_max_image Finset.univ E.ε Finset.univ_nonempty
    have hmean := expect_mono E.Ω (X := E.ε) (Y := fun _ => E.ε sm)
      fun s => hsm s (Finset.mem_univ s)
    rw [E.Ω.expect_const, E.mean_zero] at hmean
    have := hB sm
    nlinarith
  have hcpos : 0 < c := by simp only [hc]; nlinarith
  have hgeo := Geometric.hasSum_geometric_const hβ0.le hβ1 (U.u c)
  -- admissibility and value of the stationary plan
  have hadm : Admissible E U β r B₀ (steady E r B₀) := by
    refine ⟨rfl, fun n h => ?_, fun n h => hB _, fun n g => ?_, fun _ _ => hB0,
      fun _ _ => hcpos, ?_⟩
    · simp only [steady]; unfold Endowment.Y; ring
    · simp only [steady, Fin.snoc_last]; exact E.mean_zero
    · have e : ∀ n, β ^ n * ReputationTrigger.History.hexp E.Ω (n + 1)
          (fun h => |U.u ((steady E r B₀).C n h)|) = β ^ n * |U.u c| := fun n => by
        simp only [steady]; rw [ReputationTrigger.History.hexp_const]
      simp only [e]
      exact (summable_geometric_of_lt_one hβ0.le hβ1).mul_right _
  have hval : lifetime E U β (steady E r B₀) = U.u c / (1 - β) := by
    unfold lifetime
    have e : ∀ n, β ^ n * ReputationTrigger.History.hexp E.Ω (n + 1)
        (fun h => U.u ((steady E r B₀).C n h)) = β ^ n * U.u c := fun n => by
      simp only [steady]; rw [ReputationTrigger.History.hexp_const]
    simp only [e]; exact hgeo.tsum_eq
  -- every admissible plan does no better, strictly worse if it ever deviates from `c`
  have hbound : ∀ pl, Admissible E U β r B₀ pl →
      lifetime E U β pl ≤ U.u c / (1 - β) ∧
      ((∃ (h0 : Fin 1 → S) (j : ℕ) (k : Fin j → S), pl.C (0 + j) (extendD h0 j k) ≠ c) →
        lifetime E U β pl < U.u c / (1 - β)) := by
    intro pl hpl
    set T : (Fin 1 → S) → ℝ := fun h0 =>
      ∑' j, β ^ j * condE E h0 j (fun g => U.u (pl.C (0 + j) g)) with hT
    set x : (Fin 1 → S) → ℝ := fun h0 => (1 - β) * cash E r pl h0 + β * E.Ybar with hx
    have hdec : ∀ j, β ^ j * ReputationTrigger.History.hexp E.Ω (j + 1)
        (fun g => U.u (pl.C j g)) = ∑ h0, ReputationTrigger.History.histProb E.Ω h0 *
          (β ^ j * condE E h0 j (fun g => U.u (pl.C (0 + j) g))) := by
      intro j
      have key : ∀ m, m = 0 + j → ReputationTrigger.History.hexp E.Ω (m + 1)
          (fun g => U.u (pl.C m g)) = ∑ h0, ReputationTrigger.History.histProb E.Ω h0 *
            condE E h0 j (fun g => U.u (pl.C (0 + j) g)) := by
        intro m hm
        subst hm
        unfold ReputationTrigger.History.hexp condE
        exact sum_extendD E j _
      rw [key j (Nat.zero_add j).symm, Finset.mul_sum]
      apply Finset.sum_congr rfl; intro h0 _; ring
    have hsum : HasSum (fun j => ∑ h0, ReputationTrigger.History.histProb E.Ω h0 *
        (β ^ j * condE E h0 j (fun g => U.u (pl.C (0 + j) g))))
        (∑ h0, ReputationTrigger.History.histProb E.Ω h0 * T h0) :=
      hasSum_sum fun h0 _ => ((cond_utility_summable E U hβ0 hpl h0).hasSum).mul_left _
    have hlife : lifetime E U β pl = ∑ h0, ReputationTrigger.History.histProb E.Ω h0 * T h0 := by
      unfold lifetime; rw [tsum_congr hdec]; exact hsum.tsum_eq
    have hxpos : ∀ h0, 0 < x h0 := fun h0 => by
      have := output_le_cash E U hpl h0
      have := E.Y_pos (h0 (Fin.last 0))
      simp only [hx]; nlinarith
    have hmean : ∑ h0, ReputationTrigger.History.histProb E.Ω h0 * x h0 = c := by
      rw [sum_one E]
      have hzp := hpl.2.2.2.1 0 Fin.elim0
      have e : ∀ s, E.Ω.prob s * x (Fin.snoc (Fin.elim0 : Fin 0 → S) s : Fin 1 → S) =
          (1 - β) * (1 + r) * B₀ * E.Ω.prob s + (1 - β) * E.Ybar * E.Ω.prob s +
          (1 - β) * (E.Ω.prob s * E.ε s) - (1 - β) * (E.Ω.prob s *
            pl.P 0 (Fin.snoc (Fin.elim0 : Fin 0 → S) s : Fin 1 → S)) +
          β * E.Ybar * E.Ω.prob s := by
        intro s
        simp only [hx, cash, Fin.init_snoc, Fin.snoc_last]
        rw [show (Fin.elim0 : Fin 0 → S) = Fin.elim0 from rfl, hpl.1]
        unfold Endowment.Y; ring
      simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
        E.Ω.prob_sum, hzp]
      have hm := E.mean_zero
      unfold StateSpace.expect at hm
      rw [hm, hc]
      have : r = (1 - β) * (1 + r) := by linarith
      nlinarith
    have hterm : ∀ h0, T h0 ≤ (U.u c + U.du c * (x h0 - c)) / (1 - β) := fun h0 => by
      have := (cond_first_best E U hβ0 hβ1 hβ hpl h0).1
      have hs := U.supporting_line (hxpos h0) hcpos
      have : U.u (x h0) / (1 - β) ≤ (U.u c + U.du c * (x h0 - c)) / (1 - β) :=
        div_le_div_of_nonneg_right hs (by linarith)
      simp only [hT, hx] at *; linarith
    have htot : ∑ h0, ReputationTrigger.History.histProb E.Ω h0 *
        ((U.u c + U.du c * (x h0 - c)) / (1 - β)) = U.u c / (1 - β) := by
      have e : ∀ h0, ReputationTrigger.History.histProb E.Ω h0 *
          ((U.u c + U.du c * (x h0 - c)) / (1 - β)) =
          ((U.u c - U.du c * c) / (1 - β)) * ReputationTrigger.History.histProb E.Ω h0 +
          (U.du c / (1 - β)) * (ReputationTrigger.History.histProb E.Ω h0 * x h0) :=
        fun h0 => by field_simp; ring
      simp only [e, Finset.sum_add_distrib, ← Finset.mul_sum,
        ReputationTrigger.History.histProb_sum, hmean]
      field_simp; ring
    have hp : ∀ h0 : Fin 1 → S, 0 < ReputationTrigger.History.histProb E.Ω h0 :=
      fun h0 => Finset.prod_pos fun i _ => E.prob_pos (h0 i)
    refine ⟨?_, fun ⟨h0, j, k, hne⟩ => ?_⟩
    · rw [hlife, ← htot]
      exact Finset.sum_le_sum fun h0 _ => mul_le_mul_of_nonneg_left (hterm h0) (hp h0).le
    · rw [hlife, ← htot]
      refine Finset.sum_lt_sum (fun h0 _ => mul_le_mul_of_nonneg_left (hterm h0) (hp h0).le)
        ⟨h0, Finset.mem_univ _, mul_lt_mul_of_pos_left ?_ (hp h0)⟩
      by_cases hxc : x h0 = c
      · have hstr := (cond_first_best E U hβ0 hβ1 hβ hpl h0).2 ⟨j, k, by
          have : (1 - β) * cash E r pl h0 + β * E.Ybar = c := hxc
          rw [this]; exact hne⟩
        have : (U.u c + U.du c * (x h0 - c)) / (1 - β) = U.u (x h0) / (1 - β) := by
          rw [hxc]; ring
        rw [this]; exact hstr
      · have hs := U.supporting_line_strict (hxpos h0) hcpos hxc
        have : U.u (x h0) / (1 - β) < (U.u c + U.du c * (x h0 - c)) / (1 - β) :=
          div_lt_div_of_pos_right hs (by linarith)
        exact lt_of_le_of_lt (cond_first_best E U hβ0 hβ1 hβ hpl h0).1 this
  refine ⟨⟨hadm, fun pl hpl => hval ▸ (hbound pl hpl).1⟩, hval, fun pl hopt n g => ?_⟩
  by_contra hne
  have key : ∀ m (g : Fin (m + 1) → S), m = 0 + n → pl.C m g ≠ c →
      ∃ (h0 : Fin 1 → S) (j : ℕ) (k : Fin j → S), pl.C (0 + j) (extendD h0 j k) ≠ c := by
    intro m g hm hne'
    subst hm
    exact ⟨preN (Nat.le_add_right 0 n) g, n, dropN g, by rw [extendD_pre_drop]; exact hne'⟩
  have hlt := (hbound pl hopt.1).2 (key n g (Nat.zero_add n).symm hne)
  have hge := hopt.2 _ hadm
  rw [hval] at hge
  linarith

end Worrall

end ObstfeldRogoff.CapitalMarketImperfections.BulowRogoff
