/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Tactic.FieldSimp

/-!
# Nominal asset pricing in a stochastic global monetary equilibrium

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §8.7.1–8.7.4,
pp. 579–585.

Uncertainty is a finite-state Markov chain. Histories (nodes of the event tree) are pairs
`(current state, list of past states)`; the conditional expectation `E_t` is the one-step
operator `oneStep`, and `E_t X_{t+n}` is its `n`-fold iterate `iterStep`.

* Finite probability spaces: expectation, covariance, variance (`FinProb`).
* Euler equations for any asset (93), nominal bonds (95), real bonds (96) and money (98):
  each is NECESSARY (a one-period reallocation cannot raise utility at an optimum) and
  SUFFICIENT (with concave utility, no such reallocation raises utility).
* (97): the certainty-equivalence Fisher equation holds IF AND ONLY IF inflation and
  marginal utility are conditionally uncorrelated (the book says "only if").
* `v′/u′ = i/(1+i)` from (95) and (98).
* (94): proportional CRRA marginal utilities imply constant consumption shares of world
  output.
* (99): with CRRA/log utility, the money Euler equation is EXACTLY LINEAR in the
  output-adjusted real balances `w = M/(P (xY)^ρ)`: `w_t = 1 + γ E_t[w_{t+1}/ε_{t+1}]`,
  `γ = β/(1+μ)`.
* (100)–(101): with `E_t[1/ε] = 1` and `ε > 0` (the book says "nonnegative", which is not
  enough) the constant `ω = (1+μ)/(1+μ−β)` is the unique bounded solution along the whole
  event tree; every positive solution is `ω` plus a NONNEGATIVE bubble; bubbles exist; no
  positive solution exists at all when `1+μ ≤ β`; the transversality condition rules
  bubbles out when `(1+μ) min ε ≥ 1` (so `μ ≥ 0` in the deterministic case) but NOT when
  `μ < 0`. Consequences: the price-level formula, `1+i = (1+μ)/β`, and independence of the
  price level from expected future output.
* The log-linearised model of §8.7.3 is a stochastic Cagan equation; its fundamental
  solution exists (given summability) and is the unique no-bubble solution.
* §8.7.4: the stochastic cash-in-advance model (103).
* The infinite-horizon household problem on the event tree (`Household`): budget constraints
  with an arbitrary finite asset menu (money, nominal and real bonds, output claims); the Euler
  equations plus the stochastic transversality condition are SUFFICIENT for optimality against
  every feasible, positive, no-Ponzi rival (supporting hyperplane summed over the tree), and
  the Euler equations are NECESSARY at every node reached with positive probability.
* `Equilibrium87`: the §8.7 equilibrium plan (`C = xY^W`, money path with `M/P = ω(xY^W)^ρ`,
  no bonds, fund share `x`) satisfies every Euler equation and the transversality condition
  (derived, not assumed), hence is optimal for each household.
-/

namespace ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing

open Finset Filter Topology

/-! ## Finite probability spaces -/

/-- A probability distribution on a finite set of states (O&R §8.7, p. 579: the book's
random outputs and money supplies take finitely many values here). -/
structure FinProb (S : Type) [Fintype S] where
  prob : S → ℝ
  prob_nonneg : ∀ s, 0 ≤ prob s
  prob_sum : ∑ s, prob s = 1

namespace FinProb

variable {S : Type} [Fintype S] (Ω : FinProb S)

/-- Expectation `E[X] = Σ π(s) X(s)` (O&R §8.7, p. 579). -/
def expect (X : S → ℝ) : ℝ := ∑ s, Ω.prob s * X s

/-- Covariance `Cov(X, Y) = E[XY] − E[X]E[Y]` (O&R §8.7.2, p. 581). -/
def cov (X Y : S → ℝ) : ℝ := Ω.expect (fun s => X s * Y s) - Ω.expect X * Ω.expect Y

/-- Variance `Var(X) = Cov(X, X)` (O&R §8.7.5, p. 587). -/
def var (X : S → ℝ) : ℝ := Ω.cov X X

/-- The expectation of a constant is the constant (O&R §8.7). -/
theorem expect_const (c : ℝ) : Ω.expect (fun _ => c) = c := by
  simp [expect, ← Finset.sum_mul, Ω.prob_sum]

/-- Expectation is additive (O&R §8.7). -/
theorem expect_add (X Y : S → ℝ) :
    Ω.expect (fun s => X s + Y s) = Ω.expect X + Ω.expect Y := by
  simp [expect, mul_add, Finset.sum_add_distrib]

/-- Expectation respects subtraction (O&R §8.7). -/
theorem expect_sub (X Y : S → ℝ) :
    Ω.expect (fun s => X s - Y s) = Ω.expect X - Ω.expect Y := by
  simp [expect, mul_sub, Finset.sum_sub_distrib]

/-- Known (date-`t`) factors come out of the expectation (O&R (117), p. 591). -/
theorem expect_mul_left (c : ℝ) (X : S → ℝ) :
    Ω.expect (fun s => c * X s) = c * Ω.expect X := by
  simp only [expect, Finset.mul_sum]
  exact Finset.sum_congr rfl fun s _ => by ring

/-- Expectation is monotone (O&R §8.7). -/
theorem expect_mono {X Y : S → ℝ} (h : ∀ s, X s ≤ Y s) : Ω.expect X ≤ Ω.expect Y :=
  Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (h s) (Ω.prob_nonneg s)

/-- Some state has positive probability (O&R §8.7). -/
theorem exists_prob_pos : ∃ s, 0 < Ω.prob s := by
  by_contra hc
  push Not at hc
  have : ∑ s, Ω.prob s ≤ 0 := Finset.sum_nonpos fun s _ => hc s
  linarith [Ω.prob_sum]

/-- A strictly positive random variable has strictly positive expectation (O&R §8.7.2,
p. 581: `E_t u′(C_{t+1}) > 0`). -/
theorem expect_pos {X : S → ℝ} (h : ∀ s, 0 < X s) : 0 < Ω.expect X := by
  obtain ⟨s, hs⟩ := Ω.exists_prob_pos
  have hle : Ω.prob s * X s ≤ ∑ t, Ω.prob t * X t :=
    Finset.single_le_sum (f := fun t => Ω.prob t * X t)
      (fun t _ => mul_nonneg (Ω.prob_nonneg t) (h t).le) (Finset.mem_univ s)
  unfold expect
  nlinarith [mul_pos hs (h s)]

/-- The covariance decomposition `E[XY] = E[X]E[Y] + Cov(X, Y)` (O&R §8.7.2, p. 581). -/
theorem expect_mul_eq (X Y : S → ℝ) :
    Ω.expect (fun s => X s * Y s) = Ω.expect X * Ω.expect Y + Ω.cov X Y := by
  unfold cov; ring

/-- The variance as the mean squared deviation (O&R §8.7.5, p. 590). -/
theorem var_eq_expect_sq (X : S → ℝ) :
    Ω.var X = Ω.expect (fun s => (X s - Ω.expect X) ^ 2) := by
  rw [show (fun s => (X s - Ω.expect X) ^ 2) = fun s => (X s * X s + (-2 * Ω.expect X) * X s)
      + Ω.expect X ^ 2 from funext fun s => by ring, expect_add, expect_add, expect_mul_left,
    expect_const]
  simp only [var, cov]; ring

/-- Variances are nonnegative (O&R §8.7.5, p. 590). -/
theorem var_nonneg (X : S → ℝ) : 0 ≤ Ω.var X := by
  rw [var_eq_expect_sq]
  simpa [expect_const] using Ω.expect_mono (X := fun _ => (0 : ℝ))
    (fun s => sq_nonneg (X s - Ω.expect X))

/-- Covariance is additive in its first argument (O&R §8.7.5, p. 590). -/
theorem cov_add_left (X Y Z : S → ℝ) :
    Ω.cov (fun s => X s + Y s) Z = Ω.cov X Z + Ω.cov Y Z := by
  simp only [cov, add_mul, expect_add]; ring

/-- Covariance is additive in its second argument (O&R §8.7.5, p. 590). -/
theorem cov_add_right (X Y Z : S → ℝ) :
    Ω.cov X (fun s => Y s + Z s) = Ω.cov X Y + Ω.cov X Z := by
  simp only [cov, mul_add, expect_add]; ring

/-- Covariance scales in its first argument (O&R §8.7.5). -/
theorem cov_mul_left (c : ℝ) (X Y : S → ℝ) :
    Ω.cov (fun s => c * X s) Y = c * Ω.cov X Y := by
  simp only [cov, mul_assoc, expect_mul_left]; ring

/-- Covariance scales in its second argument (O&R §8.7.5). -/
theorem cov_mul_right (c : ℝ) (X Y : S → ℝ) :
    Ω.cov X (fun s => c * Y s) = c * Ω.cov X Y := by
  simp only [cov, expect_mul_left]
  rw [show (fun s => X s * (c * Y s)) = fun s => c * (X s * Y s) from
    funext fun s => by ring, expect_mul_left]
  ring

/-- Covariance is symmetric (O&R §8.7.5). -/
theorem cov_comm (X Y : S → ℝ) : Ω.cov X Y = Ω.cov Y X := by
  simp only [cov, mul_comm (X _), mul_comm (Ω.expect X)]

/-- A constant has zero covariance with anything (O&R fn 68, p. 584). -/
theorem cov_const_left (c : ℝ) (Y : S → ℝ) : Ω.cov (fun _ => c) Y = 0 := by
  simp only [cov, expect_mul_left, expect_const]; ring

/-- Adding a constant does not change a covariance (O&R p. 592: `Cov(e, c) = Cov(e, y^W)`
when `c = log x + y^W`). -/
theorem cov_add_const_right (a : ℝ) (X Y : S → ℝ) :
    Ω.cov X (fun s => a + Y s) = Ω.cov X Y := by
  rw [cov_add_right, cov_comm Ω X (fun _ => a), cov_const_left]; ring

/-- The variance of a sum (O&R fn 75, p. 588). -/
theorem var_add (X Y : S → ℝ) :
    Ω.var (fun s => X s + Y s) = Ω.var X + Ω.var Y + 2 * Ω.cov X Y := by
  simp only [var, cov_add_left, cov_add_right, cov_comm Ω Y X]; ring

/-- The variance of a difference (O&R fn 75, p. 588: `Var(e − p) = Var e + Var p −
2Cov(e, p)`). -/
theorem var_sub (X Y : S → ℝ) :
    Ω.var (fun s => X s - Y s) = Ω.var X + Ω.var Y - 2 * Ω.cov X Y := by
  rw [show (fun s => X s - Y s) = fun s => X s + (-1) * Y s from funext fun s => by ring,
    var_add]
  simp only [var, cov_mul_left, cov_mul_right]; ring

/-- Adding a constant does not change a variance (O&R fn 75, p. 588). -/
theorem var_const_add (a : ℝ) (X : S → ℝ) : Ω.var (fun s => a + X s) = Ω.var X := by
  rw [var_add, var, var, cov_const_left, cov_const_left]; ring

end FinProb

/-! ## Markov kernels and the event tree -/

/-- A Markov transition kernel on a finite state space (O&R §8.7, p. 579: outputs and money
growth shocks "may be correlated across time"). -/
structure Kernel (S : Type) [Fintype S] where
  trans : S → S → ℝ
  trans_nonneg : ∀ s s', 0 ≤ trans s s'
  trans_sum : ∀ s, ∑ s', trans s s' = 1

/-- The conditional distribution of next period's state (O&R §8.7). -/
def Kernel.row {S : Type} [Fintype S] (K : Kernel S) (s : S) : FinProb S :=
  ⟨K.trans s, K.trans_nonneg s, K.trans_sum s⟩

/-- A node of the event tree: the current state and the list of past states, most recent
first (O&R §8.7: all variables may depend on the whole history). -/
abbrev Hist (S : Type) : Type := S × List S

variable {S : Type} [Fintype S]

/-- The successor node reached when next period's state is `s'` (O&R §8.7). -/
def next (h : Hist S) (s' : S) : Hist S := (s', h.1 :: h.2)

/-- The parent node (the root is its own parent) (O&R §8.7.5.2). -/
def anc : Hist S → Hist S
  | (s, []) => (s, [])
  | (_, t :: past) => (t, past)

/-- The date of a node, counted from the root (O&R §8.7). -/
def depth (h : Hist S) : ℕ := h.2.length

omit [Fintype S] in
/-- The parent of a successor is the node itself (O&R §8.7). -/
theorem anc_next (h : Hist S) (s' : S) : anc (next h s') = h := rfl

omit [Fintype S] in
/-- A successor is one period later (O&R §8.7). -/
theorem depth_next (h : Hist S) (s' : S) : depth (next h s') = depth h + 1 := by
  simp [depth, next]

/-- The conditional expectation `E_t X_{t+1}` for a (not necessarily stochastic) kernel `k`
(O&R §8.7, p. 580, (93)). -/
def oneStep (k : S → S → ℝ) (X : Hist S → ℝ) (h : Hist S) : ℝ :=
  ∑ s', k h.1 s' * X (next h s')

/-- The `n`-period-ahead conditional expectation `E_t X_{t+n}` (O&R §8.7.3, p. 584). -/
def iterStep (k : S → S → ℝ) (n : ℕ) : (Hist S → ℝ) → Hist S → ℝ := (oneStep k)^[n]

/-- `E_t` is additive (O&R §8.7). -/
theorem oneStep_add (k : S → S → ℝ) (X Y : Hist S → ℝ) (h : Hist S) :
    oneStep k (fun g => X g + Y g) h = oneStep k X h + oneStep k Y h := by
  simp [oneStep, mul_add, Finset.sum_add_distrib]

/-- `E_t` respects subtraction (O&R §8.7). -/
theorem oneStep_sub (k : S → S → ℝ) (X Y : Hist S → ℝ) (h : Hist S) :
    oneStep k (fun g => X g - Y g) h = oneStep k X h - oneStep k Y h := by
  simp [oneStep, mul_sub, Finset.sum_sub_distrib]

/-- Constants come out of `E_t` (O&R §8.7). -/
theorem oneStep_mul_left (k : S → S → ℝ) (c : ℝ) (X : Hist S → ℝ) (h : Hist S) :
    oneStep k (fun g => c * X g) h = c * oneStep k X h := by
  simp only [oneStep, Finset.mul_sum]
  exact Finset.sum_congr rfl fun s _ => by ring

/-- `E_t` of a constant is the constant, for a stochastic kernel (O&R §8.7). -/
theorem oneStep_const {k : S → S → ℝ} (hk : ∀ s, ∑ s', k s s' = 1) (c : ℝ) (h : Hist S) :
    oneStep k (fun _ => c) h = c := by
  simp [oneStep, ← Finset.sum_mul, hk]

/-- `E_t` is monotone for a nonnegative kernel (O&R §8.7). -/
theorem oneStep_mono {k : S → S → ℝ} (hk : ∀ s s', 0 ≤ k s s') {X Y : Hist S → ℝ}
    (hXY : ∀ g, X g ≤ Y g) (h : Hist S) : oneStep k X h ≤ oneStep k Y h :=
  Finset.sum_le_sum fun _ _ => mul_le_mul_of_nonneg_left (hXY _) (hk _ _)

/-- Date-`t` known factors come out of `E_t` (O&R §8.7.5.2: "known at time t"). -/
theorem oneStep_pull (k : S → S → ℝ) (a : Hist S → ℝ) (X : Hist S → ℝ) (h : Hist S) :
    oneStep k (fun g => a (anc g) * X g) h = a h * oneStep k X h := by
  simp only [oneStep, anc_next, Finset.mul_sum]
  exact Finset.sum_congr rfl fun s _ => by ring

/-- One more period of expectation (O&R §8.7.3). -/
theorem iterStep_succ (k : S → S → ℝ) (n : ℕ) (X : Hist S → ℝ) :
    iterStep k (n + 1) X = iterStep k n (oneStep k X) :=
  Function.iterate_succ_apply _ _ _

/-- One more period of expectation, applied last: the tower property
`E_t E_{t+n} = E_t` (O&R §8.7.5.2). -/
theorem iterStep_succ' (k : S → S → ℝ) (n : ℕ) (X : Hist S → ℝ) :
    iterStep k (n + 1) X = oneStep k (iterStep k n X) :=
  Function.iterate_succ_apply' _ _ _

/-- The law of iterated expectations `E_t X_{t+m+n} = E_t E_{t+n} X_{t+m+n}`
(O&R §8.7.5.2). -/
theorem iterStep_add (k : S → S → ℝ) (m n : ℕ) (X : Hist S → ℝ) :
    iterStep k (m + n) X = iterStep k m (iterStep k n X) :=
  Function.iterate_add_apply _ _ _ _

/-- `E_t X_{t+n}` is additive (O&R §8.7). -/
theorem iterStep_add_fun (k : S → S → ℝ) (n : ℕ) (X Y : Hist S → ℝ) (h : Hist S) :
    iterStep k n (fun g => X g + Y g) h = iterStep k n X h + iterStep k n Y h := by
  induction n generalizing X Y with
  | zero => rfl
  | succ n ih =>
    rw [iterStep_succ, iterStep_succ, iterStep_succ,
      show oneStep k (fun g => X g + Y g) = fun g => oneStep k X g + oneStep k Y g from
        funext fun g => oneStep_add k X Y g, ih]

/-- `E_t X_{t+n}` respects subtraction (O&R §8.7). -/
theorem iterStep_sub_fun (k : S → S → ℝ) (n : ℕ) (X Y : Hist S → ℝ) (h : Hist S) :
    iterStep k n (fun g => X g - Y g) h = iterStep k n X h - iterStep k n Y h := by
  induction n generalizing X Y with
  | zero => rfl
  | succ n ih =>
    rw [iterStep_succ, iterStep_succ, iterStep_succ,
      show oneStep k (fun g => X g - Y g) = fun g => oneStep k X g - oneStep k Y g from
        funext fun g => oneStep_sub k X Y g, ih]

/-- Constants come out of `E_t X_{t+n}` (O&R §8.7). -/
theorem iterStep_mul_left (k : S → S → ℝ) (n : ℕ) (c : ℝ) (X : Hist S → ℝ) (h : Hist S) :
    iterStep k n (fun g => c * X g) h = c * iterStep k n X h := by
  induction n generalizing X with
  | zero => rfl
  | succ n ih =>
    rw [iterStep_succ, iterStep_succ,
      show oneStep k (fun g => c * X g) = fun g => c * oneStep k X g from
        funext fun g => oneStep_mul_left k c X g, ih]

/-- `E_t` of a constant `n` periods ahead is the constant (O&R §8.7). -/
theorem iterStep_const {k : S → S → ℝ} (hk : ∀ s, ∑ s', k s s' = 1) (n : ℕ) (c : ℝ)
    (h : Hist S) : iterStep k n (fun _ => c) h = c := by
  induction n generalizing h with
  | zero => rfl
  | succ n ih =>
    rw [iterStep_succ', oneStep, show (fun s' => k h.1 s' * iterStep k n (fun _ => c)
      (next h s')) = fun s' => k h.1 s' * c from funext fun s' => by rw [ih]]
    rw [← Finset.sum_mul, hk, one_mul]

/-- `E_t X_{t+n}` is monotone for a nonnegative kernel (O&R §8.7). -/
theorem iterStep_mono {k : S → S → ℝ} (hk : ∀ s s', 0 ≤ k s s') (n : ℕ) {X Y : Hist S → ℝ}
    (hXY : ∀ g, X g ≤ Y g) (h : Hist S) : iterStep k n X h ≤ iterStep k n Y h := by
  induction n generalizing h with
  | zero => exact hXY h
  | succ n ih =>
    rw [iterStep_succ', iterStep_succ']
    exact oneStep_mono hk (fun g => ih g) h

/-- Date-`t` known factors come out of `E_t X_{t+n}` (O&R §8.7.5.2). -/
theorem iterStep_pull (k : S → S → ℝ) (n : ℕ) (a : Hist S → ℝ) (X : Hist S → ℝ)
    (h : Hist S) :
    iterStep k n (fun g => a (anc^[n] g) * X g) h = a h * iterStep k n X h := by
  induction n generalizing X with
  | zero => rfl
  | succ n ih =>
    rw [iterStep_succ, iterStep_succ]
    have hstep : oneStep k (fun g => a (anc^[n + 1] g) * X g)
        = fun g => a (anc^[n] g) * oneStep k X g := by
      funext g
      simp only [Function.iterate_succ_apply]
      exact oneStep_pull k (fun g => a (anc^[n] g)) X g
    rw [hstep, ih]

/-- A function of the date alone moves forward deterministically (O&R §8.7). -/
theorem iterStep_depth {k : S → S → ℝ} (hk : ∀ s, ∑ s', k s s' = 1) (n : ℕ) (f : ℕ → ℝ)
    (h : Hist S) : iterStep k n (fun g => f (depth g)) h = f (depth h + n) := by
  induction n generalizing f with
  | zero => rfl
  | succ n ih =>
    rw [iterStep_succ]
    have hstep : oneStep k (fun g => f (depth g)) = fun g => f (depth g + 1) := by
      funext g
      simp only [oneStep, depth_next]
      rw [← Finset.sum_mul, hk, one_mul]
    rw [hstep, ih (fun d => f (d + 1))]
    congr 1

/-- Bounds propagate through `E_t X_{t+n}` (O&R §8.7). -/
theorem abs_iterStep_le {k : S → S → ℝ} (hk0 : ∀ s s', 0 ≤ k s s')
    (hk : ∀ s, ∑ s', k s s' = 1) (n : ℕ) {X : Hist S → ℝ} {b : ℝ} (hb : ∀ g, |X g| ≤ b)
    (h : Hist S) : |iterStep k n X h| ≤ b := by
  have h1 := iterStep_mono hk0 n (X := X) (Y := fun _ => b) (fun g => (abs_le.1 (hb g)).2) h
  have h2 := iterStep_mono hk0 n (X := fun _ => -b) (Y := X) (fun g => (abs_le.1 (hb g)).1) h
  rw [iterStep_const hk] at h1 h2
  exact abs_le.2 ⟨h2, h1⟩

/-- `E_t X_{t+n}` of a nonnegative variable is nonnegative (O&R §8.7). -/
theorem iterStep_nonneg {k : S → S → ℝ} (hk : ∀ s s', 0 ≤ k s s') (n : ℕ) {X : Hist S → ℝ}
    (hX : ∀ g, 0 ≤ X g) (h : Hist S) : 0 ≤ iterStep k n X h := by
  induction n generalizing h with
  | zero => exact hX h
  | succ n ih =>
    rw [iterStep_succ']
    exact Finset.sum_nonneg fun s _ => mul_nonneg (hk _ _) (ih _)

/-- Comparison of two kernels on nonnegative variables: if `k₁ ≤ c k₂` entrywise, then
`E¹_t X_{t+n} ≤ cⁿ E²_t X_{t+n}` (used for the transversality argument, O&R (100)). -/
theorem iterStep_le_pow_mul {k₁ k₂ : S → S → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hk₁ : ∀ s s', 0 ≤ k₁ s s') (hk₂ : ∀ s s', 0 ≤ k₂ s s')
    (hle : ∀ s s', k₁ s s' ≤ c * k₂ s s') (n : ℕ) {X : Hist S → ℝ} (hX : ∀ g, 0 ≤ X g)
    (h : Hist S) : iterStep k₁ n X h ≤ c ^ n * iterStep k₂ n X h := by
  have hnn : ∀ m g, 0 ≤ iterStep k₂ m X g := fun m g => iterStep_nonneg hk₂ m hX g
  induction n generalizing h with
  | zero => simp [iterStep]
  | succ n ih =>
    rw [iterStep_succ', iterStep_succ']
    calc oneStep k₁ (iterStep k₁ n X) h
        ≤ oneStep k₁ (fun g => c ^ n * iterStep k₂ n X g) h := oneStep_mono hk₁ ih h
      _ = c ^ n * oneStep k₁ (iterStep k₂ n X) h := oneStep_mul_left _ _ _ _
      _ ≤ c ^ n * (c * oneStep k₂ (iterStep k₂ n X) h) := by
          apply mul_le_mul_of_nonneg_left _ (pow_nonneg hc n)
          simp only [oneStep, Finset.mul_sum]
          exact Finset.sum_le_sum fun s _ => by
            rw [← mul_assoc]
            exact mul_le_mul_of_nonneg_right (hle _ _) (hnn n _)
      _ = c ^ (n + 1) * oneStep k₂ (iterStep k₂ n X) h := by ring

/-! ## Euler equations: necessity and sufficiency -/

/-- The tangent-line inequality for a concave differentiable function on `(0, ∞)`: the
supporting-hyperplane step behind every sufficiency argument (O&R §8.7.1, p. 580). -/
theorem concave_tangent {u u' : ℝ → ℝ} (hc : ConcaveOn ℝ (Set.Ioi 0) u)
    (hd : ∀ x, 0 < x → HasDerivAt u (u' x) x) {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    u y ≤ u x + u' x * (y - x) := by
  rcases lt_trichotomy x y with hxy | rfl | hxy
  · have h := hc.slope_le_of_hasDerivAt hx hy hxy (hd x hx)
    rw [slope_def_field, div_le_iff₀ (sub_pos.2 hxy)] at h
    linarith
  · simp
  · have h := hc.le_slope_of_hasDerivAt hy hx hxy (hd x hx)
    rw [slope_def_field, le_div_iff₀ (sub_pos.2 hxy)] at h
    linarith

/-- Lifetime utility, as a function of `δ`, when the agent gives up `c δ` units of
consumption at `t` to buy `δ` units of an asset with real payoff `R(s)` at `t+1`
(O&R (93), p. 580). Only the terms that change are kept. -/
def assetValue (u : ℝ → ℝ) (Ω : FinProb S) (β C c : ℝ) (C' R : S → ℝ) (δ : ℝ) : ℝ :=
  u (C - c * δ) + β * Ω.expect (fun s => u (C' s + δ * R s))

/-- The marginal value of the asset reallocation (O&R (93), p. 580). -/
theorem hasDerivAt_assetValue {u u' : ℝ → ℝ} (hd : ∀ x, 0 < x → HasDerivAt u (u' x) x)
    (Ω : FinProb S) (β : ℝ) {C : ℝ} (c : ℝ) {C' : S → ℝ} (R : S → ℝ) (hC : 0 < C)
    (hC' : ∀ s, 0 < C' s) :
    HasDerivAt (assetValue u Ω β C c C' R)
      (-(c * u' C) + β * Ω.expect (fun s => u' (C' s) * R s)) 0 := by
  have hg : HasDerivAt (fun δ : ℝ => C - c * δ) (-c) 0 := by
    simpa using HasDerivAt.const_sub C (HasDerivAt.const_mul c (hasDerivAt_id' (0 : ℝ)))
  have h1 : HasDerivAt (fun δ => u (C - c * δ)) (u' C * (-c)) 0 :=
    HasDerivAt.comp_of_eq 0 (hd C hC) hg (by simp)
  have h2 : HasDerivAt (fun δ => Ω.expect (fun s => u (C' s + δ * R s)))
      (Ω.expect fun s => u' (C' s) * R s) 0 := by
    unfold FinProb.expect
    apply HasDerivAt.fun_sum
    intro s _
    have hgs : HasDerivAt (fun δ : ℝ => C' s + δ * R s) (R s) 0 := by
      simpa using HasDerivAt.const_add (C' s) (HasDerivAt.mul_const (hasDerivAt_id' (0 : ℝ))
        (R s))
    have h3 := HasDerivAt.const_mul (Ω.prob s)
      (HasDerivAt.comp_of_eq 0 (hd (C' s) (hC' s)) hgs (by simp))
    exact h3
  have h4 := HasDerivAt.add h1 (HasDerivAt.const_mul β h2)
  unfold assetValue
  convert h4 using 1
  ring

/-- **Necessity of the asset Euler equation** (O&R (93), p. 580): if no small reallocation
into the asset raises utility, then `c u′(C_t) = β E_t[u′(C_{t+1}) R_{t+1}]`. -/
theorem asset_euler_of_isLocalMax {u u' : ℝ → ℝ} (hd : ∀ x, 0 < x → HasDerivAt u (u' x) x)
    {Ω : FinProb S} {β C c : ℝ} {C' R : S → ℝ} (hC : 0 < C) (hC' : ∀ s, 0 < C' s)
    (hmax : IsLocalMax (assetValue u Ω β C c C' R) 0) :
    c * u' C = β * Ω.expect (fun s => u' (C' s) * R s) := by
  have := hmax.hasDerivAt_eq_zero (hasDerivAt_assetValue hd Ω β c R hC hC')
  linarith

/-- **Sufficiency of the asset Euler equation** (O&R (93), p. 580): with concave utility, if
the Euler equation holds then NO feasible reallocation of any size raises utility. -/
theorem assetValue_le_of_euler {u u' : ℝ → ℝ} (hc : ConcaveOn ℝ (Set.Ioi 0) u)
    (hd : ∀ x, 0 < x → HasDerivAt u (u' x) x) {Ω : FinProb S} {β C c : ℝ} {C' R : S → ℝ}
    (hβ : 0 ≤ β) (hC : 0 < C) (hC' : ∀ s, 0 < C' s)
    (heul : c * u' C = β * Ω.expect (fun s => u' (C' s) * R s)) {δ : ℝ}
    (h1 : 0 < C - c * δ) (h2 : ∀ s, 0 < C' s + δ * R s) :
    assetValue u Ω β C c C' R δ ≤ assetValue u Ω β C c C' R 0 := by
  have t1 := concave_tangent hc hd hC h1
  have t2 : Ω.expect (fun s => u (C' s + δ * R s))
      ≤ Ω.expect (fun s => u (C' s) + δ * (u' (C' s) * R s)) :=
    Ω.expect_mono fun s => by
      have := concave_tangent hc hd (hC' s) (h2 s)
      nlinarith [this]
  rw [Ω.expect_add, Ω.expect_mul_left] at t2
  have t3 := mul_le_mul_of_nonneg_left t2 hβ
  have h5 : c * u' C * δ = β * Ω.expect (fun s => u' (C' s) * R s) * δ := by rw [heul]
  simp only [assetValue, mul_zero, sub_zero, zero_mul, add_zero]
  nlinarith [t1, t3, h5]

/-- **The asset Euler equation is necessary and sufficient** for a local optimum of the
one-period reallocation, with concave utility (O&R (93), p. 580). -/
theorem isLocalMax_assetValue_iff {u u' : ℝ → ℝ} (hc : ConcaveOn ℝ (Set.Ioi 0) u)
    (hd : ∀ x, 0 < x → HasDerivAt u (u' x) x) {Ω : FinProb S} {β C c : ℝ} {C' R : S → ℝ}
    (hβ : 0 ≤ β) (hC : 0 < C) (hC' : ∀ s, 0 < C' s) :
    IsLocalMax (assetValue u Ω β C c C' R) 0 ↔
      c * u' C = β * Ω.expect (fun s => u' (C' s) * R s) := by
  refine ⟨asset_euler_of_isLocalMax hd hC hC', fun heul => ?_⟩
  have e1 : ∀ᶠ δ in 𝓝 (0 : ℝ), 0 < C - c * δ := by
    have hcont : Continuous fun δ : ℝ => C - c * δ := by fun_prop
    exact continuousAt_const.eventually_lt hcont.continuousAt (by simpa using hC)
  have e2 : ∀ᶠ δ in 𝓝 (0 : ℝ), ∀ s, 0 < C' s + δ * R s := by
    refine Filter.eventually_all.2 fun s => ?_
    have hcont : Continuous fun δ : ℝ => C' s + δ * R s := by fun_prop
    exact (continuousAt_const.eventually_lt hcont.continuousAt (by simpa using hC' s))
  filter_upwards [e1, e2] with δ h1 h2 using assetValue_le_of_euler hc hd hβ hC hC' heul h1 h2

/-- Lifetime utility, as a function of `δ`, when the agent holds `δ` extra dollars of money
at `t` (giving up `δ/P_t` of consumption, enjoying real balances `(M_t + δ)/P_t`) and spends
them at `t+1` (O&R (98), p. 581). -/
noncomputable def moneyValue (u v : ℝ → ℝ) (Ω : FinProb S) (β C M P : ℝ) (C' P' : S → ℝ)
    (δ : ℝ) : ℝ :=
  u (C - δ / P) + v ((M + δ) / P) + β * Ω.expect (fun s => u (C' s + δ / P' s))

/-- The marginal value of holding an extra dollar (O&R (98), p. 581). -/
theorem hasDerivAt_moneyValue {u u' v v' : ℝ → ℝ} (hdu : ∀ x, 0 < x → HasDerivAt u (u' x) x)
    (hdv : ∀ x, 0 < x → HasDerivAt v (v' x) x) (Ω : FinProb S) (β : ℝ) {C M P : ℝ}
    {C' : S → ℝ} (P' : S → ℝ) (hC : 0 < C) (hM : 0 < M) (hP : 0 < P) (hC' : ∀ s, 0 < C' s) :
    HasDerivAt (moneyValue u v Ω β C M P C' P')
      (-(1 / P * u' C) + 1 / P * v' (M / P) + β * Ω.expect (fun s => 1 / P' s * u' (C' s)))
      0 := by
  have hg1 : HasDerivAt (fun δ : ℝ => C - δ / P) (-(1 / P)) 0 :=
    HasDerivAt.const_sub C (HasDerivAt.div_const (hasDerivAt_id' (0 : ℝ)) P)
  have hg2 : HasDerivAt (fun δ : ℝ => (M + δ) / P) (1 / P) 0 :=
    HasDerivAt.div_const (HasDerivAt.const_add M (hasDerivAt_id' (0 : ℝ))) P
  have h1 : HasDerivAt (fun δ => u (C - δ / P)) (u' C * (-(1 / P))) 0 :=
    HasDerivAt.comp_of_eq 0 (hdu C hC) hg1 (by simp)
  have h2 : HasDerivAt (fun δ => v ((M + δ) / P)) (v' (M / P) * (1 / P)) 0 :=
    HasDerivAt.comp_of_eq 0 (hdv (M / P) (div_pos hM hP)) hg2 (by simp)
  have h3 : HasDerivAt (fun δ => Ω.expect (fun s => u (C' s + δ / P' s)))
      (Ω.expect fun s => 1 / P' s * u' (C' s)) 0 := by
    unfold FinProb.expect
    apply HasDerivAt.fun_sum
    intro s _
    have hgs : HasDerivAt (fun δ : ℝ => C' s + δ / P' s) (1 / P' s) 0 :=
      HasDerivAt.const_add (C' s) (HasDerivAt.div_const (hasDerivAt_id' (0 : ℝ)) (P' s))
    have h4 := HasDerivAt.const_mul (Ω.prob s)
      (HasDerivAt.comp_of_eq 0 (hdu (C' s) (hC' s)) hgs (by simp))
    exact HasDerivAt.congr_deriv h4 (by ring)
  have h5 := HasDerivAt.add (HasDerivAt.add h1 h2) (HasDerivAt.const_mul β h3)
  unfold moneyValue
  convert h5 using 1
  ring

/-- **The money Euler equation (98) is necessary and sufficient** for a local optimum of the
money-holding decision, with concave `u` and `v` (O&R (98), p. 581). -/
theorem isLocalMax_moneyValue_iff {u u' v v' : ℝ → ℝ} (hcu : ConcaveOn ℝ (Set.Ioi 0) u)
    (hcv : ConcaveOn ℝ (Set.Ioi 0) v) (hdu : ∀ x, 0 < x → HasDerivAt u (u' x) x)
    (hdv : ∀ x, 0 < x → HasDerivAt v (v' x) x) {Ω : FinProb S} {β C M P : ℝ}
    {C' P' : S → ℝ} (hβ : 0 ≤ β) (hC : 0 < C) (hM : 0 < M) (hP : 0 < P)
    (hC' : ∀ s, 0 < C' s) :
    IsLocalMax (moneyValue u v Ω β C M P C' P') 0 ↔
      1 / P * u' C = 1 / P * v' (M / P) + β * Ω.expect (fun s => 1 / P' s * u' (C' s)) := by
  constructor
  · intro hmax
    have := hmax.hasDerivAt_eq_zero (hasDerivAt_moneyValue hdu hdv Ω β P' hC hM hP hC')
    linarith
  · intro heul
    have e1 : ∀ᶠ δ in 𝓝 (0 : ℝ), 0 < C - δ / P := by
      have hcont : Continuous fun δ : ℝ => C - δ / P := by fun_prop
      exact continuousAt_const.eventually_lt hcont.continuousAt (by simpa using hC)
    have e2 : ∀ᶠ δ in 𝓝 (0 : ℝ), 0 < (M + δ) / P := by
      have hcont : Continuous fun δ : ℝ => (M + δ) / P := by fun_prop
      exact continuousAt_const.eventually_lt hcont.continuousAt (by simpa using div_pos hM hP)
    have e3 : ∀ᶠ δ in 𝓝 (0 : ℝ), ∀ s, 0 < C' s + δ / P' s := by
      refine Filter.eventually_all.2 fun s => ?_
      have hcont : Continuous fun δ : ℝ => C' s + δ / P' s := by fun_prop
      exact continuousAt_const.eventually_lt hcont.continuousAt (by simpa using hC' s)
    filter_upwards [e1, e2, e3] with δ h1 h2 h3
    have t1 := concave_tangent hcu hdu hC h1
    have t2 := concave_tangent hcv hdv (div_pos hM hP) h2
    have t3 : Ω.expect (fun s => u (C' s + δ / P' s))
        ≤ Ω.expect (fun s => u (C' s) + δ * (1 / P' s * u' (C' s))) :=
      Ω.expect_mono fun s => by
        have := concave_tangent hcu hdu (hC' s) (h3 s)
        have e : u' (C' s) * (C' s + δ / P' s - C' s) = δ * (1 / P' s * u' (C' s)) := by
          ring
        linarith
    rw [Ω.expect_add, Ω.expect_mul_left] at t3
    have t4 := mul_le_mul_of_nonneg_left t3 hβ
    have e1' : u' C * (C - δ / P - C) = -(δ * (1 / P * u' C)) := by ring
    have e2' : v' (M / P) * ((M + δ) / P - M / P) = δ * (1 / P * v' (M / P)) := by
      ring
    have h6 : δ * (1 / P * u' C) = δ * (1 / P * v' (M / P))
        + δ * (β * Ω.expect (fun s => 1 / P' s * u' (C' s))) := by rw [heul]; ring
    simp only [moneyValue, zero_div, sub_zero, add_zero]
    nlinarith [t1, t2, t4, e1', e2', h6]

/-- **The nominal-bond Euler equation (95)** (O&R (95), p. 581): buying `δ` dollars of a
one-period dollar bond is a reallocation with cost `1/P_t` and payoff `(1+i)/P_{t+1}`; the
first-order condition is necessary and sufficient and reads
`u′(C_t) = β E_t[(1+i) (P_t/P_{t+1}) u′(C_{t+1})]`. -/
theorem nominal_bond_euler_iff {u u' : ℝ → ℝ} (hc : ConcaveOn ℝ (Set.Ioi 0) u)
    (hd : ∀ x, 0 < x → HasDerivAt u (u' x) x) {Ω : FinProb S} {β C P i : ℝ}
    {C' P' : S → ℝ} (hβ : 0 ≤ β) (hC : 0 < C) (hP : 0 < P) (hC' : ∀ s, 0 < C' s) :
    IsLocalMax (assetValue u Ω β C (1 / P) C' (fun s => (1 + i) / P' s)) 0 ↔
      u' C = β * Ω.expect (fun s => (1 + i) * (P / P' s) * u' (C' s)) := by
  rw [isLocalMax_assetValue_iff hc hd hβ hC hC']
  have e : Ω.expect (fun s => (1 + i) * (P / P' s) * u' (C' s))
      = P * Ω.expect (fun s => u' (C' s) * ((1 + i) / P' s)) := by
    rw [← Ω.expect_mul_left]
    congr 1; funext s; ring
  rw [e]
  constructor
  · intro h
    have hP' : u' C = P * (1 / P * u' C) := by field_simp
    rw [hP', h]; ring
  · intro h
    rw [h, show ∀ z : ℝ, 1 / P * (β * (P * z)) = β * z from fun z => by field_simp]

/-- **The real-bond Euler equation (96)** (O&R (96), p. 581):
`u′(C_t) = (1+r) β E_t[u′(C_{t+1})]`, necessary and sufficient. -/
theorem real_bond_euler_iff {u u' : ℝ → ℝ} (hc : ConcaveOn ℝ (Set.Ioi 0) u)
    (hd : ∀ x, 0 < x → HasDerivAt u (u' x) x) {Ω : FinProb S} {β C r : ℝ} {C' : S → ℝ}
    (hβ : 0 ≤ β) (hC : 0 < C) (hC' : ∀ s, 0 < C' s) :
    IsLocalMax (assetValue u Ω β C 1 C' (fun _ => 1 + r)) 0 ↔
      u' C = (1 + r) * β * Ω.expect (fun s => u' (C' s)) := by
  rw [isLocalMax_assetValue_iff hc hd hβ hC hC', one_mul,
    show (fun s => u' (C' s) * (1 + r)) = fun s => (1 + r) * u' (C' s) from
      funext fun s => by ring, Ω.expect_mul_left]
  constructor <;> intro h <;> linarith

/-! ## Nominal bonds, real bonds and money (§8.7.2) -/

/-- **(97) holds if and only if inflation and marginal utility are uncorrelated**
(O&R (95)–(97), p. 581; the book states only "only if"). Here `π = P_t/P_{t+1}` and
`m = u′(C_{t+1})`. -/
theorem fisher_iff_cov_zero {Ω : FinProb S} {uC β i r : ℝ} {π m : S → ℝ} (hβ : 0 < β)
    (hi : 0 < 1 + i) (hm : 0 < Ω.expect m)
    (h95 : uC = β * Ω.expect (fun s => (1 + i) * π s * m s))
    (h96 : uC = (1 + r) * β * Ω.expect m) :
    1 + r = (1 + i) * Ω.expect π ↔ Ω.cov π m = 0 := by
  have e : Ω.expect (fun s => (1 + i) * π s * m s) = (1 + i) * Ω.expect (fun s => π s * m s) :=
    by rw [← Ω.expect_mul_left]; congr 1; funext s; ring
  rw [e, Ω.expect_mul_eq] at h95
  have key : (1 + r) * Ω.expect m = (1 + i) * (Ω.expect π * Ω.expect m + Ω.cov π m) := by
    have := h95.symm.trans h96
    have hb : β * ((1 + r) * Ω.expect m) = β * ((1 + i) * (Ω.expect π * Ω.expect m
        + Ω.cov π m)) := by linarith
    exact (mul_left_cancel₀ hβ.ne' hb)
  constructor
  · intro h
    rw [h] at key
    have : (1 + i) * Ω.cov π m = 0 := by linarith
    rcases mul_eq_zero.1 this with h1 | h1
    · linarith
    · exact h1
  · intro h
    rw [h, add_zero] at key
    have : ((1 + r) - (1 + i) * Ω.expect π) * Ω.expect m = 0 := by linarith
    rcases mul_eq_zero.1 this with h1 | h1
    · linarith
    · linarith

/-- With deterministic consumption the certainty-equivalence Fisher equation (97) holds
(O&R p. 581: "unless consumption ... is deterministic"). -/
theorem fisher_of_deterministic_consumption {Ω : FinProb S} {uC β i r mbar : ℝ}
    {π : S → ℝ} (hβ : 0 < β) (hi : 0 < 1 + i) (hm : 0 < mbar)
    (h95 : uC = β * Ω.expect (fun s => (1 + i) * π s * mbar))
    (h96 : uC = (1 + r) * β * Ω.expect (fun _ => mbar)) :
    1 + r = (1 + i) * Ω.expect π := by
  refine (fisher_iff_cov_zero (m := fun _ => mbar) hβ hi (by rwa [Ω.expect_const]) h95
    h96).2 ?_
  rw [Ω.cov_comm, Ω.cov_const_left]

/-- **The money-demand condition** `v′(M/P)/u′(C) = i/(1+i)` from (95) and (98)
(O&R p. 582; identical to (37)). Here `A = E_t[u′(C_{t+1})/P_{t+1}]`. -/
theorem money_demand_of_euler {uC vM P β i A : ℝ} (huC : 0 < uC) (hP : 0 < P)
    (hi : 0 < 1 + i) (h98 : 1 / P * uC = 1 / P * vM + β * A)
    (h95 : 1 / P * uC = (1 + i) * β * A) : vM / uC = i / (1 + i) := by
  have hA : β * A = uC / (P * (1 + i)) := by
    field_simp; field_simp at h95; linarith
  rw [hA] at h98
  field_simp at h98 ⊢
  linarith

/-! ## Consumption allocations (94) -/

/-- **Complete risk sharing with CRRA utility gives constant consumption shares** (O&R (94),
p. 580): if every country's marginal utility `C^{−ρ}` is a country-specific constant times a
common state price, and consumption exhausts world output, then `Cⁿ = xⁿ Y^W` with
time- and state-invariant shares `xⁿ > 0`, `Σ xⁿ = 1`. -/
theorem consumption_shares {ι T : Type} [Fintype ι] [Nonempty ι] {ρ : ℝ} (hρ : ρ ≠ 0)
    {C : ι → T → ℝ} {Y : T → ℝ} {lam : ι → ℝ} {κ : T → ℝ} (hC : ∀ n t, 0 < C n t)
    (hlam : ∀ n, 0 < lam n) (hκ : ∀ t, 0 < κ t)
    (hfoc : ∀ n t, C n t ^ (-ρ) = lam n * κ t) (hY : ∀ t, ∑ n, C n t = Y t) :
    ∃ x : ι → ℝ, (∀ n, 0 < x n) ∧ ∑ n, x n = 1 ∧ ∀ n t, C n t = x n * Y t := by
  have hCeq : ∀ n t, C n t = lam n ^ (-1 / ρ) * κ t ^ (-1 / ρ) := by
    intro n t
    have h : (C n t ^ (-ρ)) ^ (-1 / ρ) = (lam n * κ t) ^ (-1 / ρ) := by rw [hfoc n t]
    rwa [← Real.rpow_mul (hC n t).le, show -ρ * (-1 / ρ) = 1 by field_simp, Real.rpow_one,
      Real.mul_rpow (hlam n).le (hκ t).le] at h
  set D := ∑ n, lam n ^ (-1 / ρ) with hD
  have hDpos : 0 < D := Finset.sum_pos (fun n _ => Real.rpow_pos_of_pos (hlam n) _)
    Finset.univ_nonempty
  refine ⟨fun n => lam n ^ (-1 / ρ) / D, fun n => div_pos (Real.rpow_pos_of_pos (hlam n) _)
    hDpos, ?_, ?_⟩
  · rw [← Finset.sum_div, ← hD, div_self hDpos.ne']
  · intro n t
    rw [← hY t, hCeq n t]
    simp only [hCeq, ← Finset.sum_mul]
    rw [← hD]
    field_simp

/-- With constant shares, every country's consumption grows with world output, so the
Euler equation (93) is the same for every country (O&R p. 580, fn 64). -/
theorem consumption_growth_eq_world {x Y Y' ρ : ℝ} (hx : 0 < x) :
    (x * Y / (x * Y')) ^ ρ = (Y / Y') ^ ρ := by
  rw [mul_div_mul_left _ _ hx.ne']

/-! ## The money Euler equation with CRRA/log utility: exact linearity (99) -/

/-- `(Y/Y′)^ρ = (xY)^ρ/(xY′)^ρ` (O&R (99), p. 583: the share `x` cancels). -/
theorem rpow_ratio_eq {x Y Y' ρ : ℝ} (hx : 0 < x) (hY : 0 < Y) (hY' : 0 < Y') :
    (Y / Y') ^ ρ = (x * Y) ^ ρ / (x * Y') ^ ρ := by
  rw [Real.div_rpow hY.le hY'.le, Real.mul_rpow hx.le hY.le, Real.mul_rpow hx.le hY'.le]
  have : 0 < x ^ ρ := Real.rpow_pos_of_pos hx ρ
  field_simp

/-- **(98) with `u = C^{1−ρ}/(1−ρ)`, `v = log` and `C = xY^W` is (99)** (O&R (99), p. 583):
`u′(C) = C^{−ρ}`, `v′(m) = 1/m`. -/
theorem money_euler_crra_iff (Ω : FinProb S) {ρ x β M P Yw : ℝ} {P' Y' : S → ℝ}
    (hx : 0 < x) (hM : 0 < M) (hP : 0 < P) (hY : 0 < Yw) (hY' : ∀ s, 0 < Y' s) :
    1 / P * (x * Yw) ^ (-ρ) = 1 / P * (1 / (M / P))
        + β * Ω.expect (fun s => 1 / P' s * (x * Y' s) ^ (-ρ)) ↔
      1 = P * (x * Yw) ^ ρ / M + β * Ω.expect (fun s => P / P' s * (Yw / Y' s) ^ ρ) := by
  have hapos : 0 < (x * Yw) ^ ρ := Real.rpow_pos_of_pos (mul_pos hx hY) ρ
  have hE : Ω.expect (fun s => P / P' s * (Yw / Y' s) ^ ρ)
      = P * (x * Yw) ^ ρ * Ω.expect (fun s => 1 / P' s * (x * Y' s) ^ (-ρ)) := by
    rw [← Ω.expect_mul_left]
    congr 1; funext s
    rw [rpow_ratio_eq hx hY (hY' s), Real.rpow_neg (mul_pos hx (hY' s)).le]
    field_simp
  rw [hE, Real.rpow_neg (mul_pos hx hY).le]
  set a := (x * Yw) ^ ρ
  set E := Ω.expect (fun s => 1 / P' s * (x * Y' s) ^ (-ρ))
  have hk : P * a ≠ 0 := by positivity
  rw [← mul_right_inj' hk]
  have l1 : P * a * (1 / P * a⁻¹) = 1 := by field_simp
  have l2 : P * a * (1 / P * (1 / (M / P)) + β * E) = P * a / M + β * (P * a * E) := by
    field_simp
  rw [l1, l2]

/-- The key pointwise identity behind the exact linearity of (99): with
`w = M/(P (xY)^ρ)` and `M′ = M (1+μ) ε`,
`(P/P′)(Y/Y′)^ρ = (1/(1+μ)) (1/w) (w′/ε)` (O&R (99)–(100), p. 583). -/
theorem price_ratio_term_eq {ρ x μ M P Yw P' Y' e : ℝ} (hx : 0 < x) (hM : 0 < M) (hP : 0 < P)
    (hY : 0 < Yw) (hP' : 0 < P') (hY' : 0 < Y') (hμ : 0 < 1 + μ) (he : 0 < e) :
    P / P' * (Yw / Y') ^ ρ = 1 / (1 + μ) * (P * (x * Yw) ^ ρ / M)
      * (M * (1 + μ) * e / (P' * (x * Y') ^ ρ) / e) := by
  rw [rpow_ratio_eq hx hY hY']
  have : 0 < (x * Yw) ^ ρ := Real.rpow_pos_of_pos (mul_pos hx hY) ρ
  have : 0 < (x * Y') ^ ρ := Real.rpow_pos_of_pos (mul_pos hx hY') ρ
  field_simp

/-- **(99) is exactly linear in output-adjusted real balances** (O&R (99)–(100), p. 583):
with `w = M/(P (xY^W)^ρ)` and money growth `M′ = M(1+μ)ε`, equation (99) holds iff
`w_t = 1 + (β/(1+μ)) E_t[w_{t+1}/ε_{t+1}]`. -/
theorem eq99_iff_linear (Ω : FinProb S) {β μ ρ x M P Yw : ℝ} {P' Y' ε : S → ℝ}
    (hx : 0 < x) (hM : 0 < M) (hP : 0 < P) (hY : 0 < Yw) (hP' : ∀ s, 0 < P' s)
    (hY' : ∀ s, 0 < Y' s) (hμ : 0 < 1 + μ) (hε : ∀ s, 0 < ε s) :
    (1 = P * (x * Yw) ^ ρ / M + β * Ω.expect (fun s => P / P' s * (Yw / Y' s) ^ ρ)) ↔
      M / (P * (x * Yw) ^ ρ) = 1 + β / (1 + μ)
        * Ω.expect (fun s => M * (1 + μ) * ε s / (P' s * (x * Y' s) ^ ρ) / ε s) := by
  have hE : Ω.expect (fun s => P / P' s * (Yw / Y' s) ^ ρ) = 1 / (1 + μ)
      * (P * (x * Yw) ^ ρ / M)
      * Ω.expect (fun s => M * (1 + μ) * ε s / (P' s * (x * Y' s) ^ ρ) / ε s) := by
    rw [← Ω.expect_mul_left]
    congr 1; funext s
    exact price_ratio_term_eq hx hM hP hY (hP' s) (hY' s) hμ (hε s)
  rw [hE]
  have hapos : 0 < (x * Yw) ^ ρ := Real.rpow_pos_of_pos (mul_pos hx hY) ρ
  set E := Ω.expect (fun s => M * (1 + μ) * ε s / (P' s * (x * Y' s) ^ ρ) / ε s)
  set a := (x * Yw) ^ ρ
  constructor
  · intro h
    field_simp at h ⊢
    linarith
  · intro h
    field_simp at h ⊢
    linarith

/-- Equation (99) at a node of the event tree (O&R (99), p. 583). -/
def Eq99 (K : Kernel S) (β ρ x : ℝ) (M P Y : Hist S → ℝ) (h : Hist S) : Prop :=
  1 = P h * (x * Y h) ^ ρ / M h
    + β * (K.row h.1).expect (fun s' => P h / P (next h s') * (Y h / Y (next h s')) ^ ρ)

/-- Output-adjusted real balances `w = M/(P (xY^W)^ρ)` (O&R (101), p. 583: the guess is
`w ≡ ω`). -/
noncomputable def realBal (ρ x : ℝ) (M P Y : Hist S → ℝ) : Hist S → ℝ :=
  fun h => M h / (P h * (x * Y h) ^ ρ)

/-- `u′(C) M/P = w`: marginal utility times real balances is the output-adjusted real
balance, so the individual transversality condition (O&R fn 31, p. 542) is a condition
on `w` (O&R (101), p. 583). -/
theorem marginal_utility_real_balances {ρ x M P Y : ℝ} (hx : 0 < x) (hY : 0 < Y) :
    (x * Y) ^ (-ρ) * (M / P) = M / (P * (x * Y) ^ ρ) := by
  rw [Real.rpow_neg (mul_pos hx hY).le]
  field_simp

/-- The risk-neutral-like kernel `P(s, s′)/ε(s′)` induced by money growth shocks
(O&R (100), p. 583). -/
noncomputable def tilt (K : Kernel S) (ε : S → ℝ) : S → S → ℝ :=
  fun s s' => K.trans s s' / ε s'

/-- The linear stochastic difference equation `w_t = 1 + γ E_t[w_{t+1}/ε_{t+1}]` at every
node (O&R (99)–(100), p. 583). -/
def LinearMoneyEq (K : Kernel S) (ε : S → ℝ) (γ : ℝ) (w : Hist S → ℝ) : Prop :=
  ∀ h, w h = 1 + γ * oneStep (tilt K ε) w h

/-- The tilted expectation is `E_t[w_{t+1}/ε_{t+1}]` (O&R (100), p. 583). -/
theorem oneStep_tilt_eq (K : Kernel S) (ε : S → ℝ) (w : Hist S → ℝ) (h : Hist S) :
    oneStep (tilt K ε) w h = (K.row h.1).expect (fun s' => w (next h s') / ε s') := by
  simp only [oneStep, tilt, Kernel.row, FinProb.expect]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- **(99) at every node is the linear equation for `w`** (O&R (99)–(100), p. 583). -/
theorem eq99_iff_linearMoneyEq (K : Kernel S) {β μ ρ x : ℝ} {M P Y : Hist S → ℝ}
    {ε : S → ℝ} (hx : 0 < x) (hM : ∀ h, 0 < M h) (hP : ∀ h, 0 < P h) (hY : ∀ h, 0 < Y h)
    (hμ : 0 < 1 + μ) (hε : ∀ s, 0 < ε s)
    (hgrowth : ∀ h s', M (next h s') = M h * (1 + μ) * ε s') :
    (∀ h, Eq99 K β ρ x M P Y h) ↔ LinearMoneyEq K ε (β / (1 + μ)) (realBal ρ x M P Y) := by
  refine forall_congr' fun h => ?_
  rw [oneStep_tilt_eq]
  have e : (fun s' => realBal ρ x M P Y (next h s') / ε s') = fun s' => M h * (1 + μ) * ε s'
      / (P (next h s') * (x * Y (next h s')) ^ ρ) / ε s' := by
    funext s'; simp only [realBal, hgrowth]
  rw [e]
  exact eq99_iff_linear (K.row h.1) hx (hM h) (hP h) (hY h) (fun _ => hP _) (fun _ => hY _) hμ
    hε

/-! ## Existence, uniqueness and bubbles (100)–(101) -/

/-- The tilted kernel is nonnegative (O&R (100), p. 583). -/
theorem tilt_nonneg (K : Kernel S) {ε : S → ℝ} (hε : ∀ s, 0 < ε s) (s s' : S) :
    0 ≤ tilt K ε s s' :=
  div_nonneg (K.trans_nonneg s s') (hε s').le

/-- **`E_t[1/ε_{t+1}] = 1` makes the tilted kernel stochastic** (O&R (100), p. 583). -/
theorem tilt_sum (K : Kernel S) {ε : S → ℝ} (hE : ∀ s, (K.row s).expect (fun s' => 1 / ε s') = 1)
    (s : S) : ∑ s', tilt K ε s s' = 1 := by
  rw [← hE s]
  simp only [tilt, Kernel.row, FinProb.expect]
  exact Finset.sum_congr rfl fun _ _ => by ring

/-- **The book's `ω`** (O&R (101), p. 583): `1/(1 − β/(1+μ)) = (1+μ)/(1+μ−β) > 0`. -/
theorem omega_eq {β μ : ℝ} (hμ : 0 < 1 + μ) (hβμ : β < 1 + μ) :
    1 / (1 - β / (1 + μ)) = (1 + μ) / (1 + μ - β) ∧ 0 < (1 + μ) / (1 + μ - β) := by
  refine ⟨?_, div_pos hμ (by linarith)⟩
  have : 1 + μ - β ≠ 0 := by linarith
  field_simp

namespace Solutions

variable (K : Kernel S) {ε : S → ℝ}

/-- **The constant `ω = 1/(1−γ)` solves the linear equation** (O&R (101), p. 583, "our
conjecture is now verified"). -/
theorem omega_solves (hE : ∀ s, (K.row s).expect (fun s' => 1 / ε s') = 1) {γ : ℝ}
    (hγ : γ ≠ 1) : LinearMoneyEq K ε γ (fun _ => 1 / (1 - γ)) := by
  intro h
  rw [oneStep_const (tilt_sum K hE)]
  have : 1 - γ ≠ 0 := sub_ne_zero.2 (Ne.symm hγ)
  field_simp
  ring

/-- **Every solution is `ω` plus a bubble** `B_t = γ E_t[B_{t+1}/ε_{t+1}]`, and conversely
(O&R p. 582, "assuming no monetary bubbles"). -/
theorem linear_iff_bubble (hE : ∀ s, (K.row s).expect (fun s' => 1 / ε s') = 1) {γ : ℝ}
    (hγ : γ ≠ 1) (w : Hist S → ℝ) :
    LinearMoneyEq K ε γ w ↔ ∀ h, w h - 1 / (1 - γ)
      = γ * oneStep (tilt K ε) (fun g => w g - 1 / (1 - γ)) h := by
  have h1 : 1 - γ ≠ 0 := sub_ne_zero.2 (Ne.symm hγ)
  refine forall_congr' fun h => ?_
  rw [oneStep_sub, oneStep_const (tilt_sum K hE)]
  constructor
  · intro hw
    rw [hw]; field_simp; ring
  · intro hw
    have : w h = 1 / (1 - γ) + γ * (oneStep (tilt K ε) w h - 1 / (1 - γ)) := by linarith
    rw [this]; field_simp; ring

/-- Iterating the bubble equation: `B_t = γⁿ Ẽ_t B_{t+n}` (O&R (100), p. 583). -/
theorem bubble_iterate {k : S → S → ℝ} {γ : ℝ} {B : Hist S → ℝ}
    (hB : ∀ h, B h = γ * oneStep k B h) (n : ℕ) (h : Hist S) :
    B h = γ ^ n * iterStep k n B h := by
  induction n generalizing h with
  | zero => simp [iterStep]
  | succ n ih =>
    have hBf : B = fun g => γ * oneStep k B g := funext hB
    rw [ih h]
    conv_lhs => rw [hBf]
    rw [iterStep_mul_left, iterStep_succ, pow_succ]
    ring

/-- **The unique bounded solution is `ω`** (O&R (101), p. 583: "existence and uniqueness
(assuming no monetary bubbles)"): along the whole event tree, a bounded solution of
`w_t = 1 + γ E_t[w_{t+1}/ε_{t+1}]` with `0 ≤ γ < 1` is the constant `1/(1−γ)`. -/
theorem unique_bounded (hε : ∀ s, 0 < ε s)
    (hE : ∀ s, (K.row s).expect (fun s' => 1 / ε s') = 1) {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) {w : Hist S → ℝ} (hw : LinearMoneyEq K ε γ w) {b : ℝ}
    (hb : ∀ h, |w h| ≤ b) (h : Hist S) : w h = 1 / (1 - γ) := by
  set ω := 1 / (1 - γ)
  have hB := (linear_iff_bubble K hE hγ1.ne w).1 hw
  have hbd : ∀ g, |w g - ω| ≤ b + |ω| := fun g =>
    (abs_sub _ _).trans (by linarith [hb g])
  have key : ∀ n : ℕ, |w h - ω| ≤ γ ^ n * (b + |ω|) := fun n => by
    rw [bubble_iterate hB n h, abs_mul, abs_of_nonneg (pow_nonneg hγ0 n)]
    exact mul_le_mul_of_nonneg_left
      (abs_iterStep_le (tilt_nonneg K hε) (tilt_sum K hE) n hbd h) (pow_nonneg hγ0 n)
  have ht : Tendsto (fun n : ℕ => γ ^ n * (b + |ω|)) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hγ0 hγ1).mul_const (b + |ω|)
  have := ge_of_tendsto' ht key
  have h0 : |w h - ω| = 0 := le_antisymm this (abs_nonneg _)
  linarith [abs_eq_zero.1 h0]

/-- **Every positive solution lies above `ω`: there are no negative bubbles** (O&R (101),
p. 583; derived from positivity of the price level alone). -/
theorem ge_omega_of_pos (hε : ∀ s, 0 < ε s)
    (hE : ∀ s, (K.row s).expect (fun s' => 1 / ε s') = 1) {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) {w : Hist S → ℝ} (hw : LinearMoneyEq K ε γ w) (hpos : ∀ h, 0 < w h)
    (h : Hist S) : 1 / (1 - γ) ≤ w h := by
  set ω := 1 / (1 - γ)
  have hB := (linear_iff_bubble K hE hγ1.ne w).1 hw
  have key : ∀ n : ℕ, -(γ ^ n * ω) ≤ w h - ω := fun n => by
    rw [bubble_iterate hB n h]
    have hlow := iterStep_mono (tilt_nonneg K hε) n (X := fun _ => -ω)
      (Y := fun g => w g - ω) (fun g => by linarith [hpos g]) h
    rw [iterStep_const (tilt_sum K hE)] at hlow
    nlinarith [pow_nonneg hγ0 n]
  have ht : Tendsto (fun n : ℕ => -(γ ^ n * ω)) atTop (𝓝 0) := by
    simpa using ((tendsto_pow_atTop_nhds_zero_of_lt_one hγ0 hγ1).mul_const ω).neg
  have := le_of_tendsto' ht key
  linarith

/-- A bubble growing deterministically at rate `1/γ` (O&R p. 582, "monetary bubbles"). -/
noncomputable def depthBubble (γ c : ℝ) : Hist S → ℝ :=
  fun h => 1 / (1 - γ) + c * γ⁻¹ ^ depth h

/-- `E_t` moves the deterministic bubble forward in time (O&R (100), p. 583). -/
theorem iterStep_depthBubble {k : S → S → ℝ} (hk : ∀ s, ∑ s', k s s' = 1) (γ c : ℝ) (n : ℕ)
    (h : Hist S) :
    iterStep k n (depthBubble γ c) h = 1 / (1 - γ) + c * γ⁻¹ ^ (depth h + n) :=
  iterStep_depth hk n (fun d => 1 / (1 - γ) + c * γ⁻¹ ^ d) h

/-- **Bubbles exist**: `ω + c γ^{−t}` solves the linear equation for every `c`
(O&R p. 582). -/
theorem depthBubble_solves (hE : ∀ s, (K.row s).expect (fun s' => 1 / ε s') = 1) {γ : ℝ}
    (hγ0 : γ ≠ 0) (hγ1 : γ ≠ 1) (c : ℝ) : LinearMoneyEq K ε γ (depthBubble γ c) := by
  intro h
  have e := iterStep_depthBubble (tilt_sum K hE) γ c 1 h
  rw [show iterStep (tilt K ε) 1 (depthBubble γ c) h = oneStep (tilt K ε) (depthBubble γ c) h
    from rfl] at e
  rw [e]
  have : 1 - γ ≠ 0 := sub_ne_zero.2 (Ne.symm hγ1)
  simp only [depthBubble, pow_succ]
  field_simp
  ring

omit [Fintype S] in
/-- Positive bubbles give positive real balances (O&R p. 582). -/
theorem depthBubble_pos {γ c : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hc : 0 ≤ c) (h : Hist S) :
    0 < depthBubble γ c h := by
  have : 0 < 1 / (1 - γ) := div_pos one_pos (by linarith)
  have : 0 ≤ c * γ⁻¹ ^ depth h := mul_nonneg hc (pow_nonneg (inv_nonneg.2 hγ0.le) _)
  simp only [depthBubble]; linarith

/-- A node at every date (O&R §8.7). -/
def nodeAt (s : S) (n : ℕ) : Hist S := (s, List.replicate n s)

omit [Fintype S] in
/-- The node `nodeAt s n` is at date `n` (O&R §8.7). -/
theorem depth_nodeAt (s : S) (n : ℕ) : depth (nodeAt s n) = n := by
  simp [depth, nodeAt]

omit [Fintype S] in
/-- **Nonzero bubbles are unbounded**, so boundedness is exactly "no bubbles"
(O&R p. 582). -/
theorem depthBubble_unbounded [Nonempty S] {γ c : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hc : c ≠ 0) : ¬ ∃ b, ∀ h : Hist S, |depthBubble γ c h| ≤ b := by
  rintro ⟨b, hb⟩
  have hgt : 1 < γ⁻¹ := one_lt_inv_iff₀.2 ⟨hγ0, hγ1⟩
  obtain ⟨n, hn⟩ := ((tendsto_pow_atTop_atTop_of_one_lt hgt).eventually_gt_atTop
    ((b + |1 / (1 - γ)|) / |c|)).exists
  have hcpos : 0 < |c| := abs_pos.2 hc
  have h1 := hb (nodeAt (Classical.arbitrary S) n)
  simp only [depthBubble, depth_nodeAt] at h1
  have h2 : |c * γ⁻¹ ^ n| ≤ b + |1 / (1 - γ)| := by
    have := abs_sub_abs_le_abs_sub (1 / (1 - γ) + c * γ⁻¹ ^ n) (1 / (1 - γ))
    simp only [add_sub_cancel_left] at this
    have := abs_add_le (1 / (1 - γ) + c * γ⁻¹ ^ n) (-(1 / (1 - γ)))
    rw [add_neg_cancel_comm, abs_neg] at this
    linarith
  rw [abs_mul, abs_of_pos (pow_pos (inv_pos.2 hγ0) n)] at h2
  rw [div_lt_iff₀ hcpos] at hn
  nlinarith

/-- **No monetary equilibrium when `1 + μ ≤ β`** (O&R (100), p. 583, where `1 + μ > β` is
assumed): if `γ ≥ 1` the linear equation has NO positive solution at all, bounded or not. -/
theorem no_positive_solution [Nonempty S] {γ : ℝ} (hγ : 1 ≤ γ)
    (hε : ∀ s, 0 < ε s) (hE : ∀ s, (K.row s).expect (fun s' => 1 / ε s') = 1)
    {w : Hist S → ℝ} (hw : LinearMoneyEq K ε γ w) : ¬ ∀ h, 0 < w h := by
  intro hpos
  have key : ∀ n : ℕ, ∀ h, (n : ℝ) ≤ w h := by
    intro n
    induction n with
    | zero => exact fun h => by simpa using (hpos h).le
    | succ n ih =>
      intro h
      have hQ : (n : ℝ) ≤ oneStep (tilt K ε) w h := by
        have := oneStep_mono (tilt_nonneg K hε) (X := fun _ => (n : ℝ)) (Y := w) ih h
        rwa [oneStep_const (tilt_sum K hE)] at this
      rw [hw h]
      push_cast
      nlinarith [Nat.cast_nonneg (α := ℝ) n]
  let h0 : Hist S := (Classical.arbitrary S, [])
  obtain ⟨n, hn⟩ := exists_nat_gt (w h0)
  linarith [key n h0]

end Solutions

open Solutions

/-! ## Transversality -/

/-- The individual transversality condition `lim β^T E_t[u′(C_{t+T}) M_{t+T}/P_{t+T}] = 0`
(O&R fn 31, p. 542, carried to the stochastic model of §8.7), written in `w`
(`marginal_utility_real_balances`). -/
def TVC (K : Kernel S) (β : ℝ) (w : Hist S → ℝ) : Prop :=
  ∀ h, Tendsto (fun T : ℕ => β ^ T * iterStep K.trans T w h) atTop (𝓝 0)

/-- The fundamental solution `ω` satisfies the transversality condition (O&R (101)). -/
theorem omega_TVC (K : Kernel S) {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (ω : ℝ) :
    TVC K β (fun _ => ω) := by
  intro h
  simp only [iterStep_const K.trans_sum]
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0 hβ1).mul_const ω

/-- **With nonnegative money growth, bubbles violate the transversality condition**
(O&R p. 582; the stochastic analogue of the deterministic argument of §8.3.5):
the deterministic bubble `ω + cγ^{−t}`, `c > 0`, fails the TVC when `μ ≥ 0`. -/
theorem depthBubble_not_TVC [Nonempty S] (K : Kernel S) {β μ c : ℝ} (hβ : 0 < β)
    (hμ : 0 ≤ μ) (hβμ : β < 1 + μ) (hc : 0 < c) :
    ¬ TVC K β (depthBubble (β / (1 + μ)) c) := by
  intro htvc
  set γ := β / (1 + μ)
  have hμ1 : 0 < 1 + μ := by linarith
  have hγ0 : 0 < γ := div_pos hβ hμ1
  have hγ1 : γ < 1 := (div_lt_one hμ1).2 hβμ
  let h0 : Hist S := (Classical.arbitrary S, [])
  have ht := htvc h0
  have hω : 0 < 1 / (1 - γ) := div_pos one_pos (by linarith)
  have key : ∀ T : ℕ, c ≤ β ^ T * iterStep K.trans T (depthBubble γ c) h0 := fun T => by
    rw [iterStep_depthBubble K.trans_sum]
    have hd : depth h0 = 0 := rfl
    rw [hd, zero_add]
    have e : β ^ T * (c * γ⁻¹ ^ T) = c * (1 + μ) ^ T := by
      rw [← mul_assoc, mul_comm (β ^ T) c, mul_assoc, ← mul_pow]
      congr 2
      simp only [γ]; field_simp
    have h1 : 1 ≤ (1 + μ) ^ T := one_le_pow₀ (by linarith)
    have h2 : 0 ≤ β ^ T * (1 / (1 - γ)) := mul_nonneg (pow_nonneg hβ.le T) hω.le
    rw [mul_add, e]
    nlinarith
  have := ge_of_tendsto' ht key
  linarith

/-- **With money SHRINKING (`μ < 0`), bubbles satisfy the transversality condition**
(O&R pp. 582–583: the book's uniqueness claim needs `μ ≥ 0`, as in the deterministic
case): the bubble `ω + cγ^{−t}` is then a second, bubbly, positive equilibrium. -/
theorem depthBubble_TVC_of_neg (K : Kernel S) {β μ c : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hμ : μ < 0) (hβμ : β < 1 + μ) : TVC K β (depthBubble (β / (1 + μ)) c) := by
  intro h
  set γ := β / (1 + μ)
  have hμ1 : 0 < 1 + μ := by linarith
  simp only [iterStep_depthBubble K.trans_sum]
  have e : ∀ T : ℕ, β ^ T * (1 / (1 - γ) + c * γ⁻¹ ^ (depth h + T))
      = β ^ T * (1 / (1 - γ)) + c * γ⁻¹ ^ depth h * (1 + μ) ^ T := fun T => by
    rw [mul_add, pow_add]
    have : β ^ T * γ⁻¹ ^ T = (1 + μ) ^ T := by
      rw [← mul_pow]; congr 1; simp only [γ]; field_simp
    rw [← this]; ring
  simp only [e]
  have h1 := (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).mul_const (1 / (1 - γ))
  have h2 := (tendsto_pow_atTop_nhds_zero_of_lt_one hμ1.le (by linarith : 1 + μ < 1)).const_mul
    (c * γ⁻¹ ^ depth h)
  simpa using h1.add h2

/-- `E_t[1/ε_{t+1}] = 1` forces `min ε ≤ 1` (O&R (100), p. 583). -/
theorem min_eps_le_one (K : Kernel S) {ε : S → ℝ} {εm : ℝ} (hεm : 0 < εm)
    (hmin : ∀ s, εm ≤ ε s) (s : S) (hE : (K.row s).expect (fun s' => 1 / ε s') = 1) :
    εm ≤ 1 := by
  have h1 : (K.row s).expect (fun s' => 1 / ε s') ≤ (K.row s).expect (fun _ => 1 / εm) :=
    (K.row s).expect_mono fun s' => one_div_le_one_div_of_le hεm (hmin s')
  rw [hE, FinProb.expect_const] at h1
  rwa [le_div_iff₀ hεm, one_mul] at h1

/-- **Uniqueness of the monetary equilibrium from the transversality condition**
(O&R (101), p. 583, made precise): if `(1+μ) min ε ≥ 1`, every POSITIVE solution of (99)
that satisfies the transversality condition is `w ≡ ω`. (By `min_eps_le_one` this forces
`μ ≥ 0`; by `depthBubble_TVC_of_neg` uniqueness genuinely fails for `μ < 0`.) -/
theorem unique_of_TVC (K : Kernel S) {ε : S → ℝ} (hε : ∀ s, 0 < ε s)
    (hE : ∀ s, (K.row s).expect (fun s' => 1 / ε s') = 1) {β μ εm : ℝ} (hβ : 0 < β)
    (hβμ : β < 1 + μ) (hεm : 0 < εm) (hmin : ∀ s, εm ≤ ε s) (hcond : 1 ≤ (1 + μ) * εm)
    {w : Hist S → ℝ} (hw : LinearMoneyEq K ε (β / (1 + μ)) w) (hpos : ∀ h, 0 < w h)
    (htvc : TVC K β w) (h : Hist S) : w h = 1 / (1 - β / (1 + μ)) := by
  set γ := β / (1 + μ)
  set ω := 1 / (1 - γ)
  have hμ1 : 0 < 1 + μ := by linarith
  have hγ0 : 0 < γ := div_pos hβ hμ1
  have hγ1 : γ < 1 := (div_lt_one hμ1).2 hβμ
  have hω : 0 < ω := div_pos one_pos (by linarith)
  set B : Hist S → ℝ := fun g => w g - ω
  have hB0 : ∀ g, 0 ≤ B g := fun g => by
    simp only [B]; linarith [ge_omega_of_pos K hε hE hγ0.le hγ1 hw hpos g]
  have hB := (linear_iff_bubble K hE hγ1.ne w).1 hw
  have hcmp : ∀ s s', tilt K ε s s' ≤ εm⁻¹ * K.trans s s' := fun s s' => by
    simp only [tilt]
    rw [div_eq_mul_inv, mul_comm]
    exact mul_le_mul_of_nonneg_right (inv_anti₀ hεm (hmin s')) (K.trans_nonneg s s')
  have hwB : w = fun g => ω + B g := funext fun g => by simp [B]
  have key : ∀ T : ℕ, B h ≤ β ^ T * iterStep K.trans T w h := fun T => by
    have h1 := bubble_iterate hB T h
    have h2 := iterStep_le_pow_mul (inv_nonneg.2 hεm.le) (tilt_nonneg K hε) K.trans_nonneg
      hcmp T hB0 h
    have hX : 0 ≤ iterStep K.trans T B h := iterStep_nonneg K.trans_nonneg T hB0 h
    have h3 : β ^ T * iterStep K.trans T w h
        = β ^ T * ω + β ^ T * iterStep K.trans T B h := by
      rw [hwB, iterStep_add_fun, iterStep_const K.trans_sum, mul_add]
    have hβsplit : β = ((1 + μ) * εm) * (γ * εm⁻¹) := by
      simp only [γ]; field_simp
    have h4 : B h ≤ (γ * εm⁻¹) ^ T * iterStep K.trans T B h := by
      calc B h = γ ^ T * iterStep (tilt K ε) T B h := h1
        _ ≤ γ ^ T * (εm⁻¹ ^ T * iterStep K.trans T B h) :=
            mul_le_mul_of_nonneg_left h2 (pow_nonneg hγ0.le T)
        _ = (γ * εm⁻¹) ^ T * iterStep K.trans T B h := by rw [mul_pow, mul_assoc]
    have h5 : 1 ≤ ((1 + μ) * εm) ^ T := one_le_pow₀ hcond
    have h6 : β ^ T * iterStep K.trans T B h
        = ((1 + μ) * εm) ^ T * ((γ * εm⁻¹) ^ T * iterStep K.trans T B h) := by
      rw [hβsplit, mul_pow, mul_assoc]
    have h7 : 0 ≤ β ^ T * ω := mul_nonneg (pow_nonneg hβ.le T) hω.le
    rw [h3, h6]
    nlinarith [hB0 h]
  have := ge_of_tendsto' (htvc h) key
  have : B h = 0 := le_antisymm this (hB0 h)
  simp only [B] at this
  linarith

/-- **Deterministic money growth** (`ε ≡ 1`): the transversality condition selects `ω`
exactly when `μ ≥ 0` (O&R (100)–(101), p. 583, with the book's §8.3.5 condition). -/
theorem unique_of_TVC_deterministic (K : Kernel S) {β μ : ℝ} (hβ : 0 < β) (hβμ : β < 1 + μ)
    (hμ : 0 ≤ μ) {w : Hist S → ℝ} (hw : LinearMoneyEq K (fun _ => 1) (β / (1 + μ)) w)
    (hpos : ∀ h, 0 < w h) (htvc : TVC K β w) (h : Hist S) :
    w h = 1 / (1 - β / (1 + μ)) :=
  unique_of_TVC K (fun _ => one_pos) (fun s => by simp [FinProb.expect_const]) hβ hβμ
    one_pos (fun _ => le_rfl) (by linarith) hw hpos htvc h

/-- **Stationary Markov equilibria**: a solution that depends only on the current state is
`ω` (finite state space, so automatically bounded) (O&R (101), p. 583). -/
theorem markov_unique (K : Kernel S) {ε : S → ℝ} (hε : ∀ s, 0 < ε s)
    (hE : ∀ s, (K.row s).expect (fun s' => 1 / ε s') = 1) {γ : ℝ} (hγ0 : 0 ≤ γ)
    (hγ1 : γ < 1) {v : S → ℝ} (hv : ∀ s, v s = 1 + γ * ∑ s', tilt K ε s s' * v s') (s : S) :
    v s = 1 / (1 - γ) := by
  have hw : LinearMoneyEq K ε γ (fun g => v g.1) := fun g => hv g.1
  have hb : ∀ g : Hist S, |v g.1| ≤ ∑ t, |v t| := fun g =>
    Finset.single_le_sum (f := fun t => |v t|) (fun t _ => abs_nonneg _) (Finset.mem_univ _)
  exact unique_bounded K hε hE hγ0 hγ1 hw hb (s, [])

/-! ## Consequences: the price level and the nominal interest rate -/

/-- **The equilibrium price level** `P_t = M_t (1 − β/(1+μ)) (xY^W_t)^{−ρ}` (O&R p. 583). -/
theorem price_level_formula {ρ x β μ M P Y : ℝ} (hx : 0 < x) (hP : 0 < P)
    (hY : 0 < Y) (hβμ : β < 1 + μ) (hμ : 0 < 1 + μ)
    (hw : M / (P * (x * Y) ^ ρ) = 1 / (1 - β / (1 + μ))) :
    P = M * (1 - β / (1 + μ)) * (x * Y) ^ (-ρ) := by
  have ha : 0 < (x * Y) ^ ρ := Real.rpow_pos_of_pos (mul_pos hx hY) ρ
  have h1 : 1 - β / (1 + μ) ≠ 0 := by
    have : β / (1 + μ) < 1 := (div_lt_one hμ).2 hβμ
    linarith
  rw [Real.rpow_neg (mul_pos hx hY).le]
  field_simp at hw ⊢
  rw [hw]
  have : 1 + μ - β ≠ 0 := by linarith
  field_simp

/-- **The price level does not depend on expected future output** (O&R p. 583): two
economies in the bubble-free equilibrium with the same current money and output have the
same current price level, whatever their output processes and kernels. -/
theorem price_level_independent_of_future_output {ρ x β μ : ℝ} {M₁ P₁ Y₁ M₂ P₂ Y₂ : ℝ}
    (hx : 0 < x) (hP₁ : 0 < P₁) (hY₁ : 0 < Y₁) (hP₂ : 0 < P₂) (hY₂ : 0 < Y₂)
    (hβμ : β < 1 + μ) (hμ : 0 < 1 + μ)
    (hw₁ : M₁ / (P₁ * (x * Y₁) ^ ρ) = 1 / (1 - β / (1 + μ)))
    (hw₂ : M₂ / (P₂ * (x * Y₂) ^ ρ) = 1 / (1 - β / (1 + μ))) (hM : M₁ = M₂)
    (hY : Y₁ = Y₂) : P₁ = P₂ := by
  rw [price_level_formula hx hP₁ hY₁ hβμ hμ hw₁,
    price_level_formula hx hP₂ hY₂ hβμ hμ hw₂, hM, hY]

/-- **Higher expected money growth lowers real-balance demand** (O&R p. 583): `ω` is
strictly decreasing in `μ` on `1 + μ > β`, `β > 0`. -/
theorem omega_strictAnti {β μ₁ μ₂ : ℝ} (hβ : 0 < β) (h₁ : β < 1 + μ₁) (h12 : μ₁ < μ₂) :
    (1 + μ₂) / (1 + μ₂ - β) < (1 + μ₁) / (1 + μ₁ - β) := by
  have a1 : 0 < 1 + μ₁ - β := by linarith
  have a2 : 0 < 1 + μ₂ - β := by linarith
  rw [div_lt_div_iff₀ a2 a1]
  nlinarith

/-- **Higher current income raises real-balance demand** (O&R p. 583): with `ρ > 0`,
`M/P = ω (xY^W)^ρ` is strictly increasing in `Y^W`. -/
theorem real_balances_strictMono {ω x ρ Y₁ Y₂ : ℝ} (hω : 0 < ω) (hx : 0 < x) (hρ : 0 < ρ)
    (hY : 0 < Y₁) (h12 : Y₁ < Y₂) : ω * (x * Y₁) ^ ρ < ω * (x * Y₂) ^ ρ :=
  mul_lt_mul_of_pos_left (Real.rpow_lt_rpow (mul_pos hx hY).le
    (mul_lt_mul_of_pos_left h12 hx) hρ) hω

/-- **The nominal interest rate** `1 + i = (1+μ)/β` (O&R p. 583): in the bubble-free
equilibrium the CRRA nominal-bond Euler equation (95),
`1 = (1+i) β E_t[(P_t/P_{t+1})(Y^W_t/Y^W_{t+1})^ρ]`, pins `i` independently of the
distribution of future output. -/
theorem nominal_rate_eq (K : Kernel S) {β μ ρ x i : ℝ} {M P Y : Hist S → ℝ} {ε : S → ℝ}
    (hx : 0 < x) (hM : ∀ h, 0 < M h) (hP : ∀ h, 0 < P h) (hY : ∀ h, 0 < Y h)
    (hμ : 0 < 1 + μ) (hβ : 0 < β) (hβμ : β < 1 + μ) (hε : ∀ s, 0 < ε s)
    (hE : ∀ s, (K.row s).expect (fun s' => 1 / ε s') = 1)
    (hgrowth : ∀ h s', M (next h s') = M h * (1 + μ) * ε s')
    (hw : ∀ h, realBal ρ x M P Y h = 1 / (1 - β / (1 + μ))) (h : Hist S)
    (h95 : 1 = (1 + i) * β
      * (K.row h.1).expect (fun s' => P h / P (next h s') * (Y h / Y (next h s')) ^ ρ)) :
    1 + i = (1 + μ) / β := by
  set ω := 1 / (1 - β / (1 + μ))
  have hγ1 : β / (1 + μ) < 1 := (div_lt_one hμ).2 hβμ
  have hω : 0 < ω := div_pos one_pos (by linarith)
  have hE' : (K.row h.1).expect (fun s' => P h / P (next h s') * (Y h / Y (next h s')) ^ ρ)
      = 1 / (1 + μ) := by
    have e : (fun s' => P h / P (next h s') * (Y h / Y (next h s')) ^ ρ)
        = fun s' => 1 / (1 + μ) * (1 / ω) * (ω * (1 / ε s')) := by
      funext s'
      rw [price_ratio_term_eq hx (hM h) (hP h) (hY h) (hP _) (hY _) hμ (hε s')]
      have h1 : P h * (x * Y h) ^ ρ / M h = 1 / ω := by
        rw [← hw h]; simp only [realBal]; field_simp
      have h2 : M h * (1 + μ) * ε s' / (P (next h s') * (x * Y (next h s')) ^ ρ) / ε s'
          = ω * (1 / ε s') := by
        rw [← hw (next h s')]; simp only [realBal, hgrowth]; field_simp
      rw [h1, h2]
    rw [e, FinProb.expect_mul_left, FinProb.expect_mul_left, hE h.1]
    field_simp
  rw [hE'] at h95
  field_simp at h95 ⊢
  linarith

/-- The equilibrium nominal rate satisfies the money-demand condition
`v′/u′ = 1/ω = 1 − β/(1+μ) = i/(1+i)` (O&R p. 582–583). -/
theorem money_demand_at_equilibrium {β μ i : ℝ} (hβ : 0 < β) (hμ : 0 < 1 + μ)
    (hi : 1 + i = (1 + μ) / β) : i / (1 + i) = 1 - β / (1 + μ) := by
  have : i = (1 + μ) / β - 1 := by linarith
  rw [hi, this]
  field_simp

/-! ## The money-growth shock must be positive (100) -/

/-- Next period's money stock is positive iff the shock is (O&R (100), p. 583: the book's
"nonnegative" must be "positive"). -/
theorem next_money_pos_iff {M μ e : ℝ} (hM : 0 < M) (hμ : 0 < 1 + μ) :
    0 < M * (1 + μ) * e ↔ 0 < e := by
  constructor
  · intro h
    by_contra hc
    push Not at hc
    have : M * (1 + μ) * e ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (by positivity) hc
    linarith
  · intro h; positivity

omit [Fintype S] in
/-- **A zero shock destroys the monetary equilibrium** (O&R (100), p. 583): if `ε(s′) = 0`
for some state then money vanishes at the successor node, so no equilibrium with positive
money (and finite `log(M/P)`) exists. Hence `ε > 0` is required, not `ε ≥ 0`. -/
theorem no_positive_money_of_eps_zero [Nonempty S] {M : Hist S → ℝ} {μ : ℝ} {ε : S → ℝ}
    (hgrowth : ∀ h s', M (next h s') = M h * (1 + μ) * ε s') {s' : S} (hz : ε s' = 0) :
    ¬ ∀ h, 0 < M h := by
  intro hpos
  have := hpos (next (Classical.arbitrary S, []) s')
  rw [hgrowth, hz, mul_zero] at this
  exact lt_irrefl 0 this

/-- **`E[1/ε] = 1` implies `E[ε] ≥ 1`** (O&R (100), p. 583): expected gross money growth is
at least `1 + μ`. -/
theorem one_le_expect_eps (Ω : FinProb S) {ε : S → ℝ} (hε : ∀ s, 0 < ε s)
    (hE : Ω.expect (fun s => 1 / ε s) = 1) : 1 ≤ Ω.expect ε := by
  have h2 : Ω.expect (fun _ => (2 : ℝ)) ≤ Ω.expect (fun s => ε s + 1 / ε s) :=
    Ω.expect_mono fun s => by
      have := hε s
      have e : ε s + 1 / ε s - 2 = (ε s - 1) ^ 2 / ε s := by field_simp; ring
      have : 0 ≤ (ε s - 1) ^ 2 / ε s := div_nonneg (sq_nonneg _) this.le
      linarith
  rw [Ω.expect_const, Ω.expect_add, hE] at h2
  linarith

/-- Expected gross money growth `E_t[M_{t+1}/M_t] = (1+μ) E_t ε ≥ 1 + μ` (O&R (100),
p. 583). -/
theorem expected_money_growth (Ω : FinProb S) {M μ : ℝ} {ε : S → ℝ} (hM : 0 < M)
    (hμ : 0 < 1 + μ) (hε : ∀ s, 0 < ε s) (hE : Ω.expect (fun s => 1 / ε s) = 1) :
    Ω.expect (fun s => M * (1 + μ) * ε s / M) = (1 + μ) * Ω.expect ε ∧
      1 + μ ≤ Ω.expect (fun s => M * (1 + μ) * ε s / M) := by
  have e : (fun s => M * (1 + μ) * ε s / M) = fun s => (1 + μ) * ε s := by
    funext s; field_simp
  rw [e, Ω.expect_mul_left]
  refine ⟨rfl, ?_⟩
  have := one_le_expect_eps Ω hε hE
  nlinarith

/-- An i.i.d. two-state kernel (O&R (100), p. 583: a concrete money-growth process). -/
noncomputable def exampleKernel : Kernel Bool :=
  ⟨fun _ _ => 1 / 2, fun _ _ => by norm_num, fun _ => by simp⟩

/-- The shocks `ε ∈ {2, 2/3}` (O&R (100), p. 583). -/
noncomputable def exampleEps : Bool → ℝ := fun b => if b then 2 else 2 / 3

/-- **The hypotheses of (100) are satisfiable with a nondegenerate shock**: `E[1/ε] = 1`
while `E[ε] = 4/3` (O&R (100), p. 583). -/
theorem example_eps_moments (s : Bool) :
    (exampleKernel.row s).expect (fun s' => 1 / exampleEps s') = 1 ∧
      (exampleKernel.row s).expect exampleEps = 4 / 3 := by
  simp [FinProb.expect, Kernel.row, exampleKernel, exampleEps]
  norm_num

/-! ## The log-linearised model (§8.7.3) -/

/-- The stochastic Cagan equation `m_t − q_t = −η (E_t q_{t+1} − q_t)` at every node
(O&R p. 584, "resembles the Cagan equation"). -/
def CaganTree (K : Kernel S) (η : ℝ) (m q : Hist S → ℝ) : Prop :=
  ∀ h, m h - q h = -η * (oneStep K.trans q h - q h)

/-- **The log-linear price equation is a Cagan equation in `q = p + ρ y^W`** with
`η = 1/ī` (O&R p. 584). -/
theorem logLinear_iff_cagan (K : Kernel S) {ibar ρ : ℝ} {m p y : Hist S → ℝ} :
    (∀ h, m h - p h = ρ * y h - 1 / ibar * (oneStep K.trans p h - p h)
        - ρ / ibar * (oneStep K.trans y h - y h)) ↔
      CaganTree K (1 / ibar) m (fun g => p g + ρ * y g) := by
  refine forall_congr' fun h => ?_
  rw [oneStep_add, oneStep_mul_left]
  beta_reduce
  constructor <;> intro H <;> linear_combination H

/-- The fundamental (no-bubble) solution
`q_t = (1/(1+η)) Σ_j (η/(1+η))^j E_t m_{t+j}` (O&R p. 584). -/
noncomputable def fundamental (K : Kernel S) (η : ℝ) (m : Hist S → ℝ) : Hist S → ℝ :=
  fun h => 1 / (1 + η) * ∑' j : ℕ, (η / (1 + η)) ^ j * iterStep K.trans j m h

/-- The stochastic no-bubble condition `lim (η/(1+η))ⁿ E_t q_{t+n} = 0` (O&R (8), p. 518,
carried to §8.7.3). -/
def NoBubble (K : Kernel S) (η : ℝ) (q : Hist S → ℝ) : Prop :=
  ∀ h, Tendsto (fun n : ℕ => (η / (1 + η)) ^ n * iterStep K.trans n q h) atTop (𝓝 0)

/-- `E_t` commutes with convergent sums (O&R p. 584). -/
theorem oneStep_tsum (k : S → S → ℝ) {a : ℕ → Hist S → ℝ}
    (ha : ∀ g, Summable fun j => a j g) (h : Hist S) :
    oneStep k (fun g => ∑' j, a j g) h = ∑' j, oneStep k (a j) h := by
  simp only [oneStep]
  rw [Summable.tsum_finsetSum fun s' _ => (ha _).mul_left _]
  exact Finset.sum_congr rfl fun s' _ => (tsum_mul_left).symm

/-- `E_t` preserves summability (O&R p. 584). -/
theorem oneStep_summable (k : S → S → ℝ) {a : ℕ → Hist S → ℝ}
    (ha : ∀ g, Summable fun j => a j g) (g : Hist S) :
    Summable fun j => oneStep k (a j) g := by
  simp only [oneStep]
  exact summable_sum fun s' _ => (ha _).mul_left _

/-- `E_t X_{t+n}` commutes with convergent sums (O&R p. 584). -/
theorem iterStep_tsum (k : S → S → ℝ) (n : ℕ) {a : ℕ → Hist S → ℝ}
    (ha : ∀ g, Summable fun j => a j g) (h : Hist S) :
    iterStep k n (fun g => ∑' j, a j g) h = ∑' j, iterStep k n (a j) h := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    rw [iterStep_succ, show oneStep k (fun g => ∑' j, a j g)
      = fun g => ∑' j, oneStep k (a j) g from funext fun g => oneStep_tsum k ha g,
      ih (oneStep_summable k ha)]
    simp only [iterStep_succ]

/-- **The fundamental solution solves the stochastic Cagan equation** (O&R p. 584), given
convergence of the discounted expected money path at every node. -/
theorem fundamental_solves (K : Kernel S) {η : ℝ} (hη : 0 < η) {m : Hist S → ℝ}
    (hsum : ∀ g, Summable fun j => (η / (1 + η)) ^ j * iterStep K.trans j m g) :
    CaganTree K η m (fundamental K η m) := by
  intro h
  set θ := η / (1 + η)
  have hE1 : oneStep K.trans (fundamental K η m) h
      = 1 / (1 + η) * ∑' j : ℕ, θ ^ j * iterStep K.trans (j + 1) m h := by
    rw [show fundamental K η m = fun g => 1 / (1 + η) * ∑' j : ℕ, θ ^ j * iterStep K.trans j m g
      from rfl, oneStep_mul_left, oneStep_tsum K.trans hsum]
    congr 2; funext j
    rw [oneStep_mul_left, ← iterStep_succ']
  have hsplit := (hsum h).tsum_eq_zero_add
  have hT : ∑' j : ℕ, θ ^ (j + 1) * iterStep K.trans (j + 1) m h
      = θ * ∑' j : ℕ, θ ^ j * iterStep K.trans (j + 1) m h := by
    rw [← tsum_mul_left]; congr 1; funext j; ring
  set T' := ∑' j : ℕ, θ ^ j * iterStep K.trans (j + 1) m h with hT'
  have hq : fundamental K η m h = 1 / (1 + η) * (m h + θ * T') := by
    change 1 / (1 + η) * ∑' j : ℕ, θ ^ j * iterStep K.trans j m h = _
    rw [hsplit, hT]
    simp only [pow_zero, one_mul]
    rfl
  rw [hE1, hq]
  simp only [θ]
  field_simp
  ring

/-- **The fundamental solution satisfies the no-bubble condition** (O&R p. 584). -/
theorem fundamental_noBubble (K : Kernel S) {η : ℝ} {m : Hist S → ℝ}
    (hsum : ∀ g, Summable fun j => (η / (1 + η)) ^ j * iterStep K.trans j m g) :
    NoBubble K η (fundamental K η m) := by
  intro h
  set θ := η / (1 + η)
  have e : ∀ n : ℕ, θ ^ n * iterStep K.trans n (fundamental K η m) h
      = 1 / (1 + η) * ∑' j : ℕ, θ ^ (j + n) * iterStep K.trans (j + n) m h := fun n => by
    rw [show fundamental K η m = fun g => 1 / (1 + η) * ∑' j : ℕ, θ ^ j * iterStep K.trans j m g
      from rfl, iterStep_mul_left, iterStep_tsum K.trans n hsum, ← mul_assoc, mul_comm (θ ^ n),
      mul_assoc, ← tsum_mul_left]
    congr 2; funext j
    rw [iterStep_mul_left, ← iterStep_add, pow_add, add_comm n j]
    ring
  simp only [e]
  simpa using (tendsto_sum_nat_add fun k => θ ^ k * iterStep K.trans k m h).const_mul
    (1 / (1 + η))

/-- **Uniqueness**: two solutions of the stochastic Cagan equation that both satisfy the
no-bubble condition coincide at every node (O&R p. 584). -/
theorem cagan_unique (K : Kernel S) {η : ℝ} (hη : 0 < η) {m q₁ q₂ : Hist S → ℝ}
    (h₁ : CaganTree K η m q₁) (h₂ : CaganTree K η m q₂) (hb₁ : NoBubble K η q₁)
    (hb₂ : NoBubble K η q₂) (h : Hist S) : q₁ h = q₂ h := by
  set θ := η / (1 + η)
  set d : Hist S → ℝ := fun g => q₁ g - q₂ g
  have hd : ∀ g, d g = θ * oneStep K.trans d g := fun g => by
    simp only [d, θ, oneStep_sub]
    have e1 := h₁ g
    have e2 := h₂ g
    field_simp
    linarith
  have key : ∀ n : ℕ, d h = θ ^ n * iterStep K.trans n q₁ h
      - θ ^ n * iterStep K.trans n q₂ h := fun n => by
    rw [bubble_iterate hd n h, iterStep_sub_fun]; ring
  have ht := (hb₁ h).sub (hb₂ h)
  rw [sub_zero] at ht
  have ht2 : Tendsto (fun _ : ℕ => d h) atTop (𝓝 0) := ht.congr fun n => (key n).symm
  have := tendsto_nhds_unique tendsto_const_nhds ht2
  simp only [d] at this
  linarith

/-- **The log-linear price level** (O&R p. 584):
`p_t = −ρ y^W_t + (ī/(1+ī)) Σ_{s≥t} (1+ī)^{−(s−t)} E_t m_s` is the unique solution of the
log-linearised equation for which `p + ρ y^W` has no bubble. -/
theorem logLinear_price_solution (K : Kernel S) {ibar ρ : ℝ} (hi : 0 < ibar)
    {m p y : Hist S → ℝ}
    (hsum : ∀ g, Summable fun j => (1 / (1 + ibar)) ^ j * iterStep K.trans j m g)
    (heq : ∀ h, m h - p h = ρ * y h - 1 / ibar * (oneStep K.trans p h - p h)
        - ρ / ibar * (oneStep K.trans y h - y h))
    (hnb : NoBubble K (1 / ibar) (fun g => p g + ρ * y g)) (h : Hist S) :
    p h = -ρ * y h + ibar / (1 + ibar)
      * ∑' j : ℕ, (1 / (1 + ibar)) ^ j * iterStep K.trans j m h := by
  have hθ : 1 / ibar / (1 + 1 / ibar) = 1 / (1 + ibar) := by field_simp; ring
  have hc : 1 / (1 + 1 / ibar) = ibar / (1 + ibar) := by field_simp; ring
  have hsum' : ∀ g, Summable fun j => (1 / ibar / (1 + 1 / ibar)) ^ j
      * iterStep K.trans j m g := by rw [hθ]; exact hsum
  have hq := cagan_unique K (one_div_pos.2 hi) ((logLinear_iff_cagan K).1 heq)
    (fundamental_solves K (one_div_pos.2 hi) hsum') hnb (fundamental_noBubble K hsum') h
  simp only [fundamental, hθ, hc] at hq
  linarith

/-! ## The stochastic cash-in-advance model (§8.7.4) -/

/-- **(103)**: a binding cash-in-advance constraint `M = P Y` gives `P = M/Y`
(O&R (103), p. 585). -/
theorem cia_price_level {M P Y : ℝ} (hY : 0 < Y) (hbind : M = P * Y) : P = M / Y := by
  rw [hbind]; field_simp

/-- Constant (unit) velocity under the cash-in-advance constraint (O&R p. 585: "a constant
velocity of money"). -/
theorem cia_velocity {M P Y : ℝ} (hM : 0 < M) (hbind : M = P * Y) : P * Y / M = 1 := by
  rw [← hbind]; exact div_self hM.ne'

/-- The cash-in-advance exchange rate from PPP (92) and (103):
`ℰ^{nm} = (Mⁿ/Yⁿ)/(M^m/Y^m)` (O&R (92), (103), pp. 580, 585). -/
theorem cia_exchange_rate {Mn Yn Mm Ym Pn Pm E : ℝ} (hYn : 0 < Yn) (hYm : 0 < Ym)
    (hPm : 0 < Pm) (hn : Mn = Pn * Yn) (hm : Mm = Pm * Ym) (hppp : Pn = E * Pm) :
    E = (Mn / Yn) / (Mm / Ym) := by
  rw [hn, hm, hppp]
  field_simp

/-- **The CIA nominal rate equals the MIU one with log utility** (O&R p. 585: "nominal
interest rates ... are determined just as in the preceding money-in-the-utility-function
model"): with `u = log`, `C = xY`, `P = M/Y` and `M′ = M(1+μ)ε`, `E[1/ε] = 1`,
`β E_t[(P_t/P_{t+1})(C_t/C_{t+1})] = β/(1+μ)`, so `1 + i = (1+μ)/β`. -/
theorem cia_bond_price_log (Ω : FinProb S) {β μ x M Y : ℝ} {Y' ε : S → ℝ} (hx : 0 < x)
    (hM : 0 < M) (hY : 0 < Y) (hY' : ∀ s, 0 < Y' s) (hμ : 0 < 1 + μ) (hε : ∀ s, 0 < ε s)
    (hE : Ω.expect (fun s => 1 / ε s) = 1) :
    β * Ω.expect (fun s => (M / Y) / (M * (1 + μ) * ε s / Y' s) * (x * Y / (x * Y' s)))
      = β / (1 + μ) := by
  have e : (fun s => (M / Y) / (M * (1 + μ) * ε s / Y' s) * (x * Y / (x * Y' s)))
      = fun s => 1 / (1 + μ) * (1 / ε s) := by
    funext s
    have := hY' s; have := hε s
    field_simp
  rw [e, Ω.expect_mul_left, hE]
  ring

/-! ## Currency substitution: dollarization (§8.3.8) -/

/-- **A positive home nominal interest rate is implied by the money Euler equation (65)**
(O&R (64)–(65), p. 552): with `(1+r)β = 1`, `u′(C_t) = u′(C_{t+1}) = U > 0` and a positive
marginal liquidity value `V = v′(·) > 0`, (65) forces `1 − βP_t/P_{t+1} > 0`, i.e. `i > 0`
(`1 + i = P_{t+1}/(βP_t)`). The book's (67) divides by this quantity. -/
theorem dollarization_home_rate_pos {U V β P P' : ℝ} (hU : 0 < U) (hV : 0 < V) (hP : 0 < P)
    (hP' : 0 < P') (h65 : 1 / P * U = 1 / P * V + 1 / P' * β * U) :
    0 < 1 - β * P / P' := by
  have : V = U * (1 - β * P / P') := by field_simp at h65 ⊢; linarith
  have h := hV
  rw [this] at h
  exact pos_of_mul_pos_right h hU.le

/-- **The foreign-currency first-order condition** (O&R (64)–(66) and the display before
(67), p. 552): `g′(M_F/P*) = (1 − βP*_t/P*_{t+1})/(1 − βP_t/P_{t+1})`. -/
theorem dollarization_foc {U V gp β P P' Ps Ps' : ℝ} (hU : 0 < U) (hV : 0 < V) (hP : 0 < P)
    (hP' : 0 < P') (hPs : 0 < Ps) (hPs' : 0 < Ps')
    (h65 : 1 / P * U = 1 / P * V + 1 / P' * β * U)
    (h66 : 1 / Ps * U = 1 / Ps * V * gp + 1 / Ps' * β * U) :
    gp = (1 - β * Ps / Ps') / (1 - β * P / P') := by
  have hpos := dollarization_home_rate_pos hU hV hP hP' h65
  have hV' : V = U * (1 - β * P / P') := by field_simp at h65 ⊢; linarith
  have hg : V * gp = U * (1 - β * Ps / Ps') := by field_simp at h66 ⊢; linarith
  rw [hV', mul_assoc] at hg
  have hg' : (1 - β * P / P') * gp = 1 - β * Ps / Ps' := mul_left_cancel₀ hU.ne' hg
  rw [eq_div_iff hpos.ne']
  linarith [hg']

/-- **Foreign-currency demand (67)** (O&R (67), p. 553): with `g(x) = a₀x − (a₁/2)x²`,
`g′(x) = a₀ − a₁x`, the interior holdings are `M_F/P* = (a₀ − ratio)/a₁`, positive iff
`a₀ > ratio`. -/
theorem dollarization_demand {a0 a1 x ratio : ℝ} (ha1 : 0 < a1) (hfoc : a0 - a1 * x = ratio) :
    x = (a0 - ratio) / a1 ∧ (0 < x ↔ ratio < a0) := by
  have hx : x = (a0 - ratio) / a1 := by field_simp; linarith
  refine ⟨hx, ?_⟩
  rw [hx, div_pos_iff_of_pos_right ha1, sub_pos]

/-- **No dollarization when home inflation does not exceed foreign inflation** (O&R p. 552,
"there is no point to using foreign currency since `a₀ ≤ 1`"): if `π ≤ π*` (gross
inflation factors) and the home nominal rate is positive, the ratio in (67) is at least `1`,
so `a₀ ≤ 1` rules out positive interior holdings. -/
theorem no_dollarization_of_low_inflation {β π πs a0 : ℝ} (hβ : 0 < β) (hπ : 0 < π)
    (hhome : 0 < 1 - β / π) (hle : π ≤ πs) (ha0 : a0 ≤ 1) :
    a0 ≤ (1 - β / πs) / (1 - β / π) := by
  have : β / πs ≤ β / π := div_le_div_of_nonneg_left hβ.le hπ hle
  rw [le_div_iff₀ hhome]
  nlinarith

/-- **Foreign-currency holdings rise with home inflation** (O&R p. 553): the ratio in (67)
is strictly decreasing in home inflation `π` when both nominal rates are positive, so the
interior `M_F/P*` is strictly increasing in `π`. -/
theorem dollarization_ratio_strictAnti {β π₁ π₂ πs : ℝ} (hβ : 0 < β) (hπ₁ : 0 < π₁)
    (h12 : π₁ < π₂) (hfor : 0 < 1 - β / πs) (hhome : 0 < 1 - β / π₁) :
    (1 - β / πs) / (1 - β / π₂) < (1 - β / πs) / (1 - β / π₁) := by
  have hπ₂ : 0 < π₂ := by linarith
  have h : β / π₂ < β / π₁ := div_lt_div_of_pos_left hβ hπ₁ h12
  have hhome2 : 0 < 1 - β / π₂ := by linarith
  exact (div_lt_div_iff_of_pos_left hfor hhome2 hhome).2 (by linarith)

/-- **The role of `a₀ > 1 − β`** (O&R p. 552, with constant foreign prices `π* = 1`):
if `a₀ > 1 − β`, foreign currency is held at all sufficiently high home inflation rates;
if `a₀ ≤ 1 − β` it is never held (for any `π > β`). -/
theorem dollarization_threshold {β a0 : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    (1 - β < a0 → ∃ πbar, ∀ π, πbar < π → (1 - β) / (1 - β / π) < a0) ∧
      (a0 ≤ 1 - β → ∀ π, β < π → a0 < (1 - β) / (1 - β / π)) := by
  constructor
  · intro ha
    have h1 : 0 < 1 - β := by linarith
    -- choose π̄ so that β/π < 1 − (1−β)/a0
    have ha0 : 0 < a0 := by linarith
    set δ := 1 - (1 - β) / a0
    have hδ : 0 < δ := by
      simp only [δ]; rw [sub_pos, div_lt_one ha0]; exact ha
    refine ⟨max β (β / δ), fun π hπ => ?_⟩
    have hπβ : β < π := lt_of_le_of_lt (le_max_left _ _) hπ
    have hπ0 : 0 < π := by linarith
    have hπδ : β / δ < π := lt_of_le_of_lt (le_max_right _ _) hπ
    have hden : 0 < 1 - β / π := by rw [sub_pos, div_lt_one hπ0]; exact hπβ
    have hsmall : β / π < δ := by
      rw [div_lt_iff₀ hπ0]; rw [div_lt_iff₀ hδ] at hπδ; linarith
    rw [div_lt_iff₀ hden]
    simp only [δ] at hsmall
    have : (1 - β) / a0 * a0 = 1 - β := by field_simp
    nlinarith
  · intro ha π hπ
    have hπ0 : 0 < π := by linarith
    have hden : 0 < 1 - β / π := by rw [sub_pos, div_lt_one hπ0]; exact hπ
    have hden1 : 1 - β / π < 1 := by have := div_pos hβ0 hπ0; linarith
    have : 1 - β < (1 - β) / (1 - β / π) := by
      rw [lt_div_iff₀ hden]; nlinarith
    linarith

/-! ## The household problem on the event tree: global optimality (§8.7.1–8.7.2) -/

/-- Extend a node by a list of future states, earliest first (O&R §8.7.1, p. 579: the
event tree of histories). -/
def extend : Hist S → List S → Hist S
  | h, [] => h
  | h, s :: l => extend (next h s) l

/-- `g` is a descendant of `h` (possibly `h` itself) (O&R §8.7.1). -/
def Desc (h g : Hist S) : Prop := ∃ l : List S, extend h l = g

omit [Fintype S] in
/-- Every node descends from itself (O&R §8.7.1). -/
theorem desc_refl (h : Hist S) : Desc h h := ⟨[], rfl⟩

omit [Fintype S] in
/-- Descendants of a child are descendants of the parent (O&R §8.7.1). -/
theorem desc_of_desc_next {h g : Hist S} (s : S) (hd : Desc (next h s) g) : Desc h g := by
  obtain ⟨l, hl⟩ := hd
  exact ⟨s :: l, hl⟩

omit [Fintype S] in
/-- Appending a state to the extension moves to a child (O&R §8.7.1). -/
theorem extend_append (h : Hist S) (l : List S) (s : S) :
    extend h (l ++ [s]) = next (extend h l) s := by
  induction l generalizing h with
  | nil => rfl
  | cons t l ih => exact ih (next h t)

omit [Fintype S] in
/-- Children of descendants are descendants (O&R §8.7.1). -/
theorem desc_next {h g : Hist S} (hd : Desc h g) (s : S) : Desc h (next g s) := by
  obtain ⟨l, rfl⟩ := hd
  exact ⟨l ++ [s], extend_append h l s⟩

omit [Fintype S] in
/-- Extension moves forward in time by the length of the list (O&R §8.7.1). -/
theorem depth_extend (h : Hist S) (l : List S) : depth (extend h l) = depth h + l.length := by
  induction l generalizing h with
  | nil => rfl
  | cons t l ih =>
    simp only [extend, ih, depth_next, List.length_cons]
    ring

/-- `E_t X_{t+n}` is monotone in the values of `X` on the subtree below the node
(O&R §8.7.1). -/
theorem iterStep_mono_desc {k : S → S → ℝ} (hk : ∀ s s', 0 ≤ k s s') (n : ℕ)
    {X Y : Hist S → ℝ} {h : Hist S} (hXY : ∀ g, Desc h g → X g ≤ Y g) :
    iterStep k n X h ≤ iterStep k n Y h := by
  induction n generalizing h with
  | zero => exact hXY h (desc_refl h)
  | succ n ih =>
    rw [iterStep_succ', iterStep_succ']
    exact Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left
      (ih fun g hg => hXY g (desc_of_desc_next s hg)) (hk _ _)

/-- `E_t X_{t+n}` depends only on the values of `X` on the subtree below the node
(O&R §8.7.1). -/
theorem iterStep_congr_desc (k : S → S → ℝ) (n : ℕ) {X Y : Hist S → ℝ} {h : Hist S}
    (hXY : ∀ g, Desc h g → X g = Y g) : iterStep k n X h = iterStep k n Y h := by
  induction n generalizing h with
  | zero => exact hXY h (desc_refl h)
  | succ n ih =>
    rw [iterStep_succ', iterStep_succ']
    exact Finset.sum_congr rfl fun s _ => by
      rw [ih fun g hg => hXY g (desc_of_desc_next s hg)]

/-- `E_t X_{t+n}` depends only on the values of `X` at date `t + n` (O&R §8.7.1). -/
theorem iterStep_congr_depth (k : S → S → ℝ) (n : ℕ) {X Y : Hist S → ℝ} {h : Hist S}
    (hXY : ∀ g, depth g = depth h + n → X g = Y g) : iterStep k n X h = iterStep k n Y h := by
  induction n generalizing h with
  | zero => exact hXY h rfl
  | succ n ih =>
    rw [iterStep_succ', iterStep_succ']
    exact Finset.sum_congr rfl fun s _ => by
      rw [ih fun g hg => hXY g (by rw [hg, depth_next]; ring)]

namespace Household

variable {J : Type} [Fintype J]

/-- The asset menu faced by a household (O&R §8.7.1–8.7.2, pp. 579–581): for each asset `j`
its real price at a node, its real payoff at a node per unit bought at the parent node, and
its real liquidity services (money: price, payoff and services all `1/P`; nominal bond: price
`1/P_t`, payoff `(1+i_t)/P_{t+1}`; real bond: price `1`, payoff `1+r_t`; output claim: price
`q_t`, payoff `q_{t+1} + d_{t+1}`), plus the real endowment/transfer. -/
structure AssetMarket (S J : Type) [Fintype S] [Fintype J] where
  price : J → Hist S → ℝ
  payoff : J → Hist S → ℝ
  service : J → Hist S → ℝ
  endow : Hist S → ℝ

/-- Real liquidity services from holdings, the argument of `v` (O&R (91), p. 579:
`v(M/P)`). -/
def services (A : AssetMarket S J) (a : J → Hist S → ℝ) (g : Hist S) : ℝ :=
  ∑ j, A.service j g * a j g

/-- **The budget constraints** at the root (initial real wealth `W₀`) and at every later
node of the subtree (O&R §8.7.1, p. 580: "the budget constraint for a country n resident"):
`C + Σ_j p_j a_j = endowment + Σ_j R_j a_j(parent)`. -/
def Feasible (A : AssetMarket S J) (h₀ : Hist S) (W₀ : ℝ) (C : Hist S → ℝ)
    (a : J → Hist S → ℝ) : Prop :=
  (C h₀ + ∑ j, A.price j h₀ * a j h₀ = W₀) ∧
    ∀ g, Desc h₀ g → ∀ s, C (next g s) + ∑ j, A.price j (next g s) * a j (next g s)
      = A.endow (next g s) + ∑ j, A.payoff j (next g s) * a j g

/-- Consumption and real balances stay in the domain of `u` and `v` (O&R (91), p. 579). -/
def Positive (A : AssetMarket S J) (h₀ : Hist S) (C : Hist S → ℝ) (a : J → Hist S → ℝ) :
    Prop :=
  ∀ g, Desc h₀ g → 0 < C g ∧ 0 < services A a g

/-- The date-`t` term `βᵗ E₀[u(C_t) + v(m_t)]` of lifetime utility (O&R (91), p. 579). -/
def utilTerm (K : Kernel S) (β : ℝ) (u v : ℝ → ℝ) (A : AssetMarket S J) (h₀ : Hist S)
    (C : Hist S → ℝ) (a : J → Hist S → ℝ) (t : ℕ) : ℝ :=
  β ^ t * iterStep K.trans t (fun g => u (C g) + v (services A a g)) h₀

/-- **Lifetime expected utility** `E₀ Σ_t βᵗ [u(C_t) + v(M_t/P_t)]` over the whole
infinite event tree (O&R (91), p. 579). -/
noncomputable def lifetimeU (K : Kernel S) (β : ℝ) (u v : ℝ → ℝ) (A : AssetMarket S J)
    (h₀ : Hist S) (C : Hist S → ℝ) (a : J → Hist S → ℝ) : ℝ :=
  ∑' t, utilTerm K β u v A h₀ C a t

/-- **The Euler equations for every asset at every node** (O&R (93), (95), (96), (98),
pp. 580–581): `p_j u′(C) = s_j v′(m) + β E_t[u′(C_{t+1}) R_{j,t+1}]`. -/
def Euler (K : Kernel S) (β : ℝ) (u' v' : ℝ → ℝ) (A : AssetMarket S J) (h₀ : Hist S)
    (C : Hist S → ℝ) (a : J → Hist S → ℝ) : Prop :=
  ∀ g, Desc h₀ g → ∀ j, A.price j g * u' (C g)
    = A.service j g * v' (services A a g)
      + β * oneStep K.trans (fun g' => u' (C g') * A.payoff j g') g

/-- The marginal-utility value at date `T+1` of the portfolio `b` carried out of date `T`:
`β^{T+1} E₀[u′(C_{T+1}) Σ_j R_{j,T+1} b_{j,T}]` (O&R fn 31, p. 542, in the stochastic
model). -/
def contValue (K : Kernel S) (β : ℝ) (u' : ℝ → ℝ) (A : AssetMarket S J) (h₀ : Hist S)
    (C : Hist S → ℝ) (b : J → Hist S → ℝ) (T : ℕ) : ℝ :=
  β ^ (T + 1) * iterStep K.trans (T + 1)
    (fun g => u' (C g) * ∑ j, A.payoff j g * b j (anc g)) h₀

/-- **The no-Ponzi condition** for a rival portfolio, valued with the candidate's marginal
utilities: `liminf_T contValue ≥ 0` (O&R §8.7; fn 31, p. 542). -/
def NoPonzi (K : Kernel S) (β : ℝ) (u' : ℝ → ℝ) (A : AssetMarket S J) (h₀ : Hist S)
    (C : Hist S → ℝ) (b : J → Hist S → ℝ) : Prop :=
  ∀ ε > 0, ∀ᶠ T in atTop, -ε ≤ contValue K β u' A h₀ C b T

/-- **The stochastic transversality condition** for the candidate plan (O&R fn 31, p. 542,
in the stochastic model of §8.7). -/
def TVCHousehold (K : Kernel S) (β : ℝ) (u' : ℝ → ℝ) (A : AssetMarket S J) (h₀ : Hist S)
    (C : Hist S → ℝ) (a : J → Hist S → ℝ) : Prop :=
  Tendsto (contValue K β u' A h₀ C a) atTop (𝓝 0)

/-- Nonnegative financial wealth (no net debt) at every node implies the no-Ponzi
condition (O&R §8.7: a natural admissibility requirement). -/
theorem noPonzi_of_nonneg_wealth (K : Kernel S) {β : ℝ} (hβ : 0 ≤ β) {u' : ℝ → ℝ}
    (A : AssetMarket S J) (h₀ : Hist S) {C : Hist S → ℝ} {b : J → Hist S → ℝ}
    (hu' : ∀ g, Desc h₀ g → 0 ≤ u' (C g))
    (hw : ∀ g, Desc h₀ g → 0 ≤ ∑ j, A.payoff j g * b j (anc g)) :
    NoPonzi K β u' A h₀ C b := by
  intro ε hε
  refine Filter.Eventually.of_forall fun T => ?_
  have : 0 ≤ contValue K β u' A h₀ C b T := by
    unfold contValue
    have h0 := iterStep_mono_desc K.trans_nonneg (T + 1) (X := fun _ => (0 : ℝ))
      (Y := fun g => u' (C g) * ∑ j, A.payoff j g * b j (anc g)) (h := h₀)
      (fun g hg => mul_nonneg (hu' g hg) (hw g hg))
    rw [iterStep_const K.trans_sum] at h0
    exact mul_nonneg (pow_nonneg hβ _) h0
  linarith

/-- **Sufficiency: the Euler equations plus the transversality condition imply global
optimality over whole plans** (O&R §8.7.1–8.7.2, pp. 579–582; the stochastic version of
the supporting-hyperplane argument). If `(C, a)` is feasible, positive, satisfies the Euler
equations for every asset at every node and the transversality condition, then its lifetime
utility is at least that of EVERY feasible positive rival `(C′, a′)` satisfying the no-Ponzi
condition (both lifetime utilities summable). -/
theorem household_sufficiency (K : Kernel S) (A : AssetMarket S J) {β : ℝ} (hβ : 0 ≤ β)
    {u u' v v' : ℝ → ℝ} (hcu : ConcaveOn ℝ (Set.Ioi 0) u)
    (hdu : ∀ x, 0 < x → HasDerivAt u (u' x) x) (hcv : ConcaveOn ℝ (Set.Ioi 0) v)
    (hdv : ∀ x, 0 < x → HasDerivAt v (v' x) x) {h₀ : Hist S} {W₀ : ℝ}
    {C C' : Hist S → ℝ} {a a' : J → Hist S → ℝ}
    (hF : Feasible A h₀ W₀ C a) (hF' : Feasible A h₀ W₀ C' a')
    (hP : Positive A h₀ C a) (hP' : Positive A h₀ C' a')
    (hE : Euler K β u' v' A h₀ C a) (htvc : TVCHousehold K β u' A h₀ C a)
    (hnp : NoPonzi K β u' A h₀ C a')
    (hs : Summable (utilTerm K β u v A h₀ C a))
    (hs' : Summable (utilTerm K β u v A h₀ C' a')) :
    lifetimeU K β u v A h₀ C' a' ≤ lifetimeU K β u v A h₀ C a := by
  -- notation
  set x : J → Hist S → ℝ := fun j g => a' j g - a j g
  set dU : Hist S → ℝ := fun g =>
    (u (C' g) + v (services A a' g)) - (u (C g) + v (services A a g))
  set LI : Hist S → ℝ := fun g => u' (C g) * ∑ j, A.payoff j g * x j (anc g)
  set H : Hist S → ℝ := fun g =>
    ∑ j, x j g * (A.service j g * v' (services A a g) - A.price j g * u' (C g))
  -- the tangent inequality at a node
  have tang : ∀ g, Desc h₀ g → dU g ≤ u' (C g) * (C' g - C g)
      + v' (services A a g) * (services A a' g - services A a g) := fun g hg => by
    have t1 := concave_tangent hcu hdu (hP g hg).1 (hP' g hg).1
    have t2 := concave_tangent hcv hdv (hP g hg).2 (hP' g hg).2
    simp only [dU]; linarith
  have hserv : ∀ g, services A a' g - services A a g = ∑ j, A.service j g * x j g := fun g => by
    simp only [services, x, ← Finset.sum_sub_distrib, mul_sub]
  -- (P1) at the root
  have P1 : dU h₀ ≤ H h₀ := by
    have hb : C' h₀ - C h₀ = -∑ j, A.price j h₀ * x j h₀ := by
      simp only [x, mul_sub, Finset.sum_sub_distrib]; linarith [hF.1, hF'.1]
    have key : u' (C h₀) * (C' h₀ - C h₀)
        + v' (services A a h₀) * (services A a' h₀ - services A a h₀) = H h₀ := by
      rw [hb, hserv]
      simp only [H, Finset.mul_sum, ← Finset.sum_neg_distrib, mul_neg, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    linarith [tang h₀ (desc_refl h₀)]
  -- (P2) at a child of a descendant
  have P2 : ∀ g, Desc h₀ g → ∀ s, dU (next g s) ≤ LI (next g s) + H (next g s) := by
    intro g hg s
    have hg' := desc_next hg s
    have hb : C' (next g s) - C (next g s) = -∑ j, A.price j (next g s) * x j (next g s)
        + ∑ j, A.payoff j (next g s) * x j g := by
      simp only [x, mul_sub, Finset.sum_sub_distrib]
      linarith [hF.2 g hg s, hF'.2 g hg s]
    have key : u' (C (next g s)) * (C' (next g s) - C (next g s))
        + v' (services A a (next g s)) * (services A a' (next g s) - services A a (next g s))
        = LI (next g s) + H (next g s) := by
      rw [hb, hserv]
      simp only [LI, H, anc_next, mul_add, Finset.mul_sum, ← Finset.sum_neg_distrib, mul_neg,
        ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    linarith [tang _ hg']
  -- (P3) the Euler equations turn `H` into a one-step-ahead expectation
  have P3 : ∀ g, Desc h₀ g → H g = -β * oneStep K.trans LI g := fun g hg => by
    have hEg := hE g hg
    have e : ∀ j, A.service j g * v' (services A a g) - A.price j g * u' (C g)
        = -β * oneStep K.trans (fun g' => u' (C g') * A.payoff j g') g := fun j => by
      rw [hEg j]; ring
    simp only [H, e, LI, oneStep, anc_next, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun j _ => by ring
  -- the telescoping bound on partial sums
  have tele : ∀ T : ℕ, ∑ t ∈ Finset.range (T + 1), β ^ t * iterStep K.trans t dU h₀
      ≤ -(β ^ (T + 1) * iterStep K.trans (T + 1) LI h₀) := by
    intro T
    induction T with
    | zero =>
      simp only [zero_add, Finset.sum_range_one, pow_zero, one_mul, pow_one]
      have := P3 h₀ (desc_refl h₀)
      change dU h₀ ≤ -(β * oneStep K.trans LI h₀)
      linarith [P1]
    | succ T ih =>
      rw [Finset.sum_range_succ]
      have hstep : iterStep K.trans (T + 1) dU h₀
          ≤ iterStep K.trans (T + 1) LI h₀ - β * iterStep K.trans (T + 2) LI h₀ := by
        rw [iterStep_succ]
        have h1 : iterStep K.trans T (oneStep K.trans dU) h₀
            ≤ iterStep K.trans T (oneStep K.trans (fun g => LI g + H g)) h₀ :=
          iterStep_mono_desc K.trans_nonneg T fun g hg =>
            Finset.sum_le_sum fun s _ =>
              mul_le_mul_of_nonneg_left (P2 g hg s) (K.trans_nonneg _ _)
        have h2 : iterStep K.trans T (oneStep K.trans (fun g => LI g + H g)) h₀
            = iterStep K.trans (T + 1) LI h₀ + iterStep K.trans (T + 1) H h₀ := by
          rw [← iterStep_succ, iterStep_add_fun]
        have h3 : iterStep K.trans (T + 1) H h₀ = -β * iterStep K.trans (T + 2) LI h₀ := by
          rw [iterStep_congr_desc K.trans (T + 1)
            (Y := fun g => -β * oneStep K.trans LI g) fun g hg => P3 g hg,
            iterStep_mul_left, ← iterStep_succ]
        linarith
      have hβT : 0 ≤ β ^ (T + 1) := pow_nonneg hβ _
      have := mul_le_mul_of_nonneg_left hstep hβT
      calc ∑ t ∈ Finset.range (T + 1), β ^ t * iterStep K.trans t dU h₀
            + β ^ (T + 1) * iterStep K.trans (T + 1) dU h₀
          ≤ -(β ^ (T + 1) * iterStep K.trans (T + 1) LI h₀)
            + β ^ (T + 1) * (iterStep K.trans (T + 1) LI h₀
              - β * iterStep K.trans (T + 2) LI h₀) := add_le_add ih this
        _ = -(β ^ (T + 1 + 1) * iterStep K.trans (T + 1 + 1) LI h₀) := by ring
  -- the terminal term is the difference of continuation values
  have hLIc : ∀ T, β ^ (T + 1) * iterStep K.trans (T + 1) LI h₀
      = contValue K β u' A h₀ C a' T - contValue K β u' A h₀ C a T := fun T => by
    simp only [contValue, ← mul_sub]
    rw [← iterStep_sub_fun]
    congr 2; funext g
    simp only [LI, x, mul_sub, Finset.sum_sub_distrib]
  -- lifetime utility difference as a limit of partial sums
  have hdiff : ∀ t, utilTerm K β u v A h₀ C' a' t - utilTerm K β u v A h₀ C a t
      = β ^ t * iterStep K.trans t dU h₀ := fun t => by
    simp only [utilTerm, ← mul_sub, ← iterStep_sub_fun]
    rfl
  have hlim : Tendsto (fun T => ∑ t ∈ Finset.range (T + 1), β ^ t * iterStep K.trans t dU h₀)
      atTop (𝓝 (lifetimeU K β u v A h₀ C' a' - lifetimeU K β u v A h₀ C a)) := by
    have := ((hs'.sub hs).hasSum.tendsto_sum_nat).comp (tendsto_add_atTop_nat 1)
    simp only [lifetimeU, ← (hs'.tsum_sub hs)]
    refine this.congr fun T => ?_
    simp only [Function.comp, hdiff]
  -- conclude
  by_contra hcon
  push Not at hcon
  set D := lifetimeU K β u v A h₀ C' a' - lifetimeU K β u v A h₀ C a with hD
  have hDpos : 0 < D := by simp only [hD]; linarith
  have e1 : ∀ᶠ T in atTop, D / 2 < ∑ t ∈ Finset.range (T + 1), β ^ t * iterStep K.trans t dU h₀ :=
    hlim.eventually (lt_mem_nhds (by linarith))
  have e2 : ∀ᶠ T in atTop, contValue K β u' A h₀ C a T < D / 4 :=
    htvc.eventually (gt_mem_nhds (by linarith))
  have e3 := hnp (D / 4) (by linarith)
  obtain ⟨T, h1, h2, h3⟩ := (e1.and (e2.and e3)).exists
  have := tele T
  rw [hLIc T] at this
  linarith

/-- **The transversality condition in holdings form** (O&R fn 31, p. 542): under the Euler
equations, `contValue_T(a) = βᵀ E₀[Σ_j a_{j,T} (p_j u′(C_T) − s_j v′(m_T))]`, the
marginal-utility value of the portfolio held at date `T`. -/
theorem contValue_eq_holdings (K : Kernel S) (A : AssetMarket S J) {β : ℝ} {u' v' : ℝ → ℝ}
    {h₀ : Hist S} {C : Hist S → ℝ} {a : J → Hist S → ℝ} (hE : Euler K β u' v' A h₀ C a)
    (T : ℕ) :
    contValue K β u' A h₀ C a T = β ^ T * iterStep K.trans T (fun g => ∑ j, a j g
      * (A.price j g * u' (C g) - A.service j g * v' (services A a g))) h₀ := by
  unfold contValue
  rw [iterStep_succ, pow_succ, mul_assoc, ← iterStep_mul_left]
  congr 1
  refine iterStep_congr_desc K.trans T fun g hg => ?_
  have e : ∀ j, A.price j g * u' (C g) - A.service j g * v' (services A a g)
      = β * oneStep K.trans (fun g' => u' (C g') * A.payoff j g') g := fun j => by
    rw [hE g hg j]; ring
  simp only [e, oneStep, anc_next, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun j _ => by ring

omit [Fintype S] in
/-- A node whose parent is `g` but which is not `g` is one period later (O&R §8.7.1). -/
theorem depth_of_anc_eq {g g'' : Hist S} (ha : anc g'' = g) (hne : g'' ≠ g) :
    depth g'' = depth g + 1 := by
  obtain ⟨s, _ | ⟨t, past⟩⟩ := g''
  · exact absurd ha hne
  · subst ha; rfl

omit [Fintype S] in
/-- A node whose parent is `g` but which is not `g` is a child of `g` (O&R §8.7.1). -/
theorem eq_next_of_anc_eq {g g'' : Hist S} (ha : anc g'' = g) (hne : g'' ≠ g) :
    g'' = next g g''.1 := by
  obtain ⟨s, _ | ⟨t, past⟩⟩ := g''
  · exact absurd ha hne
  · subst ha; rfl

omit [Fintype S] in
/-- A child is never its parent (O&R §8.7.1). -/
theorem next_ne (g : Hist S) (s : S) : next g s ≠ g := fun h => by
  have := congrArg depth h
  rw [depth_next] at this
  omega

omit [Fintype S] in
/-- A non-root node is one period after its parent (O&R §8.7.1). -/
theorem depth_anc {g : Hist S} (hg : 1 ≤ depth g) : depth (anc g) + 1 = depth g := by
  obtain ⟨s, _ | ⟨t, past⟩⟩ := g
  · simp [depth] at hg
  · rfl

omit [Fintype S] in
/-- Descendants are weakly later (O&R §8.7.1). -/
theorem depth_le_of_desc {h g : Hist S} (hd : Desc h g) : depth h ≤ depth g := by
  obtain ⟨l, rfl⟩ := hd
  rw [depth_extend]; omega

variable [DecidableEq S] [DecidableEq J]

/-- The probability of reaching `g` from `h₀` (O&R §8.7.1). -/
def reachProb (K : Kernel S) (h₀ g : Hist S) : ℝ :=
  iterStep K.trans (depth g - depth h₀) (fun g'' => if g'' = g then 1 else 0) h₀

/-- The root is reached with probability one (O&R §8.7.1). -/
theorem reachProb_self (K : Kernel S) (h₀ : Hist S) : reachProb K h₀ h₀ = 1 := by
  simp [reachProb, iterStep]

/-- **Reach probabilities multiply along the tree** (O&R §8.7.1): the probability of the
child `next g s` is that of `g` times the transition probability. -/
theorem reachProb_next (K : Kernel S) {h₀ g : Hist S} (hg : Desc h₀ g) (s : S) :
    reachProb K h₀ (next g s) = reachProb K h₀ g * K.trans g.1 s := by
  have hd := depth_le_of_desc hg
  unfold reachProb
  rw [depth_next, show depth g + 1 - depth h₀ = (depth g - depth h₀) + 1 by omega,
    iterStep_succ]
  rw [iterStep_congr_depth K.trans _ (Y := fun g'' => K.trans g.1 s
    * (if g'' = g then 1 else 0)) fun g'' hg'' => ?_, iterStep_mul_left, mul_comm]
  simp only [oneStep]
  by_cases he : g'' = g
  · subst he
    rw [Finset.sum_eq_single s]
    · simp
    · intro b _ hb
      have : next g'' b ≠ next g'' s := fun h => hb (by simpa [next] using congrArg Prod.fst h)
      simp [this]
    · simp
  · simp only [he, ↓reduceIte, mul_zero]
    refine Finset.sum_eq_zero fun b _ => ?_
    have : next g'' b ≠ next g s := fun h => he (by
      have := congrArg anc h; simpa [anc_next] using this)
    simp [this]

/-- The one-node perturbation of consumption: buy `δ` more units of asset `j` at node `g`,
paying from consumption at `g`, and consume the payoff at every child of `g`
(O&R (93), p. 580). -/
def perturbC (A : AssetMarket S J) (C : Hist S → ℝ) (g : Hist S) (j : J) (δ : ℝ) :
    Hist S → ℝ :=
  fun g'' => C g'' - (if g'' = g then A.price j g * δ else 0)
    + (if anc g'' = g ∧ g'' ≠ g then A.payoff j g'' * δ else 0)

/-- The one-node perturbation of the portfolio (O&R (93), p. 580). -/
def perturbA (a : J → Hist S → ℝ) (g : Hist S) (j : J) (δ : ℝ) : J → Hist S → ℝ :=
  fun j' g'' => a j' g'' + (if j' = j ∧ g'' = g then δ else 0)

/-- Liquidity services under the perturbation (O&R (98), p. 581). -/
theorem services_perturbA (A : AssetMarket S J) (a : J → Hist S → ℝ) (g : Hist S) (j : J)
    (δ : ℝ) (g'' : Hist S) :
    services A (perturbA a g j δ) g''
      = services A a g'' + (if g'' = g then A.service j g * δ else 0) := by
  by_cases hg : g'' = g
  · subst hg
    simp [services, perturbA, mul_add, Finset.sum_add_distrib]
  · simp [services, perturbA, hg]

/-- **The perturbed plan satisfies the budget constraints** (O&R (93), p. 580). -/
theorem feasible_perturb (A : AssetMarket S J) {h₀ : Hist S} {W₀ : ℝ} {C : Hist S → ℝ}
    {a : J → Hist S → ℝ} (hF : Feasible A h₀ W₀ C a) {g : Hist S} (hg : Desc h₀ g) (j : J)
    (δ : ℝ) : Feasible A h₀ W₀ (perturbC A C g j δ) (perturbA a g j δ) := by
  constructor
  · by_cases hr : h₀ = g
    · subst hr
      have := hF.1
      simp [perturbC, perturbA, mul_add, Finset.sum_add_distrib] at this ⊢
      linarith
    · have hnot : ¬ (anc h₀ = g ∧ h₀ ≠ g) := fun ⟨ha, hne⟩ => by
        have := depth_of_anc_eq ha hne
        have := depth_le_of_desc hg
        omega
      simp only [perturbC, perturbA, hr, hnot, and_false, ↓reduceIte, add_zero, sub_zero]
      exact hF.1
  · intro g'' hg'' s
    have hb := hF.2 g'' hg'' s
    have hn : g'' ≠ next g'' s := (next_ne g'' s).symm
    by_cases h1 : next g'' s = g
    · subst h1
      simp [perturbC, perturbA, hn, anc_next, mul_add, Finset.sum_add_distrib] at hb ⊢
      linarith
    · by_cases h2 : g'' = g
      · subst h2
        simp [perturbC, perturbA, h1, anc_next, mul_add, Finset.sum_add_distrib] at hb ⊢
        linarith
      · simp [perturbC, perturbA, h1, h2, anc_next] at hb ⊢
        linarith

/-- The one-period value of the perturbation at `g` (O&R (93), (98), pp. 580–581). -/
def localValue (K : Kernel S) (β : ℝ) (u v : ℝ → ℝ) (A : AssetMarket S J)
    (C : Hist S → ℝ) (a : J → Hist S → ℝ) (g : Hist S) (j : J) (δ : ℝ) : ℝ :=
  u (C g - A.price j g * δ) + v (services A a g + A.service j g * δ)
    + β * ∑ s, K.trans g.1 s * u (C (next g s) + A.payoff j (next g s) * δ)

/-- **The lifetime-utility effect of a one-node perturbation**
`U(δ) − U(0) = β^d ρ(g) [φ(δ) − φ(0)]`, with `d` the date and `ρ(g)` the reach probability of
the node (O&R (93), p. 580). -/
theorem lifetimeU_perturb (K : Kernel S) (A : AssetMarket S J) (β : ℝ) (u v : ℝ → ℝ)
    {h₀ : Hist S} {C : Hist S → ℝ} {a : J → Hist S → ℝ} {g : Hist S} (hg : Desc h₀ g) (j : J)
    (δ : ℝ) (hs : Summable (utilTerm K β u v A h₀ C a)) :
    Summable (utilTerm K β u v A h₀ (perturbC A C g j δ) (perturbA a g j δ)) ∧
      lifetimeU K β u v A h₀ (perturbC A C g j δ) (perturbA a g j δ)
        - lifetimeU K β u v A h₀ C a
      = β ^ (depth g - depth h₀) * reachProb K h₀ g
        * (localValue K β u v A C a g j δ - localValue K β u v A C a g j 0) := by
  set d := depth g - depth h₀
  have hdg : depth g = depth h₀ + d := by have := depth_le_of_desc hg; omega
  set dU : Hist S → ℝ := fun g'' =>
    (u (perturbC A C g j δ g'') + v (services A (perturbA a g j δ) g''))
      - (u (C g'') + v (services A a g''))
  have hzero : ∀ g'', g'' ≠ g → ¬ (anc g'' = g ∧ g'' ≠ g) → dU g'' = 0 := fun g'' h1 h2 => by
    simp only [dU, perturbC, services_perturbA, h1, h2, ↓reduceIte, sub_zero, add_zero]
    ring
  have hterm : utilTerm K β u v A h₀ (perturbC A C g j δ) (perturbA a g j δ)
      = fun t => utilTerm K β u v A h₀ C a t + β ^ t * iterStep K.trans t dU h₀ := by
    funext t
    simp only [utilTerm, ← mul_add, ← iterStep_add_fun]
    congr 2; funext g''; simp only [dU]; ring
  have hat_d : iterStep K.trans d dU h₀ = reachProb K h₀ g * dU g := by
    rw [iterStep_congr_depth K.trans d (Y := fun g'' => dU g * (if g'' = g then 1 else 0))
      (fun g'' hg'' => by
        by_cases he : g'' = g
        · subst he; simp
        · simp only [he, ↓reduceIte, mul_zero]
          refine hzero g'' he fun ⟨ha, hne⟩ => ?_
          have := depth_of_anc_eq ha hne
          omega), iterStep_mul_left, mul_comm]
    rfl
  have hat_d1 : iterStep K.trans (d + 1) dU h₀ = reachProb K h₀ g * oneStep K.trans dU g := by
    rw [iterStep_succ, iterStep_congr_depth K.trans d
      (Y := fun g'' => oneStep K.trans dU g * (if g'' = g then 1 else 0))
      (fun g'' hg'' => by
        by_cases he : g'' = g
        · subst he; simp
        · simp only [he, ↓reduceIte, mul_zero]
          refine Finset.sum_eq_zero fun b _ => ?_
          have h1 : next g'' b ≠ g := fun h => by
            have := congrArg depth h; rw [depth_next] at this; omega
          have h2 : ¬ (anc (next g'' b) = g ∧ next g'' b ≠ g) := fun ⟨ha, _⟩ =>
            he (by rwa [anc_next] at ha)
          rw [hzero _ h1 h2, mul_zero]), iterStep_mul_left, mul_comm]
    rfl
  have hat_o : ∀ t, t ≠ d → t ≠ d + 1 → iterStep K.trans t dU h₀ = 0 := fun t ht ht1 => by
    rw [iterStep_congr_depth K.trans t (Y := fun _ => 0) (fun g'' hg'' => by
      refine hzero g'' (fun h => ht (by subst h; omega)) fun ⟨ha, hne⟩ => ?_
      have := depth_of_anc_eq ha hne
      exact ht1 (by omega)), iterStep_const K.trans_sum]
  have hsupp : ∀ t ∉ ({d, d + 1} : Finset ℕ), β ^ t * iterStep K.trans t dU h₀ = 0 := by
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ht
    rw [hat_o t ht.1 ht.2, mul_zero]
  have hsum2 : Summable fun t => β ^ t * iterStep K.trans t dU h₀ :=
    summable_of_ne_finset_zero hsupp
  refine ⟨?_, ?_⟩
  · rw [hterm]; exact hs.add hsum2
  · unfold lifetimeU
    rw [hterm, hs.tsum_add hsum2, add_sub_cancel_left, tsum_eq_sum hsupp,
      Finset.sum_pair (by omega : d ≠ d + 1), hat_d, hat_d1]
    have hg1 : dU g = u (C g - A.price j g * δ) + v (services A a g + A.service j g * δ)
        - (u (C g) + v (services A a g)) := by
      have : ¬ (anc g = g ∧ g ≠ g) := fun ⟨_, h⟩ => h rfl
      simp only [dU, perturbC, services_perturbA, this, ↓reduceIte, add_zero]
    have hg2 : oneStep K.trans dU g = ∑ s, K.trans g.1 s
        * u (C (next g s) + A.payoff j (next g s) * δ)
        - ∑ s, K.trans g.1 s * u (C (next g s)) := by
      simp only [oneStep, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun s _ => ?_
      have h1 : next g s ≠ g := next_ne g s
      have h2 : anc (next g s) = g ∧ next g s ≠ g := ⟨anc_next g s, h1⟩
      simp only [dU, perturbC, services_perturbA, h1, ↓reduceIte, sub_zero, add_zero]
      rw [ite_eq_left_of_eq_true _ _ (eq_true h2)]
      ring
    rw [hg1, hg2]
    simp only [localValue, mul_zero, sub_zero, add_zero]
    rw [pow_succ]
    ring

omit [DecidableEq J] in
/-- **Necessity of the Euler equations** (O&R (93), (95), (96), (98), pp. 580–581): if a
feasible, positive plan satisfying the transversality condition is optimal against every
admissible rival (feasible, positive, no-Ponzi, summable utility), then the Euler equation
holds for every asset at every node reached with positive probability. -/
theorem household_euler_necessary (K : Kernel S) (A : AssetMarket S J) {β : ℝ} (hβ : 0 < β)
    {u u' v v' : ℝ → ℝ} (hdu : ∀ x, 0 < x → HasDerivAt u (u' x) x)
    (hdv : ∀ x, 0 < x → HasDerivAt v (v' x) x) {h₀ : Hist S} {W₀ : ℝ} {C : Hist S → ℝ}
    {a : J → Hist S → ℝ} (hF : Feasible A h₀ W₀ C a) (hP : Positive A h₀ C a)
    (htvc : TVCHousehold K β u' A h₀ C a) (hs : Summable (utilTerm K β u v A h₀ C a))
    (hopt : ∀ C' a', Feasible A h₀ W₀ C' a' → Positive A h₀ C' a' →
      NoPonzi K β u' A h₀ C a' → Summable (utilTerm K β u v A h₀ C' a') →
      lifetimeU K β u v A h₀ C' a' ≤ lifetimeU K β u v A h₀ C a)
    {g : Hist S} (hg : Desc h₀ g) (hρ : 0 < reachProb K h₀ g) (j : J) :
    A.price j g * u' (C g) = A.service j g * v' (services A a g)
      + β * oneStep K.trans (fun g' => u' (C g') * A.payoff j g') g := by
  classical
  set d := depth g - depth h₀
  have hdg : depth g = depth h₀ + d := by have := depth_le_of_desc hg; omega
  -- positivity of the perturbed plan near `δ = 0`
  have ev1 : ∀ᶠ δ in 𝓝 (0 : ℝ), 0 < C g - A.price j g * δ := by
    have hc : Continuous fun δ : ℝ => C g - A.price j g * δ := by fun_prop
    exact continuousAt_const.eventually_lt hc.continuousAt (by simpa using (hP g hg).1)
  have ev2 : ∀ᶠ δ in 𝓝 (0 : ℝ), 0 < services A a g + A.service j g * δ := by
    have hc : Continuous fun δ : ℝ => services A a g + A.service j g * δ := by fun_prop
    exact continuousAt_const.eventually_lt hc.continuousAt (by simpa using (hP g hg).2)
  have ev3 : ∀ᶠ δ in 𝓝 (0 : ℝ), ∀ s, 0 < C (next g s) + A.payoff j (next g s) * δ := by
    refine Filter.eventually_all.2 fun s => ?_
    have hc : Continuous fun δ : ℝ => C (next g s) + A.payoff j (next g s) * δ := by fun_prop
    exact continuousAt_const.eventually_lt hc.continuousAt
      (by simpa using (hP _ (desc_next hg s)).1)
  have hloc : IsLocalMax (localValue K β u v A C a g j) 0 := by
    filter_upwards [ev1, ev2, ev3] with δ h1 h2 h3
    have hPos : Positive A h₀ (perturbC A C g j δ) (perturbA a g j δ) := by
      intro g'' hg''
      rw [services_perturbA]
      by_cases he : g'' = g
      · subst he
        have : ¬ (anc g'' = g'' ∧ g'' ≠ g'') := fun ⟨_, h⟩ => h rfl
        simp only [perturbC, this, ↓reduceIte, add_zero]
        exact ⟨h1, h2⟩
      · simp only [he, ↓reduceIte, add_zero]
        refine ⟨?_, (hP g'' hg'').2⟩
        by_cases hc : anc g'' = g ∧ g'' ≠ g
        · have hval : perturbC A C g j δ g'' = C g'' + A.payoff j g'' * δ := by
            simp only [perturbC, he, ↓reduceIte, sub_zero]
            rw [ite_eq_left_of_eq_true _ _ (eq_true hc)]
          have := eq_next_of_anc_eq hc.1 hc.2
          rw [hval, this]; exact h3 _
        · simp only [perturbC, he, hc, ↓reduceIte, sub_zero, add_zero]
          exact (hP g'' hg'').1
    have hNP : NoPonzi K β u' A h₀ C (perturbA a g j δ) := by
      intro ε hε
      have hev := htvc.eventually (lt_mem_nhds (show -ε < 0 by linarith))
      filter_upwards [hev, Filter.eventually_gt_atTop d] with T hT hTd
      have heq : contValue K β u' A h₀ C (perturbA a g j δ) T = contValue K β u' A h₀ C a T := by
        unfold contValue
        congr 1
        refine iterStep_congr_depth K.trans _ fun g'' hg'' => ?_
        have hne : anc g'' ≠ g := fun h => by
          have h1 := depth_anc (g := g'') (by omega)
          rw [h] at h1; omega
        simp only [perturbA, hne, and_false, ↓reduceIte, add_zero]
      rw [heq]; exact hT.le
    have hper := lifetimeU_perturb K A β u v hg j δ hs
    have := hopt _ _ (feasible_perturb A hF hg j δ) hPos hNP hper.1
    have hpos : 0 < β ^ d * reachProb K h₀ g := mul_pos (pow_pos hβ _) hρ
    have h4 : β ^ d * reachProb K h₀ g * (localValue K β u v A C a g j δ
        - localValue K β u v A C a g j 0) ≤ 0 := by rw [← hper.2]; linarith
    have := (mul_nonpos_iff_pos_imp_nonpos.1 h4).1 hpos
    linarith
  -- the derivative of the local value
  have hderiv : HasDerivAt (localValue K β u v A C a g j)
      (-(A.price j g * u' (C g)) + A.service j g * v' (services A a g)
        + β * ∑ s, K.trans g.1 s * (u' (C (next g s)) * A.payoff j (next g s))) 0 := by
    have hc1 : HasDerivAt (fun δ : ℝ => C g - A.price j g * δ) (-A.price j g) 0 := by
      simpa using HasDerivAt.const_sub (C g) (HasDerivAt.const_mul (A.price j g)
        (hasDerivAt_id' (0 : ℝ)))
    have hc2 : HasDerivAt (fun δ : ℝ => services A a g + A.service j g * δ)
        (A.service j g) 0 := by
      simpa using HasDerivAt.const_add (services A a g) (HasDerivAt.const_mul (A.service j g)
        (hasDerivAt_id' (0 : ℝ)))
    have d1 := HasDerivAt.comp_of_eq 0 (hdu (C g) (hP g hg).1) hc1 (by simp)
    have d2 := HasDerivAt.comp_of_eq 0 (hdv _ (hP g hg).2) hc2 (by simp)
    have d3 : HasDerivAt (fun δ => ∑ s, K.trans g.1 s * u (C (next g s)
        + A.payoff j (next g s) * δ))
        (∑ s, K.trans g.1 s * (u' (C (next g s)) * A.payoff j (next g s))) 0 := by
      apply HasDerivAt.fun_sum
      intro s _
      have hcs : HasDerivAt (fun δ : ℝ => C (next g s) + A.payoff j (next g s) * δ)
          (A.payoff j (next g s)) 0 := by
        simpa using HasDerivAt.const_add (C (next g s))
          (HasDerivAt.const_mul (A.payoff j (next g s)) (hasDerivAt_id' (0 : ℝ)))
      exact HasDerivAt.const_mul _ (HasDerivAt.comp_of_eq 0
        (hdu _ (hP _ (desc_next hg s)).1) hcs (by simp))
    have := HasDerivAt.add (HasDerivAt.add d1 d2) (HasDerivAt.const_mul β d3)
    exact HasDerivAt.congr_deriv this (by ring)
  have h0 := hloc.hasDerivAt_eq_zero hderiv
  simp only [oneStep]
  linarith

end Household


/-! ## The §8.7 equilibrium plan is optimal for each household -/

namespace Equilibrium87

/-- **CRRA utility is concave**: `u′(C) = C^{−ρ}` with `ρ > 0` (O&R §8.7.3, p. 582). -/
theorem crra_concave {u : ℝ → ℝ} {ρ : ℝ} (hρ : 0 < ρ)
    (hdu : ∀ z, 0 < z → HasDerivAt u (z ^ (-ρ)) z) : ConcaveOn ℝ (Set.Ioi 0) u := by
  have hd : ∀ z ∈ Set.Ioi (0 : ℝ), deriv u z = z ^ (-ρ) := fun z hz => (hdu z hz).deriv
  refine AntitoneOn.concaveOn_of_deriv (convex_Ioi 0) ?_ ?_ ?_
  · exact fun z hz => (hdu z hz).continuousAt.continuousWithinAt
  · rw [interior_Ioi]; exact fun z hz => (hdu z hz).differentiableAt.differentiableWithinAt
  · rw [interior_Ioi]
    intro a ha b hb hab
    rw [hd a ha, hd b hb]
    exact Real.rpow_le_rpow_of_nonpos ha hab (by linarith)

variable {S : Type} [Fintype S]

/-- Equilibrium consumption `C = x Y^W` (O&R (94), p. 580). -/
def cons (x : ℝ) (y : S → ℝ) (h : Hist S) : ℝ := x * y h.1

/-- Marginal utility `u′(C) = (xY^W)^{−ρ}` (O&R §8.7.3). -/
noncomputable def lam (ρ x : ℝ) (y : S → ℝ) (h : Hist S) : ℝ := (x * y h.1) ^ (-ρ)

/-- The equilibrium price level `P = M(1 − β/(1+μ))(xY^W)^{−ρ}` (O&R p. 583). -/
noncomputable def price (β μ ρ x : ℝ) (y : S → ℝ) (M : Hist S → ℝ) (h : Hist S) : ℝ :=
  M h * (1 - β / (1 + μ)) * (x * y h.1) ^ (-ρ)

/-- The gross real interest rate that clears the real-bond market (O&R (96), p. 581):
`1 + r_t = u′(C_t)/(β E_t u′(C_{t+1}))`. -/
noncomputable def realRate (K : Kernel S) (β ρ x : ℝ) (y : S → ℝ) (g : Hist S) : ℝ :=
  lam ρ x y g / (β * oneStep K.trans (lam ρ x y) g)

/-- The dividend of the world output fund in marginal-utility units `u′(C) Y^W`
(O&R fn 64, p. 580). -/
noncomputable def divU (ρ x : ℝ) (y : S → ℝ) (h : Hist S) : ℝ := lam ρ x y h * y h.1

/-- The marginal-utility value of the output fund
`Σ_{n≥1} βⁿ E_t[u′(C_{t+n}) Y^W_{t+n}]` (O&R fn 64, p. 580). -/
noncomputable def fundU (K : Kernel S) (β ρ x : ℝ) (y : S → ℝ) (g : Hist S) : ℝ :=
  ∑' n : ℕ, β ^ (n + 1) * iterStep K.trans (n + 1) (divU ρ x y) g

/-- The output-fund price `q = fundU/u′(C)` (O&R fn 64, p. 580). -/
noncomputable def fundPrice (K : Kernel S) (β ρ x : ℝ) (y : S → ℝ) (g : Hist S) : ℝ :=
  fundU K β ρ x y g / lam ρ x y g

/-- **The §8.7 asset menu**: money (price, payoff and services `1/P`), the nominal bond
(`1 + i = (1+μ)/β`), the real bond (gross return `1 + r` set at the parent node) and the
world output fund (price `q`, payoff `q + Y^W`); endowment = the money transfer
`(M_t − M_{t−1})/P_t` (O&R §8.7.1–8.7.3, pp. 579–583). -/
noncomputable def market (K : Kernel S) (β μ ρ x : ℝ) (y : S → ℝ) (M : Hist S → ℝ) :
    Household.AssetMarket S (Fin 4) :=
  ⟨fun j h => ![1 / price β μ ρ x y M h, 1 / price β μ ρ x y M h, 1,
      fundPrice K β ρ x y h] j,
    fun j h => ![1 / price β μ ρ x y M h, ((1 + μ) / β) / price β μ ρ x y M h,
      realRate K β ρ x y (anc h), fundPrice K β ρ x y h + y h.1] j,
    fun j h => ![1 / price β μ ρ x y M h, 0, 0, 0] j,
    fun h => (M h - M (anc h)) / price β μ ρ x y M h⟩

/-- The equilibrium portfolio: the money stock, no bonds, and the constant share `x` of the
world output fund (O&R (94), p. 580). -/
def holdings (M : Hist S → ℝ) (x : ℝ) : Fin 4 → Hist S → ℝ := fun j h => ![M h, 0, 0, x] j

/-- The household's initial real wealth (O&R §8.7.1). -/
noncomputable def wealth0 (K : Kernel S) (β μ ρ x : ℝ) (y : S → ℝ) (M : Hist S → ℝ)
    (h₀ : Hist S) : ℝ :=
  cons x y h₀ + M h₀ / price β μ ρ x y M h₀ + fundPrice K β ρ x y h₀ * x

namespace Lemmas

variable {K : Kernel S} {y ε : S → ℝ} {β μ ρ x : ℝ} {M : Hist S → ℝ}

omit [Fintype S] in
/-- `u′(C)/P = 1/(M(1 − β/(1+μ)))` (O&R p. 583). -/
theorem lam_div_price (hy : ∀ s, 0 < y s) (hx : 0 < x) (h : Hist S) :
    lam ρ x y h * (1 / price β μ ρ x y M h) = 1 / (M h * (1 - β / (1 + μ))) := by
  have : 0 < (x * y h.1) ^ (-ρ) := Real.rpow_pos_of_pos (mul_pos hx (hy _)) _
  simp only [lam, price]
  field_simp

/-- `E_t[u′(C_{t+1})/P_{t+1}] = 1/(M_t(1+μ)(1 − β/(1+μ)))` (O&R (99)–(100), p. 583). -/
theorem oneStep_lam_div_price (hy : ∀ s, 0 < y s) (hx : 0 < x) (hε : ∀ s, 0 < ε s)
    (hE : ∀ s, (K.row s).expect (fun s' => 1 / ε s') = 1) (hM : ∀ h, 0 < M h)
    (hμ : 0 < 1 + μ) (hγ : β / (1 + μ) < 1)
    (hgrowth : ∀ h s', M (next h s') = M h * (1 + μ) * ε s') (g : Hist S) :
    oneStep K.trans (fun g' => lam ρ x y g' * (1 / price β μ ρ x y M g')) g
      = 1 / (M g * (1 + μ) * (1 - β / (1 + μ))) := by
  have h1 : 0 < 1 - β / (1 + μ) := by linarith
  simp only [oneStep, lam_div_price hy hx, hgrowth]
  have e : ∀ s', K.trans g.1 s' * (1 / (M g * (1 + μ) * ε s' * (1 - β / (1 + μ))))
      = 1 / (M g * (1 + μ) * (1 - β / (1 + μ))) * (K.trans g.1 s' * (1 / ε s')) := fun s' => by
    have := hM g; have := hε s'
    field_simp
  simp only [e, ← Finset.mul_sum]
  have := hE g.1
  simp only [FinProb.expect, Kernel.row] at this
  rw [this, mul_one]

/-- The dividend in marginal-utility units is bounded (finite state space)
(O&R fn 64, p. 580). -/
theorem divU_bound (hy : ∀ s, 0 < y s) (hx : 0 < x) (h : Hist S) :
    0 ≤ divU ρ x y h ∧ divU ρ x y h ≤ ∑ s, (x * y s) ^ (-ρ) * y s := by
  have hpos : ∀ s, 0 ≤ (x * y s) ^ (-ρ) * y s := fun s =>
    mul_nonneg (Real.rpow_pos_of_pos (mul_pos hx (hy s)) _).le (hy s).le
  exact ⟨hpos h.1, Finset.single_le_sum (f := fun s => (x * y s) ^ (-ρ) * y s)
    (fun s _ => hpos s) (Finset.mem_univ _)⟩

/-- The terms of the fund value are summable and bounded (O&R fn 64, p. 580). -/
theorem fundU_terms (hy : ∀ s, 0 < y s) (hx : 0 < x) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (g : Hist S) :
    Summable (fun n : ℕ => β ^ (n + 1) * iterStep K.trans (n + 1) (divU ρ x y) g) ∧
      0 ≤ fundU K β ρ x y g ∧
      fundU K β ρ x y g ≤ (∑ s, (x * y s) ^ (-ρ) * y s) * (β / (1 - β)) := by
  set B := ∑ s, (x * y s) ^ (-ρ) * y s
  have hb : ∀ n, 0 ≤ iterStep K.trans n (divU ρ x y) g ∧ iterStep K.trans n (divU ρ x y) g ≤ B :=
    fun n => ⟨iterStep_nonneg K.trans_nonneg n (fun h => (divU_bound hy hx h).1) g, by
      have := iterStep_mono K.trans_nonneg n (X := divU ρ x y) (Y := fun _ => B)
        (fun h => (divU_bound hy hx h).2) g
      rwa [iterStep_const K.trans_sum] at this⟩
  have hgeo : Summable (fun n : ℕ => B * β * β ^ n) :=
    (summable_geometric_of_lt_one hβ0 hβ1).mul_left _
  have hle : ∀ n : ℕ, β ^ (n + 1) * iterStep K.trans (n + 1) (divU ρ x y) g ≤ B * β * β ^ n :=
    fun n => by
      rw [pow_succ]
      have := mul_le_mul_of_nonneg_left (hb (n + 1)).2 (pow_nonneg hβ0 n)
      nlinarith [pow_nonneg hβ0 n]
  have hnn : ∀ n : ℕ, 0 ≤ β ^ (n + 1) * iterStep K.trans (n + 1) (divU ρ x y) g :=
    fun n => mul_nonneg (pow_nonneg hβ0 _) (hb (n + 1)).1
  have hsum := Summable.of_nonneg_of_le hnn hle hgeo
  refine ⟨hsum, tsum_nonneg hnn, ?_⟩
  calc fundU K β ρ x y g ≤ ∑' n : ℕ, B * β * β ^ n := hsum.tsum_le_tsum hle hgeo
    _ = B * (β / (1 - β)) := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one hβ0 hβ1]; field_simp

/-- **The fund-pricing recursion** `fundU_t = β E_t[fundU_{t+1} + u′(C_{t+1})Y^W_{t+1}]`
(O&R (93) for the output fund, p. 580). -/
theorem fundU_recursion (hy : ∀ s, 0 < y s) (hx : 0 < x) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    (g : Hist S) :
    fundU K β ρ x y g = β * oneStep K.trans (fun g' => fundU K β ρ x y g' + divU ρ x y g') g := by
  have hs := fun g' => (fundU_terms (K := K) (ρ := ρ) hy hx hβ0 hβ1 g').1
  have h1 : oneStep K.trans (fundU K β ρ x y) g
      = ∑' n : ℕ, β ^ (n + 1) * iterStep K.trans (n + 1 + 1) (divU ρ x y) g := by
    rw [show fundU K β ρ x y = fun g' => ∑' n : ℕ, β ^ (n + 1)
      * iterStep K.trans (n + 1) (divU ρ x y) g' from rfl, oneStep_tsum K.trans hs]
    congr 1; funext n; rw [oneStep_mul_left, ← iterStep_succ']
  have h2 : fundU K β ρ x y g = β * oneStep K.trans (divU ρ x y) g
      + ∑' n : ℕ, β ^ (n + 1 + 1) * iterStep K.trans (n + 1 + 1) (divU ρ x y) g := by
    rw [fundU, (hs g).tsum_eq_zero_add]
    simp only [zero_add, pow_one]
    rfl
  rw [oneStep_add, h1, h2, mul_add, ← tsum_mul_left, add_comm]
  congr 1
  congr 1; funext n; ring

end Lemmas

open Lemmas

variable {K : Kernel S} {y ε : S → ℝ} {β μ ρ x : ℝ} {M : Hist S → ℝ}

/-- **The equilibrium plan satisfies all four Euler equations** (O&R (93), (95), (96),
(98), pp. 580–583) with `u′(C) = C^{−ρ}` and `v = log`. -/
theorem euler_holds (hy : ∀ s, 0 < y s) (hx : 0 < x) (hε : ∀ s, 0 < ε s)
    (hE : ∀ s, (K.row s).expect (fun s' => 1 / ε s') = 1) (hM : ∀ h, 0 < M h)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hβμ : β < 1 + μ)
    (hgrowth : ∀ h s', M (next h s') = M h * (1 + μ) * ε s') (h₀ : Hist S) :
    Household.Euler K β (fun z => z ^ (-ρ)) (fun z => z⁻¹) (market K β μ ρ x y M) h₀
      (cons x y) (holdings M x) := by
  intro g _ j
  have hμ : 0 < 1 + μ := by linarith
  have hγ : β / (1 + μ) < 1 := (div_lt_one hμ).2 hβμ
  have h1γ : 0 < 1 - β / (1 + μ) := by linarith
  have hMg := hM g
  have hlamg : 0 < lam ρ x y g := Real.rpow_pos_of_pos (mul_pos hx (hy _)) _
  have hPg : 0 < price β μ ρ x y M g :=
    mul_pos (mul_pos hMg h1γ) (Real.rpow_pos_of_pos (mul_pos hx (hy _)) _)
  have hserv : Household.services (market K β μ ρ x y M) (holdings M x) g
      = M g / price β μ ρ x y M g := by
    simp [Household.services, market, holdings, Fin.sum_univ_four]; ring
  have hcons : ∀ h, (cons x y h) ^ (-ρ) = lam ρ x y h := fun h => rfl
  have hos := oneStep_lam_div_price (K := K) (ρ := ρ) hy hx hε hE hM hμ hγ hgrowth g
  fin_cases j
  · -- money (98)
    rw [hserv]
    simp only [market, Fin.zero_eta, Matrix.cons_val_zero, hcons]
    rw [hos]
    have e1 : 1 / price β μ ρ x y M g * lam ρ x y g = 1 / (M g * (1 - β / (1 + μ))) := by
      rw [mul_comm]; exact lam_div_price hy hx g
    have e2 : 1 / price β μ ρ x y M g * (M g / price β μ ρ x y M g)⁻¹ = 1 / M g := by
      field_simp
    rw [e1, e2]
    have : 1 + μ - β ≠ 0 := by linarith
    field_simp
    ring
  · -- nominal bond (95)
    simp only [market, Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero, hcons,
      zero_mul, zero_add]
    have e : (fun g' => lam ρ x y g' * ((1 + μ) / β / price β μ ρ x y M g'))
        = fun g' => (1 + μ) / β * (lam ρ x y g' * (1 / price β μ ρ x y M g')) := by
      funext g'; ring
    rw [e, oneStep_mul_left, hos, mul_comm, lam_div_price hy hx]
    field_simp
  · -- real bond (96)
    simp only [market, Fin.reduceFinMk, Matrix.cons_val, hcons, zero_mul, zero_add,
      one_mul]
    have hpos : 0 < oneStep K.trans (lam ρ x y) g :=
      Finset.sum_pos' (fun s _ => mul_nonneg (K.trans_nonneg _ _)
        (Real.rpow_pos_of_pos (mul_pos hx (hy _)) _).le) (by
          obtain ⟨s, hs⟩ := (K.row g.1).exists_prob_pos
          exact ⟨s, Finset.mem_univ _,
            mul_pos hs (Real.rpow_pos_of_pos (mul_pos hx (hy _)) _)⟩)
    have e : (fun g' => lam ρ x y g' * realRate K β ρ x y (anc g'))
        = fun g' => realRate K β ρ x y (anc g') * lam ρ x y g' := by funext g'; ring
    rw [e, oneStep_pull, realRate]
    field_simp
  · -- output fund (93)
    simp only [market, Fin.reduceFinMk, Matrix.cons_val, hcons, zero_mul, zero_add]
    have e : (fun g' => lam ρ x y g' * (fundPrice K β ρ x y g' + y g'.1))
        = fun g' => fundU K β ρ x y g' + divU ρ x y g' := by
      funext g'
      have : 0 < lam ρ x y g' := Real.rpow_pos_of_pos (mul_pos hx (hy _)) _
      simp only [fundPrice, divU]; field_simp
    rw [e, ← fundU_recursion hy hx hβ0.le hβ1, fundPrice]
    field_simp

/-- **The equilibrium plan is feasible** (O&R §8.7.1): the budget constraint holds at the
root and at every node, with the money transfer as endowment. -/
theorem feasible (h₀ : Hist S) :
    Household.Feasible (market K β μ ρ x y M) h₀ (wealth0 K β μ ρ x y M h₀) (cons x y)
      (holdings M x) := by
  constructor
  · simp [market, holdings, wealth0, Fin.sum_univ_four]; ring
  · intro g _ s
    simp [market, holdings, Fin.sum_univ_four, anc_next, cons]
    ring

/-- **The equilibrium plan is positive** (O&R §8.7.1). -/
theorem positive (hy : ∀ s, 0 < y s) (hx : 0 < x) (hM : ∀ h, 0 < M h) (hβ0 : 0 < β)
    (hβμ : β < 1 + μ) (h₀ : Hist S) :
    Household.Positive (market K β μ ρ x y M) h₀ (cons x y) (holdings M x) := by
  intro g _
  have hμ : 0 < 1 + μ := by linarith
  have h1γ : 0 < 1 - β / (1 + μ) := by have := (div_lt_one hμ).2 hβμ; linarith
  have hPg : 0 < price β μ ρ x y M g :=
    mul_pos (mul_pos (hM g) h1γ) (Real.rpow_pos_of_pos (mul_pos hx (hy _)) _)
  refine ⟨mul_pos hx (hy _), ?_⟩
  simp only [Household.services, market, holdings, Fin.sum_univ_four, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val, zero_mul, add_zero]
  exact mul_pos (one_div_pos.2 hPg) (hM g)

/-- **The transversality condition holds for the equilibrium plan** (O&R fn 31, p. 542):
derived from primitives: money contributes a bounded term (`u′(C)M/P = ω`), the output fund
the tail of a convergent series. -/
theorem tvc (hy : ∀ s, 0 < y s) (hx : 0 < x) (hε : ∀ s, 0 < ε s) (hM : ∀ h, 0 < M h)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hβμ : β < 1 + μ)
    (hgrowth : ∀ h s', M (next h s') = M h * (1 + μ) * ε s') (h₀ : Hist S) :
    Household.TVCHousehold K β (fun z => z ^ (-ρ)) (market K β μ ρ x y M) h₀ (cons x y)
      (holdings M x) := by
  have hμ : 0 < 1 + μ := by linarith
  have h1γ : 0 < 1 - β / (1 + μ) := by have := (div_lt_one hμ).2 hβμ; linarith
  set Bz := ∑ s, (x * y s) ^ (-ρ) * y s
  set B := ∑ s, 1 / ((1 + μ) * ε s * (1 - β / (1 + μ))) + x * (Bz * (β / (1 - β)) + Bz)
  set F : Hist S → ℝ := fun g => (cons x y g) ^ (-ρ)
    * ∑ j, (market K β μ ρ x y M).payoff j g * holdings M x j (anc g)
  have hF : ∀ g s, F (next g s) = 1 / ((1 + μ) * ε s * (1 - β / (1 + μ)))
      + x * (fundU K β ρ x y (next g s) + divU ρ x y (next g s)) := fun g s => by
    have hl : 0 < lam ρ x y (next g s) := Real.rpow_pos_of_pos (mul_pos hx (hy _)) _
    have hlp := lam_div_price (β := β) (μ := μ) (ρ := ρ) (M := M) hy hx (next g s)
    simp only [F, market, holdings, Fin.sum_univ_four, anc_next]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, mul_zero,
      add_zero]
    change lam ρ x y (next g s) * (1 / price β μ ρ x y M (next g s) * M g
      + (fundPrice K β ρ x y (next g s) + y (next g s).1) * x) = _
    have e1 : lam ρ x y (next g s) * (1 / price β μ ρ x y M (next g s) * M g)
        = (lam ρ x y (next g s) * (1 / price β μ ρ x y M (next g s))) * M g := by ring
    rw [mul_add, e1, hlp, hgrowth]
    simp only [fundPrice, divU]
    have := hM g; have := hε s
    field_simp
  have hbF : ∀ g s, 0 ≤ F (next g s) ∧ F (next g s) ≤ B := fun g s => by
    rw [hF]
    have t := fundU_terms (K := K) (ρ := ρ) hy hx hβ0.le hβ1 (next g s)
    have d := divU_bound (ρ := ρ) hy hx (next g s)
    have hpos : ∀ s, 0 ≤ 1 / ((1 + μ) * ε s * (1 - β / (1 + μ))) := fun s =>
      (one_div_pos.2 (mul_pos (mul_pos hμ (hε s)) h1γ)).le
    have hle := Finset.single_le_sum (f := fun s => 1 / ((1 + μ) * ε s * (1 - β / (1 + μ))))
      (fun s _ => hpos s) (Finset.mem_univ s)
    constructor
    · have := hpos s; nlinarith [t.2.1, d.1]
    · simp only [B]; nlinarith [t.2.2, d.2]
  have hbo : ∀ g, 0 ≤ oneStep K.trans F g ∧ oneStep K.trans F g ≤ B := fun g => by
    constructor
    · exact Finset.sum_nonneg fun s _ => mul_nonneg (K.trans_nonneg _ _) (hbF g s).1
    · calc oneStep K.trans F g ≤ oneStep K.trans (fun _ => B) g :=
            Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hbF g s).2 (K.trans_nonneg _ _)
        _ = B := oneStep_const K.trans_sum B g
  have hcv : ∀ T, 0 ≤ Household.contValue K β (fun z => z ^ (-ρ)) (market K β μ ρ x y M) h₀
      (cons x y) (holdings M x) T ∧ Household.contValue K β (fun z => z ^ (-ρ))
      (market K β μ ρ x y M) h₀ (cons x y) (holdings M x) T ≤ β ^ (T + 1) * B := fun T => by
    have e : Household.contValue K β (fun z => z ^ (-ρ)) (market K β μ ρ x y M) h₀ (cons x y)
        (holdings M x) T = β ^ (T + 1) * iterStep K.trans T (oneStep K.trans F) h₀ := by
      simp only [Household.contValue]; rw [iterStep_succ]
    rw [e]
    have l := iterStep_nonneg K.trans_nonneg T (fun g => (hbo g).1) h₀
    have u := iterStep_mono K.trans_nonneg T (X := oneStep K.trans F) (Y := fun _ => B)
      (fun g => (hbo g).2) h₀
    rw [iterStep_const K.trans_sum] at u
    exact ⟨mul_nonneg (pow_nonneg hβ0.le _) l, mul_le_mul_of_nonneg_left u (pow_nonneg hβ0.le _)⟩
  have hup : Tendsto (fun T : ℕ => β ^ (T + 1) * B) atTop (𝓝 0) := by
    have := ((tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).comp
      (tendsto_add_atTop_nat 1)).mul_const B
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup
    (fun T => (hcv T).1) (fun T => (hcv T).2)

/-- **The equilibrium lifetime utility is finite** (O&R (91), p. 579): consumption and real
balances depend only on the current state. -/
theorem util_summable {u : ℝ → ℝ} (hy : ∀ s, 0 < y s) (hx : 0 < x) (hM : ∀ h, 0 < M h)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hβμ : β < 1 + μ) (h₀ : Hist S) :
    Summable (Household.utilTerm K β u Real.log (market K β μ ρ x y M) h₀ (cons x y)
      (holdings M x)) := by
  have hμ : 0 < 1 + μ := by linarith
  have h1γ : 0 < 1 - β / (1 + μ) := by have := (div_lt_one hμ).2 hβμ; linarith
  set f : S → ℝ := fun s => u (x * y s) + Real.log (1 / ((1 - β / (1 + μ)) * (x * y s) ^ (-ρ)))
  have hfun : (fun g => u (cons x y g) + Real.log (Household.services (market K β μ ρ x y M)
      (holdings M x) g)) = fun g => f g.1 := by
    funext g
    have := hM g
    have : 0 < (x * y g.1) ^ (-ρ) := Real.rpow_pos_of_pos (mul_pos hx (hy _)) _
    simp only [f, cons, Household.services, market, holdings, Fin.sum_univ_four,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, mul_zero, add_zero]
    congr 2
    simp only [price]; field_simp
    ring
  have hb : ∀ g : Hist S, |f g.1| ≤ ∑ s, |f s| := fun g =>
    Finset.single_le_sum (f := fun s => |f s|) (fun s _ => abs_nonneg _) (Finset.mem_univ _)
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one hβ0.le hβ1).mul_right
    (∑ s, |f s|)) fun t => ?_
  simp only [Household.utilTerm, hfun, Real.norm_eq_abs, abs_mul, abs_of_nonneg
    (pow_nonneg hβ0.le t)]
  exact mul_le_mul_of_nonneg_left (abs_iterStep_le K.trans_nonneg K.trans_sum t hb h₀)
    (pow_nonneg hβ0.le t)

/-- **The §8.7 equilibrium allocation is optimal for each household** (O&R §8.7.1–8.7.3,
pp. 579–583): with CRRA utility `u′(C) = C^{−ρ}` and `v = log`, consumption `C = xY^W`,
money following `M_{t+1} = M_t(1+μ)ε_{t+1}` with `E_t[1/ε] = 1`, the price level
`P = M(1 − β/(1+μ))(xY^W)^{−ρ}` (so `M/P = ω(xY^W)^ρ`), `1 + i = (1+μ)/β`, the market-clearing
real rate and the output-fund price, the plan (money `M`, no bonds, fund share `x`) attains
at least the lifetime utility of EVERY feasible positive rival plan satisfying the no-Ponzi
condition with finite utility. -/
theorem equilibrium_optimal {u : ℝ → ℝ} (hρ : 0 < ρ)
    (hdu : ∀ z, 0 < z → HasDerivAt u (z ^ (-ρ)) z) (hy : ∀ s, 0 < y s) (hx : 0 < x)
    (hε : ∀ s, 0 < ε s) (hE : ∀ s, (K.row s).expect (fun s' => 1 / ε s') = 1)
    (hM : ∀ h, 0 < M h) (hβ0 : 0 < β) (hβ1 : β < 1) (hβμ : β < 1 + μ)
    (hgrowth : ∀ h s', M (next h s') = M h * (1 + μ) * ε s') (h₀ : Hist S)
    {C' : Hist S → ℝ} {a' : Fin 4 → Hist S → ℝ}
    (hF' : Household.Feasible (market K β μ ρ x y M) h₀ (wealth0 K β μ ρ x y M h₀) C' a')
    (hP' : Household.Positive (market K β μ ρ x y M) h₀ C' a')
    (hnp : Household.NoPonzi K β (fun z => z ^ (-ρ)) (market K β μ ρ x y M) h₀ (cons x y) a')
    (hs' : Summable (Household.utilTerm K β u Real.log (market K β μ ρ x y M) h₀ C' a')) :
    Household.lifetimeU K β u Real.log (market K β μ ρ x y M) h₀ C' a'
      ≤ Household.lifetimeU K β u Real.log (market K β μ ρ x y M) h₀ (cons x y)
        (holdings M x) :=
  Household.household_sufficiency K (market K β μ ρ x y M) hβ0.le (crra_concave hρ hdu) hdu
    strictConcaveOn_log_Ioi.concaveOn (fun _ hz => Real.hasDerivAt_log hz.ne')
    (feasible h₀) hF' (positive hy hx hM hβ0 hβμ h₀) hP'
    (euler_holds hy hx hε hE hM hβ0 hβ1 hβμ hgrowth h₀)
    (tvc hy hx hε hM hβ0 hβ1 hβμ hgrowth h₀) hnp (util_summable hy hx hM hβ0 hβ1 hβμ h₀) hs'

end Equilibrium87

end ObstfeldRogoff.MoneyExchangeRates.NominalAssetPricing
