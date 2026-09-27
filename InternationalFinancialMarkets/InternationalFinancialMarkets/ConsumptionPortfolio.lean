/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import InternationalFinancialMarkets.EventTree
import InternationalFinancialMarkets.Model
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Convex.SpecificFunctions.Pow

/-!
# Infinite-horizon consumption and portfolio choice

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, Supplement A to
Chapter 5, "Multiperiod Portfolio Selection", pp. 742–744.

An investor with financial wealth `W` and no other income chooses consumption `C` and shares
`x_n` (`Σ_n x_n = 1`) of `N` assets with net returns `r^n`. Uncertainty is an i.i.d. event tree
(`iidTree`, one-step probabilities `q k g s = π(s)` in `EventTree.Tree`): wealth evolves as
`W_{t+1} = (1 + r°(x_t))(W_t − C_t)`, with portfolio return `r° = Σ_n x_n r^n`
(`= r^N + Σ_{n<N} x_n (r^n − r^N)`, the book's form).

* **Portfolio condition (2).** With CRRA utility (`ρ > 0`, `ρ ≠ 1`) and consumption proportional
  to wealth, (2) is `E[(r^n − r^N)(1 + r°)^{−ρ}] = 0`, independent of wealth. It is the
  first-order condition of maximising the portfolio objective `E[(1 + r°)^{1−ρ}]/(1−ρ)`:
  sufficient (concavity) and necessary (at an interior optimum). Log utility likewise with
  `E log(1 + r°)`.
* **Bellman equation.** `V(W) = μ^{−ρ} W^{1−ρ}/(1−ρ)` with `μ = 1 − [βE(1+r°)^{1−ρ}]^{1/ρ}`
  satisfies the Bellman equation exactly, the maximum attained at `C = μW` and the optimal
  portfolio. Conversely a guess `A W^{1−ρ}/(1−ρ)` whose maximum is at `C = μW` forces
  `A = μ^{−ρ}` and the book's `μ`; `μ` is the i.i.d. fixed point of the share recursion
  (`EventTree.crra_iid_share`) and satisfies the Euler equation (1). Log utility gives
  `μ = 1 − β`.
* **Verification.** On the i.i.d. tree, over the infinite horizon, under the parameter
  condition `βE(1+r°)^{1−ρ} < 1` (log: `0 < β < 1`): every admissible plan (consumption and
  portfolio at each history, `0 < C ≤ W`, utility series convergent) satisfies the
  transversality property `β^t E V(W_t) → 0`, which we prove, and achieves at most `V(W₀)`;
  the policy `C = μW` with the optimal portfolio is admissible and attains `V(W₀)`.
* **Existence of the optimal portfolio.** Under positive state probabilities, a no-arbitrage
  (non-redundancy) condition on the return matrix (no `d ≠ 0`, `Σd = 0`, with `Σ d_n r^n ≥ 0` in
  every state) and some feasible portfolio, the closed feasible set is compact and an optimal
  portfolio exists and is interior, so it satisfies (2): for `ρ > 1` and log utility the
  objective tends to `−∞` at the boundary; for `ρ < 1` infinite marginal utility at a zero
  gross return rules the boundary out. The verification theorems are restated with only these
  primitive conditions (and the growth condition at the optimum).
* **Returns varying with the history.** On a general event tree with history-dependent returns
  the book's recursion `μ_t = (1 + [βE_t{(1 + r°_{t+1})^{1−ρ} μ_{t+1}^{−ρ}}]^{1/ρ})^{−1}` has a
  solution, the limit of backward iterations from `μ ≡ 1`, under a uniform growth condition;
  `C = μ_t W` with the date-`t` optimal portfolios attains `V_t(W) = μ_t^{−ρ}W^{1−ρ}/(1−ρ)` and
  no admissible plan does better. With log utility `μ = 1 − β` for any return process, the
  portfolio is chosen myopically to maximise `E_t log(1 + r°)`, and
  `V_t(W) = log W/(1 − β) + K_t` with `K_t` a backward-summed series that converges when the
  optimal `E_t log(1 + r°)` is uniformly bounded.
-/

namespace ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio

open Finset Filter Topology EventTree

variable {S : Type} [Fintype S] {N : ℕ}

/-- The i.i.d. event tree of O&R Supplement A, p. 744: whatever the history, the next event is
`s` with probability `π(s)`. -/
def iidTree (Ω : StateSpace S) : EventTree.Tree S :=
  ⟨fun _ _ s => Ω.prob s, fun _ _ s => Ω.prob_nonneg s, fun _ _ => Ω.prob_sum⟩

/-- The return on a portfolio `x` of the `N` assets in state `s`, `r° = Σ_n x_n r^n`
(O&R Supplement A, p. 743). -/
def portRet (r : Fin N → S → ℝ) (x : Fin N → ℝ) (s : S) : ℝ := ∑ i, x i * r i s

/-- A feasible portfolio (O&R Supplement A, p. 742): shares add up to one, `Σ_n x_n = 1`, and
the gross return `1 + r°` is positive in every state. -/
def PortFeasible (r : Fin N → S → ℝ) (x : Fin N → ℝ) : Prop :=
  ∑ i, x i = 1 ∧ ∀ s, 0 < 1 + portRet r x s

omit [Fintype S] in
/-- The book's form of the portfolio return, O&R Supplement A, p. 743: with `Σ_n x_n = 1` and
reference asset `k` (the book's asset `N`), `r° = r^k + Σ_n x_n (r^n − r^k)` (the `n = k` term
vanishes). -/
theorem portRet_eq_book (r : Fin N → S → ℝ) {x : Fin N → ℝ} (hx : ∑ i, x i = 1) (k : Fin N)
    (s : S) : portRet r x s = r k s + ∑ i, x i * (r i s - r k s) := by
  simp only [portRet, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hx, one_mul]
  ring

omit [Fintype S] in
/-- The reformulated wealth-accumulation constraint, O&R Supplement A, p. 742:
`Σ_n x_n (1 + r^n)(W − C) = (1 + r°)(W − C)` when `Σ_n x_n = 1`. -/
theorem wealth_accumulation_book (r : Fin N → S → ℝ) {x : Fin N → ℝ} (hx : ∑ i, x i = 1)
    (W C : ℝ) (s : S) :
    ∑ i, x i * (1 + r i s) * (W - C) = (1 + portRet r x s) * (W - C) := by
  simp only [portRet, mul_add, mul_one, Finset.sum_add_distrib, ← Finset.sum_mul, hx]

/-- The CRRA portfolio objective, O&R Supplement A, pp. 743–744: `E[(1 + r°)^{1−ρ}]/(1−ρ)`, the
expected utility of the gross portfolio return. -/
noncomputable def portObj (Ω : StateSpace S) (ρ : ℝ) (r : Fin N → S → ℝ) (x : Fin N → ℝ) : ℝ :=
  Ω.expect fun s => crraUtil ρ (1 + portRet r x s)

/-- The log portfolio objective, O&R Supplement A, p. 743: `E log(1 + r°)`. -/
noncomputable def logPortObj (Ω : StateSpace S) (r : Fin N → S → ℝ) (x : Fin N → ℝ) : ℝ :=
  Ω.expect fun s => Real.log (1 + portRet r x s)

/-- The portfolio condition (2) of O&R Supplement A, p. 743, at consumption proportional to
wealth and CRRA marginal utility: `E[(r^n − r^k)(1 + r°)^{−ρ}] = 0` for every asset `n`, with
reference asset `k` (the book's `N`). -/
def PortfolioCondition (Ω : StateSpace S) (ρ : ℝ) (r : Fin N → S → ℝ) (k : Fin N)
    (x : Fin N → ℝ) : Prop :=
  ∀ n, Ω.expect (fun s => (r n s - r k s) * (1 + portRet r x s) ^ (-ρ)) = 0

/-- The portfolio condition (2) in the log case, O&R Supplement A, p. 743:
`E[(r^n − r^k)(1 + r°)^{−1}] = 0` for every asset `n`. -/
def LogPortfolioCondition (Ω : StateSpace S) (r : Fin N → S → ℝ) (k : Fin N)
    (x : Fin N → ℝ) : Prop :=
  ∀ n, Ω.expect (fun s => (r n s - r k s) * (1 + portRet r x s)⁻¹) = 0

/-- Wealth invariance of the portfolio condition, O&R Supplement A, p. 743 ("multiplication of
both sides by `W_t`"): with `C_{t+1} = μW_{t+1}` and `W_{t+1} = (1 + r°)(1 − μ)W_t`, the
condition (2) `E[(r^n − r^k) u′(C_{t+1})] = 0` with `u′(C) = C^{−ρ}` holds iff
`E[(r^n − r^k)(1 + r°)^{−ρ}] = 0`, whatever `W_t > 0` (any real `ρ`; `ρ = 1` is the log case). -/
theorem portfolio_condition_wealth_invariant (Ω : StateSpace S) (ρ : ℝ) (r : Fin N → S → ℝ)
    (n k : Fin N) {x : Fin N → ℝ} (hx : ∀ s, 0 < 1 + portRet r x s) {μ W : ℝ} (hμ0 : 0 < μ)
    (hμ1 : μ < 1) (hW : 0 < W) :
    Ω.expect (fun s => (r n s - r k s) * (μ * ((1 + portRet r x s) * (1 - μ) * W)) ^ (-ρ)) = 0
      ↔ Ω.expect (fun s => (r n s - r k s) * (1 + portRet r x s) ^ (-ρ)) = 0 := by
  have h1 : 0 < 1 - μ := by linarith
  have hK : 0 < (μ * ((1 - μ) * W)) ^ (-ρ) := Real.rpow_pos_of_pos (by positivity) _
  have e : Ω.expect (fun s => (r n s - r k s) * (μ * ((1 + portRet r x s) * (1 - μ) * W)) ^ (-ρ))
      = (μ * ((1 - μ) * W)) ^ (-ρ)
        * Ω.expect (fun s => (r n s - r k s) * (1 + portRet r x s) ^ (-ρ)) := by
    simp only [StateSpace.expect, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [show μ * ((1 + portRet r x s) * (1 - μ) * W) = (μ * ((1 - μ) * W)) * (1 + portRet r x s)
      by ring, Real.mul_rpow (by positivity) (hx s).le]
    ring
  rw [e]
  constructor
  · intro h; exact (mul_eq_zero.mp h).resolve_left hK.ne'
  · intro h; rw [h, mul_zero]

/-- The perturbed portfolio `x + ε(e_n − e_k)`: move a fraction `ε` of wealth from asset `k` to
asset `n` (O&R Supplement A, p. 743, the unconstrained shares `x_n`, `n < N`). -/
def portShift (x : Fin N → ℝ) (n k : Fin N) (ε : ℝ) : Fin N → ℝ :=
  fun i => x i + ε * ((if i = n then 1 else 0) - (if i = k then 1 else 0))

/-- Shifting between assets keeps the shares adding up to one (O&R Supplement A, p. 742). -/
theorem portShift_sum (x : Fin N → ℝ) (n k : Fin N) (ε : ℝ) :
    ∑ i, portShift x n k ε i = ∑ i, x i := by
  simp [portShift, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib]

omit [Fintype S] in
/-- The return on the shifted portfolio, `r°(x + ε(e_n − e_k)) = r°(x) + ε(r^n − r^k)`
(O&R Supplement A, p. 743). -/
theorem portRet_portShift (r : Fin N → S → ℝ) (x : Fin N → ℝ) (n k : Fin N) (ε : ℝ) (s : S) :
    portRet r (portShift x n k ε) s = portRet r x s + ε * (r n s - r k s) := by
  simp only [portRet, portShift, add_mul, Finset.sum_add_distrib, sub_mul, mul_assoc,
    Finset.sum_sub_distrib, ← Finset.mul_sum, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte]

/-- Sufficiency of the portfolio condition (2), O&R Supplement A, p. 743: for CRRA utility
(`ρ > 0`, `ρ ≠ 1`), a feasible portfolio `x*` satisfying (2) maximises the portfolio objective
`E[(1 + r°)^{1−ρ}]/(1−ρ)` over all feasible portfolios (concavity). -/
theorem portfolio_condition_sufficient (Ω : StateSpace S) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≠ 1)
    (r : Fin N → S → ℝ) (k : Fin N) {xs : Fin N → ℝ} (hxs : PortFeasible r xs)
    (hfoc : PortfolioCondition Ω ρ r k xs) {x : Fin N → ℝ} (hx : PortFeasible r x) :
    portObj Ω ρ r x ≤ portObj Ω ρ r xs := by
  have hd : ∀ s, portRet r x s - portRet r xs s = ∑ i, (x i - xs i) * (r i s - r k s) := by
    intro s
    rw [portRet_eq_book r hx.1 k, portRet_eq_book r hxs.1 k]
    simp only [sub_mul, Finset.sum_sub_distrib]
    ring
  have hzero : Ω.expect (fun s => (1 + portRet r xs s) ^ (-ρ)
      * ((1 + portRet r x s) - (1 + portRet r xs s))) = 0 := by
    have e : Ω.expect (fun s => (1 + portRet r xs s) ^ (-ρ)
        * ((1 + portRet r x s) - (1 + portRet r xs s)))
        = ∑ i, (x i - xs i) * Ω.expect (fun s => (r i s - r k s) * (1 + portRet r xs s) ^ (-ρ))
        := by
      simp only [StateSpace.expect, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [show 1 + portRet r x s - (1 + portRet r xs s) = portRet r x s - portRet r xs s by ring,
        hd s, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e]
    exact Finset.sum_eq_zero fun i _ => by rw [hfoc i, mul_zero]
  have hle : ∀ s, Ω.prob s * crraUtil ρ (1 + portRet r x s) ≤ Ω.prob s
      * (crraUtil ρ (1 + portRet r xs s) + (1 + portRet r xs s) ^ (-ρ)
        * ((1 + portRet r x s) - (1 + portRet r xs s))) := fun s =>
    mul_le_mul_of_nonneg_left (crra_tangent hρ hρ1 (hxs.2 s) (hx.2 s)) (Ω.prob_nonneg s)
  have h2 := Finset.sum_le_sum fun s (_ : s ∈ univ) => hle s
  simp only [mul_add, Finset.sum_add_distrib] at h2
  unfold portObj StateSpace.expect
  unfold StateSpace.expect at hzero
  linarith

/-- Necessity of the portfolio condition (2), O&R Supplement A, p. 743: if a feasible portfolio
`x*` maximises the CRRA portfolio objective over feasible portfolios (`ρ ≠ 1`), it satisfies
`E[(r^n − r^k)(1 + r°)^{−ρ}] = 0` for every asset `n` (shift wealth between `n` and `k`). -/
theorem portfolio_condition_necessary (Ω : StateSpace S) {ρ : ℝ} (hρ1 : ρ ≠ 1)
    (r : Fin N → S → ℝ) (k : Fin N) {xs : Fin N → ℝ} (hxs : PortFeasible r xs)
    (hmax : ∀ x, PortFeasible r x → portObj Ω ρ r x ≤ portObj Ω ρ r xs) :
    PortfolioCondition Ω ρ r k xs := by
  intro n
  have hp : (1 : ℝ) - ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm hρ1)
  have hφ : ∀ ε, portObj Ω ρ r (portShift xs n k ε)
      = ∑ s, Ω.prob s * ((1 + portRet r xs s + ε * (r n s - r k s)) ^ (1 - ρ) / (1 - ρ)) := by
    intro ε
    simp only [portObj, StateSpace.expect, crraUtil, portRet_portShift, add_assoc]
  have hpos : ∀ᶠ ε in nhds (0 : ℝ), ∀ s, 0 < 1 + portRet r xs s + ε * (r n s - r k s) := by
    rw [Filter.eventually_all]
    intro s
    have c : ContinuousAt (fun ε : ℝ => 1 + portRet r xs s + ε * (r n s - r k s)) 0 := by
      fun_prop
    exact c.eventually (lt_mem_nhds (by simpa using hxs.2 s))
  have hloc : IsLocalMax (fun ε => ∑ s, Ω.prob s
      * ((1 + portRet r xs s + ε * (r n s - r k s)) ^ (1 - ρ) / (1 - ρ))) 0 := by
    filter_upwards [hpos] with ε hε
    rw [← hφ, ← hφ]
    have e0 : portShift xs n k 0 = xs := by funext i; simp [portShift]
    rw [e0]
    refine hmax _ ⟨by rw [portShift_sum]; exact hxs.1, fun s => ?_⟩
    rw [portRet_portShift, ← add_assoc]; exact hε s
  have hd : HasDerivAt (fun ε => ∑ s, Ω.prob s
      * ((1 + portRet r xs s + ε * (r n s - r k s)) ^ (1 - ρ) / (1 - ρ)))
      (∑ s, Ω.prob s * ((r n s - r k s) * (1 + portRet r xs s) ^ (-ρ))) 0 := by
    refine HasDerivAt.fun_sum fun s _ => ?_
    have h1 : HasDerivAt (fun ε : ℝ => 1 + portRet r xs s + ε * (r n s - r k s))
        (r n s - r k s) 0 := by
      simpa using HasDerivAt.const_add (1 + portRet r xs s)
        (HasDerivAt.mul_const (hasDerivAt_id (0 : ℝ)) (r n s - r k s))
    have h2 := HasDerivAt.rpow_const (p := 1 - ρ) h1 (Or.inl (by simpa using (hxs.2 s).ne'))
    have h3 := HasDerivAt.const_mul (Ω.prob s) (HasDerivAt.div_const h2 (1 - ρ))
    convert h3 using 1
    simp only [zero_mul, add_zero, show (1 : ℝ) - ρ - 1 = -ρ by ring]
    field_simp
  have := hloc.hasDerivAt_eq_zero hd
  simpa [StateSpace.expect] using this

/-- Sufficiency of the log portfolio condition, O&R Supplement A, p. 743: a feasible portfolio
satisfying `E[(r^n − r^k)(1 + r°)^{−1}] = 0` maximises `E log(1 + r°)` over feasible
portfolios. -/
theorem log_portfolio_condition_sufficient (Ω : StateSpace S) (r : Fin N → S → ℝ) (k : Fin N)
    {xs : Fin N → ℝ} (hxs : PortFeasible r xs) (hfoc : LogPortfolioCondition Ω r k xs)
    {x : Fin N → ℝ} (hx : PortFeasible r x) : logPortObj Ω r x ≤ logPortObj Ω r xs := by
  have hd : ∀ s, portRet r x s - portRet r xs s = ∑ i, (x i - xs i) * (r i s - r k s) := by
    intro s
    rw [portRet_eq_book r hx.1 k, portRet_eq_book r hxs.1 k]
    simp only [sub_mul, Finset.sum_sub_distrib]
    ring
  have hzero : Ω.expect (fun s => 1 / (1 + portRet r xs s)
      * ((1 + portRet r x s) - (1 + portRet r xs s))) = 0 := by
    have e : Ω.expect (fun s => 1 / (1 + portRet r xs s)
        * ((1 + portRet r x s) - (1 + portRet r xs s)))
        = ∑ i, (x i - xs i) * Ω.expect (fun s => (r i s - r k s) * (1 + portRet r xs s)⁻¹) := by
      simp only [StateSpace.expect, Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [show 1 + portRet r x s - (1 + portRet r xs s) = portRet r x s - portRet r xs s by ring,
        hd s, Finset.mul_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e]
    exact Finset.sum_eq_zero fun i _ => by rw [hfoc i, mul_zero]
  have hle : ∀ s, Ω.prob s * Real.log (1 + portRet r x s) ≤ Ω.prob s
      * (Real.log (1 + portRet r xs s) + 1 / (1 + portRet r xs s)
        * ((1 + portRet r x s) - (1 + portRet r xs s))) := fun s =>
    mul_le_mul_of_nonneg_left (log_tangent (hxs.2 s) (hx.2 s)) (Ω.prob_nonneg s)
  have h2 := Finset.sum_le_sum fun s (_ : s ∈ univ) => hle s
  simp only [mul_add, Finset.sum_add_distrib] at h2
  unfold logPortObj StateSpace.expect
  unfold StateSpace.expect at hzero
  linarith

/-- Necessity of the log portfolio condition, O&R Supplement A, p. 743: a feasible portfolio
maximising `E log(1 + r°)` over feasible portfolios satisfies
`E[(r^n − r^k)(1 + r°)^{−1}] = 0` for every asset `n`. -/
theorem log_portfolio_condition_necessary (Ω : StateSpace S) (r : Fin N → S → ℝ) (k : Fin N)
    {xs : Fin N → ℝ} (hxs : PortFeasible r xs)
    (hmax : ∀ x, PortFeasible r x → logPortObj Ω r x ≤ logPortObj Ω r xs) :
    LogPortfolioCondition Ω r k xs := by
  intro n
  have hφ : ∀ ε, logPortObj Ω r (portShift xs n k ε)
      = ∑ s, Ω.prob s * Real.log (1 + portRet r xs s + ε * (r n s - r k s)) := by
    intro ε
    simp only [logPortObj, StateSpace.expect, portRet_portShift, add_assoc]
  have hpos : ∀ᶠ ε in nhds (0 : ℝ), ∀ s, 0 < 1 + portRet r xs s + ε * (r n s - r k s) := by
    rw [Filter.eventually_all]
    intro s
    have c : ContinuousAt (fun ε : ℝ => 1 + portRet r xs s + ε * (r n s - r k s)) 0 := by
      fun_prop
    exact c.eventually (lt_mem_nhds (by simpa using hxs.2 s))
  have hloc : IsLocalMax (fun ε => ∑ s, Ω.prob s
      * Real.log (1 + portRet r xs s + ε * (r n s - r k s))) 0 := by
    filter_upwards [hpos] with ε hε
    rw [← hφ, ← hφ]
    have e0 : portShift xs n k 0 = xs := by funext i; simp [portShift]
    rw [e0]
    refine hmax _ ⟨by rw [portShift_sum]; exact hxs.1, fun s => ?_⟩
    rw [portRet_portShift, ← add_assoc]; exact hε s
  have hd : HasDerivAt (fun ε => ∑ s, Ω.prob s
      * Real.log (1 + portRet r xs s + ε * (r n s - r k s)))
      (∑ s, Ω.prob s * ((r n s - r k s) * (1 + portRet r xs s)⁻¹)) 0 := by
    refine HasDerivAt.fun_sum fun s _ => ?_
    have h1 : HasDerivAt (fun ε : ℝ => 1 + portRet r xs s + ε * (r n s - r k s))
        (r n s - r k s) 0 := by
      simpa using HasDerivAt.const_add (1 + portRet r xs s)
        (HasDerivAt.mul_const (hasDerivAt_id (0 : ℝ)) (r n s - r k s))
    have h2 := HasDerivAt.log h1 (by simpa using (hxs.2 s).ne')
    have h3 := HasDerivAt.const_mul (Ω.prob s) h2
    convert h3 using 1
    simp only [zero_mul, add_zero, div_eq_mul_inv]
  have := hloc.hasDerivAt_eq_zero hd
  simpa [StateSpace.expect] using this

/-! ## The Bellman equation -/

/-- The certainty-equivalent growth factor `βE(1 + r°)^{1−ρ}` of a portfolio `x`, O&R
Supplement A, p. 744. -/
noncomputable def growthFactor (Ω : StateSpace S) (β ρ : ℝ) (r : Fin N → S → ℝ)
    (x : Fin N → ℝ) : ℝ :=
  β * Ω.expect fun s => (1 + portRet r x s) ^ (1 - ρ)

/-- The CRRA consumption share `μ = 1 − [βE(1 + r°)^{1−ρ}]^{1/ρ}` at the portfolio `x`,
O&R Supplement A, p. 744. -/
noncomputable def crraShare (Ω : StateSpace S) (β ρ : ℝ) (r : Fin N → S → ℝ)
    (x : Fin N → ℝ) : ℝ :=
  1 - growthFactor Ω β ρ r x ^ (1 / ρ)

/-- The CRRA value function `V(W) = μ^{−ρ} W^{1−ρ}/(1−ρ)` (O&R Supplement A, pp. 742–744: the
book's guess `C = μW` corresponds to `V(W) = A W^{1−ρ}/(1−ρ)` with `A = μ^{−ρ}`). -/
noncomputable def crraValue (μ ρ W : ℝ) : ℝ := μ ^ (-ρ) * crraUtil ρ W

/-- The right-hand side of the Bellman equation, O&R Supplement A, p. 742:
`u(C) + βE V((1 + r°(x))(W − C))`, maximised over consumption `C` and portfolio `x`. -/
noncomputable def bellmanRHS (Ω : StateSpace S) (β : ℝ) (u V : ℝ → ℝ) (r : Fin N → S → ℝ)
    (W C : ℝ) (x : Fin N → ℝ) : ℝ :=
  u C + β * Ω.expect fun s => V ((1 + portRet r x s) * (W - C))

/-- An expectation of a positive random variable is positive (the probabilities sum to one),
O&R §5.1 conventions, used in Supplement A. -/
theorem expect_pos (Ω : StateSpace S) {f : S → ℝ} (hf : ∀ s, 0 < f s) : 0 < Ω.expect f := by
  have hlt : ∑ _s : S, (0 : ℝ) < ∑ s, Ω.prob s := by rw [Ω.prob_sum]; simp
  obtain ⟨s₀, -, hs₀⟩ := Finset.exists_lt_of_sum_lt hlt
  exact Finset.sum_pos' (fun s _ => mul_nonneg (Ω.prob_nonneg s) (hf s).le)
    ⟨s₀, Finset.mem_univ _, mul_pos hs₀ (hf s₀)⟩

/-- The growth factor is positive for a feasible portfolio and `β > 0` (O&R p. 744). -/
theorem growthFactor_pos (Ω : StateSpace S) {β : ℝ} (hβ : 0 < β) (ρ : ℝ) (r : Fin N → S → ℝ)
    {x : Fin N → ℝ} (hx : PortFeasible r x) : 0 < growthFactor Ω β ρ r x :=
  mul_pos hβ (expect_pos Ω fun s => Real.rpow_pos_of_pos (hx.2 s) _)

/-- Under the parameter condition `βE(1 + r°)^{1−ρ} < 1` the share lies in `(0, 1)`, and
`(1 − μ)^ρ = βE(1 + r°)^{1−ρ}` (O&R Supplement A, p. 744). -/
theorem crraShare_mem (Ω : StateSpace S) {β ρ : ℝ} (hβ : 0 < β) (hρ : 0 < ρ)
    (r : Fin N → S → ℝ) {x : Fin N → ℝ} (hx : PortFeasible r x)
    (hB : growthFactor Ω β ρ r x < 1) :
    0 < crraShare Ω β ρ r x ∧ crraShare Ω β ρ r x < 1
      ∧ (1 - crraShare Ω β ρ r x) ^ ρ = growthFactor Ω β ρ r x := by
  have hB0 := growthFactor_pos Ω hβ ρ r hx
  have h1 : growthFactor Ω β ρ r x ^ (1 / ρ) < 1 :=
    Real.rpow_lt_one hB0.le hB (one_div_pos.mpr hρ)
  have h2 : 0 < growthFactor Ω β ρ r x ^ (1 / ρ) := Real.rpow_pos_of_pos hB0 _
  refine ⟨by unfold crraShare; linarith, by unfold crraShare; linarith, ?_⟩
  rw [crraShare, sub_sub_cancel, one_div, Real.rpow_inv_rpow hB0.le hρ.ne']

/-- The continuation value at the CRRA guess, O&R Supplement A, p. 743: for `W − C > 0` and a
feasible portfolio, `βE[A u((1 + r°)(W − C))] = A · βE(1 + r°)^{1−ρ} · u(W − C)` with
`u(C) = C^{1−ρ}/(1−ρ)`: the portfolio and saving decisions separate. -/
theorem expect_next_crra (Ω : StateSpace S) (β ρ A : ℝ) (r : Fin N → S → ℝ) {x : Fin N → ℝ}
    (hx : PortFeasible r x) {D : ℝ} (hD : 0 < D) :
    β * Ω.expect (fun s => A * crraUtil ρ ((1 + portRet r x s) * D))
      = A * growthFactor Ω β ρ r x * crraUtil ρ D := by
  simp only [growthFactor, StateSpace.expect, crraUtil, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Real.mul_rpow (hx.2 s).le hD.le]
  ring

/-- The growth factor times utility of saving equals `β(W − C)^{1−ρ}` times the portfolio
objective (O&R Supplement A, p. 743; `ρ ≠ 1`). -/
theorem growthFactor_mul_crraUtil (Ω : StateSpace S) (β : ℝ) {ρ : ℝ} (hρ1 : ρ ≠ 1)
    (r : Fin N → S → ℝ) (x : Fin N → ℝ) (D : ℝ) :
    growthFactor Ω β ρ r x * crraUtil ρ D = β * D ^ (1 - ρ) * portObj Ω ρ r x := by
  have hp : (1 : ℝ) - ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm hρ1)
  simp only [growthFactor, portObj, StateSpace.expect, crraUtil, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun s _ => ?_
  field_simp

/-- The consumption split at the CRRA guess, O&R Supplement A, p. 744: for `0 < μ < 1`,
`0 < C < W`, `u(C) + μ^{−ρ}(1 − μ)^ρ u(W − C) ≤ μ^{−ρ} u(W)` (supporting lines at `μW` and
`(1 − μ)W`). -/
theorem crra_split_le {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≠ 1) {μ W C : ℝ} (hμ0 : 0 < μ)
    (hμ1 : μ < 1) (hC : 0 < C) (hCW : C < W) :
    crraUtil ρ C + μ ^ (-ρ) * (1 - μ) ^ ρ * crraUtil ρ (W - C) ≤ μ ^ (-ρ) * crraUtil ρ W := by
  have hW : 0 < W := hC.trans hCW
  have h1 : 0 < 1 - μ := by linarith
  have hμW : 0 < μ * W := mul_pos hμ0 hW
  have h1W : 0 < (1 - μ) * W := mul_pos h1 hW
  have hD : 0 < W - C := by linarith
  have t1 := crra_tangent hρ hρ1 hμW hC
  have t2 := crra_tangent hρ hρ1 h1W hD
  have hK : 0 ≤ μ ^ (-ρ) * (1 - μ) ^ ρ :=
    mul_nonneg (Real.rpow_nonneg hμ0.le _) (Real.rpow_nonneg h1.le _)
  have hbb : (1 - μ) ^ ρ * (1 - μ) ^ (-ρ) = 1 := by
    rw [Real.rpow_neg h1.le, mul_inv_cancel₀ (Real.rpow_pos_of_pos h1 _).ne']
  have hμp : μ ^ (1 - ρ) = μ ^ (-ρ) * μ := by
    rw [show (1 : ℝ) - ρ = -ρ + 1 by ring, Real.rpow_add hμ0, Real.rpow_one]
  have h1p : (1 - μ) ^ (1 - ρ) = (1 - μ) ^ (-ρ) * (1 - μ) := by
    rw [show (1 : ℝ) - ρ = -ρ + 1 by ring, Real.rpow_add h1, Real.rpow_one]
  have i1 : μ ^ (-ρ) * (1 - μ) ^ ρ * ((1 - μ) * W) ^ (-ρ) = (μ * W) ^ (-ρ) := by
    rw [Real.mul_rpow h1.le hW.le, Real.mul_rpow hμ0.le hW.le]
    linear_combination μ ^ (-ρ) * W ^ (-ρ) * hbb
  have i2 : crraUtil ρ (μ * W) + μ ^ (-ρ) * (1 - μ) ^ ρ * crraUtil ρ ((1 - μ) * W)
      = μ ^ (-ρ) * crraUtil ρ W := by
    simp only [crraUtil]
    rw [Real.mul_rpow hμ0.le hW.le, Real.mul_rpow h1.le hW.le, hμp, h1p]
    linear_combination μ ^ (-ρ) * (1 - μ) * W ^ (1 - ρ) / (1 - ρ) * hbb
  have t2' := mul_le_mul_of_nonneg_left t2 hK
  calc crraUtil ρ C + μ ^ (-ρ) * (1 - μ) ^ ρ * crraUtil ρ (W - C)
      ≤ crraUtil ρ (μ * W) + (μ * W) ^ (-ρ) * (C - μ * W)
        + μ ^ (-ρ) * (1 - μ) ^ ρ * (crraUtil ρ ((1 - μ) * W)
          + ((1 - μ) * W) ^ (-ρ) * (W - C - (1 - μ) * W)) := by linarith
    _ = μ ^ (-ρ) * crraUtil ρ W := by
      linear_combination i2 + (W - C - (1 - μ) * W) * i1

/-- Equality in the consumption split at `C = μW`, O&R Supplement A, p. 744:
`u(μW) + μ^{−ρ}(1 − μ)^ρ u(W − μW) = μ^{−ρ} u(W)`. -/
theorem crra_split_eq {ρ : ℝ} {μ W : ℝ} (hμ0 : 0 < μ) (hμ1 : μ < 1) (hW : 0 < W) :
    crraUtil ρ (μ * W) + μ ^ (-ρ) * (1 - μ) ^ ρ * crraUtil ρ (W - μ * W)
      = μ ^ (-ρ) * crraUtil ρ W := by
  have h1 : 0 < 1 - μ := by linarith
  have hbb : (1 - μ) ^ ρ * (1 - μ) ^ (-ρ) = 1 := by
    rw [Real.rpow_neg h1.le, mul_inv_cancel₀ (Real.rpow_pos_of_pos h1 _).ne']
  have hμp : μ ^ (1 - ρ) = μ ^ (-ρ) * μ := by
    rw [show (1 : ℝ) - ρ = -ρ + 1 by ring, Real.rpow_add hμ0, Real.rpow_one]
  have h1p : (1 - μ) ^ (1 - ρ) = (1 - μ) ^ (-ρ) * (1 - μ) := by
    rw [show (1 : ℝ) - ρ = -ρ + 1 by ring, Real.rpow_add h1, Real.rpow_one]
  rw [show W - μ * W = (1 - μ) * W by ring]
  simp only [crraUtil]
  rw [Real.mul_rpow hμ0.le hW.le, Real.mul_rpow h1.le hW.le, hμp, h1p]
  linear_combination μ ^ (-ρ) * (1 - μ) * W ^ (1 - ρ) / (1 - ρ) * hbb

/-- The Bellman equation of O&R Supplement A, pp. 742–744, solved exactly. Let `ρ > 0`,
`ρ ≠ 1`, `β > 0`, let the feasible portfolio `x*` satisfy the portfolio condition (2), and
assume `βE(1 + r°(x*))^{1−ρ} < 1`. With `μ = 1 − [βE(1 + r°)^{1−ρ}]^{1/ρ}` and
`V(W) = μ^{−ρ} W^{1−ρ}/(1−ρ)`, for every `W > 0`: every consumption `0 < C < W` and feasible
portfolio give `u(C) + βE V((1 + r°)(W − C)) ≤ V(W)`, with equality at `C = μW` and `x*`. -/
theorem bellman_crra (Ω : StateSpace S) {β ρ : ℝ} (hβ : 0 < β) (hρ : 0 < ρ) (hρ1 : ρ ≠ 1)
    (r : Fin N → S → ℝ) (k : Fin N) {xs : Fin N → ℝ} (hxs : PortFeasible r xs)
    (hfoc : PortfolioCondition Ω ρ r k xs) (hB : growthFactor Ω β ρ r xs < 1) {W : ℝ}
    (hW : 0 < W) :
    (∀ C x, 0 < C → C < W → PortFeasible r x →
      bellmanRHS Ω β (crraUtil ρ) (crraValue (crraShare Ω β ρ r xs) ρ) r W C x
        ≤ crraValue (crraShare Ω β ρ r xs) ρ W) ∧
    bellmanRHS Ω β (crraUtil ρ) (crraValue (crraShare Ω β ρ r xs) ρ) r W
        (crraShare Ω β ρ r xs * W) xs = crraValue (crraShare Ω β ρ r xs) ρ W := by
  obtain ⟨hμ0, hμ1, hBμ⟩ := crraShare_mem Ω hβ hρ r hxs hB
  set μ := crraShare Ω β ρ r xs
  have hcont : ∀ C x, C < W → PortFeasible r x → bellmanRHS Ω β (crraUtil ρ) (crraValue μ ρ) r W C x
      = crraUtil ρ C + μ ^ (-ρ) * growthFactor Ω β ρ r x * crraUtil ρ (W - C) := by
    intro C x hCW hx
    rw [bellmanRHS, ← expect_next_crra Ω β ρ (μ ^ (-ρ)) r hx (by linarith : 0 < W - C)]
    rfl
  refine ⟨fun C x hC hCW hx => ?_, ?_⟩
  · rw [hcont C x hCW hx]
    have hp : growthFactor Ω β ρ r x * crraUtil ρ (W - C)
        ≤ growthFactor Ω β ρ r xs * crraUtil ρ (W - C) := by
      rw [growthFactor_mul_crraUtil Ω β hρ1, growthFactor_mul_crraUtil Ω β hρ1]
      exact mul_le_mul_of_nonneg_left (portfolio_condition_sufficient Ω hρ hρ1 r k hxs hfoc hx)
        (mul_nonneg hβ.le (Real.rpow_nonneg (by linarith) _))
    have hμr : 0 ≤ μ ^ (-ρ) := Real.rpow_nonneg hμ0.le _
    have := crra_split_le hρ hρ1 hμ0 hμ1 hC hCW
    rw [hBμ] at this
    unfold crraValue
    nlinarith [mul_le_mul_of_nonneg_left hp hμr]
  · rw [hcont _ xs (by nlinarith) hxs, ← hBμ, mul_assoc (μ ^ (-ρ))]
    unfold crraValue
    rw [← mul_assoc]
    exact crra_split_eq hμ0 hμ1 hW

/-- The derivative of CRRA utility, `u′(C) = C^{−ρ}` (O&R Supplement A, p. 742; `ρ ≠ 1`). -/
theorem hasDerivAt_crraUtil {ρ : ℝ} (hρ1 : ρ ≠ 1) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (crraUtil ρ) (x ^ (-ρ)) x := by
  have hp : (1 : ℝ) - ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm hρ1)
  have h := HasDerivAt.div_const (HasDerivAt.rpow_const (p := 1 - ρ) (hasDerivAt_id x)
    (Or.inl hx.ne')) (1 - ρ)
  simp only [id] at h
  rw [show (1 : ℝ) - ρ - 1 = -ρ by ring] at h
  have e : 1 * (1 - ρ) * x ^ (-ρ) / (1 - ρ) = x ^ (-ρ) := by field_simp
  rw [e] at h
  exact h

/-- Solving the Bellman equation for the guess, O&R Supplement A, pp. 743–744. Suppose
`V(W) = A W^{1−ρ}/(1−ρ)` satisfies the Bellman equation at some `W > 0` with the
optimal portfolio `x*`, the maximum over consumption `0 < C < W` being attained at `C = μW` with
`0 < μ < 1`. Then `A = μ^{−ρ}` and `μ = 1 − [βE(1 + r°)^{1−ρ}]^{1/ρ}` (the first-order condition
in `C` and value matching; `ρ > 0`, `ρ ≠ 1`, `β > 0`). -/
theorem bellman_guess_pins_share (Ω : StateSpace S) {β ρ : ℝ} (hβ : 0 < β) (hρ : 0 < ρ)
    (hρ1 : ρ ≠ 1) (r : Fin N → S → ℝ) {xs : Fin N → ℝ} (hxs : PortFeasible r xs)
    {A μ W : ℝ} (hμ0 : 0 < μ) (hμ1 : μ < 1) (hW : 0 < W)
    (hmax : ∀ C, 0 < C → C < W → bellmanRHS Ω β (crraUtil ρ) (fun w => A * crraUtil ρ w) r W C xs
      ≤ bellmanRHS Ω β (crraUtil ρ) (fun w => A * crraUtil ρ w) r W (μ * W) xs)
    (hval : bellmanRHS Ω β (crraUtil ρ) (fun w => A * crraUtil ρ w) r W (μ * W) xs
      = A * crraUtil ρ W) :
    A = μ ^ (-ρ) ∧ μ = crraShare Ω β ρ r xs := by
  set B := growthFactor Ω β ρ r xs with hB_def
  have hB := growthFactor_pos Ω hβ ρ r hxs
  have h1 : 0 < 1 - μ := by linarith
  have hμW : 0 < μ * W := mul_pos hμ0 hW
  have hp : (1 : ℝ) - ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm hρ1)
  have hg : ∀ C, C < W → bellmanRHS Ω β (crraUtil ρ) (fun w => A * crraUtil ρ w) r W C xs
      = crraUtil ρ C + A * B * crraUtil ρ (W - C) := by
    intro C hCW
    rw [bellmanRHS, ← expect_next_crra Ω β ρ A r hxs (by linarith : 0 < W - C)]
  have hμWW : μ * W < W := by nlinarith
  have hloc : IsLocalMax (fun C => crraUtil ρ C + A * B * crraUtil ρ (W - C)) (μ * W) := by
    filter_upwards [Ioo_mem_nhds hμW hμWW] with C hC
    rw [← hg C hC.2, ← hg _ hμWW]
    exact hmax C hC.1 hC.2
  have hd : HasDerivAt (fun C => crraUtil ρ C + A * B * crraUtil ρ (W - C))
      ((μ * W) ^ (-ρ) + A * B * ((W - μ * W) ^ (-ρ) * (-1))) (μ * W) := by
    have hin : HasDerivAt (fun C : ℝ => W - C) (-1) (μ * W) := by
      simpa using HasDerivAt.const_sub W (hasDerivAt_id (μ * W))
    have hout := HasDerivAt.comp_of_eq (μ * W) (hasDerivAt_crraUtil hρ1
      (by linarith : 0 < W - μ * W)) hin rfl
    exact HasDerivAt.add (hasDerivAt_crraUtil hρ1 hμW) (HasDerivAt.const_mul (A * B) hout)
  have hfoc := hloc.hasDerivAt_eq_zero hd
  rw [show W - μ * W = (1 - μ) * W by ring, Real.mul_rpow hμ0.le hW.le,
    Real.mul_rpow h1.le hW.le] at hfoc
  have hWr : 0 < W ^ (-ρ) := Real.rpow_pos_of_pos hW _
  have foc : μ ^ (-ρ) = A * B * (1 - μ) ^ (-ρ) := by
    have : W ^ (-ρ) * (μ ^ (-ρ) - A * B * (1 - μ) ^ (-ρ)) = 0 := by linarith
    have := (mul_eq_zero.mp this).resolve_left hWr.ne'
    linarith
  rw [hg _ hμWW] at hval
  have hμp : μ ^ (1 - ρ) = μ ^ (-ρ) * μ := by
    rw [show (1 : ℝ) - ρ = -ρ + 1 by ring, Real.rpow_add hμ0, Real.rpow_one]
  have h1p : (1 - μ) ^ (1 - ρ) = (1 - μ) ^ (-ρ) * (1 - μ) := by
    rw [show (1 : ℝ) - ρ = -ρ + 1 by ring, Real.rpow_add h1, Real.rpow_one]
  rw [show W - μ * W = (1 - μ) * W by ring] at hval
  simp only [crraUtil] at hval
  rw [Real.mul_rpow hμ0.le hW.le, Real.mul_rpow h1.le hW.le, hμp, h1p] at hval
  field_simp at hval
  have hA' : A = μ ^ (-ρ) := by linear_combination -hval - (1 - μ) * foc
  refine ⟨hA', ?_⟩
  have hμr : 0 < μ ^ (-ρ) := Real.rpow_pos_of_pos hμ0 _
  have hB1 : B * (1 - μ) ^ (-ρ) = 1 := by
    rw [hA'] at foc
    have : μ ^ (-ρ) * (B * (1 - μ) ^ (-ρ) - 1) = 0 := by linear_combination -foc
    have := (mul_eq_zero.mp this).resolve_left hμr.ne'
    linarith
  have hBe : B = (1 - μ) ^ ρ := by
    rw [Real.rpow_neg h1.le] at hB1
    field_simp at hB1
    exact hB1
  rw [crraShare, ← hB_def, hBe, one_div, Real.rpow_rpow_inv h1.le hρ.ne']
  ring

/-- The share is the i.i.d. fixed point of the book's recursion, O&R Supplement A, p. 744:
`μ = (1 + [βE{(1 + r°)^{1−ρ} μ^{−ρ}}]^{1/ρ})^{−1}` (via `EventTree.crra_iid_share`). -/
theorem crraShare_iid_recursion (Ω : StateSpace S) {β ρ : ℝ} (hβ : 0 < β) (hρ : 0 < ρ)
    (r : Fin N → S → ℝ) {xs : Fin N → ℝ} (hxs : PortFeasible r xs)
    (hB : growthFactor Ω β ρ r xs < 1) :
    crraShare Ω β ρ r xs = (1 + (β * ∑ s, Ω.prob s * ((1 + portRet r xs s) ^ (1 - ρ)
      * crraShare Ω β ρ r xs ^ (-ρ))) ^ (1 / ρ))⁻¹ := by
  obtain ⟨hμ0, hμ1, -⟩ := crraShare_mem Ω hβ hρ r hxs hB
  exact (crra_iid_share Ω.prob (portRet r xs) Ω.prob_nonneg hxs.2 hβ.le hρ hμ0 hμ1).mpr rfl

/-- The consumption Euler equation (1), O&R Supplement A, pp. 742–744, at the solution:
with `C_t = μW_t`, `W_{t+1} = (1 + r°)(1 − μ)W_t` and `C_{t+1} = μW_{t+1}`,
`C_t^{−ρ} = βE[(1 + r°) C_{t+1}^{−ρ}]` for every `W_t > 0` (via
`EventTree.crra_share_recursion`). -/
theorem crraShare_euler (Ω : StateSpace S) {β ρ : ℝ} (hβ : 0 < β) (hρ : 0 < ρ)
    (r : Fin N → S → ℝ) {xs : Fin N → ℝ} (hxs : PortFeasible r xs)
    (hB : growthFactor Ω β ρ r xs < 1) {W : ℝ} (hW : 0 < W) :
    (crraShare Ω β ρ r xs * W) ^ (-ρ) = β * ∑ s, Ω.prob s * ((1 + portRet r xs s)
      * (crraShare Ω β ρ r xs * ((1 + portRet r xs s) * (1 - crraShare Ω β ρ r xs) * W))
        ^ (-ρ)) := by
  obtain ⟨hμ0, hμ1, -⟩ := crraShare_mem Ω hβ hρ r hxs hB
  exact (crra_share_recursion Ω.prob (portRet r xs) (fun _ => crraShare Ω β ρ r xs)
    Ω.prob_nonneg hxs.2 (fun _ => hμ0) hβ.le hρ hμ0 hμ1 hW).mpr
    (crraShare_iid_recursion Ω hβ hρ r hxs hB)

/-! ## The log case -/

/-- The constant of the log value function (O&R Supplement A, p. 743):
`K = [log(1 − β) + (β/(1 − β))(log β + E log(1 + r°))]/(1 − β)` at the portfolio `x`. -/
noncomputable def logValueConst (Ω : StateSpace S) (β : ℝ) (r : Fin N → S → ℝ)
    (x : Fin N → ℝ) : ℝ :=
  (Real.log (1 - β) + β / (1 - β) * (Real.log β + logPortObj Ω r x)) / (1 - β)

/-- The log value function `V(W) = log W/(1 − β) + K` (O&R Supplement A, p. 743). -/
noncomputable def logValue (Ω : StateSpace S) (β : ℝ) (r : Fin N → S → ℝ) (x : Fin N → ℝ)
    (W : ℝ) : ℝ :=
  Real.log W / (1 - β) + logValueConst Ω β r x

/-- The log continuation value, O&R Supplement A, p. 743: for `D = W − C > 0` and a feasible
portfolio `x`, `βE V((1 + r°(x))D) = (β/(1 − β))(E log(1 + r°(x)) + log D) + βK`. -/
theorem expect_next_log (Ω : StateSpace S) (β : ℝ) (r : Fin N → S → ℝ) (xs : Fin N → ℝ)
    {x : Fin N → ℝ} (hx : PortFeasible r x) {D : ℝ} (hD : 0 < D) :
    β * Ω.expect (fun s => logValue Ω β r xs ((1 + portRet r x s) * D))
      = β / (1 - β) * (logPortObj Ω r x + Real.log D) + β * logValueConst Ω β r xs := by
  have e : ∀ s, Ω.prob s * logValue Ω β r xs ((1 + portRet r x s) * D)
      = Ω.prob s * Real.log (1 + portRet r x s) / (1 - β)
        + Ω.prob s * (Real.log D / (1 - β) + logValueConst Ω β r xs) := by
    intro s
    rw [logValue, Real.log_mul (hx.2 s).ne' hD.ne']
    ring
  simp only [StateSpace.expect, e, Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_mul,
    Ω.prob_sum, logPortObj]
  ring

/-- The Bellman equation with log utility, O&R Supplement A, p. 743, solved exactly: for
`0 < β < 1` and a feasible portfolio `x*` satisfying the log portfolio condition, with
`V(W) = log W/(1 − β) + K`, every `0 < C < W` and feasible portfolio give
`log C + βE V((1 + r°)(W − C)) ≤ V(W)`, with equality at `C = (1 − β)W` and `x*`: the book's
`μ = 1 − β`, whatever the return distribution. -/
theorem bellman_log (Ω : StateSpace S) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (r : Fin N → S → ℝ) (k : Fin N) {xs : Fin N → ℝ} (hxs : PortFeasible r xs)
    (hfoc : LogPortfolioCondition Ω r k xs) {W : ℝ} (hW : 0 < W) :
    (∀ C x, 0 < C → C < W → PortFeasible r x →
      bellmanRHS Ω β Real.log (logValue Ω β r xs) r W C x ≤ logValue Ω β r xs W) ∧
    bellmanRHS Ω β Real.log (logValue Ω β r xs) r W ((1 - β) * W) xs = logValue Ω β r xs W := by
  have h1 : 0 < 1 - β := by linarith
  have hconst : Real.log ((1 - β) * W) + β / (1 - β) * (logPortObj Ω r xs + Real.log (β * W))
      + β * logValueConst Ω β r xs = logValue Ω β r xs W := by
    rw [logValue, logValueConst, Real.log_mul h1.ne' hW.ne', Real.log_mul hβ0.ne' hW.ne']
    field_simp
    ring
  refine ⟨fun C x hC hCW hx => ?_, ?_⟩
  · have hD : 0 < W - C := by linarith
    rw [bellmanRHS, expect_next_log Ω β r xs hx hD]
    have hp := log_portfolio_condition_sufficient Ω r k hxs hfoc hx
    have hc : 0 ≤ β / (1 - β) := div_nonneg hβ0.le h1.le
    have t1 := log_tangent (mul_pos h1 hW) hC
    have t2 := log_tangent (mul_pos hβ0 hW) hD
    have e1 : β / (1 - β) * (1 / (β * W)) = 1 / ((1 - β) * W) := by field_simp
    have t2' := mul_le_mul_of_nonneg_left t2 hc
    rw [← hconst]
    have lin : 1 / ((1 - β) * W) * (C - (1 - β) * W)
        + β / (1 - β) * (1 / (β * W) * (W - C - β * W)) = 0 := by
      rw [← mul_assoc, e1]; ring
    nlinarith [mul_le_mul_of_nonneg_left hp hc]
  · rw [bellmanRHS, expect_next_log Ω β r xs hxs (by nlinarith), ← hconst,
      show W - (1 - β) * W = β * W by ring]
    ring

/-! ## Verification on the i.i.d. event tree

A plan chooses consumption `c n h` and a portfolio `x n h` at every history `h` of every date
`t = n + 1` of the i.i.d. tree; wealth then follows `W_{t+1} = (1 + r°(x_t))(W_t − C_t)`. -/

/-- Wealth along a plan (O&R Supplement A, p. 742): `W₁ = W₀` and, after the event `s` following
the history `h`, `W(h, s) = (1 + r°(x(h))(s))(W(h) − c(h))`. -/
noncomputable def wealth (r : Fin N → S → ℝ) (W₀ : ℝ) (c : (n : ℕ) → (Fin n → S) → ℝ)
    (x : (n : ℕ) → (Fin n → S) → Fin N → ℝ) : (n : ℕ) → (Fin n → S) → ℝ
  | 0, _ => W₀
  | n + 1, g => (1 + portRet r (x n (Fin.init g)) (g (Fin.last n)))
      * (wealth r W₀ c x n (Fin.init g) - c n (Fin.init g))

omit [Fintype S] in
/-- The wealth-accumulation identity along a plan, O&R Supplement A, p. 742:
`W_{t+1} = (1 + r°_{t+1})(W_t − C_t)` after the event `s`. -/
theorem wealth_snoc (r : Fin N → S → ℝ) (W₀ : ℝ) (c : (n : ℕ) → (Fin n → S) → ℝ)
    (x : (n : ℕ) → (Fin n → S) → Fin N → ℝ) {n : ℕ} (h : Fin n → S) (s : S) :
    wealth r W₀ c x (n + 1) (Fin.snoc h s)
      = (1 + portRet r (x n h) s) * (wealth r W₀ c x n h - c n h) := by
  simp only [wealth, Fin.init_snoc, Fin.snoc_last]

/-- An admissible plan (O&R Supplement A, p. 742): positive consumption, never more than current
wealth (end-of-period financial wealth `W − C ≥ 0`), and portfolio shares adding up to one at
every history. Admissibility for the infinite-horizon problem also requires the utility series
to converge; results state that as a separate `Summable` hypothesis. -/
def Admissible (r : Fin N → S → ℝ) (W₀ : ℝ) (c : (n : ℕ) → (Fin n → S) → ℝ)
    (x : (n : ℕ) → (Fin n → S) → Fin N → ℝ) : Prop :=
  (∀ n h, 0 < c n h) ∧ (∀ n h, c n h ≤ wealth r W₀ c x n h) ∧ (∀ n h, ∑ i, x n h i = 1)

/-- Along an admissible plan the investor saves a positive amount and holds a feasible portfolio
at every history (O&R Supplement A, p. 743, footnote 1: `W_t > C_t`): next period's consumption
must be positive in every state, which forces `W − C > 0` and `1 + r° > 0`. -/
theorem admissible_step (Ω : StateSpace S) (r : Fin N → S → ℝ) (W₀ : ℝ)
    {c : (n : ℕ) → (Fin n → S) → ℝ} {x : (n : ℕ) → (Fin n → S) → Fin N → ℝ}
    (hadm : Admissible r W₀ c x) (n : ℕ) (h : Fin n → S) :
    c n h < wealth r W₀ c x n h ∧ PortFeasible r (x n h) := by
  have hS : Nonempty S := by
    by_contra hS
    rw [not_nonempty_iff] at hS
    have := Ω.prob_sum
    simp [Finset.univ_eq_empty] at this
  have hD : 0 ≤ wealth r W₀ c x n h - c n h := by linarith [hadm.2.1 n h]
  have key : ∀ s, 0 < (1 + portRet r (x n h) s) * (wealth r W₀ c x n h - c n h) := by
    intro s
    rw [← wealth_snoc]
    exact lt_of_lt_of_le (hadm.1 _ _) (hadm.2.1 _ _)
  obtain ⟨s₀⟩ := hS
  have hD' : 0 < wealth r W₀ c x n h - c n h := by
    rcases hD.lt_or_eq with h' | h'
    · exact h'
    · have := key s₀; rw [← h', mul_zero] at this; exact absurd this (lt_irrefl 0)
  exact ⟨by linarith, hadm.2.2 n h, fun s => pos_of_mul_pos_left (key s) hD'.le⟩

/-- Expectation at date `t + 1` on the i.i.d. tree as an expectation over date-`t` histories of
the conditional expectation over the next event (O&R Supplement A, p. 744; the law of iterated
expectations on the event tree of Appendix 5C). -/
theorem sum_succ_iid (Ω : StateSpace S) (n : ℕ) (f : (Fin (n + 1) → S) → ℝ) :
    ∑ g, (iidTree Ω).histProb g * f g
      = ∑ h, (iidTree Ω).histProb h * Ω.expect (fun s => f (Fin.snoc h s)) := by
  rw [sum_snoc]
  refine Finset.sum_congr rfl fun h _ => ?_
  simp only [(iidTree Ω).histProb_snoc, StateSpace.expect, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp only [iidTree]
  ring

/-- The dynamic-programming inequality summed along a plan (O&R Supplement A, p. 742): if
`u(c) + βE V(W′) ≤ V(W)` holds at every history, then for every horizon `n`,
`Σ_{t<n} β^t E u(C_t) + β^n E V(W_n) ≤ V(W₀)`. -/
theorem telescope_le (Ω : StateSpace S) {β : ℝ} (hβ : 0 ≤ β) (u V : ℝ → ℝ)
    (r : Fin N → S → ℝ) (W₀ : ℝ) (c : (n : ℕ) → (Fin n → S) → ℝ)
    (x : (n : ℕ) → (Fin n → S) → Fin N → ℝ)
    (hstep : ∀ n h, u (c n h) + β * Ω.expect (fun s => V ((1 + portRet r (x n h) s)
      * (wealth r W₀ c x n h - c n h))) ≤ V (wealth r W₀ c x n h)) (n : ℕ) :
    ∑ k ∈ range n, utilSeries (iidTree Ω) β u c k
      + β ^ n * ∑ h, (iidTree Ω).histProb h * V (wealth r W₀ c x n h) ≤ V W₀ := by
  induction n with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, pow_zero, one_mul, zero_add,
      Fintype.sum_unique, (iidTree Ω).histProb_zero]
    rfl
  | succ n ih =>
    rw [Finset.sum_range_succ, sum_succ_iid]
    simp only [wealth_snoc]
    have hle : utilSeries (iidTree Ω) β u c n + β ^ (n + 1) * ∑ h, (iidTree Ω).histProb h
        * Ω.expect (fun s => V ((1 + portRet r (x n h) s) * (wealth r W₀ c x n h - c n h)))
        ≤ β ^ n * ∑ h, (iidTree Ω).histProb h * V (wealth r W₀ c x n h) := by
      rw [utilSeries, pow_succ, mul_assoc, ← mul_add, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun h _ => ?_) (pow_nonneg hβ n)
      have := mul_le_mul_of_nonneg_left (hstep n h) ((iidTree Ω).histProb_nonneg h)
      linarith
    linarith

/-- CRRA utility is increasing: `u(c) ≤ u(W)` for `0 < c ≤ W` (from the supporting line at `W`;
O&R Supplement A). -/
theorem crraUtil_mono {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≠ 1) {c W : ℝ} (hc : 0 < c) (hcW : c ≤ W) :
    crraUtil ρ c ≤ crraUtil ρ W := by
  have hW : 0 < W := lt_of_lt_of_le hc hcW
  have t := crra_tangent hρ hρ1 hW hc
  have : W ^ (-ρ) * (c - W) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg hW.le _) (by linarith)
  linarith

/-- The transversality property of the CRRA value function, O&R Supplement A (proved, not
assumed): for every admissible plan with convergent utility series,
`β^t E V(W_t) → 0`, where `V(W) = μ^{−ρ}W^{1−ρ}/(1−ρ)`, under `βE(1 + r°(x*))^{1−ρ} < 1`.
From below, `V(W_t) ≥ μ^{−ρ}u(C_t)` and the terms of a convergent series vanish; from above,
`V ≤ 0` when `ρ > 1`, and `β^{t+1}E V(W_{t+1}) ≤ βE(1+r°)^{1−ρ} · β^t E V(W_t)` when `ρ < 1`. -/
theorem transversality_crra (Ω : StateSpace S) {β ρ : ℝ} (hβ : 0 < β) (hρ : 0 < ρ)
    (hρ1 : ρ ≠ 1) (r : Fin N → S → ℝ) (k : Fin N) {xs : Fin N → ℝ} (hxs : PortFeasible r xs)
    (hfoc : PortfolioCondition Ω ρ r k xs) (hB : growthFactor Ω β ρ r xs < 1) (W₀ : ℝ)
    {c : (n : ℕ) → (Fin n → S) → ℝ} {x : (n : ℕ) → (Fin n → S) → Fin N → ℝ}
    (hadm : Admissible r W₀ c x) (hU : Summable (utilSeries (iidTree Ω) β (crraUtil ρ) c)) :
    Tendsto (fun n => β ^ n * ∑ h, (iidTree Ω).histProb h
      * crraValue (crraShare Ω β ρ r xs) ρ (wealth r W₀ c x n h)) atTop (𝓝 0) := by
  obtain ⟨hμ0, -, -⟩ := crraShare_mem Ω hβ hρ r hxs hB
  set μ := crraShare Ω β ρ r xs
  have hμr : 0 ≤ μ ^ (-ρ) := Real.rpow_nonneg hμ0.le _
  set T := fun n => β ^ n * ∑ h, (iidTree Ω).histProb h * crraValue μ ρ (wealth r W₀ c x n h)
    with hT
  have hlow : ∀ n, μ ^ (-ρ) * utilSeries (iidTree Ω) β (crraUtil ρ) c n ≤ T n := by
    intro n
    rw [hT, utilSeries, ← mul_assoc, mul_comm (μ ^ (-ρ)), mul_assoc, Finset.mul_sum]
    refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun h _ => ?_) (pow_nonneg hβ.le n)
    have hm := crraUtil_mono hρ hρ1 (hadm.1 n h) (hadm.2.1 n h)
    have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hm hμr)
      ((iidTree Ω).histProb_nonneg h)
    unfold crraValue
    linarith
  have hlowT : Tendsto (fun n => μ ^ (-ρ) * utilSeries (iidTree Ω) β (crraUtil ρ) c n) atTop
      (𝓝 0) := by
    simpa using hU.tendsto_atTop_zero.const_mul (μ ^ (-ρ))
  rcases lt_or_gt_of_ne hρ1 with hlt | hgt
  · -- ρ < 1: geometric decay at rate βE(1+r°)^{1−ρ}
    set B := growthFactor Ω β ρ r xs
    have hB0 := growthFactor_pos Ω hβ ρ r hxs
    have hrec : ∀ n, T (n + 1) ≤ B * T n := by
      intro n
      simp only [hT]
      rw [sum_succ_iid]
      simp only [wealth_snoc]
      simp only [Finset.mul_sum]
      refine Finset.sum_le_sum fun h _ => ?_
      obtain ⟨hlt', hxn⟩ := admissible_step Ω r W₀ hadm n h
      have hD : 0 < wealth r W₀ c x n h - c n h := by linarith
      have e := expect_next_crra Ω β ρ (μ ^ (-ρ)) r hxn hD
      have hp : growthFactor Ω β ρ r (x n h) * crraUtil ρ (wealth r W₀ c x n h - c n h)
          ≤ B * crraUtil ρ (wealth r W₀ c x n h - c n h) := by
        rw [growthFactor_mul_crraUtil Ω β hρ1, growthFactor_mul_crraUtil Ω β hρ1]
        exact mul_le_mul_of_nonneg_left
          (portfolio_condition_sufficient Ω hρ hρ1 r k hxs hfoc hxn)
          (mul_nonneg hβ.le (Real.rpow_nonneg hD.le _))
      have hm := crraUtil_mono hρ hρ1 hD (by linarith [hadm.1 n h] :
        wealth r W₀ c x n h - c n h ≤ wealth r W₀ c x n h)
      have hchain : β * Ω.expect (fun s => crraValue μ ρ ((1 + portRet r (x n h) s)
          * (wealth r W₀ c x n h - c n h))) ≤ B * crraValue μ ρ (wealth r W₀ c x n h) := by
        have e' : β * Ω.expect (fun s => crraValue μ ρ ((1 + portRet r (x n h) s)
            * (wealth r W₀ c x n h - c n h))) = μ ^ (-ρ) * growthFactor Ω β ρ r (x n h)
              * crraUtil ρ (wealth r W₀ c x n h - c n h) := e
        rw [e']
        unfold crraValue
        nlinarith [mul_le_mul_of_nonneg_left hp hμr, mul_le_mul_of_nonneg_left hm
          (mul_nonneg hμr hB0.le)]
      have h3 := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hchain ((iidTree Ω).histProb_nonneg h)) (pow_nonneg hβ.le n)
      calc β ^ (n + 1) * ((iidTree Ω).histProb h * Ω.expect (fun s => crraValue μ ρ
            ((1 + portRet r (x n h) s) * (wealth r W₀ c x n h - c n h))))
          = β ^ n * ((iidTree Ω).histProb h * (β * Ω.expect (fun s => crraValue μ ρ
            ((1 + portRet r (x n h) s) * (wealth r W₀ c x n h - c n h))))) := by ring
        _ ≤ β ^ n * ((iidTree Ω).histProb h * (B * crraValue μ ρ (wealth r W₀ c x n h))) := h3
        _ = B * (β ^ n * ((iidTree Ω).histProb h * crraValue μ ρ (wealth r W₀ c x n h))) := by
          ring
    have hgeo : ∀ n, T n ≤ B ^ n * T 0 := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        calc T (n + 1) ≤ B * T n := hrec n
          _ ≤ B * (B ^ n * T 0) := mul_le_mul_of_nonneg_left ih hB0.le
          _ = B ^ (n + 1) * T 0 := by ring
    have hup : Tendsto (fun n => B ^ n * T 0) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hB0.le hB).mul_const (T 0)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlowT hup hlow hgeo
  · -- ρ > 1: the value function is negative
    have hup : ∀ n, T n ≤ 0 := by
      intro n
      refine mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hβ.le n)
        (Finset.sum_nonpos fun h _ => mul_nonpos_of_nonneg_of_nonpos
          ((iidTree Ω).histProb_nonneg h) ?_)
      exact mul_nonpos_of_nonneg_of_nonpos hμr (div_nonpos_of_nonneg_of_nonpos
        (Real.rpow_nonneg (lt_of_lt_of_le (hadm.1 n h) (hadm.2.1 n h)).le _) (by linarith))
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlowT tendsto_const_nhds hlow hup

/-- The upper half of the verification theorem, O&R Supplement A, pp. 742–744: under the
hypotheses of `bellman_crra` (`ρ > 0`, `ρ ≠ 1`, `β > 0`, `x*` feasible with the portfolio
condition (2), `βE(1 + r°(x*))^{1−ρ} < 1`) and `W₀ > 0`, every admissible plan whose utility
series converges achieves lifetime expected utility at most `V(W₀) = μ^{−ρ}W₀^{1−ρ}/(1−ρ)`. -/
theorem verification_upper_crra (Ω : StateSpace S) {β ρ : ℝ} (hβ : 0 < β) (hρ : 0 < ρ)
    (hρ1 : ρ ≠ 1) (r : Fin N → S → ℝ) (k : Fin N) {xs : Fin N → ℝ} (hxs : PortFeasible r xs)
    (hfoc : PortfolioCondition Ω ρ r k xs) (hB : growthFactor Ω β ρ r xs < 1) (W₀ : ℝ)
    {c : (n : ℕ) → (Fin n → S) → ℝ} {x : (n : ℕ) → (Fin n → S) → Fin N → ℝ}
    (hadm : Admissible r W₀ c x) (hU : Summable (utilSeries (iidTree Ω) β (crraUtil ρ) c)) :
    expectedUtility (iidTree Ω) β (crraUtil ρ) c ≤ crraValue (crraShare Ω β ρ r xs) ρ W₀ := by
  have hstep : ∀ n h, crraUtil ρ (c n h) + β * Ω.expect (fun s =>
      crraValue (crraShare Ω β ρ r xs) ρ ((1 + portRet r (x n h) s)
        * (wealth r W₀ c x n h - c n h))) ≤ crraValue (crraShare Ω β ρ r xs) ρ
          (wealth r W₀ c x n h) := by
    intro n h
    obtain ⟨hlt, hxn⟩ := admissible_step Ω r W₀ hadm n h
    exact (bellman_crra Ω hβ hρ hρ1 r k hxs hfoc hB
      (lt_of_lt_of_le (hadm.1 n h) (hadm.2.1 n h))).1 _ _ (hadm.1 n h) hlt hxn
  have htel := telescope_le Ω hβ.le (crraUtil ρ) (crraValue (crraShare Ω β ρ r xs) ρ) r W₀ c x
    hstep
  have hT := transversality_crra Ω hβ hρ hρ1 r k hxs hfoc hB W₀ hadm hU
  have h2 := (tendsto_const_nhds (x := crraValue (crraShare Ω β ρ r xs) ρ W₀)).sub hT
  rw [sub_zero] at h2
  exact le_of_tendsto_of_tendsto' hU.hasSum.tendsto_sum_nat h2 fun n => by linarith [htel n]

/-- Wealth under the optimal policy (O&R Supplement A, p. 744): `W*₁ = W₀` and
`W*(h, s) = (1 + r°(x*)(s))(1 − μ)W*(h)`. -/
noncomputable def optWealth (r : Fin N → S → ℝ) (xs : Fin N → ℝ) (μ W₀ : ℝ) :
    (n : ℕ) → (Fin n → S) → ℝ
  | 0, _ => W₀
  | n + 1, g => (1 + portRet r xs (g (Fin.last n))) * ((1 - μ) * optWealth r xs μ W₀ n (Fin.init g))

omit [Fintype S] in
/-- Optimal wealth after the event `s`, `W*(h, s) = (1 + r°(x*)(s))(1 − μ)W*(h)`
(O&R Supplement A, p. 744). -/
theorem optWealth_snoc (r : Fin N → S → ℝ) (xs : Fin N → ℝ) (μ W₀ : ℝ) {n : ℕ}
    (h : Fin n → S) (s : S) :
    optWealth r xs μ W₀ (n + 1) (Fin.snoc h s)
      = (1 + portRet r xs s) * ((1 - μ) * optWealth r xs μ W₀ n h) := by
  simp only [optWealth, Fin.init_snoc, Fin.snoc_last]

omit [Fintype S] in
/-- Optimal wealth stays positive (O&R Supplement A, p. 744; `μ < 1`, `1 + r°(x*) > 0`). -/
theorem optWealth_pos (r : Fin N → S → ℝ) {xs : Fin N → ℝ} (hxs : ∀ s, 0 < 1 + portRet r xs s)
    {μ W₀ : ℝ} (hμ1 : μ < 1) (hW₀ : 0 < W₀) : ∀ n h, 0 < optWealth r xs μ W₀ n h := by
  intro n
  induction n with
  | zero => intro h; exact hW₀
  | succ n ih =>
    intro g
    simp only [optWealth]
    exact mul_pos (hxs _) (mul_pos (by linarith) (ih _))

omit [Fintype S] in
/-- The policy `C = μW` with the portfolio `x*` generates the optimal wealth path: the wealth
of the plan `c = μW*`, `x = x*` is `W*` (O&R Supplement A, p. 744). -/
theorem wealth_optPlan (r : Fin N → S → ℝ) (xs : Fin N → ℝ) (μ W₀ : ℝ) :
    wealth r W₀ (fun n h => μ * optWealth r xs μ W₀ n h) (fun _ _ => xs)
      = optWealth r xs μ W₀ := by
  funext n
  induction n with
  | zero => rfl
  | succ n ih =>
    funext g
    simp only [wealth, optWealth, ih]
    ring

omit [Fintype S] in
/-- The optimal policy is admissible (O&R Supplement A, p. 744): `C = μW` with `0 < μ < 1` and
a feasible portfolio `x*` held at every history. -/
theorem optPlan_admissible (r : Fin N → S → ℝ) {xs : Fin N → ℝ} (hxs : PortFeasible r xs)
    {μ W₀ : ℝ} (hμ0 : 0 < μ) (hμ1 : μ < 1) (hW₀ : 0 < W₀) :
    Admissible r W₀ (fun n h => μ * optWealth r xs μ W₀ n h) (fun _ _ => xs) := by
  have hp := optWealth_pos r hxs.2 hμ1 hW₀
  refine ⟨fun n h => mul_pos hμ0 (hp n h), fun n h => ?_, fun _ _ => hxs.1⟩
  rw [wealth_optPlan]
  have := hp n h
  nlinarith

/-- The `(1−ρ)`-th moment of optimal wealth, O&R Supplement A, p. 744: with
`(1 − μ)^ρ = βE(1 + r°)^{1−ρ}`, `β^t E[(W*_t)^{1−ρ}] = (1 − μ)^t W₀^{1−ρ}`. -/
theorem optWealth_moment (Ω : StateSpace S) (β ρ : ℝ) (r : Fin N → S → ℝ) {xs : Fin N → ℝ}
    (hxs : PortFeasible r xs) {μ W₀ : ℝ} (hμ1 : μ < 1) (hW₀ : 0 < W₀)
    (hBμ : (1 - μ) ^ ρ = growthFactor Ω β ρ r xs) (n : ℕ) :
    β ^ n * ∑ h, (iidTree Ω).histProb h * optWealth r xs μ W₀ n h ^ (1 - ρ)
      = (1 - μ) ^ n * W₀ ^ (1 - ρ) := by
  have h1 : 0 < 1 - μ := by linarith
  have hp := optWealth_pos r hxs.2 hμ1 hW₀
  have hcomb : growthFactor Ω β ρ r xs * (1 - μ) ^ (1 - ρ) = 1 - μ := by
    rw [← hBμ, ← Real.rpow_add h1, show ρ + (1 - ρ) = 1 by ring, Real.rpow_one]
  induction n with
  | zero =>
    simp only [pow_zero, one_mul, Fintype.sum_unique, (iidTree Ω).histProb_zero]
    rfl
  | succ n ih =>
    rw [sum_succ_iid]
    simp only [optWealth_snoc]
    have e : ∀ h, Ω.expect (fun s => ((1 + portRet r xs s) * ((1 - μ) * optWealth r xs μ W₀ n h))
        ^ (1 - ρ)) = Ω.expect (fun s => (1 + portRet r xs s) ^ (1 - ρ)) * (1 - μ) ^ (1 - ρ)
          * optWealth r xs μ W₀ n h ^ (1 - ρ) := by
      intro h
      simp only [StateSpace.expect, Finset.sum_mul]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [Real.mul_rpow (hxs.2 s).le (mul_pos h1 (hp n h)).le,
        Real.mul_rpow h1.le (hp n h).le]
      ring
    simp only [e]
    have e2 : β ^ (n + 1) * ∑ h, (iidTree Ω).histProb h * (Ω.expect (fun s =>
        (1 + portRet r xs s) ^ (1 - ρ)) * (1 - μ) ^ (1 - ρ) * optWealth r xs μ W₀ n h ^ (1 - ρ))
        = growthFactor Ω β ρ r xs * (1 - μ) ^ (1 - ρ)
          * (β ^ n * ∑ h, (iidTree Ω).histProb h * optWealth r xs μ W₀ n h ^ (1 - ρ)) := by
      simp only [growthFactor, Finset.mul_sum]
      refine Finset.sum_congr rfl fun h _ => ?_
      ring
    rw [e2, ih, hcomb]
    ring

/-- The verification theorem for CRRA utility, O&R Supplement A, pp. 742–744, on the i.i.d.
tree over the infinite horizon. Assume `ρ > 0`, `ρ ≠ 1`, `β > 0`, a feasible portfolio `x*`
satisfying the portfolio condition (2), the parameter condition `βE(1 + r°(x*))^{1−ρ} < 1`,
and initial wealth `W₀ > 0`; let `μ = 1 − [βE(1 + r°(x*))^{1−ρ}]^{1/ρ}` and
`V(W) = μ^{−ρ}W^{1−ρ}/(1−ρ)`. Then the policy `C = μW`, `x = x*` is admissible, its utility
series converges and it attains `V(W₀)`; and every admissible plan (any consumption and
portfolio at each history, `0 < C ≤ W`, convergent utility series) achieves at most `V(W₀)`. -/
theorem verification_crra (Ω : StateSpace S) {β ρ : ℝ} (hβ : 0 < β) (hρ : 0 < ρ)
    (hρ1 : ρ ≠ 1) (r : Fin N → S → ℝ) (k : Fin N) {xs : Fin N → ℝ} (hxs : PortFeasible r xs)
    (hfoc : PortfolioCondition Ω ρ r k xs) (hB : growthFactor Ω β ρ r xs < 1) {W₀ : ℝ}
    (hW₀ : 0 < W₀) :
    let μ := crraShare Ω β ρ r xs
    let cStar := fun n (h : Fin n → S) => μ * optWealth r xs μ W₀ n h
    Admissible r W₀ cStar (fun _ _ => xs) ∧
      Summable (utilSeries (iidTree Ω) β (crraUtil ρ) cStar) ∧
      expectedUtility (iidTree Ω) β (crraUtil ρ) cStar = crraValue μ ρ W₀ ∧
      ∀ (c : (n : ℕ) → (Fin n → S) → ℝ) (x : (n : ℕ) → (Fin n → S) → Fin N → ℝ),
        Admissible r W₀ c x → Summable (utilSeries (iidTree Ω) β (crraUtil ρ) c) →
        expectedUtility (iidTree Ω) β (crraUtil ρ) c ≤ crraValue μ ρ W₀ := by
  intro μ cStar
  obtain ⟨hμ0, hμ1, hBμ⟩ := crraShare_mem Ω hβ hρ r hxs hB
  have h1 : 0 < 1 - μ := by linarith
  have hp := optWealth_pos r hxs.2 hμ1 hW₀
  have hμp : μ ^ (1 - ρ) = μ ^ (-ρ) * μ := by
    rw [show (1 : ℝ) - ρ = -ρ + 1 by ring, Real.rpow_add hμ0, Real.rpow_one]
  have hterm : ∀ n, utilSeries (iidTree Ω) β (crraUtil ρ) cStar n
      = μ ^ (1 - ρ) / (1 - ρ) * W₀ ^ (1 - ρ) * (1 - μ) ^ n := by
    intro n
    have hm := optWealth_moment Ω β ρ r hxs hμ1 hW₀ hBμ n
    have e : utilSeries (iidTree Ω) β (crraUtil ρ) cStar n = μ ^ (1 - ρ) / (1 - ρ)
        * (β ^ n * ∑ h, (iidTree Ω).histProb h * optWealth r xs μ W₀ n h ^ (1 - ρ)) := by
      simp only [utilSeries, cStar, crraUtil, Finset.mul_sum]
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [Real.mul_rpow hμ0.le (hp n h).le]
      ring
    rw [e, hm]
    ring
  have hsum : HasSum (utilSeries (iidTree Ω) β (crraUtil ρ) cStar) (crraValue μ ρ W₀) := by
    have hg := (hasSum_geometric_of_lt_one h1.le (by linarith : 1 - μ < 1)).mul_left
      (μ ^ (1 - ρ) / (1 - ρ) * W₀ ^ (1 - ρ))
    have hv : μ ^ (1 - ρ) / (1 - ρ) * W₀ ^ (1 - ρ) * (1 - (1 - μ))⁻¹ = crraValue μ ρ W₀ := by
      have hμne : μ ≠ 0 := hμ0.ne'
      rw [crraValue, crraUtil, hμp, sub_sub_cancel]
      field_simp
    rw [hv] at hg
    exact (funext hterm) ▸ hg
  exact ⟨optPlan_admissible r hxs hμ0 hμ1 hW₀, hsum.summable, hsum.tsum_eq,
    fun c x hadm hU => verification_upper_crra Ω hβ hρ hρ1 r k hxs hfoc hB W₀ hadm hU⟩

/-! ## Verification with log utility -/

/-- The expected log of wealth grows by at most `E log(1 + r°(x*))` per period along an
admissible plan (O&R Supplement A, p. 743): `Σ_h π(h) log W_t(h) ≤ log W₀ + t E log(1 + r°(x*))`
when `x*` satisfies the log portfolio condition. -/
theorem expect_log_wealth_le (Ω : StateSpace S) (r : Fin N → S → ℝ) (k : Fin N)
    {xs : Fin N → ℝ} (hxs : PortFeasible r xs) (hfoc : LogPortfolioCondition Ω r k xs)
    (W₀ : ℝ) {c : (n : ℕ) → (Fin n → S) → ℝ} {x : (n : ℕ) → (Fin n → S) → Fin N → ℝ}
    (hadm : Admissible r W₀ c x) (n : ℕ) :
    ∑ h, (iidTree Ω).histProb h * Real.log (wealth r W₀ c x n h)
      ≤ Real.log W₀ + n * logPortObj Ω r xs := by
  induction n with
  | zero =>
    simp only [Fintype.sum_unique, (iidTree Ω).histProb_zero, one_mul, CharP.cast_eq_zero,
      zero_mul, add_zero]
    rfl
  | succ n ih =>
    rw [sum_succ_iid]
    simp only [wealth_snoc]
    have hnode : ∀ h, (iidTree Ω).histProb h * Ω.expect (fun s => Real.log
        ((1 + portRet r (x n h) s) * (wealth r W₀ c x n h - c n h)))
        ≤ (iidTree Ω).histProb h * (logPortObj Ω r xs + Real.log (wealth r W₀ c x n h)) := by
      intro h
      obtain ⟨hlt, hxn⟩ := admissible_step Ω r W₀ hadm n h
      have hD : 0 < wealth r W₀ c x n h - c n h := by linarith
      have e : Ω.expect (fun s => Real.log ((1 + portRet r (x n h) s)
          * (wealth r W₀ c x n h - c n h)))
          = logPortObj Ω r (x n h) + Real.log (wealth r W₀ c x n h - c n h) := by
        simp only [StateSpace.expect, logPortObj]
        simp only [Real.log_mul (hxn.2 _).ne' hD.ne', mul_add, Finset.sum_add_distrib,
          ← Finset.sum_mul, Ω.prob_sum, one_mul]
      rw [e]
      refine mul_le_mul_of_nonneg_left ?_ ((iidTree Ω).histProb_nonneg h)
      have h1 := log_portfolio_condition_sufficient Ω r k hxs hfoc hxn
      have h2 := Real.log_le_log hD (by linarith [hadm.1 n h] :
        wealth r W₀ c x n h - c n h ≤ wealth r W₀ c x n h)
      linarith
    have hs := Finset.sum_le_sum fun h (_ : h ∈ univ) => hnode h
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul,
      (iidTree Ω).histProb_sum_eq_one, one_mul] at hs
    push_cast
    linarith

/-- The transversality property of the log value function, O&R Supplement A, p. 743 (proved,
not assumed): for `0 < β < 1` and every admissible plan with convergent utility series,
`β^t E V(W_t) → 0`, where `V(W) = log W/(1 − β) + K`. From below `V(W_t) ≥ log C_t/(1 − β) + K`;
from above `E log W_t ≤ log W₀ + tE log(1 + r°(x*))` and `tβ^t → 0`. -/
theorem transversality_log (Ω : StateSpace S) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (r : Fin N → S → ℝ) (k : Fin N) {xs : Fin N → ℝ} (hxs : PortFeasible r xs)
    (hfoc : LogPortfolioCondition Ω r k xs) (W₀ : ℝ) {c : (n : ℕ) → (Fin n → S) → ℝ}
    {x : (n : ℕ) → (Fin n → S) → Fin N → ℝ} (hadm : Admissible r W₀ c x)
    (hU : Summable (utilSeries (iidTree Ω) β Real.log c)) :
    Tendsto (fun n => β ^ n * ∑ h, (iidTree Ω).histProb h
      * logValue Ω β r xs (wealth r W₀ c x n h)) atTop (𝓝 0) := by
  have h1 : 0 < 1 - β := by linarith
  set K := logValueConst Ω β r xs
  set G := logPortObj Ω r xs
  have hT : ∀ n, β ^ n * ∑ h, (iidTree Ω).histProb h * logValue Ω β r xs (wealth r W₀ c x n h)
      = β ^ n * (∑ h, (iidTree Ω).histProb h * Real.log (wealth r W₀ c x n h)) / (1 - β)
        + β ^ n * K := by
    intro n
    have e : ∑ h, (iidTree Ω).histProb h * logValue Ω β r xs (wealth r W₀ c x n h)
        = (∑ h, (iidTree Ω).histProb h * Real.log (wealth r W₀ c x n h)) / (1 - β)
          + (∑ h : Fin n → S, (iidTree Ω).histProb h) * K := by
      rw [Finset.sum_div, Finset.sum_mul, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun h _ => by unfold logValue; ring
    rw [e, (iidTree Ω).histProb_sum_eq_one]
    ring
  have hlow : ∀ n, utilSeries (iidTree Ω) β Real.log c n / (1 - β) + β ^ n * K
      ≤ β ^ n * ∑ h, (iidTree Ω).histProb h * logValue Ω β r xs (wealth r W₀ c x n h) := by
    intro n
    rw [hT, utilSeries]
    have : ∑ h, (iidTree Ω).histProb h * Real.log (c n h)
        ≤ ∑ h, (iidTree Ω).histProb h * Real.log (wealth r W₀ c x n h) :=
      Finset.sum_le_sum fun h _ => mul_le_mul_of_nonneg_left
        (Real.log_le_log (hadm.1 n h) (hadm.2.1 n h)) ((iidTree Ω).histProb_nonneg h)
    have := mul_le_mul_of_nonneg_left this (pow_nonneg hβ0.le n)
    have := div_le_div_of_nonneg_right this h1.le
    linarith
  have hup : ∀ n, β ^ n * ∑ h, (iidTree Ω).histProb h * logValue Ω β r xs (wealth r W₀ c x n h)
      ≤ (Real.log W₀ / (1 - β) + K) * β ^ n + G / (1 - β) * (n * β ^ n) := by
    intro n
    rw [hT]
    have := mul_le_mul_of_nonneg_left (expect_log_wealth_le Ω r k hxs hfoc W₀ hadm n)
      (pow_nonneg hβ0.le n)
    have := div_le_div_of_nonneg_right this h1.le
    have e : β ^ n * (Real.log W₀ + n * G) / (1 - β) + β ^ n * K
        = (Real.log W₀ / (1 - β) + K) * β ^ n + G / (1 - β) * (n * β ^ n) := by ring
    linarith
  have hgeo := tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1
  have hlowT : Tendsto (fun n => utilSeries (iidTree Ω) β Real.log c n / (1 - β) + β ^ n * K)
      atTop (𝓝 0) := by
    simpa using (hU.tendsto_atTop_zero.div_const (1 - β)).add (hgeo.mul_const K)
  have hupT : Tendsto (fun n : ℕ => (Real.log W₀ / (1 - β) + K) * β ^ n
      + G / (1 - β) * (n * β ^ n)) atTop (𝓝 0) := by
    simpa using (hgeo.const_mul (Real.log W₀ / (1 - β) + K)).add
      ((tendsto_self_mul_const_pow_of_lt_one hβ0.le hβ1).const_mul (G / (1 - β)))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlowT hupT hlow hup

/-- The upper half of the log verification theorem, O&R Supplement A, p. 743: for `0 < β < 1`,
a feasible portfolio `x*` satisfying the log portfolio condition, every admissible plan whose
utility series converges achieves lifetime expected utility at most `V(W₀)`. -/
theorem verification_upper_log (Ω : StateSpace S) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (r : Fin N → S → ℝ) (k : Fin N) {xs : Fin N → ℝ} (hxs : PortFeasible r xs)
    (hfoc : LogPortfolioCondition Ω r k xs) (W₀ : ℝ) {c : (n : ℕ) → (Fin n → S) → ℝ}
    {x : (n : ℕ) → (Fin n → S) → Fin N → ℝ} (hadm : Admissible r W₀ c x)
    (hU : Summable (utilSeries (iidTree Ω) β Real.log c)) :
    expectedUtility (iidTree Ω) β Real.log c ≤ logValue Ω β r xs W₀ := by
  have hstep : ∀ n h, Real.log (c n h) + β * Ω.expect (fun s => logValue Ω β r xs
      ((1 + portRet r (x n h) s) * (wealth r W₀ c x n h - c n h)))
        ≤ logValue Ω β r xs (wealth r W₀ c x n h) := by
    intro n h
    obtain ⟨hlt, hxn⟩ := admissible_step Ω r W₀ hadm n h
    exact (bellman_log Ω hβ0 hβ1 r k hxs hfoc
      (lt_of_lt_of_le (hadm.1 n h) (hadm.2.1 n h))).1 _ _ (hadm.1 n h) hlt hxn
  have htel := telescope_le Ω hβ0.le Real.log (logValue Ω β r xs) r W₀ c x hstep
  have hT := transversality_log Ω hβ0 hβ1 r k hxs hfoc W₀ hadm hU
  have h2 := (tendsto_const_nhds (x := logValue Ω β r xs W₀)).sub hT
  rw [sub_zero] at h2
  exact le_of_tendsto_of_tendsto' hU.hasSum.tendsto_sum_nat h2 fun n => by linarith [htel n]

/-- Expected log of optimal wealth under log utility (O&R Supplement A, p. 744): with
`C = (1 − β)W`, `Σ_h π(h) log W*_t(h) = log W₀ + t(log β + E log(1 + r°(x*)))`. -/
theorem optWealth_expect_log (Ω : StateSpace S) {β : ℝ} (hβ0 : 0 < β) (r : Fin N → S → ℝ)
    {xs : Fin N → ℝ} (hxs : PortFeasible r xs) {W₀ : ℝ} (hW₀ : 0 < W₀) (n : ℕ) :
    ∑ h, (iidTree Ω).histProb h * Real.log (optWealth r xs (1 - β) W₀ n h)
      = Real.log W₀ + n * (Real.log β + logPortObj Ω r xs) := by
  have hp := optWealth_pos r hxs.2 (by linarith : 1 - β < 1) hW₀
  induction n with
  | zero =>
    simp only [Fintype.sum_unique, (iidTree Ω).histProb_zero, one_mul, CharP.cast_eq_zero,
      zero_mul, add_zero]
    rfl
  | succ n ih =>
    rw [sum_succ_iid]
    simp only [optWealth_snoc, sub_sub_cancel]
    have e : ∀ h, Ω.expect (fun s => Real.log ((1 + portRet r xs s)
        * (β * optWealth r xs (1 - β) W₀ n h)))
        = logPortObj Ω r xs + Real.log β + Real.log (optWealth r xs (1 - β) W₀ n h) := by
      intro h
      simp only [StateSpace.expect, logPortObj]
      simp only [Real.log_mul (hxs.2 _).ne' (mul_pos hβ0 (hp n h)).ne',
        Real.log_mul hβ0.ne' (hp n h).ne', mul_add, Finset.sum_add_distrib,
        ← Finset.sum_mul, Ω.prob_sum, one_mul]
      ring
    simp only [e, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul,
      (iidTree Ω).histProb_sum_eq_one, one_mul, ih]
    push_cast
    ring

/-- The verification theorem for log utility, O&R Supplement A, pp. 743–744, on the i.i.d. tree
over the infinite horizon: for `0 < β < 1`, a feasible portfolio `x*` satisfying the log
portfolio condition and `W₀ > 0`, with `V(W) = log W/(1 − β) + K`, the policy `C = (1 − β)W`,
`x = x*` (the book's `μ = 1 − β`) is admissible, its utility series converges and it attains
`V(W₀)`; every admissible plan with convergent utility series achieves at most `V(W₀)`. -/
theorem verification_log (Ω : StateSpace S) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (r : Fin N → S → ℝ) (k : Fin N) {xs : Fin N → ℝ} (hxs : PortFeasible r xs)
    (hfoc : LogPortfolioCondition Ω r k xs) {W₀ : ℝ} (hW₀ : 0 < W₀) :
    let cStar := fun n (h : Fin n → S) => (1 - β) * optWealth r xs (1 - β) W₀ n h
    Admissible r W₀ cStar (fun _ _ => xs) ∧
      Summable (utilSeries (iidTree Ω) β Real.log cStar) ∧
      expectedUtility (iidTree Ω) β Real.log cStar = logValue Ω β r xs W₀ ∧
      ∀ (c : (n : ℕ) → (Fin n → S) → ℝ) (x : (n : ℕ) → (Fin n → S) → Fin N → ℝ),
        Admissible r W₀ c x → Summable (utilSeries (iidTree Ω) β Real.log c) →
        expectedUtility (iidTree Ω) β Real.log c ≤ logValue Ω β r xs W₀ := by
  intro cStar
  have h1 : 0 < 1 - β := by linarith
  have hp := optWealth_pos r hxs.2 (by linarith : 1 - β < 1) hW₀
  set a := Real.log (1 - β) + Real.log W₀
  set b := Real.log β + logPortObj Ω r xs
  have hterm : ∀ n, utilSeries (iidTree Ω) β Real.log cStar n = a * β ^ n + b * (n * β ^ n) := by
    intro n
    have e : utilSeries (iidTree Ω) β Real.log cStar n = β ^ n * (Real.log (1 - β)
        + ∑ h, (iidTree Ω).histProb h * Real.log (optWealth r xs (1 - β) W₀ n h)) := by
      simp only [utilSeries, cStar, Real.log_mul h1.ne' (hp n _).ne', mul_add,
        Finset.sum_add_distrib, ← Finset.sum_mul, (iidTree Ω).histProb_sum_eq_one, one_mul]
    rw [e, optWealth_expect_log Ω hβ0 r hxs hW₀ n]
    ring
  have hnorm : ‖β‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos hβ0]; exact hβ1
  have hsum : HasSum (utilSeries (iidTree Ω) β Real.log cStar) (logValue Ω β r xs W₀) := by
    have hg := ((hasSum_geometric_of_lt_one hβ0.le hβ1).mul_left a).add
      ((hasSum_coe_mul_geometric_of_norm_lt_one hnorm).mul_left b)
    have hv : a * (1 - β)⁻¹ + b * (β / (1 - β) ^ 2) = logValue Ω β r xs W₀ := by
      simp only [a, b, logValue, logValueConst]
      field_simp
      ring
    rw [hv] at hg
    exact (funext hterm) ▸ hg
  exact ⟨optPlan_admissible r hxs h1 (by linarith) hW₀, hsum.summable, hsum.tsum_eq,
    fun c x hadm hU => verification_upper_log Ω hβ0 hβ1 r k hxs hfoc W₀ hadm hU⟩

/-! ## Existence of the optimal portfolio

The feasible portfolios form the relatively open set `{Σx = 1, 1 + r° > 0}`. Under a
no-arbitrage (non-redundancy) condition on the finite return matrix its closure is compact;
the concave portfolio objective then has a maximiser, which is interior, so it satisfies (2). -/

/-- No arbitrage and no redundant assets (a condition on the primitives of O&R Supplement A,
p. 742): no zero-cost reallocation `d ≠ 0` (`Σ_n d_n = 0`) has a nonnegative payoff
`Σ_n d_n r^n(s) ≥ 0` in every state. -/
def NoArbitrage (r : Fin N → S → ℝ) : Prop :=
  ∀ d : Fin N → ℝ, ∑ i, d i = 0 → (∀ s, 0 ≤ portRet r d s) → d = 0

/-- The closed feasible set `{Σ_n x_n = 1, 1 + r°(x) ≥ δ in every state}` (O&R Supplement A,
p. 742); `δ = 0` is the closure of the feasible portfolios. -/
def feasibleSet (r : Fin N → S → ℝ) (δ : ℝ) : Set (Fin N → ℝ) :=
  {x | ∑ i, x i = 1 ∧ ∀ s, δ ≤ 1 + portRet r x s}

/-- A probability space of states is nonempty (the probabilities sum to one). -/
theorem nonempty_of_stateSpace (Ω : StateSpace S) : Nonempty S := by
  by_contra hS
  rw [not_nonempty_iff] at hS
  have := Ω.prob_sum
  simp [Finset.univ_eq_empty] at this

omit [Fintype S] in
/-- The portfolio return is linear in the portfolio, `r°(a + c b) = r°(a) + c r°(b)`
(O&R Supplement A, p. 743). -/
theorem portRet_add_smul (r : Fin N → S → ℝ) (a b : Fin N → ℝ) (c : ℝ) (s : S) :
    portRet r (fun i => a i + c * b i) s = portRet r a s + c * portRet r b s := by
  simp only [portRet, add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]

omit [Fintype S] in
/-- Boundedness of the feasible set under no arbitrage (O&R Supplement A, p. 742): there is `R`
with `‖x − e_k‖ ≤ R` for every portfolio with `Σx = 1` and `1 + r°(x) ≥ 0` in every state. The
continuous function `d ↦ Σ_s max(0, −r°(d)(s))` is positive on the compact set of zero-cost
directions of norm one, so it has a positive minimum `ε`; along such a direction some state loses
at least `ε/#S` per unit, which bounds how far a feasible portfolio can go. -/
theorem feasible_bounded [Finite S] [Nonempty S] (r : Fin N → S → ℝ) (hNA : NoArbitrage r)
    (k : Fin N) :
    ∃ R, ∀ x ∈ feasibleSet r 0, ‖x - Pi.single k 1‖ ≤ R := by
  have := Fintype.ofFinite S
  set e : Fin N → ℝ := Pi.single k 1 with he
  have hesum : ∑ i, e i = 1 := by simp [he]
  have hret_e : ∀ s, portRet r e s = r k s := by
    intro s; simp [portRet, he, Pi.single_apply, ite_mul]
  set D : Set (Fin N → ℝ) := Metric.sphere 0 1 ∩ {d | ∑ i, d i = 0} with hD
  have hDc : IsCompact D :=
    (isCompact_sphere 0 1).inter_right (isClosed_eq (by fun_prop) continuous_const)
  set f : (Fin N → ℝ) → ℝ := fun d => ∑ s, max 0 (-portRet r d s) with hf
  have hfc : Continuous f := by
    simp only [hf, portRet]
    fun_prop
  have key : ∀ x ∈ feasibleSet r 0, ∀ d ∈ D, ∀ t : ℝ, 0 ≤ t → x = (fun i => e i + t * d i) →
      t * f d ≤ (1 + ∑ s, |r k s|) * Fintype.card S := by
    intro x hx d _ t ht hxd
    have hs : ∀ s, max 0 (-portRet r d s) * t ≤ 1 + ∑ s, |r k s| := by
      intro s
      have h0 := hx.2 s
      rw [hxd, portRet_add_smul, hret_e] at h0
      have hr : r k s ≤ ∑ s, |r k s| :=
        (le_abs_self _).trans (Finset.single_le_sum (f := fun s => |r k s|)
          (fun s _ => abs_nonneg _) (Finset.mem_univ s))
      rcases le_total 0 (-portRet r d s) with hp | hp
      · rw [max_eq_right hp]; nlinarith
      · rw [max_eq_left hp]; linarith [Finset.sum_nonneg fun s (_ : s ∈ univ) => abs_nonneg (r k s)]
    calc t * f d = ∑ s, max 0 (-portRet r d s) * t := by rw [hf, Finset.mul_sum]; simp [mul_comm]
      _ ≤ ∑ _s : S, (1 + ∑ s, |r k s|) := Finset.sum_le_sum fun s _ => hs s
      _ = (1 + ∑ s, |r k s|) * Fintype.card S := by simp; ring
  have hdecomp : ∀ x ∈ feasibleSet r 0, x - e ≠ 0 →
      ‖x - e‖⁻¹ • (x - e) ∈ D ∧ x = fun i => e i + ‖x - e‖ * (‖x - e‖⁻¹ • (x - e)) i := by
    intro x hx hne
    have hn : ‖x - e‖ ≠ 0 := norm_ne_zero_iff.mpr hne
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn]
    · simp only [Set.mem_ofPred_eq, Pi.smul_apply, Pi.sub_apply, smul_eq_mul, ← Finset.mul_sum,
        Finset.sum_sub_distrib, hx.1, hesum, sub_self, mul_zero]
    · funext i
      simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
      field_simp
      ring
  by_cases hDn : D.Nonempty
  · obtain ⟨d₀, hd₀, hmin⟩ := hDc.exists_isMinOn hDn hfc.continuousOn
    have hε : 0 < f d₀ := by
      have hnn : ∀ s ∈ univ, 0 ≤ max 0 (-portRet r d₀ s) := fun s _ => le_max_left _ _
      rcases (Finset.sum_nonneg hnn).lt_or_eq with h | h
      · exact h
      · exfalso
        have hz := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp h.symm
        have hd0 : d₀ = 0 := hNA d₀ hd₀.2 fun s => by
          have := hz s (Finset.mem_univ s)
          have h2 := le_max_right 0 (-portRet r d₀ s)
          linarith
        have := hd₀.1
        rw [hd0, mem_sphere_zero_iff_norm, norm_zero] at this
        exact zero_ne_one this
    refine ⟨(1 + ∑ s, |r k s|) * Fintype.card S / f d₀, fun x hx => ?_⟩
    rw [le_div_iff₀ hε]
    by_cases hne : x - e = 0
    · rw [hne, norm_zero, zero_mul]
      positivity
    · obtain ⟨hdD, hxd⟩ := hdecomp x hx hne
      have := key x hx _ hdD ‖x - e‖ (norm_nonneg _) hxd
      have hm : f d₀ ≤ f (‖x - e‖⁻¹ • (x - e)) := hmin hdD
      nlinarith [norm_nonneg (x - e)]
  · refine ⟨0, fun x hx => ?_⟩
    by_contra hne
    have hne' : x - e ≠ 0 := by
      intro h; rw [h, norm_zero] at hne; exact hne le_rfl
    exact hDn ⟨_, (hdecomp x hx hne').1⟩

omit [Fintype S] in
/-- The closed feasible sets are compact under no arbitrage (O&R Supplement A, p. 742). -/
theorem isCompact_feasibleSet [Finite S] [Nonempty S] (r : Fin N → S → ℝ) (hNA : NoArbitrage r)
    (k : Fin N) {δ : ℝ} (hδ : 0 ≤ δ) : IsCompact (feasibleSet r δ) := by
  obtain ⟨R, hR⟩ := feasible_bounded r hNA k
  have hcl : IsClosed (feasibleSet r δ) := by
    have e : feasibleSet r δ = {x : Fin N → ℝ | ∑ i, x i = 1}
        ∩ ⋂ s, {x : Fin N → ℝ | δ ≤ 1 + portRet r x s} := by
      ext x; simp [feasibleSet]
    rw [e]
    refine (isClosed_eq (by fun_prop) continuous_const).inter (isClosed_iInter fun s => ?_)
    exact isClosed_le continuous_const (by simp only [portRet]; fun_prop)
  refine (isCompact_closedBall (Pi.single k 1) R).of_isClosed_subset hcl fun x hx => ?_
  rw [Metric.mem_closedBall, dist_eq_norm]
  exact hR x ⟨hx.1, fun s => hδ.trans (hx.2 s)⟩

omit [Fintype S] in
/-- A uniform bound on gross portfolio returns over the closed feasible set under no arbitrage
(O&R Supplement A, p. 742): `1 + r°(x)(s) ≤ Ȳ` for some `Ȳ ≥ 0`. -/
theorem feasible_return_bounded [Finite S] [Nonempty S] (r : Fin N → S → ℝ) (hNA : NoArbitrage r)
    (k : Fin N) : ∃ Yb, 0 ≤ Yb ∧ ∀ x ∈ feasibleSet r 0, ∀ s, 1 + portRet r x s ≤ Yb := by
  have := Fintype.ofFinite S
  obtain ⟨R, hR⟩ := feasible_bounded r hNA k
  set M := ∑ s, ∑ i, |r i s|
  have hM : 0 ≤ M := Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun i _ => abs_nonneg _
  refine ⟨1 + (|R| + 1) * M, by positivity, fun x hx s => ?_⟩
  have hxi : ∀ i, |x i| ≤ |R| + 1 := by
    intro i
    have h1 := (norm_le_pi_norm (x - Pi.single k 1) i).trans (hR x hx)
    have h2 : |(Pi.single k (1 : ℝ) : Fin N → ℝ) i| ≤ 1 := by
      by_cases hi : i = k
      · subst hi; simp
      · simp [hi]
    have h3 : |x i| ≤ |x i - (Pi.single k (1 : ℝ) : Fin N → ℝ) i|
        + |(Pi.single k (1 : ℝ) : Fin N → ℝ) i| := by
      have := abs_add_le (x i - (Pi.single k (1 : ℝ) : Fin N → ℝ) i)
        ((Pi.single k (1 : ℝ) : Fin N → ℝ) i)
      simpa using this
    have h4 : |x i - (Pi.single k (1 : ℝ) : Fin N → ℝ) i| ≤ R := by
      simpa [Real.norm_eq_abs] using h1
    linarith [le_abs_self R]
  have hsum : portRet r x s ≤ (|R| + 1) * ∑ i, |r i s| := by
    simp only [portRet, Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    calc x i * r i s ≤ |x i * r i s| := le_abs_self _
      _ = |x i| * |r i s| := abs_mul _ _
      _ ≤ (|R| + 1) * |r i s| := mul_le_mul_of_nonneg_right (hxi i) (abs_nonneg _)
  have hs : ∑ i, |r i s| ≤ M :=
    Finset.single_le_sum (f := fun s => ∑ i, |r i s|)
      (fun s _ => Finset.sum_nonneg fun i _ => abs_nonneg _) (Finset.mem_univ s)
  nlinarith [abs_nonneg R]

omit [Fintype S] in
/-- From a portfolio maximising the objective over a closed feasible set that captures every
better portfolio, a maximiser over all feasible portfolios (O&R Supplement A, p. 743). -/
theorem exists_max_of_capture (r : Fin N → S → ℝ) (Φ : (Fin N → ℝ) → ℝ) {δ : ℝ} (hδ : 0 < δ)
    (hK : IsCompact (feasibleSet r δ)) (hc : ContinuousOn Φ (feasibleSet r δ))
    {x₀ : Fin N → ℝ} (hx₀ : PortFeasible r x₀)
    (hcap : ∀ x, PortFeasible r x → (∃ s, 1 + portRet r x s < δ) → Φ x < Φ x₀) :
    ∃ xs, PortFeasible r xs ∧ ∀ x, PortFeasible r x → Φ x ≤ Φ xs := by
  have hx₀K : x₀ ∈ feasibleSet r δ := by
    refine ⟨hx₀.1, fun s => ?_⟩
    by_contra h
    exact lt_irrefl _ (hcap x₀ hx₀ ⟨s, lt_of_not_ge h⟩)
  obtain ⟨xs, hxsK, hmax⟩ := hK.exists_isMaxOn ⟨x₀, hx₀K⟩ hc
  refine ⟨xs, ⟨hxsK.1, fun s => lt_of_lt_of_le hδ (hxsK.2 s)⟩, fun x hx => ?_⟩
  by_cases hxK : ∀ s, δ ≤ 1 + portRet r x s
  · exact hmax ⟨hx.1, hxK⟩
  · push Not at hxK
    exact (hcap x hx hxK).le.trans (hmax hx₀K)

/-- Existence of the optimal portfolio for CRRA utility with `ρ > 1`, O&R Supplement A,
p. 743: with all state probabilities positive, no arbitrage and some feasible portfolio, the
objective tends to `−∞` as any gross return tends to zero, so a maximiser exists. -/
theorem exists_optimal_portfolio_gt_one (Ω : StateSpace S) {ρ : ℝ} (hρ : 1 < ρ)
    (r : Fin N → S → ℝ) (k : Fin N) (hπ : ∀ s, 0 < Ω.prob s) (hNA : NoArbitrage r)
    (hF : ∃ x₀, PortFeasible r x₀) :
    ∃ xs, PortFeasible r xs ∧ ∀ x, PortFeasible r x → portObj Ω ρ r x ≤ portObj Ω ρ r xs := by
  classical
  have := nonempty_of_stateSpace Ω
  obtain ⟨x₀, hx₀⟩ := hF
  obtain ⟨s₀, hs₀⟩ := Finite.exists_min Ω.prob
  have hρ0 : 0 < ρ := by linarith
  have hρ1 : ρ ≠ 1 := hρ.ne'
  have hp : 1 - ρ < 0 := by linarith
  set p := Ω.prob s₀
  have hpp : 0 < p := hπ s₀
  have hneg : ∀ y, 0 < y → crraUtil ρ y ≤ 0 := fun y hy =>
    div_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg hy.le _) hp.le
  set Φ₀ := portObj Ω ρ r x₀
  have hΦ₀ : Φ₀ ≤ 0 := Finset.sum_nonpos fun s _ =>
    mul_nonpos_of_nonneg_of_nonpos (Ω.prob_nonneg s) (hneg _ (hx₀.2 s))
  set a := (ρ - 1) * (1 - Φ₀ / p) with ha_def
  have ha : 0 < a := mul_pos (by linarith) (by
    have : Φ₀ / p ≤ 0 := div_nonpos_of_nonpos_of_nonneg hΦ₀ hpp.le
    linarith)
  set δ := a ^ (1 / (1 - ρ)) with hδ_def
  have hδ : 0 < δ := Real.rpow_pos_of_pos ha _
  have huδ : crraUtil ρ δ = Φ₀ / p - 1 := by
    rw [crraUtil, hδ_def, one_div, Real.rpow_inv_rpow ha.le hp.ne, ha_def]
    field_simp
    ring
  refine exists_max_of_capture r (portObj Ω ρ r) hδ (isCompact_feasibleSet r hNA k hδ.le) ?_ hx₀
    ?_
  · refine continuousOn_finsetSum _ fun s _ => continuousOn_const.mul ?_
    refine ContinuousOn.div_const (ContinuousOn.rpow_const (by simp only [portRet]; fun_prop)
      fun x hx => Or.inl (lt_of_lt_of_le hδ (hx.2 s)).ne') _
  · rintro x hx ⟨s, hs⟩
    have h1 : portObj Ω ρ r x ≤ Ω.prob s * crraUtil ρ (1 + portRet r x s) := by
      unfold portObj StateSpace.expect
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ s)]
      have : ∑ s' ∈ univ.erase s, Ω.prob s' * crraUtil ρ (1 + portRet r x s') ≤ 0 :=
        Finset.sum_nonpos fun s' _ => mul_nonpos_of_nonneg_of_nonpos (Ω.prob_nonneg s')
          (hneg _ (hx.2 s'))
      linarith
    have h2 : Ω.prob s * crraUtil ρ (1 + portRet r x s) ≤ Ω.prob s * crraUtil ρ δ :=
      mul_le_mul_of_nonneg_left (crraUtil_mono hρ0 hρ1 (hx.2 s) hs.le) (Ω.prob_nonneg s)
    have h3 : Ω.prob s * crraUtil ρ δ ≤ p * crraUtil ρ δ :=
      mul_le_mul_of_nonpos_right (hs₀ s) (hneg δ hδ)
    have h4 : p * crraUtil ρ δ = Φ₀ - p := by rw [huδ]; field_simp
    linarith

/-- Existence of the optimal portfolio for log utility, O&R Supplement A, p. 743: with all state
probabilities positive, no arbitrage and some feasible portfolio, `E log(1 + r°)` has a
maximiser over the feasible portfolios (it tends to `−∞` at the boundary, and returns are
bounded above on the feasible set). -/
theorem exists_optimal_portfolio_log (Ω : StateSpace S) (r : Fin N → S → ℝ) (k : Fin N)
    (hπ : ∀ s, 0 < Ω.prob s) (hNA : NoArbitrage r) (hF : ∃ x₀, PortFeasible r x₀) :
    ∃ xs, PortFeasible r xs ∧ ∀ x, PortFeasible r x → logPortObj Ω r x ≤ logPortObj Ω r xs := by
  classical
  have := nonempty_of_stateSpace Ω
  obtain ⟨x₀, hx₀⟩ := hF
  obtain ⟨s₀, hs₀⟩ := Finite.exists_min Ω.prob
  obtain ⟨Yb, hYb0, hYb⟩ := feasible_return_bounded r hNA k
  set p := Ω.prob s₀
  have hpp : 0 < p := hπ s₀
  have hlogY : ∀ x ∈ feasibleSet r 0, ∀ s, 0 < 1 + portRet r x s →
      Real.log (1 + portRet r x s) ≤ Yb := fun x hx s hs =>
    ((Real.log_le_sub_one_of_pos hs).trans (by linarith)).trans (hYb x hx s)
  set Φ₀ := logPortObj Ω r x₀
  have hx₀c : x₀ ∈ feasibleSet r 0 := ⟨hx₀.1, fun s => (hx₀.2 s).le⟩
  have hΦ₀ : Φ₀ ≤ Yb := by
    calc Φ₀ ≤ ∑ s, Ω.prob s * Yb := Finset.sum_le_sum fun s _ =>
          mul_le_mul_of_nonneg_left (hlogY x₀ hx₀c s (hx₀.2 s)) (Ω.prob_nonneg s)
      _ = Yb := by rw [← Finset.sum_mul, Ω.prob_sum, one_mul]
  set δ := Real.exp ((Φ₀ - Yb - 1) / p)
  have hδ : 0 < δ := Real.exp_pos _
  have hlogδ : Real.log δ = (Φ₀ - Yb - 1) / p := Real.log_exp _
  have hlogδ0 : Real.log δ ≤ 0 := by
    rw [hlogδ]; exact div_nonpos_of_nonpos_of_nonneg (by linarith) hpp.le
  refine exists_max_of_capture r (logPortObj Ω r) hδ (isCompact_feasibleSet r hNA k hδ.le) ?_
    hx₀ ?_
  · refine continuousOn_finsetSum _ fun s _ => continuousOn_const.mul ?_
    exact ContinuousOn.log (by simp only [portRet]; fun_prop)
      fun x hx => (lt_of_lt_of_le hδ (hx.2 s)).ne'
  · rintro x hx ⟨s, hs⟩
    have hxc : x ∈ feasibleSet r 0 := ⟨hx.1, fun s => (hx.2 s).le⟩
    have h1 : logPortObj Ω r x ≤ Ω.prob s * Real.log (1 + portRet r x s) + Yb := by
      unfold logPortObj StateSpace.expect
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ s)]
      have : ∑ s' ∈ univ.erase s, Ω.prob s' * Real.log (1 + portRet r x s')
          ≤ ∑ s' ∈ univ.erase s, Ω.prob s' * Yb := Finset.sum_le_sum fun s' _ =>
        mul_le_mul_of_nonneg_left (hlogY x hxc s' (hx.2 s')) (Ω.prob_nonneg s')
      have h2 : ∑ s' ∈ univ.erase s, Ω.prob s' * Yb ≤ Yb := by
        rw [← Finset.sum_mul]
        have : ∑ s' ∈ univ.erase s, Ω.prob s' ≤ 1 := by
          rw [← Ω.prob_sum]
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
            fun s' _ _ => Ω.prob_nonneg s'
        nlinarith
      linarith
    have h2 : Real.log (1 + portRet r x s) ≤ Real.log δ := Real.log_le_log (hx.2 s) hs.le
    have h3 : Ω.prob s * Real.log (1 + portRet r x s) ≤ p * Real.log δ := by
      calc Ω.prob s * Real.log (1 + portRet r x s) ≤ Ω.prob s * Real.log δ :=
            mul_le_mul_of_nonneg_left h2 (Ω.prob_nonneg s)
        _ ≤ p * Real.log δ := mul_le_mul_of_nonpos_right (hs₀ s) hlogδ0
    have h4 : p * Real.log δ = Φ₀ - Yb - 1 := by rw [hlogδ]; field_simp
    linarith

/-- Existence of the optimal portfolio for CRRA utility with `0 < ρ < 1`, O&R Supplement A,
p. 743. The objective is continuous on the compact closure of the feasible set, so it has a
maximiser there; the maximiser is interior because marginal utility is infinite at a zero gross
return: moving a fraction `t` towards a feasible portfolio gains at least of order `t^{1−ρ}` in a
state where the gross return was zero and loses at most of order `t` elsewhere (concavity). -/
theorem exists_optimal_portfolio_lt_one (Ω : StateSpace S) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ : ρ < 1)
    (r : Fin N → S → ℝ) (k : Fin N) (hπ : ∀ s, 0 < Ω.prob s) (hNA : NoArbitrage r)
    (hF : ∃ x₀, PortFeasible r x₀) :
    ∃ xs, PortFeasible r xs ∧ ∀ x, PortFeasible r x → portObj Ω ρ r x ≤ portObj Ω ρ r xs := by
  have := nonempty_of_stateSpace Ω
  obtain ⟨x₀, hx₀⟩ := hF
  set p := 1 - ρ with hp_def
  have hp0 : 0 < p := by linarith
  have hp1 : p < 1 := by linarith
  have hx₀K : x₀ ∈ feasibleSet r 0 := ⟨hx₀.1, fun s => (hx₀.2 s).le⟩
  have hcont : Continuous (portObj Ω ρ r) := by
    unfold portObj StateSpace.expect crraUtil
    refine continuous_finsetSum _ fun s _ => continuous_const.mul ?_
    exact (Continuous.rpow_const (by simp only [portRet]; fun_prop)
      fun _ => Or.inr hp0.le).div_const _
  obtain ⟨xb, hxbK, hmax⟩ := (isCompact_feasibleSet r hNA k le_rfl).exists_isMaxOn ⟨x₀, hx₀K⟩
    hcont.continuousOn
  have hint : ∀ s, 0 < 1 + portRet r xb s := by
    by_contra hcon
    push Not at hcon
    obtain ⟨s₀, hs₀⟩ := hcon
    have hb0 : 1 + portRet r xb s₀ = 0 := le_antisymm hs₀ (hxbK.2 s₀)
    set b := fun s => 1 + portRet r xb s
    set a := fun s => 1 + portRet r x₀ s
    have hline : ∀ t : ℝ, ∀ s, 1 + portRet r (fun i => xb i + t * (x₀ i - xb i)) s
        = (1 - t) * b s + t * a s := by
      intro t s
      rw [portRet_add_smul]
      simp only [b, a, portRet, sub_mul, Finset.sum_sub_distrib]
      ring
    have hmem : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        (fun i => xb i + t * (x₀ i - xb i)) ∈ feasibleSet r 0 := by
      intro t ht0 ht1
      refine ⟨?_, fun s => ?_⟩
      · simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, hx₀.1,
          hxbK.1, sub_self, mul_zero, add_zero]
      · rw [hline]
        have := hxbK.2 s
        have := (hx₀.2 s).le
        nlinarith
    set c := Ω.prob s₀ * (a s₀ ^ p / p)
    have hc : 0 < c := mul_pos (hπ s₀) (div_pos (Real.rpow_pos_of_pos (hx₀.2 s₀) _) hp0)
    set M := portObj Ω ρ r xb - portObj Ω ρ r x₀
    have hM : 0 ≤ M := by
      have h : portObj Ω ρ r x₀ ≤ portObj Ω ρ r xb := hmax hx₀K
      simp only [M]; linarith
    set t := (c / (2 * (c + M))) ^ (1 / ρ) with ht_def
    have hq : 0 < c / (2 * (c + M)) := by positivity
    have hq1 : c / (2 * (c + M)) < 1 := by rw [div_lt_one (by positivity)]; linarith
    have ht0 : 0 < t := Real.rpow_pos_of_pos hq _
    have ht1 : t < 1 := Real.rpow_lt_one hq.le hq1 (one_div_pos.mpr hρ0)
    have htρ : t ^ ρ = c / (2 * (c + M)) := by
      rw [ht_def, one_div, Real.rpow_inv_rpow hq.le hρ0.ne']
    have htp : c * t ^ p = 2 * (c + M) * t := by
      rw [hp_def, show (1 : ℝ) - ρ = 1 + -ρ by ring, Real.rpow_add ht0, Real.rpow_one,
        Real.rpow_neg ht0.le, htρ]
      field_simp
    -- per-state concavity bounds
    have hconc : ∀ s, (1 - t) * (b s ^ p / p) + t * (a s ^ p / p)
        ≤ ((1 - t) * b s + t * a s) ^ p / p := by
      intro s
      have h := (Real.concaveOn_rpow hp0.le hp1.le).2 (Set.mem_Ici.mpr (hxbK.2 s))
        (Set.mem_Ici.mpr (hx₀.2 s).le) (by linarith : (0 : ℝ) ≤ 1 - t) ht0.le (by ring)
      simp only [smul_eq_mul] at h
      calc (1 - t) * (b s ^ p / p) + t * (a s ^ p / p) = ((1 - t) * b s ^ p + t * a s ^ p) / p
            := by ring
        _ ≤ ((1 - t) * b s + t * a s) ^ p / p := div_le_div_of_nonneg_right h hp0.le
    have hs0 : ((1 - t) * b s₀ + t * a s₀) ^ p / p
        = (1 - t) * (b s₀ ^ p / p) + t * (a s₀ ^ p / p) + (t ^ p - t) * (a s₀ ^ p / p) := by
      simp only [b] at hb0 ⊢
      rw [hb0, mul_zero, zero_add, Real.mul_rpow ht0.le (hx₀.2 s₀).le,
        Real.zero_rpow hp0.ne']
      ring
    have hsum : (1 - t) * portObj Ω ρ r xb + t * portObj Ω ρ r x₀ + (t ^ p - t) * c
        ≤ portObj Ω ρ r (fun i => xb i + t * (x₀ i - xb i)) := by
      have hterm : ∀ s ∈ univ, 0 ≤ Ω.prob s * (((1 - t) * b s + t * a s) ^ p / p
          - ((1 - t) * (b s ^ p / p) + t * (a s ^ p / p))) := fun s _ =>
        mul_nonneg (Ω.prob_nonneg s) (by linarith [hconc s])
      have hsingle := Finset.single_le_sum hterm (Finset.mem_univ s₀)
      rw [hs0] at hsingle
      have e1 : portObj Ω ρ r (fun i => xb i + t * (x₀ i - xb i))
          = ∑ s, Ω.prob s * (((1 - t) * b s + t * a s) ^ p / p) := by
        simp only [portObj, StateSpace.expect, crraUtil, hline, hp_def]
      have e2 : (1 - t) * portObj Ω ρ r xb + t * portObj Ω ρ r x₀
          = ∑ s, Ω.prob s * ((1 - t) * (b s ^ p / p) + t * (a s ^ p / p)) := by
        simp only [portObj, StateSpace.expect, crraUtil, hp_def, b, a, Finset.mul_sum,
          ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun s _ => by ring
      have e3 : ∑ s, Ω.prob s * (((1 - t) * b s + t * a s) ^ p / p
          - ((1 - t) * (b s ^ p / p) + t * (a s ^ p / p)))
          = ∑ s, Ω.prob s * (((1 - t) * b s + t * a s) ^ p / p)
            - ∑ s, Ω.prob s * ((1 - t) * (b s ^ p / p) + t * (a s ^ p / p)) := by
        rw [← Finset.sum_sub_distrib]; exact Finset.sum_congr rfl fun s _ => by ring
      rw [e1, e2]
      rw [e3] at hsingle
      have : Ω.prob s₀ * ((1 - t) * (b s₀ ^ p / p) + t * (a s₀ ^ p / p)
          + (t ^ p - t) * (a s₀ ^ p / p) - ((1 - t) * (b s₀ ^ p / p) + t * (a s₀ ^ p / p)))
          = (t ^ p - t) * c := by simp only [c]; ring
      linarith
    have hle : portObj Ω ρ r (fun i => xb i + t * (x₀ i - xb i)) ≤ portObj Ω ρ r xb :=
      hmax (hmem t ht0.le ht1.le)
    have : portObj Ω ρ r xb < portObj Ω ρ r (fun i => xb i + t * (x₀ i - xb i)) := by
      have e : (1 - t) * portObj Ω ρ r xb + t * portObj Ω ρ r x₀ + (t ^ p - t) * c
          = portObj Ω ρ r xb + t * (c + M) := by
        simp only [M]; linear_combination htp
      nlinarith
    linarith
  exact ⟨xb, ⟨hxbK.1, hint⟩, fun x hx => hmax ⟨hx.1, fun s => (hx.2 s).le⟩⟩

/-- Existence of an optimal portfolio satisfying the portfolio condition (2), CRRA utility
(`ρ > 0`, `ρ ≠ 1`), O&R Supplement A, p. 743: under positive state probabilities, no arbitrage
and the existence of some feasible portfolio, there is a feasible portfolio maximising the
portfolio objective, and it satisfies (2). -/
theorem exists_optimal_portfolio (Ω : StateSpace S) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≠ 1)
    (r : Fin N → S → ℝ) (k : Fin N) (hπ : ∀ s, 0 < Ω.prob s) (hNA : NoArbitrage r)
    (hF : ∃ x₀, PortFeasible r x₀) :
    ∃ xs, PortFeasible r xs ∧ (∀ x, PortFeasible r x → portObj Ω ρ r x ≤ portObj Ω ρ r xs)
      ∧ PortfolioCondition Ω ρ r k xs := by
  obtain ⟨xs, hxs, hmax⟩ : ∃ xs, PortFeasible r xs ∧
      ∀ x, PortFeasible r x → portObj Ω ρ r x ≤ portObj Ω ρ r xs := by
    rcases lt_or_gt_of_ne hρ1 with h | h
    · exact exists_optimal_portfolio_lt_one Ω hρ h r k hπ hNA hF
    · exact exists_optimal_portfolio_gt_one Ω h r k hπ hNA hF
  exact ⟨xs, hxs, hmax, portfolio_condition_necessary Ω hρ1 r k hxs hmax⟩

/-- Existence of an optimal log portfolio satisfying the log portfolio condition, O&R
Supplement A, p. 743 (positive state probabilities, no arbitrage, some feasible portfolio). -/
theorem exists_optimal_log_portfolio (Ω : StateSpace S) (r : Fin N → S → ℝ) (k : Fin N)
    (hπ : ∀ s, 0 < Ω.prob s) (hNA : NoArbitrage r) (hF : ∃ x₀, PortFeasible r x₀) :
    ∃ xs, PortFeasible r xs ∧ (∀ x, PortFeasible r x → logPortObj Ω r x ≤ logPortObj Ω r xs)
      ∧ LogPortfolioCondition Ω r k xs := by
  obtain ⟨xs, hxs, hmax⟩ := exists_optimal_portfolio_log Ω r k hπ hNA hF
  exact ⟨xs, hxs, hmax, log_portfolio_condition_necessary Ω r k hxs hmax⟩

/-- The verification theorem for CRRA utility from primitives, O&R Supplement A, pp. 742–744:
under positive state probabilities, no arbitrage, some feasible portfolio, and the growth
condition `βE(1 + r°)^{1−ρ} < 1` at optimal portfolios (all optimal portfolios give the same
value, hence the same growth factor), an optimal portfolio `x*` satisfying (2) exists, and with
`μ = 1 − [βE(1 + r°(x*))^{1−ρ}]^{1/ρ}` the policy `C = μW`, `x = x*` attains
`V(W₀) = μ^{−ρ}W₀^{1−ρ}/(1−ρ)`, which no admissible plan exceeds. -/
theorem verification_crra_of_noArbitrage (Ω : StateSpace S) {β ρ : ℝ} (hβ : 0 < β)
    (hρ : 0 < ρ) (hρ1 : ρ ≠ 1) (r : Fin N → S → ℝ) (k : Fin N) (hπ : ∀ s, 0 < Ω.prob s)
    (hNA : NoArbitrage r) (hF : ∃ x₀, PortFeasible r x₀)
    (hB : ∀ x, PortFeasible r x → (∀ x', PortFeasible r x' → portObj Ω ρ r x' ≤ portObj Ω ρ r x)
      → growthFactor Ω β ρ r x < 1) {W₀ : ℝ} (hW₀ : 0 < W₀) :
    ∃ xs, PortFeasible r xs ∧ PortfolioCondition Ω ρ r k xs ∧
      Admissible r W₀ (fun n h => crraShare Ω β ρ r xs * optWealth r xs (crraShare Ω β ρ r xs)
        W₀ n h) (fun _ _ => xs) ∧
      Summable (utilSeries (iidTree Ω) β (crraUtil ρ) fun n h => crraShare Ω β ρ r xs
        * optWealth r xs (crraShare Ω β ρ r xs) W₀ n h) ∧
      expectedUtility (iidTree Ω) β (crraUtil ρ) (fun n h => crraShare Ω β ρ r xs
        * optWealth r xs (crraShare Ω β ρ r xs) W₀ n h) = crraValue (crraShare Ω β ρ r xs) ρ W₀ ∧
      ∀ (c : (n : ℕ) → (Fin n → S) → ℝ) (x : (n : ℕ) → (Fin n → S) → Fin N → ℝ),
        Admissible r W₀ c x → Summable (utilSeries (iidTree Ω) β (crraUtil ρ) c) →
        expectedUtility (iidTree Ω) β (crraUtil ρ) c ≤ crraValue (crraShare Ω β ρ r xs) ρ W₀ := by
  obtain ⟨xs, hxs, hmax, hfoc⟩ := exists_optimal_portfolio Ω hρ hρ1 r k hπ hNA hF
  exact ⟨xs, hxs, hfoc, verification_crra Ω hβ hρ hρ1 r k hxs hfoc (hB xs hxs hmax) hW₀⟩

/-- The verification theorem for log utility from primitives, O&R Supplement A, pp. 743–744:
for `0 < β < 1`, positive state probabilities, no arbitrage and some feasible portfolio, an
optimal portfolio `x*` satisfying the log portfolio condition exists, and the policy
`C = (1 − β)W`, `x = x*` attains `V(W₀) = log W₀/(1 − β) + K`, which no admissible plan
exceeds. -/
theorem verification_log_of_noArbitrage (Ω : StateSpace S) {β : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (r : Fin N → S → ℝ) (k : Fin N) (hπ : ∀ s, 0 < Ω.prob s)
    (hNA : NoArbitrage r) (hF : ∃ x₀, PortFeasible r x₀) {W₀ : ℝ} (hW₀ : 0 < W₀) :
    ∃ xs, PortFeasible r xs ∧ LogPortfolioCondition Ω r k xs ∧
      Admissible r W₀ (fun n h => (1 - β) * optWealth r xs (1 - β) W₀ n h) (fun _ _ => xs) ∧
      Summable (utilSeries (iidTree Ω) β Real.log fun n h =>
        (1 - β) * optWealth r xs (1 - β) W₀ n h) ∧
      expectedUtility (iidTree Ω) β Real.log (fun n h => (1 - β) * optWealth r xs (1 - β) W₀ n h)
        = logValue Ω β r xs W₀ ∧
      ∀ (c : (n : ℕ) → (Fin n → S) → ℝ) (x : (n : ℕ) → (Fin n → S) → Fin N → ℝ),
        Admissible r W₀ c x → Summable (utilSeries (iidTree Ω) β Real.log c) →
        expectedUtility (iidTree Ω) β Real.log c ≤ logValue Ω β r xs W₀ := by
  obtain ⟨xs, hxs, -, hfoc⟩ := exists_optimal_log_portfolio Ω r k hπ hNA hF
  exact ⟨xs, hxs, hfoc, verification_log Ω hβ0 hβ1 r k hxs hfoc hW₀⟩

/-! ## Returns whose distribution varies with the history

O&R Supplement A, p. 744: "for CRRA preferences … `μ` is a function of time … `C = μ_t W`, where
`μ_t` varies only because of variation in the conditional distribution of expected future
returns", with the recursion `μ_t = (1 + [βE_t{(1 + r°_{t+1})^{1−ρ} μ_{t+1}^{−ρ}}]^{1/ρ})^{−1}`.
Here returns `R n h` from a date-`t` history `h` to the next event, and the conditional
probabilities `q n h` of a general event tree, may depend on the history. -/

/-- The weighted portfolio objective `Σ_s w(s)(1 + r°(x)(s))^{1−ρ}/(1−ρ)` (O&R Supplement A,
p. 744: with weights `w(s) = β q(s) μ_{t+1}(s)^{−ρ}` it is the continuation value of a unit of
saving). -/
noncomputable def weightedObj (ρ : ℝ) (r : Fin N → S → ℝ) (w : S → ℝ) (x : Fin N → ℝ) : ℝ :=
  (∑ s, w s * (1 + portRet r x s) ^ (1 - ρ)) / (1 - ρ)

/-- Existence of an optimal portfolio for positive state weights, O&R Supplement A, p. 744: the
weighted problem is the portfolio problem of `exists_optimal_portfolio` under the normalised
weights as probabilities. The maximiser also satisfies the weighted portfolio condition (2),
`Σ_s w(s)(r^n(s) − r^k(s))(1 + r°(s))^{−ρ} = 0`. -/
theorem exists_optimal_weighted [Nonempty S] {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≠ 1)
    (r : Fin N → S → ℝ) (k : Fin N) (w : S → ℝ) (hw : ∀ s, 0 < w s) (hNA : NoArbitrage r)
    (hF : ∃ x₀, PortFeasible r x₀) :
    ∃ xs, PortFeasible r xs ∧ (∀ x, PortFeasible r x → weightedObj ρ r w x ≤ weightedObj ρ r w xs)
      ∧ ∀ n, ∑ s, w s * ((r n s - r k s) * (1 + portRet r xs s) ^ (-ρ)) = 0 := by
  obtain ⟨s₀⟩ := ‹Nonempty S›
  set Z := ∑ s, w s with hZ
  have hZ0 : 0 < Z := Finset.sum_pos (fun s _ => hw s) ⟨s₀, Finset.mem_univ _⟩
  let Ω' : StateSpace S := ⟨fun s => w s / Z, fun s => (div_pos (hw s) hZ0).le, by
    rw [← Finset.sum_div, ← hZ, div_self hZ0.ne']⟩
  have e : ∀ x, portObj Ω' ρ r x = weightedObj ρ r w x / Z := by
    intro x
    simp only [portObj, StateSpace.expect, crraUtil, weightedObj, Ω', Finset.sum_div]
    exact Finset.sum_congr rfl fun s _ => by ring
  obtain ⟨xs, hxs, hmax, hfoc⟩ := exists_optimal_portfolio Ω' hρ hρ1 r k
    (fun s => div_pos (hw s) hZ0) hNA hF
  refine ⟨xs, hxs, fun x hx => ?_, fun n => ?_⟩
  · have := hmax x hx
    rw [e, e] at this
    exact (div_le_div_iff_of_pos_right hZ0).mp this
  · have := hfoc n
    simp only [StateSpace.expect, Ω'] at this
    have e2 : ∑ s, w s / Z * ((r n s - r k s) * (1 + portRet r xs s) ^ (-ρ))
        = (∑ s, w s * ((r n s - r k s) * (1 + portRet r xs s) ^ (-ρ))) / Z := by
      rw [Finset.sum_div]; exact Finset.sum_congr rfl fun s _ => by ring
    rw [e2, div_eq_zero_iff] at this
    exact this.resolve_right hZ0.ne'

/-- A chosen optimal portfolio for the weights `w` (O&R Supplement A, p. 744), by Hilbert choice;
`optPortW_spec` gives its optimality whenever an optimal portfolio exists. -/
noncomputable def optPortW (ρ : ℝ) (r : Fin N → S → ℝ) (w : S → ℝ) : Fin N → ℝ :=
  Classical.epsilon fun xs => PortFeasible r xs ∧
    ∀ x, PortFeasible r x → weightedObj ρ r w x ≤ weightedObj ρ r w xs

/-- The chosen portfolio is feasible and optimal for the weights `w`, under the hypotheses of
`exists_optimal_weighted` (O&R Supplement A, p. 744). -/
theorem optPortW_spec [Nonempty S] {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≠ 1) (r : Fin N → S → ℝ)
    (k : Fin N) (w : S → ℝ) (hw : ∀ s, 0 < w s) (hNA : NoArbitrage r)
    (hF : ∃ x₀, PortFeasible r x₀) :
    PortFeasible r (optPortW ρ r w) ∧ ∀ x, PortFeasible r x →
      weightedObj ρ r w x ≤ weightedObj ρ r w (optPortW ρ r w) := by
  obtain ⟨xs, hxs, hmax, -⟩ := exists_optimal_weighted hρ hρ1 r k w hw hNA hF
  exact Classical.epsilon_spec (p := fun xs => PortFeasible r xs ∧
    ∀ x, PortFeasible r x → weightedObj ρ r w x ≤ weightedObj ρ r w xs) ⟨xs, hxs, hmax⟩

/-- The optimal weighted growth `J(w) = Σ_s w(s)(1 + r°*(s))^{1−ρ}` at the chosen optimal
portfolio (O&R Supplement A, p. 744: `βE_t{(1 + r°_{t+1})^{1−ρ} μ_{t+1}^{−ρ}}`). -/
noncomputable def optJ (ρ : ℝ) (r : Fin N → S → ℝ) (w : S → ℝ) : ℝ :=
  ∑ s, w s * (1 + portRet r (optPortW ρ r w) s) ^ (1 - ρ)

/-- The weighted growth at any portfolio versus the optimum (O&R Supplement A, p. 744): for
`ρ < 1`, `Σ w(1 + r°)^{1−ρ} ≤ J(w)` for every feasible portfolio; for `ρ > 1`, `J(w) ≤` it. -/
theorem optJ_compare [Nonempty S] {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≠ 1) (r : Fin N → S → ℝ)
    (k : Fin N) (w : S → ℝ) (hw : ∀ s, 0 < w s) (hNA : NoArbitrage r)
    (hF : ∃ x₀, PortFeasible r x₀) {x : Fin N → ℝ} (hx : PortFeasible r x) :
    (ρ < 1 → ∑ s, w s * (1 + portRet r x s) ^ (1 - ρ) ≤ optJ ρ r w) ∧
    (1 < ρ → optJ ρ r w ≤ ∑ s, w s * (1 + portRet r x s) ^ (1 - ρ)) := by
  have h := (optPortW_spec hρ hρ1 r k w hw hNA hF).2 x hx
  unfold weightedObj at h
  refine ⟨fun hlt => ?_, fun hgt => ?_⟩
  · exact (div_le_div_iff_of_pos_right (by linarith)).mp h
  · exact (div_le_div_right_of_neg (by linarith)).mp h

/-- The optimal weighted growth is positive for positive weights (O&R Supplement A,
p. 744). -/
theorem optJ_pos [Nonempty S] {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≠ 1) (r : Fin N → S → ℝ)
    (k : Fin N) (w : S → ℝ) (hw : ∀ s, 0 < w s) (hNA : NoArbitrage r)
    (hF : ∃ x₀, PortFeasible r x₀) : 0 < optJ ρ r w := by
  obtain ⟨s₀⟩ := ‹Nonempty S›
  have hf := (optPortW_spec hρ hρ1 r k w hw hNA hF).1
  exact Finset.sum_pos (fun s _ => mul_pos (hw s) (Real.rpow_pos_of_pos (hf.2 s) _))
    ⟨s₀, Finset.mem_univ _⟩

/-- The one-period problem at the date-`t` history `h` of a general event tree: the conditional
probabilities `q(s|h)` as a state space (O&R Appendix 5C, p. 341; Supplement A, p. 744). -/
def nodeSpace (tr : EventTree.Tree S) (n : ℕ) (h : Fin n → S) : StateSpace S :=
  ⟨tr.q n h, tr.q_nonneg n h, tr.q_sum n h⟩

/-- The book's `βE_t{(1 + r°_{t+1})^{1−ρ} μ_{t+1}^{−ρ}}` at the history `h` for the portfolio
`x` (O&R Supplement A, p. 744), with returns `R n h` and next-date shares `μ(h, s)`. -/
noncomputable def nodeGrowth (tr : EventTree.Tree S) (β ρ : ℝ)
    (R : (n : ℕ) → (Fin n → S) → Fin N → S → ℝ) (μ : (n : ℕ) → (Fin n → S) → ℝ) (n : ℕ)
    (h : Fin n → S) (x : Fin N → ℝ) : ℝ :=
  β * ∑ s, tr.q n h s * ((1 + portRet (R n h) x s) ^ (1 - ρ) * μ (n + 1) (Fin.snoc h s) ^ (-ρ))

/-- A solution of the book's share recursion, O&R Supplement A, p. 744: shares
`0 < μ_t(h) < 1` and feasible portfolios `x_t(h)` at every history such that `x_t(h)` maximises
the continuation objective `βE_t{(1 + r°)^{1−ρ} μ_{t+1}^{−ρ}}/(1−ρ)` over feasible portfolios and
`μ_t = (1 + [βE_t{(1 + r°_{t+1})^{1−ρ} μ_{t+1}^{−ρ}}]^{1/ρ})^{−1}` with `r°` the return on
`x_t(h)`. -/
def SolvesShareRecursion (tr : EventTree.Tree S) (β ρ : ℝ)
    (R : (n : ℕ) → (Fin n → S) → Fin N → S → ℝ) (μ : (n : ℕ) → (Fin n → S) → ℝ)
    (xs : (n : ℕ) → (Fin n → S) → Fin N → ℝ) : Prop :=
  (∀ n h, 0 < μ n h ∧ μ n h < 1) ∧ (∀ n h, PortFeasible (R n h) (xs n h)) ∧
  (∀ n h x, PortFeasible (R n h) x →
    nodeGrowth tr β ρ R μ n h x / (1 - ρ) ≤ nodeGrowth tr β ρ R μ n h (xs n h) / (1 - ρ)) ∧
  (∀ n h, μ n h = (1 + nodeGrowth tr β ρ R μ n h (xs n h) ^ (1 / ρ))⁻¹)

/-- The weights `β q(s|h) A(h, s)` of the continuation objective at `h`, for value coefficients
`A = μ^{−ρ}` (O&R Supplement A, p. 744). -/
noncomputable def nodeWeights (tr : EventTree.Tree S) (β : ℝ) (A : (n : ℕ) → (Fin n → S) → ℝ)
    (n : ℕ) (h : Fin n → S) : S → ℝ :=
  fun s => β * tr.q n h s * A (n + 1) (Fin.snoc h s)

/-- The value-coefficient map `J ↦ (1 + J^{1/ρ})^ρ`: the book's recursion in terms of
`A_t = μ_t^{−ρ}` (O&R Supplement A, p. 744). -/
noncomputable def shareMap (ρ J : ℝ) : ℝ := (1 + J ^ (1 / ρ)) ^ ρ

/-- Backward iteration of the share recursion from `μ ≡ 1` (a final date on which all wealth is
consumed), O&R Supplement A, p. 744: `iterA m` are the value coefficients `μ^{−ρ}` with `m`
further iterations. -/
noncomputable def iterA (tr : EventTree.Tree S) (β ρ : ℝ)
    (R : (n : ℕ) → (Fin n → S) → Fin N → S → ℝ) : ℕ → (n : ℕ) → (Fin n → S) → ℝ
  | 0 => fun _ _ => 1
  | m + 1 => fun n h => shareMap ρ (optJ ρ (R n h) (nodeWeights tr β (iterA tr β ρ R m) n h))

/-- Monotonicity of the optimal weighted growth in the weights (O&R Supplement A, p. 744). -/
theorem optJ_mono [Nonempty S] {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≠ 1) (r : Fin N → S → ℝ)
    (k : Fin N) (hNA : NoArbitrage r) (hF : ∃ x₀, PortFeasible r x₀) {w w' : S → ℝ}
    (hw : ∀ s, 0 < w s) (hww : ∀ s, w s ≤ w' s) : optJ ρ r w ≤ optJ ρ r w' := by
  have hw' : ∀ s, 0 < w' s := fun s => lt_of_lt_of_le (hw s) (hww s)
  have hx := (optPortW_spec hρ hρ1 r k w hw hNA hF).1
  have hx' := (optPortW_spec hρ hρ1 r k w' hw' hNA hF).1
  have hsum : ∀ x, PortFeasible r x → ∑ s, w s * (1 + portRet r x s) ^ (1 - ρ)
      ≤ ∑ s, w' s * (1 + portRet r x s) ^ (1 - ρ) := fun x hx =>
    Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_right (hww s)
      (Real.rpow_nonneg (hx.2 s).le _)
  rcases lt_or_gt_of_ne hρ1 with hlt | hgt
  · exact (hsum _ hx).trans ((optJ_compare hρ hρ1 r k w' hw' hNA hF hx).1 hlt)
  · exact ((optJ_compare hρ hρ1 r k w hw hNA hF hx').2 hgt).trans (hsum _ hx')

/-- The growth factor is `β(1 − ρ)` times the portfolio objective (O&R Supplement A, p. 744;
`ρ ≠ 1`). -/
theorem growthFactor_eq_portObj (Ω : StateSpace S) (β : ℝ) {ρ : ℝ} (hρ1 : ρ ≠ 1)
    (r : Fin N → S → ℝ) (x : Fin N → ℝ) :
    growthFactor Ω β ρ r x = β * (1 - ρ) * portObj Ω ρ r x := by
  have hp : (1 : ℝ) - ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm hρ1)
  simp only [growthFactor, portObj, StateSpace.expect, crraUtil, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  field_simp

/-- A bound on the optimal weighted growth by the uniform growth condition (O&R Supplement A,
p. 744): if `w(s) ≤ c β q(s)` and the one-period optimal growth factor `βE(1 + r°)^{1−ρ}` at the
node is at most `G`, then `J(w) ≤ cG`. -/
theorem optJ_le_growth (Ω : StateSpace S) {β ρ : ℝ} (hβ : 0 < β) (hρ : 0 < ρ) (hρ1 : ρ ≠ 1)
    (r : Fin N → S → ℝ) (k : Fin N) (hπ : ∀ s, 0 < Ω.prob s) (hNA : NoArbitrage r)
    (hF : ∃ x₀, PortFeasible r x₀) {G c : ℝ} (hc : 0 ≤ c)
    (hG : ∀ x, PortFeasible r x → (∀ x', PortFeasible r x' → portObj Ω ρ r x' ≤ portObj Ω ρ r x)
      → growthFactor Ω β ρ r x ≤ G)
    {w : S → ℝ} (hw : ∀ s, 0 < w s) (hwle : ∀ s, w s ≤ c * (β * Ω.prob s)) :
    optJ ρ r w ≤ c * G := by
  have := nonempty_of_stateSpace Ω
  obtain ⟨xu, hxu, hmax, -⟩ := exists_optimal_portfolio Ω hρ hρ1 r k hπ hNA hF
  have hGu := hG xu hxu hmax
  have hbound : ∀ x, PortFeasible r x →
      ∑ s, w s * (1 + portRet r x s) ^ (1 - ρ) ≤ c * growthFactor Ω β ρ r x := by
    intro x hx
    simp only [growthFactor, StateSpace.expect, Finset.mul_sum]
    refine Finset.sum_le_sum fun s _ => ?_
    have := mul_le_mul_of_nonneg_right (hwle s) (Real.rpow_nonneg (hx.2 s).le (1 - ρ))
    linarith
  rcases lt_or_gt_of_ne hρ1 with hlt | hgt
  · have hx := (optPortW_spec hρ hρ1 r k w hw hNA hF).1
    have hg : growthFactor Ω β ρ r (optPortW ρ r w) ≤ growthFactor Ω β ρ r xu := by
      rw [growthFactor_eq_portObj Ω β hρ1, growthFactor_eq_portObj Ω β hρ1]
      exact mul_le_mul_of_nonneg_left (hmax _ hx) (mul_nonneg hβ.le (by linarith))
    calc optJ ρ r w ≤ c * growthFactor Ω β ρ r (optPortW ρ r w) := hbound _ hx
      _ ≤ c * G := mul_le_mul_of_nonneg_left (hg.trans hGu) hc
  · calc optJ ρ r w ≤ ∑ s, w s * (1 + portRet r xu s) ^ (1 - ρ) :=
          (optJ_compare hρ hρ1 r k w hw hNA hF hxu).2 hgt
      _ ≤ c * growthFactor Ω β ρ r xu := hbound _ hxu
      _ ≤ c * G := mul_le_mul_of_nonneg_left hGu hc

/-- Continuity of the optimal weighted growth along increasing weights (O&R Supplement A,
p. 744): if `w_m(s) → w(s)` with `0 < w_low(s) ≤ w_m(s) ≤ w(s)`, then `J(w_m) → J(w)`. For
`ρ < 1` compare at the limit optimum; for `ρ > 1` the gross returns of the `w_m`-optima are
bounded through `w_low(s)(1 + r°(s))^{1−ρ} ≤ J(w_m) ≤ J(w)`. -/
theorem optJ_tendsto [Nonempty S] {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≠ 1) (r : Fin N → S → ℝ)
    (k : Fin N) (hNA : NoArbitrage r) (hF : ∃ x₀, PortFeasible r x₀) (w : ℕ → S → ℝ)
    (ws wl : S → ℝ) (hwl : ∀ s, 0 < wl s) (hle1 : ∀ m s, wl s ≤ w m s)
    (hle2 : ∀ m s, w m s ≤ ws s) (hlim : ∀ s, Tendsto (fun m => w m s) atTop (𝓝 (ws s))) :
    Tendsto (fun m => optJ ρ r (w m)) atTop (𝓝 (optJ ρ r ws)) := by
  have hw : ∀ m s, 0 < w m s := fun m s => lt_of_lt_of_le (hwl s) (hle1 m s)
  have hws : ∀ s, 0 < ws s := fun s => lt_of_lt_of_le (hw 0 s) (hle2 0 s)
  have hup : ∀ m, optJ ρ r (w m) ≤ optJ ρ r ws := fun m =>
    optJ_mono hρ hρ1 r k hNA hF (hw m) (hle2 m)
  obtain ⟨K, hlow⟩ : ∃ K : S → ℝ, ∀ m,
      optJ ρ r ws - ∑ s, (ws s - w m s) * K s ≤ optJ ρ r (w m) := by
    rcases lt_or_gt_of_ne hρ1 with hlt | hgt
    · refine ⟨fun s => (1 + portRet r (optPortW ρ r ws) s) ^ (1 - ρ), fun m => ?_⟩
      have hx := (optPortW_spec hρ hρ1 r k ws hws hNA hF).1
      have h1 := (optJ_compare hρ hρ1 r k (w m) (hw m) hNA hF hx).1 hlt
      have e : optJ ρ r ws - ∑ s, (ws s - w m s) * (1 + portRet r (optPortW ρ r ws) s) ^ (1 - ρ)
          = ∑ s, w m s * (1 + portRet r (optPortW ρ r ws) s) ^ (1 - ρ) := by
        rw [optJ, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun s _ => by ring
      rw [e]; exact h1
    · refine ⟨fun s => optJ ρ r ws / wl s, fun m => ?_⟩
      have hxm := (optPortW_spec hρ hρ1 r k (w m) (hw m) hNA hF).1
      have h1 := (optJ_compare hρ hρ1 r k ws hws hNA hF hxm).2 hgt
      have hy : ∀ s, (1 + portRet r (optPortW ρ r (w m)) s) ^ (1 - ρ) ≤ optJ ρ r ws / wl s := by
        intro s
        rw [le_div_iff₀ (hwl s)]
        have hsingle : w m s * (1 + portRet r (optPortW ρ r (w m)) s) ^ (1 - ρ)
            ≤ optJ ρ r (w m) := Finset.single_le_sum (f := fun s =>
          w m s * (1 + portRet r (optPortW ρ r (w m)) s) ^ (1 - ρ))
          (fun s _ => mul_nonneg (hw m s).le (Real.rpow_nonneg (hxm.2 s).le _))
          (Finset.mem_univ s)
        have h2 := mul_le_mul_of_nonneg_right (hle1 m s)
          (Real.rpow_nonneg (hxm.2 s).le (1 - ρ))
        have h3 := hup m
        linarith
      have e : ∑ s, ws s * (1 + portRet r (optPortW ρ r (w m)) s) ^ (1 - ρ)
          = optJ ρ r (w m) + ∑ s, (ws s - w m s)
            * (1 + portRet r (optPortW ρ r (w m)) s) ^ (1 - ρ) := by
        rw [optJ, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun s _ => by ring
      have h4 : ∑ s, (ws s - w m s) * (1 + portRet r (optPortW ρ r (w m)) s) ^ (1 - ρ)
          ≤ ∑ s, (ws s - w m s) * (optJ ρ r ws / wl s) :=
        Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hy s)
          (by linarith [hle2 m s])
      linarith
  have hT : Tendsto (fun m => optJ ρ r ws - ∑ s, (ws s - w m s) * K s) atTop
      (𝓝 (optJ ρ r ws)) := by
    have : Tendsto (fun m => ∑ s, (ws s - w m s) * K s) atTop (𝓝 (∑ _s : S, (0 : ℝ))) :=
      tendsto_finsetSum _ fun s _ => by
        simpa using ((tendsto_const_nhds (x := ws s)).sub (hlim s)).mul_const (K s)
    simpa using (tendsto_const_nhds (x := optJ ρ r ws)).sub this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hT tendsto_const_nhds hlow hup

/-- The value-coefficient map is monotone on `[0, ∞)` (O&R Supplement A, p. 744). -/
theorem shareMap_mono {ρ : ℝ} (hρ : 0 < ρ) {J J' : ℝ} (hJ : 0 ≤ J) (hJJ : J ≤ J') :
    shareMap ρ J ≤ shareMap ρ J' := by
  unfold shareMap
  have h1 : J ^ (1 / ρ) ≤ J' ^ (1 / ρ) := Real.rpow_le_rpow hJ hJJ (by positivity)
  exact Real.rpow_le_rpow (by positivity) (by linarith) hρ.le

/-- The value-coefficient map is at least one on `[0, ∞)` (O&R Supplement A, p. 744). -/
theorem one_le_shareMap {ρ : ℝ} (hρ : 0 < ρ) {J : ℝ} (hJ : 0 ≤ J) : 1 ≤ shareMap ρ J :=
  Real.one_le_rpow (by linarith [Real.rpow_nonneg hJ (1 / ρ)]) hρ.le

/-- The value-coefficient map is continuous (O&R Supplement A, p. 744; `ρ > 0`). -/
theorem continuous_shareMap {ρ : ℝ} (hρ : 0 < ρ) : Continuous (shareMap ρ) := by
  unfold shareMap
  exact (continuous_const.add (continuous_id.rpow_const fun _ => Or.inr (by positivity))).rpow_const
    fun _ => Or.inr hρ.le

/-- The bound `Ā = (1 − G^{1/ρ})^{−ρ}` is a fixed point of `A ↦ (1 + (AG)^{1/ρ})^ρ`
(O&R Supplement A, p. 744; `0 ≤ G < 1`). -/
theorem shareMap_bound {ρ : ℝ} (hρ : 0 < ρ) {G : ℝ} (hG0 : 0 ≤ G) (hG1 : G < 1) :
    shareMap ρ ((1 - G ^ (1 / ρ)) ^ (-ρ) * G) = (1 - G ^ (1 / ρ)) ^ (-ρ) := by
  set g := G ^ (1 / ρ) with hg
  have hg0 : 0 ≤ g := Real.rpow_nonneg hG0 _
  have hg1 : g < 1 := Real.rpow_lt_one hG0 hG1 (by positivity)
  have h1 : 0 < 1 - g := by linarith
  have hGg : G = g ^ ρ := by rw [hg, one_div, Real.rpow_inv_rpow hG0 hρ.ne']
  have e1 : ((1 - g) ^ (-ρ)) ^ (1 / ρ) = (1 - g)⁻¹ := by
    rw [← Real.rpow_mul h1.le, show -ρ * (1 / ρ) = -1 by field_simp, Real.rpow_neg_one]
  have e2 : (g ^ ρ) ^ (1 / ρ) = g := by rw [one_div, Real.rpow_rpow_inv hg0 hρ.ne']
  unfold shareMap
  rw [hGg, Real.mul_rpow (Real.rpow_nonneg h1.le _) (Real.rpow_nonneg hg0 _), e1, e2,
    show 1 + (1 - g)⁻¹ * g = (1 - g)⁻¹ by field_simp; ring, Real.inv_rpow h1.le,
    Real.rpow_neg h1.le]

/-- A general event tree whose one-step probabilities sum to one has a nonempty set of events. -/
theorem nonempty_of_tree (tr : EventTree.Tree S) : Nonempty S :=
  nonempty_of_stateSpace (nodeSpace tr 0 Fin.elim0)

/-- Existence of a solution of the book's share recursion, O&R Supplement A, p. 744, for returns
and probabilities that vary with the history, as the limit of backward iterations. Assume
positive one-step probabilities, no arbitrage and some feasible portfolio at every history, and
the uniform growth condition: at every history the one-period optimal growth factor
`βE_t(1 + r°)^{1−ρ}` is at most `G < 1`. Then the iterates `iterA m` from `μ ≡ 1` increase to
the value coefficients `μ_t^{−ρ}` of a solution `(μ, x)` of the recursion, with
`μ_t ≥ 1 − G^{1/ρ}` at every history. -/
theorem exists_share_recursion_solution (tr : EventTree.Tree S) (hq : ∀ n h s, 0 < tr.q n h s)
    {β ρ : ℝ} (hβ : 0 < β) (hρ : 0 < ρ) (hρ1 : ρ ≠ 1)
    (R : (n : ℕ) → (Fin n → S) → Fin N → S → ℝ) (k : Fin N) (hNA : ∀ n h, NoArbitrage (R n h))
    (hF : ∀ n h, ∃ x₀, PortFeasible (R n h) x₀) {G : ℝ} (hG0 : 0 ≤ G) (hG1 : G < 1)
    (hG : ∀ n h x, PortFeasible (R n h) x → (∀ x', PortFeasible (R n h) x' →
      portObj (nodeSpace tr n h) ρ (R n h) x' ≤ portObj (nodeSpace tr n h) ρ (R n h) x) →
      growthFactor (nodeSpace tr n h) β ρ (R n h) x ≤ G) :
    ∃ μ xs, SolvesShareRecursion tr β ρ R μ xs ∧ (∀ n h, 1 - G ^ (1 / ρ) ≤ μ n h) ∧
      ∀ n h, Tendsto (fun m => iterA tr β ρ R m n h) atTop (𝓝 (μ n h ^ (-ρ))) := by
  have := nonempty_of_tree tr
  set Ab := (1 - G ^ (1 / ρ)) ^ (-ρ) with hAb
  have hg1 : G ^ (1 / ρ) < 1 := Real.rpow_lt_one hG0 hG1 (by positivity)
  have hAb0 : 0 ≤ Ab := Real.rpow_nonneg (by linarith) _
  -- bounds and monotonicity of the iterates
  have hbd : ∀ m n h, 1 ≤ iterA tr β ρ R m n h ∧ iterA tr β ρ R m n h ≤ Ab := by
    intro m
    induction m with
    | zero =>
      intro n h
      refine ⟨le_rfl, ?_⟩
      exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos (by linarith)
        (by linarith [Real.rpow_nonneg hG0 (1 / ρ)]) (by linarith)
    | succ m ih =>
      intro n h
      have hw : ∀ s, 0 < nodeWeights tr β (iterA tr β ρ R m) n h s := fun s =>
        mul_pos (mul_pos hβ (hq n h s)) (by linarith [(ih (n + 1) (Fin.snoc h s)).1])
      have hJ0 := (optJ_pos hρ hρ1 (R n h) k _ hw (hNA n h) (hF n h)).le
      refine ⟨one_le_shareMap hρ hJ0, ?_⟩
      have hJ : optJ ρ (R n h) (nodeWeights tr β (iterA tr β ρ R m) n h) ≤ Ab * G :=
        optJ_le_growth (nodeSpace tr n h) hβ hρ hρ1 (R n h) k (hq n h) (hNA n h) (hF n h)
          hAb0 (hG n h) hw fun s => by
            simp only [nodeWeights, nodeSpace]
            have := (ih (n + 1) (Fin.snoc h s)).2
            have hqs := (hq n h s).le
            nlinarith [mul_nonneg hβ.le hqs]
      calc iterA tr β ρ R (m + 1) n h
          = shareMap ρ (optJ ρ (R n h) (nodeWeights tr β (iterA tr β ρ R m) n h)) := rfl
        _ ≤ shareMap ρ (Ab * G) := shareMap_mono hρ hJ0 hJ
        _ = Ab := shareMap_bound hρ hG0 hG1
  have hwpos : ∀ (A : (n : ℕ) → (Fin n → S) → ℝ), (∀ n h, 1 ≤ A n h) → ∀ n h s,
      0 < nodeWeights tr β A n h s := fun A hA n h s =>
    mul_pos (mul_pos hβ (hq n h s)) (by linarith [hA (n + 1) (Fin.snoc h s)])
  have hmono : ∀ m n h, iterA tr β ρ R m n h ≤ iterA tr β ρ R (m + 1) n h := by
    intro m
    induction m with
    | zero => intro n h; exact (hbd 1 n h).1
    | succ m ih =>
      intro n h
      have hJ0 := (optJ_pos hρ hρ1 (R n h) k _ (hwpos _ (fun n h => (hbd m n h).1) n h)
        (hNA n h) (hF n h)).le
      refine shareMap_mono hρ hJ0 (optJ_mono hρ hρ1 (R n h) k (hNA n h) (hF n h)
        (hwpos _ (fun n h => (hbd m n h).1) n h) fun s => ?_)
      simp only [nodeWeights]
      exact mul_le_mul_of_nonneg_left (ih (n + 1) (Fin.snoc h s))
        (mul_nonneg hβ.le (hq n h s).le)
  have hMono : ∀ n h, Monotone fun m => iterA tr β ρ R m n h := fun n h =>
    monotone_nat_of_le_succ fun m => hmono m n h
  have hBdd : ∀ n h, BddAbove (Set.range fun m => iterA tr β ρ R m n h) := fun n h =>
    ⟨Ab, by rintro _ ⟨m, rfl⟩; exact (hbd m n h).2⟩
  set As : (n : ℕ) → (Fin n → S) → ℝ := fun n h => ⨆ m, iterA tr β ρ R m n h with hAs
  have hlimA : ∀ n h, Tendsto (fun m => iterA tr β ρ R m n h) atTop (𝓝 (As n h)) := fun n h =>
    tendsto_atTop_ciSup (hMono n h) (hBdd n h)
  have hAs1 : ∀ n h, 1 ≤ As n h := fun n h =>
    le_trans (hbd 0 n h).1 (le_ciSup (hBdd n h) 0)
  have hAsb : ∀ n h, As n h ≤ Ab := fun n h => ciSup_le fun m => (hbd m n h).2
  have hAs0 : ∀ n h, 0 < As n h := fun n h => by linarith [hAs1 n h]
  -- the limit solves the recursion
  have hrec : ∀ n h, As n h = shareMap ρ (optJ ρ (R n h) (nodeWeights tr β As n h)) := by
    intro n h
    have hJ := optJ_tendsto hρ hρ1 (R n h) k (hNA n h) (hF n h)
      (fun m => nodeWeights tr β (iterA tr β ρ R m) n h) (nodeWeights tr β As n h)
      (nodeWeights tr β (fun _ _ => 1) n h) (hwpos _ (fun _ _ => le_rfl) n h)
      (fun m s => by
        simp only [nodeWeights]
        exact mul_le_mul_of_nonneg_left (hbd m (n + 1) (Fin.snoc h s)).1
          (mul_nonneg hβ.le (hq n h s).le))
      (fun m s => by
        simp only [nodeWeights]
        exact mul_le_mul_of_nonneg_left (le_ciSup (hBdd (n + 1) (Fin.snoc h s)) m)
          (mul_nonneg hβ.le (hq n h s).le))
      (fun s => (hlimA (n + 1) (Fin.snoc h s)).const_mul _)
    have h1 : Tendsto (fun m => iterA tr β ρ R (m + 1) n h) atTop
        (𝓝 (shareMap ρ (optJ ρ (R n h) (nodeWeights tr β As n h)))) :=
      ((continuous_shareMap hρ).tendsto _).comp hJ
    have h2 : Tendsto (fun m => iterA tr β ρ R (m + 1) n h) atTop (𝓝 (As n h)) :=
      (tendsto_add_atTop_iff_nat 1).mpr (hlimA n h)
    exact tendsto_nhds_unique h2 h1
  -- the shares and portfolios
  set μ : (n : ℕ) → (Fin n → S) → ℝ := fun n h => (As n h ^ (1 / ρ))⁻¹ with hμ
  set xs : (n : ℕ) → (Fin n → S) → Fin N → ℝ :=
    fun n h => optPortW ρ (R n h) (nodeWeights tr β As n h) with hxs
  have hμA : ∀ n h, μ n h ^ (-ρ) = As n h := by
    intro n h
    simp only [hμ]
    rw [Real.inv_rpow (Real.rpow_nonneg (hAs0 n h).le _), ← Real.rpow_mul (hAs0 n h).le,
      show 1 / ρ * -ρ = -1 by field_simp, Real.rpow_neg_one, inv_inv]
  have hgrowth : ∀ n h x, nodeGrowth tr β ρ R μ n h x
      = ∑ s, nodeWeights tr β As n h s * (1 + portRet (R n h) x s) ^ (1 - ρ) := by
    intro n h x
    simp only [nodeGrowth, nodeWeights, hμA, Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => by ring
  have hwAs := hwpos As hAs1
  refine ⟨μ, xs, ⟨fun n h => ?_, fun n h => ?_, fun n h x hx => ?_, fun n h => ?_⟩,
    fun n h => ?_, fun n h => ?_⟩
  · have hJ := optJ_pos hρ hρ1 (R n h) k _ (hwAs n h) (hNA n h) (hF n h)
    have e : As n h ^ (1 / ρ) = 1 + optJ ρ (R n h) (nodeWeights tr β As n h) ^ (1 / ρ) := by
      rw [hrec n h, shareMap, ← Real.rpow_mul (by positivity), mul_one_div_cancel hρ.ne',
        Real.rpow_one]
    have hpos : 0 < optJ ρ (R n h) (nodeWeights tr β As n h) ^ (1 / ρ) :=
      Real.rpow_pos_of_pos hJ _
    simp only [hμ]
    rw [e]
    exact ⟨inv_pos.mpr (by linarith), inv_lt_one_of_one_lt₀ (by linarith)⟩
  · exact (optPortW_spec hρ hρ1 (R n h) k _ (hwAs n h) (hNA n h) (hF n h)).1
  · have := (optPortW_spec hρ hρ1 (R n h) k _ (hwAs n h) (hNA n h) (hF n h)).2 x hx
    simp only [weightedObj] at this
    rw [hgrowth, hgrowth]
    exact this
  · have e : As n h ^ (1 / ρ) = 1 + optJ ρ (R n h) (nodeWeights tr β As n h) ^ (1 / ρ) := by
      have h0 : 0 ≤ 1 + optJ ρ (R n h) (nodeWeights tr β As n h) ^ (1 / ρ) := by
        have := optJ_pos hρ hρ1 (R n h) k _ (hwAs n h) (hNA n h) (hF n h)
        positivity
      conv_lhs => rw [hrec n h, shareMap]
      rw [← Real.rpow_mul h0, mul_one_div_cancel hρ.ne', Real.rpow_one]
    simp only [hμ]
    rw [e, hgrowth]
    rfl
  · simp only [hμ]
    have h1 : As n h ^ (1 / ρ) ≤ Ab ^ (1 / ρ) :=
      Real.rpow_le_rpow (hAs0 n h).le (hAsb n h) (by positivity)
    have h2 : Ab ^ (1 / ρ) = (1 - G ^ (1 / ρ))⁻¹ := by
      rw [hAb, ← Real.rpow_mul (by linarith), show -ρ * (1 / ρ) = -1 by field_simp,
        Real.rpow_neg_one]
    rw [h2] at h1
    have h3 := inv_anti₀ (Real.rpow_pos_of_pos (hAs0 n h) _) h1
    rwa [inv_inv] at h3
  · rw [hμA]; exact hlimA n h

/-! ### Verification with history-dependent returns -/

/-- Wealth along a plan when returns depend on the history (O&R Supplement A, p. 742):
`W(h, s) = (1 + r°_h(x(h))(s))(W(h) − c(h))` with the returns `R n h` at `h`. -/
noncomputable def wealthT (R : (n : ℕ) → (Fin n → S) → Fin N → S → ℝ) (W₀ : ℝ)
    (c : (n : ℕ) → (Fin n → S) → ℝ) (x : (n : ℕ) → (Fin n → S) → Fin N → ℝ) :
    (n : ℕ) → (Fin n → S) → ℝ
  | 0, _ => W₀
  | n + 1, g => (1 + portRet (R n (Fin.init g)) (x n (Fin.init g)) (g (Fin.last n)))
      * (wealthT R W₀ c x n (Fin.init g) - c n (Fin.init g))

omit [Fintype S] in
/-- The wealth-accumulation identity with history-dependent returns (O&R Supplement A,
p. 742). -/
theorem wealthT_snoc (R : (n : ℕ) → (Fin n → S) → Fin N → S → ℝ) (W₀ : ℝ)
    (c : (n : ℕ) → (Fin n → S) → ℝ) (x : (n : ℕ) → (Fin n → S) → Fin N → ℝ) {n : ℕ}
    (h : Fin n → S) (s : S) :
    wealthT R W₀ c x (n + 1) (Fin.snoc h s)
      = (1 + portRet (R n h) (x n h) s) * (wealthT R W₀ c x n h - c n h) := by
  simp only [wealthT, Fin.init_snoc, Fin.snoc_last]

/-- An admissible plan with history-dependent returns (O&R Supplement A, p. 742): positive
consumption not exceeding wealth, shares adding up to one, at every history. -/
def AdmissibleT (R : (n : ℕ) → (Fin n → S) → Fin N → S → ℝ) (W₀ : ℝ)
    (c : (n : ℕ) → (Fin n → S) → ℝ) (x : (n : ℕ) → (Fin n → S) → Fin N → ℝ) : Prop :=
  (∀ n h, 0 < c n h) ∧ (∀ n h, c n h ≤ wealthT R W₀ c x n h) ∧ (∀ n h, ∑ i, x n h i = 1)

omit [Fintype S] in
/-- Along an admissible plan the investor saves a positive amount and holds a feasible portfolio
at every history (O&R Supplement A, p. 743, footnote 1). -/
theorem admissibleT_step [Nonempty S] (R : (n : ℕ) → (Fin n → S) → Fin N → S → ℝ) (W₀ : ℝ)
    {c : (n : ℕ) → (Fin n → S) → ℝ} {x : (n : ℕ) → (Fin n → S) → Fin N → ℝ}
    (hadm : AdmissibleT R W₀ c x) (n : ℕ) (h : Fin n → S) :
    c n h < wealthT R W₀ c x n h ∧ PortFeasible (R n h) (x n h) := by
  have hD : 0 ≤ wealthT R W₀ c x n h - c n h := by linarith [hadm.2.1 n h]
  have key : ∀ s, 0 < (1 + portRet (R n h) (x n h) s) * (wealthT R W₀ c x n h - c n h) := by
    intro s
    rw [← wealthT_snoc]
    exact lt_of_lt_of_le (hadm.1 _ _) (hadm.2.1 _ _)
  obtain ⟨s₀⟩ := ‹Nonempty S›
  have hD' : 0 < wealthT R W₀ c x n h - c n h := by
    rcases hD.lt_or_eq with h' | h'
    · exact h'
    · have := key s₀; rw [← h', mul_zero] at this; exact absurd this (lt_irrefl 0)
  exact ⟨by linarith, hadm.2.2 n h, fun s => pos_of_mul_pos_left (key s) hD'.le⟩

/-- The law of iterated expectations on a general event tree (O&R Appendix 5C, p. 341):
`Σ_{h_{t+1}} π(h_{t+1}) f = Σ_{h_t} π(h_t) Σ_s q(s|h_t) f(h_t, s)`. -/
theorem sum_succ_tree (tr : EventTree.Tree S) (n : ℕ) (f : (Fin (n + 1) → S) → ℝ) :
    ∑ g, tr.histProb g * f g = ∑ h, tr.histProb h * ∑ s, tr.q n h s * f (Fin.snoc h s) := by
  rw [sum_snoc]
  refine Finset.sum_congr rfl fun h _ => ?_
  simp only [tr.histProb_snoc, Finset.mul_sum]
  exact Finset.sum_congr rfl fun s _ => by ring

/-- The dynamic-programming inequality summed along a plan on a general tree (O&R Supplement A,
p. 742): if `u(c(h)) + βΣ_s q(s|h) v(h, s) ≤ v(h)` at every history, then
`Σ_{t<n} β^t E u(C_t) + β^n E v_n ≤ v(h_1)`. -/
theorem telescope_tree_le (tr : EventTree.Tree S) {β : ℝ} (hβ : 0 ≤ β) (u : ℝ → ℝ)
    (c v : (n : ℕ) → (Fin n → S) → ℝ)
    (hstep : ∀ n h, u (c n h) + β * ∑ s, tr.q n h s * v (n + 1) (Fin.snoc h s) ≤ v n h)
    (n : ℕ) :
    ∑ k ∈ range n, utilSeries tr β u c k + β ^ n * ∑ h, tr.histProb h * v n h
      ≤ v 0 Fin.elim0 := by
  induction n with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, pow_zero, one_mul, zero_add,
      Fintype.sum_unique, tr.histProb_zero]
    rw [Subsingleton.elim default Fin.elim0]
  | succ n ih =>
    rw [Finset.sum_range_succ, sum_succ_tree]
    have hle : utilSeries tr β u c n + β ^ (n + 1) * ∑ h, tr.histProb h
        * ∑ s, tr.q n h s * v (n + 1) (Fin.snoc h s)
        ≤ β ^ n * ∑ h, tr.histProb h * v n h := by
      rw [utilSeries, pow_succ, mul_assoc, ← mul_add, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun h _ => ?_) (pow_nonneg hβ n)
      have := mul_le_mul_of_nonneg_left (hstep n h) (tr.histProb_nonneg h)
      linarith
    linarith

/-- The summed dynamic-programming identity when the step holds with equality (O&R
Supplement A, p. 742). -/
theorem telescope_tree_eq (tr : EventTree.Tree S) (β : ℝ) (u : ℝ → ℝ)
    (c v : (n : ℕ) → (Fin n → S) → ℝ)
    (hstep : ∀ n h, u (c n h) + β * ∑ s, tr.q n h s * v (n + 1) (Fin.snoc h s) = v n h)
    (n : ℕ) :
    ∑ k ∈ range n, utilSeries tr β u c k + β ^ n * ∑ h, tr.histProb h * v n h
      = v 0 Fin.elim0 := by
  induction n with
  | zero =>
    simp only [Finset.range_zero, Finset.sum_empty, pow_zero, one_mul, zero_add,
      Fintype.sum_unique, tr.histProb_zero]
    rw [Subsingleton.elim default Fin.elim0]
  | succ n ih =>
    rw [Finset.sum_range_succ, sum_succ_tree]
    have heq : utilSeries tr β u c n + β ^ (n + 1) * ∑ h, tr.histProb h
        * ∑ s, tr.q n h s * v (n + 1) (Fin.snoc h s)
        = β ^ n * ∑ h, tr.histProb h * v n h := by
      rw [utilSeries, pow_succ, mul_assoc, ← mul_add, Finset.mul_sum, ← Finset.sum_add_distrib]
      congr 1
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [← hstep n h]; ring
    linarith

/-- The share identity of the recursion, O&R Supplement A, p. 744: if
`μ = (1 + J^{1/ρ})^{−1}` with `J ≥ 0`, then `μ^{−ρ}(1 − μ)^ρ = J`. -/
theorem share_identity {ρ : ℝ} (hρ : 0 < ρ) {J μ : ℝ} (hJ : 0 ≤ J)
    (hμ : μ = (1 + J ^ (1 / ρ))⁻¹) : μ ^ (-ρ) * (1 - μ) ^ ρ = J := by
  have hJr : 0 ≤ J ^ (1 / ρ) := Real.rpow_nonneg hJ _
  have hμ0 : 0 < μ := by rw [hμ]; positivity
  have h1 : 1 - μ = J ^ (1 / ρ) * μ := by
    rw [hμ]; field_simp; ring
  rw [h1, Real.mul_rpow hJr hμ0.le, one_div, Real.rpow_inv_rpow hJ hρ.ne', Real.rpow_neg hμ0.le]
  field_simp

/-- The continuation value at a history, O&R Supplement A, pp. 743–744: with next-date values
`V_{t+1}(h, s; W) = μ_{t+1}(h, s)^{−ρ}W^{1−ρ}/(1−ρ)`, saving `D > 0` in a feasible portfolio `x`
gives `βE_t V_{t+1}((1 + r°)D) = [βE_t{(1 + r°)^{1−ρ} μ_{t+1}^{−ρ}}] · D^{1−ρ}/(1−ρ)`. -/
theorem node_continuation (tr : EventTree.Tree S) (β ρ : ℝ)
    (R : (n : ℕ) → (Fin n → S) → Fin N → S → ℝ) (μ : (n : ℕ) → (Fin n → S) → ℝ) (n : ℕ)
    (h : Fin n → S) {x : Fin N → ℝ} (hx : PortFeasible (R n h) x) {D : ℝ} (hD : 0 < D) :
    β * ∑ s, tr.q n h s * crraValue (μ (n + 1) (Fin.snoc h s)) ρ ((1 + portRet (R n h) x s) * D)
      = nodeGrowth tr β ρ R μ n h x * crraUtil ρ D := by
  simp only [nodeGrowth, crraValue, crraUtil, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Real.mul_rpow (hx.2 s).le hD.le]
  ring

/-- The Bellman inequality at a history, O&R Supplement A, pp. 742–744: at a solution of the
share recursion, `u(C) + βE_t V_{t+1}((1 + r°(x))(W − C)) ≤ V_t(W)` for every `0 < C < W` and
feasible portfolio `x`, with `V_t(W) = μ_t^{−ρ}W^{1−ρ}/(1−ρ)`. -/
theorem bellman_node_le (tr : EventTree.Tree S) {β ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≠ 1)
    (R : (n : ℕ) → (Fin n → S) → Fin N → S → ℝ) {μ : (n : ℕ) → (Fin n → S) → ℝ}
    {xs : (n : ℕ) → (Fin n → S) → Fin N → ℝ} (hsol : SolvesShareRecursion tr β ρ R μ xs)
    (hJ : ∀ n h, 0 ≤ nodeGrowth tr β ρ R μ n h (xs n h)) (n : ℕ) (h : Fin n → S)
    {W C : ℝ} {x : Fin N → ℝ} (hC : 0 < C) (hCW : C < W) (hx : PortFeasible (R n h) x) :
    crraUtil ρ C + β * ∑ s, tr.q n h s * crraValue (μ (n + 1) (Fin.snoc h s)) ρ
      ((1 + portRet (R n h) x s) * (W - C)) ≤ crraValue (μ n h) ρ W := by
  have hD : 0 < W - C := by linarith
  rw [node_continuation tr β ρ R μ n h hx hD]
  have hopt := hsol.2.2.1 n h x hx
  have hp : nodeGrowth tr β ρ R μ n h x * crraUtil ρ (W - C)
      ≤ nodeGrowth tr β ρ R μ n h (xs n h) * crraUtil ρ (W - C) := by
    have e : ∀ y, y * crraUtil ρ (W - C) = y / (1 - ρ) * (W - C) ^ (1 - ρ) := fun y => by
      unfold crraUtil; ring
    rw [e, e]
    exact mul_le_mul_of_nonneg_right hopt (Real.rpow_nonneg hD.le _)
  have hid := share_identity hρ (hJ n h) (hsol.2.2.2 n h)
  have hsplit := crra_split_le hρ hρ1 (hsol.1 n h).1 (hsol.1 n h).2 hC hCW
  rw [hid] at hsplit
  unfold crraValue
  linarith

/-- The Bellman equation holds with equality at `C = μ_t W` and the portfolio `x_t(h)`, O&R
Supplement A, p. 744, and the continuation is `(1 − μ_t)V_t(W)`. -/
theorem bellman_node_eq (tr : EventTree.Tree S) {β ρ : ℝ} (hρ : 0 < ρ)
    (R : (n : ℕ) → (Fin n → S) → Fin N → S → ℝ) {μ : (n : ℕ) → (Fin n → S) → ℝ}
    {xs : (n : ℕ) → (Fin n → S) → Fin N → ℝ} (hsol : SolvesShareRecursion tr β ρ R μ xs)
    (hJ : ∀ n h, 0 ≤ nodeGrowth tr β ρ R μ n h (xs n h)) (n : ℕ) (h : Fin n → S) {W : ℝ}
    (hW : 0 < W) :
    β * ∑ s, tr.q n h s * crraValue (μ (n + 1) (Fin.snoc h s)) ρ
      ((1 + portRet (R n h) (xs n h) s) * ((1 - μ n h) * W))
        = (1 - μ n h) * crraValue (μ n h) ρ W ∧
    crraUtil ρ (μ n h * W) + β * ∑ s, tr.q n h s * crraValue (μ (n + 1) (Fin.snoc h s)) ρ
      ((1 + portRet (R n h) (xs n h) s) * ((1 - μ n h) * W)) = crraValue (μ n h) ρ W := by
  obtain ⟨hμ0, hμ1⟩ := hsol.1 n h
  have h1 : 0 < 1 - μ n h := by linarith
  have hid := share_identity hρ (hJ n h) (hsol.2.2.2 n h)
  have hc := node_continuation tr β ρ R μ n h (hsol.2.1 n h) (mul_pos h1 hW)
  have hbb : (1 - μ n h) ^ ρ * (1 - μ n h) ^ (1 - ρ) = 1 - μ n h := by
    rw [← Real.rpow_add h1, show ρ + (1 - ρ) = 1 by ring, Real.rpow_one]
  have e1 : nodeGrowth tr β ρ R μ n h (xs n h) * crraUtil ρ ((1 - μ n h) * W)
      = (1 - μ n h) * crraValue (μ n h) ρ W := by
    rw [← hid, crraValue, crraUtil, crraUtil, Real.mul_rpow h1.le hW.le]
    linear_combination μ n h ^ (-ρ) * W ^ (1 - ρ) / (1 - ρ) * hbb
  refine ⟨hc.trans e1, ?_⟩
  rw [hc, e1]
  have := crra_split_eq (ρ := ρ) hμ0 hμ1 hW
  rw [show W - μ n h * W = (1 - μ n h) * W by ring, hid] at this
  rw [← e1]
  unfold crraValue
  linarith

/-- The growth term of a solution is nonnegative (O&R Supplement A, p. 744). -/
theorem nodeGrowth_nonneg (tr : EventTree.Tree S) {β ρ : ℝ} (hβ : 0 ≤ β)
    (R : (n : ℕ) → (Fin n → S) → Fin N → S → ℝ) {μ : (n : ℕ) → (Fin n → S) → ℝ}
    {xs : (n : ℕ) → (Fin n → S) → Fin N → ℝ} (hsol : SolvesShareRecursion tr β ρ R μ xs)
    (n : ℕ) (h : Fin n → S) : 0 ≤ nodeGrowth tr β ρ R μ n h (xs n h) :=
  mul_nonneg hβ (Finset.sum_nonneg fun s _ => mul_nonneg (tr.q_nonneg n h s)
    (mul_nonneg (Real.rpow_nonneg ((hsol.2.1 n h).2 s).le _)
      (Real.rpow_nonneg (hsol.1 _ _).1.le _)))

/-- The transversality property with history-dependent returns, O&R Supplement A, p. 744
(proved, not assumed): at a solution of the share recursion with `μ_t ≥ μ₀ > 0` everywhere,
every admissible plan with convergent utility series has `β^t E V_t(W_t) → 0`. -/
theorem transversality_tree (tr : EventTree.Tree S) {β ρ : ℝ} (hβ : 0 < β) (hρ : 0 < ρ)
    (hρ1 : ρ ≠ 1) (R : (n : ℕ) → (Fin n → S) → Fin N → S → ℝ)
    {μ : (n : ℕ) → (Fin n → S) → ℝ} {xs : (n : ℕ) → (Fin n → S) → Fin N → ℝ}
    (hsol : SolvesShareRecursion tr β ρ R μ xs) {μ₀ : ℝ} (hμ₀ : 0 < μ₀)
    (hlow : ∀ n h, μ₀ ≤ μ n h) (W₀ : ℝ) {c : (n : ℕ) → (Fin n → S) → ℝ}
    {x : (n : ℕ) → (Fin n → S) → Fin N → ℝ} (hadm : AdmissibleT R W₀ c x)
    (hU : Summable (utilSeries tr β (crraUtil ρ) c)) :
    Tendsto (fun n => β ^ n * ∑ h, tr.histProb h
      * crraValue (μ n h) ρ (wealthT R W₀ c x n h)) atTop (𝓝 0) := by
  have := nonempty_of_tree tr
  set T := fun n => β ^ n * ∑ h, tr.histProb h * crraValue (μ n h) ρ (wealthT R W₀ c x n h)
    with hT
  have hW : ∀ n h, 0 < wealthT R W₀ c x n h := fun n h =>
    lt_of_lt_of_le (hadm.1 n h) (hadm.2.1 n h)
  have hJ := nodeGrowth_nonneg tr hβ.le R hsol
  rcases lt_or_gt_of_ne hρ1 with hlt | hgt
  · have hVnn : ∀ n h, 0 ≤ crraValue (μ n h) ρ (wealthT R W₀ c x n h) := fun n h =>
      mul_nonneg (Real.rpow_nonneg (hsol.1 n h).1.le _)
        (div_nonneg (Real.rpow_nonneg (hW n h).le _) (by linarith))
    have hT0 : ∀ n, 0 ≤ T n := fun n => mul_nonneg (pow_nonneg hβ.le n)
      (Finset.sum_nonneg fun h _ => mul_nonneg (tr.histProb_nonneg h) (hVnn n h))
    have hμ₀1 : μ₀ < 1 := lt_of_le_of_lt (hlow 0 Fin.elim0) (hsol.1 0 Fin.elim0).2
    set θ := (1 - μ₀) ^ ρ
    have hθ0 : 0 ≤ θ := Real.rpow_nonneg (by linarith) _
    have hθ1 : θ < 1 := Real.rpow_lt_one (by linarith) (by linarith) hρ
    have hrec : ∀ n, T (n + 1) ≤ θ * T n := by
      intro n
      have hms : ∀ (a : ℝ) (f : (Fin n → S) → ℝ), a * ∑ h, f h = ∑ h, a * f h :=
        fun a f => Finset.mul_sum _ _ _
      simp only [hT]
      rw [sum_succ_tree]
      simp only [wealthT_snoc, hms]
      refine Finset.sum_le_sum fun h _ => ?_
      obtain ⟨hlt', hxn⟩ := admissibleT_step R W₀ hadm n h
      have hD : 0 < wealthT R W₀ c x n h - c n h := by linarith
      have hc := node_continuation tr β ρ R μ n h hxn hD
      have hopt := hsol.2.2.1 n h (x n h) hxn
      have hle1 : nodeGrowth tr β ρ R μ n h (x n h) * crraUtil ρ (wealthT R W₀ c x n h - c n h)
          ≤ nodeGrowth tr β ρ R μ n h (xs n h) * crraUtil ρ (wealthT R W₀ c x n h) := by
        have e : ∀ y D, y * crraUtil ρ D = y / (1 - ρ) * D ^ (1 - ρ) := fun y D => by
          unfold crraUtil; ring
        have hm := crraUtil_mono hρ hρ1 hD (by linarith [hadm.1 n h] :
          wealthT R W₀ c x n h - c n h ≤ wealthT R W₀ c x n h)
        calc nodeGrowth tr β ρ R μ n h (x n h) * crraUtil ρ (wealthT R W₀ c x n h - c n h)
            ≤ nodeGrowth tr β ρ R μ n h (xs n h) * crraUtil ρ (wealthT R W₀ c x n h - c n h) := by
              rw [e, e]; exact mul_le_mul_of_nonneg_right hopt (Real.rpow_nonneg hD.le _)
          _ ≤ nodeGrowth tr β ρ R μ n h (xs n h) * crraUtil ρ (wealthT R W₀ c x n h) :=
              mul_le_mul_of_nonneg_left hm (hJ n h)
      have hid := share_identity hρ (hJ n h) (hsol.2.2.2 n h)
      have hθle : (1 - μ n h) ^ ρ ≤ θ :=
        Real.rpow_le_rpow (by linarith [(hsol.1 n h).2]) (by linarith [hlow n h]) hρ.le
      have hchain : β * ∑ s, tr.q n h s * crraValue (μ (n + 1) (Fin.snoc h s)) ρ
          ((1 + portRet (R n h) (x n h) s) * (wealthT R W₀ c x n h - c n h))
          ≤ θ * crraValue (μ n h) ρ (wealthT R W₀ c x n h) := by
        rw [hc]
        refine hle1.trans ?_
        rw [← hid]
        have := hVnn n h
        unfold crraValue at this ⊢
        have hu : 0 ≤ crraUtil ρ (wealthT R W₀ c x n h) :=
          div_nonneg (Real.rpow_nonneg (hW n h).le _) (by linarith)
        have hμr : 0 ≤ μ n h ^ (-ρ) := Real.rpow_nonneg (hsol.1 n h).1.le _
        nlinarith [mul_le_mul_of_nonneg_right hθle (mul_nonneg hμr hu)]
      have h3 := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hchain (tr.histProb_nonneg h)) (pow_nonneg hβ.le n)
      calc β ^ (n + 1) * (tr.histProb h * ∑ s, tr.q n h s * crraValue (μ (n + 1)
            (Fin.snoc h s)) ρ ((1 + portRet (R n h) (x n h) s)
              * (wealthT R W₀ c x n h - c n h)))
          = β ^ n * (tr.histProb h * (β * ∑ s, tr.q n h s * crraValue (μ (n + 1)
            (Fin.snoc h s)) ρ ((1 + portRet (R n h) (x n h) s)
              * (wealthT R W₀ c x n h - c n h)))) := by ring
        _ ≤ β ^ n * (tr.histProb h * (θ * crraValue (μ n h) ρ (wealthT R W₀ c x n h))) := h3
        _ = θ * (β ^ n * (tr.histProb h * crraValue (μ n h) ρ (wealthT R W₀ c x n h))) := by
          ring
    have hgeo : ∀ n, T n ≤ θ ^ n * T 0 := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        calc T (n + 1) ≤ θ * T n := hrec n
          _ ≤ θ * (θ ^ n * T 0) := mul_le_mul_of_nonneg_left ih hθ0
          _ = θ ^ (n + 1) * T 0 := by ring
    have hup : Tendsto (fun n => θ ^ n * T 0) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hθ0 hθ1).mul_const (T 0)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup hT0 hgeo
  · have hlowb : ∀ n, μ₀ ^ (-ρ) * utilSeries tr β (crraUtil ρ) c n ≤ T n := by
      intro n
      simp only [hT, utilSeries]
      rw [← mul_assoc, mul_comm (μ₀ ^ (-ρ)), mul_assoc, Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun h _ => ?_) (pow_nonneg hβ.le n)
      have hm := crraUtil_mono hρ hρ1 (hadm.1 n h) (hadm.2.1 n h)
      have hu : crraUtil ρ (c n h) ≤ 0 :=
        div_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg (hadm.1 n h).le _) (by linarith)
      have hμle : μ n h ^ (-ρ) ≤ μ₀ ^ (-ρ) :=
        Real.rpow_le_rpow_of_nonpos hμ₀ (hlow n h) (by linarith)
      have hμr : 0 ≤ μ n h ^ (-ρ) := Real.rpow_nonneg (hsol.1 n h).1.le _
      have h1 : μ₀ ^ (-ρ) * crraUtil ρ (c n h) ≤ μ n h ^ (-ρ) * crraUtil ρ (c n h) := by
        nlinarith
      have h2 := mul_le_mul_of_nonneg_left hm hμr
      have := mul_le_mul_of_nonneg_left (h1.trans h2) (tr.histProb_nonneg h)
      unfold crraValue
      linarith
    have hup : ∀ n, T n ≤ 0 := by
      intro n
      refine mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hβ.le n)
        (Finset.sum_nonpos fun h _ => mul_nonpos_of_nonneg_of_nonpos
          (tr.histProb_nonneg h) ?_)
      exact mul_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg (hsol.1 n h).1.le _)
        (div_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg (hW n h).le _) (by linarith))
    have hlowT : Tendsto (fun n => μ₀ ^ (-ρ) * utilSeries tr β (crraUtil ρ) c n) atTop
        (𝓝 0) := by
      simpa using hU.tendsto_atTop_zero.const_mul (μ₀ ^ (-ρ))
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlowT tendsto_const_nhds hlowb hup

/-- Wealth under the policy `C = μ_t W` with portfolios `x_t(h)` (O&R Supplement A, p. 744):
`W*(h, s) = (1 + r°_h(x_t(h))(s))(1 − μ_t(h))W*(h)`. -/
noncomputable def optWealthT (R : (n : ℕ) → (Fin n → S) → Fin N → S → ℝ)
    (xs : (n : ℕ) → (Fin n → S) → Fin N → ℝ) (μ : (n : ℕ) → (Fin n → S) → ℝ) (W₀ : ℝ) :
    (n : ℕ) → (Fin n → S) → ℝ
  | 0, _ => W₀
  | n + 1, g => (1 + portRet (R n (Fin.init g)) (xs n (Fin.init g)) (g (Fin.last n)))
      * ((1 - μ n (Fin.init g)) * optWealthT R xs μ W₀ n (Fin.init g))

omit [Fintype S] in
/-- The policy `C = μ_t W`, `x = x_t(h)` generates the wealth path `W*` (O&R Supplement A,
p. 744). -/
theorem wealthT_optPlan (R : (n : ℕ) → (Fin n → S) → Fin N → S → ℝ)
    (xs : (n : ℕ) → (Fin n → S) → Fin N → ℝ) (μ : (n : ℕ) → (Fin n → S) → ℝ) (W₀ : ℝ) :
    wealthT R W₀ (fun n h => μ n h * optWealthT R xs μ W₀ n h) xs = optWealthT R xs μ W₀ := by
  funext n
  induction n with
  | zero => rfl
  | succ n ih =>
    funext g
    simp only [wealthT, optWealthT, ih]
    ring

omit [Fintype S] in
/-- Optimal wealth stays positive (O&R Supplement A, p. 744). -/
theorem optWealthT_pos (R : (n : ℕ) → (Fin n → S) → Fin N → S → ℝ)
    {xs : (n : ℕ) → (Fin n → S) → Fin N → ℝ} {μ : (n : ℕ) → (Fin n → S) → ℝ}
    (hxs : ∀ n h s, 0 < 1 + portRet (R n h) (xs n h) s) (hμ1 : ∀ n h, μ n h < 1) {W₀ : ℝ}
    (hW₀ : 0 < W₀) : ∀ n h, 0 < optWealthT R xs μ W₀ n h := by
  intro n
  induction n with
  | zero => intro h; exact hW₀
  | succ n ih =>
    intro g
    simp only [optWealthT]
    exact mul_pos (hxs _ _ _) (mul_pos (by linarith [hμ1 n (Fin.init g)]) (ih _))

/-- The verification theorem with history-dependent returns, O&R Supplement A, p. 744. Let
`(μ, x)` solve the share recursion on the event tree `tr` (`ρ > 0`, `ρ ≠ 1`, `β > 0`), with
`μ_t ≥ μ₀ > 0` at every history, and let `W₀ > 0`. Then the policy `C = μ_t W` with portfolios
`x_t(h)` is admissible, its utility series converges and it attains
`V_1(W₀) = μ_1^{−ρ}W₀^{1−ρ}/(1−ρ)`; every admissible plan with convergent utility series
achieves at most `V_1(W₀)`. -/
theorem verification_tree (tr : EventTree.Tree S) {β ρ : ℝ} (hβ : 0 < β) (hρ : 0 < ρ)
    (hρ1 : ρ ≠ 1) (R : (n : ℕ) → (Fin n → S) → Fin N → S → ℝ)
    {μ : (n : ℕ) → (Fin n → S) → ℝ} {xs : (n : ℕ) → (Fin n → S) → Fin N → ℝ}
    (hsol : SolvesShareRecursion tr β ρ R μ xs) {μ₀ : ℝ} (hμ₀ : 0 < μ₀)
    (hlow : ∀ n h, μ₀ ≤ μ n h) {W₀ : ℝ} (hW₀ : 0 < W₀) :
    AdmissibleT R W₀ (fun n h => μ n h * optWealthT R xs μ W₀ n h) xs ∧
      Summable (utilSeries tr β (crraUtil ρ) fun n h => μ n h * optWealthT R xs μ W₀ n h) ∧
      expectedUtility tr β (crraUtil ρ) (fun n h => μ n h * optWealthT R xs μ W₀ n h)
        = crraValue (μ 0 Fin.elim0) ρ W₀ ∧
      ∀ (c : (n : ℕ) → (Fin n → S) → ℝ) (x : (n : ℕ) → (Fin n → S) → Fin N → ℝ),
        AdmissibleT R W₀ c x → Summable (utilSeries tr β (crraUtil ρ) c) →
        expectedUtility tr β (crraUtil ρ) c ≤ crraValue (μ 0 Fin.elim0) ρ W₀ := by
  have := nonempty_of_tree tr
  have hJ := nodeGrowth_nonneg tr hβ.le R hsol
  set Ws := optWealthT R xs μ W₀ with hWs
  set cs := fun n (h : Fin n → S) => μ n h * Ws n h with hcs
  have hWpos := optWealthT_pos R (fun n h s => (hsol.2.1 n h).2 s)
    (fun n h => (hsol.1 n h).2) hW₀
  have hadm : AdmissibleT R W₀ cs xs := by
    refine ⟨fun n h => mul_pos (hsol.1 n h).1 (hWpos n h), fun n h => ?_,
      fun n h => (hsol.2.1 n h).1⟩
    rw [hcs, wealthT_optPlan]
    have := hWpos n h
    nlinarith [(hsol.1 n h).2]
  -- upper bound for every admissible plan
  have hupper : ∀ (c : (n : ℕ) → (Fin n → S) → ℝ) (x : (n : ℕ) → (Fin n → S) → Fin N → ℝ),
      AdmissibleT R W₀ c x → Summable (utilSeries tr β (crraUtil ρ) c) →
      expectedUtility tr β (crraUtil ρ) c ≤ crraValue (μ 0 Fin.elim0) ρ W₀ := by
    intro c x hadm' hU
    have hstep : ∀ n h, crraUtil ρ (c n h) + β * ∑ s, tr.q n h s
        * (fun n h => crraValue (μ n h) ρ (wealthT R W₀ c x n h)) (n + 1) (Fin.snoc h s)
        ≤ (fun n h => crraValue (μ n h) ρ (wealthT R W₀ c x n h)) n h := by
      intro n h
      obtain ⟨hlt, hxn⟩ := admissibleT_step R W₀ hadm' n h
      simp only [wealthT_snoc]
      exact bellman_node_le tr hρ hρ1 R hsol hJ n h (hadm'.1 n h) hlt hxn
    have htel := telescope_tree_le tr hβ.le (crraUtil ρ) c
      (fun n h => crraValue (μ n h) ρ (wealthT R W₀ c x n h)) hstep
    have hT := transversality_tree tr hβ hρ hρ1 R hsol hμ₀ hlow W₀ hadm' hU
    have h2 := (tendsto_const_nhds (x := crraValue (μ 0 Fin.elim0) ρ W₀)).sub hT
    rw [sub_zero] at h2
    exact le_of_tendsto_of_tendsto' hU.hasSum.tendsto_sum_nat h2 fun n => by
      have := htel n
      beta_reduce at this
      rw [show wealthT R W₀ c x 0 Fin.elim0 = W₀ from rfl] at this
      linarith
  -- attainment
  set v := fun n (h : Fin n → S) => crraValue (μ n h) ρ (Ws n h) with hv
  have hWsnoc : ∀ n (h : Fin n → S) s, Ws (n + 1) (Fin.snoc h s)
      = (1 + portRet (R n h) (xs n h) s) * ((1 - μ n h) * Ws n h) := by
    intro n h s; simp only [hWs, optWealthT, Fin.init_snoc, Fin.snoc_last]
  have hstepEq : ∀ n h, crraUtil ρ (cs n h) + β * ∑ s, tr.q n h s * v (n + 1) (Fin.snoc h s)
      = v n h := by
    intro n h
    simp only [hv, hcs, hWsnoc]
    exact (bellman_node_eq tr hρ R hsol hJ n h (hWpos n h)).2
  have htel := telescope_tree_eq tr β (crraUtil ρ) cs v hstepEq
  set T := fun n => β ^ n * ∑ h, tr.histProb h * v n h with hT
  have hμ₀1 : μ₀ < 1 := lt_of_le_of_lt (hlow 0 Fin.elim0) (hsol.1 0 Fin.elim0).2
  have hTrec : ∀ n, T (n + 1) = β ^ n * ∑ h, tr.histProb h * ((1 - μ n h) * v n h) := by
    intro n
    simp only [hT]
    rw [sum_succ_tree, pow_succ, mul_assoc]
    congr 1
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    have := (bellman_node_eq tr hρ R hsol hJ n h (hWpos n h)).1
    simp only [hv, hWsnoc]
    rw [← this]; ring
  have hTlim : Tendsto T atTop (𝓝 0) := by
    have hθ0 : 0 ≤ 1 - μ₀ := by linarith
    have hθ1 : 1 - μ₀ < 1 := by linarith
    have hgeo := tendsto_pow_atTop_nhds_zero_of_lt_one hθ0 hθ1
    rcases lt_or_gt_of_ne hρ1 with hlt | hgt
    · have hvnn : ∀ n h, 0 ≤ v n h := fun n h => mul_nonneg
        (Real.rpow_nonneg (hsol.1 n h).1.le _)
        (div_nonneg (Real.rpow_nonneg (hWpos n h).le _) (by linarith))
      have hT0 : ∀ n, 0 ≤ T n := fun n => mul_nonneg (pow_nonneg hβ.le n)
        (Finset.sum_nonneg fun h _ => mul_nonneg (tr.histProb_nonneg h) (hvnn n h))
      have hgeoT : ∀ n, T n ≤ (1 - μ₀) ^ n * T 0 := by
        intro n
        induction n with
        | zero => simp
        | succ n ih =>
          have hr : T (n + 1) ≤ (1 - μ₀) * T n := by
            rw [hTrec]
            simp only [hT, Finset.mul_sum]
            refine Finset.sum_le_sum fun h _ => ?_
            have := mul_le_mul_of_nonneg_right (by linarith [hlow n h] :
              1 - μ n h ≤ 1 - μ₀) (hvnn n h)
            have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left this
              (tr.histProb_nonneg h)) (pow_nonneg hβ.le n)
            linarith
          calc T (n + 1) ≤ (1 - μ₀) * T n := hr
            _ ≤ (1 - μ₀) * ((1 - μ₀) ^ n * T 0) := mul_le_mul_of_nonneg_left ih hθ0
            _ = (1 - μ₀) ^ (n + 1) * T 0 := by ring
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
        (by simpa using hgeo.mul_const (T 0)) hT0 hgeoT
    · have hvnp : ∀ n h, v n h ≤ 0 := fun n h => mul_nonpos_of_nonneg_of_nonpos
        (Real.rpow_nonneg (hsol.1 n h).1.le _)
        (div_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg (hWpos n h).le _) (by linarith))
      have hT0 : ∀ n, T n ≤ 0 := fun n => mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hβ.le n)
        (Finset.sum_nonpos fun h _ => mul_nonpos_of_nonneg_of_nonpos (tr.histProb_nonneg h)
          (hvnp n h))
      have hgeoT : ∀ n, (1 - μ₀) ^ n * T 0 ≤ T n := by
        intro n
        induction n with
        | zero => simp
        | succ n ih =>
          have hr : (1 - μ₀) * T n ≤ T (n + 1) := by
            rw [hTrec]
            simp only [hT, Finset.mul_sum]
            refine Finset.sum_le_sum fun h _ => ?_
            have := mul_le_mul_of_nonpos_right (by linarith [hlow n h] :
              1 - μ n h ≤ 1 - μ₀) (hvnp n h)
            have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left this
              (tr.histProb_nonneg h)) (pow_nonneg hβ.le n)
            linarith
          calc (1 - μ₀) ^ (n + 1) * T 0 = (1 - μ₀) * ((1 - μ₀) ^ n * T 0) := by ring
            _ ≤ (1 - μ₀) * T n := mul_le_mul_of_nonneg_left ih hθ0
            _ ≤ T (n + 1) := hr
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le (by simpa using hgeo.mul_const (T 0))
        tendsto_const_nhds hgeoT hT0
  have hpart : Tendsto (fun n => ∑ k ∈ range n, utilSeries tr β (crraUtil ρ) cs k) atTop
      (𝓝 (crraValue (μ 0 Fin.elim0) ρ W₀)) := by
    have e : ∀ n, ∑ k ∈ range n, utilSeries tr β (crraUtil ρ) cs k
        = v 0 Fin.elim0 - T n := fun n => by linarith [htel n]
    have hv0 : v 0 Fin.elim0 = crraValue (μ 0 Fin.elim0) ρ W₀ := rfl
    simp only [e]
    simpa [hv0] using (tendsto_const_nhds (x := v 0 Fin.elim0)).sub hTlim
  have hsumm : Summable (utilSeries tr β (crraUtil ρ) cs) := by
    have hterm : ∀ k h, crraUtil ρ (cs k h) = (cs k h) ^ (1 - ρ) / (1 - ρ) := fun _ _ => rfl
    rcases lt_or_gt_of_ne hρ1 with hlt | hgt
    · have hnn : ∀ k, 0 ≤ utilSeries tr β (crraUtil ρ) cs k := fun k =>
        mul_nonneg (pow_nonneg hβ.le k) (Finset.sum_nonneg fun h _ =>
          mul_nonneg (tr.histProb_nonneg h) (by
            rw [hterm]; exact div_nonneg (Real.rpow_nonneg (hadm.1 k h).le _) (by linarith)))
      refine summable_of_sum_range_le (c := v 0 Fin.elim0) hnn fun n => ?_
      have hTn : 0 ≤ T n := mul_nonneg (pow_nonneg hβ.le n) (Finset.sum_nonneg fun h _ =>
        mul_nonneg (tr.histProb_nonneg h) (mul_nonneg (Real.rpow_nonneg (hsol.1 n h).1.le _)
          (div_nonneg (Real.rpow_nonneg (hWpos n h).le _) (by linarith))))
      linarith [htel n]
    · have hnn : ∀ k, 0 ≤ -utilSeries tr β (crraUtil ρ) cs k := fun k => by
        have : utilSeries tr β (crraUtil ρ) cs k ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hβ.le k) (Finset.sum_nonpos fun h _ =>
            mul_nonpos_of_nonneg_of_nonpos (tr.histProb_nonneg h) (by
              rw [hterm]
              exact div_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg (hadm.1 k h).le _)
                (by linarith)))
        linarith
      have hTn : ∀ n, T n ≤ 0 := fun n => mul_nonpos_of_nonneg_of_nonpos (pow_nonneg hβ.le n)
        (Finset.sum_nonpos fun h _ => mul_nonpos_of_nonneg_of_nonpos (tr.histProb_nonneg h)
          (mul_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg (hsol.1 n h).1.le _)
            (div_nonpos_of_nonneg_of_nonpos (Real.rpow_nonneg (hWpos n h).le _)
              (by linarith))))
      have := summable_of_sum_range_le (c := -v 0 Fin.elim0) hnn fun n => by
        rw [Finset.sum_neg_distrib]
        have h1 := hTn n
        simp only [hT] at h1
        linarith [htel n]
      simpa using this.neg
  exact ⟨hadm, hsumm, tendsto_nhds_unique hsumm.hasSum.tendsto_sum_nat hpart, hupper⟩

/-- The verification theorem with history-dependent returns from primitives, O&R Supplement A,
p. 744. On an event tree with positive one-step probabilities, with no arbitrage and some
feasible portfolio at every history, and under the uniform growth condition (the one-period
optimal growth factor `βE_t(1 + r°)^{1−ρ}` is at most `G < 1` at every history), a solution
`(μ, x)` of the recursion `μ_t = (1 + [βE_t{(1 + r°_{t+1})^{1−ρ} μ_{t+1}^{−ρ}}]^{1/ρ})^{−1}`
exists, obtained as the limit of backward iterations, with `μ_t ≥ 1 − G^{1/ρ}`; the policy
`C = μ_t W` with portfolios `x_t(h)` attains `V_1(W₀) = μ_1^{−ρ}W₀^{1−ρ}/(1−ρ)`, and no
admissible plan does better. -/
theorem verification_varying_returns (tr : EventTree.Tree S) (hq : ∀ n h s, 0 < tr.q n h s)
    {β ρ : ℝ} (hβ : 0 < β) (hρ : 0 < ρ) (hρ1 : ρ ≠ 1)
    (R : (n : ℕ) → (Fin n → S) → Fin N → S → ℝ) (k : Fin N) (hNA : ∀ n h, NoArbitrage (R n h))
    (hF : ∀ n h, ∃ x₀, PortFeasible (R n h) x₀) {G : ℝ} (hG0 : 0 ≤ G) (hG1 : G < 1)
    (hG : ∀ n h x, PortFeasible (R n h) x → (∀ x', PortFeasible (R n h) x' →
      portObj (nodeSpace tr n h) ρ (R n h) x' ≤ portObj (nodeSpace tr n h) ρ (R n h) x) →
      growthFactor (nodeSpace tr n h) β ρ (R n h) x ≤ G) {W₀ : ℝ} (hW₀ : 0 < W₀) :
    ∃ μ xs, SolvesShareRecursion tr β ρ R μ xs ∧ (∀ n h, 1 - G ^ (1 / ρ) ≤ μ n h) ∧
      (∀ n h, Tendsto (fun m => iterA tr β ρ R m n h) atTop (𝓝 (μ n h ^ (-ρ)))) ∧
      AdmissibleT R W₀ (fun n h => μ n h * optWealthT R xs μ W₀ n h) xs ∧
      Summable (utilSeries tr β (crraUtil ρ) fun n h => μ n h * optWealthT R xs μ W₀ n h) ∧
      expectedUtility tr β (crraUtil ρ) (fun n h => μ n h * optWealthT R xs μ W₀ n h)
        = crraValue (μ 0 Fin.elim0) ρ W₀ ∧
      ∀ (c : (n : ℕ) → (Fin n → S) → ℝ) (x : (n : ℕ) → (Fin n → S) → Fin N → ℝ),
        AdmissibleT R W₀ c x → Summable (utilSeries tr β (crraUtil ρ) c) →
        expectedUtility tr β (crraUtil ρ) c ≤ crraValue (μ 0 Fin.elim0) ρ W₀ := by
  obtain ⟨μ, xs, hsol, hlow, hlim⟩ :=
    exists_share_recursion_solution tr hq hβ hρ hρ1 R k hNA hF hG0 hG1 hG
  have hμ₀ : 0 < 1 - G ^ (1 / ρ) := by
    linarith [Real.rpow_lt_one hG0 hG1 (one_div_pos.mpr hρ)]
  exact ⟨μ, xs, hsol, hlow, hlim, verification_tree tr hβ hρ hρ1 R hsol hμ₀ hlow hW₀⟩

/-! ### Log utility with history-dependent returns

O&R Supplement A, pp. 743–744: with log utility `μ = 1 − β` whatever the return process, and
the portfolio is chosen myopically to maximise `E_t log(1 + r°)`. -/

/-- The myopic log portfolio at the history `h` (O&R Supplement A, p. 743): a feasible
maximiser of `E_t log(1 + r°)` under the conditional probabilities at `h`, by Hilbert choice
(`myopicPort_spec` gives its optimality). -/
noncomputable def myopicPort (tr : EventTree.Tree S) (R : (n : ℕ) → (Fin n → S) → Fin N → S → ℝ)
    (n : ℕ) (h : Fin n → S) : Fin N → ℝ :=
  Classical.epsilon fun xs => PortFeasible (R n h) xs ∧ ∀ x, PortFeasible (R n h) x →
    logPortObj (nodeSpace tr n h) (R n h) x ≤ logPortObj (nodeSpace tr n h) (R n h) xs

/-- Existence of the myopic log portfolio at every history (O&R Supplement A, p. 743): under
positive one-step probabilities, no arbitrage and some feasible portfolio at `h`, the chosen
portfolio is feasible and maximises `E_t log(1 + r°)`. -/
theorem myopicPort_spec (tr : EventTree.Tree S) (hq : ∀ n h s, 0 < tr.q n h s)
    (R : (n : ℕ) → (Fin n → S) → Fin N → S → ℝ) (k : Fin N) (hNA : ∀ n h, NoArbitrage (R n h))
    (hF : ∀ n h, ∃ x₀, PortFeasible (R n h) x₀) (n : ℕ) (h : Fin n → S) :
    PortFeasible (R n h) (myopicPort tr R n h) ∧ ∀ x, PortFeasible (R n h) x →
      logPortObj (nodeSpace tr n h) (R n h) x
        ≤ logPortObj (nodeSpace tr n h) (R n h) (myopicPort tr R n h) := by
  obtain ⟨xs, hxs, hmax, -⟩ := exists_optimal_log_portfolio (nodeSpace tr n h) (R n h) k
    (hq n h) (hNA n h) (hF n h)
  exact Classical.epsilon_spec (p := fun xs => PortFeasible (R n h) xs ∧
    ∀ x, PortFeasible (R n h) x →
      logPortObj (nodeSpace tr n h) (R n h) x ≤ logPortObj (nodeSpace tr n h) (R n h) xs)
    ⟨xs, hxs, hmax⟩

/-- The optimal expected log return `g_t(h) = max E_t log(1 + r°)` at the history `h`
(O&R Supplement A, p. 743). -/
noncomputable def myopicGrowth (tr : EventTree.Tree S)
    (R : (n : ℕ) → (Fin n → S) → Fin N → S → ℝ) (n : ℕ) (h : Fin n → S) : ℝ :=
  logPortObj (nodeSpace tr n h) (R n h) (myopicPort tr R n h)

/-- The terms of the backward-summed constant of the log value function (O&R Supplement A,
p. 743): `D_0(h) = log(1 − β) + (β/(1 − β))(log β + g_t(h))` and
`D_{j+1}(h) = βΣ_s q(s|h) D_j(h, s)`, so `D_j(h) = β^j E_h[D_0 at date t + j]`. -/
noncomputable def logSeriesTerm (tr : EventTree.Tree S) (β : ℝ)
    (R : (n : ℕ) → (Fin n → S) → Fin N → S → ℝ) : ℕ → (n : ℕ) → (Fin n → S) → ℝ
  | 0 => fun n h => Real.log (1 - β) + β / (1 - β) * (Real.log β + myopicGrowth tr R n h)
  | j + 1 => fun n h => β * ∑ s, tr.q n h s * logSeriesTerm tr β R j (n + 1) (Fin.snoc h s)

/-- The constant `K_t(h) = Σ_j D_j(h)` of the log value function with history-dependent returns
(O&R Supplement A, p. 743). -/
noncomputable def logConstT (tr : EventTree.Tree S) (β : ℝ)
    (R : (n : ℕ) → (Fin n → S) → Fin N → S → ℝ) (n : ℕ) (h : Fin n → S) : ℝ :=
  ∑' j, logSeriesTerm tr β R j n h

/-- The log value function `V_t(h, W) = log W/(1 − β) + K_t(h)` (O&R Supplement A, p. 743). -/
noncomputable def logValueT (tr : EventTree.Tree S) (β : ℝ)
    (R : (n : ℕ) → (Fin n → S) → Fin N → S → ℝ) (n : ℕ) (h : Fin n → S) (W : ℝ) : ℝ :=
  Real.log W / (1 - β) + logConstT tr β R n h

/-- Geometric bound on the series terms (O&R Supplement A, p. 743): if `|g_t| ≤ M` everywhere
then `|D_j(h)| ≤ β^j C` with `C = |log(1 − β)| + (β/(1 − β))(|log β| + M)`. -/
theorem logSeriesTerm_bound (tr : EventTree.Tree S) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (R : (n : ℕ) → (Fin n → S) → Fin N → S → ℝ) {M : ℝ}
    (hM : ∀ n h, |myopicGrowth tr R n h| ≤ M) (j : ℕ) :
    ∀ n h, |logSeriesTerm tr β R j n h|
      ≤ β ^ j * (|Real.log (1 - β)| + β / (1 - β) * (|Real.log β| + M)) := by
  have hb : 0 ≤ β / (1 - β) := div_nonneg hβ0.le (by linarith)
  induction j with
  | zero =>
    intro n h
    simp only [logSeriesTerm, pow_zero, one_mul]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_of_nonneg hb]
    have h2 := abs_add_le (Real.log β) (myopicGrowth tr R n h)
    have h3 := hM n h
    nlinarith
  | succ j ih =>
    intro n h
    simp only [logSeriesTerm]
    rw [abs_mul, abs_of_pos hβ0, pow_succ]
    have : |∑ s, tr.q n h s * logSeriesTerm tr β R j (n + 1) (Fin.snoc h s)|
        ≤ β ^ j * (|Real.log (1 - β)| + β / (1 - β) * (|Real.log β| + M)) := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
      calc ∑ s, |tr.q n h s * logSeriesTerm tr β R j (n + 1) (Fin.snoc h s)|
          ≤ ∑ s, tr.q n h s * (β ^ j * (|Real.log (1 - β)| + β / (1 - β) * (|Real.log β| + M)))
            := Finset.sum_le_sum fun s _ => by
              rw [abs_mul, abs_of_nonneg (tr.q_nonneg n h s)]
              exact mul_le_mul_of_nonneg_left (ih _ _) (tr.q_nonneg n h s)
        _ = β ^ j * (|Real.log (1 - β)| + β / (1 - β) * (|Real.log β| + M)) := by
          rw [← Finset.sum_mul, tr.q_sum, one_mul]
    nlinarith

/-- The backward-summed series converges (O&R Supplement A, p. 743), under `0 < β < 1` and
uniformly bounded optimal expected log returns `|g_t| ≤ M`. -/
theorem logSeries_summable (tr : EventTree.Tree S) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (R : (n : ℕ) → (Fin n → S) → Fin N → S → ℝ) {M : ℝ}
    (hM : ∀ n h, |myopicGrowth tr R n h| ≤ M) (n : ℕ) (h : Fin n → S) :
    Summable fun j => logSeriesTerm tr β R j n h :=
  Summable.of_norm_bounded ((summable_geometric_of_lt_one hβ0.le hβ1).mul_right _)
    fun j => by rw [Real.norm_eq_abs]; exact logSeriesTerm_bound tr hβ0 hβ1 R hM j n h

/-- The constant is bounded, `|K_t(h)| ≤ C/(1 − β)` (O&R Supplement A, p. 743). -/
theorem logConstT_bound (tr : EventTree.Tree S) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (R : (n : ℕ) → (Fin n → S) → Fin N → S → ℝ) {M : ℝ}
    (hM : ∀ n h, |myopicGrowth tr R n h| ≤ M) (n : ℕ) (h : Fin n → S) :
    |logConstT tr β R n h|
      ≤ (|Real.log (1 - β)| + β / (1 - β) * (|Real.log β| + M)) / (1 - β) := by
  set Cb := |Real.log (1 - β)| + β / (1 - β) * (|Real.log β| + M)
  have hg := (hasSum_geometric_of_lt_one hβ0.le hβ1).mul_right Cb
  have hs := logSeries_summable tr hβ0 hβ1 R hM n h
  have hb := fun j => logSeriesTerm_bound tr hβ0 hβ1 R hM j n h
  have e : Cb / (1 - β) = (1 - β)⁻¹ * Cb := by ring
  rw [e, abs_le]
  unfold logConstT
  constructor
  · have := Summable.tsum_le_tsum (fun j => neg_le_of_abs_le (hb j)) hg.summable.neg hs
    rw [tsum_neg, hg.tsum_eq] at this
    linarith
  · have := Summable.tsum_le_tsum (fun j => le_of_abs_le (hb j)) hs hg.summable
    rw [hg.tsum_eq] at this
    exact this

/-- The recursion for the constant, O&R Supplement A, p. 743:
`K_t(h) = log(1 − β) + (β/(1 − β))(log β + g_t(h)) + βΣ_s q(s|h) K_{t+1}(h, s)`. -/
theorem logConstT_recursion (tr : EventTree.Tree S) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (R : (n : ℕ) → (Fin n → S) → Fin N → S → ℝ) {M : ℝ}
    (hM : ∀ n h, |myopicGrowth tr R n h| ≤ M) (n : ℕ) (h : Fin n → S) :
    logConstT tr β R n h = Real.log (1 - β) + β / (1 - β) * (Real.log β + myopicGrowth tr R n h)
      + β * ∑ s, tr.q n h s * logConstT tr β R (n + 1) (Fin.snoc h s) := by
  have hs : ∀ s, Summable fun j => tr.q n h s * logSeriesTerm tr β R j (n + 1) (Fin.snoc h s) :=
    fun s => (logSeries_summable tr hβ0 hβ1 R hM _ _).mul_left _
  rw [logConstT, (logSeries_summable tr hβ0 hβ1 R hM n h).tsum_eq_zero_add]
  congr 1
  change ∑' j, β * ∑ s, tr.q n h s * logSeriesTerm tr β R j (n + 1) (Fin.snoc h s) = _
  rw [tsum_mul_left, Summable.tsum_finsetSum fun s _ => hs s]
  congr 1
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [tsum_mul_left]
  rfl

/-- The log consumption split (O&R Supplement A, p. 743): for `0 < β < 1`, `0 < C < W` and
expected log portfolio returns `G′ ≤ G`,
`log C + (β/(1 − β))(G′ + log(W − C)) ≤ log((1 − β)W) + (β/(1 − β))(G + log(βW))`. -/
theorem log_split_le {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) {W C G G' : ℝ} (hC : 0 < C)
    (hCW : C < W) (hG : G' ≤ G) :
    Real.log C + β / (1 - β) * (G' + Real.log (W - C))
      ≤ Real.log ((1 - β) * W) + β / (1 - β) * (G + Real.log (β * W)) := by
  have h1 : 0 < 1 - β := by linarith
  have hW : 0 < W := hC.trans hCW
  have hD : 0 < W - C := by linarith
  have hc : 0 ≤ β / (1 - β) := div_nonneg hβ0.le h1.le
  have t1 := log_tangent (mul_pos h1 hW) hC
  have t2 := log_tangent (mul_pos hβ0 hW) hD
  have e1 : β / (1 - β) * (1 / (β * W)) = 1 / ((1 - β) * W) := by field_simp
  have t2' := mul_le_mul_of_nonneg_left t2 hc
  have lin : 1 / ((1 - β) * W) * (C - (1 - β) * W)
      + β / (1 - β) * (1 / (β * W) * (W - C - β * W)) = 0 := by
    rw [← mul_assoc, e1]; ring
  nlinarith [mul_le_mul_of_nonneg_left hG hc]

/-- The log continuation value at a history (O&R Supplement A, p. 743): saving `D > 0` in a
feasible portfolio `x` gives
`βE_t V_{t+1}((1 + r°)D) = (β/(1 − β))(E_t log(1 + r°) + log D) + βE_t K_{t+1}`. -/
theorem log_node_continuation (tr : EventTree.Tree S) (β : ℝ)
    (R : (n : ℕ) → (Fin n → S) → Fin N → S → ℝ) (n : ℕ) (h : Fin n → S) {x : Fin N → ℝ}
    (hx : PortFeasible (R n h) x) {D : ℝ} (hD : 0 < D) :
    β * ∑ s, tr.q n h s * logValueT tr β R (n + 1) (Fin.snoc h s)
        ((1 + portRet (R n h) x s) * D)
      = β / (1 - β) * (logPortObj (nodeSpace tr n h) (R n h) x + Real.log D)
        + β * ∑ s, tr.q n h s * logConstT tr β R (n + 1) (Fin.snoc h s) := by
  have e : ∀ s, tr.q n h s * logValueT tr β R (n + 1) (Fin.snoc h s)
      ((1 + portRet (R n h) x s) * D) = tr.q n h s * Real.log (1 + portRet (R n h) x s) / (1 - β)
        + tr.q n h s * Real.log D / (1 - β)
        + tr.q n h s * logConstT tr β R (n + 1) (Fin.snoc h s) := by
    intro s
    rw [logValueT, Real.log_mul (hx.2 s).ne' hD.ne']
    ring
  simp only [e, Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_mul, tr.q_sum,
    logPortObj, StateSpace.expect, nodeSpace]
  ring

/-- The Bellman equation for log utility with history-dependent returns, O&R Supplement A,
p. 743: at every history, every `0 < C < W` and feasible portfolio give
`log C + βE_t V_{t+1}((1 + r°)(W − C)) ≤ V_t(W)`, with equality at `C = (1 − β)W` and the myopic
portfolio. -/
theorem bellman_log_node (tr : EventTree.Tree S) (hq : ∀ n h s, 0 < tr.q n h s) {β : ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (R : (n : ℕ) → (Fin n → S) → Fin N → S → ℝ) (k : Fin N)
    (hNA : ∀ n h, NoArbitrage (R n h)) (hF : ∀ n h, ∃ x₀, PortFeasible (R n h) x₀) {M : ℝ}
    (hM : ∀ n h, |myopicGrowth tr R n h| ≤ M) (n : ℕ) (h : Fin n → S) {W : ℝ} (hW : 0 < W) :
    (∀ C x, 0 < C → C < W → PortFeasible (R n h) x →
      Real.log C + β * ∑ s, tr.q n h s * logValueT tr β R (n + 1) (Fin.snoc h s)
        ((1 + portRet (R n h) x s) * (W - C)) ≤ logValueT tr β R n h W) ∧
    Real.log ((1 - β) * W) + β * ∑ s, tr.q n h s * logValueT tr β R (n + 1) (Fin.snoc h s)
        ((1 + portRet (R n h) (myopicPort tr R n h) s) * (W - (1 - β) * W))
      = logValueT tr β R n h W := by
  have h1 : 0 < 1 - β := by linarith
  obtain ⟨hxs, hmax⟩ := myopicPort_spec tr hq R k hNA hF n h
  have hconst : Real.log ((1 - β) * W) + β / (1 - β) * (myopicGrowth tr R n h
      + Real.log (β * W)) + β * ∑ s, tr.q n h s * logConstT tr β R (n + 1) (Fin.snoc h s)
      = logValueT tr β R n h W := by
    rw [logValueT, logConstT_recursion tr hβ0 hβ1 R hM n h, Real.log_mul h1.ne' hW.ne',
      Real.log_mul hβ0.ne' hW.ne']
    field_simp
    ring
  refine ⟨fun C x hC hCW hx => ?_, ?_⟩
  · rw [log_node_continuation tr β R n h hx (by linarith), ← hconst]
    have := log_split_le hβ0 hβ1 hC hCW (hmax x hx)
    unfold myopicGrowth
    linarith
  · rw [log_node_continuation tr β R n h hxs (by nlinarith), ← hconst,
      show W - (1 - β) * W = β * W by ring]
    unfold myopicGrowth
    ring

/-- The expected log of wealth along an admissible plan grows by at most `M` per period when
`|g_t| ≤ M` (O&R Supplement A, p. 743). -/
theorem expect_log_wealthT_le (tr : EventTree.Tree S) (hq : ∀ n h s, 0 < tr.q n h s)
    (R : (n : ℕ) → (Fin n → S) → Fin N → S → ℝ) (k : Fin N) (hNA : ∀ n h, NoArbitrage (R n h))
    (hF : ∀ n h, ∃ x₀, PortFeasible (R n h) x₀) {M : ℝ}
    (hM : ∀ n h, |myopicGrowth tr R n h| ≤ M) (W₀ : ℝ) {c : (n : ℕ) → (Fin n → S) → ℝ}
    {x : (n : ℕ) → (Fin n → S) → Fin N → ℝ} (hadm : AdmissibleT R W₀ c x) (n : ℕ) :
    ∑ h, tr.histProb h * Real.log (wealthT R W₀ c x n h) ≤ Real.log W₀ + n * M := by
  have := nonempty_of_tree tr
  induction n with
  | zero =>
    simp only [Fintype.sum_unique, tr.histProb_zero, one_mul, CharP.cast_eq_zero, zero_mul,
      add_zero]
    rfl
  | succ n ih =>
    rw [sum_succ_tree]
    simp only [wealthT_snoc]
    have hnode : ∀ h, tr.histProb h * ∑ s, tr.q n h s * Real.log
        ((1 + portRet (R n h) (x n h) s) * (wealthT R W₀ c x n h - c n h))
        ≤ tr.histProb h * (M + Real.log (wealthT R W₀ c x n h)) := by
      intro h
      obtain ⟨hlt, hxn⟩ := admissibleT_step R W₀ hadm n h
      have hD : 0 < wealthT R W₀ c x n h - c n h := by linarith
      have e : ∑ s, tr.q n h s * Real.log ((1 + portRet (R n h) (x n h) s)
          * (wealthT R W₀ c x n h - c n h))
          = logPortObj (nodeSpace tr n h) (R n h) (x n h)
            + Real.log (wealthT R W₀ c x n h - c n h) := by
        simp only [logPortObj, StateSpace.expect, nodeSpace,
          Real.log_mul (hxn.2 _).ne' hD.ne', mul_add, Finset.sum_add_distrib,
          ← Finset.sum_mul, tr.q_sum, one_mul]
      rw [e]
      refine mul_le_mul_of_nonneg_left ?_ (tr.histProb_nonneg h)
      have h1 := (myopicPort_spec tr hq R k hNA hF n h).2 _ hxn
      have h2 := Real.log_le_log hD (by linarith [hadm.1 n h] :
        wealthT R W₀ c x n h - c n h ≤ wealthT R W₀ c x n h)
      have h3 := le_of_abs_le (hM n h)
      unfold myopicGrowth at h3
      linarith
    have hs := Finset.sum_le_sum fun h (_ : h ∈ univ) => hnode h
    simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, tr.histProb_sum_eq_one,
      one_mul] at hs
    push_cast
    linarith

/-- `β^t E_t K_t` is bounded in absolute value by `β^t C/(1 − β)` (O&R Supplement A,
p. 743). -/
theorem abs_expect_logConstT_le (tr : EventTree.Tree S) {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (R : (n : ℕ) → (Fin n → S) → Fin N → S → ℝ) {M : ℝ}
    (hM : ∀ n h, |myopicGrowth tr R n h| ≤ M) (n : ℕ) :
    |∑ h, tr.histProb h * logConstT tr β R n h|
      ≤ (|Real.log (1 - β)| + β / (1 - β) * (|Real.log β| + M)) / (1 - β) := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ h, |tr.histProb h * logConstT tr β R n h|
      ≤ ∑ h, tr.histProb h * ((|Real.log (1 - β)| + β / (1 - β) * (|Real.log β| + M))
        / (1 - β)) := Finset.sum_le_sum fun h _ => by
          rw [abs_mul, abs_of_nonneg (tr.histProb_nonneg h)]
          exact mul_le_mul_of_nonneg_left (logConstT_bound tr hβ0 hβ1 R hM n h)
            (tr.histProb_nonneg h)
    _ = _ := by rw [← Finset.sum_mul, tr.histProb_sum_eq_one, one_mul]

/-- The transversality property for log utility with history-dependent returns, O&R
Supplement A, p. 743 (proved, not assumed): for every admissible plan with convergent utility
series, `β^t E V_t(W_t) → 0`. -/
theorem transversality_log_tree (tr : EventTree.Tree S) (hq : ∀ n h s, 0 < tr.q n h s)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (R : (n : ℕ) → (Fin n → S) → Fin N → S → ℝ)
    (k : Fin N) (hNA : ∀ n h, NoArbitrage (R n h)) (hF : ∀ n h, ∃ x₀, PortFeasible (R n h) x₀)
    {M : ℝ} (hM : ∀ n h, |myopicGrowth tr R n h| ≤ M) (W₀ : ℝ)
    {c : (n : ℕ) → (Fin n → S) → ℝ} {x : (n : ℕ) → (Fin n → S) → Fin N → ℝ}
    (hadm : AdmissibleT R W₀ c x) (hU : Summable (utilSeries tr β Real.log c)) :
    Tendsto (fun n => β ^ n * ∑ h, tr.histProb h * logValueT tr β R n h (wealthT R W₀ c x n h))
      atTop (𝓝 0) := by
  have h1 : 0 < 1 - β := by linarith
  set Kb := (|Real.log (1 - β)| + β / (1 - β) * (|Real.log β| + M)) / (1 - β)
  have hT : ∀ n, β ^ n * ∑ h, tr.histProb h * logValueT tr β R n h (wealthT R W₀ c x n h)
      = β ^ n * (∑ h, tr.histProb h * Real.log (wealthT R W₀ c x n h)) / (1 - β)
        + β ^ n * ∑ h, tr.histProb h * logConstT tr β R n h := by
    intro n
    have e : ∑ h, tr.histProb h * logValueT tr β R n h (wealthT R W₀ c x n h)
        = (∑ h, tr.histProb h * Real.log (wealthT R W₀ c x n h)) / (1 - β)
          + ∑ h, tr.histProb h * logConstT tr β R n h := by
      rw [Finset.sum_div, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun h _ => by unfold logValueT; ring
    rw [e]; ring
  have hK := fun n => abs_le.mp (abs_expect_logConstT_le tr hβ0 hβ1 R hM n)
  have hlow : ∀ n, utilSeries tr β Real.log c n / (1 - β) - β ^ n * Kb
      ≤ β ^ n * ∑ h, tr.histProb h * logValueT tr β R n h (wealthT R W₀ c x n h) := by
    intro n
    rw [hT, utilSeries]
    have hl : ∑ h, tr.histProb h * Real.log (c n h)
        ≤ ∑ h, tr.histProb h * Real.log (wealthT R W₀ c x n h) :=
      Finset.sum_le_sum fun h _ => mul_le_mul_of_nonneg_left
        (Real.log_le_log (hadm.1 n h) (hadm.2.1 n h)) (tr.histProb_nonneg h)
    have := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hl (pow_nonneg hβ0.le n))
      h1.le
    have := mul_le_mul_of_nonneg_left (hK n).1 (pow_nonneg hβ0.le n)
    linarith
  have hup : ∀ n, β ^ n * ∑ h, tr.histProb h * logValueT tr β R n h (wealthT R W₀ c x n h)
      ≤ (Real.log W₀ / (1 - β) + Kb) * β ^ n + M / (1 - β) * (n * β ^ n) := by
    intro n
    rw [hT]
    have := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left
      (expect_log_wealthT_le tr hq R k hNA hF hM W₀ hadm n) (pow_nonneg hβ0.le n)) h1.le
    have := mul_le_mul_of_nonneg_left (hK n).2 (pow_nonneg hβ0.le n)
    have e : β ^ n * (Real.log W₀ + n * M) / (1 - β) + β ^ n * Kb
        = (Real.log W₀ / (1 - β) + Kb) * β ^ n + M / (1 - β) * (n * β ^ n) := by ring
    linarith
  have hgeo := tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1
  have hlowT : Tendsto (fun n => utilSeries tr β Real.log c n / (1 - β) - β ^ n * Kb)
      atTop (𝓝 0) := by
    simpa using (hU.tendsto_atTop_zero.div_const (1 - β)).sub (hgeo.mul_const Kb)
  have hupT : Tendsto (fun n : ℕ => (Real.log W₀ / (1 - β) + Kb) * β ^ n
      + M / (1 - β) * (n * β ^ n)) atTop (𝓝 0) := by
    simpa using (hgeo.const_mul (Real.log W₀ / (1 - β) + Kb)).add
      ((tendsto_self_mul_const_pow_of_lt_one hβ0.le hβ1).const_mul (M / (1 - β)))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlowT hupT hlow hup

/-- The verification theorem for log utility with history-dependent returns, O&R Supplement A,
pp. 743–744. On an event tree with positive one-step probabilities, no arbitrage and some
feasible portfolio at every history, `0 < β < 1`, and uniformly bounded optimal expected log
returns `|max E_t log(1 + r°)| ≤ M` (the primitive condition making the backward-summed constant
converge), and `W₀ > 0`: the policy `C = (1 − β)W` (the book's `μ = 1 − β`, for any return
process) with the myopic portfolio maximising `E_t log(1 + r°)` is admissible, its utility series
converges, and it attains `V_1(W₀) = log W₀/(1 − β) + K_1`; every admissible plan with convergent
utility series achieves at most `V_1(W₀)`. -/
theorem verification_log_tree (tr : EventTree.Tree S) (hq : ∀ n h s, 0 < tr.q n h s)
    {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (R : (n : ℕ) → (Fin n → S) → Fin N → S → ℝ)
    (k : Fin N) (hNA : ∀ n h, NoArbitrage (R n h)) (hF : ∀ n h, ∃ x₀, PortFeasible (R n h) x₀)
    {M : ℝ} (hM : ∀ n h, |myopicGrowth tr R n h| ≤ M) {W₀ : ℝ} (hW₀ : 0 < W₀) :
    AdmissibleT R W₀ (fun n h => (1 - β) * optWealthT R (myopicPort tr R) (fun _ _ => 1 - β)
        W₀ n h) (myopicPort tr R) ∧
      Summable (utilSeries tr β Real.log fun n h =>
        (1 - β) * optWealthT R (myopicPort tr R) (fun _ _ => 1 - β) W₀ n h) ∧
      expectedUtility tr β Real.log (fun n h =>
        (1 - β) * optWealthT R (myopicPort tr R) (fun _ _ => 1 - β) W₀ n h)
          = logValueT tr β R 0 Fin.elim0 W₀ ∧
      ∀ (c : (n : ℕ) → (Fin n → S) → ℝ) (x : (n : ℕ) → (Fin n → S) → Fin N → ℝ),
        AdmissibleT R W₀ c x → Summable (utilSeries tr β Real.log c) →
        expectedUtility tr β Real.log c ≤ logValueT tr β R 0 Fin.elim0 W₀ := by
  have := nonempty_of_tree tr
  have h1 : 0 < 1 - β := by linarith
  set xL := myopicPort tr R with hxL
  have hxLf : ∀ n h, PortFeasible (R n h) (xL n h) := fun n h =>
    (myopicPort_spec tr hq R k hNA hF n h).1
  set Ws := optWealthT R xL (fun _ _ => 1 - β) W₀ with hWs
  set cs := fun n (h : Fin n → S) => (1 - β) * Ws n h with hcs
  have hWpos := optWealthT_pos R (fun n h s => (hxLf n h).2 s)
    (fun _ _ => (by linarith : 1 - β < 1)) hW₀
  have hadm : AdmissibleT R W₀ cs xL := by
    refine ⟨fun n h => mul_pos h1 (hWpos n h), fun n h => ?_, fun n h => (hxLf n h).1⟩
    rw [hcs, wealthT_optPlan]
    have := hWpos n h
    nlinarith
  set Kb := (|Real.log (1 - β)| + β / (1 - β) * (|Real.log β| + M)) / (1 - β)
  have hK := fun n => abs_expect_logConstT_le tr hβ0 hβ1 R hM n
  -- upper bound
  have hupper : ∀ (c : (n : ℕ) → (Fin n → S) → ℝ) (x : (n : ℕ) → (Fin n → S) → Fin N → ℝ),
      AdmissibleT R W₀ c x → Summable (utilSeries tr β Real.log c) →
      expectedUtility tr β Real.log c ≤ logValueT tr β R 0 Fin.elim0 W₀ := by
    intro c x hadm' hU
    have hstep : ∀ n h, Real.log (c n h) + β * ∑ s, tr.q n h s
        * (fun n h => logValueT tr β R n h (wealthT R W₀ c x n h)) (n + 1) (Fin.snoc h s)
        ≤ (fun n h => logValueT tr β R n h (wealthT R W₀ c x n h)) n h := by
      intro n h
      obtain ⟨hlt, hxn⟩ := admissibleT_step R W₀ hadm' n h
      simp only [wealthT_snoc]
      exact (bellman_log_node tr hq hβ0 hβ1 R k hNA hF hM n h
        (lt_of_lt_of_le (hadm'.1 n h) (hadm'.2.1 n h))).1 _ _ (hadm'.1 n h) hlt hxn
    have htel := telescope_tree_le tr hβ0.le Real.log c
      (fun n h => logValueT tr β R n h (wealthT R W₀ c x n h)) hstep
    have hT := transversality_log_tree tr hq hβ0 hβ1 R k hNA hF hM W₀ hadm' hU
    have h2 := (tendsto_const_nhds (x := logValueT tr β R 0 Fin.elim0 W₀)).sub hT
    rw [sub_zero] at h2
    exact le_of_tendsto_of_tendsto' hU.hasSum.tendsto_sum_nat h2 fun n => by
      have := htel n
      beta_reduce at this
      rw [show wealthT R W₀ c x 0 Fin.elim0 = W₀ from rfl] at this
      linarith
  -- attainment
  have hWsnoc : ∀ n (h : Fin n → S) s, Ws (n + 1) (Fin.snoc h s)
      = (1 + portRet (R n h) (xL n h) s) * (Ws n h - (1 - β) * Ws n h) := by
    intro n h s
    simp only [hWs, optWealthT, Fin.init_snoc, Fin.snoc_last]
    ring
  set v := fun n (h : Fin n → S) => logValueT tr β R n h (Ws n h) with hv
  have hstepEq : ∀ n h, Real.log (cs n h) + β * ∑ s, tr.q n h s * v (n + 1) (Fin.snoc h s)
      = v n h := by
    intro n h
    simp only [hv, hcs, hWsnoc]
    exact (bellman_log_node tr hq hβ0 hβ1 R k hNA hF hM n h (hWpos n h)).2
  have htel := telescope_tree_eq tr β Real.log cs v hstepEq
  -- expected log of optimal wealth
  set L := fun n => ∑ h, tr.histProb h * Real.log (Ws n h) with hL
  have hLb : ∀ n, |L n| ≤ |Real.log W₀| + n * (|Real.log β| + M) := by
    intro n
    induction n with
    | zero =>
      simp only [hL, Fintype.sum_unique, tr.histProb_zero, one_mul, CharP.cast_eq_zero,
        zero_mul, add_zero]
      rfl
    | succ n ih =>
      have e : L (n + 1) = ∑ h, tr.histProb h * myopicGrowth tr R n h + Real.log β + L n := by
        simp only [hL]
        rw [sum_succ_tree]
        have e3 : ∀ h s, Real.log (Ws (n + 1) (Fin.snoc h s))
            = Real.log (1 + portRet (R n h) (xL n h) s) + Real.log β + Real.log (Ws n h) := by
          intro h s
          rw [hWsnoc, show Ws n h - (1 - β) * Ws n h = β * Ws n h by ring,
            Real.log_mul ((hxLf n h).2 s).ne' (mul_pos hβ0 (hWpos n h)).ne',
            Real.log_mul hβ0.ne' (hWpos n h).ne']
          ring
        have e4 : ∀ h, ∑ s, tr.q n h s * Real.log (Ws (n + 1) (Fin.snoc h s))
            = myopicGrowth tr R n h + Real.log β + Real.log (Ws n h) := by
          intro h
          simp only [e3, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, tr.q_sum, one_mul]
          rfl
        have e2 : ∀ h, tr.histProb h * ∑ s, tr.q n h s * Real.log (Ws (n + 1) (Fin.snoc h s))
            = tr.histProb h * myopicGrowth tr R n h + tr.histProb h * Real.log β
              + tr.histProb h * Real.log (Ws n h) := by
          intro h; rw [e4]; ring
        simp only [e2, Finset.sum_add_distrib, ← Finset.sum_mul, tr.histProb_sum_eq_one,
          one_mul]
      have hg : |∑ h, tr.histProb h * myopicGrowth tr R n h| ≤ M := by
        refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
        calc ∑ h, |tr.histProb h * myopicGrowth tr R n h| ≤ ∑ h, tr.histProb h * M :=
              Finset.sum_le_sum fun h _ => by
                rw [abs_mul, abs_of_nonneg (tr.histProb_nonneg h)]
                exact mul_le_mul_of_nonneg_left (hM n h) (tr.histProb_nonneg h)
          _ = M := by rw [← Finset.sum_mul, tr.histProb_sum_eq_one, one_mul]
      rw [e]
      have := abs_add_le (∑ h, tr.histProb h * myopicGrowth tr R n h + Real.log β) (L n)
      have := abs_add_le (∑ h, tr.histProb h * myopicGrowth tr R n h) (Real.log β)
      push_cast
      linarith
  have hMn : 0 ≤ M := (abs_nonneg _).trans (hM 0 Fin.elim0)
  -- the utility terms are dominated by a summable sequence
  have hutil : ∀ n, utilSeries tr β Real.log cs n = β ^ n * (Real.log (1 - β) + L n) := by
    intro n
    have e : ∀ h, Real.log ((1 - β) * Ws n h) = Real.log (1 - β) + Real.log (Ws n h) :=
      fun h => Real.log_mul h1.ne' (hWpos n h).ne'
    simp only [utilSeries, hcs, hL, e, mul_add,
      Finset.sum_add_distrib, ← Finset.sum_mul, tr.histProb_sum_eq_one, one_mul]
  have hnorm : ‖β‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos hβ0]; exact hβ1
  have hdom : Summable fun n : ℕ => (|Real.log (1 - β)| + |Real.log W₀|) * β ^ n
      + (|Real.log β| + M) * (n * β ^ n) :=
    ((summable_geometric_of_lt_one hβ0.le hβ1).mul_left _).add
      ((hasSum_coe_mul_geometric_of_norm_lt_one hnorm).summable.mul_left _)
  have hsumm : Summable (utilSeries tr β Real.log cs) := by
    refine Summable.of_norm_bounded hdom fun n => ?_
    rw [hutil, Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0.le n)]
    have h2 := abs_add_le (Real.log (1 - β)) (L n)
    have h3 := hLb n
    have hb := pow_nonneg hβ0.le n
    have h4 : |Real.log (1 - β) + L n| ≤ |Real.log (1 - β)| + |Real.log W₀|
        + n * (|Real.log β| + M) := by linarith
    have h5 := mul_le_mul_of_nonneg_left h4 hb
    nlinarith
  -- the remainder vanishes
  have hTlim : Tendsto (fun n => β ^ n * ∑ h, tr.histProb h * v n h) atTop (𝓝 0) := by
    have hbound : ∀ n, ‖β ^ n * ∑ h, tr.histProb h * v n h‖
        ≤ (|Real.log W₀| / (1 - β) + Kb) * β ^ n
          + (|Real.log β| + M) / (1 - β) * (n * β ^ n) := by
      intro n
      have e : ∑ h, tr.histProb h * v n h
          = L n / (1 - β) + ∑ h, tr.histProb h * logConstT tr β R n h := by
        simp only [hv, hL]
        rw [Finset.sum_div, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun h _ => by unfold logValueT; ring
      rw [e, Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0.le n)]
      have hLd : |L n / (1 - β)| ≤ (|Real.log W₀| + n * (|Real.log β| + M)) / (1 - β) := by
        rw [abs_div, abs_of_pos h1]; exact div_le_div_of_nonneg_right (hLb n) h1.le
      have ha := abs_add_le (L n / (1 - β)) (∑ h, tr.histProb h * logConstT tr β R n h)
      have hb := pow_nonneg hβ0.le n
      have hsum : |L n / (1 - β) + ∑ h, tr.histProb h * logConstT tr β R n h|
          ≤ (|Real.log W₀| + n * (|Real.log β| + M)) / (1 - β) + Kb := by
        linarith [hK n]
      have := mul_le_mul_of_nonneg_left hsum hb
      have e2 : β ^ n * ((|Real.log W₀| + n * (|Real.log β| + M)) / (1 - β) + Kb)
          = (|Real.log W₀| / (1 - β) + Kb) * β ^ n
            + (|Real.log β| + M) / (1 - β) * (n * β ^ n) := by ring
      linarith
    have hgeo := tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1
    refine squeeze_zero_norm hbound ?_
    simpa using (hgeo.const_mul (|Real.log W₀| / (1 - β) + Kb)).add
      ((tendsto_self_mul_const_pow_of_lt_one hβ0.le hβ1).const_mul ((|Real.log β| + M) / (1 - β)))
  have hpart : Tendsto (fun n => ∑ k ∈ range n, utilSeries tr β Real.log cs k) atTop
      (𝓝 (logValueT tr β R 0 Fin.elim0 W₀)) := by
    have e : ∀ n, ∑ k ∈ range n, utilSeries tr β Real.log cs k
        = v 0 Fin.elim0 - β ^ n * ∑ h, tr.histProb h * v n h := fun n => by linarith [htel n]
    have hv0 : v 0 Fin.elim0 = logValueT tr β R 0 Fin.elim0 W₀ := rfl
    rw [← hv0]
    simp only [e]
    simpa using (tendsto_const_nhds (x := v 0 Fin.elim0)).sub hTlim
  exact ⟨hadm, hsumm, tendsto_nhds_unique hsumm.hasSum.tendsto_sum_nat hpart, hupper⟩

end ObstfeldRogoff.InternationalFinancialMarkets.ConsumptionPortfolio
