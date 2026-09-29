/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.MetricSpace.Contracting
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic.FieldSimp

/-!
# Brock–Mirman / Long–Plosser stochastic growth

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §7.4.1
(pp. 497–500), equations (103)–(113), footnotes 46–48; Exercise 4 (p. 512); Appendix 7B
(pp. 510–512), equations (137)–(143).

The shock is a finite-state Markov chain (i.i.d. as a special case); a contingent plan assigns
next period's capital to every node of the event tree (a list of states, most recent first).

* **Event-tree primitives** (`ev`, tower property, telescoping bound), reused by the other
  stochastic modules of this chapter.
* **Optimality of the Long–Plosser policy** `K′ = αβAK^α`, `C = (1 − αβ)AK^α` over the genuine
  infinite horizon, against every feasible contingent plan: a stochastic supporting-hyperplane
  argument gives `U_T(rival) ≤ U_T(LP) + (α/(1 − αβ))βᵀ` for every `T`, so log utility being
  unbounded below needs no summability of the rival. The book checks only the Euler equation.
* **Bellman verification**: `V(K, s) = (α/(1 − αβ)) log K + b(s)`, with the intercept `b` the
  fixed point of a contraction (Banach), satisfies the Bellman equation with the Long–Plosser
  choice as unique maximiser, and equals the (finite) expected utility of the plan.
* Euler equation (107) at every node; uniqueness of the undetermined coefficient `ω = 1 − αβ`
  (109); transversality.
* (110)–(113) exactly (pathwise); the transitory-shock response `αʲΔ`; the conditional mean of
  log output converges to `(χ₀ + ā)/(1 − α)` (Markov shocks, given `E₀ a_T → ā`; i.i.d.
  unconditionally); forgetting of initial conditions at rate `α`; for i.i.d. shocks the
  **distribution** of log output converges (tested on Lipschitz functions) to a law independent
  of the initial state.
* Exercise 4: human wealth priced with the stochastic discount factor is `(1 − α)Y/(1 − β)` and
  `C = (1 − β)[(1 + r̃)K + H]`.
* Appendix 7B: saving `βw/(1 + β)` for any portfolio (unique optimum); zero bond holdings are
  optimal iff the riskless rate is the harmonic mean `1/E[1/(1 + r̃)]` (sufficiency and
  necessity), which is at most `E[1 + r̃]`; (140)–(143) and the isomorphism with (110).
-/

namespace ObstfeldRogoff.GlobalGrowth.BrockMirman

open Finset Filter Topology

variable {S : Type*} [Fintype S]

/-! ## Event trees over a finite Markov shock

A node of the event tree is a nonempty list of shock states, most recent first: `s :: h` is
the node whose current state is `s` and whose past is `h`. -/

/-- A Markov transition kernel on the finite shock space (O&R §7.4 uses "random" shocks; we
take a finite-state Markov chain, which includes i.i.d. shocks). -/
structure IsMarkov (P : S → S → ℝ) : Prop where
  nonneg : ∀ s s', 0 ≤ P s s'
  sum_one : ∀ s, ∑ s', P s s' = 1

/-- Conditional expectation `n` periods ahead, `E_t f(node_{t+n})`, from the node with current
state `s` and past `h` (the expectation operator `E_t` of O&R (103)). -/
noncomputable def ev (P : S → S → ℝ) (f : List S → ℝ) : ℕ → S → List S → ℝ
  | 0, s, h => f (s :: h)
  | n + 1, s, h => ∑ s', P s s' * ev P f n s' (s :: h)

/-- One-step conditional expectation of `g` at a node: `E_t g(node_{t+1})` (O&R p. 497). -/
noncomputable def nextExp (P : S → S → ℝ) (g : List S → ℝ) : List S → ℝ
  | [] => 0
  | s :: h => ∑ s', P s s' * g (s' :: s :: h)

/-- `ev` depends only on the values of `f` at nonempty lists (nodes). -/
theorem ev_congr (P : S → S → ℝ) {f g : List S → ℝ} (hfg : ∀ s h, f (s :: h) = g (s :: h))
    (n : ℕ) : ∀ s h, ev P f n s h = ev P g n s h := by
  induction n with
  | zero => intro s h; exact hfg s h
  | succ n ih => intro s h; simp only [ev, ih]

/-- Linearity of the conditional expectation: sums. -/
theorem ev_add (P : S → S → ℝ) (f g : List S → ℝ) (n : ℕ) :
    ∀ s h, ev P (fun l => f l + g l) n s h = ev P f n s h + ev P g n s h := by
  induction n with
  | zero => intro s h; rfl
  | succ n ih => intro s h; simp only [ev, ih, mul_add, Finset.sum_add_distrib]

/-- Linearity of the conditional expectation: scalar multiples. -/
theorem ev_const_mul (P : S → S → ℝ) (c : ℝ) (f : List S → ℝ) (n : ℕ) :
    ∀ s h, ev P (fun l => c * f l) n s h = c * ev P f n s h := by
  induction n with
  | zero => intro s h; rfl
  | succ n ih =>
    intro s h
    simp only [ev, ih, Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => by ring

/-- Linearity of the conditional expectation: differences. -/
theorem ev_sub (P : S → S → ℝ) (f g : List S → ℝ) (n : ℕ) (s : S) (h : List S) :
    ev P (fun l => f l - g l) n s h = ev P f n s h - ev P g n s h := by
  have h1 := ev_add P f (fun l => -1 * g l) n s h
  rw [ev_const_mul] at h1
  rw [show (fun l => f l - g l) = fun l => f l + -1 * g l by funext l; ring, h1]
  ring

/-- The conditional expectation of a constant is that constant. -/
theorem ev_const {P : S → S → ℝ} (hP : IsMarkov P) (c : ℝ) (n : ℕ) :
    ∀ s h, ev P (fun _ => c) n s h = c := by
  induction n with
  | zero => intro s h; rfl
  | succ n ih => intro s h; simp only [ev, ih, ← Finset.sum_mul, hP.sum_one, one_mul]

/-- Monotonicity of the conditional expectation (only nodes matter). -/
theorem ev_mono {P : S → S → ℝ} (hP : IsMarkov P) {f g : List S → ℝ}
    (hfg : ∀ s h, f (s :: h) ≤ g (s :: h)) (n : ℕ) : ∀ s h, ev P f n s h ≤ ev P g n s h := by
  induction n with
  | zero => intro s h; exact hfg s h
  | succ n ih =>
    intro s h
    exact Finset.sum_le_sum fun s' _ =>
      mul_le_mul_of_nonneg_left (ih s' (s :: h)) (hP.nonneg s s')

/-- **Tower property**: the expectation at date `t+n` of the one-step-ahead conditional
expectation is the expectation at date `t+n+1`. -/
theorem ev_nextExp (P : S → S → ℝ) (g : List S → ℝ) (n : ℕ) :
    ∀ s h, ev P (nextExp P g) n s h = ev P g (n + 1) s h := by
  induction n with
  | zero => intro s h; rfl
  | succ n ih => intro s h; simp only [ev, ih]

/-- A quantity known at the parent node: `E_t g(node_{t+n}) = E_t g(parent of node_{t+n+1})`. -/
theorem ev_tail {P : S → S → ℝ} (hP : IsMarkov P) (g : List S → ℝ) (n : ℕ) (s : S)
    (h : List S) : ev P (fun l => g l.tail) (n + 1) s h = ev P g n s h := by
  rw [← ev_nextExp]
  refine ev_congr P (fun s h => ?_) n s h
  simp only [nextExp, List.tail_cons, ← Finset.sum_mul, hP.sum_one, one_mul]

/-- Bounds pass through the conditional expectation. -/
theorem abs_ev_le {P : S → S → ℝ} (hP : IsMarkov P) {f : List S → ℝ} {B : ℝ}
    (hf : ∀ s h, |f (s :: h)| ≤ B) (n : ℕ) (s : S) (h : List S) : |ev P f n s h| ≤ B := by
  rw [abs_le]
  constructor
  · have := ev_mono hP (f := fun _ => -B) (g := f) (fun s h => (abs_le.1 (hf s h)).1) n s h
    rwa [ev_const hP] at this
  · have := ev_mono hP (f := f) (g := fun _ => B) (fun s h => (abs_le.1 (hf s h)).2) n s h
    rwa [ev_const hP] at this

/-- A function of the node's depth has a deterministic expectation. -/
theorem ev_length {P : S → S → ℝ} (hP : IsMarkov P) (φ : ℕ → ℝ) (n : ℕ) :
    ∀ s h, ev P (fun l => φ l.length) n s h = φ (n + h.length + 1) := by
  induction n with
  | zero => intro s h; simp [ev]
  | succ n ih =>
    intro s h
    simp only [ev, ih, List.length_cons, ← Finset.sum_mul, hP.sum_one, one_mul]
    ring_nf

/-- **Discounted telescoping bound** (the supporting-hyperplane argument over an infinite
horizon). If `d_t ≤ q_t − β r_t`, `q_{t+1} ≤ r_t`, `q_0 ≤ 0` and `r_t ≥ −c`, then
`Σ_{t<T} βᵗ d_t ≤ c βᵀ` for every horizon `T`. Used for O&R §7.3.2, §7.4.1 and §7.4.2. -/
theorem telescope_bound {β c : ℝ} (hβ : 0 ≤ β) (hc : 0 ≤ c) {d q r : ℕ → ℝ}
    (hd : ∀ t, d t ≤ q t - β * r t) (hq : ∀ t, q (t + 1) ≤ r t) (h0 : q 0 ≤ 0)
    (hr : ∀ t, -c ≤ r t) (T : ℕ) : ∑ t ∈ range T, β ^ t * d t ≤ c * β ^ T := by
  have inv : ∀ T, ∑ t ∈ range T, β ^ t * d t + β ^ T * q T ≤ 0 := by
    intro T
    induction T with
    | zero => simpa using h0
    | succ T ih =>
      rw [Finset.sum_range_succ]
      have hbT : 0 ≤ β ^ T := pow_nonneg hβ T
      have h1 := mul_le_mul_of_nonneg_left (hd T) hbT
      have h2 := mul_le_mul_of_nonneg_left (hq T) (pow_nonneg hβ (T + 1))
      have : β ^ (T + 1) = β ^ T * β := pow_succ β T
      rw [this] at h2 ⊢
      linarith
  cases T with
  | zero => simpa using hc
  | succ T =>
    rw [Finset.sum_range_succ]
    have hbT : 0 ≤ β ^ T := pow_nonneg hβ T
    have h1 := mul_le_mul_of_nonneg_left (hd T) hbT
    have h3 := mul_le_mul_of_nonneg_left (hr T) (pow_nonneg hβ (T + 1))
    have : β ^ (T + 1) = β ^ T * β := pow_succ β T
    rw [this] at h3 ⊢
    linarith [inv T]

/-! ## The model (103)–(104) on the event tree -/

/-- Parameters of O&R §7.4.1: `0 < α < 1` (Cobb–Douglas share), `0 < β < 1` (discount). -/
structure Params (α β : ℝ) : Prop where
  α_pos : 0 < α
  α_lt_one : α < 1
  β_pos : 0 < β
  β_lt_one : β < 1

/-- `αβ < 1` under the parameter restrictions. -/
theorem Params.ab_lt_one {α β : ℝ} (hp : Params α β) : α * β < 1 := by
  nlinarith [hp.α_pos, hp.α_lt_one, hp.β_pos, hp.β_lt_one]

/-- `0 < αβ` under the parameter restrictions. -/
theorem Params.ab_pos {α β : ℝ} (hp : Params α β) : 0 < α * β := mul_pos hp.α_pos hp.β_pos

/-- Capital entering the node with past `h`: `K₀` at the root, otherwise the capital `k`
chosen at the parent node (capital is chosen one period ahead, O&R (104)). -/
def capIn (K₀ : ℝ) (k : List S → ℝ) : List S → ℝ
  | [] => K₀
  | s :: h => k (s :: h)

/-- Output `Y_t = A_t K_t^α` at a node (O&R p. 497). -/
noncomputable def output (A : S → ℝ) (α K₀ : ℝ) (k : List S → ℝ) : List S → ℝ
  | [] => 0
  | s :: h => A s * capIn K₀ k h ^ α

/-- Consumption from the budget constraint (104), `C_t = A_t K_t^α − K_{t+1}`, with 100 percent
depreciation. -/
noncomputable def consumption (A : S → ℝ) (α K₀ : ℝ) (k : List S → ℝ) (l : List S) : ℝ :=
  output A α K₀ k l - k l

/-- A feasible contingent capital plan: at every history, next period's capital is positive
and consumption (104) is positive. -/
def Feasible (A : S → ℝ) (α K₀ : ℝ) (k : List S → ℝ) : Prop :=
  ∀ s h, 0 < k (s :: h) ∧ k (s :: h) < A s * capIn K₀ k h ^ α

/-- Expected discounted utility (103) up to horizon `T`, from initial capital `K₀` and initial
shock state `s₀`: `Σ_{t<T} βᵗ E₀ log C_t`. -/
noncomputable def utility (P : S → S → ℝ) (A : S → ℝ) (α β K₀ : ℝ) (k : List S → ℝ) (s₀ : S)
    (T : ℕ) : ℝ :=
  ∑ t ∈ range T, β ^ t * ev P (fun l => Real.log (consumption A α K₀ k l)) t s₀ []

/-- The Long–Plosser policy, O&R p. 499: `K_{t+1} = αβ A_t K_t^α` (the value at `[]` is the
initial capital, so that the policy also records the capital entering every node). -/
noncomputable def lpPolicy (A : S → ℝ) (α β K₀ : ℝ) : List S → ℝ
  | [] => K₀
  | s :: h => α * β * (A s * lpPolicy A α β K₀ h ^ α)

omit [Fintype S] in
/-- The capital entering any node under the Long–Plosser policy. -/
theorem capIn_lpPolicy (A : S → ℝ) (α β K₀ : ℝ) (h : List S) :
    capIn K₀ (lpPolicy A α β K₀) h = lpPolicy A α β K₀ h := by
  cases h <;> rfl

omit [Fintype S] in
/-- Long–Plosser capital is positive at every node. -/
theorem lpPolicy_pos {A : S → ℝ} {α β K₀ : ℝ} (hp : Params α β) (hA : ∀ s, 0 < A s)
    (hK : 0 < K₀) (l : List S) : 0 < lpPolicy A α β K₀ l := by
  induction l with
  | nil => exact hK
  | cons s h ih =>
    simp only [lpPolicy]
    exact mul_pos hp.ab_pos (mul_pos (hA s) (Real.rpow_pos_of_pos ih α))

omit [Fintype S] in
/-- The Long–Plosser plan is feasible. -/
theorem lpPolicy_feasible {A : S → ℝ} {α β K₀ : ℝ} (hp : Params α β) (hA : ∀ s, 0 < A s)
    (hK : 0 < K₀) : Feasible A α K₀ (lpPolicy A α β K₀) := by
  intro s h
  rw [capIn_lpPolicy]
  have hY : 0 < A s * lpPolicy A α β K₀ h ^ α :=
    mul_pos (hA s) (Real.rpow_pos_of_pos (lpPolicy_pos hp hA hK h) α)
  simp only [lpPolicy]
  exact ⟨mul_pos hp.ab_pos hY, by nlinarith [hp.ab_lt_one]⟩

omit [Fintype S] in
/-- (108)–(109): under the Long–Plosser policy consumption is `C_t = (1 − αβ) A_t K_t^α`. -/
theorem consumption_lpPolicy (A : S → ℝ) (α β K₀ : ℝ) (s : S) (h : List S) :
    consumption A α K₀ (lpPolicy A α β K₀) (s :: h) =
      (1 - α * β) * (A s * lpPolicy A α β K₀ h ^ α) := by
  simp only [consumption, output, capIn_lpPolicy, lpPolicy]
  ring

omit [Fintype S] in
/-- Positivity of Long–Plosser consumption. -/
theorem consumption_lpPolicy_pos {A : S → ℝ} {α β K₀ : ℝ} (hp : Params α β)
    (hA : ∀ s, 0 < A s) (hK : 0 < K₀) (s : S) (h : List S) :
    0 < consumption A α K₀ (lpPolicy A α β K₀) (s :: h) := by
  rw [consumption_lpPolicy]
  exact mul_pos (by linarith [hp.ab_lt_one])
    (mul_pos (hA s) (Real.rpow_pos_of_pos (lpPolicy_pos hp hA hK h) α))

omit [Fintype S] in
/-- Capital entering a node under a feasible plan is positive. -/
theorem Feasible.capIn_pos {A : S → ℝ} {α K₀ : ℝ} {k : List S → ℝ} (hk : Feasible A α K₀ k)
    (hK : 0 < K₀) (h : List S) : 0 < capIn K₀ k h := by
  cases h with
  | nil => exact hK
  | cons s h => exact (hk s h).1

omit [Fintype S] in
/-- Consumption of a feasible plan is positive. -/
theorem Feasible.consumption_pos {A : S → ℝ} {α K₀ : ℝ} {k : List S → ℝ}
    (hk : Feasible A α K₀ k) (s : S) (h : List S) : 0 < consumption A α K₀ k (s :: h) := by
  simp only [consumption, output]
  linarith [(hk s h).2]

/-! ## Optimality of the Long–Plosser policy over the infinite horizon

The book verifies only the Euler equation (107) ("the conjectured solution indeed works"). We
prove that the policy is optimal among **all** feasible contingent plans, by a stochastic
supporting-hyperplane argument. Because log utility is unbounded below, the rival's utility
need not converge; the bound is stated on partial sums. -/

/-- The coefficient `α/(1 − αβ)` on `log K` in the value function. -/
noncomputable def coefK (α β : ℝ) : ℝ := α / (1 - α * β)

/-- Positivity of `α/(1 − αβ)`. -/
theorem coefK_pos {α β : ℝ} (hp : Params α β) : 0 < coefK α β :=
  div_pos hp.α_pos (by linarith [hp.ab_lt_one])

/-- The marginal-value term at a node: `(Y_t − Y°_t)/C°_t` (rival output minus Long–Plosser
output, over Long–Plosser consumption). -/
noncomputable def gapQ (A : S → ℝ) (α β K₀ : ℝ) (k : List S → ℝ) (l : List S) : ℝ :=
  (output A α K₀ k l - output A α K₀ (lpPolicy A α β K₀) l) /
    consumption A α K₀ (lpPolicy A α β K₀) l

/-- The relative capital gap `K/K° − 1` of the capital held at a node. -/
noncomputable def gapX (A : S → ℝ) (α β K₀ : ℝ) (k : List S → ℝ) (l : List S) : ℝ :=
  capIn K₀ k l / lpPolicy A α β K₀ l - 1

/-- Concavity of `x ↦ x^α` in ratio form: `x^α ≤ y^α (1 + α(x/y − 1))`. -/
theorem rpow_le_tangent {α x y : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) (hx : 0 < x) (hy : 0 < y) :
    x ^ α ≤ y ^ α * (1 + α * (x / y - 1)) := by
  have h := rpow_one_add_le_one_add_mul_self (s := x / y - 1)
    (by have := div_pos hx hy; linarith) hα0 hα1
  have hxy : x = y * (1 + (x / y - 1)) := by field_simp; ring
  calc x ^ α = y ^ α * (1 + (x / y - 1)) ^ α := by
        rw [← Real.mul_rpow hy.le (by have := div_pos hx hy; linarith), ← hxy]
    _ ≤ y ^ α * (1 + α * (x / y - 1)) :=
        mul_le_mul_of_nonneg_left h (Real.rpow_nonneg hy.le α)

omit [Fintype S] in
/-- Node inequality 1: next period's output gain is bounded by the capital gap chosen today,
`(Y − Y°)/C° ≤ (α/(1 − αβ)) (K/K° − 1)` (concavity of `K^α`). -/
theorem gapQ_le {A : S → ℝ} {α β K₀ : ℝ} (hp : Params α β) (hA : ∀ s, 0 < A s) (hK : 0 < K₀)
    {k : List S → ℝ} (hk : Feasible A α K₀ k) (s : S) (h : List S) :
    gapQ A α β K₀ k (s :: h) ≤ coefK α β * gapX A α β K₀ k h := by
  have hx := hk.capIn_pos hK h
  have hy := lpPolicy_pos hp hA hK h
  have hC := consumption_lpPolicy_pos hp hA hK s h
  have hab := hp.ab_lt_one
  simp only [gapQ, gapX, coefK, output, capIn_lpPolicy]
  rw [consumption_lpPolicy, div_le_iff₀ (by rw [← consumption_lpPolicy]; exact hC)]
  have ht := rpow_le_tangent hp.α_pos.le hp.α_lt_one.le hx hy
  have hAs := hA s
  have hyα := Real.rpow_pos_of_pos hy α
  have e : α / (1 - α * β) * (capIn K₀ k h / lpPolicy A α β K₀ h - 1) *
      ((1 - α * β) * (A s * lpPolicy A α β K₀ h ^ α)) =
      A s * (lpPolicy A α β K₀ h ^ α * (α * (capIn K₀ k h / lpPolicy A α β K₀ h - 1))) := by
    have h1 : (1 - α * β) ≠ 0 := by linarith
    field_simp
  rw [e]
  nlinarith [mul_le_mul_of_nonneg_left ht hAs.le]

omit [Fintype S] in
/-- Node inequality 2: the log-utility gain at a node is bounded by the supporting hyperplane,
`log C − log C° ≤ (Y − Y°)/C° − β (α/(1 − αβ)) (K′/K°′ − 1)`. -/
theorem log_consumption_sub_le {A : S → ℝ} {α β K₀ : ℝ} (hp : Params α β) (hA : ∀ s, 0 < A s)
    (hK : 0 < K₀) {k : List S → ℝ} (hk : Feasible A α K₀ k) (s : S) (h : List S) :
    Real.log (consumption A α K₀ k (s :: h)) -
        Real.log (consumption A α K₀ (lpPolicy A α β K₀) (s :: h)) ≤
      gapQ A α β K₀ k (s :: h) - β * (coefK α β * gapX A α β K₀ k (s :: h)) := by
  have hC := hk.consumption_pos s h
  have hC0 := consumption_lpPolicy_pos hp hA hK s h
  have hy := lpPolicy_pos hp hA hK h
  have hab := hp.ab_lt_one
  rw [← Real.log_div hC.ne' hC0.ne']
  refine (Real.log_le_sub_one_of_pos (div_pos hC hC0)).trans (le_of_eq ?_)
  have e1 : consumption A α K₀ k (s :: h) = A s * capIn K₀ k h ^ α - k (s :: h) := rfl
  have e2 : gapQ A α β K₀ k (s :: h) = (A s * capIn K₀ k h ^ α - A s * lpPolicy A α β K₀ h ^ α)
      / ((1 - α * β) * (A s * lpPolicy A α β K₀ h ^ α)) := by
    simp only [gapQ, output, capIn_lpPolicy]
    rw [consumption_lpPolicy]
  have e3 : gapX A α β K₀ k (s :: h) =
      k (s :: h) / (α * β * (A s * lpPolicy A α β K₀ h ^ α)) - 1 := rfl
  rw [e1, e2, e3, consumption_lpPolicy, coefK]
  have h1 : (1 - α * β) ≠ 0 := by linarith
  have h2 : A s * lpPolicy A α β K₀ h ^ α ≠ 0 :=
    (mul_pos (hA s) (Real.rpow_pos_of_pos hy α)).ne'
  have h3 : α ≠ 0 := hp.α_pos.ne'
  have h4 : β ≠ 0 := hp.β_pos.ne'
  have h5 : A s ≠ 0 := (hA s).ne'
  field_simp
  ring

/-- **Optimality of the Long–Plosser policy, finite-horizon form** (O&R (108)–(109), p. 499,
made rigorous). For every feasible contingent plan `k` and every horizon `T`,
`Σ_{t<T} βᵗ E₀ log C_t ≤ Σ_{t<T} βᵗ E₀ log C°_t + (α/(1 − αβ)) βᵀ`, where `C°` is Long–Plosser
consumption. The shock is an arbitrary finite-state Markov chain. -/
theorem utility_le_lp_add {P : S → S → ℝ} (hP : IsMarkov P) {A : S → ℝ} {α β K₀ : ℝ}
    (hp : Params α β) (hA : ∀ s, 0 < A s) (hK : 0 < K₀) {k : List S → ℝ}
    (hk : Feasible A α K₀ k) (s₀ : S) (T : ℕ) :
    utility P A α β K₀ k s₀ T ≤
      utility P A α β K₀ (lpPolicy A α β K₀) s₀ T + coefK α β * β ^ T := by
  set lp := lpPolicy A α β K₀
  set d : ℕ → ℝ := fun t => ev P (fun l => Real.log (consumption A α K₀ k l) -
    Real.log (consumption A α K₀ lp l)) t s₀ []
  set q : ℕ → ℝ := fun t => ev P (gapQ A α β K₀ k) t s₀ []
  set r : ℕ → ℝ := fun t => ev P (fun l => coefK α β * gapX A α β K₀ k l) t s₀ []
  have ha := coefK_pos hp
  have key := telescope_bound (d := d) (q := q) (r := r) hp.β_pos.le ha.le
    (fun t => by
      simp only [d, q, r]
      rw [← ev_const_mul, ← ev_sub]
      exact ev_mono hP (fun s h => log_consumption_sub_le hp hA hK hk s h) t s₀ [])
    (fun t => by
      simp only [q, r]
      exact (ev_mono hP (f := gapQ A α β K₀ k)
        (g := fun l => coefK α β * gapX A α β K₀ k l.tail)
        (fun s h => gapQ_le hp hA hK hk s h) (t + 1) s₀ []).trans_eq
        (ev_tail hP (fun l => coefK α β * gapX A α β K₀ k l) t s₀ []))
    (by
      simp [q, ev, gapQ, output, capIn])
    (fun t => by
      simp only [r]
      have := ev_mono hP (f := fun _ => -coefK α β)
        (g := fun l => coefK α β * gapX A α β K₀ k l) (fun s h => by
          have hx := hk.capIn_pos hK (s :: h)
          have hy := lpPolicy_pos hp hA hK (s :: h)
          simp only [gapX]
          have : 0 < capIn K₀ k (s :: h) / lpPolicy A α β K₀ (s :: h) := div_pos hx hy
          nlinarith) t s₀ []
      rwa [ev_const hP] at this)
    T
  have hsum : ∑ t ∈ range T, β ^ t * d t =
      utility P A α β K₀ k s₀ T - utility P A α β K₀ lp s₀ T := by
    simp only [d, utility, ← Finset.sum_sub_distrib, ← mul_sub]
    exact Finset.sum_congr rfl fun t _ => by rw [ev_sub]
  linarith

/-! ## The value function and Bellman verification -/

/-- The state-dependent constant in the Bellman equation,
`c(s) = log(1 − αβ) + (αβ/(1 − αβ)) log(αβ) + log A(s)/(1 − αβ)`. -/
noncomputable def bellmanConst (A : S → ℝ) (α β : ℝ) (s : S) : ℝ :=
  Real.log (1 - α * β) + α * β / (1 - α * β) * Real.log (α * β) + Real.log (A s) / (1 - α * β)

/-- The Bellman operator on the shock-dependent intercept, `(Tb)(s) = c(s) + β Σ P(s,s') b(s')`. -/
noncomputable def interceptMap (P : S → S → ℝ) (A : S → ℝ) (α β : ℝ) (b : S → ℝ) : S → ℝ :=
  fun s => bellmanConst A α β s + β * ∑ s', P s s' * b s'

/-- The intercept map is a contraction with modulus `β` in the sup metric. -/
theorem interceptMap_contracting {P : S → S → ℝ} (hP : IsMarkov P) (A : S → ℝ) {α β : ℝ}
    (hp : Params α β) :
    ContractingWith ⟨β, hp.β_pos.le⟩ (interceptMap P A α β) := by
  refine ⟨by exact_mod_cast hp.β_lt_one, LipschitzWith.of_dist_le_mul fun b b' => ?_⟩
  have hd : 0 ≤ β * dist b b' := mul_nonneg hp.β_pos.le dist_nonneg
  refine (dist_pi_le_iff hd).2 fun s => ?_
  simp only [interceptMap, Real.dist_eq]
  have e : bellmanConst A α β s + β * ∑ s', P s s' * b s' -
      (bellmanConst A α β s + β * ∑ s', P s s' * b' s') =
      β * ∑ s', P s s' * (b s' - b' s') := by
    simp only [mul_sub, Finset.sum_sub_distrib]; ring
  rw [e, abs_mul, abs_of_pos hp.β_pos]
  refine mul_le_mul_of_nonneg_left ?_ hp.β_pos.le
  calc |∑ s', P s s' * (b s' - b' s')| ≤ ∑ s', |P s s' * (b s' - b' s')| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s', P s s' * dist b b' := Finset.sum_le_sum fun s' _ => by
        rw [abs_mul, abs_of_nonneg (hP.nonneg s s')]
        refine mul_le_mul_of_nonneg_left ?_ (hP.nonneg s s')
        rw [← Real.dist_eq]
        exact dist_le_pi_dist b b' s'
    _ = dist b b' := by rw [← Finset.sum_mul, hP.sum_one, one_mul]

/-- The intercept `b` of the value function: the unique fixed point of the Bellman intercept
map (Banach's fixed-point theorem on the finite-dimensional space `S → ℝ`). -/
noncomputable def intercept {P : S → S → ℝ} (hP : IsMarkov P) (A : S → ℝ) {α β : ℝ}
    (hp : Params α β) : S → ℝ :=
  ContractingWith.fixedPoint (interceptMap P A α β) (interceptMap_contracting hP A hp)

/-- The intercept solves `b(s) = c(s) + β Σ P(s,s') b(s')`. -/
theorem intercept_spec {P : S → S → ℝ} (hP : IsMarkov P) (A : S → ℝ) {α β : ℝ}
    (hp : Params α β) (s : S) :
    intercept hP A hp s = bellmanConst A α β s + β * ∑ s', P s s' * intercept hP A hp s' := by
  have := ContractingWith.fixedPoint_isFixedPt (f := interceptMap P A α β)
    (interceptMap_contracting hP A hp)
  exact (congrFun this s).symm

/-- The value function of the Brock–Mirman problem, `V(K, s) = (α/(1 − αβ)) log K + b(s)`
(O&R p. 498 and Supplement A to Ch. 2). -/
noncomputable def value {P : S → S → ℝ} (hP : IsMarkov P) (A : S → ℝ) {α β : ℝ}
    (hp : Params α β) (K : ℝ) (s : S) : ℝ :=
  coefK α β * Real.log K + intercept hP A hp s

/-- **Bellman inequality**: for every feasible choice `0 < K′ < A(s)K^α`,
`log(A(s)K^α − K′) + β E_s V(K′, s′) ≤ V(K, s)`. -/
theorem bellman_le {P : S → S → ℝ} (hP : IsMarkov P) {A : S → ℝ} {α β : ℝ} (hp : Params α β)
    (hA : ∀ s, 0 < A s) {K k' : ℝ} (hK : 0 < K) (s : S) (hk0 : 0 < k')
    (hk1 : k' < A s * K ^ α) :
    Real.log (A s * K ^ α - k') + β * ∑ s', P s s' * value hP A hp k' s' ≤ value hP A hp K s := by
  set Y := A s * K ^ α with hYdef
  have hY : 0 < Y := mul_pos (hA s) (Real.rpow_pos_of_pos hK α)
  have hab := hp.ab_lt_one
  have hab0 := hp.ab_pos
  have hc : 0 < (1 - α * β) * Y := mul_pos (by linarith) hY
  have hkk : 0 < α * β * Y := mul_pos hab0 hY
  have l1 := Real.log_le_sub_one_of_pos (div_pos (sub_pos.2 hk1) hc)
  have l2 := Real.log_le_sub_one_of_pos (div_pos hk0 hkk)
  rw [Real.log_div (sub_pos.2 hk1).ne' hc.ne'] at l1
  rw [Real.log_div hk0.ne' hkk.ne'] at l2
  have hsum : ∑ s', P s s' * value hP A hp k' s' =
      coefK α β * Real.log k' + ∑ s', P s s' * intercept hP A hp s' := by
    simp only [value, mul_add, Finset.sum_add_distrib]
    rw [← Finset.sum_mul, hP.sum_one, one_mul]
  rw [hsum]
  have hv : value hP A hp K s = coefK α β * Real.log K + bellmanConst A α β s +
      β * ∑ s', P s s' * intercept hP A hp s' := by
    rw [value, intercept_spec hP A hp s]; ring
  rw [hv]
  have hlogY : Real.log Y = Real.log (A s) + α * Real.log K := by
    rw [hYdef, Real.log_mul (hA s).ne' (Real.rpow_pos_of_pos hK α).ne', Real.log_rpow hK]
  have hl1 : Real.log ((1 - α * β) * Y) = Real.log (1 - α * β) + Real.log Y :=
    Real.log_mul (by linarith) hY.ne'
  have hl2 : Real.log (α * β * Y) = Real.log (α * β) + Real.log Y :=
    Real.log_mul hab0.ne' hY.ne'
  rw [hl1] at l1
  rw [hl2] at l2
  have hβa : β * coefK α β = α * β / (1 - α * β) := by rw [coefK]; ring
  have hβa0 : 0 ≤ β * coefK α β := mul_nonneg hp.β_pos.le (coefK_pos hp).le
  have l2' := mul_le_mul_of_nonneg_left l2 hβa0
  have lin : (Y - k') / ((1 - α * β) * Y) - 1 + β * coefK α β * (k' / (α * β * Y) - 1) = 0 := by
    rw [hβa]
    have h1 : (1 - α * β) ≠ 0 := by linarith
    have h3 : α ≠ 0 := hp.α_pos.ne'
    have h4 : β ≠ 0 := hp.β_pos.ne'
    field_simp
    ring
  have key : Real.log (Y - k') + β * (coefK α β * Real.log k') ≤
      Real.log (1 - α * β) + Real.log Y + β * coefK α β * (Real.log (α * β) + Real.log Y) := by
    linarith
  have hfin : Real.log (1 - α * β) + Real.log Y +
      β * coefK α β * (Real.log (α * β) + Real.log Y) =
      coefK α β * Real.log K + bellmanConst A α β s := by
    rw [hlogY, hβa]
    simp only [bellmanConst, coefK]
    have h1 : (1 - α * β) ≠ 0 := by linarith
    field_simp
    ring
  linarith

/-- **Bellman equation** (the argmax): the Long–Plosser choice `K′ = αβ A(s) K^α` attains the
Bellman inequality with equality. -/
theorem bellman_eq {P : S → S → ℝ} (hP : IsMarkov P) {A : S → ℝ} {α β : ℝ} (hp : Params α β)
    (hA : ∀ s, 0 < A s) {K : ℝ} (hK : 0 < K) (s : S) :
    Real.log (A s * K ^ α - α * β * (A s * K ^ α)) +
        β * ∑ s', P s s' * value hP A hp (α * β * (A s * K ^ α)) s' = value hP A hp K s := by
  set Y := A s * K ^ α with hYdef
  have hY : 0 < Y := mul_pos (hA s) (Real.rpow_pos_of_pos hK α)
  have hab := hp.ab_lt_one
  have hab0 := hp.ab_pos
  have hsum : ∑ s', P s s' * value hP A hp (α * β * Y) s' =
      coefK α β * Real.log (α * β * Y) + ∑ s', P s s' * intercept hP A hp s' := by
    simp only [value, mul_add, Finset.sum_add_distrib]
    rw [← Finset.sum_mul, hP.sum_one, one_mul]
  rw [hsum, value, intercept_spec hP A hp s, show Y - α * β * Y = (1 - α * β) * Y by ring,
    Real.log_mul (by linarith) hY.ne', Real.log_mul hab0.ne' hY.ne', hYdef,
    Real.log_mul (hA s).ne' (Real.rpow_pos_of_pos hK α).ne', Real.log_rpow hK]
  simp only [bellmanConst, coefK]
  have h1 : (1 - α * β) ≠ 0 := by linarith
  field_simp
  ring

/-- The Long–Plosser choice is the **unique** maximiser in the Bellman equation. -/
theorem bellman_lt {P : S → S → ℝ} (hP : IsMarkov P) {A : S → ℝ} {α β : ℝ} (hp : Params α β)
    (hA : ∀ s, 0 < A s) {K k' : ℝ} (hK : 0 < K) (s : S) (hk0 : 0 < k')
    (hk1 : k' < A s * K ^ α) (hne : k' ≠ α * β * (A s * K ^ α)) :
    Real.log (A s * K ^ α - k') + β * ∑ s', P s s' * value hP A hp k' s' < value hP A hp K s := by
  set Y := A s * K ^ α with hYdef
  have hY : 0 < Y := mul_pos (hA s) (Real.rpow_pos_of_pos hK α)
  have hab := hp.ab_lt_one
  have hab0 := hp.ab_pos
  have hkk : 0 < α * β * Y := mul_pos hab0 hY
  -- strict concavity of `log k'` gives the strict inequality
  have l2 := Real.log_lt_sub_one_of_pos (div_pos hk0 hkk)
    (by
      intro h
      exact hne (by rw [div_eq_one_iff_eq hkk.ne'] at h; exact h))
  rw [Real.log_div hk0.ne' hkk.ne'] at l2
  have hc : 0 < (1 - α * β) * Y := mul_pos (by linarith) hY
  have l1 := Real.log_le_sub_one_of_pos (div_pos (sub_pos.2 hk1) hc)
  rw [Real.log_div (sub_pos.2 hk1).ne' hc.ne'] at l1
  have heq := bellman_eq hP hp hA hK s
  rw [← hYdef] at heq
  have hsum : ∀ x, ∑ s', P s s' * value hP A hp x s' =
      coefK α β * Real.log x + ∑ s', P s s' * intercept hP A hp s' := fun x => by
    simp only [value, mul_add, Finset.sum_add_distrib]
    rw [← Finset.sum_mul, hP.sum_one, one_mul]
  rw [hsum] at heq ⊢
  rw [← heq, show Y - α * β * Y = (1 - α * β) * Y by ring]
  have hβa : β * coefK α β = α * β / (1 - α * β) := by rw [coefK]; ring
  have hβa0 : 0 < β * coefK α β := mul_pos hp.β_pos (coefK_pos hp)
  have l2' := mul_lt_mul_of_pos_left l2 hβa0
  have lin : (Y - k') / ((1 - α * β) * Y) - 1 + β * coefK α β * (k' / (α * β * Y) - 1) = 0 := by
    rw [hβa]
    have h1 : (1 - α * β) ≠ 0 := by linarith
    have h3 : α ≠ 0 := hp.α_pos.ne'
    have h4 : β ≠ 0 := hp.β_pos.ne'
    field_simp
    ring
  nlinarith

/-- The value along the Long–Plosser plan at a node: `V(K_t, s_t)` with `K_t` the capital
entering the node. -/
noncomputable def valueNode {P : S → S → ℝ} (hP : IsMarkov P) (A : S → ℝ) {α β : ℝ}
    (hp : Params α β) (K₀ : ℝ) : List S → ℝ
  | [] => 0
  | s :: h => value hP A hp (lpPolicy A α β K₀ h) s

/-- Uniform bound on `log K_t` along the Long–Plosser plan (the log-AR(1) structure is stable
since `α < 1`). -/
theorem abs_log_lpPolicy_le {A : S → ℝ} {α β K₀ : ℝ} (hp : Params α β) (hA : ∀ s, 0 < A s)
    (hK : 0 < K₀) (l : List S) :
    |Real.log (lpPolicy A α β K₀ l)| ≤
      |Real.log K₀| + (|Real.log (α * β)| + ∑ s, |Real.log (A s)|) / (1 - α) := by
  have h1α : 0 < 1 - α := by linarith [hp.α_lt_one]
  set B := (|Real.log (α * β)| + ∑ s, |Real.log (A s)|) / (1 - α) with hB
  have hB0 : 0 ≤ B := div_nonneg (add_nonneg (abs_nonneg _)
    (Finset.sum_nonneg fun _ _ => abs_nonneg _)) h1α.le
  induction l with
  | nil => simp only [lpPolicy]; linarith
  | cons s h ih =>
    have hy := lpPolicy_pos hp hA hK h
    simp only [lpPolicy]
    rw [Real.log_mul hp.ab_pos.ne' (mul_pos (hA s) (Real.rpow_pos_of_pos hy α)).ne',
      Real.log_mul (hA s).ne' (Real.rpow_pos_of_pos hy α).ne', Real.log_rpow hy]
    have hs : |Real.log (A s)| ≤ ∑ s, |Real.log (A s)| :=
      Finset.single_le_sum (f := fun s => |Real.log (A s)|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ s)
    have hαB : (1 - α) * B = |Real.log (α * β)| + ∑ s, |Real.log (A s)| := by
      rw [hB]; field_simp
    calc |Real.log (α * β) + (Real.log (A s) + α * Real.log (lpPolicy A α β K₀ h))|
        ≤ |Real.log (α * β)| + (|Real.log (A s)| + α * |Real.log (lpPolicy A α β K₀ h)|) := by
          refine (abs_add_le _ _).trans (add_le_add le_rfl ((abs_add_le _ _).trans ?_))
          rw [abs_mul, abs_of_pos hp.α_pos]
      _ ≤ |Real.log K₀| + B := by
          have := mul_le_mul_of_nonneg_left ih hp.α_pos.le
          nlinarith [abs_nonneg (Real.log K₀)]

/-- The Bellman equation along the Long–Plosser plan at a node:
`log C°_t + β E_t V(K_{t+1}, s_{t+1}) = V(K_t, s_t)`. -/
theorem bellman_node {P : S → S → ℝ} (hP : IsMarkov P) {A : S → ℝ} {α β K₀ : ℝ}
    (hp : Params α β) (hA : ∀ s, 0 < A s) (hK : 0 < K₀) (s : S) (h : List S) :
    Real.log (consumption A α K₀ (lpPolicy A α β K₀) (s :: h)) +
        β * nextExp P (valueNode hP A hp K₀) (s :: h) = valueNode hP A hp K₀ (s :: h) := by
  have := bellman_eq hP hp hA (lpPolicy_pos hp hA hK h) s
  rw [consumption_lpPolicy, show (1 - α * β) * (A s * lpPolicy A α β K₀ h ^ α) =
    A s * lpPolicy A α β K₀ h ^ α - α * β * (A s * lpPolicy A α β K₀ h ^ α) by ring]
  simpa [nextExp, valueNode, lpPolicy] using this

/-- Expected Bellman equation at date `t`. -/
theorem ev_bellman {P : S → S → ℝ} (hP : IsMarkov P) {A : S → ℝ} {α β K₀ : ℝ}
    (hp : Params α β) (hA : ∀ s, 0 < A s) (hK : 0 < K₀) (s₀ : S) (t : ℕ) :
    ev P (fun l => Real.log (consumption A α K₀ (lpPolicy A α β K₀) l)) t s₀ [] +
        β * ev P (valueNode hP A hp K₀) (t + 1) s₀ [] = ev P (valueNode hP A hp K₀) t s₀ [] := by
  rw [← ev_nextExp, ← ev_const_mul, ← ev_add]
  exact ev_congr P (fun s h => bellman_node hP hp hA hK s h) t s₀ []

/-- Telescoped Bellman equation: `Σ_{t<T} βᵗ E₀ log C°_t + βᵀ E₀ V(K_T, s_T) = V(K₀, s₀)`. -/
theorem utility_lp_add_tail {P : S → S → ℝ} (hP : IsMarkov P) {A : S → ℝ} {α β K₀ : ℝ}
    (hp : Params α β) (hA : ∀ s, 0 < A s) (hK : 0 < K₀) (s₀ : S) (T : ℕ) :
    utility P A α β K₀ (lpPolicy A α β K₀) s₀ T +
        β ^ T * ev P (valueNode hP A hp K₀) T s₀ [] = value hP A hp K₀ s₀ := by
  induction T with
  | zero => simp [utility, ev, valueNode, lpPolicy]
  | succ T ih =>
    have e := ev_bellman hP hp hA hK s₀ T
    simp only [utility, Finset.sum_range_succ] at ih ⊢
    rw [← ih, ← e, pow_succ]
    ring

/-- Uniform bound on the value along the Long–Plosser plan. -/
theorem abs_valueNode_le {P : S → S → ℝ} (hP : IsMarkov P) {A : S → ℝ} {α β K₀ : ℝ}
    (hp : Params α β) (hA : ∀ s, 0 < A s) (hK : 0 < K₀) (s : S) (h : List S) :
    |valueNode hP A hp K₀ (s :: h)| ≤ coefK α β * (|Real.log K₀| +
      (|Real.log (α * β)| + ∑ s, |Real.log (A s)|) / (1 - α)) +
      ∑ s, |intercept hP A hp s| := by
  simp only [valueNode, value]
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · rw [abs_mul, abs_of_pos (coefK_pos hp)]
    exact mul_le_mul_of_nonneg_left (abs_log_lpPolicy_le hp hA hK h) (coefK_pos hp).le
  · exact Finset.single_le_sum (f := fun s => |intercept hP A hp s|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ s)

/-- The discounted tail value vanishes: `βᵀ E₀ V(K_T, s_T) → 0` along the Long–Plosser plan. -/
theorem tail_value_tendsto_zero {P : S → S → ℝ} (hP : IsMarkov P) {A : S → ℝ} {α β K₀ : ℝ}
    (hp : Params α β) (hA : ∀ s, 0 < A s) (hK : 0 < K₀) (s₀ : S) :
    Tendsto (fun T => β ^ T * ev P (valueNode hP A hp K₀) T s₀ []) atTop (𝓝 0) := by
  set B := coefK α β * (|Real.log K₀| + (|Real.log (α * β)| + ∑ s, |Real.log (A s)|) /
    (1 - α)) + ∑ s, |intercept hP A hp s|
  have hb : ∀ T, |ev P (valueNode hP A hp K₀) T s₀ []| ≤ B := fun T =>
    abs_ev_le hP (fun s h => abs_valueNode_le hP hp hA hK s h) T s₀ []
  have hg := tendsto_pow_atTop_nhds_zero_of_lt_one hp.β_pos.le hp.β_lt_one
  refine squeeze_zero_norm (fun T => ?_) (by simpa using hg.mul_const B)
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos hp.β_pos T)]
  exact mul_le_mul_of_nonneg_left (hb T) (pow_pos hp.β_pos T).le

/-- The Long–Plosser plan's partial utilities converge to `V(K₀, s₀)`. -/
theorem utility_lp_tendsto {P : S → S → ℝ} (hP : IsMarkov P) {A : S → ℝ} {α β K₀ : ℝ}
    (hp : Params α β) (hA : ∀ s, 0 < A s) (hK : 0 < K₀) (s₀ : S) :
    Tendsto (utility P A α β K₀ (lpPolicy A α β K₀) s₀) atTop (𝓝 (value hP A hp K₀ s₀)) := by
  have h := (tail_value_tendsto_zero hP hp hA hK s₀).const_sub (value hP A hp K₀ s₀)
  rw [sub_zero] at h
  refine h.congr fun T => ?_
  have := utility_lp_add_tail hP hp hA hK s₀ T
  linarith

/-- The Long–Plosser plan's expected utility (103) is a genuine (absolutely convergent)
infinite sum equal to `V(K₀, s₀)`. -/
theorem hasSum_lp {P : S → S → ℝ} (hP : IsMarkov P) {A : S → ℝ} {α β K₀ : ℝ}
    (hp : Params α β) (hA : ∀ s, 0 < A s) (hK : 0 < K₀) (s₀ : S) :
    HasSum (fun t => β ^ t *
      ev P (fun l => Real.log (consumption A α K₀ (lpPolicy A α β K₀) l)) t s₀ [])
      (value hP A hp K₀ s₀) := by
  set M := |Real.log K₀| + (|Real.log (α * β)| + ∑ s, |Real.log (A s)|) / (1 - α)
  set B := |Real.log (1 - α * β)| + ∑ s, |Real.log (A s)| + α * M
  have hab := hp.ab_lt_one
  have hnode : ∀ s h, |Real.log (consumption A α K₀ (lpPolicy A α β K₀) (s :: h))| ≤ B := by
    intro s h
    have hy := lpPolicy_pos hp hA hK h
    rw [consumption_lpPolicy, Real.log_mul (by linarith)
      (mul_pos (hA s) (Real.rpow_pos_of_pos hy α)).ne',
      Real.log_mul (hA s).ne' (Real.rpow_pos_of_pos hy α).ne', Real.log_rpow hy]
    have hs : |Real.log (A s)| ≤ ∑ s, |Real.log (A s)| :=
      Finset.single_le_sum (f := fun s => |Real.log (A s)|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ s)
    have hm := mul_le_mul_of_nonneg_left (abs_log_lpPolicy_le hp hA hK h) hp.α_pos.le
    calc _ ≤ |Real.log (1 - α * β)| + (|Real.log (A s)| +
          |α * Real.log (lpPolicy A α β K₀ h)|) :=
          (abs_add_le _ _).trans (add_le_add le_rfl (abs_add_le _ _))
      _ ≤ B := by rw [abs_mul, abs_of_pos hp.α_pos]; linarith
  have hsum : Summable (fun t => β ^ t *
      ev P (fun l => Real.log (consumption A α K₀ (lpPolicy A α β K₀) l)) t s₀ []) := by
    refine Summable.of_norm_bounded
      ((summable_geometric_of_lt_one hp.β_pos.le hp.β_lt_one).mul_right B) fun t => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos hp.β_pos t)]
    exact mul_le_mul_of_nonneg_left (abs_ev_le hP hnode t s₀ []) (pow_pos hp.β_pos t).le
  exact (hsum.hasSum_iff_tendsto_nat).2 (utility_lp_tendsto hP hp hA hK s₀)

/-- **Optimality over the infinite horizon** (O&R pp. 498–499, made rigorous): for every
feasible contingent plan and every `ε > 0`, eventually `Σ_{t<T} βᵗ E₀ log C_t ≤ V(K₀, s₀) + ε`,
where `V(K₀, s₀)` is the Long–Plosser plan's expected utility. No summability of the rival is
needed (the transversality term is `(α/(1 − αβ)) βᵀ`). -/
theorem utility_eventually_le {P : S → S → ℝ} (hP : IsMarkov P) {A : S → ℝ} {α β K₀ : ℝ}
    (hp : Params α β) (hA : ∀ s, 0 < A s) (hK : 0 < K₀) {k : List S → ℝ}
    (hk : Feasible A α K₀ k) (s₀ : S) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T in atTop, utility P A α β K₀ k s₀ T ≤ value hP A hp K₀ s₀ + ε := by
  have h1 := utility_lp_tendsto hP hp hA hK s₀
  have h2 := (tendsto_pow_atTop_nhds_zero_of_lt_one hp.β_pos.le hp.β_lt_one).const_mul
    (coefK α β)
  rw [mul_zero] at h2
  have h3 := h1.add h2
  rw [add_zero] at h3
  filter_upwards [h3.eventually (gt_mem_nhds (lt_add_of_pos_right _ hε))] with T hT
  linarith [utility_le_lp_add hP hp hA hK hk s₀ T]

/-- If a feasible plan's expected utility converges, it is at most the Long–Plosser value. -/
theorem tsum_le_value {P : S → S → ℝ} (hP : IsMarkov P) {A : S → ℝ} {α β K₀ : ℝ}
    (hp : Params α β) (hA : ∀ s, 0 < A s) (hK : 0 < K₀) {k : List S → ℝ}
    (hk : Feasible A α K₀ k) (s₀ : S)
    (hs : Summable (fun t => β ^ t *
      ev P (fun l => Real.log (consumption A α K₀ k l)) t s₀ [])) :
    ∑' t, β ^ t * ev P (fun l => Real.log (consumption A α K₀ k l)) t s₀ [] ≤
      value hP A hp K₀ s₀ := by
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hlim := hs.hasSum.tendsto_sum_nat
  refine le_of_tendsto hlim ?_
  filter_upwards [utility_eventually_le hP hp hA hK hk s₀ hε] with T hT
  exact hT

/-- The value `V(K₀, s₀)` is the maximal expected utility, attained by the Long–Plosser plan. -/
theorem tsum_lp_eq_value {P : S → S → ℝ} (hP : IsMarkov P) {A : S → ℝ} {α β K₀ : ℝ}
    (hp : Params α β) (hA : ∀ s, 0 < A s) (hK : 0 < K₀) (s₀ : S) :
    ∑' t, β ^ t * ev P (fun l => Real.log (consumption A α K₀ (lpPolicy A α β K₀) l)) t s₀ [] =
      value hP A hp K₀ s₀ :=
  (hasSum_lp hP hp hA hK s₀).tsum_eq

/-! ## Euler equation, transversality and the undetermined coefficient -/

/-- The gross return on capital, `1 + r̃_{t+1} = α A_{t+1} K_{t+1}^{α−1}` (O&R (106)). -/
noncomputable def grossReturn (α a K : ℝ) : ℝ := α * a * K ^ (α - 1)

/-- (106): the gross return is the marginal product of capital, `∂(A K^α)/∂K`. -/
theorem hasDerivAt_output_grossReturn {α a K : ℝ} (hK : 0 < K) :
    HasDerivAt (fun x => a * x ^ α) (grossReturn α a K) K := by
  have := (Real.hasDerivAt_rpow_const (p := α) (Or.inl hK.ne')).const_mul a
  simpa [grossReturn, mul_comm, mul_left_comm, mul_assoc] using this

/-- **Euler equation (105)/(107)** along the Long–Plosser plan at every node, for any
finite-state Markov shock: `1/C_t = β E_t[(1 + r̃_{t+1})/C_{t+1}]`. -/
theorem euler_lp {P : S → S → ℝ} (hP : IsMarkov P) {A : S → ℝ} {α β K₀ : ℝ}
    (hp : Params α β) (hA : ∀ s, 0 < A s) (hK : 0 < K₀) (s : S) (h : List S) :
    1 / consumption A α K₀ (lpPolicy A α β K₀) (s :: h) =
      β * ∑ s', P s s' * (grossReturn α (A s') (lpPolicy A α β K₀ (s :: h)) /
        consumption A α K₀ (lpPolicy A α β K₀) (s' :: s :: h)) := by
  have hk := lpPolicy_pos hp hA hK (s :: h)
  have hab := hp.ab_lt_one
  have hterm : ∀ s', grossReturn α (A s') (lpPolicy A α β K₀ (s :: h)) /
      consumption A α K₀ (lpPolicy A α β K₀) (s' :: s :: h) =
      α / ((1 - α * β) * lpPolicy A α β K₀ (s :: h)) := by
    intro s'
    rw [consumption_lpPolicy, grossReturn, Real.rpow_sub_one hk.ne']
    have h1 : (1 - α * β) ≠ 0 := by linarith
    have h2 := (hA s').ne'
    have h3 := (Real.rpow_pos_of_pos hk α).ne'
    field_simp
  simp only [hterm, ← Finset.sum_mul, hP.sum_one, one_mul]
  rw [consumption_lpPolicy]
  conv_rhs => rw [show lpPolicy A α β K₀ (s :: h) =
    α * β * (A s * lpPolicy A α β K₀ h ^ α) from rfl]
  have h1 : (1 - α * β) ≠ 0 := by linarith
  have h2 := (hA s).ne'
  have h3 := (Real.rpow_pos_of_pos (lpPolicy_pos hp hA hK h) α).ne'
  have h4 := hp.α_pos.ne'
  have h5 := hp.β_pos.ne'
  field_simp

/-- **(108)–(109), uniqueness of the undetermined coefficient.** If a constant consumption share
`C = ωY` (with `0 < ω < 1`, hence `K′ = (1 − ω)Y`) is used at a node and at all its successors,
the Euler equation (107) holds at the node if and only if `ω = 1 − αβ`. -/
theorem euler_share_iff {P : S → S → ℝ} (hP : IsMarkov P) {A : S → ℝ} {α β ω Y : ℝ}
    (hp : Params α β) (hA : ∀ s, 0 < A s) (s : S) (hω0 : 0 < ω) (hω1 : ω < 1) (hY : 0 < Y) :
    1 / (ω * Y) = β * ∑ s', P s s' * (grossReturn α (A s') ((1 - ω) * Y) /
        (ω * (A s' * ((1 - ω) * Y) ^ α))) ↔ ω = 1 - α * β := by
  have hk : 0 < (1 - ω) * Y := mul_pos (by linarith) hY
  have hterm : ∀ s', grossReturn α (A s') ((1 - ω) * Y) / (ω * (A s' * ((1 - ω) * Y) ^ α)) =
      α / (ω * ((1 - ω) * Y)) := by
    intro s'
    rw [grossReturn, Real.rpow_sub_one hk.ne']
    have h2 := (hA s').ne'
    have h3 := (Real.rpow_pos_of_pos hk α).ne'
    field_simp
  simp only [hterm, ← Finset.sum_mul, hP.sum_one, one_mul]
  have h1 : (1 - ω) ≠ 0 := by linarith
  constructor
  · intro h
    field_simp at h
    nlinarith [hω0, hY]
  · intro h
    subst h
    have h4 := hp.α_pos.ne'
    have h5 := hp.β_pos.ne'
    field_simp
    ring

/-- **Transversality** along the Long–Plosser plan: `βᵀ E₀[u′(C_T) K_{T+1}] = βᵀ αβ/(1 − αβ)`,
which tends to zero (O&R fn 46; the book leaves this implicit). -/
theorem transversality_lp {P : S → S → ℝ} (hP : IsMarkov P) {A : S → ℝ} {α β K₀ : ℝ}
    (hp : Params α β) (hA : ∀ s, 0 < A s) (hK : 0 < K₀) (s₀ : S) :
    (∀ T, β ^ T * ev P (fun l => lpPolicy A α β K₀ l /
        consumption A α K₀ (lpPolicy A α β K₀) l) T s₀ [] = β ^ T * (α * β / (1 - α * β))) ∧
      Tendsto (fun T => β ^ T * ev P (fun l => lpPolicy A α β K₀ l /
        consumption A α K₀ (lpPolicy A α β K₀) l) T s₀ []) atTop (𝓝 0) := by
  have hab := hp.ab_lt_one
  have hnode : ∀ s h, lpPolicy A α β K₀ (s :: h) /
      consumption A α K₀ (lpPolicy A α β K₀) (s :: h) = α * β / (1 - α * β) := by
    intro s h
    rw [consumption_lpPolicy]
    simp only [lpPolicy]
    have h1 : (1 - α * β) ≠ 0 := by linarith
    have h2 := (hA s).ne'
    have h3 := (Real.rpow_pos_of_pos (lpPolicy_pos hp hA hK h) α).ne'
    field_simp
  have hev : ∀ T, ev P (fun l => lpPolicy A α β K₀ l /
      consumption A α K₀ (lpPolicy A α β K₀) l) T s₀ [] = α * β / (1 - α * β) := fun T => by
    rw [ev_congr P (g := fun _ => α * β / (1 - α * β)) hnode, ev_const hP]
  refine ⟨fun T => by rw [hev], ?_⟩
  simp only [hev]
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hp.β_pos.le hp.β_lt_one).mul_const
    (α * β / (1 - α * β))

/-! ## The log-linear law of motion (110)–(113), pathwise -/

/-- Capital along one realised shock path under the Long–Plosser policy:
`K_{t+1} = αβ A_t K_t^α` (O&R p. 499). -/
noncomputable def capitalPath (α β K₀ : ℝ) (A : ℕ → ℝ) : ℕ → ℝ
  | 0 => K₀
  | t + 1 => α * β * (A t * capitalPath α β K₀ A t ^ α)

/-- Log output along a realised path, `y_t = log(A_t K_t^α)`. -/
noncomputable def logOutputPath (α β K₀ : ℝ) (A : ℕ → ℝ) (t : ℕ) : ℝ :=
  Real.log (A t * capitalPath α β K₀ A t ^ α)

/-- Positivity of capital along a path. -/
theorem capitalPath_pos {α β K₀ : ℝ} (hp : Params α β) {A : ℕ → ℝ} (hA : ∀ t, 0 < A t)
    (hK : 0 < K₀) (t : ℕ) : 0 < capitalPath α β K₀ A t := by
  induction t with
  | zero => exact hK
  | succ t ih => exact mul_pos hp.ab_pos (mul_pos (hA t) (Real.rpow_pos_of_pos ih α))

/-- **(110)**: `y_{t+1} = χ₀ + α y_t + a_{t+1}` with `χ₀ = α log(αβ)` and `a = log A`, exactly
(no approximation), along every shock path. -/
theorem logOutput_ar1 {α β K₀ : ℝ} (hp : Params α β) {A : ℕ → ℝ} (hA : ∀ t, 0 < A t)
    (hK : 0 < K₀) (t : ℕ) :
    logOutputPath α β K₀ A (t + 1) =
      α * Real.log (α * β) + α * logOutputPath α β K₀ A t + Real.log (A (t + 1)) := by
  have hk := capitalPath_pos hp hA hK t
  have hY : 0 < A t * capitalPath α β K₀ A t ^ α := mul_pos (hA t) (Real.rpow_pos_of_pos hk α)
  simp only [logOutputPath, capitalPath]
  rw [Real.log_mul (hA (t + 1)).ne' (Real.rpow_pos_of_pos (mul_pos hp.ab_pos hY) α).ne',
    Real.log_rpow (mul_pos hp.ab_pos hY), Real.log_mul hp.ab_pos.ne' hY.ne']
  ring

/-- **(111)**: the steady state `ȳ = (χ₀ + ā)/(1 − α)` is the unique solution of
`ȳ = χ₀ + αȳ + ā`. -/
theorem steady_logOutput_iff {α χ₀ a y : ℝ} (hα : α < 1) :
    y = χ₀ + α * y + a ↔ y = (χ₀ + a) / (1 - α) := by
  have h : (1 - α) ≠ 0 := by linarith
  constructor
  · intro hy; field_simp; linarith
  · intro hy; rw [hy]; field_simp; ring

/-- (111): `dȳ/dā = 1/(1 − α)`: a permanent change in mean log productivity raises mean log
output more than proportionally. -/
theorem hasDerivAt_steady_logOutput {α χ₀ : ℝ} (a : ℝ) :
    HasDerivAt (fun a => (χ₀ + a) / (1 - α)) (1 / (1 - α)) a := by
  have := ((hasDerivAt_id a).const_add χ₀).div_const (1 - α)
  simpa using this

/-- **(112)**: deviations from the steady state follow
`y_{t+1} − ȳ = α(y_t − ȳ) + (a_{t+1} − ā)`. -/
theorem logOutput_deviation {α β K₀ : ℝ} (hp : Params α β) {A : ℕ → ℝ} (hA : ∀ t, 0 < A t)
    (hK : 0 < K₀) (abar : ℝ) (t : ℕ) :
    logOutputPath α β K₀ A (t + 1) - (α * Real.log (α * β) + abar) / (1 - α) =
      α * (logOutputPath α β K₀ A t - (α * Real.log (α * β) + abar) / (1 - α)) +
        (Real.log (A (t + 1)) - abar) := by
  rw [logOutput_ar1 hp hA hK t]
  have h : (1 - α) ≠ 0 := by linarith [hp.α_lt_one]
  field_simp
  ring

/-- **(113)**, the reduced form (footnote 48):
`y_t − ȳ = Σ_{s=1}^{t} α^{t−s}(a_s − ā) + α^t (y_0 − ȳ)`. -/
theorem logOutput_reduced_form {α β K₀ : ℝ} (hp : Params α β) {A : ℕ → ℝ}
    (hA : ∀ t, 0 < A t) (hK : 0 < K₀) (abar : ℝ) (t : ℕ) :
    logOutputPath α β K₀ A t - (α * Real.log (α * β) + abar) / (1 - α) =
      ∑ j ∈ range t, α ^ (t - 1 - j) * (Real.log (A (j + 1)) - abar) +
        α ^ t * (logOutputPath α β K₀ A 0 - (α * Real.log (α * β) + abar) / (1 - α)) := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [logOutput_deviation hp hA hK abar t, ih, Finset.sum_range_succ, mul_add, Finset.mul_sum]
    have hs : ∀ j ∈ range t, α * (α ^ (t - 1 - j) * (Real.log (A (j + 1)) - abar)) =
        α ^ (t + 1 - 1 - j) * (Real.log (A (j + 1)) - abar) := by
      intro j hj
      have hj' : j < t := Finset.mem_range.1 hj
      rw [show t + 1 - 1 - j = (t - 1 - j) + 1 by omega, pow_succ]
      ring
    rw [Finset.sum_congr rfl hs, show t + 1 - 1 - t = 0 by omega, pow_zero, pow_succ]
    ring

/-- O&R p. 499: a purely transitory one-period shock `Δ` to `a` at date `t₀` raises
`y_{t₀+j}` by exactly `αʲ Δ` (so date `t₀+1` output rises by only `α Δ`). -/
theorem transitory_shock_response {α β K₀ : ℝ} (hp : Params α β) {A A' : ℕ → ℝ}
    (hA : ∀ t, 0 < A t) (hA' : ∀ t, 0 < A' t) (hK : 0 < K₀) (t₀ : ℕ) (Δ : ℝ)
    (hbefore : ∀ t, t ≠ t₀ → A' t = A t) (hat : Real.log (A' t₀) = Real.log (A t₀) + Δ) :
    (∀ t, t < t₀ → logOutputPath α β K₀ A' t = logOutputPath α β K₀ A t) ∧
      ∀ j, logOutputPath α β K₀ A' (t₀ + j) - logOutputPath α β K₀ A (t₀ + j) = α ^ j * Δ := by
  have hcap : ∀ t, t ≤ t₀ → capitalPath α β K₀ A' t = capitalPath α β K₀ A t := by
    intro t ht
    induction t with
    | zero => rfl
    | succ t ih =>
      simp only [capitalPath]
      rw [ih (by omega), hbefore t (by omega)]
  refine ⟨fun t ht => ?_, fun j => ?_⟩
  · simp only [logOutputPath]; rw [hcap t ht.le, hbefore t ht.ne]
  · induction j with
    | zero =>
      simp only [add_zero, pow_zero, one_mul, logOutputPath]
      rw [hcap t₀ le_rfl, Real.log_mul (hA' t₀).ne'
        (Real.rpow_pos_of_pos (capitalPath_pos hp hA hK t₀) α).ne',
        Real.log_mul (hA t₀).ne' (Real.rpow_pos_of_pos (capitalPath_pos hp hA hK t₀) α).ne',
        hat]
      ring
    | succ j ih =>
      rw [show t₀ + (j + 1) = (t₀ + j) + 1 by omega, logOutput_ar1 hp hA' hK,
        logOutput_ar1 hp hA hK, hbefore _ (by omega), pow_succ]
      linear_combination α * ih

/-! ## The conditional mean of log output on the event tree -/

/-- Log output at a node under the Long–Plosser policy, `y = log A(s) + α log K`. -/
noncomputable def logOutput (A : S → ℝ) (α β K₀ : ℝ) : List S → ℝ
  | [] => 0
  | s :: h => Real.log (A s) + α * Real.log (lpPolicy A α β K₀ h)

/-- Log productivity at a node, `a = log A(s)`. -/
noncomputable def logProd (A : S → ℝ) : List S → ℝ
  | [] => 0
  | s :: _ => Real.log (A s)

omit [Fintype S] in
/-- `logOutput` is the log of output (O&R p. 499). -/
theorem logOutput_eq {A : S → ℝ} {α β K₀ : ℝ} (hp : Params α β) (hA : ∀ s, 0 < A s)
    (hK : 0 < K₀) (s : S) (h : List S) :
    logOutput A α β K₀ (s :: h) = Real.log (output A α K₀ (lpPolicy A α β K₀) (s :: h)) := by
  simp only [logOutput, output, capIn_lpPolicy]
  rw [Real.log_mul (hA s).ne' (Real.rpow_pos_of_pos (lpPolicy_pos hp hA hK h) α).ne',
    Real.log_rpow (lpPolicy_pos hp hA hK h)]

omit [Fintype S] in
/-- (110) on the tree: `y(s'::node) = χ₀ + α y(node) + log A(s')`. -/
theorem logOutput_cons_cons {A : S → ℝ} {α β K₀ : ℝ} (hp : Params α β) (hA : ∀ s, 0 < A s)
    (hK : 0 < K₀) (s' s : S) (h : List S) :
    logOutput A α β K₀ (s' :: s :: h) =
      α * Real.log (α * β) + α * logOutput A α β K₀ (s :: h) + Real.log (A s') := by
  have hy := lpPolicy_pos hp hA hK h
  have hY : 0 < A s * lpPolicy A α β K₀ h ^ α := mul_pos (hA s) (Real.rpow_pos_of_pos hy α)
  simp only [logOutput, lpPolicy]
  rw [Real.log_mul hp.ab_pos.ne' hY.ne', Real.log_mul (hA s).ne' (Real.rpow_pos_of_pos hy α).ne',
    Real.log_rpow hy]
  ring

/-- The conditional mean `m_T = E₀ y_T` obeys `m_{T+1} = χ₀ + α m_T + E₀ a_{T+1}` (linearity of
expectation applied to (110)). -/
theorem mean_logOutput_succ {P : S → S → ℝ} (hP : IsMarkov P) {A : S → ℝ} {α β K₀ : ℝ}
    (hp : Params α β) (hA : ∀ s, 0 < A s) (hK : 0 < K₀) (s₀ : S) (T : ℕ) :
    ev P (logOutput A α β K₀) (T + 1) s₀ [] =
      α * Real.log (α * β) + α * ev P (logOutput A α β K₀) T s₀ [] +
        ev P (logProd A) (T + 1) s₀ [] := by
  rw [← ev_nextExp, ← ev_nextExp, ← ev_const_mul, ← ev_const hP (α * Real.log (α * β)) T s₀ [],
    ← ev_add, ← ev_add]
  refine ev_congr P (fun s h => ?_) T s₀ []
  simp only [nextExp, logOutput_cons_cons hp hA hK, logProd, mul_add, Finset.sum_add_distrib,
    ← Finset.sum_mul, hP.sum_one, one_mul]

/-- A stable linear recursion driven by a convergent forcing term converges:
`m_{T+1} = c + α m_T + e_{T+1}`, `e_T → ē`, `0 ≤ α < 1` imply `m_T → (c + ē)/(1 − α)`. -/
theorem tendsto_of_linear_recursion {α c ebar : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) {m e : ℕ → ℝ}
    (hm : ∀ T, m (T + 1) = c + α * m T + e (T + 1)) (he : Tendsto e atTop (𝓝 ebar)) :
    Tendsto m atTop (𝓝 ((c + ebar) / (1 - α))) := by
  set ybar := (c + ebar) / (1 - α)
  have h1α : 0 < 1 - α := by linarith
  have hy : ybar = c + α * ybar + ebar := (steady_logOutput_iff hα1).2 rfl
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 he ((1 - α) * ε / 2) (by positivity)
  have hdev : ∀ j, |m (N + j) - ybar| ≤ α ^ j * |m N - ybar| + ε / 2 := by
    intro j
    induction j with
    | zero => simp; linarith
    | succ j ih =>
      have hE := hN (N + j + 1) (by omega)
      rw [Real.dist_eq] at hE
      have hrec : m (N + (j + 1)) - ybar = α * (m (N + j) - ybar) + (e (N + j + 1) - ebar) := by
        rw [show N + (j + 1) = N + j + 1 by omega, hm]; linarith
      rw [hrec, pow_succ]
      calc |α * (m (N + j) - ybar) + (e (N + j + 1) - ebar)|
          ≤ α * |m (N + j) - ybar| + |e (N + j + 1) - ebar| := by
            refine (abs_add_le _ _).trans ?_
            rw [abs_mul, abs_of_nonneg hα0]
        _ ≤ α * (α ^ j * |m N - ybar| + ε / 2) + (1 - α) * ε / 2 := by
            gcongr
        _ = α ^ j * α * |m N - ybar| + ε / 2 := by ring
  have hpow := tendsto_pow_atTop_nhds_zero_of_lt_one hα0 hα1
  obtain ⟨J, hJ⟩ := Metric.tendsto_atTop.1 (hpow.mul_const |m N - ybar|) (ε / 2) (by positivity)
  refine ⟨N + J, fun n hn => ?_⟩
  obtain ⟨j, rfl⟩ : ∃ j, n = N + j := ⟨n - N, by omega⟩
  have := hJ j (by omega)
  rw [Real.dist_eq, zero_mul, sub_zero, abs_of_nonneg (by positivity)] at this
  rw [Real.dist_eq]
  linarith [hdev j]

/-- **(111), the stochastic steady state** (Markov shocks). If the conditional mean of log
productivity converges, `E₀ a_T → ā` (the book's assumption `lim E_t a_{t+T} = ā`), then the
conditional mean of log output converges to `ȳ = (χ₀ + ā)/(1 − α)`. -/
theorem mean_logOutput_tendsto {P : S → S → ℝ} (hP : IsMarkov P) {A : S → ℝ} {α β K₀ : ℝ}
    (hp : Params α β) (hA : ∀ s, 0 < A s) (hK : 0 < K₀) (s₀ : S) {abar : ℝ}
    (ha : Tendsto (fun T => ev P (logProd A) T s₀ []) atTop (𝓝 abar)) :
    Tendsto (fun T => ev P (logOutput A α β K₀) T s₀ []) atTop
      (𝓝 ((α * Real.log (α * β) + abar) / (1 - α))) :=
  tendsto_of_linear_recursion hp.α_pos.le hp.α_lt_one
    (fun T => mean_logOutput_succ hP hp hA hK s₀ T) ha

/-- I.i.d. shocks: the transition kernel does not depend on the current state. -/
def IsIID (P : S → S → ℝ) (p : S → ℝ) : Prop := ∀ s s', P s s' = p s'

/-- With i.i.d. shocks `E₀ a_T = Σ p(s) log A(s)` for every `T ≥ 1`. -/
theorem mean_logProd_iid {P : S → S → ℝ} {p : S → ℝ} (hP : IsMarkov P) (hiid : IsIID P p)
    (A : S → ℝ) (s₀ : S) (T : ℕ) :
    ev P (logProd A) (T + 1) s₀ [] = ∑ s, p s * Real.log (A s) := by
  rw [← ev_nextExp]
  rw [ev_congr P (g := fun _ => ∑ s, p s * Real.log (A s)) (fun s h => by
    simp only [nextExp, logProd]
    exact Finset.sum_congr rfl fun s' _ => by rw [hiid]), ev_const hP]

/-- **(111) for i.i.d. shocks**, unconditionally: `E₀ y_T → (χ₀ + ā)/(1 − α)` with
`ā = Σ p(s) log A(s)`. -/
theorem mean_logOutput_tendsto_iid {P : S → S → ℝ} {p : S → ℝ} (hP : IsMarkov P)
    (hiid : IsIID P p) {A : S → ℝ} {α β K₀ : ℝ} (hp : Params α β) (hA : ∀ s, 0 < A s)
    (hK : 0 < K₀) (s₀ : S) :
    Tendsto (fun T => ev P (logOutput A α β K₀) T s₀ []) atTop
      (𝓝 ((α * Real.log (α * β) + ∑ s, p s * Real.log (A s)) / (1 - α))) := by
  refine mean_logOutput_tendsto hP hp hA hK s₀ ?_
  rw [← tendsto_add_atTop_iff_nat 1]
  simp only [mean_logProd_iid hP hiid A s₀]
  exact tendsto_const_nhds

/-! ## Stochastic stability: forgetting the initial condition and the limiting law -/

omit [Fintype S] in
/-- Along the same shock history, two initial capital stocks give log capital differing by
`α^{depth}(log K₀ − log K₀')`: the log-AR(1) law of motion contracts at rate `α`. -/
theorem log_lpPolicy_sub {A : S → ℝ} {α β K₀ K₀' : ℝ} (hp : Params α β) (hA : ∀ s, 0 < A s)
    (hK : 0 < K₀) (hK' : 0 < K₀') (l : List S) :
    Real.log (lpPolicy A α β K₀ l) - Real.log (lpPolicy A α β K₀' l) =
      α ^ l.length * (Real.log K₀ - Real.log K₀') := by
  induction l with
  | nil => simp [lpPolicy]
  | cons s h ih =>
    have hy := lpPolicy_pos hp hA hK h
    have hy' := lpPolicy_pos hp hA hK' h
    simp only [lpPolicy, List.length_cons]
    rw [Real.log_mul hp.ab_pos.ne' (mul_pos (hA s) (Real.rpow_pos_of_pos hy α)).ne',
      Real.log_mul (hA s).ne' (Real.rpow_pos_of_pos hy α).ne', Real.log_rpow hy,
      Real.log_mul hp.ab_pos.ne' (mul_pos (hA s) (Real.rpow_pos_of_pos hy' α)).ne',
      Real.log_mul (hA s).ne' (Real.rpow_pos_of_pos hy' α).ne', Real.log_rpow hy', pow_succ]
    linear_combination α * ih

omit [Fintype S] in
/-- The corresponding log-output gap at a node. -/
theorem logOutput_sub {A : S → ℝ} {α β K₀ K₀' : ℝ} (hp : Params α β) (hA : ∀ s, 0 < A s)
    (hK : 0 < K₀) (hK' : 0 < K₀') (s : S) (h : List S) :
    logOutput A α β K₀ (s :: h) - logOutput A α β K₀' (s :: h) =
      α ^ (s :: h).length * (Real.log K₀ - Real.log K₀') := by
  have := log_lpPolicy_sub hp hA hK hK' h
  simp only [logOutput, List.length_cons, pow_succ]
  linear_combination α * this

/-- Two-sided bound on a difference of conditional expectations. -/
theorem abs_ev_sub_le {P : S → S → ℝ} (hP : IsMarkov P) {f g φ : List S → ℝ}
    (h : ∀ s h, |f (s :: h) - g (s :: h)| ≤ φ (s :: h)) (n : ℕ) (s : S) (hh : List S) :
    |ev P f n s hh - ev P g n s hh| ≤ ev P φ n s hh := by
  rw [← ev_sub, abs_le]
  constructor
  · have := ev_mono hP (f := fun l => -1 * φ l) (g := fun l => f l - g l)
      (fun s h' => by have := (abs_le.1 (h s h')).1; linarith) n s hh
    rw [ev_const_mul] at this
    linarith
  · exact ev_mono hP (fun s h' => (abs_le.1 (h s h')).2) n s hh

/-- **Forgetting the initial condition.** For every `L`-Lipschitz test function `g`,
`|E₀ g(y_T) − E₀ g(y'_T)| ≤ L α^{T+1} |log K₀ − log K₀'|`, for any finite-state Markov shock. -/
theorem ev_logOutput_coupling {P : S → S → ℝ} (hP : IsMarkov P) {A : S → ℝ} {α β K₀ K₀' : ℝ}
    (hp : Params α β) (hA : ∀ s, 0 < A s) (hK : 0 < K₀) (hK' : 0 < K₀') {g : ℝ → ℝ} {L : ℝ}
    (hg : ∀ x y, |g x - g y| ≤ L * |x - y|) (s₀ : S) (T : ℕ) :
    |ev P (fun l => g (logOutput A α β K₀ l)) T s₀ [] -
        ev P (fun l => g (logOutput A α β K₀' l)) T s₀ []| ≤
      L * α ^ (T + 1) * |Real.log K₀ - Real.log K₀'| := by
  have hb := abs_ev_sub_le hP (f := fun l => g (logOutput A α β K₀ l))
    (g := fun l => g (logOutput A α β K₀' l))
    (φ := fun l => L * α ^ l.length * |Real.log K₀ - Real.log K₀'|) (fun s h => by
      refine (hg _ _).trans (le_of_eq ?_)
      rw [logOutput_sub hp hA hK hK' s h, abs_mul, abs_of_pos (pow_pos hp.α_pos _)]
      ring) T s₀ []
  rwa [ev_length hP (fun n => L * α ^ n * |Real.log K₀ - Real.log K₀'|), List.length_nil,
    add_zero] at hb

omit [Fintype S] in
/-- The Long–Plosser policy restarted one period later: capital along `l ++ [s]` from `K₀` equals
capital along `l` from `K₁ = αβ A(s) K₀^α`. -/
theorem lpPolicy_append (A : S → ℝ) (α β K₀ : ℝ) (s : S) (l : List S) :
    lpPolicy A α β K₀ (l ++ [s]) = lpPolicy A α β (lpPolicy A α β K₀ [s]) l := by
  induction l with
  | nil => rfl
  | cons s' l ih => simp only [List.cons_append, lpPolicy, ih]

/-- The subtree below a date-0 state is an event tree in its own right. -/
theorem ev_append (P : S → S → ℝ) (f : List S → ℝ) (s : S) (n : ℕ) :
    ∀ s' h, ev P f n s' (h ++ [s]) = ev P (fun l => f (l ++ [s])) n s' h := by
  induction n with
  | zero => intro s' h; rfl
  | succ n ih =>
    intro s' h
    simp only [ev]
    exact Finset.sum_congr rfl fun s'' _ => by congr 1; exact ih s'' (s' :: h)

/-- The law of log output, tested on `g`: `E g(y_T)` from initial capital `K` and state `s`. -/
noncomputable def lawTest (P : S → S → ℝ) (A : S → ℝ) (α β : ℝ) (g : ℝ → ℝ) (T : ℕ) (K : ℝ)
    (s : S) : ℝ :=
  ev P (fun l => g (logOutput A α β K l)) T s []

/-- Markov restart: with i.i.d. shocks, `E_{K,s} g(y_{T+1}) = Σ p(s') E_{K₁,s'} g(y_T)` with
`K₁ = αβ A(s) K^α`. -/
theorem lawTest_succ {P : S → S → ℝ} {p : S → ℝ} (hiid : IsIID P p) (A : S → ℝ) (α β : ℝ)
    (g : ℝ → ℝ) (T : ℕ) (K : ℝ) (s : S) :
    lawTest P A α β g (T + 1) K s =
      ∑ s', p s' * lawTest P A α β g T (lpPolicy A α β K [s]) s' := by
  simp only [lawTest, ev]
  refine Finset.sum_congr rfl fun s' _ => ?_
  rw [hiid, show ([s] : List S) = [] ++ [s] from rfl, ev_append]
  congr 1
  refine ev_congr P (fun s'' h => ?_) T s' []
  simp only [List.cons_append, List.nil_append, logOutput]
  rw [lpPolicy_append]

/-- **Convergence of the distribution of log output** (the stochastic steady state of O&R
(110)–(111), i.i.d. shocks). For every Lipschitz test function `g` there is a limit `Λ` such that
`E₀ g(y_T) → Λ` from **every** initial capital `K₀ > 0` and initial state `s₀`: the law of `y_T`
(equivalently of `log K_{T+1} = log αβ + y_T`) converges weakly to a unique stationary law. -/
theorem law_logOutput_converges {P : S → S → ℝ} {p : S → ℝ} (hP : IsMarkov P)
    (hiid : IsIID P p) {A : S → ℝ} {α β : ℝ} (hp : Params α β) (hA : ∀ s, 0 < A s)
    {g : ℝ → ℝ} {L : ℝ} (hL : 0 ≤ L) (hg : ∀ x y, |g x - g y| ≤ L * |x - y|) :
    ∃ Λ : ℝ, ∀ K₀ s₀, 0 < K₀ →
      Tendsto (fun T => lawTest P A α β g T K₀ s₀) atTop (𝓝 Λ) := by
  by_cases hS : Nonempty S
  swap
  · exact ⟨0, fun _ s₀ _ => absurd ⟨s₀⟩ hS⟩
  obtain ⟨s₁⟩ := hS
  -- the averaged law `G_T(K) = Σ p(s) E_{K,s} g(y_T)`
  set G : ℕ → ℝ → ℝ := fun T K => ∑ s, p s * lawTest P A α β g T K s with hG
  have hp0 : ∀ s, 0 ≤ p s := fun s => by rw [← hiid s₁ s]; exact hP.nonneg s₁ s
  have hcoup : ∀ T K K', 0 < K → 0 < K' → ∀ s,
      |lawTest P A α β g T K s - lawTest P A α β g T K' s| ≤
        L * α ^ (T + 1) * |Real.log K - Real.log K'| :=
    fun T K K' hK hK' s => ev_logOutput_coupling hP hp hA hK hK' hg s T
  have hGcoup : ∀ T K K', 0 < K → 0 < K' →
      |G T K - G T K'| ≤ ∑ s, p s * (L * α ^ (T + 1) * |Real.log K - Real.log K'|) := by
    intro T K K' hK hK'
    simp only [hG, ← Finset.sum_sub_distrib, ← mul_sub]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun s _ => ?_)
    rw [abs_mul, abs_of_nonneg (hp0 s)]
    exact mul_le_mul_of_nonneg_left (hcoup T K K' hK hK' s) (hp0 s)
  have hpsum : ∀ c : ℝ, ∑ s, p s * c = (∑ s, p s) * c := fun c => by rw [Finset.sum_mul]
  set Pm := ∑ s, p s
  have hPm : Pm = 1 := by
    simp only [Pm]; rw [← hP.sum_one s₁]
    exact Finset.sum_congr rfl fun s _ => (hiid s₁ s).symm
  -- `G_{T+1}(K) = Σ p(s) G_T(K₁(K,s))`
  have hGsucc : ∀ T K, G (T + 1) K = ∑ s, p s * G T (lpPolicy A α β K [s]) := by
    intro T K
    simp only [hG, lawTest_succ hiid]
  have hK1 : ∀ K, 0 < K → ∀ s, 0 < lpPolicy A α β K [s] := fun K hK s =>
    lpPolicy_pos hp hA hK [s]
  -- Cauchy estimate for each `K`
  have hcauchy : ∀ K, 0 < K → CauchySeq (fun T => G T K) := by
    intro K hK
    set D := ∑ s, |Real.log (lpPolicy A α β K [s]) - Real.log K|
    refine cauchySeq_of_le_geometric α (L * α * D) hp.α_lt_one fun T => ?_
    rw [Real.dist_eq, abs_sub_comm, hGsucc]
    have : ∑ s, p s * (G T (lpPolicy A α β K [s]) - G T K) =
        ∑ s, p s * G T (lpPolicy A α β K [s]) - G T K := by
      rw [Finset.sum_congr rfl (fun s _ => mul_sub (p s) _ _), Finset.sum_sub_distrib,
        hpsum (G T K), hPm, one_mul]
    rw [← this]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ s, |p s * (G T (lpPolicy A α β K [s]) - G T K)|
        ≤ ∑ s, p s * (L * α ^ (T + 1) * D) := Finset.sum_le_sum fun s _ => by
          rw [abs_mul, abs_of_nonneg (hp0 s)]
          refine mul_le_mul_of_nonneg_left ((hGcoup T _ K (hK1 K hK s) hK).trans ?_) (hp0 s)
          rw [hpsum, hPm, one_mul]
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hL (pow_pos hp.α_pos _).le)
          exact Finset.single_le_sum
            (f := fun s => |Real.log (lpPolicy A α β K [s]) - Real.log K|)
            (fun _ _ => abs_nonneg _) (Finset.mem_univ s)
      _ = L * α * D * α ^ T := by rw [hpsum, hPm, pow_succ]; ring
  choose Λ hΛ using fun K : {K : ℝ // 0 < K} => cauchySeq_tendsto_of_complete (hcauchy K.1 K.2)
  set Λ₁ := Λ ⟨1, one_pos⟩
  -- the limit does not depend on `K`
  have hsame : ∀ K (hK : 0 < K), Tendsto (fun T => G T K) atTop (𝓝 Λ₁) := by
    intro K hK
    have hdiff : Tendsto (fun T => G T K - G T 1) atTop (𝓝 0) := by
      refine squeeze_zero_norm (fun T => (hGcoup T K 1 hK one_pos).trans (le_of_eq ?_))
        (?_ : Tendsto (fun T => Pm * (L * α ^ (T + 1) * |Real.log K - Real.log 1|)) atTop
          (𝓝 0))
      · rw [hpsum]
      · have h := (tendsto_pow_atTop_nhds_zero_of_lt_one hp.α_pos.le hp.α_lt_one)
        have h2 := ((h.const_mul α).const_mul L).mul_const |Real.log K - Real.log 1|
        have h3 := h2.const_mul Pm
        simp only [mul_zero, zero_mul] at h3
        refine h3.congr fun T => ?_
        rw [pow_succ]; ring
    have := (hΛ ⟨1, one_pos⟩).add hdiff
    rw [add_zero] at this
    exact this.congr fun T => by ring
  refine ⟨Λ₁, fun K₀ s₀ hK => ?_⟩
  rw [← tendsto_add_atTop_iff_nat 1]
  have hK1' := hK1 K₀ hK s₀
  -- `E_{K₀,s₀} g(y_{T+1})` versus `G_T(K₁)`
  have hstep : ∀ T, lawTest P A α β g (T + 1) K₀ s₀ = G T (lpPolicy A α β K₀ [s₀]) := by
    intro T; rw [lawTest_succ hiid]
  simp only [hstep]
  exact hsame _ hK1'

/-! ## Exercise 4: consumption and wealth in the Long–Plosser model -/

/-- The wage `w_t L = (1 − α) Y_t` (marginal product of labour with `L = 1`). -/
noncomputable def wage (A : S → ℝ) (α β K₀ : ℝ) (l : List S) : ℝ :=
  (1 - α) * output A α K₀ (lpPolicy A α β K₀) l

omit [Fintype S] in
/-- (106) with 100 percent depreciation: `(1 + r̃_t) K_t = α Y_t`. -/
theorem grossReturn_mul_capital {A : S → ℝ} {α β K₀ : ℝ} (hp : Params α β) (hA : ∀ s, 0 < A s)
    (hK : 0 < K₀) (s : S) (h : List S) :
    grossReturn α (A s) (lpPolicy A α β K₀ h) * lpPolicy A α β K₀ h =
      α * output A α K₀ (lpPolicy A α β K₀) (s :: h) := by
  have hy := lpPolicy_pos hp hA hK h
  simp only [grossReturn, output, capIn_lpPolicy]
  rw [Real.rpow_sub_one hy.ne']
  field_simp

/-- **Exercise 4, human wealth.** At every node, the stochastically discounted value of current
and future wages, `Σ_{n≥0} E_t[βⁿ (u′(C_{t+n})/u′(C_t)) w_{t+n} L]`, converges and equals
`(1 − α) Y_t/(1 − β)`. -/
theorem hasSum_human_wealth {P : S → S → ℝ} (hP : IsMarkov P) {A : S → ℝ} {α β K₀ : ℝ}
    (hp : Params α β) (hA : ∀ s, 0 < A s) (hK : 0 < K₀) (s : S) (h : List S) :
    HasSum (fun n => β ^ n * ev P (fun l => consumption A α K₀ (lpPolicy A α β K₀) (s :: h) /
        consumption A α K₀ (lpPolicy A α β K₀) l * wage A α β K₀ l) n s h)
      ((1 - α) * output A α K₀ (lpPolicy A α β K₀) (s :: h) / (1 - β)) := by
  set C := consumption A α K₀ (lpPolicy A α β K₀) (s :: h)
  have hab := hp.ab_lt_one
  have hnode : ∀ s' h', C / consumption A α K₀ (lpPolicy A α β K₀) (s' :: h') *
      wage A α β K₀ (s' :: h') = C * (1 - α) / (1 - α * β) := by
    intro s' h'
    rw [consumption_lpPolicy]
    simp only [wage, output, capIn_lpPolicy]
    have h1 : (1 - α * β) ≠ 0 := by linarith
    have h2 := (hA s').ne'
    have h3 := (Real.rpow_pos_of_pos (lpPolicy_pos hp hA hK h') α).ne'
    field_simp
  have hev : ∀ n, ev P (fun l => C / consumption A α K₀ (lpPolicy A α β K₀) l *
      wage A α β K₀ l) n s h = C * (1 - α) / (1 - α * β) := fun n => by
    rw [ev_congr P (g := fun _ => C * (1 - α) / (1 - α * β)) hnode, ev_const hP]
  simp only [hev]
  have hg := (hasSum_geometric_of_lt_one hp.β_pos.le hp.β_lt_one).mul_right
    (C * (1 - α) / (1 - α * β))
  convert hg using 1
  simp only [C]
  rw [consumption_lpPolicy]
  simp only [output, capIn_lpPolicy]
  have h1 : (1 - α * β) ≠ 0 := by linarith
  have h4 : (1 - β) ≠ 0 := by linarith [hp.β_lt_one]
  field_simp

/-- **Exercise 4** (p. 512): equilibrium consumption is `(1 − β)` times total wealth,
`C_t = (1 − β)[(1 + r̃_t) K_t + H_t]`, where `H_t` is the human wealth of
`hasSum_human_wealth`. Interpretation (Ch. 5, Supplement A): with log utility consumption is the
annuity value of financial plus human wealth, human wealth being priced with the stochastic
discount factor `βⁿ u′(C_{t+n})/u′(C_t)`. -/
theorem exercise4_consumption {P : S → S → ℝ} (hP : IsMarkov P) {A : S → ℝ} {α β K₀ : ℝ}
    (hp : Params α β) (hA : ∀ s, 0 < A s) (hK : 0 < K₀) (s : S) (h : List S) :
    consumption A α K₀ (lpPolicy A α β K₀) (s :: h) = (1 - β) *
      (grossReturn α (A s) (lpPolicy A α β K₀ h) * lpPolicy A α β K₀ h +
        ∑' n, β ^ n * ev P (fun l => consumption A α K₀ (lpPolicy A α β K₀) (s :: h) /
          consumption A α K₀ (lpPolicy A α β K₀) l * wage A α β K₀ l) n s h) := by
  rw [(hasSum_human_wealth hP hp hA hK s h).tsum_eq, grossReturn_mul_capital hp hA hK s h,
    consumption_lpPolicy]
  simp only [output, capIn_lpPolicy]
  have h4 : (1 - β) ≠ 0 := by linarith [hp.β_lt_one]
  field_simp
  ring

/-! ## Appendix 7B: a stochastic overlapping-generations model -/

namespace StochasticOLG

/-- Gross portfolio return with bond share `x`: `x(1 + r) + (1 − x)(1 + r̃(s))`, O&R (139). -/
def portfolioReturn (R : ℝ) (Rt : S → ℝ) (x : ℝ) (s : S) : ℝ := x * R + (1 - x) * Rt s

/-- Lifetime expected utility (138)–(139) of a young agent with wage `w`, consumption `c` and
bond share `x`, risky gross returns `Rt(s)` with probabilities `p(s)`. -/
noncomputable def lifetimeUtility (β R w : ℝ) (p Rt : S → ℝ) (c x : ℝ) : ℝ :=
  Real.log c + β * ∑ s, p s * Real.log ((w - c) * portfolioReturn R Rt x s)

/-- A probability mass function on the finite state space. -/
structure IsPMF (p : S → ℝ) : Prop where
  nonneg : ∀ s, 0 ≤ p s
  sum_one : ∑ s, p s = 1

/-- Separating the saving decision from the portfolio decision (log utility). -/
theorem lifetimeUtility_eq {β R w : ℝ} {p Rt : S → ℝ} (hp : IsPMF p) {c x : ℝ} (hc : c < w)
    (hR : ∀ s, 0 < portfolioReturn R Rt x s) :
    lifetimeUtility β R w p Rt c x = Real.log c + β * Real.log (w - c) +
      β * ∑ s, p s * Real.log (portfolioReturn R Rt x s) := by
  simp only [lifetimeUtility]
  rw [Finset.sum_congr rfl fun s _ => by
    rw [Real.log_mul (sub_pos.2 hc).ne' (hR s).ne', mul_add],
    Finset.sum_add_distrib, ← Finset.sum_mul, hp.sum_one, one_mul]
  ring

/-- `log c + β log(w − c)` is uniquely maximised on `(0, w)` at `c = w/(1 + β)`. -/
theorem saving_lt {β w c : ℝ} (hβ : 0 < β) (hw : 0 < w) (hc0 : 0 < c) (hc1 : c < w)
    (hne : c ≠ w / (1 + β)) :
    Real.log c + β * Real.log (w - c) <
      Real.log (w / (1 + β)) + β * Real.log (w - w / (1 + β)) := by
  have hc' : 0 < w / (1 + β) := by positivity
  have hd' : 0 < w - w / (1 + β) := by
    rw [sub_pos, div_lt_iff₀ (by linarith)]; nlinarith
  have hne1 : c / (w / (1 + β)) ≠ 1 := by
    intro h; exact hne (by rw [div_eq_one_iff_eq hc'.ne'] at h; exact h)
  have l1 := Real.log_lt_sub_one_of_pos (div_pos hc0 hc') hne1
  have l2 := Real.log_le_sub_one_of_pos (div_pos (sub_pos.2 hc1) hd')
  rw [Real.log_div hc0.ne' hc'.ne'] at l1
  rw [Real.log_div (sub_pos.2 hc1).ne' hd'.ne'] at l2
  have l2' := mul_le_mul_of_nonneg_left l2 hβ.le
  have lin : c / (w / (1 + β)) - 1 + β * ((w - c) / (w - w / (1 + β)) - 1) = 0 := by
    have h1 : (1 + β) ≠ 0 := by linarith
    have h2 : w ≠ 0 := hw.ne'
    have h3 : β ≠ 0 := hβ.ne'
    rw [show w - w / (1 + β) = w * β / (1 + β) by field_simp; ring]
    field_simp
    ring
  nlinarith

/-- **(140), first part**: for ANY portfolio (with positive returns in every state), the young
consume `w/(1 + β)` and save `s^Y = βw/(1 + β)`; this is the unique optimal saving. -/
theorem young_consumption_optimal {β R w : ℝ} {p Rt : S → ℝ} (hp : IsPMF p) (hβ : 0 < β)
    (hw : 0 < w) {x : ℝ} (hR : ∀ s, 0 < portfolioReturn R Rt x s) {c : ℝ} (hc0 : 0 < c)
    (hc1 : c < w) (hne : c ≠ w / (1 + β)) :
    lifetimeUtility β R w p Rt c x < lifetimeUtility β R w p Rt (w / (1 + β)) x := by
  have hc' : w / (1 + β) < w := by rw [div_lt_iff₀ (by linarith)]; nlinarith
  rw [lifetimeUtility_eq hp hc1 hR, lifetimeUtility_eq hp hc' hR]
  linarith [saving_lt hβ hw hc0 hc1 hne]

/-- The expected log portfolio return, `g(x) = E log(x R + (1 − x) R̃)`. -/
noncomputable def expLogReturn (R : ℝ) (p Rt : S → ℝ) (x : ℝ) : ℝ :=
  ∑ s, p s * Real.log (portfolioReturn R Rt x s)

/-- **Sufficiency**: if the riskless rate is the harmonic mean of risky returns,
`(1 + r) E[1/(1 + r̃)] = 1`, then zero bond holdings (`x = 0`) are optimal. -/
theorem expLogReturn_le_zero {R : ℝ} {p Rt : S → ℝ} (hp : IsPMF p) (hRt : ∀ s, 0 < Rt s)
    (hharm : R * ∑ s, p s / Rt s = 1) {x : ℝ} (hR : ∀ s, 0 < portfolioReturn R Rt x s) :
    expLogReturn R p Rt x ≤ expLogReturn R p Rt 0 := by
  have key : ∀ s, p s * Real.log (portfolioReturn R Rt x s) ≤
      p s * Real.log (Rt s) + x * (R * (p s / Rt s) - p s) := by
    intro s
    have l := Real.log_le_sub_one_of_pos (div_pos (hR s) (hRt s))
    rw [Real.log_div (hR s).ne' (hRt s).ne'] at l
    have := mul_le_mul_of_nonneg_left l (hp.nonneg s)
    have e : p s * (portfolioReturn R Rt x s / Rt s - 1) = x * (R * (p s / Rt s) - p s) := by
      have := (hRt s).ne'
      simp only [portfolioReturn]; field_simp; ring
    linarith
  calc expLogReturn R p Rt x ≤ ∑ s, (p s * Real.log (Rt s) + x * (R * (p s / Rt s) - p s)) :=
        Finset.sum_le_sum fun s _ => key s
    _ = expLogReturn R p Rt 0 := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib, ← Finset.mul_sum,
          hharm, hp.sum_one, sub_self, mul_zero, add_zero]
        simp [expLogReturn, portfolioReturn]

/-- Joint optimality in (139)–(140): under the harmonic-mean riskless rate, `(c, x) =
(w/(1 + β), 0)` maximises lifetime utility over all feasible choices. -/
theorem young_optimum {β R w : ℝ} {p Rt : S → ℝ} (hp : IsPMF p) (hβ : 0 < β) (hw : 0 < w)
    (hRt : ∀ s, 0 < Rt s) (hharm : R * ∑ s, p s / Rt s = 1) {c x : ℝ} (hc0 : 0 < c)
    (hc1 : c < w) (hR : ∀ s, 0 < portfolioReturn R Rt x s) :
    lifetimeUtility β R w p Rt c x ≤ lifetimeUtility β R w p Rt (w / (1 + β)) 0 := by
  have hR0 : ∀ s, 0 < portfolioReturn R Rt 0 s := fun s => by simp [portfolioReturn, hRt s]
  have hc' : w / (1 + β) < w := by rw [div_lt_iff₀ (by linarith)]; nlinarith
  rw [lifetimeUtility_eq hp hc1 hR, lifetimeUtility_eq hp hc' hR0]
  have h1 := expLogReturn_le_zero hp hRt hharm hR
  simp only [expLogReturn] at h1
  rcases eq_or_ne c (w / (1 + β)) with h | h
  · subst h; nlinarith
  · nlinarith [saving_lt hβ hw hc0 hc1 h]

/-- **Necessity**: if zero bond holdings are optimal (bond market clearing in the symmetric
equilibrium, O&R p. 511), the riskless rate must be the harmonic mean,
`1 + r = 1/E[1/(1 + r̃)]`. -/
theorem harmonic_of_zero_optimal {R : ℝ} {p Rt : S → ℝ} (hp : IsPMF p) (hRt : ∀ s, 0 < Rt s)
    (hopt : ∀ x, (∀ s, 0 < portfolioReturn R Rt x s) →
      expLogReturn R p Rt x ≤ expLogReturn R p Rt 0) :
    R * ∑ s, p s / Rt s = 1 := by
  have hderiv : HasDerivAt (expLogReturn R p Rt) (∑ s, p s * ((R - Rt s) / Rt s)) 0 := by
    have : ∀ s ∈ (Finset.univ : Finset S), HasDerivAt
        (fun x => p s * Real.log (portfolioReturn R Rt x s)) (p s * ((R - Rt s) / Rt s)) 0 := by
      intro s _
      have hfun : ∀ x, portfolioReturn R Rt x s = (R - Rt s) * x + Rt s := fun x => by
        simp only [portfolioReturn]; ring
      have hl : HasDerivAt (fun x => (R - Rt s) * x + Rt s) (R - Rt s) 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).const_mul (R - Rt s)).add_const (Rt s)
      have h2 := (hl.log (by simp [(hRt s).ne'])).const_mul (p s)
      simp only [hfun]
      simpa using h2
    have h3 := HasDerivAt.fun_sum this
    exact h3
  have hloc : IsLocalMax (expLogReturn R p Rt) 0 := by
    have hev : ∀ᶠ x in 𝓝 (0 : ℝ), ∀ s, 0 < portfolioReturn R Rt x s := by
      rw [Filter.eventually_all]
      intro s
      have hc : Continuous fun x => portfolioReturn R Rt x s := by
        simp only [portfolioReturn]; fun_prop
      exact hc.continuousAt.eventually (lt_mem_nhds (by simp [portfolioReturn, hRt s]))
    filter_upwards [hev] with x hx
    exact hopt x hx
  have h0 := hloc.hasDerivAt_eq_zero hderiv
  have e : ∑ s, p s * ((R - Rt s) / Rt s) = R * ∑ s, p s / Rt s - ∑ s, p s := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun s _ => by field_simp [(hRt s).ne']
  rw [e, hp.sum_one] at h0
  linarith

/-- The equilibrium riskless gross rate `1/E[1/(1 + r̃)]` is at most the mean risky gross return
`E[1 + r̃]` (harmonic ≤ arithmetic mean): `E[1 + r̃] · E[1/(1 + r̃)] ≥ 1`. -/
theorem mean_mul_harmonic_ge_one {p Rt : S → ℝ} (hp : IsPMF p) (hRt : ∀ s, 0 < Rt s) :
    1 ≤ (∑ s, p s * Rt s) * ∑ s, p s / Rt s := by
  rw [Finset.sum_mul_sum]
  have hsym : ∑ i, ∑ j, p i * Rt i * (p j / Rt j) = ∑ i, ∑ j, p j * Rt j * (p i / Rt i) :=
    Finset.sum_comm
  have hterm : ∀ i j, 2 * (p i * p j) ≤ p i * Rt i * (p j / Rt j) + p j * Rt j * (p i / Rt i) := by
    intro i j
    have hi := hRt i
    have hj := hRt j
    have e : p i * Rt i * (p j / Rt j) + p j * Rt j * (p i / Rt i) - 2 * (p i * p j) =
        p i * p j * ((Rt i - Rt j) ^ 2 / (Rt i * Rt j)) := by
      field_simp; ring
    have : 0 ≤ p i * p j * ((Rt i - Rt j) ^ 2 / (Rt i * Rt j)) :=
      mul_nonneg (mul_nonneg (hp.nonneg i) (hp.nonneg j)) (by positivity)
    linarith
  have hone : ∑ i, ∑ j, p i * p j = 1 := by
    rw [← Finset.sum_mul_sum, hp.sum_one, one_mul]
  have h2 : 2 * ∑ i, ∑ j, p i * p j ≤ ∑ i, ∑ j, p i * Rt i * (p j / Rt j) +
      ∑ i, ∑ j, p j * Rt j * (p i / Rt i) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum fun j _ => hterm i j
  rw [hone, ← hsym] at h2
  linarith

/-- (137): the wage is the marginal product of labour, `∂(A K^α L^{1−α})/∂L = (1 − α) A k^α`
with `k = K/L`. -/
theorem hasDerivAt_wage {α a K L : ℝ} (hK : 0 < K) (hL : 0 < L) :
    HasDerivAt (fun L => a * K ^ α * L ^ (1 - α)) ((1 - α) * a * (K / L) ^ α) L := by
  have h := (Real.hasDerivAt_rpow_const (p := 1 - α) (Or.inl hL.ne')).const_mul (a * K ^ α)
  convert h using 1
  rw [Real.div_rpow hK.le hL.le, show (1 - α - 1) = -α by ring, Real.rpow_neg hL.le]
  field_simp

/-- **(141)**: with saving `s^Y = βw/(1 + β)` (140), aggregate capital `K_{t+1} = L_t s^Y_t`,
labour `L_{t+1} = (1 + n)L_t` and wage `w_t = (1 − α) A_t k_t^α`, capital per young worker obeys
`k_{t+1} = β(1 − α) A_t k_t^α / ((1 + β)(1 + n))`. -/
theorem olg_capital_accumulation {α β n A k w L L' K' : ℝ} (hL : 0 < L) (hn : 0 < 1 + n)
    (hw : w = (1 - α) * A * k ^ α) (hK' : K' = L * (β * w / (1 + β))) (hL' : L' = (1 + n) * L)
    (hβ : 0 < 1 + β) :
    K' / L' = β * (1 - α) * A * k ^ α / ((1 + β) * (1 + n)) := by
  rw [hK', hL', hw]
  field_simp

/-- **(142)–(143)**: in logs, `k_{t+1} = log[β(1 − α)/((1 + β)(1 + n))] + α k_t + a_t`, and log
output `y_t = a_t + α k_t` obeys `y_{t+1} = χ₀ + α y_t + a_{t+1}` with
`χ₀ = α log[β(1 − α)/((1 + β)(1 + n))]`: isomorphic to (110). -/
theorem olg_log_dynamics {α β n : ℝ} (hα1 : α < 1) (hβ : 0 < β) (hn : 0 < 1 + n)
    {A : ℕ → ℝ} (hA : ∀ t, 0 < A t) {k : ℕ → ℝ} (hk0 : 0 < k 0)
    (hk : ∀ t, k (t + 1) = β * (1 - α) * A t * k t ^ α / ((1 + β) * (1 + n))) (t : ℕ) :
    Real.log (k (t + 1)) = Real.log (β * (1 - α) / ((1 + β) * (1 + n))) + α * Real.log (k t) +
        Real.log (A t) ∧
      Real.log (A (t + 1) * k (t + 1) ^ α) =
        α * Real.log (β * (1 - α) / ((1 + β) * (1 + n))) +
          α * Real.log (A t * k t ^ α) + Real.log (A (t + 1)) := by
  have hc : 0 < β * (1 - α) / ((1 + β) * (1 + n)) :=
    div_pos (mul_pos hβ (by linarith)) (mul_pos (by linarith) hn)
  have hpos : ∀ t, 0 < k t := by
    intro t
    induction t with
    | zero => exact hk0
    | succ t ih =>
      rw [hk]
      exact div_pos (mul_pos (mul_pos (mul_pos hβ (by linarith)) (hA t))
        (Real.rpow_pos_of_pos ih α)) (mul_pos (by linarith) hn)
  have hform : k (t + 1) = β * (1 - α) / ((1 + β) * (1 + n)) * (A t * k t ^ α) := by
    rw [hk]; ring
  have hkt := hpos t
  have h1 : Real.log (k (t + 1)) = Real.log (β * (1 - α) / ((1 + β) * (1 + n))) +
      α * Real.log (k t) + Real.log (A t) := by
    rw [hform, Real.log_mul hc.ne' (mul_pos (hA t) (Real.rpow_pos_of_pos hkt α)).ne',
      Real.log_mul (hA t).ne' (Real.rpow_pos_of_pos hkt α).ne', Real.log_rpow hkt]
    ring
  refine ⟨h1, ?_⟩
  rw [Real.log_mul (hA (t + 1)).ne' (Real.rpow_pos_of_pos (hpos (t + 1)) α).ne',
    Real.log_rpow (hpos (t + 1)), h1,
    Real.log_mul (hA t).ne' (Real.rpow_pos_of_pos hkt α).ne', Real.log_rpow hkt]
  ring

end StochasticOLG

end ObstfeldRogoff.GlobalGrowth.BrockMirman
