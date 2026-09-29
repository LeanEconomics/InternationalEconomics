/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

/-!
# Pegs, floats and the optimal exchange-rate feedback rule (Poole)

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §9.4.1,
pp. 631–632, and Exercise 3, pp. 657–658.

The stochastic small open economy of Exercise 3 (all of `p*`, `i*`, `ȳ`, `q̄` normalised to 0):
* UIP `i_{t+1} = E_t e_{t+1} − e_t`;
* Lucas supply `y_t = θ (p_t − E_{t−1} p_t)`;
* goods demand `y_t = δ (e_t − p_t) + ε_t`;
* money market `m_t − p_t = −η i_{t+1} + φ y_t + v_t`.

**Stochastic structure.** The shocks `(ε_t, v_t)` are iid over a finite state space `S`
with probabilities `prob`; the only moment assumptions used are `E ε = E v = 0` and
`E ε v = 0` (the book's normality and independence are used only through these).
A history is a list of realised states, newest first; every endogenous variable is a
function of the history (an event tree). `E_{t−1}` at the node `h` is the average over the
next state `s`, and `E_t` at the node `s :: h` averages over the state after that. So
the equilibrium concept is the full history-dependent rational-expectations equilibrium,
with no minimal-state-variable restriction imposed a priori.

**No-bubble condition.** The only selection device is that the price level is bounded
on the tree (`Bounded p`).

Main results.
* Under the feedback rule `m − m̄ = Φ (e − ē)` (with `ē = m̄`), the expected price level
  obeys `E_{t−1} x_{t+1} = λ x_t` with `λ = (η + 1 − Φ)/η`. On a finite event tree a
  bounded solution of this is identically zero once `|λ| > 1`, which holds exactly when
  `Φ < 1` or `Φ > 1 + 2η`. In that region the equilibrium is unique among bounded ones and
  output is `y = θ ((η − Φ) ε − δ v)/((η − Φ)(θ + δ) + δ (1 + φ θ))`.
* For `1 < Φ < 1 + 2η` there are bounded sunspot equilibria with different output.
* Float (`Φ = 0`, part (a)), peg (part (b)), the Poole ranking (part (c)).
* Part (d): with `u = η − Φ` the conditional output variance is
  `θ² (u² σ_ε² + δ² σ_v²)/(u (θ + δ) + δ (1 + φ θ))²`. Cauchy–Schwarz gives its exact
  global minimum and the unique minimiser `u* = (θ + δ) δ σ_v²/((1 + φ θ) σ_ε²)`, so
  `Φ* = η − u* < η`. The peg is only the limit `Φ → −∞`: the book's `Φ → ∞` (p. 632) and
  "between 0 and ∞" (Ex. 3(d)) have the wrong sign.
-/

namespace ObstfeldRogoff.NominalRigidities.PooleRegimeChoice

open Finset Filter Topology

/-- O&R Exercise 3, p. 657: the structural parameters `θ` (supply slope), `δ` (demand
elasticity to the real exchange rate), `η` (interest semi-elasticity of money demand),
`φ` (income elasticity of money demand), all positive. -/
structure PooleParams where
  θ : ℝ
  δ : ℝ
  η : ℝ
  φ : ℝ
  θ_pos : 0 < θ
  δ_pos : 0 < δ
  η_pos : 0 < η
  φ_pos : 0 < φ

/-- O&R Exercise 3, p. 657: iid shocks on a finite state space. `eps` is the goods-demand
shock `ε`, `v` the money-demand shock; both have mean zero and are uncorrelated. -/
structure PooleShocks (S : Type) [Fintype S] where
  prob : S → ℝ
  eps : S → ℝ
  v : S → ℝ
  prob_nonneg : ∀ s, 0 ≤ prob s
  prob_sum : ∑ s, prob s = 1
  eps_mean : ∑ s, prob s * eps s = 0
  v_mean : ∑ s, prob s * v s = 0
  eps_v_uncorr : ∑ s, prob s * (eps s * v s) = 0

variable {S : Type} [Fintype S]

/-- O&R Exercise 3, p. 657: the expectation of a function of the current state. -/
def expect (Sh : PooleShocks S) (f : S → ℝ) : ℝ := ∑ s, Sh.prob s * f s

/-- O&R Exercise 3, p. 657: the variance `σ_ε²` of the goods-demand shock. -/
def sigE2 (Sh : PooleShocks S) : ℝ := expect Sh fun s => Sh.eps s ^ 2

/-- O&R Exercise 3, p. 657: the variance `σ_v²` of the money-demand shock. -/
def sigV2 (Sh : PooleShocks S) : ℝ := expect Sh fun s => Sh.v s ^ 2

/-- O&R Exercise 3, p. 657: the conditional expectation at the node `h` of a variable on the
event tree, averaging over the next state (`E_{t−1}` of a date-`t` variable). -/
def nodeEx (Sh : PooleShocks S) (f : List S → ℝ) (h : List S) : ℝ :=
  ∑ s, Sh.prob s * f (s :: h)

/-- The no-bubble condition used throughout (O&R p. 658 hint): a variable on the event tree
is bounded. -/
def Bounded (f : List S → ℝ) : Prop := ∃ M, ∀ h, |f h| ≤ M

/-- O&R Exercise 3, p. 657: a rational-expectations equilibrium on the event tree under a
policy relating `(m_t, e_t)`. At every node `s :: h` (current state `s`, past history `h`)
UIP, supply, goods demand, money demand and the policy hold. -/
def IsEqm (P : PooleParams) (Sh : PooleShocks S) (policy : ℝ → ℝ → Prop)
    (p e y m i : List S → ℝ) : Prop :=
  ∀ (s : S) (h : List S),
    i (s :: h) = nodeEx Sh e (s :: h) - e (s :: h) ∧
    y (s :: h) = P.θ * (p (s :: h) - nodeEx Sh p h) ∧
    y (s :: h) = P.δ * (e (s :: h) - p (s :: h)) + Sh.eps s ∧
    m (s :: h) - p (s :: h) = -P.η * i (s :: h) + P.φ * y (s :: h) + Sh.v s ∧
    policy (m (s :: h)) (e (s :: h))

/-- O&R Exercise 3(a), p. 658: the fixed money supply `m_t = m̄`. -/
def floatPolicy (mbar : ℝ) : ℝ → ℝ → Prop := fun m _ => m = mbar

/-- O&R Exercise 3(b), p. 658: the peg `e_t = ē = m̄`, money adjusting. -/
def pegPolicy (mbar : ℝ) : ℝ → ℝ → Prop := fun _ e => e = mbar

/-- O&R p. 632 and Exercise 3(d): the feedback rule `m_t − m̄ = Φ (e_t − ē)` with `ē = m̄`. -/
def feedbackPolicy (mbar Φ : ℝ) : ℝ → ℝ → Prop := fun m e => m = mbar + Φ * (e - mbar)

/-- O&R Exercise 3(d): the denominator `u (θ + δ) + δ (1 + φ θ)` of the equilibrium output
formula, as a function of `u = η − Φ`. -/
def den (P : PooleParams) (u : ℝ) : ℝ := u * (P.θ + P.δ) + P.δ * (1 + P.φ * P.θ)

/-- O&R Exercise 3(d): equilibrium output in state `s` under the rule `Φ`. -/
noncomputable def outputMSV (P : PooleParams) (Sh : PooleShocks S) (Φ : ℝ) (s : S) : ℝ :=
  P.θ * ((P.η - Φ) * Sh.eps s - P.δ * Sh.v s) / den P (P.η - Φ)

/-- O&R Exercise 3(d): equilibrium price level in state `s` under the rule `Φ`. -/
noncomputable def pMSV (P : PooleParams) (Sh : PooleShocks S) (mbar Φ : ℝ) (s : S) : ℝ :=
  mbar + outputMSV P Sh Φ s / P.θ

/-- O&R Exercise 3(d): equilibrium exchange rate in state `s` under the rule `Φ`. -/
noncomputable def eMSV (P : PooleParams) (Sh : PooleShocks S) (mbar Φ : ℝ) (s : S) : ℝ :=
  pMSV P Sh mbar Φ s + (outputMSV P Sh Φ s - Sh.eps s) / P.δ

/-- O&R Exercise 3(d): equilibrium money supply in state `s` under the rule `Φ`. -/
noncomputable def mMSV (P : PooleParams) (Sh : PooleShocks S) (mbar Φ : ℝ) (s : S) : ℝ :=
  mbar + Φ * (eMSV P Sh mbar Φ s - mbar)

/-- O&R Exercise 3(d): equilibrium nominal interest rate in state `s` under the rule `Φ`. -/
noncomputable def iMSV (P : PooleParams) (Sh : PooleShocks S) (mbar Φ : ℝ) (s : S) : ℝ :=
  mbar - eMSV P Sh mbar Φ s

/-- A variable on the event tree that depends only on the current state (value `d` at the
root, before any shock). Used to build the stationary equilibria of O&R Exercise 3. -/
def onHead (d : ℝ) (g : S → ℝ) : List S → ℝ
  | [] => d
  | s :: _ => g s

/-! ### Expectation algebra -/

/-- Linearity of the expectation (O&R Exercise 3 background). -/
theorem expect_add (Sh : PooleShocks S) (f g : S → ℝ) :
    expect Sh (fun s => f s + g s) = expect Sh f + expect Sh g := by
  unfold expect
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun s _ => by ring

/-- Linearity of the expectation (O&R Exercise 3 background). -/
theorem expect_sub (Sh : PooleShocks S) (f g : S → ℝ) :
    expect Sh (fun s => f s - g s) = expect Sh f - expect Sh g := by
  unfold expect
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun s _ => by ring

/-- Homogeneity of the expectation (O&R Exercise 3 background). -/
theorem expect_const_mul (Sh : PooleShocks S) (c : ℝ) (f : S → ℝ) :
    expect Sh (fun s => c * f s) = c * expect Sh f := by
  unfold expect
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun s _ => by ring

/-- Division by a constant commutes with the expectation (O&R Exercise 3 background). -/
theorem expect_div_const (Sh : PooleShocks S) (c : ℝ) (f : S → ℝ) :
    expect Sh (fun s => f s / c) = expect Sh f / c := by
  unfold expect
  rw [div_eq_mul_inv, Finset.sum_mul]
  exact Finset.sum_congr rfl fun s _ => by ring

/-- The expectation of a constant (O&R Exercise 3 background). -/
theorem expect_const (Sh : PooleShocks S) (c : ℝ) : expect Sh (fun _ => c) = c := by
  unfold expect
  rw [← Finset.sum_mul, Sh.prob_sum, one_mul]

/-- `E ε = 0` (O&R Exercise 3, p. 657). -/
theorem expect_eps (Sh : PooleShocks S) : expect Sh (fun s => Sh.eps s) = 0 := Sh.eps_mean

/-- `E v = 0` (O&R Exercise 3, p. 657). -/
theorem expect_v (Sh : PooleShocks S) : expect Sh (fun s => Sh.v s) = 0 := Sh.v_mean

/-- The node expectation is the expectation over the next state (O&R Exercise 3). -/
theorem nodeEx_eq_expect (Sh : PooleShocks S) (f : List S → ℝ) (h : List S) :
    nodeEx Sh f h = expect Sh (fun s => f (s :: h)) := rfl

/-- A bounded variable has a bounded conditional expectation (O&R Exercise 3). -/
theorem abs_nodeEx_le (Sh : PooleShocks S) (f : List S → ℝ) (M : ℝ) (hM : ∀ g, |f g| ≤ M)
    (h : List S) : |nodeEx Sh f h| ≤ M := by
  unfold nodeEx
  calc |∑ s, Sh.prob s * f (s :: h)| ≤ ∑ s, |Sh.prob s * f (s :: h)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s, Sh.prob s * M := by
        refine Finset.sum_le_sum fun s _ => ?_
        rw [abs_mul, abs_of_nonneg (Sh.prob_nonneg s)]
        exact mul_le_mul_of_nonneg_left (hM _) (Sh.prob_nonneg s)
    _ = M := by rw [← Finset.sum_mul, Sh.prob_sum, one_mul]

/-- The node expectation of a variable depending only on the current state (O&R Ex. 3). -/
theorem nodeEx_onHead (Sh : PooleShocks S) (d : ℝ) (g : S → ℝ) (h : List S) :
    nodeEx Sh (onHead d g) h = expect Sh g := rfl

omit [Fintype S] in
/-- A variable depending only on the current state is bounded (O&R Exercise 3). -/
theorem bounded_onHead [Finite S] (d : ℝ) (g : S → ℝ) : Bounded (onHead d g) := by
  have := Fintype.ofFinite S
  refine ⟨|d| + ∑ s, |g s|, fun h => ?_⟩
  have hsum : 0 ≤ ∑ s, |g s| := Finset.sum_nonneg fun s _ => abs_nonneg _
  cases h with
  | nil => simp only [onHead]; linarith
  | cons s _ =>
    simp only [onHead]
    have := Finset.single_le_sum (f := fun s => |g s|) (fun s _ => abs_nonneg (g s))
      (Finset.mem_univ s)
    linarith [abs_nonneg d]

/-! ### Bounded solutions of the expected-level recursion on the event tree -/

/-- The no-bubble lemma on a finite event tree: a bounded `x` with `E_{t−1} x_{t+1} = λ x_t`
at every node and `|λ| > 1` is identically zero (O&R p. 658; the stochastic counterpart
of the no-bubble argument of §9.2.3). -/
theorem tree_eigen_bounded_zero (Sh : PooleShocks S) (x : List S → ℝ) (lam : ℝ)
    (hlam : 1 < |lam|) (hx : ∀ h, nodeEx Sh x h = lam * x h) (hb : Bounded x) :
    ∀ h, x h = 0 := by
  obtain ⟨M, hM⟩ := hb
  have key : ∀ n : ℕ, ∀ h, |x h| * |lam| ^ n ≤ M := by
    intro n
    induction n with
    | zero => intro h; simpa using hM h
    | succ n ih =>
      intro h
      have hmul : nodeEx Sh (fun g => x g * |lam| ^ n) h = nodeEx Sh x h * |lam| ^ n := by
        unfold nodeEx
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun s _ => by ring
      have hbound := abs_nodeEx_le Sh (fun g => x g * |lam| ^ n) M
        (fun g => by rw [abs_mul, abs_pow, abs_abs]; exact ih g) h
      rw [hmul, hx, abs_mul, abs_mul, abs_pow, abs_abs] at hbound
      calc |x h| * |lam| ^ (n + 1) = |lam| * |x h| * |lam| ^ n := by ring
        _ ≤ M := hbound
  intro h
  by_contra hne
  have hpos : 0 < |x h| := abs_pos.mpr hne
  have ht : Tendsto (fun n : ℕ => |x h| * |lam| ^ n) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt hlam).const_mul_atTop hpos
  obtain ⟨n, hn⟩ := (ht.eventually_gt_atTop M).exists
  exact absurd (key n h) (not_le.mpr hn)

/-- O&R p. 632 / Ex. 3(d): the root `λ = (η + 1 − Φ)/η` of the expected-level recursion is
outside the unit circle exactly when `Φ < 1` or `Φ > 1 + 2η` (the determinacy region). -/
theorem one_lt_abs_lambda_iff {η Φ : ℝ} (hη : 0 < η) :
    1 < |(η + 1 - Φ) / η| ↔ Φ < 1 ∨ 1 + 2 * η < Φ := by
  rw [abs_div, abs_of_pos hη, lt_div_iff₀ hη, one_mul, lt_abs]
  constructor
  · rintro (h | h)
    · left; linarith
    · right; linarith
  · rintro (h | h)
    · left; linarith
    · right; linarith

/-- O&R p. 632 / Ex. 3(d): the root `λ` is strictly inside the unit circle exactly when
`1 < Φ < 1 + 2η` (the indeterminacy region). -/
theorem abs_lambda_lt_one_iff {η Φ : ℝ} (hη : 0 < η) :
    |(η + 1 - Φ) / η| < 1 ↔ 1 < Φ ∧ Φ < 1 + 2 * η := by
  rw [abs_div, abs_of_pos hη, div_lt_iff₀ hη, one_mul, abs_lt]
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> linarith
  · rintro ⟨h1, h2⟩; constructor <;> linarith

/-! ### Expected levels in any equilibrium -/

/-- O&R Exercise 3: in any equilibrium (any policy) expected output is zero,
`E_{t−1} y_t = 0`, because output responds only to price surprises. -/
theorem eqm_nodeEx_y {P : PooleParams} {Sh : PooleShocks S} {policy : ℝ → ℝ → Prop}
    {p e y m i : List S → ℝ} (hE : IsEqm P Sh policy p e y m i) (h : List S) :
    nodeEx Sh y h = 0 := by
  have hf : (fun s => y (s :: h)) = fun s => P.θ * (p (s :: h) - nodeEx Sh p h) :=
    funext fun s => (hE s h).2.1
  have h1 : expect Sh (fun s => y (s :: h)) =
      expect Sh (fun s => P.θ * (p (s :: h) - nodeEx Sh p h)) := congrArg _ hf
  simp only [expect_const_mul, expect_sub, expect_const] at h1
  rw [nodeEx_eq_expect, h1, nodeEx_eq_expect, sub_self, mul_zero]

/-- O&R Exercise 3: in any equilibrium (any policy) `E_{t−1} e_t = E_{t−1} p_t`, i.e. the
expected real exchange rate is at its (normalised) long-run value 0. -/
theorem eqm_nodeEx_e {P : PooleParams} {Sh : PooleShocks S} {policy : ℝ → ℝ → Prop}
    {p e y m i : List S → ℝ} (hE : IsEqm P Sh policy p e y m i) (h : List S) :
    nodeEx Sh e h = nodeEx Sh p h := by
  have hf : (fun s => y (s :: h)) =
      fun s => P.δ * (e (s :: h) - p (s :: h)) + Sh.eps s :=
    funext fun s => (hE s h).2.2.1
  have h1 : expect Sh (fun s => y (s :: h)) =
      expect Sh (fun s => P.δ * (e (s :: h) - p (s :: h)) + Sh.eps s) := congrArg _ hf
  simp only [expect_add, expect_const_mul, expect_sub, expect_eps] at h1
  have hy : expect Sh (fun s => y (s :: h)) = 0 := eqm_nodeEx_y hE h
  rw [hy, add_zero] at h1
  have hd : P.δ ≠ 0 := P.δ_pos.ne'
  have h2 : expect Sh (fun s => e (s :: h)) - expect Sh (fun s => p (s :: h)) = 0 := by
    rcases mul_eq_zero.mp h1.symm with h3 | h3
    · exact absurd h3 hd
    · exact h3
  rw [nodeEx_eq_expect, nodeEx_eq_expect]
  linarith

/-- O&R p. 632 / Ex. 3(d): under the feedback rule the expected price level
`c_h = E_{t−1} p_t` satisfies `η (E_{t−1} c_{t+1} − m̄) = (η + 1 − Φ)(c_t − m̄)`. -/
theorem feedback_level_recursion {P : PooleParams} {Sh : PooleShocks S} {mbar Φ : ℝ}
    {p e y m i : List S → ℝ} (hE : IsEqm P Sh (feedbackPolicy mbar Φ) p e y m i)
    (h : List S) :
    P.η * (nodeEx Sh (nodeEx Sh p) h - mbar) = (P.η + 1 - Φ) * (nodeEx Sh p h - mbar) := by
  have hmon : (fun s => m (s :: h) - p (s :: h)) = fun s =>
      -P.η * (nodeEx Sh p (s :: h) - e (s :: h)) + P.φ * y (s :: h) + Sh.v s := by
    funext s
    rw [(hE s h).2.2.2.1, (hE s h).1, eqm_nodeEx_e hE (s :: h)]
  have hpol : (fun s => m (s :: h)) = fun s => mbar + Φ * (e (s :: h) - mbar) :=
    funext fun s => (hE s h).2.2.2.2
  have h1 : expect Sh (fun s => m (s :: h) - p (s :: h)) = expect Sh (fun s =>
      -P.η * (nodeEx Sh p (s :: h) - e (s :: h)) + P.φ * y (s :: h) + Sh.v s) :=
    congrArg _ hmon
  have h2 : expect Sh (fun s => m (s :: h)) =
      expect Sh (fun s => mbar + Φ * (e (s :: h) - mbar)) := congrArg _ hpol
  simp only [expect_add, expect_sub, expect_const_mul, expect_const, expect_v] at h1 h2
  have hy : expect Sh (fun s => y (s :: h)) = 0 := eqm_nodeEx_y hE h
  have he : expect Sh (fun s => e (s :: h)) = expect Sh (fun s => p (s :: h)) :=
    eqm_nodeEx_e hE h
  rw [hy, he] at h1
  rw [he] at h2
  rw [nodeEx_eq_expect Sh (nodeEx Sh p), nodeEx_eq_expect Sh p]
  linear_combination h1 - h2

/-- O&R p. 632 / Ex. 3(d): in the determinacy region `Φ < 1` or `Φ > 1 + 2η`, every
equilibrium with a bounded price level has `E_{t−1} p_t = m̄` at every node. -/
theorem feedback_expected_price_eq {P : PooleParams} {Sh : PooleShocks S} {mbar Φ : ℝ}
    (hdet : Φ < 1 ∨ 1 + 2 * P.η < Φ) {p e y m i : List S → ℝ}
    (hE : IsEqm P Sh (feedbackPolicy mbar Φ) p e y m i) (hb : Bounded p) (h : List S) :
    nodeEx Sh p h = mbar := by
  have hη := P.η_pos
  have hx : ∀ g, nodeEx Sh (fun g' => nodeEx Sh p g' - mbar) g =
      (P.η + 1 - Φ) / P.η * (nodeEx Sh p g - mbar) := by
    intro g
    have hr := feedback_level_recursion hE g
    have hsub : nodeEx Sh (fun g' => nodeEx Sh p g' - mbar) g =
        nodeEx Sh (nodeEx Sh p) g - mbar := by
      rw [nodeEx_eq_expect, expect_sub, expect_const]
      rfl
    rw [hsub]
    field_simp
    linear_combination hr
  obtain ⟨M, hM⟩ := hb
  have hbx : Bounded (fun g => nodeEx Sh p g - mbar) := by
    refine ⟨M + |mbar|, fun g => ?_⟩
    have := abs_nodeEx_le Sh p M hM g
    calc |nodeEx Sh p g - mbar| ≤ |nodeEx Sh p g| + |mbar| := abs_sub _ _
      _ ≤ M + |mbar| := by linarith
  have := tree_eigen_bounded_zero Sh _ _ ((one_lt_abs_lambda_iff hη).mpr hdet) hx hbx h
  linarith

/-- O&R Exercise 3(d): the reduced form at one node. Given the equilibrium equations at
`s :: h`, output satisfies `y · den = θ ((η − Φ) ε − δ v + δ w)`, where
`w = η (E_t e_{t+1} − m̄) − (η + 1 − Φ)(E_{t−1} p_t − m̄)` is the expectation-revision
(sunspot) term. -/
theorem feedback_node_reduced_form (P : PooleParams) (mbar Φ ε v y p e m i X c : ℝ)
    (hi : i = X - e) (hs : y = P.θ * (p - c)) (hg : y = P.δ * (e - p) + ε)
    (hm : m - p = -P.η * i + P.φ * y + v) (hpol : m = mbar + Φ * (e - mbar)) :
    y * den P (P.η - Φ) = P.θ * ((P.η - Φ) * ε - P.δ * v +
      P.δ * (P.η * (X - mbar) - (P.η + 1 - Φ) * (c - mbar))) := by
  unfold den
  linear_combination (P.δ * (P.η - Φ + 1)) * hs + (P.θ * (P.η - Φ)) * hg +
    (-P.θ * P.δ) * hm + (P.θ * P.δ) * hpol + (P.θ * P.δ * P.η) * hi

/-- O&R Exercise 3(d), uniqueness: in the determinacy region and away from the pole
`den = 0`, every equilibrium with a bounded price level coincides at every node with the
stationary solution `(pMSV, eMSV, outputMSV, mMSV, iMSV)` of the current state. -/
theorem feedback_eqm_unique {P : PooleParams} {Sh : PooleShocks S} {mbar Φ : ℝ}
    (hdet : Φ < 1 ∨ 1 + 2 * P.η < Φ) (hden : den P (P.η - Φ) ≠ 0)
    {p e y m i : List S → ℝ} (hE : IsEqm P Sh (feedbackPolicy mbar Φ) p e y m i)
    (hb : Bounded p) (s : S) (h : List S) :
    y (s :: h) = outputMSV P Sh Φ s ∧ p (s :: h) = pMSV P Sh mbar Φ s ∧
      e (s :: h) = eMSV P Sh mbar Φ s ∧ m (s :: h) = mMSV P Sh mbar Φ s ∧
      i (s :: h) = iMSV P Sh mbar Φ s := by
  obtain ⟨hi, hs, hg, hm, hpol⟩ := hE s h
  have hc : nodeEx Sh p h = mbar := feedback_expected_price_eq hdet hE hb h
  have hX : nodeEx Sh e (s :: h) = mbar := by
    rw [eqm_nodeEx_e hE (s :: h)]
    exact feedback_expected_price_eq hdet hE hb (s :: h)
  have hred := feedback_node_reduced_form P mbar Φ (Sh.eps s) (Sh.v s) _ _ _ _ _ _ _
    hi hs hg hm hpol
  rw [hX, hc] at hred
  have hy : y (s :: h) = outputMSV P Sh Φ s := by
    unfold outputMSV
    rw [eq_div_iff hden, hred]
    ring
  have hθ := P.θ_pos.ne'
  have hδ := P.δ_pos.ne'
  have hp : p (s :: h) = pMSV P Sh mbar Φ s := by
    unfold pMSV
    rw [← hy, hs, hc]
    field_simp
    ring
  have he : e (s :: h) = eMSV P Sh mbar Φ s := by
    unfold eMSV
    rw [← hp, ← hy, hg]
    field_simp
    ring
  refine ⟨hy, hp, he, ?_, ?_⟩
  · unfold mMSV
    rw [← he]
    exact hpol
  · unfold iMSV
    rw [← he, hi, hX]

/-- O&R Exercise 3(d): the stationary solution has zero-mean output. -/
theorem expect_outputMSV (P : PooleParams) (Sh : PooleShocks S) (Φ : ℝ) :
    expect Sh (outputMSV P Sh Φ) = 0 := by
  have : outputMSV P Sh Φ = fun s =>
      (P.θ * (P.η - Φ) / den P (P.η - Φ)) * Sh.eps s +
        (-(P.θ * P.δ) / den P (P.η - Φ)) * Sh.v s := by
    funext s
    unfold outputMSV
    ring
  rw [this, expect_add, expect_const_mul, expect_const_mul, expect_eps, expect_v]
  ring

/-- O&R Exercise 3(d): the stationary solution has `E p = m̄`. -/
theorem expect_pMSV (P : PooleParams) (Sh : PooleShocks S) (mbar Φ : ℝ) :
    expect Sh (pMSV P Sh mbar Φ) = mbar := by
  have : pMSV P Sh mbar Φ = fun s => mbar + outputMSV P Sh Φ s / P.θ := rfl
  rw [this, expect_add, expect_const, expect_div_const, expect_outputMSV, zero_div, add_zero]

/-- O&R Exercise 3(d): the stationary solution has `E e = m̄`. -/
theorem expect_eMSV (P : PooleParams) (Sh : PooleShocks S) (mbar Φ : ℝ) :
    expect Sh (eMSV P Sh mbar Φ) = mbar := by
  have : eMSV P Sh mbar Φ = fun s =>
      pMSV P Sh mbar Φ s + (outputMSV P Sh Φ s - Sh.eps s) / P.δ := rfl
  rw [this, expect_add, expect_div_const, expect_sub, expect_eps, expect_outputMSV]
  have h2 := expect_pMSV P Sh mbar Φ
  simp only [h2, sub_zero, zero_div, add_zero]

/-- O&R Exercise 3(d), existence: away from the pole the stationary solution, placed on the
event tree, is an equilibrium with bounded variables (whatever `Φ`). -/
theorem feedback_eqm_exists (P : PooleParams) (Sh : PooleShocks S) (mbar Φ : ℝ)
    (hden : den P (P.η - Φ) ≠ 0) :
    IsEqm P Sh (feedbackPolicy mbar Φ) (onHead mbar (pMSV P Sh mbar Φ))
      (onHead mbar (eMSV P Sh mbar Φ)) (onHead 0 (outputMSV P Sh Φ))
      (onHead mbar (mMSV P Sh mbar Φ)) (onHead 0 (iMSV P Sh mbar Φ)) := by
  intro s h
  have hθ := P.θ_pos.ne'
  have hδ := P.δ_pos.ne'
  simp only [onHead, nodeEx_onHead, expect_eMSV, expect_pMSV]
  have hY : outputMSV P Sh Φ s * den P (P.η - Φ) =
      P.θ * ((P.η - Φ) * Sh.eps s - P.δ * Sh.v s) := by
    unfold outputMSV
    exact div_mul_cancel₀ _ hden
  refine ⟨rfl, ?_, ?_, ?_, rfl⟩
  · unfold pMSV
    field_simp
    ring
  · unfold eMSV
    field_simp
    ring
  · unfold iMSV mMSV eMSV pMSV
    unfold den at hY
    field_simp
    linear_combination (-1 : ℝ) * hY

/-! ### Moments of the equilibrium output -/

/-- O&R Exercise 3: `E (α ε + β v)² = α² σ_ε² + β² σ_v²` (uncorrelated shocks). -/
theorem expect_sq_comb (Sh : PooleShocks S) (α β : ℝ) :
    expect Sh (fun s => (α * Sh.eps s + β * Sh.v s) ^ 2) =
      α ^ 2 * sigE2 Sh + β ^ 2 * sigV2 Sh := by
  have hf : (fun s => (α * Sh.eps s + β * Sh.v s) ^ 2) = fun s =>
      α ^ 2 * Sh.eps s ^ 2 + (2 * α * β) * (Sh.eps s * Sh.v s) + β ^ 2 * Sh.v s ^ 2 := by
    funext s
    ring
  have hc : expect Sh (fun s => Sh.eps s * Sh.v s) = 0 := Sh.eps_v_uncorr
  rw [hf, expect_add, expect_add, expect_const_mul, expect_const_mul, expect_const_mul, hc]
  unfold sigE2 sigV2
  ring

/-- O&R Exercise 3(d): the one-period conditional variance of output as a function of
`u = η − Φ`: `θ² (u² σ_ε² + δ² σ_v²)/(u (θ + δ) + δ (1 + φ θ))²`. -/
noncomputable def outputVar (P : PooleParams) (a b u : ℝ) : ℝ :=
  P.θ ^ 2 * (u ^ 2 * a + P.δ ^ 2 * b) / den P u ^ 2

/-- O&R Exercise 3(a): the conditional output variance under the float (`u = η`). -/
noncomputable def floatVar (P : PooleParams) (a b : ℝ) : ℝ := outputVar P a b P.η

/-- O&R Exercise 3(b): the conditional output variance under the peg,
`θ² σ_ε²/(θ + δ)²`. -/
noncomputable def pegVar (P : PooleParams) (a : ℝ) : ℝ := P.θ ^ 2 * a / (P.θ + P.δ) ^ 2

/-- O&R Exercise 3(d): the variance-minimising `u* = (θ + δ) δ σ_v²/((1 + φ θ) σ_ε²)`. -/
noncomputable def optimalU (P : PooleParams) (a b : ℝ) : ℝ :=
  (P.θ + P.δ) * P.δ * b / ((1 + P.φ * P.θ) * a)

/-- O&R Exercise 3(d): the optimal feedback coefficient `Φ* = η − u*`. -/
noncomputable def optimalPhi (P : PooleParams) (a b : ℝ) : ℝ := P.η - optimalU P a b

/-- O&R Exercise 3(d): the minimal conditional output variance
`θ² σ_ε² σ_v²/((θ + δ)² σ_v² + (1 + φ θ)² σ_ε²)`. -/
noncomputable def minVar (P : PooleParams) (a b : ℝ) : ℝ :=
  P.θ ^ 2 * a * b / ((P.θ + P.δ) ^ 2 * b + (1 + P.φ * P.θ) ^ 2 * a)

/-- O&R Exercise 3(d): the stationary output has conditional variance `outputVar`. -/
theorem expect_outputMSV_sq (P : PooleParams) (Sh : PooleShocks S) (Φ : ℝ) :
    expect Sh (fun s => outputMSV P Sh Φ s ^ 2) =
      outputVar P (sigE2 Sh) (sigV2 Sh) (P.η - Φ) := by
  have hf : (fun s => outputMSV P Sh Φ s ^ 2) = fun s =>
      ((P.θ * (P.η - Φ) / den P (P.η - Φ)) * Sh.eps s +
        (-(P.θ * P.δ) / den P (P.η - Φ)) * Sh.v s) ^ 2 := by
    funext s
    unfold outputMSV
    ring
  rw [hf, expect_sq_comb]
  unfold outputVar
  ring

/-- O&R Exercise 3(d): in the determinacy region, in every bounded equilibrium,
`E_{t−1} y_t = 0` and `E_{t−1} y_t² = outputVar (η − Φ)` at every node. -/
theorem feedback_output_moments {P : PooleParams} {Sh : PooleShocks S} {mbar Φ : ℝ}
    (hdet : Φ < 1 ∨ 1 + 2 * P.η < Φ) (hden : den P (P.η - Φ) ≠ 0)
    {p e y m i : List S → ℝ} (hE : IsEqm P Sh (feedbackPolicy mbar Φ) p e y m i)
    (hb : Bounded p) (h : List S) :
    nodeEx Sh y h = 0 ∧
      nodeEx Sh (fun g => y g ^ 2) h = outputVar P (sigE2 Sh) (sigV2 Sh) (P.η - Φ) := by
  refine ⟨eqm_nodeEx_y hE h, ?_⟩
  rw [← expect_outputMSV_sq, nodeEx_eq_expect]
  unfold expect
  exact Finset.sum_congr rfl fun s _ => by
    dsimp only
    rw [(feedback_eqm_unique hdet hden hE hb s h).1]

/-! ### Part (a): the float -/

/-- O&R Exercise 3(a): a fixed money supply is the feedback rule with `Φ = 0`. -/
theorem floatPolicy_eq (mbar : ℝ) : floatPolicy mbar = feedbackPolicy mbar 0 := by
  funext m e
  simp [floatPolicy, feedbackPolicy]

/-- O&R Exercise 3: `den u > 0` for `u ≥ 0`. -/
theorem den_pos (P : PooleParams) {u : ℝ} (hu : 0 ≤ u) : 0 < den P u := by
  unfold den
  have := P.θ_pos
  have := P.δ_pos
  have := P.φ_pos
  positivity

/-- O&R Exercise 3(a): under the float every equilibrium with a bounded price level has
output `y = θ (η ε − δ v)/D₃` with `D₃ = δ (1 + η) + θ (η + φ δ)`, and the hint of the
book holds: `E_t e_{t+1} = E_t p_{t+1} = m̄` at every node. -/
theorem float_eqm_unique {P : PooleParams} {Sh : PooleShocks S} {mbar : ℝ}
    {p e y m i : List S → ℝ} (hE : IsEqm P Sh (floatPolicy mbar) p e y m i)
    (hb : Bounded p) (s : S) (h : List S) :
    y (s :: h) = P.θ * (P.η * Sh.eps s - P.δ * Sh.v s) /
        (P.δ * (1 + P.η) + P.θ * (P.η + P.φ * P.δ)) ∧
      nodeEx Sh e (s :: h) = mbar ∧ nodeEx Sh p (s :: h) = mbar := by
  rw [floatPolicy_eq] at hE
  have hdet : (0 : ℝ) < 1 ∨ 1 + 2 * P.η < 0 := Or.inl one_pos
  have hden : den P (P.η - 0) ≠ 0 := (den_pos P (by linarith [P.η_pos])).ne'
  have hp := feedback_expected_price_eq hdet hE hb (s :: h)
  refine ⟨?_, by rw [eqm_nodeEx_e hE]; exact hp, hp⟩
  rw [(feedback_eqm_unique hdet hden hE hb s h).1]
  unfold outputMSV den
  congr 1 <;> ring

/-- O&R Exercise 3(a): the float's conditional output variance,
`θ² (η² σ_ε² + δ² σ_v²)/D₃²`. -/
theorem floatVar_eq (P : PooleParams) (a b : ℝ) :
    floatVar P a b = P.θ ^ 2 * (P.η ^ 2 * a + P.δ ^ 2 * b) /
      (P.δ * (1 + P.η) + P.θ * (P.η + P.φ * P.δ)) ^ 2 := by
  unfold floatVar outputVar den
  congr 1
  ring

/-- O&R Exercise 3(a): under the float, in every equilibrium with a bounded price level,
`E_{t−1} y_t² = θ² (η² σ_ε² + δ² σ_v²)/D₃²` at every node. -/
theorem float_output_var {P : PooleParams} {Sh : PooleShocks S} {mbar : ℝ}
    {p e y m i : List S → ℝ} (hE : IsEqm P Sh (floatPolicy mbar) p e y m i)
    (hb : Bounded p) (h : List S) :
    nodeEx Sh (fun g => y g ^ 2) h = floatVar P (sigE2 Sh) (sigV2 Sh) := by
  rw [floatPolicy_eq] at hE
  have hden : den P (P.η - 0) ≠ 0 := (den_pos P (by linarith [P.η_pos])).ne'
  have := (feedback_output_moments (Or.inl one_pos) hden hE hb h).2
  rw [sub_zero] at this
  exact this

/-! ### Part (b): the peg -/

/-- O&R Exercise 3(b) and p. 631: under the peg every equilibrium (no boundedness needed)
has `y = θ ε/(θ + δ)`, `p = m̄ + ε/(θ + δ)`, `i = 0` and money
`m = m̄ + (1 + φ θ) ε/(θ + δ) + v`: money-demand shocks are fully accommodated and have no
real effect. -/
theorem peg_eqm_unique {P : PooleParams} {Sh : PooleShocks S} {mbar : ℝ}
    {p e y m i : List S → ℝ} (hE : IsEqm P Sh (pegPolicy mbar) p e y m i)
    (s : S) (h : List S) :
    y (s :: h) = P.θ * Sh.eps s / (P.θ + P.δ) ∧
      p (s :: h) = mbar + Sh.eps s / (P.θ + P.δ) ∧ e (s :: h) = mbar ∧ i (s :: h) = 0 ∧
      m (s :: h) = mbar + (1 + P.φ * P.θ) * Sh.eps s / (P.θ + P.δ) + Sh.v s := by
  have hpeg : ∀ s' h', e (s' :: h') = mbar := fun s' h' => (hE s' h').2.2.2.2
  have hEe : ∀ g, nodeEx Sh e g = mbar := by
    intro g
    rw [nodeEx_eq_expect]
    simp only [hpeg, expect_const]
  have hc : nodeEx Sh p h = mbar := by rw [← eqm_nodeEx_e hE h, hEe]
  obtain ⟨hi, hs, hg, hm, _⟩ := hE s h
  rw [hEe, hpeg] at hi
  rw [hc] at hs
  rw [hpeg] at hg
  have hθδ : P.θ + P.δ ≠ 0 := by linarith [P.θ_pos, P.δ_pos]
  have hy : y (s :: h) = P.θ * Sh.eps s / (P.θ + P.δ) := by
    rw [eq_div_iff hθδ]
    linear_combination P.δ * hs + P.θ * hg
  have hp : p (s :: h) = mbar + Sh.eps s / (P.θ + P.δ) := by
    field_simp
    linear_combination hg - hs
  have hi0 : i (s :: h) = 0 := by rw [hi, sub_self]
  refine ⟨hy, hp, hpeg s h, hi0, ?_⟩
  rw [hi0, hy, hp] at hm
  field_simp
  field_simp at hm
  linear_combination hm

/-- O&R Exercise 3(b): the announced money path is consistent: `E_{t−1} m_t = m̄`. -/
theorem peg_expected_money {P : PooleParams} {Sh : PooleShocks S} {mbar : ℝ}
    {p e y m i : List S → ℝ} (hE : IsEqm P Sh (pegPolicy mbar) p e y m i) (h : List S) :
    nodeEx Sh m h = mbar := by
  have hf : (fun s => m (s :: h)) = fun s =>
      mbar + ((1 + P.φ * P.θ) / (P.θ + P.δ)) * Sh.eps s + Sh.v s := by
    funext s
    rw [(peg_eqm_unique hE s h).2.2.2.2]
    ring
  rw [nodeEx_eq_expect, hf, expect_add, expect_add, expect_const, expect_const_mul, expect_eps,
    expect_v]
  ring

/-- O&R Exercise 3(b), existence: the peg allocation is an equilibrium. -/
theorem peg_eqm_exists (P : PooleParams) (Sh : PooleShocks S) (mbar : ℝ) :
    IsEqm P Sh (pegPolicy mbar) (onHead mbar fun s => mbar + Sh.eps s / (P.θ + P.δ))
      (onHead mbar fun _ => mbar) (onHead 0 fun s => P.θ * Sh.eps s / (P.θ + P.δ))
      (onHead mbar fun s => mbar + (1 + P.φ * P.θ) * Sh.eps s / (P.θ + P.δ) + Sh.v s)
      (onHead 0 fun _ => 0) := by
  intro s h
  have hθδ : P.θ + P.δ ≠ 0 := by linarith [P.θ_pos, P.δ_pos]
  simp only [onHead, nodeEx_onHead, expect_const]
  have hEp : expect Sh (fun s => mbar + Sh.eps s / (P.θ + P.δ)) = mbar := by
    rw [expect_add, expect_const, expect_div_const, expect_eps, zero_div, add_zero]
  rw [hEp]
  refine ⟨by ring, ?_, ?_, ?_, rfl⟩
  · field_simp
    ring
  · field_simp
    ring
  · field_simp
    ring

/-- O&R Exercise 3(b): under the peg `E_{t−1} y_t² = θ² σ_ε²/(θ + δ)²`, independent of
the money-demand variance. -/
theorem peg_output_var {P : PooleParams} {Sh : PooleShocks S} {mbar : ℝ}
    {p e y m i : List S → ℝ} (hE : IsEqm P Sh (pegPolicy mbar) p e y m i) (h : List S) :
    nodeEx Sh (fun g => y g ^ 2) h = pegVar P (sigE2 Sh) := by
  have hf : (fun s => y (s :: h) ^ 2) = fun s =>
      (P.θ / (P.θ + P.δ) * Sh.eps s + 0 * Sh.v s) ^ 2 := by
    funext s
    rw [(peg_eqm_unique hE s h).1]
    ring
  rw [nodeEx_eq_expect, hf, expect_sq_comb]
  unfold pegVar
  rw [div_pow]
  ring

/-! ### Part (c): Poole's comparison -/

/-- O&R Exercise 3(c): `D₃ = den η > η (θ + δ)`. -/
theorem den_eta_gt (P : PooleParams) : P.η * (P.θ + P.δ) < den P P.η := by
  unfold den
  have := P.δ_pos
  have := P.φ_pos
  have := P.θ_pos
  have : 0 < P.δ * (1 + P.φ * P.θ) := by positivity
  linarith

/-- O&R Exercise 3(c): the exact Poole criterion. The peg is at least as good as the float
iff `σ_ε² (D₃² − η² (θ + δ)²) ≤ (θ + δ)² δ² σ_v²`. -/
theorem peg_le_float_iff (P : PooleParams) (a b : ℝ) :
    pegVar P a ≤ floatVar P a b ↔
      a * (den P P.η ^ 2 - P.η ^ 2 * (P.θ + P.δ) ^ 2) ≤ (P.θ + P.δ) ^ 2 * P.δ ^ 2 * b := by
  have hθ := P.θ_pos
  have hA : 0 < P.θ + P.δ := by linarith [P.δ_pos]
  have hD : 0 < den P P.η := den_pos P P.η_pos.le
  unfold pegVar floatVar outputVar
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hθ2 : 0 < P.θ ^ 2 := by positivity
  constructor
  · intro h
    nlinarith
  · intro h
    nlinarith

/-- O&R Exercise 3(c): the peg is strictly better than the float as soon as
`σ_ε²/σ_v²` is below an explicit positive threshold; in particular as `σ_ε²/σ_v² → 0`. -/
theorem peg_lt_float_of_small_ratio (P : PooleParams) :
    ∃ rbar > 0, ∀ a b : ℝ, 0 ≤ a → a < rbar * b → pegVar P a < floatVar P a b := by
  have hθ := P.θ_pos
  have hA : 0 < P.θ + P.δ := by linarith [P.δ_pos]
  have hδ := P.δ_pos
  have hD : 0 < den P P.η := den_pos P P.η_pos.le
  have hgap : 0 < den P P.η ^ 2 - P.η ^ 2 * (P.θ + P.δ) ^ 2 := by
    have h1 := den_eta_gt P
    have h2 : 0 < P.η * (P.θ + P.δ) := mul_pos P.η_pos hA
    nlinarith
  refine ⟨(P.θ + P.δ) ^ 2 * P.δ ^ 2 / (den P P.η ^ 2 - P.η ^ 2 * (P.θ + P.δ) ^ 2),
    by positivity, fun a b ha hab => ?_⟩
  have hkey : a * (den P P.η ^ 2 - P.η ^ 2 * (P.θ + P.δ) ^ 2) <
      (P.θ + P.δ) ^ 2 * P.δ ^ 2 * b := by
    rw [div_mul_eq_mul_div, lt_div_iff₀ hgap] at hab
    linarith
  unfold pegVar floatVar outputVar
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  have hθ2 : 0 < P.θ ^ 2 := by positivity
  nlinarith

/-- O&R Exercise 3(c): with only money-demand shocks (`σ_ε² = 0 < σ_v²`) the peg is
strictly better. -/
theorem peg_lt_float_of_eps_zero (P : PooleParams) {b : ℝ} (hb : 0 < b) :
    pegVar P 0 < floatVar P 0 b := by
  have hD : 0 < den P P.η := den_pos P P.η_pos.le
  have := P.θ_pos
  have := P.δ_pos
  unfold pegVar floatVar outputVar
  simp only [mul_zero, zero_div, zero_add]
  positivity

/-- O&R Exercise 3(c): with only goods-demand shocks (`σ_v² = 0 < σ_ε²`) the float is
strictly better. -/
theorem float_lt_peg_of_v_zero (P : PooleParams) {a : ℝ} (ha : 0 < a) :
    floatVar P a 0 < pegVar P a := by
  have hA : 0 < P.θ + P.δ := by linarith [P.θ_pos, P.δ_pos]
  have hD : 0 < den P P.η := den_pos P P.η_pos.le
  have h1 := den_eta_gt P
  have hθ := P.θ_pos
  unfold pegVar floatVar outputVar
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  have h2 : 0 < P.η * (P.θ + P.δ) := mul_pos P.η_pos hA
  have h3 : (P.η * (P.θ + P.δ)) ^ 2 < den P P.η ^ 2 := by nlinarith
  have hθ2 : 0 < P.θ ^ 2 := by positivity
  have h4 := mul_lt_mul_of_pos_left h3 (mul_pos hθ2 ha)
  nlinarith [h4]

/-! ### Part (d): the optimal feedback rule -/

/-- O&R Exercise 3(d), the Cauchy–Schwarz identity behind the optimum:
`(u² a + δ² b)((θ+δ)² b + (1+φθ)² a) − a b den(u)² = (u a (1+φθ) − δ b (θ+δ))²`. -/
theorem optimum_identity (P : PooleParams) (a b u : ℝ) :
    (u ^ 2 * a + P.δ ^ 2 * b) * ((P.θ + P.δ) ^ 2 * b + (1 + P.φ * P.θ) ^ 2 * a) -
        a * b * den P u ^ 2 =
      (u * a * (1 + P.φ * P.θ) - P.δ * b * (P.θ + P.δ)) ^ 2 := by
  unfold den
  ring

/-- O&R Exercise 3(d): for `σ_ε² > 0`, `σ_v² ≥ 0`, every admissible rule (away from the pole)
has conditional output variance at least `minVar`. -/
theorem minVar_le_outputVar (P : PooleParams) {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (u : ℝ)
    (hden : den P u ≠ 0) : minVar P a b ≤ outputVar P a b u := by
  have hθ := P.θ_pos
  have hC : 0 < 1 + P.φ * P.θ := by have := P.φ_pos; positivity
  have hQ : 0 < (P.θ + P.δ) ^ 2 * b + (1 + P.φ * P.θ) ^ 2 * a := by positivity
  have hD2 : 0 < den P u ^ 2 := by positivity
  unfold minVar outputVar
  rw [div_le_div_iff₀ hQ hD2]
  have hid := optimum_identity P a b u
  have hθ2 : 0 ≤ P.θ ^ 2 := by positivity
  nlinarith [mul_nonneg hθ2 (sq_nonneg (u * a * (1 + P.φ * P.θ) - P.δ * b * (P.θ + P.δ)))]

/-- O&R Exercise 3(d): the variance equals `minVar` exactly at `u = u*`. -/
theorem outputVar_eq_minVar_iff (P : PooleParams) {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b)
    (u : ℝ) (hden : den P u ≠ 0) : outputVar P a b u = minVar P a b ↔ u = optimalU P a b := by
  have hθ := P.θ_pos
  have hC : 0 < 1 + P.φ * P.θ := by have := P.φ_pos; positivity
  have hQ : 0 < (P.θ + P.δ) ^ 2 * b + (1 + P.φ * P.θ) ^ 2 * a := by positivity
  have hD2 : 0 < den P u ^ 2 := by positivity
  have hid := optimum_identity P a b u
  unfold minVar outputVar optimalU
  rw [div_eq_div_iff hD2.ne' hQ.ne', eq_div_iff (by positivity)]
  have hθ2 : 0 < P.θ ^ 2 := by positivity
  constructor
  · intro h
    have h1 : P.θ ^ 2 * (u * a * (1 + P.φ * P.θ) - P.δ * b * (P.θ + P.δ)) ^ 2 = 0 := by
      linear_combination h - P.θ ^ 2 * hid
    have h2 := (mul_eq_zero.mp h1).resolve_left hθ2.ne'
    have h3 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2
    linear_combination h3
  · intro h
    have h3 : u * a * (1 + P.φ * P.θ) - P.δ * b * (P.θ + P.δ) = 0 := by
      linear_combination h
    have h4 := hid
    rw [h3] at h4
    linear_combination P.θ ^ 2 * h4

/-- O&R Exercise 3(d): `u* ≥ 0`, so the optimal rule is admissible (`den u* > 0`). -/
theorem optimalU_nonneg (P : PooleParams) {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) :
    0 ≤ optimalU P a b := by
  unfold optimalU
  have := P.θ_pos
  have := P.δ_pos
  have := P.φ_pos
  positivity

/-- O&R Exercise 3(d): the optimal rule attains `minVar`. -/
theorem outputVar_optimalU (P : PooleParams) {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) :
    outputVar P a b (optimalU P a b) = minVar P a b :=
  (outputVar_eq_minVar_iff P ha hb _ (den_pos P (optimalU_nonneg P ha hb)).ne').mpr rfl

/-- O&R Exercise 3(d), existence and uniqueness of the optimal feedback rule: for
`σ_ε² > 0`, `σ_v² ≥ 0` there is exactly one admissible `Φ` minimising the conditional output
variance over all admissible `Φ'`, namely `Φ* = η − u*`. -/
theorem exists_unique_optimal_rule (P : PooleParams) {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) :
    ∃! Φ, den P (P.η - Φ) ≠ 0 ∧
      ∀ Φ', den P (P.η - Φ') ≠ 0 → outputVar P a b (P.η - Φ) ≤ outputVar P a b (P.η - Φ') := by
  have hadm : den P (P.η - optimalPhi P a b) ≠ 0 := by
    unfold optimalPhi
    rw [sub_sub_cancel]
    exact (den_pos P (optimalU_nonneg P ha hb)).ne'
  refine ⟨optimalPhi P a b, ⟨hadm, fun Φ' hΦ' => ?_⟩, ?_⟩
  · unfold optimalPhi
    rw [sub_sub_cancel, outputVar_optimalU P ha hb]
    exact minVar_le_outputVar P ha hb _ hΦ'
  · rintro Φ ⟨hΦ, hmin⟩
    have h1 := hmin (optimalPhi P a b) hadm
    have h2 : outputVar P a b (P.η - optimalPhi P a b) = minVar P a b := by
      unfold optimalPhi
      rw [sub_sub_cancel, outputVar_optimalU P ha hb]
    have h3 := minVar_le_outputVar P ha hb _ hΦ
    have h4 : outputVar P a b (P.η - Φ) = minVar P a b := by linarith
    have h5 := (outputVar_eq_minVar_iff P ha hb _ hΦ).mp h4
    unfold optimalPhi
    linarith

/-- O&R Exercise 3(d), closed form of the optimal rule:
`Φ* = η − (θ + δ) δ σ_v²/((1 + φ θ) σ_ε²)`. -/
theorem optimalPhi_eq (P : PooleParams) (a b : ℝ) :
    optimalPhi P a b = P.η - (P.θ + P.δ) * P.δ * b / ((1 + P.φ * P.θ) * a) := rfl

/-- O&R Exercise 3(d), sign correction: with `σ_ε², σ_v² > 0`, `Φ* < η`; the optimal
coefficient is never "between 0 and ∞" in the book's sense unless `u* < η`. -/
theorem optimalPhi_lt_eta (P : PooleParams) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    optimalPhi P a b < P.η := by
  unfold optimalPhi optimalU
  have := P.θ_pos
  have := P.δ_pos
  have := P.φ_pos
  have : 0 < (P.θ + P.δ) * P.δ * b / ((1 + P.φ * P.θ) * a) := by positivity
  linarith

/-- O&R Exercise 3(d): `Φ* < 0` (leaning *against* the float's direction: money rises when
the currency appreciates) exactly when `u* > η`. -/
theorem optimalPhi_neg_iff (P : PooleParams) (a b : ℝ) :
    optimalPhi P a b < 0 ↔ P.η < optimalU P a b := by
  unfold optimalPhi
  constructor <;> intro h <;> linarith

/-- O&R Exercise 3(d): the optimum is strictly better than the peg when both shocks are
present. -/
theorem minVar_lt_pegVar (P : PooleParams) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    minVar P a b < pegVar P a := by
  have hθ := P.θ_pos
  have hA : 0 < P.θ + P.δ := by linarith [P.δ_pos]
  have hC : 0 < 1 + P.φ * P.θ := by have := P.φ_pos; positivity
  unfold minVar pegVar
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  have h1 : 0 < P.θ ^ 2 * a * ((1 + P.φ * P.θ) ^ 2 * a) := by positivity
  nlinarith

/-- O&R Exercise 3(d): the optimum is at least as good as the float, with equality iff
`u* = η`, i.e. iff `η (1 + φ θ) σ_ε² = (θ + δ) δ σ_v²` (then the float is optimal). -/
theorem minVar_le_floatVar (P : PooleParams) {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) :
    minVar P a b ≤ floatVar P a b ∧
      (floatVar P a b = minVar P a b ↔ P.η = optimalU P a b) :=
  ⟨minVar_le_outputVar P ha hb _ (den_pos P P.η_pos.le).ne',
    outputVar_eq_minVar_iff P ha hb _ (den_pos P P.η_pos.le).ne'⟩

/-- O&R Exercise 3(d): the pole of the output formula, `den (η − Φ) = 0` iff
`Φ = η + δ (1 + φ θ)/(θ + δ)`; there the equilibrium fails to exist (see
`feedback_no_eqm_at_pole`). -/
theorem den_eq_zero_iff (P : PooleParams) (Φ : ℝ) :
    den P (P.η - Φ) = 0 ↔ Φ = P.η + P.δ * (1 + P.φ * P.θ) / (P.θ + P.δ) := by
  have hA : P.θ + P.δ ≠ 0 := by linarith [P.θ_pos, P.δ_pos]
  unfold den
  constructor
  · intro h
    field_simp
    linear_combination -h
  · intro h
    rw [h]
    field_simp
    ring

/-- O&R Exercise 3(d): at the pole, in the determinacy region, no bounded equilibrium exists
as soon as some state has `(η − Φ) ε ≠ δ v`. -/
theorem feedback_no_eqm_at_pole {P : PooleParams} {Sh : PooleShocks S} {mbar Φ : ℝ}
    (hdet : Φ < 1 ∨ 1 + 2 * P.η < Φ) (hpole : den P (P.η - Φ) = 0) (s : S)
    (hs : (P.η - Φ) * Sh.eps s ≠ P.δ * Sh.v s) {p e y m i : List S → ℝ}
    (hE : IsEqm P Sh (feedbackPolicy mbar Φ) p e y m i) (hb : Bounded p) : False := by
  obtain ⟨hi, hsu, hg, hm, hpol⟩ := hE s []
  have hc : nodeEx Sh p [] = mbar := feedback_expected_price_eq hdet hE hb []
  have hX : nodeEx Sh e [s] = mbar := by
    rw [eqm_nodeEx_e hE [s]]
    exact feedback_expected_price_eq hdet hE hb [s]
  have hred := feedback_node_reduced_form P mbar Φ (Sh.eps s) (Sh.v s) _ _ _ _ _ _ _
    hi hsu hg hm hpol
  rw [hX, hc, hpole, mul_zero] at hred
  have h1 : (P.η - Φ) * Sh.eps s - P.δ * Sh.v s = 0 := by
    have := (mul_eq_zero.mp (by linear_combination -hred : P.θ *
      ((P.η - Φ) * Sh.eps s - P.δ * Sh.v s) = 0)).resolve_left P.θ_pos.ne'
    exact this
  exact hs (by linear_combination h1)

/-- The limit lemma used for "the peg is a limit": `(α u + β)/(A u + B) → α/A` along any
filter on which `u⁻¹ → 0` and `u ≠ 0` eventually (O&R Exercise 3(d)). -/
theorem tendsto_linear_ratio {l : Filter ℝ} (hl : Tendsto (fun u : ℝ => u⁻¹) l (𝓝 0))
    (hne : ∀ᶠ u in l, u ≠ 0) (α β A B : ℝ) (hA : A ≠ 0) :
    Tendsto (fun u => (α * u + β) / (A * u + B)) l (𝓝 (α / A)) := by
  have hc : ContinuousAt (fun t : ℝ => (α + β * t) / (A + B * t)) 0 := by
    apply ContinuousAt.div (by fun_prop) (by fun_prop)
    simpa using hA
  have h1 := hc.tendsto.comp hl
  have h0 : (α + β * 0) / (A + B * 0) = α / A := by simp
  rw [h0] at h1
  refine h1.congr' (hne.mono fun u hu => ?_)
  simp only [Function.comp_apply]
  rw [show α + β * u⁻¹ = (α * u + β) / u by field_simp,
    show A + B * u⁻¹ = (A * u + B) / u by field_simp, div_div_div_cancel_right₀ hu]

/-- The limit lemma for variances: `(a u² + b)/(A u + B)² → a/A²` along any filter on which
`u⁻¹ → 0` and `u ≠ 0` eventually (O&R Exercise 3(d)). -/
theorem tendsto_quadratic_ratio {l : Filter ℝ} (hl : Tendsto (fun u : ℝ => u⁻¹) l (𝓝 0))
    (hne : ∀ᶠ u in l, u ≠ 0) (a b A B : ℝ) (hA : A ≠ 0) :
    Tendsto (fun u => (a * u ^ 2 + b) / (A * u + B) ^ 2) l (𝓝 (a / A ^ 2)) := by
  have hc : ContinuousAt (fun t : ℝ => (a + b * t ^ 2) / (A + B * t) ^ 2) 0 := by
    apply ContinuousAt.div (by fun_prop) (by fun_prop)
    simpa using hA
  have h1 := hc.tendsto.comp hl
  have h0 : (a + b * 0 ^ 2) / (A + B * 0) ^ 2 = a / A ^ 2 := by simp
  rw [h0] at h1
  refine h1.congr' (hne.mono fun u hu => ?_)
  simp only [Function.comp_apply]
  rw [show a + b * u⁻¹ ^ 2 = (a * u ^ 2 + b) / u ^ 2 by field_simp,
    show (A + B * u⁻¹) ^ 2 = (A * u + B) ^ 2 / u ^ 2 by field_simp,
    div_div_div_cancel_right₀ (pow_ne_zero 2 hu)]

/-- O&R Exercise 3(d): `η − Φ → +∞` as `Φ → −∞`. -/
theorem tendsto_eta_sub_atBot (η : ℝ) : Tendsto (fun Φ : ℝ => η - Φ) atBot atTop :=
  tendsto_atBot_atTop.2 fun b => ⟨η - b, fun Φ hΦ => by linarith⟩

/-- O&R Exercise 3(d): `η − Φ → −∞` as `Φ → +∞`. -/
theorem tendsto_eta_sub_atTop (η : ℝ) : Tendsto (fun Φ : ℝ => η - Φ) atTop atBot :=
  tendsto_atTop_atBot.2 fun b => ⟨η - b, fun Φ hΦ => by linarith⟩

/-- O&R Exercise 3(d), "the peg is only a limit": as `Φ → −∞` the conditional output
variance tends to the peg's `θ² σ_ε²/(θ + δ)²`. -/
theorem outputVar_tendsto_peg_atBot (P : PooleParams) (a b : ℝ) :
    Tendsto (fun Φ => outputVar P a b (P.η - Φ)) atBot (𝓝 (pegVar P a)) := by
  have hA : P.θ + P.δ ≠ 0 := by linarith [P.θ_pos, P.δ_pos]
  have h := tendsto_quadratic_ratio tendsto_inv_atTop_zero
    (eventually_ne_atTop 0) (P.θ ^ 2 * a) (P.θ ^ 2 * (P.δ ^ 2 * b)) (P.θ + P.δ)
    (P.δ * (1 + P.φ * P.θ)) hA
  have h2 := h.comp (tendsto_eta_sub_atBot P.η)
  unfold pegVar
  refine h2.congr fun Φ => ?_
  simp only [Function.comp_apply]
  unfold outputVar den
  ring

/-- O&R Exercise 3(d): as `Φ → +∞` (i.e. through the pole) the variance also tends to the
peg value. -/
theorem outputVar_tendsto_peg_atTop (P : PooleParams) (a b : ℝ) :
    Tendsto (fun Φ => outputVar P a b (P.η - Φ)) atTop (𝓝 (pegVar P a)) := by
  have hA : P.θ + P.δ ≠ 0 := by linarith [P.θ_pos, P.δ_pos]
  have h := tendsto_quadratic_ratio tendsto_inv_atBot_zero
    (eventually_ne_atBot 0) (P.θ ^ 2 * a) (P.θ ^ 2 * (P.δ ^ 2 * b)) (P.θ + P.δ)
    (P.δ * (1 + P.φ * P.θ)) hA
  have h2 := h.comp (tendsto_eta_sub_atTop P.η)
  unfold pegVar
  refine h2.congr fun Φ => ?_
  simp only [Function.comp_apply]
  unfold outputVar den
  ring

/-- O&R Exercise 3(d): the equilibrium output itself converges, state by state, to the peg's
output `θ ε/(θ + δ)` as `Φ → −∞`. -/
theorem outputMSV_tendsto_peg (P : PooleParams) (Sh : PooleShocks S) (s : S) :
    Tendsto (fun Φ => outputMSV P Sh Φ s) atBot (𝓝 (P.θ * Sh.eps s / (P.θ + P.δ))) := by
  have hA : P.θ + P.δ ≠ 0 := by linarith [P.θ_pos, P.δ_pos]
  have h := tendsto_linear_ratio tendsto_inv_atTop_zero (eventually_ne_atTop 0)
    (P.θ * Sh.eps s) (-(P.θ * P.δ * Sh.v s)) (P.θ + P.δ) (P.δ * (1 + P.φ * P.θ)) hA
  have h2 := h.comp (tendsto_eta_sub_atBot P.η)
  refine h2.congr fun Φ => ?_
  simp only [Function.comp_apply]
  unfold outputMSV den
  ring

/-- O&R Exercise 3(d): with `σ_ε² = 0 < σ_v²` no admissible rule is optimal: the infimum
(zero, the peg's value) is approached but never attained by a finite `Φ`. -/
theorem no_optimal_rule_of_eps_zero (P : PooleParams) {b : ℝ} (hb : 0 < b) :
    ¬∃ u, den P u ≠ 0 ∧ ∀ u', den P u' ≠ 0 → outputVar P 0 b u ≤ outputVar P 0 b u' := by
  rintro ⟨u, hu, hmin⟩
  have hA : 0 < P.θ + P.δ := by linarith [P.θ_pos, P.δ_pos]
  have hθ := P.θ_pos
  have hδ := P.δ_pos
  set D := den P u with hD
  have hC : 0 < P.δ * (1 + P.φ * P.θ) := by have := P.φ_pos; positivity
  set u' := (2 * |D| + 1 - P.δ * (1 + P.φ * P.θ)) / (P.θ + P.δ) with hu'
  have hdu' : den P u' = 2 * |D| + 1 := by
    unfold den
    rw [hu']
    field_simp
    ring
  have hpos : 0 < 2 * |D| + 1 := by positivity
  have h1 := hmin u' (by rw [hdu']; exact hpos.ne')
  unfold outputVar at h1
  rw [hdu', ← hD] at h1
  simp only [mul_zero, zero_add] at h1
  have hD2 : 0 < D ^ 2 := by positivity
  rw [div_le_div_iff₀ hD2 (by positivity)] at h1
  have hk : 0 < P.θ ^ 2 * (P.δ ^ 2 * b) := by positivity
  have h2 : D ^ 2 < (2 * |D| + 1) ^ 2 := by
    have := sq_abs D
    nlinarith [abs_nonneg D]
  nlinarith

/-- O&R Exercise 3(d), a feedback rule never reproduces the peg: in the determinacy region
and away from the pole, if a bounded equilibrium has `e ≡ m̄` then
`(θ + δ) v + (1 + φ θ) ε = 0` in every state, a degenerate shock structure. -/
theorem feedback_peg_only_limit {P : PooleParams} {Sh : PooleShocks S} {mbar Φ : ℝ}
    (hdet : Φ < 1 ∨ 1 + 2 * P.η < Φ) (hden : den P (P.η - Φ) ≠ 0)
    {p e y m i : List S → ℝ} (hE : IsEqm P Sh (feedbackPolicy mbar Φ) p e y m i)
    (hb : Bounded p) (hpeg : ∀ s h, e (s :: h) = mbar) (s : S) :
    (P.θ + P.δ) * Sh.v s + (1 + P.φ * P.θ) * Sh.eps s = 0 := by
  have hu := feedback_eqm_unique hdet hden hE hb s []
  have he : eMSV P Sh mbar Φ s = mbar := by rw [← hu.2.2.1, hpeg]
  have hY : outputMSV P Sh Φ s * den P (P.η - Φ) =
      P.θ * ((P.η - Φ) * Sh.eps s - P.δ * Sh.v s) := by
    unfold outputMSV
    exact div_mul_cancel₀ _ hden
  have hθ := P.θ_pos.ne'
  have hδ := P.δ_pos.ne'
  unfold eMSV pMSV at he
  field_simp at he
  unfold den at hY
  have h3 : P.θ * P.δ * ((P.θ + P.δ) * Sh.v s + (1 + P.φ * P.θ) * Sh.eps s) = 0 := by
    linear_combination (P.θ + P.δ) * hY +
      (-(P.η - Φ) * (P.θ + P.δ) - P.δ * (1 + P.φ * P.θ)) * he
  rcases mul_eq_zero.mp h3 with h4 | h4
  · exact absurd h4 (mul_ne_zero hθ hδ)
  · exact h4

/-- O&R Exercise 3: `σ_v² ≥ 0`. -/
theorem sigV2_nonneg (Sh : PooleShocks S) : 0 ≤ sigV2 Sh := by
  unfold sigV2 expect
  exact Finset.sum_nonneg fun s _ => mul_nonneg (Sh.prob_nonneg s) (sq_nonneg _)

/-- O&R Exercise 3(d), optimality at the level of equilibria: if `σ_ε² > 0`, then in the
determinacy region every bounded equilibrium under any admissible rule has conditional output
variance at least `minVar` at every node, with equality iff `Φ = Φ*`. -/
theorem feedback_eqm_var_ge_min {P : PooleParams} {Sh : PooleShocks S} (ha : 0 < sigE2 Sh)
    {mbar Φ : ℝ} (hdet : Φ < 1 ∨ 1 + 2 * P.η < Φ) (hden : den P (P.η - Φ) ≠ 0)
    {p e y m i : List S → ℝ} (hE : IsEqm P Sh (feedbackPolicy mbar Φ) p e y m i)
    (hb : Bounded p) (h : List S) :
    minVar P (sigE2 Sh) (sigV2 Sh) ≤ nodeEx Sh (fun g => y g ^ 2) h ∧
      (nodeEx Sh (fun g => y g ^ 2) h = minVar P (sigE2 Sh) (sigV2 Sh) ↔
        Φ = optimalPhi P (sigE2 Sh) (sigV2 Sh)) := by
  rw [(feedback_output_moments hdet hden hE hb h).2]
  refine ⟨minVar_le_outputVar P ha (sigV2_nonneg Sh) _ hden, ?_⟩
  rw [outputVar_eq_minVar_iff P ha (sigV2_nonneg Sh) _ hden]
  unfold optimalPhi
  constructor <;> intro h' <;> linarith

/-- O&R Exercise 3(d): the stationary equilibrium under `Φ*` exists and attains `minVar` at
every node (whether or not `Φ*` is in the determinacy region). -/
theorem optimal_rule_eqm_attains (P : PooleParams) (Sh : PooleShocks S) (ha : 0 < sigE2 Sh)
    (mbar : ℝ) (h : List S) :
    IsEqm P Sh (feedbackPolicy mbar (optimalPhi P (sigE2 Sh) (sigV2 Sh)))
      (onHead mbar (pMSV P Sh mbar (optimalPhi P (sigE2 Sh) (sigV2 Sh))))
      (onHead mbar (eMSV P Sh mbar (optimalPhi P (sigE2 Sh) (sigV2 Sh))))
      (onHead 0 (outputMSV P Sh (optimalPhi P (sigE2 Sh) (sigV2 Sh))))
      (onHead mbar (mMSV P Sh mbar (optimalPhi P (sigE2 Sh) (sigV2 Sh))))
      (onHead 0 (iMSV P Sh mbar (optimalPhi P (sigE2 Sh) (sigV2 Sh)))) ∧
    nodeEx Sh (fun g => onHead 0 (outputMSV P Sh (optimalPhi P (sigE2 Sh) (sigV2 Sh))) g ^ 2) h
      = minVar P (sigE2 Sh) (sigV2 Sh) := by
  have hadm : den P (P.η - optimalPhi P (sigE2 Sh) (sigV2 Sh)) ≠ 0 := by
    unfold optimalPhi
    rw [sub_sub_cancel]
    exact (den_pos P (optimalU_nonneg P ha (sigV2_nonneg Sh))).ne'
  refine ⟨feedback_eqm_exists P Sh mbar _ hadm, ?_⟩
  change expect Sh (fun s => outputMSV P Sh (optimalPhi P (sigE2 Sh) (sigV2 Sh)) s ^ 2) = _
  rw [expect_outputMSV_sq]
  unfold optimalPhi
  rw [sub_sub_cancel]
  exact outputVar_optimalU P ha (sigV2_nonneg Sh)

/-! ### The sign of the optimal coefficient (O&R p. 632 and Ex. 3(d) flags) -/

/-- O&R p. 632: as the ratio `σ_ε²/σ_v²` of real to monetary shock variances tends to zero,
the optimal coefficient `Φ* = η − (θ+δ) δ/((1+φθ) r)` tends to `−∞` (not `+∞`). -/
theorem optimalPhi_tendsto_atBot (P : PooleParams) :
    Tendsto (fun r : ℝ => P.η - (P.θ + P.δ) * P.δ / ((1 + P.φ * P.θ) * r)) (𝓝[>] 0)
      atBot := by
  have hK : 0 < (P.θ + P.δ) * P.δ / (1 + P.φ * P.θ) := by
    have := P.θ_pos
    have := P.δ_pos
    have := P.φ_pos
    positivity
  have h := tendsto_inv_nhdsGT_zero.const_mul_atTop hK
  refine tendsto_atBot.2 fun c => (h.eventually_ge_atTop (P.η - c)).mono fun r hr => ?_
  have he : (P.θ + P.δ) * P.δ / ((1 + P.φ * P.θ) * r) =
      (P.θ + P.δ) * P.δ / (1 + P.φ * P.θ) * r⁻¹ := by
    simp only [div_eq_mul_inv, mul_inv]
    ring
  rw [he]
  linarith

/-- O&R p. 632: the optimal coefficient as a function of the variance ratio `r = σ_ε²/σ_v²`
(an identity for all `a, b`, including the junk value `b = 0`). -/
theorem optimalPhi_eq_ratio (P : PooleParams) (a b : ℝ) :
    optimalPhi P a b = P.η - (P.θ + P.δ) * P.δ / ((1 + P.φ * P.θ) * (a / b)) := by
  unfold optimalPhi optimalU
  congr 1
  rw [mul_div_assoc', div_div_eq_mul_div]

/-- O&R p. 632, the book's claim is false: `Φ*` does NOT tend to `+∞` as `σ_ε²/σ_v² → 0`. -/
theorem optimalPhi_not_tendsto_atTop (P : PooleParams) :
    ¬Tendsto (fun r : ℝ => P.η - (P.θ + P.δ) * P.δ / ((1 + P.φ * P.θ) * r)) (𝓝[>] 0)
      atTop :=
  fun h => (optimalPhi_tendsto_atBot P).not_tendsto disjoint_atBot_atTop h

/-- The survey's counterexample parameters `θ = 1.1, δ = 0.6, η = 2, φ = 0.5` (O&R Ex. 3). -/
noncomputable def signExample : PooleParams :=
  ⟨1.1, 0.6, 2, 0.5, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- O&R Ex. 3(d) flag: with `σ_ε = 0.7`, `σ_v = 4` (so `σ_ε² = 0.49`, `σ_v² = 16`) the optimal
coefficient is about `−19.49`: negative, so not "between 0 (float) and ∞ (peg)". -/
theorem signExample_optimalPhi :
    -19.5 < optimalPhi signExample 0.49 16 ∧ optimalPhi signExample 0.49 16 < -19 := by
  unfold optimalPhi optimalU signExample
  norm_num

/-- Parameters `θ = δ = φ = 1`, `η = 3` for the indeterminacy example (O&R Ex. 3). -/
noncomputable def indetExample : PooleParams :=
  ⟨1, 1, 3, 1, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- O&R Ex. 3(d), a new finding: with `σ_ε² = σ_v² = 1` the optimal coefficient is `Φ* = 2`,
inside the indeterminacy region `1 < Φ < 1 + 2η = 7`, where bounded sunspot equilibria with
different output exist (`sunspot_eqm`). -/
theorem indetExample_optimalPhi :
    optimalPhi indetExample 1 1 = 2 ∧ 1 < optimalPhi indetExample 1 1 ∧
      optimalPhi indetExample 1 1 < 1 + 2 * indetExample.η := by
  unfold optimalPhi optimalU indetExample
  norm_num

/-- O&R Ex. 3(d): the optimal rule is in the indeterminacy region exactly when `u* < η − 1`
(for `σ_ε² > 0`, `σ_v² ≥ 0`). -/
theorem optimalPhi_indeterminate_iff (P : PooleParams) {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) :
    (1 < optimalPhi P a b ∧ optimalPhi P a b < 1 + 2 * P.η) ↔ optimalU P a b < P.η - 1 := by
  have h0 := optimalU_nonneg P ha hb
  have hη := P.η_pos
  unfold optimalPhi
  constructor
  · rintro ⟨h1, _⟩
    linarith
  · intro h
    constructor <;> linarith

/-! ### Sunspot equilibria in the indeterminacy region -/

/-- O&R Ex. 3(d): the root `λ = (η + 1 − Φ)/η` of the expected-level recursion. -/
noncomputable def sunLam (P : PooleParams) (Φ : ℝ) : ℝ := (P.η + 1 - Φ) / P.η

/-- O&R Ex. 3(d): the sunspot component of the expected price level,
`x_{s :: h} = λ x_h + w_s`, `x_{[]} = 0`. -/
def sunspotLevel (lam : ℝ) (w : S → ℝ) : List S → ℝ
  | [] => 0
  | s :: h => lam * sunspotLevel lam w h + w s

/-- O&R Ex. 3(d): output in a sunspot equilibrium, in which the money-demand shock is
effectively `v − η w`. -/
noncomputable def ySun (P : PooleParams) (Sh : PooleShocks S) (Φ : ℝ) (w : S → ℝ)
    (s : S) : ℝ :=
  P.θ * ((P.η - Φ) * Sh.eps s - P.δ * (Sh.v s - P.η * w s)) / den P (P.η - Φ)

/-- O&R Ex. 3(d): the price level in a sunspot equilibrium. -/
noncomputable def pSun (P : PooleParams) (Sh : PooleShocks S) (mbar Φ : ℝ) (w : S → ℝ) :
    List S → ℝ
  | [] => mbar
  | s :: h => mbar + sunspotLevel (sunLam P Φ) w h + ySun P Sh Φ w s / P.θ

/-- O&R Ex. 3(d): the exchange rate in a sunspot equilibrium. -/
noncomputable def eSun (P : PooleParams) (Sh : PooleShocks S) (mbar Φ : ℝ) (w : S → ℝ) :
    List S → ℝ
  | [] => mbar
  | s :: h => pSun P Sh mbar Φ w (s :: h) + (ySun P Sh Φ w s - Sh.eps s) / P.δ

/-- O&R Ex. 3(d): the money supply in a sunspot equilibrium (the feedback rule). -/
noncomputable def mSun (P : PooleParams) (Sh : PooleShocks S) (mbar Φ : ℝ) (w : S → ℝ)
    (g : List S) : ℝ :=
  mbar + Φ * (eSun P Sh mbar Φ w g - mbar)

/-- O&R Ex. 3(d): the nominal interest rate in a sunspot equilibrium (UIP). -/
noncomputable def iSun (P : PooleParams) (Sh : PooleShocks S) (mbar Φ : ℝ) (w : S → ℝ)
    (g : List S) : ℝ :=
  nodeEx Sh (eSun P Sh mbar Φ w) g - eSun P Sh mbar Φ w g

/-- O&R Ex. 3(d): sunspot output has mean zero when `E w = 0`. -/
theorem expect_ySun (P : PooleParams) (Sh : PooleShocks S) (Φ : ℝ) {w : S → ℝ}
    (hw : expect Sh w = 0) : expect Sh (ySun P Sh Φ w) = 0 := by
  have hf : ySun P Sh Φ w = fun s =>
      (P.θ * (P.η - Φ) / den P (P.η - Φ)) * Sh.eps s +
        (-(P.θ * P.δ) / den P (P.η - Φ)) * Sh.v s +
        (P.θ * P.δ * P.η / den P (P.η - Φ)) * w s := by
    funext s
    unfold ySun
    ring
  rw [hf, expect_add, expect_add, expect_const_mul, expect_const_mul, expect_const_mul,
    expect_eps, expect_v, hw]
  ring

/-- O&R Ex. 3(d): `E_{t−1} p_t = m̄ + x_h` in the sunspot equilibrium. -/
theorem nodeEx_pSun (P : PooleParams) (Sh : PooleShocks S) (mbar Φ : ℝ) {w : S → ℝ}
    (hw : expect Sh w = 0) (h : List S) :
    nodeEx Sh (pSun P Sh mbar Φ w) h = mbar + sunspotLevel (sunLam P Φ) w h := by
  rw [nodeEx_eq_expect]
  simp only [pSun]
  rw [expect_add, expect_const, expect_div_const, expect_ySun P Sh Φ hw, zero_div, add_zero]

/-- O&R Ex. 3(d): `E_{t−1} e_t = m̄ + x_h` in the sunspot equilibrium. -/
theorem nodeEx_eSun (P : PooleParams) (Sh : PooleShocks S) (mbar Φ : ℝ) {w : S → ℝ}
    (hw : expect Sh w = 0) (h : List S) :
    nodeEx Sh (eSun P Sh mbar Φ w) h = mbar + sunspotLevel (sunLam P Φ) w h := by
  rw [nodeEx_eq_expect]
  simp only [eSun, pSun]
  rw [expect_add, expect_add, expect_const, expect_div_const, expect_div_const, expect_sub,
    expect_eps, expect_ySun P Sh Φ hw]
  ring

/-- O&R Ex. 3(d): for `|λ| < 1` the sunspot level is bounded by `Σ|w|/(1 − |λ|)`. -/
theorem abs_sunspotLevel_le {lam : ℝ} (hlam : |lam| < 1) (w : S → ℝ) (h : List S) :
    |sunspotLevel lam w h| ≤ (∑ s, |w s|) / (1 - |lam|) := by
  have hpos : 0 < 1 - |lam| := by linarith
  have hW : 0 ≤ ∑ s, |w s| := Finset.sum_nonneg fun s _ => abs_nonneg _
  induction h with
  | nil => simp only [sunspotLevel, abs_zero]; positivity
  | cons s h ih =>
    simp only [sunspotLevel]
    have hs := Finset.single_le_sum (f := fun s => |w s|) (fun s _ => abs_nonneg (w s))
      (Finset.mem_univ s)
    have h1 : |lam * sunspotLevel lam w h + w s| ≤ |lam| * |sunspotLevel lam w h| + |w s| := by
      rw [← abs_mul]
      exact abs_add_le _ _
    have h2 : |lam| * |sunspotLevel lam w h| ≤ |lam| * ((∑ s, |w s|) / (1 - |lam|)) :=
      mul_le_mul_of_nonneg_left ih (abs_nonneg _)
    have h3 : |lam| * ((∑ s, |w s|) / (1 - |lam|)) + ∑ s, |w s| =
        (∑ s, |w s|) / (1 - |lam|) := by
      field_simp
      ring
    linarith

/-- O&R Ex. 3(d): for any `Φ` away from the pole and any mean-zero sunspot `w`, the sunspot
allocation is an equilibrium on the event tree. -/
theorem sunspot_isEqm (P : PooleParams) (Sh : PooleShocks S) (mbar Φ : ℝ)
    (hden : den P (P.η - Φ) ≠ 0) {w : S → ℝ} (hw : expect Sh w = 0) :
    IsEqm P Sh (feedbackPolicy mbar Φ) (pSun P Sh mbar Φ w) (eSun P Sh mbar Φ w)
      (onHead 0 (ySun P Sh Φ w)) (mSun P Sh mbar Φ w) (iSun P Sh mbar Φ w) := by
  intro s h
  have hθ := P.θ_pos.ne'
  have hδ := P.δ_pos.ne'
  have hη := P.η_pos.ne'
  have hY : ySun P Sh Φ w s * den P (P.η - Φ) =
      P.θ * ((P.η - Φ) * Sh.eps s - P.δ * (Sh.v s - P.η * w s)) := by
    unfold ySun
    exact div_mul_cancel₀ _ hden
  refine ⟨rfl, ?_, ?_, ?_, rfl⟩
  · rw [nodeEx_pSun P Sh mbar Φ hw]
    simp only [onHead, pSun]
    field_simp
    ring
  · simp only [onHead, eSun]
    field_simp
    ring
  · unfold mSun iSun
    rw [nodeEx_eSun P Sh mbar Φ hw]
    simp only [onHead, eSun, pSun, sunspotLevel]
    unfold sunLam
    unfold den at hY
    field_simp
    linear_combination (-1 : ℝ) * hY

/-- O&R Ex. 3(d), indeterminacy: for `1 < Φ < 1 + 2η` the sunspot equilibrium has a bounded
price level and exchange rate, so the no-bubble condition does not select a unique
equilibrium there. -/
theorem sunspot_bounded (P : PooleParams) (Sh : PooleShocks S) (mbar Φ : ℝ)
    (hind : 1 < Φ ∧ Φ < 1 + 2 * P.η) (w : S → ℝ) :
    Bounded (pSun P Sh mbar Φ w) ∧ Bounded (eSun P Sh mbar Φ w) := by
  have hlam : |sunLam P Φ| < 1 := (abs_lambda_lt_one_iff P.η_pos).mpr hind
  set B := (∑ s, |w s|) / (1 - |sunLam P Φ|)
  have hB : 0 ≤ B := by
    have : 0 < 1 - |sunLam P Φ| := by linarith
    have hW : 0 ≤ ∑ s, |w s| := Finset.sum_nonneg fun s _ => abs_nonneg _
    positivity
  have hYb : ∀ s, |ySun P Sh Φ w s / P.θ| ≤ ∑ s', |ySun P Sh Φ w s' / P.θ| := fun s =>
    Finset.single_le_sum (f := fun s => |ySun P Sh Φ w s / P.θ|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ s)
  have hZb : ∀ s, |(ySun P Sh Φ w s - Sh.eps s) / P.δ| ≤
      ∑ s', |(ySun P Sh Φ w s' - Sh.eps s') / P.δ| := fun s =>
    Finset.single_le_sum (f := fun s => |(ySun P Sh Φ w s - Sh.eps s) / P.δ|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ s)
  have hS1 : 0 ≤ ∑ s', |ySun P Sh Φ w s' / P.θ| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hS2 : 0 ≤ ∑ s', |(ySun P Sh Φ w s' - Sh.eps s') / P.δ| :=
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hp : ∀ g, |pSun P Sh mbar Φ w g| ≤ |mbar| + B + ∑ s', |ySun P Sh Φ w s' / P.θ| := by
    intro g
    cases g with
    | nil => simp only [pSun]; linarith
    | cons s h =>
      simp only [pSun]
      have h1 := abs_sunspotLevel_le hlam w h
      have h2 := hYb s
      calc |mbar + sunspotLevel (sunLam P Φ) w h + ySun P Sh Φ w s / P.θ|
          ≤ |mbar + sunspotLevel (sunLam P Φ) w h| + |ySun P Sh Φ w s / P.θ| :=
            abs_add_le _ _
        _ ≤ |mbar| + |sunspotLevel (sunLam P Φ) w h| + |ySun P Sh Φ w s / P.θ| := by
            linarith [abs_add_le mbar (sunspotLevel (sunLam P Φ) w h)]
        _ ≤ _ := by linarith
  refine ⟨⟨_, hp⟩, ⟨|mbar| + B + ∑ s', |ySun P Sh Φ w s' / P.θ| +
    ∑ s', |(ySun P Sh Φ w s' - Sh.eps s') / P.δ|, fun g => ?_⟩⟩
  cases g with
  | nil => simp only [eSun]; linarith
  | cons s h =>
    simp only [eSun]
    have h1 := hp (s :: h)
    have h2 := hZb s
    calc |pSun P Sh mbar Φ w (s :: h) + (ySun P Sh Φ w s - Sh.eps s) / P.δ|
        ≤ |pSun P Sh mbar Φ w (s :: h)| + |(ySun P Sh Φ w s - Sh.eps s) / P.δ| :=
          abs_add_le _ _
      _ ≤ _ := by linarith

/-- O&R Ex. 3(d): sunspot output differs from the stationary output by `θ δ η w/den`, so it
differs in every state where `w ≠ 0`. -/
theorem ySun_sub_outputMSV (P : PooleParams) (Sh : PooleShocks S) (Φ : ℝ) (w : S → ℝ)
    (s : S) (hden : den P (P.η - Φ) ≠ 0) :
    ySun P Sh Φ w s - outputMSV P Sh Φ s = P.θ * P.δ * P.η * w s / den P (P.η - Φ) ∧
      (w s ≠ 0 → ySun P Sh Φ w s ≠ outputMSV P Sh Φ s) := by
  have he : ySun P Sh Φ w s - outputMSV P Sh Φ s =
      P.θ * P.δ * P.η * w s / den P (P.η - Φ) := by
    unfold ySun outputMSV
    ring
  refine ⟨he, fun hws hEq => ?_⟩
  rw [hEq, sub_self] at he
  have hθ := P.θ_pos.ne'
  have hδ := P.δ_pos.ne'
  have hη := P.η_pos.ne'
  have := (div_eq_zero_iff.mp he.symm).resolve_right hden
  simp [hθ, hδ, hη, hws] at this

/-! ### The determinacy boundary: history-dependent sunspots for `|λ| ≤ 1` -/

/-- O&R Ex. 3(d): `|λ| ≤ 1` exactly when `1 ≤ Φ ≤ 1 + 2η` (the closed indeterminacy region,
including the boundary `Φ = 1` (`λ = 1`) and `Φ = 1 + 2η` (`λ = −1`)). -/
theorem abs_lambda_le_one_iff {η Φ : ℝ} (hη : 0 < η) :
    |(η + 1 - Φ) / η| ≤ 1 ↔ 1 ≤ Φ ∧ Φ ≤ 1 + 2 * η := by
  rw [abs_div, abs_of_pos hη, div_le_iff₀ hη, one_mul, abs_le]
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> linarith
  · rintro ⟨h1, h2⟩; constructor <;> linarith

/-- O&R Ex. 3(d): the sunspot component of the expected price level with a history-dependent
revision, `x_{s :: h} = λ x_h + w_s(h)`, `x_{[]} = 0`. -/
def sunspotLevelH (lam : ℝ) (w : S → List S → ℝ) : List S → ℝ
  | [] => 0
  | s :: h => lam * sunspotLevelH lam w h + w s h

/-- O&R Ex. 3(d): output at node `s :: h` in a sunspot equilibrium with revision `w_s(h)`. -/
noncomputable def ySunH (P : PooleParams) (Sh : PooleShocks S) (Φ : ℝ) (w : S → List S → ℝ)
    (s : S) (h : List S) : ℝ :=
  P.θ * ((P.η - Φ) * Sh.eps s - P.δ * (Sh.v s - P.η * w s h)) / den P (P.η - Φ)

/-- O&R Ex. 3(d): sunspot output as a variable on the event tree. -/
noncomputable def ySunTree (P : PooleParams) (Sh : PooleShocks S) (Φ : ℝ)
    (w : S → List S → ℝ) : List S → ℝ
  | [] => 0
  | s :: h => ySunH P Sh Φ w s h

/-- O&R Ex. 3(d): the price level in a history-dependent sunspot equilibrium. -/
noncomputable def pSunH (P : PooleParams) (Sh : PooleShocks S) (mbar Φ : ℝ)
    (w : S → List S → ℝ) : List S → ℝ
  | [] => mbar
  | s :: h => mbar + sunspotLevelH (sunLam P Φ) w h + ySunH P Sh Φ w s h / P.θ

/-- O&R Ex. 3(d): the exchange rate in a history-dependent sunspot equilibrium. -/
noncomputable def eSunH (P : PooleParams) (Sh : PooleShocks S) (mbar Φ : ℝ)
    (w : S → List S → ℝ) : List S → ℝ
  | [] => mbar
  | s :: h => pSunH P Sh mbar Φ w (s :: h) + (ySunH P Sh Φ w s h - Sh.eps s) / P.δ

/-- O&R Ex. 3(d): money (the feedback rule) in a history-dependent sunspot equilibrium. -/
noncomputable def mSunH (P : PooleParams) (Sh : PooleShocks S) (mbar Φ : ℝ)
    (w : S → List S → ℝ) (g : List S) : ℝ :=
  mbar + Φ * (eSunH P Sh mbar Φ w g - mbar)

/-- O&R Ex. 3(d): the interest rate (UIP) in a history-dependent sunspot equilibrium. -/
noncomputable def iSunH (P : PooleParams) (Sh : PooleShocks S) (mbar Φ : ℝ)
    (w : S → List S → ℝ) (g : List S) : ℝ :=
  nodeEx Sh (eSunH P Sh mbar Φ w) g - eSunH P Sh mbar Φ w g

/-- O&R Ex. 3(d): with mean-zero revisions, sunspot output has conditional mean zero. -/
theorem expect_ySunH (P : PooleParams) (Sh : PooleShocks S) (Φ : ℝ) {w : S → List S → ℝ}
    (hw : ∀ h, expect Sh (fun s => w s h) = 0) (h : List S) :
    expect Sh (fun s => ySunH P Sh Φ w s h) = 0 := by
  have hf : (fun s => ySunH P Sh Φ w s h) = fun s =>
      (P.θ * (P.η - Φ) / den P (P.η - Φ)) * Sh.eps s +
        (-(P.θ * P.δ) / den P (P.η - Φ)) * Sh.v s +
        (P.θ * P.δ * P.η / den P (P.η - Φ)) * w s h := by
    funext s
    unfold ySunH
    ring
  rw [hf, expect_add, expect_add, expect_const_mul, expect_const_mul, expect_const_mul,
    expect_eps, expect_v, hw h]
  ring

/-- O&R Ex. 3(d): `E_{t−1} p_t = m̄ + x_h` in the history-dependent sunspot equilibrium. -/
theorem nodeEx_pSunH (P : PooleParams) (Sh : PooleShocks S) (mbar Φ : ℝ)
    {w : S → List S → ℝ} (hw : ∀ h, expect Sh (fun s => w s h) = 0) (h : List S) :
    nodeEx Sh (pSunH P Sh mbar Φ w) h = mbar + sunspotLevelH (sunLam P Φ) w h := by
  rw [nodeEx_eq_expect]
  simp only [pSunH]
  rw [expect_add, expect_const, expect_div_const, expect_ySunH P Sh Φ hw, zero_div, add_zero]

/-- O&R Ex. 3(d): `E_{t−1} e_t = m̄ + x_h` in the history-dependent sunspot equilibrium. -/
theorem nodeEx_eSunH (P : PooleParams) (Sh : PooleShocks S) (mbar Φ : ℝ)
    {w : S → List S → ℝ} (hw : ∀ h, expect Sh (fun s => w s h) = 0) (h : List S) :
    nodeEx Sh (eSunH P Sh mbar Φ w) h = mbar + sunspotLevelH (sunLam P Φ) w h := by
  rw [nodeEx_eq_expect]
  simp only [eSunH, pSunH]
  rw [expect_add, expect_add, expect_const, expect_div_const, expect_div_const, expect_sub,
    expect_eps, expect_ySunH P Sh Φ hw]
  ring

/-- O&R Ex. 3(d): for any `Φ` away from the pole and any mean-zero history-dependent revision
`w`, the sunspot allocation is an equilibrium on the event tree. -/
theorem sunspotH_isEqm (P : PooleParams) (Sh : PooleShocks S) (mbar Φ : ℝ)
    (hden : den P (P.η - Φ) ≠ 0) {w : S → List S → ℝ}
    (hw : ∀ h, expect Sh (fun s => w s h) = 0) :
    IsEqm P Sh (feedbackPolicy mbar Φ) (pSunH P Sh mbar Φ w) (eSunH P Sh mbar Φ w)
      (ySunTree P Sh Φ w) (mSunH P Sh mbar Φ w) (iSunH P Sh mbar Φ w) := by
  intro s h
  have hθ := P.θ_pos.ne'
  have hδ := P.δ_pos.ne'
  have hη := P.η_pos.ne'
  have hY : ySunH P Sh Φ w s h * den P (P.η - Φ) =
      P.θ * ((P.η - Φ) * Sh.eps s - P.δ * (Sh.v s - P.η * w s h)) := by
    unfold ySunH
    exact div_mul_cancel₀ _ hden
  refine ⟨rfl, ?_, ?_, ?_, rfl⟩
  · rw [nodeEx_pSunH P Sh mbar Φ hw]
    simp only [ySunTree, pSunH]
    field_simp
    ring
  · simp only [ySunTree, eSunH]
    field_simp
    ring
  · unfold mSunH iSunH
    rw [nodeEx_eSunH P Sh mbar Φ hw]
    simp only [ySunTree, eSunH, pSunH, sunspotLevelH]
    unfold sunLam
    unfold den at hY
    field_simp
    linear_combination (-1 : ℝ) * hY

/-- O&R Ex. 3(d): a bounded "martingale-type" sunspot level,
`x_{s :: h} = λ x_h + (1 − |x_h|) g_s`, `x_{[]} = 0`. -/
noncomputable def boundedLevel (lam : ℝ) (g : S → ℝ) : List S → ℝ
  | [] => 0
  | s :: h => lam * boundedLevel lam g h + (1 - |boundedLevel lam g h|) * g s

/-- O&R Ex. 3(d): the history-dependent revision `w_s(h) = (1 − |x_h|) g_s` generating
`boundedLevel`. -/
noncomputable def martRev (lam : ℝ) (g : S → ℝ) (s : S) (h : List S) : ℝ :=
  (1 - |boundedLevel lam g h|) * g s

omit [Fintype S] in
/-- O&R Ex. 3(d): for `|λ| ≤ 1` and `|g| ≤ 1` the level stays in `[−1, 1]` at every node. -/
theorem abs_boundedLevel_le {lam : ℝ} (hlam : |lam| ≤ 1) {g : S → ℝ} (hg : ∀ s, |g s| ≤ 1)
    (h : List S) : |boundedLevel lam g h| ≤ 1 := by
  induction h with
  | nil => simp [boundedLevel]
  | cons s h ih =>
    simp only [boundedLevel]
    have h0 : 0 ≤ 1 - |boundedLevel lam g h| := by linarith
    calc |lam * boundedLevel lam g h + (1 - |boundedLevel lam g h|) * g s|
        ≤ |lam| * |boundedLevel lam g h| + (1 - |boundedLevel lam g h|) * |g s| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_mul, abs_of_nonneg h0]
      _ ≤ 1 * |boundedLevel lam g h| + (1 - |boundedLevel lam g h|) * 1 := by
          have := abs_nonneg (boundedLevel lam g h)
          have := mul_le_mul_of_nonneg_right hlam this
          have := mul_le_mul_of_nonneg_left (hg s) h0
          linarith
      _ = 1 := by ring

omit [Fintype S] in
/-- O&R Ex. 3(d): `boundedLevel` is the sunspot level generated by the revisions `martRev`. -/
theorem sunspotLevelH_martRev (lam : ℝ) (g : S → ℝ) (h : List S) :
    sunspotLevelH lam (martRev lam g) h = boundedLevel lam g h := by
  induction h with
  | nil => rfl
  | cons s h ih =>
    simp only [sunspotLevelH, boundedLevel, martRev, ih]

/-- O&R Ex. 3(d): the revisions `martRev` have conditional mean zero when `E g = 0`. -/
theorem expect_martRev (Sh : PooleShocks S) (lam : ℝ) {g : S → ℝ} (hg : expect Sh g = 0)
    (h : List S) : expect Sh (fun s => martRev lam g s h) = 0 := by
  unfold martRev
  rw [expect_const_mul, hg, mul_zero]

/-- O&R Ex. 3(d), the boundary settled (and the whole closed region): for
`1 ≤ Φ ≤ 1 + 2η` — including `Φ = 1` (`λ = 1`) and `Φ = 1 + 2η` (`λ = −1`) — away from the
pole, every mean-zero `g` with `|g| ≤ 1` yields an equilibrium with bounded price level and
exchange rate whose output at the first node is `outputMSV + θ δ η g/den`. -/
theorem boundary_sunspot_eqm (P : PooleParams) (Sh : PooleShocks S) (mbar Φ : ℝ)
    (hreg : 1 ≤ Φ ∧ Φ ≤ 1 + 2 * P.η) (hden : den P (P.η - Φ) ≠ 0) {g : S → ℝ}
    (hg0 : expect Sh g = 0) (hg1 : ∀ s, |g s| ≤ 1) :
    IsEqm P Sh (feedbackPolicy mbar Φ) (pSunH P Sh mbar Φ (martRev (sunLam P Φ) g))
      (eSunH P Sh mbar Φ (martRev (sunLam P Φ) g)) (ySunTree P Sh Φ (martRev (sunLam P Φ) g))
      (mSunH P Sh mbar Φ (martRev (sunLam P Φ) g))
      (iSunH P Sh mbar Φ (martRev (sunLam P Φ) g)) ∧
    Bounded (pSunH P Sh mbar Φ (martRev (sunLam P Φ) g)) ∧
    Bounded (eSunH P Sh mbar Φ (martRev (sunLam P Φ) g)) ∧
    ∀ s, ySunTree P Sh Φ (martRev (sunLam P Φ) g) [s] =
      outputMSV P Sh Φ s + P.θ * P.δ * P.η * g s / den P (P.η - Φ) := by
  have hlam : |sunLam P Φ| ≤ 1 := (abs_lambda_le_one_iff P.η_pos).mpr hreg
  set w := martRev (sunLam P Φ) g
  have hw : ∀ h, expect Sh (fun s => w s h) = 0 := expect_martRev Sh _ hg0
  have hwb : ∀ s h, |w s h| ≤ 1 := by
    intro s h
    have h1 := abs_boundedLevel_le hlam hg1 h
    have h0 : 0 ≤ 1 - |boundedLevel (sunLam P Φ) g h| := by linarith
    simp only [w, martRev]
    rw [abs_mul, abs_of_nonneg h0]
    have h2 : (1 - |boundedLevel (sunLam P Φ) g h|) * |g s| ≤ 1 * 1 :=
      mul_le_mul (by linarith [abs_nonneg (boundedLevel (sunLam P Φ) g h)]) (hg1 s)
        (abs_nonneg _) (by norm_num)
    linarith
  have hθ := P.θ_pos
  have hδ := P.δ_pos
  set K := ∑ s, |outputMSV P Sh Φ s| + |P.θ * P.δ * P.η / den P (P.η - Φ)|
  have hyb : ∀ s h, |ySunH P Sh Φ w s h| ≤ K := by
    intro s h
    have he : ySunH P Sh Φ w s h =
        outputMSV P Sh Φ s + P.θ * P.δ * P.η / den P (P.η - Φ) * w s h := by
      unfold ySunH outputMSV
      ring
    rw [he]
    have h1 := Finset.single_le_sum (f := fun s => |outputMSV P Sh Φ s|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ s)
    have h2 : |P.θ * P.δ * P.η / den P (P.η - Φ) * w s h| ≤
        |P.θ * P.δ * P.η / den P (P.η - Φ)| := by
      rw [abs_mul]
      have := hwb s h
      have := abs_nonneg (P.θ * P.δ * P.η / den P (P.η - Φ))
      nlinarith
    calc _ ≤ |outputMSV P Sh Φ s| + |P.θ * P.δ * P.η / den P (P.η - Φ) * w s h| :=
          abs_add_le _ _
      _ ≤ K := by simp only [K]; linarith
  have hlev : ∀ h, |sunspotLevelH (sunLam P Φ) w h| ≤ 1 := fun h => by
    simp only [w]
    rw [sunspotLevelH_martRev]
    exact abs_boundedLevel_le hlam hg1 h
  have hK : 0 ≤ K := by
    have := Finset.sum_nonneg (s := Finset.univ) fun s _ => abs_nonneg (outputMSV P Sh Φ s)
    have := abs_nonneg (P.θ * P.δ * P.η / den P (P.η - Φ))
    simp only [K]
    linarith
  have hE : ∑ s, |Sh.eps s| ≥ 0 := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hp : ∀ x, |pSunH P Sh mbar Φ w x| ≤ |mbar| + 1 + K / P.θ := by
    intro x
    cases x with
    | nil =>
      simp only [pSunH]
      have : 0 ≤ K / P.θ := by positivity
      linarith
    | cons s h =>
      simp only [pSunH]
      have h1 := hlev h
      have h2 : |ySunH P Sh Φ w s h / P.θ| ≤ K / P.θ := by
        rw [abs_div, abs_of_pos hθ]
        exact div_le_div_of_nonneg_right (hyb s h) hθ.le
      calc _ ≤ |mbar + sunspotLevelH (sunLam P Φ) w h| + |ySunH P Sh Φ w s h / P.θ| :=
            abs_add_le _ _
        _ ≤ |mbar| + |sunspotLevelH (sunLam P Φ) w h| + |ySunH P Sh Φ w s h / P.θ| := by
            linarith [abs_add_le mbar (sunspotLevelH (sunLam P Φ) w h)]
        _ ≤ _ := by linarith
  refine ⟨sunspotH_isEqm P Sh mbar Φ hden hw, ⟨_, hp⟩,
    ⟨|mbar| + 1 + K / P.θ + (K + ∑ s, |Sh.eps s|) / P.δ, fun x => ?_⟩, fun s => ?_⟩
  · have hq : 0 ≤ (K + ∑ s, |Sh.eps s|) / P.δ := by positivity
    cases x with
    | nil =>
      simp only [eSunH]
      have : 0 ≤ K / P.θ := by positivity
      linarith
    | cons s h =>
      simp only [eSunH]
      have h1 := hp (s :: h)
      have h3 := Finset.single_le_sum (f := fun s => |Sh.eps s|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ s)
      have h2 : |(ySunH P Sh Φ w s h - Sh.eps s) / P.δ| ≤ (K + ∑ s, |Sh.eps s|) / P.δ := by
        rw [abs_div, abs_of_pos hδ]
        refine div_le_div_of_nonneg_right ?_ hδ.le
        have := abs_sub (ySunH P Sh Φ w s h) (Sh.eps s)
        have := hyb s h
        linarith
      calc _ ≤ |pSunH P Sh mbar Φ w (s :: h)| + |(ySunH P Sh Φ w s h - Sh.eps s) / P.δ| :=
            abs_add_le _ _
        _ ≤ _ := by linarith
  · simp only [ySunTree, ySunH, w, martRev, boundedLevel, abs_zero, sub_zero, one_mul]
    unfold outputMSV
    ring

/-- O&R Ex. 3(d), the exact determinacy result: away from the pole, and provided the state
space carries some nonzero mean-zero variable, output is the same in every bounded
equilibrium (it equals `outputMSV`) if and only if `Φ < 1` or `Φ > 1 + 2η`. On the boundary
`Φ = 1`, `Φ = 1 + 2η` the equilibrium is indeterminate. -/
theorem bounded_eqm_output_unique_iff (P : PooleParams) (Sh : PooleShocks S) (mbar Φ : ℝ)
    (hden : den P (P.η - Φ) ≠ 0) (hnd : ∃ g : S → ℝ, expect Sh g = 0 ∧ ∃ s, g s ≠ 0) :
    (∀ p e y m i : List S → ℝ, IsEqm P Sh (feedbackPolicy mbar Φ) p e y m i → Bounded p →
      ∀ s h, y (s :: h) = outputMSV P Sh Φ s) ↔ (Φ < 1 ∨ 1 + 2 * P.η < Φ) := by
  constructor
  · intro hu
    by_contra hdet
    push Not at hdet
    obtain ⟨g, hg0, s0, hs0⟩ := hnd
    set c := 1 + ∑ s, |g s|
    have hc : 0 < c := by
      have := Finset.sum_nonneg (s := Finset.univ) fun s _ => abs_nonneg (g s)
      simp only [c]
      linarith
    have hg0' : expect Sh (fun s => g s / c) = 0 := by rw [expect_div_const, hg0, zero_div]
    have hg1' : ∀ s, |g s / c| ≤ 1 := by
      intro s
      rw [abs_div, abs_of_pos hc, div_le_one hc]
      have := Finset.single_le_sum (f := fun s => |g s|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ s)
      simp only [c]
      linarith
    obtain ⟨hE, hb, _, hy⟩ :=
      boundary_sunspot_eqm P Sh mbar Φ ⟨hdet.1, hdet.2⟩ hden hg0' hg1'
    have h1 := hu _ _ _ _ _ hE hb s0 []
    rw [hy s0] at h1
    have h2 : P.θ * P.δ * P.η * (g s0 / c) / den P (P.η - Φ) = 0 := by linarith
    have hθ := P.θ_pos.ne'
    have hδ := P.δ_pos.ne'
    have hη := P.η_pos.ne'
    rcases div_eq_zero_iff.mp h2 with h3 | h3
    · simp [hθ, hδ, hη, hs0, hc.ne'] at h3
    · exact hden h3
  · intro hdet p e y m i hE hb s h
    exact (feedback_eqm_unique hdet hden hE hb s h).1

/-- O&R Ex. 3(d): at the boundary `Φ = 1` (`λ = 1`) bounded sunspot equilibria exist. -/
theorem sunspot_at_phi_one (P : PooleParams) (Sh : PooleShocks S) (mbar : ℝ)
    (hden : den P (P.η - 1) ≠ 0) {g : S → ℝ} (hg0 : expect Sh g = 0)
    (hg1 : ∀ s, |g s| ≤ 1) :
    sunLam P 1 = 1 ∧ IsEqm P Sh (feedbackPolicy mbar 1)
      (pSunH P Sh mbar 1 (martRev (sunLam P 1) g)) (eSunH P Sh mbar 1 (martRev (sunLam P 1) g))
      (ySunTree P Sh 1 (martRev (sunLam P 1) g)) (mSunH P Sh mbar 1 (martRev (sunLam P 1) g))
      (iSunH P Sh mbar 1 (martRev (sunLam P 1) g)) ∧
    Bounded (pSunH P Sh mbar 1 (martRev (sunLam P 1) g)) := by
  have hη := P.η_pos
  obtain ⟨h1, h2, _, _⟩ := boundary_sunspot_eqm P Sh mbar 1 ⟨le_refl _, by linarith⟩ hden hg0 hg1
  refine ⟨?_, h1, h2⟩
  unfold sunLam
  field_simp
  ring

/-- O&R Ex. 3(d): at the boundary `Φ = 1 + 2η` (`λ = −1`) bounded sunspot equilibria exist. -/
theorem sunspot_at_phi_one_add_two_eta (P : PooleParams) (Sh : PooleShocks S) (mbar : ℝ)
    (hden : den P (P.η - (1 + 2 * P.η)) ≠ 0) {g : S → ℝ} (hg0 : expect Sh g = 0)
    (hg1 : ∀ s, |g s| ≤ 1) :
    sunLam P (1 + 2 * P.η) = -1 ∧ IsEqm P Sh (feedbackPolicy mbar (1 + 2 * P.η))
      (pSunH P Sh mbar (1 + 2 * P.η) (martRev (sunLam P (1 + 2 * P.η)) g))
      (eSunH P Sh mbar (1 + 2 * P.η) (martRev (sunLam P (1 + 2 * P.η)) g))
      (ySunTree P Sh (1 + 2 * P.η) (martRev (sunLam P (1 + 2 * P.η)) g))
      (mSunH P Sh mbar (1 + 2 * P.η) (martRev (sunLam P (1 + 2 * P.η)) g))
      (iSunH P Sh mbar (1 + 2 * P.η) (martRev (sunLam P (1 + 2 * P.η)) g)) ∧
    Bounded (pSunH P Sh mbar (1 + 2 * P.η) (martRev (sunLam P (1 + 2 * P.η)) g)) := by
  have hη := P.η_pos
  obtain ⟨h1, h2, _, _⟩ :=
    boundary_sunspot_eqm P Sh mbar (1 + 2 * P.η) ⟨by linarith, le_refl _⟩ hden hg0 hg1
  refine ⟨?_, h1, h2⟩
  unfold sunLam
  field_simp
  ring

end ObstfeldRogoff.NominalRigidities.PooleRegimeChoice
