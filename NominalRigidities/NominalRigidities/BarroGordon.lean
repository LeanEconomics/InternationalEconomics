/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Order.Monotone.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

/-!
# The Kydland–Prescott / Barro–Gordon model of monetary credibility

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §9.5.1
(pp. 635–639), §9.5.3 (pp. 644–646) and Exercise 5 (p. 658).

Supply shocks `z` live on a finite state space `S` with probabilities `p` (`p ≥ 0`,
`Σ p = 1`) and conditional mean zero (`E z = 0`); expectations are finite sums `expect p f`.

* (26)–(31): with `y = ȳ − (w − p) − z`, `w = E p` and target `ȳ + k`, the loss is
  `L = (π − πᵉ − z − k)² + χ π²` (`loss_derivation`).
* (32)–(35), one-shot game: the loss is strictly convex in `π` (second derivative
  `2(1 + χ) > 0`), the first-order condition is necessary and sufficient, the best response
  (33) is the unique minimiser, and the rational-expectations equilibrium is **unique**:
  `πᵉ = k/χ`, `π = k/χ + z/(1 + χ)` (`oneShot_eqm_iff`).
* (36), commitment: among **all** state-contingent rules `π : S → ℝ` with `πᵉ = E π`, the
  expected loss is `V_C + χ (E π)² + (1 + χ) E(π − E π − z/(1 + χ))²`, so the rule
  `π = z/(1 + χ)` is optimal, and it is the unique optimum on the support of `p`.
  Loss rankings: `V_C = k² + χσ²/(1 + χ)`, discretion `V_D = V_C + k²/χ`, zero inflation
  `V_0 = k² + σ²`; `V_C ≤ V_0`, `V_C < V_D`, and `V_0 < V_D ↔ σ²/(1 + χ) < k²/χ`.
* §9.5.3, (45)–(48), Alesina's partisan model: unique equilibrium `πᵉ = P/χᴸ`, surprises
  `(1 − P)/χᴸ` and `−P/χᴸ`; a known winner gives no surprise.
* Exercise 5 (central bank secrecy), solved for a general finite distribution of `λ` and then
  for the book's two-point case (`E L = k`, `k − 1/2`, `k + 1` versus `k`).
-/

namespace ObstfeldRogoff.NominalRigidities.BarroGordon

open Finset

variable {S : Type*} [Fintype S]

/-! ## Finite expectations -/

/-- Expectation over a finite state space with probabilities `p` (O&R §9.5.1, the operator
`E_{t−1}` of (27), (34)). -/
def expect (p f : S → ℝ) : ℝ := ∑ s, p s * f s

/-- Linearity of `expect` in sums (O&R §9.5.1). -/
theorem expect_add (p f g : S → ℝ) :
    expect p (fun s => f s + g s) = expect p f + expect p g := by
  unfold expect
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun s _ => by ring

/-- Linearity of `expect` in differences (O&R §9.5.1). -/
theorem expect_sub (p f g : S → ℝ) :
    expect p (fun s => f s - g s) = expect p f - expect p g := by
  unfold expect
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun s _ => by ring

/-- Homogeneity of `expect` (O&R §9.5.1). -/
theorem expect_const_mul (p f : S → ℝ) (c : ℝ) :
    expect p (fun s => c * f s) = c * expect p f := by
  unfold expect
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun s _ => by ring

/-- The expectation of a constant is the constant (O&R §9.5.1). -/
theorem expect_const (p : S → ℝ) (h1 : ∑ s, p s = 1) (c : ℝ) :
    expect p (fun _ => c) = c := by
  unfold expect
  rw [← Finset.sum_mul, h1, one_mul]

/-- Monotonicity of `expect` (O&R §9.5.1). -/
theorem expect_mono (p f g : S → ℝ) (hp : ∀ s, 0 ≤ p s) (hfg : ∀ s, f s ≤ g s) :
    expect p f ≤ expect p g :=
  Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hfg s) (hp s)

/-- Nonnegativity of `expect` (O&R §9.5.1). -/
theorem expect_nonneg (p f : S → ℝ) (hp : ∀ s, 0 ≤ p s) (hf : ∀ s, 0 ≤ f s) :
    0 ≤ expect p f :=
  Finset.sum_nonneg fun s _ => mul_nonneg (hp s) (hf s)

/-- A nonnegative function with zero expectation vanishes on the support (O&R §9.5.1). -/
theorem expect_eq_zero_iff (p f : S → ℝ) (hp : ∀ s, 0 ≤ p s) (hf : ∀ s, 0 ≤ f s) :
    expect p f = 0 ↔ ∀ s, 0 < p s → f s = 0 := by
  unfold expect
  rw [Finset.sum_eq_zero_iff_of_nonneg fun s _ => mul_nonneg (hp s) (hf s)]
  constructor
  · intro h s hs
    have := h s (Finset.mem_univ s)
    rcases mul_eq_zero.1 this with h0 | h0
    · exact absurd h0 hs.ne'
    · exact h0
  · intro h s _
    rcases (hp s).lt_or_eq with hs | hs
    · rw [h s hs, mul_zero]
    · rw [← hs, zero_mul]

/-- Two functions that agree on the support have the same expectation (O&R §9.5.1). -/
theorem expect_congr_support (p f g : S → ℝ) (hfg : ∀ s, 0 < p s → f s = g s)
    (hp : ∀ s, 0 ≤ p s) : expect p f = expect p g := by
  unfold expect
  refine Finset.sum_congr rfl fun s _ => ?_
  rcases (hp s).lt_or_eq with hs | hs
  · rw [hfg s hs]
  · rw [← hs, zero_mul, zero_mul]

/-! ## The model, (26)–(31) -/

/-- O&R (31), p. 637: the one-period loss `(π − πᵉ − z − k)² + χπ²`. -/
def bgLoss (χ k π πe z : ℝ) : ℝ := (π - πe - z - k) ^ 2 + χ * π ^ 2

/-- O&R (26)–(31), pp. 636–637: with output `y = ȳ − (w − p) − z` (26), the wage set at the
expected price level `w = E p` (27), inflation `π = p − p₋₁` (28), expected inflation
`πᵉ = E p − p₋₁`, and target output `ȳ + k` (30), the loss (29) `(y − (ȳ + k))² + χπ²` is (31). -/
theorem loss_derivation (ybar k χ z w p pprev : ℝ) :
    ((ybar - (w - p) - z) - (ybar + k)) ^ 2 + χ * (p - pprev) ^ 2 =
      bgLoss χ k (p - pprev) (w - pprev) z := by
  unfold bgLoss
  ring

/-- O&R (33), p. 637: the policymaker's best response `(k + πᵉ + z)/(1 + χ)`. -/
noncomputable def bestResponse (χ k πe z : ℝ) : ℝ := (k + πe + z) / (1 + χ)

/-- O&R (31)–(33): completing the square, `L(π) = (1 + χ)(π − π̂)² + χ(k + πᵉ + z)²/(1 + χ)`
with `π̂` the best response (33). -/
theorem bgLoss_eq_sq (χ k π πe z : ℝ) (hχ : 0 < 1 + χ) :
    bgLoss χ k π πe z = (1 + χ) * (π - bestResponse χ k πe z) ^ 2 +
      χ * (k + πe + z) ^ 2 / (1 + χ) := by
  unfold bgLoss bestResponse
  field_simp
  ring

/-- O&R (53), p. 649: the minimised loss is `χ(k + πᵉ + z)²/(1 + χ)`. -/
theorem bgLoss_bestResponse (χ k πe z : ℝ) (hχ : 0 < 1 + χ) :
    bgLoss χ k (bestResponse χ k πe z) πe z = χ * (k + πe + z) ^ 2 / (1 + χ) := by
  rw [bgLoss_eq_sq χ k _ πe z hχ, sub_self]
  ring

/-- O&R (33): the best response is a global minimiser of the loss (31). -/
theorem bestResponse_isMin (χ k π πe z : ℝ) (hχ : 0 < 1 + χ) :
    bgLoss χ k (bestResponse χ k πe z) πe z ≤ bgLoss χ k π πe z := by
  rw [bgLoss_eq_sq χ k π πe z hχ, bgLoss_bestResponse χ k πe z hχ]
  have := mul_nonneg hχ.le (sq_nonneg (π - bestResponse χ k πe z))
  linarith

/-- O&R (33): the best response is the unique minimiser (strict convexity). -/
theorem eq_bestResponse_of_le (χ k π πe z : ℝ) (hχ : 0 < 1 + χ)
    (h : bgLoss χ k π πe z ≤ bgLoss χ k (bestResponse χ k πe z) πe z) :
    π = bestResponse χ k πe z := by
  rw [bgLoss_eq_sq χ k π πe z hχ, bgLoss_bestResponse χ k πe z hχ] at h
  have h2 : (1 + χ) * (π - bestResponse χ k πe z) ^ 2 ≤ 0 := by linarith
  have h3 : (π - bestResponse χ k πe z) ^ 2 = 0 :=
    le_antisymm (nonpos_of_mul_nonpos_right (by linarith) hχ) (sq_nonneg _)
  exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h3)

/-- O&R (32), p. 637: the derivative of the loss (31) in `π` is
`2(π − πᵉ − z − k) + 2χπ`. -/
theorem hasDerivAt_bgLoss (χ k π πe z : ℝ) :
    HasDerivAt (fun x => bgLoss χ k x πe z) (2 * (π - πe - z - k) + 2 * χ * π) π := by
  have h1 : HasDerivAt (fun x : ℝ => x - πe - z - k) 1 π :=
    ((((hasDerivAt_id π).sub_const πe).sub_const z).sub_const k)
  have h2 := h1.pow 2
  have h3 := ((hasDerivAt_id π).pow 2).const_mul χ
  have h4 := HasDerivAt.add h2 h3
  convert h4 using 1
  · ext x
    simp [bgLoss]
  · simp
    ring

/-- O&R p. 638 ("ignoring second-order conditions"): the derivative of the marginal loss is
`2(1 + χ)`, positive whenever `1 + χ > 0`. -/
theorem hasDerivAt_marginal_bgLoss (χ k π πe z : ℝ) :
    HasDerivAt (fun x => 2 * (x - πe - z - k) + 2 * χ * x) (2 * (1 + χ)) π := by
  have h1 : HasDerivAt (fun x : ℝ => x - πe - z - k) 1 π :=
    ((((hasDerivAt_id π).sub_const πe).sub_const z).sub_const k)
  have h2 := HasDerivAt.add (h1.const_mul 2) ((hasDerivAt_id π).const_mul (2 * χ))
  convert h2 using 1
  · ext x
    simp
  · ring

/-- O&R (32)–(33): the first-order condition holds exactly at the best response. -/
theorem foc_iff (χ k π πe z : ℝ) (hχ : 0 < 1 + χ) :
    2 * (π - πe - z - k) + 2 * χ * π = 0 ↔ π = bestResponse χ k πe z := by
  unfold bestResponse
  rw [eq_div_iff hχ.ne']
  constructor <;> intro h <;> linarith

/-- O&R (32): the first-order condition is necessary and sufficient for a global minimum. -/
theorem isMin_iff_foc (χ k π πe z : ℝ) (hχ : 0 < 1 + χ) :
    (∀ x, bgLoss χ k π πe z ≤ bgLoss χ k x πe z) ↔
      2 * (π - πe - z - k) + 2 * χ * π = 0 := by
  rw [foc_iff χ k π πe z hχ]
  constructor
  · intro h
    exact eq_bestResponse_of_le χ k π πe z hχ (h _)
  · rintro rfl x
    exact bestResponse_isMin χ k x πe z hχ

/-! ## The one-shot game, (34)–(35) -/

/-- O&R §9.5.1.2, pp. 637–638: a one-shot equilibrium is a state-contingent inflation choice
`π` that minimises (31) in every state given `πᵉ`, with rational expectations `πᵉ = E π`. -/
def IsOneShotEqm (p z : S → ℝ) (χ k : ℝ) (π : S → ℝ) (πe : ℝ) : Prop :=
  (∀ s x, bgLoss χ k (π s) πe (z s) ≤ bgLoss χ k x πe (z s)) ∧ πe = expect p π

/-- O&R (34)–(35), p. 638: the one-shot game has a **unique** equilibrium,
`πᵉ = k/χ` and `π = k/χ + z/(1 + χ)` in every state. -/
theorem oneShot_eqm_iff (p z : S → ℝ) (χ k : ℝ) (hχ : 0 < χ) (h1 : ∑ s, p s = 1)
    (hz : expect p z = 0) (π : S → ℝ) (πe : ℝ) :
    IsOneShotEqm p z χ k π πe ↔ πe = k / χ ∧ ∀ s, π s = k / χ + z s / (1 + χ) := by
  have hχ1 : 0 < 1 + χ := by linarith
  have hBR : ∀ e s, bestResponse χ k e (z s) = (k + e) / (1 + χ) + z s / (1 + χ) := by
    intro e s
    unfold bestResponse
    ring
  constructor
  · rintro ⟨hopt, hre⟩
    have hπ : ∀ s, π s = (k + πe) / (1 + χ) + z s / (1 + χ) := fun s =>
      (eq_bestResponse_of_le χ k (π s) πe (z s) hχ1 (hopt s _)).trans (hBR πe s)
    have hE : expect p π = (k + πe) / (1 + χ) := by
      have : expect p π = expect p (fun s => (k + πe) / (1 + χ) + z s * (1 / (1 + χ))) := by
        unfold expect
        exact Finset.sum_congr rfl fun s _ => by rw [hπ s]; ring
      rw [this, expect_add, expect_const p h1]
      have h2 : expect p (fun s => z s * (1 / (1 + χ))) = expect p z * (1 / (1 + χ)) := by
        rw [mul_comm, ← expect_const_mul]
        unfold expect
        exact Finset.sum_congr rfl fun s _ => by ring
      rw [h2, hz]
      ring
    have hpe : πe = k / χ := by
      rw [hE] at hre
      field_simp at hre ⊢
      linarith
    refine ⟨hpe, fun s => ?_⟩
    rw [hπ s, hpe]
    field_simp
    ring
  · rintro ⟨hpe, hπ⟩
    refine ⟨fun s x => ?_, ?_⟩
    · have : π s = bestResponse χ k πe (z s) := by
        rw [hπ s, hBR, hpe]
        field_simp
        ring
      rw [this]
      exact bestResponse_isMin χ k x πe (z s) hχ1
    · have : expect p π = expect p (fun s => k / χ + z s * (1 / (1 + χ))) := by
        unfold expect
        exact Finset.sum_congr rfl fun s _ => by rw [hπ s]; ring
      rw [this, expect_add, expect_const p h1]
      have h2 : expect p (fun s => z s * (1 / (1 + χ))) = expect p z * (1 / (1 + χ)) := by
        rw [mul_comm, ← expect_const_mul]
        unfold expect
        exact Finset.sum_congr rfl fun s _ => by ring
      rw [h2, hz, hpe]
      ring

/-- O&R (34), p. 638: expected inflation `k/χ` rises with the wedge `k`. -/
theorem expInfl_strictMono_k (χ : ℝ) (hχ : 0 < χ) : StrictMono fun k : ℝ => k / χ :=
  fun _ _ h => div_lt_div_of_pos_right h hχ

/-- O&R (34), p. 638: expected inflation `k/χ` falls with the weight `χ` (for `k > 0`). -/
theorem expInfl_strictAntiOn_chi (k : ℝ) (hk : 0 < k) :
    StrictAntiOn (fun χ : ℝ => k / χ) (Set.Ioi 0) :=
  fun _ ha _ _ h => div_lt_div_of_pos_left hk ha h

/-- O&R p. 638: in equilibrium the inflation surprise is `z/(1 + χ)`, and the output gap
`y − ȳ = π − πᵉ − z` is `−χz/(1 + χ)`; the authorities never systematically surprise. -/
theorem oneShot_surprise (χ k z : ℝ) (hχ : 0 < 1 + χ) :
    (k / χ + z / (1 + χ)) - k / χ = z / (1 + χ) ∧
      (k / χ + z / (1 + χ)) - k / χ - z = -(χ * z) / (1 + χ) := by
  refine ⟨by ring, ?_⟩
  field_simp
  ring

/-- O&R p. 638: with `πᵉ = 0` the marginal loss of inflation at `π = 0` is `−2(z + k)`, so for
`z = 0` and `k > 0` zero inflation is not a best response (the intuition for (34)). -/
theorem zero_not_bestResponse (χ k : ℝ) (hk : 0 < k) (hχ : 0 < 1 + χ) :
    ¬ ∀ x, bgLoss χ k 0 0 0 ≤ bgLoss χ k x 0 0 := by
  rw [isMin_iff_foc χ k 0 0 0 hχ]
  intro h
  linarith

/-! ## Commitment, (36) -/

/-- O&R (36), p. 639: expected social loss of a state-contingent rule `π` when expectations are
rational, `πᵉ = E π`. -/
def expLoss (p z : S → ℝ) (χ k : ℝ) (π : S → ℝ) : ℝ :=
  expect p (fun s => bgLoss χ k (π s) (expect p π) (z s))

/-- O&R (36), p. 639: the commitment value `V_C = k² + χσ²/(1 + χ)`. -/
noncomputable def valueCommit (χ k σ2 : ℝ) : ℝ := k ^ 2 + χ * σ2 / (1 + χ)

/-- O&R (35), p. 638: the discretionary value `V_D = k² + k²/χ + χσ²/(1 + χ)`. -/
noncomputable def valueDiscretion (χ k σ2 : ℝ) : ℝ := k ^ 2 + k ^ 2 / χ + χ * σ2 / (1 + χ)

/-- O&R p. 639: the zero-inflation-rule value `V_0 = k² + σ²`. -/
def valueZero (k σ2 : ℝ) : ℝ := k ^ 2 + σ2

/-- O&R (36): the variance of the supply shock, `σ² = E z²` (as `E z = 0`). -/
def varZ (p z : S → ℝ) : ℝ := expect p (fun s => z s ^ 2)

/-- O&R (36), pp. 639–640: the expected loss of any rule decomposes as
`k² + χ(Eπ)² + E(π − Eπ − z)² + χE(π − Eπ)²` (the cross terms vanish by `E z = 0`). -/
theorem expLoss_decomp (p z : S → ℝ) (χ k : ℝ) (h1 : ∑ s, p s = 1) (hz : expect p z = 0)
    (π : S → ℝ) :
    expLoss p z χ k π = k ^ 2 + χ * expect p π ^ 2 +
      expect p (fun s => (π s - expect p π - z s) ^ 2) +
      χ * expect p (fun s => (π s - expect p π) ^ 2) := by
  set a := expect p π with ha
  have key : expLoss p z χ k π = expect p (fun s =>
      ((k ^ 2 + χ * a ^ 2) + ((π s - a - z s) ^ 2 + χ * (π s - a) ^ 2)) +
        ((2 * χ * a - 2 * k) * π s + (-(2 * χ * a - 2 * k) * a) + 2 * k * z s)) := by
    unfold expLoss
    rw [← ha]
    unfold expect bgLoss
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [key]
  simp only [expect_add, expect_const_mul, expect_const p h1]
  rw [hz, ← ha]
  ring

/-- O&R (36): `(g − z)² + χg² = (1 + χ)(g − z/(1 + χ))² + χz²/(1 + χ)`. -/
theorem sq_split (χ g z : ℝ) (hχ : 0 < 1 + χ) :
    (g - z) ^ 2 + χ * g ^ 2 = (1 + χ) * (g - z / (1 + χ)) ^ 2 + χ * z ^ 2 / (1 + χ) := by
  field_simp
  ring

/-- O&R (36), p. 639: the exact excess loss of an arbitrary rule over commitment,
`E L = V_C + χ(Eπ)² + (1 + χ)E(π − Eπ − z/(1 + χ))²`. -/
theorem expLoss_eq_commit_add (p z : S → ℝ) (χ k : ℝ) (hχ : 0 < 1 + χ) (h1 : ∑ s, p s = 1)
    (hz : expect p z = 0) (π : S → ℝ) :
    expLoss p z χ k π = valueCommit χ k (varZ p z) + χ * expect p π ^ 2 +
      (1 + χ) * expect p (fun s => (π s - expect p π - z s / (1 + χ)) ^ 2) := by
  rw [expLoss_decomp p z χ k h1 hz π]
  have : expect p (fun s => (π s - expect p π - z s) ^ 2) +
      χ * expect p (fun s => (π s - expect p π) ^ 2) =
      (1 + χ) * expect p (fun s => (π s - expect p π - z s / (1 + χ)) ^ 2) +
        χ / (1 + χ) * varZ p z := by
    unfold varZ
    rw [← expect_const_mul, ← expect_const_mul, ← expect_const_mul, ← expect_add, ← expect_add]
    congr 1
    funext s
    rw [sq_split χ (π s - expect p π) (z s) hχ]
    ring
  unfold valueCommit
  rw [add_assoc (k ^ 2 + χ * expect p π ^ 2), this]
  field_simp
  ring

/-- O&R (36): the commitment rule `π = z/(1 + χ)`. -/
noncomputable def commitRule (χ : ℝ) (z : S → ℝ) : S → ℝ := fun s => z s / (1 + χ)

/-- O&R (36): the commitment rule has mean zero. -/
theorem expect_commitRule (p z : S → ℝ) (χ : ℝ) (hz : expect p z = 0) :
    expect p (commitRule χ z) = 0 := by
  have : expect p (commitRule χ z) = expect p (fun s => (1 / (1 + χ)) * z s) := by
    unfold expect commitRule
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [this, expect_const_mul, hz, mul_zero]

/-- O&R (36): the commitment rule attains `V_C = k² + χσ²/(1 + χ)`. -/
theorem expLoss_commitRule (p z : S → ℝ) (χ k : ℝ) (hχ : 0 < 1 + χ) (h1 : ∑ s, p s = 1)
    (hz : expect p z = 0) :
    expLoss p z χ k (commitRule χ z) = valueCommit χ k (varZ p z) := by
  rw [expLoss_eq_commit_add p z χ k hχ h1 hz, expect_commitRule p z χ hz]
  have : expect p (fun s => (commitRule χ z s - 0 - z s / (1 + χ)) ^ 2) = 0 := by
    unfold expect commitRule
    simp
  rw [this]
  ring

/-- O&R (36), p. 639: the commitment rule minimises `E L` among **all** rules `π : S → ℝ`
subject to `πᵉ = E π` (`χ ≥ 0`). -/
theorem commitRule_optimal (p z : S → ℝ) (χ k : ℝ) (hχ : 0 ≤ χ) (hp : ∀ s, 0 ≤ p s)
    (h1 : ∑ s, p s = 1) (hz : expect p z = 0) (π : S → ℝ) :
    expLoss p z χ k (commitRule χ z) ≤ expLoss p z χ k π := by
  have hχ1 : 0 < 1 + χ := by linarith
  rw [expLoss_commitRule p z χ k hχ1 h1 hz, expLoss_eq_commit_add p z χ k hχ1 h1 hz]
  have h2 := expect_nonneg p (fun s => (π s - expect p π - z s / (1 + χ)) ^ 2) hp
    fun s => sq_nonneg _
  have h3 := mul_nonneg hχ (sq_nonneg (expect p π))
  have h4 := mul_nonneg hχ1.le h2
  linarith

/-- O&R (36): the commitment optimum is unique on the support of the shock distribution:
`E L(π) = V_C` iff `π = z/(1 + χ)` in every state of positive probability (`χ > 0`). -/
theorem commitRule_unique (p z : S → ℝ) (χ k : ℝ) (hχ : 0 < χ) (hp : ∀ s, 0 ≤ p s)
    (h1 : ∑ s, p s = 1) (hz : expect p z = 0) (π : S → ℝ) :
    expLoss p z χ k π = valueCommit χ k (varZ p z) ↔
      ∀ s, 0 < p s → π s = z s / (1 + χ) := by
  have hχ1 : 0 < 1 + χ := by linarith
  rw [expLoss_eq_commit_add p z χ k hχ1 h1 hz]
  set f := fun s => (π s - expect p π - z s / (1 + χ)) ^ 2
  have h2 := expect_nonneg p f hp fun s => sq_nonneg _
  have h3 := mul_nonneg hχ.le (sq_nonneg (expect p π))
  constructor
  · intro h
    have hA : χ * expect p π ^ 2 = 0 := by nlinarith
    have hB : expect p f = 0 := by nlinarith
    have ha : expect p π = 0 := by
      rcases mul_eq_zero.1 hA with h0 | h0
      · exact absurd h0 hχ.ne'
      · exact pow_eq_zero_iff two_ne_zero |>.1 h0
    intro s hs
    have := (expect_eq_zero_iff p f hp fun s => sq_nonneg _).1 hB s hs
    simp only [f, ha, sub_zero] at this
    exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 this)
  · intro h
    have hπ : expect p π = expect p (commitRule χ z) :=
      expect_congr_support p π (commitRule χ z) (fun s hs => h s hs) hp
    rw [expect_commitRule p z χ hz] at hπ
    have hB : expect p f = 0 := by
      refine (expect_eq_zero_iff p f hp fun s => sq_nonneg _).2 fun s hs => ?_
      simp only [f, hπ, h s hs]
      ring
    rw [hπ, hB]
    ring

/-- O&R (35): the discretionary equilibrium policy, as a rule. -/
noncomputable def discretionRule (χ k : ℝ) (z : S → ℝ) : S → ℝ := fun s => k / χ + z s / (1 + χ)

/-- O&R (35): the discretionary equilibrium has expected social loss
`V_D = k² + k²/χ + χσ²/(1 + χ)`. -/
theorem expLoss_discretion (p z : S → ℝ) (χ k : ℝ) (hχ : 0 < χ) (h1 : ∑ s, p s = 1)
    (hz : expect p z = 0) :
    expLoss p z χ k (discretionRule χ k z) = valueDiscretion χ k (varZ p z) := by
  have hχ1 : 0 < 1 + χ := by linarith
  have hE : expect p (discretionRule χ k z) = k / χ := by
    have : expect p (discretionRule χ k z) =
        expect p (fun s => k / χ + (1 / (1 + χ)) * z s) := by
      unfold expect discretionRule
      exact Finset.sum_congr rfl fun s _ => by ring
    rw [this, expect_add, expect_const p h1, expect_const_mul, hz, mul_zero, add_zero]
  rw [expLoss_eq_commit_add p z χ k hχ1 h1 hz, hE]
  have : expect p (fun s => (discretionRule χ k z s - k / χ - z s / (1 + χ)) ^ 2) = 0 := by
    unfold expect discretionRule
    simp
  rw [this]
  unfold valueCommit valueDiscretion
  field_simp
  ring

/-- O&R p. 639: the zero-inflation rule has expected loss `V_0 = k² + σ²`. -/
theorem expLoss_zero (p z : S → ℝ) (χ k : ℝ) (h1 : ∑ s, p s = 1) (hz : expect p z = 0) :
    expLoss p z χ k (fun _ => 0) = valueZero k (varZ p z) := by
  rw [expLoss_decomp p z χ k h1 hz, expect_const p h1]
  unfold valueZero varZ expect
  simp only [sub_zero, zero_sub, even_two, Even.neg_pow, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, mul_zero, add_zero, Finset.sum_const_zero]

/-- O&R p. 639: commitment beats the zero-inflation rule, `V_0 − V_C = σ²/(1 + χ) ≥ 0`. -/
theorem valueZero_sub_valueCommit (χ k σ2 : ℝ) (hχ : 0 < 1 + χ) :
    valueZero k σ2 - valueCommit χ k σ2 = σ2 / (1 + χ) := by
  unfold valueZero valueCommit
  field_simp
  ring

/-- O&R (35)–(36): discretion costs exactly `k²/χ` more than commitment. -/
theorem valueDiscretion_sub_valueCommit (χ k σ2 : ℝ) :
    valueDiscretion χ k σ2 - valueCommit χ k σ2 = k ^ 2 / χ := by
  unfold valueDiscretion valueCommit
  ring

/-- O&R p. 639: `V_C < V_D` whenever there is an inflation bias (`k ≠ 0`, `χ > 0`). -/
theorem valueCommit_lt_valueDiscretion (χ k σ2 : ℝ) (hχ : 0 < χ) (hk : k ≠ 0) :
    valueCommit χ k σ2 < valueDiscretion χ k σ2 := by
  have := valueDiscretion_sub_valueCommit χ k σ2
  have : 0 < k ^ 2 / χ := div_pos (by positivity) hχ
  linarith

/-- O&R p. 639: the zero-inflation rule beats discretion iff `σ²/(1 + χ) < k²/χ`. -/
theorem valueZero_lt_valueDiscretion_iff (χ k σ2 : ℝ) (hχ : 0 < 1 + χ) :
    valueZero k σ2 < valueDiscretion χ k σ2 ↔ σ2 / (1 + χ) < k ^ 2 / χ := by
  have h1 := valueZero_sub_valueCommit χ k σ2 hχ
  have h2 := valueDiscretion_sub_valueCommit χ k σ2
  constructor <;> intro h <;> linarith

/-- O&R p. 637 (time inconsistency): if wage setters believe `πᵉ = 0`, the ex post optimum is
`(k + z)/(1 + χ)`, which differs from the commitment rule `z/(1 + χ)` whenever `k ≠ 0`; the
announced rule strictly loses ex post. -/
theorem commitRule_time_inconsistent (χ k z : ℝ) (hχ : 0 < 1 + χ) (hk : k ≠ 0) :
    bestResponse χ k 0 z ≠ z / (1 + χ) ∧
      bgLoss χ k (bestResponse χ k 0 z) 0 z < bgLoss χ k (z / (1 + χ)) 0 z := by
  have hne : bestResponse χ k 0 z ≠ z / (1 + χ) := by
    unfold bestResponse
    intro h
    rw [div_left_inj' hχ.ne'] at h
    exact hk (by linarith)
  refine ⟨hne, ?_⟩
  rcases (bestResponse_isMin χ k (z / (1 + χ)) 0 z hχ).lt_or_eq with h | h
  · exact h
  · exact absurd (eq_bestResponse_of_le χ k _ 0 z hχ h.ge) hne.symm

/-! ## Partisan political business cycles, §9.5.3, (45)–(48) -/

/-- O&R (45), p. 645: the liberal policymaker's loss `−(π − πᵉ − k) + (χᴸ/2)π²`. -/
noncomputable def liberalLoss (χL k π πe : ℝ) : ℝ := -(π - πe - k) + χL / 2 * π ^ 2

/-- O&R (45): completing the square around `1/χᴸ`. -/
theorem liberalLoss_eq (χL k π πe : ℝ) (hχ : 0 < χL) :
    liberalLoss χL k π πe = liberalLoss χL k (1 / χL) πe + χL / 2 * (π - 1 / χL) ^ 2 := by
  unfold liberalLoss
  field_simp
  ring

/-- O&R (47), p. 645: `1/χᴸ` is the liberals' unique best response, whatever `πᵉ`. -/
theorem liberal_isMin_iff (χL k π πe : ℝ) (hχ : 0 < χL) :
    (∀ x, liberalLoss χL k π πe ≤ liberalLoss χL k x πe) ↔ π = 1 / χL := by
  constructor
  · intro h
    have h2 := h (1 / χL)
    rw [liberalLoss_eq χL k π πe hχ] at h2
    have h3 : χL / 2 * (π - 1 / χL) ^ 2 ≤ 0 := by linarith
    have h4 : (π - 1 / χL) ^ 2 = 0 :=
      le_antisymm (nonpos_of_mul_nonpos_right h3 (by positivity)) (sq_nonneg _)
    exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h4)
  · rintro rfl x
    rw [liberalLoss_eq χL k x πe hχ]
    have : 0 ≤ χL / 2 * (x - 1 / χL) ^ 2 := by positivity
    linarith

/-- O&R (46), p. 645: the conservatives' loss `π²` has the unique minimiser `0`. -/
theorem conservative_isMin_iff (π : ℝ) : (∀ x : ℝ, π ^ 2 ≤ x ^ 2) ↔ π = 0 := by
  constructor
  · intro h
    have := h 0
    exact pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm (by simpa using this) (sq_nonneg _))
  · rintro rfl x
    simp [sq_nonneg]

/-- O&R (47)–(48), p. 645: the election equilibrium with liberal win probability `P`: each
party plays its best response and expectations are rational, `πᵉ = Pπᴸ + (1 − P)πᶜ`. -/
def IsPartisanEqm (P χL k πL πC πe : ℝ) : Prop :=
  (∀ x, liberalLoss χL k πL πe ≤ liberalLoss χL k x πe) ∧ (∀ x : ℝ, πC ^ 2 ≤ x ^ 2) ∧
    πe = P * πL + (1 - P) * πC

/-- O&R (47)–(48): the election equilibrium is unique: `πᴸ = 1/χᴸ`, `πᶜ = 0`, `πᵉ = P/χᴸ`. -/
theorem partisan_eqm_iff (P χL k πL πC πe : ℝ) (hχ : 0 < χL) :
    IsPartisanEqm P χL k πL πC πe ↔ πL = 1 / χL ∧ πC = 0 ∧ πe = P / χL := by
  unfold IsPartisanEqm
  rw [liberal_isMin_iff χL k πL πe hχ, conservative_isMin_iff]
  constructor
  · rintro ⟨rfl, rfl, rfl⟩
    exact ⟨rfl, rfl, by ring⟩
  · rintro ⟨rfl, rfl, rfl⟩
    exact ⟨rfl, rfl, by ring⟩

/-- O&R (48), p. 645: with win probability `1/2`, `πᵉ = 1/(2χᴸ)`. -/
theorem partisan_half (χL : ℝ) : (1 / 2 : ℝ) / χL = 1 / (2 * χL) := by
  rw [div_div]

/-- O&R p. 645: the output surprise `π − πᵉ` is `(1 − P)/χᴸ > 0` if liberals win and
`−P/χᴸ < 0` if conservatives win; it is zero on average. -/
theorem partisan_surprises (P χL : ℝ) :
    1 / χL - P / χL = (1 - P) / χL ∧ 0 - P / χL = -(P / χL) ∧
      P * (1 / χL - P / χL) + (1 - P) * (0 - P / χL) = 0 := by
  refine ⟨by ring, by ring, by ring⟩

/-- O&R p. 645: when the winner is known in advance (`P = 1` or `P = 0`) there is no
surprise, so output is at its natural rate under either party. -/
theorem partisan_known_winner (χL : ℝ) :
    1 / χL - (1 : ℝ) / χL = 0 ∧ (0 : ℝ) - 0 / χL = 0 := by
  constructor <;> ring

/-- O&R p. 645: with an uncertain election (`0 < P < 1`) both surprises are nonzero, with
signs: a liberal win raises output, a conservative win lowers it. -/
theorem partisan_surprise_signs (P χL : ℝ) (hχ : 0 < χL) (hP0 : 0 < P) (hP1 : P < 1) :
    0 < (1 - P) / χL ∧ -(P / χL) < 0 :=
  ⟨div_pos (by linarith) hχ, neg_neg_of_pos (div_pos hP0 hχ)⟩

/-! ## Exercise 5: central bank secrecy -/

/-- O&R Exercise 5, p. 658: the loss `−λ(π − πᵉ − k) + π²/2`. -/
noncomputable def secrecyLoss (k lam π πe : ℝ) : ℝ := -lam * (π - πe - k) + π ^ 2 / 2

/-- O&R Ex. 5: completing the square, `L(π) = L(λ) + (π − λ)²/2`. -/
theorem secrecyLoss_eq (k lam π πe : ℝ) :
    secrecyLoss k lam π πe = secrecyLoss k lam lam πe + (π - lam) ^ 2 / 2 := by
  unfold secrecyLoss
  ring

/-- O&R Ex. 5: `λ` is the unique best response, whatever `πᵉ`. -/
theorem secrecy_isMin_iff (k lam π πe : ℝ) :
    (∀ x, secrecyLoss k lam π πe ≤ secrecyLoss k lam x πe) ↔ π = lam := by
  constructor
  · intro h
    have h2 := h lam
    rw [secrecyLoss_eq k lam π πe] at h2
    have h4 : (π - lam) ^ 2 = 0 := le_antisymm (by linarith) (sq_nonneg _)
    exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h4)
  · rintro rfl x
    rw [secrecyLoss_eq k π x πe]
    have := sq_nonneg (x - π)
    linarith

/-- O&R Ex. 5(a): the one-shot equilibrium with random `λ` observed by the bank only. -/
def IsSecrecyEqm (p lam : S → ℝ) (k : ℝ) (π : S → ℝ) (πe : ℝ) : Prop :=
  (∀ s x, secrecyLoss k (lam s) (π s) πe ≤ secrecyLoss k (lam s) x πe) ∧ πe = expect p π

/-- O&R Ex. 5(a): the equilibrium is unique: `π = λ` and `πᵉ = E λ`. -/
theorem secrecy_eqm_iff (p lam : S → ℝ) (k : ℝ) (π : S → ℝ) (πe : ℝ) :
    IsSecrecyEqm p lam k π πe ↔ (∀ s, π s = lam s) ∧ πe = expect p lam := by
  unfold IsSecrecyEqm
  simp only [secrecy_isMin_iff]
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨h, by rw [show π = lam from funext h]⟩
  · rintro ⟨h, rfl⟩
    exact ⟨h, by rw [show π = lam from funext h]⟩

/-- O&R Ex. 5(a): equilibrium expected loss `k m + m²/2 − Var λ/2` where `m = E λ`,
`Var λ = E λ² − m²`. -/
theorem secrecy_eqm_loss (p lam : S → ℝ) (k : ℝ) :
    expect p (fun s => secrecyLoss k (lam s) (lam s) (expect p lam)) =
      k * expect p lam + expect p lam ^ 2 / 2 -
        (expect p (fun s => lam s ^ 2) - expect p lam ^ 2) / 2 := by
  have : expect p (fun s => secrecyLoss k (lam s) (lam s) (expect p lam)) =
      expect p (fun s => (-(1 / 2 : ℝ)) * lam s ^ 2 + (expect p lam + k) * lam s) := by
    unfold expect secrecyLoss
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [this, expect_add, expect_const_mul, expect_const_mul]
  ring

/-- O&R Ex. 5(b): with `πᵉ = 0` imposed (`E π = 0`), the expected loss of a committed rule is
`k m − Var λ/2 + E(π − (λ − m))²/2`. -/
theorem secrecy_commit_loss (p lam : S → ℝ) (k : ℝ) (h1 : ∑ s, p s = 1) (π : S → ℝ)
    (hπ : expect p π = 0) :
    expect p (fun s => secrecyLoss k (lam s) (π s) 0) =
      k * expect p lam - (expect p (fun s => lam s ^ 2) - expect p lam ^ 2) / 2 +
        expect p (fun s => (π s - (lam s - expect p lam)) ^ 2) / 2 := by
  set m := expect p lam with hm
  have e1 : expect p (fun s => secrecyLoss k (lam s) (π s) 0) =
      expect p (fun s => k * lam s + (-1 : ℝ) * (lam s * π s) + (1 / 2 : ℝ) * π s ^ 2) := by
    unfold expect secrecyLoss
    exact Finset.sum_congr rfl fun s _ => by ring
  have e2 : expect p (fun s => (π s - (lam s - m)) ^ 2) =
      expect p (fun s => π s ^ 2 + (-2 : ℝ) * (lam s * π s) + (2 * m) * π s +
        (lam s ^ 2 + (-2 * m) * lam s + m ^ 2)) := by
    unfold expect
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [e1, e2]
  simp only [expect_add, expect_const_mul, expect_const p h1]
  rw [hπ, ← hm]
  ring

/-- O&R Ex. 5(b): the optimal committed rule with `πᵉ = 0` is `π = λ − E λ`, with loss
`k m − Var λ/2`; it is unique on the support. -/
theorem secrecy_commit_optimal (p lam : S → ℝ) (k : ℝ) (hp : ∀ s, 0 ≤ p s)
    (h1 : ∑ s, p s = 1) (π : S → ℝ) (hπ : expect p π = 0) :
    k * expect p lam - (expect p (fun s => lam s ^ 2) - expect p lam ^ 2) / 2 ≤
        expect p (fun s => secrecyLoss k (lam s) (π s) 0) ∧
      (expect p (fun s => secrecyLoss k (lam s) (π s) 0) =
          k * expect p lam - (expect p (fun s => lam s ^ 2) - expect p lam ^ 2) / 2 ↔
        ∀ s, 0 < p s → π s = lam s - expect p lam) := by
  rw [secrecy_commit_loss p lam k h1 π hπ]
  have hn := expect_nonneg p (fun s => (π s - (lam s - expect p lam)) ^ 2) hp
    fun s => sq_nonneg _
  refine ⟨by linarith, ?_⟩
  constructor
  · intro h
    have h0 : expect p (fun s => (π s - (lam s - expect p lam)) ^ 2) = 0 := by linarith
    intro s hs
    have := (expect_eq_zero_iff p _ hp fun s => sq_nonneg _).1 h0 s hs
    exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 this)
  · intro h
    have h0 : expect p (fun s => (π s - (lam s - expect p lam)) ^ 2) = 0 :=
      (expect_eq_zero_iff p _ hp fun s => sq_nonneg _).2 fun s hs => by rw [h s hs]; ring
    rw [h0]
    ring

/-- O&R Ex. 5(b): the rule `λ − E λ` does satisfy the constraint `E π = 0`. -/
theorem secrecy_commit_rule_mean (p lam : S → ℝ) (h1 : ∑ s, p s = 1) :
    expect p (fun s => lam s - expect p lam) = 0 := by
  rw [expect_sub, expect_const p h1, sub_self]

/-- O&R Ex. 5(b): the constraint `πᵉ = 0` does not bind: for **any** rule with rational
`πᵉ = E π`, the expected loss is at least `k m − Var λ/2`. -/
theorem secrecy_unconstrained_bound (p lam : S → ℝ) (k : ℝ) (hp : ∀ s, 0 ≤ p s)
    (h1 : ∑ s, p s = 1) (π : S → ℝ) :
    k * expect p lam - (expect p (fun s => lam s ^ 2) - expect p lam ^ 2) / 2 ≤
      expect p (fun s => secrecyLoss k (lam s) (π s) (expect p π)) := by
  set m := expect p lam with hm
  set a := expect p π with ha
  have e1 : expect p (fun s => secrecyLoss k (lam s) (π s) a) =
      expect p (fun s => (a + k) * lam s + (-1 : ℝ) * (lam s * π s) +
        (1 / 2 : ℝ) * π s ^ 2) := by
    unfold expect secrecyLoss
    exact Finset.sum_congr rfl fun s _ => by ring
  have e2 : expect p (fun s => ((π s - a) - (lam s - m)) ^ 2) =
      expect p (fun s => π s ^ 2 + (-2 : ℝ) * (lam s * π s) + (2 * m - 2 * a) * π s +
        (lam s ^ 2 + (2 * a - 2 * m) * lam s + (a - m) ^ 2)) := by
    unfold expect
    exact Finset.sum_congr rfl fun s _ => by ring
  have hn := expect_nonneg p (fun s => ((π s - a) - (lam s - m)) ^ 2) hp fun s => sq_nonneg _
  rw [e2] at hn
  rw [e1]
  simp only [expect_add, expect_const_mul, expect_const p h1] at hn ⊢
  rw [← hm] at hn ⊢
  nlinarith [sq_nonneg a]

/-- O&R Ex. 5(c): if `λ` is revealed before `πᵉ` is set, the equilibrium in each state has
`πᵉ = π = λ`. -/
def IsRevealEqm (lam : S → ℝ) (k : ℝ) (π πe : S → ℝ) : Prop :=
  ∀ s, (∀ x, secrecyLoss k (lam s) (π s) (πe s) ≤ secrecyLoss k (lam s) x (πe s)) ∧
    πe s = π s

omit [Fintype S] in
/-- O&R Ex. 5(c): the revealing equilibrium is unique: `π = πᵉ = λ`. -/
theorem reveal_eqm_iff (lam : S → ℝ) (k : ℝ) (π πe : S → ℝ) :
    IsRevealEqm lam k π πe ↔ ∀ s, π s = lam s ∧ πe s = lam s := by
  unfold IsRevealEqm
  simp only [secrecy_isMin_iff]
  constructor
  · intro h s
    exact ⟨(h s).1, (h s).2.trans (h s).1⟩
  · intro h s
    exact ⟨(h s).1, (h s).2.trans (h s).1.symm⟩

/-- O&R Ex. 5(c): the ex ante (`t − 2`) loss is `k m + E λ²/2` under revelation, and
secrecy is better by exactly `Var λ = E λ² − m² ≥ 0`. -/
theorem reveal_vs_secrecy (p lam : S → ℝ) (k : ℝ) (hp : ∀ s, 0 ≤ p s) (h1 : ∑ s, p s = 1) :
    expect p (fun s => secrecyLoss k (lam s) (lam s) (lam s)) =
        k * expect p lam + expect p (fun s => lam s ^ 2) / 2 ∧
      expect p (fun s => secrecyLoss k (lam s) (lam s) (lam s)) -
          expect p (fun s => secrecyLoss k (lam s) (lam s) (expect p lam)) =
        expect p (fun s => lam s ^ 2) - expect p lam ^ 2 ∧
      0 ≤ expect p (fun s => lam s ^ 2) - expect p lam ^ 2 := by
  have e1 : expect p (fun s => secrecyLoss k (lam s) (lam s) (lam s)) =
      expect p (fun s => k * lam s + (1 / 2 : ℝ) * lam s ^ 2) := by
    unfold expect secrecyLoss
    exact Finset.sum_congr rfl fun s _ => by ring
  have hv : expect p (fun s => lam s ^ 2) - expect p lam ^ 2 =
      expect p (fun s => (lam s - expect p lam) ^ 2) := by
    have : expect p (fun s => (lam s - expect p lam) ^ 2) = expect p (fun s =>
        lam s ^ 2 + (-2 * expect p lam) * lam s + expect p lam ^ 2) := by
      unfold expect
      exact Finset.sum_congr rfl fun s _ => by ring
    rw [this, expect_add, expect_add, expect_const_mul, expect_const p h1]
    ring
  have e2 := secrecy_eqm_loss p lam k
  rw [e1, expect_add, expect_const_mul, expect_const_mul] at *
  refine ⟨by ring, by rw [e2]; ring, ?_⟩
  rw [hv]
  exact expect_nonneg p _ hp fun s => sq_nonneg _

/-- O&R Ex. 5, the book's case: `λ ∈ {0, 2}` with probability `1/2` each (indexed by `Bool`). -/
def lamTwo : Bool → ℝ := fun b => if b then 2 else 0

/-- O&R Ex. 5: the uniform distribution on the two states. -/
noncomputable def pHalf : Bool → ℝ := fun _ => 1 / 2

/-- O&R Ex. 5: `pHalf` sums to one. -/
theorem pHalf_sum : ∑ b, pHalf b = 1 := by
  simp [pHalf]

/-- O&R Ex. 5(a)–(c), the book's numbers: `E λ = 1`, `E λ² = 2`, so the one-shot loss is `k`,
the best committed rule (`π = λ − 1`) gives `k − 1/2`, revelation gives `k + 1`. -/
theorem secrecy_two_point (k : ℝ) :
    expect pHalf lamTwo = 1 ∧ expect pHalf (fun b => lamTwo b ^ 2) = 2 ∧
      expect pHalf (fun b => secrecyLoss k (lamTwo b) (lamTwo b) (expect pHalf lamTwo)) = k ∧
      expect pHalf (fun b => secrecyLoss k (lamTwo b) (lamTwo b - 1) 0) = k - 1 / 2 ∧
      expect pHalf (fun b => secrecyLoss k (lamTwo b) (lamTwo b) (lamTwo b)) = k + 1 := by
  have hm : expect pHalf lamTwo = 1 := by
    simp [expect, pHalf, lamTwo]
  refine ⟨hm, ?_, ?_, ?_, ?_⟩
  · simp [expect, pHalf, lamTwo]
    norm_num
  · rw [hm]
    simp [expect, pHalf, lamTwo, secrecyLoss]
    ring
  · simp [expect, pHalf, lamTwo, secrecyLoss]
    ring
  · simp [expect, pHalf, lamTwo, secrecyLoss]
    ring

end ObstfeldRogoff.NominalRigidities.BarroGordon
