/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Solving systems of linear difference equations

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*,
Supplement C to Chapter 2, pp. 726–741.

Time is discrete and indexed by `ℕ` (except for the backward solution SC(4), whose sum
runs to the infinite past and is therefore stated on `ℤ`). The book's scalar equation
SC(1), `z_t = a z_{t-1} + m_t`, is written `z (t+1) = a * z t + m (t+1)`.

* C.1 (scalar): particular solution SC(6), capital example SC(7), backward solution SC(4),
  forward solution SC(9), general solution SC(10), uniqueness of the bubble-free solution
  (under transversality, a growth bound, or boundedness) and the asset-price example.
* C.2 (2 × 2): characteristic roots SC(14), eigenvectors SC(15)–(16), decoupling SC(17),
  steady state SC(18), saddle-path existence and uniqueness SC(19)–(21), and the
  polynomial-factorisation form SC(22).
* C.3: the companion-matrix reduction of a second-order scalar equation.

The stochastic versions SC(11)–(12) and C.2.5 are not formalised (no probability here).
-/

namespace ObstfeldRogoff.SmallOpenEconomyDynamics.LinearDifferenceEquations

open Filter Topology

/-! ## C.1 First-order scalar equations -/

/-- O&R SC(1), p. 726: `z` solves the first-order linear difference equation
`z_t = a z_{t-1} + m_t`, written forward one period on `ℕ`. -/
def ScalarSolves (a : ℝ) (m z : ℕ → ℝ) : Prop :=
  ∀ t : ℕ, z (t + 1) = a * z t + m (t + 1)

/-- A real sequence is bounded (the book's "non-explosive"), O&R p. 730. -/
def SeqBounded (z : ℕ → ℝ) : Prop :=
  ∃ M : ℝ, ∀ t : ℕ, |z t| ≤ M

/-- O&R SC(5), p. 727 (general solution, on `ℕ`): any two solutions of SC(1) with the same
forcing differ by a homogeneous term `b₀ aᵗ`, with `b₀` the difference of initial values. -/
theorem scalar_general_solution {a : ℝ} {m z w : ℕ → ℝ} (hz : ScalarSolves a m z)
    (hw : ScalarSolves a m w) (t : ℕ) : z t = w t + (z 0 - w 0) * a ^ t := by
  induction t with
  | zero => simp
  | succ n ih => rw [hz n, hw n, ih, pow_succ]; ring

/-- O&R p. 727 fn 11: the homogeneous equation `z_t = a z_{t-1}` has solutions `z₀ aᵗ`. -/
theorem scalar_homogeneous_solution {a : ℝ} {z : ℕ → ℝ} (hz : ScalarSolves a (fun _ => 0) z)
    (t : ℕ) : z t = z 0 * a ^ t := by
  have h0 : ScalarSolves a (fun _ => 0) (fun _ => 0) := fun _ => by ring
  simpa using scalar_general_solution hz h0 t

/-- O&R SC(5), p. 727: adding a homogeneous term `b₀ aᵗ` to a solution gives a solution. -/
theorem scalar_add_homogeneous {a : ℝ} {m z : ℕ → ℝ} (hz : ScalarSolves a m z) (b₀ : ℝ) :
    ScalarSolves a m (fun t => z t + b₀ * a ^ t) := by
  intro t; simp only; rw [hz t, pow_succ]; ring

/-- O&R SC(6), p. 728 (particular solution): a solution of SC(1) with initial value `z₀`
satisfies `z_t = ∑_{s=1}^t a^{t-s} m_s + aᵗ z₀`. Valid for every `a` (the book's remark that
SC(6) holds also for `|a| ≥ 1`). -/
theorem scalar_particular_solution {a : ℝ} {m z : ℕ → ℝ} (hz : ScalarSolves a m z) (t : ℕ) :
    z t = ∑ s ∈ Finset.Icc 1 t, a ^ (t - s) * m s + a ^ t * z 0 := by
  induction t with
  | zero => simp
  | succ n ih =>
    rw [hz n, ih, Finset.sum_Icc_succ_top (by omega), Nat.sub_self, pow_zero, one_mul,
      mul_add, Finset.mul_sum, pow_succ]
    have hs : ∀ s ∈ Finset.Icc 1 n, a * (a ^ (n - s) * m s) = a ^ (n + 1 - s) * m s := by
      intro s hs
      rw [Finset.mem_Icc] at hs
      rw [show n + 1 - s = n - s + 1 by omega, pow_succ]; ring
    rw [Finset.sum_congr rfl hs]; ring

/-- O&R SC(6), p. 728 (converse): the formula `∑_{s=1}^t a^{t-s} m_s + aᵗ c` solves SC(1). -/
theorem scalar_particular_solves (a c : ℝ) (m : ℕ → ℝ) :
    ScalarSolves a m (fun t => ∑ s ∈ Finset.Icc 1 t, a ^ (t - s) * m s + a ^ t * c) := by
  intro n
  simp only
  rw [Finset.sum_Icc_succ_top (by omega), Nat.sub_self, pow_zero, one_mul, mul_add,
    Finset.mul_sum, pow_succ]
  have hs : ∀ s ∈ Finset.Icc 1 n, a * (a ^ (n - s) * m s) = a ^ (n + 1 - s) * m s := by
    intro s hs
    rw [Finset.mem_Icc] at hs
    rw [show n + 1 - s = n - s + 1 by omega, pow_succ]; ring
  rw [Finset.sum_congr rfl hs]; ring

/-- O&R SC(7), p. 728 (capital accumulation example): if `K_t = (1-δ) K_{t-1} + I_t` then
`K_t = ∑_{s=1}^t (1-δ)^{t-s} I_s + (1-δ)ᵗ K₀`. -/
theorem capital_accumulation_solution (δ : ℝ) {I K : ℕ → ℝ}
    (hK : ∀ t : ℕ, K (t + 1) = (1 - δ) * K t + I (t + 1)) (t : ℕ) :
    K t = ∑ s ∈ Finset.Icc 1 t, (1 - δ) ^ (t - s) * I s + (1 - δ) ^ t * K 0 :=
  scalar_particular_solution hK t

/-- O&R C.1.1, p. 726: with a stable root `|a| < 1` and bounded forcing `|m_t| ≤ M`, every
solution of SC(1) stays bounded, by `max |z₀| (M / (1 - |a|))`. -/
theorem scalar_stable_bounded {a M : ℝ} {m z : ℕ → ℝ} (hz : ScalarSolves a m z)
    (ha : |a| < 1) (hm : ∀ t, |m t| ≤ M) (t : ℕ) : |z t| ≤ max |z 0| (M / (1 - |a|)) := by
  have hpos : 0 < 1 - |a| := by linarith
  induction t with
  | zero => exact le_max_left _ _
  | succ n ih =>
    set B := max |z 0| (M / (1 - |a|))
    have hB : M ≤ (1 - |a|) * B := by
      have := le_max_right |z 0| (M / (1 - |a|))
      rw [div_le_iff₀ hpos] at this; linarith
    rw [hz n]
    calc |a * z n + m (n + 1)| ≤ |a| * |z n| + |m (n + 1)| := by
          rw [← abs_mul]; exact abs_add_le _ _
      _ ≤ |a| * B + M := by
          gcongr
          exact hm _
      _ ≤ B := by linarith

/-- O&R SC(4), p. 727 (backward solution, on `ℤ`): `z_t = ∑_{s ≤ t} a^{t-s} m_s`, written
as `∑_{k ≥ 0} aᵏ m_{t-k}`. -/
noncomputable def backwardSolution (a : ℝ) (m : ℤ → ℝ) (t : ℤ) : ℝ :=
  ∑' k : ℕ, a ^ k * m (t - k)

/-- O&R SC(4), p. 727: for `|a| < 1` and bounded forcing, the backward solution solves
`z_t = a z_{t-1} + m_t` at every date `t ∈ ℤ`. -/
theorem scalar_backward_solution {a M : ℝ} {m : ℤ → ℝ} (ha : |a| < 1)
    (hm : ∀ t, |m t| ≤ M) (t : ℤ) :
    backwardSolution a m t = a * backwardSolution a m (t - 1) + m t := by
  have hsum : ∀ u : ℤ, Summable (fun k : ℕ => a ^ k * m (u - k)) := by
    intro u
    refine Summable.of_norm_bounded
      ((summable_geometric_of_lt_one (abs_nonneg a) ha).mul_left M) (fun k => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_pow, mul_comm (M)]
    exact mul_le_mul_of_nonneg_left (hm _) (pow_nonneg (abs_nonneg a) k)
  unfold backwardSolution
  rw [(hsum t).tsum_eq_zero_add, ← tsum_mul_left]
  simp only [pow_zero, one_mul, Nat.cast_zero, sub_zero]
  have : ∀ k : ℕ, a ^ (k + 1) * m (t - ((k + 1 : ℕ) : ℤ)) = a * (a ^ k * m (t - 1 - k)) := by
    intro k; rw [pow_succ]; push_cast; rw [show t - (k + 1) = t - 1 - k by ring]; ring
  simp only [this]; ring

/-- O&R SC(4)–(5), p. 727: for `|a| < 1` the backward solution is the only bounded solution
on `ℤ` (the homogeneous term `b₀ aᵗ` explodes as `t → -∞` unless `b₀ = 0`). -/
theorem scalar_backward_unique {a B : ℝ} {m z : ℤ → ℝ} (ha : |a| < 1)
    (hm : ∀ t, |m t| ≤ B) (hz : ∀ t, z t = a * z (t - 1) + m t)
    (hzb : ∀ t, |z t| ≤ B) (t : ℤ) : z t = backwardSolution a m t := by
  set w := backwardSolution a m
  have hw : ∀ t, w t = a * w (t - 1) + m t := scalar_backward_solution ha hm
  have hwb : ∀ t, |w t| ≤ B / (1 - |a|) := by
    intro u
    rw [← Real.norm_eq_abs, div_eq_mul_inv]
    refine tsum_of_norm_bounded (f := fun k : ℕ => a ^ k * m (u - k))
      ((hasSum_geometric_of_lt_one (abs_nonneg a) ha).mul_left B) (fun k => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_pow, mul_comm B]
    exact mul_le_mul_of_nonneg_left (hm _) (pow_nonneg (abs_nonneg a) k)
  have hiter : ∀ n : ℕ, ∀ u : ℤ, z u - w u = a ^ n * (z (u - n) - w (u - n)) := by
    intro n
    induction n with
    | zero => intro u; simp
    | succ k ih =>
      intro u
      rw [ih u, hz (u - k), hw (u - k)]
      push_cast
      rw [show u - k - 1 = u - (k + 1) by ring, pow_succ]; ring
  set C := B + B / (1 - |a|)
  have hbd : ∀ n : ℕ, |z t - w t| ≤ C * |a| ^ n := by
    intro n
    rw [hiter n t, abs_mul, abs_pow, mul_comm C]
    gcongr
    calc |z (t - n) - w (t - n)| ≤ |z (t - n)| + |w (t - n)| := abs_sub _ _
      _ ≤ C := add_le_add (hzb _) (hwb _)
  have hlim : Tendsto (fun n : ℕ => C * |a| ^ n) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg a) ha).const_mul C
  have h0 : |z t - w t| ≤ 0 := ge_of_tendsto' hlim hbd
  have : z t - w t = 0 := abs_nonpos_iff.mp h0
  linarith

/-- O&R p. 730: if `|b₀| |a|ᵗ ≤ K gᵗ` for every `t` with `0 ≤ g < |a|`, then `b₀ = 0`.
This is the mechanism by which a non-explosiveness condition kills the bubble term. -/
theorem bubble_coeff_eq_zero {a b g K : ℝ} (hg : 0 ≤ g) (hga : g < |a|)
    (hb : ∀ t : ℕ, |b| * |a| ^ t ≤ K * g ^ t) : b = 0 := by
  have ha : 0 < |a| := lt_of_le_of_lt hg hga
  have hr0 : 0 ≤ g / |a| := div_nonneg hg ha.le
  have hr1 : g / |a| < 1 := (div_lt_one ha).mpr hga
  have hbd : ∀ t : ℕ, |b| ≤ K * (g / |a|) ^ t := by
    intro t
    have hpos : 0 < |a| ^ t := pow_pos ha t
    rw [div_pow, ← mul_div_assoc, le_div_iff₀ hpos]
    exact hb t
  have hlim : Tendsto (fun t : ℕ => K * (g / |a|) ^ t) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).const_mul K
  have : |b| ≤ 0 := ge_of_tendsto' hlim hbd
  exact abs_nonpos_iff.mp this

/-- O&R SC(9), p. 729 (forward solution): `z_t = -∑_{s ≥ t+1} (1/a)^{s-t} m_s`, written as
`-∑_{k ≥ 0} (1/a)^{k+1} m_{t+1+k}`. -/
noncomputable def forwardSolution (a : ℝ) (m : ℕ → ℝ) (t : ℕ) : ℝ :=
  -∑' k : ℕ, (1 / a) ^ (k + 1) * m (t + 1 + k)

/-- O&R p. 729 fn 13: under the growth hypothesis `|m_t| ≤ M gᵗ` with `0 ≤ g < |a|`, each term
of the forward sum SC(9) is dominated by a geometric term with ratio `g / |a| < 1`. -/
theorem forward_term_bound {a g M : ℝ} {m : ℕ → ℝ} (hg : 0 ≤ g) (hga : g < |a|)
    (hm : ∀ t, |m t| ≤ M * g ^ t) (t k : ℕ) :
    |(1 / a) ^ (k + 1) * m (t + 1 + k)| ≤ M * g ^ (t + 1) / |a| * (g / |a|) ^ k := by
  have ha : 0 < |a| := lt_of_le_of_lt hg hga
  rw [abs_mul, abs_pow, abs_div, abs_one]
  calc (1 / |a|) ^ (k + 1) * |m (t + 1 + k)| ≤ (1 / |a|) ^ (k + 1) * (M * g ^ (t + 1 + k)) :=
        mul_le_mul_of_nonneg_left (hm _) (pow_nonneg (by positivity) _)
    _ = M * g ^ (t + 1) / |a| * (g / |a|) ^ k := by
        rw [div_pow, div_pow, pow_add, pow_succ]; field_simp; ring

/-- O&R p. 729 fn 13: under the growth hypothesis the forward sum SC(9) converges. -/
theorem forward_summable {a g M : ℝ} {m : ℕ → ℝ} (hg : 0 ≤ g) (hga : g < |a|)
    (hm : ∀ t, |m t| ≤ M * g ^ t) (t : ℕ) :
    Summable (fun k : ℕ => (1 / a) ^ (k + 1) * m (t + 1 + k)) := by
  have ha : 0 < |a| := lt_of_le_of_lt hg hga
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one (div_nonneg hg ha.le)
    ((div_lt_one ha).mpr hga)).mul_left (M * g ^ (t + 1) / |a|)) (fun k => ?_)
  rw [Real.norm_eq_abs]
  exact forward_term_bound hg hga hm t k

/-- O&R SC(9), p. 729: under the growth hypothesis `|m_t| ≤ M gᵗ`, `0 ≤ g < |a|`, the forward
solution grows no faster than `gᵗ`: `|z_t| ≤ (M g / (|a| - g)) gᵗ`. -/
theorem forward_growth_bound {a g M : ℝ} {m : ℕ → ℝ} (hg : 0 ≤ g) (hga : g < |a|)
    (hm : ∀ t, |m t| ≤ M * g ^ t) (t : ℕ) :
    |forwardSolution a m t| ≤ M * g / (|a| - g) * g ^ t := by
  have ha : 0 < |a| := lt_of_le_of_lt hg hga
  have hr1 : g / |a| < 1 := (div_lt_one ha).mpr hga
  have hsub : 0 < |a| - g := by linarith
  unfold forwardSolution
  rw [abs_neg, ← Real.norm_eq_abs]
  have h := tsum_of_norm_bounded (f := fun k : ℕ => (1 / a) ^ (k + 1) * m (t + 1 + k))
    ((hasSum_geometric_of_lt_one (div_nonneg hg ha.le) hr1).mul_left (M * g ^ (t + 1) / |a|))
    (fun k => by rw [Real.norm_eq_abs]; exact forward_term_bound hg hga hm t k)
  refine h.trans (le_of_eq ?_)
  have h1 : 1 - g / |a| = (|a| - g) / |a| := by field_simp
  rw [h1, pow_succ]; field_simp

/-- O&R SC(9), p. 729: the forward solution solves SC(1) when `|a| > g ≥ 0` and the forcing
satisfies the growth hypothesis of fn 13. -/
theorem scalar_forward_solution {a g M : ℝ} {m : ℕ → ℝ} (hg : 0 ≤ g) (hga : g < |a|)
    (hm : ∀ t, |m t| ≤ M * g ^ t) : ScalarSolves a m (forwardSolution a m) := by
  have ha : a ≠ 0 := abs_pos.mp (lt_of_le_of_lt hg hga)
  intro t
  have e : ∀ k : ℕ, a * ((1 / a) ^ (k + 1) * m (t + 1 + k)) = (1 / a) ^ k * m (t + 1 + k) := by
    intro k; rw [pow_succ]; field_simp
  have hs : Summable (fun k : ℕ => (1 / a) ^ k * m (t + 1 + k)) := by
    simpa only [e] using (forward_summable hg hga hm t).mul_left a
  have hS : a * ∑' k : ℕ, (1 / a) ^ (k + 1) * m (t + 1 + k)
      = m (t + 1) + ∑' k : ℕ, (1 / a) ^ (k + 1) * m (t + 1 + 1 + k) := by
    rw [← tsum_mul_left]
    simp only [e]
    rw [hs.tsum_eq_zero_add]
    simp only [pow_zero, one_mul, add_zero]
    congr 1
    exact tsum_congr (fun k => by rw [show t + 1 + (k + 1) = t + 1 + 1 + k by ring])
  unfold forwardSolution
  linarith

/-- O&R p. 730: a sequence growing no faster than `hᵗ` with `0 ≤ h < |a|` satisfies the
transversality (no-bubble) condition `z_T / a^T → 0`. -/
theorem transversality_of_growth {a h C : ℝ} {x : ℕ → ℝ} (hh : 0 ≤ h) (hha : h < |a|)
    (hx : ∀ t, |x t| ≤ C * h ^ t) : Tendsto (fun T : ℕ => x T / a ^ T) atTop (𝓝 0) := by
  have ha : 0 < |a| := lt_of_le_of_lt hh hha
  have hlim : Tendsto (fun T : ℕ => C * (h / |a|) ^ T) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (div_nonneg hh ha.le)
      ((div_lt_one ha).mpr hha)).const_mul C
  refine squeeze_zero_norm (fun T => ?_) hlim
  rw [Real.norm_eq_abs, abs_div, abs_pow, div_pow, ← mul_div_assoc]
  exact div_le_div_of_nonneg_right (hx T) (pow_nonneg ha.le T)

/-- O&R SC(10), p. 730 (general solution for `|a| > 1`): every solution of SC(1) equals the
forward solution plus a bubble term `b₀ aᵗ`, with `b₀ = z₀ - (forward solution)₀`. -/
theorem scalar_forward_general_solution {a g M : ℝ} {m z : ℕ → ℝ} (hg : 0 ≤ g) (hga : g < |a|)
    (hm : ∀ t, |m t| ≤ M * g ^ t) (hz : ScalarSolves a m z) (t : ℕ) :
    z t = forwardSolution a m t + (z 0 - forwardSolution a m 0) * a ^ t :=
  scalar_general_solution hz (scalar_forward_solution hg hga hm) t

/-- O&R p. 730 (bubble-free uniqueness): under the growth hypothesis on `m`, a solution of SC(1)
satisfying the transversality condition `z_T / a^T → 0` is the forward solution SC(9),
i.e. `b₀ = 0` in SC(10). -/
theorem scalar_forward_unique_of_transversality {a g M : ℝ} {m z : ℕ → ℝ} (hg : 0 ≤ g)
    (hga : g < |a|) (hm : ∀ t, |m t| ≤ M * g ^ t) (hz : ScalarSolves a m z)
    (htv : Tendsto (fun T : ℕ => z T / a ^ T) atTop (𝓝 0)) (t : ℕ) :
    z t = forwardSolution a m t := by
  have ha : a ≠ 0 := abs_pos.mp (lt_of_le_of_lt hg hga)
  obtain ⟨b, hb_def⟩ : ∃ b, z 0 - forwardSolution a m 0 = b := ⟨_, rfl⟩
  have hf : Tendsto (fun T : ℕ => forwardSolution a m T / a ^ T + b) atTop (𝓝 (0 + b)) :=
    (transversality_of_growth hg hga (forward_growth_bound hg hga hm)).add_const b
  have heq : (fun T : ℕ => z T / a ^ T) = fun T => forwardSolution a m T / a ^ T + b := by
    funext T
    rw [scalar_forward_general_solution hg hga hm hz T, hb_def]
    field_simp
  rw [heq] at htv
  have hb : b = 0 := by simpa using tendsto_nhds_unique hf htv
  rw [scalar_forward_general_solution hg hga hm hz t, hb_def, hb, zero_mul, add_zero]

/-- O&R p. 730: under the growth hypothesis on `m`, the only solution of SC(1) that grows more
slowly than `|a|ᵗ` (here `|z_t| ≤ C hᵗ` with `0 ≤ h < |a|`) is the forward solution SC(9). -/
theorem scalar_forward_unique_of_growth {a g h M C : ℝ} {m z : ℕ → ℝ} (hg : 0 ≤ g)
    (hga : g < |a|) (hm : ∀ t, |m t| ≤ M * g ^ t) (hz : ScalarSolves a m z) (hh : 0 ≤ h)
    (hha : h < |a|) (hzC : ∀ t, |z t| ≤ C * h ^ t) (t : ℕ) : z t = forwardSolution a m t :=
  scalar_forward_unique_of_transversality hg hga hm hz (transversality_of_growth hh hha hzC) t

/-- O&R p. 730: with `|a| > 1` and bounded forcing, the forward solution SC(9) is the unique
bounded solution of SC(1). -/
theorem scalar_forward_unique_of_bounded {a M : ℝ} {m z : ℕ → ℝ} (ha : 1 < |a|)
    (hm : ∀ t, |m t| ≤ M) (hz : ScalarSolves a m z) (hzb : SeqBounded z) (t : ℕ) :
    z t = forwardSolution a m t := by
  obtain ⟨B, hB⟩ := hzb
  exact scalar_forward_unique_of_growth zero_le_one ha (fun s => by simpa using hm s) hz
    zero_le_one ha (fun s => by simpa using hB s) t

/-- O&R SC(9), p. 729: with `|a| > 1` and bounded forcing `|m_t| ≤ M`, the forward solution is
bounded, by `M / (|a| - 1)`. -/
theorem forward_bounded {a M : ℝ} {m : ℕ → ℝ} (ha : 1 < |a|) (hm : ∀ t, |m t| ≤ M) (t : ℕ) :
    |forwardSolution a m t| ≤ M / (|a| - 1) := by
  simpa using forward_growth_bound zero_le_one ha (fun s => by simpa using hm s) t

/-- O&R p. 730: with `|a| > 1` and bounded forcing, any nonzero bubble coefficient `b₀ ≠ 0`
in the general solution SC(10) makes the solution explode (it is unbounded). -/
theorem forward_plus_bubble_unbounded {a M b₀ : ℝ} {m : ℕ → ℝ} (ha : 1 < |a|)
    (hm : ∀ t, |m t| ≤ M) (hb₀ : b₀ ≠ 0) :
    ¬ SeqBounded (fun t => forwardSolution a m t + b₀ * a ^ t) := by
  intro hbd
  have hsol := scalar_add_homogeneous
    (scalar_forward_solution zero_le_one ha (fun s => by simpa using hm s)) b₀
  have h0 := scalar_forward_unique_of_bounded ha hm hsol hbd 0
  simp only [pow_zero, mul_one, add_eq_left] at h0
  exact hb₀ h0

/-- O&R p. 730 (asset-price example): if the ex-dividend value obeys
`V_t = (1+r) V_{t-1} - d_t` with `r > 0`, bounded dividends, and the no-bubble condition
`(1/(1+r))^T V_T → 0`, then `V_t = ∑_{s ≥ t+1} (1/(1+r))^{s-t} d_s`. -/
theorem asset_value_no_bubble {r M : ℝ} {d V : ℕ → ℝ} (hr : 0 < r) (hd : ∀ t, |d t| ≤ M)
    (hV : ∀ t, V (t + 1) = (1 + r) * V t - d (t + 1))
    (hnb : Tendsto (fun T : ℕ => (1 / (1 + r)) ^ T * V T) atTop (𝓝 0)) (t : ℕ) :
    V t = ∑' k : ℕ, (1 / (1 + r)) ^ (k + 1) * d (t + 1 + k) := by
  have ha : 1 < |1 + r| := by rw [abs_of_pos (by linarith)]; linarith
  have hsol : ScalarSolves (1 + r) (fun s => -d s) V := fun s => by rw [hV s]; ring
  have htv : Tendsto (fun T : ℕ => V T / (1 + r) ^ T) atTop (𝓝 0) := by
    refine hnb.congr (fun T => ?_)
    rw [div_pow, one_pow]; field_simp
  have h := scalar_forward_unique_of_transversality zero_le_one ha
    (fun s => by simpa using hd s) hsol htv t
  rw [h]
  unfold forwardSolution
  simp only [mul_neg, tsum_neg, neg_neg]

/-! ## C.2 First-order 2 × 2 systems

The system SC(13) is `z_t = A z_{t-1} + m_t` with `A = [[a₁₁, a₁₂], [a₂₁, a₂₂]]`, written in
components and forward one period. Throughout, `ω₁, ω₂` are real characteristic roots, given
through `ω₁ + ω₂ = tr A` and `ω₁ ω₂ = det A`, and the eigenvector of `ω_i` is `(e_i, 1)`. -/

/-- O&R SC(13), p. 732: `(z₁, z₂)` solves the 2 × 2 system `z_t = A z_{t-1} + m_t`. -/
def SystemSolves (a₁₁ a₁₂ a₂₁ a₂₂ : ℝ) (m₁ m₂ z₁ z₂ : ℕ → ℝ) : Prop :=
  ∀ t : ℕ, z₁ (t + 1) = a₁₁ * z₁ t + a₁₂ * z₂ t + m₁ (t + 1) ∧
    z₂ (t + 1) = a₂₁ * z₁ t + a₂₂ * z₂ t + m₂ (t + 1)

/-- O&R SC(14), p. 733: if `ω₁ + ω₂ = tr A` and `ω₁ ω₂ = det A` then the characteristic
polynomial factors: `det (A - ω I) = (ω - ω₁)(ω - ω₂)`. -/
theorem charpoly_factor {a₁₁ a₁₂ a₂₁ a₂₂ ω₁ ω₂ : ℝ} (hsum : ω₁ + ω₂ = a₁₁ + a₂₂)
    (hprod : ω₁ * ω₂ = a₁₁ * a₂₂ - a₁₂ * a₂₁) (ω : ℝ) :
    Matrix.det !![a₁₁ - ω, a₁₂; a₂₁, a₂₂ - ω] = (ω - ω₁) * (ω - ω₂) := by
  rw [Matrix.det_fin_two_of]
  linear_combination ω * hsum - hprod

/-- O&R SC(14), p. 733: under the same hypotheses `tr A = ω₁ + ω₂` and `det A = ω₁ ω₂`
in matrix form. -/
theorem trace_det_eq_roots {a₁₁ a₁₂ a₂₁ a₂₂ ω₁ ω₂ : ℝ} (hsum : ω₁ + ω₂ = a₁₁ + a₂₂)
    (hprod : ω₁ * ω₂ = a₁₁ * a₂₂ - a₁₂ * a₂₁) :
    Matrix.trace !![a₁₁, a₁₂; a₂₁, a₂₂] = ω₁ + ω₂ ∧
      Matrix.det !![a₁₁, a₁₂; a₂₁, a₂₂] = ω₁ * ω₂ := by
  rw [Matrix.trace_fin_two_of, Matrix.det_fin_two_of]
  exact ⟨hsum.symm, hprod.symm⟩

/-- O&R SC(14), p. 733 (the derivation): two distinct roots of
`ω² - (tr A) ω + det A = 0` have sum `tr A` and product `det A`. -/
theorem vieta_of_distinct_roots {a₁₁ a₁₂ a₂₁ a₂₂ ω₁ ω₂ : ℝ} (hne : ω₁ ≠ ω₂)
    (h₁ : ω₁ ^ 2 - (a₁₁ + a₂₂) * ω₁ + (a₁₁ * a₂₂ - a₁₂ * a₂₁) = 0)
    (h₂ : ω₂ ^ 2 - (a₁₁ + a₂₂) * ω₂ + (a₁₁ * a₂₂ - a₁₂ * a₂₁) = 0) :
    ω₁ + ω₂ = a₁₁ + a₂₂ ∧ ω₁ * ω₂ = a₁₁ * a₂₂ - a₁₂ * a₂₁ := by
  have hsub : (ω₁ - ω₂) * (ω₁ + ω₂ - (a₁₁ + a₂₂)) = 0 := by linear_combination h₁ - h₂
  have hsum : ω₁ + ω₂ = a₁₁ + a₂₂ := by
    rcases mul_eq_zero.mp hsub with h | h
    · exact absurd (sub_eq_zero.mp h) hne
    · linarith
  refine ⟨hsum, ?_⟩
  linear_combination ω₁ * hsum - h₁

/-- O&R p. 733 and fn 15: the characteristic roots are real and distinct when
`(tr A)² > 4 det A`; they are `(tr A ± √((tr A)² - 4 det A)) / 2`. -/
theorem exists_distinct_real_roots {a₁₁ a₁₂ a₂₁ a₂₂ : ℝ}
    (hdisc : 4 * (a₁₁ * a₂₂ - a₁₂ * a₂₁) < (a₁₁ + a₂₂) ^ 2) :
    ∃ ω₁ ω₂ : ℝ, ω₂ < ω₁ ∧ ω₁ + ω₂ = a₁₁ + a₂₂ ∧ ω₁ * ω₂ = a₁₁ * a₂₂ - a₁₂ * a₂₁ := by
  set Δ := (a₁₁ + a₂₂) ^ 2 - 4 * (a₁₁ * a₂₂ - a₁₂ * a₂₁)
  have hΔ : 0 < Δ := by simp only [Δ]; linarith
  have hsq : Real.sqrt Δ ^ 2 = Δ := Real.sq_sqrt hΔ.le
  have hpos : 0 < Real.sqrt Δ := Real.sqrt_pos.mpr hΔ
  refine ⟨((a₁₁ + a₂₂) + Real.sqrt Δ) / 2, ((a₁₁ + a₂₂) - Real.sqrt Δ) / 2, by linarith,
    by ring, ?_⟩
  linear_combination (-1 / 4 : ℝ) * hsq

/-- O&R p. 736: if `1 - tr A + det A < 0` (the characteristic polynomial is negative at 1)
then the roots are real and distinct, `(tr A)² > 4 det A`. -/
theorem discriminant_pos_of_charpoly_one_neg {a₁₁ a₁₂ a₂₁ a₂₂ : ℝ}
    (h : 1 - (a₁₁ + a₂₂) + (a₁₁ * a₂₂ - a₁₂ * a₂₁) < 0) :
    4 * (a₁₁ * a₂₂ - a₁₂ * a₂₁) < (a₁₁ + a₂₂) ^ 2 := by
  nlinarith [sq_nonneg (a₁₁ + a₂₂ - 2)]

/-- O&R SC(18), p. 734 and SC(14): `1 - tr A + det A = (1 - ω₁)(1 - ω₂)`. -/
theorem one_sub_trace_add_det {a₁₁ a₁₂ a₂₁ a₂₂ ω₁ ω₂ : ℝ} (hsum : ω₁ + ω₂ = a₁₁ + a₂₂)
    (hprod : ω₁ * ω₂ = a₁₁ * a₂₂ - a₁₂ * a₂₁) :
    1 - (a₁₁ + a₂₂) + (a₁₁ * a₂₂ - a₁₂ * a₂₁) = (1 - ω₁) * (1 - ω₂) := by
  linear_combination hsum - hprod

/-- O&R p. 736 (the `q`-model argument, generalised): if `det A > 0` and
`1 - tr A + det A < 0`, the larger root exceeds one and the smaller lies in `(0, 1)`:
`0 < ω₂ < 1 < ω₁`. -/
theorem saddle_roots_of_charpoly_one_neg {a₁₁ a₁₂ a₂₁ a₂₂ ω₁ ω₂ : ℝ} (hle : ω₂ ≤ ω₁)
    (hsum : ω₁ + ω₂ = a₁₁ + a₂₂) (hprod : ω₁ * ω₂ = a₁₁ * a₂₂ - a₁₂ * a₂₁)
    (hdet : 0 < a₁₁ * a₂₂ - a₁₂ * a₂₁)
    (h1 : 1 - (a₁₁ + a₂₂) + (a₁₁ * a₂₂ - a₁₂ * a₂₁) < 0) :
    0 < ω₂ ∧ ω₂ < 1 ∧ 1 < ω₁ := by
  rw [one_sub_trace_add_det hsum hprod] at h1
  have h21 : ω₂ < 1 ∧ 1 < ω₁ := by
    rcases lt_or_ge ω₂ 1 with h | h
    · refine ⟨h, ?_⟩
      by_contra hc
      push Not at hc
      nlinarith
    · nlinarith
  refine ⟨?_, h21⟩
  rw [← hprod] at hdet
  by_contra hc
  push Not at hc
  nlinarith

/-- O&R SC(14), p. 733: each `ω_i` with the stated sum and product is a root of the
characteristic equation `ω² - (tr A) ω + det A = 0`. -/
theorem charpoly_root {a₁₁ a₁₂ a₂₁ a₂₂ ω₁ ω₂ : ℝ} (hsum : ω₁ + ω₂ = a₁₁ + a₂₂)
    (hprod : ω₁ * ω₂ = a₁₁ * a₂₂ - a₁₂ * a₂₁) :
    ω₁ ^ 2 - (a₁₁ + a₂₂) * ω₁ + (a₁₁ * a₂₂ - a₁₂ * a₂₁) = 0 ∧
      ω₂ ^ 2 - (a₁₁ + a₂₂) * ω₂ + (a₁₁ * a₂₂ - a₁₂ * a₂₁) = 0 := by
  constructor
  · linear_combination ω₁ * hsum - hprod
  · linear_combination ω₂ * hsum - hprod

/-- O&R SC(15), p. 733: for a root `ω` and `a₂₁ ≠ 0`, `e = (ω - a₂₂)/a₂₁` makes `(e, 1)` an
eigenvector: `a₁₁ e + a₁₂ = ω e` and `a₂₁ e + a₂₂ = ω`. -/
theorem eigvec_eq {a₁₁ a₁₂ a₂₁ a₂₂ ω e : ℝ} (ha₂₁ : a₂₁ ≠ 0)
    (hroot : ω ^ 2 - (a₁₁ + a₂₂) * ω + (a₁₁ * a₂₂ - a₁₂ * a₂₁) = 0)
    (he : e = (ω - a₂₂) / a₂₁) : a₁₁ * e + a₁₂ = ω * e ∧ a₂₁ * e + a₂₂ = ω := by
  subst he
  constructor
  · field_simp; linear_combination -hroot
  · field_simp; ring

/-- O&R SC(15), p. 733 (second form): if moreover `ω ≠ a₁₁` then also `e = a₁₂/(ω - a₁₁)`.
(The book's second expression needs `ω ≠ a₁₁`, which holds when `a₁₂ ≠ 0`; see
`root_ne_a11`.) -/
theorem eigvec_alt_form {a₁₁ a₁₂ a₂₁ a₂₂ ω e : ℝ} (ha₂₁ : a₂₁ ≠ 0)
    (hroot : ω ^ 2 - (a₁₁ + a₂₂) * ω + (a₁₁ * a₂₂ - a₁₂ * a₂₁) = 0)
    (he : e = (ω - a₂₂) / a₂₁) (hω : ω ≠ a₁₁) : e = a₁₂ / (ω - a₁₁) := by
  have h := (eigvec_eq ha₂₁ hroot he).1
  have hω' : ω - a₁₁ ≠ 0 := sub_ne_zero.mpr hω
  field_simp
  linear_combination -h

/-- O&R SC(15), p. 733: if `a₁₂ ≠ 0` and `a₂₁ ≠ 0`, no characteristic root equals `a₁₁`, so
both forms of SC(15) are defined. -/
theorem root_ne_a11 {a₁₁ a₁₂ a₂₁ a₂₂ ω : ℝ} (ha₁₂ : a₁₂ ≠ 0) (ha₂₁ : a₂₁ ≠ 0)
    (hroot : ω ^ 2 - (a₁₁ + a₂₂) * ω + (a₁₁ * a₂₂ - a₁₂ * a₂₁) = 0) : ω ≠ a₁₁ := by
  intro h
  subst h
  have : a₁₂ * a₂₁ = 0 := by linear_combination -hroot
  rcases mul_eq_zero.mp this with h | h
  · exact ha₁₂ h
  · exact ha₂₁ h

/-- O&R p. 733: distinct roots give distinct eigenvector slopes, `e₁ ≠ e₂`. -/
theorem eigvec_distinct {a₂₁ a₂₂ ω₁ ω₂ e₁ e₂ : ℝ} (ha₂₁ : a₂₁ ≠ 0) (hne : ω₁ ≠ ω₂)
    (he₁ : e₁ = (ω₁ - a₂₂) / a₂₁) (he₂ : e₂ = (ω₂ - a₂₂) / a₂₁) : e₁ ≠ e₂ := by
  intro h
  apply hne
  rw [he₁, he₂] at h
  field_simp at h
  linarith

/-- O&R SC(16), p. 733: `E = [[e₁, e₂], [1, 1]]` has inverse `(e₁ - e₂)⁻¹ [[1, -e₂], [-1, e₁]]`
when `e₁ ≠ e₂`. -/
theorem eigvec_matrix_inverse {e₁ e₂ : ℝ} (he : e₁ ≠ e₂) :
    !![e₁, e₂; 1, 1] * ((e₁ - e₂)⁻¹ • !![1, -e₂; -1, e₁]) = 1 ∧
      ((e₁ - e₂)⁻¹ • !![1, -e₂; -1, e₁]) * !![e₁, e₂; 1, 1] = 1 := by
  have h : e₁ - e₂ ≠ 0 := sub_ne_zero.mpr he
  constructor <;>
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring

/-- O&R p. 734: `A E = E Ω` with `Ω = diag(ω₁, ω₂)`, for the eigenvectors of SC(15). -/
theorem eigvec_diagonalizes {a₁₁ a₁₂ a₂₁ a₂₂ ω₁ ω₂ e₁ e₂ : ℝ} (ha₂₁ : a₂₁ ≠ 0)
    (hsum : ω₁ + ω₂ = a₁₁ + a₂₂) (hprod : ω₁ * ω₂ = a₁₁ * a₂₂ - a₁₂ * a₂₁)
    (he₁ : e₁ = (ω₁ - a₂₂) / a₂₁) (he₂ : e₂ = (ω₂ - a₂₂) / a₂₁) :
    !![a₁₁, a₁₂; a₂₁, a₂₂] * !![e₁, e₂; 1, 1] = !![e₁, e₂; 1, 1] * !![ω₁, 0; 0, ω₂] := by
  obtain ⟨r₁, r₂⟩ := charpoly_root hsum hprod
  obtain ⟨p₁, q₁⟩ := eigvec_eq ha₂₁ r₁ he₁
  obtain ⟨p₂, q₂⟩ := eigvec_eq ha₂₁ r₂ he₂
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;>
    linarith

/-- O&R SC(18), p. 734: with constant forcing `(m₁, m₂)` and `1 - tr A + det A ≠ 0`, the
steady state `z̄₁ = ((1-a₂₂) m₁ + a₁₂ m₂)/(1 - tr A + det A)`,
`z̄₂ = (a₂₁ m₁ + (1-a₁₁) m₂)/(1 - tr A + det A)` is a fixed point of the system. -/
theorem steady_state {a₁₁ a₁₂ a₂₁ a₂₂ m₁ m₂ : ℝ}
    (hD : 1 - (a₁₁ + a₂₂) + (a₁₁ * a₂₂ - a₁₂ * a₂₁) ≠ 0) :
    let z₁ := ((1 - a₂₂) * m₁ + a₁₂ * m₂) / (1 - (a₁₁ + a₂₂) + (a₁₁ * a₂₂ - a₁₂ * a₂₁))
    let z₂ := (a₂₁ * m₁ + (1 - a₁₁) * m₂) / (1 - (a₁₁ + a₂₂) + (a₁₁ * a₂₂ - a₁₂ * a₂₁))
    z₁ = a₁₁ * z₁ + a₁₂ * z₂ + m₁ ∧ z₂ = a₂₁ * z₁ + a₂₂ * z₂ + m₂ := by
  intro z₁ z₂
  have e₁ : z₁ * (1 - (a₁₁ + a₂₂) + (a₁₁ * a₂₂ - a₁₂ * a₂₁)) = (1 - a₂₂) * m₁ + a₁₂ * m₂ :=
    div_mul_cancel₀ _ hD
  have e₂ : z₂ * (1 - (a₁₁ + a₂₂) + (a₁₁ * a₂₂ - a₁₂ * a₂₁)) = a₂₁ * m₁ + (1 - a₁₁) * m₂ :=
    div_mul_cancel₀ _ hD
  constructor
  · apply mul_right_cancel₀ hD
    linear_combination (1 - a₁₁) * e₁ - a₁₂ * e₂
  · apply mul_right_cancel₀ hD
    linear_combination (1 - a₂₂) * e₂ - a₂₁ * e₁

/-- O&R SC(18), p. 734: when `1 - tr A + det A ≠ 0` the steady state is unique. -/
theorem steady_state_unique {a₁₁ a₁₂ a₂₁ a₂₂ m₁ m₂ x₁ x₂ : ℝ}
    (hD : 1 - (a₁₁ + a₂₂) + (a₁₁ * a₂₂ - a₁₂ * a₂₁) ≠ 0)
    (h₁ : x₁ = a₁₁ * x₁ + a₁₂ * x₂ + m₁) (h₂ : x₂ = a₂₁ * x₁ + a₂₂ * x₂ + m₂) :
    x₁ = ((1 - a₂₂) * m₁ + a₁₂ * m₂) / (1 - (a₁₁ + a₂₂) + (a₁₁ * a₂₂ - a₁₂ * a₂₁)) ∧
      x₂ = (a₂₁ * m₁ + (1 - a₁₁) * m₂) / (1 - (a₁₁ + a₂₂) + (a₁₁ * a₂₂ - a₁₂ * a₂₁)) := by
  constructor
  · rw [eq_div_iff hD]; linear_combination (1 - a₂₂) * h₁ + a₁₂ * h₂
  · rw [eq_div_iff hD]; linear_combination a₂₁ * h₁ + (1 - a₁₁) * h₂

/-- O&R p. 736: with a saddle configuration `|ω₁| > 1 > |ω₂|`, no root equals one, so
`1 - tr A + det A ≠ 0` and the steady state SC(18) exists. -/
theorem charpoly_one_ne_zero_of_saddle {a₁₁ a₁₂ a₂₁ a₂₂ ω₁ ω₂ : ℝ}
    (hsum : ω₁ + ω₂ = a₁₁ + a₂₂) (hprod : ω₁ * ω₂ = a₁₁ * a₂₂ - a₁₂ * a₂₁)
    (hω₁ : 1 < |ω₁|) (hω₂ : |ω₂| < 1) :
    1 - (a₁₁ + a₂₂) + (a₁₁ * a₂₂ - a₁₂ * a₂₁) ≠ 0 := by
  rw [one_sub_trace_add_det hsum hprod]
  refine mul_ne_zero (fun h => ?_) (fun h => ?_)
  · have : ω₁ = 1 := by linarith
    rw [this, abs_one] at hω₁; exact lt_irrefl _ hω₁
  · have : ω₂ = 1 := by linarith
    rw [this, abs_one] at hω₂; exact lt_irrefl _ hω₂

/-- O&R SC(17), p. 734 (decoupling, before dividing by `e₁ - e₂`): if `(z₁, z₂)` solves the
system then `z₁ - e₂ z₂` solves the scalar equation with root `ω₁` and forcing `m₁ - e₂ m₂`,
and `e₁ z₂ - z₁` solves the one with root `ω₂` and forcing `e₁ m₂ - m₁`. -/
theorem decouple {a₁₁ a₁₂ a₂₁ a₂₂ ω₁ ω₂ e₁ e₂ : ℝ} {m₁ m₂ z₁ z₂ : ℕ → ℝ} (ha₂₁ : a₂₁ ≠ 0)
    (hsum : ω₁ + ω₂ = a₁₁ + a₂₂) (hprod : ω₁ * ω₂ = a₁₁ * a₂₂ - a₁₂ * a₂₁)
    (he₁ : e₁ = (ω₁ - a₂₂) / a₂₁) (he₂ : e₂ = (ω₂ - a₂₂) / a₂₁)
    (hz : SystemSolves a₁₁ a₁₂ a₂₁ a₂₂ m₁ m₂ z₁ z₂) :
    ScalarSolves ω₁ (fun t => m₁ t - e₂ * m₂ t) (fun t => z₁ t - e₂ * z₂ t) ∧
      ScalarSolves ω₂ (fun t => e₁ * m₂ t - m₁ t) (fun t => e₁ * z₂ t - z₁ t) := by
  obtain ⟨r₁, r₂⟩ := charpoly_root hsum hprod
  obtain ⟨p₁, q₁⟩ := eigvec_eq ha₂₁ r₁ he₁
  obtain ⟨p₂, q₂⟩ := eigvec_eq ha₂₁ r₂ he₂
  constructor
  · intro t
    obtain ⟨h₁, h₂⟩ := hz t
    simp only
    rw [h₁, h₂]
    linear_combination (-z₁ t) * q₂ - z₁ t * hsum + z₂ t * p₂ + z₂ t * e₂ * hsum
  · intro t
    obtain ⟨h₁, h₂⟩ := hz t
    simp only
    rw [h₁, h₂]
    linear_combination z₁ t * q₁ + z₁ t * hsum - z₂ t * p₁ - z₂ t * e₁ * hsum

/-- O&R SC(17), p. 734 (dividing by `e₁ - e₂`): scaling a solution of SC(1) and its forcing
by a constant gives a solution. -/
theorem scalar_const_mul {a c : ℝ} {m z : ℕ → ℝ} (hz : ScalarSolves a m z) :
    ScalarSolves a (fun t => c * m t) (fun t => c * z t) := by
  intro t; simp only; rw [hz t]; ring

/-- O&R SC(17), p. 734 (the book's form): the transformed variables `z' = E⁻¹ z`, i.e.
`z'₁ = (z₁ - e₂ z₂)/(e₁ - e₂)` and `z'₂ = (e₁ z₂ - z₁)/(e₁ - e₂)`, obey the decoupled equations
`z'₁ₜ = ω₁ z'₁ₜ₋₁ + (m₁ₜ - e₂ m₂ₜ)/(e₁ - e₂)` and
`z'₂ₜ = ω₂ z'₂ₜ₋₁ + (e₁ m₂ₜ - m₁ₜ)/(e₁ - e₂)`. -/
theorem decoupled_system {a₁₁ a₁₂ a₂₁ a₂₂ ω₁ ω₂ e₁ e₂ : ℝ} {m₁ m₂ z₁ z₂ : ℕ → ℝ}
    (ha₂₁ : a₂₁ ≠ 0) (hsum : ω₁ + ω₂ = a₁₁ + a₂₂) (hprod : ω₁ * ω₂ = a₁₁ * a₂₂ - a₁₂ * a₂₁)
    (he₁ : e₁ = (ω₁ - a₂₂) / a₂₁) (he₂ : e₂ = (ω₂ - a₂₂) / a₂₁)
    (hz : SystemSolves a₁₁ a₁₂ a₂₁ a₂₂ m₁ m₂ z₁ z₂) :
    ScalarSolves ω₁ (fun t => (m₁ t - e₂ * m₂ t) / (e₁ - e₂))
        (fun t => (z₁ t - e₂ * z₂ t) / (e₁ - e₂)) ∧
      ScalarSolves ω₂ (fun t => (e₁ * m₂ t - m₁ t) / (e₁ - e₂))
        (fun t => (e₁ * z₂ t - z₁ t) / (e₁ - e₂)) := by
  obtain ⟨h₁, h₂⟩ := decouple ha₂₁ hsum hprod he₁ he₂ hz
  exact ⟨by simpa only [div_eq_inv_mul] using scalar_const_mul (c := (e₁ - e₂)⁻¹) h₁,
    by simpa only [div_eq_inv_mul] using scalar_const_mul (c := (e₁ - e₂)⁻¹) h₂⟩

/-- O&R p. 734 (`z = E z'`): the original variables are recovered from the decoupled ones as
`z₁ = e₁ z'₁ + e₂ z'₂` and `z₂ = z'₁ + z'₂`, when `e₁ ≠ e₂`. -/
theorem decoupled_reconstruct {e₁ e₂ x₁ x₂ : ℝ} (he : e₁ ≠ e₂) :
    x₁ = e₁ * ((x₁ - e₂ * x₂) / (e₁ - e₂)) + e₂ * ((e₁ * x₂ - x₁) / (e₁ - e₂)) ∧
      x₂ = (x₁ - e₂ * x₂) / (e₁ - e₂) + (e₁ * x₂ - x₁) / (e₁ - e₂) := by
  have h : e₁ - e₂ ≠ 0 := sub_ne_zero.mpr he
  constructor <;> (field_simp; ring)

/-- O&R p. 737 (`z = E z'`, converse of SC(17)): solutions `y₁, y₂` of the two decoupled
scalar equations (unscaled forcings `m₁ - e₂ m₂` and `e₁ m₂ - m₁`) recombine into a solution
`z₁ = (e₁ y₁ + e₂ y₂)/(e₁ - e₂)`, `z₂ = (y₁ + y₂)/(e₁ - e₂)` of the system. -/
theorem recouple {a₁₁ a₁₂ a₂₁ a₂₂ ω₁ ω₂ e₁ e₂ : ℝ} {m₁ m₂ y₁ y₂ : ℕ → ℝ} (ha₂₁ : a₂₁ ≠ 0)
    (hsum : ω₁ + ω₂ = a₁₁ + a₂₂) (hprod : ω₁ * ω₂ = a₁₁ * a₂₂ - a₁₂ * a₂₁) (hne : ω₁ ≠ ω₂)
    (he₁ : e₁ = (ω₁ - a₂₂) / a₂₁) (he₂ : e₂ = (ω₂ - a₂₂) / a₂₁)
    (hy₁ : ScalarSolves ω₁ (fun t => m₁ t - e₂ * m₂ t) y₁)
    (hy₂ : ScalarSolves ω₂ (fun t => e₁ * m₂ t - m₁ t) y₂) :
    SystemSolves a₁₁ a₁₂ a₂₁ a₂₂ m₁ m₂ (fun t => (e₁ * y₁ t + e₂ * y₂ t) / (e₁ - e₂))
      (fun t => (y₁ t + y₂ t) / (e₁ - e₂)) := by
  obtain ⟨r₁, r₂⟩ := charpoly_root hsum hprod
  obtain ⟨p₁, q₁⟩ := eigvec_eq ha₂₁ r₁ he₁
  obtain ⟨p₂, q₂⟩ := eigvec_eq ha₂₁ r₂ he₂
  have hd : e₁ - e₂ ≠ 0 := sub_ne_zero.mpr (eigvec_distinct ha₂₁ hne he₁ he₂)
  intro t
  constructor
  · simp only
    rw [div_eq_iff hd, add_mul, add_mul, mul_assoc a₁₁, div_mul_cancel₀ _ hd, mul_assoc a₁₂,
      div_mul_cancel₀ _ hd, hy₁ t, hy₂ t]
    linear_combination (-y₁ t) * p₁ - y₂ t * p₂
  · simp only
    rw [div_eq_iff hd, add_mul, add_mul, mul_assoc a₂₁, div_mul_cancel₀ _ hd, mul_assoc a₂₂,
      div_mul_cancel₀ _ hd, hy₁ t, hy₂ t]
    linear_combination (-y₁ t) * q₁ - y₂ t * q₂

/-- O&R p. 737 (`z = E z'`): bounded sequences are closed under linear combinations, so
boundedness passes between original and decoupled variables. -/
theorem seqBounded_lin_comb {x y : ℕ → ℝ} (hx : SeqBounded x) (hy : SeqBounded y) (c d : ℝ) :
    SeqBounded (fun t => c * x t + d * y t) := by
  obtain ⟨A, hA⟩ := hx
  obtain ⟨B, hB⟩ := hy
  refine ⟨|c| * A + |d| * B, fun t => ?_⟩
  calc |c * x t + d * y t| ≤ |c * x t| + |d * y t| := abs_add_le _ _
    _ = |c| * |x t| + |d| * |y t| := by rw [abs_mul, abs_mul]
    _ ≤ |c| * A + |d| * B := by gcongr <;> simp [hA, hB]

/-- O&R SC(19)–(21), pp. 735–738 (saddle-path uniqueness): if `|ω₁| > 1`, two bounded
solutions of the system with the same forcing and the same initial value of the predetermined
variable `z₂` coincide. Hence the unstable coefficient `b₁₀` must vanish. (No condition on `ω₂`
is needed for uniqueness; `|ω₂| < 1` is needed only for existence, `saddle_path_exists`.) -/
theorem saddle_path_unique {a₁₁ a₁₂ a₂₁ a₂₂ ω₁ ω₂ e₁ e₂ : ℝ} {m₁ m₂ z₁ z₂ w₁ w₂ : ℕ → ℝ}
    (ha₂₁ : a₂₁ ≠ 0) (hsum : ω₁ + ω₂ = a₁₁ + a₂₂) (hprod : ω₁ * ω₂ = a₁₁ * a₂₂ - a₁₂ * a₂₁)
    (hne : ω₁ ≠ ω₂) (he₁ : e₁ = (ω₁ - a₂₂) / a₂₁) (he₂ : e₂ = (ω₂ - a₂₂) / a₂₁)
    (hω₁ : 1 < |ω₁|) (hz : SystemSolves a₁₁ a₁₂ a₂₁ a₂₂ m₁ m₂ z₁ z₂)
    (hw : SystemSolves a₁₁ a₁₂ a₂₁ a₂₂ m₁ m₂ w₁ w₂) (hz₁ : SeqBounded z₁)
    (hz₂ : SeqBounded z₂) (hw₁ : SeqBounded w₁) (hw₂ : SeqBounded w₂) (h0 : z₂ 0 = w₂ 0)
    (t : ℕ) : z₁ t = w₁ t ∧ z₂ t = w₂ t := by
  obtain ⟨dz₁, dz₂⟩ := decouple ha₂₁ hsum hprod he₁ he₂ hz
  obtain ⟨dw₁, dw₂⟩ := decouple ha₂₁ hsum hprod he₁ he₂ hw
  have hd : e₁ - e₂ ≠ 0 := sub_ne_zero.mpr (eigvec_distinct ha₂₁ hne he₁ he₂)
  set y₁ : ℕ → ℝ := fun t => (z₁ t - e₂ * z₂ t) - (w₁ t - e₂ * w₂ t)
  set y₂ : ℕ → ℝ := fun t => (e₁ * z₂ t - z₁ t) - (e₁ * w₂ t - w₁ t)
  have hy₁ : ScalarSolves ω₁ (fun _ => 0) y₁ := by
    intro s
    have a := dz₁ s
    have b := dw₁ s
    simp only [y₁] at a b ⊢
    linear_combination a - b
  have hy₂ : ScalarSolves ω₂ (fun _ => 0) y₂ := by
    intro s
    have a := dz₂ s
    have b := dw₂ s
    simp only [y₂] at a b ⊢
    linear_combination a - b
  have hy₁b : SeqBounded y₁ := by
    have h := seqBounded_lin_comb (seqBounded_lin_comb (seqBounded_lin_comb hz₁ hz₂ 1 (-e₂))
      (seqBounded_lin_comb hw₁ hw₂ 1 (-e₂)) 1 (-1)) hz₁ 1 0
    convert h using 2 with s
    simp only [y₁]; ring
  obtain ⟨K, hK⟩ := hy₁b
  have hy₁0 : y₁ 0 = 0 := by
    refine bubble_coeff_eq_zero zero_le_one hω₁ (K := K) (fun s => ?_)
    rw [← abs_pow, ← abs_mul, one_pow, mul_one, ← scalar_homogeneous_solution hy₁ s]
    exact hK s
  have hy₁t : ∀ s, y₁ s = 0 := fun s => by
    rw [scalar_homogeneous_solution hy₁ s, hy₁0, zero_mul]
  have hy₂0 : y₂ 0 = 0 := by
    have := hy₁0
    simp only [y₁, y₂] at this ⊢
    rw [h0] at this ⊢
    linarith
  have hy₂t : ∀ s, y₂ s = 0 := fun s => by
    rw [scalar_homogeneous_solution hy₂ s, hy₂0, zero_mul]
  have a := hy₁t t
  have b := hy₂t t
  simp only [y₁, y₂] at a b
  have h2 : (e₁ - e₂) * (z₂ t - w₂ t) = 0 := by linear_combination a + b
  have h2' : z₂ t = w₂ t := by
    have := (mul_eq_zero.mp h2).resolve_left hd
    linarith
  refine ⟨?_, h2'⟩
  rw [h2'] at a
  linarith

/-- O&R SC(20)–(21), pp. 737–738 (saddle-path existence, time-varying forcing): if
`|ω₁| > 1 > |ω₂|` and the forcing is bounded, then for every initial value `z₂₀` of the
predetermined variable there is a bounded solution of the system with `z₂ 0 = z₂₀`. It is built
by solving the unstable decoupled equation forward (SC(9), `b₁₀ = 0`) and the stable one
backward from the initial condition (SC(6)); by `saddle_path_unique` it is the only one. -/
theorem saddle_path_exists {a₁₁ a₁₂ a₂₁ a₂₂ ω₁ ω₂ e₁ e₂ M₁ M₂ : ℝ} {m₁ m₂ : ℕ → ℝ}
    (ha₂₁ : a₂₁ ≠ 0) (hsum : ω₁ + ω₂ = a₁₁ + a₂₂) (hprod : ω₁ * ω₂ = a₁₁ * a₂₂ - a₁₂ * a₂₁)
    (hne : ω₁ ≠ ω₂) (he₁ : e₁ = (ω₁ - a₂₂) / a₂₁) (he₂ : e₂ = (ω₂ - a₂₂) / a₂₁)
    (hω₁ : 1 < |ω₁|) (hω₂ : |ω₂| < 1) (hm₁ : ∀ t, |m₁ t| ≤ M₁) (hm₂ : ∀ t, |m₂ t| ≤ M₂)
    (z₂₀ : ℝ) :
    ∃ z₁ z₂ : ℕ → ℝ, SystemSolves a₁₁ a₁₂ a₂₁ a₂₂ m₁ m₂ z₁ z₂ ∧ SeqBounded z₁ ∧
      SeqBounded z₂ ∧ z₂ 0 = z₂₀ := by
  have hd : e₁ - e₂ ≠ 0 := sub_ne_zero.mpr (eigvec_distinct ha₂₁ hne he₁ he₂)
  have hmb₁ : SeqBounded m₁ := ⟨M₁, hm₁⟩
  have hmb₂ : SeqBounded m₂ := ⟨M₂, hm₂⟩
  obtain ⟨N₁, hN₁⟩ := seqBounded_lin_comb hmb₁ hmb₂ 1 (-e₂)
  obtain ⟨N₂, hN₂⟩ := seqBounded_lin_comb hmb₂ hmb₁ e₁ (-1)
  have hn₁ : ∀ t, |m₁ t - e₂ * m₂ t| ≤ N₁ := fun t => by
    have := hN₁ t; simp only at this
    rwa [show 1 * m₁ t + -e₂ * m₂ t = m₁ t - e₂ * m₂ t by ring] at this
  have hn₂ : ∀ t, |e₁ * m₂ t - m₁ t| ≤ N₂ := fun t => by
    have := hN₂ t; simp only at this
    rwa [show e₁ * m₂ t + -1 * m₁ t = e₁ * m₂ t - m₁ t by ring] at this
  set y₁ := forwardSolution ω₁ (fun t => m₁ t - e₂ * m₂ t)
  have hy₁ : ScalarSolves ω₁ (fun t => m₁ t - e₂ * m₂ t) y₁ :=
    scalar_forward_solution zero_le_one hω₁ (fun s => by simpa using hn₁ s)
  set c := (e₁ - e₂) * z₂₀ - y₁ 0
  set y₂ : ℕ → ℝ := fun t =>
    ∑ s ∈ Finset.Icc 1 t, ω₂ ^ (t - s) * (e₁ * m₂ s - m₁ s) + ω₂ ^ t * c
  have hy₂ : ScalarSolves ω₂ (fun t => e₁ * m₂ t - m₁ t) y₂ := scalar_particular_solves ω₂ c _
  have hy₁b : SeqBounded y₁ := ⟨_, forward_bounded hω₁ hn₁⟩
  have hy₂b : SeqBounded y₂ := ⟨_, scalar_stable_bounded hy₂ hω₂ hn₂⟩
  refine ⟨fun t => (e₁ * y₁ t + e₂ * y₂ t) / (e₁ - e₂), fun t => (y₁ t + y₂ t) / (e₁ - e₂),
    recouple ha₂₁ hsum hprod hne he₁ he₂ hy₁ hy₂, ?_, ?_, ?_⟩
  · have h := seqBounded_lin_comb hy₁b hy₂b (e₁ / (e₁ - e₂)) (e₂ / (e₁ - e₂))
    convert h using 2 with t
    field_simp
  · have h := seqBounded_lin_comb hy₁b hy₂b (1 / (e₁ - e₂)) (1 / (e₁ - e₂))
    convert h using 2 with t
    field_simp
  · simp only [y₂, c]
    simp
    field_simp

/-- O&R SC(19), p. 736 (saddle path with constant forcing): let `|ω₁| > 1 > |ω₂|` and let
`(z̄₁, z̄₂)` be a steady state (SC(18)). Then the path
`z₁ₜ - z̄₁ = e₂ (z₂₀ - z̄₂) ω₂ᵗ`, `z₂ₜ - z̄₂ = (z₂₀ - z̄₂) ω₂ᵗ` solves the system, is bounded,
starts at `z₂₀`, lies on the saddle path `z₁ - z̄₁ = e₂ (z₂ - z̄₂)` and converges to the
steady state. -/
theorem saddle_path_constant_solves {a₁₁ a₁₂ a₂₁ a₂₂ ω₁ ω₂ e₂ m₁ m₂ x₁ x₂ : ℝ}
    (ha₂₁ : a₂₁ ≠ 0) (hsum : ω₁ + ω₂ = a₁₁ + a₂₂) (hprod : ω₁ * ω₂ = a₁₁ * a₂₂ - a₁₂ * a₂₁)
    (he₂ : e₂ = (ω₂ - a₂₂) / a₂₁) (hω₂ : |ω₂| < 1)
    (hss₁ : x₁ = a₁₁ * x₁ + a₁₂ * x₂ + m₁) (hss₂ : x₂ = a₂₁ * x₁ + a₂₂ * x₂ + m₂) (z₂₀ : ℝ) :
    SystemSolves a₁₁ a₁₂ a₂₁ a₂₂ (fun _ => m₁) (fun _ => m₂)
        (fun t => x₁ + e₂ * (z₂₀ - x₂) * ω₂ ^ t) (fun t => x₂ + (z₂₀ - x₂) * ω₂ ^ t) ∧
      SeqBounded (fun t => x₁ + e₂ * (z₂₀ - x₂) * ω₂ ^ t) ∧
      SeqBounded (fun t => x₂ + (z₂₀ - x₂) * ω₂ ^ t) ∧
      (∀ t : ℕ, (x₁ + e₂ * (z₂₀ - x₂) * ω₂ ^ t) - x₁ = e₂ * ((x₂ + (z₂₀ - x₂) * ω₂ ^ t) - x₂)) ∧
      Tendsto (fun t => x₁ + e₂ * (z₂₀ - x₂) * ω₂ ^ t) atTop (𝓝 x₁) ∧
      Tendsto (fun t => x₂ + (z₂₀ - x₂) * ω₂ ^ t) atTop (𝓝 x₂) := by
  obtain ⟨_, r₂⟩ := charpoly_root hsum hprod
  obtain ⟨p₂, q₂⟩ := eigvec_eq ha₂₁ r₂ he₂
  have hpow : ∀ t : ℕ, |ω₂ ^ t| ≤ 1 := fun t => by
    rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) hω₂.le
  have hlim : Tendsto (fun t : ℕ => ω₂ ^ t) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_iff.mpr hω₂
  have hone : SeqBounded (fun _ => (1 : ℝ)) := ⟨1, fun _ => by simp⟩
  have hpb : SeqBounded (fun t => ω₂ ^ t) := ⟨1, hpow⟩
  refine ⟨fun t => ⟨?_, ?_⟩, ?_, ?_, fun t => by ring, ?_, ?_⟩
  · simp only; rw [pow_succ]
    linear_combination hss₁ - (z₂₀ - x₂) * ω₂ ^ t * p₂
  · simp only; rw [pow_succ]
    linear_combination hss₂ - (z₂₀ - x₂) * ω₂ ^ t * q₂
  · convert seqBounded_lin_comb hone hpb x₁ (e₂ * (z₂₀ - x₂)) using 2 with t; ring
  · convert seqBounded_lin_comb hone hpb x₂ (z₂₀ - x₂) using 2 with t; ring
  · simpa using (hlim.const_mul (e₂ * (z₂₀ - x₂))).const_add x₁
  · simpa using (hlim.const_mul (z₂₀ - x₂)).const_add x₂

/-- O&R SC(19), p. 736 (uniqueness of the saddle path, constant forcing): if
`|ω₁| > 1 > |ω₂|` and `(z̄₁, z̄₂)` is a steady state, every bounded solution with
`z₂ 0 = z₂₀` is `z₁ₜ = z̄₁ + e₂ (z₂₀ - z̄₂) ω₂ᵗ`, `z₂ₜ = z̄₂ + (z₂₀ - z̄₂) ω₂ᵗ`. -/
theorem saddle_path_constant_unique {a₁₁ a₁₂ a₂₁ a₂₂ ω₁ ω₂ e₁ e₂ m₁ m₂ x₁ x₂ z₂₀ : ℝ}
    {z₁ z₂ : ℕ → ℝ} (ha₂₁ : a₂₁ ≠ 0) (hsum : ω₁ + ω₂ = a₁₁ + a₂₂)
    (hprod : ω₁ * ω₂ = a₁₁ * a₂₂ - a₁₂ * a₂₁) (hne : ω₁ ≠ ω₂) (he₁ : e₁ = (ω₁ - a₂₂) / a₂₁)
    (he₂ : e₂ = (ω₂ - a₂₂) / a₂₁) (hω₁ : 1 < |ω₁|) (hω₂ : |ω₂| < 1)
    (hss₁ : x₁ = a₁₁ * x₁ + a₁₂ * x₂ + m₁) (hss₂ : x₂ = a₂₁ * x₁ + a₂₂ * x₂ + m₂)
    (hz : SystemSolves a₁₁ a₁₂ a₂₁ a₂₂ (fun _ => m₁) (fun _ => m₂) z₁ z₂)
    (hz₁ : SeqBounded z₁) (hz₂ : SeqBounded z₂) (h0 : z₂ 0 = z₂₀) (t : ℕ) :
    z₁ t = x₁ + e₂ * (z₂₀ - x₂) * ω₂ ^ t ∧ z₂ t = x₂ + (z₂₀ - x₂) * ω₂ ^ t := by
  obtain ⟨hp, hp₁, hp₂, -, -, -⟩ :=
    saddle_path_constant_solves ha₂₁ hsum hprod he₂ hω₂ hss₁ hss₂ z₂₀
  exact saddle_path_unique ha₂₁ hsum hprod hne he₁ he₂ hω₁ hz hp hz₁ hz₂ hp₁ hp₂
    (by simp [h0]) t

/-! ### C.2.4 The polynomial-factorisation method -/

/-- O&R p. 739 (C.2.4): the lag polynomial factors through the characteristic roots,
`1 - (tr A) L + (det A) L² = (1 - ω₁ L)(1 - ω₂ L)`. -/
theorem lag_polynomial_factor {a₁₁ a₁₂ a₂₁ a₂₂ ω₁ ω₂ : ℝ} (hsum : ω₁ + ω₂ = a₁₁ + a₂₂)
    (hprod : ω₁ * ω₂ = a₁₁ * a₂₂ - a₁₂ * a₂₁) (L : ℝ) :
    1 - (a₁₁ + a₂₂) * L + (a₁₁ * a₂₂ - a₁₂ * a₂₁) * L ^ 2 = (1 - ω₁ * L) * (1 - ω₂ * L) := by
  linear_combination L * hsum - L ^ 2 * hprod

/-- O&R SC(22), p. 739 (lead operator `L⁻¹`): a shifted bounded sequence is bounded. -/
theorem seqBounded_shift {x : ℕ → ℝ} (hx : SeqBounded x) (j : ℕ) :
    SeqBounded (fun t => x (t + j)) := by
  obtain ⟨B, hB⟩ := hx
  exact ⟨B, fun t => hB (t + j)⟩

/-- O&R SC(22), p. 739, first row (polynomial-factorisation form): if `|ω₁| > 1`, the forcing
is bounded and `(z₁, z₂)` is a solution with `z₁` bounded, then
`z₁ₜ = ω₂ z₁ₜ₋₁ - (1/ω₁) ∑_{s ≥ t} (1/ω₁)^{s-t} [m₁ₛ₊₁ - a₂₂ m₁ₛ + a₁₂ m₂ₛ]`,
written here at date `t + 1`. -/
theorem polynomial_factorization_row1 {a₁₁ a₁₂ a₂₁ a₂₂ ω₁ ω₂ : ℝ} {m₁ m₂ z₁ z₂ : ℕ → ℝ}
    (hsum : ω₁ + ω₂ = a₁₁ + a₂₂) (hprod : ω₁ * ω₂ = a₁₁ * a₂₂ - a₁₂ * a₂₁) (hω₁ : 1 < |ω₁|)
    (hm₁ : SeqBounded m₁) (hm₂ : SeqBounded m₂)
    (hz : SystemSolves a₁₁ a₁₂ a₂₁ a₂₂ m₁ m₂ z₁ z₂) (hz₁ : SeqBounded z₁) (t : ℕ) :
    z₁ (t + 1) = ω₂ * z₁ t -
      ∑' k : ℕ, (1 / ω₁) ^ (k + 1) * (m₁ (t + 2 + k) - a₂₂ * m₁ (t + 1 + k) +
        a₁₂ * m₂ (t + 1 + k)) := by
  set n : ℕ → ℝ := fun s => m₁ (s + 1) - a₂₂ * m₁ s + a₁₂ * m₂ s
  set u : ℕ → ℝ := fun s => z₁ (s + 1) - ω₂ * z₁ s
  have hu : ScalarSolves ω₁ n u := by
    intro s
    obtain ⟨A, -⟩ := hz (s + 1)
    obtain ⟨C, B⟩ := hz s
    simp only [u, n]
    linear_combination A + a₁₂ * B - a₂₂ * C - z₁ (s + 1) * hsum + z₁ s * hprod
  obtain ⟨N, hN⟩ : SeqBounded n := by
    convert seqBounded_lin_comb (seqBounded_lin_comb (seqBounded_shift hm₁ 1) hm₁ 1 (-a₂₂))
      hm₂ 1 a₁₂ using 2 with s
    simp only [n]; ring
  have hub : SeqBounded u := by
    convert seqBounded_lin_comb (seqBounded_shift hz₁ 1) hz₁ 1 (-ω₂) using 2 with s
    simp only [u]; ring
  have h := scalar_forward_unique_of_bounded hω₁ hN hu hub t
  simp only [u, forwardSolution, n] at h
  have e : ∀ k : ℕ, t + 1 + k + 1 = t + 2 + k := fun k => by ring
  simp only [e] at h
  linarith

/-- O&R SC(22), p. 739, second row: under the same hypotheses with `z₂` bounded,
`z₂ₜ = ω₂ z₂ₜ₋₁ - (1/ω₁) ∑_{s ≥ t} (1/ω₁)^{s-t} [a₂₁ m₁ₛ + m₂ₛ₊₁ - a₁₁ m₂ₛ]`,
written here at date `t + 1`. -/
theorem polynomial_factorization_row2 {a₁₁ a₁₂ a₂₁ a₂₂ ω₁ ω₂ : ℝ} {m₁ m₂ z₁ z₂ : ℕ → ℝ}
    (hsum : ω₁ + ω₂ = a₁₁ + a₂₂) (hprod : ω₁ * ω₂ = a₁₁ * a₂₂ - a₁₂ * a₂₁) (hω₁ : 1 < |ω₁|)
    (hm₁ : SeqBounded m₁) (hm₂ : SeqBounded m₂)
    (hz : SystemSolves a₁₁ a₁₂ a₂₁ a₂₂ m₁ m₂ z₁ z₂) (hz₂ : SeqBounded z₂) (t : ℕ) :
    z₂ (t + 1) = ω₂ * z₂ t -
      ∑' k : ℕ, (1 / ω₁) ^ (k + 1) * (a₂₁ * m₁ (t + 1 + k) + m₂ (t + 2 + k) -
        a₁₁ * m₂ (t + 1 + k)) := by
  set n : ℕ → ℝ := fun s => a₂₁ * m₁ s + m₂ (s + 1) - a₁₁ * m₂ s
  set u : ℕ → ℝ := fun s => z₂ (s + 1) - ω₂ * z₂ s
  have hu : ScalarSolves ω₁ n u := by
    intro s
    obtain ⟨-, A⟩ := hz (s + 1)
    obtain ⟨C, B⟩ := hz s
    simp only [u, n]
    linear_combination A + a₂₁ * C - a₁₁ * B - z₂ (s + 1) * hsum + z₂ s * hprod
  obtain ⟨N, hN⟩ : SeqBounded n := by
    convert seqBounded_lin_comb (seqBounded_lin_comb hm₁ (seqBounded_shift hm₂ 1) a₂₁ 1)
      hm₂ 1 (-a₁₁) using 2 with s
    simp only [n]; ring
  have hub : SeqBounded u := by
    convert seqBounded_lin_comb (seqBounded_shift hz₂ 1) hz₂ 1 (-ω₂) using 2 with s
    simp only [u]; ring
  have h := scalar_forward_unique_of_bounded hω₁ hN hu hub t
  simp only [u, forwardSolution, n] at h
  have e : ∀ k : ℕ, t + 1 + k + 1 = t + 2 + k := fun k => by ring
  simp only [e] at h
  linarith

/-! ## C.3 Higher-order equations -/

/-- O&R C.3, p. 741: a second-order equation `z_t = a₁ z_{t-1} + a₂ z_{t-2} + m_t` becomes
the first-order system with companion matrix `[[a₁, a₂], [1, 0]]` for `(z_t, z'_t) =
(z_t, z_{t-1})` and forcing `(m_t, 0)`; here `z₁ t = z (t+1)`, `z₂ t = z t`. -/
theorem companion_of_second_order {a₁ a₂ : ℝ} {m z : ℕ → ℝ}
    (hz : ∀ t, z (t + 2) = a₁ * z (t + 1) + a₂ * z t + m (t + 2)) :
    SystemSolves a₁ a₂ 1 0 (fun t => m (t + 1)) (fun _ => 0) (fun t => z (t + 1)) z := by
  intro t
  exact ⟨by simpa using hz t, by ring⟩

/-- O&R C.3, p. 741 (converse): the second component of a solution of the companion system
solves the second-order scalar equation. -/
theorem second_order_of_companion {a₁ a₂ : ℝ} {m₁ z₁ z₂ : ℕ → ℝ}
    (hz : SystemSolves a₁ a₂ 1 0 m₁ (fun _ => 0) z₁ z₂) (t : ℕ) :
    z₂ (t + 2) = a₁ * z₂ (t + 1) + a₂ * z₂ t + m₁ (t + 1) := by
  have h1 := (hz t).1
  have h2 := (hz t).2
  have h3 := (hz (t + 1)).2
  simp only [one_mul, zero_mul, add_zero] at h2 h3
  rw [h3, h1, ← h2]

/-- O&R C.3, p. 741: the companion matrix has `tr = a₁` and `det = -a₂`, so with roots
`ω₁ + ω₂ = a₁`, `ω₁ ω₂ = -a₂` the lag polynomial factors as
`1 - a₁ L - a₂ L² = (1 - ω₁ L)(1 - ω₂ L)` (as in C.2.4). -/
theorem companion_lag_polynomial {a₁ a₂ ω₁ ω₂ : ℝ} (hsum : ω₁ + ω₂ = a₁)
    (hprod : ω₁ * ω₂ = -a₂) (L : ℝ) :
    Matrix.trace !![a₁, a₂; 1, 0] = a₁ ∧ Matrix.det !![a₁, a₂; 1, 0] = -a₂ ∧
      1 - a₁ * L - a₂ * L ^ 2 = (1 - ω₁ * L) * (1 - ω₂ * L) := by
  rw [Matrix.trace_fin_two_of, Matrix.det_fin_two_of]
  refine ⟨by ring, by ring, ?_⟩
  linear_combination L * hsum - L ^ 2 * hprod

end ObstfeldRogoff.SmallOpenEconomyDynamics.LinearDifferenceEquations
