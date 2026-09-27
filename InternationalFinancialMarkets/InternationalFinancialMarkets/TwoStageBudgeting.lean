/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import InternationalFinancialMarkets.Model
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Risk aversion, intertemporal substitution and two-stage budgeting

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §5.1.8,
pp. 282–285, including footnote 14.

Lifetime utility is `u(C₁) + βu(Ω(C₂))` (O&R (20)) with the CES certainty equivalent
`Ω(C₂) = [Σ π(s)C₂(s)^{1−ρ}]^{1/(1−ρ)}` (O&R (23)), `0 < ρ ≠ 1`. Date-1 prices of state
claims are `p(s)/(1+r)`, and `Z₂ = Σ p(s)C₂(s)` is date-2 spending in sure date-2 units. We
prove:
* the demands (24) cost exactly `Z₂` and attain `Ω = Z₂/P`, with `P` the price index (25), and
  no bundle costing at most `Z₂` does better (strictly, unless it is the demand bundle): this
  is the second stage of two-stage budgeting, and lifetime utility (20) is bounded by (21);
* `P ≤ 1`, with equality iff `p = π`, for probability vectors `p`, `π > 0` (O&R p. 285);
* the Euler equation (27) and `C₁ = W₁/(1 + ((1+r)/P)^{σ−1}β^σ)` for isoelastic `u`;
* footnote 14: `C₁ = Y₁` iff `1 + r = 1 + r^CA = (1/β)[Σ p(s)Y₂(s)/(P^{1−σ}Y₁)]^{1/σ}`, and
  `CA₁ > 0` iff `r > r^CA`;
* with `P < 1`, `C₁` lies below its certainty benchmark (`P = 1`) if `σ > 1` and above it if
  `σ < 1`; `σ = 1` and `p = π` are the special cases in which the benchmark is exact; with
  `β(1+r) = 1` and `Y₁ = Σ p(s)Y₂(s)`, `CA₁ > 0` when `σ > 1` and `CA₁ < 0` when `σ < 1`.
-/

namespace ObstfeldRogoff.InternationalFinancialMarkets.TwoStageBudgeting

open Finset

variable {S : Type} [Fintype S]

/-! ## Tangent-line inequalities for powers -/

/-- Bernoulli's inequality for a negative exponent (used for the CES optimality in O&R §5.1.8):
for `a < 0` and `t > 0`, `1 + a(t − 1) ≤ t^a`, strictly if `t ≠ 1`. -/
theorem one_add_mul_le_rpow_of_neg {a t : ℝ} (ha : a < 0) (ht : 0 < t) :
    1 + a * (t - 1) ≤ t ^ a ∧ (t ≠ 1 → 1 + a * (t - 1) < t ^ a) := by
  have e : t ^ a = t * (1 + (t⁻¹ - 1)) ^ (1 - a) := by
    rw [add_sub_cancel, Real.inv_rpow ht.le, ← Real.rpow_neg ht.le, neg_sub,
      Real.rpow_sub_one ht.ne']
    field_simp
  have hs : -1 ≤ t⁻¹ - 1 := by have := inv_pos.mpr ht; linarith
  have key : t * (1 + (1 - a) * (t⁻¹ - 1)) = 1 + a * (t - 1) := by field_simp; ring
  rw [e, ← key]
  refine ⟨mul_le_mul_of_nonneg_left
    (one_add_mul_self_le_rpow_one_add hs (by linarith)) ht.le, fun h1 => ?_⟩
  have hs' : t⁻¹ - 1 ≠ 0 := by
    intro h0
    exact h1 (inv_eq_one.mp (sub_eq_zero.mp h0))
  exact mul_lt_mul_of_pos_left (one_add_mul_self_lt_rpow_one_add hs hs' (by linarith)) ht

/-- Tangent-line inequality for `x ↦ x^a`, `0 < a < 1` (concave), O&R §5.1.8:
`x^a ≤ y^a + a y^{a−1}(x − y)` for `x, y > 0`, strictly if `x ≠ y`. -/
theorem rpow_le_tangent {a x y : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hx : 0 < x) (hy : 0 < y) :
    x ^ a ≤ y ^ a + a * y ^ (a - 1) * (x - y) ∧
      (x ≠ y → x ^ a < y ^ a + a * y ^ (a - 1) * (x - y)) := by
  have hya : 0 < y ^ a := Real.rpow_pos_of_pos hy a
  have ex : x ^ a = y ^ a * (1 + (x / y - 1)) ^ a := by
    rw [add_sub_cancel, Real.div_rpow hx.le hy.le]
    field_simp
  have et : y ^ a + a * y ^ (a - 1) * (x - y) = y ^ a * (1 + a * (x / y - 1)) := by
    rw [Real.rpow_sub_one hy.ne']
    field_simp
  have hs : -1 ≤ x / y - 1 := by have := div_pos hx hy; linarith
  rw [ex, et]
  refine ⟨mul_le_mul_of_nonneg_left
    (rpow_one_add_le_one_add_mul_self hs ha0.le ha1.le) hya.le, fun hxy => ?_⟩
  have hs' : x / y - 1 ≠ 0 := by
    intro h0
    exact hxy ((div_eq_one_iff_eq hy.ne').mp (sub_eq_zero.mp h0))
  exact mul_lt_mul_of_pos_left (rpow_one_add_lt_one_add_mul_self hs hs' ha0 ha1) hya

/-- Tangent-line inequality for `x ↦ x^a`, `a < 0` (convex), O&R §5.1.8:
`y^a + a y^{a−1}(x − y) ≤ x^a` for `x, y > 0`, strictly if `x ≠ y`. -/
theorem tangent_le_rpow_of_neg {a x y : ℝ} (ha : a < 0) (hx : 0 < x) (hy : 0 < y) :
    y ^ a + a * y ^ (a - 1) * (x - y) ≤ x ^ a ∧
      (x ≠ y → y ^ a + a * y ^ (a - 1) * (x - y) < x ^ a) := by
  have hya : 0 < y ^ a := Real.rpow_pos_of_pos hy a
  have ex : x ^ a = y ^ a * (x / y) ^ a := by
    rw [Real.div_rpow hx.le hy.le]
    field_simp
  have et : y ^ a + a * y ^ (a - 1) * (x - y) = y ^ a * (1 + a * (x / y - 1)) := by
    rw [Real.rpow_sub_one hy.ne']
    field_simp
  have h := one_add_mul_le_rpow_of_neg ha (div_pos hx hy)
  rw [ex, et]
  refine ⟨mul_le_mul_of_nonneg_left h.1 hya.le, fun hxy => ?_⟩
  exact mul_lt_mul_of_pos_left (h.2 fun h1 => hxy ((div_eq_one_iff_eq hy.ne').mp h1)) hya

/-! ## The CES certainty equivalent, its price index and demands (O&R (23)–(25)) -/

/-- The CES certainty-equivalent consumption index, O&R (23), p. 283:
`Ω(C₂) = [Σ π(s)C₂(s)^{1−ρ}]^{1/(1−ρ)}`. -/
noncomputable def cesIndex (Ω : StateSpace S) (ρ : ℝ) (C : S → ℝ) : ℝ :=
  (∑ s, Ω.prob s * C s ^ (1 - ρ)) ^ (1 / (1 - ρ))

/-- The date-2 consumption-based price index, O&R (25), p. 283:
`P = [Σ π(s)^{1/ρ} p(s)^{(ρ−1)/ρ}]^{ρ/(ρ−1)}`. -/
noncomputable def priceIndex (Ω : StateSpace S) (ρ : ℝ) (p : S → ℝ) : ℝ :=
  (∑ s, Ω.prob s ^ (1 / ρ) * p s ^ ((ρ - 1) / ρ)) ^ (ρ / (ρ - 1))

/-- The state-contingent consumption demands, O&R (24), p. 283:
`C₂(s) = [(p(s)/π(s))/P]^{−1/ρ} Z₂/P`. -/
noncomputable def cesDemand (Ω : StateSpace S) (ρ : ℝ) (p : S → ℝ) (Z : ℝ) (s : S) : ℝ :=
  (p s / Ω.prob s / priceIndex Ω ρ p) ^ (-1 / ρ) * (Z / priceIndex Ω ρ p)

/-- A finite state space with probabilities summing to one is nonempty (used throughout
O&R §5.1.8). -/
theorem univ_nonempty_of_stateSpace (Ω : StateSpace S) : (Finset.univ : Finset S).Nonempty := by
  by_contra h
  rw [Finset.not_nonempty_iff_eq_empty] at h
  have h1 := Ω.prob_sum
  rw [h, Finset.sum_empty] at h1
  exact zero_ne_one h1

/-- The sum inside the price index (25) is positive, O&R p. 283 (for `π, p > 0`). -/
theorem priceSum_pos (Ω : StateSpace S) (hπ : ∀ s, 0 < Ω.prob s) (p : S → ℝ)
    (hp : ∀ s, 0 < p s) (ρ : ℝ) :
    0 < ∑ s, Ω.prob s ^ (1 / ρ) * p s ^ ((ρ - 1) / ρ) :=
  Finset.sum_pos (fun s _ => by have := hπ s; have := hp s; positivity)
    (univ_nonempty_of_stateSpace Ω)

/-- The price index (25) is positive, O&R p. 283 (for `π, p > 0`). -/
theorem priceIndex_pos (Ω : StateSpace S) (hπ : ∀ s, 0 < Ω.prob s) (p : S → ℝ)
    (hp : ∀ s, 0 < p s) (ρ : ℝ) : 0 < priceIndex Ω ρ p :=
  Real.rpow_pos_of_pos (priceSum_pos Ω hπ p hp ρ) _

/-- Cost of the demands (24), O&R p. 283: `Σ p(s)C₂(s) = Z₂` (for `π, p, Z₂ > 0`,
`0 < ρ ≠ 1`). -/
theorem demand_cost (Ω : StateSpace S) (hπ : ∀ s, 0 < Ω.prob s) (p : S → ℝ)
    (hp : ∀ s, 0 < p s) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≠ 1) {Z : ℝ} (hZ : 0 < Z) :
    ∑ s, p s * cesDemand Ω ρ p Z s = Z := by
  have hD0 := priceSum_pos Ω hπ p hp ρ
  have hP := priceIndex_pos Ω hπ p hp ρ
  set D0 := ∑ s, Ω.prob s ^ (1 / ρ) * p s ^ ((ρ - 1) / ρ) with hD0def
  set P := priceIndex Ω ρ p with hPdef
  have hρ1' : ρ - 1 ≠ 0 := sub_ne_zero.mpr hρ1
  have hPpow : P ^ ((1 - ρ) / ρ) = D0⁻¹ := by
    rw [hPdef, priceIndex, ← hD0def, ← Real.rpow_mul hD0.le,
      show ρ / (ρ - 1) * ((1 - ρ) / ρ) = -1 by field_simp; ring, Real.rpow_neg_one]
  have term : ∀ s, p s * cesDemand Ω ρ p Z s =
      Z * P ^ ((1 - ρ) / ρ) * (Ω.prob s ^ (1 / ρ) * p s ^ ((ρ - 1) / ρ)) := fun s => by
    have := hπ s
    have := hp s
    refine Real.log_injOn_pos (Set.mem_Ioi.2 (by unfold cesDemand; positivity))
      (Set.mem_Ioi.2 (by positivity)) ?_
    simp only [cesDemand, ← hPdef]
    simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_rpow]
    field_simp
    ring
  rw [Finset.sum_congr rfl fun s _ => term s, ← Finset.mul_sum, ← hD0def, hPpow]
  field_simp

/-- The first-order condition behind the demands (24), O&R pp. 283–284:
`π(s)C₂(s)^{−ρ} = λ p(s)` with the same `λ = (Z₂/P)^{−ρ}/P` in every state. -/
theorem demand_foc (Ω : StateSpace S) (hπ : ∀ s, 0 < Ω.prob s) (p : S → ℝ)
    (hp : ∀ s, 0 < p s) {ρ : ℝ} (hρ0 : 0 < ρ) {Z : ℝ} (hZ : 0 < Z) (s : S) :
    Ω.prob s * cesDemand Ω ρ p Z s ^ (-ρ) =
      p s * ((Z / priceIndex Ω ρ p) ^ (-ρ) / priceIndex Ω ρ p) := by
  have hP := priceIndex_pos Ω hπ p hp ρ
  set P := priceIndex Ω ρ p with hPdef
  have := hπ s
  have := hp s
  refine Real.log_injOn_pos (Set.mem_Ioi.2 (by unfold cesDemand; positivity))
    (Set.mem_Ioi.2 (by positivity)) ?_
  simp only [cesDemand, ← hPdef]
  simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_rpow]
  field_simp
  ring

/-- The demands (24) attain the consumption index `Ω = Z₂/P`, O&R (24)–(25), p. 283 (for
`π, p, Z₂ > 0`, `0 < ρ ≠ 1`). -/
theorem cesIndex_demand (Ω : StateSpace S) (hπ : ∀ s, 0 < Ω.prob s) (p : S → ℝ)
    (hp : ∀ s, 0 < p s) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≠ 1) {Z : ℝ} (hZ : 0 < Z) :
    ∑ s, Ω.prob s * cesDemand Ω ρ p Z s ^ (1 - ρ) = (Z / priceIndex Ω ρ p) ^ (1 - ρ) ∧
      cesIndex Ω ρ (cesDemand Ω ρ p Z) = Z / priceIndex Ω ρ p := by
  have hD0 := priceSum_pos Ω hπ p hp ρ
  have hP := priceIndex_pos Ω hπ p hp ρ
  set D0 := ∑ s, Ω.prob s ^ (1 / ρ) * p s ^ ((ρ - 1) / ρ) with hD0def
  set P := priceIndex Ω ρ p with hPdef
  have hρ1' : ρ - 1 ≠ 0 := sub_ne_zero.mpr hρ1
  have h1ρ : 1 - ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm hρ1)
  have hPpow : P ^ ((1 - ρ) / ρ) = D0⁻¹ := by
    rw [hPdef, priceIndex, ← hD0def, ← Real.rpow_mul hD0.le,
      show ρ / (ρ - 1) * ((1 - ρ) / ρ) = -1 by field_simp; ring, Real.rpow_neg_one]
  have term : ∀ s, Ω.prob s * cesDemand Ω ρ p Z s ^ (1 - ρ) =
      (Z / P) ^ (1 - ρ) * P ^ ((1 - ρ) / ρ) *
        (Ω.prob s ^ (1 / ρ) * p s ^ ((ρ - 1) / ρ)) := fun s => by
    have := hπ s
    have := hp s
    refine Real.log_injOn_pos (Set.mem_Ioi.2 (by unfold cesDemand; positivity))
      (Set.mem_Ioi.2 (by positivity)) ?_
    simp only [cesDemand, ← hPdef]
    simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_rpow]
    field_simp
    ring
  have hsum : ∑ s, Ω.prob s * cesDemand Ω ρ p Z s ^ (1 - ρ) = (Z / P) ^ (1 - ρ) := by
    rw [Finset.sum_congr rfl fun s _ => term s, ← Finset.mul_sum, ← hD0def, hPpow]
    field_simp
  refine ⟨hsum, ?_⟩
  rw [cesIndex, hsum, one_div, Real.rpow_rpow_inv (by positivity) h1ρ]

/-- Second-stage optimality of the demands (24), O&R §5.1.8, p. 283 (two-stage budgeting, step
2): for `π, p, Z₂ > 0` and `0 < ρ ≠ 1`, every positive bundle `C₂` with `Σ p(s)C₂(s) ≤ Z₂` has
`Ω(C₂) ≤ Z₂/P`, strictly unless `C₂` is the demand bundle (24). Proof: the tangent-line
inequality for `x^{1−ρ}` at the demands, whose marginal utilities are proportional to `p`. -/
theorem cesIndex_le (Ω : StateSpace S) (hπ : ∀ s, 0 < Ω.prob s) (p : S → ℝ)
    (hp : ∀ s, 0 < p s) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≠ 1) {Z : ℝ} (hZ : 0 < Z)
    (C : S → ℝ) (hC : ∀ s, 0 < C s) (hbud : ∑ s, p s * C s ≤ Z) :
    cesIndex Ω ρ C ≤ Z / priceIndex Ω ρ p ∧
      ((∃ s, C s ≠ cesDemand Ω ρ p Z s) → cesIndex Ω ρ C < Z / priceIndex Ω ρ p) := by
  have hP := priceIndex_pos Ω hπ p hp ρ
  set P := priceIndex Ω ρ p with hPdef
  set D := cesDemand Ω ρ p Z with hDdef
  have hD : ∀ s, 0 < D s := fun s => by
    have := hπ s; have := hp s
    simp only [hDdef, cesDemand, ← hPdef]
    positivity
  set lam := (Z / P) ^ (-ρ) / P with hlam
  have hlampos : 0 < lam := by positivity
  have hfoc : ∀ s, Ω.prob s * D s ^ (-ρ) = p s * lam := demand_foc Ω hπ p hp hρ0 hZ
  have hcost : ∑ s, p s * D s = Z := demand_cost Ω hπ p hp hρ0 hρ1 hZ
  obtain ⟨hval, hind⟩ := cesIndex_demand Ω hπ p hp hρ0 hρ1 hZ
  rw [← hDdef, ← hPdef] at hval hind
  rw [← hind]
  set a := 1 - ρ with ha
  have ha1 : a - 1 = -ρ := by rw [ha]; ring
  have lin : ∑ s, Ω.prob s * (D s ^ a + a * D s ^ (a - 1) * (C s - D s)) =
      ∑ s, Ω.prob s * D s ^ a + a * lam * (∑ s, p s * C s - Z) := by
    rw [← hcost, ← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [ha1, show Ω.prob s * (D s ^ a + a * D s ^ (-ρ) * (C s - D s)) =
      Ω.prob s * D s ^ a + a * (Ω.prob s * D s ^ (-ρ)) * (C s - D s) by ring, hfoc s]
    ring
  have hDsum : 0 < ∑ s, Ω.prob s * D s ^ a :=
    Finset.sum_pos (fun s _ => by have := hπ s; have := hD s; positivity)
      (univ_nonempty_of_stateSpace Ω)
  have hCsum : 0 ≤ ∑ s, Ω.prob s * C s ^ a :=
    Finset.sum_nonneg fun s _ => by have := hπ s; have := hC s; positivity
  rcases lt_or_gt_of_ne hρ1 with hlt | hgt
  · -- ρ < 1: `x^a` concave, the sum is maximised at the demands.
    have ha0 : 0 < a := by rw [ha]; linarith
    have ha1' : a < 1 := by rw [ha]; linarith
    have hexp : 0 < 1 / a := by positivity
    have hterm : ∀ s, Ω.prob s * C s ^ a ≤
        Ω.prob s * (D s ^ a + a * D s ^ (a - 1) * (C s - D s)) := fun s =>
      mul_le_mul_of_nonneg_left (rpow_le_tangent ha0 ha1' (hC s) (hD s)).1 (hπ s).le
    have hneg : a * lam * (∑ s, p s * C s - Z) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
    have hle : ∑ s, Ω.prob s * C s ^ a ≤ ∑ s, Ω.prob s * D s ^ a := by
      have := Finset.sum_le_sum fun s (_ : s ∈ Finset.univ) => hterm s
      linarith
    refine ⟨Real.rpow_le_rpow hCsum hle hexp.le, fun ⟨s0, hs0⟩ => ?_⟩
    have hlt' : ∑ s, Ω.prob s * C s ^ a < ∑ s, Ω.prob s * D s ^ a := by
      have := Finset.sum_lt_sum (fun s (_ : s ∈ Finset.univ) => hterm s)
        ⟨s0, Finset.mem_univ _, mul_lt_mul_of_pos_left
          ((rpow_le_tangent ha0 ha1' (hC s0) (hD s0)).2 hs0) (hπ s0)⟩
      linarith
    exact Real.rpow_lt_rpow hCsum hlt' hexp
  · -- ρ > 1: `x^a` convex with `a < 0`, the sum is minimised at the demands.
    have ha0 : a < 0 := by rw [ha]; linarith
    have hexp : 1 / a < 0 := by rw [one_div]; exact inv_lt_zero.mpr ha0
    have hterm : ∀ s, Ω.prob s * (D s ^ a + a * D s ^ (a - 1) * (C s - D s)) ≤
        Ω.prob s * C s ^ a := fun s =>
      mul_le_mul_of_nonneg_left (tangent_le_rpow_of_neg ha0 (hC s) (hD s)).1 (hπ s).le
    have hpos : 0 ≤ a * lam * (∑ s, p s * C s - Z) :=
      mul_nonneg_of_nonpos_of_nonpos (mul_nonpos_of_nonpos_of_nonneg ha0.le hlampos.le)
        (by linarith)
    have hle : ∑ s, Ω.prob s * D s ^ a ≤ ∑ s, Ω.prob s * C s ^ a := by
      have := Finset.sum_le_sum fun s (_ : s ∈ Finset.univ) => hterm s
      linarith
    refine ⟨Real.rpow_le_rpow_of_nonpos hDsum hle hexp.le, fun ⟨s0, hs0⟩ => ?_⟩
    have hlt' : ∑ s, Ω.prob s * D s ^ a < ∑ s, Ω.prob s * C s ^ a := by
      have := Finset.sum_lt_sum (fun s (_ : s ∈ Finset.univ) => hterm s)
        ⟨s0, Finset.mem_univ _, mul_lt_mul_of_pos_left
          ((tangent_le_rpow_of_neg ha0 (hC s0) (hD s0)).2 hs0) (hπ s0)⟩
      linarith
    exact Real.rpow_lt_rpow_of_neg hDsum hlt' hexp

/-- Two-stage budgeting reduces (20) to (21), O&R pp. 282–283: for any increasing `u` and
`β ≥ 0`, lifetime utility (20) of any positive plan `(C₁, C₂)` is at most
`u(C₁) + βu(Z₂/P)` with `Z₂ = Σ p(s)C₂(s)` its date-2 spending, with equality at the demands
(24). -/
theorem lifetime_le_two_stage (Ω : StateSpace S) (hπ : ∀ s, 0 < Ω.prob s) (p : S → ℝ)
    (hp : ∀ s, 0 < p s) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≠ 1) {u : ℝ → ℝ} (hu : Monotone u)
    {β : ℝ} (hβ : 0 ≤ β) (C1 : ℝ) (C2 : S → ℝ) (hC2 : ∀ s, 0 < C2 s) :
    u C1 + β * u (cesIndex Ω ρ C2) ≤
        u C1 + β * u ((∑ s, p s * C2 s) / priceIndex Ω ρ p) ∧
      (0 < (∑ s, p s * C2 s) → u C1 + β * u (cesIndex Ω ρ (cesDemand Ω ρ p (∑ s, p s * C2 s)))
        = u C1 + β * u ((∑ s, p s * C2 s) / priceIndex Ω ρ p)) := by
  have hZ : 0 < ∑ s, p s * C2 s :=
    Finset.sum_pos (fun s _ => mul_pos (hp s) (hC2 s)) (univ_nonempty_of_stateSpace Ω)
  refine ⟨?_, fun hZ' => by rw [(cesIndex_demand Ω hπ p hp hρ0 hρ1 hZ').2]⟩
  have := (cesIndex_le Ω hπ p hp hρ0 hρ1 hZ C2 hC2 le_rfl).1
  have := hu this
  nlinarith

/-- The price index is at most one, with equality iff prices are actuarially fair,
O&R p. 285: for probability vectors `π > 0`, `p > 0` (`Σ p(s) = 1`) and `0 < ρ ≠ 1`,
`P ≤ 1`, and `P = 1` iff `p(s) = π(s)` for all `s`. (The book's argument: the sure bundle
`C₂ ≡ 1` costs `Σ p(s) = 1` and has `Ω = 1`, and it is the demand bundle only at fair
prices.) -/
theorem priceIndex_le_one (Ω : StateSpace S) (hπ : ∀ s, 0 < Ω.prob s) (p : S → ℝ)
    (hp : ∀ s, 0 < p s) (hpsum : ∑ s, p s = 1) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≠ 1) :
    priceIndex Ω ρ p ≤ 1 ∧ (priceIndex Ω ρ p = 1 ↔ ∀ s, p s = Ω.prob s) := by
  have hP := priceIndex_pos Ω hπ p hp ρ
  have hone : cesIndex Ω ρ (fun _ => 1) = 1 := by
    simp only [cesIndex, Real.one_rpow, mul_one, Ω.prob_sum]
  have hbud : ∑ s, p s * (fun _ => (1 : ℝ)) s ≤ 1 := by simp [hpsum]
  have h := cesIndex_le Ω hπ p hp hρ0 hρ1 one_pos (fun _ => 1) (fun _ => one_pos) hbud
  rw [hone] at h
  have hle : priceIndex Ω ρ p ≤ 1 := by
    have := h.1
    rw [le_div_iff₀ hP, one_mul] at this
    exact this
  refine ⟨hle, ⟨fun hP1 => ?_, fun hfair => ?_⟩⟩
  · by_contra hne
    push Not at hne
    obtain ⟨s, hs⟩ := hne
    have hdem : (fun _ => (1 : ℝ)) s ≠ cesDemand Ω ρ p 1 s := by
      intro h1
      simp only [cesDemand, hP1, div_one, mul_one] at h1
      have hps := hp s
      have hπs := hπ s
      have hlog := congrArg Real.log h1.symm
      rw [Real.log_one, Real.log_rpow (by positivity)] at hlog
      have hl : Real.log (p s / Ω.prob s) = 0 := by
        rcases mul_eq_zero.mp hlog with h0 | h0
        · exact absurd h0 (div_ne_zero (by norm_num) hρ0.ne')
        · exact h0
      have := Real.eq_one_of_pos_of_log_eq_zero (by positivity) hl
      exact hs ((div_eq_one_iff_eq hπs.ne').mp this)
    have := h.2 ⟨s, hdem⟩
    rw [hP1] at this
    norm_num at this
  · have e : ∑ s, Ω.prob s ^ (1 / ρ) * p s ^ ((ρ - 1) / ρ) = 1 := by
      refine (Finset.sum_congr rfl fun s _ => ?_).trans Ω.prob_sum
      rw [hfair s, ← Real.rpow_add (hπ s), show 1 / ρ + (ρ - 1) / ρ = 1 by field_simp; ring,
        Real.rpow_one]
    rw [priceIndex, e, Real.one_rpow]

/-! ## The first stage: saving and the current account (O&R (21)–(22), (27), footnote 14) -/

/-- The intertemporal Euler equation (27), O&R p. 284: with isoelastic `u′(C) = C^{−1/σ}`
(`σ > 0`), the first-stage Euler equation `u′(C₁) = (1+r)β(1/P)u′(Z₂/P)` is equivalent to
`Z₂ = (1+r)^σ β^σ (1/P)^{σ−1} C₁` (all quantities positive). -/
theorem euler_27 {σ r β C1 Z2 P : ℝ} (hσ : 0 < σ) (hr : 0 < 1 + r) (hβ : 0 < β)
    (hC1 : 0 < C1) (hZ2 : 0 < Z2) (hP : 0 < P) :
    C1 ^ (-1 / σ) = (1 + r) * β * P⁻¹ * (Z2 / P) ^ (-1 / σ) ↔
      Z2 = (1 + r) ^ σ * β ^ σ * (1 / P) ^ (σ - 1) * C1 := by
  constructor
  · intro h
    have hL := congrArg Real.log h
    simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_rpow,
      Real.log_inv] at hL
    refine Real.log_injOn_pos (Set.mem_Ioi.2 hZ2) (Set.mem_Ioi.2 (by positivity)) ?_
    simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_rpow, Real.log_one]
    field_simp at hL ⊢
    linarith
  · intro h
    refine Real.log_injOn_pos (Set.mem_Ioi.2 (by positivity))
      (Set.mem_Ioi.2 (by positivity)) ?_
    have hL := congrArg Real.log h
    simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_rpow,
      Real.log_one] at hL
    simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_rpow, Real.log_inv]
    field_simp at hL ⊢
    linarith

/-- Date-1 consumption, O&R p. 284: the Euler equation (27) and the lifetime budget (22),
`C₁ + Z₂/(1+r) = W₁`, give `C₁ = W₁/(1 + ((1+r)/P)^{σ−1}β^σ)`. -/
theorem consumption_27 {σ r β C1 Z2 P W1 : ℝ} (hr : 0 < 1 + r) (hβ : 0 < β) (hP : 0 < P)
    (h27 : Z2 = (1 + r) ^ σ * β ^ σ * (1 / P) ^ (σ - 1) * C1)
    (hbud : C1 + Z2 / (1 + r) = W1) :
    C1 = W1 / (1 + ((1 + r) / P) ^ (σ - 1) * β ^ σ) := by
  have e : Z2 / (1 + r) = ((1 + r) / P) ^ (σ - 1) * β ^ σ * C1 := by
    rw [h27, Real.div_rpow hr.le hP.le, Real.div_rpow zero_le_one hP.le, Real.one_rpow,
      Real.rpow_sub_one hr.ne']
    have : 0 < P ^ (σ - 1) := Real.rpow_pos_of_pos hP _
    field_simp
  rw [eq_div_iff (by positivity)]
  linarith

/-- The current-account-autarky interest rate and the sign of the current account, O&R
footnote 14, p. 285: with `W₁ = Y₁ + V/(1+r)`, `V = Σ p(s)Y₂(s) > 0` and
`C₁ = W₁/(1 + ((1+r)/P)^{σ−1}β^σ)`, define
`1 + r^CA = (1/β)[V/(P^{1−σ}Y₁)]^{1/σ}`. Then `CA₁ = Y₁ − C₁` is positive iff `r > r^CA`,
negative iff `r < r^CA`, and zero (`C₁ = Y₁`) iff `r = r^CA`. -/
theorem current_account_sign_rCA {σ r β P Y1 V : ℝ} (hσ : 0 < σ) (hr : 0 < 1 + r)
    (hβ : 0 < β) (hP : 0 < P) (hY1 : 0 < Y1) (hV : 0 < V) :
    let CA := Y1 - (Y1 + V / (1 + r)) / (1 + ((1 + r) / P) ^ (σ - 1) * β ^ σ)
    let RCA := 1 / β * (V / (P ^ (1 - σ) * Y1)) ^ (1 / σ)
    (0 < CA ↔ RCA < 1 + r) ∧ (CA < 0 ↔ 1 + r < RCA) ∧ (CA = 0 ↔ 1 + r = RCA) := by
  intro CA RCA
  set R := 1 + r with hR
  set K := (R / P) ^ (σ - 1) * β ^ σ with hK
  have hKpos : 0 < K := by positivity
  set g : ℝ → ℝ := fun x => Y1 * P ^ (1 - σ) * (β * x) ^ σ with hg
  have hgmono : ∀ x y, 0 < x → 0 < y → (g x < g y ↔ x < y) := fun x y hx hy => by
    simp only [hg]
    rw [mul_lt_mul_iff_right₀ (by positivity), Real.rpow_lt_rpow_iff (by positivity)
      (by positivity) hσ, mul_lt_mul_iff_right₀ hβ]
  have hRCA : 0 < RCA := by positivity
  have hgRCA : g RCA = V := by
    simp only [hg, RCA]
    rw [show β * (1 / β * (V / (P ^ (1 - σ) * Y1)) ^ (1 / σ)) =
      (V / (P ^ (1 - σ) * Y1)) ^ (1 / σ) by field_simp, one_div,
      Real.rpow_inv_rpow (by positivity) hσ.ne']
    have : 0 < P ^ (1 - σ) := Real.rpow_pos_of_pos hP _
    field_simp
  have hgR : Y1 * K * R = g R := by
    simp only [hK, hg]
    refine Real.log_injOn_pos (Set.mem_Ioi.2 (by positivity))
      (Set.mem_Ioi.2 (by positivity)) ?_
    simp (disch := positivity) only [Real.log_mul, Real.log_div, Real.log_rpow]
    ring
  have hCA : CA = (g R - V) / (R * (1 + K)) := by
    simp only [CA, ← hR, ← hK, ← hgR]
    field_simp
    ring
  have hden : 0 < R * (1 + K) := by positivity
  have hpos : 0 < CA ↔ RCA < R := by
    rw [hCA, div_pos_iff_of_pos_right hden, sub_pos, ← hgRCA]
    exact hgmono _ _ hRCA hr
  have hneg : CA < 0 ↔ R < RCA := by
    rw [hCA, div_neg_iff, sub_neg, ← hgRCA]
    constructor
    · rintro (⟨h1, _⟩ | ⟨h1, _⟩)
      · exact absurd h1 (not_lt.mpr (le_of_lt (by linarith [hgRCA ▸ h1])))
      · exact (hgmono _ _ hr hRCA).mp h1
    · intro h
      exact Or.inr ⟨(hgmono _ _ hr hRCA).mpr h, hden⟩
  refine ⟨hpos, hneg, ?_⟩
  constructor
  · intro h0
    rcases lt_trichotomy R RCA with h | h | h
    · exact absurd (hneg.mpr h) (by rw [h0]; exact lt_irrefl 0)
    · exact h
    · exact absurd (hpos.mpr h) (by rw [h0]; exact lt_irrefl 0)
  · intro h
    rw [hCA, h, hgRCA, sub_self, zero_div]

/-- Date-1 consumption versus its certainty benchmark, O&R p. 285: when `P < 1` (prices not
actuarially fair) the consumption-based real interest rate `(1+r)/P` exceeds `1 + r`, so
`C₁ = W₁/(1 + ((1+r)/P)^{σ−1}β^σ)` is strictly below the certainty benchmark
`W₁/(1 + (1+r)^{σ−1}β^σ)` (the value at `P = 1`) if `σ > 1`, and strictly above it if
`σ < 1` (`W₁ > 0`). -/
theorem consumption_vs_certainty {σ r β P W1 : ℝ} (hr : 0 < 1 + r) (hβ : 0 < β)
    (hP0 : 0 < P) (hP1 : P < 1) (hW : 0 < W1) :
    (1 < σ → W1 / (1 + ((1 + r) / P) ^ (σ - 1) * β ^ σ) <
      W1 / (1 + (1 + r) ^ (σ - 1) * β ^ σ)) ∧
    (σ < 1 → W1 / (1 + (1 + r) ^ (σ - 1) * β ^ σ) <
      W1 / (1 + ((1 + r) / P) ^ (σ - 1) * β ^ σ)) := by
  have hlt : 1 + r < (1 + r) / P := by
    rw [lt_div_iff₀ hP0]
    nlinarith
  have hbσ : 0 < β ^ σ := Real.rpow_pos_of_pos hβ σ
  constructor
  · intro hσ
    have h := Real.rpow_lt_rpow hr.le hlt (by linarith : 0 < σ - 1)
    apply div_lt_div_of_pos_left hW (by positivity)
    nlinarith
  · intro hσ
    have h := Real.rpow_lt_rpow_of_neg hr hlt (by linarith : σ - 1 < 0)
    apply div_lt_div_of_pos_left hW (by positivity)
    nlinarith

/-- Special case 1, O&R p. 284: with `σ = 1` the income and substitution effects of `P ≠ 1`
offset exactly, and `C₁ = W₁/(1+β)` whatever `P` (as in the log example of §5.1.6). -/
theorem consumption_sigma_one {r β P W1 : ℝ} :
    W1 / (1 + ((1 + r) / P) ^ ((1 : ℝ) - 1) * β ^ (1 : ℝ)) = W1 / (1 + β) := by
  rw [sub_self, Real.rpow_zero, Real.rpow_one, one_mul]

/-- Special case 2, O&R pp. 284–285: at actuarially fair prices `p = π` the price index is
`P = 1`, so `C₁ = W₁/(1 + (1+r)^{σ−1}β^σ)`, the certainty formula with date-2 output
`Σ p(s)Y₂(s)`. -/
theorem consumption_fair_prices (Ω : StateSpace S) (hπ : ∀ s, 0 < Ω.prob s) (p : S → ℝ)
    (hfair : ∀ s, p s = Ω.prob s) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≠ 1) (σ r β W1 : ℝ) :
    W1 / (1 + ((1 + r) / priceIndex Ω ρ p) ^ (σ - 1) * β ^ σ) =
      W1 / (1 + (1 + r) ^ (σ - 1) * β ^ σ) := by
  have hp : ∀ s, 0 < p s := fun s => (hfair s).symm ▸ hπ s
  have hpsum : ∑ s, p s = 1 := by rw [Finset.sum_congr rfl fun s _ => hfair s, Ω.prob_sum]
  rw [((priceIndex_le_one Ω hπ p hp hpsum hρ0 hρ1).2.mpr hfair), div_one]

/-- A current-account surplus from risk alone, O&R p. 285: even with `β(1+r) = 1` and
`Y₁ = V = Σ p(s)Y₂(s)` (which would give `CA₁ = 0` under certainty), `P < 1` implies
`CA₁ = Y₁ − C₁ > 0` when `σ > 1` and `CA₁ < 0` when `σ < 1`, where
`C₁ = (Y₁ + V/(1+r))/(1 + ((1+r)/P)^{σ−1}β^σ)`. -/
theorem current_account_fair_rate {σ r β P Y1 : ℝ} (hr : 0 < 1 + r) (hβR : β * (1 + r) = 1)
    (hP0 : 0 < P) (hP1 : P < 1) (hY1 : 0 < Y1) :
    (1 < σ → 0 < Y1 - (Y1 + Y1 / (1 + r)) / (1 + ((1 + r) / P) ^ (σ - 1) * β ^ σ)) ∧
      (σ < 1 → Y1 - (Y1 + Y1 / (1 + r)) / (1 + ((1 + r) / P) ^ (σ - 1) * β ^ σ) < 0) := by
  have hβ' : β = (1 + r)⁻¹ := eq_inv_of_mul_eq_one_left hβR
  have hβ : 0 < β := by rw [hβ']; positivity
  have hb : (1 + r) ^ (σ - 1) * β ^ σ = β := by
    rw [hβ', Real.inv_rpow hr.le, ← Real.rpow_neg hr.le, ← Real.rpow_add hr,
      show σ - 1 + -σ = -1 by ring, Real.rpow_neg_one]
  have hbench : (Y1 + Y1 / (1 + r)) / (1 + (1 + r) ^ (σ - 1) * β ^ σ) = Y1 := by
    rw [hb, hβ']
    field_simp
  have h := consumption_vs_certainty (σ := σ) hr hβ hP0 hP1
    (by positivity : 0 < Y1 + Y1 / (1 + r))
  rw [hbench] at h
  exact ⟨fun hσ => by linarith [h.1 hσ], fun hσ => by linarith [h.2 hσ]⟩

end ObstfeldRogoff.InternationalFinancialMarkets.TwoStageBudgeting
