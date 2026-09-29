/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import InternationalFinancialMarkets.Model
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Risk aversion, intertemporal substitution and two-stage budgeting

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §5.1.8,
pp. 282–285, including footnotes 13 and 14.

Lifetime utility is `u(C₁) + βu(Ω(C₂))` (O&R (20)) with the CES certainty equivalent
`Ω(C₂) = [Σ π(s)C₂(s)^{1−ρ}]^{1/(1−ρ)}` (O&R (23)), `0 < ρ ≠ 1`, or its log limit (the
geometric mean `exp(Σ π(s) log C₂(s))`) at `ρ = 1` (footnote 13). Date-1 prices of state
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
  `β(1+r) = 1` and `Y₁ = Σ p(s)Y₂(s)`, `CA₁ > 0` when `σ > 1` and `CA₁ < 0` when `σ < 1`;
* stage 2 at `ρ = 1` (demands `π(s)Z₂/p(s)`, `P = exp(Σ π(s) log(p(s)/π(s)))`), so that
  stage 2 holds for every `ρ > 0`;
* stage 1 in full for isoelastic `u(C) = C^{1−1/σ}/(1 − 1/σ)` (log at `σ = 1`): the consumption
  function maximises (21) subject to (22) (sufficiency, by concavity), strictly, so any
  maximiser equals it (necessity and uniqueness); a feasible point is optimal iff it satisfies
  (27), iff it satisfies the Euler equation;
* two-stage budgeting solves (20): the two-stage plan maximises `u(C₁) + βu(Ω(C₂))` over all
  positive state-contingent plans on the budget line and is the unique maximiser, for any
  index with the stage-2 properties;
* the Epstein–Zin/Kreps–Porteus preferences (26) (as printed, and with the `ρ = 1`, `σ = 1`
  log limits of footnote 13): their unique optimum is the two-stage plan, with stage 2 as under
  expected utility and stage 1 using `σ`; when `σ = 1/ρ`, (26) equals expected utility
  `C₁^{1−ρ}/(1−ρ) + βΣ π(s)C₂(s)^{1−ρ}/(1−ρ)` identically, so the two rank all plans alike
  and have the same unique optimum; conversely (26) ranks positive plans as expected utility
  does only when `σ = 1/ρ`;
* the current-account statements of p. 285 and footnote 14 restated at the optimum of (26).
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


/-! ## The log limit `ρ = 1` of the certainty equivalent (O&R footnote 13) -/

/-- The tangent-line inequality for `log` (used for the `ρ = 1` and `σ = 1` cases of O&R
§5.1.8, footnote 13): `log x ≤ log y + (x − y)/y` for `x, y > 0`, strictly if `x ≠ y`. -/
theorem log_le_tangent {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Real.log x ≤ Real.log y + (x - y) / y ∧
      (x ≠ y → Real.log x < Real.log y + (x - y) / y) := by
  have e : Real.log x - Real.log y = Real.log (x / y) := (Real.log_div hx.ne' hy.ne').symm
  have e2 : (x - y) / y = x / y - 1 := by field_simp
  refine ⟨by linarith [Real.log_le_sub_one_of_pos (div_pos hx hy)], fun hxy => ?_⟩
  have := Real.log_lt_sub_one_of_pos (div_pos hx hy)
    (fun h => hxy ((div_eq_one_iff_eq hy.ne').mp h))
  linarith

/-- The certainty equivalent (23) in its `ρ = 1` (log) limit, O&R footnote 13, p. 284: the
geometric mean `Ω(C₂) = exp(Σ π(s) log C₂(s))` (the L'Hospital limit of (23) as `ρ → 1`). -/
noncomputable def geoIndex (Ω : StateSpace S) (C : S → ℝ) : ℝ :=
  Real.exp (∑ s, Ω.prob s * Real.log (C s))

/-- The price index (25) in its `ρ = 1` limit, O&R footnote 13, p. 284:
`P = exp(Σ π(s) log(p(s)/π(s)))`. -/
noncomputable def geoPrice (Ω : StateSpace S) (p : S → ℝ) : ℝ :=
  Real.exp (∑ s, Ω.prob s * Real.log (p s / Ω.prob s))

/-- The demands (24) at `ρ = 1`, O&R (24) and footnote 13, p. 283–284:
`C₂(s) = π(s)Z₂/p(s)`. -/
noncomputable def geoDemand (Ω : StateSpace S) (p : S → ℝ) (Z : ℝ) (s : S) : ℝ :=
  Ω.prob s * Z / p s

/-- The `ρ = 1` demands are the formula (24) with `ρ = 1`, O&R (24), p. 283:
`[(p(s)/π(s))/P]^{−1} Z₂/P = π(s)Z₂/p(s)` (for `π(s), p(s), P > 0`). -/
theorem geoDemand_eq_24 (Ω : StateSpace S) (p : S → ℝ) {P Z : ℝ} {s : S}
    (hπ : 0 < Ω.prob s) (hp : 0 < p s) (hP : 0 < P) :
    (p s / Ω.prob s / P) ^ (-1 / (1 : ℝ)) * (Z / P) = geoDemand Ω p Z s := by
  rw [div_one, Real.rpow_neg_one, geoDemand]
  field_simp

/-- Stage 2 at `ρ = 1`, O&R (24)–(25) and footnote 13, pp. 283–284: for `π, p, Z₂ > 0` the
demands `π(s)Z₂/p(s)` are positive, cost exactly `Z₂`, and attain `Ω = Z₂/P`; and every
positive bundle costing at most `Z₂` has `Ω(C₂) ≤ Z₂/P`, strictly unless it is the demand
bundle. -/
theorem geo_stage_two (Ω : StateSpace S) (hπ : ∀ s, 0 < Ω.prob s) (p : S → ℝ)
    (hp : ∀ s, 0 < p s) {Z : ℝ} (hZ : 0 < Z) :
    (∀ s, 0 < geoDemand Ω p Z s) ∧ ∑ s, p s * geoDemand Ω p Z s = Z ∧
      geoIndex Ω (geoDemand Ω p Z) = Z / geoPrice Ω p ∧
      ∀ C : S → ℝ, (∀ s, 0 < C s) → ∑ s, p s * C s ≤ Z →
        geoIndex Ω C ≤ Z / geoPrice Ω p ∧
          ((∃ s, C s ≠ geoDemand Ω p Z s) → geoIndex Ω C < Z / geoPrice Ω p) := by
  have hD : ∀ s, 0 < geoDemand Ω p Z s := fun s => by
    have := hπ s; have := hp s; unfold geoDemand; positivity
  have hcost : ∑ s, p s * geoDemand Ω p Z s = Z := by
    rw [Finset.sum_congr rfl fun s _ => show p s * geoDemand Ω p Z s = Z * Ω.prob s by
      have := (hp s).ne'; unfold geoDemand; field_simp, ← Finset.mul_sum, Ω.prob_sum,
      mul_one]
  have hlogD : ∑ s, Ω.prob s * Real.log (geoDemand Ω p Z s) =
      Real.log Z - ∑ s, Ω.prob s * Real.log (p s / Ω.prob s) := by
    have e : ∀ s, Ω.prob s * Real.log (geoDemand Ω p Z s) =
        Ω.prob s * Real.log Z - Ω.prob s * Real.log (p s / Ω.prob s) := fun s => by
      have := hπ s; have := hp s
      unfold geoDemand
      simp (disch := positivity) only [Real.log_mul, Real.log_div]
      ring
    rw [Finset.sum_congr rfl fun s _ => e s, Finset.sum_sub_distrib, ← Finset.sum_mul,
      Ω.prob_sum, one_mul]
  have hval : geoIndex Ω (geoDemand Ω p Z) = Z / geoPrice Ω p := by
    rw [geoIndex, geoPrice, hlogD, Real.exp_sub, Real.exp_log hZ]
  refine ⟨hD, hcost, hval, fun C hC hbud => ?_⟩
  have hterm : ∀ s, Ω.prob s * Real.log (C s) ≤
      Ω.prob s * Real.log (geoDemand Ω p Z s) + (p s * C s / Z - Ω.prob s) := fun s => by
    have e : Ω.prob s * ((C s - geoDemand Ω p Z s) / geoDemand Ω p Z s) =
        p s * C s / Z - Ω.prob s := by
      have := (hπ s).ne'; have := (hp s).ne'; unfold geoDemand; field_simp
    have := mul_le_mul_of_nonneg_left (log_le_tangent (hC s) (hD s)).1 (hπ s).le
    linarith
  have hlin : ∑ s, (p s * C s / Z - Ω.prob s) ≤ 0 := by
    rw [Finset.sum_sub_distrib, ← Finset.sum_div, Ω.prob_sum, sub_nonpos,
      div_le_one hZ]
    exact hbud
  have hsum := Finset.sum_le_sum fun s (_ : s ∈ Finset.univ) => hterm s
  rw [Finset.sum_add_distrib] at hsum
  rw [← hval]
  refine ⟨Real.exp_le_exp.mpr (by linarith), fun ⟨s0, hs0⟩ => ?_⟩
  have hlt := Finset.sum_lt_sum (fun s (_ : s ∈ Finset.univ) => hterm s)
    ⟨s0, Finset.mem_univ _, by
      have e : Ω.prob s0 * ((C s0 - geoDemand Ω p Z s0) / geoDemand Ω p Z s0) =
          p s0 * C s0 / Z - Ω.prob s0 := by
        have := (hπ s0).ne'; have := (hp s0).ne'; unfold geoDemand; field_simp
      have := mul_lt_mul_of_pos_left ((log_le_tangent (hC s0) (hD s0)).2 hs0) (hπ s0)
      linarith⟩
  rw [Finset.sum_add_distrib] at hlt
  exact Real.exp_lt_exp.mpr (by linarith)

/-- The CES certainty equivalent (23) of a positive bundle is positive, O&R p. 283 (for
`π > 0`). -/
theorem cesIndex_pos (Ω : StateSpace S) (hπ : ∀ s, 0 < Ω.prob s) (ρ : ℝ) {C : S → ℝ}
    (hC : ∀ s, 0 < C s) : 0 < cesIndex Ω ρ C :=
  Real.rpow_pos_of_pos (Finset.sum_pos (fun s _ => by have := hπ s; have := hC s; positivity)
    (univ_nonempty_of_stateSpace Ω)) _

/-! ## The risk index for every `ρ > 0` -/

/-- The certainty-equivalent index of O&R (23) for every `ρ > 0`: the CES form (23) for
`ρ ≠ 1` and its log limit, the geometric mean, for `ρ = 1` (footnote 13, p. 284). -/
noncomputable def riskIndex (Ω : StateSpace S) (ρ : ℝ) (C : S → ℝ) : ℝ :=
  if ρ = 1 then geoIndex Ω C else cesIndex Ω ρ C

/-- The price index (25) for every `ρ > 0` (log limit at `ρ = 1`, O&R footnote 13). -/
noncomputable def riskPrice (Ω : StateSpace S) (ρ : ℝ) (p : S → ℝ) : ℝ :=
  if ρ = 1 then geoPrice Ω p else priceIndex Ω ρ p

/-- The demands (24) for every `ρ > 0` (log limit at `ρ = 1`, O&R footnote 13). -/
noncomputable def riskDemand (Ω : StateSpace S) (ρ : ℝ) (p : S → ℝ) (Z : ℝ) (s : S) : ℝ :=
  if ρ = 1 then geoDemand Ω p Z s else cesDemand Ω ρ p Z s

/-- Stage 2 of two-stage budgeting for every `ρ > 0`, O&R (23)–(25), p. 283 and footnote 13:
for `π, p > 0`, the price index is positive, the index of a positive bundle is positive, and
for every `Z₂ > 0` the demands (24) are positive, cost `Z₂` and attain `Ω = Z₂/P`, while every
positive bundle costing at most `Z₂` has `Ω ≤ Z₂/P`, strictly unless it is the demand
bundle. -/
theorem risk_stage_two (Ω : StateSpace S) (hπ : ∀ s, 0 < Ω.prob s) (p : S → ℝ)
    (hp : ∀ s, 0 < p s) {ρ : ℝ} (hρ : 0 < ρ) :
    0 < riskPrice Ω ρ p ∧ (∀ C : S → ℝ, (∀ s, 0 < C s) → 0 < riskIndex Ω ρ C) ∧
      ∀ Z : ℝ, 0 < Z → (∀ s, 0 < riskDemand Ω ρ p Z s) ∧
        ∑ s, p s * riskDemand Ω ρ p Z s = Z ∧
        riskIndex Ω ρ (riskDemand Ω ρ p Z) = Z / riskPrice Ω ρ p ∧
        ∀ C : S → ℝ, (∀ s, 0 < C s) → ∑ s, p s * C s ≤ Z →
          riskIndex Ω ρ C ≤ Z / riskPrice Ω ρ p ∧
            ((∃ s, C s ≠ riskDemand Ω ρ p Z s) → riskIndex Ω ρ C < Z / riskPrice Ω ρ p) := by
  by_cases h1 : ρ = 1
  · have eI : riskIndex Ω ρ = geoIndex Ω := funext fun C => by simp [riskIndex, h1]
    have eP : riskPrice Ω ρ p = geoPrice Ω p := by simp [riskPrice, h1]
    have eD : riskDemand Ω ρ p = geoDemand Ω p := funext fun Z => funext fun s => by
      simp [riskDemand, h1]
    rw [eI, eP, eD]
    exact ⟨Real.exp_pos _, fun C _ => Real.exp_pos _, fun Z hZ => geo_stage_two Ω hπ p hp hZ⟩
  · have eI : riskIndex Ω ρ = cesIndex Ω ρ := funext fun C => by simp [riskIndex, h1]
    have eP : riskPrice Ω ρ p = priceIndex Ω ρ p := by simp [riskPrice, h1]
    have eD : riskDemand Ω ρ p = cesDemand Ω ρ p := funext fun Z => funext fun s => by
      simp [riskDemand, h1]
    rw [eI, eP, eD]
    have hP := priceIndex_pos Ω hπ p hp ρ
    refine ⟨hP, fun C hC => cesIndex_pos Ω hπ ρ hC, fun Z hZ => ⟨fun s => ?_,
      demand_cost Ω hπ p hp hρ h1 hZ, (cesIndex_demand Ω hπ p hp hρ h1 hZ).2,
      fun C hC hbud => cesIndex_le Ω hπ p hp hρ h1 hZ C hC hbud⟩⟩
    have := hπ s; have := hp s
    unfold cesDemand
    positivity

/-! ## Isoelastic period utility (O&R (26), p. 283) -/

/-- Isoelastic period utility with intertemporal substitution elasticity `σ > 0`, O&R (26),
p. 283: `u(C) = C^{1−1/σ}/(1 − 1/σ)`, with its log limit `u(C) = log C` at `σ = 1` (footnote
13, p. 284). -/
noncomputable def isoU (σ c : ℝ) : ℝ :=
  if σ = 1 then Real.log c else c ^ (1 - 1 / σ) / (1 - 1 / σ)

/-- The marginal utility of isoelastic utility, O&R p. 284: `u′(C) = C^{−1/σ}` for `σ, C > 0`
(including `σ = 1`, where `u′(C) = 1/C`). -/
theorem isoU_hasDerivAt {σ x : ℝ} (hσ : 0 < σ) (hx : 0 < x) :
    HasDerivAt (isoU σ) (x ^ (-1 / σ)) x := by
  by_cases h1 : σ = 1
  · have hf : isoU σ = Real.log := funext fun c => by simp [isoU, h1]
    rw [hf, h1, div_one, Real.rpow_neg_one]
    exact Real.hasDerivAt_log hx.ne'
  · have ha : 1 - 1 / σ ≠ 0 := by
      intro h
      have : 1 / σ = 1 := by linarith
      exact h1 (by rw [one_div, inv_eq_one] at this; exact this)
    have hf : isoU σ = fun c => c ^ (1 - 1 / σ) / (1 - 1 / σ) :=
      funext fun c => by simp [isoU, h1]
    rw [hf]
    refine ((Real.hasDerivAt_rpow_const (p := 1 - 1 / σ) (Or.inl hx.ne')).div_const
      (1 - 1 / σ)).congr_deriv ?_
    rw [show 1 - 1 / σ - 1 = -1 / σ by ring]
    field_simp

/-- The tangent-line inequality for isoelastic utility (concavity), O&R §5.1.8: for `σ > 0`
and `x, y > 0`, `u(x) ≤ u(y) + y^{−1/σ}(x − y)`, strictly if `x ≠ y`. -/
theorem isoU_tangent {σ x y : ℝ} (hσ : 0 < σ) (hx : 0 < x) (hy : 0 < y) :
    isoU σ x ≤ isoU σ y + y ^ (-1 / σ) * (x - y) ∧
      (x ≠ y → isoU σ x < isoU σ y + y ^ (-1 / σ) * (x - y)) := by
  by_cases h1 : σ = 1
  · have e : y ^ (-1 / σ) * (x - y) = (x - y) / y := by
      rw [h1, div_one, Real.rpow_neg_one]; field_simp
    simp only [isoU, h1, ite_true]
    rw [h1] at e
    rw [e]
    exact log_le_tangent hx hy
  · simp only [isoU, h1, ite_false]
    set a := 1 - 1 / σ with ha
    have ha1 : -1 / σ = a - 1 := by rw [ha]; ring
    rw [ha1]
    have key : x ^ a / a - (y ^ a / a + y ^ (a - 1) * (x - y)) =
        (x ^ a - (y ^ a + a * y ^ (a - 1) * (x - y))) / a := by
      have ha0 : a ≠ 0 := by
        intro h
        have : 1 / σ = 1 := by rw [ha] at h; linarith
        exact h1 (by rw [one_div, inv_eq_one] at this; exact this)
      field_simp
    rcases lt_or_gt_of_ne h1 with hlt | hgt
    · -- σ < 1: `a < 0`.
      have ha0 : a < 0 := by
        rw [ha, sub_neg, lt_div_iff₀ hσ]; linarith
      have h := tangent_le_rpow_of_neg ha0 hx hy
      refine ⟨?_, fun hxy => ?_⟩
      · have := div_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr h.1) ha0.le
        linarith
      · have := div_neg_of_pos_of_neg (sub_pos.mpr (h.2 hxy)) ha0
        linarith
    · -- σ > 1: `0 < a < 1`.
      have ha0 : 0 < a := by
        rw [ha, sub_pos, div_lt_one hσ]; exact hgt
      have ha1' : a < 1 := by
        rw [ha]; have : 0 < 1 / σ := by positivity
        linarith
      have h := rpow_le_tangent ha0 ha1' hx hy
      refine ⟨?_, fun hxy => ?_⟩
      · have := div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr h.1) ha0.le
        linarith
      · have := div_neg_of_neg_of_pos (sub_neg.mpr (h.2 hxy)) ha0
        linarith

/-- Isoelastic utility is strictly increasing on `(0, ∞)`, O&R (26): for `σ > 0` and
`0 < x < y`, `u(x) < u(y)`. -/
theorem isoU_lt_of_lt {σ x y : ℝ} (hσ : 0 < σ) (hx : 0 < x) (hxy : x < y) :
    isoU σ x < isoU σ y := by
  have hy : 0 < y := hx.trans hxy
  have h := (isoU_tangent hσ hx hy).2 hxy.ne
  have : y ^ (-1 / σ) * (x - y) < 0 :=
    mul_neg_of_pos_of_neg (Real.rpow_pos_of_pos hy _) (by linarith)
  linarith

/-- Isoelastic utility is monotone on `(0, ∞)`, O&R (26): for `σ > 0` and `0 < x ≤ y`,
`u(x) ≤ u(y)`. -/
theorem isoU_le_of_le {σ x y : ℝ} (hσ : 0 < σ) (hx : 0 < x) (hxy : x ≤ y) :
    isoU σ x ≤ isoU σ y := by
  rcases hxy.lt_or_eq with h | h
  · exact (isoU_lt_of_lt hσ hx h).le
  · rw [h]

/-! ## Stage 1: the optimal division of spending across dates (O&R (21), (22), (27)) -/

/-- The stage-1 objective (21), O&R p. 282, with isoelastic `u`: `u(C₁) + βu(Z₂/P)`. -/
noncomputable def stageOneObjective (σ β P C1 Z2 : ℝ) : ℝ :=
  isoU σ C1 + β * isoU σ (Z2 / P)

/-- The stage-1 consumption function, O&R p. 284:
`C₁ = W₁/(1 + ((1+r)/P)^{σ−1}β^σ)`. -/
noncomputable def stageOneC1 (σ r β P W1 : ℝ) : ℝ :=
  W1 / (1 + ((1 + r) / P) ^ (σ - 1) * β ^ σ)

/-- Stage-1 date-2 spending, O&R (22), p. 282: `Z₂ = (1+r)(W₁ − C₁)` at the stage-1
consumption function. -/
noncomputable def stageOneZ2 (σ r β P W1 : ℝ) : ℝ :=
  (1 + r) * (W1 - stageOneC1 σ r β P W1)

/-- The stage-1 solution satisfies (27), O&R p. 284:
`Z₂ = (1+r)^σ β^σ (1/P)^{σ−1} C₁` (for `1 + r, β, P > 0`). -/
theorem stageOneZ2_eq_27 {σ r β P W1 : ℝ} (hr : 0 < 1 + r) (hβ : 0 < β) (hP : 0 < P) :
    stageOneZ2 σ r β P W1 =
      (1 + r) ^ σ * β ^ σ * (1 / P) ^ (σ - 1) * stageOneC1 σ r β P W1 := by
  have hK : (1 + r) * (((1 + r) / P) ^ (σ - 1) * β ^ σ) =
      (1 + r) ^ σ * β ^ σ * (1 / P) ^ (σ - 1) := by
    rw [Real.div_rpow hr.le hP.le, Real.div_rpow zero_le_one hP.le, Real.one_rpow,
      Real.rpow_sub_one hr.ne']
    have : 0 < P ^ (σ - 1) := Real.rpow_pos_of_pos hP _
    field_simp
  have hKpos : 0 < ((1 + r) / P) ^ (σ - 1) * β ^ σ := by positivity
  rw [← hK, stageOneZ2, stageOneC1]
  field_simp
  ring

/-- The stage-1 solution is feasible, O&R (22), p. 282: for `W₁ > 0` (and `1 + r, β, P > 0`),
`C₁ > 0`, `Z₂ > 0` and `C₁ + Z₂/(1+r) = W₁`. -/
theorem stageOne_feasible {σ r β P W1 : ℝ} (hr : 0 < 1 + r) (hβ : 0 < β) (hP : 0 < P)
    (hW : 0 < W1) :
    0 < stageOneC1 σ r β P W1 ∧ 0 < stageOneZ2 σ r β P W1 ∧
      stageOneC1 σ r β P W1 + stageOneZ2 σ r β P W1 / (1 + r) = W1 := by
  have hC : 0 < stageOneC1 σ r β P W1 := by unfold stageOneC1; positivity
  refine ⟨hC, ?_, by rw [stageOneZ2]; field_simp; ring⟩
  rw [stageOneZ2_eq_27 hr hβ hP]
  positivity

/-- The stage-1 solution satisfies the bond Euler equation, O&R p. 284:
`u′(C₁) = (1+r)β(1/P)u′(Z₂/P)` with `u′(C) = C^{−1/σ}` (see `isoU_hasDerivAt`). -/
theorem stageOne_euler {σ r β P W1 : ℝ} (hσ : 0 < σ) (hr : 0 < 1 + r) (hβ : 0 < β)
    (hP : 0 < P) (hW : 0 < W1) :
    stageOneC1 σ r β P W1 ^ (-1 / σ) =
      (1 + r) * β * P⁻¹ * (stageOneZ2 σ r β P W1 / P) ^ (-1 / σ) := by
  obtain ⟨hC, hZ, -⟩ := stageOne_feasible (σ := σ) hr hβ hP hW
  exact (euler_27 hσ hr hβ hC hZ hP).mpr (stageOneZ2_eq_27 hr hβ hP)

/-- Stage-1 optimality (sufficiency, by concavity), O&R pp. 283–284: for `σ, β, P, W₁ > 0` and
`1 + r > 0`, the stage-1 solution maximises the objective (21) over all `C₁, Z₂ > 0` with
`C₁ + Z₂/(1+r) = W₁` (O&R (22)), strictly at every other feasible point. -/
theorem stageOne_optimal {σ r β P W1 : ℝ} (hσ : 0 < σ) (hr : 0 < 1 + r) (hβ : 0 < β)
    (hP : 0 < P) (hW : 0 < W1) {C1 Z2 : ℝ} (hC1 : 0 < C1) (hZ2 : 0 < Z2)
    (hbud : C1 + Z2 / (1 + r) = W1) :
    stageOneObjective σ β P C1 Z2 ≤
        stageOneObjective σ β P (stageOneC1 σ r β P W1) (stageOneZ2 σ r β P W1) ∧
      (C1 ≠ stageOneC1 σ r β P W1 → stageOneObjective σ β P C1 Z2 <
        stageOneObjective σ β P (stageOneC1 σ r β P W1) (stageOneZ2 σ r β P W1)) := by
  obtain ⟨hc, hz, hb⟩ := stageOne_feasible (σ := σ) hr hβ hP hW
  have heul := stageOne_euler hσ hr hβ hP hW
  set c := stageOneC1 σ r β P W1
  set z := stageOneZ2 σ r β P W1
  set e := c ^ (-1 / σ) with he
  set m := (z / P) ^ (-1 / σ) with hm
  have t1 := isoU_tangent hσ hC1 hc
  have t2 := (isoU_tangent hσ (div_pos hZ2 hP) (div_pos hz hP)).1
  rw [← he] at t1
  rw [← hm] at t2
  have hlin : β * (m * (Z2 / P - z / P)) = e * ((Z2 - z) / (1 + r)) := by
    rw [heul]; field_simp
  have hzero : e * (C1 - c) + e * ((Z2 - z) / (1 + r)) = 0 := by
    rw [← mul_add, show C1 - c + (Z2 - z) / (1 + r) = 0 by rw [sub_div]; linarith, mul_zero]
  have t2' := mul_le_mul_of_nonneg_left t2 hβ.le
  simp only [stageOneObjective]
  refine ⟨by nlinarith [t1.1], fun hne => by nlinarith [t1.2 hne]⟩

/-- Stage-1 uniqueness and necessity, O&R p. 284: any feasible `(C₁, Z₂)` (positive, with
`C₁ + Z₂/(1+r) = W₁`) doing at least as well as the stage-1 solution in (21) is the stage-1
solution. -/
theorem stageOne_unique {σ r β P W1 : ℝ} (hσ : 0 < σ) (hr : 0 < 1 + r) (hβ : 0 < β)
    (hP : 0 < P) (hW : 0 < W1) {C1 Z2 : ℝ} (hC1 : 0 < C1) (hZ2 : 0 < Z2)
    (hbud : C1 + Z2 / (1 + r) = W1)
    (hge : stageOneObjective σ β P (stageOneC1 σ r β P W1) (stageOneZ2 σ r β P W1) ≤
      stageOneObjective σ β P C1 Z2) :
    C1 = stageOneC1 σ r β P W1 ∧ Z2 = stageOneZ2 σ r β P W1 := by
  have hC : C1 = stageOneC1 σ r β P W1 := by
    by_contra hne
    exact absurd hge (not_le.mpr ((stageOne_optimal hσ hr hβ hP hW hC1 hZ2 hbud).2 hne))
  refine ⟨hC, ?_⟩
  obtain ⟨-, -, hb⟩ := stageOne_feasible (σ := σ) hr hβ hP hW
  rw [← hC] at hb
  have : Z2 / (1 + r) = stageOneZ2 σ r β P W1 / (1 + r) := by linarith
  field_simp at this
  exact this

/-- The stage-1 problem is solved exactly by the stage-1 solution, O&R pp. 283–284: a feasible
`(C₁, Z₂)` maximises (21) over the feasible set iff it equals
`(W₁/(1 + ((1+r)/P)^{σ−1}β^σ), (1+r)(W₁ − C₁))`. -/
theorem stageOne_maximiser_iff {σ r β P W1 : ℝ} (hσ : 0 < σ) (hr : 0 < 1 + r) (hβ : 0 < β)
    (hP : 0 < P) (hW : 0 < W1) {C1 Z2 : ℝ} (hC1 : 0 < C1) (hZ2 : 0 < Z2)
    (hbud : C1 + Z2 / (1 + r) = W1) :
    (∀ C1' Z2' : ℝ, 0 < C1' → 0 < Z2' → C1' + Z2' / (1 + r) = W1 →
      stageOneObjective σ β P C1' Z2' ≤ stageOneObjective σ β P C1 Z2) ↔
      C1 = stageOneC1 σ r β P W1 ∧ Z2 = stageOneZ2 σ r β P W1 := by
  obtain ⟨hc, hz, hb⟩ := stageOne_feasible (σ := σ) hr hβ hP hW
  constructor
  · intro hmax
    exact stageOne_unique hσ hr hβ hP hW hC1 hZ2 hbud (hmax _ _ hc hz hb)
  · rintro ⟨rfl, rfl⟩ C1' Z2' h1 h2 hb'
    exact (stageOne_optimal hσ hr hβ hP hW h1 h2 hb').1

/-- The stage-1 optimum is characterised by (27), O&R p. 284 (necessity and sufficiency): a
feasible `(C₁, Z₂)` maximises (21) subject to (22) iff `Z₂ = (1+r)^σβ^σ(1/P)^{σ−1}C₁`. -/
theorem stageOne_maximiser_iff_27 {σ r β P W1 : ℝ} (hσ : 0 < σ) (hr : 0 < 1 + r)
    (hβ : 0 < β) (hP : 0 < P) (hW : 0 < W1) {C1 Z2 : ℝ} (hC1 : 0 < C1) (hZ2 : 0 < Z2)
    (hbud : C1 + Z2 / (1 + r) = W1) :
    (∀ C1' Z2' : ℝ, 0 < C1' → 0 < Z2' → C1' + Z2' / (1 + r) = W1 →
      stageOneObjective σ β P C1' Z2' ≤ stageOneObjective σ β P C1 Z2) ↔
      Z2 = (1 + r) ^ σ * β ^ σ * (1 / P) ^ (σ - 1) * C1 := by
  rw [stageOne_maximiser_iff hσ hr hβ hP hW hC1 hZ2 hbud]
  constructor
  · rintro ⟨rfl, rfl⟩
    exact stageOneZ2_eq_27 hr hβ hP
  · intro h27
    have hC : C1 = stageOneC1 σ r β P W1 := consumption_27 hr hβ hP h27 hbud
    refine ⟨hC, ?_⟩
    rw [stageOneZ2, ← hC, ← hbud]
    field_simp
    ring

/-- The stage-1 optimum is characterised by the bond Euler equation, O&R p. 284: a feasible
`(C₁, Z₂)` maximises (21) subject to (22) iff `u′(C₁) = (1+r)β(1/P)u′(Z₂/P)` with
`u′(C) = C^{−1/σ}`. -/
theorem stageOne_maximiser_iff_euler {σ r β P W1 : ℝ} (hσ : 0 < σ) (hr : 0 < 1 + r)
    (hβ : 0 < β) (hP : 0 < P) (hW : 0 < W1) {C1 Z2 : ℝ} (hC1 : 0 < C1) (hZ2 : 0 < Z2)
    (hbud : C1 + Z2 / (1 + r) = W1) :
    (∀ C1' Z2' : ℝ, 0 < C1' → 0 < Z2' → C1' + Z2' / (1 + r) = W1 →
      stageOneObjective σ β P C1' Z2' ≤ stageOneObjective σ β P C1 Z2) ↔
      C1 ^ (-1 / σ) = (1 + r) * β * P⁻¹ * (Z2 / P) ^ (-1 / σ) := by
  rw [stageOne_maximiser_iff_27 hσ hr hβ hP hW hC1 hZ2 hbud, euler_27 hσ hr hβ hC1 hZ2 hP]

/-! ## Two-stage budgeting solves the original problem (O&R (20)–(22)) -/

/-- Two-stage budgeting solves (20), O&R pp. 282–284, for any consumption index `Ω` with the
stage-2 properties (positive on positive bundles; demands `D(Z₂)` positive, costing `Z₂` and
attaining `Z₂/P`; every positive bundle costing at most `Z₂` has index at most `Z₂/P`,
strictly unless it is `D(Z₂)`). With isoelastic `u` (`σ > 0`), `β, W₁ > 0`, `1 + r > 0`,
`p > 0` and at least one state: the plan `C₁* = W₁/(1 + ((1+r)/P)^{σ−1}β^σ)`,
`C₂* = D(Z₂*)`, `Z₂* = (1+r)(W₁ − C₁*)` is feasible for (22) with `Z₂ = Σ p(s)C₂(s)`; it
maximises `u(C₁) + βu(Ω(C₂))` over ALL positive state-contingent plans on the budget line;
and it is the unique maximiser (any feasible plan doing at least as well equals it). -/
theorem two_stage_optimal_of_index (p : S → ℝ) (hp : ∀ s, 0 < p s)
    (hne : (Finset.univ : Finset S).Nonempty) {I : (S → ℝ) → ℝ} {Dm : ℝ → S → ℝ} {P : ℝ}
    (hP : 0 < P) (hIpos : ∀ C : S → ℝ, (∀ s, 0 < C s) → 0 < I C)
    (hDpos : ∀ Z, 0 < Z → ∀ s, 0 < Dm Z s) (hcost : ∀ Z, 0 < Z → ∑ s, p s * Dm Z s = Z)
    (hval : ∀ Z, 0 < Z → I (Dm Z) = Z / P)
    (hle : ∀ Z, 0 < Z → ∀ C : S → ℝ, (∀ s, 0 < C s) → ∑ s, p s * C s ≤ Z →
      I C ≤ Z / P ∧ ((∃ s, C s ≠ Dm Z s) → I C < Z / P))
    {σ r β W1 : ℝ} (hσ : 0 < σ) (hr : 0 < 1 + r) (hβ : 0 < β) (hW : 0 < W1) :
    (0 < stageOneC1 σ r β P W1 ∧ (∀ s, 0 < Dm (stageOneZ2 σ r β P W1) s) ∧
      stageOneC1 σ r β P W1 + (∑ s, p s * Dm (stageOneZ2 σ r β P W1) s) / (1 + r) = W1) ∧
    (∀ (C1 : ℝ) (C2 : S → ℝ), 0 < C1 → (∀ s, 0 < C2 s) →
      C1 + (∑ s, p s * C2 s) / (1 + r) = W1 →
      isoU σ C1 + β * isoU σ (I C2) ≤ isoU σ (stageOneC1 σ r β P W1) +
        β * isoU σ (I (Dm (stageOneZ2 σ r β P W1)))) ∧
    (∀ (C1 : ℝ) (C2 : S → ℝ), 0 < C1 → (∀ s, 0 < C2 s) →
      C1 + (∑ s, p s * C2 s) / (1 + r) = W1 →
      isoU σ (stageOneC1 σ r β P W1) + β * isoU σ (I (Dm (stageOneZ2 σ r β P W1))) ≤
        isoU σ C1 + β * isoU σ (I C2) →
      C1 = stageOneC1 σ r β P W1 ∧ C2 = Dm (stageOneZ2 σ r β P W1)) := by
  obtain ⟨hc, hz, hb⟩ := stageOne_feasible (σ := σ) hr hβ hP hW
  set c := stageOneC1 σ r β P W1 with hcdef
  set z := stageOneZ2 σ r β P W1 with hzdef
  have hUstar : isoU σ c + β * isoU σ (I (Dm z)) = stageOneObjective σ β P c z := by
    rw [stageOneObjective, hval z hz]
  -- every feasible plan is bounded by its stage-1 value
  have hbound : ∀ (C1 : ℝ) (C2 : S → ℝ), (∀ s, 0 < C2 s) →
      isoU σ C1 + β * isoU σ (I C2) ≤ stageOneObjective σ β P C1 (∑ s, p s * C2 s) ∧
      ((∃ s, C2 s ≠ Dm (∑ s, p s * C2 s) s) →
        isoU σ C1 + β * isoU σ (I C2) < stageOneObjective σ β P C1 (∑ s, p s * C2 s)) := by
    intro C1 C2 hC2
    have hZ : 0 < ∑ s, p s * C2 s := Finset.sum_pos (fun s _ => mul_pos (hp s) (hC2 s)) hne
    have h := hle _ hZ C2 hC2 le_rfl
    simp only [stageOneObjective]
    refine ⟨?_, fun hex => ?_⟩
    · have := isoU_le_of_le hσ (hIpos C2 hC2) h.1
      nlinarith
    · have := isoU_lt_of_lt hσ (hIpos C2 hC2) (h.2 hex)
      nlinarith
  refine ⟨⟨hc, hDpos z hz, by rw [hcost z hz]; exact hb⟩, fun C1 C2 hC1 hC2 hbud => ?_,
    fun C1 C2 hC1 hC2 hbud hge => ?_⟩
  · have hZ : 0 < ∑ s, p s * C2 s := Finset.sum_pos (fun s _ => mul_pos (hp s) (hC2 s)) hne
    rw [hUstar]
    exact (hbound C1 C2 hC2).1.trans (stageOne_optimal hσ hr hβ hP hW hC1 hZ hbud).1
  · have hZ : 0 < ∑ s, p s * C2 s := Finset.sum_pos (fun s _ => mul_pos (hp s) (hC2 s)) hne
    rw [hUstar] at hge
    have h1 := (hbound C1 C2 hC2).1
    obtain ⟨hC, hZeq⟩ := stageOne_unique hσ hr hβ hP hW hC1 hZ hbud (hge.trans h1)
    refine ⟨hC, funext fun s => ?_⟩
    by_contra hne'
    have h2 := (hbound C1 C2 hC2).2 ⟨s, by rw [hZeq]; exact hne'⟩
    rw [hC, ← hcdef] at hge
    rw [hC, hZeq, ← hcdef, ← hzdef] at h2
    linarith

/-! ## The Epstein–Zin / Kreps–Porteus preferences (26) (O&R p. 283, footnote 13) -/

/-- The preferences (26), O&R p. 283: `U₁ = u(C₁) + βu(Ω(C₂))` with isoelastic
`u(C) = C^{1−1/σ}/(1 − 1/σ)` (intertemporal elasticity `σ > 0`, log at `σ = 1`) and the CES
certainty equivalent (23) with relative risk aversion `ρ > 0` (geometric mean at `ρ = 1`);
footnote 13 cites Epstein and Zin (1989) and Weil (1989b, 1990), and handles `ρ = 1` and
`σ = 1` by L'Hospital's rule, as here. -/
noncomputable def ezUtility (Ω : StateSpace S) (ρ σ β C1 : ℝ) (C2 : S → ℝ) : ℝ :=
  isoU σ C1 + β * isoU σ (riskIndex Ω ρ C2)

/-- The preferences (26) exactly as printed, O&R p. 283: for `σ ≠ 1`, `ρ ≠ 1`,
`U₁ = C₁^{1−1/σ}/(1 − 1/σ) + β{[Σ π(s)C₂(s)^{1−ρ}]^{1/(1−ρ)}}^{1−1/σ}/(1 − 1/σ)`. -/
theorem ezUtility_eq_printed (Ω : StateSpace S) {ρ σ : ℝ} (hρ : ρ ≠ 1) (hσ : σ ≠ 1)
    (β C1 : ℝ) (C2 : S → ℝ) :
    ezUtility Ω ρ σ β C1 C2 = C1 ^ (1 - 1 / σ) / (1 - 1 / σ) +
      β * (((∑ s, Ω.prob s * C2 s ^ (1 - ρ)) ^ (1 / (1 - ρ))) ^ (1 - 1 / σ) /
        (1 - 1 / σ)) := by
  simp only [ezUtility, isoU, riskIndex, cesIndex, hρ, hσ, ite_false]

/-- The two-stage solution of (26), O&R pp. 283–284: for `ρ, σ > 0`, `π, p > 0`, `β, W₁ > 0`
and `1 + r > 0`, with `P` the price index (25) (at risk aversion `ρ`), stage 2 is identical to
the expected-utility case (demands (24)) and stage 1 uses the intertemporal elasticity `σ`:
the plan `C₁* = W₁/(1 + ((1+r)/P)^{σ−1}β^σ)`, `C₂* = (24)` at `Z₂* = (1+r)(W₁ − C₁*)` is
feasible, maximises (26) over all positive plans with `C₁ + Σ p(s)C₂(s)/(1+r) = W₁`, and is
the unique maximiser. -/
theorem ez_two_stage_optimal (Ω : StateSpace S) (hπ : ∀ s, 0 < Ω.prob s) (p : S → ℝ)
    (hp : ∀ s, 0 < p s) {ρ σ r β W1 : ℝ} (hρ : 0 < ρ) (hσ : 0 < σ) (hr : 0 < 1 + r)
    (hβ : 0 < β) (hW : 0 < W1) :
    let P := riskPrice Ω ρ p
    let C1s := stageOneC1 σ r β P W1
    let C2s := riskDemand Ω ρ p (stageOneZ2 σ r β P W1)
    (0 < C1s ∧ (∀ s, 0 < C2s s) ∧ C1s + (∑ s, p s * C2s s) / (1 + r) = W1) ∧
    (∀ (C1 : ℝ) (C2 : S → ℝ), 0 < C1 → (∀ s, 0 < C2 s) →
      C1 + (∑ s, p s * C2 s) / (1 + r) = W1 →
      ezUtility Ω ρ σ β C1 C2 ≤ ezUtility Ω ρ σ β C1s C2s) ∧
    (∀ (C1 : ℝ) (C2 : S → ℝ), 0 < C1 → (∀ s, 0 < C2 s) →
      C1 + (∑ s, p s * C2 s) / (1 + r) = W1 →
      ezUtility Ω ρ σ β C1s C2s ≤ ezUtility Ω ρ σ β C1 C2 → C1 = C1s ∧ C2 = C2s) := by
  obtain ⟨hP, hIpos, h2⟩ := risk_stage_two Ω hπ p hp hρ
  exact two_stage_optimal_of_index p hp (univ_nonempty_of_stateSpace Ω) hP hIpos
    (fun Z hZ => (h2 Z hZ).1) (fun Z hZ => (h2 Z hZ).2.1) (fun Z hZ => (h2 Z hZ).2.2.1)
    (fun Z hZ => (h2 Z hZ).2.2.2) hσ hr hβ hW

/-- CRRA period utility with relative risk aversion `ρ > 0`, O&R (13), p. 278, and p. 284:
`u(C) = C^{1−ρ}/(1 − ρ)`, with `u(C) = log C` at `ρ = 1`. -/
noncomputable def crraU (ρ c : ℝ) : ℝ :=
  if ρ = 1 then Real.log c else c ^ (1 - ρ) / (1 - ρ)

/-- Expected lifetime utility, O&R p. 284 (the special case of (20)/(21) the book compares with
(26)): `U₁ = C₁^{1−ρ}/(1−ρ) + β Σ π(s)C₂(s)^{1−ρ}/(1−ρ)` (log at `ρ = 1`). -/
noncomputable def expectedUtility (Ω : StateSpace S) (ρ β C1 : ℝ) (C2 : S → ℝ) : ℝ :=
  crraU ρ C1 + β * ∑ s, Ω.prob s * crraU ρ (C2 s)

/-- Isoelastic utility with `σ = 1/ρ` is CRRA utility with coefficient `ρ`, O&R p. 284:
`C^{1−1/σ}/(1 − 1/σ) = C^{1−ρ}/(1 − ρ)` (and both are `log C` when `ρ = σ = 1`). -/
theorem isoU_inv_eq_crraU (ρ : ℝ) : isoU (1 / ρ) = crraU ρ := by
  funext c
  have hiff : 1 / ρ = 1 ↔ ρ = 1 := by
    rw [one_div, inv_eq_one]
  by_cases h1 : ρ = 1
  · simp [isoU, crraU, h1]
  · have h1' : ¬ (1 / ρ = 1) := fun h => h1 (hiff.mp h)
    simp only [isoU, crraU, h1, h1', ite_false, one_div_one_div]

/-- The reduction of (26) to expected utility, O&R p. 284: when `σ = 1/ρ`, (26)
coincides with expected utility, `U₁ = C₁^{1−ρ}/(1−ρ) + β Σ π(s)C₂(s)^{1−ρ}/(1−ρ)`, for every
plan with `C₂ ≥ 0` (the transform relating them is the identity, a strictly increasing
function; the book's `ρ > 0` is not needed for the identity). -/
theorem ez_eq_expectedUtility (Ω : StateSpace S) (ρ β C1 : ℝ)
    {C2 : S → ℝ} (hC2 : ∀ s, 0 ≤ C2 s) :
    ezUtility Ω ρ (1 / ρ) β C1 C2 = expectedUtility Ω ρ β C1 C2 := by
  rw [ezUtility, expectedUtility, isoU_inv_eq_crraU ρ]
  congr 2
  by_cases h1 : ρ = 1
  · simp only [crraU, riskIndex, geoIndex, h1, ite_true, Real.log_exp]
  · have h1ρ : 1 - ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
    have hX : 0 ≤ ∑ s, Ω.prob s * C2 s ^ (1 - ρ) :=
      Finset.sum_nonneg fun s _ =>
        mul_nonneg (Ω.prob_nonneg s) (Real.rpow_nonneg (hC2 s) _)
    simp only [crraU, riskIndex, cesIndex, h1, ite_false]
    rw [one_div, Real.rpow_inv_rpow hX h1ρ, Finset.sum_div]
    exact Finset.sum_congr rfl fun s _ => by ring

/-- (26) with `σ = 1/ρ` represents the expected-utility ordering, O&R p. 284: for all plans
with nonnegative date-2 consumption, `U^{EZ}(C) ≤ U^{EZ}(C′)` iff
`U^{EU}(C) ≤ U^{EU}(C′)`. -/
theorem ez_le_iff_expectedUtility (Ω : StateSpace S) (ρ β C1 C1' : ℝ)
    {C2 C2' : S → ℝ} (hC2 : ∀ s, 0 ≤ C2 s) (hC2' : ∀ s, 0 ≤ C2' s) :
    ezUtility Ω ρ (1 / ρ) β C1 C2 ≤ ezUtility Ω ρ (1 / ρ) β C1' C2' ↔
      expectedUtility Ω ρ β C1 C2 ≤ expectedUtility Ω ρ β C1' C2' := by
  rw [ez_eq_expectedUtility Ω ρ β C1 hC2, ez_eq_expectedUtility Ω ρ β C1' hC2']

/-- The expected-utility optimum is the two-stage optimum with `σ = 1/ρ`, O&R p. 284: for
`ρ > 0`, `π, p > 0`, `β, W₁ > 0`, `1 + r > 0`, the plan
`C₁* = W₁/(1 + ((1+r)/P)^{1/ρ−1}β^{1/ρ})`, `C₂* = (24)` at `Z₂* = (1+r)(W₁ − C₁*)` maximises
expected utility over all positive plans with `C₁ + Σ p(s)C₂(s)/(1+r) = W₁`, and is the unique
maximiser. -/
theorem expectedUtility_two_stage_optimal (Ω : StateSpace S) (hπ : ∀ s, 0 < Ω.prob s)
    (p : S → ℝ) (hp : ∀ s, 0 < p s) {ρ r β W1 : ℝ} (hρ : 0 < ρ) (hr : 0 < 1 + r)
    (hβ : 0 < β) (hW : 0 < W1) :
    let P := riskPrice Ω ρ p
    let C1s := stageOneC1 (1 / ρ) r β P W1
    let C2s := riskDemand Ω ρ p (stageOneZ2 (1 / ρ) r β P W1)
    (0 < C1s ∧ (∀ s, 0 < C2s s) ∧ C1s + (∑ s, p s * C2s s) / (1 + r) = W1) ∧
    (∀ (C1 : ℝ) (C2 : S → ℝ), 0 < C1 → (∀ s, 0 < C2 s) →
      C1 + (∑ s, p s * C2 s) / (1 + r) = W1 →
      expectedUtility Ω ρ β C1 C2 ≤ expectedUtility Ω ρ β C1s C2s) ∧
    (∀ (C1 : ℝ) (C2 : S → ℝ), 0 < C1 → (∀ s, 0 < C2 s) →
      C1 + (∑ s, p s * C2 s) / (1 + r) = W1 →
      expectedUtility Ω ρ β C1s C2s ≤ expectedUtility Ω ρ β C1 C2 → C1 = C1s ∧ C2 = C2s) := by
  intro P C1s C2s
  obtain ⟨hfeas, hopt, huniq⟩ :=
    ez_two_stage_optimal Ω hπ p hp (σ := 1 / ρ) (r := r) (β := β) (W1 := W1) hρ
      (by positivity) hr hβ hW
  have hs : ∀ s, 0 ≤ C2s s := fun s => (hfeas.2.1 s).le
  refine ⟨hfeas, fun C1 C2 hC1 hC2 hbud => ?_, fun C1 C2 hC1 hC2 hbud hge => ?_⟩
  · have := hopt C1 C2 hC1 hC2 hbud
    rwa [ez_le_iff_expectedUtility Ω ρ β C1 _ (fun s => (hC2 s).le) hs] at this
  · refine huniq C1 C2 hC1 hC2 hbud ?_
    rwa [ez_le_iff_expectedUtility Ω ρ β _ C1 hs (fun s => (hC2 s).le)]

/-- "Only when `σ = 1/ρ`", O&R p. 284: for `ρ, σ, β > 0` and `π, p > 0`, the preferences (26)
rank all positive plans exactly as expected utility (with risk aversion `ρ`) does iff
`σ = 1/ρ`. The converse direction compares the unique optima at `W₁ = 1` and
`1 + r = P` and `1 + r = 2P`: equal date-1 consumption at both rates forces
`2^{σ−1} = 2^{1/ρ−1}`. -/
theorem ez_same_ordering_iff (Ω : StateSpace S) (hπ : ∀ s, 0 < Ω.prob s) (p : S → ℝ)
    (hp : ∀ s, 0 < p s) {ρ σ β : ℝ} (hρ : 0 < ρ) (hσ : 0 < σ) (hβ : 0 < β) :
    (∀ (C1 C1' : ℝ) (C2 C2' : S → ℝ), 0 < C1 → 0 < C1' → (∀ s, 0 < C2 s) →
      (∀ s, 0 < C2' s) →
      (ezUtility Ω ρ σ β C1 C2 ≤ ezUtility Ω ρ σ β C1' C2' ↔
        expectedUtility Ω ρ β C1 C2 ≤ expectedUtility Ω ρ β C1' C2')) ↔ σ = 1 / ρ := by
  constructor
  · intro hord
    obtain ⟨hP, -, -⟩ := risk_stage_two Ω hπ p hp hρ
    set P := riskPrice Ω ρ p with hPdef
    have key : ∀ R : ℝ, 0 < R →
        (R / P) ^ (σ - 1) * β ^ σ = (R / P) ^ (1 / ρ - 1) * β ^ (1 / ρ) := by
      intro R hR
      have hr : 0 < 1 + (R - 1) := by linarith
      obtain ⟨hf1, -, hu1⟩ := ez_two_stage_optimal Ω hπ p hp (σ := σ) (r := R - 1) (β := β)
        (W1 := 1) hρ hσ hr hβ one_pos
      obtain ⟨hf2, ho2, -⟩ := expectedUtility_two_stage_optimal Ω hπ p hp (r := R - 1)
        (β := β) (W1 := 1) hρ hr hβ one_pos
      have h1 := ho2 _ _ hf1.1 hf1.2.1 hf1.2.2
      have h2 := (hord _ _ _ _ hf1.1 hf2.1 hf1.2.1 hf2.2.1).mpr h1
      have h3 := (hu1 _ _ hf2.1 hf2.2.1 hf2.2.2 h2).1
      simp only [stageOneC1, show 1 + (R - 1) = R by ring, ← hPdef] at h3
      have hA : 0 < (R / P) ^ (σ - 1) * β ^ σ := by positivity
      have hB : 0 < (R / P) ^ (1 / ρ - 1) * β ^ (1 / ρ) := by positivity
      rw [div_eq_div_iff (by positivity) (by positivity)] at h3
      linarith
    have k1 := key P hP
    have k2 := key (2 * P) (by positivity)
    rw [div_self hP.ne', Real.one_rpow, Real.one_rpow, one_mul, one_mul] at k1
    rw [mul_div_assoc, div_self hP.ne', mul_one, k1] at k2
    have hb : 0 < β ^ (1 / ρ) := by positivity
    have k3 : (2 : ℝ) ^ (σ - 1) = 2 ^ (1 / ρ - 1) := mul_right_cancel₀ hb.ne' k2
    have k4 := congrArg Real.log k3
    rw [Real.log_rpow two_pos, Real.log_rpow two_pos] at k4
    have hl : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
    have := mul_right_cancel₀ hl k4
    linarith
  · intro h
    subst h
    intro C1 C1' C2 C2' _ _ hC2 hC2'
    exact ez_le_iff_expectedUtility Ω ρ β C1 C1' (fun s => (hC2 s).le) (fun s => (hC2' s).le)

/-! ## The current account under (26) (O&R p. 285, footnote 14) -/

/-- The current account at the optimum of (26), O&R footnote 14, p. 285: with
`W₁ = Y₁ + V/(1+r)`, `V = Σ p(s)Y₂(s) > 0`, the optimal `C₁` (stage 1 with elasticity `σ`) gives
`CA₁ = Y₁ − C₁ > 0` iff `r > r^CA`, `< 0` iff `r < r^CA`, `= 0` iff `r = r^CA`, where
`1 + r^CA = (1/β)[V/(P^{1−σ}Y₁)]^{1/σ}`. -/
theorem ez_current_account_sign {σ r β P Y1 V : ℝ} (hσ : 0 < σ) (hr : 0 < 1 + r)
    (hβ : 0 < β) (hP : 0 < P) (hY1 : 0 < Y1) (hV : 0 < V) :
    (0 < Y1 - stageOneC1 σ r β P (Y1 + V / (1 + r)) ↔
        1 / β * (V / (P ^ (1 - σ) * Y1)) ^ (1 / σ) < 1 + r) ∧
      (Y1 - stageOneC1 σ r β P (Y1 + V / (1 + r)) < 0 ↔
        1 + r < 1 / β * (V / (P ^ (1 - σ) * Y1)) ^ (1 / σ)) ∧
      (Y1 - stageOneC1 σ r β P (Y1 + V / (1 + r)) = 0 ↔
        1 + r = 1 / β * (V / (P ^ (1 - σ) * Y1)) ^ (1 / σ)) :=
  current_account_sign_rCA hσ hr hβ hP hY1 hV

/-- Risk and the current account under (26), O&R p. 285: with `P < 1` (prices not actuarially
fair), optimal `C₁` is strictly below its certainty benchmark (`P = 1`) if `σ > 1` and strictly
above it if `σ < 1`, whatever the risk aversion `ρ`; and with `β(1+r) = 1`,
`Y₁ = V = Σ p(s)Y₂(s)`, the optimum has `CA₁ > 0` if `σ > 1` and `CA₁ < 0` if `σ < 1`. -/
theorem ez_consumption_vs_certainty {σ r β P W1 Y1 : ℝ} (hr : 0 < 1 + r) (hβ : 0 < β)
    (hP0 : 0 < P) (hP1 : P < 1) (hW : 0 < W1) (hY1 : 0 < Y1) :
    (1 < σ → stageOneC1 σ r β P W1 < stageOneC1 σ r β 1 W1) ∧
      (σ < 1 → stageOneC1 σ r β 1 W1 < stageOneC1 σ r β P W1) ∧
      (β * (1 + r) = 1 → (1 < σ → 0 < Y1 - stageOneC1 σ r β P (Y1 + Y1 / (1 + r))) ∧
        (σ < 1 → Y1 - stageOneC1 σ r β P (Y1 + Y1 / (1 + r)) < 0)) := by
  have h := consumption_vs_certainty (σ := σ) hr hβ hP0 hP1 hW
  simp only [stageOneC1, div_one]
  exact ⟨h.1, h.2, fun hβR => current_account_fair_rate hr hβR hP0 hP1 hY1⟩

end ObstfeldRogoff.InternationalFinancialMarkets.TwoStageBudgeting
