/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GlobalGrowth.BrockMirman
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue

/-!
# A two-country stochastic growth model with 100 percent depreciation

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §7.4.2
(pp. 500–501), equations (114)–(116), and the two-country log-linear model of §7.4.3.5
(p. 507), equation (136).

* **The investment share `Ψ`** (the book's "easy to check"): for `0 ≤ α < 1` and any finite
  distributions of the i.i.d. country shocks, `Ψ = E[AΨ^α/(AΨ^α + A*(1 − Ψ)^α)]` has **exactly one**
  solution in `(0, 1)`. Proof: in logit coordinates the residual has slope at most `α − 1 < 0`
  (a variance inequality, `E σ² ≥ (E σ)²`), so it is strictly decreasing and unbounded both ways.
  `Ψ = 0, 1` are spurious fixed points; symmetric countries give `Ψ = 1/2`.
* **The world planner** on the event tree over `A^W` (any finite Markov chain) and i.i.d.
  country shocks: when `Ψ` is the fixed point, (115)–(116) are optimal against every feasible
  world plan (supporting hyperplane, bound `(α/(1 − αβ))βᵀ` on partial sums), with finite welfare.
* All four Euler equations hold iff `Ψ` is the fixed point; consumption growth is equalised; a
  Home productivity shock raises investment in both countries; (136) and the investment shift.
-/

namespace ObstfeldRogoff.GlobalGrowth.TwoCountryRBC

open Finset Filter Topology
open ObstfeldRogoff.GlobalGrowth.BrockMirman

/-! ## The investment-share fixed point `Ψ = E[AΨ^α/(AΨ^α + A*(1−Ψ)^α)]` -/

/-- Home's share of next-period world output ex `A^W` when Home holds the share `Ψ` of world
capital: `a Ψ^α/(a Ψ^α + b (1 − Ψ)^α)` (O&R p. 501, `Y_{t+1}/Y^W_{t+1}`). -/
noncomputable def shareFn (α a b Ψ : ℝ) : ℝ := a * Ψ ^ α / (a * Ψ ^ α + b * (1 - Ψ) ^ α)

/-- The right side of the book's definition of `Ψ` (p. 501), for i.i.d. country shocks `A`
(pmf `p`) and `A*` (pmf `q`), independent of each other: `G(Ψ) = E[AΨ^α/(AΨ^α + A*(1−Ψ)^α)]`. -/
noncomputable def psiMap {I J : Type*} [Fintype I] [Fintype J] (α : ℝ) (p : I → ℝ) (q : J → ℝ)
    (A : I → ℝ) (As : J → ℝ) (Ψ : ℝ) : ℝ :=
  ∑ i, ∑ j, p i * q j * shareFn α (A i) (As j) Ψ

/-- The logistic function `σ(x) = 1/(1 + eˣ)`. -/
noncomputable def logistic (x : ℝ) : ℝ := 1 / (1 + Real.exp x)

/-- `0 < σ(x) < 1`. -/
theorem logistic_mem (x : ℝ) : 0 < logistic x ∧ logistic x < 1 := by
  have h := Real.exp_pos x
  refine ⟨by unfold logistic; positivity, ?_⟩
  unfold logistic
  rw [div_lt_one (by linarith)]
  linarith

/-- `σ′ = −σ(1 − σ)`. -/
theorem hasDerivAt_logistic (x : ℝ) :
    HasDerivAt logistic (-(logistic x * (1 - logistic x))) x := by
  have h1 : HasDerivAt (fun x => 1 + Real.exp x) (Real.exp x) x := by
    simpa using (Real.hasDerivAt_exp x).const_add 1
  have h2 := h1.inv (by positivity)
  have e : logistic = fun x => (1 + Real.exp x)⁻¹ := by funext x; simp [logistic]
  rw [e]
  convert h2 using 1
  have hp : (1 + Real.exp x) ≠ 0 := by positivity
  field_simp
  ring

/-- Share in logistic form: with `v = log((1−Ψ)/Ψ)` and `ρ = log(b/a)`,
`a Ψ^α/(a Ψ^α + b(1−Ψ)^α) = σ(ρ + α v)`. -/
theorem shareFn_eq_logistic {α a b Ψ : ℝ} (ha : 0 < a) (hb : 0 < b) (hΨ0 : 0 < Ψ)
    (hΨ1 : Ψ < 1) :
    shareFn α a b Ψ = logistic (Real.log (b / a) + α * Real.log ((1 - Ψ) / Ψ)) := by
  have h1 : 0 < 1 - Ψ := by linarith
  unfold shareFn logistic
  rw [Real.exp_add, Real.exp_log (div_pos hb ha), ← Real.log_rpow (div_pos h1 hΨ0),
    Real.exp_log (Real.rpow_pos_of_pos (div_pos h1 hΨ0) α), Real.div_rpow h1.le hΨ0.le]
  have hA := Real.rpow_pos_of_pos hΨ0 α
  have hB := Real.rpow_pos_of_pos h1 α
  field_simp

/-- `σ(log((1−Ψ)/Ψ)) = Ψ` on `(0,1)`. -/
theorem logistic_logit {Ψ : ℝ} (hΨ0 : 0 < Ψ) (hΨ1 : Ψ < 1) :
    logistic (Real.log ((1 - Ψ) / Ψ)) = Ψ := by
  unfold logistic
  rw [Real.exp_log (div_pos (by linarith) hΨ0)]
  field_simp
  ring

/-- The mixture `m(v) = Σ_k w_k σ(α v + ρ_k)`. -/
noncomputable def mixture {ι : Type*} [Fintype ι] (α : ℝ) (w ρ : ι → ℝ) (v : ℝ) : ℝ :=
  ∑ k, w k * logistic (α * v + ρ k)

/-- Hypotheses on the mixture weights: a probability vector. -/
structure Weights {ι : Type*} [Fintype ι] (w : ι → ℝ) : Prop where
  nonneg : ∀ k, 0 ≤ w k
  sum_one : ∑ k, w k = 1

/-- `0 < m(v) < 1`. -/
theorem mixture_mem {ι : Type*} [Fintype ι] {α : ℝ} {w ρ : ι → ℝ} (hw : Weights w) (v : ℝ) :
    0 < mixture α w ρ v ∧ mixture α w ρ v < 1 := by
  obtain ⟨k₀, -, hk₀⟩ := Finset.exists_ne_zero_of_sum_ne_zero
    (show ∑ k, w k ≠ 0 by rw [hw.sum_one]; exact one_ne_zero)
  have hpos : 0 < w k₀ := lt_of_le_of_ne (hw.nonneg k₀) (Ne.symm hk₀)
  constructor
  · unfold mixture
    calc (0 : ℝ) < w k₀ * logistic (α * v + ρ k₀) :=
          mul_pos hpos (logistic_mem _).1
      _ ≤ ∑ k, w k * logistic (α * v + ρ k) :=
          Finset.single_le_sum (f := fun k => w k * logistic (α * v + ρ k))
            (fun k _ => mul_nonneg (hw.nonneg k) (logistic_mem _).1.le) (Finset.mem_univ k₀)
  · unfold mixture
    have : ∑ k, w k * logistic (α * v + ρ k) < ∑ k, w k := by
      refine Finset.sum_lt_sum (fun k _ => ?_) ⟨k₀, Finset.mem_univ k₀, ?_⟩
      · exact mul_le_of_le_one_right (hw.nonneg k) (logistic_mem _).2.le
      · exact mul_lt_of_lt_one_right hpos (logistic_mem _).2
    rwa [hw.sum_one] at this

/-- The logit-transformed fixed-point residual `ψ(v) = log((1 − m(v))/m(v)) − v`. -/
noncomputable def residual {ι : Type*} [Fintype ι] (α : ℝ) (w ρ : ι → ℝ) (v : ℝ) : ℝ :=
  Real.log (1 - mixture α w ρ v) - Real.log (mixture α w ρ v) - v

/-- The mixture's dispersion term `S(v) = Σ w_k σ_k(1 − σ_k)`. -/
noncomputable def dispersion {ι : Type*} [Fintype ι] (α : ℝ) (w ρ : ι → ℝ) (v : ℝ) : ℝ :=
  ∑ k, w k * (logistic (α * v + ρ k) * (1 - logistic (α * v + ρ k)))

/-- `m′(v) = −α S(v)`. -/
theorem hasDerivAt_mixture {ι : Type*} [Fintype ι] (α : ℝ) (w ρ : ι → ℝ) (v : ℝ) :
    HasDerivAt (mixture α w ρ) (-α * dispersion α w ρ v) v := by
  have : ∀ k ∈ (Finset.univ : Finset ι), HasDerivAt (fun v => w k * logistic (α * v + ρ k))
      (w k * (-(logistic (α * v + ρ k) * (1 - logistic (α * v + ρ k))) * α)) v := by
    intro k _
    have hin : HasDerivAt (fun v => α * v + ρ k) α v := by
      simpa using ((hasDerivAt_id v).const_mul α).add_const (ρ k)
    exact ((hasDerivAt_logistic (α * v + ρ k)).comp v hin).const_mul (w k)
  have h := HasDerivAt.fun_sum this
  unfold mixture dispersion
  convert h using 1
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- **Variance inequality**: `S(v) ≤ m(v)(1 − m(v))` (equivalently `E σ² ≥ (E σ)²`). -/
theorem dispersion_le {ι : Type*} [Fintype ι] {α : ℝ} {w ρ : ι → ℝ} (hw : Weights w) (v : ℝ) :
    dispersion α w ρ v ≤ mixture α w ρ v * (1 - mixture α w ρ v) := by
  set m := mixture α w ρ v
  have hvar : 0 ≤ ∑ k, w k * (logistic (α * v + ρ k) - m) ^ 2 :=
    Finset.sum_nonneg fun k _ => mul_nonneg (hw.nonneg k) (sq_nonneg _)
  have e1 : ∑ k, w k * (logistic (α * v + ρ k) - m) ^ 2 =
      ∑ k, w k * logistic (α * v + ρ k) ^ 2 - 2 * m * (∑ k, w k * logistic (α * v + ρ k)) +
        m ^ 2 * ∑ k, w k := by
    have : ∀ k, w k * (logistic (α * v + ρ k) - m) ^ 2 = w k * logistic (α * v + ρ k) ^ 2 -
        2 * m * (w k * logistic (α * v + ρ k)) + m ^ 2 * w k := fun k => by ring
    simp only [this, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  have hmdef : ∑ k, w k * logistic (α * v + ρ k) = m := rfl
  rw [hmdef] at e1
  have e2 : dispersion α w ρ v = m - ∑ k, w k * logistic (α * v + ρ k) ^ 2 := by
    simp only [dispersion, m, mixture, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hw.sum_one] at e1
  rw [e2]
  nlinarith

/-- The residual is differentiable with `ψ′(v) = α S/(1 − m) + α S/m − 1`. -/
theorem hasDerivAt_residual {ι : Type*} [Fintype ι] {α : ℝ} {w ρ : ι → ℝ} (hw : Weights w)
    (v : ℝ) :
    HasDerivAt (residual α w ρ)
      (α * dispersion α w ρ v / (1 - mixture α w ρ v) +
        α * dispersion α w ρ v / mixture α w ρ v - 1) v := by
  have hm := hasDerivAt_mixture α w ρ v
  obtain ⟨h0, h1⟩ := mixture_mem (α := α) (ρ := ρ) hw v
  have hA : HasDerivAt (fun v => Real.log (1 - mixture α w ρ v))
      ((-(-α * dispersion α w ρ v)) / (1 - mixture α w ρ v)) v :=
    (hm.const_sub 1).log (by linarith)
  have hB : HasDerivAt (fun v => Real.log (mixture α w ρ v))
      ((-α * dispersion α w ρ v) / mixture α w ρ v) v := hm.log h0.ne'
  have h := (hA.sub hB).sub (hasDerivAt_id v)
  refine HasDerivAt.congr_deriv (f := residual α w ρ) h ?_
  ring

/-- **Slope bound**: `ψ′(v) ≤ α − 1 < 0`. -/
theorem deriv_residual_le {ι : Type*} [Fintype ι] {α : ℝ} (hα : 0 ≤ α) {w ρ : ι → ℝ}
    (hw : Weights w) (v : ℝ) : deriv (residual α w ρ) v ≤ α - 1 := by
  rw [(hasDerivAt_residual hw v).deriv]
  obtain ⟨h0, h1⟩ := mixture_mem (α := α) (ρ := ρ) hw v
  have hS := dispersion_le (α := α) (ρ := ρ) hw v
  have e : α * dispersion α w ρ v / (1 - mixture α w ρ v) +
      α * dispersion α w ρ v / mixture α w ρ v =
      α * (dispersion α w ρ v / (mixture α w ρ v * (1 - mixture α w ρ v))) := by
    field_simp [(show (1 - mixture α w ρ v) ≠ 0 by linarith)]
    ring
  rw [e]
  have hm1 : 0 < mixture α w ρ v * (1 - mixture α w ρ v) := mul_pos h0 (by linarith)
  have : dispersion α w ρ v / (mixture α w ρ v * (1 - mixture α w ρ v)) ≤ 1 :=
    (div_le_one hm1).2 hS
  nlinarith

/-- The residual is differentiable. -/
theorem differentiable_residual {ι : Type*} [Fintype ι] {α : ℝ} {w ρ : ι → ℝ}
    (hw : Weights w) : Differentiable ℝ (residual α w ρ) :=
  fun v => (hasDerivAt_residual hw v).differentiableAt

/-- **The residual has exactly one root** (for `0 ≤ α < 1`): it falls with slope at most
`α − 1`, so it is strictly decreasing and unbounded in both directions. -/
theorem existsUnique_residual_root {ι : Type*} [Fintype ι] {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    {w ρ : ι → ℝ} (hw : Weights w) : ∃! v, residual α w ρ v = 0 := by
  have hd := differentiable_residual (α := α) (ρ := ρ) hw
  have hslope : ∀ x y, x ≤ y → residual α w ρ y - residual α w ρ x ≤ (α - 1) * (y - x) :=
    fun x y hxy => image_sub_le_mul_sub_of_deriv_le hd (deriv_residual_le hα0 hw) hxy
  have hc : Continuous (residual α w ρ) := hd.continuous
  set r0 := residual α w ρ 0
  set v1 := r0 / (1 - α)
  have h1α : 0 < 1 - α := by linarith
  have hex : ∃ v, residual α w ρ v = 0 := by
    rcases le_or_gt 0 r0 with h | h
    · have hv1 : 0 ≤ v1 := div_nonneg h h1α.le
      have hle := hslope 0 v1 hv1
      have hval : residual α w ρ v1 ≤ 0 := by
        have : (α - 1) * (v1 - 0) = -r0 := by simp only [v1]; field_simp; ring
        linarith
      obtain ⟨v, -, hv0⟩ := intermediate_value_Icc' hv1 hc.continuousOn ⟨hval, h⟩
      exact ⟨v, hv0⟩
    · have hv1 : v1 ≤ 0 := div_nonpos_of_nonpos_of_nonneg h.le h1α.le
      have hle := hslope v1 0 hv1
      have hval : 0 ≤ residual α w ρ v1 := by
        have : (α - 1) * (0 - v1) = r0 := by simp only [v1]; field_simp; ring
        linarith
      obtain ⟨v, -, hv0⟩ := intermediate_value_Icc' hv1 hc.continuousOn ⟨h.le, hval⟩
      exact ⟨v, hv0⟩
  obtain ⟨x, hx⟩ := hex
  refine ⟨x, hx, fun y hy => ?_⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have := hslope y x h.le; nlinarith
  · have := hslope x y h.le; nlinarith

/-- Weights `w(i,j) = p(i) q(j)` of two independent pmfs form a probability vector. -/
theorem weights_prod {I J : Type*} [Fintype I] [Fintype J] {p : I → ℝ} {q : J → ℝ}
    (hp : Weights p) (hq : Weights q) : Weights (fun k : I × J => p k.1 * q k.2) := by
  refine ⟨fun k => mul_nonneg (hp.nonneg _) (hq.nonneg _), ?_⟩
  rw [Fintype.sum_prod_type]
  simp only [← Finset.mul_sum, hq.sum_one, mul_one, hp.sum_one]

/-- On `(0,1)`, `G(Ψ) = m(log((1 − Ψ)/Ψ))` with weights `p(i)q(j)` and `ρ = log(A*_j/A_i)`. -/
theorem psiMap_eq_mixture {I J : Type*} [Fintype I] [Fintype J] {α : ℝ} {p : I → ℝ}
    {q : J → ℝ} {A : I → ℝ} {As : J → ℝ} (hA : ∀ i, 0 < A i) (hAs : ∀ j, 0 < As j) {Ψ : ℝ}
    (hΨ0 : 0 < Ψ) (hΨ1 : Ψ < 1) :
    psiMap α p q A As Ψ = mixture α (fun k : I × J => p k.1 * q k.2)
      (fun k => Real.log (As k.2 / A k.1)) (Real.log ((1 - Ψ) / Ψ)) := by
  unfold psiMap mixture
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [shareFn_eq_logistic (hA i) (hAs j) hΨ0 hΨ1, add_comm]

/-- **Existence and uniqueness of the interior investment share** (O&R p. 501, "easy to check",
made precise): for `0 < α < 1` and i.i.d. positive country shocks with any finite
distributions, `Ψ = E[AΨ^α/(AΨ^α + A*(1 − Ψ)^α)]` has exactly one solution in `(0, 1)`. -/
theorem existsUnique_psi {I J : Type*} [Fintype I] [Fintype J] {α : ℝ} (hα0 : 0 ≤ α)
    (hα1 : α < 1) {p : I → ℝ} {q : J → ℝ} (hp : Weights p) (hq : Weights q) {A : I → ℝ}
    {As : J → ℝ} (hA : ∀ i, 0 < A i) (hAs : ∀ j, 0 < As j) :
    ∃! Ψ, (0 < Ψ ∧ Ψ < 1) ∧ psiMap α p q A As Ψ = Ψ := by
  set w := fun k : I × J => p k.1 * q k.2
  set ρ := fun k : I × J => Real.log (As k.2 / A k.1)
  have hw := weights_prod hp hq
  obtain ⟨v, hv, huniq⟩ := existsUnique_residual_root (ρ := ρ) hα0 hα1 hw
  obtain ⟨m0, m1⟩ := mixture_mem (α := α) (ρ := ρ) hw v
  have hlogit : Real.log ((1 - mixture α w ρ v) / mixture α w ρ v) = v := by
    rw [Real.log_div (by linarith) m0.ne']; unfold residual at hv; linarith
  refine ⟨mixture α w ρ v, ⟨⟨m0, m1⟩, ?_⟩, ?_⟩
  · rw [psiMap_eq_mixture hA hAs m0 m1]
    simp only [w, ρ] at hlogit ⊢
    rw [hlogit]
  · rintro Ψ ⟨⟨h0, h1⟩, hfix⟩
    have hroot : residual α w ρ (Real.log ((1 - Ψ) / Ψ)) = 0 := by
      have e := psiMap_eq_mixture (α := α) (p := p) (q := q) hA hAs h0 h1
      rw [hfix] at e
      unfold residual
      rw [← e, Real.log_div (by linarith) h0.ne']
      ring
    have := huniq _ hroot
    have e1 : logistic v = mixture α w ρ v := by
      rw [← logistic_logit m0 m1, hlogit]
    rw [← logistic_logit h0 h1, this]
    exact e1

/-- The corner values `Ψ = 0` and `Ψ = 1` are spurious fixed points (O&R p. 501). -/
theorem psiMap_zero_one {I J : Type*} [Fintype I] [Fintype J] {α : ℝ} (hα : 0 < α)
    {p : I → ℝ} {q : J → ℝ} (hp : Weights p) (hq : Weights q) {A : I → ℝ} {As : J → ℝ}
    (hA : ∀ i, 0 < A i) :
    psiMap α p q A As 0 = 0 ∧ psiMap α p q A As 1 = 1 := by
  constructor
  · simp [psiMap, shareFn, Real.zero_rpow hα.ne']
  · have : ∀ i j, shareFn α (A i) (As j) 1 = 1 := fun i j => by
      simp [shareFn, Real.zero_rpow hα.ne', (hA i).ne']
    simp only [psiMap, this, mul_one, ← Finset.mul_sum, hq.sum_one, hp.sum_one]

/-- **Symmetric countries** (identically distributed `A` and `A*`): `Ψ = 1/2`. -/
theorem psiMap_half {I : Type*} [Fintype I] {α : ℝ} {p : I → ℝ} (hp : Weights p)
    {A : I → ℝ} (hA : ∀ i, 0 < A i) : psiMap α p p A A (1 / 2) = 1 / 2 := by
  have hs : ∀ i j, shareFn α (A i) (A j) (1 / 2) = A i / (A i + A j) := by
    intro i j
    have h := Real.rpow_pos_of_pos (show (0 : ℝ) < 1 / 2 by norm_num) α
    have hi := hA i
    have hj := hA j
    simp only [shareFn, show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num]
    field_simp
  simp only [psiMap, hs]
  have hsym : ∑ i, ∑ j, p i * p j * (A i / (A i + A j)) =
      ∑ i, ∑ j, p j * p i * (A j / (A j + A i)) := Finset.sum_comm
  have htot : ∑ i, ∑ j, (p i * p j * (A i / (A i + A j)) + p j * p i * (A j / (A j + A i))) =
      1 := by
    have : ∀ i j, p i * p j * (A i / (A i + A j)) + p j * p i * (A j / (A j + A i)) =
        p i * p j := fun i j => by
      have := hA i; have := hA j
      field_simp; ring
    simp only [this, ← Finset.mul_sum, hp.sum_one, mul_one]
  rw [Finset.sum_congr rfl fun i _ => Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← hsym] at htot
  linarith

/-- With symmetric countries the unique interior investment share is `1/2`. -/
theorem psi_symmetric_unique {I : Type*} [Fintype I] {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1)
    {p : I → ℝ} (hp : Weights p) {A : I → ℝ} (hA : ∀ i, 0 < A i) {Ψ : ℝ} (hΨ0 : 0 < Ψ)
    (hΨ1 : Ψ < 1) (hfix : psiMap α p p A A Ψ = Ψ) : Ψ = 1 / 2 := by
  obtain ⟨Ψ₀, -, huniq⟩ := existsUnique_psi hα0 hα1 hp hp hA hA
  rw [huniq Ψ ⟨⟨hΨ0, hΨ1⟩, hfix⟩, ← huniq (1 / 2) ⟨⟨by norm_num, by norm_num⟩, psiMap_half hp hA⟩]

/-! ## The world planner's problem on the event tree

The shock state is `(w, i, j) ∈ W × I × J`: `A^W = AW(w)` follows an arbitrary finite Markov
chain `PW`, while the country components `A = A(i)` and `A* = As(j)` are i.i.d. over time with
pmfs `p` and `q`, independent of each other and of `A^W` (O&R p. 500). -/

namespace Planner

variable {W I J : Type*} [Fintype W] [Fintype I] [Fintype J]

/-- The product transition kernel on `W × I × J`. -/
def kernel (PW : W → W → ℝ) (p : I → ℝ) (q : J → ℝ) (s s' : W × I × J) : ℝ :=
  PW s.1 s'.1 * (p s'.2.1 * q s'.2.2)

/-- The product kernel is a Markov kernel. -/
theorem kernel_isMarkov {PW : W → W → ℝ} (hPW : IsMarkov PW) {p : I → ℝ} {q : J → ℝ}
    (hp : Weights p) (hq : Weights q) : IsMarkov (kernel PW p q) := by
  refine ⟨fun s s' => mul_nonneg (hPW.nonneg _ _) (mul_nonneg (hp.nonneg _) (hq.nonneg _)),
    fun s => ?_⟩
  simp only [kernel, Fintype.sum_prod_type, ← Finset.mul_sum, hq.sum_one,
    mul_one, hp.sum_one, hPW.sum_one]

/-- Conditional expectations of functions of the country shocks do not depend on the current
state (i.i.d. country components). -/
theorem kernel_expect {PW : W → W → ℝ} (hPW : IsMarkov PW) (p : I → ℝ) (q : J → ℝ)
    (f : I → J → ℝ) (s : W × I × J) :
    ∑ s', kernel PW p q s s' * f s'.2.1 s'.2.2 = ∑ i, ∑ j, p i * q j * f i j := by
  simp only [kernel, Fintype.sum_prod_type]
  simp only [mul_assoc, ← Finset.mul_sum, ← Finset.sum_mul, hPW.sum_one, one_mul]

/-- World output `Y^W = A^W [A K^α + A* (K*)^α]` at a node, given the capital plans (O&R
p. 500 and (114)). -/
noncomputable def worldOutput (AW : W → ℝ) (A : I → ℝ) (As : J → ℝ) (α K₀ Ks₀ : ℝ)
    (k ks : List (W × I × J) → ℝ) : List (W × I × J) → ℝ
  | [] => 0
  | s :: h => AW s.1 * (A s.2.1 * capIn K₀ k h ^ α + As s.2.2 * capIn Ks₀ ks h ^ α)

/-- Foreign consumption from the world resource constraint (114). -/
noncomputable def foreignCons (AW : W → ℝ) (A : I → ℝ) (As : J → ℝ) (α K₀ Ks₀ : ℝ)
    (k ks c : List (W × I × J) → ℝ) (l : List (W × I × J)) : ℝ :=
  worldOutput AW A As α K₀ Ks₀ k ks l - k l - ks l - c l

/-- A feasible world plan: positive Home and Foreign capital and consumption at every node,
with the world resource constraint (114). -/
def Feasible (AW : W → ℝ) (A : I → ℝ) (As : J → ℝ) (α K₀ Ks₀ : ℝ)
    (k ks c : List (W × I × J) → ℝ) : Prop :=
  ∀ s h, 0 < k (s :: h) ∧ 0 < ks (s :: h) ∧ 0 < c (s :: h) ∧
    0 < foreignCons AW A As α K₀ Ks₀ k ks c (s :: h)

/-- The planner's expected welfare up to horizon `T`, with weight `κ` on Home (O&R p. 500). -/
noncomputable def welfare (P : W × I × J → W × I × J → ℝ) (AW : W → ℝ) (A : I → ℝ)
    (As : J → ℝ) (α β κ K₀ Ks₀ : ℝ) (k ks c : List (W × I × J) → ℝ) (s₀ : W × I × J)
    (T : ℕ) : ℝ :=
  ∑ t ∈ range T, β ^ t * ev P (fun l => κ * Real.log (c l) +
    (1 - κ) * Real.log (foreignCons AW A As α K₀ Ks₀ k ks c l)) t s₀ []

/-- The conjectured policy (115)–(116): capital carried out of each node,
`(K′, K*′) = (Ψ αβ Y^W, (1 − Ψ) αβ Y^W)`; the value at `[]` is initial capital. -/
noncomputable def optCap (AW : W → ℝ) (A : I → ℝ) (As : J → ℝ) (α β Ψ K₀ Ks₀ : ℝ) :
    List (W × I × J) → ℝ × ℝ
  | [] => (K₀, Ks₀)
  | s :: h => (Ψ * α * β * (AW s.1 * (A s.2.1 * (optCap AW A As α β Ψ K₀ Ks₀ h).1 ^ α +
      As s.2.2 * (optCap AW A As α β Ψ K₀ Ks₀ h).2 ^ α)),
      (1 - Ψ) * α * β * (AW s.1 * (A s.2.1 * (optCap AW A As α β Ψ K₀ Ks₀ h).1 ^ α +
      As s.2.2 * (optCap AW A As α β Ψ K₀ Ks₀ h).2 ^ α)))

/-- Home capital under the conjectured policy. -/
noncomputable def optK (AW : W → ℝ) (A : I → ℝ) (As : J → ℝ) (α β Ψ K₀ Ks₀ : ℝ)
    (l : List (W × I × J)) : ℝ := (optCap AW A As α β Ψ K₀ Ks₀ l).1

/-- Foreign capital under the conjectured policy. -/
noncomputable def optKs (AW : W → ℝ) (A : I → ℝ) (As : J → ℝ) (α β Ψ K₀ Ks₀ : ℝ)
    (l : List (W × I × J)) : ℝ := (optCap AW A As α β Ψ K₀ Ks₀ l).2

/-- Home consumption under (115), `C = κ(1 − αβ) Y^W`. -/
noncomputable def optC (AW : W → ℝ) (A : I → ℝ) (As : J → ℝ) (α β κ Ψ K₀ Ks₀ : ℝ)
    (l : List (W × I × J)) : ℝ :=
  κ * (1 - α * β) * worldOutput AW A As α K₀ Ks₀ (optK AW A As α β Ψ K₀ Ks₀)
    (optKs AW A As α β Ψ K₀ Ks₀) l

omit [Fintype W] [Fintype I] [Fintype J] in
/-- Capital entering a node under the conjectured policy. -/
theorem capIn_opt (AW : W → ℝ) (A : I → ℝ) (As : J → ℝ) (α β Ψ K₀ Ks₀ : ℝ)
    (h : List (W × I × J)) :
    capIn K₀ (optK AW A As α β Ψ K₀ Ks₀) h = optK AW A As α β Ψ K₀ Ks₀ h ∧
      capIn Ks₀ (optKs AW A As α β Ψ K₀ Ks₀) h = optKs AW A As α β Ψ K₀ Ks₀ h := by
  cases h <;> exact ⟨rfl, rfl⟩

omit [Fintype W] [Fintype I] [Fintype J] in
/-- Under the conjectured policy, capital carried out of a node is `(Ψ αβ Y^W, (1 − Ψ) αβ Y^W)`. -/
theorem optCap_cons (AW : W → ℝ) (A : I → ℝ) (As : J → ℝ) (α β Ψ K₀ Ks₀ : ℝ)
    (s : W × I × J) (h : List (W × I × J)) :
    optK AW A As α β Ψ K₀ Ks₀ (s :: h) = Ψ * α * β * worldOutput AW A As α K₀ Ks₀
      (optK AW A As α β Ψ K₀ Ks₀) (optKs AW A As α β Ψ K₀ Ks₀) (s :: h) ∧
    optKs AW A As α β Ψ K₀ Ks₀ (s :: h) = (1 - Ψ) * α * β * worldOutput AW A As α K₀ Ks₀
      (optK AW A As α β Ψ K₀ Ks₀) (optKs AW A As α β Ψ K₀ Ks₀) (s :: h) := by
  simp only [worldOutput, (capIn_opt AW A As α β Ψ K₀ Ks₀ h).1,
    (capIn_opt AW A As α β Ψ K₀ Ks₀ h).2]
  exact ⟨rfl, rfl⟩

/-- Standing assumptions for the two-country planner. -/
structure Assumptions (AW : W → ℝ) (A : I → ℝ) (As : J → ℝ) (α β κ Ψ K₀ Ks₀ : ℝ) : Prop where
  params : Params α β
  κ_pos : 0 < κ
  κ_lt_one : κ < 1
  Ψ_pos : 0 < Ψ
  Ψ_lt_one : Ψ < 1
  AW_pos : ∀ w, 0 < AW w
  A_pos : ∀ i, 0 < A i
  As_pos : ∀ j, 0 < As j
  K₀_pos : 0 < K₀
  Ks₀_pos : 0 < Ks₀

omit [Fintype W] [Fintype I] [Fintype J] in
/-- Positivity of capital and output under the conjectured policy. -/
theorem opt_pos {AW : W → ℝ} {A : I → ℝ} {As : J → ℝ} {α β κ Ψ K₀ Ks₀ : ℝ}
    (H : Assumptions AW A As α β κ Ψ K₀ Ks₀) (l : List (W × I × J)) :
    0 < optK AW A As α β Ψ K₀ Ks₀ l ∧ 0 < optKs AW A As α β Ψ K₀ Ks₀ l := by
  induction l with
  | nil => exact ⟨H.K₀_pos, H.Ks₀_pos⟩
  | cons s h ih =>
    have hY : 0 < AW s.1 * (A s.2.1 * (optCap AW A As α β Ψ K₀ Ks₀ h).1 ^ α +
        As s.2.2 * (optCap AW A As α β Ψ K₀ Ks₀ h).2 ^ α) :=
      mul_pos (H.AW_pos _) (add_pos (mul_pos (H.A_pos _) (Real.rpow_pos_of_pos ih.1 α))
        (mul_pos (H.As_pos _) (Real.rpow_pos_of_pos ih.2 α)))
    have hab := H.params.ab_pos
    refine ⟨?_, ?_⟩
    · change 0 < Ψ * α * β * _
      have := mul_pos H.Ψ_pos hab
      rw [mul_assoc Ψ]
      exact mul_pos this hY
    · change 0 < (1 - Ψ) * α * β * _
      have := mul_pos (sub_pos.2 H.Ψ_lt_one) hab
      rw [mul_assoc (1 - Ψ)]
      exact mul_pos this hY

omit [Fintype W] [Fintype I] [Fintype J] in
/-- World output under the conjectured policy is positive. -/
theorem optY_pos {AW : W → ℝ} {A : I → ℝ} {As : J → ℝ} {α β κ Ψ K₀ Ks₀ : ℝ}
    (H : Assumptions AW A As α β κ Ψ K₀ Ks₀) (s : W × I × J) (h : List (W × I × J)) :
    0 < worldOutput AW A As α K₀ Ks₀ (optK AW A As α β Ψ K₀ Ks₀)
      (optKs AW A As α β Ψ K₀ Ks₀) (s :: h) := by
  simp only [worldOutput, (capIn_opt AW A As α β Ψ K₀ Ks₀ h).1,
    (capIn_opt AW A As α β Ψ K₀ Ks₀ h).2]
  exact mul_pos (H.AW_pos _) (add_pos (mul_pos (H.A_pos _)
    (Real.rpow_pos_of_pos (opt_pos H h).1 α))
    (mul_pos (H.As_pos _) (Real.rpow_pos_of_pos (opt_pos H h).2 α)))

omit [Fintype W] [Fintype I] [Fintype J] in
/-- Under (115)–(116) Foreign consumption is `(1 − κ)(1 − αβ) Y^W`. -/
theorem foreignCons_opt {AW : W → ℝ} {A : I → ℝ} {As : J → ℝ} {α β κ Ψ K₀ Ks₀ : ℝ}
    (s : W × I × J) (h : List (W × I × J)) :
    foreignCons AW A As α K₀ Ks₀ (optK AW A As α β Ψ K₀ Ks₀) (optKs AW A As α β Ψ K₀ Ks₀)
      (optC AW A As α β κ Ψ K₀ Ks₀) (s :: h) = (1 - κ) * (1 - α * β) *
      worldOutput AW A As α K₀ Ks₀ (optK AW A As α β Ψ K₀ Ks₀)
        (optKs AW A As α β Ψ K₀ Ks₀) (s :: h) := by
  simp only [foreignCons, optC, (optCap_cons AW A As α β Ψ K₀ Ks₀ s h).1,
    (optCap_cons AW A As α β Ψ K₀ Ks₀ s h).2]
  ring

omit [Fintype W] [Fintype I] [Fintype J] in
/-- The conjectured plan (115)–(116) is feasible. -/
theorem opt_feasible {AW : W → ℝ} {A : I → ℝ} {As : J → ℝ} {α β κ Ψ K₀ Ks₀ : ℝ}
    (H : Assumptions AW A As α β κ Ψ K₀ Ks₀) :
    Feasible AW A As α K₀ Ks₀ (optK AW A As α β Ψ K₀ Ks₀) (optKs AW A As α β Ψ K₀ Ks₀)
      (optC AW A As α β κ Ψ K₀ Ks₀) := by
  intro s h
  have hY := optY_pos H s h
  have hab := H.params.ab_lt_one
  refine ⟨(opt_pos H (s :: h)).1, (opt_pos H (s :: h)).2, ?_, ?_⟩
  · exact mul_pos (mul_pos H.κ_pos (by linarith)) hY
  · rw [foreignCons_opt]
    exact mul_pos (mul_pos (by linarith [H.κ_lt_one]) (by linarith)) hY

/-- World output under the conjectured policy. -/
noncomputable def optY (AW : W → ℝ) (A : I → ℝ) (As : J → ℝ) (α β Ψ K₀ Ks₀ : ℝ) :
    List (W × I × J) → ℝ :=
  worldOutput AW A As α K₀ Ks₀ (optK AW A As α β Ψ K₀ Ks₀) (optKs AW A As α β Ψ K₀ Ks₀)

/-- The output-gap term `(Y^W − Y°)/X°` with `X° = (1 − αβ) Y°`. -/
noncomputable def outGap (AW : W → ℝ) (A : I → ℝ) (As : J → ℝ) (α β Ψ K₀ Ks₀ : ℝ)
    (k ks : List (W × I × J) → ℝ) (l : List (W × I × J)) : ℝ :=
  (worldOutput AW A As α K₀ Ks₀ k ks l - optY AW A As α β Ψ K₀ Ks₀ l) /
    ((1 - α * β) * optY AW A As α β Ψ K₀ Ks₀ l)

/-- The share-weighted capital gap `(α/(1 − αβ)) [Ψ (K/K° − 1) + (1 − Ψ)(K*/K*° − 1)]`. -/
noncomputable def capGap (AW : W → ℝ) (A : I → ℝ) (As : J → ℝ) (α β Ψ K₀ Ks₀ : ℝ)
    (k ks : List (W × I × J) → ℝ) (l : List (W × I × J)) : ℝ :=
  coefK α β * (Ψ * (capIn K₀ k l / optK AW A As α β Ψ K₀ Ks₀ l - 1) +
    (1 - Ψ) * (capIn Ks₀ ks l / optKs AW A As α β Ψ K₀ Ks₀ l - 1))

omit [Fintype W] [Fintype I] [Fintype J] in
/-- Output-gap bound at any node (concavity of `K^α` in each country):
`(Y − Y°)/X° ≤ (α/(1 − αβ)) [π (K/K° − 1) + (1 − π)(K*/K*° − 1)]`, where
`π = A K°^α/(A K°^α + A* K*°^α)` is Home's share of output. -/
theorem outGap_le {AW : W → ℝ} {A : I → ℝ} {As : J → ℝ} {α β κ Ψ K₀ Ks₀ : ℝ}
    (H : Assumptions AW A As α β κ Ψ K₀ Ks₀) {k ks c : List (W × I × J) → ℝ}
    (hf : Feasible AW A As α K₀ Ks₀ k ks c) (s : W × I × J) (g : List (W × I × J)) :
    outGap AW A As α β Ψ K₀ Ks₀ k ks (s :: g) ≤ coefK α β *
      (A s.2.1 * optK AW A As α β Ψ K₀ Ks₀ g ^ α /
          (A s.2.1 * optK AW A As α β Ψ K₀ Ks₀ g ^ α +
            As s.2.2 * optKs AW A As α β Ψ K₀ Ks₀ g ^ α) *
        (capIn K₀ k g / optK AW A As α β Ψ K₀ Ks₀ g - 1) +
       (1 - A s.2.1 * optK AW A As α β Ψ K₀ Ks₀ g ^ α /
          (A s.2.1 * optK AW A As α β Ψ K₀ Ks₀ g ^ α +
            As s.2.2 * optKs AW A As α β Ψ K₀ Ks₀ g ^ α)) *
        (capIn Ks₀ ks g / optKs AW A As α β Ψ K₀ Ks₀ g - 1)) := by
  have hp := H.params
  have hab := hp.ab_lt_one
  set x := capIn K₀ k g
  set xs := capIn Ks₀ ks g
  set y := optK AW A As α β Ψ K₀ Ks₀ g
  set ys := optKs AW A As α β Ψ K₀ Ks₀ g
  have hx : 0 < x := by
    cases g with
    | nil => exact H.K₀_pos
    | cons s' g' => exact (hf s' g').1
  have hxs : 0 < xs := by
    cases g with
    | nil => exact H.Ks₀_pos
    | cons s' g' => exact (hf s' g').2.1
  have hy := (opt_pos H g).1
  have hys := (opt_pos H g).2
  have hw := H.AW_pos s.1
  have ha := H.A_pos s.2.1
  have hb := H.As_pos s.2.2
  have hyα := Real.rpow_pos_of_pos hy α
  have hysα := Real.rpow_pos_of_pos hys α
  have t1 := rpow_le_tangent hp.α_pos.le hp.α_lt_one.le hx hy
  have t2 := rpow_le_tangent hp.α_pos.le hp.α_lt_one.le hxs hys
  have hY : optY AW A As α β Ψ K₀ Ks₀ (s :: g) =
      AW s.1 * (A s.2.1 * y ^ α + As s.2.2 * ys ^ α) := by
    simp only [optY, worldOutput, (capIn_opt AW A As α β Ψ K₀ Ks₀ g).1,
      (capIn_opt AW A As α β Ψ K₀ Ks₀ g).2, y, ys]
  have hYr : worldOutput AW A As α K₀ Ks₀ k ks (s :: g) =
      AW s.1 * (A s.2.1 * x ^ α + As s.2.2 * xs ^ α) := rfl
  simp only [outGap, coefK]
  rw [hY, hYr]
  have hD : 0 < A s.2.1 * y ^ α + As s.2.2 * ys ^ α := by positivity
  have h1 : (1 - α * β) ≠ 0 := by linarith
  rw [div_le_iff₀ (mul_pos (by linarith) (mul_pos hw hD))]
  have e : α / (1 - α * β) * (A s.2.1 * y ^ α / (A s.2.1 * y ^ α + As s.2.2 * ys ^ α) *
      (x / y - 1) + (1 - A s.2.1 * y ^ α / (A s.2.1 * y ^ α + As s.2.2 * ys ^ α)) *
      (xs / ys - 1)) * ((1 - α * β) * (AW s.1 * (A s.2.1 * y ^ α + As s.2.2 * ys ^ α))) =
      AW s.1 * (A s.2.1 * (y ^ α * (α * (x / y - 1))) +
        As s.2.2 * (ys ^ α * (α * (xs / ys - 1)))) := by
    field_simp
    ring
  rw [e]
  have := mul_le_mul_of_nonneg_left t1 ha.le
  have := mul_le_mul_of_nonneg_left t2 hb.le
  have := mul_le_mul_of_nonneg_left
    (add_le_add (mul_le_mul_of_nonneg_left t1 ha.le) (mul_le_mul_of_nonneg_left t2 hb.le))
    hw.le
  nlinarith

/-- Scale invariance of the output share: `a(Ψc)^α/(a(Ψc)^α + b((1 − Ψ)c)^α) = shareFn α a b Ψ`. -/
theorem shareFn_scale {α a b Ψ c : ℝ} (ha : 0 < a) (hb : 0 < b) (hΨ0 : 0 < Ψ) (hΨ1 : Ψ < 1)
    (hc : 0 < c) :
    a * (Ψ * c) ^ α / (a * (Ψ * c) ^ α + b * ((1 - Ψ) * c) ^ α) = shareFn α a b Ψ := by
  have h1 : 0 < 1 - Ψ := by linarith
  rw [Real.mul_rpow hΨ0.le hc.le, Real.mul_rpow h1.le hc.le]
  unfold shareFn
  have hcα := Real.rpow_pos_of_pos hc α
  have hA := Real.rpow_pos_of_pos hΨ0 α
  have hB := Real.rpow_pos_of_pos h1 α
  rw [div_eq_div_iff (by positivity) (by positivity)]
  ring

omit [Fintype W] [Fintype I] [Fintype J] in
/-- Under the conjectured policy, Home's output share next period is `shareFn α A A* Ψ`
(the capital ratio is `Ψ/(1 − Ψ)` at every non-root node). -/
theorem share_opt {AW : W → ℝ} {A : I → ℝ} {As : J → ℝ} {α β κ Ψ K₀ Ks₀ : ℝ}
    (H : Assumptions AW A As α β κ Ψ K₀ Ks₀) {a b : ℝ} (ha : 0 < a) (hb : 0 < b)
    (s : W × I × J) (h : List (W × I × J)) :
    a * optK AW A As α β Ψ K₀ Ks₀ (s :: h) ^ α /
        (a * optK AW A As α β Ψ K₀ Ks₀ (s :: h) ^ α +
          b * optKs AW A As α β Ψ K₀ Ks₀ (s :: h) ^ α) = shareFn α a b Ψ := by
  rw [(optCap_cons AW A As α β Ψ K₀ Ks₀ s h).1, (optCap_cons AW A As α β Ψ K₀ Ks₀ s h).2]
  set Y := worldOutput AW A As α K₀ Ks₀ (optK AW A As α β Ψ K₀ Ks₀)
    (optKs AW A As α β Ψ K₀ Ks₀) (s :: h)
  rw [show Ψ * α * β * Y = Ψ * (α * β * Y) by ring,
    show (1 - Ψ) * α * β * Y = (1 - Ψ) * (α * β * Y) by ring]
  exact shareFn_scale ha hb H.Ψ_pos H.Ψ_lt_one (mul_pos H.params.ab_pos (optY_pos H s h))

/-- **Expected output-gap bound**: when `Ψ` solves the fixed point `Ψ = G(Ψ)`,
`E_t[(Y_{t+1} − Y°_{t+1})/X°_{t+1}] ≤ (α/(1 − αβ))[Ψ(K′/K°′ − 1) + (1 − Ψ)(K*′/K*°′ − 1)]`. -/
theorem nextExp_outGap_le {PW : W → W → ℝ} (hPW : IsMarkov PW) {p : I → ℝ} {q : J → ℝ}
    {AW : W → ℝ} {A : I → ℝ} {As : J → ℝ} {α β κ Ψ K₀ Ks₀ : ℝ}
    (H : Assumptions AW A As α β κ Ψ K₀ Ks₀) (hp : Weights p) (hq : Weights q)
    (hfix : psiMap α p q A As Ψ = Ψ) {k ks c : List (W × I × J) → ℝ}
    (hf : Feasible AW A As α K₀ Ks₀ k ks c) (s : W × I × J) (h : List (W × I × J)) :
    nextExp (kernel PW p q) (outGap AW A As α β Ψ K₀ Ks₀ k ks) (s :: h) ≤
      capGap AW A As α β Ψ K₀ Ks₀ k ks (s :: h) := by
  have hM := kernel_isMarkov hPW hp hq
  set X1 := capIn K₀ k (s :: h) / optK AW A As α β Ψ K₀ Ks₀ (s :: h) - 1
  set X2 := capIn Ks₀ ks (s :: h) / optKs AW A As α β Ψ K₀ Ks₀ (s :: h) - 1
  have hb : ∀ s', outGap AW A As α β Ψ K₀ Ks₀ k ks (s' :: s :: h) ≤
      coefK α β * X1 * shareFn α (A s'.2.1) (As s'.2.2) Ψ +
        coefK α β * X2 * (1 - shareFn α (A s'.2.1) (As s'.2.2) Ψ) := by
    intro s'
    have := outGap_le H hf s' (s :: h)
    rw [share_opt H (H.A_pos _) (H.As_pos _)] at this
    linarith
  calc nextExp (kernel PW p q) (outGap AW A As α β Ψ K₀ Ks₀ k ks) (s :: h)
      ≤ ∑ s', kernel PW p q s s' * (coefK α β * X1 * shareFn α (A s'.2.1) (As s'.2.2) Ψ +
          coefK α β * X2 * (1 - shareFn α (A s'.2.1) (As s'.2.2) Ψ)) :=
        Finset.sum_le_sum fun s' _ => mul_le_mul_of_nonneg_left (hb s') (hM.nonneg s s')
    _ = coefK α β * X1 * psiMap α p q A As Ψ + coefK α β * X2 * (1 - psiMap α p q A As Ψ) := by
        have e1 : ∑ s', kernel PW p q s s' * shareFn α (A s'.2.1) (As s'.2.2) Ψ =
            psiMap α p q A As Ψ :=
          kernel_expect hPW p q (fun i j => shareFn α (A i) (As j) Ψ) s
        have e2 : ∀ s', kernel PW p q s s' *
            (coefK α β * X1 * shareFn α (A s'.2.1) (As s'.2.2) Ψ +
              coefK α β * X2 * (1 - shareFn α (A s'.2.1) (As s'.2.2) Ψ)) =
            (coefK α β * X1 - coefK α β * X2) *
              (kernel PW p q s s' * shareFn α (A s'.2.1) (As s'.2.2) Ψ) +
            coefK α β * X2 * kernel PW p q s s' := fun s' => by ring
        simp only [e2]
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, e1, hM.sum_one]
        ring
    _ = capGap AW A As α β Ψ K₀ Ks₀ k ks (s :: h) := by
        rw [hfix, capGap]; ring

omit [Fintype W] [Fintype I] [Fintype J] in
/-- Node supporting-hyperplane inequality for the planner:
`κ log C + (1 − κ) log C* − [κ log C° + (1 − κ) log C*°] ≤ (Y − Y°)/X° − β capGap`. -/
theorem welfare_node_le {AW : W → ℝ} {A : I → ℝ} {As : J → ℝ} {α β κ Ψ K₀ Ks₀ : ℝ}
    (H : Assumptions AW A As α β κ Ψ K₀ Ks₀) {k ks c : List (W × I × J) → ℝ}
    (hf : Feasible AW A As α K₀ Ks₀ k ks c) (s : W × I × J) (h : List (W × I × J)) :
    κ * Real.log (c (s :: h)) + (1 - κ) * Real.log (foreignCons AW A As α K₀ Ks₀ k ks c (s :: h))
      - (κ * Real.log (optC AW A As α β κ Ψ K₀ Ks₀ (s :: h)) + (1 - κ) *
        Real.log (foreignCons AW A As α K₀ Ks₀ (optK AW A As α β Ψ K₀ Ks₀)
          (optKs AW A As α β Ψ K₀ Ks₀) (optC AW A As α β κ Ψ K₀ Ks₀) (s :: h))) ≤
      outGap AW A As α β Ψ K₀ Ks₀ k ks (s :: h) -
        β * capGap AW A As α β Ψ K₀ Ks₀ k ks (s :: h) := by
  have hp := H.params
  have hab := hp.ab_lt_one
  obtain ⟨hk, hks, hc, hcs⟩ := hf s h
  set Yo := optY AW A As α β Ψ K₀ Ks₀ (s :: h) with hYo
  have hY : 0 < Yo := optY_pos H s h
  have hX : 0 < (1 - α * β) * Yo := mul_pos (by linarith) hY
  have hκ := H.κ_pos
  have hκ1 : 0 < 1 - κ := by linarith [H.κ_lt_one]
  have hC0 : optC AW A As α β κ Ψ K₀ Ks₀ (s :: h) = κ * ((1 - α * β) * Yo) := by
    simp only [optC, hYo, optY]; ring
  have hCs0 := foreignCons_opt (AW := AW) (A := A) (As := As) (α := α) (β := β) (κ := κ)
    (Ψ := Ψ) (K₀ := K₀) (Ks₀ := Ks₀) s h
  rw [hC0, hCs0, show (1 - κ) * (1 - α * β) * worldOutput AW A As α K₀ Ks₀
    (optK AW A As α β Ψ K₀ Ks₀) (optKs AW A As α β Ψ K₀ Ks₀) (s :: h) =
    (1 - κ) * ((1 - α * β) * Yo) by simp only [hYo, optY]; ring]
  have l1 := Real.log_le_sub_one_of_pos (div_pos hc (mul_pos hκ hX))
  have l2 := Real.log_le_sub_one_of_pos (div_pos hcs (mul_pos hκ1 hX))
  rw [Real.log_div hc.ne' (mul_pos hκ hX).ne'] at l1
  rw [Real.log_div hcs.ne' (mul_pos hκ1 hX).ne'] at l2
  have l1' := mul_le_mul_of_nonneg_left l1 hκ.le
  have l2' := mul_le_mul_of_nonneg_left l2 hκ1.le
  have hsum : κ * (c (s :: h) / (κ * ((1 - α * β) * Yo)) - 1) +
      (1 - κ) * (foreignCons AW A As α K₀ Ks₀ k ks c (s :: h) /
        ((1 - κ) * ((1 - α * β) * Yo)) - 1) =
      outGap AW A As α β Ψ K₀ Ks₀ k ks (s :: h) -
        β * capGap AW A As α β Ψ K₀ Ks₀ k ks (s :: h) := by
    have hk0 := (optCap_cons AW A As α β Ψ K₀ Ks₀ s h).1
    have hks0 := (optCap_cons AW A As α β Ψ K₀ Ks₀ s h).2
    simp only [outGap, capGap, coefK, foreignCons, capIn]
    rw [hk0, hks0]
    have eY : worldOutput AW A As α K₀ Ks₀ (optK AW A As α β Ψ K₀ Ks₀)
        (optKs AW A As α β Ψ K₀ Ks₀) (s :: h) = Yo := rfl
    have eY2 : optY AW A As α β Ψ K₀ Ks₀ (s :: h) = Yo := rfl
    simp only [eY, eY2]
    have h1 : (1 - α * β) ≠ 0 := by linarith
    have h2 := hY.ne'
    have h3 := hκ.ne'
    have h4 := hκ1.ne'
    have h5 := H.Ψ_pos.ne'
    have h6 := (sub_pos.2 H.Ψ_lt_one).ne'
    have h7 := hp.α_pos.ne'
    have h8 := hp.β_pos.ne'
    field_simp
    ring
  linarith

/-- **Optimality of (115)–(116) for the world planner** (O&R p. 501, made rigorous: the book
checks only the four Euler equations). If `Ψ ∈ (0, 1)` solves `Ψ = G(Ψ)`, then for every
feasible world plan and every horizon `T`,
`welfare_T(rival) ≤ welfare_T(115–116) + (α/(1 − αβ)) βᵀ`. -/
theorem welfare_le_opt_add {PW : W → W → ℝ} (hPW : IsMarkov PW) {p : I → ℝ} {q : J → ℝ}
    {AW : W → ℝ} {A : I → ℝ} {As : J → ℝ} {α β κ Ψ K₀ Ks₀ : ℝ}
    (H : Assumptions AW A As α β κ Ψ K₀ Ks₀) (hp : Weights p) (hq : Weights q)
    (hfix : psiMap α p q A As Ψ = Ψ) {k ks c : List (W × I × J) → ℝ}
    (hf : Feasible AW A As α K₀ Ks₀ k ks c) (s₀ : W × I × J) (T : ℕ) :
    welfare (kernel PW p q) AW A As α β κ K₀ Ks₀ k ks c s₀ T ≤
      welfare (kernel PW p q) AW A As α β κ K₀ Ks₀ (optK AW A As α β Ψ K₀ Ks₀)
        (optKs AW A As α β Ψ K₀ Ks₀) (optC AW A As α β κ Ψ K₀ Ks₀) s₀ T +
        coefK α β * β ^ T := by
  set P := kernel PW p q
  have hM : IsMarkov P := kernel_isMarkov hPW hp hq
  have hpar := H.params
  set U : List (W × I × J) → ℝ := fun l => κ * Real.log (c l) +
    (1 - κ) * Real.log (foreignCons AW A As α K₀ Ks₀ k ks c l)
  set Uo : List (W × I × J) → ℝ := fun l => κ * Real.log (optC AW A As α β κ Ψ K₀ Ks₀ l) +
    (1 - κ) * Real.log (foreignCons AW A As α K₀ Ks₀ (optK AW A As α β Ψ K₀ Ks₀)
      (optKs AW A As α β Ψ K₀ Ks₀) (optC AW A As α β κ Ψ K₀ Ks₀) l)
  have ha := coefK_pos hpar
  have key := telescope_bound (d := fun t => ev P (fun l => U l - Uo l) t s₀ [])
    (q := fun t => ev P (outGap AW A As α β Ψ K₀ Ks₀ k ks) t s₀ [])
    (r := fun t => ev P (capGap AW A As α β Ψ K₀ Ks₀ k ks) t s₀ []) hpar.β_pos.le ha.le
    (fun t => by
      rw [← ev_const_mul, ← ev_sub]
      exact ev_mono hM (fun s h => welfare_node_le H hf s h) t s₀ [])
    (fun t => by
      rw [← ev_nextExp]
      exact ev_mono hM (fun s h => nextExp_outGap_le hPW H hp hq hfix hf s h) t s₀ [])
    (by simp [ev, outGap, optY, worldOutput, capIn])
    (fun t => by
      have := ev_mono hM (f := fun _ => -coefK α β)
        (g := capGap AW A As α β Ψ K₀ Ks₀ k ks) (fun s h => by
          obtain ⟨hk, hks, -, -⟩ := hf s h
          have r1 : 0 < capIn K₀ k (s :: h) / optK AW A As α β Ψ K₀ Ks₀ (s :: h) :=
            div_pos hk (opt_pos H (s :: h)).1
          have r2 : 0 < capIn Ks₀ ks (s :: h) / optKs AW A As α β Ψ K₀ Ks₀ (s :: h) :=
            div_pos hks (opt_pos H (s :: h)).2
          simp only [capGap]
          have hΨ := H.Ψ_pos
          have hΨ1 : 0 < 1 - Ψ := by linarith [H.Ψ_lt_one]
          nlinarith [mul_pos hΨ r1, mul_pos hΨ1 r2]) t s₀ []
      rwa [ev_const hM] at this)
    T
  have hsum : ∑ t ∈ range T, β ^ t * ev P (fun l => U l - Uo l) t s₀ [] =
      welfare P AW A As α β κ K₀ Ks₀ k ks c s₀ T -
        welfare P AW A As α β κ K₀ Ks₀ (optK AW A As α β Ψ K₀ Ks₀)
          (optKs AW A As α β Ψ K₀ Ks₀) (optC AW A As α β κ Ψ K₀ Ks₀) s₀ T := by
    simp only [welfare, ← Finset.sum_sub_distrib, ← mul_sub]
    exact Finset.sum_congr rfl fun t _ => by rw [ev_sub]
  linarith


omit [Fintype W] [Fintype I] [Fintype J] in
/-- World output under (115)–(116) at a successor node. -/
theorem optY_cons (AW : W → ℝ) (A : I → ℝ) (As : J → ℝ) (α β Ψ K₀ Ks₀ : ℝ) (s : W × I × J)
    (g : List (W × I × J)) :
    optY AW A As α β Ψ K₀ Ks₀ (s :: g) = AW s.1 * (A s.2.1 * optK AW A As α β Ψ K₀ Ks₀ g ^ α +
      As s.2.2 * optKs AW A As α β Ψ K₀ Ks₀ g ^ α) := by
  simp only [optY, worldOutput, (capIn_opt AW A As α β Ψ K₀ Ks₀ g).1,
    (capIn_opt AW A As α β Ψ K₀ Ks₀ g).2]

omit [Fintype W] [Fintype I] [Fintype J] in
/-- (116): `K′ = Ψ (αβ Y^W)` and `K*′ = (1 − Ψ)(αβ Y^W)`. -/
theorem optK_cons' (AW : W → ℝ) (A : I → ℝ) (As : J → ℝ) (α β Ψ K₀ Ks₀ : ℝ) (s : W × I × J)
    (h : List (W × I × J)) :
    optK AW A As α β Ψ K₀ Ks₀ (s :: h) = Ψ * (α * β * optY AW A As α β Ψ K₀ Ks₀ (s :: h)) ∧
      optKs AW A As α β Ψ K₀ Ks₀ (s :: h) =
        (1 - Ψ) * (α * β * optY AW A As α β Ψ K₀ Ks₀ (s :: h)) := by
  rw [(optCap_cons AW A As α β Ψ K₀ Ks₀ s h).1, (optCap_cons AW A As α β Ψ K₀ Ks₀ s h).2]
  exact ⟨by simp only [optY]; ring, by simp only [optY]; ring⟩

omit [Fintype W] [Fintype I] [Fintype J] in
/-- (115): `C = κ (1 − αβ) Y^W` and `C* = (1 − κ)(1 − αβ) Y^W`. -/
theorem optC_eq (AW : W → ℝ) (A : I → ℝ) (As : J → ℝ) (α β κ Ψ K₀ Ks₀ : ℝ) (s : W × I × J)
    (h : List (W × I × J)) :
    optC AW A As α β κ Ψ K₀ Ks₀ (s :: h) = κ * ((1 - α * β) * optY AW A As α β Ψ K₀ Ks₀ (s :: h))
      ∧ foreignCons AW A As α K₀ Ks₀ (optK AW A As α β Ψ K₀ Ks₀) (optKs AW A As α β Ψ K₀ Ks₀)
        (optC AW A As α β κ Ψ K₀ Ks₀) (s :: h) =
        (1 - κ) * ((1 - α * β) * optY AW A As α β Ψ K₀ Ks₀ (s :: h)) := by
  refine ⟨by simp only [optC, optY]; ring, ?_⟩
  rw [foreignCons_opt]
  simp only [optY]
  ring

omit [Fintype W] [Fintype I] [Fintype J] in
/-- Log world output under (115)–(116) is a log-AR(1):
`log Y°_{t+1} = log(A^W[AΨ^α + A*(1 − Ψ)^α]) + α log(αβ) + α log Y°_t`. -/
theorem log_optY_cons_cons {AW : W → ℝ} {A : I → ℝ} {As : J → ℝ} {α β κ Ψ K₀ Ks₀ : ℝ}
    (H : Assumptions AW A As α β κ Ψ K₀ Ks₀) (s' s : W × I × J) (h : List (W × I × J)) :
    Real.log (optY AW A As α β Ψ K₀ Ks₀ (s' :: s :: h)) =
      Real.log (AW s'.1 * (A s'.2.1 * Ψ ^ α + As s'.2.2 * (1 - Ψ) ^ α)) +
        α * Real.log (α * β) + α * Real.log (optY AW A As α β Ψ K₀ Ks₀ (s :: h)) := by
  have hY : 0 < optY AW A As α β Ψ K₀ Ks₀ (s :: h) := optY_pos H s h
  have hab := H.params.ab_pos
  have hc : 0 < α * β * optY AW A As α β Ψ K₀ Ks₀ (s :: h) := mul_pos hab hY
  have e : optY AW A As α β Ψ K₀ Ks₀ (s' :: s :: h) =
      AW s'.1 * (A s'.2.1 * Ψ ^ α + As s'.2.2 * (1 - Ψ) ^ α) *
        (α * β * optY AW A As α β Ψ K₀ Ks₀ (s :: h)) ^ α := by
    rw [optY_cons, (optK_cons' AW A As α β Ψ K₀ Ks₀ s h).1,
      (optK_cons' AW A As α β Ψ K₀ Ks₀ s h).2,
      Real.mul_rpow H.Ψ_pos.le hc.le, Real.mul_rpow (sub_pos.2 H.Ψ_lt_one).le hc.le]
    ring
  have hz : 0 < AW s'.1 * (A s'.2.1 * Ψ ^ α + As s'.2.2 * (1 - Ψ) ^ α) :=
    mul_pos (H.AW_pos _) (add_pos (mul_pos (H.A_pos _) (Real.rpow_pos_of_pos H.Ψ_pos α))
      (mul_pos (H.As_pos _) (Real.rpow_pos_of_pos (sub_pos.2 H.Ψ_lt_one) α)))
  rw [e, Real.log_mul hz.ne' (Real.rpow_pos_of_pos hc α).ne', Real.log_rpow hc,
    Real.log_mul hab.ne' hY.ne']
  ring

/-- Uniform bound on log world output under (115)–(116). -/
theorem abs_log_optY_le {AW : W → ℝ} {A : I → ℝ} {As : J → ℝ} {α β κ Ψ K₀ Ks₀ : ℝ}
    (H : Assumptions AW A As α β κ Ψ K₀ Ks₀) (h : List (W × I × J)) (s : W × I × J) :
    |Real.log (optY AW A As α β Ψ K₀ Ks₀ (s :: h))| ≤
      ∑ s : W × I × J, |Real.log (optY AW A As α β Ψ K₀ Ks₀ [s])| +
        (|α * Real.log (α * β)| + ∑ s : W × I × J,
          |Real.log (AW s.1 * (A s.2.1 * Ψ ^ α + As s.2.2 * (1 - Ψ) ^ α))|) / (1 - α) := by
  have h1α : 0 < 1 - α := by linarith [H.params.α_lt_one]
  set R := ∑ s : W × I × J, |Real.log (optY AW A As α β Ψ K₀ Ks₀ [s])|
  set Z := ∑ s : W × I × J, |Real.log (AW s.1 * (A s.2.1 * Ψ ^ α + As s.2.2 * (1 - Ψ) ^ α))|
  have hR0 : 0 ≤ R := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hZ0 : 0 ≤ Z := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hB0 : 0 ≤ (|α * Real.log (α * β)| + Z) / (1 - α) :=
    div_nonneg (add_nonneg (abs_nonneg _) hZ0) h1α.le
  induction h generalizing s with
  | nil =>
    have := Finset.single_le_sum (f := fun s : W × I × J =>
      |Real.log (optY AW A As α β Ψ K₀ Ks₀ [s])|) (fun _ _ => abs_nonneg _) (Finset.mem_univ s)
    linarith
  | cons s₁ h ih =>
    rw [log_optY_cons_cons H s s₁ h]
    have hz := Finset.single_le_sum (f := fun s : W × I × J =>
      |Real.log (AW s.1 * (A s.2.1 * Ψ ^ α + As s.2.2 * (1 - Ψ) ^ α))|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ s)
    have hih := mul_le_mul_of_nonneg_left (ih s₁) H.params.α_pos.le
    have hkey : (1 - α) * ((|α * Real.log (α * β)| + Z) / (1 - α)) =
        |α * Real.log (α * β)| + Z := by field_simp
    calc _ ≤ |Real.log (AW s.1 * (A s.2.1 * Ψ ^ α + As s.2.2 * (1 - Ψ) ^ α))| +
          |α * Real.log (α * β)| +
          α * |Real.log (optY AW A As α β Ψ K₀ Ks₀ (s₁ :: h))| := by
          refine (abs_add_le _ _).trans (add_le_add ((abs_add_le _ _)) ?_)
          rw [abs_mul, abs_of_pos H.params.α_pos]
      _ ≤ R + (|α * Real.log (α * β)| + Z) / (1 - α) := by
          nlinarith [H.params.α_pos]

/-- **The optimal world welfare is finite**: along (115)–(116) the expected-utility series
converges absolutely. -/
theorem summable_opt {PW : W → W → ℝ} (hPW : IsMarkov PW) {p : I → ℝ} {q : J → ℝ}
    {AW : W → ℝ} {A : I → ℝ} {As : J → ℝ} {α β κ Ψ K₀ Ks₀ : ℝ}
    (H : Assumptions AW A As α β κ Ψ K₀ Ks₀) (hp : Weights p) (hq : Weights q)
    (s₀ : W × I × J) :
    Summable (fun t => β ^ t * ev (kernel PW p q) (fun l =>
      κ * Real.log (optC AW A As α β κ Ψ K₀ Ks₀ l) +
      (1 - κ) * Real.log (foreignCons AW A As α K₀ Ks₀ (optK AW A As α β Ψ K₀ Ks₀)
        (optKs AW A As α β Ψ K₀ Ks₀) (optC AW A As α β κ Ψ K₀ Ks₀) l)) t s₀ []) := by
  have hM := kernel_isMarkov hPW hp hq
  have hpar := H.params
  have hab := hpar.ab_lt_one
  set M := ∑ s : W × I × J, |Real.log (optY AW A As α β Ψ K₀ Ks₀ [s])| +
    (|α * Real.log (α * β)| + ∑ s : W × I × J,
      |Real.log (AW s.1 * (A s.2.1 * Ψ ^ α + As s.2.2 * (1 - Ψ) ^ α))|) / (1 - α)
  set B := |κ * Real.log κ| + |(1 - κ) * Real.log (1 - κ)| + |Real.log (1 - α * β)| + M
  have hκ := H.κ_pos
  have hκ1 : 0 < 1 - κ := by linarith [H.κ_lt_one]
  have hnode : ∀ s h, |κ * Real.log (optC AW A As α β κ Ψ K₀ Ks₀ (s :: h)) +
      (1 - κ) * Real.log (foreignCons AW A As α K₀ Ks₀ (optK AW A As α β Ψ K₀ Ks₀)
        (optKs AW A As α β Ψ K₀ Ks₀) (optC AW A As α β κ Ψ K₀ Ks₀) (s :: h))| ≤ B := by
    intro s h
    have hY : 0 < optY AW A As α β Ψ K₀ Ks₀ (s :: h) := optY_pos H s h
    have hbd := abs_log_optY_le H h s
    have h1ab : 0 < 1 - α * β := by linarith
    rw [(optC_eq AW A As α β κ Ψ K₀ Ks₀ s h).1, (optC_eq AW A As α β κ Ψ K₀ Ks₀ s h).2]
    rw [Real.log_mul hκ.ne' (mul_pos h1ab hY).ne',
      Real.log_mul hκ1.ne' (mul_pos h1ab hY).ne',
      Real.log_mul h1ab.ne' hY.ne']
    have e3 : κ * (Real.log κ + (Real.log (1 - α * β) +
        Real.log (optY AW A As α β Ψ K₀ Ks₀ (s :: h)))) + (1 - κ) * (Real.log (1 - κ) +
        (Real.log (1 - α * β) + Real.log (optY AW A As α β Ψ K₀ Ks₀ (s :: h)))) =
        κ * Real.log κ + (1 - κ) * Real.log (1 - κ) + Real.log (1 - α * β) +
          Real.log (optY AW A As α β Ψ K₀ Ks₀ (s :: h)) := by ring
    rw [e3]
    refine (abs_add_le _ _).trans ?_
    refine le_trans (add_le_add ((abs_add_le _ _).trans
      (add_le_add (abs_add_le _ _) le_rfl)) hbd) ?_
    simp only [B]
    linarith
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one hpar.β_pos.le hpar.β_lt_one).mul_right B) fun t => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (pow_pos hpar.β_pos t)]
  exact mul_le_mul_of_nonneg_left (abs_ev_le hM hnode t s₀ []) (pow_pos hpar.β_pos t).le

/-- **Infinite-horizon optimality of (115)–(116)**: for every feasible world plan and `ε > 0`,
eventually `welfare_T(rival) ≤ W° + ε`, where `W°` is the (finite) welfare of (115)–(116);
if the rival's welfare series converges, its sum is at most `W°`. -/
theorem opt_is_optimal {PW : W → W → ℝ} (hPW : IsMarkov PW) {p : I → ℝ} {q : J → ℝ}
    {AW : W → ℝ} {A : I → ℝ} {As : J → ℝ} {α β κ Ψ K₀ Ks₀ : ℝ}
    (H : Assumptions AW A As α β κ Ψ K₀ Ks₀) (hp : Weights p) (hq : Weights q)
    (hfix : psiMap α p q A As Ψ = Ψ) {k ks c : List (W × I × J) → ℝ}
    (hf : Feasible AW A As α K₀ Ks₀ k ks c) (s₀ : W × I × J) :
    (∀ ε > 0, ∀ᶠ T in atTop, welfare (kernel PW p q) AW A As α β κ K₀ Ks₀ k ks c s₀ T ≤
      ∑' t, β ^ t * ev (kernel PW p q) (fun l =>
        κ * Real.log (optC AW A As α β κ Ψ K₀ Ks₀ l) +
        (1 - κ) * Real.log (foreignCons AW A As α K₀ Ks₀ (optK AW A As α β Ψ K₀ Ks₀)
          (optKs AW A As α β Ψ K₀ Ks₀) (optC AW A As α β κ Ψ K₀ Ks₀) l)) t s₀ [] + ε) ∧
    (Summable (fun t => β ^ t * ev (kernel PW p q) (fun l => κ * Real.log (c l) +
        (1 - κ) * Real.log (foreignCons AW A As α K₀ Ks₀ k ks c l)) t s₀ []) →
      ∑' t, β ^ t * ev (kernel PW p q) (fun l => κ * Real.log (c l) +
        (1 - κ) * Real.log (foreignCons AW A As α K₀ Ks₀ k ks c l)) t s₀ [] ≤
      ∑' t, β ^ t * ev (kernel PW p q) (fun l =>
        κ * Real.log (optC AW A As α β κ Ψ K₀ Ks₀ l) +
        (1 - κ) * Real.log (foreignCons AW A As α K₀ Ks₀ (optK AW A As α β Ψ K₀ Ks₀)
          (optKs AW A As α β Ψ K₀ Ks₀) (optC AW A As α β κ Ψ K₀ Ks₀) l)) t s₀ []) := by
  have hpar := H.params
  have hopt := (summable_opt hPW H hp hq s₀).hasSum.tendsto_sum_nat
  have h2 := (tendsto_pow_atTop_nhds_zero_of_lt_one hpar.β_pos.le hpar.β_lt_one).const_mul
    (coefK α β)
  rw [mul_zero] at h2
  have h3 := hopt.add h2
  rw [add_zero] at h3
  have hev : ∀ ε > 0, ∀ᶠ T in atTop, welfare (kernel PW p q) AW A As α β κ K₀ Ks₀ k ks c s₀ T ≤
      ∑' t, β ^ t * ev (kernel PW p q) (fun l =>
        κ * Real.log (optC AW A As α β κ Ψ K₀ Ks₀ l) +
        (1 - κ) * Real.log (foreignCons AW A As α K₀ Ks₀ (optK AW A As α β Ψ K₀ Ks₀)
          (optKs AW A As α β Ψ K₀ Ks₀) (optC AW A As α β κ Ψ K₀ Ks₀) l)) t s₀ [] + ε := by
    intro ε hε
    filter_upwards [h3.eventually (gt_mem_nhds (lt_add_of_pos_right _ hε))] with T hT
    have := welfare_le_opt_add hPW H hp hq hfix hf s₀ T
    simp only [welfare] at this ⊢
    linarith
  refine ⟨hev, fun hs => le_of_forall_pos_le_add fun ε hε => ?_⟩
  refine le_of_tendsto hs.hasSum.tendsto_sum_nat ?_
  filter_upwards [hev ε hε] with T hT
  exact hT

/-! ## The four Euler equations -/

omit [Fintype W] [Fintype I] [Fintype J] in
/-- The marginal-utility-weighted return on Home capital at a successor node:
`α A^W A (K′)^{α−1}/C′ = (α/(κ(1 − αβ)K′)) · shareFn α A A* Ψ`. -/
theorem euler_term_home {AW : W → ℝ} {A : I → ℝ} {As : J → ℝ} {α β κ Ψ K₀ Ks₀ : ℝ}
    (H : Assumptions AW A As α β κ Ψ K₀ Ks₀) (s' s : W × I × J) (h : List (W × I × J)) :
    α * AW s'.1 * A s'.2.1 * optK AW A As α β Ψ K₀ Ks₀ (s :: h) ^ (α - 1) /
        optC AW A As α β κ Ψ K₀ Ks₀ (s' :: s :: h) =
      α / (κ * (1 - α * β) * optK AW A As α β Ψ K₀ Ks₀ (s :: h)) *
        shareFn α (A s'.2.1) (As s'.2.2) Ψ := by
  rw [← share_opt H (H.A_pos s'.2.1) (H.As_pos s'.2.2) s h]
  have hk := (opt_pos H (s :: h)).1
  have hks := (opt_pos H (s :: h)).2
  have hab := H.params.ab_lt_one
  simp only [optC, worldOutput, (capIn_opt AW A As α β Ψ K₀ Ks₀ (s :: h)).1,
    (capIn_opt AW A As α β Ψ K₀ Ks₀ (s :: h)).2]
  rw [Real.rpow_sub_one hk.ne']
  have h1 : (1 - α * β) ≠ 0 := by linarith
  have h2 := (H.AW_pos s'.1).ne'
  have h3 := H.κ_pos.ne'
  have h4 := (Real.rpow_pos_of_pos hk α).ne'
  have h5 : A s'.2.1 * optK AW A As α β Ψ K₀ Ks₀ (s :: h) ^ α +
      As s'.2.2 * optKs AW A As α β Ψ K₀ Ks₀ (s :: h) ^ α ≠ 0 :=
    (add_pos (mul_pos (H.A_pos _) (Real.rpow_pos_of_pos hk α))
      (mul_pos (H.As_pos _) (Real.rpow_pos_of_pos hks α))).ne'
  field_simp

/-- **Euler equation for Home capital** (p. 501): along (115)–(116),
`1/C_t = β E_t[α A^W_{t+1} A_{t+1} K_{t+1}^{α−1}/C_{t+1}]` holds at a node **if and only if**
`Ψ = G(Ψ)`. -/
theorem euler_home_iff {PW : W → W → ℝ} (hPW : IsMarkov PW) {p : I → ℝ} {q : J → ℝ}
    {AW : W → ℝ} {A : I → ℝ} {As : J → ℝ} {α β κ Ψ K₀ Ks₀ : ℝ}
    (H : Assumptions AW A As α β κ Ψ K₀ Ks₀)
    (s : W × I × J) (h : List (W × I × J)) :
    1 / optC AW A As α β κ Ψ K₀ Ks₀ (s :: h) = β * ∑ s', kernel PW p q s s' *
      (α * AW s'.1 * A s'.2.1 * optK AW A As α β Ψ K₀ Ks₀ (s :: h) ^ (α - 1) /
        optC AW A As α β κ Ψ K₀ Ks₀ (s' :: s :: h)) ↔ psiMap α p q A As Ψ = Ψ := by
  have e1 : ∑ s', kernel PW p q s s' * shareFn α (A s'.2.1) (As s'.2.2) Ψ =
      psiMap α p q A As Ψ := kernel_expect hPW p q (fun i j => shareFn α (A i) (As j) Ψ) s
  have hsum : ∑ s', kernel PW p q s s' *
      (α * AW s'.1 * A s'.2.1 * optK AW A As α β Ψ K₀ Ks₀ (s :: h) ^ (α - 1) /
        optC AW A As α β κ Ψ K₀ Ks₀ (s' :: s :: h)) =
      α / (κ * (1 - α * β) * optK AW A As α β Ψ K₀ Ks₀ (s :: h)) * psiMap α p q A As Ψ := by
    rw [← e1, Finset.mul_sum]
    exact Finset.sum_congr rfl fun s' _ => by rw [euler_term_home H]; ring
  rw [hsum, (optC_eq AW A As α β κ Ψ K₀ Ks₀ s h).1, (optK_cons' AW A As α β Ψ K₀ Ks₀ s h).1]
  have hY := optY_pos H s h
  have hab := H.params.ab_lt_one
  set Y := optY AW A As α β Ψ K₀ Ks₀ (s :: h)
  have hY' : 0 < Y := hY
  have h1 : (1 - α * β) ≠ 0 := by linarith
  have h3 := H.κ_pos.ne'
  have h5 := H.Ψ_pos.ne'
  have h7 := H.params.α_pos.ne'
  have h8 := H.params.β_pos.ne'
  have e : β * (α / (κ * (1 - α * β) * (Ψ * (α * β * Y))) * psiMap α p q A As Ψ) =
      psiMap α p q A As Ψ / Ψ * (1 / (κ * ((1 - α * β) * Y))) := by
    field_simp
  rw [e]
  have hD : (1 / (κ * ((1 - α * β) * Y))) ≠ 0 := by
    have : 0 < κ * ((1 - α * β) * Y) := mul_pos H.κ_pos (mul_pos (by linarith) hY')
    positivity
  constructor
  · intro heq
    have h2 : psiMap α p q A As Ψ / Ψ = 1 :=
      mul_right_cancel₀ hD (by rw [one_mul]; exact heq.symm)
    rwa [div_eq_one_iff_eq h5] at h2
  · intro hfix
    rw [hfix, div_self h5, one_mul]

omit [Fintype W] [Fintype I] [Fintype J] in
/-- The marginal-utility-weighted return on Foreign capital at a successor node:
`α A^W A* (K*′)^{α−1}/C′ = (α/(κ(1 − αβ)K*′)) · (1 − shareFn α A A* Ψ)`. -/
theorem euler_term_foreign {AW : W → ℝ} {A : I → ℝ} {As : J → ℝ} {α β κ Ψ K₀ Ks₀ : ℝ}
    (H : Assumptions AW A As α β κ Ψ K₀ Ks₀) (s' s : W × I × J) (h : List (W × I × J)) :
    α * AW s'.1 * As s'.2.2 * optKs AW A As α β Ψ K₀ Ks₀ (s :: h) ^ (α - 1) /
        optC AW A As α β κ Ψ K₀ Ks₀ (s' :: s :: h) =
      α / (κ * (1 - α * β) * optKs AW A As α β Ψ K₀ Ks₀ (s :: h)) *
        (1 - shareFn α (A s'.2.1) (As s'.2.2) Ψ) := by
  rw [← share_opt H (H.A_pos s'.2.1) (H.As_pos s'.2.2) s h]
  have hk := (opt_pos H (s :: h)).1
  have hks := (opt_pos H (s :: h)).2
  have hab := H.params.ab_lt_one
  simp only [optC, worldOutput, (capIn_opt AW A As α β Ψ K₀ Ks₀ (s :: h)).1,
    (capIn_opt AW A As α β Ψ K₀ Ks₀ (s :: h)).2]
  rw [Real.rpow_sub_one hks.ne']
  have h1 : (1 - α * β) ≠ 0 := by linarith
  have h2 := (H.AW_pos s'.1).ne'
  have h3 := H.κ_pos.ne'
  have h4 := (Real.rpow_pos_of_pos hks α).ne'
  have h5 : A s'.2.1 * optK AW A As α β Ψ K₀ Ks₀ (s :: h) ^ α +
      As s'.2.2 * optKs AW A As α β Ψ K₀ Ks₀ (s :: h) ^ α ≠ 0 :=
    (add_pos (mul_pos (H.A_pos _) (Real.rpow_pos_of_pos hk α))
      (mul_pos (H.As_pos _) (Real.rpow_pos_of_pos hks α))).ne'
  field_simp
  ring

/-- **Euler equation for Foreign capital** (p. 501): along (115)–(116),
`1/C_t = β E_t[α A^W_{t+1} A*_{t+1} (K*_{t+1})^{α−1}/C_{t+1}]` holds **iff** `Ψ = G(Ψ)`. With
`C*_{t+1}/C*_t = C_{t+1}/C_t` (`consumption_growth_equal`), the Foreign consumer's two Euler
equations are the same two conditions, so all four hold iff `Ψ` is the fixed point. -/
theorem euler_foreign_iff {PW : W → W → ℝ} (hPW : IsMarkov PW) {p : I → ℝ} {q : J → ℝ}
    {AW : W → ℝ} {A : I → ℝ} {As : J → ℝ} {α β κ Ψ K₀ Ks₀ : ℝ}
    (H : Assumptions AW A As α β κ Ψ K₀ Ks₀) (hp : Weights p) (hq : Weights q)
    (s : W × I × J) (h : List (W × I × J)) :
    1 / optC AW A As α β κ Ψ K₀ Ks₀ (s :: h) = β * ∑ s', kernel PW p q s s' *
      (α * AW s'.1 * As s'.2.2 * optKs AW A As α β Ψ K₀ Ks₀ (s :: h) ^ (α - 1) /
        optC AW A As α β κ Ψ K₀ Ks₀ (s' :: s :: h)) ↔ psiMap α p q A As Ψ = Ψ := by
  have hM := kernel_isMarkov hPW hp hq
  have e1 : ∑ s', kernel PW p q s s' * (1 - shareFn α (A s'.2.1) (As s'.2.2) Ψ) =
      1 - psiMap α p q A As Ψ := by
    simp only [mul_sub, mul_one, Finset.sum_sub_distrib, hM.sum_one]
    rw [kernel_expect hPW p q (fun i j => shareFn α (A i) (As j) Ψ) s]
    rfl
  have hsum : ∑ s', kernel PW p q s s' *
      (α * AW s'.1 * As s'.2.2 * optKs AW A As α β Ψ K₀ Ks₀ (s :: h) ^ (α - 1) /
        optC AW A As α β κ Ψ K₀ Ks₀ (s' :: s :: h)) =
      α / (κ * (1 - α * β) * optKs AW A As α β Ψ K₀ Ks₀ (s :: h)) *
        (1 - psiMap α p q A As Ψ) := by
    rw [← e1, Finset.mul_sum]
    exact Finset.sum_congr rfl fun s' _ => by rw [euler_term_foreign H]; ring
  rw [hsum, (optC_eq AW A As α β κ Ψ K₀ Ks₀ s h).1, (optK_cons' AW A As α β Ψ K₀ Ks₀ s h).2]
  have hY := optY_pos H s h
  have hab := H.params.ab_lt_one
  set Y := optY AW A As α β Ψ K₀ Ks₀ (s :: h)
  have hY' : 0 < Y := hY
  have h1 : (1 - α * β) ≠ 0 := by linarith
  have h3 := H.κ_pos.ne'
  have h5 : (1 - Ψ) ≠ 0 := (sub_pos.2 H.Ψ_lt_one).ne'
  have h7 := H.params.α_pos.ne'
  have h8 := H.params.β_pos.ne'
  have e : β * (α / (κ * (1 - α * β) * ((1 - Ψ) * (α * β * Y))) * (1 - psiMap α p q A As Ψ)) =
      (1 - psiMap α p q A As Ψ) / (1 - Ψ) * (1 / (κ * ((1 - α * β) * Y))) := by
    field_simp
  rw [e]
  have hD : (1 / (κ * ((1 - α * β) * Y))) ≠ 0 := by
    have : 0 < κ * ((1 - α * β) * Y) := mul_pos H.κ_pos (mul_pos (by linarith) hY')
    positivity
  constructor
  · intro heq
    have h2 : (1 - psiMap α p q A As Ψ) / (1 - Ψ) = 1 :=
      mul_right_cancel₀ hD (by rw [one_mul]; exact heq.symm)
    rw [div_eq_one_iff_eq h5] at h2
    linarith
  · intro hfix
    rw [hfix, div_self h5, one_mul]

omit [Fintype W] [Fintype I] [Fintype J] in
/-- Complete markets equalise consumption growth (p. 501): `C_{t+1}/C_t = C*_{t+1}/C*_t`. -/
theorem consumption_growth_equal {AW : W → ℝ} {A : I → ℝ} {As : J → ℝ} {α β κ Ψ K₀ Ks₀ : ℝ}
    (H : Assumptions AW A As α β κ Ψ K₀ Ks₀) (s' s : W × I × J) (h : List (W × I × J)) :
    optC AW A As α β κ Ψ K₀ Ks₀ (s' :: s :: h) / optC AW A As α β κ Ψ K₀ Ks₀ (s :: h) =
      foreignCons AW A As α K₀ Ks₀ (optK AW A As α β Ψ K₀ Ks₀) (optKs AW A As α β Ψ K₀ Ks₀)
        (optC AW A As α β κ Ψ K₀ Ks₀) (s' :: s :: h) /
      foreignCons AW A As α K₀ Ks₀ (optK AW A As α β Ψ K₀ Ks₀) (optKs AW A As α β Ψ K₀ Ks₀)
        (optC AW A As α β κ Ψ K₀ Ks₀) (s :: h) := by
  rw [(optC_eq AW A As α β κ Ψ K₀ Ks₀ s' (s :: h)).1, (optC_eq AW A As α β κ Ψ K₀ Ks₀ s h).1,
    (optC_eq AW A As α β κ Ψ K₀ Ks₀ s' (s :: h)).2, (optC_eq AW A As α β κ Ψ K₀ Ks₀ s h).2]
  have hY : 0 < optY AW A As α β Ψ K₀ Ks₀ (s :: h) := optY_pos H s h
  have hab := H.params.ab_lt_one
  have h1 : (1 - α * β) ≠ 0 := by linarith
  have h3 := H.κ_pos.ne'
  have h4 : (1 - κ) ≠ 0 := (sub_pos.2 H.κ_lt_one).ne'
  field_simp

/-- A positive Home productivity disturbance raises investment in **both** countries (p. 501):
`K′ = Ψ αβ Y^W` and `K*′ = (1 − Ψ) αβ Y^W` are strictly increasing in current Home
productivity `A`, holding capital stocks and the other shocks fixed. -/
theorem investment_increasing_in_home_shock {α β Ψ aw b k ks a a' : ℝ} (hp : Params α β)
    (hΨ0 : 0 < Ψ) (hΨ1 : Ψ < 1) (haw : 0 < aw) (hk : 0 < k) (haa : a < a') :
    Ψ * α * β * (aw * (a * k ^ α + b * ks ^ α)) < Ψ * α * β * (aw * (a' * k ^ α + b * ks ^ α)) ∧
      (1 - Ψ) * α * β * (aw * (a * k ^ α + b * ks ^ α)) <
        (1 - Ψ) * α * β * (aw * (a' * k ^ α + b * ks ^ α)) := by
  have hkα := Real.rpow_pos_of_pos hk α
  have h1 : aw * (a * k ^ α + b * ks ^ α) < aw * (a' * k ^ α + b * ks ^ α) := by
    have := mul_lt_mul_of_pos_right haa hkα
    exact mul_lt_mul_of_pos_left (by linarith) haw
  have hα := hp.α_pos
  have hβ := hp.β_pos
  have h1Ψ : 0 < 1 - Ψ := by linarith
  exact ⟨mul_lt_mul_of_pos_left h1 (by positivity), mul_lt_mul_of_pos_left h1 (by positivity)⟩

/-! ## The two-country log-linear model (136) -/

/-- **(136)**, p. 507: the two linearised Euler equations
`E c − c₋₁ = (1 − α)(1 − β)(E e − k)` and `E c − c₋₁ = (1 − α)(1 − β)(E e* − k*)` (common
consumption growth under complete markets) imply `E(e − k) = E(e* − k*)`. -/
theorem eq136 {α β Ec c₀ Ee Ees k ks : ℝ} (hα : α < 1) (hβ : β < 1)
    (hH : Ec - c₀ = (1 - α) * (1 - β) * (Ee - k))
    (hF : Ec - c₀ = (1 - α) * (1 - β) * (Ees - ks)) : Ee - k = Ees - ks := by
  have h : (1 - α) * (1 - β) ≠ 0 := mul_ne_zero (by linarith) (by linarith)
  exact mul_left_cancel₀ h (hH.symm.trans hF)

/-- p. 507: holding global investment constant (symmetric countries, `k + k* = 0` in log
deviations), `k = (E e − E e*)/2`: higher expected Home productivity shifts investment to Home. -/
theorem investment_shift {Ee Ees k ks : ℝ} (h136 : Ee - k = Ees - ks) (hglob : k + ks = 0) :
    k = (Ee - Ees) / 2 := by linarith

end Planner

end ObstfeldRogoff.GlobalGrowth.TwoCountryRBC
