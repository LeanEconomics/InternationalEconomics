/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import InternationalFinancialMarkets.Model
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Fin

/-!
# Aggregation under complete markets

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §5.2.2,
pp. 292–294, footnotes 20–21.

* With complete markets and HARA period utility `u(c) = (a₀ + a₁c)^{1-ρ}/(1 − ρ)` common to
  all agents (common `a₀, a₁, ρ, β`), per-capita consumption satisfies the representative
  agent's Euler equation (39), and per-capita consumption satisfies the per-capita budget
  constraint.
* With distinct CRRA coefficients `ρᵢ`, the geometric means `c̃` of consumption satisfy a
  CRRA Euler equation whose coefficient `ρ̃` is the harmonic mean of the `ρᵢ` (p. 294).
* Footnote 21: with a riskless bond as the only asset, aggregation fails; we give an explicit
  two-agent, two-state log-utility counterexample.
-/

namespace ObstfeldRogoff.InternationalFinancialMarkets.Aggregation

open Finset

variable {ι : Type} [Fintype ι]

/-- The HARA/CRRA Euler equation solved for levels, O&R p. 292: for positive `x₁, x₂, m` and
`ρ ≠ 0`, `x₁^{-ρ} = m x₂^{-ρ}` iff `x₁ = m^{(-ρ)⁻¹} x₂` (raise both sides to `−1/ρ`). -/
theorem euler_level_iff {x1 x2 m ρ : ℝ} (h1 : 0 < x1) (h2 : 0 < x2) (hm : 0 < m)
    (hρ : ρ ≠ 0) : x1 ^ (-ρ) = m * x2 ^ (-ρ) ↔ x1 = m ^ (-ρ)⁻¹ * x2 := by
  have hn : -ρ ≠ 0 := neg_ne_zero.2 hρ
  constructor
  · intro h
    rw [← Real.rpow_rpow_inv h1.le hn, h,
      Real.mul_rpow hm.le (Real.rpow_nonneg h2.le _), Real.rpow_rpow_inv h2.le hn]
  · intro h
    rw [h, Real.mul_rpow (Real.rpow_nonneg hm.le _) h2.le, ← Real.rpow_mul hm.le,
      inv_mul_cancel₀ hn, Real.rpow_one]

/-- The per-capita (arithmetic mean) value `Σᵢ xᵢ / I`, O&R p. 293. -/
noncomputable def perCapita (x : ι → ℝ) : ℝ := (∑ i, x i) / Fintype.card ι

/-- The per-capita value of `a₀ + a₁xᵢ` is `a₀ + a₁` times the per-capita value of `x`. -/
theorem perCapita_affine [Nonempty ι] (a0 a1 : ℝ) (x : ι → ℝ) :
    perCapita (fun i => a0 + a1 * x i) = a0 + a1 * perCapita x := by
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  unfold perCapita
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul]
  field_simp

/-- **HARA aggregation**, O&R (39), p. 293: if every agent `i` has HARA utility with common
`a₀, a₁, ρ ≠ 0, β` and satisfies the state-`s` Euler equation
`(a₀ + a₁c₁ⁱ)^{-ρ} = [β(1 + r)π(s)/p(s)] (a₀ + a₁c₂ⁱ(s))^{-ρ}` (with positive marginal-utility
arguments), then per-capita consumption `c = Σᵢcⁱ/I` satisfies the same Euler equation. -/
theorem hara_aggregation [Nonempty ι] {a0 a1 ρ β r π p : ℝ} {c1 c2 : ι → ℝ} (hρ : ρ ≠ 0)
    (hβ : 0 < β) (hr : 0 < 1 + r) (hπ : 0 < π) (hp : 0 < p)
    (h1 : ∀ i, 0 < a0 + a1 * c1 i) (h2 : ∀ i, 0 < a0 + a1 * c2 i)
    (heuler : ∀ i, (a0 + a1 * c1 i) ^ (-ρ) = β * (1 + r) * π / p * (a0 + a1 * c2 i) ^ (-ρ)) :
    (a0 + a1 * perCapita c1) ^ (-ρ) =
      β * (1 + r) * π / p * (a0 + a1 * perCapita c2) ^ (-ρ) := by
  set m := β * (1 + r) * π / p with hmdef
  have hm : 0 < m := by positivity
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hlev : ∀ i, a0 + a1 * c1 i = m ^ (-ρ)⁻¹ * (a0 + a1 * c2 i) := fun i =>
    (euler_level_iff (h1 i) (h2 i) hm hρ).1 (heuler i)
  have hpos2 : 0 < a0 + a1 * perCapita c2 := by
    rw [← perCapita_affine]
    unfold perCapita
    exact div_pos (Finset.sum_pos (fun i _ => h2 i) Finset.univ_nonempty) hn
  have hpos1 : 0 < a0 + a1 * perCapita c1 := by
    rw [← perCapita_affine]
    unfold perCapita
    exact div_pos (Finset.sum_pos (fun i _ => h1 i) Finset.univ_nonempty) hn
  refine (euler_level_iff hpos1 hpos2 hm hρ).2 ?_
  rw [← perCapita_affine, ← perCapita_affine]
  unfold perCapita
  simp only [hlev]
  rw [← Finset.mul_sum, mul_div_assoc]

/-- **Per-capita budget constraint**, O&R p. 293: budget constraints are linear, so if every
agent satisfies `c₁ⁱ + Σ_s q(s) c₂ⁱ(s) = wⁱ`, per-capita consumption satisfies the budget
constraint with per-capita wealth. -/
theorem perCapita_budget {S : Type} [Fintype S] {q : S → ℝ} {c1 w : ι → ℝ}
    {c2 : ι → S → ℝ} (hb : ∀ i, c1 i + ∑ s, q s * c2 i s = w i) :
    perCapita c1 + ∑ s, q s * perCapita (fun i => c2 i s) = perCapita w := by
  unfold perCapita
  simp only [mul_div_assoc', ← Finset.sum_div, Finset.mul_sum]
  rw [Finset.sum_comm, ← add_div, ← Finset.sum_add_distrib]
  simp only [hb]

/-- The unweighted geometric mean `c̃ = Πᵢ (cⁱ)^{1/I}`, O&R p. 293. -/
noncomputable def geoMean (c : ι → ℝ) : ℝ := ∏ i, c i ^ (1 / (Fintype.card ι : ℝ))

/-- The harmonic mean `ρ̃ = 1/((1/I) Σᵢ 1/ρᵢ)` of risk-aversion coefficients, O&R p. 294. -/
noncomputable def harmonicMean (ρ : ι → ℝ) : ℝ :=
  1 / (1 / (Fintype.card ι : ℝ) * ∑ i, 1 / ρ i)

/-- **Geometric-mean aggregation**, O&R p. 294: if agents have CRRA utility with possibly
distinct `ρᵢ > 0` (common `β`) and all satisfy the state-`s` Euler equation
`q c₁ⁱ^{-ρᵢ} = π β c₂ⁱ^{-ρᵢ}` at the common Arrow–Debreu price `q = p(s)/(1 + r) > 0`, then the
geometric means satisfy `q = π β (c̃₂/c̃₁)^{-ρ̃}` with `ρ̃` the harmonic mean of the `ρᵢ`.
(Verified: the book's formula is correct.) -/
theorem geometric_aggregation [Nonempty ι] {q π β : ℝ} {ρ c1 c2 : ι → ℝ} (hq : 0 < q)
    (hπ : 0 < π) (hβ : 0 < β) (hρ : ∀ i, 0 < ρ i) (h1 : ∀ i, 0 < c1 i) (h2 : ∀ i, 0 < c2 i)
    (heuler : ∀ i, q * c1 i ^ (-ρ i) = π * β * c2 i ^ (-ρ i)) :
    q = π * β * (geoMean c2 / geoMean c1) ^ (-harmonicMean ρ) := by
  set m := π * β / q with hmdef
  have hm : 0 < m := by positivity
  set n : ℝ := (Fintype.card ι : ℝ) with hndef
  have hn : 0 < n := by rw [hndef]; exact_mod_cast Fintype.card_pos
  -- each agent: c₂ⁱ = m^{1/ρᵢ} c₁ⁱ
  have hlev : ∀ i, c2 i = m ^ (1 / ρ i) * c1 i := by
    intro i
    have e : c1 i ^ (-ρ i) = m * c2 i ^ (-ρ i) := by
      rw [hmdef]; field_simp; linarith [heuler i]
    have := (euler_level_iff (h1 i) (h2 i) hm (hρ i).ne').1 e
    rw [this, ← mul_assoc, ← Real.rpow_add hm]
    rw [show 1 / ρ i + (-ρ i)⁻¹ = 0 by field_simp; ring, Real.rpow_zero, one_mul]
  set e : ℝ := 1 / n * ∑ i, 1 / ρ i with hedef
  have he : 0 < e := by
    rw [hedef]
    exact mul_pos (by positivity) (Finset.sum_pos (fun i _ => by have := hρ i; positivity)
      Finset.univ_nonempty)
  have hG1 : 0 < geoMean c1 := by
    unfold geoMean
    exact Finset.prod_pos fun i _ => Real.rpow_pos_of_pos (h1 i) _
  have hG2 : geoMean c2 = m ^ e * geoMean c1 := by
    unfold geoMean
    simp only [hlev]
    simp only [Real.mul_rpow (Real.rpow_nonneg hm.le _) (h1 _).le, Finset.prod_mul_distrib,
      ← Real.rpow_mul hm.le]
    congr 1
    rw [← Real.rpow_sum_of_pos hm, hedef, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring
  have hH : harmonicMean ρ = 1 / e := by unfold harmonicMean; rw [hedef]
  rw [hG2, mul_div_assoc, div_self hG1.ne', mul_one, hH, ← Real.rpow_mul hm.le,
    show e * -(1 / e) = -1 by field_simp, Real.rpow_neg_one, hmdef]
  field_simp

/-! ## Footnote 21: aggregation fails with bonds only -/

/-- The bond Euler equation with log utility (`a₀ = 0`, `a₁ = 1`, `ρ = 1` in (38)) and two
states, O&R footnote 21: `c₁^{-1} = β(1 + r) Σ_s π(s) c₂(s)^{-1}`. -/
def logBondEuler (π : Fin 2 → ℝ) (βR c1 : ℝ) (c2 : Fin 2 → ℝ) : Prop :=
  c1 ^ (-1 : ℝ) = βR * ∑ s, π s * c2 s ^ (-1 : ℝ)

/-- **Aggregation fails with a riskless bond only**, O&R footnote 21, p. 293. Two equally
likely states, `β(1 + r) = 1`, log utility. Agent A consumes `c₁ = 3/2`, `c₂ = (1, 3)`; agent B
consumes `c₁ = 3/2`, `c₂ = (3, 1)`. Both satisfy their bond Euler equations (this is a
bonds-only equilibrium with zero bond trade when endowments equal these consumptions), but
per-capita consumption `c₁ = 3/2`, `c₂ = (2, 2)` violates the bond Euler equation: agents'
marginal rates of substitution between the two states differ. -/
theorem bonds_only_aggregation_fails :
    logBondEuler ![1 / 2, 1 / 2] 1 (3 / 2) ![1, 3] ∧
      logBondEuler ![1 / 2, 1 / 2] 1 (3 / 2) ![3, 1] ∧
      ¬ logBondEuler ![1 / 2, 1 / 2] 1 ((3 / 2 + 3 / 2) / 2)
        (fun s => (![1, 3] s + ![3, 1] s) / 2) := by
  unfold logBondEuler
  simp only [Real.rpow_neg_one, Fin.sum_univ_two]
  norm_num

end ObstfeldRogoff.InternationalFinancialMarkets.Aggregation
