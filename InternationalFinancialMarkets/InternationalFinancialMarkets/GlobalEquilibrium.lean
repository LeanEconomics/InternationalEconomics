/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import InternationalFinancialMarkets.Probability
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# A global complete-markets equilibrium

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §5.2,
pp. 285–299, and Exercise 2, p. 345.

Two countries, Home and Foreign, trade a complete set of Arrow–Debreu securities on date 1
for the `S` states of date 2. Both have CRRA period utility with the same coefficient `ρ`
and discount factor `β`. We write `q(s) = p(s)/(1 + r)` for the date-1 price of the state-`s`
security, so the Euler equation (5) is `q(s) C₁^{-ρ} = π(s) β C₂(s)^{-ρ}`.

Main results:
* equilibrium prices (30), (31), (32) and the world interest rate (33);
* prices are actuarially fair iff world date-2 output is state-independent (p. 287);
* constant consumption shares (35)–(36), equal consumption growth across countries, and the
  closed form for Home's share `μ` (footnote 16);
* the planner weights `κ = μ^ρ/(μ^ρ + (1 − μ)^ρ)` of footnote 17: the first-order conditions
  and global optimality (via the tangent-line inequality for CRRA utility);
* different `ρ`, `β` across countries: equation (37) and perfect correlation of consumption
  growth (footnote 18);
* efficient investment (40)–(41) and the log/linear example `K₂ + K₂* = βY₁ᵂ/(1 + β)`
  (§5.2.4.1);
* Exercise 2 (log date-1, linear date-2 utility).
-/

namespace ObstfeldRogoff.InternationalFinancialMarkets.GlobalEquilibrium

open Finset StateSpace

variable {S : Type} [Fintype S]

/-! ## Two CRRA facts -/

/-- CRRA Euler equation in ratio form, O&R (5) with `u′(C) = C^{-ρ}`, p. 286:
`q C₁^{-ρ} = π β C₂^{-ρ}` iff `q = π β (C₂/C₁)^{-ρ}`. -/
theorem crra_euler_iff {q π β ρ C1 C2 : ℝ} (h1 : 0 < C1) (h2 : 0 < C2) :
    q * C1 ^ (-ρ) = π * β * C2 ^ (-ρ) ↔ q = π * β * (C2 / C1) ^ (-ρ) := by
  have hp : 0 < C1 ^ (-ρ) := Real.rpow_pos_of_pos h1 _
  rw [Real.div_rpow h2.le h1.le]
  constructor
  · intro h; field_simp; linarith
  · intro h; rw [h]; field_simp

/-- The map `x ↦ x^{-ρ}` is injective on positive reals when `ρ ≠ 0` (used for p. 287). -/
theorem rpow_neg_inj {x y ρ : ℝ} (hx : 0 < x) (hy : 0 < y) (hρ : ρ ≠ 0)
    (h : x ^ (-ρ) = y ^ (-ρ)) : x = y := by
  have hn : -ρ ≠ 0 := neg_ne_zero.2 hρ
  rw [← Real.rpow_rpow_inv hx.le hn, ← Real.rpow_rpow_inv hy.le hn, h]

/-! ## The two-country CRRA equilibrium (§5.2.1) -/

/-- A two-country complete-markets equilibrium with common CRRA utility, O&R §5.2.1,
pp. 286–289: Euler equations (5) for Home and Foreign at common Arrow–Debreu prices
`p(s)/(1 + r)`, market clearing (28)–(29), the no-arbitrage condition `Σ p(s) = 1` (7) and
Home's intertemporal budget constraint (18). States have positive probability and all
consumption levels are positive (interiority, implicit in the book). -/
structure GlobalEqm (S : Type) [Fintype S] where
  Ω : StateSpace S
  β : ℝ
  ρ : ℝ
  r : ℝ
  p : S → ℝ
  Y1 : ℝ
  Y1f : ℝ
  Y2 : S → ℝ
  Y2f : S → ℝ
  C1 : ℝ
  C1f : ℝ
  C2 : S → ℝ
  C2f : S → ℝ
  prob_pos : ∀ s, 0 < Ω.prob s
  beta_pos : 0 < β
  rho_pos : 0 < ρ
  gross_pos : 0 < 1 + r
  C1_pos : 0 < C1
  C1f_pos : 0 < C1f
  C2_pos : ∀ s, 0 < C2 s
  C2f_pos : ∀ s, 0 < C2f s
  euler : ∀ s, p s / (1 + r) * C1 ^ (-ρ) = Ω.prob s * β * C2 s ^ (-ρ)
  euler_f : ∀ s, p s / (1 + r) * C1f ^ (-ρ) = Ω.prob s * β * C2f s ^ (-ρ)
  clear1 : C1 + C1f = Y1 + Y1f
  clear2 : ∀ s, C2 s + C2f s = Y2 s + Y2f s
  price_sum : ∑ s, p s = 1
  budget : C1 + ∑ s, p s / (1 + r) * C2 s = Y1 + ∑ s, p s / (1 + r) * Y2 s

namespace GlobalEqm

variable (E : GlobalEqm S)

/-- World date-1 output `Y₁ᵂ = Y₁ + Y₁*`, O&R p. 286. -/
def worldY1 : ℝ := E.Y1 + E.Y1f

/-- World date-2 output `Y₂ᵂ(s) = Y₂(s) + Y₂*(s)`, O&R p. 286. -/
def worldY2 (s : S) : ℝ := E.Y2 s + E.Y2f s

/-- World date-1 output is positive (it equals total positive consumption). -/
theorem worldY1_pos : 0 < E.worldY1 := by
  unfold worldY1; rw [← E.clear1]; linarith [E.C1_pos, E.C1f_pos]

/-- World date-2 output is positive in every state. -/
theorem worldY2_pos (s : S) : 0 < E.worldY2 s := by
  unfold worldY2; rw [← E.clear2 s]; linarith [E.C2_pos s, E.C2f_pos s]

/-- Home and Foreign consumption growth are equal state by state, O&R (36), p. 288:
`C₂(s)/C₁ = C₂*(s)/C₁*`. -/
theorem growth_eq (s : S) : E.C2 s / E.C1 = E.C2f s / E.C1f := by
  have h1 := (crra_euler_iff E.C1_pos (E.C2_pos s)).1 (E.euler s)
  have h2 := (crra_euler_iff E.C1f_pos (E.C2f_pos s)).1 (E.euler_f s)
  have hπβ : 0 < E.Ω.prob s * E.β := mul_pos (E.prob_pos s) E.beta_pos
  have h : (E.C2 s / E.C1) ^ (-E.ρ) = (E.C2f s / E.C1f) ^ (-E.ρ) := by
    have := h1.symm.trans h2
    exact mul_left_cancel₀ hπβ.ne' this
  exact rpow_neg_inj (div_pos (E.C2_pos s) E.C1_pos) (div_pos (E.C2f_pos s) E.C1f_pos)
    E.rho_pos.ne' h

/-- Consumption growth equals world output growth, O&R (36), p. 288:
`C₂(s)/C₁ = Y₂ᵂ(s)/Y₁ᵂ`. -/
theorem growth_eq_world (s : S) : E.C2 s / E.C1 = E.worldY2 s / E.worldY1 := by
  have h := E.growth_eq s
  have h1 := E.C1_pos; have h1f := E.C1f_pos
  unfold worldY1 worldY2
  rw [← E.clear1, ← E.clear2 s]
  rw [div_eq_div_iff h1.ne' h1f.ne'] at h
  rw [div_eq_div_iff h1.ne' (by linarith)]
  linarith

/-- **Equilibrium Arrow–Debreu prices**, O&R (30), p. 286:
`p(s)/(1 + r) = π(s) β [Y₂ᵂ(s)/Y₁ᵂ]^{-ρ}`. -/
theorem ad_price (s : S) :
    E.p s / (1 + E.r) = E.Ω.prob s * E.β * (E.worldY2 s / E.worldY1) ^ (-E.ρ) := by
  rw [← E.growth_eq_world s]
  exact (crra_euler_iff E.C1_pos (E.C2_pos s)).1 (E.euler s)

/-- The price in the form `p(s) = (1 + r) β (Y₁ᵂ)^ρ π(s) Y₂ᵂ(s)^{-ρ}` (step towards (32)). -/
theorem price_expand (s : S) :
    E.p s = (1 + E.r) * E.β * E.worldY1 ^ E.ρ *
      (E.Ω.prob s * E.worldY2 s ^ (-E.ρ)) := by
  have h := E.ad_price s
  rw [Real.div_rpow (E.worldY2_pos s).le E.worldY1_pos.le, Real.rpow_neg E.worldY1_pos.le]
    at h
  have hg := E.gross_pos
  have hY : 0 < E.worldY1 ^ E.ρ := Real.rpow_pos_of_pos E.worldY1_pos _
  field_simp at h
  rw [h]; ring

/-- Relative prices of two contingent claims, O&R (31), p. 287:
`p(s)/p(s′) = [Y₂ᵂ(s)/Y₂ᵂ(s′)]^{-ρ} · π(s)/π(s′)`. -/
theorem price_ratio (s s' : S) :
    E.p s / E.p s' = (E.worldY2 s / E.worldY2 s') ^ (-E.ρ) * (E.Ω.prob s / E.Ω.prob s') := by
  rw [E.price_expand s, E.price_expand s',
    Real.div_rpow (E.worldY2_pos s).le (E.worldY2_pos s').le]
  have := E.gross_pos; have := E.beta_pos; have := E.prob_pos s'
  have : 0 < E.worldY1 ^ E.ρ := Real.rpow_pos_of_pos E.worldY1_pos _
  have : 0 < E.worldY2 s' ^ (-E.ρ) := Real.rpow_pos_of_pos (E.worldY2_pos s') _
  field_simp

/-- The normalising sum `Σ π(s) Y₂ᵂ(s)^{-ρ}` of (32)–(33) is positive. -/
theorem kernel_sum_pos : 0 < ∑ s, E.Ω.prob s * E.worldY2 s ^ (-E.ρ) := by
  have hne : (Finset.univ : Finset S).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have := E.price_sum; rw [h, Finset.sum_empty] at this; exact zero_ne_one this
  exact Finset.sum_pos (fun s _ => mul_pos (E.prob_pos s)
    (Real.rpow_pos_of_pos (E.worldY2_pos s) _)) hne

/-- The normalisation from `Σ p(s) = 1`: `(1 + r) β (Y₁ᵂ)^ρ Σ π Y₂ᵂ^{-ρ} = 1`. -/
theorem normalisation :
    (1 + E.r) * E.β * E.worldY1 ^ E.ρ *
      ∑ s, E.Ω.prob s * E.worldY2 s ^ (-E.ρ) = 1 := by
  calc _ = ∑ s, E.p s := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun s _ => (E.price_expand s).symm
    _ = 1 := E.price_sum

/-- **Date-2 prices**, O&R (32), p. 287:
`p(s) = π(s) Y₂ᵂ(s)^{-ρ} / Σ_{s′} π(s′) Y₂ᵂ(s′)^{-ρ}`. -/
theorem price_formula (s : S) :
    E.p s = E.Ω.prob s * E.worldY2 s ^ (-E.ρ) /
      ∑ s', E.Ω.prob s' * E.worldY2 s' ^ (-E.ρ) := by
  have hK := E.kernel_sum_pos
  have hn := E.normalisation
  rw [eq_div_iff hK.ne', E.price_expand s]
  calc (1 + E.r) * E.β * E.worldY1 ^ E.ρ * (E.Ω.prob s * E.worldY2 s ^ (-E.ρ)) *
        ∑ s', E.Ω.prob s' * E.worldY2 s' ^ (-E.ρ)
      = ((1 + E.r) * E.β * E.worldY1 ^ E.ρ * ∑ s', E.Ω.prob s' * E.worldY2 s' ^ (-E.ρ)) *
        (E.Ω.prob s * E.worldY2 s ^ (-E.ρ)) := by ring
    _ = _ := by rw [hn, one_mul]

/-- **The world interest rate**, O&R (33), p. 287:
`1 + r = (Y₁ᵂ)^{-ρ} / (β Σ π(s) Y₂ᵂ(s)^{-ρ})`. -/
theorem interest_formula :
    1 + E.r = E.worldY1 ^ (-E.ρ) / (E.β * ∑ s, E.Ω.prob s * E.worldY2 s ^ (-E.ρ)) := by
  have hK := E.kernel_sum_pos
  have hn := E.normalisation
  have hb := E.beta_pos
  have hY : 0 < E.worldY1 ^ E.ρ := Real.rpow_pos_of_pos E.worldY1_pos _
  rw [Real.rpow_neg E.worldY1_pos.le, eq_div_iff (by positivity)]
  field_simp
  linarith

/-- **Actuarially fair prices iff no aggregate risk**, O&R p. 287: for `ρ > 0` and positive
state probabilities, `p(s) = π(s)` for every state iff world date-2 output is the same in
all states. -/
theorem fair_iff_no_aggregate_risk :
    (∀ s, E.p s = E.Ω.prob s) ↔ ∀ s s', E.worldY2 s = E.worldY2 s' := by
  have hK := E.kernel_sum_pos
  constructor
  · intro h
    -- every `Y₂ᵂ(s)^{-ρ}` equals the normalising sum
    have key : ∀ s, E.worldY2 s ^ (-E.ρ) = ∑ s', E.Ω.prob s' * E.worldY2 s' ^ (-E.ρ) := by
      intro s
      have h1 := E.price_formula s
      rw [h s, eq_div_iff hK.ne'] at h1
      have hp := E.prob_pos s
      nlinarith [mul_left_cancel₀ hp.ne' (show E.Ω.prob s *
        (∑ s', E.Ω.prob s' * E.worldY2 s' ^ (-E.ρ)) =
          E.Ω.prob s * E.worldY2 s ^ (-E.ρ) by linarith)]
    intro s s'
    exact rpow_neg_inj (E.worldY2_pos s) (E.worldY2_pos s') E.rho_pos.ne'
      ((key s).trans (key s').symm)
  · intro h s
    rw [E.price_formula s]
    obtain ⟨s0⟩ : Nonempty S := ⟨s⟩
    have hc : ∀ s', E.worldY2 s' ^ (-E.ρ) = E.worldY2 s0 ^ (-E.ρ) := fun s' => by rw [h s' s0]
    simp only [hc]
    rw [← Finset.sum_mul, E.Ω.prob_sum, one_mul]
    have : 0 < E.worldY2 s0 ^ (-E.ρ) := Real.rpow_pos_of_pos (E.worldY2_pos s0) _
    field_simp

/-- Home's consumption share `μ = C₁/Y₁ᵂ`, O&R p. 288. -/
noncomputable def share : ℝ := E.C1 / E.worldY1

/-- The share lies strictly between zero and one. -/
theorem share_mem : 0 < E.share ∧ E.share < 1 := by
  have h1 := E.C1_pos; have h2 := E.C1f_pos; have hY := E.worldY1_pos
  unfold share
  refine ⟨div_pos h1 hY, (div_lt_one hY).2 ?_⟩
  unfold worldY1; rw [← E.clear1]; linarith

/-- Home date-1 consumption is the share `μ` of world output, O&R p. 289. -/
theorem C1_eq : E.C1 = E.share * E.worldY1 := by
  unfold share; field_simp [E.worldY1_pos.ne']

/-- Foreign date-1 consumption is the share `1 − μ` of world output, O&R p. 289. -/
theorem C1f_eq : E.C1f = (1 - E.share) * E.worldY1 := by
  have h := E.C1_eq
  have hc : E.C1 + E.C1f = E.worldY1 := E.clear1
  linarith [show (1 - E.share) * E.worldY1 = E.worldY1 - E.share * E.worldY1 by ring]

/-- **Constant consumption shares**, O&R (35)–(36), p. 288–289: Home consumes the same
fraction `μ` of world output in every state of date 2 as on date 1. -/
theorem C2_eq (s : S) : E.C2 s = E.share * E.worldY2 s := by
  have h := E.growth_eq_world s
  have h1 := E.C1_pos; have hY := E.worldY1_pos
  unfold share
  rw [div_eq_div_iff h1.ne' hY.ne'] at h
  field_simp
  linarith

/-- Foreign consumes the constant fraction `1 − μ` of world date-2 output, O&R p. 289. -/
theorem C2f_eq (s : S) : E.C2f s = (1 - E.share) * E.worldY2 s := by
  have h := E.C2_eq s
  have hc : E.C2 s + E.C2f s = E.worldY2 s := E.clear2 s
  linarith [show (1 - E.share) * E.worldY2 s = E.worldY2 s - E.share * E.worldY2 s by ring]

/-- Equation (35), p. 288, in the book's form: `C₂(s)/C₂(s′) = C₂*(s)/C₂*(s′) =
Y₂ᵂ(s)/Y₂ᵂ(s′)`. -/
theorem consumption_ratio_across_states (s s' : S) :
    E.C2 s / E.C2 s' = E.worldY2 s / E.worldY2 s' ∧
      E.C2f s / E.C2f s' = E.worldY2 s / E.worldY2 s' := by
  obtain ⟨h0, h1⟩ := E.share_mem
  have : 0 < 1 - E.share := by linarith
  rw [E.C2_eq, E.C2_eq, E.C2f_eq, E.C2f_eq]
  constructor
  · rw [mul_div_mul_left _ _ h0.ne']
  · rw [mul_div_mul_left _ _ this.ne']

/-- The date-1 Arrow–Debreu price in the form `q(s) = β (Y₁ᵂ)^ρ π(s) Y₂ᵂ(s)^{-ρ}`. -/
theorem ad_price_expand (s : S) :
    E.p s / (1 + E.r) = E.β * E.worldY1 ^ E.ρ * (E.Ω.prob s * E.worldY2 s ^ (-E.ρ)) := by
  rw [E.price_expand s]; field_simp [E.gross_pos.ne']

/-- **Home's share is its share of world wealth at Arrow–Debreu prices**, O&R p. 289 and
footnote 16: `μ = (Y₁ + Σ q(s) Y₂(s)) / (Y₁ᵂ + Σ q(s) Y₂ᵂ(s))`, `q(s) = p(s)/(1 + r)`. -/
theorem share_eq_wealth_share :
    E.share = (E.Y1 + ∑ s, E.p s / (1 + E.r) * E.Y2 s) /
      (E.worldY1 + ∑ s, E.p s / (1 + E.r) * E.worldY2 s) := by
  have hq : ∀ s, 0 < E.p s / (1 + E.r) := fun s => by
    rw [E.ad_price_expand s]
    have := Real.rpow_pos_of_pos E.worldY1_pos E.ρ
    have := Real.rpow_pos_of_pos (E.worldY2_pos s) (-E.ρ)
    have := E.prob_pos s; have := E.beta_pos
    positivity
  have hD : 0 < E.worldY1 + ∑ s, E.p s / (1 + E.r) * E.worldY2 s := by
    have := E.worldY1_pos
    have := Finset.sum_nonneg (fun s (_ : s ∈ Finset.univ) =>
      (mul_pos (hq s) (E.worldY2_pos s)).le)
    linarith
  rw [eq_div_iff hD.ne', ← E.budget, E.C1_eq]
  simp only [E.C2_eq]
  have e : ∀ s, E.p s / (1 + E.r) * (E.share * E.worldY2 s) =
      E.share * (E.p s / (1 + E.r) * E.worldY2 s) := fun s => by ring
  simp only [e, ← Finset.mul_sum]
  ring

/-- **Closed form for the consumption share**, O&R footnote 16, p. 289:
`μ = [Y₁(Y₁ᵂ)^{-ρ} + β Σ π(s) Y₂(s) Y₂ᵂ(s)^{-ρ}] / [(Y₁ᵂ)^{1-ρ} + β Σ π(s) Y₂ᵂ(s)^{1-ρ}]`. -/
theorem share_closed_form :
    E.share = (E.Y1 * E.worldY1 ^ (-E.ρ) +
        E.β * ∑ s, E.Ω.prob s * E.Y2 s * E.worldY2 s ^ (-E.ρ)) /
      (E.worldY1 ^ (1 - E.ρ) + E.β * ∑ s, E.Ω.prob s * E.worldY2 s ^ (1 - E.ρ)) := by
  rw [E.share_eq_wealth_share]
  simp only [E.ad_price_expand]
  have hY := E.worldY1_pos
  have hA : 0 < E.worldY1 ^ E.ρ := Real.rpow_pos_of_pos hY _
  have hAi : E.worldY1 ^ (-E.ρ) = (E.worldY1 ^ E.ρ)⁻¹ := Real.rpow_neg hY.le _
  have h1 : E.worldY1 ^ (1 - E.ρ) = E.worldY1 * (E.worldY1 ^ E.ρ)⁻¹ := by
    rw [sub_eq_add_neg, Real.rpow_add hY, Real.rpow_one, hAi]
  have h2 : ∀ s, E.worldY2 s ^ (1 - E.ρ) = E.worldY2 s * E.worldY2 s ^ (-E.ρ) := fun s => by
    rw [sub_eq_add_neg, Real.rpow_add (E.worldY2_pos s), Real.rpow_one]
  simp only [h2]
  rw [hAi, h1]
  have eN : E.Y1 + ∑ s, E.β * E.worldY1 ^ E.ρ *
      (E.Ω.prob s * E.worldY2 s ^ (-E.ρ)) * E.Y2 s =
      E.worldY1 ^ E.ρ * (E.Y1 * (E.worldY1 ^ E.ρ)⁻¹ +
        E.β * ∑ s, E.Ω.prob s * E.Y2 s * E.worldY2 s ^ (-E.ρ)) := by
    rw [mul_add, Finset.mul_sum, Finset.mul_sum]
    congr 1
    · field_simp
    · exact Finset.sum_congr rfl fun s _ => by ring
  have eD : E.worldY1 + ∑ s, E.β * E.worldY1 ^ E.ρ *
      (E.Ω.prob s * E.worldY2 s ^ (-E.ρ)) * E.worldY2 s =
      E.worldY1 ^ E.ρ * (E.worldY1 * (E.worldY1 ^ E.ρ)⁻¹ +
        E.β * ∑ s, E.Ω.prob s * (E.worldY2 s * E.worldY2 s ^ (-E.ρ))) := by
    rw [mul_add, Finset.mul_sum, Finset.mul_sum]
    congr 1
    · field_simp
    · exact Finset.sum_congr rfl fun s _ => by ring
  rw [eN, eD, mul_div_mul_left _ _ hA.ne']

end GlobalEqm

/-! ## The social planner (footnote 17) -/

/-- CRRA period utility `u(C) = C^{1-ρ}/(1 − ρ)`, O&R (13), p. 277 (for `ρ ≠ 1`). -/
noncomputable def crraU (ρ c : ℝ) : ℝ := c ^ (1 - ρ) / (1 - ρ)

/-- Normalised tangent-line inequality for powers: for `y > 0`, `t < 1`, `t ≠ 0`,
`(y^t − 1)/t ≤ y − 1` (Bernoulli for `0 < t < 1`, weighted AM–GM for `t < 0`). Used for
the concavity argument behind O&R footnote 17. -/
theorem pow_tangent {t y : ℝ} (ht1 : t < 1) (ht0 : t ≠ 0) (hy : 0 < y) :
    (y ^ t - 1) / t ≤ y - 1 := by
  rcases lt_or_gt_of_ne ht0 with ht | ht
  · rw [div_le_iff_of_neg ht]
    have hw1 : 0 ≤ 1 / (1 - t) := by apply div_nonneg <;> linarith
    have hw2 : 0 ≤ -t / (1 - t) := by apply div_nonneg <;> linarith
    have hne : 1 - t ≠ 0 := by linarith
    have hw : 1 / (1 - t) + -t / (1 - t) = 1 := by field_simp; ring
    have h := Real.geom_mean_le_arith_mean2_weighted hw1 hw2
      (Real.rpow_nonneg hy.le t) hy.le hw
    rw [← Real.rpow_mul hy.le, ← Real.rpow_add hy,
      show t * (1 / (1 - t)) + -t / (1 - t) = 0 by field_simp; ring, Real.rpow_zero] at h
    have h' : 1 - t ≤ y ^ t - t * y := by
      have hpos : 0 < 1 - t := by linarith
      have := mul_le_mul_of_nonneg_left h hpos.le
      have e : (1 - t) * (1 / (1 - t) * y ^ t + -t / (1 - t) * y) = y ^ t - t * y := by
        field_simp; ring
      linarith
    linarith
  · rw [div_le_iff₀ ht]
    have h := rpow_one_add_le_one_add_mul_self (s := y - 1) (by linarith) ht.le ht1.le
    rw [show 1 + (y - 1) = y by ring] at h
    linarith

/-- **CRRA utility lies below its tangent**: for `ρ > 0`, `ρ ≠ 1`, `a, x > 0`,
`u(x) ≤ u(a) + a^{-ρ}(x − a)` (concavity of CRRA utility, used for footnote 17). -/
theorem crraU_le_tangent {ρ a x : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≠ 1) (ha : 0 < a) (hx : 0 < x) :
    crraU ρ x ≤ crraU ρ a + a ^ (-ρ) * (x - a) := by
  have ht1 : 1 - ρ < 1 := by linarith
  have ht0 : 1 - ρ ≠ 0 := sub_ne_zero.2 (Ne.symm hρ1)
  have hy : 0 < x / a := div_pos hx ha
  have key := pow_tangent ht1 ht0 hy
  have hA : 0 < a ^ (1 - ρ) := Real.rpow_pos_of_pos ha _
  have hxa : x ^ (1 - ρ) = a ^ (1 - ρ) * (x / a) ^ (1 - ρ) := by
    rw [← Real.mul_rpow ha.le hy.le, mul_div_cancel₀ _ ha.ne']
  have hat : a ^ (-ρ) = a ^ (1 - ρ) / a := by
    rw [show -ρ = (1 - ρ) - 1 by ring]; exact Real.rpow_sub_one ha.ne' _
  unfold crraU
  rw [hxa, hat]
  have e1 : a ^ (1 - ρ) * (x / a) ^ (1 - ρ) / (1 - ρ) =
      a ^ (1 - ρ) / (1 - ρ) + a ^ (1 - ρ) * (((x / a) ^ (1 - ρ) - 1) / (1 - ρ)) := by
    field_simp; ring
  have e2 : a ^ (1 - ρ) / a * (x - a) = a ^ (1 - ρ) * (x / a - 1) := by
    field_simp
  rw [e1, e2]
  have := mul_le_mul_of_nonneg_left key hA.le
  linarith

/-- One pooling step of the planner problem: if `κ a^{-ρ} = (1 − κ) a*^{-ρ}` (equal weighted
marginal utilities) and `d + d* = a + a*`, then `κu(d) + (1−κ)u(d*) ≤ κu(a) + (1−κ)u(a*)`. -/
theorem planner_pair_le {ρ κ a af d df : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≠ 1) (hκ0 : 0 ≤ κ)
    (hκ1 : κ ≤ 1) (ha : 0 < a) (haf : 0 < af) (hd : 0 < d) (hdf : 0 < df)
    (hfoc : κ * a ^ (-ρ) = (1 - κ) * af ^ (-ρ)) (hfeas : d + df = a + af) :
    κ * crraU ρ d + (1 - κ) * crraU ρ df ≤ κ * crraU ρ a + (1 - κ) * crraU ρ af := by
  have h1 := mul_le_mul_of_nonneg_left (crraU_le_tangent hρ0 hρ1 ha hd) hκ0
  have h2 := mul_le_mul_of_nonneg_left (crraU_le_tangent hρ0 hρ1 haf hdf)
    (by linarith : (0 : ℝ) ≤ 1 - κ)
  have e : κ * (a ^ (-ρ) * (d - a)) + (1 - κ) * (af ^ (-ρ) * (df - af)) = 0 := by
    have : df - af = -(d - a) := by linarith
    rw [this]
    linear_combination (d - a) * hfoc
  nlinarith

/-- The planner's weight on Home, O&R footnote 17, p. 289: `κ = μ^ρ/(μ^ρ + (1 − μ)^ρ)`. -/
noncomputable def plannerWeight (ρ μ : ℝ) : ℝ := μ ^ ρ / (μ ^ ρ + (1 - μ) ^ ρ)

/-- The planner weight lies in `(0, 1)` for `0 < μ < 1`. -/
theorem plannerWeight_mem {ρ μ : ℝ} (h0 : 0 < μ) (h1 : μ < 1) :
    0 < plannerWeight ρ μ ∧ plannerWeight ρ μ < 1 := by
  have a : 0 < μ ^ ρ := Real.rpow_pos_of_pos h0 _
  have b : 0 < (1 - μ) ^ ρ := Real.rpow_pos_of_pos (by linarith) _
  unfold plannerWeight
  exact ⟨div_pos a (by linarith), (div_lt_one (by linarith)).2 (by linarith)⟩

/-- **Planner first-order condition**, O&R footnote 17: with `κ = μ^ρ/(μ^ρ + (1−μ)^ρ)`,
constant shares `μ`, `1 − μ` of any positive output `Y` equate weighted marginal utilities:
`κ(μY)^{-ρ} = (1 − κ)((1 − μ)Y)^{-ρ}`. -/
theorem planner_foc {ρ μ Y : ℝ} (h0 : 0 < μ) (h1 : μ < 1) (hY : 0 < Y) :
    plannerWeight ρ μ * (μ * Y) ^ (-ρ) = (1 - plannerWeight ρ μ) * ((1 - μ) * Y) ^ (-ρ) := by
  have h1' : 0 < 1 - μ := by linarith
  have a : 0 < μ ^ ρ := Real.rpow_pos_of_pos h0 _
  have b : 0 < (1 - μ) ^ ρ := Real.rpow_pos_of_pos h1' _
  rw [Real.mul_rpow h0.le hY.le, Real.mul_rpow h1'.le hY.le, Real.rpow_neg h0.le,
    Real.rpow_neg h1'.le]
  unfold plannerWeight
  field_simp
  ring

/-- The utilitarian objective `κU + (1 − κ)U*`, O&R footnote 17, with
`U = u(C₁) + β E u(C₂)` and CRRA `u`. -/
noncomputable def socialWelfare (Ω : StateSpace S) (β ρ κ D1 D1f : ℝ) (D2 D2f : S → ℝ) : ℝ :=
  κ * (crraU ρ D1 + β * Ω.expect (fun s => crraU ρ (D2 s))) +
    (1 - κ) * (crraU ρ D1f + β * Ω.expect (fun s => crraU ρ (D2f s)))

/-- Social welfare regrouped date by date and state by state. -/
theorem socialWelfare_eq (Ω : StateSpace S) (β ρ κ D1 D1f : ℝ) (D2 D2f : S → ℝ) :
    socialWelfare Ω β ρ κ D1 D1f D2 D2f =
      (κ * crraU ρ D1 + (1 - κ) * crraU ρ D1f) +
        β * ∑ s, Ω.prob s * (κ * crraU ρ (D2 s) + (1 - κ) * crraU ρ (D2f s)) := by
  unfold socialWelfare StateSpace.expect
  simp only [mul_add, Finset.mul_sum, Finset.sum_add_distrib]
  have e1 : ∀ s, β * (Ω.prob s * (κ * crraU ρ (D2 s))) = κ * (β * (Ω.prob s * crraU ρ (D2 s))) :=
    fun s => by ring
  have e2 : ∀ s, β * (Ω.prob s * ((1 - κ) * crraU ρ (D2f s))) =
      (1 - κ) * (β * (Ω.prob s * crraU ρ (D2f s))) := fun s => by ring
  simp only [e1, e2]
  ring

namespace GlobalEqm

variable (E : GlobalEqm S)

/-- **The equilibrium is the planner's optimum**, O&R footnote 17, p. 289: with CRRA utility
(`ρ ≠ 1`) and `κ = μ^ρ/(μ^ρ + (1 − μ)^ρ)`, the equilibrium allocation maximises
`κU + (1 − κ)U*` over all positive allocations that exhaust world output on both dates. -/
theorem planner_optimal (hρ1 : E.ρ ≠ 1) (D1 D1f : ℝ) (D2 D2f : S → ℝ) (h1 : 0 < D1)
    (h1f : 0 < D1f) (h2 : ∀ s, 0 < D2 s) (h2f : ∀ s, 0 < D2f s)
    (hf1 : D1 + D1f = E.worldY1) (hf2 : ∀ s, D2 s + D2f s = E.worldY2 s) :
    socialWelfare E.Ω E.β E.ρ (plannerWeight E.ρ E.share) D1 D1f D2 D2f ≤
      socialWelfare E.Ω E.β E.ρ (plannerWeight E.ρ E.share) E.C1 E.C1f E.C2 E.C2f := by
  obtain ⟨hμ0, hμ1⟩ := E.share_mem
  obtain ⟨hκ0, hκ1⟩ := plannerWeight_mem (ρ := E.ρ) hμ0 hμ1
  rw [socialWelfare_eq, socialWelfare_eq]
  have d1 := planner_pair_le E.rho_pos hρ1 hκ0.le hκ1.le E.C1_pos E.C1f_pos h1 h1f
    (by rw [E.C1_eq, E.C1f_eq]; exact planner_foc hμ0 hμ1 E.worldY1_pos)
    (by rw [hf1]; exact E.clear1.symm)
  have d2 : ∀ s, E.Ω.prob s * (plannerWeight E.ρ E.share * crraU E.ρ (D2 s) +
      (1 - plannerWeight E.ρ E.share) * crraU E.ρ (D2f s)) ≤
      E.Ω.prob s * (plannerWeight E.ρ E.share * crraU E.ρ (E.C2 s) +
      (1 - plannerWeight E.ρ E.share) * crraU E.ρ (E.C2f s)) := fun s =>
    mul_le_mul_of_nonneg_left (planner_pair_le E.rho_pos hρ1 hκ0.le hκ1.le (E.C2_pos s)
      (E.C2f_pos s) (h2 s) (h2f s)
      (by rw [E.C2_eq, E.C2f_eq]; exact planner_foc hμ0 hμ1 (E.worldY2_pos s))
      (by rw [hf2 s]; exact (E.clear2 s).symm)) (E.Ω.prob_nonneg s)
  have := mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun s (_ : s ∈ Finset.univ) => d2 s)
    E.beta_pos.le
  linarith

end GlobalEqm

/-! ## Different risk aversion and discount factors: equation (37) -/

/-- **Consumption growth across countries with different `ρ`, `β`**, O&R (37), p. 290: if
countries `n` and `m` face the same Arrow–Debreu price `q` for a state of probability `π > 0`
and their CRRA Euler equations (34) hold, then
`log(c₂ⁿ/c₁ⁿ) = (ρₘ/ρₙ) log(c₂ᵐ/c₁ᵐ) + (1/ρₙ) log(βₙ/βₘ)`. -/
theorem log_growth_relation {q π βn βm ρn ρm c1n c2n c1m c2m : ℝ} (hπ : 0 < π)
    (hβn : 0 < βn) (hβm : 0 < βm) (hρn : 0 < ρn) (h1n : 0 < c1n) (h2n : 0 < c2n)
    (h1m : 0 < c1m) (h2m : 0 < c2m)
    (hn : q * c1n ^ (-ρn) = π * βn * c2n ^ (-ρn))
    (hm : q * c1m ^ (-ρm) = π * βm * c2m ^ (-ρm)) :
    Real.log (c2n / c1n) =
      ρm / ρn * Real.log (c2m / c1m) + 1 / ρn * Real.log (βn / βm) := by
  have en := (crra_euler_iff h1n h2n).1 hn
  have em := (crra_euler_iff h1m h2m).1 hm
  have gn : 0 < c2n / c1n := div_pos h2n h1n
  have gm : 0 < c2m / c1m := div_pos h2m h1m
  have h : π * βn * (c2n / c1n) ^ (-ρn) = π * βm * (c2m / c1m) ^ (-ρm) := en.symm.trans em
  have hl := congrArg Real.log h
  have pn : 0 < (c2n / c1n) ^ (-ρn) := Real.rpow_pos_of_pos gn _
  have pm : 0 < (c2m / c1m) ^ (-ρm) := Real.rpow_pos_of_pos gm _
  rw [Real.log_mul (by positivity) pn.ne', Real.log_mul hπ.ne' hβn.ne',
    Real.log_mul (by positivity) pm.ne', Real.log_mul hπ.ne' hβm.ne',
    Real.log_rpow gn, Real.log_rpow gm] at hl
  rw [Real.log_div hβn.ne' hβm.ne']
  field_simp
  linarith

/-- Correlation is symmetric. -/
theorem corr_symm (Ω : StateSpace S) (X Y : S → ℝ) : Ω.corr X Y = Ω.corr Y X := by
  unfold StateSpace.corr
  rw [Ω.cov_comm, mul_comm]

/-- **Perfectly correlated consumption growth**, O&R (37) and footnote 18, p. 290: with
state-contingent prices common to countries `n` and `m`, CRRA Euler equations, possibly
different `ρₙ, ρₘ > 0` and `βₙ, βₘ > 0`, and non-degenerate consumption growth in `m`, the
log consumption growth rates have correlation one. -/
theorem corr_growth_eq_one (Ω : StateSpace S) {q : S → ℝ} {βn βm ρn ρm c1n c1m : ℝ}
    {c2n c2m : S → ℝ} (hπ : ∀ s, 0 < Ω.prob s) (hβn : 0 < βn) (hβm : 0 < βm)
    (hρn : 0 < ρn) (hρm : 0 < ρm) (h1n : 0 < c1n) (h2n : ∀ s, 0 < c2n s)
    (h1m : 0 < c1m) (h2m : ∀ s, 0 < c2m s)
    (hn : ∀ s, q s * c1n ^ (-ρn) = Ω.prob s * βn * c2n s ^ (-ρn))
    (hm : ∀ s, q s * c1m ^ (-ρm) = Ω.prob s * βm * c2m s ^ (-ρm))
    (hvar : 0 < Ω.var (fun s => Real.log (c2m s / c1m))) :
    Ω.corr (fun s => Real.log (c2n s / c1n)) (fun s => Real.log (c2m s / c1m)) = 1 := by
  have hfun : (fun s => Real.log (c2n s / c1n)) = fun s =>
      1 / ρn * Real.log (βn / βm) + ρm / ρn * Real.log (c2m s / c1m) := by
    funext s
    rw [log_growth_relation (hπ s) hβn hβm hρn h1n (h2n s) h1m (h2m s) (hn s) (hm s)]
    ring
  rw [hfun, corr_symm]
  exact Ω.corr_affine (div_pos hρm hρn) hvar

/-! ## Efficient investment under uncertainty (§5.2.4) -/

/-- The firm's present value, O&R p. 298: `Σ_s q(s)[A(s)F(K) + K] − K` with
`q(s) = p(s)/(1 + r)`, zero depreciation and `K₁ = 0`. -/
def firmValue (q A : S → ℝ) (F : ℝ → ℝ) (K : ℝ) : ℝ := ∑ s, q s * (A s * F K + K) - K

/-- The derivative of the firm's present value in `K`, O&R p. 298. -/
theorem firmValue_hasDerivAt (q A : S → ℝ) {F : ℝ → ℝ} {F' K : ℝ} (hF : HasDerivAt F F' K) :
    HasDerivAt (firmValue q A F) (∑ s, q s * (A s * F' + 1) - 1) K := by
  unfold firmValue
  have hs : ∀ s ∈ (Finset.univ : Finset S), HasDerivAt (fun k => q s * (A s * F k + k))
      (q s * (A s * F' + 1)) K := fun s _ =>
    HasDerivAt.const_mul (q s) (HasDerivAt.add (HasDerivAt.const_mul (A s) hF) (hasDerivAt_id K))
  exact HasDerivAt.sub (HasDerivAt.fun_sum hs) (hasDerivAt_id K)

/-- **Investment first-order condition**, O&R (40), p. 298: at an (interior, local) maximum
of the firm's present value, `Σ_s q(s)[A(s)F′(K₂) + 1] = 1`. -/
theorem investment_foc (q A : S → ℝ) {F : ℝ → ℝ} {F' K : ℝ} (hF : HasDerivAt F F' K)
    (hmax : IsLocalMax (firmValue q A F) K) : ∑ s, q s * (A s * F' + 1) = 1 := by
  have := hmax.hasDerivAt_eq_zero (firmValue_hasDerivAt q A hF)
  linarith

/-- **The marginal value product of capital equals the world interest rate**, O&R p. 298:
with `q = p/(1 + r)` and `Σ p(s) = 1`, (40) is `Σ_s p(s) A(s) F′(K₂) = r`; the same `r` for
Home and Foreign firms. -/
theorem investment_rate {p A : S → ℝ} {r F' : ℝ} (hr : 1 + r ≠ 0) (hp : ∑ s, p s = 1)
    (hfoc : ∑ s, p s / (1 + r) * (A s * F' + 1) = 1) : ∑ s, p s * A s * F' = r := by
  have e : ∑ s, p s / (1 + r) * (A s * F' + 1) =
      (∑ s, p s * A s * F' + ∑ s, p s) / (1 + r) := by
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    exact Finset.sum_congr rfl fun s _ => by field_simp
  rw [e, hp, div_eq_one_iff_eq hr] at hfoc
  linarith

/-- **Investment Euler equation**, O&R (41), p. 298: if the Euler equations (5)
`q(s) u′(C₁) = π(s) β u′(C₂(s))` hold and the firm satisfies (40), then
`u′(C₁) = Σ_s π(s) β u′(C₂(s)) [A(s)F′(K₂) + 1]`. Here `mu1 = u′(C₁)`, `mu2 s = u′(C₂(s))`;
the same holds for Foreign consumption with Home's investment, since prices are common. -/
theorem investment_euler {q π A mu2 : S → ℝ} {β mu1 F' : ℝ}
    (heuler : ∀ s, q s * mu1 = π s * β * mu2 s) (hfoc : ∑ s, q s * (A s * F' + 1) = 1) :
    mu1 = ∑ s, π s * β * mu2 s * (A s * F' + 1) := by
  calc mu1 = (∑ s, q s * (A s * F' + 1)) * mu1 := by rw [hfoc, one_mul]
    _ = ∑ s, q s * mu1 * (A s * F' + 1) := by
        rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun s _ => by ring
    _ = _ := Finset.sum_congr rfl fun s _ => by rw [heuler s]

/-- **Prices with investment under log utility**, O&R §5.2.4.1, p. 298: with Euler equations
`q(s)/C₁ = π(s)β/C₂(s)` in both countries and market clearing
`C₁ + C₁* = Y₁ᵂ − K₂ − K₂*`, `C₂(s) + C₂*(s) = Y₂ᵂ(s) + K₂ + K₂*`,
`q(s) = π(s)β(Y₁ᵂ − K₂ − K₂*)/(Y₂ᵂ(s) + K₂ + K₂*)`. -/
theorem log_investment_price {q π β C1 C1f C2 C2f Y1W Y2W K Kf : ℝ} (h1 : 0 < C1)
    (h1f : 0 < C1f) (h2 : 0 < C2) (h2f : 0 < C2f)
    (he : q / C1 = π * β / C2) (hef : q / C1f = π * β / C2f)
    (hc1 : C1 + C1f = Y1W - K - Kf) (hc2 : C2 + C2f = Y2W + K + Kf) :
    q = π * β * (Y1W - K - Kf) / (Y2W + K + Kf) := by
  rw [div_eq_div_iff h1.ne' h2.ne'] at he
  rw [div_eq_div_iff h1f.ne' h2f.ne'] at hef
  rw [← hc1, ← hc2, eq_div_iff (by linarith)]
  linarith

/-- **World investment in the log/linear example**, O&R §5.2.4.1, p. 299: with `F(K) = K`,
if both firms' first-order conditions hold at the log-utility prices,
`Σ_s π(s)β(Y₁ᵂ − K₂ − K₂*)/(A(s)K₂ + A*(s)K₂* + K₂ + K₂*) · [A(s) + 1] = 1` and the same with
`A*`, then `K₂ + K₂* = βY₁ᵂ/(1 + β)`. (Nonnegativity of investment is not imposed.) -/
theorem log_linear_world_investment (Ω : StateSpace S) {A Af : S → ℝ} {β Y1W K Kf : ℝ}
    (hβ : 0 < β) (hD : ∀ s, 0 < A s * K + Af s * Kf + K + Kf)
    (hfoc : ∑ s, Ω.prob s * β * (Y1W - K - Kf) / (A s * K + Af s * Kf + K + Kf) *
      (A s + 1) = 1)
    (hfocf : ∑ s, Ω.prob s * β * (Y1W - K - Kf) / (A s * K + Af s * Kf + K + Kf) *
      (Af s + 1) = 1) :
    K + Kf = β * Y1W / (1 + β) := by
  have e : K * (∑ s, Ω.prob s * β * (Y1W - K - Kf) / (A s * K + Af s * Kf + K + Kf) *
      (A s + 1)) + Kf * (∑ s, Ω.prob s * β * (Y1W - K - Kf) /
        (A s * K + Af s * Kf + K + Kf) * (Af s + 1)) = ∑ s, Ω.prob s * β * (Y1W - K - Kf) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun s _ => ?_
    set X := Ω.prob s * β * (Y1W - K - Kf)
    set D := A s * K + Af s * Kf + K + Kf with hDdef
    calc K * (X / D * (A s + 1)) + Kf * (X / D * (Af s + 1))
        = X / D * ((A s + 1) * K + (Af s + 1) * Kf) := by ring
      _ = X / D * D := by rw [hDdef]; ring
      _ = X := div_mul_cancel₀ X (hD s).ne'
  rw [hfoc, hfocf, ← Finset.sum_mul, ← Finset.sum_mul, Ω.prob_sum, one_mul] at e
  have hsum : K + Kf = β * (Y1W - K - Kf) := by linarith
  rw [eq_div_iff (by linarith)]
  linarith

/-! ## Exercise 2: risk neutrality at date 2 -/

/-- **Exercise 2**, O&R p. 345: with `U = log C₁ + β Σ π(s) C₂(s)` in both countries, the
Euler equations `q(s)/C₁ = π(s)β` and `q(s)/C₁* = π(s)β` with `q = p/(1 + r)`, clearing
`C₁ + C₁* = Y₁ᵂ` and `Σ p(s) = 1` imply `C₁ = C₁* = Y₁ᵂ/2`, actuarially fair prices
`p(s) = π(s)`, and `1 + r = 2/(βY₁ᵂ)`. -/
theorem exercise2 (Ω : StateSpace S) {p : S → ℝ} {β r C1 C1f Y1W : ℝ} (hβ : 0 < β)
    (hr : 0 < 1 + r) (h1 : 0 < C1) (h1f : 0 < C1f)
    (he : ∀ s, p s / (1 + r) / C1 = Ω.prob s * β)
    (hef : ∀ s, p s / (1 + r) / C1f = Ω.prob s * β)
    (hc : C1 + C1f = Y1W) (hp : ∑ s, p s = 1) :
    C1 = Y1W / 2 ∧ C1f = Y1W / 2 ∧ (∀ s, p s = Ω.prob s) ∧ 1 + r = 2 / (β * Y1W) := by
  -- sum each Euler equation over states
  have hs : ∀ C : ℝ, 0 < C → (∀ s, p s / (1 + r) / C = Ω.prob s * β) →
      1 = (1 + r) * β * C := by
    intro C hC h
    have : ∑ s, p s / (1 + r) / C = ∑ s, Ω.prob s * β := Finset.sum_congr rfl fun s _ => h s
    rw [← Finset.sum_div, ← Finset.sum_div, hp, ← Finset.sum_mul, Ω.prob_sum, one_mul] at this
    field_simp at this
    linarith
  have a := hs C1 h1 he
  have b := hs C1f h1f hef
  have hrb : 0 < (1 + r) * β := mul_pos hr hβ
  have heq : C1 = C1f := by
    have : (1 + r) * β * C1 = (1 + r) * β * C1f := by linarith
    exact mul_left_cancel₀ hrb.ne' this
  have hC1 : C1 = Y1W / 2 := by linarith
  refine ⟨hC1, by linarith, fun s => ?_, ?_⟩
  · have h := he s
    rw [div_div, div_eq_iff (by positivity)] at h
    calc p s = Ω.prob s * ((1 + r) * β * C1) := by rw [h]; ring
      _ = Ω.prob s := by rw [← a, mul_one]
  · have hY : 0 < Y1W := by linarith
    rw [eq_div_iff (by positivity)]
    rw [hC1] at a
    linarith

/-- **Exercise 2: the date-2 allocation is indeterminate**, O&R p. 345. With fair prices
`p = π`, any reallocation `C₂ ↦ C₂ + D`, `C₂* ↦ C₂* − D` of zero expected value leaves both
countries' intertemporal budgets and date-2 market clearing unchanged; the Euler equations
of Exercise 2 do not involve date-2 consumption at all, so only the value of date-2
consumption is pinned down. -/
theorem exercise2_indeterminate (Ω : StateSpace S) {r : ℝ} {C2 C2f Y2 Y2f D : S → ℝ}
    (hD : Ω.expect D = 0) :
    (∑ s, Ω.prob s / (1 + r) * (C2 s + D s) = ∑ s, Ω.prob s / (1 + r) * C2 s) ∧
      (∑ s, Ω.prob s / (1 + r) * (C2f s - D s) = ∑ s, Ω.prob s / (1 + r) * C2f s) ∧
      ((∀ s, C2 s + C2f s = Y2 s + Y2f s) →
        ∀ s, (C2 s + D s) + (C2f s - D s) = Y2 s + Y2f s) := by
  have key : ∑ s, Ω.prob s / (1 + r) * D s = 0 := by
    have : ∑ s, Ω.prob s / (1 + r) * D s = Ω.expect D / (1 + r) := by
      unfold StateSpace.expect; rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun s _ => by ring
    rw [this, hD, zero_div]
  refine ⟨?_, ?_, fun h s => by linarith [h s]⟩
  · simp only [mul_add, Finset.sum_add_distrib, key, add_zero]
  · simp only [mul_sub, Finset.sum_sub_distrib, key, sub_zero]

end ObstfeldRogoff.InternationalFinancialMarkets.GlobalEquilibrium
