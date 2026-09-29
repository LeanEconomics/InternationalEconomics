/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import InternationalFinancialMarkets.Model
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Convex.Deriv

/-!
# Trade across random states of nature: the small-country case

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §5.1.1–5.1.6,
pp. 270–280, Appendix 5B, pp. 337–340, and Exercises 1 and 3, pp. 345–346.

A small endowment economy lives for two dates; date-2 output `Y2(s)` depends on the state
`s` (a finite type, probabilities `Ω.prob s = π(s)`). Arrow–Debreu (AD) security `s` pays one
unit in state `s` only and costs `p(s)/(1+r)` on date 1; the riskless bond costs one unit and
pays `1 + r`. We prove:
* no-arbitrage with bonds and AD securities holds iff `Σ p(s) = 1` and `p ≥ 0` (O&R (7));
  bonds are redundant and AD securities span every payoff (§5.1.2);
* the budget constraints (2)+(3) are equivalent to the intertemporal constraint (4)/(18);
* from the first-order conditions (5): the bond Euler equation (8), (6) and (9), and
  sufficiency of (5) for a concave utility;
* necessity of (5)–(6) at any optimum interior to an open consumption domain `D` (e.g.
  `(0, ∞)`) at which `u` is differentiable, with no concavity: for the book's problem in the
  AD holdings `B₂` and for plans under both the equality and the `≤` form of the budget (4),
  by a one-dimensional perturbation along the budget line; (6), (8) and (9) follow as
  corollaries of optimality; under the `≤` form the budget binds when `u′(C₁) ≠ 0`; and, for
  concave differentiable `u`, iff characterisations of the optimum by (5) (plus a binding
  budget in the `≤` form with `u′ > 0`);
* full insurance iff prices are actuarially fair, `p = π` (O&R (10));
* the exact CRRA form of (11) and the Arrow–Pratt coefficient (12);
* log-utility closed forms (15)–(17), footnotes 9 and 10;
* Appendix 5B: (78)–(81), the sign of `CA₁` is that of `r − r^CA` (footnote 51) and not
  that of `r − r^A`, footnote 50, gross flows `B₂(1)`, `B₂(2)`, and Exercise 1;
* Exercise 3 (quadratic utility): certainty equivalence, the Kuhn–Tucker solution with the
  date-2 nonnegativity constraint (the book's "`C_t`" in part (b) is a typo for `C₁`), and
  full insurance under complete markets with fair prices.
-/

namespace ObstfeldRogoff.InternationalFinancialMarkets.SmallCountry

open Finset

variable {S : Type} [Fintype S]

/-! ## Arrow–Debreu securities and bonds (§5.1.2, pp. 272–273) -/

/-- Payoff of one state-`s'` Arrow–Debreu security in state `s`, O&R §5.1.2, p. 272:
one unit if `s = s'`, nothing otherwise. -/
def adPayoff [DecidableEq S] (s' s : S) : ℝ := if s = s' then 1 else 0

/-- Date-2 payoff in state `s` of a portfolio of `b` riskless bonds (each paying `1 + r`) and
`B s'` state-`s'` AD securities, O&R §5.1.2, p. 272. -/
def portfolioPayoff [DecidableEq S] (r b : ℝ) (B : S → ℝ) (s : S) : ℝ :=
  (1 + r) * b + ∑ s', B s' * adPayoff s' s

/-- Date-1 cost of the portfolio: bonds cost 1, AD security `s` costs `p(s)/(1+r)`,
O&R §5.1.3, p. 273. -/
noncomputable def portfolioCost (p : S → ℝ) (r b : ℝ) (B : S → ℝ) : ℝ :=
  b + ∑ s, p s / (1 + r) * B s

/-- No arbitrage, O&R §5.1.4, pp. 276–277: every portfolio with a nonnegative payoff in every
state has a nonnegative cost. -/
def NoArbitrage [DecidableEq S] (p : S → ℝ) (r : ℝ) : Prop :=
  ∀ (b : ℝ) (B : S → ℝ), (∀ s, 0 ≤ portfolioPayoff r b B s) → 0 ≤ portfolioCost p r b B

/-- The payoff of an AD portfolio is the vector of its holdings, O&R §5.1.2, p. 272. -/
theorem portfolioPayoff_eq [DecidableEq S] (r b : ℝ) (B : S → ℝ) (s : S) :
    portfolioPayoff r b B s = (1 + r) * b + B s := by
  simp [portfolioPayoff, adPayoff]

/-- AD securities span all payoffs (complete markets), O&R §5.1.2, pp. 272–273: every date-2
payoff `X` is delivered by the pure AD portfolio `B = X`, at cost `Σ p(s)X(s)/(1+r)`. -/
theorem ad_span [DecidableEq S] (p : S → ℝ) (r : ℝ) (X : S → ℝ) :
    (∀ s, portfolioPayoff r 0 X s = X s) ∧
      portfolioCost p r 0 X = (∑ s, p s * X s) / (1 + r) := by
  refine ⟨fun s => by simp [portfolioPayoff_eq], ?_⟩
  simp only [portfolioCost, zero_add, Finset.sum_div]
  exact Finset.sum_congr rfl fun s _ => by ring

/-- No-arbitrage pricing, O&R (7), p. 277: with `1 + r > 0`, there is no arbitrage between the
bond and the AD securities iff the AD prices satisfy `Σ p(s) = 1` and `p(s) ≥ 0`. The book's
argument (`1 + r` units of every AD security replicate the bond) is the `Σ p = 1` half. -/
theorem noArbitrage_iff [DecidableEq S] (p : S → ℝ) {r : ℝ} (hr : 0 < 1 + r) :
    NoArbitrage p r ↔ (∑ s, p s = 1 ∧ ∀ s, 0 ≤ p s) := by
  have hr0 : 1 + r ≠ 0 := hr.ne'
  constructor
  · intro h
    have h1 := h 1 (fun _ => -(1 + r)) (fun s => by simp [portfolioPayoff_eq])
    have h2 := h (-1) (fun _ => 1 + r) (fun s => by simp [portfolioPayoff_eq])
    have e1 : ∀ c : ℝ, ∑ s, p s / (1 + r) * (c * (1 + r)) = c * ∑ s, p s := fun c => by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun s _ => by field_simp
    simp only [portfolioCost] at h1 h2
    have e1' := e1 (-1)
    have e2' := e1 1
    simp only [neg_mul, one_mul] at e1' e2'
    rw [e1'] at h1
    rw [e2'] at h2
    refine ⟨by linarith, fun s => ?_⟩
    have h3 := h 0 (fun t => if t = s then 1 else 0) (fun t => by
      simp only [portfolioPayoff_eq, mul_zero, zero_add]
      split_ifs <;> norm_num)
    simp only [portfolioCost, mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, ↓reduceIte,
      zero_add] at h3
    exact (div_nonneg_iff.mp h3).elim (fun h => h.1) (fun h => absurd h.2 (not_le.mpr hr))
  · rintro ⟨hsum, hpos⟩ b B hB
    have : portfolioCost p r b B = ∑ s, p s / (1 + r) * portfolioPayoff r b B s := by
      simp only [portfolioCost, portfolioPayoff_eq, mul_add, Finset.sum_add_distrib]
      congr 1
      rw [show ∑ s, p s / (1 + r) * ((1 + r) * b) = ∑ s, p s * b from
        Finset.sum_congr rfl fun s _ => by field_simp, ← Finset.sum_mul, hsum, one_mul]
    rw [this]
    exact Finset.sum_nonneg fun s _ => mul_nonneg (div_nonneg (hpos s) hr.le) (hB s)

/-- Bonds are redundant, O&R §5.1.2, p. 272: when `Σ p(s) = 1`, a portfolio of `b` bonds and
AD holdings `B` has the same payoff and the same cost as the pure AD portfolio
`B + (1 + r)b`. -/
theorem bond_redundant [DecidableEq S] (p : S → ℝ) {r : ℝ} (hr : 1 + r ≠ 0) (hsum : ∑ s, p s = 1)
    (b : ℝ) (B : S → ℝ) :
    (∀ s, portfolioPayoff r b B s = portfolioPayoff r 0 (fun s => B s + (1 + r) * b) s) ∧
      portfolioCost p r b B = portfolioCost p r 0 (fun s => B s + (1 + r) * b) := by
  refine ⟨fun s => by simp only [portfolioPayoff_eq]; ring, ?_⟩
  simp only [portfolioCost, mul_add, Finset.sum_add_distrib, zero_add]
  rw [add_comm]
  congr 1
  rw [show ∑ s, p s / (1 + r) * ((1 + r) * b) = ∑ s, p s * b from
    Finset.sum_congr rfl fun s _ => by field_simp, ← Finset.sum_mul, hsum, one_mul]

/-! ## Budget constraints (§5.1.3, pp. 273–276) -/

/-- The budget constraints, O&R (2), (3) and (18), pp. 273–281: consumption `(C₁, C₂)` is
financed by some AD holdings `B₂` satisfying (2) and (3) iff it satisfies the intertemporal
budget constraint (18), `C₁ − Y₁ + Σ p(s)[C₂(s) − Y₂(s)]/(1+r) = 0`. -/
theorem budget_iff (p : S → ℝ) (r Y1 C1 : ℝ) (Y2 C2 : S → ℝ) :
    (∃ B2 : S → ℝ, ∑ s, p s / (1 + r) * B2 s = Y1 - C1 ∧ ∀ s, C2 s = Y2 s + B2 s) ↔
      C1 - Y1 + ∑ s, p s / (1 + r) * (C2 s - Y2 s) = 0 := by
  constructor
  · rintro ⟨B2, h2, h3⟩
    have : ∑ s, p s / (1 + r) * (C2 s - Y2 s) = ∑ s, p s / (1 + r) * B2 s :=
      Finset.sum_congr rfl fun s _ => by rw [h3 s]; ring
    rw [this, h2]; ring
  · intro h
    exact ⟨fun s => C2 s - Y2 s, by linarith, fun s => by ring⟩

/-- The intertemporal budget constraint in present-value form, O&R (4), p. 275:
(18) is equivalent to `C₁ + Σ p(s)C₂(s)/(1+r) = Y₁ + Σ p(s)Y₂(s)/(1+r)`. -/
theorem budget_pv_iff (p : S → ℝ) (r Y1 C1 : ℝ) (Y2 C2 : S → ℝ) :
    C1 - Y1 + ∑ s, p s / (1 + r) * (C2 s - Y2 s) = 0 ↔
      C1 + ∑ s, p s / (1 + r) * C2 s = Y1 + ∑ s, p s / (1 + r) * Y2 s := by
  simp only [mul_sub, Finset.sum_sub_distrib]
  constructor <;> intro h <;> linarith

/-! ## First-order conditions (§5.1.4, pp. 276–278) -/

/-- The bond Euler equation, O&R (8), p. 277: summing the AD first-order conditions (5),
`p(s)u′(C₁)/(1+r) = π(s)βu′(C₂(s))`, over states and using `Σ p(s) = 1` (O&R (7)) gives
`u′(C₁) = (1+r)βE[u′(C₂)]`. -/
theorem bond_euler (Ω : StateSpace S) (p : S → ℝ) {r : ℝ} (hr : 1 + r ≠ 0)
    (hsum : ∑ s, p s = 1) (β : ℝ) (du : ℝ → ℝ) (C1 : ℝ) (C2 : S → ℝ)
    (hfoc : ∀ s, p s / (1 + r) * du C1 = Ω.prob s * β * du (C2 s)) :
    du C1 = (1 + r) * β * Ω.expect (fun s => du (C2 s)) := by
  have h : ∑ s, p s / (1 + r) * du C1 = ∑ s, Ω.prob s * β * du (C2 s) :=
    Finset.sum_congr rfl fun s _ => hfoc s
  rw [← Finset.sum_mul, ← Finset.sum_div, hsum] at h
  have e : β * Ω.expect (fun s => du (C2 s)) = ∑ s, Ω.prob s * β * du (C2 s) := by
    simp only [StateSpace.expect, Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [mul_assoc, e, ← h]
  field_simp

/-- The marginal rate of substitution equals the relative price, O&R (6), p. 276:
`π(s)βu′(C₂(s))/u′(C₁) = p(s)/(1+r)`, from (5) when `u′(C₁) ≠ 0`. -/
theorem mrs_eq_price (Ω : StateSpace S) (p : S → ℝ) (r β : ℝ) (du : ℝ → ℝ) (C1 : ℝ)
    (C2 : S → ℝ) (hd : du C1 ≠ 0)
    (hfoc : ∀ s, p s / (1 + r) * du C1 = Ω.prob s * β * du (C2 s)) (s : S) :
    Ω.prob s * β * du (C2 s) / du C1 = p s / (1 + r) := by
  rw [← hfoc s]
  field_simp

/-- The across-state first-order condition, O&R (9), p. 277:
`π(s)u′(C₂(s))/[π(t)u′(C₂(t))] = p(s)/p(t)`, from (5) for states `s` and `t`. -/
theorem mrs_ratio_eq_price_ratio (Ω : StateSpace S) (p : S → ℝ) {r β : ℝ} (hr : 1 + r ≠ 0)
    (hβ : β ≠ 0) (du : ℝ → ℝ) (C1 : ℝ) (C2 : S → ℝ) (hd : du C1 ≠ 0)
    (hfoc : ∀ s, p s / (1 + r) * du C1 = Ω.prob s * β * du (C2 s)) (s t : S) :
    Ω.prob s * du (C2 s) / (Ω.prob t * du (C2 t)) = p s / p t := by
  have e : ∀ s, p s = (1 + r) * β * (Ω.prob s * du (C2 s)) / du C1 := fun s => by
    rw [eq_div_iff hd, show (1 + r) * β * (Ω.prob s * du (C2 s)) =
      (1 + r) * (Ω.prob s * β * du (C2 s)) by ring, ← hfoc s]
    field_simp
  rw [e s, e t]
  field_simp

/-- A differentiable concave function lies below its tangent lines (used for the sufficiency
of the first-order conditions (5), O&R §5.1.4, p. 276): if `u` is concave on `D` with
derivative `du x` at `x ∈ D`, then `u y ≤ u x + du x (y − x)` for `y ∈ D`. -/
theorem supergradient_of_concaveOn {D : Set ℝ} {u : ℝ → ℝ} (hconc : ConcaveOn ℝ D u)
    {x y d : ℝ} (hx : x ∈ D) (hy : y ∈ D) (hu : HasDerivAt u d x) :
    u y ≤ u x + d * (y - x) := by
  rcases lt_trichotomy x y with hxy | rfl | hxy
  · have h := hconc.slope_le_of_hasDerivAt hx hy hxy hu
    rw [slope_def_field, div_le_iff₀ (sub_pos.mpr hxy)] at h
    linarith
  · simp
  · have h := hconc.le_slope_of_hasDerivAt hy hx hxy hu
    rw [slope_def_field, le_div_iff₀ (sub_pos.mpr hxy)] at h
    linarith

/-- Expected lifetime utility (1) as a function of the AD holdings `B`, O&R p. 276:
`u(Y₁ − Σ p(s)B(s)/(1+r)) + Σ π(s)βu(Y₂(s) + B(s))`. -/
noncomputable def lifetimeUtility (Ω : StateSpace S) (u : ℝ → ℝ) (p : S → ℝ) (r β Y1 : ℝ)
    (Y2 B : S → ℝ) : ℝ :=
  u (Y1 - ∑ s, p s / (1 + r) * B s) + ∑ s, Ω.prob s * β * u (Y2 s + B s)

/-- Sufficiency of the first-order conditions (5), O&R p. 276 (implicit in the book): if `u` is
concave and differentiable on a convex set `D` of consumption levels, `β ≥ 0`, and the holdings
`B` satisfy (5), then `B` maximises expected utility (1) over all holdings `B'` whose
consumption stays in `D`. -/
theorem foc_sufficient (Ω : StateSpace S) {D : Set ℝ} {u du : ℝ → ℝ}
    (hconc : ConcaveOn ℝ D u) (hu : ∀ x ∈ D, HasDerivAt u (du x) x) (p : S → ℝ)
    {r β : ℝ} (hβ : 0 ≤ β) (Y1 : ℝ) (Y2 B B' : S → ℝ)
    (hC1 : Y1 - ∑ s, p s / (1 + r) * B s ∈ D) (hC2 : ∀ s, Y2 s + B s ∈ D)
    (hC1' : Y1 - ∑ s, p s / (1 + r) * B' s ∈ D) (hC2' : ∀ s, Y2 s + B' s ∈ D)
    (hfoc : ∀ s, p s / (1 + r) * du (Y1 - ∑ s, p s / (1 + r) * B s) =
      Ω.prob s * β * du (Y2 s + B s)) :
    lifetimeUtility Ω u p r β Y1 Y2 B' ≤ lifetimeUtility Ω u p r β Y1 Y2 B := by
  set C1 := Y1 - ∑ s, p s / (1 + r) * B s with hC1def
  have h1 := supergradient_of_concaveOn hconc hC1 hC1' (hu C1 hC1)
  have h2 : ∀ s, Ω.prob s * β * u (Y2 s + B' s) ≤
      Ω.prob s * β * (u (Y2 s + B s) + du (Y2 s + B s) * (B' s - B s)) := fun s => by
    have := supergradient_of_concaveOn hconc (hC2 s) (hC2' s) (hu _ (hC2 s))
    refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (Ω.prob_nonneg s) hβ)
    convert this using 3; ring
  have key : du C1 * ((Y1 - ∑ s, p s / (1 + r) * B' s) - C1) =
      -∑ s, Ω.prob s * β * du (Y2 s + B s) * (B' s - B s) := by
    rw [hC1def, show Y1 - ∑ s, p s / (1 + r) * B' s - (Y1 - ∑ s, p s / (1 + r) * B s) =
      -∑ s, p s / (1 + r) * (B' s - B s) by
        simp only [mul_sub, Finset.sum_sub_distrib]; ring, mul_neg, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl fun s _ => by rw [← hfoc s]; ring
  have hsum := Finset.sum_le_sum fun s (_ : s ∈ Finset.univ) => h2 s
  have e : ∑ s, Ω.prob s * β * (u (Y2 s + B s) + du (Y2 s + B s) * (B' s - B s)) =
      ∑ s, Ω.prob s * β * u (Y2 s + B s) +
        ∑ s, Ω.prob s * β * du (Y2 s + B s) * (B' s - B s) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun s _ => by ring
  simp only [lifetimeUtility]
  rw [e] at hsum
  linarith

/-! ## Necessity of the first-order conditions (§5.1.4, pp. 275–277)

A consumption plan is a pair `(C₁, C₂(·))`. Consumption is restricted to an open set `D`
(for instance `D = (0, ∞)`, the domain of CRRA or log utility), so the optimum is interior and
corner solutions are excluded by hypothesis rather than by assumption on `u`. -/

/-- Expected lifetime utility of a consumption plan, O&R (1), p. 273:
`u(C₁) + Σ π(s)βu(C₂(s))`. -/
noncomputable def planUtility (Ω : StateSpace S) (u : ℝ → ℝ) (β C1 : ℝ) (C2 : S → ℝ) : ℝ :=
  u C1 + ∑ s, Ω.prob s * β * u (C2 s)

/-- The date-1 present value of a consumption plan at AD prices, the left-hand side of O&R (4),
p. 275: `C₁ + Σ p(s)C₂(s)/(1+r)`. The budget constraint (4) is
`planValue p r C₁ C₂ = planValue p r Y₁ Y₂`. -/
noncomputable def planValue (p : S → ℝ) (r C1 : ℝ) (C2 : S → ℝ) : ℝ :=
  C1 + ∑ s, p s / (1 + r) * C2 s

/-- Optimality of a plan along its budget line, O&R §5.1.4, p. 276: `(C₁, C₂)` (with
consumption in `D`) does at least as well as every plan with consumption in `D` and the same
present value (4). Both forms of the budget constraint (equality and `≤`) and the book's
unconstrained problem in `B₂` imply it (see `isPlanOptimum_of_budget_eq`,
`isPlanOptimum_of_budget_le`, `isPlanOptimum_of_lifetime`). -/
def IsPlanOptimum (Ω : StateSpace S) (D : Set ℝ) (u : ℝ → ℝ) (p : S → ℝ) (r β C1 : ℝ)
    (C2 : S → ℝ) : Prop :=
  ∀ (C1' : ℝ) (C2' : S → ℝ), C1' ∈ D → (∀ s, C2' s ∈ D) →
    planValue p r C1' C2' = planValue p r C1 C2 →
      planUtility Ω u β C1' C2' ≤ planUtility Ω u β C1 C2

/-- The book's objective in terms of asset holdings is the plan objective, O&R p. 276:
`U₁(B₂) = u(C₁) + Σ π(s)βu(C₂(s))` with `C₁ = Y₁ − Σ p(s)B₂(s)/(1+r)`, `C₂ = Y₂ + B₂`. -/
theorem lifetimeUtility_eq_planUtility (Ω : StateSpace S) (u : ℝ → ℝ) (p : S → ℝ)
    (r β Y1 : ℝ) (Y2 B : S → ℝ) :
    lifetimeUtility Ω u p r β Y1 Y2 B =
      planUtility Ω u β (Y1 - ∑ s, p s / (1 + r) * B s) (fun s => Y2 s + B s) := rfl

/-- The plan financed by AD holdings `B₂` satisfies the budget constraint (4), O&R p. 275:
its present value equals that of the endowment. -/
theorem planValue_of_holdings (p : S → ℝ) (r Y1 : ℝ) (Y2 B : S → ℝ) :
    planValue p r (Y1 - ∑ s, p s / (1 + r) * B s) (fun s => Y2 s + B s) =
      planValue p r Y1 Y2 := by
  simp only [planValue, mul_add, Finset.sum_add_distrib]
  ring

/-- The equality form of the budget constraint (4)/(18), O&R p. 275: if `(C₁, C₂)` satisfies
(4) and maximises expected utility over all plans in `D` satisfying (4), it is a plan
optimum. -/
theorem isPlanOptimum_of_budget_eq (Ω : StateSpace S) {D : Set ℝ} {u : ℝ → ℝ} (p : S → ℝ)
    (r β Y1 C1 : ℝ) (Y2 C2 : S → ℝ) (hbud : planValue p r C1 C2 = planValue p r Y1 Y2)
    (hmax : ∀ (C1' : ℝ) (C2' : S → ℝ), C1' ∈ D → (∀ s, C2' s ∈ D) →
      planValue p r C1' C2' = planValue p r Y1 Y2 →
        planUtility Ω u β C1' C2' ≤ planUtility Ω u β C1 C2) :
    IsPlanOptimum Ω D u p r β C1 C2 :=
  fun C1' C2' h1 h2 hv => hmax C1' C2' h1 h2 (hv.trans hbud)

/-- The `≤` form of the budget constraint (4), O&R p. 275: if `(C₁, C₂)` satisfies
`planValue ≤ planValue(Y₁, Y₂)` and maximises expected utility over all plans in `D` doing
so, it is a plan optimum (whether or not its budget binds). -/
theorem isPlanOptimum_of_budget_le (Ω : StateSpace S) {D : Set ℝ} {u : ℝ → ℝ} (p : S → ℝ)
    (r β Y1 C1 : ℝ) (Y2 C2 : S → ℝ) (hbud : planValue p r C1 C2 ≤ planValue p r Y1 Y2)
    (hmax : ∀ (C1' : ℝ) (C2' : S → ℝ), C1' ∈ D → (∀ s, C2' s ∈ D) →
      planValue p r C1' C2' ≤ planValue p r Y1 Y2 →
        planUtility Ω u β C1' C2' ≤ planUtility Ω u β C1 C2) :
    IsPlanOptimum Ω D u p r β C1 C2 :=
  fun C1' C2' h1 h2 hv => hmax C1' C2' h1 h2 (hv.trans_le hbud)

/-- The book's unconstrained problem in the AD holdings, O&R p. 276: if `B₂` maximises
`U₁(B₂) = u(Y₁ − Σ p(s)B₂(s)/(1+r)) + Σ π(s)βu(Y₂(s) + B₂(s))` over all holdings whose
consumption stays in `D`, the plan it finances is a plan optimum. -/
theorem isPlanOptimum_of_lifetime (Ω : StateSpace S) {D : Set ℝ} {u : ℝ → ℝ} (p : S → ℝ)
    (r β Y1 : ℝ) (Y2 B : S → ℝ)
    (hmax : ∀ B' : S → ℝ, Y1 - ∑ s, p s / (1 + r) * B' s ∈ D → (∀ s, Y2 s + B' s ∈ D) →
      lifetimeUtility Ω u p r β Y1 Y2 B' ≤ lifetimeUtility Ω u p r β Y1 Y2 B) :
    IsPlanOptimum Ω D u p r β (Y1 - ∑ s, p s / (1 + r) * B s) (fun s => Y2 s + B s) := by
  intro C1' C2' h1 h2 hv
  rw [planValue_of_holdings] at hv
  have hC1' : Y1 - ∑ s, p s / (1 + r) * (C2' s - Y2 s) = C1' := by
    simp only [planValue, mul_sub, Finset.sum_sub_distrib] at hv ⊢
    linarith
  have hC2' : (fun s => Y2 s + (C2' s - Y2 s)) = C2' := funext fun s => by ring
  have h := hmax (fun s => C2' s - Y2 s) (by rw [hC1']; exact h1)
    (fun s => by simpa using h2 s)
  rw [lifetimeUtility_eq_planUtility, lifetimeUtility_eq_planUtility, hC1', hC2'] at h
  exact h

/-- Necessity of the first-order conditions (5)–(6), O&R pp. 276–277: if `(C₁, C₂)` is a plan
optimum with consumption in an open set `D`, and `u` has derivative `du x` at `C₁` and at every
`C₂(s)`, then for every state `s`, `p(s)u′(C₁)/(1+r) = π(s)βu′(C₂(s))`. No concavity is used.
Proof: the one-dimensional perturbation `C₁ − p(s)t/(1+r)`, `C₂(s) + t` stays on the budget
line and in `D` for small `t`, so `t = 0` is a local maximum of expected utility along it and
its derivative `−p(s)u′(C₁)/(1+r) + π(s)βu′(C₂(s))` vanishes. -/
theorem foc_of_isPlanOptimum (Ω : StateSpace S) {D : Set ℝ} (hD : IsOpen D) {u du : ℝ → ℝ}
    (p : S → ℝ) {r β C1 : ℝ} {C2 : S → ℝ} (hC1 : C1 ∈ D) (hC2 : ∀ s, C2 s ∈ D)
    (hu1 : HasDerivAt u (du C1) C1) (hu2 : ∀ s, HasDerivAt u (du (C2 s)) (C2 s))
    (hopt : IsPlanOptimum Ω D u p r β C1 C2) (s : S) :
    p s / (1 + r) * du C1 = Ω.prob s * β * du (C2 s) := by
  classical
  set q := p s / (1 + r) with hq
  set e : S → ℝ := fun s' => if s' = s then 1 else 0 with he
  set g : ℝ → ℝ := fun t => planUtility Ω u β (C1 - q * t) (fun s' => C2 s' + t * e s')
    with hg
  have hloc : IsLocalMax g 0 := by
    have h1 : ∀ᶠ t in nhds (0 : ℝ), C1 - q * t ∈ D := by
      have hc : Continuous (fun t : ℝ => C1 - q * t) := by fun_prop
      exact hc.continuousAt.preimage_mem_nhds (by simpa using hD.mem_nhds hC1)
    have h2 : ∀ᶠ t in nhds (0 : ℝ), C2 s + t ∈ D := by
      have hc : Continuous (fun t : ℝ => C2 s + t) := by fun_prop
      exact hc.continuousAt.preimage_mem_nhds (by simpa using hD.mem_nhds (hC2 s))
    filter_upwards [h1, h2] with t ht1 ht2
    have hg0 : g 0 = planUtility Ω u β C1 C2 := by simp [hg]
    rw [hg0]
    refine hopt _ _ ht1 (fun s' => ?_) ?_
    · by_cases hs : s' = s
      · subst hs; simpa [he] using ht2
      · simpa [he, hs] using hC2 s'
    · simp only [planValue, mul_add, Finset.sum_add_distrib, he, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, ite_true]
      ring
  have hderiv : HasDerivAt g
      (du C1 * (-q) + ∑ s', Ω.prob s' * β * (du (C2 s') * e s')) 0 := by
    have hin : HasDerivAt (fun t : ℝ => C1 - q * t) (-q) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).const_mul q).const_sub C1
    have hu1' : HasDerivAt u (du C1) (C1 - q * 0) := by simpa using hu1
    have hA : HasDerivAt (fun t => u (C1 - q * t)) (du C1 * (-q)) 0 := hu1'.comp 0 hin
    have hB : ∀ s' ∈ Finset.univ, HasDerivAt (fun t => Ω.prob s' * β * u (C2 s' + t * e s'))
        (Ω.prob s' * β * (du (C2 s') * e s')) 0 := by
      intro s' _
      have hin' : HasDerivAt (fun t : ℝ => C2 s' + t * e s') (e s') 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (e s')).const_add (C2 s')
      have hu2' : HasDerivAt u (du (C2 s')) (C2 s' + 0 * e s') := by simpa using hu2 s'
      exact (hu2'.comp 0 hin').const_mul _
    exact hA.add (HasDerivAt.fun_sum hB)
  have h0 := hloc.hasDerivAt_eq_zero hderiv
  simp only [he, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true] at h0
  linarith

/-- Necessity of the first-order conditions (5), O&R p. 276, in the book's own form (the FOC
in `B₂(s)`): if the AD holdings `B₂` maximise `U₁(B₂)` over all holdings with consumption in
the open set `D`, and `u` is differentiable at `C₁` and every `C₂(s)`, then (5) holds in every
state. -/
theorem foc_necessary (Ω : StateSpace S) {D : Set ℝ} (hD : IsOpen D) {u du : ℝ → ℝ}
    (p : S → ℝ) (r β Y1 : ℝ) (Y2 B : S → ℝ)
    (hC1 : Y1 - ∑ s, p s / (1 + r) * B s ∈ D) (hC2 : ∀ s, Y2 s + B s ∈ D)
    (hu1 : HasDerivAt u (du (Y1 - ∑ s, p s / (1 + r) * B s))
      (Y1 - ∑ s, p s / (1 + r) * B s))
    (hu2 : ∀ s, HasDerivAt u (du (Y2 s + B s)) (Y2 s + B s))
    (hmax : ∀ B' : S → ℝ, Y1 - ∑ s, p s / (1 + r) * B' s ∈ D → (∀ s, Y2 s + B' s ∈ D) →
      lifetimeUtility Ω u p r β Y1 Y2 B' ≤ lifetimeUtility Ω u p r β Y1 Y2 B) (s : S) :
    p s / (1 + r) * du (Y1 - ∑ s, p s / (1 + r) * B s) = Ω.prob s * β * du (Y2 s + B s) :=
  foc_of_isPlanOptimum Ω hD p (C2 := fun s => Y2 s + B s) hC1 hC2 hu1 hu2
    (isPlanOptimum_of_lifetime Ω p r β Y1 Y2 B hmax) s

/-- Necessity of (5) on the positive orthant, O&R pp. 275–277: with consumption restricted to
`(0, ∞)` (the domain of CRRA and log utility) and the equality budget (4), an optimum with
`C₁ > 0`, `C₂ > 0` at which `u` is differentiable satisfies (5) in every state. -/
theorem foc_necessary_pos (Ω : StateSpace S) {u du : ℝ → ℝ} (p : S → ℝ) (r β Y1 C1 : ℝ)
    (Y2 C2 : S → ℝ) (hC1 : 0 < C1) (hC2 : ∀ s, 0 < C2 s)
    (hu1 : HasDerivAt u (du C1) C1) (hu2 : ∀ s, HasDerivAt u (du (C2 s)) (C2 s))
    (hbud : planValue p r C1 C2 = planValue p r Y1 Y2)
    (hmax : ∀ (C1' : ℝ) (C2' : S → ℝ), 0 < C1' → (∀ s, 0 < C2' s) →
      planValue p r C1' C2' = planValue p r Y1 Y2 →
        planUtility Ω u β C1' C2' ≤ planUtility Ω u β C1 C2) (s : S) :
    p s / (1 + r) * du C1 = Ω.prob s * β * du (C2 s) :=
  foc_of_isPlanOptimum Ω isOpen_Ioi p hC1 hC2 hu1 hu2
    (isPlanOptimum_of_budget_eq Ω (D := Set.Ioi 0) p r β Y1 C1 Y2 C2 hbud
      fun C1' C2' h1 h2 hv => hmax C1' C2' h1 h2 hv) s

/-- O&R (6), p. 276, as a consequence of optimality: at a plan optimum in an open `D` with
`u` differentiable at the plan and `u′(C₁) ≠ 0`, the marginal rate of substitution equals the
relative price, `π(s)βu′(C₂(s))/u′(C₁) = p(s)/(1+r)`. -/
theorem mrs_eq_price_of_optimum (Ω : StateSpace S) {D : Set ℝ} (hD : IsOpen D)
    {u du : ℝ → ℝ} (p : S → ℝ) {r β C1 : ℝ} {C2 : S → ℝ} (hC1 : C1 ∈ D)
    (hC2 : ∀ s, C2 s ∈ D) (hu1 : HasDerivAt u (du C1) C1)
    (hu2 : ∀ s, HasDerivAt u (du (C2 s)) (C2 s)) (hopt : IsPlanOptimum Ω D u p r β C1 C2)
    (hd : du C1 ≠ 0) (s : S) :
    Ω.prob s * β * du (C2 s) / du C1 = p s / (1 + r) :=
  mrs_eq_price Ω p r β du C1 C2 hd (foc_of_isPlanOptimum Ω hD p hC1 hC2 hu1 hu2 hopt) s

/-- The stochastic Euler equation for bonds (8), O&R p. 277, as a consequence of optimality:
at a plan optimum in an open `D` with `u` differentiable at the plan, `Σ p(s) = 1` (O&R (7))
and `1 + r ≠ 0`, `u′(C₁) = (1+r)βE[u′(C₂)]`. -/
theorem bond_euler_of_optimum (Ω : StateSpace S) {D : Set ℝ} (hD : IsOpen D)
    {u du : ℝ → ℝ} (p : S → ℝ) {r β C1 : ℝ} {C2 : S → ℝ} (hr : 1 + r ≠ 0)
    (hsum : ∑ s, p s = 1) (hC1 : C1 ∈ D) (hC2 : ∀ s, C2 s ∈ D)
    (hu1 : HasDerivAt u (du C1) C1) (hu2 : ∀ s, HasDerivAt u (du (C2 s)) (C2 s))
    (hopt : IsPlanOptimum Ω D u p r β C1 C2) :
    du C1 = (1 + r) * β * Ω.expect (fun s => du (C2 s)) :=
  bond_euler Ω p hr hsum β du C1 C2 (foc_of_isPlanOptimum Ω hD p hC1 hC2 hu1 hu2 hopt)

/-- The across-state condition (9), O&R p. 277, as a consequence of optimality: at a plan
optimum in an open `D` with `u` differentiable at the plan, `1 + r ≠ 0`, `β ≠ 0` and
`u′(C₁) ≠ 0`, `π(s)u′(C₂(s))/[π(t)u′(C₂(t))] = p(s)/p(t)`. -/
theorem mrs_ratio_of_optimum (Ω : StateSpace S) {D : Set ℝ} (hD : IsOpen D)
    {u du : ℝ → ℝ} (p : S → ℝ) {r β C1 : ℝ} {C2 : S → ℝ} (hr : 1 + r ≠ 0) (hβ : β ≠ 0)
    (hC1 : C1 ∈ D) (hC2 : ∀ s, C2 s ∈ D) (hu1 : HasDerivAt u (du C1) C1)
    (hu2 : ∀ s, HasDerivAt u (du (C2 s)) (C2 s)) (hopt : IsPlanOptimum Ω D u p r β C1 C2)
    (hd : du C1 ≠ 0) (s t : S) :
    Ω.prob s * du (C2 s) / (Ω.prob t * du (C2 t)) = p s / p t :=
  mrs_ratio_eq_price_ratio Ω p hr hβ du C1 C2 hd
    (foc_of_isPlanOptimum Ω hD p hC1 hC2 hu1 hu2 hopt) s t

/-- The budget binds at an optimum when date-1 marginal utility is nonzero, O&R p. 275
(implicit): under the `≤` form of (4), if `(C₁, C₂)` is optimal among plans in the open set
`D`, `u` is differentiable at `C₁` and `u′(C₁) ≠ 0`, then (4) holds with equality. Proof: with
slack, `C₁ + t` is feasible for small `t` of either sign, forcing `u′(C₁) = 0`. -/
theorem budget_binds_of_optimum (Ω : StateSpace S) {D : Set ℝ} (hD : IsOpen D)
    {u du : ℝ → ℝ} (p : S → ℝ) (r β Y1 C1 : ℝ) (Y2 C2 : S → ℝ) (hC1 : C1 ∈ D)
    (hC2 : ∀ s, C2 s ∈ D) (hu1 : HasDerivAt u (du C1) C1)
    (hbud : planValue p r C1 C2 ≤ planValue p r Y1 Y2)
    (hmax : ∀ (C1' : ℝ) (C2' : S → ℝ), C1' ∈ D → (∀ s, C2' s ∈ D) →
      planValue p r C1' C2' ≤ planValue p r Y1 Y2 →
        planUtility Ω u β C1' C2' ≤ planUtility Ω u β C1 C2)
    (hd : du C1 ≠ 0) :
    planValue p r C1 C2 = planValue p r Y1 Y2 := by
  by_contra hne
  have hlt : planValue p r C1 C2 < planValue p r Y1 Y2 := lt_of_le_of_ne hbud hne
  set g : ℝ → ℝ := fun t => planUtility Ω u β (C1 + t) C2 with hg
  have hloc : IsLocalMax g 0 := by
    have h1 : ∀ᶠ t in nhds (0 : ℝ), C1 + t ∈ D := by
      have hc : Continuous (fun t : ℝ => C1 + t) := by fun_prop
      exact hc.continuousAt.preimage_mem_nhds (by simpa using hD.mem_nhds hC1)
    filter_upwards [h1, eventually_lt_nhds (sub_pos.mpr hlt)] with t ht1 ht2
    have hg0 : g 0 = planUtility Ω u β C1 C2 := by simp [hg]
    rw [hg0]
    refine hmax _ _ ht1 hC2 ?_
    simp only [planValue] at ht2 ⊢
    linarith
  have hderiv : HasDerivAt g (du C1) 0 := by
    have hin : HasDerivAt (fun t : ℝ => C1 + t) 1 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_add C1
    have hu1' : HasDerivAt u (du C1) (C1 + 0) := by simpa using hu1
    have hA := (hu1'.comp 0 hin).add_const (∑ s, Ω.prob s * β * u (C2 s))
    rw [mul_one] at hA
    exact hA
  exact hd (hloc.hasDerivAt_eq_zero hderiv)

/-- The concave-tangent bound for plans (used for sufficiency of (5), O&R p. 276): if `u` is
concave on `D` with derivative `du x` at every `x ∈ D`, `β ≥ 0`, every `π(s) ≥ 0`, and
`(C₁, C₂)` in `D` satisfies (5), then for every plan `(C₁′, C₂′)` in `D`,
`U(C₁′, C₂′) ≤ U(C₁, C₂) + u′(C₁)·[PV(C₁′, C₂′) − PV(C₁, C₂)]`. -/
theorem planUtility_le_of_foc (Ω : StateSpace S) {D : Set ℝ} {u du : ℝ → ℝ}
    (hconc : ConcaveOn ℝ D u) (hu : ∀ x ∈ D, HasDerivAt u (du x) x) (p : S → ℝ)
    {r β : ℝ} (hβ : 0 ≤ β) {C1 C1' : ℝ} {C2 C2' : S → ℝ} (hC1 : C1 ∈ D)
    (hC2 : ∀ s, C2 s ∈ D) (hC1' : C1' ∈ D) (hC2' : ∀ s, C2' s ∈ D)
    (hfoc : ∀ s, p s / (1 + r) * du C1 = Ω.prob s * β * du (C2 s)) :
    planUtility Ω u β C1' C2' ≤
      planUtility Ω u β C1 C2 + du C1 * (planValue p r C1' C2' - planValue p r C1 C2) := by
  have h1 := supergradient_of_concaveOn hconc hC1 hC1' (hu C1 hC1)
  have h2 : ∀ s, Ω.prob s * β * u (C2' s) ≤
      Ω.prob s * β * u (C2 s) + p s / (1 + r) * du C1 * (C2' s - C2 s) := fun s => by
    have := supergradient_of_concaveOn hconc (hC2 s) (hC2' s) (hu _ (hC2 s))
    rw [hfoc s]
    have hk := mul_le_mul_of_nonneg_left this (mul_nonneg (Ω.prob_nonneg s) hβ)
    linarith
  have hsum := Finset.sum_le_sum fun s (_ : s ∈ Finset.univ) => h2 s
  rw [Finset.sum_add_distrib] at hsum
  have e : ∑ s, p s / (1 + r) * du C1 * (C2' s - C2 s) =
      du C1 * (∑ s, p s / (1 + r) * C2' s - ∑ s, p s / (1 + r) * C2 s) := by
    rw [mul_sub, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun s _ => by ring
  simp only [planUtility, planValue]
  rw [e] at hsum
  nlinarith

/-- Characterisation of the optimum under the equality budget (4)/(18), O&R pp. 275–277: for
`u` concave on an open set `D` and differentiable there, `β ≥ 0`, and a
plan `(C₁, C₂)` in `D` satisfying (4), the plan maximises expected utility over all plans in
`D` satisfying (4) iff the first-order conditions (5) hold in every state. -/
theorem optimum_iff_foc_budget_eq (Ω : StateSpace S) {D : Set ℝ} (hD : IsOpen D)
    {u du : ℝ → ℝ} (hconc : ConcaveOn ℝ D u) (hu : ∀ x ∈ D, HasDerivAt u (du x) x)
    (p : S → ℝ) {r β : ℝ} (hβ : 0 ≤ β) (Y1 C1 : ℝ) (Y2 C2 : S → ℝ) (hC1 : C1 ∈ D)
    (hC2 : ∀ s, C2 s ∈ D) (hbud : planValue p r C1 C2 = planValue p r Y1 Y2) :
    (∀ (C1' : ℝ) (C2' : S → ℝ), C1' ∈ D → (∀ s, C2' s ∈ D) →
      planValue p r C1' C2' = planValue p r Y1 Y2 →
        planUtility Ω u β C1' C2' ≤ planUtility Ω u β C1 C2) ↔
      ∀ s, p s / (1 + r) * du C1 = Ω.prob s * β * du (C2 s) := by
  constructor
  · intro hmax
    exact foc_of_isPlanOptimum Ω hD p hC1 hC2 (hu C1 hC1) (fun s => hu _ (hC2 s))
      (isPlanOptimum_of_budget_eq Ω p r β Y1 C1 Y2 C2 hbud hmax)
  · intro hfoc C1' C2' h1 h2 hv
    have := planUtility_le_of_foc Ω hconc hu p hβ hC1 hC2 h1 h2 hfoc
    rw [hv, hbud, sub_self, mul_zero, add_zero] at this
    exact this

/-- Characterisation of the optimum under the `≤` budget, O&R pp. 275–277: for `u` concave and
differentiable on an open set `D` with `u′ > 0` on `D` (more is preferred), `β ≥ 0`, and a
plan `(C₁, C₂)` in `D` with `PV ≤ PV(Y₁, Y₂)`, the plan maximises expected utility over all
plans in `D` with `PV ≤ PV(Y₁, Y₂)` iff the budget (4) binds and (5) holds in every state. -/
theorem optimum_iff_foc_budget_le (Ω : StateSpace S) {D : Set ℝ} (hD : IsOpen D)
    {u du : ℝ → ℝ} (hconc : ConcaveOn ℝ D u) (hu : ∀ x ∈ D, HasDerivAt u (du x) x)
    (hdpos : ∀ x ∈ D, 0 < du x) (p : S → ℝ) {r β : ℝ} (hβ : 0 ≤ β) (Y1 C1 : ℝ)
    (Y2 C2 : S → ℝ) (hC1 : C1 ∈ D) (hC2 : ∀ s, C2 s ∈ D)
    (hbud : planValue p r C1 C2 ≤ planValue p r Y1 Y2) :
    (∀ (C1' : ℝ) (C2' : S → ℝ), C1' ∈ D → (∀ s, C2' s ∈ D) →
      planValue p r C1' C2' ≤ planValue p r Y1 Y2 →
        planUtility Ω u β C1' C2' ≤ planUtility Ω u β C1 C2) ↔
      planValue p r C1 C2 = planValue p r Y1 Y2 ∧
        ∀ s, p s / (1 + r) * du C1 = Ω.prob s * β * du (C2 s) := by
  constructor
  · intro hmax
    exact ⟨budget_binds_of_optimum Ω hD p r β Y1 C1 Y2 C2 hC1 hC2 (hu C1 hC1) hbud hmax
        (hdpos C1 hC1).ne',
      foc_of_isPlanOptimum Ω hD p hC1 hC2 (hu C1 hC1) (fun s => hu _ (hC2 s))
        (isPlanOptimum_of_budget_le Ω p r β Y1 C1 Y2 C2 hbud hmax)⟩
  · rintro ⟨heq, hfoc⟩ C1' C2' h1 h2 hv
    have := planUtility_le_of_foc Ω hconc hu p hβ hC1 hC2 h1 h2 hfoc
    have hneg : du C1 * (planValue p r C1' C2' - planValue p r C1 C2) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (hdpos C1 hC1).le (by rw [heq]; linarith)
    linarith

/-- Characterisation of the optimum in the book's problem in `B₂`, O&R p. 276: for `u` concave
and differentiable on an open set `D`, `β ≥ 0`, and holdings `B₂` with consumption in `D`, the
holdings maximise `U₁` over all holdings with consumption in `D` iff the first-order
conditions (5) hold in every state (necessity: `foc_necessary`; sufficiency:
`foc_sufficient`). -/
theorem foc_iff (Ω : StateSpace S) {D : Set ℝ} (hD : IsOpen D) {u du : ℝ → ℝ}
    (hconc : ConcaveOn ℝ D u) (hu : ∀ x ∈ D, HasDerivAt u (du x) x) (p : S → ℝ)
    {r β : ℝ} (hβ : 0 ≤ β) (Y1 : ℝ) (Y2 B : S → ℝ)
    (hC1 : Y1 - ∑ s, p s / (1 + r) * B s ∈ D) (hC2 : ∀ s, Y2 s + B s ∈ D) :
    (∀ B' : S → ℝ, Y1 - ∑ s, p s / (1 + r) * B' s ∈ D → (∀ s, Y2 s + B' s ∈ D) →
      lifetimeUtility Ω u p r β Y1 Y2 B' ≤ lifetimeUtility Ω u p r β Y1 Y2 B) ↔
      ∀ s, p s / (1 + r) * du (Y1 - ∑ s, p s / (1 + r) * B s) =
        Ω.prob s * β * du (Y2 s + B s) := by
  constructor
  · intro hmax
    exact foc_necessary Ω hD p r β Y1 Y2 B hC1 hC2 (hu _ hC1) (fun s => hu _ (hC2 s)) hmax
  · intro hfoc B' h1 h2
    exact foc_sufficient Ω hconc hu p hβ Y1 Y2 B B' hC1 hC2 h1 h2 hfoc

/-! ## Full insurance and actuarially fair prices (§5.1.4, pp. 277–278) -/

/-- Full insurance iff actuarially fair prices, O&R (10), p. 277, for any number of states: if the
FOCs (5) hold with `Σ p(s) = 1`, `u′` strictly decreasing, `u′(C₁) ≠ 0`, `β > 0`, `1 + r > 0` and
every `π(s) > 0`, then date-2 consumption is the same in all states iff `p(s) = π(s)` for all
`s`. -/
theorem full_insurance_iff_fair (Ω : StateSpace S) (p : S → ℝ) {r β : ℝ} (hr : 0 < 1 + r)
    (hβ : 0 < β) (hsum : ∑ s, p s = 1) {du : ℝ → ℝ} (hanti : StrictAnti du) (C1 : ℝ)
    (C2 : S → ℝ) (hd : du C1 ≠ 0) (hπ : ∀ s, 0 < Ω.prob s)
    (hfoc : ∀ s, p s / (1 + r) * du C1 = Ω.prob s * β * du (C2 s)) :
    (∀ s t, C2 s = C2 t) ↔ ∀ s, p s = Ω.prob s := by
  have hk : du C1 / (1 + r) ≠ 0 := div_ne_zero hd hr.ne'
  constructor
  · intro hc s
    have key : ∀ t, p s * Ω.prob t = p t * Ω.prob s := fun t => by
      have hs := hfoc s
      have ht := hfoc t
      rw [← hc s t] at ht
      refine mul_right_cancel₀ hk ?_
      linear_combination Ω.prob t * hs - Ω.prob s * ht
    have := Finset.sum_congr rfl fun t (_ : t ∈ Finset.univ) => key t
    rwa [← Finset.mul_sum, Ω.prob_sum, mul_one, ← Finset.sum_mul, hsum, one_mul] at this
  · intro hp
    have e : ∀ s, du (C2 s) = du C1 / ((1 + r) * β) := fun s => by
      have h := hfoc s
      rw [hp s] at h
      have hπs := (hπ s).ne'
      field_simp at h ⊢
      linear_combination -h
    intro s t
    exact hanti.injective ((e s).trans (e t).symm)

/-- Full insurance iff actuarially fair relative prices for two given states, O&R (9)–(10),
p. 277: under the FOCs (5) with `u′ > 0` at the consumption points, `u′` strictly decreasing,
`β > 0`, `1 + r > 0` and `π > 0`, `C₂(s) = C₂(t)` iff `p(s)/p(t) = π(s)/π(t)`. -/
theorem full_insurance_iff_fair_ratio (Ω : StateSpace S) (p : S → ℝ) {r β : ℝ}
    (hr : 0 < 1 + r) (hβ : 0 < β) {du : ℝ → ℝ} (hanti : StrictAnti du) (C1 : ℝ) (C2 : S → ℝ)
    (hd : 0 < du C1) (hd2 : ∀ s, 0 < du (C2 s)) (hπ : ∀ s, 0 < Ω.prob s)
    (hfoc : ∀ s, p s / (1 + r) * du C1 = Ω.prob s * β * du (C2 s)) (s t : S) :
    C2 s = C2 t ↔ p s / p t = Ω.prob s / Ω.prob t := by
  have e : ∀ s, p s = (1 + r) * β * (Ω.prob s * du (C2 s)) / du C1 := fun s => by
    rw [eq_div_iff hd.ne', show (1 + r) * β * (Ω.prob s * du (C2 s)) =
      (1 + r) * (Ω.prob s * β * du (C2 s)) by ring, ← hfoc s]
    field_simp
  have hπt := (hπ t).ne'
  have hπs := (hπ s).ne'
  have hdt := (hd2 t).ne'
  rw [e s, e t]
  constructor
  · intro h
    rw [h]
    field_simp
  · intro h
    apply hanti.injective
    field_simp at h
    linear_combination h

/-! ## Risk aversion (§5.1.5, pp. 278–279) -/

/-- The CRRA version of (11), O&R pp. 278–279, in exact (not differential) form: if the FOCs (5)
hold with `u′(C) = C^{-ρ}`, `ρ > 0`, and all quantities positive, then
`log(C₂(t)/C₂(s)) = (1/ρ) log(p(s)/p(t)) + (1/ρ) log(π(t)/π(s))`; in particular `1/ρ` is the
elasticity of relative state consumption with respect to relative AD prices. -/
theorem crra_log_ratio (Ω : StateSpace S) (p : S → ℝ) {r β ρ C1 : ℝ} (C2 : S → ℝ)
    (hr : 0 < 1 + r) (hβ : 0 < β) (hρ : 0 < ρ) (hC1 : 0 < C1) (hC2 : ∀ s, 0 < C2 s)
    (hp : ∀ s, 0 < p s) (hπ : ∀ s, 0 < Ω.prob s)
    (hfoc : ∀ s, p s / (1 + r) * C1 ^ (-ρ) = Ω.prob s * β * C2 s ^ (-ρ)) (s t : S) :
    Real.log (C2 t / C2 s) =
      1 / ρ * Real.log (p s / p t) + 1 / ρ * Real.log (Ω.prob t / Ω.prob s) := by
  have L : ∀ s, Real.log (p s) - Real.log (1 + r) - ρ * Real.log C1 =
      Real.log (Ω.prob s) + Real.log β - ρ * Real.log (C2 s) := fun s => by
    have h := congrArg Real.log (hfoc s)
    have h1 := (hp s).ne'
    have h2 := (hπ s).ne'
    have h3 := (hC2 s).ne'
    rw [Real.log_mul (div_ne_zero h1 hr.ne') (Real.rpow_pos_of_pos hC1 _).ne',
      Real.log_div h1 hr.ne', Real.log_rpow hC1,
      Real.log_mul (mul_ne_zero h2 hβ.ne') (Real.rpow_pos_of_pos (hC2 s) _).ne',
      Real.log_mul h2 hβ.ne', Real.log_rpow (hC2 s)] at h
    linarith
  have Ls := L s
  have Lt := L t
  rw [Real.log_div (hC2 t).ne' (hC2 s).ne', Real.log_div (hp s).ne' (hp t).ne',
    Real.log_div (hπ t).ne' (hπ s).ne']
  have : ρ * (Real.log (C2 t) - Real.log (C2 s)) = (Real.log (p s) - Real.log (p t)) +
      (Real.log (Ω.prob t) - Real.log (Ω.prob s)) := by linarith
  field_simp
  linarith

/-- The Arrow–Pratt coefficient of relative risk aversion, O&R (12)–(13), pp. 278–279: for CRRA
utility `u(C) = C^{1−ρ}/(1−ρ)` (`ρ ≠ 1`) and `C > 0`, `u′(C) = C^{−ρ}`,
`u″(C) = −ρC^{−ρ−1}`, and `−Cu″(C)/u′(C) = ρ`. -/
theorem crra_arrow_pratt {ρ c : ℝ} (hρ : ρ ≠ 1) (hc : 0 < c) :
    HasDerivAt (fun x => x ^ (1 - ρ) / (1 - ρ)) (c ^ (-ρ)) c ∧
      HasDerivAt (fun x => x ^ (-ρ)) (-ρ * c ^ (-ρ - 1)) c ∧
      -(c * (-ρ * c ^ (-ρ - 1))) / c ^ (-ρ) = ρ := by
  have h1ρ : 1 - ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm hρ)
  refine ⟨?_, Real.hasDerivAt_rpow_const (Or.inl hc.ne'), ?_⟩
  · have h := (Real.hasDerivAt_rpow_const (p := 1 - ρ) (Or.inl hc.ne')).div_const (1 - ρ)
    refine HasDerivAt.congr_deriv h ?_
    rw [show 1 - ρ - 1 = -ρ by ring]
    field_simp
  · rw [Real.rpow_sub_one hc.ne']
    have : 0 < c ^ (-ρ) := Real.rpow_pos_of_pos hc _
    field_simp

/-! ## Log utility (§5.1.6, pp. 279–280) -/

/-- Log utility, the spending rule behind O&R (16), pp. 279–280: with `u′(C) = 1/C` the FOCs (5)
say `p(s)C₂(s)/(1+r) = π(s)βC₁`. -/
theorem log_state_spending_eq (Ω : StateSpace S) (p : S → ℝ) {r β C1 : ℝ} (C2 : S → ℝ)
    (hC1 : 0 < C1) (hC2 : ∀ s, 0 < C2 s)
    (hfoc : ∀ s, p s / (1 + r) * C1⁻¹ = Ω.prob s * β * (C2 s)⁻¹) (s : S) :
    p s / (1 + r) * C2 s = Ω.prob s * β * C1 := by
  have h := hfoc s
  have := (hC2 s).ne'
  field_simp at h
  linear_combination h

/-- Log-utility consumption demands, O&R (15)–(16) and footnote 9, p. 280: if the FOCs (5) hold
with `u′(C) = 1/C` and the budget (4) holds, then with `W₁ = Y₁ + Σ p(s)Y₂(s)/(1+r)`:
`C₁ = W₁/(1+β)`, `p(s)C₂(s)/(1+r) = π(s)βW₁/(1+β)`, and (if `p(s) > 0`)
`C₂(s) = π(s)(1+r)βW₁/((1+β)p(s))`. -/
theorem log_consumption_demands (Ω : StateSpace S) (p : S → ℝ) {r β C1 Y1 : ℝ}
    (C2 Y2 : S → ℝ) (hr : 0 < 1 + r) (hβ : 0 < β) (hC1 : 0 < C1) (hC2 : ∀ s, 0 < C2 s)
    (hfoc : ∀ s, p s / (1 + r) * C1⁻¹ = Ω.prob s * β * (C2 s)⁻¹)
    (hbud : C1 + ∑ s, p s / (1 + r) * C2 s = Y1 + ∑ s, p s / (1 + r) * Y2 s) :
    C1 = (Y1 + ∑ s, p s / (1 + r) * Y2 s) / (1 + β) ∧
      (∀ s, p s / (1 + r) * C2 s =
        Ω.prob s * β / (1 + β) * (Y1 + ∑ s, p s / (1 + r) * Y2 s)) ∧
      (∀ s, 0 < p s → C2 s =
        Ω.prob s * (1 + r) * β * (Y1 + ∑ s, p s / (1 + r) * Y2 s) / ((1 + β) * p s)) := by
  have hsp := log_state_spending_eq Ω p C2 hC1 hC2 hfoc
  have hsum : ∑ s, p s / (1 + r) * C2 s = β * C1 := by
    rw [Finset.sum_congr rfl fun s _ => hsp s, ← Finset.sum_mul, ← Finset.sum_mul,
      Ω.prob_sum]
    ring
  have hC1eq : C1 = (Y1 + ∑ s, p s / (1 + r) * Y2 s) / (1 + β) := by
    rw [eq_div_iff (by positivity), ← hbud, hsum]; ring
  refine ⟨hC1eq, fun s => by rw [hsp s, hC1eq]; field_simp, fun s hps => ?_⟩
  have h := hsp s
  rw [hC1eq] at h
  generalize Y1 + ∑ s, p s / (1 + r) * Y2 s = W at h ⊢
  rw [eq_div_iff (by positivity)]
  field_simp at h
  linear_combination h

/-- The log-utility current account, O&R (17), p. 280:
`CA₁ = Y₁ − C₁ = βY₁/(1+β) − [Σ p(s)Y₂(s)/(1+r)]/(1+β)`. -/
theorem log_current_account (Ω : StateSpace S) (p : S → ℝ) {r β C1 Y1 : ℝ}
    (C2 Y2 : S → ℝ) (hr : 0 < 1 + r) (hβ : 0 < β) (hC1 : 0 < C1) (hC2 : ∀ s, 0 < C2 s)
    (hfoc : ∀ s, p s / (1 + r) * C1⁻¹ = Ω.prob s * β * (C2 s)⁻¹)
    (hbud : C1 + ∑ s, p s / (1 + r) * C2 s = Y1 + ∑ s, p s / (1 + r) * Y2 s) :
    Y1 - C1 = β / (1 + β) * Y1 - 1 / (1 + β) * ∑ s, p s / (1 + r) * Y2 s := by
  rw [(log_consumption_demands Ω p C2 Y2 hr hβ hC1 hC2 hfoc hbud).1]
  field_simp
  ring

/-- O&R footnote 10, p. 280: the world-market value of date-2 output equals its expected value,
`Σ p(s)Y₂(s) = E[Y₂]`, for every output vector `Y₂` iff prices are actuarially fair, `p = π`. -/
theorem value_eq_expectation_iff (Ω : StateSpace S) (p : S → ℝ) :
    (∀ Y2 : S → ℝ, ∑ s, p s * Y2 s = Ω.expect Y2) ↔ ∀ s, p s = Ω.prob s := by
  classical
  constructor
  · intro h s
    simpa [StateSpace.expect] using h (fun t => if t = s then 1 else 0)
  · intro h Y2
    simp [StateSpace.expect, h]

/-- O&R footnote 10, p. 280, for two states and a given output vector: if `p` and `π` are
probability vectors and `Y₂(1) ≠ Y₂(2)`, then `p(1)Y₂(1) + p(2)Y₂(2) = E[Y₂]` iff
`p = π`. (With `Y₂(1) = Y₂(2)` the equality holds at any prices.) -/
theorem value_eq_expectation_two_iff {p1 p2 π1 π2 Ya Yb : ℝ} (hp : p1 + p2 = 1)
    (hπ : π1 + π2 = 1) (hY : Ya ≠ Yb) :
    p1 * Ya + p2 * Yb = π1 * Ya + π2 * Yb ↔ p1 = π1 ∧ p2 = π2 := by
  constructor
  · intro h
    have h' : (p1 - π1) * (Ya - Yb) = 0 := by linear_combination h + Yb * hπ - Yb * hp
    rcases mul_eq_zero.mp h' with h1 | h1
    · exact ⟨by linarith, by linarith⟩
    · exact absurd (sub_eq_zero.mp h1) hY
  · rintro ⟨rfl, rfl⟩
    rfl

/-! ## Appendix 5B: comparative advantage and gross flows (pp. 337–340) -/

/-- The "current-account autarky" interest rate, O&R (78), p. 338, for any number of states: if
the country consumes `C₁ = Y₁` and `C₂(s) = π(s)V/p(s)` with `V = Σ p(s)Y₂(s)`, and the gross
rate `R = 1 + r^CA` satisfies the log-utility bond Euler equation (8),
`1/Y₁ = RβE[1/C₂]`, then `R = V/(βY₁)`. -/
theorem rCA_formula (Ω : StateSpace S) (p : S → ℝ) {β Y1 R : ℝ} (Y2 : S → ℝ) (hβ : 0 < β)
    (hY1 : 0 < Y1) (hp : ∀ s, 0 < p s) (hπ : ∀ s, 0 < Ω.prob s) (hsum : ∑ s, p s = 1)
    (hV : 0 < ∑ s, p s * Y2 s)
    (hE : Y1⁻¹ = R * β * Ω.expect (fun s => (Ω.prob s * (∑ t, p t * Y2 t) / p s)⁻¹)) :
    R = (∑ s, p s * Y2 s) / (β * Y1) := by
  have hE' : Ω.expect (fun s => (Ω.prob s * (∑ t, p t * Y2 t) / p s)⁻¹) =
      (∑ s, p s * Y2 s)⁻¹ := by
    simp only [StateSpace.expect]
    rw [Finset.sum_congr rfl fun s _ => show Ω.prob s * (Ω.prob s * (∑ t, p t * Y2 t) / p s)⁻¹
      = p s * (∑ t, p t * Y2 t)⁻¹ by
        have := (hπ s).ne'; have := (hp s).ne'; field_simp, ← Finset.sum_mul, hsum, one_mul]
  rw [hE'] at hE
  rw [eq_div_iff (by positivity)]
  field_simp at hE
  linear_combination -hE

/-- The autarky interest rate, O&R (79), p. 338: if `R = 1 + r^A` satisfies the log-utility bond
Euler equation (8) at the endowment, `1/Y₁ = RβE[1/Y₂]`, then `R = [βY₁E(1/Y₂)]⁻¹`
(for two states: `R = (1/(βY₁))[π(1)/Y₂(1) + π(2)/Y₂(2)]⁻¹`). -/
theorem rA_formula (Ω : StateSpace S) {β Y1 R : ℝ} (Y2 : S → ℝ) (hY1 : Y1 ≠ 0)
    (hE : Y1⁻¹ = R * β * Ω.expect (fun s => (Y2 s)⁻¹)) :
    R = (β * Y1 * Ω.expect (fun s => (Y2 s)⁻¹))⁻¹ := by
  have hne : Ω.expect (fun s => (Y2 s)⁻¹) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hE
    exact inv_ne_zero hY1 hE
  have h1 : R * (β * Y1 * Ω.expect (fun s => (Y2 s)⁻¹)) = 1 := by
    rw [show R * (β * Y1 * Ω.expect (fun s => (Y2 s)⁻¹)) =
      (R * β * Ω.expect (fun s => (Y2 s)⁻¹)) * Y1 by ring, ← hE, inv_mul_cancel₀ hY1]
  exact eq_inv_of_mul_eq_one_left h1

/-- The current account has the sign of `r − r^CA`, O&R Appendix 5B and footnote 51, p. 338,
for any `β(1+r)`: with `V = Σ p(s)Y₂(s)` and `1 + r^CA = V/(βY₁)`, the log-utility current
account (17) equals `βY₁(r − r^CA)/((1+β)(1+r))`. -/
theorem current_account_eq_mul_rCA {β Y1 V r rCA : ℝ} (hβ : 0 < β) (hY1 : 0 < Y1)
    (hr : 0 < 1 + r) (hCA : 1 + rCA = V / (β * Y1)) :
    β / (1 + β) * Y1 - 1 / (1 + β) * (V / (1 + r)) =
      β * Y1 / ((1 + β) * (1 + r)) * (r - rCA) := by
  have hV : V = β * Y1 * (1 + rCA) := by rw [hCA]; field_simp
  rw [hV]
  field_simp
  ring

/-- Sign of the current account, O&R footnote 51, p. 338: `CA₁ > 0` iff `r > r^CA` and
`CA₁ < 0` iff `r < r^CA` (log utility, any `β(1+r)`). -/
theorem current_account_sign_iff {β Y1 V r rCA : ℝ} (hβ : 0 < β) (hY1 : 0 < Y1)
    (hr : 0 < 1 + r) (hCA : 1 + rCA = V / (β * Y1)) :
    (0 < β / (1 + β) * Y1 - 1 / (1 + β) * (V / (1 + r)) ↔ rCA < r) ∧
      (β / (1 + β) * Y1 - 1 / (1 + β) * (V / (1 + r)) < 0 ↔ r < rCA) := by
  rw [current_account_eq_mul_rCA hβ hY1 hr hCA]
  have hk : 0 < β * Y1 / ((1 + β) * (1 + r)) := by positivity
  constructor
  · rw [mul_pos_iff_of_pos_left hk, sub_pos]
  · constructor
    · intro h
      by_contra h'
      push Not at h'
      have := mul_nonneg hk.le (sub_nonneg.mpr h')
      linarith
    · intro h
      have := mul_neg_of_pos_of_neg hk (sub_neg.mpr h)
      linarith

/-- The sign of `CA₁` is NOT that of `r − r^A`, O&R p. 338 ("not `r − r^A`"): a
numerical case with `π = (1/2, 1/2)`, `Y₁ = 1`, `Y₂ = (1, 3)`, `β = 1`, `p = (1/10, 9/10)` and
`r = 1`. The autarky rate (79) is `r^A = 1/2 < r`, yet the current account (17) is
`1/2 − 2.8/4 = −1/5 < 0`. -/
theorem current_account_sign_not_autarky_rate :
    (1 : ℝ) / (1 * 1 * ((1 / 2) / 1 + (1 / 2) / 3)) - 1 < 1 ∧
      (1 : ℝ) / (1 + 1) * 1 - 1 / (1 + 1) * (((1 / 10) * 1 + (9 / 10) * 3) / (1 + 1)) < 0 := by
  norm_num

/-- No output uncertainty, O&R footnote 50, p. 338: if `Y₂(1) = Y₂(2) = Y₂`, `p` and `π` are
probability vectors, then `1 + r^A = [βY₁(π(1)/Y₂ + π(2)/Y₂)]⁻¹` equals
`1 + r^CA = (p(1)Y₂ + p(2)Y₂)/(βY₁)`, and the current account (17) is
`CA₁ = (Y₂/(1+β))[1/(1+r^A) − 1/(1+r)]`, where `1/(1+r^A) = βY₁(π(1)/Y₂ + π(2)/Y₂)`. -/
theorem no_output_risk {π1 π2 p1 p2 β Y1 Y2 r : ℝ} (hπ : π1 + π2 = 1) (hp : p1 + p2 = 1)
    (hβ : 0 < β) (hY1 : 0 < Y1) (hY2 : 0 < Y2) (hr : 0 < 1 + r) :
    (β * Y1 * (π1 / Y2 + π2 / Y2))⁻¹ = (p1 * Y2 + p2 * Y2) / (β * Y1) ∧
      β / (1 + β) * Y1 - 1 / (1 + β) * ((p1 * Y2 + p2 * Y2) / (1 + r)) =
        Y2 / (1 + β) * ((β * Y1 * (π1 / Y2 + π2 / Y2)) - (1 + r)⁻¹) := by
  have e1 : π1 / Y2 + π2 / Y2 = 1 / Y2 := by rw [← add_div, hπ]
  have e2 : p1 * Y2 + p2 * Y2 = Y2 := by rw [← add_mul, hp, one_mul]
  rw [e1, e2]
  constructor
  · field_simp
  · field_simp

/-- Log-utility autarky prices, O&R (80), p. 338: if the FOC (5) holds at the endowment
(`C₁ = Y₁`, `C₂ = Y₂`) with `u′(C) = 1/C`, the autarky AD prices are
`p^A(s)/(1+r^A) = π(s)βY₁/Y₂(s)`; hence `p^A(s)/p^A(t) = [π(s)/Y₂(s)]/[π(t)/Y₂(t)]`
(O&R p. 339). -/
theorem autarky_prices_log (Ω : StateSpace S) (pA : S → ℝ) {RA β Y1 : ℝ} (Y2 : S → ℝ)
    (hRA : 0 < RA) (hβ : 0 < β) (hY1 : 0 < Y1) (hY2 : ∀ s, 0 < Y2 s)
    (hπ : ∀ s, 0 < Ω.prob s)
    (hfoc : ∀ s, pA s / RA * Y1⁻¹ = Ω.prob s * β * (Y2 s)⁻¹) :
    (∀ s, pA s / RA = Ω.prob s * β * Y1 / Y2 s) ∧
      ∀ s t, pA s / pA t = (Ω.prob s / Y2 s) / (Ω.prob t / Y2 t) := by
  have e : ∀ s, pA s / RA = Ω.prob s * β * Y1 / Y2 s := fun s => by
    have h := hfoc s
    have := (hY2 s).ne'
    field_simp at h ⊢
    linear_combination h
  refine ⟨e, fun s t => ?_⟩
  have es : pA s = RA * (Ω.prob s * β * Y1 / Y2 s) := by rw [← e s]; field_simp
  have et : pA t = RA * (Ω.prob t * β * Y1 / Y2 t) := by rw [← e t]; field_simp
  have := (hY2 s).ne'
  have := (hY2 t).ne'
  have := (hπ t).ne'
  rw [es, et]
  field_simp

/-- The current account in terms of autarky and world AD prices, O&R (81), p. 339, for any
number of states: if the autarky prices `q^A(s) = p^A(s)/(1+r^A)` satisfy the log FOC at the
endowment (so (80) holds) and `Σ π(s) = 1`, then the log-utility current account (17) equals
`Σ_s (Y₂(s)/(1+β))[q^A(s) − p(s)/(1+r)]`. -/
theorem current_account_autarky_prices (Ω : StateSpace S) (p qA : S → ℝ) {r β Y1 : ℝ}
    (Y2 : S → ℝ) (hβ : 0 < β) (hY2 : ∀ s, 0 < Y2 s)
    (hfoc : ∀ s, qA s * Y1⁻¹ = Ω.prob s * β * (Y2 s)⁻¹) (hY1 : 0 < Y1) :
    β / (1 + β) * Y1 - 1 / (1 + β) * ∑ s, p s / (1 + r) * Y2 s =
      ∑ s, Y2 s / (1 + β) * (qA s - p s / (1 + r)) := by
  have e : ∀ s, Y2 s / (1 + β) * (qA s - p s / (1 + r)) =
      Ω.prob s * (β * Y1 / (1 + β)) - 1 / (1 + β) * (p s / (1 + r) * Y2 s) := fun s => by
    have h := hfoc s
    have := (hY2 s).ne'
    have hq : qA s = Ω.prob s * β * Y1 / Y2 s := by
      field_simp at h ⊢
      linear_combination h
    rw [hq]
    field_simp
  rw [Finset.sum_congr rfl fun s _ => e s, Finset.sum_sub_distrib, ← Finset.sum_mul,
    Ω.prob_sum, ← Finset.mul_sum]
  ring

/-- Gross asset flows with a balanced current account, O&R Appendix 5B.2, pp. 339–340: two
states, log utility, `C₁ = Y₁` and `r = r^CA`, i.e. `βY₁(1+r) = V = p(1)Y₂(1) + p(2)Y₂(2)`. If
the state FOCs (5) hold, then `C₂(s) = π(s)V/p(s)` and, writing `p^A(1)/p^A(2) =
[π(1)/Y₂(1)]/[π(2)/Y₂(2)]` (from (80)),
`B₂(1) = (p(2)/p(1))π(2)Y₂(1)[p^A(1)/p^A(2) − p(1)/p(2)]` and
`B₂(2) = −π(2)Y₂(1)[p^A(1)/p^A(2) − p(1)/p(2)]`. -/
theorem gross_flows_balanced {π1 π2 p1 p2 β Y1 Y21 Y22 r C21 C22 : ℝ} (hπ : π1 + π2 = 1)
    (hπ1 : 0 < π1) (hπ2 : 0 < π2) (hp1 : 0 < p1) (hp2 : 0 < p2) (hY1 : 0 < Y1)
    (hY21 : 0 < Y21) (hr : 0 < 1 + r) (hC21 : 0 < C21) (hC22 : 0 < C22)
    (hCA : β * Y1 * (1 + r) = p1 * Y21 + p2 * Y22)
    (hfoc1 : p1 / (1 + r) * Y1⁻¹ = π1 * β * C21⁻¹)
    (hfoc2 : p2 / (1 + r) * Y1⁻¹ = π2 * β * C22⁻¹) :
    C21 = π1 * (p1 * Y21 + p2 * Y22) / p1 ∧ C22 = π2 * (p1 * Y21 + p2 * Y22) / p2 ∧
      C21 - Y21 = p2 / p1 * π2 * Y21 * ((π1 / Y21) / (π2 / Y22) - p1 / p2) ∧
      C22 - Y22 = -(π2 * Y21 * ((π1 / Y21) / (π2 / Y22) - p1 / p2)) := by
  have e1 : C21 = π1 * (p1 * Y21 + p2 * Y22) / p1 := by
    rw [← hCA]
    field_simp at hfoc1 ⊢
    linear_combination hfoc1
  have e2 : C22 = π2 * (p1 * Y21 + p2 * Y22) / p2 := by
    rw [← hCA]
    field_simp at hfoc2 ⊢
    linear_combination hfoc2
  refine ⟨e1, e2, ?_, ?_⟩
  · obtain rfl : π1 = 1 - π2 := by linarith
    rw [e1]
    field_simp
    ring
  · obtain rfl : π1 = 1 - π2 := by linarith
    rw [e2]
    field_simp
    ring

/-- Gross AD purchases with an unbalanced current account, O&R Exercise 1, p. 345: two states,
log utility, FOCs (5) and budget (4). With `CA₁ = Y₁ − C₁`, `B₂(s) = C₂(s) − Y₂(s)` and
`p^A(1)/p^A(2) = [π(1)/Y₂(1)]/[π(2)/Y₂(2)]` (from (80)),
`p(1)B₂(1)/(1+r) = (p(2)π(2)Y₂(1)/(1+r))[p^A(1)/p^A(2) − p(1)/p(2)] + π(1)CA₁` and
`p(2)B₂(2)/(1+r) = −(p(2)π(2)Y₂(1)/(1+r))[p^A(1)/p^A(2) − p(1)/p(2)] + π(2)CA₁`. -/
theorem exercise1_gross_purchases {π1 π2 p1 p2 β C1 Y1 Y21 Y22 r C21 C22 : ℝ}
    (hπ : π1 + π2 = 1) (hπ2 : 0 < π2) (hp2 : 0 < p2) (hY21 : 0 < Y21) (hY22 : 0 < Y22)
    (hr : 0 < 1 + r) (hC1 : 0 < C1) (hC21 : 0 < C21) (hC22 : 0 < C22)
    (hfoc1 : p1 / (1 + r) * C1⁻¹ = π1 * β * C21⁻¹)
    (hfoc2 : p2 / (1 + r) * C1⁻¹ = π2 * β * C22⁻¹)
    (hbud : C1 + p1 / (1 + r) * C21 + p2 / (1 + r) * C22 =
      Y1 + p1 / (1 + r) * Y21 + p2 / (1 + r) * Y22) :
    p1 / (1 + r) * (C21 - Y21) =
        p2 * π2 * Y21 / (1 + r) * ((π1 / Y21) / (π2 / Y22) - p1 / p2) + π1 * (Y1 - C1) ∧
      p2 / (1 + r) * (C22 - Y22) =
        -(p2 * π2 * Y21 / (1 + r) * ((π1 / Y21) / (π2 / Y22) - p1 / p2)) +
          π2 * (Y1 - C1) := by
  have hr0 := hr.ne'
  have := hC1.ne'
  have s1 : p1 / (1 + r) * C21 = π1 * β * C1 := by
    have := hC21.ne'
    field_simp at hfoc1 ⊢
    linear_combination hfoc1
  have s2 : p2 / (1 + r) * C22 = π2 * β * C1 := by
    have := hC22.ne'
    field_simp at hfoc2 ⊢
    linear_combination hfoc2
  have hC1eq : C1 * (1 + β) = Y1 + p1 / (1 + r) * Y21 + p2 / (1 + r) * Y22 := by
    linear_combination hbud - s1 - s2 - β * C1 * hπ
  have t : p2 * π2 * Y21 / (1 + r) * ((π1 / Y21) / (π2 / Y22) - p1 / p2) =
      (π1 * p2 * Y22 - π2 * p1 * Y21) / (1 + r) := by
    have := hπ2.ne'
    have := hp2.ne'
    have := hY21.ne'
    have := hY22.ne'
    field_simp
  rw [t]
  constructor
  · linear_combination s1 + π1 * hC1eq + (p1 * Y21 / (1 + r)) * hπ
  · linear_combination s2 + π2 * hC1eq + (p2 * Y22 / (1 + r)) * hπ

/-! ## Exercise 3: quadratic utility, incomplete and complete markets (pp. 345–346) -/

/-- Quadratic period utility `u(C) = C − a₀C²/2`, O&R Exercise 3, p. 345. -/
noncomputable def quadU (a0 c : ℝ) : ℝ := c - a0 / 2 * c ^ 2

/-- Lifetime utility in Exercise 3 (bonds only, `β = 1/(1+r)`), O&R p. 345, as a function of
`C₁`, with `A = (1+r)B₁ + Y₁`: date-2 consumption is `C₂(s) = (1+r)(A − C₁) + Y₂(s)`, and
`U = u(C₁) + (1+r)⁻¹E[u(C₂)]`. -/
noncomputable def quadLifetime (Ω : StateSpace S) (a0 r A : ℝ) (Y2 : S → ℝ) (C1 : ℝ) : ℝ :=
  quadU a0 C1 + (1 + r)⁻¹ * Ω.expect (fun s => quadU a0 ((1 + r) * (A - C1) + Y2 s))

/-- The certainty-equivalent consumption level of Exercise 3(a), O&R p. 346:
`C₁* = ((1+r)/(2+r))[A + E(Y₂)/(1+r)]` with `A = (1+r)B₁ + Y₁`. -/
noncomputable def quadCstar (Ω : StateSpace S) (r A : ℝ) (Y2 : S → ℝ) : ℝ :=
  (1 + r) / (2 + r) * (A + Ω.expect Y2 / (1 + r))

/-- Expected quadratic utility of `k + Y₂` in terms of the first two moments of `Y₂`
(used for Exercise 3, O&R p. 345). -/
theorem quad_expect (Ω : StateSpace S) (a0 k : ℝ) (Y2 : S → ℝ) :
    Ω.expect (fun s => quadU a0 (k + Y2 s)) =
      k + Ω.expect Y2 - a0 / 2 * (k ^ 2 + 2 * k * Ω.expect Y2 +
        Ω.expect (fun s => Y2 s ^ 2)) := by
  simp only [StateSpace.expect, quadU]
  rw [Finset.sum_congr rfl fun s _ => show Ω.prob s * (k + Y2 s - a0 / 2 * (k + Y2 s) ^ 2) =
    Ω.prob s * (k - a0 / 2 * k ^ 2) + (1 - a0 * k) * (Ω.prob s * Y2 s) +
      (-(a0 / 2)) * (Ω.prob s * Y2 s ^ 2) by ring, Finset.sum_add_distrib,
    Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, ← Finset.mul_sum, Ω.prob_sum]
  ring

/-- Exercise 3(a), O&R p. 346, certainty equivalence: with `β(1+r) = 1` and bonds only, the
Euler equation `u′(C₁) = E[u′(C₂)]` for quadratic utility (`a₀ ≠ 0`) holds iff
`C₁ = ((1+r)/(2+r))[(1+r)B₁ + Y₁ + E(Y₂)/(1+r)]`, the same as under certainty with `Y₂`
replaced by `E(Y₂)`. -/
theorem quad_euler_iff (Ω : StateSpace S) {a0 r : ℝ} (ha0 : a0 ≠ 0) (hr : 0 < 1 + r)
    (A C1 : ℝ) (Y2 : S → ℝ) :
    1 - a0 * C1 = Ω.expect (fun s => 1 - a0 * ((1 + r) * (A - C1) + Y2 s)) ↔
      C1 = quadCstar Ω r A Y2 := by
  have e : Ω.expect (fun s => 1 - a0 * ((1 + r) * (A - C1) + Y2 s)) =
      1 - a0 * ((1 + r) * (A - C1) + Ω.expect Y2) := by
    simp only [StateSpace.expect]
    rw [Finset.sum_congr rfl fun s _ => show Ω.prob s * (1 - a0 * ((1 + r) * (A - C1) + Y2 s))
      = Ω.prob s * (1 - a0 * ((1 + r) * (A - C1))) + (-a0) * (Ω.prob s * Y2 s) by ring,
      Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, Ω.prob_sum]
    ring
  have h2r : (2 + r) ≠ 0 := by linarith
  rw [e, quadCstar]
  constructor
  · intro h
    have h' : C1 = (1 + r) * (A - C1) + Ω.expect Y2 :=
      mul_left_cancel₀ ha0 (by linarith)
    field_simp
    linarith
  · intro h
    have h' : C1 = (1 + r) * (A - C1) + Ω.expect Y2 := by
      rw [h]; field_simp; ring
    rw [← h']

/-- Exercise 3(a), O&R p. 346: lifetime utility is an exact concave quadratic around `C₁*`,
`U(C₁) = U(C₁*) − a₀(2+r)(C₁ − C₁*)²/2`; so `C₁*` is the unique global maximiser when the
nonnegativity constraints are ignored. -/
theorem quad_lifetime_eq (Ω : StateSpace S) {r : ℝ} (a0 : ℝ) (hr : 0 < 1 + r) (A C1 : ℝ)
    (Y2 : S → ℝ) :
    quadLifetime Ω a0 r A Y2 C1 = quadLifetime Ω a0 r A Y2 (quadCstar Ω r A Y2) -
      a0 * (2 + r) / 2 * (C1 - quadCstar Ω r A Y2) ^ 2 := by
  have h2r : (2 + r) ≠ 0 := by linarith
  have hr0 := hr.ne'
  simp only [quadLifetime, quad_expect, quadCstar]
  simp only [quadU]
  field_simp
  ring

/-- Exercise 3(a), O&R p. 346: the implied date-2 consumption is
`C₂(s) = C₁* + Y₂(s) − E(Y₂)`, so `E[C₂] = C₁*` (consumption is a martingale). -/
theorem quad_C2_at_optimum (Ω : StateSpace S) {r : ℝ} (hr : 0 < 1 + r) (A : ℝ) (Y2 : S → ℝ)
    (s : S) :
    (1 + r) * (A - quadCstar Ω r A Y2) + Y2 s = quadCstar Ω r A Y2 + (Y2 s - Ω.expect Y2) := by
  have h2r : (2 + r) ≠ 0 := by linarith
  simp only [quadCstar]
  field_simp
  ring

/-- Exercise 3(b), O&R p. 346, feasibility: if state `s₀` has the lowest output, the date-2
nonnegativity constraints `C₂(s) ≥ 0` for all `s` are equivalent to the single constraint
`C₁ ≤ (1+r)B₁ + Y₁ + Y₂(s₀)/(1+r)`. -/
theorem quad_feasible_iff {T : Type} {r : ℝ} (hr : 0 < 1 + r) (A C1 : ℝ) (Y2 : T → ℝ)
    (s0 : T) (hmin : ∀ s, Y2 s0 ≤ Y2 s) :
    (∀ s, 0 ≤ (1 + r) * (A - C1) + Y2 s) ↔ C1 ≤ A + Y2 s0 / (1 + r) := by
  have e : (1 + r) * (A - C1) + Y2 s0 = (1 + r) * (A + Y2 s0 / (1 + r) - C1) := by
    field_simp; ring
  have key : 0 ≤ (1 + r) * (A - C1) + Y2 s0 ↔ C1 ≤ A + Y2 s0 / (1 + r) := by
    rw [e]
    constructor
    · intro h
      have := (mul_nonneg_iff_of_pos_left hr).mp h
      linarith
    · intro h
      exact mul_nonneg hr.le (by linarith)
  constructor
  · intro h
    exact key.mp (h s0)
  · intro h s
    linarith [key.mpr h, hmin s]

/-- Exercise 3(b), O&R p. 346, nonbinding case: if `(1+r)B₁ + Y₁ + ((2+r)/(1+r))Y₂(s₀) ≥ E(Y₂)`
(with `s₀` the lowest-output state and `a₀ ≥ 0`), then `C₁*` of part (a) satisfies the
nonnegativity constraints and maximises lifetime utility among all feasible `C₁`. -/
theorem quad_nonbinding (Ω : StateSpace S) {a0 r : ℝ} (ha0 : 0 ≤ a0) (hr : 0 < 1 + r)
    (A : ℝ) (Y2 : S → ℝ) (s0 : S) (hmin : ∀ s, Y2 s0 ≤ Y2 s)
    (hcond : Ω.expect Y2 ≤ A + (2 + r) / (1 + r) * Y2 s0) :
    (∀ s, 0 ≤ (1 + r) * (A - quadCstar Ω r A Y2) + Y2 s) ∧
      ∀ C1, quadLifetime Ω a0 r A Y2 C1 ≤ quadLifetime Ω a0 r A Y2 (quadCstar Ω r A Y2) := by
  have h2r : 0 < 2 + r := by linarith
  refine ⟨(quad_feasible_iff hr A _ Y2 s0 hmin).mpr ?_, fun C1 => ?_⟩
  · have hy : (2 + r) / (1 + r) * Y2 s0 = (2 + r) * (Y2 s0 / (1 + r)) := by ring
    have hm : Ω.expect Y2 = (1 + r) * (Ω.expect Y2 / (1 + r)) := by field_simp
    rw [hy] at hcond
    rw [hm] at hcond
    simp only [quadCstar]
    rw [div_mul_eq_mul_div, div_le_iff₀ h2r]
    linarith
  · rw [quad_lifetime_eq Ω a0 hr A C1 Y2]
    have : 0 ≤ a0 * (2 + r) / 2 * (C1 - quadCstar Ω r A Y2) ^ 2 := by positivity
    linarith

/-- Exercise 3(b), O&R p. 346, binding case (precautionary saving): if
`(1+r)B₁ + Y₁ + ((2+r)/(1+r))Y₂(s₀) < E(Y₂)` (with `s₀` the lowest-output state, `a₀ > 0`),
then the optimum is the corner `C₁ = (1+r)B₁ + Y₁ + Y₂(s₀)/(1+r)` — the book prints "`C_t`",
a typo for `C₁` — which lies strictly below `C₁*`, maximises lifetime utility over the feasible
set, and violates the bond Euler equation: `u′(C₁) > E[u′(C₂)]` (the Kuhn–Tucker multiplier on
the nonnegativity constraint is positive). -/
theorem quad_binding (Ω : StateSpace S) {a0 r : ℝ} (ha0 : 0 < a0) (hr : 0 < 1 + r)
    (A : ℝ) (Y2 : S → ℝ) (s0 : S) (hmin : ∀ s, Y2 s0 ≤ Y2 s)
    (hcond : A + (2 + r) / (1 + r) * Y2 s0 < Ω.expect Y2) :
    A + Y2 s0 / (1 + r) < quadCstar Ω r A Y2 ∧
      (∀ s, 0 ≤ (1 + r) * (A - (A + Y2 s0 / (1 + r))) + Y2 s) ∧
      (∀ C1, (∀ s, 0 ≤ (1 + r) * (A - C1) + Y2 s) →
        quadLifetime Ω a0 r A Y2 C1 ≤ quadLifetime Ω a0 r A Y2 (A + Y2 s0 / (1 + r))) ∧
      Ω.expect (fun s => 1 - a0 * ((1 + r) * (A - (A + Y2 s0 / (1 + r))) + Y2 s)) <
        1 - a0 * (A + Y2 s0 / (1 + r)) := by
  have h2r : 0 < 2 + r := by linarith
  have hr0 := hr.ne'
  set Cb := A + Y2 s0 / (1 + r) with hCb
  set Cs := quadCstar Ω r A Y2 with hCs
  have hlt : Cb < Cs := by
    have hy : (2 + r) / (1 + r) * Y2 s0 = (2 + r) * (Y2 s0 / (1 + r)) := by ring
    have hm : Ω.expect Y2 = (1 + r) * (Ω.expect Y2 / (1 + r)) := by field_simp
    rw [hy] at hcond
    rw [hm] at hcond
    rw [hCb, hCs, quadCstar, div_mul_eq_mul_div, lt_div_iff₀ h2r]
    linarith
  refine ⟨hlt, (quad_feasible_iff hr A Cb Y2 s0 hmin).mpr le_rfl, fun C1 hC1 => ?_, ?_⟩
  · have hle := (quad_feasible_iff hr A C1 Y2 s0 hmin).mp hC1
    rw [quad_lifetime_eq Ω a0 hr A C1 Y2, quad_lifetime_eq Ω a0 hr A Cb Y2, ← hCs]
    have h1 : (Cb - Cs) ^ 2 ≤ (C1 - Cs) ^ 2 := by nlinarith
    have : 0 ≤ a0 * (2 + r) / 2 := by positivity
    nlinarith
  · have e : Ω.expect (fun s => 1 - a0 * ((1 + r) * (A - Cb) + Y2 s)) =
        1 - a0 * ((1 + r) * (A - Cb) + Ω.expect Y2) := by
      simp only [StateSpace.expect]
      rw [Finset.sum_congr rfl fun s _ => show Ω.prob s * (1 - a0 * ((1 + r) * (A - Cb) + Y2 s))
        = Ω.prob s * (1 - a0 * ((1 + r) * (A - Cb))) + (-a0) * (Ω.prob s * Y2 s) by ring,
        Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum, Ω.prob_sum]
      ring
    have hstar : Cs = (1 + r) * (A - Cs) + Ω.expect Y2 := by
      rw [hCs, quadCstar]; field_simp; ring
    rw [e]
    have : Cb < (1 + r) * (A - Cb) + Ω.expect Y2 := by nlinarith
    nlinarith

/-- Exercise 3(c), O&R p. 346, complete markets with actuarially fair prices `p = π` and
`β = 1/(1+r)`: the FOCs (5) for quadratic utility (`a₀ ≠ 0`, `π > 0`) and the budget (4)
(with initial assets, `A = (1+r)B₁ + Y₁`) imply full insurance, `C₂(s) = C₁` for all `s`, with
`C₁ = C₁*` of part (a); nonnegativity is then automatic whenever lifetime resources
`A + E(Y₂)/(1+r)` are nonnegative, which is why it can be disregarded. -/
theorem quad_complete_markets (Ω : StateSpace S) {a0 r : ℝ} (ha0 : a0 ≠ 0) (hr : 0 < 1 + r)
    (hπ : ∀ s, 0 < Ω.prob s) (A C1 : ℝ) (C2 Y2 : S → ℝ)
    (hfoc : ∀ s, Ω.prob s / (1 + r) * (1 - a0 * C1) =
      Ω.prob s * (1 + r)⁻¹ * (1 - a0 * C2 s))
    (hbud : C1 + ∑ s, Ω.prob s / (1 + r) * C2 s = A + ∑ s, Ω.prob s / (1 + r) * Y2 s) :
    (∀ s, C2 s = C1) ∧ C1 = quadCstar Ω r A Y2 ∧
      (0 ≤ A + Ω.expect Y2 / (1 + r) → ∀ s, 0 ≤ C2 s) := by
  have h2r : 0 < 2 + r := by linarith
  have hr0 := hr.ne'
  have hC2 : ∀ s, C2 s = C1 := fun s => by
    have h := hfoc s
    have hk : Ω.prob s * (1 + r)⁻¹ * a0 ≠ 0 :=
      mul_ne_zero (mul_ne_zero (hπ s).ne' (inv_ne_zero hr0)) ha0
    refine mul_left_cancel₀ hk ?_
    rw [div_eq_mul_inv] at h
    linear_combination h
  have hsumY : ∑ s, Ω.prob s / (1 + r) * Y2 s = Ω.expect Y2 / (1 + r) := by
    simp only [StateSpace.expect, Finset.sum_div]
    exact Finset.sum_congr rfl fun s _ => by ring
  have hsumC : ∑ s, Ω.prob s / (1 + r) * C2 s = C1 / (1 + r) := by
    rw [Finset.sum_congr rfl fun s _ => by rw [hC2 s], ← Finset.sum_mul, ← Finset.sum_div,
      Ω.prob_sum]
    ring
  rw [hsumY, hsumC] at hbud
  have hC1 : C1 = quadCstar Ω r A Y2 := by
    rw [quadCstar, ← hbud]
    field_simp
    ring
  refine ⟨hC2, hC1, fun hW s => ?_⟩
  rw [hC2 s, hC1, quadCstar]
  exact mul_nonneg (div_nonneg hr.le h2r.le) hW

end ObstfeldRogoff.InternationalFinancialMarkets.SmallCountry
