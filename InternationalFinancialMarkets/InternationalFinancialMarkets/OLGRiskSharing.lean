/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import InternationalFinancialMarkets.EventTree
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Intragenerational risk sharing and the Lucas two-good model

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §5.6,
pp. 332–335, and Chapter 5 Exercise 6, p. 347.

**§5.6.** Home and Foreign residents live two periods and have log utility
`log c^Y_t + βE_t log c^O_{t+1}`. Everyone in Home receives `y_t` (Foreign `y*_t`); date-`t+1`
states `s` have probabilities `π_t(s)`. The young of date `t` trade Arrow–Debreu claims on
date-`t+1` consumption only among themselves. We prove:
* at the book's prices `1 + r_{t+1} = (y_t + y*_t)^{−1}/(βE_t[(y_{t+1} + y*_{t+1})^{−1}])` and
  `p_t(s) = π_t(s)(y_{t+1}(s) + y*_{t+1}(s))^{−1}/E_t[(y_{t+1} + y*_{t+1})^{−1}]`, the allocation
  `c^Y = μ_t(y + y*)`, `c^O(s) = μ_t(y_{t+1}(s) + y*_{t+1}(s))` (and `1 − μ_t` for Foreign)
  satisfies both cohorts' first-order conditions and budget constraints, markets clear, and
  it is optimal for each young agent (log concavity);
* conversely every such within-cohort equilibrium has this allocation, the book's share
  `μ_t = [y_t/(y_t + y*_t) + βE_t{y_{t+1}/(y_{t+1} + y*_{t+1})}]/(1 + β)` (footnote 16 with
  `ρ = 1`), and these prices;
* aggregate consumption (76).

**Exercise 6** (Lucas 1982). With identical tastes and equal pooled portfolios both countries
have wealth `½(X + pY)`, so identical demands and market clearing give `C_X = X/2`,
`C_Y = Y/2` and `p = u_Y/u_X` at `(X/2, Y/2)`. For asset prices we take a finite Markov chain
for the endowment state and a truncated horizon: the Euler equation
`V_t u_X(t) = βE_t[u_X(t+1)(V_{t+1} + D_{t+1})]` with zero terminal value gives the finite
present-value sum `V_t = Σ_k β^k E_t[u_X(t+k) D_{t+k}]/u_X(t)` (for `V_X`, `D = X`; for `V_Y`,
`D = pY`), converging to the infinite sum when it is summable. The riskless bond price is
`βE_t[u_X(t+1)]/u_X(t)` and the price of sure `Y` in units of `Y` is
`βE_t[u_Y(t+1)]/u_Y(t)` (the own-rate of interest on `Y` is its reciprocal minus one).
-/

namespace ObstfeldRogoff.InternationalFinancialMarkets.OLGRiskSharing

open Finset Filter Topology

variable {S : Type} [Fintype S]

/-! ## §5.6: the within-cohort equilibrium -/

/-- The Home cohort's consumption share, O&R §5.6, p. 334 (footnote 16 with `ρ = 1`):
`μ_t = [y_t/(y_t + y*_t) + βΣ_s π_t(s) y_{t+1}(s)/(y_{t+1}(s) + y*_{t+1}(s))]/(1 + β)`. -/
noncomputable def cohortShare (β : ℝ) (π : S → ℝ) (y ys : ℝ) (y1 ys1 : S → ℝ) : ℝ :=
  1 / (1 + β) * (y / (y + ys) + β * ∑ s, π s * (y1 s / (y1 s + ys1 s)))

/-- The equilibrium gross interest rate, O&R §5.6, p. 334:
`1 + r_{t+1} = (y_t + y*_t)^{−1}/(βE_t[(y_{t+1} + y*_{t+1})^{−1}])`. -/
noncomputable def cohortGrossRate (β : ℝ) (π : S → ℝ) (y ys : ℝ) (y1 ys1 : S → ℝ) : ℝ :=
  1 / (y + ys) / (β * ∑ s, π s * (1 / (y1 s + ys1 s)))

/-- The equilibrium Arrow–Debreu prices, O&R §5.6, p. 334:
`p_t(s) = π_t(s)(y_{t+1}(s) + y*_{t+1}(s))^{−1}/E_t[(y_{t+1} + y*_{t+1})^{−1}]`. -/
noncomputable def cohortPrice (π : S → ℝ) (y1 ys1 : S → ℝ) (s : S) : ℝ :=
  π s * (1 / (y1 s + ys1 s)) / ∑ s', π s' * (1 / (y1 s' + ys1 s'))

/-- The expected inverse of next-period world output is positive (O&R §5.6, p. 334). -/
theorem expected_inverse_pos (π : S → ℝ) (hπ0 : ∀ s, 0 ≤ π s) (hπ1 : ∑ s, π s = 1)
    {y1 ys1 : S → ℝ} (hy1 : ∀ s, 0 < y1 s + ys1 s) :
    0 < ∑ s, π s * (1 / (y1 s + ys1 s)) := by
  have hlt : ∑ _s : S, (0 : ℝ) < ∑ s, π s := by rw [hπ1]; simp
  obtain ⟨s₀, -, hs₀⟩ := Finset.exists_lt_of_sum_lt hlt
  exact Finset.sum_pos' (fun s _ => mul_nonneg (hπ0 s) (one_div_pos.mpr (hy1 s)).le)
    ⟨s₀, Finset.mem_univ _, mul_pos hs₀ (one_div_pos.mpr (hy1 s₀))⟩

/-- The equilibrium Arrow–Debreu prices sum to one (O&R §5.6, p. 334; the no-arbitrage
condition (7) with a riskless bond). -/
theorem cohortPrice_sum (π : S → ℝ) (hπ0 : ∀ s, 0 ≤ π s) (hπ1 : ∑ s, π s = 1)
    {y1 ys1 : S → ℝ} (hy1 : ∀ s, 0 < y1 s + ys1 s) :
    ∑ s, cohortPrice π y1 ys1 s = 1 := by
  simp only [cohortPrice, ← Finset.sum_div]
  exact div_self (expected_inverse_pos π hπ0 hπ1 hy1).ne'

/-- The Home and Foreign cohort shares sum to one, O&R §5.6, p. 334: Foreign's share is
`1 − μ_t`. -/
theorem cohortShare_add (β : ℝ) (π : S → ℝ) (hπ1 : ∑ s, π s = 1) {y ys : ℝ}
    {y1 ys1 : S → ℝ} (hβ : 0 < β) (hy : 0 < y + ys) (hy1 : ∀ s, 0 < y1 s + ys1 s) :
    cohortShare β π y ys y1 ys1 + cohortShare β π ys y ys1 y1 = 1 := by
  have e : ∀ s, π s * (y1 s / (y1 s + ys1 s)) + π s * (ys1 s / (ys1 s + y1 s)) = π s := by
    intro s
    have := (hy1 s).ne'
    rw [add_comm (ys1 s) (y1 s)]
    field_simp
  have hsum : ∑ s, π s * (y1 s / (y1 s + ys1 s)) + ∑ s, π s * (ys1 s / (ys1 s + y1 s)) = 1 := by
    rw [← Finset.sum_add_distrib, ← hπ1]
    exact Finset.sum_congr rfl fun s _ => e s
  unfold cohortShare
  rw [add_comm ys y]
  set A := ∑ s, π s * (y1 s / (y1 s + ys1 s))
  set B := ∑ s, π s * (ys1 s / (ys1 s + y1 s))
  have h1 : (1 : ℝ) + β ≠ 0 := by linarith
  field_simp
  linear_combination (y + ys) * β * hsum

/-- The equilibrium interest rate and Arrow–Debreu prices of O&R §5.6, p. 334 depend on Home
and Foreign endowments only through world output, so they are the same whether computed
from Home's or from Foreign's side. -/
theorem cohort_prices_symm (β : ℝ) (π : S → ℝ) (y ys : ℝ) (y1 ys1 : S → ℝ) (s : S) :
    cohortGrossRate β π ys y ys1 y1 = cohortGrossRate β π y ys y1 ys1 ∧
      cohortPrice π ys1 y1 s = cohortPrice π y1 ys1 s := by
  refine ⟨?_, ?_⟩ <;>
    simp only [cohortGrossRate, cohortPrice, add_comm ys y, add_comm (ys1 _) (y1 _)]

/-- The within-cohort equilibrium of O&R §5.6, p. 334 (verification). At the book's prices,
the allocation `c^Y = μ(y + y*)`, `c^O(s) = μ(y_{t+1}(s) + y*_{t+1}(s))` for Home, with
`μ = μ_t`, satisfies Home's log-utility first-order conditions
`[p(s)/(1 + r)](1/c^Y) = βπ(s)/c^O(s)` and Home's budget constraint
`c^Y + Σ_s p(s)c^O(s)/(1 + r) = y + Σ_s p(s)y_{t+1}(s)/(1 + r)`. (Foreign is the same
statement with the roles of `y`, `y*` exchanged, by `cohortShare_add`.) -/
theorem cohort_equilibrium (π : S → ℝ) (hπ0 : ∀ s, 0 ≤ π s) (hπ1 : ∑ s, π s = 1)
    {β y ys : ℝ} {y1 ys1 : S → ℝ} (hβ : 0 < β) (hy : 0 < y + ys)
    (hy1 : ∀ s, 0 < y1 s + ys1 s) (hμ : 0 < cohortShare β π y ys y1 ys1) :
    (∀ s, cohortPrice π y1 ys1 s / cohortGrossRate β π y ys y1 ys1
        * (1 / (cohortShare β π y ys y1 ys1 * (y + ys)))
      = β * π s * (1 / (cohortShare β π y ys y1 ys1 * (y1 s + ys1 s)))) ∧
    cohortShare β π y ys y1 ys1 * (y + ys) + 1 / cohortGrossRate β π y ys y1 ys1
        * ∑ s, cohortPrice π y1 ys1 s * (cohortShare β π y ys y1 ys1 * (y1 s + ys1 s))
      = y + 1 / cohortGrossRate β π y ys y1 ys1 * ∑ s, cohortPrice π y1 ys1 s * y1 s := by
  have hE := expected_inverse_pos π hπ0 hπ1 hy1
  set E := ∑ s, π s * (1 / (y1 s + ys1 s)) with hEdef
  set μ := cohortShare β π y ys y1 ys1 with hμdef
  -- the price of a claim in date-`t` units
  have hq : ∀ s, cohortPrice π y1 ys1 s / cohortGrossRate β π y ys y1 ys1
      = β * π s * (y + ys) / (y1 s + ys1 s) := by
    intro s
    have := (hy1 s).ne'
    simp only [cohortPrice, cohortGrossRate, ← hEdef]
    field_simp
  refine ⟨fun s => ?_, ?_⟩
  · rw [hq s]
    have := (hy1 s).ne'
    field_simp
  · have e1 : ∀ s, 1 / cohortGrossRate β π y ys y1 ys1 * cohortPrice π y1 ys1 s
        = β * π s * (y + ys) / (y1 s + ys1 s) := by
      intro s; rw [← hq s]; ring
    simp only [Finset.mul_sum, ← mul_assoc, e1]
    have e2 : ∀ s, β * π s * (y + ys) / (y1 s + ys1 s) * μ * (y1 s + ys1 s)
        = μ * β * (y + ys) * π s := by
      intro s; have := (hy1 s).ne'; field_simp
    have e3 : ∀ s, β * π s * (y + ys) / (y1 s + ys1 s) * y1 s
        = β * (y + ys) * (π s * (y1 s / (y1 s + ys1 s))) := by
      intro s; have := (hy1 s).ne'; field_simp
    simp only [e2, e3, ← Finset.mul_sum, hπ1, mul_one]
    rw [hμdef, cohortShare]
    have h1 : (1 : ℝ) + β ≠ 0 := by linarith
    field_simp

/-- Optimality of the young agent's plan, O&R §5.6, p. 333: with log utility, a positive plan
`(c^Y, c^O)` satisfying the first-order conditions `q(s)/c^Y = βπ(s)/c^O(s)` (where
`q(s) = p(s)/(1 + r)` is the date-`t` price of the state-`s` claim) maximises
`log c^Y + βΣπ(s) log c^O(s)` among positive plans that cost no more. -/
theorem young_plan_optimal (π q : S → ℝ) (hπ0 : ∀ s, 0 ≤ π s) {β : ℝ} (hβ : 0 ≤ β)
    {cY cY' : ℝ} {cO cO' : S → ℝ} (hcY : 0 < cY) (hcY' : 0 < cY') (hcO : ∀ s, 0 < cO s)
    (hcO' : ∀ s, 0 < cO' s) (hfoc : ∀ s, q s * (1 / cY) = β * π s * (1 / cO s))
    (hbud : cY' + ∑ s, q s * cO' s ≤ cY + ∑ s, q s * cO s) :
    Real.log cY' + β * ∑ s, π s * Real.log (cO' s)
      ≤ Real.log cY + β * ∑ s, π s * Real.log (cO s) := by
  have h := EventTree.foc_plan_optimal (H := fun _ => S) {0} (fun _ => Finset.univ)
    Real.log (fun x => 1 / x) (fun x y hx hy => EventTree.log_tangent hx hy)
    (fun _ s => β * π s) (fun _ s => q s)
    (fun _ _ s _ => mul_nonneg hβ (hπ0 s)) hcY hcY' (fun _ _ s _ => hcO s)
    (fun _ _ s _ => hcO' s) (one_div_pos.mpr hcY).le (fun _ _ s _ => hfoc s)
    (by simpa using hbud)
  simp only [Finset.sum_singleton, mul_assoc, ← Finset.mul_sum] at h
  exact h

/-- Characterisation of the within-cohort equilibrium, O&R §5.6, p. 334 ("you can confirm").
Suppose the Home and Foreign young both satisfy their log-utility first-order conditions
`[p(s)/R] c^O(s) = βπ(s) c^Y` at common prices (gross rate `R > 0`, `p(s) > 0`, `Σp = 1`),
Home's budget constraint holds, and markets clear today and in every state tomorrow. Then
`c^Y = μ_t(y + y*)`, `c^O(s) = μ_t(y_{t+1}(s) + y*_{t+1}(s))` with the book's `μ_t`, and `R`,
`p` are the book's prices. -/
theorem cohort_equilibrium_unique (π : S → ℝ) (hπ0 : ∀ s, 0 ≤ π s) (hπ1 : ∑ s, π s = 1)
    {β y ys R : ℝ} {y1 ys1 p : S → ℝ} (hβ : 0 < β) (hy : 0 < y + ys)
    (hy1 : ∀ s, 0 < y1 s + ys1 s) (hR : 0 < R) (hp : ∀ s, 0 < p s) (hpsum : ∑ s, p s = 1)
    {cY cYs : ℝ} {cO cOs : S → ℝ} (hcY : 0 < cY)
    (hfoc : ∀ s, p s / R * cO s = β * π s * cY)
    (hfocs : ∀ s, p s / R * cOs s = β * π s * cYs)
    (hbud : cY + 1 / R * ∑ s, p s * cO s = y + 1 / R * ∑ s, p s * y1 s)
    (hclear : cY + cYs = y + ys) (hclear1 : ∀ s, cO s + cOs s = y1 s + ys1 s) :
    cY = cohortShare β π y ys y1 ys1 * (y + ys) ∧
    (∀ s, cO s = cohortShare β π y ys y1 ys1 * (y1 s + ys1 s)) ∧
    R = cohortGrossRate β π y ys y1 ys1 ∧ ∀ s, p s = cohortPrice π y1 ys1 s := by
  have hW := hy.ne'
  -- consumption growth is equalised: `c^O(s) = (c^Y/(y + y*))(y_{t+1}(s) + y*_{t+1}(s))`
  have hcO : ∀ s, cO s = cY / (y + ys) * (y1 s + ys1 s) := by
    intro s
    have hq : 0 < p s / R := div_pos (hp s) hR
    have h1 : p s / R * (cO s * cYs) = p s / R * (cOs s * cY) := by
      linear_combination cYs * hfoc s - cY * hfocs s
    have h2 := mul_left_cancel₀ hq.ne' h1
    rw [div_mul_eq_mul_div, eq_div_iff hW]
    linear_combination h2 - cO s * hclear + cY * hclear1 s
  -- date-`t` claim prices
  have hq : ∀ s, p s / R = β * π s * (y + ys) / (y1 s + ys1 s) := by
    intro s
    have h := hfoc s
    rw [hcO s] at h
    have := (hy1 s).ne'
    rw [eq_div_iff this]
    field_simp at h
    rw [div_mul_eq_mul_div, div_eq_iff hR.ne']
    linarith
  have hbud' : cY + β * cY = y + β * (y + ys) * ∑ s, π s * (y1 s / (y1 s + ys1 s)) := by
    have e1 : 1 / R * ∑ s, p s * cO s = β * cY := by
      rw [Finset.mul_sum]
      rw [show β * cY = ∑ s, β * π s * cY by
        rw [← Finset.sum_mul, ← Finset.mul_sum, hπ1]; ring]
      exact Finset.sum_congr rfl fun s _ => by rw [← hfoc s]; ring
    have e2 : 1 / R * ∑ s, p s * y1 s
        = β * (y + ys) * ∑ s, π s * (y1 s / (y1 s + ys1 s)) := by
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      have := (hy1 s).ne'
      rw [show 1 / R * (p s * y1 s) = p s / R * y1 s by ring, hq s]
      field_simp
    rw [e1, e2] at hbud
    exact hbud
  have hshare : cY = cohortShare β π y ys y1 ys1 * (y + ys) := by
    unfold cohortShare
    set A := ∑ s, π s * (y1 s / (y1 s + ys1 s))
    have h1 : (1 : ℝ) + β ≠ 0 := by linarith
    field_simp
    linarith
  have hE := expected_inverse_pos π hπ0 hπ1 hy1
  set E := ∑ s, π s * (1 / (y1 s + ys1 s)) with hEd
  clear_value E
  -- the price normalisation pins down `R`
  have hRinv : 1 / R = β * (y + ys) * E := by
    calc 1 / R = 1 / R * ∑ s, p s := by rw [hpsum, mul_one]
      _ = _ := ?_
    rw [hEd, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [show 1 / R * p s = p s / R by ring, hq s]
    field_simp
  have hRv : R = cohortGrossRate β π y ys y1 ys1 := by
    unfold cohortGrossRate
    rw [← hEd, eq_div_iff (mul_pos hβ hE).ne', eq_div_iff hW]
    field_simp at hRinv
    linarith
  refine ⟨hshare, fun s => ?_, hRv, fun s => ?_⟩
  · rw [hcO s, hshare]; field_simp
  · have h := hq s
    rw [div_eq_iff hR.ne'] at h
    rw [h, hRv]
    unfold cohortGrossRate cohortPrice
    rw [← hEd]
    have := (hy1 s).ne'
    field_simp

/-- Aggregate Home per capita consumption, O&R (76), p. 334: the young of date `t` consume
`μ_t(y_t + y*_t)` and the old (young at `t − 1`) consume `μ_{t−1}(y_t + y*_t)`, so
`c_t = ½(μ_t + μ_{t−1})(y_t + y*_t)`, which expands to
`(y_t + y*_t)/(2(1 + β)) · [y_t/(y_t + y*_t) + βE_t{…} + y_{t−1}/(y_{t−1} + y*_{t−1}) +
βE_{t−1}{y_t/(y_t + y*_t)}]`. Here date-`t` endowments are functions of the date-`t` state
(`yt`, `yst`, probabilities `πprev` from date `t − 1`) and `s₀` is the realised state. -/
theorem aggregate_consumption (β : ℝ) (hβ : 0 < β) (π πprev : S → ℝ)
    (yprev ysprev : ℝ) (yt yst y1 ys1 : S → ℝ) (s₀ : S) :
    1 / 2 * (cohortShare β π (yt s₀) (yst s₀) y1 ys1 * (yt s₀ + yst s₀)
        + cohortShare β πprev yprev ysprev yt yst * (yt s₀ + yst s₀))
      = (yt s₀ + yst s₀) / (2 * (1 + β))
        * (yt s₀ / (yt s₀ + yst s₀) + β * ∑ s, π s * (y1 s / (y1 s + ys1 s))
          + yprev / (yprev + ysprev) + β * ∑ s, πprev s * (yt s / (yt s + yst s))) := by
  unfold cohortShare
  have h1 : (1 : ℝ) + β ≠ 0 := by linarith
  field_simp
  ring

/-- O&R §5.6, p. 334: if Home's output is exactly half of world output today and expected to
be half tomorrow, the current Home young consume exactly half of their generation's world
output in both periods of life: `μ_t = 1/2`. -/
theorem cohortShare_half (π : S → ℝ) {β y ys : ℝ} {y1 ys1 : S → ℝ} (hβ : 0 < β)
    (h0 : y / (y + ys) = 1 / 2) (h1 : ∑ s, π s * (y1 s / (y1 s + ys1 s)) = 1 / 2) :
    cohortShare β π y ys y1 ys1 = 1 / 2 := by
  unfold cohortShare
  rw [h0, h1]
  have : (1 : ℝ) + β ≠ 0 := by linarith
  field_simp

/-! ## Exercise 6: the Lucas (1982) two-good model -/

/-- Exercise 6(b), O&R p. 347 (static allocation). Suppose both countries have the same
demand function `D(p, w) = (C_X, C_Y)` (identical tastes) and, holding equal pooled
portfolios, the same wealth `w = ½(X + pY)`. Then market clearing in both goods gives
`C_X = X/2`, `C_Y = Y/2`, and if the common first-order condition `u_Y = p u_X` holds at the
demanded bundle with `u_X > 0`, then `p = u_Y(X/2, Y/2)/u_X(X/2, Y/2)`. -/
theorem lucas_allocation (D : ℝ → ℝ → ℝ × ℝ) (uX uY : ℝ → ℝ → ℝ) {X Y p : ℝ}
    (hX : (D p ((X + p * Y) / 2)).1 + (D p ((X + p * Y) / 2)).1 = X)
    (hY : (D p ((X + p * Y) / 2)).2 + (D p ((X + p * Y) / 2)).2 = Y)
    (hfoc : uY (D p ((X + p * Y) / 2)).1 (D p ((X + p * Y) / 2)).2
      = p * uX (D p ((X + p * Y) / 2)).1 (D p ((X + p * Y) / 2)).2)
    (huX : 0 < uX (X / 2) (Y / 2)) :
    (D p ((X + p * Y) / 2)).1 = X / 2 ∧ (D p ((X + p * Y) / 2)).2 = Y / 2 ∧
      p = uY (X / 2) (Y / 2) / uX (X / 2) (Y / 2) := by
  have h1 : (D p ((X + p * Y) / 2)).1 = X / 2 := by linarith
  have h2 : (D p ((X + p * Y) / 2)).2 = Y / 2 := by linarith
  refine ⟨h1, h2, ?_⟩
  rw [h1, h2] at hfoc
  rw [eq_div_iff huX.ne', hfoc]

/-- The `k`-step conditional expectation `E_s[f(s_{t+k})]` for a Markov chain with transition
probabilities `P s s'` (used for Exercise 6(c), O&R p. 347). -/
noncomputable def iterExpect (P : S → S → ℝ) : ℕ → (S → ℝ) → S → ℝ
  | 0, f => f
  | k + 1, f => fun s => ∑ s', P s s' * iterExpect P k f s'

/-- Truncated present-value pricing, Exercise 6(a),(c), O&R p. 347 (cf. (56)–(58), (61)).
Let `m(s) = u_X(X(s)/2, Y(s)/2)` be marginal utility of good `X` at the equilibrium
allocation and `D` a dividend in units of `X` (`D = X` for Home's claim, `D = pY` for
Foreign's). If claim prices `V_N` (with `N` periods of dividends left, `V_0 = 0`) satisfy the
Euler equation `m(s)V_{N+1}(s) = βE_s[m(s′)(D(s′) + V_N(s′))]`, then
`m(s)V_N(s) = Σ_{k<N} β^{k+1} E_s[m(s_{t+k+1}) D(s_{t+k+1})]`. -/
theorem lucas_claim_price (P : S → S → ℝ) (β : ℝ) (m D : S → ℝ) (V : ℕ → S → ℝ)
    (hV0 : ∀ s, V 0 s = 0)
    (heuler : ∀ N s, m s * V (N + 1) s = β * ∑ s', P s s' * (m s' * (D s' + V N s'))) :
    ∀ N s, m s * V N s
      = ∑ k ∈ range N, β ^ (k + 1) * iterExpect P (k + 1) (fun s' => m s' * D s') s := by
  intro N
  induction N with
  | zero => intro s; simp [hV0]
  | succ N ih =>
    intro s
    rw [heuler, Finset.sum_range_succ']
    simp only [Finset.sum_add_distrib, ih, Finset.mul_sum, mul_add]
    rw [Finset.sum_comm, add_comm]
    congr 1
    · refine Finset.sum_congr rfl fun k _ => ?_
      simp only [iterExpect, Finset.mul_sum]
      refine Finset.sum_congr rfl fun s' _ => ?_
      ring_nf
    · simp [iterExpect, Finset.mul_sum]

/-- The infinite-horizon claim price as a limit, Exercise 6(c), O&R p. 347: if the discounted
expected dividends `β^{k+1}E_s[m D]` are summable with sum `L`, the truncated prices converge,
`m(s)V_N(s) → L`, so `V(s) = L/m(s)` is the expected present value. -/
theorem lucas_claim_price_limit (P : S → S → ℝ) (β : ℝ) (m D : S → ℝ) (V : ℕ → S → ℝ)
    (hV0 : ∀ s, V 0 s = 0)
    (heuler : ∀ N s, m s * V (N + 1) s = β * ∑ s', P s s' * (m s' * (D s' + V N s')))
    (s : S) {L : ℝ}
    (hL : HasSum (fun k => β ^ (k + 1) * iterExpect P (k + 1) (fun s' => m s' * D s') s) L) :
    Tendsto (fun N => m s * V N s) atTop (𝓝 L) := by
  have e : (fun N => m s * V N s)
      = fun N => ∑ k ∈ range N, β ^ (k + 1) * iterExpect P (k + 1) (fun s' => m s' * D s') s :=
    funext fun N => lucas_claim_price P β m D V hV0 heuler N s
  rw [e]
  exact hL.tendsto_sum_nat

/-- Riskless rates in the Lucas model, Exercise 6(d), O&R p. 347. A one-period claim paying
one unit of `X` has Euler equation `q m_X(s) = βE_s[m_X(s′)]`, so its price is
`βE_s[u_X(s′)]/u_X(s)`. A sure unit of `Y` next period is worth `βE_s[u_X(s′)p(s′)]` in `X`
utility; since `u_X p = u_Y` at the equilibrium, its price in units of current `Y`
(`p(s) = u_Y(s)/u_X(s)`) is `βE_s[u_Y(s′)]/u_Y(s)`, whose reciprocal is one plus the
own-rate of interest on `Y`. -/
theorem lucas_riskless_prices (P : S → S → ℝ) (β : ℝ) (mX mY p : S → ℝ) (s : S)
    (hmX : 0 < mX s) (hmY : 0 < mY s) (hp : ∀ s', p s' = mY s' / mX s')
    (hmX' : ∀ s', 0 < mX s') {qX qY : ℝ}
    (hqX : qX * mX s = β * ∑ s', P s s' * mX s')
    (hqY : qY * p s * mX s = β * ∑ s', P s s' * (mX s' * p s')) :
    qX = β * (∑ s', P s s' * mX s') / mX s ∧ qY = β * (∑ s', P s s' * mY s') / mY s := by
  refine ⟨by rw [eq_div_iff hmX.ne']; linarith, ?_⟩
  have e : ∀ s', mX s' * p s' = mY s' := fun s' => by
    rw [hp s']; field_simp [(hmX' s').ne']
  simp only [e] at hqY
  rw [hp s] at hqY
  rw [eq_div_iff hmY.ne']
  field_simp at hqY
  linarith

end ObstfeldRogoff.InternationalFinancialMarkets.OLGRiskSharing
