/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import InternationalFinancialMarkets.Model
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp

/-!
# International portfolio diversification

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §5.3,
pp. 300–304, and Exercises 4 and 5, pp. 346–347.

`N` countries (a finite type `ι`) trade only a riskless bond and claims to each country's
date-2 output (share prices `V₁ᵐ`). Budget constraints (42)–(43), bond Euler equation (8) and
share Euler equations (44).

* §5.3.2: with identical CRRA utility, the guess `xᵐₙ = μⁿ`, `Bⁿ = 0`, `C = μⁿYᵂ`, the rate
  (49) and share prices (50) satisfy every first-order condition, budget constraint and
  market-clearing condition.
* §5.3.3: `V₁ᵐ` equals the Arrow–Debreu value of country `m`'s output at prices (30); the
  allocation satisfies every complete-markets equilibrium condition, even though `S` may
  exceed `N + 1` by any amount.
* Exercise 4: the log-utility guesses (89)–(90).
* Exercise 5: CARA utility — (a) complete markets, (b) bonds and shares with equal fund
  shares plus a riskless loan, (c) different absolute risk aversions.
-/

namespace ObstfeldRogoff.InternationalFinancialMarkets.PortfolioDiversification

open Finset

variable {ι S : Type} [Fintype ι] [Fintype S]

/-! ## The CRRA equilibrium (§5.3.2) -/

/-- World date-1 output `Y₁ᵂ = Σₘ Y₁ᵐ`, O&R (46), p. 302. -/
def worldOut1 (Y1 : ι → ℝ) : ℝ := ∑ m, Y1 m

/-- World date-2 output `Y₂ᵂ(s) = Σₘ Y₂ᵐ(s)`, O&R (47), p. 302. -/
def worldOut2 (Y2 : ι → S → ℝ) (s : S) : ℝ := ∑ m, Y2 m s

/-- The equilibrium gross interest rate, O&R (49), p. 302:
`1 + r = (Y₁ᵂ)^{-ρ} / (β Σ_s π(s) Y₂ᵂ(s)^{-ρ})`. -/
noncomputable def grossRate (Ω : StateSpace S) (β ρ : ℝ) (Y1 : ι → ℝ) (Y2 : ι → S → ℝ) : ℝ :=
  worldOut1 Y1 ^ (-ρ) / (β * ∑ s, Ω.prob s * worldOut2 Y2 s ^ (-ρ))

/-- The Arrow–Debreu price `π(s) β [Y₂ᵂ(s)/Y₁ᵂ]^{-ρ}` of O&R (30), p. 286, in the
`N`-country economy. -/
noncomputable def adPrice (Ω : StateSpace S) (β ρ : ℝ) (Y1 : ι → ℝ) (Y2 : ι → S → ℝ)
    (s : S) : ℝ :=
  Ω.prob s * β * (worldOut2 Y2 s / worldOut1 Y1) ^ (-ρ)

/-- Equilibrium share prices, O&R (50), p. 303:
`V₁ᵐ = Σ_s π(s) β [Y₂ᵂ(s)/Y₁ᵂ]^{-ρ} Y₂ᵐ(s)`. -/
noncomputable def sharePrice (Ω : StateSpace S) (β ρ : ℝ) (Y1 : ι → ℝ) (Y2 : ι → S → ℝ)
    (m : ι) : ℝ :=
  ∑ s, Ω.prob s * β * (worldOut2 Y2 s / worldOut1 Y1) ^ (-ρ) * Y2 m s

/-- Country `n`'s share of initial world wealth, O&R (45), p. 302:
`μⁿ = (Y₁ⁿ + V₁ⁿ)/Σₘ(Y₁ᵐ + V₁ᵐ)`. -/
noncomputable def wealthShare (Ω : StateSpace S) (β ρ : ℝ) (Y1 : ι → ℝ) (Y2 : ι → S → ℝ)
    (n : ι) : ℝ :=
  (Y1 n + sharePrice Ω β ρ Y1 Y2 n) / ∑ m, (Y1 m + sharePrice Ω β ρ Y1 Y2 m)

/-- Positive endowments for the §5.3.2 economy: at least one country, positive outputs,
`β > 0`. -/
structure PortfolioEconomy (ι S : Type) [Fintype ι] [Fintype S] where
  Ω : StateSpace S
  β : ℝ
  ρ : ℝ
  Y1 : ι → ℝ
  Y2 : ι → S → ℝ
  nonempty : Nonempty ι
  beta_pos : 0 < β
  Y1_pos : ∀ m, 0 < Y1 m
  Y2_pos : ∀ m s, 0 < Y2 m s

namespace PortfolioEconomy

variable (P : PortfolioEconomy ι S)

/-- Shorthand for the rate (49). -/
noncomputable def R : ℝ := grossRate P.Ω P.β P.ρ P.Y1 P.Y2

/-- Shorthand for share prices (50). -/
noncomputable def V (m : ι) : ℝ := sharePrice P.Ω P.β P.ρ P.Y1 P.Y2 m

/-- Shorthand for wealth shares (45). -/
noncomputable def μ (n : ι) : ℝ := wealthShare P.Ω P.β P.ρ P.Y1 P.Y2 n

/-- The conjectured consumption `C₁ⁿ = μⁿY₁ᵂ`, O&R (46), p. 302. -/
noncomputable def C1 (n : ι) : ℝ := P.μ n * worldOut1 P.Y1

/-- The conjectured consumption `C₂ⁿ(s) = μⁿY₂ᵂ(s)`, O&R (47), p. 302. -/
noncomputable def C2 (n : ι) (s : S) : ℝ := P.μ n * worldOut2 P.Y2 s

/-- The conjectured portfolio `xᵐₙ = μⁿ`, O&R (48), p. 302 (bond holdings are zero). -/
noncomputable def x (n _m : ι) : ℝ := P.μ n

/-- World date-1 output is positive. -/
theorem worldOut1_pos : 0 < worldOut1 P.Y1 := by
  have := P.nonempty
  exact Finset.sum_pos (fun m _ => P.Y1_pos m) Finset.univ_nonempty

/-- World date-2 output is positive in every state. -/
theorem worldOut2_pos (s : S) : 0 < worldOut2 P.Y2 s := by
  have := P.nonempty
  exact Finset.sum_pos (fun m _ => P.Y2_pos m s) Finset.univ_nonempty

/-- Share prices (50) are nonnegative. -/
theorem V_nonneg (m : ι) : 0 ≤ P.V m := by
  unfold V sharePrice
  refine Finset.sum_nonneg fun s _ => ?_
  have := P.Ω.prob_nonneg s; have := P.beta_pos; have := P.Y2_pos m s
  have := Real.rpow_nonneg (div_pos (P.worldOut2_pos s) P.worldOut1_pos).le (-P.ρ)
  positivity

/-- World wealth `Σₘ (Y₁ᵐ + V₁ᵐ)` is positive. -/
theorem wealth_pos : 0 < ∑ m, (P.Y1 m + P.V m) := by
  have := P.nonempty
  exact Finset.sum_pos (fun m _ => by linarith [P.Y1_pos m, P.V_nonneg m])
    Finset.univ_nonempty

/-- Wealth shares (45) are positive. -/
theorem μ_pos (n : ι) : 0 < P.μ n := by
  have hV := P.V_nonneg n
  unfold V at hV
  unfold μ wealthShare
  exact div_pos (by linarith [P.Y1_pos n]) P.wealth_pos

/-- Wealth shares sum to one. -/
theorem sum_μ : ∑ n, P.μ n = 1 := by
  unfold μ wealthShare
  rw [← Finset.sum_div]
  exact div_self P.wealth_pos.ne'

/-- The share price (50) in expanded form: `V₁ᵐ (Y₁ᵂ)^{-ρ} = β Σ_s π(s) Y₂ᵂ(s)^{-ρ} Y₂ᵐ(s)`. -/
theorem V_mul (m : ι) :
    P.V m * worldOut1 P.Y1 ^ (-P.ρ) =
      P.β * ∑ s, P.Ω.prob s * worldOut2 P.Y2 s ^ (-P.ρ) * P.Y2 m s := by
  unfold V sharePrice
  have hY : 0 < worldOut1 P.Y1 ^ (-P.ρ) := Real.rpow_pos_of_pos P.worldOut1_pos _
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Real.div_rpow (P.worldOut2_pos s).le P.worldOut1_pos.le]
  field_simp

/-- **Date-1 budget constraint** (42), O&R p. 303: with `Bⁿ = 0` and `xᵐₙ = μⁿ`,
`Y₁ⁿ + V₁ⁿ = C₁ⁿ + B₂ⁿ + Σₘ xᵐₙ V₁ᵐ`. -/
theorem budget_date1 (n : ι) :
    P.Y1 n + P.V n = P.C1 n + 0 + ∑ m, P.x n m * P.V m := by
  unfold C1 x
  rw [add_zero, ← Finset.mul_sum, ← mul_add, worldOut1, ← Finset.sum_add_distrib]
  unfold μ wealthShare
  exact (div_mul_cancel₀ _ P.wealth_pos.ne').symm

/-- **Date-2 budget constraint** (43), O&R p. 302: `C₂ⁿ(s) = (1 + r)B₂ⁿ + Σₘ xᵐₙ Y₂ᵐ(s)` with
`B₂ⁿ = 0`. -/
theorem budget_date2 (n : ι) (s : S) :
    P.C2 n s = P.R * 0 + ∑ m, P.x n m * P.Y2 m s := by
  unfold C2 x worldOut2
  rw [mul_zero, zero_add, Finset.mul_sum]

/-- **Bond Euler equation** (8) at the rate (49), O&R p. 302:
`C₁ⁿ^{-ρ} = (1 + r) β Σ_s π(s) C₂ⁿ(s)^{-ρ}`. -/
theorem bond_euler (n : ι) :
    P.C1 n ^ (-P.ρ) = P.R * P.β * ∑ s, P.Ω.prob s * P.C2 n s ^ (-P.ρ) := by
  have hμ := P.μ_pos n
  have hK : 0 < ∑ s, P.Ω.prob s * worldOut2 P.Y2 s ^ (-P.ρ) := by
    obtain ⟨s0, hs0⟩ : ∃ s, 0 < P.Ω.prob s := by
      by_contra h
      push Not at h
      have : ∑ s, P.Ω.prob s ≤ 0 := Finset.sum_nonpos fun s _ => h s
      rw [P.Ω.prob_sum] at this; linarith
    exact Finset.sum_pos' (fun s _ => mul_nonneg (P.Ω.prob_nonneg s)
      (Real.rpow_nonneg (P.worldOut2_pos s).le _))
      ⟨s0, Finset.mem_univ _, mul_pos hs0 (Real.rpow_pos_of_pos (P.worldOut2_pos s0) _)⟩
  unfold C1 C2 R grossRate
  simp only [Real.mul_rpow hμ.le (P.worldOut2_pos _).le, Real.mul_rpow hμ.le P.worldOut1_pos.le]
  have e : ∑ s, P.Ω.prob s * (P.μ n ^ (-P.ρ) * worldOut2 P.Y2 s ^ (-P.ρ)) =
      P.μ n ^ (-P.ρ) * ∑ s, P.Ω.prob s * worldOut2 P.Y2 s ^ (-P.ρ) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun s _ => by ring
  rw [e]
  have := P.beta_pos
  field_simp

/-- **Share Euler equations** (44) at share prices (50), O&R p. 303:
`V₁ᵐ C₁ⁿ^{-ρ} = β Σ_s π(s) C₂ⁿ(s)^{-ρ} Y₂ᵐ(s)` for every country `n` and claim `m`. -/
theorem share_euler (n m : ι) :
    P.V m * P.C1 n ^ (-P.ρ) = P.β * ∑ s, P.Ω.prob s * P.C2 n s ^ (-P.ρ) * P.Y2 m s := by
  have hμ := P.μ_pos n
  unfold C1 C2
  simp only [Real.mul_rpow hμ.le (P.worldOut2_pos _).le, Real.mul_rpow hμ.le P.worldOut1_pos.le]
  have e : ∑ s, P.Ω.prob s * (P.μ n ^ (-P.ρ) * worldOut2 P.Y2 s ^ (-P.ρ)) * P.Y2 m s =
      P.μ n ^ (-P.ρ) * ∑ s, P.Ω.prob s * worldOut2 P.Y2 s ^ (-P.ρ) * P.Y2 m s := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun s _ => by ring
  rw [e]
  have h := P.V_mul m
  calc P.V m * (P.μ n ^ (-P.ρ) * worldOut1 P.Y1 ^ (-P.ρ))
      = P.μ n ^ (-P.ρ) * (P.V m * worldOut1 P.Y1 ^ (-P.ρ)) := by ring
    _ = _ := by rw [h]; ring

/-- **Market clearing**, O&R p. 302: every country's shares are fully held
(`Σₙ xᵐₙ = 1`), bonds are in zero net supply, and consumption exhausts world output on both
dates. -/
theorem market_clearing :
    (∀ m, ∑ n, P.x n m = 1) ∧ (∑ _n : ι, (0 : ℝ)) = 0 ∧
      ∑ n, P.C1 n = worldOut1 P.Y1 ∧ ∀ s, ∑ n, P.C2 n s = worldOut2 P.Y2 s := by
  refine ⟨fun m => P.sum_μ, by simp, ?_, fun s => ?_⟩
  · unfold C1; rw [← Finset.sum_mul, P.sum_μ, one_mul]
  · unfold C2; rw [← Finset.sum_mul, P.sum_μ, one_mul]

/-! ## Efficiency of the allocation (§5.3.3) -/

/-- **Share prices are Arrow–Debreu values**, O&R p. 303 comparing (50) with (30):
`V₁ᵐ = Σ_s [p(s)/(1 + r)] Y₂ᵐ(s)` at the complete-markets prices (30). -/
theorem V_eq_ad_value (m : ι) :
    P.V m = ∑ s, adPrice P.Ω P.β P.ρ P.Y1 P.Y2 s * P.Y2 m s := rfl

/-- The complete-markets interest rate: the `p(s) = (1 + r) · adPrice(s)` implied by (49) sum
to one, O&R (7) and p. 303 comparing (49) with (33). -/
theorem ad_prices_normalised :
    ∑ s, P.R * adPrice P.Ω P.β P.ρ P.Y1 P.Y2 s = 1 := by
  have hY : 0 < worldOut1 P.Y1 ^ (-P.ρ) := Real.rpow_pos_of_pos P.worldOut1_pos _
  have hK : ∑ s, adPrice P.Ω P.β P.ρ P.Y1 P.Y2 s * worldOut1 P.Y1 ^ (-P.ρ) =
      P.β * ∑ s, P.Ω.prob s * worldOut2 P.Y2 s ^ (-P.ρ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    unfold adPrice
    rw [Real.div_rpow (P.worldOut2_pos s).le P.worldOut1_pos.le]
    field_simp
  obtain ⟨s0, hs0⟩ : ∃ s, 0 < P.Ω.prob s := by
    by_contra h'
    push Not at h'
    have : ∑ s, P.Ω.prob s ≤ 0 := Finset.sum_nonpos fun s _ => h' s
    rw [P.Ω.prob_sum] at this; linarith
  have hpos : 0 < ∑ s, adPrice P.Ω P.β P.ρ P.Y1 P.Y2 s := by
    refine Finset.sum_pos' (fun s _ => ?_) ⟨s0, Finset.mem_univ _, ?_⟩
    · unfold adPrice
      have := P.Ω.prob_nonneg s; have := P.beta_pos
      have := Real.rpow_nonneg (div_pos (P.worldOut2_pos s) P.worldOut1_pos).le (-P.ρ)
      positivity
    · unfold adPrice
      have := P.beta_pos
      have := Real.rpow_pos_of_pos (div_pos (P.worldOut2_pos s0) P.worldOut1_pos) (-P.ρ)
      positivity
  unfold R grossRate
  rw [← Finset.mul_sum, ← hK, ← Finset.sum_mul]
  field_simp

/-- **The bonds-and-shares allocation satisfies the complete-markets Euler equations**,
O&R §5.3.3, p. 303: `adPrice(s) · C₁ⁿ^{-ρ} = π(s) β C₂ⁿ(s)^{-ρ}` for every country and
state, i.e. (5) at prices (30). -/
theorem ad_euler (n : ι) (s : S) :
    adPrice P.Ω P.β P.ρ P.Y1 P.Y2 s * P.C1 n ^ (-P.ρ) =
      P.Ω.prob s * P.β * P.C2 n s ^ (-P.ρ) := by
  have hμ := P.μ_pos n
  unfold adPrice C1 C2
  rw [Real.mul_rpow hμ.le (P.worldOut2_pos _).le, Real.mul_rpow hμ.le P.worldOut1_pos.le,
    Real.div_rpow (P.worldOut2_pos s).le P.worldOut1_pos.le]
  have : 0 < worldOut1 P.Y1 ^ (-P.ρ) := Real.rpow_pos_of_pos P.worldOut1_pos _
  field_simp

/-- **The allocation satisfies the complete-markets budget constraints**, O&R §5.3.3, p. 303:
`C₁ⁿ + Σ_s adPrice(s) C₂ⁿ(s) = Y₁ⁿ + Σ_s adPrice(s) Y₂ⁿ(s)`. Together with `ad_euler`,
`ad_prices_normalised` and `market_clearing`, the equilibrium of §5.3.2 is a complete-markets
equilibrium, for any number of states `S` (in particular `S ≫ N + 1`). -/
theorem ad_budget (n : ι) :
    P.C1 n + ∑ s, adPrice P.Ω P.β P.ρ P.Y1 P.Y2 s * P.C2 n s =
      P.Y1 n + ∑ s, adPrice P.Ω P.β P.ρ P.Y1 P.Y2 s * P.Y2 n s := by
  have h := P.budget_date1 n
  rw [← V_eq_ad_value]
  unfold C1 C2 x at *
  rw [add_zero, ← Finset.mul_sum] at h
  rw [h]
  have e : ∑ s, adPrice P.Ω P.β P.ρ P.Y1 P.Y2 s * (P.μ n * worldOut2 P.Y2 s) =
      P.μ n * ∑ m, P.V m := by
    unfold worldOut2
    simp only [V_eq_ad_value, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun s _ => by ring
  rw [e, ← h]

/-! ## Exercise 4: the log-utility solution -/

/-- Share prices under log utility, O&R Exercise 4, p. 346:
`V₁ᵐ = β Σ_s π(s) (Y₁ᵂ/Y₂ᵂ(s)) Y₂ᵐ(s)`. -/
noncomputable def logV (m : ι) : ℝ :=
  P.β * ∑ s, P.Ω.prob s * (worldOut1 P.Y1 / worldOut2 P.Y2 s) * P.Y2 m s

/-- The guess (89), O&R p. 346: `C₁ⁿ = (Y₁ⁿ + V₁ⁿ)/(1 + β)`. -/
noncomputable def logC1 (n : ι) : ℝ := (P.Y1 n + P.logV n) / (1 + P.β)

/-- The guess (90), O&R p. 346:
`C₂ⁿ(s) = β/(1 + β) · (Y₁ⁿ + V₁ⁿ) · Σₘ Y₂ᵐ(s)/Σₘ V₁ᵐ`. -/
noncomputable def logC2 (n : ι) (s : S) : ℝ :=
  P.β / (1 + P.β) * (P.Y1 n + P.logV n) * (worldOut2 P.Y2 s / ∑ m, P.logV m)

/-- The portfolio behind (90): savings `β(Y₁ⁿ + V₁ⁿ)/(1 + β)` spread over the global fund, an
equal share `β(Y₁ⁿ + V₁ⁿ)/((1 + β) Σₘ V₁ᵐ)` of every country's output; bonds are zero. -/
noncomputable def logX (n _m : ι) : ℝ :=
  P.β * (P.Y1 n + P.logV n) / ((1 + P.β) * ∑ m, P.logV m)

/-- The gross interest rate under log utility: `1 + r = 1/(β Σ_s π(s) Y₁ᵂ/Y₂ᵂ(s))`
((49) with `ρ = 1`). -/
noncomputable def logR : ℝ := 1 / (P.β * ∑ s, P.Ω.prob s * (worldOut1 P.Y1 / worldOut2 P.Y2 s))

/-- Under log utility the value of all claims is `Σₘ V₁ᵐ = βY₁ᵂ` (Exercise 4). -/
theorem logV_sum : ∑ m, P.logV m = P.β * worldOut1 P.Y1 := by
  unfold logV
  rw [← Finset.mul_sum, Finset.sum_comm]
  congr 1
  have e : ∀ s, ∑ m, P.Ω.prob s * (worldOut1 P.Y1 / worldOut2 P.Y2 s) * P.Y2 m s =
      P.Ω.prob s * worldOut1 P.Y1 := fun s => by
    rw [← Finset.mul_sum]
    have := (P.worldOut2_pos s).ne'
    unfold worldOut2 at this ⊢
    field_simp
  simp only [e]
  rw [← Finset.sum_mul, P.Ω.prob_sum, one_mul]

/-- The log-utility share prices are (50) with `ρ = 1`. -/
theorem logV_eq_sharePrice (m : ι) : P.logV m = sharePrice P.Ω P.β 1 P.Y1 P.Y2 m := by
  unfold logV sharePrice
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [Real.rpow_neg_one, inv_div]
  ring

/-- **Exercise 4: budget constraints** (42)–(43) hold for the guesses (89)–(90) with zero
bond holdings. -/
theorem log_budgets (n : ι) :
    P.Y1 n + P.logV n = P.logC1 n + 0 + ∑ m, P.logX n m * P.logV m ∧
      ∀ s, P.logC2 n s = P.logR * 0 + ∑ m, P.logX n m * P.Y2 m s := by
  have hW : 0 < ∑ m, P.logV m := by
    rw [P.logV_sum]; exact mul_pos P.beta_pos P.worldOut1_pos
  have hb := P.beta_pos
  refine ⟨?_, fun s => ?_⟩
  · unfold logC1 logX
    rw [← Finset.mul_sum, add_zero]
    field_simp
  · unfold logC2 logX worldOut2
    rw [mul_zero, zero_add, ← Finset.mul_sum]
    field_simp

/-- Consumption growth under the log guesses equals world output growth:
`C₂ⁿ(s)/C₁ⁿ = Y₂ᵂ(s)/Y₁ᵂ`. -/
theorem log_growth (n : ι) (s : S) :
    P.logC2 n s = P.logC1 n * (worldOut2 P.Y2 s / worldOut1 P.Y1) := by
  unfold logC2 logC1
  rw [P.logV_sum]
  have := P.beta_pos; have := P.worldOut1_pos.ne'
  field_simp

/-- **Exercise 4: first-order conditions.** Under log utility the share Euler equations (44)
`V₁ᵐ/C₁ⁿ = β Σ_s π(s) Y₂ᵐ(s)/C₂ⁿ(s)` and the bond Euler equation (8)
`1/C₁ⁿ = (1 + r) β Σ_s π(s)/C₂ⁿ(s)` hold at the prices `logV`, `logR`. -/
theorem log_eulers (n : ι) :
    (∀ m, P.logV m / P.logC1 n = P.β * ∑ s, P.Ω.prob s * P.Y2 m s / P.logC2 n s) ∧
      1 / P.logC1 n = P.logR * P.β * ∑ s, P.Ω.prob s / P.logC2 n s := by
  have hC1 : 0 < P.logC1 n := by
    unfold logC1
    have hV : 0 ≤ P.logV n := by
      unfold logV
      refine mul_nonneg P.beta_pos.le (Finset.sum_nonneg fun s _ => ?_)
      have := P.Ω.prob_nonneg s; have := P.Y2_pos n s
      have := div_pos P.worldOut1_pos (P.worldOut2_pos s)
      positivity
    have := P.Y1_pos n; have := P.beta_pos
    positivity
  have hY := P.worldOut1_pos
  simp only [P.log_growth]
  have e : ∀ s, 1 / (P.logC1 n * (worldOut2 P.Y2 s / worldOut1 P.Y1)) =
      (worldOut1 P.Y1 / worldOut2 P.Y2 s) / P.logC1 n := fun s => by
    have := (P.worldOut2_pos s).ne'
    field_simp
  refine ⟨fun m => ?_, ?_⟩
  · have e2 : ∀ s, P.Ω.prob s * P.Y2 m s / (P.logC1 n * (worldOut2 P.Y2 s / worldOut1 P.Y1)) =
        P.Ω.prob s * (worldOut1 P.Y1 / worldOut2 P.Y2 s) * P.Y2 m s / P.logC1 n := fun s => by
      have := (P.worldOut2_pos s).ne'
      field_simp
    simp only [e2, ← Finset.sum_div]
    unfold logV
    rw [mul_div_assoc]
  · have e2 : ∀ s, P.Ω.prob s / (P.logC1 n * (worldOut2 P.Y2 s / worldOut1 P.Y1)) =
        P.Ω.prob s * (worldOut1 P.Y1 / worldOut2 P.Y2 s) / P.logC1 n := fun s => by
      have := (P.worldOut2_pos s).ne'
      field_simp
    simp only [e2, ← Finset.sum_div]
    unfold logR
    set K := ∑ s, P.Ω.prob s * (worldOut1 P.Y1 / worldOut2 P.Y2 s) with hKdef
    have hK : 0 < ∑ s, P.Ω.prob s * (worldOut1 P.Y1 / worldOut2 P.Y2 s) := by
      have h := P.logV_sum
      have hpos : 0 < P.β * worldOut1 P.Y1 := mul_pos P.beta_pos hY
      rw [← h] at hpos
      unfold logV at hpos
      by_contra hc
      push Not at hc
      have hle : ∀ m, P.β * ∑ s, P.Ω.prob s * (worldOut1 P.Y1 / worldOut2 P.Y2 s) * P.Y2 m s
          ≤ 0 := fun m => by
        refine mul_nonpos_of_nonneg_of_nonpos P.beta_pos.le ?_
        have : ∀ s, 0 ≤ P.Ω.prob s * (worldOut1 P.Y1 / worldOut2 P.Y2 s) := fun s =>
          mul_nonneg (P.Ω.prob_nonneg s) (div_pos hY (P.worldOut2_pos s)).le
        have hz : ∀ s, P.Ω.prob s * (worldOut1 P.Y1 / worldOut2 P.Y2 s) = 0 := fun s =>
          le_antisymm ((Finset.single_le_sum (fun s _ => this s) (Finset.mem_univ s)).trans hc)
            (this s)
        simp [hz]
      linarith [Finset.sum_nonpos fun m (_ : m ∈ Finset.univ) => hle m]
    have := P.beta_pos
    field_simp
    rw [hKdef]; exact (div_self hK.ne').symm

/-- **Exercise 4: market clearing.** Every claim is fully held, and consumption exhausts
world output on both dates. -/
theorem log_clearing :
    (∀ m, ∑ n, P.logX n m = 1) ∧ ∑ n, P.logC1 n = worldOut1 P.Y1 ∧
      ∀ s, ∑ n, P.logC2 n s = worldOut2 P.Y2 s := by
  have hW := P.logV_sum
  have hb := P.beta_pos; have hY := P.worldOut1_pos
  have hsum : ∑ n, (P.Y1 n + P.logV n) = (1 + P.β) * worldOut1 P.Y1 := by
    rw [Finset.sum_add_distrib, hW]; unfold worldOut1; ring
  refine ⟨fun m => ?_, ?_, fun s => ?_⟩
  · unfold logX
    rw [← Finset.sum_div, ← Finset.mul_sum, hsum, hW]
    field_simp
  · unfold logC1
    rw [← Finset.sum_div, hsum]
    field_simp
  · unfold logC2
    rw [← Finset.sum_mul, ← Finset.mul_sum, hsum, hW]
    field_simp

/-- **Exercise 4 agrees with §5.3.2**: the log guess (89) is `C₁ⁿ = μⁿY₁ᵂ` with the wealth
share (45) computed at the `ρ = 1` share prices. -/
theorem logC1_eq_share (n : ι) :
    P.logC1 n = wealthShare P.Ω P.β 1 P.Y1 P.Y2 n * worldOut1 P.Y1 := by
  unfold wealthShare logC1
  simp only [← P.logV_eq_sharePrice]
  rw [Finset.sum_add_distrib, P.logV_sum, show ∑ m, P.Y1 m = worldOut1 P.Y1 from rfl]
  have := P.beta_pos; have := P.worldOut1_pos
  field_simp

end PortfolioEconomy

/-! ## Exercise 5: exponential (CARA) utility -/

namespace Exercise5

/-- The CARA pricing kernel sum `Σ_s π(s) exp(−κΔ(s))`, O&R Exercise 5, p. 346–347. -/
noncomputable def caraKernel (Ω : StateSpace S) (κ : ℝ) (Δ : S → ℝ) : ℝ :=
  ∑ s, Ω.prob s * Real.exp (-(κ * Δ s))

/-- The price of a claim to `Z(s)` under CARA risk sharing: `β Σ_s π(s) exp(−κΔ(s)) Z(s)`. -/
noncomputable def caraValue (Ω : StateSpace S) (β κ : ℝ) (Δ Z : S → ℝ) : ℝ :=
  β * ∑ s, Ω.prob s * Real.exp (-(κ * Δ s)) * Z s

/-- The gross riskless rate `1 + r = 1/(β Σ_s π(s) exp(−κΔ(s)))`. -/
noncomputable def caraRate (Ω : StateSpace S) (β κ : ℝ) (Δ : S → ℝ) : ℝ :=
  1 / (β * caraKernel Ω κ Δ)

/-- The CARA kernel sum is positive. -/
theorem caraKernel_pos (Ω : StateSpace S) (κ : ℝ) (Δ : S → ℝ) : 0 < caraKernel Ω κ Δ := by
  obtain ⟨s0, hs0⟩ : ∃ s, 0 < Ω.prob s := by
    by_contra h
    push Not at h
    have : ∑ s, Ω.prob s ≤ 0 := Finset.sum_nonpos fun s _ => h s
    rw [Ω.prob_sum] at this; linarith
  exact Finset.sum_pos' (fun s _ => mul_nonneg (Ω.prob_nonneg s) (Real.exp_pos _).le)
    ⟨s0, Finset.mem_univ _, mul_pos hs0 (Real.exp_pos _)⟩

/-- CARA Euler equation in ratio form (`u′(C) = e^{-γC}`), Exercise 5:
`q e^{-γa} = K e^{-γb}` iff `q = K e^{-γ(b − a)}`. -/
theorem cara_euler_iff {q K γ a b : ℝ} :
    q * Real.exp (-(γ * a)) = K * Real.exp (-(γ * b)) ↔ q = K * Real.exp (-(γ * (b - a))) := by
  have e : Real.exp (-(γ * b)) = Real.exp (-(γ * (b - a))) * Real.exp (-(γ * a)) := by
    rw [← Real.exp_add]; ring_nf
  rw [e, ← mul_assoc]
  exact mul_left_inj' (Real.exp_pos _).ne'

/-- **Share Euler equations under a linear sharing rule**: if `γ(c₂(s) − c₁) = κΔ(s)` then
for any payoff `Z`, `caraValue(Z) · e^{-γc₁} = β Σ_s π(s) e^{-γc₂(s)} Z(s)` (O&R (44) with
CARA utility). -/
theorem cara_share_euler (Ω : StateSpace S) {β γ κ c1 : ℝ} {c2 Δ : S → ℝ}
    (hrule : ∀ s, γ * (c2 s - c1) = κ * Δ s) (Z : S → ℝ) :
    caraValue Ω β κ Δ Z * Real.exp (-(γ * c1)) =
      β * ∑ s, Ω.prob s * Real.exp (-(γ * c2 s)) * Z s := by
  have e : ∀ s, Real.exp (-(γ * c2 s)) = Real.exp (-(κ * Δ s)) * Real.exp (-(γ * c1)) :=
    fun s => by rw [← Real.exp_add, ← hrule s]; ring_nf
  unfold caraValue
  simp only [e]
  rw [mul_assoc, Finset.sum_mul]
  congr 1
  exact Finset.sum_congr rfl fun s _ => by ring

/-- **Bond Euler equation under a linear sharing rule**: if `γ(c₂(s) − c₁) = κΔ(s)` and
`β > 0`, then `e^{-γc₁} = (1 + r) β Σ_s π(s) e^{-γc₂(s)}` at `1 + r = caraRate` (O&R (8)). -/
theorem cara_bond_euler (Ω : StateSpace S) {β γ κ c1 : ℝ} {c2 Δ : S → ℝ} (hβ : 0 < β)
    (hrule : ∀ s, γ * (c2 s - c1) = κ * Δ s) :
    Real.exp (-(γ * c1)) = caraRate Ω β κ Δ * β * ∑ s, Ω.prob s * Real.exp (-(γ * c2 s)) := by
  have h := cara_share_euler Ω (β := β) hrule (fun _ => 1)
  simp only [mul_one] at h
  have hK := caraKernel_pos Ω κ Δ
  rw [mul_assoc, ← h]
  unfold caraRate caraValue caraKernel at *
  simp only [mul_one]
  field_simp

/-- **Exercise 5(a): complete markets with CARA utility**, O&R p. 347. With a common
`γ > 0`, Euler equations `q(s) e^{-γC₁} = π(s) β e^{-γC₂(s)}` for Home and Foreign
(`π(s) > 0`, `β > 0`) and market clearing, (i) consumption differences are constant across
dates and states, `C₂(s) − C₂*(s) = C₁ − C₁*`; (ii) `C₁ = Y₁ᵂ/2 − μ`, `C₂(s) = Y₂ᵂ(s)/2 − μ`
and `C₁* = Y₁ᵂ/2 + μ`, `C₂*(s) = Y₂ᵂ(s)/2 + μ` with `μ = (C₁* − C₁)/2`; (iii) prices are
`q(s) = π(s) β exp(−γ(Y₂ᵂ(s) − Y₁ᵂ)/2)`. -/
theorem exercise5a (Ω : StateSpace S) {q C2 C2f Y2W : S → ℝ} {β γ C1 C1f Y1W : ℝ}
    (hπ : ∀ s, 0 < Ω.prob s) (hβ : 0 < β) (hγ : 0 < γ)
    (he : ∀ s, q s * Real.exp (-(γ * C1)) = Ω.prob s * β * Real.exp (-(γ * C2 s)))
    (hef : ∀ s, q s * Real.exp (-(γ * C1f)) = Ω.prob s * β * Real.exp (-(γ * C2f s)))
    (hc1 : C1 + C1f = Y1W) (hc2 : ∀ s, C2 s + C2f s = Y2W s) :
    (∀ s, C2 s - C2f s = C1 - C1f) ∧
      (C1 = Y1W / 2 - (C1f - C1) / 2 ∧ C1f = Y1W / 2 + (C1f - C1) / 2) ∧
      (∀ s, C2 s = Y2W s / 2 - (C1f - C1) / 2 ∧ C2f s = Y2W s / 2 + (C1f - C1) / 2) ∧
      ∀ s, q s = Ω.prob s * β * Real.exp (-(γ * ((Y2W s - Y1W) / 2))) := by
  have hd : ∀ s, C2 s - C1 = C2f s - C1f := by
    intro s
    have h1 := cara_euler_iff.1 (he s)
    have h2 := cara_euler_iff.1 (hef s)
    have hpb : 0 < Ω.prob s * β := mul_pos (hπ s) hβ
    have h3 := mul_left_cancel₀ hpb.ne' (h1.symm.trans h2)
    have h4 := Real.exp_injective h3
    have : γ * (C2 s - C1) = γ * (C2f s - C1f) := by linarith
    exact mul_left_cancel₀ hγ.ne' this
  refine ⟨fun s => by linarith [hd s], ⟨by linarith, by linarith⟩,
    fun s => ⟨by linarith [hd s, hc2 s], by linarith [hd s, hc2 s]⟩, fun s => ?_⟩
  rw [cara_euler_iff.1 (he s), show C2 s - C1 = (Y2W s - Y1W) / 2 by linarith [hd s, hc2 s]]

/-- **Exercise 5(a): the consumption gap** from Home's Arrow–Debreu budget constraint
`C₁ + Σ q C₂ = Y₁ + Σ q Y₂`: with `C₁ = Y₁ᵂ/2 − μ`, `C₂(s) = Y₂ᵂ(s)/2 − μ`,
`μ(1 + Σ_s q(s)) = Y₁ᵂ/2 + Σ_s q(s)Y₂ᵂ(s)/2 − Y₁ − Σ_s q(s)Y₂(s)`. -/
theorem exercise5a_gap {q Y2 Y2W : S → ℝ} {μ Y1 Y1W : ℝ}
    (hb : (Y1W / 2 - μ) + ∑ s, q s * (Y2W s / 2 - μ) = Y1 + ∑ s, q s * Y2 s) :
    μ * (1 + ∑ s, q s) = Y1W / 2 + ∑ s, q s * Y2W s / 2 - Y1 - ∑ s, q s * Y2 s := by
  have e : ∑ s, q s * (Y2W s / 2 - μ) = ∑ s, q s * Y2W s / 2 - μ * ∑ s, q s := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [e] at hb
  linarith

/-- **Exercise 5(b): bonds and shares support the efficient CARA allocation**, O&R p. 347.
Let `Δ(s) = Y₂ᵂ(s) − Y₁ᵂ`, share prices `V = caraValue(Y₂)`, `V* = caraValue(Y₂*)` and
`1 + r = caraRate`, all with `κ = γ/2`. Both countries hold half of each country's claim
(half the world fund); Home holds bonds `B = −μ/(1 + r)` (so for `μ > 0` Foreign lends to
Home). Then with `C = Yᵂ/2 − μ`, `C* = Yᵂ/2 + μ` on both dates:
the date-2 budgets (43) hold for both countries; Home's date-1 budget (42) implies Foreign's;
and all bond and share Euler equations (8), (44) hold in both countries. -/
theorem exercise5b (Ω : StateSpace S) {Y2 Y2f : S → ℝ} {β γ μ Y1 Y1f : ℝ} (hβ : 0 < β) :
    let Δ := fun s => (Y2 s + Y2f s) - (Y1 + Y1f)
    let R := caraRate Ω β (γ / 2) Δ
    let V := caraValue Ω β (γ / 2) Δ Y2
    let Vf := caraValue Ω β (γ / 2) Δ Y2f
    let B := -μ / R
    (∀ s, (Y2 s + Y2f s) / 2 - μ = R * B + 1 / 2 * Y2 s + 1 / 2 * Y2f s) ∧
      (∀ s, (Y2 s + Y2f s) / 2 + μ = R * (-B) + 1 / 2 * Y2 s + 1 / 2 * Y2f s) ∧
      (Y1 + V = ((Y1 + Y1f) / 2 - μ) + B + 1 / 2 * V + 1 / 2 * Vf →
        Y1f + Vf = ((Y1 + Y1f) / 2 + μ) + (-B) + 1 / 2 * V + 1 / 2 * Vf) ∧
      (∀ δ : ℝ,
        Real.exp (-(γ * ((Y1 + Y1f) / 2 + δ))) =
          R * β * ∑ s, Ω.prob s * Real.exp (-(γ * ((Y2 s + Y2f s) / 2 + δ))) ∧
        V * Real.exp (-(γ * ((Y1 + Y1f) / 2 + δ))) =
          β * ∑ s, Ω.prob s * Real.exp (-(γ * ((Y2 s + Y2f s) / 2 + δ))) * Y2 s ∧
        Vf * Real.exp (-(γ * ((Y1 + Y1f) / 2 + δ))) =
          β * ∑ s, Ω.prob s * Real.exp (-(γ * ((Y2 s + Y2f s) / 2 + δ))) * Y2f s) := by
  intro Δ R V Vf B
  have hR : R ≠ 0 := by
    have := caraKernel_pos Ω (γ / 2) Δ
    change 1 / (β * caraKernel Ω (γ / 2) Δ) ≠ 0
    positivity
  have hRB : R * B = -μ := by change R * (-μ / R) = -μ; field_simp
  refine ⟨fun s => by rw [hRB]; ring, fun s => by rw [mul_neg, hRB]; ring,
    fun h => by linarith, fun δ => ?_⟩
  have hrule : ∀ s, γ * (((Y2 s + Y2f s) / 2 + δ) - ((Y1 + Y1f) / 2 + δ)) = γ / 2 * Δ s :=
    fun s => by simp only [Δ]; ring
  exact ⟨cara_bond_euler Ω hβ hrule, cara_share_euler Ω hrule Y2, cara_share_euler Ω hrule Y2f⟩

/-- **Exercise 5(b): the bonds-and-shares allocation is efficient**, O&R p. 347: it
satisfies the complete-markets Euler equations of 5(a) at `q(s) = π(s)β exp(−(γ/2)Δ(s))`,
share prices are Arrow–Debreu values `V = Σ q(s)Y₂(s)`, and `1 + r = 1/Σ_s q(s)`. -/
theorem exercise5b_efficient (Ω : StateSpace S) {Y2 Y2f : S → ℝ} {β γ δ Y1 Y1f : ℝ} :
    let Δ := fun s => (Y2 s + Y2f s) - (Y1 + Y1f)
    let q := fun s => Ω.prob s * β * Real.exp (-(γ / 2 * Δ s))
    (∀ s, q s * Real.exp (-(γ * ((Y1 + Y1f) / 2 + δ))) =
        Ω.prob s * β * Real.exp (-(γ * ((Y2 s + Y2f s) / 2 + δ)))) ∧
      caraValue Ω β (γ / 2) Δ Y2 = ∑ s, q s * Y2 s ∧
      caraRate Ω β (γ / 2) Δ = 1 / ∑ s, q s := by
  intro Δ q
  refine ⟨fun s => ?_, ?_, ?_⟩
  · refine cara_euler_iff.2 ?_
    change Ω.prob s * β * Real.exp (-(γ / 2 * Δ s)) = _
    congr 3
    simp only [Δ]; ring
  · unfold caraValue
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => by simp only [q]; ring
  · unfold caraRate caraKernel
    congr 1
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ => by simp only [q]; ring

/-- **Exercise 5(c): linear sharing with different CARA coefficients**, O&R p. 347. With
Home `γ > 0`, Foreign `γ* > 0`, common Arrow–Debreu prices, `π(s) > 0`, `β > 0` and market
clearing, consumption changes are shared linearly: Home absorbs the fraction
`θ = γ*/(γ + γ*)` of every change in world output, `C₂(s) − C₁ = θ(Y₂ᵂ(s) − Y₁ᵂ)`, and Foreign
the fraction `1 − θ`. -/
theorem exercise5c_sharing (Ω : StateSpace S) {q C2 C2f Y2W : S → ℝ}
    {β γ γf C1 C1f Y1W : ℝ} (hπ : ∀ s, 0 < Ω.prob s) (hβ : 0 < β) (hγ : 0 < γ) (hγf : 0 < γf)
    (he : ∀ s, q s * Real.exp (-(γ * C1)) = Ω.prob s * β * Real.exp (-(γ * C2 s)))
    (hef : ∀ s, q s * Real.exp (-(γf * C1f)) = Ω.prob s * β * Real.exp (-(γf * C2f s)))
    (hc1 : C1 + C1f = Y1W) (hc2 : ∀ s, C2 s + C2f s = Y2W s) (s : S) :
    C2 s - C1 = γf / (γ + γf) * (Y2W s - Y1W) ∧
      C2f s - C1f = γ / (γ + γf) * (Y2W s - Y1W) := by
  have h1 := cara_euler_iff.1 (he s)
  have h2 := cara_euler_iff.1 (hef s)
  have hpb : 0 < Ω.prob s * β := mul_pos (hπ s) hβ
  have h4 := Real.exp_injective (mul_left_cancel₀ hpb.ne' (h1.symm.trans h2))
  have hs : 0 < γ + γf := by linarith
  have hsum : (C2 s - C1) + (C2f s - C1f) = Y2W s - Y1W := by linarith [hc2 s]
  constructor
  · rw [div_mul_eq_mul_div, eq_div_iff hs.ne']
    linear_combination (-1) * h4 + γf * hsum
  · rw [div_mul_eq_mul_div, eq_div_iff hs.ne']
    linear_combination h4 + γ * hsum

/-- **Exercise 5(c): bonds and shares support the linear sharing rule**, O&R p. 347 and
footnote 27. With `θ = γ*/(γ + γ*)` and `κ = γγ*/(γ + γ*)`, share prices `caraValue`, rate
`caraRate` (both at `κ`, `Δ = Y₂ᵂ − Y₁ᵂ`): Home holds the fraction `θ` of the world fund and
bonds `B = (C₁ − θY₁ᵂ)/(1 + r)`, Foreign holds `1 − θ` and `−B`. Then the date-2 budgets
(43) deliver `C₂ = C₁ + θΔ`, `C₂* = C₁* + (1 − θ)Δ`, Home's date-1 budget (42) implies
Foreign's, and every bond and share Euler equation holds in both countries at common prices.
The less risk-averse country (smaller `γ`) holds more than half of the risky fund. -/
theorem exercise5c_support (Ω : StateSpace S) {Y2 Y2f : S → ℝ} {β γ γf C1 C1f Y1 Y1f : ℝ}
    (hβ : 0 < β) (hγ : 0 < γ) (hγf : 0 < γf) (hc1 : C1 + C1f = Y1 + Y1f) :
    let θ := γf / (γ + γf)
    let κ := γ * γf / (γ + γf)
    let Δ := fun s => (Y2 s + Y2f s) - (Y1 + Y1f)
    let R := caraRate Ω β κ Δ
    let V := caraValue Ω β κ Δ Y2
    let Vf := caraValue Ω β κ Δ Y2f
    let B := (C1 - θ * (Y1 + Y1f)) / R
    (∀ s, C1 + θ * Δ s = R * B + θ * Y2 s + θ * Y2f s) ∧
      (∀ s, C1f + (1 - θ) * Δ s = R * (-B) + (1 - θ) * Y2 s + (1 - θ) * Y2f s) ∧
      (Y1 + V = C1 + B + θ * V + θ * Vf →
        Y1f + Vf = C1f + (-B) + (1 - θ) * V + (1 - θ) * Vf) ∧
      (Real.exp (-(γ * C1)) = R * β * ∑ s, Ω.prob s * Real.exp (-(γ * (C1 + θ * Δ s))) ∧
        ∀ Z : S → ℝ, caraValue Ω β κ Δ Z * Real.exp (-(γ * C1)) =
          β * ∑ s, Ω.prob s * Real.exp (-(γ * (C1 + θ * Δ s))) * Z s) ∧
      (Real.exp (-(γf * C1f)) =
          R * β * ∑ s, Ω.prob s * Real.exp (-(γf * (C1f + (1 - θ) * Δ s))) ∧
        ∀ Z : S → ℝ, caraValue Ω β κ Δ Z * Real.exp (-(γf * C1f)) =
          β * ∑ s, Ω.prob s * Real.exp (-(γf * (C1f + (1 - θ) * Δ s))) * Z s) := by
  intro θ κ Δ R V Vf B
  have hs : 0 < γ + γf := by linarith
  have hR : R ≠ 0 := by
    have := caraKernel_pos Ω κ Δ
    change 1 / (β * caraKernel Ω κ Δ) ≠ 0
    positivity
  have hRB : R * B = C1 - θ * (Y1 + Y1f) := by
    change R * ((C1 - θ * (Y1 + Y1f)) / R) = _; field_simp
  have hrule : ∀ s, γ * ((C1 + θ * Δ s) - C1) = κ * Δ s := fun s => by
    simp only [θ, κ]; field_simp; ring
  have hrulef : ∀ s, γf * ((C1f + (1 - θ) * Δ s) - C1f) = κ * Δ s := fun s => by
    simp only [θ, κ]; field_simp; ring
  refine ⟨fun s => ?_, fun s => ?_, fun h => ?_,
    ⟨cara_bond_euler Ω hβ hrule, cara_share_euler Ω hrule⟩,
    ⟨cara_bond_euler Ω hβ hrulef, cara_share_euler Ω hrulef⟩⟩
  · rw [hRB]; simp only [Δ]; ring
  · rw [mul_neg, hRB]; simp only [Δ]; linear_combination hc1
  · linear_combination (-1) * h + (-1) * hc1

end Exercise5

end ObstfeldRogoff.InternationalFinancialMarkets.PortfolioDiversification
