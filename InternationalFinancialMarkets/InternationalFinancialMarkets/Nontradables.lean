/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import InternationalFinancialMarkets.Probability
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add

/-!
# The role of nontradables

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §5.5,
pp. 319–329.

`N` countries (a type `ι`) consume a tradable good `C_T` and a nontradable good `C_N`, with
period utility `u(C_T, C_N)` (O&R (62)); date-2 states are a finite type `S` with
probabilities `π(s)`. AD securities pay tradables; each country has its own relative price of
nontradables `p_N`. Marginal utilities are given as functions `uT, uN : ℝ → ℝ → ℝ`
(`uT C_T C_N = ∂u/∂C_T`). We prove:
* the efficiency condition (67) from the Euler equations (65) and nontradables market
  clearing (66), and that the second Euler equation in (65) follows from the first and the
  intratemporal condition (64);
* the claim prices (68)–(69) do not depend on whose marginal rate of substitution is used;
* preference shocks: (71) from (70);
* additively separable utility `C_T^{1−ρ}/(1−ρ) + v(C_N)`: tradables consumption growth is
  equalised and equals world tradables growth (74), and the home-bias portfolio
  (footnote 48) satisfies every country's Euler equation for every nontradables claim;
* CES–CRRA utility (72): its marginal utilities (as exact derivatives), the cross-partial
  `∂²u/∂C_N∂C_T` has the sign of `1 − θρ`, the revenue `p_N Y_N` increases in `Y_N` iff
  `θ > 1`, (72) is additively separable iff `θρ = 1`, and the log-linearised equation (73)
  as an exact identity between logarithmic derivatives along any differentiable path;
* log Cobb–Douglas: `p_N Y_N = ((1−γ)/γ) C_T`, so nontradables payoffs are perfectly
  correlated with world tradables and portfolios are indeterminate (p. 329).
-/

namespace ObstfeldRogoff.InternationalFinancialMarkets.Nontradables

open Finset Filter Topology

variable {S : Type} {ι : Type}

/-! ## Complete markets in tradables (§5.5.1, pp. 319–322) -/

/-- **O&R (5.67), p. 321**: if every country's tradables Euler equation (65),
`[p(s)/(1+r)]u_T(C_{T,1}ⁿ, C_{N,1}ⁿ) = π(s)βu_T(C_{T,2}ⁿ(s), C_{N,2}ⁿ(s))`, holds, nontradables
markets clear (66), `C_N = Y_N`, and date-1 marginal utilities are nonzero, then the ex post
marginal rates of substitution for tradables are equal across countries. -/
theorem efficiency_tradables (π p : S → ℝ) (r β : ℝ) (uT : ℝ → ℝ → ℝ)
    (CT1 CN1 YN1 : ι → ℝ) (CT2 CN2 YN2 : ι → S → ℝ)
    (hu : ∀ n, uT (CT1 n) (CN1 n) ≠ 0)
    (heuler : ∀ n s, p s / (1 + r) * uT (CT1 n) (CN1 n) = π s * β * uT (CT2 n s) (CN2 n s))
    (hclear1 : ∀ n, CN1 n = YN1 n) (hclear2 : ∀ n s, CN2 n s = YN2 n s) (m n : ι) (s : S) :
    π s * β * uT (CT2 m s) (YN2 m s) / uT (CT1 m) (YN1 m) =
      π s * β * uT (CT2 n s) (YN2 n s) / uT (CT1 n) (YN1 n) := by
  have key : ∀ k, π s * β * uT (CT2 k s) (YN2 k s) / uT (CT1 k) (YN1 k) = p s / (1 + r) := by
    intro k
    rw [← hclear1, ← hclear2, ← heuler k s]
    field_simp [hu k]
  rw [key m, key n]

/-- **The second Euler equation in (65), O&R p. 320**: it follows from the first and the
intratemporal condition (64), `u_N = p_N u_T`, on date 1 and in state `s` (with `p_{N,1} ≠ 0`):
`(1/p_{N,1})[p_{N,2}(s)p(s)/(1+r)]u_N(date 1) = π(s)βu_N(date 2, s)`. -/
theorem euler_nontradables_of_intratemporal (π p : S → ℝ) (r β pN1 uT1 uN1 : ℝ)
    (pN2 uT2 uN2 : S → ℝ) (hpN1 : pN1 ≠ 0) (h64₁ : uN1 = pN1 * uT1)
    (h64₂ : ∀ s, uN2 s = pN2 s * uT2 s) (heuler : ∀ s, p s / (1 + r) * uT1 = π s * β * uT2 s)
    (s : S) :
    1 / pN1 * (pN2 s * p s / (1 + r)) * uN1 = π s * β * uN2 s := by
  rw [h64₁, h64₂ s]
  have h := heuler s
  field_simp at h ⊢
  linear_combination pN2 s * h

/-- **O&R (5.68)–(5.69), pp. 322**: under the hypotheses of `efficiency_tradables`, the AD
value `Σ p(s)X(s)/(1+r)` of any tradables-denominated payoff `X` equals
`Σ π(s)β[u_T(C_{T,2}ⁿ(s), Y_{N,2}ⁿ(s))/u_T(C_{T,1}ⁿ, Y_{N,1}ⁿ)]X(s)` for EVERY country `n`.
With `X = Y_{T,2}ᵐ` this is (68) (`V_{T,1}ᵐ`), with `X = p_{N,2}ᵐY_{N,2}ᵐ` it is (69)
(`V_{N,1}ᵐ`). -/
theorem claim_price_any_country [Fintype S] (π p : S → ℝ) (r β : ℝ) (uT : ℝ → ℝ → ℝ)
    (CT1 CN1 YN1 : ι → ℝ) (CT2 CN2 YN2 : ι → S → ℝ)
    (hu : ∀ n, uT (CT1 n) (CN1 n) ≠ 0)
    (heuler : ∀ n s, p s / (1 + r) * uT (CT1 n) (CN1 n) = π s * β * uT (CT2 n s) (CN2 n s))
    (hclear1 : ∀ n, CN1 n = YN1 n) (hclear2 : ∀ n s, CN2 n s = YN2 n s) (X : S → ℝ) (n : ι) :
    ∑ s, p s * X s / (1 + r) =
      ∑ s, π s * β * uT (CT2 n s) (YN2 n s) / uT (CT1 n) (YN1 n) * X s := by
  refine Finset.sum_congr rfl fun s _ => ?_
  have h := heuler n s
  rw [hclear1, hclear2] at h
  have hu' := hu n
  rw [hclear1] at hu'
  rw [← h]
  field_simp [hu']

/-- **O&R (5.68)–(5.69), p. 322, independence of the country**: the valuations of any
tradables-denominated payoff by the marginal rates of substitution of countries `n` and `k`
coincide. -/
theorem claim_price_independent [Fintype S] (π p : S → ℝ) (r β : ℝ) (uT : ℝ → ℝ → ℝ)
    (CT1 CN1 YN1 : ι → ℝ) (CT2 CN2 YN2 : ι → S → ℝ)
    (hu : ∀ n, uT (CT1 n) (CN1 n) ≠ 0)
    (heuler : ∀ n s, p s / (1 + r) * uT (CT1 n) (CN1 n) = π s * β * uT (CT2 n s) (CN2 n s))
    (hclear1 : ∀ n, CN1 n = YN1 n) (hclear2 : ∀ n s, CN2 n s = YN2 n s) (X : S → ℝ)
    (n k : ι) :
    ∑ s, π s * β * uT (CT2 n s) (YN2 n s) / uT (CT1 n) (YN1 n) * X s =
      ∑ s, π s * β * uT (CT2 k s) (YN2 k s) / uT (CT1 k) (YN1 k) * X s := by
  rw [← claim_price_any_country π p r β uT CT1 CN1 YN1 CT2 CN2 YN2 hu heuler hclear1 hclear2,
    ← claim_price_any_country π p r β uT CT1 CN1 YN1 CT2 CN2 YN2 hu heuler hclear1 hclear2]

/-! ## Preference shocks (§5.5.2, pp. 322–323) -/

/-- **O&R (5.71), p. 323**: with state-dependent preferences `u(C₂(s); εⁿ(s))` (O&R (70)),
the Euler equations `[p(s)/(1+r)]u′(C₁ⁿ) = π(s)βu′(C₂ⁿ(s); εⁿ(s))` for all countries imply
equal marginal rates of substitution (nonzero date-1 marginal utilities). -/
theorem efficiency_preference_shocks (π p : S → ℝ) (r β : ℝ) (u1' : ℝ → ℝ)
    (u2' : ℝ → ℝ → ℝ) (C1 : ι → ℝ) (C2 ε : ι → S → ℝ) (hu : ∀ n, u1' (C1 n) ≠ 0)
    (heuler : ∀ n s, p s / (1 + r) * u1' (C1 n) = π s * β * u2' (C2 n s) (ε n s))
    (m n : ι) (s : S) :
    π s * β * u2' (C2 m s) (ε m s) / u1' (C1 m) = π s * β * u2' (C2 n s) (ε n s) / u1' (C1 n) := by
  rw [← heuler m s, ← heuler n s]
  field_simp [hu m, hu n]

/-! ## Additively separable utility (§5.5.3, pp. 326–327) -/

/-- **Equal tradables growth, O&R p. 322 and (5.74), p. 326**: with additive utility
`C_T^{1−ρ}/(1−ρ) + v(C_N)` (so `u_T = C_T^{−ρ}`, `ρ > 0`), the tradables Euler equations
`[p(s)/(1+r)](C_{T,1}ⁿ)^{−ρ} = π(s)β(C_{T,2}ⁿ(s))^{−ρ}` with `π(s), β > 0` and positive
consumptions imply that tradables consumption growth is the same in every country. -/
theorem additive_tradables_growth_equal (π p : S → ℝ) {r β ρ : ℝ} (hρ : 0 < ρ) (hβ : 0 < β)
    (hπ : ∀ s, 0 < π s) (CT1 : ι → ℝ) (CT2 : ι → S → ℝ) (h1 : ∀ n, 0 < CT1 n)
    (h2 : ∀ n s, 0 < CT2 n s)
    (heuler : ∀ n s, p s / (1 + r) * CT1 n ^ (-ρ) = π s * β * CT2 n s ^ (-ρ)) (m n : ι)
    (s : S) :
    CT2 m s / CT1 m = CT2 n s / CT1 n := by
  have key : ∀ k, (CT2 k s / CT1 k) ^ (-ρ) = p s / (1 + r) / (π s * β) := by
    intro k
    have hpb : 0 < π s * β := mul_pos (hπ s) hβ
    have hc : 0 < CT1 k ^ (-ρ) := Real.rpow_pos_of_pos (h1 k) _
    rw [Real.div_rpow (h2 k s).le (h1 k).le, eq_div_iff hpb.ne', div_mul_eq_mul_div,
      div_eq_iff hc.ne', heuler k s]
    ring
  have hne : -ρ ≠ 0 := by linarith
  exact Real.rpow_left_injOn hne (div_pos (h2 m s) (h1 m)).le (div_pos (h2 n s) (h1 n)).le
    (by simp only [key m, key n])

/-- **O&R (5.74), p. 326**: under the hypotheses of `additive_tradables_growth_equal`, with
finitely many countries and world tradables market clearing on both dates
(`Σₙ C_{T,1}ⁿ = Y_{T,1}^W`, `Σₙ C_{T,2}ⁿ(s) = Y_{T,2}^W(s)`), every country's tradables
growth equals world tradables growth: `C_{T,2}ⁿ(s)/C_{T,1}ⁿ = Y_{T,2}^W(s)/Y_{T,1}^W`. -/
theorem additive_tradables_growth_world [Fintype ι] (π p : S → ℝ) {r β ρ : ℝ} (hρ : 0 < ρ)
    (hβ : 0 < β) (hπ : ∀ s, 0 < π s) (CT1 : ι → ℝ) (CT2 : ι → S → ℝ) (h1 : ∀ n, 0 < CT1 n)
    (h2 : ∀ n s, 0 < CT2 n s)
    (heuler : ∀ n s, p s / (1 + r) * CT1 n ^ (-ρ) = π s * β * CT2 n s ^ (-ρ))
    {YW1 : ℝ} {YW2 : S → ℝ} (hYW1 : YW1 ≠ 0) (hc1 : ∑ n, CT1 n = YW1)
    (hc2 : ∀ s, ∑ n, CT2 n s = YW2 s) (n : ι) (s : S) :
    CT2 n s / CT1 n = YW2 s / YW1 := by
  have hk : ∀ k, CT2 k s = CT2 n s / CT1 n * CT1 k := by
    intro k
    rw [← additive_tradables_growth_equal π p hρ hβ hπ CT1 CT2 h1 h2 heuler k n s]
    field_simp [(h1 k).ne']
  have hsum : YW2 s = CT2 n s / CT1 n * YW1 := by
    rw [← hc2 s, ← hc1, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => hk k
  rw [hsum]
  field_simp

/-- **The home-bias equilibrium, O&R p. 327 and footnote 48**: with additive utility, let each
country consume a constant share `μₙ > 0` of world tradables on both dates (the equilibrium
(74)) and price every nontradables claim by
`V_{N,1}ᵐ = Σ π(s)β(Y_{T,2}^W(s)/Y_{T,1}^W)^{−ρ}p_{N,2}ᵐ(s)Y_{N,2}ᵐ(s)`. Then every country
`n`'s Euler equation for every claim `m`,
`(C_{T,1}ⁿ)^{−ρ}V_{N,1}ᵐ = βΣπ(s)(C_{T,2}ⁿ(s))^{−ρ}p_{N,2}ᵐ(s)Y_{N,2}ᵐ(s)`, holds; and the
home-bias holdings `x_{N,m}ⁿ = 1` if `m = n`, `0` otherwise, clear every claim market. Since
with additive utility tradables consumption does not depend on nontradables holdings, no
country gains from diversifying its nontradables portfolio. -/
theorem home_bias_equilibrium [Fintype S] [Fintype ι] [DecidableEq ι] (π : S → ℝ) {β ρ YW1 : ℝ}
    (YW2 : S → ℝ) (μ CT1 : ι → ℝ) (CT2 pN2 YN2 : ι → S → ℝ) (hμ : ∀ n, 0 < μ n)
    (hYW1 : 0 < YW1) (hYW2 : ∀ s, 0 < YW2 s) (hC1 : ∀ n, CT1 n = μ n * YW1)
    (hC2 : ∀ n s, CT2 n s = μ n * YW2 s) :
    (∀ n m, CT1 n ^ (-ρ) *
        (∑ s, π s * β * (YW2 s / YW1) ^ (-ρ) * (pN2 m s * YN2 m s)) =
      β * ∑ s, π s * CT2 n s ^ (-ρ) * (pN2 m s * YN2 m s)) ∧
      ∀ m, ∑ n : ι, (if m = n then (1 : ℝ) else 0) = 1 := by
  refine ⟨fun n m => ?_, fun m => by simp⟩
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [hC1, hC2, Real.div_rpow (hYW2 s).le hYW1.le, Real.mul_rpow (hμ n).le hYW1.le,
    Real.mul_rpow (hμ n).le (hYW2 s).le]
  have : 0 < YW1 ^ (-ρ) := Real.rpow_pos_of_pos hYW1 _
  field_simp

/-! ## CES–CRRA utility (§5.5.2–5.5.3, pp. 324–328) -/

/-- The CES aggregator's inner sum in O&R (5.72), p. 324:
`Z = γ^{1/θ}C_T^{(θ−1)/θ} + (1−γ)^{1/θ}C_N^{(θ−1)/θ}`. -/
noncomputable def cesInner (γ θ CT CN : ℝ) : ℝ :=
  γ ^ (1 / θ) * CT ^ ((θ - 1) / θ) + (1 - γ) ^ (1 / θ) * CN ^ ((θ - 1) / θ)

/-- **CES–CRRA utility, O&R (5.72), p. 324**: `u = [Z^{θ/(θ−1)}]^{1−ρ}/(1−ρ)`. -/
noncomputable def cesCrraUtility (γ θ ρ CT CN : ℝ) : ℝ :=
  (cesInner γ θ CT CN ^ (θ / (θ - 1))) ^ (1 - ρ) / (1 - ρ)

/-- The marginal utility of tradables for (5.72), O&R p. 324:
`u_T = γ^{1/θ}C_T^{(θ−1)/θ − 1}Z^{θ(1−ρ)/(θ−1) − 1}`. -/
noncomputable def cesMUT (γ θ ρ CT CN : ℝ) : ℝ :=
  γ ^ (1 / θ) * CT ^ ((θ - 1) / θ - 1) * cesInner γ θ CT CN ^ (θ * (1 - ρ) / (θ - 1) - 1)

/-- The marginal utility of nontradables for (5.72), O&R p. 324:
`u_N = (1−γ)^{1/θ}C_N^{(θ−1)/θ − 1}Z^{θ(1−ρ)/(θ−1) − 1}`. -/
noncomputable def cesMUN (γ θ ρ CT CN : ℝ) : ℝ :=
  (1 - γ) ^ (1 / θ) * CN ^ ((θ - 1) / θ - 1) * cesInner γ θ CT CN ^ (θ * (1 - ρ) / (θ - 1) - 1)

/-- The inner sum is positive at positive consumptions, O&R p. 324 (`0 < γ < 1`). -/
theorem cesInner_pos {γ θ CT CN : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hT : 0 < CT) (hN : 0 < CN) :
    0 < cesInner γ θ CT CN := by
  unfold cesInner
  have : 0 < 1 - γ := by linarith
  positivity

/-- **`u_T` is the partial derivative of (5.72) in `C_T`**, O&R p. 324 (`θ > 0`, `θ ≠ 1`,
`ρ ≠ 1`, `0 < γ < 1`, positive consumptions). -/
theorem hasDerivAt_cesCrra_T {γ θ ρ CT CN : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hθ : 0 < θ)
    (hθ1 : θ ≠ 1) (hρ1 : ρ ≠ 1) (hT : 0 < CT) (hN : 0 < CN) :
    HasDerivAt (fun c => cesCrraUtility γ θ ρ c CN) (cesMUT γ θ ρ CT CN) CT := by
  have hZ := cesInner_pos (θ := θ) hγ0 hγ1 hT hN
  have hθ1' : θ - 1 ≠ 0 := sub_ne_zero.mpr hθ1
  have h1ρ : 1 - ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm hρ1)
  have hd1 := ((Real.hasDerivAt_rpow_const (p := (θ - 1) / θ) (Or.inl hT.ne')).const_mul
    (γ ^ (1 / θ))).add_const ((1 - γ) ^ (1 / θ) * CN ^ ((θ - 1) / θ))
  have hd2 := hd1.rpow_const (p := θ / (θ - 1)) (Or.inl hZ.ne')
  have hZa : 0 < cesInner γ θ CT CN ^ (θ / (θ - 1)) := Real.rpow_pos_of_pos hZ _
  have hd3 := (hd2.rpow_const (p := 1 - ρ) (Or.inl hZa.ne')).div_const (1 - ρ)
  unfold cesCrraUtility cesInner
  convert hd3 using 1
  unfold cesMUT
  change _ = γ ^ (1 / θ) * ((θ - 1) / θ * CT ^ ((θ - 1) / θ - 1)) * (θ / (θ - 1)) *
      cesInner γ θ CT CN ^ (θ / (θ - 1) - 1) * (1 - ρ) *
      (cesInner γ θ CT CN ^ (θ / (θ - 1))) ^ (1 - ρ - 1) / (1 - ρ)
  rw [← Real.rpow_mul hZ.le]
  have hexp : θ * (1 - ρ) / (θ - 1) - 1 = (θ / (θ - 1) - 1) + θ / (θ - 1) * (1 - ρ - 1) := by
    field_simp; ring
  rw [hexp, Real.rpow_add hZ]
  field_simp

/-- **`u_N` is the partial derivative of (5.72) in `C_N`**, O&R p. 324 (same hypotheses). -/
theorem hasDerivAt_cesCrra_N {γ θ ρ CT CN : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hθ : 0 < θ)
    (hθ1 : θ ≠ 1) (hρ1 : ρ ≠ 1) (hT : 0 < CT) (hN : 0 < CN) :
    HasDerivAt (fun c => cesCrraUtility γ θ ρ CT c) (cesMUN γ θ ρ CT CN) CN := by
  have hZ := cesInner_pos (θ := θ) hγ0 hγ1 hT hN
  have hθ1' : θ - 1 ≠ 0 := sub_ne_zero.mpr hθ1
  have h1ρ : 1 - ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm hρ1)
  have hd1 := ((Real.hasDerivAt_rpow_const (p := (θ - 1) / θ) (Or.inl hN.ne')).const_mul
    ((1 - γ) ^ (1 / θ))).const_add (γ ^ (1 / θ) * CT ^ ((θ - 1) / θ))
  have hd2 := hd1.rpow_const (p := θ / (θ - 1)) (Or.inl hZ.ne')
  have hZa : 0 < cesInner γ θ CT CN ^ (θ / (θ - 1)) := Real.rpow_pos_of_pos hZ _
  have hd3 := (hd2.rpow_const (p := 1 - ρ) (Or.inl hZa.ne')).div_const (1 - ρ)
  unfold cesCrraUtility cesInner
  convert hd3 using 1
  unfold cesMUN
  change _ = (1 - γ) ^ (1 / θ) * ((θ - 1) / θ * CN ^ ((θ - 1) / θ - 1)) * (θ / (θ - 1)) *
      cesInner γ θ CT CN ^ (θ / (θ - 1) - 1) * (1 - ρ) *
      (cesInner γ θ CT CN ^ (θ / (θ - 1))) ^ (1 - ρ - 1) / (1 - ρ)
  rw [← Real.rpow_mul hZ.le]
  have hexp : θ * (1 - ρ) / (θ - 1) - 1 = (θ / (θ - 1) - 1) + θ / (θ - 1) * (1 - ρ - 1) := by
    field_simp; ring
  rw [hexp, Real.rpow_add hZ]
  field_simp

/-- The cross-partial `∂²u/∂C_N∂C_T` of (5.72), O&R p. 328, in closed form:
`((1 − θρ)/θ)·γ^{1/θ}(1−γ)^{1/θ}C_T^{(θ−1)/θ − 1}C_N^{(θ−1)/θ − 1}Z^{θ(1−ρ)/(θ−1) − 2}`. -/
noncomputable def cesCross (γ θ ρ CT CN : ℝ) : ℝ :=
  (1 - θ * ρ) / θ * (γ ^ (1 / θ) * (1 - γ) ^ (1 / θ) * CT ^ ((θ - 1) / θ - 1) *
    CN ^ ((θ - 1) / θ - 1) * cesInner γ θ CT CN ^ (θ * (1 - ρ) / (θ - 1) - 1 - 1))

/-- **The cross-partial of (5.72), O&R p. 328**: `cesCross` is the derivative of `u_T` in
`C_N` (hypotheses as in `hasDerivAt_cesCrra_T`, except that `ρ = 1` is allowed). -/
theorem hasDerivAt_cesMUT_N {γ θ ρ CT CN : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hθ : 0 < θ)
    (hθ1 : θ ≠ 1) (hT : 0 < CT) (hN : 0 < CN) :
    HasDerivAt (fun c => cesMUT γ θ ρ CT c) (cesCross γ θ ρ CT CN) CN := by
  have hZ := cesInner_pos (θ := θ) hγ0 hγ1 hT hN
  have hθ1' : θ - 1 ≠ 0 := sub_ne_zero.mpr hθ1
  have hd1 := ((Real.hasDerivAt_rpow_const (p := (θ - 1) / θ) (Or.inl hN.ne')).const_mul
    ((1 - γ) ^ (1 / θ))).const_add (γ ^ (1 / θ) * CT ^ ((θ - 1) / θ))
  have hd2 := (hd1.rpow_const (p := θ * (1 - ρ) / (θ - 1) - 1) (Or.inl hZ.ne')).const_mul
    (γ ^ (1 / θ) * CT ^ ((θ - 1) / θ - 1))
  unfold cesMUT cesInner
  convert hd2 using 1
  unfold cesCross
  change _ = γ ^ (1 / θ) * CT ^ ((θ - 1) / θ - 1) * ((1 - γ) ^ (1 / θ) *
      ((θ - 1) / θ * CN ^ ((θ - 1) / θ - 1)) * (θ * (1 - ρ) / (θ - 1) - 1) *
      cesInner γ θ CT CN ^ (θ * (1 - ρ) / (θ - 1) - 1 - 1))
  field_simp
  ring

/-- **The sign of the cross-partial, O&R p. 328**: at positive consumptions,
`∂²u/∂C_N∂C_T > 0 ↔ θρ < 1` and `∂²u/∂C_N∂C_T < 0 ↔ θρ > 1` (so when `θ > 1/ρ` a higher
nontradables endowment lowers the marginal utility of tradables). -/
theorem cesCross_sign {γ θ ρ CT CN : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hθ : 0 < θ)
    (hT : 0 < CT) (hN : 0 < CN) :
    (0 < cesCross γ θ ρ CT CN ↔ θ * ρ < 1) ∧ (cesCross γ θ ρ CT CN < 0 ↔ 1 < θ * ρ) := by
  have hZ := cesInner_pos (θ := θ) hγ0 hγ1 hT hN
  have h1γ : 0 < 1 - γ := by linarith
  have hP : 0 < γ ^ (1 / θ) * (1 - γ) ^ (1 / θ) * CT ^ ((θ - 1) / θ - 1) *
      CN ^ ((θ - 1) / θ - 1) * cesInner γ θ CT CN ^ (θ * (1 - ρ) / (θ - 1) - 1 - 1) := by
    positivity
  unfold cesCross
  set P := γ ^ (1 / θ) * (1 - γ) ^ (1 / θ) * CT ^ ((θ - 1) / θ - 1) *
      CN ^ ((θ - 1) / θ - 1) * cesInner γ θ CT CN ^ (θ * (1 - ρ) / (θ - 1) - 1 - 1) with hPdef
  have hQ : 0 < P / θ := div_pos hP hθ
  have e : (1 - θ * ρ) / θ * P = (1 - θ * ρ) * (P / θ) := by ring
  rw [e]
  constructor
  · rw [mul_pos_iff_of_pos_right hQ]
    constructor <;> intro h <;> linarith
  · rw [← neg_pos, ← neg_mul, mul_pos_iff_of_pos_right hQ]
    constructor <;> intro h <;> linarith

/-- **(5.72) is additive when `θρ = 1`, O&R p. 324**: then
`u = γ^{1/θ}C_T^{1−ρ}/(1−ρ) + (1−γ)^{1/θ}C_N^{1−ρ}/(1−ρ)`. -/
theorem cesCrra_additive_of_theta_rho {γ θ ρ CT CN : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hθ : 0 < θ) (hθ1 : θ ≠ 1) (hθρ : θ * ρ = 1) (hT : 0 < CT) (hN : 0 < CN) :
    cesCrraUtility γ θ ρ CT CN =
      γ ^ (1 / θ) * CT ^ (1 - ρ) / (1 - ρ) + (1 - γ) ^ (1 / θ) * CN ^ (1 - ρ) / (1 - ρ) := by
  have hZ := cesInner_pos (θ := θ) hγ0 hγ1 hT hN
  have hθ1' : θ - 1 ≠ 0 := sub_ne_zero.mpr hθ1
  have hρ : ρ = 1 / θ := by field_simp; linarith
  have hk : (θ - 1) / θ = 1 - ρ := by rw [hρ]; field_simp
  have ha : θ / (θ - 1) * (1 - ρ) = 1 := by rw [hρ]; field_simp
  unfold cesCrraUtility
  rw [← Real.rpow_mul hZ.le, ha, Real.rpow_one]
  unfold cesInner
  rw [hk]
  ring

/-- **Additivity forces `θρ = 1`, O&R p. 324**: if (5.72) is additively separable on the
positive orthant, `u(C_T, C_N) = f(C_T) + g(C_N)`, then `θρ = 1`. -/
theorem theta_rho_of_cesCrra_additive {γ θ ρ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hθ : 0 < θ)
    (hθ1 : θ ≠ 1) (hρ1 : ρ ≠ 1)
    (hsep : ∃ f g : ℝ → ℝ, ∀ CT CN, 0 < CT → 0 < CN → cesCrraUtility γ θ ρ CT CN = f CT + g CN) :
    θ * ρ = 1 := by
  obtain ⟨f, g, hfg⟩ := hsep
  -- `u_T(1, ·)` is constant on `(0, ∞)`
  have hf : ∀ CN, 0 < CN → HasDerivAt f (cesMUT γ θ ρ 1 CN) 1 := by
    intro CN hN
    have h := hasDerivAt_cesCrra_T hγ0 hγ1 hθ hθ1 hρ1 one_pos hN
    have hev : (fun c => f c + g CN) =ᶠ[𝓝 1] fun c => cesCrraUtility γ θ ρ c CN :=
      (eventually_gt_nhds one_pos).mono fun c hc => (hfg c CN hc hN).symm
    have h2 := (h.congr_of_eventuallyEq hev).add_const (-g CN)
    simpa using h2
  have hconst : ∀ CN, 0 < CN → cesMUT γ θ ρ 1 CN = cesMUT γ θ ρ 1 1 :=
    fun CN hN => (hf CN hN).unique (hf 1 one_pos)
  have hd := hasDerivAt_cesMUT_N (ρ := ρ) hγ0 hγ1 hθ hθ1 one_pos one_pos
  have hev : (fun _ : ℝ => cesMUT γ θ ρ 1 1) =ᶠ[𝓝 1] fun c => cesMUT γ θ ρ 1 c :=
    (eventually_gt_nhds one_pos).mono fun c hc => (hconst c hc).symm
  have h0 : cesCross γ θ ρ 1 1 = 0 :=
    (hd.congr_of_eventuallyEq hev).unique (hasDerivAt_const (1 : ℝ) (cesMUT γ θ ρ 1 1))
  have hs := cesCross_sign (ρ := ρ) hγ0 hγ1 hθ one_pos one_pos
  rw [h0] at hs
  rcases lt_trichotomy (θ * ρ) 1 with h | h | h
  · exact absurd (hs.1.mpr h) (lt_irrefl 0)
  · exact h
  · exact absurd (hs.2.mpr h) (lt_irrefl 0)

/-- **O&R p. 324: (5.72) is additively separable iff `θρ = 1`** (on the positive orthant;
`θ > 0`, `θ ≠ 1`, `ρ ≠ 1`, `0 < γ < 1`). -/
theorem cesCrra_additive_iff {γ θ ρ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hθ : 0 < θ)
    (hθ1 : θ ≠ 1) (hρ1 : ρ ≠ 1) :
    (∃ f g : ℝ → ℝ, ∀ CT CN, 0 < CT → 0 < CN → cesCrraUtility γ θ ρ CT CN = f CT + g CN) ↔
      θ * ρ = 1 :=
  ⟨theta_rho_of_cesCrra_additive hγ0 hγ1 hθ hθ1 hρ1, fun hθρ =>
    ⟨fun CT => γ ^ (1 / θ) * CT ^ (1 - ρ) / (1 - ρ),
      fun CN => (1 - γ) ^ (1 / θ) * CN ^ (1 - ρ) / (1 - ρ),
      fun _ _ hT hN => cesCrra_additive_of_theta_rho hγ0 hγ1 hθ hθ1 hθρ hT hN⟩⟩

/-- **The relative price of nontradables under (5.72), O&R (5.64), p. 320**:
`p_N = u_N/u_T = (1−γ)^{1/θ}C_N^{(θ−1)/θ − 1}/(γ^{1/θ}C_T^{(θ−1)/θ − 1})`. -/
theorem ces_relative_price {γ θ ρ CT CN : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hT : 0 < CT)
    (hN : 0 < CN) :
    cesMUN γ θ ρ CT CN / cesMUT γ θ ρ CT CN =
      (1 - γ) ^ (1 / θ) * CN ^ ((θ - 1) / θ - 1) / (γ ^ (1 / θ) * CT ^ ((θ - 1) / θ - 1)) := by
  have hZ := cesInner_pos (θ := θ) hγ0 hγ1 hT hN
  unfold cesMUN cesMUT
  have : 0 < cesInner γ θ CT CN ^ (θ * (1 - ρ) / (θ - 1) - 1) := Real.rpow_pos_of_pos hZ _
  have : 0 < γ ^ (1 / θ) := Real.rpow_pos_of_pos hγ0 _
  have : 0 < CT ^ ((θ - 1) / θ - 1) := Real.rpow_pos_of_pos hT _
  field_simp

/-- **Nontradables revenue, O&R p. 328**: under (5.72) with `C_N = Y_N` and `C_T` held fixed,
`p_N Y_N = (1−γ)^{1/θ}Y_N^{(θ−1)/θ}/(γ^{1/θ}C_T^{(θ−1)/θ − 1})`, which is strictly increasing
in `Y_N > 0` if and only if `θ > 1` (`θ > 0`). -/
theorem ces_revenue_strictMono_iff {γ θ ρ CT : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hθ : 0 < θ)
    (hT : 0 < CT) :
    StrictMonoOn (fun Y => cesMUN γ θ ρ CT Y / cesMUT γ θ ρ CT Y * Y) (Set.Ioi 0) ↔ 1 < θ := by
  set c := (1 - γ) ^ (1 / θ) / (γ ^ (1 / θ) * CT ^ ((θ - 1) / θ - 1)) with hc
  have h1γ : 0 < 1 - γ := by linarith
  have hcpos : 0 < c := by positivity
  have hform : ∀ Y, 0 < Y → cesMUN γ θ ρ CT Y / cesMUT γ θ ρ CT Y * Y = c * Y ^ ((θ - 1) / θ) := by
    intro Y hY
    rw [ces_relative_price hγ0 hγ1 hT hY, Real.rpow_sub_one hY.ne', hc]
    field_simp
  constructor
  · intro hmono
    by_contra hle
    push Not at hle
    have hk : (θ - 1) / θ ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hθ.le
    have h12 := hmono (Set.mem_Ioi.mpr one_pos) (Set.mem_Ioi.mpr two_pos) one_lt_two
    simp only at h12
    rw [hform 1 one_pos, hform 2 two_pos] at h12
    have := Real.rpow_le_rpow_of_nonpos one_pos one_le_two hk
    nlinarith
  · intro hθ1'
    have hk : 0 < (θ - 1) / θ := div_pos (by linarith) hθ
    intro x hx y hy hxy
    simp only
    rw [hform x hx, hform y hy]
    exact mul_lt_mul_of_pos_left (Real.rpow_lt_rpow (le_of_lt hx) hxy hk) hcpos

/-- **The log-linearised equation (5.73) as an exact identity, O&R p. 324**: along any path
`t ↦ (C_T(t), Y_N(t), λ(t))` of positive values differentiable at `t₀` on which the
efficiency condition `u_T(C_T, Y_N) = λ` holds identically, the logarithmic derivatives
(`x̂ = x′/x`) satisfy
`Ĉ_T = [−θλ̂ + (1−φ)(1−θρ)Ŷ_N]/[1 − φ(1−θρ)]`, with
`φ = γ^{1/θ}C_T^{(θ−1)/θ}/Z ∈ (0, 1)`; the denominator is positive. (Hypotheses: `θ > 0`,
`θ ≠ 1`, `ρ > 0`, `0 < γ < 1`.) -/
theorem ces_loglinear_exact {γ θ ρ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hθ : 0 < θ)
    (hθ1 : θ ≠ 1) (hρ : 0 < ρ) (c y l : ℝ → ℝ) {c' y' l' t₀ : ℝ} (hc0 : ∀ t, 0 < c t)
    (hy0 : ∀ t, 0 < y t) (hpath : ∀ t, cesMUT γ θ ρ (c t) (y t) = l t)
    (hc : HasDerivAt c c' t₀) (hy : HasDerivAt y y' t₀) (hl : HasDerivAt l l' t₀) :
    0 < 1 - γ ^ (1 / θ) * c t₀ ^ ((θ - 1) / θ) / cesInner γ θ (c t₀) (y t₀) *
        (1 - θ * ρ) ∧
      c' / c t₀ = (-θ * (l' / l t₀) + (1 - γ ^ (1 / θ) * c t₀ ^ ((θ - 1) / θ) /
          cesInner γ θ (c t₀) (y t₀)) * (1 - θ * ρ) * (y' / y t₀)) /
        (1 - γ ^ (1 / θ) * c t₀ ^ ((θ - 1) / θ) / cesInner γ θ (c t₀) (y t₀) * (1 - θ * ρ)) := by
  have hθ1' : θ - 1 ≠ 0 := sub_ne_zero.mpr hθ1
  have h1γ : 0 < 1 - γ := by linarith
  have hZ := cesInner_pos (θ := θ) hγ0 hγ1 (hc0 t₀) (hy0 t₀)
  have hA : 0 < γ ^ (1 / θ) := Real.rpow_pos_of_pos hγ0 _
  have hB : 0 < (1 - γ) ^ (1 / θ) := Real.rpow_pos_of_pos h1γ _
  have hX : 0 < c t₀ ^ ((θ - 1) / θ) := Real.rpow_pos_of_pos (hc0 t₀) _
  have hYk : 0 < y t₀ ^ ((θ - 1) / θ) := Real.rpow_pos_of_pos (hy0 t₀) _
  -- the share `φ` lies in `(0, 1)`
  have hφ0 : 0 < γ ^ (1 / θ) * c t₀ ^ ((θ - 1) / θ) / cesInner γ θ (c t₀) (y t₀) := by
    positivity
  have hφ1 : γ ^ (1 / θ) * c t₀ ^ ((θ - 1) / θ) / cesInner γ θ (c t₀) (y t₀) < 1 := by
    rw [div_lt_one hZ]; unfold cesInner; nlinarith [mul_pos hB hYk]
  have hden : 0 < 1 - γ ^ (1 / θ) * c t₀ ^ ((θ - 1) / θ) / cesInner γ θ (c t₀) (y t₀) *
      (1 - θ * ρ) := by
    nlinarith [mul_pos hφ0 (mul_pos hθ hρ)]
  refine ⟨hden, ?_⟩
  -- differentiate `u_T(c(t), y(t))`
  have hZd := ((hc.rpow_const (p := (θ - 1) / θ) (Or.inl (hc0 t₀).ne')).const_mul
    (γ ^ (1 / θ))).add ((hy.rpow_const (p := (θ - 1) / θ) (Or.inl (hy0 t₀).ne')).const_mul
    ((1 - γ) ^ (1 / θ)))
  have hMd := ((hc.rpow_const (p := (θ - 1) / θ - 1) (Or.inl (hc0 t₀).ne')).const_mul
    (γ ^ (1 / θ))).mul (hZd.rpow_const (p := θ * (1 - ρ) / (θ - 1) - 1) (Or.inl hZ.ne'))
  have hMd' := hMd.congr_of_eventuallyEq (f₁ := l) (Filter.Eventually.of_forall fun t => by
    rw [← hpath t]; rfl)
  have hl' := hl.unique hMd'
  have hlt : l t₀ = cesMUT γ θ ρ (c t₀) (y t₀) := (hpath t₀).symm
  rw [hl', hlt, eq_div_iff hden.ne']
  unfold cesMUT
  unfold cesInner at hZ ⊢
  simp only [Pi.add_apply, Real.rpow_sub_one (hc0 t₀).ne', Real.rpow_sub_one (hy0 t₀).ne',
    Real.rpow_sub_one hZ.ne']
  have hc0' := hc0 t₀
  have hy0' := hy0 t₀
  have hW : 0 < (γ ^ (1 / θ) * c t₀ ^ ((θ - 1) / θ) + (1 - γ) ^ (1 / θ) * y t₀ ^ ((θ - 1) / θ)) ^
      (θ * (1 - ρ) / (θ - 1)) := Real.rpow_pos_of_pos hZ _
  generalize c t₀ ^ ((θ - 1) / θ) = X at *
  generalize y t₀ ^ ((θ - 1) / θ) = Yk at *
  generalize (γ ^ (1 / θ) * X + (1 - γ) ^ (1 / θ) * Yk) ^ (θ * (1 - ρ) / (θ - 1)) = W at *
  generalize γ ^ (1 / θ) = A at *
  generalize (1 - γ) ^ (1 / θ) = B at *
  field_simp
  ring

/-! ## Log Cobb–Douglas utility (p. 328–329) -/

/-- The relative price of nontradables under `u = γ log C_T + (1−γ) log C_N`, O&R p. 328:
`p_N = u_N/u_T = ((1−γ)/C_N)/(γ/C_T)`. -/
noncomputable def cdRelPrice (γ CT CN : ℝ) : ℝ := ((1 - γ) / CN) / (γ / CT)

/-- **The Cobb–Douglas marginal utilities, O&R p. 328**: `∂u/∂C_T = γ/C_T` and
`∂u/∂C_N = (1−γ)/C_N` at positive consumptions, so `p_N = cdRelPrice`. -/
theorem cd_marginal_utilities {γ CT CN : ℝ} (hT : 0 < CT) (hN : 0 < CN) :
    HasDerivAt (fun c => γ * Real.log c + (1 - γ) * Real.log CN) (γ / CT) CT ∧
      HasDerivAt (fun c => γ * Real.log CT + (1 - γ) * Real.log c) ((1 - γ) / CN) CN := by
  constructor
  · have h := ((Real.hasDerivAt_log hT.ne').const_mul γ).add_const ((1 - γ) * Real.log CN)
    convert h using 1
    field_simp
  · have h := ((Real.hasDerivAt_log hN.ne').const_mul (1 - γ)).const_add (γ * Real.log CT)
    convert h using 1
    field_simp

/-- **Cobb–Douglas nontradables revenue, O&R p. 328–329**: with `C_N = Y_N`,
`p_N Y_N = ((1−γ)/γ)C_T`, independent of `Y_N`. -/
theorem cd_revenue {γ CT YN : ℝ} (hγ : γ ≠ 0) (hT : CT ≠ 0) (hN : YN ≠ 0) :
    cdRelPrice γ CT YN * YN = (1 - γ) / γ * CT := by
  unfold cdRelPrice
  field_simp

/-- **Portfolio indeterminacy, O&R p. 329**: under log Cobb–Douglas utility, if a country's
tradables consumption is a share `μ > 0` of world tradables output `Y_T^W` in every state,
the payoff `p_N Y_N` of its nontradables claim is perfectly correlated with `Y_T^W`
(`Corr = 1`, given `Var(Y_T^W) > 0`), so it is a perfect substitute for the world tradables
portfolio. -/
theorem cd_payoff_corr_one [Fintype S] (Ω : StateSpace S) (YW CT YN : S → ℝ) {γ μ : ℝ} (hγ0 : 0 < γ)
    (hγ1 : γ < 1) (hμ : 0 < μ) (hYN : ∀ s, YN s ≠ 0) (hCT : ∀ s, CT s = μ * YW s)
    (hYW : ∀ s, YW s ≠ 0) (hvar : 0 < Ω.var YW) :
    Ω.corr YW (fun s => cdRelPrice γ (CT s) (YN s) * YN s) = 1 := by
  have e : (fun s => cdRelPrice γ (CT s) (YN s) * YN s) =
      fun s => 0 + ((1 - γ) / γ * μ) * YW s := by
    funext s
    rw [cd_revenue hγ0.ne' (by rw [hCT]; exact mul_ne_zero hμ.ne' (hYW s)) (hYN s), hCT]
    ring
  rw [e]
  have hb : 0 < (1 - γ) / γ * μ := by
    have : 0 < 1 - γ := by linarith
    positivity
  exact Ω.corr_affine hb hvar

end ObstfeldRogoff.InternationalFinancialMarkets.Nontradables
