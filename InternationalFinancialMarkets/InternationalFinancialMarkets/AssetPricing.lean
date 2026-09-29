/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import InternationalFinancialMarkets.Probability
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

/-!
# Asset pricing: the consumption-based CAPM

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §5.4,
pp. 306–319, and the Lucas welfare-cost application of §5.5, pp. 329–331.

Uncertainty is a finite state space (`InternationalFinancialMarkets.Model`), with moments from
`InternationalFinancialMarkets.Probability`. The stochastic discount factor (intertemporal
marginal rate of substitution) is `M(s) = βu′(C₂(s))/u′(C₁)`. We prove:
* (51) `V = E[MY]` from the Arrow–Debreu (AD) pricing condition (6), the bond price
  `E[M] = 1/(1+r)` from `Σ p(s) = 1`, (52) `V = E[Y]/(1+r) + Cov(M, Y)`, and the
  consumption CAPM (53), together with footnote 32 (shift invariance of the covariance);
* §5.4.1.3: under incomplete markets, every country that trades bonds and the country-`m`
  share has the same `Cov(Mⁿ, rᵐ)`, and with multiplicative productivity shocks spanned by
  bonds and shares every owner values investment identically, including its derivative;
* the Hansen–Jagannathan bound (footnote 38);
* the equity-premium relation, exactly, for the linearised discount factor
  `M = β(1 − ρ(C₂/C₁ − 1))` (the Taylor approximation leading to it is informal in the book),
  and the Mankiw–Zeldes calibration `ρ ≈ 25.7`;
* the lognormal riskless rate (p. 313), exact under the lognormal moment-generating identity
  (taken as a hypothesis), and the 3.34 percent figure;
* Lucas's welfare cost of consumption variability (75): the closed forms, the book's
  `τ = {exp[½(1−ρ)ρV]}^{1/(1−ρ)} − 1` equals exactly `exp(ρV/2) − 1` (so `τ ≥ ρV/2`), and
  `τ ≈ 0.35%` at `ρ = 10`;
* infinite-horizon pricing (59) and (61) in a deterministic (perfect-foresight) economy:
  the truncated identity, and the limit under an explicit no-bubble hypothesis; plus the
  date-by-date decomposition of (59) into discount factors (60) and covariances.
-/

namespace ObstfeldRogoff.InternationalFinancialMarkets.AssetPricing

open Finset Filter Topology

variable {S : Type} [Fintype S] (Ω : StateSpace S)

/-! ## The consumption CAPM (§5.4.1, pp. 306–308) -/

/-- **O&R (5.51), pp. 306–307**: if AD prices satisfy the first-order condition (6),
`p(s)/(1+r) = π(s)M(s)` with `M = βu′(C₂)/u′(C₁)`, then the AD value of the payoff `Y`
equals `E[MY]`. -/
theorem price_eq_expect_sdf (p M Y : S → ℝ) (r : ℝ)
    (hfoc : ∀ s, p s / (1 + r) = Ω.prob s * M s) :
    ∑ s, p s * Y s / (1 + r) = Ω.expect (fun s => M s * Y s) := by
  unfold StateSpace.expect
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [mul_div_right_comm, hfoc s]
  ring

/-- **The bond price**, O&R (5.8) as used on p. 307: with `Σ p(s) = 1` (O&R (5.7)) and the
first-order conditions (6), `E[M] = 1/(1+r)`. -/
theorem expect_sdf_eq_bond_price (p M : S → ℝ) {r : ℝ}
    (hp : ∑ s, p s = 1) (hfoc : ∀ s, p s / (1 + r) = Ω.prob s * M s) :
    Ω.expect M = 1 / (1 + r) := by
  unfold StateSpace.expect
  rw [← Finset.sum_congr rfl fun s _ => hfoc s, ← Finset.sum_div, hp]

/-- **O&R (5.52), p. 307**: if `V = E[MY]` and the bond is priced by `E[M] = 1/(1+r)`, then
`V = E[Y]/(1+r) + Cov(M, Y)`. -/
theorem price_eq_discounted_mean_add_cov (M Y : S → ℝ) {r V : ℝ}
    (hV : V = Ω.expect (fun s => M s * Y s)) (hbond : Ω.expect M = 1 / (1 + r)) :
    V = Ω.expect Y / (1 + r) + Ω.cov M Y := by
  rw [hV, Ω.expect_mul_eq, hbond]
  ring

/-- **Pricing a gross return**, O&R p. 307: a gross return `R` with `E[MR] = 1`, and the bond
Euler equation `E[M] = 1/(1+r)` (`r > −1`), satisfy `E[R] − (1+r) = −(1+r) Cov(M, R)`. -/
theorem expect_gross_return_sub (M R : S → ℝ) {r : ℝ} (hr : 1 + r ≠ 0)
    (hR : Ω.expect (fun s => M s * R s) = 1) (hbond : Ω.expect M = 1 / (1 + r)) :
    Ω.expect R - (1 + r) = -(1 + r) * Ω.cov M R := by
  have h := Ω.expect_mul_eq M R
  rw [hR, hbond] at h
  field_simp at h ⊢
  linarith

/-- **The consumption-based CAPM, O&R (5.53), p. 307**: with `V = E[MY] ≠ 0`, the bond price
`E[M] = 1/(1+r)` and the net return `rᵐ = (Y − V)/V`,
`E[rᵐ] − r = −(1+r)Cov(M, 1 + rᵐ) = −(1+r)Cov(M, rᵐ − r)`. -/
theorem consumption_capm (M Y : S → ℝ) {r V : ℝ} (hr : 1 + r ≠ 0) (hV0 : V ≠ 0)
    (hV : V = Ω.expect (fun s => M s * Y s)) (hbond : Ω.expect M = 1 / (1 + r)) :
    Ω.expect (fun s => (Y s - V) / V) - r =
        -(1 + r) * Ω.cov M (fun s => 1 + (Y s - V) / V) ∧
      Ω.expect (fun s => (Y s - V) / V) - r =
        -(1 + r) * Ω.cov M (fun s => (Y s - V) / V - r) := by
  have hR : Ω.expect (fun s => M s * (1 + (Y s - V) / V)) = 1 := by
    have e : (fun s => M s * (1 + (Y s - V) / V)) = fun s => V⁻¹ * (M s * Y s) := by
      funext s; field_simp; ring
    rw [e, Ω.expect_smul, ← hV, inv_mul_cancel₀ hV0]
  have h := expect_gross_return_sub Ω M (fun s => 1 + (Y s - V) / V) hr hR hbond
  rw [Ω.expect_add, Ω.expect_const] at h
  have hshift : Ω.cov M (fun s => (Y s - V) / V - r) =
      Ω.cov M (fun s => 1 + (Y s - V) / V) := by
    rw [Ω.cov_comm, Ω.cov_comm M (fun s => 1 + (Y s - V) / V)]
    have e1 : (fun s => (Y s - V) / V - r) = fun s => -r + (Y s - V) / V := by
      funext s; ring
    rw [e1, Ω.cov_const_add, Ω.cov_const_add]
  refine ⟨by linarith, by rw [hshift]; linarith⟩

/-- **O&R footnote 32, p. 308**: `Cov(M, rᵐ + a₀) = Cov(M, rᵐ)` for any constant `a₀`. -/
theorem cov_add_const_right (M X : S → ℝ) (a₀ : ℝ) :
    Ω.cov M (fun s => X s + a₀) = Ω.cov M X := by
  rw [Ω.cov_comm, Ω.cov_comm M X]
  have e : (fun s => X s + a₀) = fun s => a₀ + X s := by funext s; ring
  rw [e, Ω.cov_const_add]

/-! ## Incomplete markets (§5.4.1.3, pp. 308–309) -/

/-- **O&R §5.4.1.3, p. 308**: under incomplete markets, if every country `n` trades the
riskless bond (Euler equation (8), `E[Mⁿ] = 1/(1+r)`) and the country-`m` share (Euler
equation (44), `E[Mⁿ(1 + rᵐ)] = 1`), then
`Cov(Mⁿ, rᵐ) = (1/(1+r))(1 + r − E(1 + rᵐ))`, the same for every country. -/
theorem cov_sdf_return_incomplete {ι : Type} (M : ι → S → ℝ) (rm : S → ℝ) {r : ℝ}
    (hr : 1 + r ≠ 0)
    (hbond : ∀ n, Ω.expect (M n) = 1 / (1 + r))
    (hshare : ∀ n, Ω.expect (fun s => M n s * (1 + rm s)) = 1) :
    (∀ n, Ω.cov (M n) rm = 1 / (1 + r) * (1 + r - Ω.expect (fun s => 1 + rm s))) ∧
      ∀ n k, Ω.cov (M n) rm = Ω.cov (M k) rm := by
  have key : ∀ n, Ω.cov (M n) rm = 1 / (1 + r) * (1 + r - Ω.expect (fun s => 1 + rm s)) := by
    intro n
    have h := Ω.expect_mul_eq (M n) (fun s => 1 + rm s)
    rw [hshare n, hbond n] at h
    have hc : Ω.cov (M n) (fun s => 1 + rm s) = Ω.cov (M n) rm := by
      rw [Ω.cov_comm, Ω.cov_const_add, Ω.cov_comm]
    rw [← hc]
    field_simp at h ⊢
    linarith
  exact ⟨key, fun n k => by rw [key n, key k]⟩

/-- **Investment under incomplete markets, O&R pp. 308–309**: the country-`m` firm pays
`A(s)F(K) + K` (multiplicative productivity uncertainty, no depreciation, footnote 35). If
every owner `n` prices the bond (`E[Mⁿ] = 1/(1+r)`) and the firm's shares at the installed
capital `K₀` (`E[Mⁿ(AF(K₀) + K₀)] = V₀`, the common share price) and `F(K₀) ≠ 0`, then for
EVERY `K` all owners agree on the net value `V − K`, which equals
`E[AF(K) + K]/(1+r) + Cov(Mⁿ, A)F(K) − K`. -/
theorem investment_value_invariant {ι : Type} (M : ι → S → ℝ) (A : S → ℝ) (F : ℝ → ℝ)
    {r K₀ V₀ : ℝ} (hF : F K₀ ≠ 0) (hbond : ∀ n, Ω.expect (M n) = 1 / (1 + r))
    (hshare : ∀ n, Ω.expect (fun s => M n s * (A s * F K₀ + K₀)) = V₀) (K : ℝ) :
    (∀ n, Ω.expect (fun s => M n s * (A s * F K + K)) - K =
        Ω.expect (fun s => A s * F K + K) / (1 + r) + Ω.cov (M n) A * F K - K) ∧
      ∀ n k, Ω.expect (fun s => M n s * (A s * F K + K)) - K =
        Ω.expect (fun s => M k s * (A s * F K + K)) - K := by
  have lin : ∀ n (x y : ℝ), Ω.expect (fun s => M n s * (A s * x + y)) =
      x * Ω.expect (fun s => M n s * A s) + y * Ω.expect (M n) := by
    intro n x y
    have e : (fun s => M n s * (A s * x + y)) = fun s => x * (M n s * A s) + y * M n s := by
      funext s; ring
    rw [e, Ω.expect_add, Ω.expect_smul, Ω.expect_smul]
  have hMA : ∀ n, Ω.expect (fun s => M n s * A s) = (V₀ - K₀ / (1 + r)) / F K₀ := by
    intro n
    have h := hshare n
    rw [lin, hbond, mul_one_div] at h
    rw [eq_div_iff hF]
    linarith
  refine ⟨fun n => ?_, fun n k => by rw [lin, lin, hMA, hMA, hbond, hbond]⟩
  have e2 : (fun s => A s * F K + K) = fun s => K + F K * A s := by funext s; ring
  rw [lin, e2, Ω.expect_add, Ω.expect_const, Ω.expect_smul, Ω.expect_mul_eq, hbond]
  ring

/-- **The investment derivative, O&R p. 309**: with the net value written as in
`investment_value_invariant`, `d(V − K)/dK = E[(AF′(K) + 1)/(1+r)] + Cov(Mⁿ, A)F′(K) − 1`,
which (by `investment_value_invariant`) does not depend on the owner `n`. -/
theorem investment_value_hasDerivAt (M A : S → ℝ) (F : ℝ → ℝ) {r F' K : ℝ}
    (hFd : HasDerivAt F F' K) :
    HasDerivAt (fun k => Ω.expect (fun s => A s * F k + k) / (1 + r) + Ω.cov M A * F k - k)
      (Ω.expect (fun s => (A s * F' + 1) / (1 + r)) + Ω.cov M A * F' - 1) K := by
  have e : (fun k => Ω.expect (fun s => A s * F k + k) / (1 + r) + Ω.cov M A * F k - k) =
      fun k => (Ω.expect A / (1 + r) + Ω.cov M A) * F k + (1 / (1 + r) - 1) * k := by
    funext k
    have e2 : (fun s => A s * F k + k) = fun s => k + F k * A s := by funext s; ring
    rw [e2, Ω.expect_add, Ω.expect_const, Ω.expect_smul]
    ring
  have e3 : Ω.expect (fun s => (A s * F' + 1) / (1 + r)) =
      Ω.expect A * F' / (1 + r) + 1 / (1 + r) := by
    have e4 : (fun s => (A s * F' + 1) / (1 + r)) =
        fun s => 1 / (1 + r) + (F' / (1 + r)) * A s := by
      funext s; ring
    rw [e4, Ω.expect_add, Ω.expect_const, Ω.expect_smul]
    ring
  rw [e, e3]
  have h1 := (hFd.const_mul (Ω.expect A / (1 + r) + Ω.cov M A))
  have h2 := ((hasDerivAt_id' K).const_mul (1 / (1 + r) - 1))
  refine (HasDerivAt.add h1 h2).congr_deriv ?_
  ring

/-! ## The Hansen–Jagannathan bound (footnote 38, pp. 311–312) -/

/-- **The Hansen–Jagannathan bound, O&R footnote 38**: if the gross return `R = 1 + rᵐ`
satisfies the Euler equation `E[MR] = 1`, then `Std(M)Std(R) ≥ 1 − E(M)E(R)`. -/
theorem hansen_jagannathan (M R : S → ℝ) (hR : Ω.expect (fun s => M s * R s) = 1) :
    1 - Ω.expect M * Ω.expect R ≤ Ω.std M * Ω.std R := by
  have h := Ω.expect_mul_eq M R
  rw [hR] at h
  have hc : Ω.cov M R = 1 - Ω.expect M * Ω.expect R := by linarith
  rw [← hc]
  exact (le_abs_self _).trans (Ω.abs_cov_le M R)

/-- **The Hansen–Jagannathan bound in ratio form**, O&R footnote 38:
`Std(M) ≥ (1 − E(M)E(R))/Std(R)` when `Std(R) > 0`. -/
theorem hansen_jagannathan_div (M R : S → ℝ) (hR : Ω.expect (fun s => M s * R s) = 1)
    (hstd : 0 < Ω.std R) :
    (1 - Ω.expect M * Ω.expect R) / Ω.std R ≤ Ω.std M := by
  rw [div_le_iff₀ hstd]
  exact hansen_jagannathan Ω M R hR

/-! ## The equity premium (§5.4.2, pp. 310–312) -/

/-- **The equity premium, exact version of O&R p. 311**: if the discount factor is exactly
the linearised `M = β(1 − ρ(g − 1))`, `g = C₂/C₁` (the book obtains this only by a Taylor
approximation), `E[M] = 1/(1+r)` and `E[M(1 + rᵐ)] = 1`, then
`E[rᵐ] − r = (1+r)βρ Cov(g − 1, rᵐ − r) = (1+r)βρ Cov(g, rᵐ)`. -/
theorem equity_premium_linear_sdf (g rm : S → ℝ) {β ρ r : ℝ} (hr : 1 + r ≠ 0)
    (hbond : Ω.expect (fun s => β * (1 - ρ * (g s - 1))) = 1 / (1 + r))
    (hshare : Ω.expect (fun s => β * (1 - ρ * (g s - 1)) * (1 + rm s)) = 1) :
    Ω.expect rm - r = (1 + r) * β * ρ * Ω.cov (fun s => g s - 1) (fun s => rm s - r) ∧
      Ω.expect rm - r = (1 + r) * β * ρ * Ω.cov g rm := by
  have h := expect_gross_return_sub Ω (fun s => β * (1 - ρ * (g s - 1))) (fun s => 1 + rm s)
    hr hshare hbond
  rw [Ω.expect_add, Ω.expect_const] at h
  have hM : (fun s => β * (1 - ρ * (g s - 1))) = fun s => (β + β * ρ) + (-(β * ρ)) * g s := by
    funext s; ring
  have hc : Ω.cov (fun s => β * (1 - ρ * (g s - 1))) (fun s => 1 + rm s) =
      -(β * ρ) * Ω.cov g rm := by
    rw [hM, Ω.cov_const_add, Ω.cov_smul, Ω.cov_comm, Ω.cov_const_add, Ω.cov_comm]
  have hc2 : Ω.cov (fun s => g s - 1) (fun s => rm s - r) = Ω.cov g rm := by
    have e1 : (fun s => g s - 1) = fun s => -1 + g s := by funext s; ring
    have e2 : (fun s => rm s - r) = fun s => -r + rm s := by funext s; ring
    rw [e1, e2, Ω.cov_const_add, Ω.cov_comm, Ω.cov_const_add, Ω.cov_comm]
  rw [hc] at h
  rw [hc2]
  exact ⟨by linarith, by linarith⟩

/-- **Covariance via correlation**, O&R p. 311: `Cov(X, Y) = Corr(X, Y)·Std(X)·Std(Y)` when
both standard deviations are positive (so the equity premium is `(1+r)βρκ Std Std`). -/
theorem cov_eq_corr_mul_std (X Y : S → ℝ) (hX : 0 < Ω.std X) (hY : 0 < Ω.std Y) :
    Ω.cov X Y = Ω.corr X Y * Ω.std X * Ω.std Y := by
  unfold StateSpace.corr
  field_simp

/-- **The Mankiw–Zeldes calibration, O&R p. 311**: with `(1+r)β = 1`, `κ = 0.4`,
`Std(g) = 0.036`, `Std(rᵐ − r) = 0.167`, matching the premium `0.0618` requires
`ρ = 0.0618/(0.4·0.036·0.167) ≈ 25.7` ("roughly 26"). -/
theorem mankiw_zeldes_rho :
    (25.6 : ℝ) < 0.0618 / (0.4 * 0.036 * 0.167) ∧
      (0.0618 : ℝ) / (0.4 * 0.036 * 0.167) < 25.8 := by
  constructor <;> norm_num

/-! ## The riskless-rate puzzle (p. 313) -/

/-- **The lognormal riskless rate, O&R p. 313**: with CRRA utility the bond Euler equation is
`(1+r)E[βg^{−ρ}] = 1`, `g = C_{t+1}/C_t > 0`. If `log g` satisfies the lognormal
moment-generating identity at `k = −ρ`,
`E[exp(−ρ log g)] = exp(−ρE log g + (ρ²/2)Var(log g))` (an explicit hypothesis; footnote 41),
then exactly `log(1+r) = ρE log g − (ρ²/2)Var(log g) − log β`. -/
theorem log_riskless_rate_lognormal (g : S → ℝ) {β ρ r : ℝ} (hβ : 0 < β)
    (hg : ∀ s, 0 < g s)
    (heuler : (1 + r) * Ω.expect (fun s => β * g s ^ (-ρ)) = 1)
    (hmgf : Ω.expect (fun s => Real.exp (-ρ * Real.log (g s))) =
      Real.exp (-ρ * Ω.expect (fun s => Real.log (g s)) +
        ρ ^ 2 / 2 * Ω.var (fun s => Real.log (g s)))) :
    Real.log (1 + r) = ρ * Ω.expect (fun s => Real.log (g s)) -
      ρ ^ 2 / 2 * Ω.var (fun s => Real.log (g s)) - Real.log β := by
  have hpow : (fun s => β * g s ^ (-ρ)) = fun s => β * Real.exp (-ρ * Real.log (g s)) := by
    funext s
    rw [Real.rpow_def_of_pos (hg s), mul_comm (Real.log (g s))]
  rw [hpow, Ω.expect_smul, hmgf] at heuler
  have h1 : 1 + r = (β * Real.exp (-ρ * Ω.expect (fun s => Real.log (g s)) +
      ρ ^ 2 / 2 * Ω.var (fun s => Real.log (g s))))⁻¹ := by
    exact eq_inv_of_mul_eq_one_left heuler
  rw [h1, Real.log_inv, Real.log_mul hβ.ne' (Real.exp_pos _).ne', Real.log_exp]
  ring

/-- **The 3.34 percent figure, O&R p. 313**: with `E log g = 0.018`, `Var(log g) = 0.0013`,
`ρ = 2`, `β = 1`, the formula gives `log(1+r) = 0.0334`. -/
theorem riskless_rate_mehra_prescott :
    (2 : ℝ) * 0.018 - (2 : ℝ) ^ 2 / 2 * 0.0013 - Real.log 1 = 0.0334 := by
  rw [Real.log_one]; norm_num

/-! ## Lucas's welfare cost of consumption variability (pp. 329–331) -/

/-- Lucas's consumption path, O&R p. 330: `C_{t+n}(ε) = (1+g)ⁿ C̄ exp(ε − V/2)`, where `ε` is
the (i.i.d.) shock with variance `V`. -/
noncomputable def lucasConsumption (g Cbar V : ℝ) (n : ℕ) (e : ℝ) : ℝ :=
  (1 + g) ^ n * Cbar * Real.exp (e - V / 2)

/-- **Expected utility per period, O&R p. 330**: if the shock satisfies the lognormal
moment-generating identity `E[exp((1−ρ)ε)] = exp((1−ρ)²V/2)` (hypothesis), then
`E[C_{t+n}^{1−ρ}] = ((1+g)ⁿC̄)^{1−ρ} exp[−½(1−ρ)ρV]`. -/
theorem expect_lucas_rpow (ε : S → ℝ) {g Cbar V ρ : ℝ} (hg : -1 < g) (hC : 0 < Cbar)
    (hmgf : Ω.expect (fun s => Real.exp ((1 - ρ) * ε s)) = Real.exp ((1 - ρ) ^ 2 * V / 2))
    (n : ℕ) :
    Ω.expect (fun s => lucasConsumption g Cbar V n (ε s) ^ (1 - ρ)) =
      ((1 + g) ^ n * Cbar) ^ (1 - ρ) * Real.exp (-(1 / 2) * (1 - ρ) * ρ * V) := by
  have hpos : 0 ≤ (1 + g) ^ n * Cbar := by
    have : 0 < 1 + g := by linarith
    positivity
  have e : (fun s => lucasConsumption g Cbar V n (ε s) ^ (1 - ρ)) =
      fun s => (((1 + g) ^ n * Cbar) ^ (1 - ρ) * Real.exp (-((1 - ρ) * V / 2))) *
        Real.exp ((1 - ρ) * ε s) := by
    funext s
    unfold lucasConsumption
    rw [Real.mul_rpow hpos (Real.exp_pos _).le, ← Real.exp_mul, mul_assoc, ← Real.exp_add]
    congr 2
    ring
  rw [e, Ω.expect_smul, hmgf, mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- **Expected consumption, O&R p. 330**: with `E[exp ε] = exp(V/2)` (lognormal identity at
`k = 1`, hypothesis), `E[C_{t+n}] = (1+g)ⁿC̄`, the certainty path `C̄_s = E_t C_s`. -/
theorem expect_lucas_consumption (ε : S → ℝ) {g Cbar V : ℝ}
    (hmgf1 : Ω.expect (fun s => Real.exp (ε s)) = Real.exp (V / 2)) (n : ℕ) :
    Ω.expect (fun s => lucasConsumption g Cbar V n (ε s)) = (1 + g) ^ n * Cbar := by
  have e : (fun s => lucasConsumption g Cbar V n (ε s)) =
      fun s => ((1 + g) ^ n * Cbar * Real.exp (-(V / 2))) * Real.exp (ε s) := by
    funext s
    unfold lucasConsumption
    rw [mul_assoc ((1 + g) ^ n * Cbar), ← Real.exp_add]
    congr 2
    ring
  rw [e, Ω.expect_smul, hmgf1, mul_assoc, ← Real.exp_add]
  simp

/-- **Lifetime utility under uncertainty, O&R p. 330**: with `β > 0`, `g > −1`, `ρ ≠ 1` and
`β(1+g)^{1−ρ} < 1`, `U_t = Σ βⁿ E[C_{t+n}^{1−ρ}]/(1−ρ)` converges to
`C̄^{1−ρ}/(1−ρ) · 1/(1 − β(1+g)^{1−ρ}) · exp[−½(1−ρ)ρV]`. -/
theorem lucas_lifetime_utility (ε : S → ℝ) {β g Cbar V ρ : ℝ} (hβ : 0 < β) (hg : -1 < g)
    (hC : 0 < Cbar) (hconv : β * (1 + g) ^ (1 - ρ) < 1)
    (hmgf : Ω.expect (fun s => Real.exp ((1 - ρ) * ε s)) = Real.exp ((1 - ρ) ^ 2 * V / 2)) :
    HasSum (fun n : ℕ => β ^ n *
        Ω.expect (fun s => lucasConsumption g Cbar V n (ε s) ^ (1 - ρ)) / (1 - ρ))
      (Cbar ^ (1 - ρ) / (1 - ρ) * (1 / (1 - β * (1 + g) ^ (1 - ρ))) *
        Real.exp (-(1 / 2) * (1 - ρ) * ρ * V)) := by
  have h1g : 0 < 1 + g := by linarith
  have hq0 : 0 ≤ β * (1 + g) ^ (1 - ρ) := by positivity
  have hgeo := (hasSum_geometric_of_lt_one hq0 hconv).mul_left
    (Cbar ^ (1 - ρ) / (1 - ρ) * Real.exp (-(1 / 2) * (1 - ρ) * ρ * V))
  convert hgeo using 1
  · funext n
    rw [expect_lucas_rpow Ω ε hg hC hmgf n, Real.mul_rpow (by positivity) hC.le,
      ← Real.rpow_pow_comm h1g.le, mul_pow]
    ring
  · rw [one_div]; ring

/-- **Lifetime utility on the certainty path, O&R p. 330**: `Ū_t = Σ βⁿ((1+g)ⁿC̄)^{1−ρ}/(1−ρ)
= C̄^{1−ρ}/(1−ρ) · 1/(1 − β(1+g)^{1−ρ})`. -/
theorem lucas_certain_utility {β g Cbar ρ : ℝ} (hβ : 0 < β) (hg : -1 < g) (hC : 0 < Cbar)
    (hconv : β * (1 + g) ^ (1 - ρ) < 1) :
    HasSum (fun n : ℕ => β ^ n * ((1 + g) ^ n * Cbar) ^ (1 - ρ) / (1 - ρ))
      (Cbar ^ (1 - ρ) / (1 - ρ) * (1 / (1 - β * (1 + g) ^ (1 - ρ)))) := by
  have h1g : 0 < 1 + g := by linarith
  have hq0 : 0 ≤ β * (1 + g) ^ (1 - ρ) := by positivity
  have hgeo := (hasSum_geometric_of_lt_one hq0 hconv).mul_left (Cbar ^ (1 - ρ) / (1 - ρ))
  convert hgeo using 1
  · funext n
    rw [Real.mul_rpow (by positivity) hC.le, ← Real.rpow_pow_comm h1g.le, mul_pow]
    ring
  · rw [one_div]

/-- **The book's welfare cost simplifies exactly, O&R (75), p. 330**: for `ρ ≠ 1`,
`{exp[½(1−ρ)ρV]}^{1/(1−ρ)} − 1 = exp(ρV/2) − 1`. (The book reports only the unsimplified
formula and the first-order approximation `τ ≈ ρV/2`.) -/
theorem lucas_tau_simplifies {ρ V : ℝ} (hρ : ρ ≠ 1) :
    Real.exp (1 / 2 * (1 - ρ) * ρ * V) ^ (1 / (1 - ρ)) - 1 = Real.exp (ρ * V / 2) - 1 := by
  have h : 1 - ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm hρ)
  rw [← Real.exp_mul]
  congr 2
  field_simp

/-- **The equivalent variation, O&R p. 330**: for `C̄ > 0` and `ρ ≠ 1`, `τ > −1` solves
`[(1+τ)C̄]^{1−ρ}/(1−ρ) · exp[−½(1−ρ)ρV] = C̄^{1−ρ}/(1−ρ)` if and only if
`τ = exp(ρV/2) − 1`. -/
theorem lucas_tau_iff {ρ V Cbar τ : ℝ} (hρ : ρ ≠ 1) (hC : 0 < Cbar) (hτ : -1 < τ) :
    ((1 + τ) * Cbar) ^ (1 - ρ) / (1 - ρ) * Real.exp (-(1 / 2) * (1 - ρ) * ρ * V) =
        Cbar ^ (1 - ρ) / (1 - ρ) ↔ τ = Real.exp (ρ * V / 2) - 1 := by
  have h : 1 - ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm hρ)
  have h1 : 0 < 1 + τ := by linarith
  have hCp : 0 < Cbar ^ (1 - ρ) := Real.rpow_pos_of_pos hC _
  have hcne : Cbar ^ (1 - ρ) / (1 - ρ) ≠ 0 := div_ne_zero hCp.ne' h
  have hE : Real.exp (ρ * V / 2 * (1 - ρ)) * Real.exp (-(1 / 2) * (1 - ρ) * ρ * V) = 1 := by
    rw [← Real.exp_add, show ρ * V / 2 * (1 - ρ) + -(1 / 2) * (1 - ρ) * ρ * V = 0 by ring,
      Real.exp_zero]
  rw [Real.mul_rpow h1.le hC.le]
  have step1 : ((1 + τ) ^ (1 - ρ) * Cbar ^ (1 - ρ) / (1 - ρ) *
      Real.exp (-(1 / 2) * (1 - ρ) * ρ * V) = Cbar ^ (1 - ρ) / (1 - ρ)) ↔
      (1 + τ) ^ (1 - ρ) * Real.exp (-(1 / 2) * (1 - ρ) * ρ * V) = 1 := by
    constructor
    · intro heq
      refine mul_left_cancel₀ hcne ?_
      linear_combination heq
    · intro heq
      calc (1 + τ) ^ (1 - ρ) * Cbar ^ (1 - ρ) / (1 - ρ) * Real.exp (-(1 / 2) * (1 - ρ) * ρ * V)
          = Cbar ^ (1 - ρ) / (1 - ρ) *
              ((1 + τ) ^ (1 - ρ) * Real.exp (-(1 / 2) * (1 - ρ) * ρ * V)) := by ring
        _ = Cbar ^ (1 - ρ) / (1 - ρ) := by rw [heq, mul_one]
  have step2 : (1 + τ) ^ (1 - ρ) * Real.exp (-(1 / 2) * (1 - ρ) * ρ * V) = 1 ↔
      (1 + τ) ^ (1 - ρ) = Real.exp (ρ * V / 2) ^ (1 - ρ) := by
    rw [← Real.exp_mul]
    constructor
    · intro heq
      calc (1 + τ) ^ (1 - ρ)
          = (1 + τ) ^ (1 - ρ) * (Real.exp (ρ * V / 2 * (1 - ρ)) *
              Real.exp (-(1 / 2) * (1 - ρ) * ρ * V)) := by rw [hE, mul_one]
        _ = Real.exp (ρ * V / 2 * (1 - ρ)) *
              ((1 + τ) ^ (1 - ρ) * Real.exp (-(1 / 2) * (1 - ρ) * ρ * V)) := by ring
        _ = Real.exp (ρ * V / 2 * (1 - ρ)) := by rw [heq, mul_one]
    · intro heq
      rw [heq, hE]
  rw [step1, step2]
  constructor
  · intro heq
    have := Real.rpow_left_injOn h (show (0 : ℝ) ≤ 1 + τ from h1.le)
      (show (0 : ℝ) ≤ Real.exp (ρ * V / 2) from (Real.exp_pos _).le) heq
    linarith
  · intro heq
    rw [show 1 + τ = Real.exp (ρ * V / 2) by linarith]

/-- **The first-order approximation (75) is a lower bound**, O&R p. 330: the exact cost
`τ = exp(ρV/2) − 1` satisfies `ρV/2 ≤ τ`, and `τ ≤ (ρV/2)/(1 − ρV/2)` when `0 ≤ ρV/2 < 1`. -/
theorem lucas_tau_bounds {ρ V : ℝ} (h0 : 0 ≤ ρ * V / 2) (h1 : ρ * V / 2 < 1) :
    ρ * V / 2 ≤ Real.exp (ρ * V / 2) - 1 ∧
      Real.exp (ρ * V / 2) - 1 ≤ (ρ * V / 2) / (1 - ρ * V / 2) := by
  constructor
  · linarith [Real.add_one_le_exp (ρ * V / 2)]
  · have h := Real.exp_bound_div_one_sub_of_interval h0 h1
    have hpos : 0 < 1 - ρ * V / 2 := by linarith
    have e : ρ * V / 2 / (1 - ρ * V / 2) = 1 / (1 - ρ * V / 2) - 1 := by
      rw [div_sub_one hpos.ne', sub_sub_cancel]
    rw [e]; linarith

/-- **Lucas's number, O&R p. 330**: with `Var(ε) = 0.000708` and `ρ = 10`, the exact cost
`τ = exp(ρV/2) − 1` lies between 0.35 and 0.36 percent ("about a third of a percent"). -/
theorem lucas_tau_numeric :
    (0.0035 : ℝ) < Real.exp (10 * 0.000708 / 2) - 1 ∧
      Real.exp (10 * 0.000708 / 2) - 1 < (0.0036 : ℝ) := by
  obtain ⟨hl, hu⟩ := lucas_tau_bounds (ρ := 10) (V := 0.000708) (by norm_num) (by norm_num)
  constructor
  · have : (0.0035 : ℝ) < 10 * 0.000708 / 2 := by norm_num
    linarith
  · have : (10 : ℝ) * 0.000708 / 2 / (1 - 10 * 0.000708 / 2) < 0.0036 := by norm_num
    linarith

/-! ## Infinite-horizon pricing (§5.4.3, pp. 315–317), perfect-foresight version -/

/-- **Truncated forward iteration of (57), O&R p. 316** (deterministic economy). If the equity
Euler equation `u′(C_s)V_s = βu′(C_{s+1})(Y_{s+1} + V_{s+1})` holds on every date, with
marginal utilities `m s = u′(C_s) ≠ 0`, then for every horizon `T`,
`V_t = Σ_{k<T} β^{k+1}(m_{t+k+1}/m_t)Y_{t+k+1} + β^T(m_{t+T}/m_t)V_{t+T}`. -/
theorem price_truncated (m V Y : ℕ → ℝ) {β : ℝ} (hm : ∀ s, m s ≠ 0)
    (heuler : ∀ s, m s * V s = β * m (s + 1) * (Y (s + 1) + V (s + 1))) (t T : ℕ) :
    V t = ∑ k ∈ range T, β ^ (k + 1) * (m (t + k + 1) / m t) * Y (t + k + 1) +
      β ^ T * (m (t + T) / m t) * V (t + T) := by
  induction T with
  | zero => simp [hm t]
  | succ T ih =>
    rw [ih, Finset.sum_range_succ]
    have h := heuler (t + T)
    have hV : V (t + T) = β * m (t + T + 1) * (Y (t + T + 1) + V (t + T + 1)) / m (t + T) := by
      rw [← h]; field_simp [hm (t + T)]
    rw [hV, show t + (T + 1) = t + T + 1 by ring]
    field_simp [hm t, hm (t + T)]
    ring

/-- **O&R (5.59), p. 316** (deterministic economy): with the Euler equation (57) on every
date, `β ≥ 0`, positive marginal utilities, nonnegative dividends, and the no-bubble condition
`β^T(m_{t+T}/m_t)V_{t+T} → 0`, the price is the present value
`V_t = Σ_{k≥0} β^{k+1}(m_{t+k+1}/m_t)Y_{t+k+1}`. -/
theorem price_eq_present_value (m V Y : ℕ → ℝ) {β : ℝ} (hβ : 0 ≤ β) (hm : ∀ s, 0 < m s)
    (hY : ∀ s, 0 ≤ Y s)
    (heuler : ∀ s, m s * V s = β * m (s + 1) * (Y (s + 1) + V (s + 1))) (t : ℕ)
    (hbubble : Tendsto (fun T => β ^ T * (m (t + T) / m t) * V (t + T)) atTop (𝓝 0)) :
    HasSum (fun k => β ^ (k + 1) * (m (t + k + 1) / m t) * Y (t + k + 1)) (V t) := by
  have hnn : ∀ k, 0 ≤ β ^ (k + 1) * (m (t + k + 1) / m t) * Y (t + k + 1) := by
    intro k
    have := hm t
    have := hm (t + k + 1)
    have := hY (t + k + 1)
    positivity
  rw [hasSum_iff_tendsto_nat_of_nonneg hnn]
  have hpart : (fun T => ∑ k ∈ range T, β ^ (k + 1) * (m (t + k + 1) / m t) * Y (t + k + 1)) =
      fun T => V t - β ^ T * (m (t + T) / m t) * V (t + T) := by
    funext T
    have := price_truncated m V Y (fun s => (hm s).ne') heuler t T
    linarith
  rw [hpart]
  simpa using (tendsto_const_nhds (x := V t)).sub hbubble

/-- **O&R (5.61), p. 317** (deterministic economy): with CRRA marginal utility
`u′(C) = C^{−ρ}` and each country consuming a constant share `μ > 0` of world output `Y^W > 0`,
the discount factor in (59) is `β^{s−t}(Y^W_s/Y^W_t)^{−ρ}`, independent of `μ`. -/
theorem crra_share_discount (YW : ℕ → ℝ) {μ ρ : ℝ} (hμ : 0 < μ) (hY : ∀ s, 0 < YW s)
    (t s : ℕ) :
    (μ * YW s) ^ (-ρ) / (μ * YW t) ^ (-ρ) = (YW s / YW t) ^ (-ρ) := by
  rw [Real.mul_rpow hμ.le (hY s).le, Real.mul_rpow hμ.le (hY t).le,
    Real.div_rpow (hY s).le (hY t).le]
  have : 0 < μ ^ (-ρ) := Real.rpow_pos_of_pos hμ _
  field_simp

/-- **O&R (5.61), p. 317** (deterministic economy): combining `price_eq_present_value` and
`crra_share_discount`, `V_t = Σ_{s>t} β^{s−t}(Y^W_s/Y^W_t)^{−ρ}Yᵐ_s` under the Euler equation
for `C = μY^W` and the no-bubble condition. -/
theorem price_crra_world_output (YW V Y : ℕ → ℝ) {β μ ρ : ℝ} (hβ : 0 ≤ β) (hμ : 0 < μ)
    (hYW : ∀ s, 0 < YW s) (hY : ∀ s, 0 ≤ Y s)
    (heuler : ∀ s, (μ * YW s) ^ (-ρ) * V s =
      β * (μ * YW (s + 1)) ^ (-ρ) * (Y (s + 1) + V (s + 1))) (t : ℕ)
    (hbubble : Tendsto (fun T => β ^ T * ((μ * YW (t + T)) ^ (-ρ) / (μ * YW t) ^ (-ρ)) *
      V (t + T)) atTop (𝓝 0)) :
    HasSum (fun k => β ^ (k + 1) * (YW (t + k + 1) / YW t) ^ (-ρ) * Y (t + k + 1)) (V t) := by
  have h := price_eq_present_value (fun s => (μ * YW s) ^ (-ρ)) V Y hβ
    (fun s => Real.rpow_pos_of_pos (mul_pos hμ (hYW s)) _) hY heuler t hbubble
  simpa only [crra_share_discount YW hμ hYW] using h

/-- **The decomposition in (59), O&R pp. 316–317**: date by date, the value of the date-`k`
payoff `E_k[M_k Y_k]` equals `R_k E_k[Y_k] + Cov_k(M_k, Y_k)` with the discount factor
`R_k = E_k[M_k]` of (60); summing over a finite horizon gives the truncated form of (59). -/
theorem truncated_price_decomposition (Ωk : ℕ → StateSpace S) (M Y : ℕ → S → ℝ) (T : ℕ) :
    ∑ k ∈ range T, (Ωk k).expect (fun s => M k s * Y k s) =
      ∑ k ∈ range T, (Ωk k).expect (M k) * (Ωk k).expect (Y k) +
        ∑ k ∈ range T, (Ωk k).cov (M k) (Y k) := by
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => (Ωk k).expect_mul_eq (M k) (Y k)

end ObstfeldRogoff.InternationalFinancialMarkets.AssetPricing
