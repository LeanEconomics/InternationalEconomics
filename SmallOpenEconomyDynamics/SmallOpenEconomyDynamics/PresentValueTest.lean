/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import SmallOpenEconomyDynamics.PresentValue
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Real
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
import Mathlib.Probability.Process.Filtration
import Mathlib.Analysis.Matrix.Normed
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# The present-value test of the current account

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §2.3.5,
pp. 90–93 (equations (2.42)–(2.45), footnotes 28–29), with Exercises 5 and 6, p. 126.

Net output is `Z = Y − I − G`. Equation (2.42) says `CA_t = Z_t − E_t Z̃_t`, with
`E_t Z̃_t = (r/(1+r)) Σ_{s≥t} (1+r)^{-(s-t)} E_t Z_s`; Campbell's form (2.43) is
`CA_t = −Σ_{s>t} (1+r)^{-(s-t)} E_t ΔZ_s`.

Contents.
* Deterministic summation by parts (Exercise 6): the finite-horizon identity
  `campbell_finite_horizon`, the infinite version `campbell_deterministic` (under absolute
  summability of the present value), and `campbell_of_tail`, which needs only the book's tail
  condition `(1+r)^{-T} Z_T → 0` and summable changes.
* Stochastic version, with Mathlib's conditional expectation `μ[·|ℱ t]` for `E_t`:
  `campbell_eq_43` derives (2.43) from (2.42). The forecasts are summed pathwise, as in the book,
  so no interchange of `E_t` and `Σ` is needed there. Where an interchange is needed (Exercise 5,
  footnote 29), it is proved from Mathlib's `condExp_tsum` under the standing assumption
  `Σ_s (1+r)^{-s} E|Z_{t+s}| < ∞` (the stochastic form of the growth condition on p. 66).
* Exercise 5 (Campbell's residual test): `condExp_residual_eq_zero` (forward direction),
  `campbell_of_residual` and `campbell_iff_residual` (converse, corrected).
  **Correction.** The book says (2.43) holds *if and only if*
  `CA_{t+1} − ΔZ_{t+1} − (1+r) CA_t` is uncorrelated with date-`t` information. The "if"
  direction is false without a no-bubble condition `lim_n (1+r)^{-n} E_t CA_{t+n} = 0`. The
  counterexample `residual_orthogonality_insufficient` has `Z = 0` and `CA_t = (1+r)^t`. The
  corrected iff is `campbell_iff_residual`.
* Footnote 29: `condExp_coarser_info` (tower property) and `campbell_coarser_information`:
  (2.43) survives conditioning on any coarser information set for which `CA_t` is measurable.
* The VAR forecast (2.44)–(2.45): the matrix geometric series of footnote 28
  (`tsum_pow_succ_eq_mul_inv`, with the sufficient row-sum condition
  `summable_disc_smul_pow`), iterated forecasts `E_t x_{t+k} = Ψ^k x_t` (`condExp_var_pow`),
  the predicted current account (2.45) (`var_predicted_current_account`), and the tested
  restriction `CA_t = ĈA_t` (`var_null_restriction`).
-/

namespace ObstfeldRogoff.SmallOpenEconomyDynamics.PresentValueTest

open MeasureTheory Filter Topology Finset
open scoped Matrix
open ObstfeldRogoff.SmallOpenEconomyDynamics.PresentValue

/-! ## Deterministic summation by parts -/

/-- `1 − 1/(1 + r) = r/(1 + r)`, the annuity factor of O&R (2.42), p. 90. -/
theorem one_sub_disc_eq {r : ℝ} (hr : 0 < 1 + r) : 1 - disc r = r / (1 + r) := by
  unfold disc
  field_simp
  ring

/-- Finite-horizon summation by parts behind O&R (2.43), p. 90 (Exercise 6, p. 126):
`Σ_{s<T} (1+r)^{-(s+1)} ΔZ_{s+1} = (1+r)^{-T} Z_T − Z_0 + (1 − 1/(1+r)) Σ_{s<T} (1+r)^{-s} Z_s`. -/
theorem sum_disc_diff_eq (r : ℝ) (Z : ℕ → ℝ) (T : ℕ) :
    ∑ s ∈ range T, disc r ^ (s + 1) * (Z (s + 1) - Z s) =
      disc r ^ T * Z T - Z 0 + (1 - disc r) * ∑ s ∈ range T, disc r ^ s * Z s := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [sum_range_succ, ih, sum_range_succ]
    ring

/-- Finite-horizon Campbell identity, O&R (2.43), p. 90: net output less its truncated
annuity value equals minus the discounted sum of future changes plus the terminal term
`(1+r)^{-T} Z_T`. -/
theorem campbell_finite_horizon (r : ℝ) (Z : ℕ → ℝ) (T : ℕ) :
    Z 0 - (1 - disc r) * ∑ s ∈ range T, disc r ^ s * Z s =
      -∑ s ∈ range T, disc r ^ (s + 1) * (Z (s + 1) - Z s) + disc r ^ T * Z T := by
  rw [sum_disc_diff_eq]
  ring

/-- The tail condition `(1+r)^{-T} Z_T → 0` needed for O&R (2.43), p. 90, holds whenever the
present value of `Z` converges absolutely. -/
theorem tail_tendsto_zero {r : ℝ} {Z : ℕ → ℝ} (hZ : Summable fun s => disc r ^ s * Z s) :
    Tendsto (fun T => disc r ^ T * Z T) atTop (𝓝 0) :=
  hZ.tendsto_atTop_zero

/-- If the present value of `Z` converges, so does the discounted sum of its changes, the
right-hand side of O&R (2.43), p. 90. -/
theorem summable_disc_diff {r : ℝ} {Z : ℕ → ℝ} (hZ : Summable fun s => disc r ^ s * Z s) :
    Summable fun s => disc r ^ (s + 1) * (Z (s + 1) - Z s) := by
  have h1 : Summable fun s => disc r ^ (s + 1) * Z (s + 1) :=
    (summable_nat_add_iff 1).2 hZ
  have h2 : Summable fun s => disc r * (disc r ^ s * Z s) := hZ.mul_left _
  refine (h1.sub h2).congr fun s => ?_
  ring

/-- Deterministic Campbell identity, O&R (2.43), p. 90 (Exercise 6, p. 126): if the present
value of `Z` converges and `r > 0`, then `Z_0 − Z̃ = −Σ_{s≥0} (1+r)^{-(s+1)} (Z_{s+1} − Z_s)`,
where `Z̃` is the permanent value (2.42). -/
theorem campbell_deterministic {r : ℝ} (hr : 0 < r) {Z : ℕ → ℝ}
    (hZ : Summable fun s => disc r ^ s * Z s) :
    Z 0 - permanent r Z = -∑' s, disc r ^ (s + 1) * (Z (s + 1) - Z s) := by
  have hr1 : 0 < 1 + r := by linarith
  have h1 : Summable fun s => disc r ^ (s + 1) * Z (s + 1) :=
    (summable_nat_add_iff 1).2 hZ
  have h2 : Summable fun s => disc r * (disc r ^ s * Z s) := hZ.mul_left _
  have e1 : ∑' s, disc r ^ (s + 1) * Z (s + 1) = pv r Z - Z 0 := by
    unfold pv
    rw [hZ.tsum_eq_zero_add]
    simp
  have e2 : ∑' s, disc r * (disc r ^ s * Z s) = disc r * pv r Z := by
    unfold pv
    exact tsum_mul_left
  have e3 : ∑' s, disc r ^ (s + 1) * (Z (s + 1) - Z s) =
      ∑' s, disc r ^ (s + 1) * Z (s + 1) - ∑' s, disc r * (disc r ^ s * Z s) := by
    rw [← h1.tsum_sub h2]
    exact tsum_congr fun s => by ring
  rw [e3, e1, e2]
  unfold permanent
  rw [← one_sub_disc_eq hr1]
  ring

/-- O&R (2.43), p. 90, derived under the book's tail condition only: if the discounted changes
are summable and `(1+r)^{-T} Z_T → 0`, the truncated permanent values converge and
`Z_0 − lim_T (r/(1+r)) Σ_{s<T} (1+r)^{-s} Z_s = −Σ (1+r)^{-(s+1)} ΔZ_{s+1}`. (The limit may be
only conditionally convergent, so it is stated with partial sums.) -/
theorem campbell_of_tail {r : ℝ} (hr : 0 < 1 + r) {Z : ℕ → ℝ}
    (hD : Summable fun s => disc r ^ (s + 1) * (Z (s + 1) - Z s))
    (htail : Tendsto (fun T => disc r ^ T * Z T) atTop (𝓝 0)) :
    Tendsto (fun T => Z 0 - r / (1 + r) * ∑ s ∈ range T, disc r ^ s * Z s) atTop
      (𝓝 (-∑' s, disc r ^ (s + 1) * (Z (s + 1) - Z s))) := by
  have h := (hD.hasSum.tendsto_sum_nat.neg).add htail
  rw [add_zero] at h
  refine h.congr fun T => ?_
  rw [← one_sub_disc_eq hr, campbell_finite_horizon]

/-! ## The stochastic version: conditional expectations -/

namespace Stochastic

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- Conditional expected permanent net output `E_t Z̃_t = (r/(1+r)) Σ_{s≥0} (1+r)^{-s} E_t Z_{t+s}`,
O&R (2.42), p. 90, taken as the sum of the conditional forecasts (as the book writes it). -/
noncomputable def forecastPermanent (μ : Measure Ω) (ℱ : Filtration ℕ m0) (r : ℝ)
    (Z : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => r / (1 + r) * ∑' s, disc r ^ s * μ[Z (t + s) | ℱ t] ω

/-- The right-hand side of O&R (2.43), p. 90, without its minus sign:
`Σ_{s≥0} (1+r)^{-(s+1)} E_t ΔZ_{t+s+1}`. -/
noncomputable def campbellPV (μ : Measure Ω) (ℱ : Filtration ℕ m0) (r : ℝ)
    (Z : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => ∑' s, disc r ^ (s + 1) * μ[Z (t + s + 1) - Z (t + s) | ℱ t] ω

/-- The Campbell residual of Exercise 5, p. 126:
`e_{t+1} = CA_{t+1} − ΔZ_{t+1} − (1+r) CA_t`. -/
noncomputable def campbellResidual (r : ℝ) (CA Z : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  CA (t + 1) - (Z (t + 1) - Z t) - (1 + r) • CA t

/-- Technical lemma for O&R (2.43), p. 90: summable `L¹` norms give a finite sum of
lower integrals (the hypothesis of Mathlib's `condExp_tsum`). -/
theorem tsum_lintegral_ne_top {f : ℕ → Ω → ℝ} (hf : ∀ s, Integrable (f s) μ)
    (hs : Summable fun s => ∫ ω, |f s ω| ∂μ) : ∑' s, ∫⁻ ω, ‖f s ω‖ₑ ∂μ ≠ ⊤ := by
  have h (s : ℕ) : ∫⁻ ω, ‖f s ω‖ₑ ∂μ = ‖∫ ω, |f s ω| ∂μ‖ₑ := by
    rw [← ofReal_integral_norm_eq_lintegral_enorm (hf s), Real.enorm_eq_ofReal_abs,
      abs_of_nonneg (integral_nonneg fun ω => abs_nonneg _)]
    rfl
  rw [funext h]
  exact tsum_enorm_ne_top_iff_summable_norm.2 hs.abs

/-- Technical lemma for O&R (2.43), p. 90: summable `L¹` norms give almost-sure absolute
summability of the random series. -/
theorem ae_summable_of_integral {f : ℕ → Ω → ℝ} (hf : ∀ s, Integrable (f s) μ)
    (hs : Summable fun s => ∫ ω, |f s ω| ∂μ) : ∀ᵐ ω ∂μ, Summable fun s => f s ω := by
  have h : ∑' s, eLpNorm (f s) 1 μ ≠ ⊤ := by
    rw [show (fun s => eLpNorm (f s) 1 μ) = fun s => ∫⁻ ω, ‖f s ω‖ₑ ∂μ from
      funext fun s => eLpNorm_one_eq_lintegral_enorm (hf s).1]
    exact tsum_lintegral_ne_top hf hs
  filter_upwards [summable_norm_of_tsum_eLpNorm_ne_top le_rfl h] with ω hω
  exact hω.of_norm

/-- Interchange of conditional expectation and an infinite sum, needed to take `E_t` of the
present value in O&R (2.43), p. 90, and footnote 29, p. 92: valid when the `L¹` norms are
summable. -/
theorem condExp_tsum_of_integral (m : MeasurableSpace Ω) {f : ℕ → Ω → ℝ}
    (hf : ∀ s, Integrable (f s) μ) (hs : Summable fun s => ∫ ω, |f s ω| ∂μ) :
    μ[fun ω => ∑' s, f s ω | m] =ᵐ[μ] fun ω => ∑' s, μ[f s | m] ω :=
  condExp_tsum (fun s => (hf s).1) (tsum_lintegral_ne_top hf hs)

/-- The `L¹` norm of a discounted conditional forecast is at most the discounted `L¹` norm of the
variable (conditional Jensen), O&R (2.42), p. 90. -/
theorem integral_abs_mul_condExp_le (m : MeasurableSpace Ω) {c : ℝ} (hc : 0 ≤ c)
    (X : Ω → ℝ) : ∫ ω, |c * μ[X | m] ω| ∂μ ≤ c * ∫ ω, |X ω| ∂μ := by
  simp_rw [abs_mul, abs_of_nonneg hc, integral_const_mul]
  exact mul_le_mul_of_nonneg_left (integral_abs_condExp_le X) hc

/-- Under the standing assumption that net output has a discounted-summable `L¹` norm
(the stochastic form of O&R's growth condition, p. 66), the discounted forecasts of the changes
`ΔZ` have summable `L¹` norms, for any information set `m`. Used for O&R (2.43), p. 90. -/
theorem summable_integral_diff_forecast {r : ℝ} (hr : 0 < 1 + r) {Z : ℕ → Ω → ℝ}
    (hZ : ∀ t, Integrable (Z t) μ)
    (hS : ∀ t, Summable fun s => disc r ^ s * ∫ ω, |Z (t + s) ω| ∂μ) (t : ℕ)
    (m : MeasurableSpace Ω) :
    Summable fun s => ∫ ω, |disc r ^ (s + 1) * μ[Z (t + s + 1) - Z (t + s) | m] ω| ∂μ := by
  have hd := (disc_pos hr).le
  have hB : Summable fun s => disc r ^ (s + 1) * ∫ ω, |Z (t + s + 1) ω| ∂μ +
      disc r * (disc r ^ s * ∫ ω, |Z (t + s) ω| ∂μ) :=
    ((summable_nat_add_iff 1).2 (hS t)).add ((hS t).mul_left _)
  refine Summable.of_nonneg_of_le (fun s => integral_nonneg fun ω => abs_nonneg _)
    (fun s => ?_) hB
  refine (integral_abs_mul_condExp_le m (pow_nonneg hd _) _).trans ?_
  have hsub : ∫ ω, |(Z (t + s + 1) - Z (t + s)) ω| ∂μ ≤
      ∫ ω, |Z (t + s + 1) ω| ∂μ + ∫ ω, |Z (t + s) ω| ∂μ := by
    rw [← integral_add (hZ _).abs (hZ _).abs]
    refine integral_mono ((hZ _).sub (hZ _)).abs ((hZ _).abs.add (hZ _).abs) fun ω => ?_
    exact abs_sub _ _
  calc disc r ^ (s + 1) * ∫ ω, |(Z (t + s + 1) - Z (t + s)) ω| ∂μ
      ≤ disc r ^ (s + 1) * (∫ ω, |Z (t + s + 1) ω| ∂μ + ∫ ω, |Z (t + s) ω| ∂μ) :=
        mul_le_mul_of_nonneg_left hsub (pow_nonneg hd _)
    _ = _ := by ring

/-- The realised discounted changes in net output have summable `L¹` norms under the standing
discounted-`L¹` assumption; this makes the random present value of footnote 29, p. 92,
well defined and integrable. -/
theorem summable_integral_diff {r : ℝ} (hr : 0 < 1 + r) {Z : ℕ → Ω → ℝ}
    (hZ : ∀ t, Integrable (Z t) μ)
    (hS : ∀ t, Summable fun s => disc r ^ s * ∫ ω, |Z (t + s) ω| ∂μ) (t : ℕ) :
    Summable fun s => ∫ ω, |disc r ^ (s + 1) * (Z (t + s + 1) - Z (t + s)) ω| ∂μ := by
  have hd := (disc_pos hr).le
  have hB : Summable fun s => disc r ^ (s + 1) * ∫ ω, |Z (t + s + 1) ω| ∂μ +
      disc r * (disc r ^ s * ∫ ω, |Z (t + s) ω| ∂μ) :=
    ((summable_nat_add_iff 1).2 (hS t)).add ((hS t).mul_left _)
  refine Summable.of_nonneg_of_le (fun s => integral_nonneg fun ω => abs_nonneg _)
    (fun s => ?_) hB
  simp_rw [abs_mul, abs_of_nonneg (pow_nonneg hd _), integral_const_mul]
  have hsub : ∫ ω, |(Z (t + s + 1) - Z (t + s)) ω| ∂μ ≤
      ∫ ω, |Z (t + s + 1) ω| ∂μ + ∫ ω, |Z (t + s) ω| ∂μ := by
    rw [← integral_add (hZ _).abs (hZ _).abs]
    refine integral_mono ((hZ _).sub (hZ _)).abs ((hZ _).abs.add (hZ _).abs) fun ω => ?_
    exact abs_sub _ _
  calc disc r ^ (s + 1) * ∫ ω, |(Z (t + s + 1) - Z (t + s)) ω| ∂μ
      ≤ disc r ^ (s + 1) * (∫ ω, |Z (t + s + 1) ω| ∂μ + ∫ ω, |Z (t + s) ω| ∂μ) :=
        mul_le_mul_of_nonneg_left hsub (pow_nonneg hd _)
    _ = _ := by ring

/-- Under the standing discounted-`L¹` assumption on net output (O&R's growth condition, p. 66),
the conditional forecasts in O&R (2.42), p. 90, are almost surely discount-summable. -/
theorem ae_summable_forecast {r : ℝ} (hr : 0 < 1 + r) {ℱ : Filtration ℕ m0}
    {Z : ℕ → Ω → ℝ} (hS : ∀ t, Summable fun s => disc r ^ s * ∫ ω, |Z (t + s) ω| ∂μ)
    (t : ℕ) : ∀ᵐ ω ∂μ, Summable fun s => disc r ^ s * μ[Z (t + s) | ℱ t] ω :=
  ae_summable_of_integral (f := fun s ω => disc r ^ s * μ[Z (t + s) | ℱ t] ω)
    (fun _ => integrable_condExp.const_mul _)
    (Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => abs_nonneg _)
      (fun _ => integral_abs_mul_condExp_le _ (pow_nonneg (disc_pos hr).le _) _) (hS t))

/-- The forecast of a change is the change in forecasts, `E_t ΔZ_s = E_t Z_s − E_t Z_{s−1}`
(linearity of conditional expectation), simultaneously for all horizons almost surely; used in
Exercise 6, p. 126. -/
theorem ae_condExp_diff {ℱ : Filtration ℕ m0} {Z : ℕ → Ω → ℝ}
    (hZ : ∀ t, Integrable (Z t) μ) (t : ℕ) :
    ∀ᵐ ω ∂μ, ∀ s, μ[Z (t + s + 1) - Z (t + s) | ℱ t] ω =
      μ[Z (t + s + 1) | ℱ t] ω - μ[Z (t + s) | ℱ t] ω :=
  ae_all_iff.2 fun _ => condExp_sub (hZ _) (hZ _) _

/-- **Exercise 6, p. 126: derivation of O&R (2.43), p. 90.** If the current account obeys the
permanent-income form (2.42), `CA_t = Z_t − E_t Z̃_t`, with `Z_t` known at `t` and the forecasts
discount-summable, then `CA_t = −Σ_{s>t} (1+r)^{-(s-t)} E_t ΔZ_s` almost surely. -/
theorem campbell_eq_43 [IsProbabilityMeasure μ] {r : ℝ} (hr : 0 < r) {ℱ : Filtration ℕ m0}
    {Z CA : ℕ → Ω → ℝ} (hZ : ∀ t, Integrable (Z t) μ) {t : ℕ}
    (hZt : StronglyMeasurable[ℱ t] (Z t))
    (hsum : ∀ᵐ ω ∂μ, Summable fun s => disc r ^ s * μ[Z (t + s) | ℱ t] ω)
    (h42 : CA t =ᵐ[μ] fun ω => Z t ω - forecastPermanent μ ℱ r Z t ω) :
    CA t =ᵐ[μ] fun ω => -campbellPV μ ℱ r Z t ω := by
  have hself : μ[Z t | ℱ t] = Z t := condExp_of_stronglyMeasurable (ℱ.le t) hZt (hZ t)
  filter_upwards [h42, hsum, ae_condExp_diff (ℱ := ℱ) hZ t] with ω h1 h2 h3
  rw [h1]
  have key := campbell_deterministic hr h2
  simp only [add_zero, hself] at key
  unfold permanent pv at key
  unfold forecastPermanent campbellPV
  simp only [h3]
  exact key

/-- Linearity of conditional expectation applied to the Campbell residual of Exercise 5, p. 126:
`E[e_{u+1} | m] = E[CA_{u+1} | m] − E[ΔZ_{u+1} | m] − (1+r) E[CA_u | m]`. -/
theorem condExp_residual_ae {r : ℝ} {Z CA : ℕ → Ω → ℝ} (hZ : ∀ t, Integrable (Z t) μ)
    (hCA : ∀ t, Integrable (CA t) μ) (m : MeasurableSpace Ω) (u : ℕ) :
    μ[campbellResidual r CA Z u | m] =ᵐ[μ]
      μ[CA (u + 1) | m] - μ[Z (u + 1) - Z u | m] - (1 + r) • μ[CA u | m] := by
  unfold campbellResidual
  refine (condExp_sub ((hCA _).sub ((hZ _).sub (hZ _))) ((hCA _).smul (1 + r)) _).trans ?_
  exact EventuallyEq.sub (condExp_sub (hCA _) ((hZ _).sub (hZ _)) _) (condExp_smul _ _ _)

/-- If the Campbell residual is unpredictable at every date, O&R Exercise 5, p. 126, then the
date-`t` forecasts `V_n = E_t CA_{t+n}` obey `(1+r) V_n = −E_t ΔZ_{t+n+1} + V_{n+1}` for all `n`,
almost surely (law of iterated expectations). -/
theorem ae_forecast_recursion [IsProbabilityMeasure μ] {r : ℝ} {ℱ : Filtration ℕ m0}
    {Z CA : ℕ → Ω → ℝ} (hZ : ∀ t, Integrable (Z t) μ) (hCA : ∀ t, Integrable (CA t) μ)
    (hres : ∀ t, μ[campbellResidual r CA Z t | ℱ t] =ᵐ[μ] 0) (t : ℕ) :
    ∀ᵐ ω ∂μ, ∀ n, (1 + r) * μ[CA (t + n) | ℱ t] ω =
      -μ[Z (t + n + 1) - Z (t + n) | ℱ t] ω + μ[CA (t + n + 1) | ℱ t] ω := by
  refine ae_all_iff.2 fun n => ?_
  have h0 : μ[campbellResidual r CA Z (t + n) | ℱ t] =ᵐ[μ] 0 := by
    have htow := condExp_condExp_of_le (μ := μ) (f := campbellResidual r CA Z (t + n))
      (ℱ.mono (Nat.le_add_right t n)) (ℱ.le (t + n))
    refine htow.symm.trans ?_
    refine (condExp_congr_ae (hres (t + n))).trans ?_
    rw [condExp_zero]
  filter_upwards [h0, condExp_residual_ae (r := r) hZ hCA (ℱ t) (t + n)] with ω h0 hlin
  rw [h0] at hlin
  simp only [Pi.zero_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at hlin
  linarith

/-- Under the standing discounted-`L¹` assumption, the discounted forecasts of future changes in
O&R (2.43), p. 90, are almost surely summable. -/
theorem ae_summable_diff_forecast {r : ℝ} (hr : 0 < 1 + r) {ℱ : Filtration ℕ m0}
    {Z : ℕ → Ω → ℝ} (hZ : ∀ t, Integrable (Z t) μ)
    (hS : ∀ t, Summable fun s => disc r ^ s * ∫ ω, |Z (t + s) ω| ∂μ) (t : ℕ) :
    ∀ᵐ ω ∂μ, Summable fun s => disc r ^ (s + 1) * μ[Z (t + s + 1) - Z (t + s) | ℱ t] ω :=
  ae_summable_of_integral (f := fun s ω => disc r ^ (s + 1) * μ[Z (t + s + 1) - Z (t + s) | ℱ t] ω)
    (fun _ => integrable_condExp.const_mul _) (summable_integral_diff_forecast hr hZ hS t (ℱ t))

/-- **Exercise 5, p. 126, forward direction.** If O&R (2.43), p. 90, holds at every date, the
Campbell residual `e_{t+1} = CA_{t+1} − ΔZ_{t+1} − (1+r) CA_t` has zero conditional expectation
given date-`t` information, hence is uncorrelated with every date-`t` variable. -/
theorem condExp_residual_eq_zero [IsProbabilityMeasure μ] {r : ℝ} (hr : 0 < 1 + r)
    {ℱ : Filtration ℕ m0} {Z CA : ℕ → Ω → ℝ} (hZ : ∀ t, Integrable (Z t) μ)
    (hS : ∀ t, Summable fun s => disc r ^ s * ∫ ω, |Z (t + s) ω| ∂μ)
    (hCA : ∀ t, Integrable (CA t) μ) (hCAad : ∀ t, StronglyMeasurable[ℱ t] (CA t))
    (h43 : ∀ t, CA t =ᵐ[μ] fun ω => -campbellPV μ ℱ r Z t ω) (t : ℕ) :
    μ[campbellResidual r CA Z t | ℱ t] =ᵐ[μ] 0 := by
  have e : ∀ s, t + 1 + s = t + s + 1 := fun s => Nat.add_right_comm t 1 s
  have hself : μ[CA t | ℱ t] = CA t := condExp_of_stronglyMeasurable (ℱ.le t) (hCAad t) (hCA t)
  -- `E_t CA_{t+1}` by the interchange of `E_t` and the sum, then the tower property
  have hT := condExp_tsum_of_integral (ℱ t)
    (f := fun s ω => disc r ^ (s + 1) * μ[Z (t + 1 + s + 1) - Z (t + 1 + s) | ℱ (t + 1)] ω)
    (fun _ => integrable_condExp.const_mul _) (summable_integral_diff_forecast hr hZ hS _ _)
  have hTow : ∀ᵐ ω ∂μ, ∀ s,
      μ[fun ω => disc r ^ (s + 1) * μ[Z (t + 1 + s + 1) - Z (t + 1 + s) | ℱ (t + 1)] ω | ℱ t] ω
        = disc r ^ (s + 1) * μ[Z (t + (s + 1) + 1) - Z (t + (s + 1)) | ℱ t] ω := by
    refine ae_all_iff.2 fun s => ?_
    have a := condExp_smul (μ := μ) (disc r ^ (s + 1))
      (μ[Z (t + 1 + s + 1) - Z (t + 1 + s) | ℱ (t + 1)]) (ℱ t)
    have b := condExp_condExp_of_le (μ := μ) (f := Z (t + 1 + s + 1) - Z (t + 1 + s))
      (ℱ.mono (Nat.le_succ t)) (ℱ.le (t + 1))
    filter_upwards [a, b] with ω ha hb
    have ha' : μ[fun ω => disc r ^ (s + 1) * μ[Z (t + 1 + s + 1) - Z (t + 1 + s) | ℱ (t + 1)] ω
        | ℱ t] ω = disc r ^ (s + 1) *
          μ[μ[Z (t + 1 + s + 1) - Z (t + 1 + s) | ℱ (t + 1)] | ℱ t] ω := ha
    rw [ha', hb, e s]
    rfl
  have hE1 : ∀ᵐ ω ∂μ, μ[CA (t + 1) | ℱ t] ω =
      -∑' s, disc r ^ (s + 1) * μ[Z (t + (s + 1) + 1) - Z (t + (s + 1)) | ℱ t] ω := by
    have h1 := (condExp_congr_ae (m := ℱ t) (h43 (t + 1))).trans
      (condExp_neg (μ := μ) (campbellPV μ ℱ r Z (t + 1)) (ℱ t))
    filter_upwards [h1, hT, hTow] with ω h1 h2 h3
    rw [h1, Pi.neg_apply]
    unfold campbellPV
    rw [h2, tsum_congr h3]
  filter_upwards [condExp_residual_ae (r := r) hZ hCA (ℱ t) t, hE1, h43 t,
    ae_summable_diff_forecast hr (ℱ := ℱ) hZ hS t] with ω hlin hE1 h43t hsum
  rw [hlin]
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, hself]
  rw [hE1, h43t]
  unfold campbellPV
  rw [hsum.tsum_eq_zero_add]
  have hd := one_add_mul_disc hr
  have hmul : (1 + r) * ∑' s, disc r ^ (s + 1 + 1) *
      μ[Z (t + (s + 1) + 1) - Z (t + (s + 1)) | ℱ t] ω =
        ∑' s, disc r ^ (s + 1) * μ[Z (t + (s + 1) + 1) - Z (t + (s + 1)) | ℱ t] ω := by
    rw [← tsum_mul_left]
    refine tsum_congr fun s => ?_
    rw [pow_succ, ← mul_assoc, ← mul_assoc, mul_comm (1 + r), mul_assoc _ (1 + r), hd, mul_one]
  rw [← hmul]
  simp only [add_zero, zero_add, pow_one]
  linear_combination (μ[Z (t + 1) - Z t | ℱ t] ω) * hd

/-- Exercise 5, p. 126, the key step: once the Campbell residual is unpredictable, O&R (2.43),
p. 90, holds at date `t` exactly when the no-bubble condition
`(1+r)^{-n} E_t CA_{t+n} → 0` holds (almost surely, pathwise in `ω`). -/
theorem ae_campbell_iff_noBubble [IsProbabilityMeasure μ] {r : ℝ} (hr : 0 < 1 + r)
    {ℱ : Filtration ℕ m0} {Z CA : ℕ → Ω → ℝ} (hZ : ∀ t, Integrable (Z t) μ)
    (hS : ∀ t, Summable fun s => disc r ^ s * ∫ ω, |Z (t + s) ω| ∂μ)
    (hCA : ∀ t, Integrable (CA t) μ) (hCAad : ∀ t, StronglyMeasurable[ℱ t] (CA t))
    (hres : ∀ t, μ[campbellResidual r CA Z t | ℱ t] =ᵐ[μ] 0) (t : ℕ) :
    ∀ᵐ ω ∂μ, (CA t ω = -campbellPV μ ℱ r Z t ω ↔
      Tendsto (fun n => disc r ^ n * μ[CA (t + n) | ℱ t] ω) atTop (𝓝 0)) := by
  have hself : μ[CA t | ℱ t] = CA t := condExp_of_stronglyMeasurable (ℱ.le t) (hCAad t) (hCA t)
  filter_upwards [ae_forecast_recursion hZ hCA hres t,
    ae_summable_diff_forecast hr (ℱ := ℱ) hZ hS t] with ω hrec hsum
  set V : ℕ → ℝ := fun n => μ[CA (t + n) | ℱ t] ω with hV
  set D : ℕ → ℝ := fun k => -μ[Z (t + (k - 1) + 1) - Z (t + (k - 1)) | ℱ t] ω with hD
  have h : ∀ s, (1 + r) * V s = D (s + 1) + V (s + 1) := by
    intro s
    simp only [hV, hD, add_tsub_cancel_right]
    exact hrec s
  have hs : Summable fun s => disc r ^ (s + 1) * D (s + 1) := by
    refine hsum.neg.congr fun s => ?_
    simp only [hD, add_tsub_cancel_right]
    ring
  have hV0 : V 0 = CA t ω := by simp only [hV, add_zero, hself]
  have hsumD : ∑' s, disc r ^ (s + 1) * D (s + 1) = -campbellPV μ ℱ r Z t ω := by
    unfold campbellPV
    rw [← tsum_neg]
    refine tsum_congr fun s => ?_
    simp only [hD, add_tsub_cancel_right]
    ring
  rw [← hV0, ← hsumD]
  exact forward_solution_iff hr h hs

/-- **Exercise 5, p. 126, converse direction (corrected).** If the Campbell residual
`CA_{t+1} − ΔZ_{t+1} − (1+r) CA_t` is unpredictable at every date AND the no-bubble condition
`(1+r)^{-n} E_t CA_{t+n} → 0` holds, then O&R (2.43), p. 90, holds at `t`. The book states the
converse without the no-bubble condition; see `residual_orthogonality_insufficient`. -/
theorem campbell_of_residual [IsProbabilityMeasure μ] {r : ℝ} (hr : 0 < 1 + r)
    {ℱ : Filtration ℕ m0} {Z CA : ℕ → Ω → ℝ} (hZ : ∀ t, Integrable (Z t) μ)
    (hS : ∀ t, Summable fun s => disc r ^ s * ∫ ω, |Z (t + s) ω| ∂μ)
    (hCA : ∀ t, Integrable (CA t) μ) (hCAad : ∀ t, StronglyMeasurable[ℱ t] (CA t))
    (hres : ∀ t, μ[campbellResidual r CA Z t | ℱ t] =ᵐ[μ] 0) (t : ℕ)
    (hnb : ∀ᵐ ω ∂μ, Tendsto (fun n => disc r ^ n * μ[CA (t + n) | ℱ t] ω) atTop (𝓝 0)) :
    CA t =ᵐ[μ] fun ω => -campbellPV μ ℱ r Z t ω := by
  filter_upwards [ae_campbell_iff_noBubble hr hZ hS hCA hCAad hres t, hnb] with ω h1 h2
  exact h1.2 h2

/-- **Exercise 5, p. 126 (corrected iff).** Given integrable, adapted `CA` and net output with
discount-summable `L¹` norms, O&R (2.43), p. 90, holds at every date if and only if the Campbell
residual `CA_{t+1} − ΔZ_{t+1} − (1+r) CA_t` is unpredictable from date-`t` information at every
date and the no-bubble condition `lim_n (1+r)^{-n} E_t CA_{t+n} = 0` holds at every date. -/
theorem campbell_iff_residual [IsProbabilityMeasure μ] {r : ℝ} (hr : 0 < 1 + r)
    {ℱ : Filtration ℕ m0} {Z CA : ℕ → Ω → ℝ} (hZ : ∀ t, Integrable (Z t) μ)
    (hS : ∀ t, Summable fun s => disc r ^ s * ∫ ω, |Z (t + s) ω| ∂μ)
    (hCA : ∀ t, Integrable (CA t) μ) (hCAad : ∀ t, StronglyMeasurable[ℱ t] (CA t)) :
    (∀ t, CA t =ᵐ[μ] fun ω => -campbellPV μ ℱ r Z t ω) ↔
      (∀ t, μ[campbellResidual r CA Z t | ℱ t] =ᵐ[μ] 0) ∧
        ∀ t, ∀ᵐ ω ∂μ, Tendsto (fun n => disc r ^ n * μ[CA (t + n) | ℱ t] ω) atTop (𝓝 0) := by
  constructor
  · intro h43
    have hres := condExp_residual_eq_zero hr hZ hS hCA hCAad h43
    refine ⟨hres, fun t => ?_⟩
    filter_upwards [ae_campbell_iff_noBubble hr hZ hS hCA hCAad hres t, h43 t] with ω h1 h2
    exact h1.1 h2
  · rintro ⟨hres, hnb⟩ t
    exact campbell_of_residual hr hZ hS hCA hCAad hres t (hnb t)

/-- **The no-bubble condition cannot be dropped from Exercise 5, p. 126.** With zero net output
and the explosive current account `CA_t = (1+r)^t` (integrable and adapted), the Campbell residual
is identically zero, yet O&R (2.43), p. 90, fails at date 0 (it would force `CA_0 = 0`). -/
theorem residual_orthogonality_insufficient [IsProbabilityMeasure μ] (r : ℝ)
    (ℱ : Filtration ℕ m0) :
    ∃ Z CA : ℕ → Ω → ℝ, (∀ t, Integrable (Z t) μ) ∧ (∀ t, Integrable (CA t) μ) ∧
      (∀ t, StronglyMeasurable[ℱ t] (CA t)) ∧
      (∀ t, μ[campbellResidual r CA Z t | ℱ t] =ᵐ[μ] 0) ∧
      ¬ (CA 0 =ᵐ[μ] fun ω => -campbellPV μ ℱ r Z 0 ω) := by
  refine ⟨fun _ _ => 0, fun t _ => (1 + r) ^ t, fun _ => integrable_const _,
    fun _ => integrable_const _, fun _ => stronglyMeasurable_const, fun t => ?_, ?_⟩
  · have h0 : campbellResidual r (fun t (_ : Ω) => (1 + r) ^ t) (fun _ (_ : Ω) => (0 : ℝ)) t
        = 0 := by
      funext ω
      simp only [campbellResidual, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
        pow_succ]
      ring
    rw [h0, condExp_zero]
  · intro h
    have hc : campbellPV μ ℱ r (fun _ _ => 0) 0 = 0 := by
      funext ω
      simp [campbellPV, condExp_zero]
    obtain ⟨ω, hω⟩ := h.exists
    simp [hc] at hω

/-! ### Footnote 29: coarser information sets -/

/-- **O&R footnote 29, p. 92 (tower property).** If `CA = −E[PV | 𝓘]` for the full information
set `𝓘`, and `CA` is measurable with respect to a coarser `𝓖 ⊆ 𝓘`, then also `CA = −E[PV | 𝓖]`:
the econometrician's smaller information set gives the same prediction. -/
theorem condExp_coarser_info [IsProbabilityMeasure μ] {𝓖 𝓘 : MeasurableSpace Ω}
    (h𝓖 : 𝓖 ≤ 𝓘) (h𝓘 : 𝓘 ≤ m0) {CA PV : Ω → ℝ} (hCA : CA =ᵐ[μ] -μ[PV | 𝓘])
    (hCAm : StronglyMeasurable[𝓖] CA) : CA =ᵐ[μ] -μ[PV | 𝓖] := by
  have hint : Integrable CA μ := integrable_condExp.neg.congr hCA.symm
  have hself : μ[CA | 𝓖] = CA := condExp_of_stronglyMeasurable (h𝓖.trans h𝓘) hCAm hint
  have h := (condExp_congr_ae (m := 𝓖) hCA).trans
    ((condExp_neg (μ[PV | 𝓘]) 𝓖).trans (condExp_condExp_of_le h𝓖 h𝓘).neg)
  rwa [hself] at h

/-- The realised present value of future net-output changes,
`Σ_{s≥0} (1+r)^{-(s+1)} ΔZ_{t+s+1}`, the random variable inside the expectation of O&R
footnote 29, p. 92. -/
noncomputable def pvChanges (r : ℝ) (Z : ℕ → Ω → ℝ) (t : ℕ) : Ω → ℝ :=
  fun ω => ∑' s, disc r ^ (s + 1) * (Z (t + s + 1) - Z (t + s)) ω

/-- The sum of conditional forecasts of future changes equals the conditional expectation of
their realised present value, for any information set `m` (O&R (2.43), p. 90, and footnote 29,
p. 92): the interchange `Σ E[·|m] = E[Σ ·|m]`, proved under the standing `L¹` assumption. -/
theorem forecastSum_ae_eq_condExp {r : ℝ} (hr : 0 < 1 + r) {Z : ℕ → Ω → ℝ}
    (hZ : ∀ t, Integrable (Z t) μ)
    (hS : ∀ t, Summable fun s => disc r ^ s * ∫ ω, |Z (t + s) ω| ∂μ) (t : ℕ)
    (m : MeasurableSpace Ω) :
    (fun ω => ∑' s, disc r ^ (s + 1) * μ[Z (t + s + 1) - Z (t + s) | m] ω) =ᵐ[μ]
      μ[pvChanges r Z t | m] := by
  have hT := condExp_tsum_of_integral m
    (f := fun s ω => disc r ^ (s + 1) * (Z (t + s + 1) - Z (t + s)) ω)
    (fun _ => ((hZ _).sub (hZ _)).const_mul _) (summable_integral_diff hr hZ hS t)
  have hsm : ∀ᵐ ω ∂μ, ∀ s,
      μ[fun ω => disc r ^ (s + 1) * (Z (t + s + 1) - Z (t + s)) ω | m] ω =
        disc r ^ (s + 1) * μ[Z (t + s + 1) - Z (t + s) | m] ω :=
    ae_all_iff.2 fun s => condExp_smul (μ := μ) (disc r ^ (s + 1)) (Z (t + s + 1) - Z (t + s)) m
  filter_upwards [hT, hsm] with ω h1 h2
  unfold pvChanges
  rw [h1, tsum_congr h2]

/-- **O&R footnote 29, p. 92, for the model.** If O&R (2.43), p. 90, holds with respect to the
consumers' information `ℱ t`, then it holds with respect to any coarser information set
`𝓖 ⊆ ℱ t` (for example the econometrician's VAR information `(ΔZ_t, CA_t)`) for which `CA_t` is
measurable: `CA_t = −Σ_{s>t} (1+r)^{-(s-t)} E[ΔZ_s | 𝓖]`. -/
theorem campbell_coarser_information [IsProbabilityMeasure μ] {r : ℝ} (hr : 0 < 1 + r)
    {ℱ : Filtration ℕ m0} {Z CA : ℕ → Ω → ℝ} (hZ : ∀ t, Integrable (Z t) μ)
    (hS : ∀ t, Summable fun s => disc r ^ s * ∫ ω, |Z (t + s) ω| ∂μ) {t : ℕ}
    (h43 : CA t =ᵐ[μ] fun ω => -campbellPV μ ℱ r Z t ω) {𝓖 : MeasurableSpace Ω}
    (h𝓖 : 𝓖 ≤ ℱ t) (hCAm : StronglyMeasurable[𝓖] (CA t)) :
    CA t =ᵐ[μ] fun ω => -∑' s, disc r ^ (s + 1) * μ[Z (t + s + 1) - Z (t + s) | 𝓖] ω := by
  have h1 : CA t =ᵐ[μ] -μ[pvChanges r Z t | ℱ t] := by
    filter_upwards [h43, forecastSum_ae_eq_condExp hr hZ hS t (ℱ t)] with ω h1 h2
    rw [h1, Pi.neg_apply, ← h2]
    rfl
  have h2 := condExp_coarser_info h𝓖 (ℱ.le t) h1 hCAm
  filter_upwards [h2, forecastSum_ae_eq_condExp hr hZ hS t 𝓖] with ω h2 h3
  rw [h2, Pi.neg_apply, ← h3]

/-! ### The VAR forecast (2.44)–(2.45) -/

/-- The matrix geometric series of O&R footnote 28, p. 91: if `Σ_k A^k` converges then
`Σ_{k≥1} A^k = A (I − A)^{-1}`. -/
theorem tsum_pow_succ_eq_mul_inv {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (hA : Summable fun k => A ^ k) :
    ∑' k, A ^ (k + 1) = A * (1 - A)⁻¹ := by
  rw [Matrix.inv_eq_left_inv hA.tsum_pow_mul_one_sub, ← hA.tsum_mul_left]
  simp only [pow_succ']

/-- A sufficient condition for the matrix geometric series of O&R footnote 28, p. 91, to
converge: every absolute row sum of `A` is below one (the `ℓ∞` operator norm `‖A‖ < 1`). -/
theorem summable_pow_of_rowSum_lt_one {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n ℝ} (h : ∀ i, ∑ j, |A i j| < 1) : Summable fun k => A ^ k := by
  let _ := Matrix.linftyOpNormedRing (n := n) (α := ℝ)
  let _ := Matrix.linftyOpNormedAlgebra (R := ℝ) (n := n) (α := ℝ)
  have : CompleteSpace (Matrix n n ℝ) := FiniteDimensional.complete ℝ _
  have hA : ‖A‖ < 1 := by
    rw [Matrix.linfty_opNorm_def]
    have : (Finset.univ.sup fun i : n => ∑ j : n, ‖A i j‖₊) < 1 := by
      rw [Finset.sup_lt_iff (by simp)]
      intro i _
      rw [← NNReal.coe_lt_coe, NNReal.coe_sum]
      simpa [coe_nnnorm, Real.norm_eq_abs] using h i
    exact_mod_cast this
  exact summable_geometric_of_norm_lt_one hA

/-- With `Ψ` scaled by `1/(1+r)`, the summability of `Σ_k (Ψ/(1+r))^k` in O&R footnote 28,
p. 91, holds when every absolute row sum of the VAR matrix `Ψ` is below `1 + r`. -/
theorem summable_disc_smul_pow {n : Type*} [Fintype n] [DecidableEq n] {r : ℝ}
    (hr : 0 < 1 + r) {Ψ : Matrix n n ℝ} (h : ∀ i, ∑ j, |Ψ i j| < 1 + r) :
    Summable fun k => (disc r • Ψ) ^ k := by
  refine summable_pow_of_rowSum_lt_one fun i => ?_
  have hd := disc_pos hr
  simp only [Matrix.smul_apply, smul_eq_mul, abs_mul, abs_of_pos hd, ← Finset.mul_sum]
  calc disc r * ∑ j, |Ψ i j| < disc r * (1 + r) := mul_lt_mul_of_pos_left (h i) hd
    _ = 1 := by rw [mul_comm, one_add_mul_disc hr]

/-- Iterated VAR forecasts, O&R p. 91: if `E_t x_{t+1} = Ψ x_t` at every date (the VAR (2.44)
with unpredictable errors) and `x_t` is known at `t`, then `E_t x_{t+k} = Ψ^k x_t` (law of
iterated expectations and linearity). -/
theorem condExp_var_pow [IsProbabilityMeasure μ] {ℱ : Filtration ℕ m0}
    {x : ℕ → Ω → Fin 2 → ℝ} {Ψ : Matrix (Fin 2) (Fin 2) ℝ} (hx : ∀ t, Integrable (x t) μ)
    (hvar : ∀ t, μ[x (t + 1) | ℱ t] =ᵐ[μ] fun ω => Ψ *ᵥ x t ω) {t : ℕ}
    (hxt : StronglyMeasurable[ℱ t] (x t)) (k : ℕ) :
    μ[x (t + k) | ℱ t] =ᵐ[μ] fun ω => (Ψ ^ k) *ᵥ x t ω := by
  induction k with
  | zero =>
    have h := condExp_of_stronglyMeasurable (μ := μ) (ℱ.le t) hxt (hx t)
    refine Eventually.of_forall fun ω => ?_
    simp only [add_zero, h, pow_zero, Matrix.one_mulVec]
  | succ k ih =>
    let T : (Fin 2 → ℝ) →L[ℝ] (Fin 2 → ℝ) := LinearMap.toContinuousLinearMap (Matrix.mulVecLin Ψ)
    have htow := condExp_condExp_of_le (μ := μ) (f := x (t + k + 1))
      (ℱ.mono (Nat.le_add_right t k)) (ℱ.le (t + k))
    have h1 := condExp_congr_ae (m := ℱ t) (hvar (t + k))
    have h2 := T.comp_condExp_comm (μ := μ) (m := ℱ t) (hx (t + k))
    have hT : (fun ω => Ψ *ᵥ x (t + k) ω) = T ∘ x (t + k) := by
      funext ω
      simp [T]
    rw [hT] at h1
    filter_upwards [htow, h1, h2, ih] with ω a b c d
    change μ[x (t + k + 1) | ℱ t] ω = _
    rw [← a, b, ← c, Function.comp_apply, d]
    simp [T, pow_succ', Matrix.mulVec_mulVec]

/-- The component forecast `E_t ΔZ_{t+k}`: the conditional expectation of the first coordinate
of `x_{t+k}` is the first coordinate of `E_t x_{t+k}` (premultiplication by `[1 0]`, p. 91). -/
theorem condExp_coord {m : MeasurableSpace Ω} {X : Ω → Fin 2 → ℝ}
    (hX : Integrable X μ) (i : Fin 2) :
    μ[fun ω => X ω i | m] =ᵐ[μ] fun ω => μ[X | m] ω i := by
  have h := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) i).comp_condExp_comm
    (μ := μ) (m := m) hX
  exact h.symm

/-- **O&R (2.45), p. 91, deterministic core.** For `A = Ψ/(1+r)` with convergent geometric
series, `−Σ_{s≥1} (1+r)^{-s} [1 0] Ψ^s v = −[1 0] (Ψ/(1+r)) (I − Ψ/(1+r))^{-1} v`. -/
theorem var_forecast_sum {r : ℝ} {Ψ : Matrix (Fin 2) (Fin 2) ℝ}
    (hsum : Summable fun k => (disc r • Ψ) ^ k) (v : Fin 2 → ℝ) :
    -∑' s, disc r ^ (s + 1) * ((Ψ ^ (s + 1)) *ᵥ v) 0 =
      -(((disc r • Ψ) * (1 - disc r • Ψ)⁻¹) *ᵥ v) 0 := by
  let L : Matrix (Fin 2) (Fin 2) ℝ →+ ℝ :=
    { toFun := fun B => (B *ᵥ v) 0
      map_zero' := by simp
      map_add' := fun B C => by simp [Matrix.add_mulVec] }
  have hL : Continuous L :=
    (continuous_apply 0).comp (continuous_id.matrix_mulVec continuous_const)
  have hs : Summable fun k => (disc r • Ψ) ^ (k + 1) := (summable_nat_add_iff 1).2 hsum
  rw [← tsum_pow_succ_eq_mul_inv hsum]
  have e : (((∑' k, (disc r • Ψ) ^ (k + 1)) *ᵥ v) 0) = L (∑' k, (disc r • Ψ) ^ (k + 1)) := rfl
  rw [e, hs.map_tsum L hL]
  congr 1
  refine tsum_congr fun s => ?_
  simp [L, smul_pow, Matrix.smul_mulVec]

/-- **O&R (2.45), p. 91.** Under the VAR (2.44) with `E_t x_{t+1} = Ψ x_t`, `x_t = (ΔZ_t, CA_t)`
known at `t`, and a convergent series `Σ_k (Ψ/(1+r))^k`, the model's predicted current account
`−Σ_{s>t} (1+r)^{-(s-t)} E_t ΔZ_s` equals `−[1 0] (Ψ/(1+r)) (I − Ψ/(1+r))^{-1} x_t` a.s. -/
theorem var_predicted_current_account [IsProbabilityMeasure μ] {r : ℝ}
    {ℱ : Filtration ℕ m0} {x : ℕ → Ω → Fin 2 → ℝ} {Ψ : Matrix (Fin 2) (Fin 2) ℝ}
    (hx : ∀ t, Integrable (x t) μ) (hvar : ∀ t, μ[x (t + 1) | ℱ t] =ᵐ[μ] fun ω => Ψ *ᵥ x t ω)
    {t : ℕ} (hxt : StronglyMeasurable[ℱ t] (x t)) (hsum : Summable fun k => (disc r • Ψ) ^ k) :
    (fun ω => -∑' s, disc r ^ (s + 1) * μ[fun ω' => x (t + s + 1) ω' 0 | ℱ t] ω) =ᵐ[μ]
      fun ω => -(((disc r • Ψ) * (1 - disc r • Ψ)⁻¹) *ᵥ x t ω) 0 := by
  have h1 : ∀ᵐ ω ∂μ, ∀ s, μ[fun ω' => x (t + s + 1) ω' 0 | ℱ t] ω = μ[x (t + s + 1) | ℱ t] ω 0 :=
    ae_all_iff.2 fun s => condExp_coord (hx _) 0
  have h2 : ∀ᵐ ω ∂μ, ∀ s, μ[x (t + (s + 1)) | ℱ t] ω = (Ψ ^ (s + 1)) *ᵥ x t ω :=
    ae_all_iff.2 fun s => condExp_var_pow hx hvar hxt (s + 1)
  filter_upwards [h1, h2] with ω h1 h2
  rw [← var_forecast_sum hsum]
  congr 2
  funext s
  rw [h1 s]
  exact congrArg (fun w => disc r ^ (s + 1) * w 0) (h2 s)

/-- **The restriction tested on p. 92.** If, in addition, the current account is the second VAR
coordinate and satisfies O&R (2.43), p. 90, with the VAR forecasts, then
`CA_t = [Φ_ΔZ Φ_CA] x_t` with `[Φ_ΔZ Φ_CA] = −[1 0] (Ψ/(1+r)) (I − Ψ/(1+r))^{-1}`, i.e. the
predicted and actual current accounts coincide almost surely. -/
theorem var_null_restriction [IsProbabilityMeasure μ] {r : ℝ}
    {ℱ : Filtration ℕ m0} {x : ℕ → Ω → Fin 2 → ℝ} {Ψ : Matrix (Fin 2) (Fin 2) ℝ}
    (hx : ∀ t, Integrable (x t) μ) (hvar : ∀ t, μ[x (t + 1) | ℱ t] =ᵐ[μ] fun ω => Ψ *ᵥ x t ω)
    {t : ℕ} (hxt : StronglyMeasurable[ℱ t] (x t)) (hsum : Summable fun k => (disc r • Ψ) ^ k)
    (h43 : (fun ω => x t ω 1) =ᵐ[μ]
      fun ω => -∑' s, disc r ^ (s + 1) * μ[fun ω' => x (t + s + 1) ω' 0 | ℱ t] ω) :
    (fun ω => x t ω 1) =ᵐ[μ] fun ω => -(((disc r • Ψ) * (1 - disc r • Ψ)⁻¹) *ᵥ x t ω) 0 :=
  h43.trans (var_predicted_current_account hx hvar hxt hsum)

end Stochastic

end ObstfeldRogoff.SmallOpenEconomyDynamics.PresentValueTest
