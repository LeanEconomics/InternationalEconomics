/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import SmallOpenEconomyDynamics.PresentValue
import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondJensen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# A stochastic current account model

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §2.3,
pp. 79–96, Exercises 3 and 4 (pp. 125–126), and Supplement A.3 (p. 722).

Uncertainty uses Mathlib's measure-theoretic conditional expectation. The book's `E_t X` is
`μ[X | ℱ t]` for a filtration `ℱ` on a probability space. Random variables are equal almost
surely (`=ᵐ[μ]`). The stochastic Euler equation (2.28)–(2.29) is a hypothesis throughout, in
conditional-expectation form. Its variational derivation needs differentiation under the
integral and is not formalised. Supplement A.3's dynamic-programming route to it, from the
first-order and envelope conditions, is `euler_of_bellman`.

Contents:
* Hall's random walk (2.31) and the martingale property of consumption (footnote 18):
  `hall_random_walk`, `hall_martingale`, `hall_condExp_future`.
* Certainty equivalence (2.32): `certainty_equivalence`. The book exchanges `E_t` with an
  infinite sum. Here the finite-horizon expected budget identity is exact, and the limit rests
  on explicit expected-transversality and summability hypotheses.
* AR(1) output (2.33)–(2.37): forecasts `output_forecast`, the consumption function
  `consumption_ar1`, the current account `current_account_ar1`, and Deaton's numbers (p. 85).
* Nonstationary output (2.38) and Exercise 4: forecasts, forecast revisions (4b), consumption
  change as revised permanent income (4a), the consumption innovation `(1 + r)/(1 + r − ρ) ε`
  (4c) and the current-account response `−ρ/(1 + r − ρ)` (4d).
* Risky capital (2.40), stated with a conditional covariance (footnote 23).
* Precautionary saving (§2.3.6): `u''' ≥ 0` makes `u'` convex, conditional Jensen, a
  mean-preserving spread raises expected marginal utility, and a two-period comparative static
  (more income risk, lower consumption). Isoelastic `u'''` > 0 (footnote 32).
* Exercise 3: under conditional lognormality, `E_t log C_{t+1} − log C_t = v_t/(2σ)`. The drift
  is constant only when the conditional variance `v_t` is.
-/

namespace ObstfeldRogoff.SmallOpenEconomyDynamics.StochasticConsumption

open MeasureTheory Filter Topology Finset
open ObstfeldRogoff.SmallOpenEconomyDynamics.PresentValue (disc)

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}

/-- Quadratic period utility, O&R (2.30), p. 81: `u(C) = C − (a₀/2) C²`. -/
noncomputable def quadU (a0 C : ℝ) : ℝ := C - a0 / 2 * C ^ 2

/-- Marginal utility of the quadratic utility (2.30), p. 81: `u'(C) = 1 − a₀ C`. -/
def quadMU (a0 C : ℝ) : ℝ := 1 - a0 * C

/-- O&R p. 81: the marginal utility of (2.30) is `1 − a₀ C`, linear in `C`. -/
theorem hasDerivAt_quadU (a0 c : ℝ) : HasDerivAt (quadU a0) (quadMU a0 c) c := by
  have h := ((hasDerivAt_id c).sub ((hasDerivAt_pow 2 c).const_mul (a0 / 2)))
  have e : quadU a0 = (id - fun y => a0 / 2 * y ^ 2) := by funext y; simp [quadU]
  rw [e]
  convert h using 1
  simp only [quadMU]; norm_num; ring

/-- **Hall's random walk**, O&R (2.31), p. 81. With quadratic utility (2.30), `a₀ ≠ 0` and
`(1 + r) β = 1`, the stochastic Euler equation (2.29) `u'(C_t) = (1 + r) β E_t u'(C_{t+1})`
(taken as a hypothesis in conditional-expectation form; its variational derivation is not
formalised) implies `E_t C_{t+1} = C_t` almost surely. -/
theorem hall_random_walk [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m0) {C : ℕ → Ω → ℝ} {a0 r β : ℝ} (ha0 : a0 ≠ 0)
    (hrβ : (1 + r) * β = 1) (t : ℕ) (hC : StronglyMeasurable[ℱ t] (C t))
    (hCi : Integrable (C t) μ) (hCi' : Integrable (C (t + 1)) μ)
    (heuler : μ[fun ω => quadMU a0 (C (t + 1) ω) | ℱ t] =ᵐ[μ]
      fun ω => quadMU a0 (C t ω) / ((1 + r) * β)) :
    μ[C (t + 1) | ℱ t] =ᵐ[μ] C t := by
  have hlin : μ[fun ω => quadMU a0 (C (t + 1) ω) | ℱ t] =ᵐ[μ]
      fun ω => 1 - a0 * μ[C (t + 1) | ℱ t] ω := by
    have h1 : (fun ω => quadMU a0 (C (t + 1) ω)) = (fun _ => (1 : ℝ)) - a0 • C (t + 1) := by
      funext ω; simp [quadMU]
    rw [h1]
    filter_upwards [condExp_sub (integrable_const (1 : ℝ)) (hCi'.smul a0) (ℱ t),
      condExp_smul (μ := μ) a0 (C (t + 1)) (ℱ t)] with ω h2 h3
    rw [h2, Pi.sub_apply, h3, condExp_const (ℱ.le t)]
    simp
  have hCt : μ[C t | ℱ t] = C t := condExp_of_stronglyMeasurable (ℱ.le t) hC hCi
  filter_upwards [hlin, heuler] with ω h1 h2
  rw [h1, hrβ, div_one] at h2
  simp only [quadMU] at h2
  have : a0 * μ[C (t + 1) | ℱ t] ω = a0 * C t ω := by linarith
  exact mul_left_cancel₀ ha0 this

/-- **Consumption is a martingale**, O&R (2.31) and footnote 18, p. 81: under the hypotheses of
`hall_random_walk` at every date, and with consumption known at each date, `C` is a martingale
with respect to the information filtration `ℱ`. -/
theorem hall_martingale [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m0) {C : ℕ → Ω → ℝ} {a0 r β : ℝ} (ha0 : a0 ≠ 0)
    (hrβ : (1 + r) * β = 1) (hC : StronglyAdapted ℱ C) (hCi : ∀ t, Integrable (C t) μ)
    (heuler : ∀ t, μ[fun ω => quadMU a0 (C (t + 1) ω) | ℱ t] =ᵐ[μ]
      fun ω => quadMU a0 (C t ω) / ((1 + r) * β)) :
    Martingale C ℱ μ :=
  martingale_nat hC hCi fun t =>
    (hall_random_walk ℱ ha0 hrβ t (hC t) (hCi t) (hCi (t + 1)) (heuler t)).symm

/-- O&R p. 81: for any `s > t`, `E_t C_s = E_t C_{s−1} = ⋯ = C_t` (law of iterated
expectations applied to Hall's random walk). -/
theorem hall_condExp_future [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m0) {C : ℕ → Ω → ℝ} {a0 r β : ℝ} (ha0 : a0 ≠ 0)
    (hrβ : (1 + r) * β = 1) (hC : StronglyAdapted ℱ C) (hCi : ∀ t, Integrable (C t) μ)
    (heuler : ∀ t, μ[fun ω => quadMU a0 (C (t + 1) ω) | ℱ t] =ᵐ[μ]
      fun ω => quadMU a0 (C t ω) / ((1 + r) * β)) {t s : ℕ} (hts : t ≤ s) :
    μ[C s | ℱ t] =ᵐ[μ] C t :=
  (hall_martingale ℱ ha0 hrβ hC hCi heuler).2 t s hts

/-- Expected-value budget recursion, O&R p. 81. If net foreign assets obey the current account
identity `B_{s+1} = (1 + r) B_s + Z_s − C_s` in every state (`Z = Y − G − I`) and consumption is a
martingale, then the date-`t` forecasts `b_n = E_t B_{t+n}` satisfy almost surely, for all `n`,
`b_{n+1} = (1 + r) b_n + (E_t Z_{t+n} − C_t)`. -/
theorem condExp_budget_step (ℱ : Filtration ℕ m0) {B Z C : ℕ → Ω → ℝ} {r : ℝ} (t : ℕ)
    (hbud : ∀ s ω, B (s + 1) ω = (1 + r) * B s ω + Z s ω - C s ω)
    (hBi : ∀ s, Integrable (B s) μ) (hZi : ∀ s, Integrable (Z s) μ)
    (hCi : ∀ s, Integrable (C s) μ) (hmart : Martingale C ℱ μ) :
    ∀ᵐ ω ∂μ, ∀ n, μ[B (t + (n + 1)) | ℱ t] ω =
      (1 + r) * μ[B (t + n) | ℱ t] ω + (μ[Z (t + n) | ℱ t] ω - C t ω) := by
  rw [ae_all_iff]
  intro n
  have hf : B (t + (n + 1)) = (1 + r) • B (t + n) + Z (t + n) - C (t + n) := by
    funext ω; simp [← hbud]; rfl
  rw [hf]
  filter_upwards [condExp_sub (((hBi (t + n)).smul (1 + r)).add (hZi (t + n)))
      (hCi (t + n)) (ℱ t),
    condExp_add ((hBi (t + n)).smul (1 + r)) (hZi (t + n)) (ℱ t),
    condExp_smul (μ := μ) (1 + r) (B (t + n)) (ℱ t),
    hmart.2 t (t + n) (Nat.le_add_right t n)] with ω h1 h2 h3 h4
  rw [h1, Pi.sub_apply, h2, Pi.add_apply, h3, h4]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- **Certainty equivalence**, O&R (2.32), p. 81:
`C_t = (r/(1 + r)) [(1 + r) B_t + Σ_{s ≥ t} (1 + r)^{−(s−t)} E_t (Y − G − I)_s]`.
Derived from the martingale property of consumption and the state-by-state current account
identity. The book passes from the almost-sure intertemporal budget constraint to its
expectation by exchanging `E_t` with an infinite sum; here the finite-horizon expectation is
exact and the limit is handled by two explicit hypotheses: the expected discounted terminal
assets vanish (`htvc`, the expected transversality condition) and the discounted net-output
forecasts are summable (`hsum`). Requires `r > 0` (p. 66). -/
theorem certainty_equivalence [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m0) {B Z C : ℕ → Ω → ℝ} {r : ℝ} (hr : 0 < r)
    (t : ℕ) (hbud : ∀ s ω, B (s + 1) ω = (1 + r) * B s ω + Z s ω - C s ω)
    (hBi : ∀ s, Integrable (B s) μ) (hZi : ∀ s, Integrable (Z s) μ)
    (hCi : ∀ s, Integrable (C s) μ) (hmart : Martingale C ℱ μ)
    (hBt : StronglyMeasurable[ℱ t] (B t))
    (hsum : ∀ᵐ ω ∂μ, Summable fun k => disc r ^ k * μ[Z (t + k) | ℱ t] ω)
    (htvc : ∀ᵐ ω ∂μ, Tendsto (fun n => disc r ^ n * μ[B (t + n) | ℱ t] ω) atTop (𝓝 0)) :
    ∀ᵐ ω ∂μ, C t ω =
      r / (1 + r) * ((1 + r) * B t ω + ∑' k, disc r ^ k * μ[Z (t + k) | ℱ t] ω) := by
  have hr1 : 0 < 1 + r := by linarith
  have hB0 : μ[B (t + 0) | ℱ t] = B t := condExp_of_stronglyMeasurable (ℱ.le t) hBt (hBi t)
  filter_upwards [condExp_budget_step ℱ t hbud hBi hZi hCi hmart, hsum, htvc]
    with ω hstep hs htv
  set d := disc r with hd
  set S := ∑' k, d ^ k * μ[Z (t + k) | ℱ t] ω with hS
  have hd1 : (1 + r) * d = 1 := PresentValue.one_add_mul_disc hr1
  have hgeo : HasSum (fun s => d ^ s) ((1 + r) / r) := PresentValue.hasSum_disc_pow hr
  have hN : HasSum (fun s => d ^ (s + 1) * (μ[Z (t + s) | ℱ t] ω - C t ω))
      (d * S - C t ω * d * ((1 + r) / r)) := by
    have := (hs.hasSum.mul_left d).sub (hgeo.mul_left (C t ω * d))
    convert this using 1
    funext s; ring
  have key := (PresentValue.discounted_tendsto_zero_iff hr1 hstep hN.summable).1 htv
  rw [hN.tsum_eq, hB0] at key
  have hdr : d * ((1 + r) / r) = 1 / r := by
    field_simp; linarith
  have : C t ω * (1 / r) = B t ω + d * S := by
    rw [← hdr]; linarith
  field_simp at this
  rw [this, hd, PresentValue.disc]
  field_simp

/-- **Certainty equivalence from the Euler equation**, O&R (2.30)–(2.32), p. 81: combining
`hall_martingale` with `certainty_equivalence`. Quadratic utility, `(1 + r) β = 1`, the Euler
equation (2.29) at every date, the current account identity in every state, and the expected
transversality and summability hypotheses give the consumption function (2.32) almost surely. -/
theorem certainty_equivalence_quadratic [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m0) {B Z C : ℕ → Ω → ℝ} {a0 r β : ℝ} (hr : 0 < r) (ha0 : a0 ≠ 0)
    (hrβ : (1 + r) * β = 1) (hC : StronglyAdapted ℱ C)
    (heuler : ∀ t, μ[fun ω => quadMU a0 (C (t + 1) ω) | ℱ t] =ᵐ[μ]
      fun ω => quadMU a0 (C t ω) / ((1 + r) * β))
    (t : ℕ) (hbud : ∀ s ω, B (s + 1) ω = (1 + r) * B s ω + Z s ω - C s ω)
    (hBi : ∀ s, Integrable (B s) μ) (hZi : ∀ s, Integrable (Z s) μ)
    (hCi : ∀ s, Integrable (C s) μ) (hBt : StronglyMeasurable[ℱ t] (B t))
    (hsum : ∀ᵐ ω ∂μ, Summable fun k => disc r ^ k * μ[Z (t + k) | ℱ t] ω)
    (htvc : ∀ᵐ ω ∂μ, Tendsto (fun n => disc r ^ n * μ[B (t + n) | ℱ t] ω) atTop (𝓝 0)) :
    ∀ᵐ ω ∂μ, C t ω =
      r / (1 + r) * ((1 + r) * B t ω + ∑' k, disc r ^ k * μ[Z (t + k) | ℱ t] ω) :=
  certainty_equivalence ℱ hr t hbud hBi hZi hCi (hall_martingale ℱ ha0 hrβ hC hCi heuler) hBt
    hsum htvc

/-- One-step forecast of an AR(1) deviation, O&R (2.33), p. 82: if
`y_{s+1} = ρ y_s + ε_{s+1}` with `E_s ε_{s+1} = 0` and `y_s` known at `s`, then
`E_s y_{s+1} = ρ y_s`. -/
theorem ar1_condExp_step [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) {y ε : ℕ → Ω → ℝ}
    {ρ : ℝ} (s : ℕ) (hy : ∀ ω, y (s + 1) ω = ρ * y s ω + ε (s + 1) ω)
    (hys : StronglyMeasurable[ℱ s] (y s)) (hyi : Integrable (y s) μ)
    (hεi : Integrable (ε (s + 1)) μ) (hε : μ[ε (s + 1) | ℱ s] =ᵐ[μ] 0) :
    μ[y (s + 1) | ℱ s] =ᵐ[μ] fun ω => ρ * y s ω := by
  have hf : y (s + 1) = ρ • y s + ε (s + 1) := by funext ω; simp [hy]
  rw [hf]
  filter_upwards [condExp_add (hyi.smul ρ) hεi (ℱ s), condExp_smul (μ := μ) ρ (y s) (ℱ s), hε]
    with ω h1 h2 h3
  rw [h1, Pi.add_apply, h2, h3, condExp_of_stronglyMeasurable (ℱ.le s) hys hyi]
  simp

/-- **AR(1) forecasts**, O&R (2.34), p. 82: if `y_{s+1} = ρ y_s + ε_{s+1}` with
`E_s ε_{s+1} = 0` at every date, then `E_t y_{t+k} = ρ^k y_t` (iterated forward substitution
plus the law of iterated expectations, footnote 20). -/
theorem ar1_forecast [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) {y ε : ℕ → Ω → ℝ} {ρ : ℝ}
    (hy : ∀ s ω, y (s + 1) ω = ρ * y s ω + ε (s + 1) ω) (hya : StronglyAdapted ℱ y)
    (hyi : ∀ s, Integrable (y s) μ) (hεi : ∀ s, Integrable (ε s) μ)
    (hε : ∀ s, μ[ε (s + 1) | ℱ s] =ᵐ[μ] 0) (t k : ℕ) :
    μ[y (t + k) | ℱ t] =ᵐ[μ] fun ω => ρ ^ k * y t ω := by
  induction k with
  | zero =>
    refine ae_of_all _ fun ω => ?_
    simp [condExp_of_stronglyMeasurable (ℱ.le t) (hya t) (hyi t)]
  | succ k ih =>
    have hstep := ar1_condExp_step ℱ (t + k) (hy (t + k)) (hya (t + k)) (hyi (t + k))
      (hεi (t + k + 1)) (hε (t + k))
    have htow := ℱ.condExp_condExp (μ := μ) (y (t + k + 1)) (Nat.le_add_right t k)
    have hc := condExp_congr_ae (m := ℱ t) hstep
    have hsm : (fun ω => ρ * y (t + k) ω) = ρ • y (t + k) := rfl
    rw [hsm] at hc
    filter_upwards [htow, hc, condExp_smul (μ := μ) ρ (y (t + k)) (ℱ t), ih]
      with ω h1 h2 h3 h4
    change μ[y (t + k + 1) | ℱ t] ω = _
    rw [← h1, h2, h3, Pi.smul_apply, h4, smul_eq_mul, pow_succ]
    ring

/-- **Stationary output forecasts**, O&R (2.33)–(2.34), p. 82: if
`Y_{s+1} − Ȳ = ρ (Y_s − Ȳ) + ε_{s+1}` with `E_s ε_{s+1} = 0`, then
`E_t Y_{t+k} = Ȳ + ρ^k (Y_t − Ȳ)` almost surely. -/
theorem output_forecast [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) {Y ε : ℕ → Ω → ℝ}
    {ρ Ybar : ℝ} (hY : ∀ s ω, Y (s + 1) ω - Ybar = ρ * (Y s ω - Ybar) + ε (s + 1) ω)
    (hYa : StronglyAdapted ℱ Y) (hYi : ∀ s, Integrable (Y s) μ)
    (hεi : ∀ s, Integrable (ε s) μ) (hε : ∀ s, μ[ε (s + 1) | ℱ s] =ᵐ[μ] 0) (t k : ℕ) :
    μ[Y (t + k) | ℱ t] =ᵐ[μ] fun ω => Ybar + ρ ^ k * (Y t ω - Ybar) := by
  have hya : StronglyAdapted ℱ (fun s => Y s - fun _ => Ybar) :=
    fun s => (hYa s).sub stronglyMeasurable_const
  have hyi : ∀ s, Integrable ((fun s => Y s - fun _ => Ybar) s) μ :=
    fun s => (hYi s).sub (integrable_const Ybar)
  have h := ar1_forecast ℱ (y := fun s => Y s - fun _ => Ybar) (fun s ω => hY s ω) hya hyi hεi
    hε t k
  filter_upwards [h, condExp_sub (hYi (t + k)) (integrable_const Ybar) (ℱ t)] with ω h1 h2
  rw [h2, Pi.sub_apply, condExp_const (ℱ.le t)] at h1
  simp only [Pi.sub_apply] at h1
  linarith

/-- Moving-average form of an AR(1), finite-horizon version of O&R (2.36), p. 83:
`y_{s+n} = ρ^n y_s + Σ_{k<n} ρ^{n−1−k} ε_{s+k+1}` (a pathwise identity). -/
theorem ar1_moving_average {y ε : ℕ → Ω → ℝ} {ρ : ℝ}
    (hy : ∀ s ω, y (s + 1) ω = ρ * y s ω + ε (s + 1) ω) (s n : ℕ) (ω : Ω) :
    y (s + n) ω = ρ ^ n * y s ω + ∑ k ∈ range n, ρ ^ (n - 1 - k) * ε (s + k + 1) ω := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← add_assoc, hy, ih, sum_range_succ, mul_add, mul_sum, pow_succ]
    have : ∑ k ∈ range n, ρ * (ρ ^ (n - 1 - k) * ε (s + k + 1) ω) =
        ∑ k ∈ range n, ρ ^ (n + 1 - 1 - k) * ε (s + k + 1) ω := by
      refine sum_congr rfl fun k hk => ?_
      have hk' : k < n := mem_range.1 hk
      rw [← mul_assoc, ← pow_succ']
      congr 2
      omega
    rw [this]
    simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, one_mul]
    ring

/-- Present value of AR(1) forecasts, used in O&R (2.35), p. 83:
`Σ_{k ≥ 0} (1 + r)^{−k} ρ^k = (1 + r)/(1 + r − ρ)` whenever `|ρ| < 1 + r`. -/
theorem hasSum_disc_mul_pow {r ρ : ℝ} (hρ : |ρ| < 1 + r) :
    HasSum (fun k => disc r ^ k * ρ ^ k) ((1 + r) / (1 + r - ρ)) := by
  have hr1 : 0 < 1 + r := lt_of_le_of_lt (abs_nonneg ρ) hρ
  have habs : |disc r * ρ| < 1 := by
    rw [abs_mul, abs_of_pos (PresentValue.disc_pos hr1), PresentValue.disc,
      inv_mul_lt_iff₀ hr1, mul_one]
    exact hρ
  have h := hasSum_geometric_of_abs_lt_one habs
  have hne : 1 + r - ρ ≠ 0 := by
    have := neg_abs_le ρ; have := le_abs_self ρ; intro h; linarith
  convert h using 1
  · funext k; rw [mul_pow]
  · rw [PresentValue.disc]; field_simp

/-- The denominator of O&R (2.35), p. 83, is nonzero: `1 + r − ρ ≠ 0` whenever `|ρ| < 1 + r`. -/
theorem one_add_sub_ne_zero {r ρ : ℝ} (hρ : |ρ| < 1 + r) : 1 + r - ρ ≠ 0 := by
  have := le_abs_self ρ; intro h; linarith

/-- **Consumption with AR(1) output**, O&R (2.35), p. 83: with `G = I = 0`, output following
(2.33), and consumption given by the certainty-equivalence rule (2.32) (hypothesis `hCE`,
supplied by `certainty_equivalence`), `C_t = r B_t + Ȳ + r (Y_t − Ȳ)/(1 + r − ρ)` almost surely.
The book's `0 ≤ ρ ≤ 1` is replaced by the weaker `|ρ| < 1 + r`, which is what the present value
needs. -/
theorem consumption_ar1 [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0) {B Y ε C : ℕ → Ω → ℝ}
    {r ρ Ybar : ℝ} (hr : 0 < r) (hρ : |ρ| < 1 + r)
    (hY : ∀ s ω, Y (s + 1) ω - Ybar = ρ * (Y s ω - Ybar) + ε (s + 1) ω)
    (hYa : StronglyAdapted ℱ Y) (hYi : ∀ s, Integrable (Y s) μ)
    (hεi : ∀ s, Integrable (ε s) μ) (hε : ∀ s, μ[ε (s + 1) | ℱ s] =ᵐ[μ] 0) (t : ℕ)
    (hCE : ∀ᵐ ω ∂μ, C t ω =
      r / (1 + r) * ((1 + r) * B t ω + ∑' k, disc r ^ k * μ[Y (t + k) | ℱ t] ω)) :
    ∀ᵐ ω ∂μ, C t ω = r * B t ω + Ybar + r * (Y t ω - Ybar) / (1 + r - ρ) := by
  have hf : ∀ᵐ ω ∂μ, ∀ k, μ[Y (t + k) | ℱ t] ω = Ybar + ρ ^ k * (Y t ω - Ybar) :=
    ae_all_iff.2 fun k => output_forecast ℱ hY hYa hYi hεi hε t k
  filter_upwards [hCE, hf] with ω h1 h2
  have hsum : HasSum (fun k => disc r ^ k * μ[Y (t + k) | ℱ t] ω)
      (Ybar * ((1 + r) / r) + (Y t ω - Ybar) * ((1 + r) / (1 + r - ρ))) := by
    have := ((PresentValue.hasSum_disc_pow hr).mul_left Ybar).add
      ((hasSum_disc_mul_pow hρ).mul_left (Y t ω - Ybar))
    convert this using 1
    funext k; rw [h2]; ring
  have hne := one_add_sub_ne_zero hρ
  have hr1 : 1 + r ≠ 0 := by linarith
  rw [h1, hsum.tsum_eq]
  field_simp
  ring

/-- Consumption in terms of the innovation, O&R p. 83: substituting
`Y_t − Ȳ = ρ (Y_{t−1} − Ȳ) + ε_t` into (2.35) gives
`C_t = r B_t + Ȳ + (rρ/(1 + r − ρ)) (Y_{t−1} − Ȳ) + (r/(1 + r − ρ)) ε_t`. -/
theorem consumption_innovation_form {r ρ B Ybar Yt Yprev e C : ℝ} (hne : 1 + r - ρ ≠ 0)
    (hC : C = r * B + Ybar + r * (Yt - Ybar) / (1 + r - ρ))
    (hY : Yt - Ybar = ρ * (Yprev - Ybar) + e) :
    C = r * B + Ybar + r * ρ / (1 + r - ρ) * (Yprev - Ybar) + r / (1 + r - ρ) * e := by
  rw [hC, hY]
  field_simp
  ring

/-- **The current account with AR(1) output**, O&R (2.37), p. 83: from (2.35) and the current
account identity `CA_t = r B_t + Y_t − C_t`,
`CA_t = ρ ((1 − ρ)/(1 + r − ρ)) (Y_{t−1} − Ȳ) + ((1 − ρ)/(1 + r − ρ)) ε_t`. -/
theorem current_account_ar1 {r ρ B Ybar Yt Yprev e C : ℝ} (hne : 1 + r - ρ ≠ 0)
    (hC : C = r * B + Ybar + r * (Yt - Ybar) / (1 + r - ρ))
    (hY : Yt - Ybar = ρ * (Yprev - Ybar) + e) :
    r * B + Yt - C =
      ρ * ((1 - ρ) / (1 + r - ρ)) * (Yprev - Ybar) + (1 - ρ) / (1 + r - ρ) * e := by
  have hYt : Yt = Ybar + (ρ * (Yprev - Ybar) + e) := by linarith
  rw [hC, hYt]
  field_simp
  ring

/-- Almost-sure form of O&R (2.37), p. 83: under the hypotheses of `consumption_ar1` at date
`t + 1`, `CA_{t+1} = r B_{t+1} + Y_{t+1} − C_{t+1}` equals
`ρ ((1 − ρ)/(1 + r − ρ)) (Y_t − Ȳ) + ((1 − ρ)/(1 + r − ρ)) ε_{t+1}` almost surely. -/
theorem current_account_ar1_ae [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0)
    {B Y ε C : ℕ → Ω → ℝ} {r ρ Ybar : ℝ} (hr : 0 < r) (hρ : |ρ| < 1 + r)
    (hY : ∀ s ω, Y (s + 1) ω - Ybar = ρ * (Y s ω - Ybar) + ε (s + 1) ω)
    (hYa : StronglyAdapted ℱ Y) (hYi : ∀ s, Integrable (Y s) μ)
    (hεi : ∀ s, Integrable (ε s) μ) (hε : ∀ s, μ[ε (s + 1) | ℱ s] =ᵐ[μ] 0) (t : ℕ)
    (hCE : ∀ᵐ ω ∂μ, C (t + 1) ω = r / (1 + r) *
      ((1 + r) * B (t + 1) ω + ∑' k, disc r ^ k * μ[Y (t + 1 + k) | ℱ (t + 1)] ω)) :
    ∀ᵐ ω ∂μ, r * B (t + 1) ω + Y (t + 1) ω - C (t + 1) ω =
      ρ * ((1 - ρ) / (1 + r - ρ)) * (Y t ω - Ybar) + (1 - ρ) / (1 + r - ρ) * ε (t + 1) ω := by
  filter_upwards [consumption_ar1 ℱ hr hρ hY hYa hYi hεi hε (t + 1) hCE] with ω h
  exact current_account_ar1 (one_add_sub_ne_zero hρ) h (hY t ω)

/-- O&R p. 83: a temporary shock (`0 ≤ ρ < 1`, `r > 0`) raises the current account,
`(1 − ρ)/(1 + r − ρ) > 0`, and raises consumption less than one for one,
`r/(1 + r − ρ) < 1`. -/
theorem temporary_shock_effects {r ρ : ℝ} (hr : 0 < r) (hρ1 : ρ < 1) :
    0 < (1 - ρ) / (1 + r - ρ) ∧ r / (1 + r - ρ) < 1 := by
  have h : 0 < 1 + r - ρ := by linarith
  refine ⟨div_pos (by linarith) h, ?_⟩
  rw [div_lt_one h]
  linarith

/-- O&R p. 83: a permanent shock (`ρ = 1`) has no current account effect, and consumption moves
one for one with output (`r > 0`). -/
theorem permanent_shock_effects {r : ℝ} (hr : 0 < r) :
    (1 : ℝ) * ((1 - 1) / (1 + r - 1)) = 0 ∧ (1 - 1 : ℝ) / (1 + r - 1) = 0 ∧
      r / (1 + r - 1) = 1 := by
  refine ⟨by simp, by simp, ?_⟩
  rw [add_sub_cancel_left]
  exact div_self hr.ne'

/-- The predictable part of the current account, O&R p. 84: with
`E_{t−1} Y_{t+k} = Ȳ + ρ^{k+1} (Y_{t−1} − Ȳ)`,
`E_{t−1} Y_t − (r/(1 + r)) Σ_{k ≥ 0} (1 + r)^{−k} E_{t−1} Y_{t+k}
  = ρ ((1 − ρ)/(1 + r − ρ)) (Y_{t−1} − Ȳ)`. -/
theorem expected_current_account {r ρ Ybar y : ℝ} (hr : 0 < r) (hρ : |ρ| < 1 + r) :
    (Ybar + ρ * y) - r / (1 + r) * ∑' k, disc r ^ k * (Ybar + ρ ^ (k + 1) * y) =
      ρ * ((1 - ρ) / (1 + r - ρ)) * y := by
  have hsum : HasSum (fun k => disc r ^ k * (Ybar + ρ ^ (k + 1) * y))
      (Ybar * ((1 + r) / r) + ρ * y * ((1 + r) / (1 + r - ρ))) := by
    have := ((PresentValue.hasSum_disc_pow hr).mul_left Ybar).add
      ((hasSum_disc_mul_pow hρ).mul_left (ρ * y))
    convert this using 1
    funext k; ring
  have hne := one_add_sub_ne_zero hρ
  have hr1 : 1 + r ≠ 0 := by linarith
  rw [hsum.tsum_eq]
  field_simp
  ring

/-- **Deaton's paradox numerics**, O&R p. 85: at `ρ = 0.96` and `r = 0.04` the consumption
response `r/(1 + r − ρ)` to an output shock is one half. -/
theorem deaton_consumption_response : (0.04 : ℝ) / (1 + 0.04 - 0.96) = 0.5 := by norm_num

/-- **Nonstationary output forecasts**, O&R (2.38), p. 84: if output growth
`D_{s+1} = Y_{s+1} − Y_s` follows `D_{s+1} = ρ D_s + ε_{s+1}` with `E_s ε_{s+1} = 0`, then
`E_t Y_{t+k} = Y_t + (ρ + ρ² + ⋯ + ρ^k) D_t`. -/
theorem nonstationary_forecast [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0)
    {Y D ε : ℕ → Ω → ℝ} {ρ : ℝ} (hY : ∀ s ω, Y (s + 1) ω = Y s ω + D (s + 1) ω)
    (hD : ∀ s ω, D (s + 1) ω = ρ * D s ω + ε (s + 1) ω) (hYa : StronglyAdapted ℱ Y)
    (hDa : StronglyAdapted ℱ D) (hYi : ∀ s, Integrable (Y s) μ)
    (hDi : ∀ s, Integrable (D s) μ) (hεi : ∀ s, Integrable (ε s) μ)
    (hε : ∀ s, μ[ε (s + 1) | ℱ s] =ᵐ[μ] 0) (t k : ℕ) :
    μ[Y (t + k) | ℱ t] =ᵐ[μ] fun ω => Y t ω + (∑ j ∈ range k, ρ ^ (j + 1)) * D t ω := by
  induction k with
  | zero =>
    refine ae_of_all _ fun ω => ?_
    simp [condExp_of_stronglyMeasurable (ℱ.le t) (hYa t) (hYi t)]
  | succ k ih =>
    have hf : Y (t + (k + 1)) = Y (t + k) + D (t + (k + 1)) := by
      funext ω; exact hY (t + k) ω
    rw [hf]
    filter_upwards [condExp_add (hYi (t + k)) (hDi (t + (k + 1))) (ℱ t), ih,
      ar1_forecast ℱ hD hDa hDi hεi hε t (k + 1)] with ω h1 h2 h3
    rw [h1, Pi.add_apply, h2, h3, sum_range_succ]
    ring

/-- **Forecast revisions**, O&R Exercise 4(b), p. 126: under (2.38), for `s = t + 1 + k > t`,
`(E_{t+1} − E_t) Y_s = (1 + ρ + ⋯ + ρ^{s−(t+1)}) ε_{t+1}`. This is also the claim of p. 84
that an output surprise raises `Y_{t+k}` by `(1 + ρ + ⋯ + ρ^k) ε`. -/
theorem nonstationary_revision [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0)
    {Y D ε : ℕ → Ω → ℝ} {ρ : ℝ} (hY : ∀ s ω, Y (s + 1) ω = Y s ω + D (s + 1) ω)
    (hD : ∀ s ω, D (s + 1) ω = ρ * D s ω + ε (s + 1) ω) (hYa : StronglyAdapted ℱ Y)
    (hDa : StronglyAdapted ℱ D) (hYi : ∀ s, Integrable (Y s) μ)
    (hDi : ∀ s, Integrable (D s) μ) (hεi : ∀ s, Integrable (ε s) μ)
    (hε : ∀ s, μ[ε (s + 1) | ℱ s] =ᵐ[μ] 0) (t k : ℕ) :
    μ[Y (t + 1 + k) | ℱ (t + 1)] - μ[Y (t + 1 + k) | ℱ t] =ᵐ[μ]
      fun ω => (∑ j ∈ range (k + 1), ρ ^ j) * ε (t + 1) ω := by
  have h1 := nonstationary_forecast ℱ hY hD hYa hDa hYi hDi hεi hε (t + 1) k
  have h0 : μ[Y (t + 1 + k) | ℱ t] =ᵐ[μ]
      fun ω => Y t ω + (∑ j ∈ range (k + 1), ρ ^ (j + 1)) * D t ω := by
    rw [show t + 1 + k = t + (k + 1) by omega]
    exact nonstationary_forecast ℱ hY hD hYa hDa hYi hDi hεi hε t (k + 1)
  filter_upwards [h1, h0] with ω e1 e0
  rw [Pi.sub_apply, e1, e0, hY t ω, hD t ω]
  have hH : ∑ j ∈ range (k + 1), ρ ^ j = ∑ j ∈ range k, ρ ^ (j + 1) + 1 := by
    rw [sum_range_succ']; simp
  have hG : ∑ j ∈ range (k + 1), ρ ^ (j + 1) = ρ * ∑ j ∈ range (k + 1), ρ ^ j := by
    rw [mul_sum]; exact sum_congr rfl fun j _ => pow_succ' ρ j
  rw [hG, hH]
  ring

/-- Closed form of the revision weight in Exercise 4(b), p. 126:
`1 + ρ + ⋯ + ρ^{n−1} = (1 − ρ^n)/(1 − ρ)` for `ρ ≠ 1`. -/
theorem revision_weight_closed_form {ρ : ℝ} (hρ : ρ ≠ 1) (n : ℕ) :
    ∑ j ∈ range n, ρ ^ j = (1 - ρ ^ n) / (1 - ρ) := by
  rw [geom_sum_eq hρ, ← neg_div_neg_eq, neg_sub, neg_sub]

/-- **Consumption change as revised permanent income**, O&R Exercise 4(a), p. 125. With
`G = I = 0`, suppose (2.32) holds at `t` and at `t + 1`, written with the date-`t` forecasts
`F₀ k = E_t Y_{t+1+k}` and date-`t+1` forecasts `F₁ k = E_{t+1} Y_{t+1+k}` (the date-`t` sum split
as `Y_t + (1 + r)^{-1} Σ_k (1 + r)^{-k} F₀ k`, using that `Y_t` is known at `t`), and that the
current account identity `B_{t+1} = (1 + r) B_t + Y_t − C_t` holds. Then
`C_{t+1} − C_t = (r/(1 + r)) Σ_k (1 + r)^{-k} (E_{t+1} − E_t) Y_{t+1+k}`.
The interchange of the difference with the infinite sum is justified by the two summability
hypotheses. -/
theorem consumption_change_revisions {r C0 C1 B0 B1 Y0 : ℝ} {F0 F1 : ℕ → ℝ} (hr : 0 < r)
    (h0 : Summable fun k => disc r ^ k * F0 k) (h1 : Summable fun k => disc r ^ k * F1 k)
    (hC0 : C0 = r / (1 + r) * ((1 + r) * B0 + (Y0 + disc r * ∑' k, disc r ^ k * F0 k)))
    (hC1 : C1 = r / (1 + r) * ((1 + r) * B1 + ∑' k, disc r ^ k * F1 k))
    (hB : B1 = (1 + r) * B0 + Y0 - C0) :
    C1 - C0 = r / (1 + r) * ∑' k, disc r ^ k * (F1 k - F0 k) := by
  have hsub : ∑' k, disc r ^ k * (F1 k - F0 k) =
      ∑' k, disc r ^ k * F1 k - ∑' k, disc r ^ k * F0 k := by
    rw [← h1.tsum_sub h0]; congr 1; funext k; ring
  have hr1 : 1 + r ≠ 0 := by linarith
  rw [hsub, hC1, hB, hC0, PresentValue.disc]
  field_simp
  ring

/-- Present value of the revision weights, used in O&R Exercise 4(c), p. 126: for `ρ ≠ 1` and
`|ρ| < 1 + r`, `Σ_{k ≥ 0} (1 + r)^{-k} (1 + ρ + ⋯ + ρ^k) = (1 + r)²/(r (1 + r − ρ))`. -/
theorem hasSum_revision_weights {r ρ : ℝ} (hr : 0 < r) (hρ : |ρ| < 1 + r) (hρ1 : ρ ≠ 1) :
    HasSum (fun k => disc r ^ k * ∑ j ∈ range (k + 1), ρ ^ j)
      ((1 + r) ^ 2 / (r * (1 + r - ρ))) := by
  have hρ1' : ρ - 1 ≠ 0 := sub_ne_zero.2 hρ1
  have h := ((hasSum_disc_mul_pow hρ).mul_left (ρ / (ρ - 1))).sub
    ((PresentValue.hasSum_disc_pow hr).mul_left (1 / (ρ - 1)))
  have hne := one_add_sub_ne_zero hρ
  convert h using 1
  · funext k
    rw [geom_sum_eq hρ1]
    field_simp
    ring
  · field_simp
    ring

/-- **Consumption innovation via forecast revisions**, O&R Exercise 4(c), p. 126: combining
Exercise 4(a) with the revisions of Exercise 4(b),
`(r/(1 + r)) Σ_k (1 + r)^{-k} (1 + ρ + ⋯ + ρ^k) ε = ((1 + r)/(1 + r − ρ)) ε`. -/
theorem consumption_innovation_from_revisions {r ρ : ℝ} (hr : 0 < r) (hρ : |ρ| < 1 + r)
    (hρ1 : ρ ≠ 1) (e : ℝ) :
    r / (1 + r) * ∑' k, disc r ^ k * ((∑ j ∈ range (k + 1), ρ ^ j) * e) =
      (1 + r) / (1 + r - ρ) * e := by
  have h := (hasSum_revision_weights hr hρ hρ1).mul_right e
  have hr1 : 1 + r ≠ 0 := by linarith
  have hne := one_add_sub_ne_zero hρ
  rw [show (fun k => disc r ^ k * ((∑ j ∈ range (k + 1), ρ ^ j) * e)) =
    fun k => disc r ^ k * (∑ j ∈ range (k + 1), ρ ^ j) * e by funext k; ring, h.tsum_eq]
  field_simp

/-- **Consumption with nonstationary output**, O&R (2.38) with (2.32), p. 84: if output growth
`D` follows `D_{s+1} = ρ D_s + ε_{s+1}` and consumption obeys (2.32) with `G = I = 0`, then
`C_t = r B_t + Y_t + (ρ/(1 + r − ρ)) D_t` almost surely (`ρ ≠ 1`, `|ρ| < 1 + r`). -/
theorem consumption_nonstationary [IsProbabilityMeasure μ] (ℱ : Filtration ℕ m0)
    {B Y D ε C : ℕ → Ω → ℝ} {r ρ : ℝ} (hr : 0 < r) (hρ : |ρ| < 1 + r) (hρ1 : ρ ≠ 1)
    (hY : ∀ s ω, Y (s + 1) ω = Y s ω + D (s + 1) ω)
    (hD : ∀ s ω, D (s + 1) ω = ρ * D s ω + ε (s + 1) ω) (hYa : StronglyAdapted ℱ Y)
    (hDa : StronglyAdapted ℱ D) (hYi : ∀ s, Integrable (Y s) μ)
    (hDi : ∀ s, Integrable (D s) μ) (hεi : ∀ s, Integrable (ε s) μ)
    (hε : ∀ s, μ[ε (s + 1) | ℱ s] =ᵐ[μ] 0) (t : ℕ)
    (hCE : ∀ᵐ ω ∂μ, C t ω =
      r / (1 + r) * ((1 + r) * B t ω + ∑' k, disc r ^ k * μ[Y (t + k) | ℱ t] ω)) :
    ∀ᵐ ω ∂μ, C t ω = r * B t ω + Y t ω + ρ / (1 + r - ρ) * D t ω := by
  have hf : ∀ᵐ ω ∂μ, ∀ k, μ[Y (t + k) | ℱ t] ω =
      Y t ω + (∑ j ∈ range k, ρ ^ (j + 1)) * D t ω :=
    ae_all_iff.2 fun k => nonstationary_forecast ℱ hY hD hYa hDa hYi hDi hεi hε t k
  have hρ1' : ρ - 1 ≠ 0 := sub_ne_zero.2 hρ1
  have hne := one_add_sub_ne_zero hρ
  have hr1 : 1 + r ≠ 0 := by linarith
  filter_upwards [hCE, hf] with ω h1 h2
  have hsum : HasSum (fun k => disc r ^ k * μ[Y (t + k) | ℱ t] ω)
      (Y t ω * ((1 + r) / r) + ρ * D t ω / (ρ - 1) * ((1 + r) / (1 + r - ρ)) -
        ρ * D t ω / (ρ - 1) * ((1 + r) / r)) := by
    have := (((PresentValue.hasSum_disc_pow hr).mul_left (Y t ω)).add
      ((hasSum_disc_mul_pow hρ).mul_left (ρ * D t ω / (ρ - 1)))).sub
      ((PresentValue.hasSum_disc_pow hr).mul_left (ρ * D t ω / (ρ - 1)))
    convert this using 1
    funext k
    rw [h2]
    have hg : ∑ j ∈ range k, ρ ^ (j + 1) = ρ * ((ρ ^ k - 1) / (ρ - 1)) := by
      rw [← geom_sum_eq hρ1, mul_sum]; exact sum_congr rfl fun j _ => pow_succ' ρ j
    rw [hg]
    field_simp
    ring
  rw [h1, hsum.tsum_eq]
  field_simp
  ring

/-- **Consumption innovation with nonstationary output**, O&R Exercise 4(c), p. 126: with the
consumption rule of `consumption_nonstationary` at `t` and `t + 1` and the current account
identity, `C_{t+1} − C_t = ((1 + r)/(1 + r − ρ)) ε_{t+1}`. For `0 < ρ < 1` the coefficient exceeds
one (`consumption_more_volatile`). -/
theorem consumption_innovation_nonstationary {r ρ B0 B1 Y0 Y1 D0 D1 C0 C1 e : ℝ}
    (hne : 1 + r - ρ ≠ 0)
    (hC0 : C0 = r * B0 + Y0 + ρ / (1 + r - ρ) * D0)
    (hC1 : C1 = r * B1 + Y1 + ρ / (1 + r - ρ) * D1)
    (hB : B1 = (1 + r) * B0 + Y0 - C0) (hY : Y1 = Y0 + D1) (hD : D1 = ρ * D0 + e) :
    C1 - C0 = (1 + r) / (1 + r - ρ) * e := by
  rw [hC1, hB, hY, hD, hC0]
  field_simp
  ring

/-- Almost-sure form of Exercise 4(c), p. 126: under the hypotheses of
`consumption_nonstationary` at dates `t` and `t + 1`, and the current account identity
`B_{t+1} = (1 + r) B_t + Y_t − C_t`, `C_{t+1} − C_t = ((1 + r)/(1 + r − ρ)) ε_{t+1}` a.s. -/
theorem consumption_innovation_nonstationary_ae [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ m0) {B Y D ε C : ℕ → Ω → ℝ} {r ρ : ℝ} (hr : 0 < r) (hρ : |ρ| < 1 + r)
    (hρ1 : ρ ≠ 1) (hY : ∀ s ω, Y (s + 1) ω = Y s ω + D (s + 1) ω)
    (hD : ∀ s ω, D (s + 1) ω = ρ * D s ω + ε (s + 1) ω) (hYa : StronglyAdapted ℱ Y)
    (hDa : StronglyAdapted ℱ D) (hYi : ∀ s, Integrable (Y s) μ)
    (hDi : ∀ s, Integrable (D s) μ) (hεi : ∀ s, Integrable (ε s) μ)
    (hε : ∀ s, μ[ε (s + 1) | ℱ s] =ᵐ[μ] 0) (t : ℕ)
    (hB : ∀ ω, B (t + 1) ω = (1 + r) * B t ω + Y t ω - C t ω)
    (hCE : ∀ s, ∀ᵐ ω ∂μ, C s ω =
      r / (1 + r) * ((1 + r) * B s ω + ∑' k, disc r ^ k * μ[Y (s + k) | ℱ s] ω)) :
    ∀ᵐ ω ∂μ, C (t + 1) ω - C t ω = (1 + r) / (1 + r - ρ) * ε (t + 1) ω := by
  filter_upwards [consumption_nonstationary ℱ hr hρ hρ1 hY hD hYa hDa hYi hDi hεi hε t (hCE t),
    consumption_nonstationary ℱ hr hρ hρ1 hY hD hYa hDa hYi hDi hεi hε (t + 1) (hCE (t + 1))]
    with ω h0 h1
  exact consumption_innovation_nonstationary (one_add_sub_ne_zero hρ) h0 h1 (hB ω) (hY t ω)
    (hD t ω)

/-- **Current account with nonstationary output**, O&R Exercise 4(d), p. 126, and the claim at the
end of §2.3.3, p. 84. With the consumption rule `C_s = r B_s + Y_s + (ρ/(1 + r − ρ)) D_s` at `t` and
`t + 1`, `CA_s = r B_s + Y_s − C_s` satisfies `CA_t = −(ρ/(1 + r − ρ)) D_t` and
`CA_{t+1} = ρ CA_t − (ρ/(1 + r − ρ)) ε_{t+1}`: the response to an innovation is
`−ρ/(1 + r − ρ)`. -/
theorem current_account_nonstationary {r ρ B0 B1 Y0 Y1 D0 D1 C0 C1 e : ℝ}
    (hC0 : C0 = r * B0 + Y0 + ρ / (1 + r - ρ) * D0)
    (hC1 : C1 = r * B1 + Y1 + ρ / (1 + r - ρ) * D1) (hD : D1 = ρ * D0 + e) :
    r * B0 + Y0 - C0 = -(ρ / (1 + r - ρ)) * D0 ∧
      r * B1 + Y1 - C1 = ρ * (r * B0 + Y0 - C0) - ρ / (1 + r - ρ) * e := by
  constructor
  · rw [hC0]; ring
  · rw [hC1, hC0, hD]; ring

/-- Signs in O&R Exercise 4(c)–(d), p. 126: for `0 < ρ` and `|ρ| < 1 + r`, a positive output
innovation produces a current account deficit (`−ρ/(1 + r − ρ) < 0`) and a consumption innovation
larger than the output innovation (`(1 + r)/(1 + r − ρ) > 1`). -/
theorem consumption_more_volatile {r ρ : ℝ} (hρ0 : 0 < ρ) (hρ : |ρ| < 1 + r) :
    -(ρ / (1 + r - ρ)) < 0 ∧ 1 < (1 + r) / (1 + r - ρ) := by
  have h : 0 < 1 + r - ρ := by have := le_abs_self ρ; linarith
  refine ⟨neg_neg_of_pos (div_pos hρ0 h), ?_⟩
  rw [one_lt_div h]
  linarith

/-- Conditional covariance, O&R footnote 23, p. 86:
`Cov(X, Y | m) = E[XY | m] − E[X | m] E[Y | m]`. With `m = ℱ t` this is the book's `Cov_t`. -/
noncomputable def condCov (μ : Measure Ω) (m : MeasurableSpace Ω) (X Y : Ω → ℝ) : Ω → ℝ :=
  μ[X * Y | m] - μ[X | m] * μ[Y | m]

/-- O&R footnote 23, p. 86: `E(XY) = E(X) E(Y) + Cov(X, Y)`, in conditional form. -/
theorem condExp_mul_eq_add_condCov (m : MeasurableSpace Ω) (X Y : Ω → ℝ) :
    μ[X * Y | m] = μ[X | m] * μ[Y | m] + condCov μ m X Y := by
  simp [condCov]

/-- O&R footnote 23, p. 86: adding a constant does not change a covariance,
`Cov(a₀ + X, Y) = Cov(X, Y)` (conditional version, almost surely). -/
theorem condCov_const_add [IsProbabilityMeasure μ] {m : MeasurableSpace Ω} (hm : m ≤ m0)
    (a0 : ℝ) {X Y : Ω → ℝ} (hX : Integrable X μ) (hY : Integrable Y μ)
    (hXY : Integrable (X * Y) μ) :
    condCov μ m (fun ω => a0 + X ω) Y =ᵐ[μ] condCov μ m X Y := by
  have h1 : (fun ω => a0 + X ω) * Y = a0 • Y + X * Y := by
    funext ω; simp; ring
  have h2 : (fun ω => a0 + X ω) = (fun _ => a0) + X := rfl
  unfold condCov
  rw [h1, h2]
  filter_upwards [condExp_add (hY.smul a0) hXY m, condExp_smul (μ := μ) a0 Y m,
    condExp_add (integrable_const a0) hX m] with ω e1 e2 e3
  simp only [Pi.sub_apply, Pi.mul_apply]
  rw [e1, e3, Pi.add_apply, e2, Pi.add_apply, condExp_const hm]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- **Risky capital**, O&R (2.40), p. 86. Let `m` be the date-`t` information, `u'(C_t)` known
at `t` and nonzero, `W = u'(C_{t+1})`, `R = A_{t+1} F'(K_{t+1})`, and `M = u'(C_{t+1})/u'(C_t)`.
Given the bond Euler equation (2.29) `E_t u'(C_{t+1}) = u'(C_t)/((1 + r) β)` and the capital
Euler equation `u'(C_t) = E_t{[1 + R] β u'(C_{t+1})}` (both taken as hypotheses), and
`(1 + r) β = 1`, we get `E_t R = r − Cov_t(R, M)`. -/
theorem risky_capital_return {m : MeasurableSpace Ω} {up : ℝ → ℝ} {Ct Ct1 R : Ω → ℝ} {r β : ℝ}
    (hrβ : (1 + r) * β = 1)
    (hpos : ∀ ω, up (Ct ω) ≠ 0) (hmeas : StronglyMeasurable[m] fun ω => up (Ct ω))
    (hW : Integrable (fun ω => up (Ct1 ω)) μ)
    (hRW : Integrable (fun ω => R ω * up (Ct1 ω)) μ)
    (hM : Integrable (fun ω => up (Ct1 ω) / up (Ct ω)) μ)
    (hRM : Integrable (fun ω => R ω * (up (Ct1 ω) / up (Ct ω))) μ)
    (hbond : μ[fun ω => up (Ct1 ω) | m] =ᵐ[μ] fun ω => up (Ct ω) / ((1 + r) * β))
    (hcap : μ[fun ω => (1 + R ω) * (β * up (Ct1 ω)) | m] =ᵐ[μ] fun ω => up (Ct ω)) :
    μ[R | m] =ᵐ[μ] fun ω => r - condCov μ m R (fun ω => up (Ct1 ω) / up (Ct ω)) ω := by
  have hβ : β ≠ 0 := by rintro rfl; simp at hrβ
  set W : Ω → ℝ := fun ω => up (Ct1 ω) with hWdef
  set q : Ω → ℝ := fun ω => (up (Ct ω))⁻¹ with hqdef
  have hq : StronglyMeasurable[m] q := hmeas.inv₀
  have hMq : (fun ω => up (Ct1 ω) / up (Ct ω)) = q * W := by
    funext ω; simp [hqdef, hWdef, div_eq_inv_mul]
  have hRMq : R * (fun ω => up (Ct1 ω) / up (Ct ω)) = q * (R * W) := by
    funext ω; simp [hqdef, hWdef, div_eq_inv_mul]; ring
  have hcapf : (fun ω => (1 + R ω) * (β * up (Ct1 ω))) = β • W + β • (R * W) := by
    funext ω; simp [hWdef]; ring
  rw [hcapf] at hcap
  have hRW' : Integrable (R * W) μ := hRW
  have eM := condExp_mul_of_stronglyMeasurable_left hq (hMq ▸ hM) hW
  have eRM := condExp_mul_of_stronglyMeasurable_left hq (hRMq ▸ hRM) hRW'
  unfold condCov
  rw [hRMq, hMq]
  filter_upwards [eM, eRM, hbond, hcap, condExp_add (hW.smul β) (hRW'.smul β) m,
    condExp_smul (μ := μ) β W m, condExp_smul (μ := μ) β (R * W) m]
    with ω h1 h2 h3 h4 h5 h6 h7
  rw [h5, Pi.add_apply, h6, h7] at h4
  simp only [Pi.smul_apply, smul_eq_mul] at h4
  simp only [Pi.sub_apply, Pi.mul_apply]
  rw [h1, h2, Pi.mul_apply, Pi.mul_apply]
  have h3' : μ[W | m] ω = up (Ct ω) := by rw [h3, hrβ, div_one]
  rw [h3'] at h4 ⊢
  have hp := hpos ω
  have hRWv : μ[R * W | m] ω = up (Ct ω) / β - up (Ct ω) := by
    field_simp; linarith
  rw [hRWv]
  simp only [hqdef]
  have hr : r = 1 / β - 1 := by field_simp; linarith
  rw [hr]
  field_simp
  ring

/-- O&R §2.3.6, p. 94: if `u''' ≥ 0` on an open convex set then marginal utility `u'` is convex
there (`u''` is the derivative of `u'` and `u'''` that of `u''`). -/
theorem convexOn_of_third_deriv_nonneg {D : Set ℝ} (hD : Convex ℝ D) (hDo : IsOpen D)
    {up upp uppp : ℝ → ℝ} (h2 : ∀ x ∈ D, HasDerivAt up (upp x) x)
    (h3 : ∀ x ∈ D, HasDerivAt upp (uppp x) x) (h3nn : ∀ x ∈ D, 0 ≤ uppp x) :
    ConvexOn ℝ D up := by
  refine convexOn_of_hasDerivWithinAt2_nonneg (f' := upp) (f'' := uppp) hD
    (fun x hx => (h2 x hx).continuousAt.continuousWithinAt) (fun x hx => ?_)
    (fun x hx => ?_) (fun x hx => ?_)
  · rw [hDo.interior_eq] at hx ⊢; exact (h2 x hx).hasDerivWithinAt
  · rw [hDo.interior_eq] at hx ⊢; exact (h3 x hx).hasDerivWithinAt
  · rw [hDo.interior_eq] at hx; exact h3nn x hx

/-- **Isoelastic prudence**, O&R footnote 32, p. 95: for `u'(C) = C^{−1/σ}` with `σ > 0` and
`C > 0`, `u''(C) = −(1/σ) C^{−1/σ−1}` and `u'''(C) = (1/σ)(1 + 1/σ) C^{−1/σ−2} > 0`. -/
theorem crra_third_derivative {σ C : ℝ} (hσ : 0 < σ) (hC : 0 < C) :
    HasDerivAt (fun c : ℝ => c ^ (-1 / σ)) (-1 / σ * C ^ (-1 / σ - 1)) C ∧
      HasDerivAt (fun c : ℝ => -1 / σ * c ^ (-1 / σ - 1))
        (1 / σ * (1 + 1 / σ) * C ^ (-1 / σ - 2)) C ∧
      0 < 1 / σ * (1 + 1 / σ) * C ^ (-1 / σ - 2) := by
  refine ⟨Real.hasDerivAt_rpow_const (Or.inl hC.ne'), ?_, ?_⟩
  · have h := (Real.hasDerivAt_rpow_const (p := -1 / σ - 1) (Or.inl hC.ne')).const_mul (-1 / σ)
    convert h using 1
    rw [show -1 / σ - 1 - 1 = -1 / σ - 2 by ring]
    ring
  · have := Real.rpow_pos_of_pos hC (-1 / σ - 2)
    positivity

/-- O&R §2.3.6 and footnote 32, pp. 94–95: isoelastic marginal utility `C^{−1/σ}` is convex on
`C > 0`. -/
theorem crra_marginal_utility_convex {σ : ℝ} (hσ : 0 < σ) :
    ConvexOn ℝ (Set.Ioi 0) fun c : ℝ => c ^ (-1 / σ) :=
  convexOn_of_third_deriv_nonneg (convex_Ioi 0) isOpen_Ioi
    (fun _ hx => (crra_third_derivative hσ hx).1) (fun _ hx => (crra_third_derivative hσ hx).2.1)
    (fun _ hx => (crra_third_derivative hσ hx).2.2.le)

/-- **Jensen and precautionary saving**, O&R §2.3.6, p. 94: if marginal utility is convex (and
continuous) on a closed convex set containing next period's consumption, then
`E_t u'(C_{t+1}) ≥ u'(E_t C_{t+1})` almost surely (conditional Jensen). -/
theorem condExp_marginal_utility_ge [IsProbabilityMeasure μ] {m : MeasurableSpace Ω}
    (hm : m ≤ m0) {up : ℝ → ℝ} {s : Set ℝ} (hconv : ConvexOn ℝ s up) (hcont : ContinuousOn up s)
    (hs : IsClosed s) {C : Ω → ℝ} (hCs : ∀ᵐ ω ∂μ, C ω ∈ s) (hC : Integrable C μ)
    (hupC : Integrable (up ∘ C) μ) :
    up ∘ μ[C | m] ≤ᵐ[μ] μ[up ∘ C | m] :=
  hconv.map_condExp_le hm hcont.lowerSemicontinuousOn hCs hs hC hupC

/-- **A mean-preserving spread raises expected marginal utility**, O&R §2.3.6, p. 94. If
`C' = C + η` where `C` is known given the information `m` and `E[η | m] = 0` (a mean-preserving
spread in the sense of added noise), and `u'` is convex and continuous on a closed convex set
containing `C'`, then `E u'(C) ≤ E u'(C + η)`. -/
theorem mps_raises_expected_marginal_utility [IsProbabilityMeasure μ] {m : MeasurableSpace Ω}
    (hm : m ≤ m0) {up : ℝ → ℝ} {s : Set ℝ} (hconv : ConvexOn ℝ s up) (hcont : ContinuousOn up s)
    (hs : IsClosed s) {C η : Ω → ℝ} (hCm : StronglyMeasurable[m] C) (hη : μ[η | m] =ᵐ[μ] 0)
    (hCs : ∀ᵐ ω ∂μ, C ω + η ω ∈ s) (hC : Integrable C μ) (hηi : Integrable η μ)
    (hupC : Integrable (up ∘ C) μ) (hupCη : Integrable (up ∘ (C + η)) μ) :
    ∫ ω, up (C ω) ∂μ ≤ ∫ ω, up (C ω + η ω) ∂μ := by
  have hJ := condExp_marginal_utility_ge (C := C + η) hm hconv hcont hs hCs (hC.add hηi) hupCη
  have hmean : μ[C + η | m] =ᵐ[μ] C := by
    filter_upwards [condExp_add hC hηi m, hη] with ω h1 h2
    rw [h1, Pi.add_apply, h2, condExp_of_stronglyMeasurable hm hCm hC]
    simp
  have hle : up ∘ C ≤ᵐ[μ] μ[up ∘ (C + η) | m] := by
    filter_upwards [hJ, hmean] with ω h1 h2
    simpa [h2] using h1
  calc ∫ ω, up (C ω) ∂μ ≤ ∫ ω, μ[up ∘ (C + η) | m] ω ∂μ :=
        integral_mono_ae hupC integrable_condExp hle
    _ = ∫ ω, up (C ω + η ω) ∂μ := by rw [integral_condExp hm]; rfl

/-- **Precautionary saving in a two-period model**, O&R §2.3.6, pp. 94–95. Wealth `W` is split
into consumption `c` today and savings, so tomorrow's consumption is `(1 + r)(W − c) + Y` with
random income `Y`. Let `c` solve the Euler equation (2.29) under income `Y`, and `c'` solve it
under the riskier income `Y + η` with `E[η | m] = 0` and `Y` known given `m` (a mean-preserving
spread). If `u'` is strictly decreasing (`u'' < 0`), convex (`u''' ≥ 0`) and continuous, then
`c' ≤ c`: more income risk means more saving. The Euler equations are hypotheses. -/
theorem precautionary_saving_two_period [IsProbabilityMeasure μ] {m : MeasurableSpace Ω}
    (hm : m ≤ m0) {up : ℝ → ℝ} (hanti : StrictAnti up) (hconv : ConvexOn ℝ Set.univ up)
    (hcont : Continuous up) {r β W c c' : ℝ} (hr1 : 0 < 1 + r) (hβ : 0 < β) {Y η : Ω → ℝ}
    (hYm : StronglyMeasurable[m] Y) (hη : μ[η | m] =ᵐ[μ] 0) (hYi : Integrable Y μ)
    (hηi : Integrable η μ)
    (hi : Integrable (fun ω => up ((1 + r) * (W - c) + Y ω)) μ)
    (hi' : Integrable (fun ω => up ((1 + r) * (W - c') + Y ω)) μ)
    (hi'' : Integrable (fun ω => up ((1 + r) * (W - c') + Y ω + η ω)) μ)
    (heuler : up c = (1 + r) * β * ∫ ω, up ((1 + r) * (W - c) + Y ω) ∂μ)
    (heuler' : up c' = (1 + r) * β * ∫ ω, up ((1 + r) * (W - c') + Y ω + η ω) ∂μ) :
    c' ≤ c := by
  by_contra hcc
  push Not at hcc
  have h1 : up c' < up c := hanti hcc
  have hmps := mps_raises_expected_marginal_utility (μ := μ) hm hconv hcont.continuousOn
    isClosed_univ (C := fun ω => (1 + r) * (W - c') + Y ω) (η := η)
    (stronglyMeasurable_const.add hYm) hη (ae_of_all _ fun _ => Set.mem_univ _)
    ((integrable_const _).add hYi) hηi hi' hi''
  have hmono : ∫ ω, up ((1 + r) * (W - c) + Y ω) ∂μ ≤
      ∫ ω, up ((1 + r) * (W - c') + Y ω) ∂μ := by
    refine integral_mono hi hi' fun ω => hanti.antitone ?_
    have : (1 + r) * (W - c') ≤ (1 + r) * (W - c) :=
      mul_le_mul_of_nonneg_left (by linarith) hr1.le
    linarith
  have hk : 0 < (1 + r) * β := mul_pos hr1 hβ
  have : up c ≤ up c' := by
    rw [heuler, heuler']
    exact mul_le_mul_of_nonneg_left (hmono.trans hmps) hk.le
  linarith

/-- **Hall's random walk under lognormality**, O&R Exercise 3, p. 125. With isoelastic marginal
utility `u'(C) = C^{−1/σ}`, `(1 + r) β = 1`, and `log C_{t+1}` conditionally normal given the
date-`t` information `m` with conditional mean `μ_t` and variance `v_t` (hypotheses: the
conditional moment generating function `E_t exp(θ log C_{t+1}) = exp(θ μ_t + θ² v_t / 2)` and
`E_t log C_{t+1} = μ_t`), the Euler equation (2.29) gives
`E_t log C_{t+1} − log C_t = v_t/(2σ)`.
The book's "constant drift" requires, in addition, a constant conditional variance `v_t`. -/
theorem lognormal_consumption_drift {m : MeasurableSpace Ω} {Ct Ct1 mean var : Ω → ℝ}
    {σ r β : ℝ} (hσ : 0 < σ) (hrβ : (1 + r) * β = 1) (hCt : ∀ ω, 0 < Ct ω)
    (hCt1 : ∀ ω, 0 < Ct1 ω)
    (heuler : μ[fun ω => Ct1 ω ^ (-1 / σ) | m] =ᵐ[μ] fun ω => Ct ω ^ (-1 / σ) / ((1 + r) * β))
    (hmgf : ∀ θ : ℝ, μ[fun ω => Real.exp (θ * Real.log (Ct1 ω)) | m] =ᵐ[μ]
      fun ω => Real.exp (θ * mean ω + θ ^ 2 * var ω / 2))
    (hmean : μ[fun ω => Real.log (Ct1 ω) | m] =ᵐ[μ] mean) :
    μ[fun ω => Real.log (Ct1 ω) | m] - (fun ω => Real.log (Ct ω)) =ᵐ[μ]
      fun ω => var ω / (2 * σ) := by
  have hf : (fun ω => Ct1 ω ^ (-1 / σ)) =
      fun ω => Real.exp (-1 / σ * Real.log (Ct1 ω)) := by
    funext ω; rw [Real.rpow_def_of_pos (hCt1 ω), mul_comm]
  rw [hf] at heuler
  filter_upwards [heuler, hmgf (-1 / σ), hmean] with ω h1 h2 h3
  rw [h1, hrβ, div_one, Real.rpow_def_of_pos (hCt ω)] at h2
  have h4 := Real.exp_injective h2
  rw [Pi.sub_apply, h3]
  field_simp at h4 ⊢
  linarith

/-- **Random walk with constant drift**, O&R Exercise 3, p. 125: if in addition the conditional
variance is a constant `v` and `log C_t` is known at `t`, then
`E_t [log C_{t+1} − log C_t − v/(2σ)] = 0`, i.e. `log C` is a random walk (martingale) with drift
`v/(2σ)`. -/
theorem lognormal_random_walk_drift [IsProbabilityMeasure μ] {m : MeasurableSpace Ω}
    (hm : m ≤ m0) {Ct Ct1 mean : Ω → ℝ} {σ r β v : ℝ} (hσ : 0 < σ) (hrβ : (1 + r) * β = 1)
    (hCt : ∀ ω, 0 < Ct ω) (hCt1 : ∀ ω, 0 < Ct1 ω)
    (hLm : StronglyMeasurable[m] fun ω => Real.log (Ct ω))
    (hL : Integrable (fun ω => Real.log (Ct ω)) μ)
    (hL1 : Integrable (fun ω => Real.log (Ct1 ω)) μ)
    (heuler : μ[fun ω => Ct1 ω ^ (-1 / σ) | m] =ᵐ[μ] fun ω => Ct ω ^ (-1 / σ) / ((1 + r) * β))
    (hmgf : ∀ θ : ℝ, μ[fun ω => Real.exp (θ * Real.log (Ct1 ω)) | m] =ᵐ[μ]
      fun ω => Real.exp (θ * mean ω + θ ^ 2 * v / 2))
    (hmean : μ[fun ω => Real.log (Ct1 ω) | m] =ᵐ[μ] mean) :
    μ[fun ω => Real.log (Ct1 ω) - Real.log (Ct ω) - v / (2 * σ) | m] =ᵐ[μ] 0 := by
  have hd := lognormal_consumption_drift (var := fun _ => v) hσ hrβ hCt hCt1 heuler hmgf hmean
  have hf : (fun ω => Real.log (Ct1 ω) - Real.log (Ct ω) - v / (2 * σ)) =
      (fun ω => Real.log (Ct1 ω)) - (fun ω => Real.log (Ct ω)) - fun _ => v / (2 * σ) := rfl
  rw [hf]
  filter_upwards [condExp_sub (hL1.sub hL) (integrable_const (v / (2 * σ))) m,
    condExp_sub hL1 hL m, hd] with ω h1 h2 h3
  rw [h1, Pi.sub_apply, h2, condExp_const hm, condExp_of_stronglyMeasurable hm hLm hL]
  simp only [Pi.sub_apply] at h3 ⊢
  rw [h3]
  simp

/-- **Stochastic Euler equation from dynamic programming**, O&R Supplement A.3, p. 722: the
first-order condition of the stochastic Bellman equation,
`u'(C_t) = (1 + r) β E_t J'_{t+1}(W_{t+1})`, and the envelope condition
`u'(C_{t+1}) = J'_{t+1}(W_{t+1})` (both hypotheses; `J'` may depend on the date-`t+1` state) give
the stochastic Euler equation (2.29), `u'(C_t) = (1 + r) β E_t u'(C_{t+1})`. -/
theorem euler_of_bellman {m : MeasurableSpace Ω} {up : ℝ → ℝ} {Jp : Ω → ℝ → ℝ}
    {Ct Ct1 W1 : Ω → ℝ} {r β : ℝ}
    (hfoc : (fun ω => up (Ct ω)) =ᵐ[μ] fun ω => (1 + r) * β * μ[fun ω => Jp ω (W1 ω) | m] ω)
    (henv : ∀ᵐ ω ∂μ, up (Ct1 ω) = Jp ω (W1 ω)) :
    (fun ω => up (Ct ω)) =ᵐ[μ] fun ω => (1 + r) * β * μ[fun ω => up (Ct1 ω) | m] ω := by
  filter_upwards [hfoc, condExp_congr_ae (m := m) henv] with ω h1 h2
  rw [h1, h2]

end ObstfeldRogoff.SmallOpenEconomyDynamics.StochasticConsumption
