/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity

/-!
# Exchange-rate facts: the precise statistical and arithmetic content

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §9.1,
pp. 605–608 (Figures 9.1–9.3, Mussa's volatility facts), §9.3.1, pp. 623–624 (the half-life
of PPP deviations), §9.3.3, p. 628 (the Great Depression regression and Figure 9.10), and the
CBI regression of §9.5.3, p. 646.

The empirical claims of §9.1 are not theorems, but they rest on the identity
`q = e + p* − p` (eq. (4), p. 609). For any finite sample or finite-state distribution this
implies exact second-moment facts:
* `|sd(q) − sd(e)| ≤ sd(p* − p)` (the standard deviation is a seminorm);
* `corr(q, e) ≥ (sd e − sd(p* − p))/sd q`;
so when relative price levels are an order of magnitude less volatile than the nominal rate,
`0.9 sd e ≤ sd q ≤ 1.1 sd e` and `corr(q, e) ≥ 9/11`: the book's "the short-run volatility
of real exchange rates is very similar to that of nominal exchange rates" (p. 606). The same
bounds apply to first differences (Figure 9.2). Under a peg, `sd q = sd(p* − p)`.

Arithmetic (all with explicit numerical bounds):
* the half-life `X = ln 2/(−ln 0.85)` solves `0.85^X = 1/2` uniquely and lies in
  `(4.264, 4.266)`, so it rounds to 4.3 (the book's "roughly 4.2" understates it, p. 624);
* the p. 628 regression: `t = 0.49/0.23 ≈ 2.13`; the elasticity reading "1% ⇒ 0.5%" is right;
  but read literally (logs of ratios) the intercept 2.45 predicts IP ratios above 2.9 for every
  WPI ratio in Figure 9.10's range, while the figure's IP ratios are all at most 1.5. Read as
  logs of the 100-based indices of Figure 9.10 the equation is consistent (fitted indices in
  `[50, 150]` over the plotted WPI range): the variables are mislabelled;
* the CBI regression of p. 646.
-/

namespace ObstfeldRogoff.NominalRigidities.ExchangeRateFacts

open Finset Real

variable {S : Type} [Fintype S]

/-! ### Moments of a finite distribution -/

/-- O&R §9.1: the mean of a variable under weights `p` (a sample or a finite distribution). -/
def mean (p f : S → ℝ) : ℝ := ∑ i, p i * f i

/-- O&R §9.1: the covariance under weights `p`. -/
def cov (p f g : S → ℝ) : ℝ := ∑ i, p i * ((f i - mean p f) * (g i - mean p g))

/-- O&R §9.1: the variance under weights `p`. -/
def var (p f : S → ℝ) : ℝ := cov p f f

/-- O&R §9.1: the standard deviation (volatility) under weights `p`. -/
noncomputable def sd (p f : S → ℝ) : ℝ := √(var p f)

/-- O&R (4), p. 609: the (log) real exchange rate `q = e + p* − p`. -/
def realRate (e pstar pdom : S → ℝ) : S → ℝ := fun i => e i + (pstar i - pdom i)

/-- The mean is additive (O&R §9.1 background). -/
theorem mean_add (p f g : S → ℝ) : mean p (fun i => f i + g i) = mean p f + mean p g := by
  unfold mean
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The mean is homogeneous (O&R §9.1 background). -/
theorem mean_const_mul (p f : S → ℝ) (t : ℝ) : mean p (fun i => t * f i) = t * mean p f := by
  unfold mean
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The covariance is symmetric (O&R §9.1 background). -/
theorem cov_comm (p f g : S → ℝ) : cov p f g = cov p g f := by
  unfold cov
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The variance is nonnegative for nonnegative weights (O&R §9.1 background). -/
theorem var_nonneg {p : S → ℝ} (hp : ∀ i, 0 ≤ p i) (f : S → ℝ) : 0 ≤ var p f := by
  unfold var cov
  exact Finset.sum_nonneg fun i _ => mul_nonneg (hp i) (mul_self_nonneg _)

/-- The covariance is additive in its first argument (O&R §9.1 background). -/
theorem cov_add_left (p f g h : S → ℝ) :
    cov p (fun i => f i + g i) h = cov p f h + cov p g h := by
  unfold cov
  rw [mean_add, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The variance of `f + t g` is the quadratic `var f + 2 t cov(f, g) + t² var g`
(O&R §9.1 background). -/
theorem var_add_smul (p f g : S → ℝ) (t : ℝ) :
    var p (fun i => f i + t * g i) = var p f + 2 * t * cov p f g + t ^ 2 * var p g := by
  unfold var cov
  have hm : mean p (fun i => f i + t * g i) = mean p f + t * mean p g := by
    rw [mean_add, mean_const_mul]
  rw [hm]
  have hs : ∀ i, p i * ((f i + t * g i - (mean p f + t * mean p g)) *
      (f i + t * g i - (mean p f + t * mean p g))) =
      p i * ((f i - mean p f) * (f i - mean p f)) +
        2 * t * (p i * ((f i - mean p f) * (g i - mean p g))) +
        t ^ 2 * (p i * ((g i - mean p g) * (g i - mean p g))) := fun i => by ring
  rw [Finset.sum_congr rfl fun i _ => hs i, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum]

/-- The variance of a sum: `var(e + x) = var e + 2 cov(e, x) + var x` (O&R §9.1). -/
theorem var_add (p e x : S → ℝ) :
    var p (fun i => e i + x i) = var p e + 2 * cov p e x + var p x := by
  have := var_add_smul p e x 1
  simp only [one_mul, one_pow] at this
  rw [this]
  ring

/-- Cauchy–Schwarz for the covariance: `cov(f, g)² ≤ var f · var g` (O&R §9.1). -/
theorem cov_sq_le {p : S → ℝ} (hp : ∀ i, 0 ≤ p i) (f g : S → ℝ) :
    cov p f g ^ 2 ≤ var p f * var p g := by
  have h : ∀ t : ℝ, 0 ≤ var p g * (t * t) + 2 * cov p f g * t + var p f := by
    intro t
    have := var_nonneg hp (fun i => f i + t * g i)
    rw [var_add_smul] at this
    linarith
  have hd := discrim_le_zero h
  unfold discrim at hd
  linarith

/-- `|cov(f, g)| ≤ sd f · sd g` (O&R §9.1). -/
theorem abs_cov_le {p : S → ℝ} (hp : ∀ i, 0 ≤ p i) (f g : S → ℝ) :
    |cov p f g| ≤ sd p f * sd p g := by
  unfold sd
  rw [← Real.sqrt_mul (var_nonneg hp f)]
  exact Real.abs_le_sqrt (cov_sq_le hp f g)

/-- `sd f² = var f` (O&R §9.1 background). -/
theorem sd_sq {p : S → ℝ} (hp : ∀ i, 0 ≤ p i) (f : S → ℝ) : sd p f ^ 2 = var p f :=
  Real.sq_sqrt (var_nonneg hp f)

/-- `sd f ≥ 0` (O&R §9.1 background). -/
theorem sd_nonneg (p f : S → ℝ) : 0 ≤ sd p f := Real.sqrt_nonneg _

/-- O&R §9.1: the volatility of a sum is at most the sum of volatilities,
`sd(e + x) ≤ sd e + sd x`. -/
theorem sd_add_le {p : S → ℝ} (hp : ∀ i, 0 ≤ p i) (e x : S → ℝ) :
    sd p (fun i => e i + x i) ≤ sd p e + sd p x := by
  have h1 := var_add p e x
  have h2 := abs_cov_le hp e x
  have h3 := le_abs_self (cov p e x)
  have he := sd_sq hp e
  have hx := sd_sq hp x
  have hq : var p (fun i => e i + x i) ≤ (sd p e + sd p x) ^ 2 := by nlinarith
  calc sd p (fun i => e i + x i) = √(var p (fun i => e i + x i)) := rfl
    _ ≤ √((sd p e + sd p x) ^ 2) := Real.sqrt_le_sqrt hq
    _ = sd p e + sd p x := Real.sqrt_sq (add_nonneg (sd_nonneg p e) (sd_nonneg p x))

/-- O&R §9.1: `|sd e − sd x| ≤ sd(e + x)`. -/
theorem abs_sd_sub_le {p : S → ℝ} (hp : ∀ i, 0 ≤ p i) (e x : S → ℝ) :
    |sd p e - sd p x| ≤ sd p (fun i => e i + x i) := by
  have h1 := var_add p e x
  have h2 := abs_cov_le hp e x
  have h3 := neg_abs_le (cov p e x)
  have he := sd_sq hp e
  have hx := sd_sq hp x
  have hq : (sd p e - sd p x) ^ 2 ≤ var p (fun i => e i + x i) := by nlinarith
  exact Real.abs_le_sqrt hq

/-- O&R §9.1 (Figures 9.1–9.3), the volatility triangle inequality: with
`q = e + (p* − p)`, `|sd q − sd e| ≤ sd(p* − p)`. Real and nominal volatility differ by at
most the volatility of relative price levels. -/
theorem abs_sd_real_sub_sd_nominal_le {p : S → ℝ} (hp : ∀ i, 0 ≤ p i) (e pstar pdom : S → ℝ) :
    |sd p (realRate e pstar pdom) - sd p e| ≤ sd p (fun i => pstar i - pdom i) := by
  have h1 := sd_add_le hp e (fun i => pstar i - pdom i)
  have h2 := abs_sd_sub_le hp e (fun i => pstar i - pdom i)
  have h3 := le_abs_self (sd p e - sd p (fun i => pstar i - pdom i))
  unfold realRate
  rw [abs_le]
  constructor <;> linarith

/-- O&R §9.1: `cov(q, e) = var e + cov(p* − p, e)`. -/
theorem cov_real_nominal (p e pstar pdom : S → ℝ) :
    cov p (realRate e pstar pdom) e = var p e + cov p (fun i => pstar i - pdom i) e := by
  unfold realRate var
  exact cov_add_left p e (fun i => pstar i - pdom i) e

/-- O&R §9.1: the correlation of real and nominal rates is at least
`(sd e − sd(p* − p))/sd q` (when both volatilities are positive). -/
theorem corr_real_nominal_ge {p : S → ℝ} (hp : ∀ i, 0 ≤ p i) (e pstar pdom : S → ℝ)
    (he : 0 < sd p e) (hq : 0 < sd p (realRate e pstar pdom)) :
    (sd p e - sd p (fun i => pstar i - pdom i)) / sd p (realRate e pstar pdom) ≤
      cov p (realRate e pstar pdom) e / (sd p (realRate e pstar pdom) * sd p e) := by
  have h1 := cov_real_nominal p e pstar pdom
  have h2 := abs_cov_le hp (fun i => pstar i - pdom i) e
  have h3 := neg_abs_le (cov p (fun i => pstar i - pdom i) e)
  have hv := sd_sq hp e
  have hnum : sd p e * (sd p e - sd p (fun i => pstar i - pdom i)) ≤
      cov p (realRate e pstar pdom) e := by nlinarith
  rw [div_le_div_iff₀ hq (mul_pos hq he)]
  nlinarith

/-- O&R p. 606, "an order of magnitude": if relative price levels are at most a tenth as
volatile as the nominal rate, then `0.9 sd e ≤ sd q ≤ 1.1 sd e` and `corr(q, e) ≥ 9/11`. -/
theorem order_of_magnitude {p : S → ℝ} (hp : ∀ i, 0 ≤ p i) (e pstar pdom : S → ℝ)
    (he : 0 < sd p e) (hx : sd p (fun i => pstar i - pdom i) ≤ sd p e / 10) :
    9 / 10 * sd p e ≤ sd p (realRate e pstar pdom) ∧
      sd p (realRate e pstar pdom) ≤ 11 / 10 * sd p e ∧
      9 / 11 ≤ cov p (realRate e pstar pdom) e / (sd p (realRate e pstar pdom) * sd p e) := by
  have h1 := abs_sd_real_sub_sd_nominal_le hp e pstar pdom
  rw [abs_le] at h1
  have hq1 : 9 / 10 * sd p e ≤ sd p (realRate e pstar pdom) := by linarith
  have hq2 : sd p (realRate e pstar pdom) ≤ 11 / 10 * sd p e := by linarith
  have hq : 0 < sd p (realRate e pstar pdom) := by linarith
  refine ⟨hq1, hq2, ?_⟩
  have h2 := corr_real_nominal_ge hp e pstar pdom he hq
  have h3 : 9 / 11 ≤ (sd p e - sd p (fun i => pstar i - pdom i)) /
      sd p (realRate e pstar pdom) := by
    rw [le_div_iff₀ hq]
    linarith
  linarith

/-- O&R §9.1 (Mussa): under a peg (`e` constant) the real exchange rate is exactly as volatile
as relative price levels, `sd q = sd(p* − p)`. -/
theorem sd_real_of_peg {p : S → ℝ} (hsum : ∑ i, p i = 1) (e pstar pdom : S → ℝ) (c : ℝ)
    (hpeg : ∀ i, e i = c) :
    sd p (realRate e pstar pdom) = sd p (fun i => pstar i - pdom i) := by
  have hme : mean p e = c := by
    unfold mean
    simp only [hpeg, ← Finset.sum_mul, hsum, one_mul]
  have hq : realRate e pstar pdom = fun i => c + (pstar i - pdom i) := by
    funext i
    unfold realRate
    rw [hpeg]
  unfold sd var cov
  rw [hq]
  have hm : mean p (fun i => c + (pstar i - pdom i)) = c + mean p (fun i => pstar i - pdom i) := by
    have := mean_add p (fun _ => c) (fun i => pstar i - pdom i)
    rw [this]
    congr 1
    unfold mean
    rw [← Finset.sum_mul, hsum, one_mul]
  rw [hm]
  congr 1
  exact Finset.sum_congr rfl fun i _ => by ring

/-- O&R Figure 9.2: first differences obey the same identity,
`Δq_t = Δe_t + Δ(p* − p)_t`, so every bound above applies to them. -/
theorem diff_real_rate (e pstar pdom : ℕ → ℝ) (t : ℕ) :
    (e (t + 1) + (pstar (t + 1) - pdom (t + 1))) - (e t + (pstar t - pdom t)) =
      (e (t + 1) - e t) + ((pstar (t + 1) - pstar t) - (pdom (t + 1) - pdom t)) := by
  ring

/-- O&R Figure 9.2: the volatility triangle inequality for first differences over a sample
of `T` periods with weights `w` (e.g. `1/T`). -/
theorem abs_sd_diff_le {T : ℕ} {w : Fin T → ℝ} (hw : ∀ i, 0 ≤ w i) (e pstar pdom : ℕ → ℝ) :
    |sd w (fun t : Fin T => (e (t + 1) + (pstar (t + 1) - pdom (t + 1))) -
        (e t + (pstar t - pdom t))) - sd w (fun t : Fin T => e (t + 1) - e t)| ≤
      sd w (fun t : Fin T => (pstar (t + 1) - pstar t) - (pdom (t + 1) - pdom t)) := by
  have h := abs_sd_real_sub_sd_nominal_le hw (fun t : Fin T => e (t + 1) - e t)
    (fun t : Fin T => pstar (t + 1) - pstar t) (fun t : Fin T => pdom (t + 1) - pdom t)
  have hq : realRate (fun t : Fin T => e (t + 1) - e t)
      (fun t : Fin T => pstar (t + 1) - pstar t) (fun t : Fin T => pdom (t + 1) - pdom t) =
      fun t : Fin T => (e (t + 1) + (pstar (t + 1) - pdom (t + 1))) -
        (e t + (pstar t - pdom t)) := by
    funext t
    unfold realRate
    ring
  rw [hq] at h
  exact h

/-! ### The half-life of PPP deviations (p. 624) -/

/-- O&R p. 624: the AR(1) `q_t = a₀ + ρ q_{t−1}` (deterministic skeleton, i.e. the path of
conditional means): deviations from `a₀/(1 − ρ)` decay as `ρ^t`. -/
theorem ar1_deviation {a0 ρ : ℝ} (hρ : ρ ≠ 1) (q : ℕ → ℝ) (hq : ∀ t, q (t + 1) = a0 + ρ * q t)
    (t : ℕ) : q t - a0 / (1 - ρ) = ρ ^ t * (q 0 - a0 / (1 - ρ)) := by
  have h1 : 1 - ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm hρ)
  induction t with
  | zero => simp
  | succ n ih =>
    rw [hq n, pow_succ]
    have : q n = ρ ^ n * (q 0 - a0 / (1 - ρ)) + a0 / (1 - ρ) := by linarith
    rw [this]
    field_simp
    ring

/-- O&R p. 624: the half-life `X = ln 2/(−ln 0.85)` of the book's estimate `ρ = 0.85`. -/
noncomputable def halfLife : ℝ := Real.log 2 / (-Real.log 0.85)

/-- Numerical bounds `−0.16254 < ln 0.85 < −0.1625` from the Taylor series of `ln(1 − x)` with
explicit remainder (O&R p. 624). -/
theorem log_085_bounds : -0.16254 < Real.log 0.85 ∧ Real.log 0.85 < -0.1625 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := 0.15) (by norm_num [abs_of_pos]) 5
  norm_num [Finset.sum_range_succ, abs_of_pos] at h
  rw [abs_le] at h
  obtain ⟨h1, h2⟩ := h
  constructor <;> norm_num at h1 h2 ⊢ <;> linarith

/-- O&R p. 624: `0.85^X = 1/2`. -/
theorem halfLife_spec : (0.85 : ℝ) ^ halfLife = 1 / 2 := by
  have hL : Real.log 0.85 ≠ 0 := by linarith [log_085_bounds.2]
  rw [Real.rpow_def_of_pos (by norm_num)]
  unfold halfLife
  rw [show Real.log 0.85 * (Real.log 2 / -Real.log 0.85) = -Real.log 2 by field_simp,
    Real.exp_neg, Real.exp_log two_pos]
  norm_num

/-- O&R p. 624: the half-life is the unique solution of `0.85^X = 1/2`. -/
theorem halfLife_unique {Y : ℝ} (hY : (0.85 : ℝ) ^ Y = 1 / 2) : Y = halfLife := by
  have hL : Real.log 0.85 ≠ 0 := by linarith [log_085_bounds.2]
  have h := congrArg Real.log hY
  rw [Real.log_rpow (by norm_num), one_div, Real.log_inv] at h
  unfold halfLife
  field_simp
  linarith

/-- O&R p. 624: `4.264 < X < 4.266`. -/
theorem halfLife_bounds : 4.264 < halfLife ∧ halfLife < 4.266 := by
  obtain ⟨h1, h2⟩ := log_085_bounds
  have h3 := Real.log_two_gt_d9
  have h4 := Real.log_two_lt_d9
  have hL : 0 < -Real.log 0.85 := by linarith
  unfold halfLife
  constructor
  · rw [lt_div_iff₀ hL]
    norm_num at h3 ⊢
    linarith
  · rw [div_lt_iff₀ hL]
    norm_num at h4 ⊢
    linarith

/-- O&R p. 624, imprecision: `X > 4.25`, so to one decimal the half-life is 4.3 years, not
"roughly 4.2". -/
theorem halfLife_gt : 4.25 < halfLife := by linarith [halfLife_bounds.1]

/-- O&R p. 624: in whole years, deviations are still above half after 4 years
(`0.85⁴ ≈ 0.522`) and below half after 5 (`0.85⁵ ≈ 0.444`). -/
theorem halfLife_discrete : (1 : ℝ) / 2 < 0.85 ^ 4 ∧ (0.85 : ℝ) ^ 5 < 1 / 2 := by
  constructor <;> norm_num

/-! ### The Great Depression regression (p. 628, Figure 9.10) -/

/-- O&R p. 628: the fitted line `log(IP₃₅/IP₂₉) = 2.45 + 0.49 log(WPI₃₅/WPI₂₉)`. -/
def gdFit (w : ℝ) : ℝ := 2.45 + 0.49 * w

/-- O&R p. 628: the slope's t-statistic `0.49/0.23` lies in `(2.13, 2.131)`, above 1.96. -/
theorem gd_slope_tstat : (2.13 : ℝ) < 0.49 / 0.23 ∧ (0.49 : ℝ) / 0.23 < 2.131 ∧
    (1.96 : ℝ) < 0.49 / 0.23 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num

/-- O&R p. 628: the intercept's t-statistic `2.45/0.21` lies in `(11.66, 11.67)`. -/
theorem gd_intercept_tstat : (11.66 : ℝ) < 2.45 / 0.21 ∧ (2.45 : ℝ) / 0.21 < 11.67 := by
  constructor <;> norm_num

/-- O&R p. 628, "a 1 percent increase in cumulative inflation is correlated with a 0.5 percent
cumulative increase in industrial production": a rise of 0.01 in log WPI raises fitted log IP
by 0.0049, within 0.0001 of 0.005 (the elasticity reading is correct). -/
theorem gd_elasticity (w : ℝ) : gdFit (w + 0.01) - gdFit w = 0.0049 ∧
    |gdFit (w + 0.01) - gdFit w - 0.005| ≤ 0.0001 := by
  unfold gdFit
  constructor
  · ring
  · rw [show 2.45 + 0.49 * (w + 0.01) - (2.45 + 0.49 * w) - (0.005 : ℝ) = -0.0001 by ring]
    norm_num

/-- O&R p. 628, read literally (logs of ratios), the intercept says a country with zero
cumulative inflation had `IP₃₅/IP₂₉ = e^{2.45} > 11`. -/
theorem gd_ratio_intercept : 11 < Real.exp (gdFit 0) := by
  unfold gdFit
  have he := Real.exp_one_gt_d9
  have hq := Real.quadratic_le_exp_of_nonneg (x := 0.45) (by norm_num)
  have hsplit : Real.exp (2.45 + 0.49 * 0) = Real.exp 1 * Real.exp 1 * Real.exp 0.45 := by
    rw [← Real.exp_add, ← Real.exp_add]
    norm_num
  rw [hsplit]
  have h1 : (2.7182818283 : ℝ) * 2.7182818283 < Real.exp 1 * Real.exp 1 := by
    have : (0 : ℝ) < 2.7182818283 := by norm_num
    nlinarith
  have h2 : (0 : ℝ) < Real.exp 1 * Real.exp 1 := by positivity
  norm_num at hq h1
  nlinarith

/-- O&R p. 628 and Figure 9.10, the mislabelling: read literally, for every WPI ratio at least
0.4 (the left edge of Figure 9.10) the fitted IP ratio exceeds 2.96, while every IP ratio in
Figure 9.10 is at most 1.5. So the regressand cannot be `log(IP₃₅/IP₂₉)`. -/
theorem gd_ratio_reading_inconsistent (W : ℝ) (hW : 0.4 ≤ W) :
    2.96 < Real.exp (gdFit (Real.log W)) ∧ (1.5 : ℝ) < Real.exp (gdFit (Real.log W)) := by
  have hlog : -1 < Real.log 0.4 := by
    rw [neg_lt, ← Real.log_inv, Real.log_lt_iff_lt_exp (by norm_num)]
    have := Real.exp_one_gt_d9
    norm_num
    linarith
  have h1 : Real.log 0.4 ≤ Real.log W := Real.log_le_log (by norm_num) hW
  have h2 : 1.96 < gdFit (Real.log W) := by
    unfold gdFit
    norm_num at h1 hlog ⊢
    linarith
  have h3 := Real.add_one_le_exp (gdFit (Real.log W))
  constructor <;> linarith

/-- O&R p. 628: the regression in logs of 100-based indices, `log(100 I) = 2.45 +
0.49 log(100 W)`, is the ratio regression with intercept `2.45 − 0.51 ln 100` and the same
slope. -/
theorem gd_index_reparam {I W : ℝ} (hI : 0 < I) (hW : 0 < W) :
    Real.log (100 * I) = 2.45 + 0.49 * Real.log (100 * W) ↔
      Real.log I = (2.45 - 0.51 * Real.log 100) + 0.49 * Real.log W := by
  rw [Real.log_mul (by norm_num) hI.ne', Real.log_mul (by norm_num) hW.ne']
  constructor <;> intro h <;> linarith

/-- Numerical bounds `2.3021 < ln 10 < 2.3030` via `ln 10 = 3 ln 2 − ln 0.8` and the series
for `ln 0.8` (used for O&R p. 628). -/
theorem log_ten_bounds : 2.3021 < Real.log 10 ∧ Real.log 10 < 2.3030 := by
  have h := Real.abs_log_sub_add_sum_range_le (x := 0.2) (by norm_num [abs_of_pos]) 4
  norm_num [Finset.sum_range_succ, abs_of_pos] at h
  rw [abs_le] at h
  obtain ⟨h1, h2⟩ := h
  have h10 : Real.log 10 = 3 * Real.log 2 - Real.log 0.8 := by
    rw [show (10 : ℝ) = 2 ^ 3 / 0.8 by norm_num, Real.log_div (by norm_num) (by norm_num),
      Real.log_pow]
    norm_num
  have h3 := Real.log_two_gt_d9
  have h4 := Real.log_two_lt_d9
  rw [h10]
  norm_num at h1 h2 h3 h4 ⊢
  constructor <;> linarith

/-- O&R p. 628: under the index reading the implied ratio-form intercept is
`2.45 − 0.51 ln 100 ∈ (0.10, 0.11)`: zero inflation predicts an IP ratio of about 1.1. -/
theorem gd_index_intercept :
    0.10 < 2.45 - 0.51 * Real.log 100 ∧ 2.45 - 0.51 * Real.log 100 < 0.11 := by
  obtain ⟨h1, h2⟩ := log_ten_bounds
  have h100 : Real.log 100 = 2 * Real.log 10 := by
    rw [show (100 : ℝ) = 10 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [h100]
  constructor <;> linarith

/-- O&R Figure 9.10: under the index reading every WPI index in the plotted range
`[40, 120]` gives a fitted IP index in `[50, 150]`, the plotted range: the index reading is
consistent with the figure. -/
theorem gd_index_reading_consistent (W : ℝ) (hW1 : 40 ≤ W) (hW2 : W ≤ 120) :
    50 ≤ Real.exp (gdFit (Real.log W)) ∧ Real.exp (gdFit (Real.log W)) ≤ 150 := by
  obtain ⟨h10a, h10b⟩ := log_ten_bounds
  have h3 := Real.log_two_gt_d9
  have h4 := Real.log_two_lt_d9
  have hW : 0 < W := by linarith
  have hl1 : Real.log 40 ≤ Real.log W := Real.log_le_log (by norm_num) hW1
  have hl2 : Real.log W ≤ Real.log 120 := Real.log_le_log hW hW2
  have h40 : Real.log 40 = 2 * Real.log 2 + Real.log 10 := by
    rw [show (40 : ℝ) = 2 ^ 2 * 10 by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow]
    norm_num
  have h50 : Real.log 50 = 2 * Real.log 10 - Real.log 2 := by
    rw [show (50 : ℝ) = 10 ^ 2 / 2 by norm_num, Real.log_div (by norm_num) (by norm_num),
      Real.log_pow]
    norm_num
  have h120 : Real.log 120 = Real.log 1.2 + 2 * Real.log 10 := by
    rw [show (120 : ℝ) = 1.2 * 10 ^ 2 by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow]
    norm_num
  have h150 : Real.log 150 = Real.log 1.5 + 2 * Real.log 10 := by
    rw [show (150 : ℝ) = 1.5 * 10 ^ 2 by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow]
    norm_num
  have h12 : Real.log 1.2 ≤ 1.2 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  have h15 : 1 - (1.5 : ℝ)⁻¹ ≤ Real.log 1.5 := Real.one_sub_inv_le_log_of_pos (by norm_num)
  constructor
  · rw [← Real.exp_log (show (0 : ℝ) < 50 by norm_num)]
    apply Real.exp_le_exp.mpr
    unfold gdFit
    rw [h50]
    rw [h40] at hl1
    norm_num at h3 h4 h10a h10b ⊢
    nlinarith
  · rw [← Real.exp_log (show (0 : ℝ) < 150 by norm_num)]
    apply Real.exp_le_exp.mpr
    unfold gdFit
    rw [h150]
    rw [h120] at hl2
    norm_num at h12 h15 h10a h10b ⊢
    nlinarith

/-! ### The CBI regression (p. 646, Figure 9.11) -/

/-- O&R p. 646: the fitted line `π = 8.30 − 6.02 CBI`. -/
def cbiFit (c : ℝ) : ℝ := 8.30 - 6.02 * c

/-- O&R p. 646 and Figure 9.11: fitted average inflation is 7.698% at CBI = 0.1 and 4.086%
at CBI = 0.7 (the ends of the plotted range), a fall of 3.612 points. -/
theorem cbi_fitted_values : cbiFit 0.1 = 7.698 ∧ cbiFit 0.7 = 4.086 ∧
    cbiFit 0.1 - cbiFit 0.7 = 3.612 := by
  unfold cbiFit
  refine ⟨?_, ?_, ?_⟩ <;> norm_num

/-- O&R p. 646: the t-statistics, `6.02/2.35 ∈ (2.56, 2.57)` for the slope and
`8.30/1.57 ∈ (5.28, 5.29)` for the intercept. -/
theorem cbi_tstats : (2.56 : ℝ) < 6.02 / 2.35 ∧ (6.02 : ℝ) / 2.35 < 2.57 ∧
    (5.28 : ℝ) < 8.30 / 1.57 ∧ (8.30 : ℝ) / 1.57 < 5.29 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num

end ObstfeldRogoff.NominalRigidities.ExchangeRateFacts
