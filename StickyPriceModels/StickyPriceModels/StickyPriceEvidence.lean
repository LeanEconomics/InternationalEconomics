/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Fin.VecNotation
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases

/-!
# Evidence on sticky prices, wealth effects and the J-curve

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*: Box 10.1
("More Empirical Evidence on Sticky Prices"), p. 676; the Application "Wealth Effects and the
Real Exchange Rate", pp. 694–696, with its cross-section regression (p. 694) and Table 10.1
(p. 695).

The empirical material is formalised as precise algebraic and statistical claims:
* simple least squares on a finite sample: the normal equations are necessary and sufficient
  for minimising the residual sum of squares (unique minimiser), the minimum value, `0 ≤ R² ≤ 1`,
  and the exact identity `t² = (N − 2) R²/(1 − R²)` linking the slope `t`-statistic to `R²`;
* the regression `Δ log p = 0.039 + 1.042 ΔB/Y`, s.e. `(0.027)`, `(0.433)`, `R² = 0.31`:
  its `t`-ratios, significance for every critical value in `[1.45, 2.40]`, non-rejection of a
  unit slope, and internal consistency of the reported `R²` with the reported coefficient and
  standard error for the book's 15 OECD countries (the implied `R²` rounds to 0.31, robustly to
  the rounding of the reported numbers);
* Table 10.1: the J-curve pattern (negative in year 1, positive afterwards, strictly increasing,
  strictly diminishing increments, exactly one sign change) and the "modest impact" claim;
* Box 10.1: kurtosis is invariant to affine changes of units and to sign flips (so comparing
  the kurtosis of price increases with that of price cuts is unit-free), Pearson's inequality
  `kurtosis ≥ 1 + skewness²` (so excess kurtosis is at least `−2`), and the reported
  numbers (31.2 vs 4.6; Blinder's 55 percent; Kashyap's 12–18 month spells).
-/

namespace ObstfeldRogoff.StickyPriceModels.StickyPriceEvidence

open Finset

/-! ## Simple least squares on a finite sample -/

/-- O&R p. 694 (least squares): residual sum of squares `Σ (y_i − α − β x_i)²` of the line
`α + β x` on the sample `(x_i, y_i)`, `i < n`. -/
def rss {n : ℕ} (x y : Fin n → ℝ) (α β : ℝ) : ℝ := ∑ i, (y i - α - β * x i) ^ 2

/-- Sample mean `(1/N) Σ z_i` (O&R p. 694, least squares). -/
noncomputable def sampleMean {n : ℕ} (z : Fin n → ℝ) : ℝ := (∑ i, z i) / n

/-- Centred cross-product `Σ x_i y_i − (Σ x_i)(Σ y_i)/N` (O&R p. 694, least squares). -/
noncomputable def sxy {n : ℕ} (x y : Fin n → ℝ) : ℝ :=
  ∑ i, x i * y i - (∑ i, x i) * (∑ i, y i) / n

/-- OLS slope `sxy/sxx` (O&R p. 694, the coefficient 1.042). -/
noncomputable def olsSlope {n : ℕ} (x y : Fin n → ℝ) : ℝ := sxy x y / sxy x x

/-- OLS intercept `ȳ − β̂ x̄` (O&R p. 694, the coefficient 0.039). -/
noncomputable def olsIntercept {n : ℕ} (x y : Fin n → ℝ) : ℝ :=
  sampleMean y - olsSlope x y * sampleMean x

/-- Coefficient of determination `R² = sxy²/(sxx syy)` (O&R p. 694, `R² = 0.31`). -/
noncomputable def rSquared {n : ℕ} (x y : Fin n → ℝ) : ℝ :=
  sxy x y ^ 2 / (sxy x x * sxy y y)

/-- Classical OLS standard error of the slope, `√((RSS/(N − 2))/sxx)` (O&R p. 694, the 0.433). -/
noncomputable def slopeSE {n : ℕ} (x y : Fin n → ℝ) : ℝ :=
  Real.sqrt (rss x y (olsIntercept x y) (olsSlope x y) / (n - 2) / sxy x x)

/-- Slope `t`-statistic `β̂/se(β̂)` (O&R p. 694, `1.042/0.433`). -/
noncomputable def slopeT {n : ℕ} (x y : Fin n → ℝ) : ℝ := olsSlope x y / slopeSE x y

/-- Expansion of the residual sum of squares into raw sample sums (O&R p. 694). -/
theorem rss_expand {n : ℕ} (x y : Fin n → ℝ) (α β : ℝ) :
    rss x y α β = ∑ i, y i ^ 2 - 2 * α * ∑ i, y i - 2 * β * ∑ i, x i * y i + n * α ^ 2 +
      2 * α * β * ∑ i, x i + β ^ 2 * ∑ i, x i ^ 2 := by
  unfold rss
  have e : ∀ i, (y i - α - β * x i) ^ 2 = y i ^ 2 - 2 * α * y i - 2 * β * (x i * y i) +
      α ^ 2 + 2 * α * β * x i + β ^ 2 * x i ^ 2 := fun i => by ring
  simp only [e, sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_const, card_univ,
    Fintype.card_fin, nsmul_eq_mul]

/-- The centred sums are the textbook ones: `sxy = Σ (x_i − x̄)(y_i − ȳ)` (O&R p. 694). -/
theorem sxy_eq_centred {n : ℕ} (hn : n ≠ 0) (x y : Fin n → ℝ) :
    sxy x y = ∑ i, (x i - sampleMean x) * (y i - sampleMean y) := by
  have hN : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
  have e : ∀ i, (x i - sampleMean x) * (y i - sampleMean y) = x i * y i -
      sampleMean y * x i - sampleMean x * y i + sampleMean x * sampleMean y := fun i => by ring
  simp only [e, sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_const, card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  unfold sxy sampleMean
  field_simp
  ring

/-- `sxx = Σ (x_i − x̄)² ≥ 0` (O&R p. 694). -/
theorem sxx_nonneg {n : ℕ} (hn : n ≠ 0) (x : Fin n → ℝ) : 0 ≤ sxy x x := by
  rw [sxy_eq_centred hn]
  exact sum_nonneg fun i _ => mul_self_nonneg _

/-- O&R p. 694 (least squares, exact decomposition): for every line `(α, β)`,
`RSS(α, β) = (syy − sxy²/sxx) + N (α − α̂ + (β − β̂) x̄)² + sxx (β − β̂)²`. -/
theorem rss_decomposition {n : ℕ} (hn : n ≠ 0) (x y : Fin n → ℝ) (hxx : sxy x x ≠ 0)
    (α β : ℝ) :
    rss x y α β = (sxy y y - sxy x y ^ 2 / sxy x x) +
      n * (α - olsIntercept x y + (β - olsSlope x y) * sampleMean x) ^ 2 +
        sxy x x * (β - olsSlope x y) ^ 2 := by
  have hN : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
  rw [rss_expand]
  unfold olsIntercept olsSlope sampleMean
  set sx := ∑ i, x i
  set sy := ∑ i, y i
  have hxx' : ∑ i, x i ^ 2 = sxy x x + sx ^ 2 / n := by
    unfold sxy; simp only [sq]; ring
  have hyy' : ∑ i, y i ^ 2 = sxy y y + sy ^ 2 / n := by
    unfold sxy; simp only [sq]; ring
  have hxy' : ∑ i, x i * y i = sxy x y + sx * sy / n := by
    unfold sxy; ring
  rw [hxx', hyy', hxy']
  field_simp
  ring

/-- O&R p. 694 (least squares, necessity and sufficiency; existence and uniqueness): with
`N > 0` and a non-degenerate regressor (`sxx > 0`), `(α, β)` minimises the residual sum of
squares iff `β = sxy/sxx` and `α = ȳ − β x̄`. -/
theorem ols_minimises_iff {n : ℕ} (hn : n ≠ 0) (x y : Fin n → ℝ) (hxx : 0 < sxy x x)
    (α β : ℝ) :
    (∀ α' β', rss x y α β ≤ rss x y α' β') ↔ β = olsSlope x y ∧ α = olsIntercept x y := by
  have hN : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
  have hdec := rss_decomposition hn x y hxx.ne'
  constructor
  · intro h
    have h1 := h (olsIntercept x y) (olsSlope x y)
    rw [hdec, hdec] at h1
    simp only [sub_self, zero_mul, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, mul_zero] at h1
    have ha := mul_nonneg hN.le (sq_nonneg (α - olsIntercept x y +
      (β - olsSlope x y) * sampleMean x))
    have hb := mul_nonneg hxx.le (sq_nonneg (β - olsSlope x y))
    have hb0 : sxy x x * (β - olsSlope x y) ^ 2 = 0 := by linarith
    have hβ : (β - olsSlope x y) ^ 2 = 0 := by
      rcases mul_eq_zero.1 hb0 with h0 | h0
      · exact absurd h0 hxx.ne'
      · exact h0
    have hβ' : β = olsSlope x y := by
      have := pow_eq_zero_iff (n := 2) two_ne_zero |>.1 hβ
      linarith
    have ha0 : (n : ℝ) * (α - olsIntercept x y + (β - olsSlope x y) * sampleMean x) ^ 2 = 0 := by
      linarith
    have hα : (α - olsIntercept x y + (β - olsSlope x y) * sampleMean x) ^ 2 = 0 := by
      rcases mul_eq_zero.1 ha0 with h0 | h0
      · exact absurd h0 hN.ne'
      · exact h0
    have := pow_eq_zero_iff (n := 2) two_ne_zero |>.1 hα
    rw [hβ', sub_self, zero_mul, add_zero] at this
    exact ⟨hβ', by linarith⟩
  · rintro ⟨rfl, rfl⟩ α' β'
    rw [hdec, hdec]
    simp only [sub_self, zero_mul, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, mul_zero]
    have ha := mul_nonneg hN.le (sq_nonneg (α' - olsIntercept x y +
      (β' - olsSlope x y) * sampleMean x))
    have hb := mul_nonneg hxx.le (sq_nonneg (β' - olsSlope x y))
    linarith

/-- O&R p. 694: the minimised residual sum of squares is `syy − sxy²/sxx`. -/
theorem rss_at_ols {n : ℕ} (hn : n ≠ 0) (x y : Fin n → ℝ) (hxx : sxy x x ≠ 0) :
    rss x y (olsIntercept x y) (olsSlope x y) = sxy y y - sxy x y ^ 2 / sxy x x := by
  rw [rss_decomposition hn x y hxx]
  simp

/-- O&R p. 694: `R² = 1 − RSS/syy` at the least-squares line. -/
theorem rSquared_eq_one_sub {n : ℕ} (hn : n ≠ 0) (x y : Fin n → ℝ) (hxx : sxy x x ≠ 0)
    (hyy : sxy y y ≠ 0) :
    rSquared x y = 1 - rss x y (olsIntercept x y) (olsSlope x y) / sxy y y := by
  rw [rss_at_ols hn x y hxx]
  unfold rSquared
  field_simp
  ring

/-- O&R p. 694: `0 ≤ R² ≤ 1` (the upper bound is the Cauchy–Schwarz inequality
`sxy² ≤ sxx syy`, obtained here from `RSS ≥ 0`). -/
theorem rSquared_mem_Icc {n : ℕ} (hn : n ≠ 0) (x y : Fin n → ℝ) (hxx : 0 < sxy x x)
    (hyy : 0 < sxy y y) : 0 ≤ rSquared x y ∧ rSquared x y ≤ 1 := by
  have hrss : 0 ≤ rss x y (olsIntercept x y) (olsSlope x y) :=
    sum_nonneg fun i _ => sq_nonneg _
  constructor
  · unfold rSquared
    positivity
  · rw [rSquared_eq_one_sub hn x y hxx.ne' hyy.ne']
    have := div_nonneg hrss hyy.le
    linarith

/-- O&R p. 694 (exact identity linking the reported statistics): with `N > 2`, `sxx > 0`,
`syy > 0` and an imperfect fit (`RSS > 0`), the slope `t`-statistic satisfies
`t² = (N − 2) R²/(1 − R²)`. -/
theorem slopeT_sq {n : ℕ} (hn : 2 < n) (x y : Fin n → ℝ) (hxx : 0 < sxy x x)
    (hyy : 0 < sxy y y) (hrss : 0 < rss x y (olsIntercept x y) (olsSlope x y)) :
    slopeT x y ^ 2 = (n - 2) * rSquared x y / (1 - rSquared x y) := by
  have hn0 : n ≠ 0 := by omega
  have hN : (2 : ℝ) < n := by exact_mod_cast hn
  have hN2 : (0 : ℝ) < n - 2 := by linarith
  have hR := rSquared_eq_one_sub hn0 x y hxx.ne' hyy.ne'
  set R := rss x y (olsIntercept x y) (olsSlope x y) with hRdef
  have hvar : 0 ≤ R / (n - 2) / sxy x x := by positivity
  have h1R : 1 - rSquared x y = R / sxy y y := by rw [hR]; ring
  unfold slopeT slopeSE
  rw [← hRdef, div_pow, Real.sq_sqrt hvar, h1R]
  unfold rSquared olsSlope
  have hR0 : R ≠ 0 := hrss.ne'
  field_simp

/-- O&R p. 694: inverting the identity, the `R²` implied by a slope `t`-statistic is
`t²/(N − 2 + t²)`. -/
theorem rSquared_of_slopeT {n : ℕ} (hn : 2 < n) (x y : Fin n → ℝ) (hxx : 0 < sxy x x)
    (hyy : 0 < sxy y y) (hrss : 0 < rss x y (olsIntercept x y) (olsSlope x y)) :
    rSquared x y = slopeT x y ^ 2 / (n - 2 + slopeT x y ^ 2) := by
  have hn0 : n ≠ 0 := by omega
  have hN : (2 : ℝ) < n := by exact_mod_cast hn
  have ht := slopeT_sq hn x y hxx hyy hrss
  have h1 : 1 - rSquared x y ≠ 0 := by
    rw [rSquared_eq_one_sub hn0 x y hxx.ne' hyy.ne']
    have := div_pos hrss hyy
    linarith
  have hpos : 0 < (n : ℝ) - 2 + slopeT x y ^ 2 := by
    have := sq_nonneg (slopeT x y); linarith
  rw [eq_div_iff hpos.ne', ht]
  field_simp
  ring

/-! ## The wealth-effects regression (p. 694) -/

/-- O&R p. 694: the slope `t`-ratio `1.042/0.433` lies in `(2.40, 2.41)`. -/
theorem wealth_slope_tratio :
    (2.40 : ℝ) < 1.042 / 0.433 ∧ (1.042 : ℝ) / 0.433 < 2.41 := by
  constructor <;> norm_num

/-- O&R p. 694: the intercept `t`-ratio `0.039/0.027` lies in `(1.44, 1.45)`. -/
theorem wealth_intercept_tratio :
    (1.44 : ℝ) < 0.039 / 0.027 ∧ (0.039 : ℝ) / 0.027 < 1.45 := by
  constructor <;> norm_num

/-- O&R p. 694: for every two-sided critical value `cv ∈ [1.45, 2.40]` (this range contains
both the normal 1.96 and the Student-`t` with 13 degrees of freedom, 2.160), the slope is
significant and the intercept is not. -/
theorem wealth_significance {cv : ℝ} (h1 : 1.45 ≤ cv) (h2 : cv ≤ 2.40) :
    cv < (1.042 : ℝ) / 0.433 ∧ (0.039 : ℝ) / 0.027 < cv := by
  constructor
  · have := wealth_slope_tratio.1; linarith
  · have := wealth_intercept_tratio.2; linarith

/-- O&R p. 694: 1.96 and 2.160 lie in the critical-value range of `wealth_significance`. -/
theorem standard_critical_values_in_range :
    ((1.45 : ℝ) ≤ 1.96 ∧ (1.96 : ℝ) ≤ 2.40) ∧ ((1.45 : ℝ) ≤ 2.160 ∧ (2.160 : ℝ) ≤ 2.40) := by
  norm_num

/-- O&R p. 694 ("an increase of 1 percent ... is associated with a 1 percent appreciation"):
the hypothesis of a unit slope is not rejected for any critical value `cv ≥ 0.1`, because
`|1.042 − 1|/0.433 < 0.1`. -/
theorem wealth_unit_slope_not_rejected {cv : ℝ} (hcv : 0.1 ≤ cv) :
    |(1.042 : ℝ) - 1| / 0.433 < cv := by
  have : |(1.042 : ℝ) - 1| / 0.433 < 0.1 := by
    rw [abs_of_pos (by norm_num)]; norm_num
  linarith

/-- O&R p. 694 with `slopeT_sq` (internal consistency, point version): for the book's 15 OECD
countries (`N − 2 = 13`) the `R²` implied by the reported `t = 1.042/0.433` lies in
`[0.305, 0.315)`, i.e. rounds to the reported 0.31. -/
theorem wealth_implied_rSquared :
    (0.305 : ℝ) ≤ (1.042 / 0.433) ^ 2 / (13 + (1.042 / 0.433) ^ 2) ∧
      (1.042 / 0.433 : ℝ) ^ 2 / (13 + (1.042 / 0.433) ^ 2) < 0.315 := by
  constructor <;> norm_num

/-- O&R p. 694 (internal consistency, robust to rounding): for every coefficient `b` and
standard error `s` that round to the reported 1.042 and 0.433, the implied `R²`
`(b/s)²/(13 + (b/s)²)` rounds to the reported 0.31. -/
theorem wealth_implied_rSquared_robust {b s : ℝ} (hb1 : 1.0415 ≤ b) (hb2 : b ≤ 1.0425)
    (hs1 : 0.4325 ≤ s) (hs2 : s ≤ 0.4335) :
    (0.305 : ℝ) ≤ (b / s) ^ 2 / (13 + (b / s) ^ 2) ∧ (b / s) ^ 2 / (13 + (b / s) ^ 2) < 0.315 := by
  have hs : 0 < s := by linarith
  have ht1 : 2.40 ≤ b / s := by rw [le_div_iff₀ hs]; linarith
  have ht2 : b / s ≤ 2.42 := by rw [div_le_iff₀ hs]; linarith
  set t := b / s
  have hsq1 : 5.76 ≤ t ^ 2 := by nlinarith
  have hsq2 : t ^ 2 ≤ 5.8564 := by nlinarith
  have hpos : 0 < 13 + t ^ 2 := by linarith
  constructor
  · rw [le_div_iff₀ hpos]; linarith
  · rw [div_lt_iff₀ hpos]; linarith

/-! ## Table 10.1: the J-curve (p. 695) -/

/-- O&R Table 10.1, p. 695: change in the U.S. current account (percent of GDP) in years 1–6
after a 20 percent real dollar depreciation (average of six econometric models). -/
noncomputable def caResponse : Fin 6 → ℝ := ![-0.24, 0.61, 1.22, 1.36, 1.46, 1.54]

/-- O&R Table 10.1: year-on-year increments of the current-account response. -/
noncomputable def caIncrement (i : Fin 5) : ℝ := caResponse i.succ - caResponse i.castSucc

/-- O&R p. 695 (the "J-curve" effect): the current account deteriorates in year 1. -/
theorem caResponse_year_one_neg : caResponse 0 < 0 := by
  norm_num [caResponse]

/-- O&R p. 695: the current account improves in every year from year 2 on. -/
theorem caResponse_later_pos : ∀ i : Fin 6, i ≠ 0 → 0 < caResponse i := by
  intro i hi
  fin_cases i <;> first | exact absurd rfl hi | norm_num [caResponse]

/-- O&R p. 695 ("only over time do the quantity responses outweigh the price effects"): the
response is strictly increasing over the six years. -/
theorem caResponse_strictMono : StrictMono caResponse := by
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  fin_cases i <;> norm_num [caResponse]

/-- O&R p. 695: the increments strictly diminish (the response is concave in time). -/
theorem caIncrement_strictAnti : StrictAnti caIncrement := by
  rw [Fin.strictAnti_iff_succ_lt]
  intro i
  fin_cases i <;> norm_num [caIncrement, caResponse]

/-- O&R p. 695 (J-curve, precise): there is exactly one year-to-year sign change, from year 1
to year 2. -/
theorem caResponse_unique_sign_change :
    ∃! i : Fin 5, caResponse i.castSucc < 0 ∧ 0 < caResponse i.succ := by
  refine ⟨0, ?_, ?_⟩
  · norm_num [caResponse]
  · intro i hi
    fin_cases i
    · rfl
    all_goals norm_num [caResponse] at hi

/-- O&R p. 695 ("a very substantial permanent depreciation has only a relatively modest impact
on the current account"): per percentage point of depreciation, the response never exceeds
0.08 percent of GDP. -/
theorem caResponse_modest : ∀ i : Fin 6, caResponse i / 20 < 0.08 := by
  intro i
  fin_cases i <;> norm_num [caResponse]

/-- O&R Table 10.1: the cumulative six-year improvement is 5.95 percent of one year's GDP. -/
theorem caResponse_cumulative : ∑ i, caResponse i = 5.95 := by
  simp [caResponse, Fin.sum_univ_succ]
  norm_num

/-! ## Box 10.1: kurtosis of price changes (p. 676) -/

/-- Box 10.1, p. 676: weighted mean `Σ p_i z_i` of a finite distribution of price changes. -/
def wMean {ι : Type*} [Fintype ι] (p z : ι → ℝ) : ℝ := ∑ i, p i * z i

/-- Box 10.1: `k`-th central moment `Σ p_i (z_i − μ)^k`. -/
def cMoment {ι : Type*} [Fintype ι] (p z : ι → ℝ) (k : ℕ) : ℝ :=
  ∑ i, p i * (z i - wMean p z) ^ k

/-- Box 10.1: kurtosis `m₄/m₂²` (excess kurtosis is this minus 3). -/
noncomputable def kurtosis {ι : Type*} [Fintype ι] (p z : ι → ℝ) : ℝ :=
  cMoment p z 4 / cMoment p z 2 ^ 2

/-- Box 10.1: affine change of units `a + b z` shifts the mean affinely (weights sum to one). -/
theorem wMean_affine {ι : Type*} [Fintype ι] {p : ι → ℝ} (hp : ∑ i, p i = 1) (z : ι → ℝ)
    (a b : ℝ) : wMean p (fun i => a + b * z i) = a + b * wMean p z := by
  unfold wMean
  have e : ∀ i, p i * (a + b * z i) = a * p i + b * (p i * z i) := fun i => by ring
  simp only [e, sum_add_distrib, ← mul_sum, hp, mul_one]

/-- Box 10.1: central moments scale as `b^k` under `a + b z`. -/
theorem cMoment_affine {ι : Type*} [Fintype ι] {p : ι → ℝ} (hp : ∑ i, p i = 1) (z : ι → ℝ)
    (a b : ℝ) (k : ℕ) : cMoment p (fun i => a + b * z i) k = b ^ k * cMoment p z k := by
  unfold cMoment
  rw [wMean_affine hp, mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [show a + b * z i - (a + b * wMean p z) = b * (z i - wMean p z) by ring, mul_pow]
  ring

/-- Box 10.1 (the kurtosis comparison is unit-free): kurtosis is invariant to every affine
change of units `a + b z` with `b ≠ 0`. -/
theorem kurtosis_affine {ι : Type*} [Fintype ι] {p : ι → ℝ} (hp : ∑ i, p i = 1) (z : ι → ℝ)
    (a : ℝ) {b : ℝ} (hb : b ≠ 0) : kurtosis p (fun i => a + b * z i) = kurtosis p z := by
  unfold kurtosis
  rw [cMoment_affine hp, cMoment_affine hp, mul_pow, ← pow_mul]
  exact mul_div_mul_left _ _ (pow_ne_zero _ hb)

/-- Box 10.1: kurtosis is unchanged by a sign flip, so price cuts may be measured as negative
changes or as positive magnitudes. -/
theorem kurtosis_neg {ι : Type*} [Fintype ι] {p : ι → ℝ} (hp : ∑ i, p i = 1) (z : ι → ℝ) :
    kurtosis p (fun i => -z i) = kurtosis p z := by
  have := kurtosis_affine hp z 0 (b := -1) (by norm_num)
  simpa using this

/-- Box 10.1: the first central moment vanishes. -/
theorem cMoment_one {ι : Type*} [Fintype ι] {p : ι → ℝ} (hp : ∑ i, p i = 1) (z : ι → ℝ) :
    cMoment p z 1 = 0 := by
  unfold cMoment
  simp only [pow_one, mul_sub, sum_sub_distrib, ← sum_mul, hp, one_mul]
  unfold wMean
  ring

/-- Box 10.1 (Pearson's inequality): for a nonnegative weighting summing to one with positive
variance, `m₄/m₂² ≥ 1 + m₃²/m₂³`, i.e. kurtosis is at least one plus the squared skewness. -/
theorem pearson_inequality {ι : Type*} [Fintype ι] {p : ι → ℝ} (hp0 : ∀ i, 0 ≤ p i)
    (hp : ∑ i, p i = 1) (z : ι → ℝ) (hvar : 0 < cMoment p z 2) :
    1 + cMoment p z 3 ^ 2 / cMoment p z 2 ^ 3 ≤ kurtosis p z := by
  set m2 := cMoment p z 2
  set c := cMoment p z 3 / m2
  have hnn : 0 ≤ ∑ i, p i * ((z i - wMean p z) ^ 2 - c * (z i - wMean p z) - m2) ^ 2 :=
    sum_nonneg fun i _ => mul_nonneg (hp0 i) (sq_nonneg _)
  have e : ∀ i, p i * ((z i - wMean p z) ^ 2 - c * (z i - wMean p z) - m2) ^ 2 =
      p i * (z i - wMean p z) ^ 4 - 2 * c * (p i * (z i - wMean p z) ^ 3) +
        (c ^ 2 - 2 * m2) * (p i * (z i - wMean p z) ^ 2) +
          2 * c * m2 * (p i * (z i - wMean p z) ^ 1) + m2 ^ 2 * p i := fun i => by ring
  simp only [e, sum_add_distrib, sum_sub_distrib, ← mul_sum] at hnn
  have h1 := cMoment_one hp z
  unfold cMoment at h1
  rw [h1, hp] at hnn
  change 0 ≤ cMoment p z 4 - 2 * c * cMoment p z 3 + (c ^ 2 - 2 * m2) * m2 + 2 * c * m2 * 0 +
    m2 ^ 2 * 1 at hnn
  unfold kurtosis
  rw [← sub_nonneg]
  have e2 : cMoment p z 4 / m2 ^ 2 - (1 + cMoment p z 3 ^ 2 / m2 ^ 3) =
      (cMoment p z 4 - 2 * c * cMoment p z 3 + (c ^ 2 - 2 * m2) * m2 + 2 * c * m2 * 0 +
        m2 ^ 2 * 1) / m2 ^ 2 := by
    simp only [c]
    field_simp
    ring
  rw [e2]
  positivity

/-- Box 10.1: excess kurtosis (kurtosis − 3) is never below `−2`, so the reported excess
kurtoses are far inside the admissible range. -/
theorem excess_kurtosis_ge {ι : Type*} [Fintype ι] {p : ι → ℝ} (hp0 : ∀ i, 0 ≤ p i)
    (hp : ∑ i, p i = 1) (z : ι → ℝ) (hvar : 0 < cMoment p z 2) : -2 ≤ kurtosis p z - 3 := by
  have := pearson_inequality hp0 hp z hvar
  have : 0 ≤ cMoment p z 3 ^ 2 / cMoment p z 2 ^ 3 := by positivity
  linarith

/-- Box 10.1, p. 676 (Kashyap 1995): the excess kurtosis of price increases (31.2) is more than
six times that of price cuts (4.6), and both exceed the normal benchmark 0. -/
theorem kashyap_kurtosis_comparison :
    (6 : ℝ) * 4.6 < 31.2 ∧ (0 : ℝ) < 4.6 := by norm_num

/-- Box 10.1, p. 676 (Blinder 1991): 55 percent of GNP repriced no more than once a year is a
majority. -/
theorem blinder_majority : (1 / 2 : ℝ) < 0.55 := by norm_num

/-- Box 10.1, p. 676 (Kashyap 1995): an average spell of `D ∈ [12, 18]` months between price
changes means between two thirds of a change and one change per year. -/
theorem kashyap_annual_frequency {D : ℝ} (h1 : 12 ≤ D) (h2 : D ≤ 18) :
    (2 / 3 : ℝ) ≤ 12 / D ∧ 12 / D ≤ 1 := by
  have hD : 0 < D := by linarith
  constructor
  · rw [le_div_iff₀ hD]; linarith
  · rw [div_le_one hD]; exact h1

end ObstfeldRogoff.StickyPriceModels.StickyPriceEvidence
