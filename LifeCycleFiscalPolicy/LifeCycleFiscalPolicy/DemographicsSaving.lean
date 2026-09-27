/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Output growth, demographics and saving

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*,
§3.3.2–§3.3.3, pp. 148–152, and Exercise 1, p. 195.

* **Growth and saving** (pp. 149–150). With `β(1 + r) = 1` and no taxes, lifetime
  earnings grow at rate `e` (`y^O_{t+1} = (1 + e)y^Y_t`) and each generation's youth
  endowment grows at rate `g`. Then the private saving rate is
  `S^P/Y = −β/(1 + β) · eg/(2 + e + g)`. It falls with `e` (when `g > 0`) and rises with
  `g` iff `e < 0`.
* **Population growth** (O&R (3.33), p. 151). With cohorts growing at rate `n` and
  constant individual saving `s^Y`, `S^P/Y = n s^Y/((1 + n)y^Y + y^O)`, increasing in
  `n` when the young save.
* **Exercise 1** (three-period lives, `r = 0`, log utility, no borrowing by the young).
  Earnings are `y^Y` when young, `(1 + e)y^Y` in middle age and zero in old age.
  Unconstrained, each period consumes a third of lifetime income, which is optimal
  by the AM–GM inequality. For `e > 1` the young are constrained and consume their
  income. With youth income growing at `g`, the aggregate saving rate falls with `e`
  if the young can borrow, but **rises** with `e` when the constraint binds.
-/

namespace ObstfeldRogoff.LifeCycleFiscalPolicy.DemographicsSaving

/-- The private saving rate with growing earnings, O&R p. 150: with `y^Y_t = y`,
`y^O_t = (1 + e)y/(1 + g)` and saving given by (3.23),
`S^P/Y = −β/(1 + β) · eg/(2 + e + g)`. -/
theorem saving_rate_growth {β e g y : ℝ} (hβ : 0 < 1 + β) (hg : 0 < 1 + g) (hy : 0 < y)
    (heg : 0 < 2 + e + g) :
    β / (1 + β) * ((y - (1 + e) * y) - (y / (1 + g) - (1 + e) * (y / (1 + g)))) /
        (y + (1 + e) * (y / (1 + g))) =
      -(β / (1 + β) * (e * g / (2 + e + g))) := by
  have h1 := hβ.ne'
  have h2 := hg.ne'
  have h3 := hy.ne'
  have h4 := heg.ne'
  have hY : y + (1 + e) * (y / (1 + g)) = y * (2 + e + g) / (1 + g) := by field_simp; ring
  rw [hY]
  field_simp
  ring

/-- The saving rate as a function of lifetime earnings growth `e` and output growth `g`. -/
noncomputable def savingRate (β e g : ℝ) : ℝ := -(β / (1 + β) * (e * g / (2 + e + g)))

/-- **Faster lifetime earnings growth lowers saving**, O&R p. 150:
`d(S^P/Y)/de = −β/(1 + β) · g(2 + g)/(2 + e + g)² < 0` when `g > 0` and `β > 0`. -/
theorem hasDerivAt_savingRate_e {β e g : ℝ} (heg : 2 + e + g ≠ 0) :
    HasDerivAt (fun e => savingRate β e g)
      (-(β / (1 + β) * (g * (2 + g) / (2 + e + g) ^ 2))) e := by
  unfold savingRate
  have hd : HasDerivAt (fun e : ℝ => 2 + e + g) 1 e := by
    simpa using ((hasDerivAt_id e).const_add 2).add_const g
  have := (((hasDerivAt_id e).mul_const g).div hd heg).const_mul (β / (1 + β))
  convert this.neg using 1
  · funext y
    simp only [Pi.div_apply, id, Pi.neg_apply]
  · simp only [id]
    field_simp
    ring

theorem savingRate_e_deriv_neg {β e g : ℝ} (hβ : 0 < β) (hg : 0 < g) (heg : 0 < 2 + e + g) :
    -(β / (1 + β) * (g * (2 + g) / (2 + e + g) ^ 2)) < 0 := by
  have : 0 < β / (1 + β) * (g * (2 + g) / (2 + e + g) ^ 2) := by positivity
  linarith

/-- **Faster output growth raises saving iff earnings fall over the life cycle**, O&R p. 150:
`d(S^P/Y)/dg = −β/(1 + β) · e(2 + e)/(2 + e + g)²`, positive iff `e < 0` (given `e ≥ −1`). -/
theorem hasDerivAt_savingRate_g {β e g : ℝ} (heg : 2 + e + g ≠ 0) :
    HasDerivAt (fun g => savingRate β e g)
      (-(β / (1 + β) * (e * (2 + e) / (2 + e + g) ^ 2))) g := by
  unfold savingRate
  have hd : HasDerivAt (fun g : ℝ => 2 + e + g) 1 g := by
    simpa using (hasDerivAt_id g).const_add (2 + e)
  have := (((hasDerivAt_id g).const_mul e).div hd heg).const_mul (β / (1 + β))
  convert this.neg using 1
  · funext y
    simp only [Pi.div_apply, id, Pi.neg_apply]
  · simp only [id]
    field_simp
    ring

theorem savingRate_g_deriv_pos_iff {β e g : ℝ} (hβ : 0 < β) (he : -1 ≤ e) (heg : 0 < 2 + e + g) :
    0 < -(β / (1 + β) * (e * (2 + e) / (2 + e + g) ^ 2)) ↔ e < 0 := by
  have hk : 0 < β / (1 + β) := by positivity
  have hd : 0 < (2 + e + g) ^ 2 := by positivity
  rw [neg_pos, mul_neg_iff]
  simp only [hk, not_lt.2 hk.le, true_and, false_and, false_or, div_neg_iff, hd,
    not_lt.2 hd.le, and_true, and_false, or_false]
  constructor
  · intro h
    by_contra hc
    push Not at hc
    nlinarith
  · intro h
    nlinarith

/-- **Population growth and saving**, O&R (3.33), p. 151: with `N_t = (1 + n)N_{t−1}`,
`S^P/Y = (N_t − N_{t−1})s^Y/(N_t y^Y + N_{t−1}y^O) = n s^Y/((1 + n)y^Y + y^O)`. -/
theorem saving_rate_population {n N sY yY yO : ℝ} (hN : 0 < N)
    (hden : 0 < (1 + n) * yY + yO) :
    ((1 + n) * N - N) * sY / ((1 + n) * N * yY + N * yO) = n * sY / ((1 + n) * yY + yO) := by
  have h1 := hN.ne'
  have h2 := hden.ne'
  have : (1 + n) * N * yY + N * yO = N * ((1 + n) * yY + yO) := by ring
  rw [this]
  field_simp
  ring

/-- **Faster population growth raises saving when the young save**, O&R p. 151:
`d(S^P/Y)/dn = s^Y(y^Y + y^O)/((1 + n)y^Y + y^O)² > 0` for `s^Y > 0`. -/
theorem hasDerivAt_saving_rate_population {n sY yY yO : ℝ} (hden : (1 + n) * yY + yO ≠ 0) :
    HasDerivAt (fun n => n * sY / ((1 + n) * yY + yO))
      (sY * (yY + yO) / ((1 + n) * yY + yO) ^ 2) n := by
  have hd : HasDerivAt (fun n : ℝ => (1 + n) * yY + yO) yY n := by
    simpa using (((hasDerivAt_id n).const_add 1).mul_const yY).add_const yO
  have := ((hasDerivAt_id n).mul_const sY).div hd hden
  convert this using 1
  · funext y
    simp only [Pi.div_apply, id]
  · simp only [id]
    field_simp
    ring

/-! ### Exercise 1: three-period lives (O&R p. 195) -/

/-- **The unconstrained three-period plan is optimal** (Exercise 1): with `r = 0` and log utility,
spending a third of lifetime income `W` in each period maximises `log c^Y + log c^M + log c^O`
over positive plans with `c^Y + c^M + c^O = W` (AM–GM). -/
theorem three_period_optimal {W cY cM cO : ℝ} (hY : 0 < cY) (hM : 0 < cM) (hO : 0 < cO)
    (hW : cY + cM + cO = W) :
    Real.log cY + Real.log cM + Real.log cO ≤ 3 * Real.log (W / 3) := by
  have h := Real.geom_mean_le_arith_mean3_weighted (w₁ := 1 / 3) (w₂ := 1 / 3) (w₃ := 1 / 3)
    (p₁ := cY) (p₂ := cM) (p₃ := cO) (by norm_num) (by norm_num) (by norm_num) hY.le hM.le hO.le
    (by norm_num)
  have hW3 : 0 < W / 3 := by linarith
  have hlhs : 0 < cY ^ (1 / 3 : ℝ) * cM ^ (1 / 3 : ℝ) * cO ^ (1 / 3 : ℝ) := by positivity
  have hrhs : 1 / 3 * cY + 1 / 3 * cM + 1 / 3 * cO = W / 3 := by rw [← hW]; ring
  rw [hrhs] at h
  have hl := Real.log_le_log hlhs h
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_rpow hY, Real.log_rpow hM, Real.log_rpow hO] at hl
  linarith

/-- **Exercise 1(a), unconstrained case** (`e ≤ 1`): with `y^M = (1 + e)y^Y` and `y^O = 0`, each
period consumes `(2 + e)y^Y/3`, so the young save `(1 − e)y^Y/3 ≥ 0`, the middle-aged save
`(1 + 2e)y^Y/3` and the old dissave `(2 + e)y^Y/3`. -/
theorem ex1_unconstrained_saving (e y : ℝ) :
    y - (2 + e) * y / 3 = (1 - e) * y / 3 ∧
      (1 + e) * y - (2 + e) * y / 3 = (1 + 2 * e) * y / 3 ∧
      0 - (2 + e) * y / 3 = -((2 + e) * y / 3) := by
  refine ⟨by ring, by ring, by ring⟩

/-- The young want to borrow exactly when `e > 1` (Exercise 1(a)): the unconstrained youth saving
`(1 − e)y^Y/3` is negative iff `e > 1`. -/
theorem ex1_constraint_binds_iff {e y : ℝ} (hy : 0 < y) : (1 - e) * y / 3 < 0 ↔ 1 < e := by
  constructor
  · intro h
    by_contra hc
    push Not at hc
    nlinarith
  · intro h
    have : (1 - e) * y < 0 := mul_neg_of_neg_of_pos (by linarith) hy
    linarith

/-- **Exercise 1(a), constrained case** (`e > 1`): the young consume their income and save
nothing; the middle-aged and old split `(1 + e)y^Y` equally, so the middle-aged save
`(1 + e)y^Y/2` and the old dissave as much. -/
theorem ex1_constrained_saving (e y : ℝ) :
    y - y = 0 ∧ (1 + e) * y - (1 + e) * y / 2 = (1 + e) * y / 2 ∧
      0 - (1 + e) * y / 2 = -((1 + e) * y / 2) := by
  refine ⟨by ring, by ring, by ring⟩

/-- **Exercise 1(b), unconstrained**: with youth income growing at `g`, the aggregate saving rate
of the three generations alive at `t` out of output `y^Y_t + (1 + e)y^Y_{t−1}` is
`g[(1 − e)(1 + g) + 2 + e]/(3(1 + g)(2 + e + g))`. -/
theorem ex1_saving_rate_unconstrained {e g y : ℝ} (hg : 0 < 1 + g) (hy : 0 < y)
    (heg : 0 < 2 + e + g) :
    ((1 - e) * y / 3 + (1 + 2 * e) * (y / (1 + g)) / 3 - (2 + e) * (y / (1 + g) ^ 2) / 3) /
        (y + (1 + e) * (y / (1 + g))) =
      g * ((1 - e) * (1 + g) + 2 + e) / (3 * (1 + g) * (2 + e + g)) := by
  have h1 := hg.ne'
  have h2 := hy.ne'
  have h3 := heg.ne'
  have hY : y + (1 + e) * (y / (1 + g)) = y * (2 + e + g) / (1 + g) := by field_simp; ring
  rw [hY]
  field_simp
  ring

/-- **Exercise 1(b), constrained** (`e > 1`): the aggregate saving rate is
`(1 + e)g/(2(1 + g)(2 + e + g))`. -/
theorem ex1_saving_rate_constrained {e g y : ℝ} (hg : 0 < 1 + g) (hy : 0 < y)
    (heg : 0 < 2 + e + g) :
    (0 + (1 + e) * (y / (1 + g)) / 2 - (1 + e) * (y / (1 + g) ^ 2) / 2) /
        (y + (1 + e) * (y / (1 + g))) =
      (1 + e) * g / (2 * (1 + g) * (2 + e + g)) := by
  have h1 := hg.ne'
  have h2 := hy.ne'
  have h3 := heg.ne'
  have hY : y + (1 + e) * (y / (1 + g)) = y * (2 + e + g) / (1 + g) := by field_simp; ring
  rw [hY]
  field_simp
  ring

/-- **Exercise 1(c), young can borrow**: the unconstrained saving rate falls as `e` rises
(for `g > 0` and `0 ≤ e < e'`). -/
theorem ex1_unconstrained_rate_anti_e {g e e' : ℝ} (hg : 0 < g) (he : 0 ≤ e) (hee : e < e') :
    g * ((1 - e') * (1 + g) + 2 + e') / (3 * (1 + g) * (2 + e' + g)) <
      g * ((1 - e) * (1 + g) + 2 + e) / (3 * (1 + g) * (2 + e + g)) := by
  have hd1 : 0 < 3 * (1 + g) * (2 + e + g) := by positivity
  have hd2 : 0 < 3 * (1 + g) * (2 + e' + g) := by nlinarith
  rw [div_lt_div_iff₀ hd2 hd1]
  have key : (3 + g - e' * g) * (2 + e + g) < (3 + g - e * g) * (2 + e' + g) := by
    nlinarith [mul_pos (sub_pos.2 hee) (by positivity : (0 : ℝ) < 3 + g + g * (2 + g))]
  have hpos : 0 < 3 * g * (1 + g) := by positivity
  nlinarith [mul_lt_mul_of_pos_left key hpos]

/-- **Exercise 1(c), young constrained**: when the borrowing constraint binds, the saving rate
**rises** with `e` (for `g > 0`): the opposite of the unconstrained case. -/
theorem ex1_constrained_rate_mono_e {g e e' : ℝ} (hg : 0 < g) (he : 0 ≤ e) (hee : e < e') :
    (1 + e) * g / (2 * (1 + g) * (2 + e + g)) < (1 + e') * g / (2 * (1 + g) * (2 + e' + g)) := by
  have hd1 : 0 < 2 * (1 + g) * (2 + e + g) := by positivity
  have hd2 : 0 < 2 * (1 + g) * (2 + e' + g) := by nlinarith
  rw [div_lt_div_iff₀ hd1 hd2]
  nlinarith [mul_pos hg (by linarith : (0 : ℝ) < e' - e), mul_pos hg hg]

/-- **Exercise 1(d), first part**: if the young can borrow, youth endowments grow at `g`, and
middle-age endowment `m` and old-age endowment `0` are constant, aggregate saving at `t` is
`y^Y_t [1 − (1 + 1/(1 + g) + 1/(1 + g)²)/3]`, positive for `g > 0`: the middle-aged terms cancel. -/
theorem ex1d_saving {g y m : ℝ} (hg : 0 < g) (hy : 0 < y) :
    (y - (y + m) / 3) + (m - (y / (1 + g) + m) / 3) + (0 - (y / (1 + g) ^ 2 + m) / 3) =
        y * (1 - (1 + 1 / (1 + g) + 1 / (1 + g) ^ 2) / 3) ∧
      0 < y * (1 - (1 + 1 / (1 + g) + 1 / (1 + g) ^ 2) / 3) := by
  have h1 : (0 : ℝ) < 1 + g := by linarith
  refine ⟨by field_simp; ring, mul_pos hy ?_⟩
  have a : 1 / (1 + g) < 1 := (div_lt_one h1).2 (by linarith)
  have b : 1 / (1 + g) ^ 2 < 1 := (div_lt_one (by positivity)).2 (by nlinarith)
  linarith

end ObstfeldRogoff.LifeCycleFiscalPolicy.DemographicsSaving
