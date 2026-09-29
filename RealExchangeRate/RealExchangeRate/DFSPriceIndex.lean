/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# The Ricardian price index: cost minimisation and the moving-cutoff derivative

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §4.5.1, pp. 236–238,
fn 36, p. 246, and §4.5.5.1, p. 251.

* T19 (pp. 237–238): `P = exp ∫₀¹ log p` is the minimum cost of one unit of
  `C = exp ∫₀¹ log c`, attained by the equal-spending demand `c = P/p` (40). The proof uses
  `e^y ≥ 1 + y` pointwise (a hand-rolled Jensen inequality), not Lagrange multipliers.
* (54) (fn 36, p. 246): the derivative of `log P` in `ν` with a moving cutoff; the boundary term
  vanishes because the cutoff good costs the same in both countries.
* T25 (p. 251): holding `w`, `w*`, `z^H` fixed,
  `d log(P/P*)/dz^F = log(1−κ) − log[wa(z^F)/(w*a*(z^F))]`, which is ZERO at the equilibrium
  cutoff `wa(z^F) = (1−κ)w*a*(z^F)`. The book attributes the effect of a rise in `z^F` to the
  explicit term `z^F log(1−κ)`; that term is exactly cancelled, to first order, by the moving
  integration limit. For a discrete rise beyond the equilibrium
  cutoff the book's direction (Foreign's CPI rises relative to Home's) is nevertheless correct,
  as a second-order effect: `log(P/P*)` is maximised in `z^F` at the equilibrium cutoff.
-/

namespace ObstfeldRogoff.RealExchangeRate.DFSPriceIndex

open Set MeasureTheory

/-- T19, O&R pp. 237–238: if prices `p` and quantities `c` are positive on `[0,1]` and the
consumption index is one, `∫₀¹ log c = 0`, then the expenditure `∫₀¹ p c` is at least
`P = exp ∫₀¹ log p`. -/
theorem priceIndex_le_cost {p c : ℝ → ℝ} (hp : ∀ z ∈ Icc (0 : ℝ) 1, 0 < p z)
    (hc : ∀ z ∈ Icc (0 : ℝ) 1, 0 < c z)
    (hpc : IntervalIntegrable (fun z => p z * c z) volume 0 1)
    (hlp : IntervalIntegrable (fun z => Real.log (p z)) volume 0 1)
    (hlc : IntervalIntegrable (fun z => Real.log (c z)) volume 0 1)
    (hC : ∫ z in (0 : ℝ)..1, Real.log (c z) = 0) :
    Real.exp (∫ z in (0 : ℝ)..1, Real.log (p z)) ≤ ∫ z in (0 : ℝ)..1, p z * c z := by
  set I := ∫ z in (0 : ℝ)..1, Real.log (p z) with hI
  set P := Real.exp I with hP
  have hpt : ∀ z ∈ Icc (0 : ℝ) 1,
      P * (1 + Real.log (p z) + Real.log (c z) - I) ≤ p z * c z := by
    intro z hz
    have hpz := hp z hz
    have hcz := hc z hz
    have h1 := Real.add_one_le_exp (Real.log (p z) + Real.log (c z) - I)
    have h2 : Real.exp (Real.log (p z) + Real.log (c z) - I) * P = p z * c z := by
      rw [hP, ← Real.exp_add, sub_add_cancel, Real.exp_add, Real.exp_log hpz, Real.exp_log hcz]
    have hPpos : 0 < P := Real.exp_pos _
    nlinarith
  have hint : IntervalIntegrable (fun z => P * (1 + Real.log (p z) + Real.log (c z) - I))
      volume 0 1 :=
    (((intervalIntegrable_const.add hlp).add hlc).sub intervalIntegrable_const).const_mul P
  have hval : ∫ z in (0 : ℝ)..1, P * (1 + Real.log (p z) + Real.log (c z) - I) = P := by
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_sub ((intervalIntegrable_const.add hlp).add hlc)
        intervalIntegrable_const,
      intervalIntegral.integral_add (intervalIntegrable_const.add hlp) hlc,
      intervalIntegral.integral_add intervalIntegrable_const hlp, hC, ← hI]
    simp
  rw [← hval]
  exact intervalIntegral.integral_mono_on zero_le_one hint hpc hpt

/-- T19 and (40), O&R p. 238: the demand `c(z) = P/p(z)` has consumption index one
(`∫₀¹ log c = 0`) and costs exactly `P = exp ∫₀¹ log p`, so it attains the minimum. -/
theorem priceIndex_attained {p : ℝ → ℝ} (hp : ∀ z ∈ Icc (0 : ℝ) 1, 0 < p z)
    (hlp : IntervalIntegrable (fun z => Real.log (p z)) volume 0 1) :
    (∫ z in (0 : ℝ)..1, Real.log (Real.exp (∫ y in (0 : ℝ)..1, Real.log (p y)) / p z)) = 0 ∧
      (∫ z in (0 : ℝ)..1, p z * (Real.exp (∫ y in (0 : ℝ)..1, Real.log (p y)) / p z)) =
        Real.exp (∫ y in (0 : ℝ)..1, Real.log (p y)) := by
  set I := ∫ y in (0 : ℝ)..1, Real.log (p y) with hI
  have hu : ∀ z ∈ uIcc (0 : ℝ) 1, 0 < p z := by
    intro z hz; rw [uIcc_of_le zero_le_one] at hz; exact hp z hz
  constructor
  · have e : EqOn (fun z => Real.log (Real.exp I / p z)) (fun z => I - Real.log (p z))
        (uIcc 0 1) := by
      intro z hz
      simp only
      rw [Real.log_div (Real.exp_pos I).ne' (hu z hz).ne', Real.log_exp]
    rw [intervalIntegral.integral_congr e,
      intervalIntegral.integral_sub intervalIntegrable_const hlp, ← hI]
    simp
  · have e : EqOn (fun z => p z * (Real.exp I / p z)) (fun _ => Real.exp I) (uIcc 0 1) := by
      intro z hz
      simp only
      field_simp [(hu z hz).ne']
    rw [intervalIntegral.integral_congr e]
    simp

/-- O&R p. 238, after (40): with demand `c(z) = (P/p(z)) C`, spending on any interval
`[z₁, z₂]` of goods is `(z₂ − z₁) P C`. -/
theorem expenditure_on_interval {p : ℝ → ℝ} {P C z1 z2 : ℝ}
    (hp : ∀ z ∈ uIcc z1 z2, p z ≠ 0) :
    ∫ z in z1..z2, p z * (P / p z * C) = (z2 - z1) * (P * C) := by
  have e : EqOn (fun z => p z * (P / p z * C)) (fun _ => P * C) (uIcc z1 z2) := by
    intro z hz
    simp only
    field_simp [hp z hz]
  rw [intervalIntegral.integral_congr e]
  simp only [intervalIntegral.integral_const, smul_eq_mul]

/-- O&R (54) and fn 36, p. 246: while Foreign productivity is `ν` times higher,
`log P(ν) = z̄ log w + ∫₀^{z̄} log a + (1 − z̄)(log w* − log ν) + ∫_{z̄}^1 log a*` (with
`p = wa` on `[0, z̄]` and `p = w*a*/ν` on `(z̄, 1]`). If `w(ν)`, `w*(ν)`, `z̄(ν)` are
differentiable at `ν = 1` and the cutoff good costs the same in both countries at `ν = 1`
(`w a(z̄) = w* a*(z̄)`), the moving-limit terms cancel and
`d log P/dν = z̄ ŵ + (1 − z̄)(ŵ* − 1)`, which at `z̄ = 1/2` is (54):
`P̂ = (ŵ + ŵ*)/2 − ν̂/2`. -/
theorem logPriceIndex_hasDerivAt {la laS w wS zb : ℝ → ℝ} {w1 wS1 z1 : ℝ}
    (hla : Continuous la) (hlaS : Continuous laS) (hw : HasDerivAt w w1 1)
    (hwS : HasDerivAt wS wS1 1) (hzb : HasDerivAt zb z1 1) (hw0 : 0 < w 1) (hwS0 : 0 < wS 1)
    (hcut : Real.log (w 1) + la (zb 1) = Real.log (wS 1) + laS (zb 1)) :
    HasDerivAt
      (fun ν => zb ν * Real.log (w ν) + (∫ z in (0 : ℝ)..zb ν, la z) +
        (1 - zb ν) * (Real.log (wS ν) - Real.log ν) + ∫ z in zb ν..1, laS z)
      (zb 1 * (w1 / w 1) + (1 - zb 1) * (wS1 / wS 1 - 1)) 1 := by
  have hA : HasDerivAt (fun ν => ∫ z in (0 : ℝ)..zb ν, la z) (la (zb 1) * z1) 1 :=
    (hla.integral_hasStrictDerivAt 0 (zb 1)).hasDerivAt.comp 1 hzb
  have hB0 : HasDerivAt (fun ν => ∫ z in (0 : ℝ)..zb ν, laS z) (laS (zb 1) * z1) 1 :=
    (hlaS.integral_hasStrictDerivAt 0 (zb 1)).hasDerivAt.comp 1 hzb
  have hBeq : (fun ν => ∫ z in zb ν..1, laS z) =
      fun ν => (∫ z in (0 : ℝ)..1, laS z) - ∫ z in (0 : ℝ)..zb ν, laS z := by
    funext ν
    rw [intervalIntegral.integral_interval_sub_left (hlaS.intervalIntegrable _ _)
      (hlaS.intervalIntegrable _ _)]
  have hB : HasDerivAt (fun ν => ∫ z in zb ν..1, laS z) (-(laS (zb 1) * z1)) 1 := by
    rw [hBeq]
    exact (hB0.const_sub _)
  have hlw : HasDerivAt (fun ν => Real.log (w ν)) (w1 / w 1) 1 := hw.log hw0.ne'
  have hlwS : HasDerivAt (fun ν => Real.log (wS ν)) (wS1 / wS 1) 1 := hwS.log hwS0.ne'
  have hlν : HasDerivAt (fun ν : ℝ => Real.log ν) 1 1 := by
    simpa using Real.hasDerivAt_log (x := (1 : ℝ)) one_ne_zero
  have h1 := hzb.mul hlw
  have h2 := (hzb.const_sub 1).mul (hlwS.sub hlν)
  have htot := ((h1.add hA).add h2).add hB
  convert htot using 1
  simp only [Pi.sub_apply, Real.log_one, sub_zero]
  linear_combination -z1 * hcut

/-- The log real exchange rate as a function of `z^F`, O&R p. 251 (`log_realExchangeRate` in
`DFSTransportCosts`), with `f = log(wa)`, `g = log(w*a*)` and `w`, `w*`, `z^H` held fixed:
`Φ(z^F) = ∫_{z^F}^{z^H} (f − g) + (z^F − (1 − z^H)) log(1−κ)`. -/
noncomputable def logRERInCutoff (κ zH : ℝ) (f g : ℝ → ℝ) (zF : ℝ) : ℝ :=
  (∫ z in zF..zH, (f z - g z)) + (zF - (1 - zH)) * Real.log (1 - κ)

/-- T25, O&R p. 251: for continuous `f, g`,
`dΦ/dz^F = log(1−κ) − (f(z^F) − g(z^F))`: the explicit term contributes `log(1−κ)` and the
moving lower limit contributes `−(f − g)(z^F)`. -/
theorem logRERInCutoff_hasDerivAt {κ zH x : ℝ} {f g : ℝ → ℝ} (hf : Continuous f)
    (hg : Continuous g) :
    HasDerivAt (logRERInCutoff κ zH f g) (Real.log (1 - κ) - (f x - g x)) x := by
  have hc : Continuous fun z => f z - g z := hf.sub hg
  have heq : logRERInCutoff κ zH f g = fun u =>
      (∫ z in (0 : ℝ)..zH, (f z - g z)) - (∫ z in (0 : ℝ)..u, (f z - g z)) +
        (u - (1 - zH)) * Real.log (1 - κ) := by
    funext u
    unfold logRERInCutoff
    rw [intervalIntegral.integral_interval_sub_left (hc.intervalIntegrable _ _)
      (hc.intervalIntegrable _ _)]
  rw [heq]
  have h1 := (hc.integral_hasStrictDerivAt 0 x).hasDerivAt.const_sub
    (∫ z in (0 : ℝ)..zH, (f z - g z))
  have h2 : HasDerivAt (fun u : ℝ => (u - (1 - zH)) * Real.log (1 - κ)) (Real.log (1 - κ)) x := by
    simpa using ((hasDerivAt_id x).sub_const (1 - zH)).mul_const (Real.log (1 - κ))
  convert h1.add h2 using 1
  ring

/-- T25, O&R p. 251 — the book's mechanism fails to first order: at the equilibrium cutoff,
where `w a(z^F) = (1−κ) w* a*(z^F)`, i.e. `f(z^F) = log(1−κ) + g(z^F)`, the derivative of
`log(P/P*)` in `z^F` (holding `w`, `w*`, `z^H` fixed) is exactly zero, although the explicit
term `z^F log(1−κ)` alone would give `log(1−κ) < 0`. -/
theorem logRERInCutoff_deriv_zero_at_cutoff {κ zH x : ℝ} {f g : ℝ → ℝ} (hf : Continuous f)
    (hg : Continuous g) (hcut : f x = Real.log (1 - κ) + g x) :
    HasDerivAt (logRERInCutoff κ zH f g) 0 x := by
  have h := logRERInCutoff_hasDerivAt (κ := κ) (zH := zH) (x := x) hf hg
  rwa [hcut, show Real.log (1 - κ) - (Real.log (1 - κ) + g x - g x) = 0 by ring] at h

/-- O&R p. 251: with `f = log(wa)`, `g = log(w*a*)`, the integrand of `dΦ/dz^F` is
`log(1−κ) − (f − g) = log[(1−κ) w* a*/(w a)]`, negative exactly for goods Home produces more
cheaply than Foreign can import them (`(1−κ) w* a* < w a`, i.e. goods above the equilibrium
`z^F` when `A` is decreasing). -/
theorem cutoff_integrand_eq {κ a aS w wS : ℝ} (hκ1 : κ < 1) (ha : 0 < a) (haS : 0 < aS)
    (hw : 0 < w) (hwS : 0 < wS) :
    Real.log (1 - κ) - (Real.log (w * a) - Real.log (wS * aS)) =
      Real.log ((1 - κ) * (wS * aS) / (w * a)) ∧
      (Real.log ((1 - κ) * (wS * aS) / (w * a)) < 0 ↔ (1 - κ) * (wS * aS) < w * a) := by
  have h1 : 0 < 1 - κ := by linarith
  have hwa : 0 < w * a := mul_pos hw ha
  have hwsa : 0 < wS * aS := mul_pos hwS haS
  constructor
  · rw [Real.log_div (by positivity) hwa.ne', Real.log_mul h1.ne' hwsa.ne']
    ring
  · rw [Real.log_neg_iff (by positivity), div_lt_one hwa]

/-- O&R p. 251, the discrete version: if the integrand `log(1−κ) − (f − g)` is negative on
`(x₀, x₁)` (goods beyond the equilibrium cutoff `x₀`) and continuous, then moving `z^F` from
`x₀` up to `x₁` strictly lowers `log(P/P*)`: Foreign's CPI rises relative to Home's, as the
book says, but only through the goods newly imported at a CIF premium, not through the explicit
`z^F log(1−κ)` term. -/
theorem logRERInCutoff_decreases {κ zH x0 x1 : ℝ} {f g : ℝ → ℝ} (hf : Continuous f)
    (hg : Continuous g) (hlt : x0 < x1)
    (hneg : ∀ z ∈ Ioo x0 x1, Real.log (1 - κ) - (f z - g z) < 0) :
    logRERInCutoff κ zH f g x1 < logRERInCutoff κ zH f g x0 := by
  have hc : Continuous fun z => f z - g z := hf.sub hg
  have hdiff : logRERInCutoff κ zH f g x1 - logRERInCutoff κ zH f g x0 =
      ∫ z in x0..x1, (Real.log (1 - κ) - (f z - g z)) := by
    unfold logRERInCutoff
    rw [intervalIntegral.integral_sub intervalIntegrable_const (hc.intervalIntegrable _ _),
      intervalIntegral.integral_const, smul_eq_mul,
      ← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable x0 x1)
        (hc.intervalIntegrable x1 zH)]
    ring
  have hpos : 0 < ∫ z in x0..x1, -(Real.log (1 - κ) - (f z - g z)) :=
    intervalIntegral.intervalIntegral_pos_of_pos_on
      ((continuous_const.sub hc).neg.intervalIntegrable _ _)
      (fun z hz => neg_pos.mpr (hneg z hz)) hlt
  rw [intervalIntegral.integral_neg] at hpos
  linarith

end ObstfeldRogoff.RealExchangeRate.DFSPriceIndex
