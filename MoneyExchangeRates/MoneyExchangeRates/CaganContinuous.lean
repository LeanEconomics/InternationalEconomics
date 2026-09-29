/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MoneyExchangeRates.CaganModel
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Function.Floor

/-!
# The Cagan model in continuous time

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §8.2.5,
pp. 521–523.

* The continuous-time Cagan equation (15) `m − p = −η ṗ`, with `ṗ` a right derivative
  (fn 10) so that money may jump (announced policy changes).
* The fundamental solution (16) `p_t = (1/η)∫_t^∞ e^{−(s−t)/η} m_s ds` (with `b₀ = 0`) is
  continuous, has right derivative `(p_t − m_t)/η` everywhere and a two-sided derivative at
  every continuity point of `m` (fn 9, Leibniz rule).
* Every continuous solution on a half-line `[t₀, ∞)` is (16) plus `b₀ e^{t/η}` for a unique
  `b₀`; the no-bubble condition `e^{−t/η} p_t → 0` holds iff `b₀ = 0`, so (16) with `b₀ = 0`
  is the unique no-bubble solution; bubble paths have `|p_t| → ∞`.
* Neutrality (weights integrate to one), monotonicity, constant money, and (18)–(19) for
  constant money growth; the integration-by-parts form of (18) (fn 11) in general.
* The period-`h` model (17): its forward solution (with weights `(1+h/η)^{−(s−t)/h}`), the
  limit `h → 0` of the equation (17) is (15), the limit of the weights is `e^{−(s−t)/η}`, and
  the period-`h` no-bubble price level converges to (16) as `h → 0`.

Standing assumptions on money (`AdmissibleMoney`): measurable, locally integrable, and
growing at most like `e^{κs}` with `κ < 1/η` (the continuous-time analogue of fn 6).
-/

namespace ObstfeldRogoff.MoneyExchangeRates.CaganContinuous

open Filter Topology MeasureTheory Set

/-- O&R (16) and fn 6, pp. 518, 522: money paths for which the forward integral (16)
converges: measurable, locally integrable, and `|m_s| ≤ A e^{κ s}` for `s ≥ 0` with
`κ < 1/η`. -/
structure AdmissibleMoney (η : ℝ) (m : ℝ → ℝ) : Prop where
  meas : Measurable m
  locInt : ∀ a b : ℝ, IntervalIntegrable m volume a b
  growth : ∃ A κ : ℝ, κ < 1 / η ∧ ∀ s : ℝ, 0 ≤ s → |m s| ≤ A * Real.exp (κ * s)

/-- O&R (16), p. 522: the discounted money integrand `e^{−s/η} m_s`. -/
noncomputable def weighted (η : ℝ) (m : ℝ → ℝ) (s : ℝ) : ℝ := Real.exp (-s / η) * m s

/-- O&R (16), p. 522: the discounted integrand is locally integrable. -/
theorem weighted_intervalIntegrable {η : ℝ} {m : ℝ → ℝ} (hm : AdmissibleMoney η m)
    (a b : ℝ) : IntervalIntegrable (weighted η m) volume a b :=
  (hm.locInt a b).continuousOn_mul (by fun_prop)

/-- O&R (16), p. 522: the discounted integrand is measurable. -/
theorem weighted_measurable {η : ℝ} {m : ℝ → ℝ} (hm : AdmissibleMoney η m) :
    Measurable (weighted η m) :=
  (Real.continuous_exp.comp (continuous_id.neg.div_const η)).measurable.mul hm.meas

/-- O&R (16), p. 522: the discounted integrand is integrable on `(0, ∞)`. -/
theorem weighted_integrableOn_Ioi_zero {η : ℝ} {m : ℝ → ℝ}
    (hm : AdmissibleMoney η m) : IntegrableOn (weighted η m) (Ioi 0) := by
  obtain ⟨A, κ, hκ, hA⟩ := hm.growth
  have hneg : κ - 1 / η < 0 := by linarith
  have hint : IntegrableOn (fun s => A * Real.exp ((κ - 1 / η) * s)) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi hneg 0).const_mul A
  refine Integrable.mono' hint (weighted_measurable hm).aestronglyMeasurable ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi fun s hs => ?_
  have hs0 : 0 ≤ s := le_of_lt hs
  rw [Real.norm_eq_abs, weighted, abs_mul, Real.abs_exp]
  calc Real.exp (-s / η) * |m s| ≤ Real.exp (-s / η) * (A * Real.exp (κ * s)) :=
        mul_le_mul_of_nonneg_left (hA s hs0) (Real.exp_pos _).le
    _ = A * Real.exp ((κ - 1 / η) * s) := by
        rw [mul_left_comm, ← Real.exp_add]; congr 2; ring

/-- O&R (16), p. 522: the discounted integrand is integrable on every half-line `(t, ∞)`. -/
theorem weighted_integrableOn_Ioi {η : ℝ} {m : ℝ → ℝ}
    (hm : AdmissibleMoney η m) (t : ℝ) : IntegrableOn (weighted η m) (Ioi t) := by
  have h0 := weighted_integrableOn_Ioi_zero hm
  rcases le_or_gt 0 t with ht | ht
  · exact h0.mono_set (Ioi_subset_Ioi ht)
  · have h1 : IntegrableOn (weighted η m) (Ioc t 0) :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le).1 (weighted_intervalIntegrable hm t 0)
    rw [← Ioc_union_Ioi_eq_Ioi ht.le]
    exact h1.union h0

/-- O&R (16), p. 522: the fundamental (no-bubble, `b₀ = 0`) price level
`p_t = (1/η) ∫_t^∞ e^{−(s−t)/η} m_s ds`. -/
noncomputable def contFundamental (η : ℝ) (m : ℝ → ℝ) (t : ℝ) : ℝ :=
  1 / η * ∫ s in Ioi t, Real.exp (-(s - t) / η) * m s

/-- O&R (16), p. 522: `p_t = (1/η) e^{t/η} ∫_t^∞ e^{−s/η} m_s ds`. -/
theorem contFundamental_eq_exp_mul (η : ℝ) (m : ℝ → ℝ) (t : ℝ) :
    contFundamental η m t = 1 / η * Real.exp (t / η) * ∫ s in Ioi t, weighted η m s := by
  have h := integral_const_mul (μ := volume.restrict (Ioi t)) (Real.exp (t / η)) (weighted η m)
  unfold contFundamental
  rw [mul_assoc, ← h]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun s => ?_)
  simp only [weighted]
  rw [← mul_assoc, ← Real.exp_add]
  congr 2
  ring

/-- O&R (16), p. 522: with a fixed base point, `∫_t^∞ e^{−s/η} m_s = I₀ − ∫_0^t e^{−s/η} m_s`
where `I₀ = ∫_0^∞ e^{−s/η} m_s`. -/
theorem integral_Ioi_weighted {η : ℝ} {m : ℝ → ℝ} (hm : AdmissibleMoney η m)
    (t : ℝ) :
    ∫ s in Ioi t, weighted η m s =
      (∫ s in Ioi 0, weighted η m s) - ∫ s in (0 : ℝ)..t, weighted η m s := by
  rw [← intervalIntegral.integral_interval_add_Ioi (weighted_integrableOn_Ioi_zero hm)
    (weighted_integrableOn_Ioi hm t)]
  ring

/-- O&R (16), p. 522: the representation of the fundamental with a fixed base point. -/
theorem contFundamental_eq {η : ℝ} {m : ℝ → ℝ} (hm : AdmissibleMoney η m)
    (t : ℝ) :
    contFundamental η m t = 1 / η * Real.exp (t / η) *
      ((∫ s in Ioi 0, weighted η m s) - ∫ s in (0 : ℝ)..t, weighted η m s) := by
  rw [contFundamental_eq_exp_mul, integral_Ioi_weighted hm]

/-- O&R fn 10, p. 522: the fundamental price level is continuous even when money jumps. -/
theorem contFundamental_continuous {η : ℝ} {m : ℝ → ℝ}
    (hm : AdmissibleMoney η m) : Continuous (contFundamental η m) := by
  have hc : Continuous fun t => ∫ s in (0 : ℝ)..t, weighted η m s :=
    intervalIntegral.continuous_primitive (weighted_intervalIntegrable hm) 0
  have : contFundamental η m = fun t => 1 / η * Real.exp (t / η) *
      ((∫ s in Ioi 0, weighted η m s) - ∫ s in (0 : ℝ)..t, weighted η m s) :=
    funext (contFundamental_eq hm)
  rw [this]
  fun_prop

/-- O&R fn 9–10, p. 522: at every point where money is right-continuous the fundamental has
right derivative `(p_t − m_t)/η`, i.e. it solves (15) with `ṗ` the right derivative. -/
theorem contFundamental_hasDerivWithinAt {η : ℝ} (hη : 0 < η) {m : ℝ → ℝ}
    (hm : AdmissibleMoney η m) {t : ℝ} (hrc : ContinuousWithinAt m (Ici t) t) :
    HasDerivWithinAt (contFundamental η m) ((contFundamental η m t - m t) / η) (Ici t) t := by
  have hwc : ContinuousWithinAt (weighted η m) (Ioi t) t :=
    ((Real.continuous_exp.comp (continuous_id.neg.div_const η)).continuousAt.continuousWithinAt
      ).mul (hrc.mono Ioi_subset_Ici_self)
  have hF : HasDerivWithinAt (fun u => ∫ s in (0 : ℝ)..u, weighted η m s) (weighted η m t)
      (Ici t) t :=
    intervalIntegral.integral_hasDerivWithinAt_right (weighted_intervalIntegrable hm 0 t)
      (weighted_measurable hm).stronglyMeasurable.stronglyMeasurableAtFilter hwc
  have hE : HasDerivWithinAt (fun u => 1 / η * Real.exp (u / η)) (1 / η * (Real.exp (t / η) *
      (1 / η))) (Ici t) t := by
    have := ((hasDerivAt_id t).div_const η).exp.const_mul (1 / η)
    simpa using this.hasDerivWithinAt
  have hprod := hE.mul ((hasDerivWithinAt_const t (Ici t)
    (∫ s in Ioi 0, weighted η m s)).sub hF)
  have heq : contFundamental η m = fun u => 1 / η * Real.exp (u / η) *
      ((∫ s in Ioi 0, weighted η m s) - ∫ s in (0 : ℝ)..u, weighted η m s) :=
    funext (contFundamental_eq hm)
  rw [heq]
  convert hprod using 1
  have h1 : Real.exp (-t / η) = (Real.exp (t / η))⁻¹ := by rw [neg_div, Real.exp_neg]
  simp only [Pi.sub_apply, weighted, h1]
  field_simp
  ring

/-- O&R fn 9, p. 522: at every continuity point of money the fundamental is differentiable with
`ṗ_t = (p_t − m_t)/η` (Leibniz rule). -/
theorem contFundamental_hasDerivAt {η : ℝ} (hη : 0 < η) {m : ℝ → ℝ}
    (hm : AdmissibleMoney η m) {t : ℝ} (hc : ContinuousAt m t) :
    HasDerivAt (contFundamental η m) ((contFundamental η m t - m t) / η) t := by
  have hwc : ContinuousAt (weighted η m) t :=
    (Real.continuous_exp.comp (continuous_id.neg.div_const η)).continuousAt.mul hc
  have hF : HasDerivAt (fun u => ∫ s in (0 : ℝ)..u, weighted η m s) (weighted η m t) t :=
    intervalIntegral.integral_hasDerivAt_right (weighted_intervalIntegrable hm 0 t)
      (weighted_measurable hm).stronglyMeasurable.stronglyMeasurableAtFilter hwc
  have hE : HasDerivAt (fun u => 1 / η * Real.exp (u / η)) (1 / η * (Real.exp (t / η) *
      (1 / η))) t := by
    simpa using ((hasDerivAt_id t).div_const η).exp.const_mul (1 / η)
  have hprod := hE.mul ((hasDerivAt_const t (∫ s in Ioi 0, weighted η m s)).sub hF)
  have heq : contFundamental η m = fun u => 1 / η * Real.exp (u / η) *
      ((∫ s in Ioi 0, weighted η m s) - ∫ s in (0 : ℝ)..u, weighted η m s) :=
    funext (contFundamental_eq hm)
  rw [heq]
  convert hprod using 1
  have h1 : Real.exp (-t / η) = (Real.exp (t / η))⁻¹ := by rw [neg_div, Real.exp_neg]
  simp only [Pi.sub_apply, weighted, h1]
  field_simp
  ring

/-- O&R (15), fn 10, pp. 521–522: `p` solves the continuous-time Cagan equation on the
half-line `[t₀, ∞)`: it is continuous there (no anticipated jumps) and at every `t ≥ t₀` its
right derivative is `(p_t − m_t)/η`. -/
def IsCaganSolOn (η : ℝ) (m p : ℝ → ℝ) (t₀ : ℝ) : Prop :=
  ContinuousOn p (Ici t₀) ∧ ∀ t, t₀ ≤ t → HasDerivWithinAt p ((p t - m t) / η) (Ici t) t

/-- O&R (16), p. 522: the fundamental solves (15) on every half-line when money is
right-continuous. -/
theorem contFundamental_isSol {η : ℝ} (hη : 0 < η) {m : ℝ → ℝ} (hm : AdmissibleMoney η m)
    (hrc : ∀ t, ContinuousWithinAt m (Ici t) t) (t₀ : ℝ) :
    IsCaganSolOn η m (contFundamental η m) t₀ :=
  ⟨(contFundamental_continuous hm).continuousOn,
    fun t _ => contFundamental_hasDerivWithinAt hη hm (hrc t)⟩

/-- O&R (16), p. 522: the bubble term `b₀ e^{t/η}` solves the homogeneous equation. -/
theorem hasDerivAt_bubble {η : ℝ} (b t : ℝ) :
    HasDerivAt (fun u => b * Real.exp (u / η)) (b * Real.exp (t / η) / η) t := by
  have := (((hasDerivAt_id' t).div_const η).exp).const_mul b
  convert this using 1; ring

/-- O&R (16), p. 522: adding a bubble `b₀ e^{t/η}` to a solution gives a solution. -/
theorem isCaganSolOn_add_bubble {η : ℝ} {m p : ℝ → ℝ} {t₀ : ℝ} (hp : IsCaganSolOn η m p t₀)
    (b : ℝ) : IsCaganSolOn η m (fun t => p t + b * Real.exp (t / η)) t₀ := by
  refine ⟨hp.1.add (by fun_prop), fun t ht => ?_⟩
  have := (hp.2 t ht).add (hasDerivAt_bubble (η := η) b t).hasDerivWithinAt
  convert this using 1
  ring

/-- O&R (16), p. 522: **every** continuous solution of (15) on `[t₀, ∞)` is the fundamental
plus a bubble: `p_t = (16) + b₀ e^{t/η}` for all `t ≥ t₀`, with
`b₀ = (p_{t₀} − p^F_{t₀}) e^{−t₀/η}`. -/
theorem isCaganSolOn_eq_fundamental_add_bubble {η : ℝ} (hη : 0 < η) {m p : ℝ → ℝ}
    (hm : AdmissibleMoney η m) (hrc : ∀ t, ContinuousWithinAt m (Ici t) t) {t₀ : ℝ}
    (hp : IsCaganSolOn η m p t₀) (t : ℝ) (ht : t₀ ≤ t) :
    p t = contFundamental η m t +
      (p t₀ - contFundamental η m t₀) * Real.exp (-t₀ / η) * Real.exp (t / η) := by
  set F := contFundamental η m with hFdef
  set w : ℝ → ℝ := fun u => (p u - F u) * Real.exp (-u / η) with hw
  have hFsol := contFundamental_isSol hη hm hrc t₀
  have hwc : ContinuousOn w (Icc t₀ t) :=
    ((hp.1.sub hFsol.1).mul (by fun_prop)).mono Icc_subset_Ici_self
  have hwd : ∀ x ∈ Ico t₀ t, HasDerivWithinAt w 0 (Ici x) x := by
    intro x hx
    have hx0 : t₀ ≤ x := hx.1
    have h1 := (hp.2 x hx0).sub (hFsol.2 x hx0)
    have h2 : HasDerivAt (fun u => Real.exp (-u / η)) (Real.exp (-x / η) * (-1 / η)) x := by
      have := ((hasDerivAt_id x).neg.div_const η).exp
      simpa [neg_div] using this
    have h3 := h1.mul h2.hasDerivWithinAt
    convert h3 using 1
    simp only [Pi.sub_apply]
    field_simp
    ring
  have hconst := constant_of_has_deriv_right_zero hwc hwd t ⟨ht, le_rfl⟩
  simp only [hw] at hconst
  have he : Real.exp (-t / η) * Real.exp (t / η) = 1 := by rw [← Real.exp_add]; simp [neg_div]
  have key : p t - F t = (p t₀ - F t₀) * Real.exp (-t₀ / η) * Real.exp (t / η) := by
    rw [← hconst]
    linear_combination (-(p t - F t)) * he
  linarith

/-- O&R (16), p. 522: the characterisation of all solutions on `[t₀, ∞)`: `p` solves (15) iff
`p = (16) + b₀ e^{t/η}` on `[t₀, ∞)` for some `b₀` (necessarily unique). -/
theorem isCaganSolOn_iff {η : ℝ} (hη : 0 < η) {m p : ℝ → ℝ} (hm : AdmissibleMoney η m)
    (hrc : ∀ t, ContinuousWithinAt m (Ici t) t) (t₀ : ℝ) :
    IsCaganSolOn η m p t₀ ↔
      ∃ b : ℝ, ∀ t, t₀ ≤ t → p t = contFundamental η m t + b * Real.exp (t / η) := by
  constructor
  · intro hp
    exact ⟨_, fun t ht => isCaganSolOn_eq_fundamental_add_bubble hη hm hrc hp t ht⟩
  · rintro ⟨b, hb⟩
    have hq := isCaganSolOn_add_bubble (contFundamental_isSol hη hm hrc t₀) b
    refine ⟨hq.1.congr fun t ht => hb t ht, fun t ht => ?_⟩
    have := (hq.2 t ht).congr_of_mem (fun u hu => hb u (le_trans ht hu)) self_mem_Ici
    rw [hb t ht]; exact this

/-- O&R (16), p. 522: the bubble coefficient is unique. -/
theorem bubble_coeff_unique {η : ℝ} {m p : ℝ → ℝ} {t₀ b b' : ℝ}
    (hb : ∀ t, t₀ ≤ t → p t = contFundamental η m t + b * Real.exp (t / η))
    (hb' : ∀ t, t₀ ≤ t → p t = contFundamental η m t + b' * Real.exp (t / η)) : b = b' := by
  have := (hb t₀ le_rfl).symm.trans (hb' t₀ le_rfl)
  have hpos := Real.exp_pos (t₀ / η)
  have : (b - b') * Real.exp (t₀ / η) = 0 := by linarith
  rcases mul_eq_zero.1 this with h | h
  · linarith
  · linarith

/-- O&R (16), p. 522: the discounted fundamental vanishes at infinity:
`e^{−t/η} p^F_t → 0` (the continuous-time no-bubble condition). -/
theorem contFundamental_noBubble {η : ℝ} {m : ℝ → ℝ} (hm : AdmissibleMoney η m) :
    Tendsto (fun t => Real.exp (-t / η) * contFundamental η m t) atTop (𝓝 0) := by
  have hI := intervalIntegral_tendsto_integral_Ioi (μ := volume) 0
    (weighted_integrableOn_Ioi_zero hm) tendsto_id
  have h1 := (tendsto_const_nhds (x := ∫ s in Ioi 0, weighted η m s)).sub hI
  rw [sub_self] at h1
  have h2 := h1.const_mul (1 / η)
  rw [mul_zero] at h2
  refine h2.congr fun t => ?_
  rw [contFundamental_eq hm]
  have he : Real.exp (-t / η) * Real.exp (t / η) = 1 := by rw [← Real.exp_add]; simp [neg_div]
  simp only [id]
  linear_combination (-(1 / η * ((∫ s in Ioi 0, weighted η m s) -
    ∫ s in (0 : ℝ)..t, weighted η m s))) * he

/-- O&R (16), p. 522: along a solution, `e^{−t/η} p_t` converges to the bubble coefficient. -/
theorem isCaganSolOn_discounted_tendsto {η : ℝ} (hη : 0 < η) {m p : ℝ → ℝ}
    (hm : AdmissibleMoney η m) (hrc : ∀ t, ContinuousWithinAt m (Ici t) t) {t₀ : ℝ}
    (hp : IsCaganSolOn η m p t₀) :
    Tendsto (fun t => Real.exp (-t / η) * p t) atTop
      (𝓝 ((p t₀ - contFundamental η m t₀) * Real.exp (-t₀ / η))) := by
  have h := (contFundamental_noBubble hm).add_const
    ((p t₀ - contFundamental η m t₀) * Real.exp (-t₀ / η))
  rw [zero_add] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop t₀] with t ht
  rw [isCaganSolOn_eq_fundamental_add_bubble hη hm hrc hp t ht]
  have he : Real.exp (-t / η) * Real.exp (t / η) = 1 := by rw [← Real.exp_add]; simp [neg_div]
  linear_combination (-((p t₀ - contFundamental η m t₀) * Real.exp (-t₀ / η))) * he

/-- O&R (16), p. 522: a solution satisfies the no-bubble condition `e^{−t/η} p_t → 0` iff it
coincides with the fundamental on `[t₀, ∞)` (`b₀ = 0`). -/
theorem noBubble_iff_eq_fundamental {η : ℝ} (hη : 0 < η) {m p : ℝ → ℝ}
    (hm : AdmissibleMoney η m) (hrc : ∀ t, ContinuousWithinAt m (Ici t) t) {t₀ : ℝ}
    (hp : IsCaganSolOn η m p t₀) :
    Tendsto (fun t => Real.exp (-t / η) * p t) atTop (𝓝 0) ↔
      ∀ t, t₀ ≤ t → p t = contFundamental η m t := by
  have hlim := isCaganSolOn_discounted_tendsto hη hm hrc hp
  constructor
  · intro h t ht
    have hb := tendsto_nhds_unique hlim h
    have hb0 : p t₀ - contFundamental η m t₀ = 0 := by
      rcases mul_eq_zero.1 hb with h | h
      · exact h
      · exact absurd h (Real.exp_pos _).ne'
    rw [isCaganSolOn_eq_fundamental_add_bubble hη hm hrc hp t ht, hb0]; ring
  · intro h
    rw [h t₀ le_rfl, sub_self, zero_mul] at hlim
    exact hlim

/-- O&R (16), p. 522: **existence and uniqueness**: on every half-line `[t₀, ∞)` the
fundamental is the unique solution of (15) satisfying the no-bubble condition. -/
theorem existsUnique_noBubble {η : ℝ} (hη : 0 < η) {m : ℝ → ℝ} (hm : AdmissibleMoney η m)
    (hrc : ∀ t, ContinuousWithinAt m (Ici t) t) (t₀ : ℝ) :
    (IsCaganSolOn η m (contFundamental η m) t₀ ∧
        Tendsto (fun t => Real.exp (-t / η) * contFundamental η m t) atTop (𝓝 0)) ∧
      ∀ p, IsCaganSolOn η m p t₀ → Tendsto (fun t => Real.exp (-t / η) * p t) atTop (𝓝 0) →
        ∀ t, t₀ ≤ t → p t = contFundamental η m t :=
  ⟨⟨contFundamental_isSol hη hm hrc t₀, contFundamental_noBubble hm⟩,
    fun _ hp h => (noBubble_iff_eq_fundamental hη hm hrc hp).1 h⟩

/-- O&R (16), p. 522: a solution with a bubble (`p_{t₀} ≠ p^F_{t₀}`) explodes:
`|p_t| → ∞`. -/
theorem bubble_abs_tendsto_atTop {η : ℝ} (hη : 0 < η) {m p : ℝ → ℝ}
    (hm : AdmissibleMoney η m) (hrc : ∀ t, ContinuousWithinAt m (Ici t) t) {t₀ : ℝ}
    (hp : IsCaganSolOn η m p t₀) (hb : p t₀ ≠ contFundamental η m t₀) :
    Tendsto (fun t => |p t|) atTop atTop := by
  have hlim := (isCaganSolOn_discounted_tendsto hη hm hrc hp).abs
  have hpos : 0 < |(p t₀ - contFundamental η m t₀) * Real.exp (-t₀ / η)| :=
    abs_pos.2 (mul_ne_zero (sub_ne_zero.2 hb) (Real.exp_pos _).ne')
  have hexp : Tendsto (fun t => Real.exp (t / η)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (tendsto_id.atTop_div_const hη)
  have h3 := hlim.pos_mul_atTop hpos hexp
  refine h3.congr fun t => ?_
  have he : Real.exp (-t / η) * Real.exp (t / η) = 1 := by rw [← Real.exp_add]; simp [neg_div]
  rw [abs_mul, abs_of_pos (Real.exp_pos _), mul_comm, ← mul_assoc, mul_comm (Real.exp _), he,
    one_mul]

/-! ## Examples: constant money, constant money growth, integration by parts -/

/-- O&R (18), p. 523: the discounted time trend vanishes: `e^{−t/η}(a + b t) → 0`. -/
theorem tendsto_exp_neg_mul_affine {η : ℝ} (hη : 0 < η) (a b : ℝ) :
    Tendsto (fun t => Real.exp (-t / η) * (a + b * t)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun t => Real.exp (-t / η)) atTop (𝓝 0) := by
    have := Real.tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.atTop_div_const hη)
    refine this.congr fun t => ?_; simp [neg_div]
  have h2 : Tendsto (fun t => (t / η) * Real.exp (-(t / η))) atTop (𝓝 0) := by
    have := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp
      (tendsto_id.atTop_div_const hη)
    refine this.congr fun t => ?_
    simp
  have h3 := (h1.const_mul a).add (h2.const_mul (b * η))
  simp only [mul_zero, add_zero] at h3
  refine h3.congr fun t => ?_
  rw [neg_div]
  field_simp

/-- O&R (18), p. 523: an affine money path `m_s = m₀ + μ s` is admissible. -/
theorem admissible_affine {η : ℝ} (hη : 0 < η) (m₀ μ : ℝ) :
    AdmissibleMoney η (fun s => m₀ + μ * s) := by
  refine ⟨by fun_prop, fun a b => (by fun_prop : Continuous fun s : ℝ => m₀ + μ * s)
    |>.intervalIntegrable a b, ⟨|m₀| + 2 * η * |μ|, 1 / (2 * η), ?_, fun s hs => ?_⟩⟩
  · rw [div_lt_div_iff₀ (by positivity) hη]; linarith
  · have h1 : 1 ≤ Real.exp (1 / (2 * η) * s) := Real.one_le_exp (by positivity)
    have h2 : 1 / (2 * η) * s + 1 ≤ Real.exp (1 / (2 * η) * s) := Real.add_one_le_exp _
    have h3 : s ≤ 2 * η * Real.exp (1 / (2 * η) * s) := by
      have : s = 2 * η * (1 / (2 * η) * s) := by field_simp
      nlinarith
    calc |m₀ + μ * s| ≤ |m₀| + |μ| * s := by
          calc |m₀ + μ * s| ≤ |m₀| + |μ * s| := abs_add_le _ _
            _ = |m₀| + |μ| * s := by rw [abs_mul, abs_of_nonneg hs]
      _ ≤ |m₀| * Real.exp (1 / (2 * η) * s) + |μ| * (2 * η * Real.exp (1 / (2 * η) * s)) :=
          add_le_add (le_mul_of_one_le_right (abs_nonneg _) h1)
            (mul_le_mul_of_nonneg_left h3 (abs_nonneg _))
      _ = (|m₀| + 2 * η * |μ|) * Real.exp (1 / (2 * η) * s) := by ring

/-- O&R (18), p. 523: with constant money growth `ṁ = μ` (`m_s = m₀ + μ s`), the
fundamental price level is `p_t = m_t + ημ`. -/
theorem contFundamental_affine {η : ℝ} (hη : 0 < η) (m₀ μ t : ℝ) :
    contFundamental η (fun s => m₀ + μ * s) t = m₀ + μ * t + η * μ := by
  have hm := admissible_affine hη m₀ μ
  have hrc : ∀ u, ContinuousWithinAt (fun s => m₀ + μ * s) (Ici u) u :=
    fun u => (by fun_prop : Continuous fun s : ℝ => m₀ + μ * s).continuousWithinAt
  have hsol : IsCaganSolOn η (fun s => m₀ + μ * s) (fun s => m₀ + μ * s + η * μ) t := by
    refine ⟨by fun_prop, fun u _ => ?_⟩
    have : HasDerivAt (fun s => m₀ + μ * s + η * μ) μ u := by
      simpa using (((hasDerivAt_id u).const_mul μ).const_add m₀).add_const (η * μ)
    convert this.hasDerivWithinAt using 1
    field_simp; ring
  have hnb : Tendsto (fun s => Real.exp (-s / η) * (m₀ + μ * s + η * μ)) atTop (𝓝 0) := by
    have := tendsto_exp_neg_mul_affine hη (m₀ + η * μ) μ
    refine this.congr fun s => by ring
  exact ((noBubble_iff_eq_fundamental hη hm hrc hsol).1 hnb t le_rfl).symm

/-- O&R (19), p. 523: with constant money growth, every solution on `[0, ∞)` is
`p_t = m_t + ημ + b₀ e^{t/η}` with `b₀ = p₀ − m₀ − ημ`. -/
theorem affine_general_solution {η : ℝ} (hη : 0 < η) {m₀ μ : ℝ} {p : ℝ → ℝ}
    (hp : IsCaganSolOn η (fun s => m₀ + μ * s) p 0) (t : ℝ) (ht : 0 ≤ t) :
    p t = m₀ + μ * t + η * μ + (p 0 - m₀ - η * μ) * Real.exp (t / η) := by
  have hrc : ∀ u, ContinuousWithinAt (fun s => m₀ + μ * s) (Ici u) u :=
    fun u => (by fun_prop : Continuous fun s : ℝ => m₀ + μ * s).continuousWithinAt
  rw [isCaganSolOn_eq_fundamental_add_bubble hη (admissible_affine hη m₀ μ) hrc hp t ht,
    contFundamental_affine hη, contFundamental_affine hη]
  simp only [mul_zero, add_zero, neg_zero, zero_div, Real.exp_zero, mul_one]
  ring

/-- O&R p. 519 and (16): a constant money supply `m̄` gives the constant price level `m̄`. -/
theorem contFundamental_const {η : ℝ} (hη : 0 < η) (c t : ℝ) :
    contFundamental η (fun _ => c) t = c := by
  have := contFundamental_affine hη c 0 t
  simpa using this

/-- O&R (16), p. 522 (neutrality): the weights `(1/η) e^{−(s−t)/η}` integrate to one over
`[t, ∞)`. -/
theorem weights_integrate_to_one {η : ℝ} (hη : 0 < η) (t : ℝ) :
    1 / η * ∫ s in Ioi t, Real.exp (-(s - t) / η) = 1 := by
  have := contFundamental_const hη 1 t
  unfold contFundamental at this
  simpa using this

/-- O&R (16), p. 522: the forward integrand `e^{−(s−t)/η} m_s` is integrable on `(t, ∞)`. -/
theorem integrableOn_forward {η : ℝ} {m : ℝ → ℝ} (hm : AdmissibleMoney η m) (t : ℝ) :
    IntegrableOn (fun s => Real.exp (-(s - t) / η) * m s) (Ioi t) := by
  have := (weighted_integrableOn_Ioi hm t).const_mul (Real.exp (t / η))
  refine IntegrableOn.congr_fun this (fun s _ => ?_) measurableSet_Ioi
  simp only [weighted]
  rw [← mul_assoc, ← Real.exp_add]; congr 2; ring

/-- O&R p. 519 and (16) (**neutrality**): adding a constant to the money path adds it to the
price level. -/
theorem contFundamental_add_const {η : ℝ} (hη : 0 < η) {m : ℝ → ℝ}
    (hm : AdmissibleMoney η m) (c t : ℝ) :
    contFundamental η (fun s => m s + c) t = contFundamental η m t + c := by
  have hc := contFundamental_const hη c t
  have h1 := integrableOn_forward hm t
  have h2 := integrableOn_forward (admissible_affine hη c 0) t
  simp only [zero_mul, add_zero] at h2
  unfold contFundamental at hc ⊢
  simp_rw [mul_add]
  rw [integral_add h1 h2, mul_add, hc]

/-- O&R (16), p. 522: the price level is monotone in the money path. -/
theorem contFundamental_mono {η : ℝ} (hη : 0 < η) {m m' : ℝ → ℝ} (hm : AdmissibleMoney η m)
    (hm' : AdmissibleMoney η m') (hle : ∀ s, m s ≤ m' s) (t : ℝ) :
    contFundamental η m t ≤ contFundamental η m' t := by
  unfold contFundamental
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact setIntegral_mono_on (integrableOn_forward hm t) (integrableOn_forward hm' t)
    measurableSet_Ioi fun s _ => mul_le_mul_of_nonneg_left (hle s) (Real.exp_pos _).le

/-- O&R (18) and fn 11, p. 523 (integration by parts): if money is differentiable with an
admissible right-continuous derivative `ṁ`, then
`p_t = m_t + ∫_t^∞ e^{−(s−t)/η} ṁ_s ds`. -/
theorem contFundamental_integration_by_parts {η : ℝ} (hη : 0 < η) {m dm : ℝ → ℝ}
    (hm : AdmissibleMoney η m) (hdm : AdmissibleMoney η dm) (hd : ∀ t, HasDerivAt m (dm t) t)
    (hdrc : ∀ t, ContinuousWithinAt dm (Ici t) t) (t : ℝ) :
    contFundamental η m t = m t + ∫ s in Ioi t, Real.exp (-(s - t) / η) * dm s := by
  have hmc : Continuous m := continuous_iff_continuousAt.2 fun u => (hd u).continuousAt
  have hrc : ∀ u, ContinuousWithinAt m (Ici u) u := fun u => hmc.continuousWithinAt
  set q : ℝ → ℝ := fun u => m u + η * contFundamental η dm u with hq
  have hqe : ∀ u, q u = m u + ∫ s in Ioi u, Real.exp (-(s - u) / η) * dm s := by
    intro u; simp only [hq, contFundamental]; field_simp
  have hsol : IsCaganSolOn η m q t := by
    refine ⟨(hmc.add ((contFundamental_continuous hdm).const_smul η)).continuousOn,
      fun u _ => ?_⟩
    have := (hd u).hasDerivWithinAt.add
      ((contFundamental_hasDerivWithinAt hη hdm (hdrc u)).const_mul η)
    convert this using 1
    simp only [hq]; field_simp; ring
  have hnb : Tendsto (fun u => Real.exp (-u / η) * q u) atTop (𝓝 0) := by
    obtain ⟨A, κ, hκ, hA⟩ := hm.growth
    have hneg : κ - 1 / η < 0 := by linarith
    have h1 : Tendsto (fun u => A * Real.exp ((κ - 1 / η) * u)) atTop (𝓝 0) := by
      have := (Real.tendsto_exp_atBot.comp
        (tendsto_id.const_mul_atTop_of_neg hneg)).const_mul A
      simpa using this
    have h2 : Tendsto (fun u => Real.exp (-u / η) * m u) atTop (𝓝 0) := by
      refine squeeze_zero_norm' ?_ h1
      filter_upwards [eventually_ge_atTop 0] with u hu
      rw [Real.norm_eq_abs, abs_mul, Real.abs_exp]
      calc Real.exp (-u / η) * |m u| ≤ Real.exp (-u / η) * (A * Real.exp (κ * u)) :=
            mul_le_mul_of_nonneg_left (hA u hu) (Real.exp_pos _).le
        _ = A * Real.exp ((κ - 1 / η) * u) := by
            rw [mul_left_comm, ← Real.exp_add]; congr 2; ring
    have h3 := h2.add ((contFundamental_noBubble hdm).const_mul η)
    simp only [mul_zero, add_zero] at h3
    refine h3.congr fun u => ?_
    simp only [hq]; ring
  rw [← hqe t]
  exact ((noBubble_iff_eq_fundamental hη hm hrc hsol).1 hnb t le_rfl).symm

/-! ## The period-`h` model (17) and the limit `h → 0` -/

/-- O&R (17), p. 522: along the grid `t, t+h, t+2h, …` the period-`h` Cagan equation
`m − p = −(η/h)(p_{t+h} − p_t)` is the discrete Cagan model (5) with semielasticity `η/h`. -/
theorem periodH_iff {η h : ℝ} (m p : ℝ → ℝ) (t : ℝ) :
    (∀ j : ℕ, m (t + j * h) - p (t + j * h) =
        -(η / h) * (p (t + ((j + 1 : ℕ) : ℝ) * h) - p (t + j * h))) ↔
      CaganModel.IsCaganPath (η / h) (fun j : ℕ => m (t + j * h))
        (fun j : ℕ => p (t + j * h)) := by
  unfold CaganModel.IsCaganPath caganResidual
  refine forall_congr' fun j => ?_
  constructor <;> intro H <;> linarith

/-- O&R p. 522: the period-`h` discount factor is `(η/h)/(1+η/h) = (1 + h/η)^{−1}`. -/
theorem periodH_disc {η h : ℝ} (hη : 0 < η) (hh : 0 < h) :
    CaganModel.disc (η / h) = (1 + h / η)⁻¹ := by
  unfold CaganModel.disc; field_simp; ring

/-- O&R p. 522: the period-`h` scale factor is `1/(1 + η/h) = h/(h + η)`. -/
theorem periodH_scale {η h : ℝ} (hη : 0 < η) (hh : 0 < h) : 1 / (1 + η / h) = h / (h + η) := by
  field_simp

/-- O&R p. 522: period-`h` bubbles grow by the factor `1 + h/η` per period, i.e. like
`b₀(1 + h/η)^{t/h}`. -/
theorem periodH_bubble_factor {η h : ℝ} (hη : 0 < η) (hh : 0 < h) :
    (CaganModel.disc (η / h))⁻¹ = 1 + h / η := by
  rw [periodH_disc hη hh, inv_inv]

/-- O&R p. 522: the period-`h` no-bubble price level
`p_t = (1/(h+η)) Σ_{s=t,t+h,…} (1 + h/η)^{−(s−t)/h} m_s h`. -/
noncomputable def periodHPrice (η h : ℝ) (m : ℝ → ℝ) (t : ℝ) : ℝ :=
  h / (h + η) * ∑' j : ℕ, (1 + h / η)⁻¹ ^ j * m (t + j * h)

/-- O&R p. 522: the period-`h` no-bubble price level is the discrete fundamental (9) with
semielasticity `η/h`. -/
theorem periodHPrice_eq_fundamental {η h : ℝ} (hη : 0 < η) (hh : 0 < h) (m : ℝ → ℝ)
    (t : ℝ) :
    periodHPrice η h m t = CaganModel.fundamental (η / h) (fun j : ℕ => m (t + j * h)) 0 := by
  unfold periodHPrice CaganModel.fundamental
  rw [periodH_disc hη hh, periodH_scale hη hh]
  simp

/-- O&R (17), p. 522: a solution of the period-`h` equation along the grid that satisfies the
period-`h` no-bubble condition equals the period-`h` forward solution. -/
theorem periodH_solution_eq {η h : ℝ} (hη : 0 < η) (hh : 0 < h) {m p : ℝ → ℝ} {t : ℝ}
    (hsum : CaganModel.CaganSummable (η / h) (fun j : ℕ => m (t + j * h)))
    (hp : ∀ j : ℕ, m (t + j * h) - p (t + j * h) =
        -(η / h) * (p (t + ((j + 1 : ℕ) : ℝ) * h) - p (t + j * h)))
    (hnb : Tendsto (fun T : ℕ => CaganModel.disc (η / h) ^ T * p (t + T * h)) atTop (𝓝 0)) :
    p t = periodHPrice η h m t := by
  have hηh : 0 < η / h := div_pos hη hh
  have := CaganModel.eq_fundamental_of_noBubble hηh hsum ((periodH_iff m p t).1 hp) hnb
  have h0 := congrFun this 0
  simp only [Nat.cast_zero, zero_mul, add_zero] at h0
  rw [h0, periodHPrice_eq_fundamental hη hh]

/-- O&R (15), (17) and fn 10, p. 522: letting `h → 0` in the period-`h` equation gives the
continuous-time equation: `(η/h)(p_{t+h} − p_t) → η ṗ_t` with `ṗ` the right derivative. -/
theorem periodH_equation_limit {η : ℝ} {p : ℝ → ℝ} {t d : ℝ}
    (hd : HasDerivWithinAt p d (Ici t) t) :
    Tendsto (fun h => η / h * (p (t + h) - p t)) (𝓝[>] 0) (𝓝 (η * d)) := by
  have h1 := (hasDerivWithinAt_iff_tendsto_slope.1 hd)
  rw [Ici_sdiff_left] at h1
  have h2 : Tendsto (fun h : ℝ => t + h) (𝓝[>] 0) (𝓝[>] t) := by
    refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
    · have : Tendsto (fun h : ℝ => t + h) (𝓝 0) (𝓝 (t + 0)) :=
        tendsto_const_nhds.add tendsto_id
      rw [add_zero] at this
      exact this.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with h hh
      simp only [mem_Ioi] at hh ⊢; linarith
  have h3 := (h1.comp h2).const_mul η
  refine h3.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  simp only [Function.comp, slope_def_field]
  rw [add_sub_cancel_left]
  ring

/-- O&R p. 522: the period-`h` weights converge to the continuous-time weights:
`(1 + h/η)^{−u/h} → e^{−u/η}` as `h → 0⁺`. -/
theorem periodH_weight_limit {η : ℝ} (hη : 0 < η) (u : ℝ) :
    Tendsto (fun h => (1 + h / η) ^ (-u / h)) (𝓝[>] 0) (𝓝 (Real.exp (-u / η))) := by
  have h1 : Tendsto (fun x : ℝ => (1 + (1 / η) / x) ^ x) atTop (𝓝 (Real.exp (1 / η))) :=
    Real.tendsto_one_add_div_rpow_exp (1 / η)
  have h2 := h1.comp tendsto_inv_nhdsGT_zero
  have h3 : ContinuousAt (fun y : ℝ => y ^ (-u)) (Real.exp (1 / η)) :=
    Real.continuousAt_rpow_const _ _ (Or.inl (Real.exp_pos _).ne')
  have h4 := h3.tendsto.comp h2
  rw [← Real.exp_mul] at h4
  have e : 1 / η * -u = -u / η := by ring
  rw [e] at h4
  refine h4.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  simp only [mem_Ioi] at hh
  simp only [Function.comp]
  rw [← Real.rpow_mul (by positivity)]
  congr 1
  · field_simp
  · field_simp

/-- O&R p. 522: the grid index `⌈(s − t)/h⌉ − 1` of the period containing `s`. -/
noncomputable def stepIndex (t h s : ℝ) : ℕ := ⌈(s - t) / h⌉₊ - 1

/-- O&R p. 522: on `(t + jh, t + (j+1)h]` the grid index is `j`. -/
theorem stepIndex_eq {t h : ℝ} (hh : 0 < h) {j : ℕ} {s : ℝ}
    (hs : s ∈ Ioc (t + j * h) (t + (j + 1) * h)) : stepIndex t h s = j := by
  unfold stepIndex
  have hc : ⌈(s - t) / h⌉₊ = j + 1 := by
    rw [Nat.ceil_eq_iff (by omega)]
    simp only [Nat.add_sub_cancel]
    constructor
    · rw [lt_div_iff₀ hh]; linarith [hs.1]
    · rw [div_le_iff₀ hh]; push_cast; linarith [hs.2]
  omega

/-- O&R p. 522: for `s > t`, `(s − t)/h − 1 ≤ index < (s − t)/h`. -/
theorem stepIndex_bounds {t h s : ℝ} (hh : 0 < h) (hs : t < s) :
    (s - t) / h - 1 ≤ (stepIndex t h s : ℝ) ∧ (stepIndex t h s : ℝ) < (s - t) / h := by
  have hx : 0 < (s - t) / h := div_pos (by linarith) hh
  have h1 : 1 ≤ ⌈(s - t) / h⌉₊ := Nat.one_le_iff_ne_zero.2 (by
    rw [Ne, Nat.ceil_eq_zero, not_le]; exact hx)
  have h2 := Nat.le_ceil ((s - t) / h)
  have h3 := Nat.ceil_lt_add_one hx.le
  unfold stepIndex
  rw [Nat.cast_sub h1]
  push_cast
  constructor <;> linarith

/-- O&R p. 522: the integral of a grid-step function over `[t, t + Nh]` is the Riemann sum
`h Σ_{j<N} d_j`. -/
theorem step_intervalIntegral (d : ℕ → ℝ) {t h : ℝ} (hh : 0 < h) (N : ℕ) :
    ∫ s in t..t + N * h, d (stepIndex t h s) = h * ∑ j ∈ Finset.range N, d j := by
  have hpiece : ∀ k : ℕ, EqOn (fun s => d (stepIndex t h s)) (fun _ => d k)
      (uIoc (t + k * h) (t + ((k + 1 : ℕ) : ℝ) * h)) := by
    intro k s hs
    rw [uIoc_of_le (by push_cast; nlinarith)] at hs
    simp only
    rw [stepIndex_eq hh (j := k) (by push_cast at hs; exact hs)]
  have hsum := intervalIntegral.sum_integral_adjacent_intervals (μ := volume)
    (f := fun s => d (stepIndex t h s)) (a := fun k : ℕ => t + k * h) (n := N)
    (fun k _ => (intervalIntegrable_const (c := d k)).congr (hpiece k).symm)
  simp only [Nat.cast_zero, zero_mul, add_zero] at hsum
  rw [← hsum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [intervalIntegral.integral_congr_ae (ae_of_all _ fun s hs => hpiece k hs),
    intervalIntegral.integral_const]
  push_cast
  simp only [smul_eq_mul]
  ring

/-- O&R p. 522 (**the limit `h → 0`**): for continuous admissible money, the period-`h`
no-bubble price level converges to the continuous-time fundamental (16) as `h → 0⁺`
(dominated convergence applied to the Riemann-sum representation). -/
theorem periodHPrice_tendsto {η : ℝ} (hη : 0 < η) {m : ℝ → ℝ} (hm : AdmissibleMoney η m)
    (hmc : Continuous m) (t : ℝ) :
    Tendsto (fun h => periodHPrice η h m t) (𝓝[>] 0) (𝓝 (contFundamental η m t)) := by
  obtain ⟨A, κ, hκ, hA⟩ := hm.growth
  set κ' := max κ 0 with hκ'def
  have hκ'0 : 0 ≤ κ' := le_max_right _ _
  have hκ' : κ' < 1 / η := max_lt hκ (by positivity)
  obtain ⟨K, hK⟩ := (isCompact_Icc (a := t) (b := 0)).exists_bound_of_continuousOn
    hmc.continuousOn
  set D := |A| + |K| * Real.exp (-κ' * t) with hD
  have hmD : ∀ x, t ≤ x → |m x| ≤ D * Real.exp (κ' * x) := by
    intro x hx
    rcases le_or_gt 0 x with h0 | h0
    · have e1 : A * Real.exp (κ * x) ≤ |A| * Real.exp (κ' * x) :=
        mul_le_mul (le_abs_self A) (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_right
          (le_max_left _ _) h0)) (Real.exp_pos _).le (abs_nonneg _)
      have e2 : 0 ≤ |K| * Real.exp (-κ' * t) * Real.exp (κ' * x) := by positivity
      calc |m x| ≤ A * Real.exp (κ * x) := hA x h0
        _ ≤ |A| * Real.exp (κ' * x) := e1
        _ ≤ D * Real.exp (κ' * x) := by rw [hD, add_mul]; linarith
    · have e1 : |m x| ≤ K := by simpa using hK x ⟨hx, h0.le⟩
      have e2 : 1 ≤ Real.exp (-κ' * t) * Real.exp (κ' * x) := by
        rw [← Real.exp_add]; exact Real.one_le_exp (by nlinarith)
      have e3 : 0 ≤ |A| * Real.exp (κ' * x) := by positivity
      calc |m x| ≤ |K| := e1.trans (le_abs_self K)
        _ ≤ |K| * (Real.exp (-κ' * t) * Real.exp (κ' * x)) := le_mul_of_one_le_right
            (abs_nonneg _) e2
        _ ≤ D * Real.exp (κ' * x) := by rw [hD, add_mul]; nlinarith
  set ρ := (κ' + 1 / η) / 2 with hρ
  have hρ1 : κ' < ρ := by rw [hρ]; linarith
  have hρ2 : ρ < 1 / η := by rw [hρ]; linarith
  have hρ0 : 0 < ρ := lt_of_le_of_lt hκ'0 hρ1
  set h₀ := 1 / ρ - η with hh₀
  have hh₀pos : 0 < h₀ := by
    rw [hh₀, sub_pos, lt_div_iff₀ hρ0]
    rw [lt_div_iff₀ hη] at hρ2; linarith
  -- the step-function integrand
  set F : ℝ → ℝ → ℝ := fun h s => 1 / (h + η) * ((1 + h / η)⁻¹ ^ stepIndex t h s *
    m (t + (stepIndex t h s : ℝ) * h)) with hF
  set C := 1 / η * D * Real.exp (1 + ρ * t) with hC
  set bound : ℝ → ℝ := fun s => C * Real.exp ((κ' - ρ) * s) with hbound
  have hbound_int : IntegrableOn bound (Ioi t) :=
    (integrableOn_exp_mul_Ioi (by linarith) t).const_mul C
  have hF_meas : ∀ h, Measurable (F h) := by
    intro h
    have : F h = fun s => (fun k : ℕ => 1 / (h + η) * ((1 + h / η)⁻¹ ^ (k - 1) *
        m (t + ((k - 1 : ℕ) : ℝ) * h))) ⌈(s - t) / h⌉₊ := rfl
    rw [this]
    exact (measurable_from_nat (f := fun k : ℕ => 1 / (h + η) * ((1 + h / η)⁻¹ ^ (k - 1) *
        m (t + ((k - 1 : ℕ) : ℝ) * h)))).comp
      ((measurable_id'.sub_const t).div_const h).nat_ceil
  have hF_bound : ∀ h, 0 < h → h < h₀ → ∀ s, t < s → |F h s| ≤ bound s := by
    intro h hh hhh s hs
    obtain ⟨hn1, hn2⟩ := stepIndex_bounds hh hs
    set n := stepIndex t h s
    have hnh : (n : ℝ) * h < s - t := by rwa [lt_div_iff₀ hh] at hn2
    have hnh0 : 0 ≤ (n : ℝ) * h := by positivity
    have hL : h / (η + h) ≤ Real.log (1 + h / η) := by
      have := Real.one_sub_inv_le_log_of_pos (x := 1 + h / η) (by positivity)
      have e : 1 - (1 + h / η)⁻¹ = h / (η + h) := by field_simp; ring
      linarith
    have hρh : ρ < 1 / (η + h) := by
      have : η + h < 1 / ρ := by rw [hh₀] at hhh; linarith
      rw [lt_div_iff₀ (by linarith)]
      rw [lt_div_iff₀ hρ0] at this; linarith
    have hpow : (1 + h / η)⁻¹ ^ n ≤ Real.exp (1 - ρ * (s - t)) := by
      have e : (1 + h / η)⁻¹ ^ n = Real.exp (-(n * Real.log (1 + h / η))) := by
        rw [← Real.exp_log (show (0 : ℝ) < (1 + h / η)⁻¹ by positivity), ← Real.exp_nat_mul,
          Real.log_inv]
        congr 1; ring
      rw [e, Real.exp_le_exp]
      have k1 : (n : ℝ) * (h / (η + h)) ≤ n * Real.log (1 + h / η) :=
        mul_le_mul_of_nonneg_left hL (Nat.cast_nonneg n)
      have k2 : ((s - t) / h - 1) * (h / (η + h)) ≤ (n : ℝ) * (h / (η + h)) :=
        mul_le_mul_of_nonneg_right hn1 (by positivity)
      have k3 : ((s - t) / h - 1) * (h / (η + h)) = (s - t) / (η + h) - h / (η + h) := by
        field_simp
      have k4 : ρ * (s - t) ≤ (s - t) / (η + h) := by
        rw [div_eq_mul_one_div]; nlinarith
      have k5 : h / (η + h) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
      linarith
    have hmn : |m (t + n * h)| ≤ D * Real.exp (κ' * s) := by
      refine (hmD _ (by linarith)).trans (mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (by linarith) hκ'0)) ?_)
      have := (abs_nonneg (m t)).trans (hmD t le_rfl)
      exact nonneg_of_mul_nonneg_left this (Real.exp_pos _)
    have hD0 : 0 ≤ D := by rw [hD]; positivity
    have hsc : 1 / (h + η) ≤ 1 / η := one_div_le_one_div_of_le hη (by linarith)
    simp only [hF, hbound, hC]
    rw [abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (h + η)),
      abs_of_pos (by positivity : (0 : ℝ) < (1 + h / η)⁻¹ ^ n)]
    calc 1 / (h + η) * ((1 + h / η)⁻¹ ^ n * |m (t + n * h)|)
        ≤ 1 / η * (Real.exp (1 - ρ * (s - t)) * (D * Real.exp (κ' * s))) := by
          gcongr
      _ = 1 / η * D * Real.exp (1 + ρ * t) * Real.exp ((κ' - ρ) * s) := by
          have ee : Real.exp (1 - ρ * (s - t)) * Real.exp (κ' * s) =
              Real.exp (1 + ρ * t) * Real.exp ((κ' - ρ) * s) := by
            rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
          linear_combination (1 / η * D) * ee
  -- the pointwise limit
  have hlim : ∀ s, t < s → Tendsto (fun h => F h s) (𝓝[>] 0)
      (𝓝 (1 / η * (Real.exp (-(s - t) / η) * m s))) := by
    intro s hs
    have hNh : Tendsto (fun h => (stepIndex t h s : ℝ) * h) (𝓝[>] 0) (𝓝 (s - t)) := by
      have hlow : Tendsto (fun h : ℝ => s - t - h) (𝓝[>] 0) (𝓝 (s - t)) := by
        have : Tendsto (fun h : ℝ => s - t - h) (𝓝 0) (𝓝 (s - t - 0)) :=
          tendsto_const_nhds.sub tendsto_id
        rw [sub_zero] at this; exact this.mono_left nhdsWithin_le_nhds
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
      · filter_upwards [self_mem_nhdsWithin] with h hh
        have k1 := mul_le_mul_of_nonneg_right (stepIndex_bounds hh hs).1 hh.le
        have k2 : (s - t) / h * h = s - t := div_mul_cancel₀ _ (ne_of_gt hh)
        nlinarith
      · filter_upwards [self_mem_nhdsWithin] with h hh
        have := (stepIndex_bounds hh hs).2
        rw [lt_div_iff₀ hh] at this; linarith
    have hscale : Tendsto (fun h : ℝ => 1 / (h + η)) (𝓝[>] 0) (𝓝 (1 / η)) := by
      have : Tendsto (fun h : ℝ => 1 / (h + η)) (𝓝 0) (𝓝 (1 / (0 + η))) :=
        tendsto_const_nhds.div (tendsto_id.add tendsto_const_nhds) (by simp [hη.ne'])
      rw [zero_add] at this; exact this.mono_left nhdsWithin_le_nhds
    have hlog : Tendsto (fun h : ℝ => h⁻¹ * Real.log (1 + (1 / η) / h⁻¹)) (𝓝[>] 0)
        (𝓝 (1 / η)) :=
      (Real.tendsto_mul_log_one_add_div_atTop (1 / η)).comp tendsto_inv_nhdsGT_zero
    have hpow : Tendsto (fun h => (1 + h / η)⁻¹ ^ stepIndex t h s) (𝓝[>] 0)
        (𝓝 (Real.exp (-(s - t) / η))) := by
      have h1 := (hNh.mul hlog).neg
      have h2 := (Real.continuous_exp.tendsto _).comp h1
      have e : -((s - t) * (1 / η)) = -(s - t) / η := by ring
      rw [e] at h2
      refine h2.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with h hh
      simp only [mem_Ioi] at hh
      simp only [Function.comp]
      rw [← Real.exp_log (show (0 : ℝ) < (1 + h / η)⁻¹ by positivity), ← Real.exp_nat_mul,
        Real.log_inv]
      have e2 : (1 / η) / h⁻¹ = h / η := by field_simp
      rw [e2]
      congr 1
      field_simp
    have hm_lim : Tendsto (fun h => m (t + (stepIndex t h s : ℝ) * h)) (𝓝[>] 0) (𝓝 (m s)) := by
      have h' : Tendsto (fun h => t + (stepIndex t h s : ℝ) * h) (𝓝[>] 0) (𝓝 (t + (s - t))) :=
        tendsto_const_nhds.add hNh
      rw [add_sub_cancel] at h'
      exact (hmc.tendsto s).comp h'
    exact hscale.mul (hpow.mul hm_lim)
  -- for small `h` the integral of the step function is the period-`h` price
  have hint_eq : ∀ h, 0 < h → h < h₀ → ∫ s in Ioi t, F h s = periodHPrice η h m t := by
    intro h hh hhh
    set c : ℕ → ℝ := fun j => 1 / (h + η) * ((1 + h / η)⁻¹ ^ j * m (t + j * h)) with hc
    have hFint : IntegrableOn (F h) (Ioi t) := by
      refine Integrable.mono' hbound_int (hF_meas h).aestronglyMeasurable ?_
      exact ae_restrict_of_forall_mem measurableSet_Ioi fun s hs => by
        rw [Real.norm_eq_abs]; exact hF_bound h hh hhh s hs
    have hFabs : IntegrableOn (fun s => |F h s|) (Ioi t) := hFint.abs
    have hpart : ∀ N : ℕ, ∫ s in t..t + N * h, F h s = h * ∑ j ∈ Finset.range N, c j :=
      fun N => step_intervalIntegral c hh N
    have hpartabs : ∀ N : ℕ, ∫ s in t..t + N * h, |F h s| =
        h * ∑ j ∈ Finset.range N, |c j| :=
      fun N => step_intervalIntegral (fun j => |c j|) hh N
    have hle : ∀ N : ℕ, ∑ j ∈ Finset.range N, |c j| ≤ (∫ s in Ioi t, |F h s|) / h := by
      intro N
      rw [le_div_iff₀ hh, mul_comm, ← hpartabs N,
        intervalIntegral.integral_of_le (le_add_of_nonneg_right (by positivity))]
      exact setIntegral_mono_set hFabs (ae_of_all _ fun _ => abs_nonneg _)
        Ioc_subset_Ioi_self.eventuallyLE
    have hsumm : Summable c :=
      Summable.of_abs (summable_of_sum_range_le (fun _ => abs_nonneg _) hle)
    have hlim1 : Tendsto (fun N : ℕ => ∫ s in t..t + N * h, F h s) atTop
        (𝓝 (∫ s in Ioi t, F h s)) :=
      intervalIntegral_tendsto_integral_Ioi t hFint
        (tendsto_atTop_add_const_left _ t (tendsto_natCast_atTop_atTop.atTop_mul_const hh))
    have hlim2 : Tendsto (fun N : ℕ => ∫ s in t..t + N * h, F h s) atTop
        (𝓝 (h * ∑' j, c j)) := by
      simp_rw [hpart]; exact hsumm.tendsto_sum_tsum_nat.const_mul h
    rw [tendsto_nhds_unique hlim1 hlim2]
    unfold periodHPrice
    rw [hc, tsum_mul_left]
    ring
  -- dominated convergence
  have hDCT : Tendsto (fun h => ∫ s in Ioi t, F h s) (𝓝[>] 0)
      (𝓝 (∫ s in Ioi t, 1 / η * (Real.exp (-(s - t) / η) * m s))) := by
    refine tendsto_integral_filter_of_dominated_convergence bound ?_ ?_ hbound_int ?_
    · exact Eventually.of_forall fun h => (hF_meas h).aestronglyMeasurable
    · filter_upwards [Ioo_mem_nhdsGT hh₀pos] with h hh
      exact ae_restrict_of_forall_mem measurableSet_Ioi fun s hs => by
        rw [Real.norm_eq_abs]; exact hF_bound h hh.1 hh.2 s hs
    · exact ae_restrict_of_forall_mem measurableSet_Ioi hlim
  have hlimval : (∫ s in Ioi t, 1 / η * (Real.exp (-(s - t) / η) * m s)) =
      contFundamental η m t := by
    unfold contFundamental; rw [integral_const_mul]
  rw [← hlimval]
  refine hDCT.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT hh₀pos] with h hh
  exact hint_eq h hh.1 hh.2

end ObstfeldRogoff.MoneyExchangeRates.CaganContinuous
