/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MoneyExchangeRates.CaganContinuous
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Speculative attacks on fixed exchange rates

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §8.4.2,
pp. 558–566 (Figure 8.4, Table 8.1).

A perfect-foresight Krugman–Flood–Garber model in continuous time: money-market equilibrium
(70) `m − e = −η ė`; under the peg money is fixed at `m̄ = ē` (71); the central-bank balance
sheet (72) `M = B_H + ℰ̄ B_F`; domestic credit grows at rate `μ` (73), so reserves fall (74).

Results (stronger than the book):
* The post-attack float with no bubble is the shadow rate `ẽ_t = b_{H,t} + ημ` (75); every
  continuous post-attack float is `ẽ_t + b_T e^{(t−T)/η}`.
* **Existence and uniqueness of the attack equilibrium**: with `μ > 0` the equilibrium (peg
  before `T`, no-bubble float after `T`, no anticipated jump at `T`) exists and is unique, with
  `T = (ē − b_{H,0} − ημ)/μ` (76). Switching earlier would be an anticipated discrete
  appreciation, later an anticipated discrete depreciation.
* The attack comes exactly `η` before natural exhaustion `T₀ = (ē − b_{H,0})/μ`; reserves just
  before the attack are `ℰ̄ B_{F,T} = M̄(1 − e^{−ημ}) > 0`; log money drops by exactly `ημ`;
  log reserves decline at an increasing rate (Figure 8.4).
* (77) with the misprint corrected: `ē = log(B_{H,0} + ℰ̄ B_{F,0})` (the book prints
  `log(B_{H,0} + B_{F,0})`, which is right only when `ℰ̄ = 1`); `T > 0` iff
  `log(1 + ℰ̄B_{F,0}/B_{H,0}) > ημ`; `T` rises with reserves and falls with `μ`; when the formula
  is negative the shadow rate already exceeds the peg at date 0 (immediate attack).
* Bubbles: without the no-bubble condition the attack equilibria form a one-parameter family
  indexed by `b_T`, with `T = (ē − b_{H,0} − ημ − b_T)/μ`, strictly decreasing in `b_T`. The
  `μ = 0` case (where the book's formula divides by zero): with no bubble there is never an
  attack when reserves are positive; with bubbles, **every** date is an attack date for the
  bubble `b_T = ē − b_{H,0} = log(1 + ℰ̄B_{F,0}/B_{H,0})`.
* Table 8.1 arithmetic.
-/

namespace ObstfeldRogoff.MoneyExchangeRates.SpeculativeAttack

open Filter Topology Set CaganContinuous

/-! ## Domestic credit, reserves and the shadow rate -/

/-- O&R (73) and fn 52, p. 562: domestic credit grows at rate `μ`,
`B_{H,t} = B_{H,0} e^{μt}`, so `b_{H,t} = b_{H,0} + μt`. -/
theorem log_domestic_credit {BH0 : ℝ} (hB : 0 < BH0) (μ t : ℝ) :
    Real.log (BH0 * Real.exp (μ * t)) = Real.log BH0 + μ * t := by
  rw [Real.log_mul hB.ne' (Real.exp_pos _).ne', Real.log_exp]

/-- O&R (72), p. 560: under the peg the reserves `ℰ̄B_{F,t} = M̄ − B_{H,t}` keep the money
supply fixed; by (74) `ℰ̄ Ḃ_F = −Ḃ_H`: reserve losses exactly match credit expansion. -/
theorem reserves_hasDerivAt (Mbar Ebar BH0 μ t : ℝ) :
    HasDerivAt (fun s => (Mbar - BH0 * Real.exp (μ * s)) / Ebar)
      (-(BH0 * Real.exp (μ * t) * μ) / Ebar) t := by
  have h1 : HasDerivAt (fun s => BH0 * Real.exp (μ * s)) (BH0 * (Real.exp (μ * t) * μ)) t := by
    have := ((hasDerivAt_id' t).const_mul μ).exp.const_mul BH0
    simpa using this
  have := (h1.const_sub Mbar).div_const Ebar
  convert this using 1
  ring

/-- O&R (75), p. 562: the shadow floating rate `ẽ_t = b_{H,t} + ημ`. -/
def shadowRate (η μ bH0 t : ℝ) : ℝ := bH0 + μ * t + η * μ

/-- O&R (75) and fn 50, p. 562: the shadow rate solves (70) with money `m = b_H`
(`ẽ̇ = μ` and `m − ẽ = −ημ`). -/
theorem shadowRate_solves (η μ bH0 t : ℝ) :
    HasDerivAt (shadowRate η μ bH0) μ t ∧
      (bH0 + μ * t) - shadowRate η μ bH0 t = -η * μ := by
  refine ⟨?_, by unfold shadowRate; ring⟩
  have := (((hasDerivAt_id' t).const_mul μ).const_add bH0).add_const (η * μ)
  unfold shadowRate; simpa using this

/-- O&R (75), p. 562: the shadow rate is the no-bubble (fundamental) float (16) for the money
path `b_{H,t} = b_{H,0} + μt`. -/
theorem shadowRate_eq_fundamental {η : ℝ} (hη : 0 < η) (μ bH0 t : ℝ) :
    shadowRate η μ bH0 t = contFundamental η (fun s => bH0 + μ * s) t := by
  rw [contFundamental_affine hη]; rfl

/-- O&R (70), p. 559: a path that agrees on `[t₀, ∞)` with a solution of (70) is itself a
solution there. -/
theorem isCaganSolOn_of_eqOn {η : ℝ} {m p q : ℝ → ℝ} {t₀ : ℝ} (hq : IsCaganSolOn η m q t₀)
    (heq : ∀ t, t₀ ≤ t → p t = q t) : IsCaganSolOn η m p t₀ := by
  refine ⟨hq.1.congr fun t ht => heq t ht, fun t ht => ?_⟩
  have := (hq.2 t ht).congr_of_mem (fun u hu => heq u (le_trans ht hu)) self_mem_Ici
  rw [heq t ht]; exact this

/-- O&R p. 564: every continuous post-attack float on `[T, ∞)` is the shadow rate plus a
bubble, `ẽ_t + b_T e^{(t−T)/η}`. -/
theorem float_eq_shadow_add_bubble {η : ℝ} (hη : 0 < η) {μ bH0 T : ℝ} {e : ℝ → ℝ}
    (he : IsCaganSolOn η (fun s => bH0 + μ * s) e T) (t : ℝ) (ht : T ≤ t) :
    e t = shadowRate η μ bH0 t + (e T - shadowRate η μ bH0 T) * Real.exp ((t - T) / η) := by
  have hrc : ∀ u, ContinuousWithinAt (fun s => bH0 + μ * s) (Ici u) u :=
    fun u => (by fun_prop : Continuous fun s : ℝ => bH0 + μ * s).continuousWithinAt
  rw [isCaganSolOn_eq_fundamental_add_bubble hη (admissible_affine hη bH0 μ) hrc he t ht,
    ← shadowRate_eq_fundamental hη, ← shadowRate_eq_fundamental hη, mul_assoc,
    ← Real.exp_add]
  congr 3; ring

/-- O&R p. 564: conversely the shadow rate plus any bubble `b_T e^{(t−T)/η}` solves (70) on
`[T, ∞)`. -/
theorem shadow_add_bubble_isSol {η : ℝ} (hη : 0 < η) (μ bH0 T b : ℝ) :
    IsCaganSolOn η (fun s => bH0 + μ * s)
      (fun t => shadowRate η μ bH0 t + b * Real.exp ((t - T) / η)) T := by
  refine ⟨by unfold shadowRate; fun_prop, fun t _ => ?_⟩
  have h1 := (shadowRate_solves η μ bH0 t).1
  have h2 : HasDerivAt (fun u => b * Real.exp ((u - T) / η))
      (b * (Real.exp ((t - T) / η) * (1 / η))) t := by
    have := (((hasDerivAt_id' t).sub_const T).div_const η).exp.const_mul b
    simpa using this
  have := (h1.add h2).hasDerivWithinAt (s := Ici t)
  convert this using 1
  unfold shadowRate
  field_simp
  ring

/-! ## The attack equilibrium -/

/-- O&R §8.4.2.3–8.4.2.4, pp. 561–562: an attack equilibrium with collapse date `T`: the rate
is pegged at `ē` before `T`, floats according to (70) with money `b_H` from `T` on (with no
bubble), and there is no anticipated discrete jump at `T` (the path is continuous at `T`). -/
def IsAttackEqm (η μ ebar bH0 T : ℝ) (e : ℝ → ℝ) : Prop :=
  (∀ t, t < T → e t = ebar) ∧ IsCaganSolOn η (fun s => bH0 + μ * s) e T ∧ ContinuousAt e T ∧
    Tendsto (fun t => Real.exp (-t / η) * e t) atTop (𝓝 0)

/-- O&R (76), p. 562: the attack date `T = (ē − b_{H,0} − ημ)/μ`. -/
noncomputable def attackTime (η μ ebar bH0 : ℝ) : ℝ := (ebar - bH0 - η * μ) / μ

/-- O&R p. 562: at the attack date the shadow rate equals the peg. -/
theorem shadowRate_attackTime {η μ ebar bH0 : ℝ} (hμ : μ ≠ 0) :
    shadowRate η μ bH0 (attackTime η μ ebar bH0) = ebar := by
  unfold shadowRate attackTime; field_simp; ring

/-- O&R p. 561: a path pegged at `ē` before `T` and continuous at `T` has `e_T = ē` (no
anticipated jump). -/
theorem eq_peg_of_continuousAt {e : ℝ → ℝ} {ebar T : ℝ} (hpeg : ∀ t, t < T → e t = ebar)
    (hc : ContinuousAt e T) : e T = ebar := by
  have h1 : Tendsto e (𝓝[<] T) (𝓝 (e T)) := hc.tendsto.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto e (𝓝[<] T) (𝓝 ebar) :=
    tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun t ht => (hpeg t ht).symm)
  exact tendsto_nhds_unique h1 h2

/-- O&R (75)–(76), p. 562: in any attack equilibrium the post-attack float is the shadow rate
and the collapse date is `T = (ē − b_{H,0} − ημ)/μ`. -/
theorem attackEqm_characterisation {η μ ebar bH0 T : ℝ} (hη : 0 < η) (hμ : μ ≠ 0)
    {e : ℝ → ℝ} (h : IsAttackEqm η μ ebar bH0 T e) :
    T = attackTime η μ ebar bH0 ∧ ∀ t, T ≤ t → e t = shadowRate η μ bH0 t := by
  obtain ⟨hpeg, hsol, hc, hnb⟩ := h
  have hrc : ∀ u, ContinuousWithinAt (fun s => bH0 + μ * s) (Ici u) u :=
    fun u => (by fun_prop : Continuous fun s : ℝ => bH0 + μ * s).continuousWithinAt
  have hfl : ∀ t, T ≤ t → e t = shadowRate η μ bH0 t := fun t ht => by
    rw [(noBubble_iff_eq_fundamental hη (admissible_affine hη bH0 μ) hrc hsol).1 hnb t ht,
      shadowRate_eq_fundamental hη]
  refine ⟨?_, hfl⟩
  have h1 := eq_peg_of_continuousAt hpeg hc
  rw [hfl T le_rfl] at h1
  unfold attackTime; unfold shadowRate at h1
  field_simp
  linarith

/-- O&R (76), p. 562: with `μ > 0` the attack equilibrium **exists**: the path
`max(ē, ẽ_t)` (peg until the shadow rate reaches the peg, float afterwards). -/
theorem attackEqm_exists {η μ : ℝ} (hη : 0 < η) (hμ : 0 < μ) (ebar bH0 : ℝ) :
    IsAttackEqm η μ ebar bH0 (attackTime η μ ebar bH0)
      (fun t => max ebar (shadowRate η μ bH0 t)) := by
  set T := attackTime η μ ebar bH0
  have hT : shadowRate η μ bH0 T = ebar := shadowRate_attackTime hμ.ne'
  have hlt : ∀ t, t < T → shadowRate η μ bH0 t < ebar := by
    intro t ht; rw [← hT]; unfold shadowRate; nlinarith
  have hge : ∀ t, T ≤ t → ebar ≤ shadowRate η μ bH0 t := by
    intro t ht; rw [← hT]; unfold shadowRate; nlinarith
  have heq : ∀ t, T ≤ t → max ebar (shadowRate η μ bH0 t) = shadowRate η μ bH0 t :=
    fun t ht => max_eq_right (hge t ht)
  have hsh : IsCaganSolOn η (fun s => bH0 + μ * s) (shadowRate η μ bH0) T := by
    have := shadow_add_bubble_isSol hη μ bH0 T 0
    simp only [zero_mul, add_zero] at this
    exact this
  refine ⟨fun t ht => max_eq_left (hlt t ht).le, isCaganSolOn_of_eqOn hsh heq, ?_, ?_⟩
  · exact (by unfold shadowRate; fun_prop : Continuous fun t =>
      max ebar (shadowRate η μ bH0 t)).continuousAt
  · have := tendsto_exp_neg_mul_affine hη (bH0 + η * μ) μ
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop T] with t ht
    rw [heq t ht]; unfold shadowRate; ring

/-- O&R (76), p. 562: **uniqueness**: every attack equilibrium has the collapse date (76) and
coincides with `max(ē, ẽ_t)`. -/
theorem attackEqm_unique {η μ : ℝ} (hη : 0 < η) (hμ : 0 < μ) {ebar bH0 T : ℝ} {e : ℝ → ℝ}
    (h : IsAttackEqm η μ ebar bH0 T e) :
    T = attackTime η μ ebar bH0 ∧ e = fun t => max ebar (shadowRate η μ bH0 t) := by
  obtain ⟨hT, hfl⟩ := attackEqm_characterisation hη hμ.ne' h
  refine ⟨hT, funext fun t => ?_⟩
  have hTe : shadowRate η μ bH0 T = ebar := by rw [hT]; exact shadowRate_attackTime hμ.ne'
  rcases lt_or_ge t T with ht | ht
  · rw [h.1 t ht, max_eq_left]
    rw [← hTe]; unfold shadowRate; nlinarith
  · rw [hfl t ht, max_eq_right]
    rw [← hTe]; unfold shadowRate; nlinarith

/-- O&R p. 562: a switch to the no-bubble float at any other date `T′` would involve a
discrete jump `ẽ_{T′} − ē = μ(T′ − T)`: an anticipated appreciation if `T′ < T` (so nobody
attacks early) and an anticipated depreciation if `T′ > T` (so speculators attack before). -/
theorem jump_at_other_date {η μ ebar bH0 : ℝ} (hμ : μ ≠ 0) (T' : ℝ) :
    shadowRate η μ bH0 T' - ebar = μ * (T' - attackTime η μ ebar bH0) := by
  unfold shadowRate attackTime; field_simp; ring

/-- O&R p. 565: before the attack the rate is constant (`ė = 0`, so `i = i*`); after it the
rate depreciates at `μ` (so the home interest rate jumps up by `μ`). -/
theorem depreciation_before_after {η μ : ℝ} (hμ : 0 < μ) (ebar bH0 t : ℝ) :
    (t < attackTime η μ ebar bH0 →
        HasDerivAt (fun s => max ebar (shadowRate η μ bH0 s)) 0 t) ∧
      (attackTime η μ ebar bH0 < t →
        HasDerivAt (fun s => max ebar (shadowRate η μ bH0 s)) μ t) := by
  have hT : shadowRate η μ bH0 (attackTime η μ ebar bH0) = ebar := shadowRate_attackTime hμ.ne'
  constructor
  · intro ht
    have hev : (fun s => max ebar (shadowRate η μ bH0 s)) =ᶠ[𝓝 t] fun _ => ebar := by
      filter_upwards [Iio_mem_nhds ht] with s hs
      refine max_eq_left ?_
      rw [← hT]; unfold shadowRate; simp only [mem_Iio] at hs; nlinarith
    exact (hasDerivAt_const t ebar).congr_of_eventuallyEq hev
  · intro ht
    have hev : (fun s => max ebar (shadowRate η μ bH0 s)) =ᶠ[𝓝 t] shadowRate η μ bH0 := by
      filter_upwards [Ioi_mem_nhds ht] with s hs
      refine max_eq_right ?_
      rw [← hT]; unfold shadowRate; simp only [mem_Ioi] at hs; nlinarith
    exact (shadowRate_solves η μ bH0 t).1.congr_of_eventuallyEq hev

/-! ## Timing relative to natural exhaustion, reserves at the attack -/

/-- O&R p. 561: the date at which reserves would run out without an attack,
`T₀ = (ē − b_{H,0})/μ` (when `b_{H,T₀} = ē`). -/
noncomputable def exhaustionTime (μ ebar bH0 : ℝ) : ℝ := (ebar - bH0) / μ

/-- O&R p. 561, sharpened: the attack comes **exactly `η`** before natural exhaustion. -/
theorem attackTime_eq_exhaustion_sub {η μ ebar bH0 : ℝ} (hμ : μ ≠ 0) :
    attackTime η μ ebar bH0 = exhaustionTime μ ebar bH0 - η := by
  unfold attackTime exhaustionTime; field_simp

/-- O&R p. 561: without an attack, reserves `M̄ − B_{H,t}` (with `M̄ = e^{ē}`) would reach
zero exactly at `T₀`. -/
theorem reserves_zero_at_exhaustion {μ ebar bH0 : ℝ} (hμ : μ ≠ 0) :
    Real.exp ebar - Real.exp (bH0 + μ * exhaustionTime μ ebar bH0) = 0 := by
  unfold exhaustionTime; rw [mul_div_cancel₀ _ hμ]; ring_nf

/-- O&R p. 562 and Figure 8.4: just before the attack, reserves are
`ℰ̄B_{F,T} = M̄ − B_{H,T} = M̄(1 − e^{−ημ})`, strictly positive. -/
theorem reserves_at_attack {η μ ebar bH0 : ℝ} (hμ : μ ≠ 0) :
    Real.exp ebar - Real.exp (bH0 + μ * attackTime η μ ebar bH0) =
      Real.exp ebar * (1 - Real.exp (-(η * μ))) := by
  have : bH0 + μ * attackTime η μ ebar bH0 = ebar + -(η * μ) := by
    unfold attackTime; field_simp; ring
  rw [this, Real.exp_add]; ring

/-- O&R p. 562: the reserves remaining at the attack are strictly positive when `ημ > 0`. -/
theorem reserves_at_attack_pos {η μ ebar bH0 : ℝ} (hη : 0 < η) (hμ : 0 < μ) :
    0 < Real.exp ebar - Real.exp (bH0 + μ * attackTime η μ ebar bH0) := by
  rw [reserves_at_attack hμ.ne']
  have : Real.exp (-(η * μ)) < 1 := Real.exp_lt_one_iff.2 (by nlinarith)
  have := Real.exp_pos ebar
  nlinarith

/-- O&R p. 561 and Figure 8.4: at the attack log money drops from `ē` to `b_{H,T} = ē − ημ`,
i.e. by exactly `ημ` (the fall in real balances required by the jump in expected
depreciation from `0` to `μ`). -/
theorem money_drop_at_attack {η μ ebar bH0 : ℝ} (hμ : μ ≠ 0) :
    ebar - (bH0 + μ * attackTime η μ ebar bH0) = η * μ := by
  unfold attackTime; field_simp; ring

/-- O&R Figure 8.4: reserves are strictly positive throughout the fixed-rate period
`t ≤ T` (for `μ > 0`). -/
theorem reserves_pos_before_attack {η μ ebar bH0 : ℝ} (hη : 0 < η) (hμ : 0 < μ) {t : ℝ}
    (ht : t ≤ attackTime η μ ebar bH0) : 0 < Real.exp ebar - Real.exp (bH0 + μ * t) := by
  have h1 := reserves_at_attack_pos (ebar := ebar) (bH0 := bH0) hη hμ
  have h2 : Real.exp (bH0 + μ * t) ≤ Real.exp (bH0 + μ * attackTime η μ ebar bH0) :=
    Real.exp_le_exp.2 (by nlinarith)
  linarith

/-- O&R Figure 8.4: the derivative of log reserves `log(M̄ − B_{H,t})` is
`−μB_{H,t}/(M̄ − B_{H,t})`. -/
theorem log_reserves_hasDerivAt {Mbar BH0 μ t : ℝ} (hpos : 0 < Mbar - BH0 * Real.exp (μ * t)) :
    HasDerivAt (fun s => Real.log (Mbar - BH0 * Real.exp (μ * s)))
      (-(μ * (BH0 * Real.exp (μ * t))) / (Mbar - BH0 * Real.exp (μ * t))) t := by
  have h1 : HasDerivAt (fun s => Mbar - BH0 * Real.exp (μ * s))
      (-(BH0 * (Real.exp (μ * t) * μ))) t := by
    have := (((hasDerivAt_id' t).const_mul μ).exp.const_mul BH0).const_sub Mbar
    simpa using this
  have := h1.log hpos.ne'
  convert this using 1
  ring

/-- O&R p. 562 and Figure 8.4: log reserves decline at an increasing rate: the rate of decline
`μB_{H,t}/(M̄ − B_{H,t})` is strictly increasing in `t` while reserves are positive
(`B_{H,0} > 0`, `μ > 0`). -/
theorem log_reserves_decline_accelerates {Mbar BH0 μ : ℝ} (hB : 0 < BH0) (hμ : 0 < μ)
    {t₁ t₂ : ℝ} (h12 : t₁ < t₂) (hpos : 0 < Mbar - BH0 * Real.exp (μ * t₂)) :
    μ * (BH0 * Real.exp (μ * t₁)) / (Mbar - BH0 * Real.exp (μ * t₁)) <
      μ * (BH0 * Real.exp (μ * t₂)) / (Mbar - BH0 * Real.exp (μ * t₂)) := by
  have he : Real.exp (μ * t₁) < Real.exp (μ * t₂) := Real.exp_lt_exp.2 (by nlinarith)
  have hB1 : BH0 * Real.exp (μ * t₁) < BH0 * Real.exp (μ * t₂) := mul_lt_mul_of_pos_left he hB
  have hpos1 : 0 < Mbar - BH0 * Real.exp (μ * t₁) := by linarith
  have hx1 : 0 < BH0 * Real.exp (μ * t₁) := by positivity
  have hM : 0 < Mbar := by linarith
  rw [div_lt_div_iff₀ hpos1 hpos]
  nlinarith [mul_pos (mul_pos hμ hM) (sub_pos.2 hB1)]

/-! ## Formula (77), corrected -/

/-- O&R (77), p. 564, corrected: with `ē = log(B_{H,0} + ℰ̄B_{F,0})` (from (71)–(72)) the
attack date is `T = [log(B_{H,0} + ℰ̄B_{F,0}) − b_{H,0} − ημ]/μ =
[log(1 + ℰ̄B_{F,0}/B_{H,0}) − ημ]/μ`. -/
theorem attackTime_corrected {η μ Ebar BH0 BF0 : ℝ} (hB : 0 < BH0) (hE : 0 < Ebar)
    (hF : 0 ≤ BF0) :
    attackTime η μ (Real.log (BH0 + Ebar * BF0)) (Real.log BH0) =
      (Real.log (1 + Ebar * BF0 / BH0) - η * μ) / μ := by
  unfold attackTime
  congr 1
  rw [show 1 + Ebar * BF0 / BH0 = (BH0 + Ebar * BF0) / BH0 by field_simp,
    Real.log_div (by positivity) hB.ne']

/-- O&R (77), p. 564: the printed version `log(B_{H,0} + B_{F,0})` agrees with the correct
`log(B_{H,0} + ℰ̄B_{F,0})` only if `ℰ̄ = 1` (or `B_{F,0} = 0`). -/
theorem printed_77_wrong {Ebar BH0 BF0 : ℝ} (hB : 0 < BH0) (hE : 0 < Ebar) (hF : 0 < BF0)
    (hE1 : Ebar ≠ 1) : Real.log (BH0 + BF0) ≠ Real.log (BH0 + Ebar * BF0) := by
  intro h
  have := Real.log_injOn_pos (by simp only [mem_Ioi]; positivity)
    (by simp only [mem_Ioi]; positivity) h
  apply hE1
  have : (Ebar - 1) * BF0 = 0 := by linarith
  rcases mul_eq_zero.1 this with h1 | h1
  · linarith
  · linarith

/-- O&R p. 564: the fixed-rate period has positive length iff
`log(1 + ℰ̄B_{F,0}/B_{H,0}) > ημ` (`μ > 0`). -/
theorem attackTime_pos_iff {η μ Ebar BH0 BF0 : ℝ} (hμ : 0 < μ) (hB : 0 < BH0) (hE : 0 < Ebar)
    (hF : 0 ≤ BF0) :
    0 < attackTime η μ (Real.log (BH0 + Ebar * BF0)) (Real.log BH0) ↔
      η * μ < Real.log (1 + Ebar * BF0 / BH0) := by
  rw [attackTime_corrected hB hE hF, div_pos_iff_of_pos_right hμ, sub_pos]

/-- O&R p. 564: the larger the initial reserves, the later the attack. -/
theorem attackTime_strictMono_reserves {η μ Ebar BH0 : ℝ} (hμ : 0 < μ) (hB : 0 < BH0)
    (hE : 0 < Ebar) {BF0 BF0' : ℝ} (hF : 0 ≤ BF0) (hlt : BF0 < BF0') :
    attackTime η μ (Real.log (BH0 + Ebar * BF0)) (Real.log BH0) <
      attackTime η μ (Real.log (BH0 + Ebar * BF0')) (Real.log BH0) := by
  unfold attackTime
  have : Real.log (BH0 + Ebar * BF0) < Real.log (BH0 + Ebar * BF0') :=
    Real.log_lt_log (by positivity) (by nlinarith)
  exact div_lt_div_of_pos_right (by linarith) hμ

/-- O&R p. 564: faster credit growth brings the attack forward (`B_{F,0} > 0`). -/
theorem attackTime_strictAnti_growth {η Ebar BH0 BF0 : ℝ} (hB : 0 < BH0)
    (hE : 0 < Ebar) (hF : 0 < BF0) {μ μ' : ℝ} (hμ : 0 < μ) (hlt : μ < μ') :
    attackTime η μ' (Real.log (BH0 + Ebar * BF0)) (Real.log BH0) <
      attackTime η μ (Real.log (BH0 + Ebar * BF0)) (Real.log BH0) := by
  rw [attackTime_corrected hB hE hF.le, attackTime_corrected hB hE hF.le]
  have hL : 0 < Real.log (1 + Ebar * BF0 / BH0) := Real.log_pos (by
    have : 0 < Ebar * BF0 / BH0 := by positivity
    linarith)
  have hμ' : 0 < μ' := by linarith
  have e1 : (Real.log (1 + Ebar * BF0 / BH0) - η * μ') / μ' =
      Real.log (1 + Ebar * BF0 / BH0) / μ' - η := by field_simp
  have e2 : (Real.log (1 + Ebar * BF0 / BH0) - η * μ) / μ =
      Real.log (1 + Ebar * BF0 / BH0) / μ - η := by field_simp
  have : Real.log (1 + Ebar * BF0 / BH0) / μ' < Real.log (1 + Ebar * BF0 / BH0) / μ :=
    div_lt_div_of_pos_left hL hμ hlt
  rw [e1, e2]; linarith

/-- O&R p. 564: if the formula gives `T < 0`, the shadow rate already exceeds the peg at date
0, so the attack must take place immediately. -/
theorem immediate_attack {η μ ebar bH0 : ℝ} (hμ : 0 < μ) (hT : attackTime η μ ebar bH0 < 0) :
    ebar < shadowRate η μ bH0 0 := by
  unfold attackTime at hT; unfold shadowRate
  rw [div_neg_iff] at hT
  rcases hT with ⟨-, h⟩ | ⟨h1, -⟩
  · linarith
  · linarith

/-! ## Bubbles and the `μ = 0` case -/

/-- O&R p. 564: an attack equilibrium in which post-attack bubbles are not ruled out. -/
def IsBubbleAttackEqm (η μ ebar bH0 T : ℝ) (e : ℝ → ℝ) : Prop :=
  (∀ t, t < T → e t = ebar) ∧ IsCaganSolOn η (fun s => bH0 + μ * s) e T ∧ ContinuousAt e T

/-- O&R p. 564: with a post-attack bubble `b_T`, the float is `log B_{H,t} + ημ +
b_T e^{(t−T)/η}` and the attack date satisfies `ē = b_{H,0} + μT + ημ + b_T`. -/
theorem bubbleAttackEqm_characterisation {η μ ebar bH0 T : ℝ} (hη : 0 < η) {e : ℝ → ℝ}
    (h : IsBubbleAttackEqm η μ ebar bH0 T e) :
    ∃ bT : ℝ, (∀ t, T ≤ t → e t = shadowRate η μ bH0 t + bT * Real.exp ((t - T) / η)) ∧
      ebar = shadowRate η μ bH0 T + bT := by
  obtain ⟨hpeg, hsol, hc⟩ := h
  refine ⟨e T - shadowRate η μ bH0 T, fun t ht => float_eq_shadow_add_bubble hη hsol t ht, ?_⟩
  have := eq_peg_of_continuousAt hpeg hc
  linarith

/-- O&R p. 564: with a bubble `b_T` the attack date is `T = (ē − b_{H,0} − ημ − b_T)/μ`. -/
theorem bubble_attackTime {η μ ebar bH0 T bT : ℝ} (hμ : μ ≠ 0)
    (h : ebar = shadowRate η μ bH0 T + bT) : T = attackTime η μ ebar bH0 - bT / μ := by
  unfold attackTime; unfold shadowRate at h; field_simp; linarith

/-- O&R p. 564: for every bubble size `b_T` there is an attack equilibrium (collapse date
`T = (ē − b_{H,0} − ημ − b_T)/μ`): the attack equilibria without the no-bubble condition
form a one-parameter family. -/
theorem bubbleAttackEqm_exists {η μ : ℝ} (hη : 0 < η) (hμ : μ ≠ 0) (ebar bH0 bT : ℝ) :
    IsBubbleAttackEqm η μ ebar bH0 (attackTime η μ ebar bH0 - bT / μ)
      (fun t => shadowRate η μ bH0 (max t (attackTime η μ ebar bH0 - bT / μ)) +
        bT * Real.exp ((max t (attackTime η μ ebar bH0 - bT / μ) -
          (attackTime η μ ebar bH0 - bT / μ)) / η)) := by
  set T := attackTime η μ ebar bH0 - bT / μ with hTdef
  refine ⟨fun t ht => ?_, isCaganSolOn_of_eqOn (shadow_add_bubble_isSol hη μ bH0 T bT)
    fun t ht => by simp only [max_eq_left ht], by unfold shadowRate; fun_prop⟩
  simp only
  rw [max_eq_right ht.le, sub_self, zero_div, Real.exp_zero, mul_one, hTdef]
  unfold shadowRate attackTime; field_simp; ring

/-- O&R p. 564: the attack date is strictly decreasing in the bubble `b_T` (for `μ > 0`):
bubbles bring attacks forward. -/
theorem bubble_attackTime_strictAnti {η μ ebar bH0 : ℝ} (hμ : 0 < μ) {b b' : ℝ} (hbb : b < b') :
    attackTime η μ ebar bH0 - b' / μ < attackTime η μ ebar bH0 - b / μ := by
  have := div_lt_div_of_pos_right hbb hμ
  linarith

/-- O&R p. 564 (the `μ = 0` case, where the displayed formula is undefined): with no bubble
there is **no** attack equilibrium when reserves are positive (`ē > b_{H,0}`): the peg
survives forever. -/
theorem no_attack_without_growth {η ebar bH0 T : ℝ} (hη : 0 < η) (hres : bH0 < ebar)
    {e : ℝ → ℝ} : ¬ IsAttackEqm η 0 ebar bH0 T e := by
  intro h
  obtain ⟨hpeg, hsol, hc, hnb⟩ := h
  have hrc : ∀ u, ContinuousWithinAt (fun s => bH0 + 0 * s) (Ici u) u :=
    fun u => (by fun_prop : Continuous fun s : ℝ => bH0 + 0 * s).continuousWithinAt
  have hfl := (noBubble_iff_eq_fundamental hη (admissible_affine hη bH0 0) hrc hsol).1 hnb T le_rfl
  rw [contFundamental_affine hη] at hfl
  have := eq_peg_of_continuousAt hpeg hc
  simp only [zero_mul, add_zero, mul_zero] at hfl
  linarith

/-- O&R p. 564 (the `μ = 0` case made precise): with bubbles, an attack at date `T` is an
equilibrium iff the bubble is `b_T = ē − b_{H,0}`, whatever `T` is: attack timing is
indeterminate and bubbles can make **any** date an attack date. -/
theorem attack_without_growth_iff {η ebar bH0 T : ℝ} (hη : 0 < η) {e : ℝ → ℝ}
    (h : IsBubbleAttackEqm η 0 ebar bH0 T e) :
    ∀ t, T ≤ t → e t = bH0 + (ebar - bH0) * Real.exp ((t - T) / η) := by
  obtain ⟨bT, hfl, hT⟩ := bubbleAttackEqm_characterisation hη h
  intro t ht
  rw [hfl t ht]
  unfold shadowRate at hT ⊢
  have : bT = ebar - bH0 := by linarith
  rw [this]; ring

/-- O&R p. 564: with `μ = 0`, **every** date `T` is the date of some bubble-driven attack
equilibrium. -/
theorem attack_without_growth_any_date {η : ℝ} (hη : 0 < η) (ebar bH0 T : ℝ) :
    IsBubbleAttackEqm η 0 ebar bH0 T
      (fun t => shadowRate η 0 bH0 (max t T) +
        (ebar - bH0) * Real.exp ((max t T - T) / η)) := by
  refine ⟨fun t ht => ?_, isCaganSolOn_of_eqOn (shadow_add_bubble_isSol hη 0 bH0 T (ebar - bH0))
    fun t ht => by simp only [max_eq_left ht], by unfold shadowRate; fun_prop⟩
  simp only
  rw [max_eq_right ht.le, sub_self, zero_div, Real.exp_zero, mul_one]
  unfold shadowRate; ring

/-- O&R p. 564: the `μ = 0` attack bubble is `b_T = log(1 + ℰ̄B_{F,0}/B_{H,0})`, positive when
reserves are positive. -/
theorem zero_growth_bubble_size {Ebar BH0 BF0 : ℝ} (hB : 0 < BH0) (hE : 0 < Ebar)
    (hF : 0 < BF0) :
    Real.log (BH0 + Ebar * BF0) - Real.log BH0 = Real.log (1 + Ebar * BF0 / BH0) ∧
      0 < Real.log (1 + Ebar * BF0 / BH0) := by
  constructor
  · rw [show 1 + Ebar * BF0 / BH0 = (BH0 + Ebar * BF0) / BH0 by field_simp,
      Real.log_div (by positivity) hB.ne']
  · exact Real.log_pos (by have : 0 < Ebar * BF0 / BH0 := by positivity
                           linarith)

/-! ## Table 8.1 -/

/-- O&R Table 8.1, p. 566: reserves/base ratios recomputed from the GNP shares: Belgium
`12.1/6.7 ≈ 1.806` (printed 180), Norway `18.7/6.3 ≈ 2.968` (printed 297), Ireland
`16.1/9.1 ≈ 1.769` (printed 177). -/
theorem table_8_1_ratios :
    ((1.80 : ℝ) < 12.1 / 6.7 ∧ (12.1 : ℝ) / 6.7 < 1.81) ∧
      ((2.96 : ℝ) < 18.7 / 6.3 ∧ (18.7 : ℝ) / 6.3 < 2.97) ∧
      ((1.76 : ℝ) < 16.1 / 9.1 ∧ (16.1 : ℝ) / 9.1 < 1.77) := by
  norm_num

/-- O&R Table 8.1, p. 566: Italy's printed ratio 48 is not an error: the rounded entries give
`5.6/11.9 ≈ 0.471`, but unrounded values within the rounding intervals (e.g. base `11.85`,
reserves `5.65`) give a ratio that rounds to 48 percent. -/
theorem table_8_1_italy :
    (0.47 : ℝ) < 5.6 / 11.9 ∧ (5.6 : ℝ) / 11.9 < 0.475 ∧
      (0.475 : ℝ) ≤ 5.65 / 11.85 ∧ (5.65 : ℝ) / 11.85 < 0.485 := by
  norm_num

end ObstfeldRogoff.MoneyExchangeRates.SpeculativeAttack
