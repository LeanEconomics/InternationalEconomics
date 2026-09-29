/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NominalRigidities.DornbuschModel
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.MeanValue

/-!
# The Dornbusch model in continuous time

NOT in Obstfeld and Rogoff (1996): the book gives only the discrete-time version (§9.2,
pp. 609–621). This module formalises the continuous-time model of Dornbusch (1976), with the
same building blocks as O&R (1)–(6) and the normalisation `p* = ȳ = i* = 0` of p. 612:
UIP `i = ė`, money demand `m̄ − p = −ηi + φy`, demand `y = δ(e − p − q̄)` and the Mussa Phillips
curve `ṗ = ψy + ė`. With `q = e − p` this reduces to the linear ODE system
`q̇ = −ψδ(q − q̄)`, `ė = [e − m̄ − q̄ − (1−φδ)(q − q̄)]/η`.

Results (T31 of the chapter survey):

* the reduction and its converse;
* the exact global saddle-path theorem: `d = e − m̄ − q̄ − κ(q − q̄)` with the SAME
  `κ = (1−φδ)/(1+ψδη)` as in discrete time satisfies `ḋ = d/η`, so `d(t) = d(0) e^{t/η}` and
  `q(t) − q̄ = (q(0) − q̄) e^{−ψδ t}` (uniqueness of the linear ODE solutions is proved from the
  mean value theorem); for every `q(0)` exactly one `e(0)` gives a convergent (equivalently
  bounded, equivalently no-bubble, `e^{−t/η} e(t) → 0`) path; every other one explodes or
  implodes; `κ` is the unique invariant slope;
* stability needs only `ψδ > 0` (no analogue of the discrete-time bound `ψδ < 2`), and the
  adjustment is always monotone;
* the overshooting formula (17) holds verbatim: after `m̄ → m̄′`,
  `q(0) − q̄ = Δm(1+ψδη)/D` and `e(0) − ē′ = Δm(1−φδ)/D`, overshooting iff `φδ < 1`; the price
  level is `p(t) = m̄′ − e^{−ψδ t}Δm`; output is above `ȳ` at every date (with no condition on
  `ψδ`); and a real shock is absorbed at once.
-/

namespace ObstfeldRogoff.NominalRigidities.DornbuschContinuousTime

open Filter Topology Set Real DornbuschModel DornbuschModel.DornbuschParams

variable (P : DornbuschParams)

/-! ## Linear ODEs on `[0, ∞)` -/

/-- Dornbusch (1976), continuous time (not in O&R): a solution of `ẋ = a x` on `[0, ∞)` (right
derivative at `0`) is `x(t) = x(0) e^{a t}`. Proof: `x(t) e^{−a t}` has zero derivative, so it is
constant by the mean value theorem. -/
theorem linear_ode_unique (a : ℝ) (x : ℝ → ℝ)
    (hx : ∀ t, 0 ≤ t → HasDerivWithinAt x (a * x t) (Ici 0) t) (t : ℝ) (ht : 0 ≤ t) :
    x t = x 0 * exp (a * t) := by
  have hg : ∀ s, 0 ≤ s → HasDerivWithinAt (fun s ↦ x s * exp (-a * s)) 0 (Ici 0) s := by
    intro s hs
    have h2 : HasDerivAt (fun s ↦ exp (-a * s)) (exp (-a * s) * (-a * 1)) s :=
      ((hasDerivAt_id s).const_mul (-a)).exp
    have := (hx s hs).mul h2.hasDerivWithinAt
    convert this using 1
    ring
  have hcont : ContinuousOn (fun s ↦ x s * exp (-a * s)) (Icc 0 t) := fun s hs ↦
    ((hg s hs.1).continuousWithinAt).mono Icc_subset_Ici_self
  have h := constant_of_has_deriv_right_zero hcont
    (fun s hs ↦ (hg s hs.1).mono (Ici_subset_Ici.2 hs.1)) t ⟨ht, le_rfl⟩
  simp only [mul_zero, exp_zero, mul_one] at h
  have e1 : x t = x t * exp (-a * t) * exp (a * t) := by
    rw [mul_assoc, ← exp_add]
    simp
  rw [e1, h]

/-- Continuous time: `e^{−c t} → 0` for `c > 0`. -/
theorem exp_neg_tendsto (c : ℝ) (hc : 0 < c) :
    Tendsto (fun t ↦ exp (-c * t)) atTop (𝓝 0) := by
  have := tendsto_exp_neg_atTop_nhds_zero.comp (tendsto_id.const_mul_atTop hc)
  refine this.congr fun t ↦ ?_
  simp only [Function.comp, id]
  ring_nf

/-- Continuous time: `e^{t/η} → ∞`. -/
theorem exp_growth_tendsto : Tendsto (fun t ↦ exp (1 / P.η * t)) atTop atTop :=
  tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop (by have := P.η_pos; positivity))

/-! ## The model and its reduction -/

/-- Continuous-time Dornbusch model (not in O&R; the analogue of O&R (1)–(6) with
`p* = ȳ = i* = 0` and money constant at `m̄`): for `t ≥ 0`, `e` and `p` have right/two-sided
derivatives `de`, `dp` on `[0, ∞)`, UIP `i = ė`, money demand `m̄ − p = −ηi + φy`, demand
`y = δ(e − p − q̄)`, and the Mussa Phillips curve `ṗ = ψy + ė`. -/
def CTStructural (qbar mbar : ℝ) (e p de dp y i : ℝ → ℝ) : Prop :=
  ∀ t, 0 ≤ t → HasDerivWithinAt e (de t) (Ici 0) t ∧ HasDerivWithinAt p (dp t) (Ici 0) t ∧
    i t = de t ∧ mbar - p t = -P.η * i t + P.φ * y t ∧ y t = P.δ * (e t - p t - qbar) ∧
    dp t = P.ψ * y t + de t

/-- Continuous-time Dornbusch model, reduced form: `q̇ = −ψδ(q − q̄)` and
`ė = [e − m̄ − q̄ − (1−φδ)(q − q̄)]/η` on `[0, ∞)`. -/
def CTReduced (qbar mbar : ℝ) (e q : ℝ → ℝ) : Prop :=
  ∀ t, 0 ≤ t → HasDerivWithinAt q (-(P.ψ * P.δ) * (q t - qbar)) (Ici 0) t ∧
    HasDerivWithinAt e ((e t - mbar - qbar - (1 - P.φ * P.δ) * (q t - qbar)) / P.η) (Ici 0) t

/-- Continuous time: the structural model implies the reduced system for `q = e − p`. -/
theorem ct_structural_to_reduced (qbar mbar : ℝ) (e p de dp y i : ℝ → ℝ)
    (h : CTStructural P qbar mbar e p de dp y i) :
    CTReduced P qbar mbar e (fun t ↦ e t - p t) := by
  intro t ht
  obtain ⟨he, hp, hi, hm, hy, hph⟩ := h t ht
  constructor
  · convert he.sub hp using 1
    rw [hph, hy]
    ring
  · convert he using 1
    rw [hi, hy] at hm
    field_simp [P.η_pos.ne']
    linear_combination -hm

/-- Continuous time: every solution of the reduced system comes from the structural model with
`p = e − q`, `y = δ(q − q̄)` and `i = ė`. -/
theorem ct_reduced_to_structural (qbar mbar : ℝ) (e q : ℝ → ℝ)
    (h : CTReduced P qbar mbar e q) :
    CTStructural P qbar mbar e (fun t ↦ e t - q t)
      (fun t ↦ (e t - mbar - qbar - (1 - P.φ * P.δ) * (q t - qbar)) / P.η)
      (fun t ↦ (e t - mbar - qbar - (1 - P.φ * P.δ) * (q t - qbar)) / P.η +
        P.ψ * P.δ * (q t - qbar))
      (fun t ↦ P.δ * (q t - qbar))
      (fun t ↦ (e t - mbar - qbar - (1 - P.φ * P.δ) * (q t - qbar)) / P.η) := by
  intro t ht
  obtain ⟨hq, he⟩ := h t ht
  refine ⟨he, ?_, rfl, ?_, by ring, by ring⟩
  · convert he.sub hq using 1
    ring
  · field_simp [P.η_pos.ne']
    ring

/-! ## The exact saddle-path theorem -/

/-- Continuous time (T31): the saddle deviation `d = e − m̄ − q̄ − κ(q − q̄)`. -/
noncomputable def ctDev (qbar mbar : ℝ) (e q : ℝ → ℝ) (t : ℝ) : ℝ :=
  e t - (mbar + qbar) - P.κ * (q t - qbar)

/-- Continuous time (T31, exact): along any solution, `ḋ = d/η`, with the SAME `κ` as in
discrete time. -/
theorem ctDev_deriv (qbar mbar : ℝ) (e q : ℝ → ℝ) (h : CTReduced P qbar mbar e q) (t : ℝ)
    (ht : 0 ≤ t) :
    HasDerivWithinAt (ctDev P qbar mbar e q) (1 / P.η * ctDev P qbar mbar e q t) (Ici 0) t := by
  obtain ⟨hq, he⟩ := h t ht
  have := (he.sub_const (mbar + qbar)).sub ((hq.sub_const qbar).const_mul P.κ)
  unfold ctDev
  convert this using 1
  have hκ := P.κ_mul
  field_simp [P.η_pos.ne']
  linear_combination -(q t - qbar) * hκ

/-- Continuous time: `q(t) − q̄ = (q(0) − q̄) e^{−ψδ t}` along any solution. -/
theorem ct_q_closed_form (qbar mbar : ℝ) (e q : ℝ → ℝ) (h : CTReduced P qbar mbar e q) (t : ℝ)
    (ht : 0 ≤ t) : q t - qbar = (q 0 - qbar) * exp (-(P.ψ * P.δ) * t) :=
  linear_ode_unique (-(P.ψ * P.δ)) (fun t ↦ q t - qbar)
    (fun s hs ↦ ((h s hs).1.sub_const qbar)) t ht

/-- Continuous time (T31): `d(t) = d(0) e^{t/η}` along any solution. -/
theorem ct_dev_closed_form (qbar mbar : ℝ) (e q : ℝ → ℝ) (h : CTReduced P qbar mbar e q)
    (t : ℝ) (ht : 0 ≤ t) :
    ctDev P qbar mbar e q t = ctDev P qbar mbar e q 0 * exp (1 / P.η * t) :=
  linear_ode_unique (1 / P.η) _ (fun s hs ↦ ctDev_deriv P qbar mbar e q h s hs) t ht

/-- Continuous time (T31): every solution is
`e(t) = m̄ + q̄ + κ(q(0) − q̄)e^{−ψδ t} + d(0) e^{t/η}`. -/
theorem ct_e_closed_form (qbar mbar : ℝ) (e q : ℝ → ℝ) (h : CTReduced P qbar mbar e q) (t : ℝ)
    (ht : 0 ≤ t) :
    e t = mbar + qbar + P.κ * ((q 0 - qbar) * exp (-(P.ψ * P.δ) * t)) +
      ctDev P qbar mbar e q 0 * exp (1 / P.η * t) := by
  rw [← ct_dev_closed_form P qbar mbar e q h t ht, ← ct_q_closed_form P qbar mbar e q h t ht]
  unfold ctDev
  ring

/-- Continuous time: the real exchange rate converges to `q̄` for every `ψδ > 0` (no analogue
of the discrete-time stability bound `ψδ < 2`). -/
theorem ct_q_tendsto (qbar mbar : ℝ) (e q : ℝ → ℝ) (h : CTReduced P qbar mbar e q) :
    Tendsto q atTop (𝓝 qbar) := by
  have h1 := ((exp_neg_tendsto (P.ψ * P.δ) P.ψδ_pos).const_mul (q 0 - qbar)).const_add qbar
  rw [mul_zero, add_zero] at h1
  refine h1.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with t ht
  have := ct_q_closed_form P qbar mbar e q h t ht
  linarith

/-- Continuous time: the adjustment of `q` is monotone: `q(t) − q̄` keeps the sign of
`q(0) − q̄` and `|q(t) − q̄|` is nonincreasing. -/
theorem ct_q_monotone (qbar mbar : ℝ) (e q : ℝ → ℝ) (h : CTReduced P qbar mbar e q) (s t : ℝ)
    (hs : 0 ≤ s) (hst : s ≤ t) :
    0 ≤ (q t - qbar) * (q 0 - qbar) ∧ |q t - qbar| ≤ |q s - qbar| := by
  rw [ct_q_closed_form P qbar mbar e q h t (hs.trans hst), ct_q_closed_form P qbar mbar e q h s hs]
  constructor
  · have := exp_pos (-(P.ψ * P.δ) * t)
    nlinarith [mul_self_nonneg (q 0 - qbar)]
  · rw [abs_mul, abs_mul, abs_of_pos (exp_pos _), abs_of_pos (exp_pos _)]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    apply exp_le_exp.2
    have := P.ψδ_pos
    nlinarith

/-- Continuous time (T31): the explicit solution through `(q(0), d(0))`. -/
noncomputable def ctSolE (qbar mbar q0 d0 : ℝ) (t : ℝ) : ℝ :=
  mbar + qbar + P.κ * ((q0 - qbar) * exp (-(P.ψ * P.δ) * t)) + d0 * exp (1 / P.η * t)

/-- Continuous time (T31): the explicit real exchange rate `q̄ + (q(0) − q̄)e^{−ψδ t}`. -/
noncomputable def ctSolQ (qbar q0 : ℝ) (t : ℝ) : ℝ := qbar + (q0 - qbar) * exp (-(P.ψ * P.δ) * t)

/-- Continuous time (T31): the explicit paths solve the reduced system for every
`(q(0), d(0))`. -/
theorem ct_sol_reduced (qbar mbar q0 d0 : ℝ) :
    CTReduced P qbar mbar (ctSolE P qbar mbar q0 d0) (ctSolQ P qbar q0) := by
  intro t _
  have h1 : HasDerivAt (fun t ↦ exp (-(P.ψ * P.δ) * t))
      (exp (-(P.ψ * P.δ) * t) * (-(P.ψ * P.δ) * 1)) t :=
    ((hasDerivAt_id t).const_mul (-(P.ψ * P.δ))).exp
  have h2 : HasDerivAt (fun t ↦ exp (1 / P.η * t)) (exp (1 / P.η * t) * (1 / P.η * 1)) t :=
    ((hasDerivAt_id t).const_mul (1 / P.η)).exp
  constructor
  · have := ((h1.const_mul (q0 - qbar)).const_add qbar).hasDerivWithinAt (s := Ici 0)
    unfold ctSolQ
    convert this using 1
    ring
  · have := ((((h1.const_mul (q0 - qbar)).const_mul P.κ).const_add (mbar + qbar)).add
      (h2.const_mul d0)).hasDerivWithinAt (s := Ici 0)
    unfold ctSolE ctSolQ
    convert this using 1
    have hκ := P.κ_mul
    set E := exp (-(P.ψ * P.δ) * t)
    set F := exp (1 / P.η * t)
    field_simp [P.η_pos.ne']
    linear_combination (q0 - qbar) * E * hκ

/-- Continuous time (T31): a solution is determined by `(e(0), q(0))` on `[0, ∞)`. -/
theorem ct_unique_of_init (qbar mbar : ℝ) (e q e' q' : ℝ → ℝ) (h : CTReduced P qbar mbar e q)
    (h' : CTReduced P qbar mbar e' q') (he : e 0 = e' 0) (hq : q 0 = q' 0) (t : ℝ)
    (ht : 0 ≤ t) : e t = e' t ∧ q t = q' t := by
  have h1 := ct_q_closed_form P qbar mbar e q h t ht
  have h2 := ct_q_closed_form P qbar mbar e' q' h' t ht
  rw [ct_e_closed_form P qbar mbar e q h t ht, ct_e_closed_form P qbar mbar e' q' h' t ht]
  unfold ctDev
  rw [he, hq]
  rw [hq] at h1
  exact ⟨rfl, by linarith⟩

/-- Continuous time (T31): above the saddle path (`d(0) > 0`) the exchange rate explodes. -/
theorem ct_explodes (qbar mbar : ℝ) (e q : ℝ → ℝ) (h : CTReduced P qbar mbar e q)
    (hd : 0 < ctDev P qbar mbar e q 0) : Tendsto e atTop atTop := by
  have h1 := (exp_growth_tendsto P).atTop_mul_const hd
  have h2 : Tendsto (fun t ↦ mbar + qbar + P.κ * ((q 0 - qbar) * exp (-(P.ψ * P.δ) * t)))
      atTop (𝓝 (mbar + qbar + P.κ * ((q 0 - qbar) * 0))) :=
    (((exp_neg_tendsto (P.ψ * P.δ) P.ψδ_pos).const_mul _).const_mul _).const_add _
  refine (h1.atTop_add h2).congr' ?_
  filter_upwards [eventually_ge_atTop 0] with t ht
  rw [ct_e_closed_form P qbar mbar e q h t ht]
  ring

/-- Continuous time (T31): below the saddle path (`d(0) < 0`) the exchange rate implodes. -/
theorem ct_implodes (qbar mbar : ℝ) (e q : ℝ → ℝ) (h : CTReduced P qbar mbar e q)
    (hd : ctDev P qbar mbar e q 0 < 0) : Tendsto e atTop atBot := by
  have h1 := (exp_growth_tendsto P).atTop_mul_const_of_neg hd
  have h2 : Tendsto (fun t ↦ mbar + qbar + P.κ * ((q 0 - qbar) * exp (-(P.ψ * P.δ) * t)))
      atTop (𝓝 (mbar + qbar + P.κ * ((q 0 - qbar) * 0))) :=
    (((exp_neg_tendsto (P.ψ * P.δ) P.ψδ_pos).const_mul _).const_mul _).const_add _
  refine (h1.atBot_add h2).congr' ?_
  filter_upwards [eventually_ge_atTop 0] with t ht
  rw [ct_e_closed_form P qbar mbar e q h t ht]
  ring

/-- Continuous time (T31): a solution converges to the steady state `(m̄ + q̄, q̄)` iff it starts
on the saddle path `e(0) = m̄ + q̄ + κ(q(0) − q̄)`. -/
theorem ct_converges_iff (qbar mbar : ℝ) (e q : ℝ → ℝ) (h : CTReduced P qbar mbar e q) :
    Tendsto e atTop (𝓝 (mbar + qbar)) ↔ e 0 = mbar + qbar + P.κ * (q 0 - qbar) := by
  constructor
  · intro hc
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact not_tendsto_nhds_of_tendsto_atBot
        (ct_implodes P qbar mbar e q h (by unfold ctDev; linarith)) _ hc
    · exact not_tendsto_nhds_of_tendsto_atTop
        (ct_explodes P qbar mbar e q h (by unfold ctDev; linarith)) _ hc
  · intro h0
    have h2 : Tendsto (fun t ↦ mbar + qbar + P.κ * ((q 0 - qbar) * exp (-(P.ψ * P.δ) * t)))
        atTop (𝓝 (mbar + qbar + P.κ * ((q 0 - qbar) * 0))) :=
      (((exp_neg_tendsto (P.ψ * P.δ) P.ψδ_pos).const_mul _).const_mul _).const_add _
    simp only [mul_zero, add_zero] at h2
    refine h2.congr' ?_
    filter_upwards [eventually_ge_atTop 0] with t ht
    have hz : ctDev P qbar mbar e q 0 = 0 := by unfold ctDev; rw [h0]; ring
    rw [ct_e_closed_form P qbar mbar e q h t ht, hz]
    ring

/-- Continuous time (T31): a solution is bounded on `[0, ∞)` iff it starts on the saddle
path. -/
theorem ct_bounded_iff (qbar mbar : ℝ) (e q : ℝ → ℝ) (h : CTReduced P qbar mbar e q) :
    (∃ B, ∀ t, 0 ≤ t → |e t| ≤ B) ↔ e 0 = mbar + qbar + P.κ * (q 0 - qbar) := by
  constructor
  · rintro ⟨B, hB⟩
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · obtain ⟨t, ht⟩ := ((tendsto_atBot.1 (ct_implodes P qbar mbar e q h
        (by unfold ctDev; linarith)) (-B - 1)).and (eventually_ge_atTop 0)).exists
      have := neg_abs_le (e t)
      linarith [hB t ht.2, ht.1]
    · obtain ⟨t, ht⟩ := ((tendsto_atTop.1 (ct_explodes P qbar mbar e q h
        (by unfold ctDev; linarith)) (B + 1)).and (eventually_ge_atTop 0)).exists
      have := le_abs_self (e t)
      linarith [hB t ht.2, ht.1]
  · intro h0
    refine ⟨|mbar + qbar| + |P.κ| * |q 0 - qbar|, fun t ht ↦ ?_⟩
    have hz : ctDev P qbar mbar e q 0 = 0 := by unfold ctDev; rw [h0]; ring
    rw [ct_e_closed_form P qbar mbar e q h t ht, hz, zero_mul, add_zero]
    have hexp : exp (-(P.ψ * P.δ) * t) ≤ 1 := by
      rw [exp_le_one_iff]
      have := P.ψδ_pos
      nlinarith
    calc |mbar + qbar + P.κ * ((q 0 - qbar) * exp (-(P.ψ * P.δ) * t))|
        ≤ |mbar + qbar| + |P.κ| * (|q 0 - qbar| * exp (-(P.ψ * P.δ) * t)) := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_mul, abs_of_pos (exp_pos _)]
      _ ≤ |mbar + qbar| + |P.κ| * (|q 0 - qbar| * 1) := by gcongr
      _ = |mbar + qbar| + |P.κ| * |q 0 - qbar| := by ring

/-- Continuous time (T31): along every solution `e^{−t/η} e(t) → d(0)`. -/
theorem ct_discounted_e_tendsto (qbar mbar : ℝ) (e q : ℝ → ℝ) (h : CTReduced P qbar mbar e q) :
    Tendsto (fun t ↦ exp (-(1 / P.η) * t) * e t) atTop (𝓝 (ctDev P qbar mbar e q 0)) := by
  have hη : 0 < 1 / P.η := by have := P.η_pos; positivity
  have h1 := (exp_neg_tendsto (1 / P.η) hη).mul_const (mbar + qbar)
  have h2 := (exp_neg_tendsto (P.ψ * P.δ + 1 / P.η) (by linarith [P.ψδ_pos])).mul_const
    (P.κ * (q 0 - qbar))
  have h3 := (h1.add h2).add_const (ctDev P qbar mbar e q 0)
  simp only [zero_mul, add_zero, zero_add] at h3
  refine h3.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with t ht
  rw [ct_e_closed_form P qbar mbar e q h t ht]
  have e1 : exp (-(P.ψ * P.δ + 1 / P.η) * t) =
      exp (-(1 / P.η) * t) * exp (-(P.ψ * P.δ) * t) := by rw [← exp_add]; ring_nf
  have e2 : exp (-(1 / P.η) * t) * exp (1 / P.η * t) = 1 := by rw [← exp_add]; simp
  rw [e1]
  linear_combination (-(ctDev P qbar mbar e q 0)) * e2

/-- Continuous time (T31): the no-bubble condition `e^{−t/η} e(t) → 0` holds iff the solution
starts on the saddle path. -/
theorem ct_no_bubble_iff (qbar mbar : ℝ) (e q : ℝ → ℝ) (h : CTReduced P qbar mbar e q) :
    Tendsto (fun t ↦ exp (-(1 / P.η) * t) * e t) atTop (𝓝 0) ↔
      e 0 = mbar + qbar + P.κ * (q 0 - qbar) := by
  have h1 := ct_discounted_e_tendsto P qbar mbar e q h
  constructor
  · intro h2
    have := tendsto_nhds_unique h1 h2
    unfold ctDev at this
    linarith
  · intro h0
    have hz : ctDev P qbar mbar e q 0 = 0 := by unfold ctDev; rw [h0]; ring
    rw [hz] at h1
    exact h1

/-- Continuous time (T31, the saddle-path theorem): for every `q(0)` exactly one `e(0)` gives a
convergent solution, namely `e(0) = m̄ + q̄ + κ(q(0) − q̄)` (the analogue of O&R (16)). -/
theorem ct_saddle_path_theorem (qbar mbar q0 : ℝ) :
    ∃! e0 : ℝ, ∃ e q : ℝ → ℝ, e 0 = e0 ∧ q 0 = q0 ∧ CTReduced P qbar mbar e q ∧
      Tendsto e atTop (𝓝 (mbar + qbar)) := by
  refine ⟨mbar + qbar + P.κ * (q0 - qbar), ⟨ctSolE P qbar mbar q0 0, ctSolQ P qbar q0,
    by unfold ctSolE; simp, by unfold ctSolQ; simp, ct_sol_reduced P qbar mbar q0 0, ?_⟩, ?_⟩
  · rw [ct_converges_iff P qbar mbar _ _ (ct_sol_reduced P qbar mbar q0 0)]
    unfold ctSolE ctSolQ
    simp
  · rintro e0 ⟨e, q, he, hq, hr, hc⟩
    rw [ct_converges_iff P qbar mbar e q hr, he, hq] at hc
    exact hc

/-- Continuous time (T31): the saddle slope is unique. A slope `k` makes `ê − k q̂` evolve
autonomously at rate `1/η` from every state iff `k = κ`. -/
theorem ct_saddle_slope_unique (k : ℝ) :
    (∀ ehat qhat : ℝ, (ehat - (1 - P.φ * P.δ) * qhat) / P.η - k * (-(P.ψ * P.δ) * qhat) =
      1 / P.η * (ehat - k * qhat)) ↔ k = P.κ := by
  have hη := P.η_pos.ne'
  have hd := P.slope_denom_pos.ne'
  constructor
  · intro h
    have h1 := h 0 1
    field_simp at h1
    unfold κ
    rw [eq_div_iff hd]
    linear_combination h1
  · rintro rfl ehat qhat
    have hκ := P.κ_mul
    field_simp
    linear_combination qhat * hκ

/-! ## Unanticipated shocks: overshooting in continuous time -/

/-- Continuous time: the equilibrium after an unanticipated permanent money change `m̄ → m̄′` at
`t = 0` from the steady state: the post-shock reduced system, the predetermined price level
`p(0) = e(0) − q(0) = m̄`, and the no-bubble condition. -/
def CTPermShock (qbar mbar mbar' : ℝ) (e q : ℝ → ℝ) : Prop :=
  CTReduced P qbar mbar' e q ∧ e 0 - q 0 = mbar ∧
    Tendsto (fun t ↦ exp (-(1 / P.η) * t) * e t) atTop (𝓝 0)

/-- Continuous time (T31): the overshooting formula (17) holds verbatim:
`q(0) − q̄ = Δm(1+ψδη)/D` and `e(0) − ē′ = Δm(1−φδ)/D`. -/
theorem ct_perm_shock_impact (qbar mbar mbar' : ℝ) (e q : ℝ → ℝ)
    (h : CTPermShock P qbar mbar mbar' e q) :
    q 0 - qbar = (mbar' - mbar) * (1 + P.ψ * P.δ * P.η) / P.D ∧
      e 0 - (mbar' + qbar) = (mbar' - mbar) * (1 - P.φ * P.δ) / P.D := by
  obtain ⟨hr, hp, hb⟩ := h
  have h0 := (ct_no_bubble_iff P qbar mbar' e q hr).1 hb
  have hq : q 0 - qbar = (mbar' - mbar) * (1 + P.ψ * P.δ * P.η) / P.D := by
    have h1 : (1 - P.κ) * (q 0 - qbar) = mbar' - mbar := by linear_combination h0 - hp
    rw [P.one_sub_κ, div_mul_eq_mul_div, div_eq_iff P.slope_denom_pos.ne'] at h1
    rw [eq_div_iff P.D_pos.ne']
    linarith
  refine ⟨hq, ?_⟩
  have : e 0 - (mbar' + qbar) = P.κ * (q 0 - qbar) := by linarith
  rw [this, hq, ← P.κ_mul]
  ring

/-- Continuous time (T31): for `Δm > 0`, overshooting iff `φδ < 1`, exact adjustment iff
`φδ = 1`, undershooting iff `φδ > 1`. -/
theorem ct_overshooting_iff (qbar mbar mbar' : ℝ) (e q : ℝ → ℝ)
    (h : CTPermShock P qbar mbar mbar' e q) (hΔ : mbar < mbar') :
    (mbar' + qbar < e 0 ↔ P.φ * P.δ < 1) ∧ (e 0 = mbar' + qbar ↔ P.φ * P.δ = 1) ∧
      (e 0 < mbar' + qbar ↔ 1 < P.φ * P.δ) := by
  have hi := (ct_perm_shock_impact P qbar mbar mbar' e q h).2
  have hD := P.D_pos
  have hpos : 0 < mbar' - mbar := by linarith
  have key : ∀ c : ℝ, 0 < (mbar' - mbar) * c / P.D ↔ 0 < c := fun c ↦ by
    rw [div_pos_iff_of_pos_right hD]
    exact ⟨fun h1 ↦ pos_of_mul_pos_right h1 hpos.le, fun h1 ↦ mul_pos hpos h1⟩
  refine ⟨?_, ?_, ?_⟩
  · have := key (1 - P.φ * P.δ)
    constructor
    · intro h1; have := this.1 (by linarith); linarith
    · intro h1; have := this.2 (by linarith); linarith
  · constructor
    · intro h1
      rw [h1, sub_self] at hi
      rcases mul_eq_zero.1 ((div_eq_zero_iff.1 hi.symm).resolve_right hD.ne') with h2 | h2
      · linarith
      · linarith
    · intro h1
      rw [h1, sub_self, mul_zero, zero_div] at hi
      linarith
  · have := key (P.φ * P.δ - 1)
    have e1 : (mbar' - mbar) * (P.φ * P.δ - 1) / P.D = -((mbar' - mbar) * (1 - P.φ * P.δ) / P.D)
      := by ring
    rw [e1, ← hi] at this
    constructor
    · intro h1; exact sub_pos.1 (this.1 (by linarith))
    · intro h1; have := this.2 (by linarith); linarith

/-- Continuous time (T31): the post-shock paths,
`e(t) = m̄′ + q̄ + e^{−ψδ t}(1−φδ)Δm/D`, `q(t) − q̄ = e^{−ψδ t}(1+ψδη)Δm/D` and the price level
`p(t) = e(t) − q(t) = m̄′ − e^{−ψδ t}Δm`. -/
theorem ct_perm_shock_path (qbar mbar mbar' : ℝ) (e q : ℝ → ℝ)
    (h : CTPermShock P qbar mbar mbar' e q) (t : ℝ) (ht : 0 ≤ t) :
    e t = mbar' + qbar + exp (-(P.ψ * P.δ) * t) * ((mbar' - mbar) * (1 - P.φ * P.δ) / P.D) ∧
      q t - qbar = exp (-(P.ψ * P.δ) * t) * ((mbar' - mbar) * (1 + P.ψ * P.δ * P.η) / P.D) ∧
      e t - q t = mbar' - exp (-(P.ψ * P.δ) * t) * (mbar' - mbar) := by
  have hi := ct_perm_shock_impact P qbar mbar mbar' e q h
  obtain ⟨hr, -, hb⟩ := h
  have h0 := (ct_no_bubble_iff P qbar mbar' e q hr).1 hb
  have hz : ctDev P qbar mbar' e q 0 = 0 := by unfold ctDev; rw [h0]; ring
  have he := ct_e_closed_form P qbar mbar' e q hr t ht
  have hq := ct_q_closed_form P qbar mbar' e q hr t ht
  rw [hz, zero_mul, add_zero] at he
  have hq' : q t - qbar = exp (-(P.ψ * P.δ) * t) *
      ((mbar' - mbar) * (1 + P.ψ * P.δ * P.η) / P.D) := by rw [hq, hi.1]; ring
  have he' : e t = mbar' + qbar + exp (-(P.ψ * P.δ) * t) *
      ((mbar' - mbar) * (1 - P.φ * P.δ) / P.D) := by
    rw [he, hi.1, ← P.κ_mul]; ring
  refine ⟨he', hq', ?_⟩
  have hD := P.D_pos.ne'
  have : (mbar' - mbar) * (1 - P.φ * P.δ) / P.D -
      (mbar' - mbar) * (1 + P.ψ * P.δ * P.η) / P.D = -(mbar' - mbar) := by
    field_simp
    unfold D
    ring
  linear_combination he' - hq' + exp (-(P.ψ * P.δ) * t) * this

/-- Continuous time (T31): after a money increase, output `y = δ(q − q̄)` is above its natural
rate at every date, with NO condition on `ψδ` (in discrete time `ψδ < 1` is needed). -/
theorem ct_perm_shock_output_pos (qbar mbar mbar' : ℝ) (e q : ℝ → ℝ)
    (h : CTPermShock P qbar mbar mbar' e q) (hΔ : mbar < mbar') (t : ℝ) (ht : 0 ≤ t) :
    0 < P.δ * (q t - qbar) := by
  rw [(ct_perm_shock_path P qbar mbar mbar' e q h t ht).2.1]
  exact mul_pos P.δ_pos (mul_pos (exp_pos _)
    (div_pos (mul_pos (by linarith) P.slope_denom_pos) P.D_pos))

/-- Continuous time (T31): the nominal interest rate `i = ė` after the shock is
`−ψδ e^{−ψδ t}(1−φδ)Δm/D`; with `Δm > 0` it is below `i* = 0` iff there is overshooting. -/
theorem ct_perm_shock_interest (qbar mbar mbar' : ℝ) (e q : ℝ → ℝ)
    (h : CTPermShock P qbar mbar mbar' e q) (t : ℝ) (ht : 0 ≤ t) :
    (e t - mbar' - qbar - (1 - P.φ * P.δ) * (q t - qbar)) / P.η =
      -(P.ψ * P.δ) * exp (-(P.ψ * P.δ) * t) * ((mbar' - mbar) * (1 - P.φ * P.δ) / P.D) := by
  obtain ⟨he, hq, -⟩ := ct_perm_shock_path P qbar mbar mbar' e q h t ht
  rw [he, hq]
  have hD := P.D_pos.ne'
  field_simp [P.η_pos.ne']
  unfold D
  ring

/-- Continuous time (T31): long-run neutrality, `e → m̄′ + q̄`, `q → q̄`, `p → m̄′`. -/
theorem ct_perm_shock_long_run (qbar mbar mbar' : ℝ) (e q : ℝ → ℝ)
    (h : CTPermShock P qbar mbar mbar' e q) :
    Tendsto e atTop (𝓝 (mbar' + qbar)) ∧ Tendsto (fun t ↦ e t - q t) atTop (𝓝 mbar') := by
  have hx := exp_neg_tendsto (P.ψ * P.δ) P.ψδ_pos
  constructor
  · have := (hx.mul_const ((mbar' - mbar) * (1 - P.φ * P.δ) / P.D)).const_add (mbar' + qbar)
    rw [zero_mul, add_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 0] with t ht
    exact (ct_perm_shock_path P qbar mbar mbar' e q h t ht).1.symm
  · have := (hx.mul_const (mbar' - mbar)).const_sub mbar'
    rw [zero_mul, sub_zero] at this
    refine this.congr' ?_
    filter_upwards [eventually_ge_atTop 0] with t ht
    exact (ct_perm_shock_path P qbar mbar mbar' e q h t ht).2.2.symm

/-- Continuous time (T31): the permanent-shock equilibrium exists and is unique on `[0, ∞)`. -/
theorem ct_perm_shock_exists_unique (qbar mbar mbar' : ℝ) :
    (∃ e q : ℝ → ℝ, CTPermShock P qbar mbar mbar' e q) ∧
      ∀ e q e' q' : ℝ → ℝ, CTPermShock P qbar mbar mbar' e q →
        CTPermShock P qbar mbar mbar' e' q' → ∀ t, 0 ≤ t → e t = e' t ∧ q t = q' t := by
  constructor
  · set q0 := qbar + (mbar' - mbar) * (1 + P.ψ * P.δ * P.η) / P.D
    refine ⟨ctSolE P qbar mbar' q0 0, ctSolQ P qbar q0, ct_sol_reduced P qbar mbar' q0 0, ?_,
      ?_⟩
    · unfold ctSolE ctSolQ
      simp only [mul_zero, exp_zero, mul_one, add_zero]
      have h1 : (1 - P.κ) * ((mbar' - mbar) * (1 + P.ψ * P.δ * P.η) / P.D) = mbar' - mbar := by
        rw [P.one_sub_κ]
        have hD := P.D_pos.ne'
        have hA := P.slope_denom_pos.ne'
        set A := 1 + P.ψ * P.δ * P.η
        field_simp
      simp only [q0]
      linear_combination -h1
    · rw [ct_no_bubble_iff P qbar mbar' _ _ (ct_sol_reduced P qbar mbar' q0 0)]
      unfold ctSolE ctSolQ
      simp
  · intro e q e' q' h h' t ht
    have h1 := ct_perm_shock_path P qbar mbar mbar' e q h t ht
    have h2 := ct_perm_shock_path P qbar mbar mbar' e' q' h' t ht
    exact ⟨by rw [h1.1, h2.1], by linarith [h1.2.1, h2.2.1]⟩

/-- Continuous time (O&R fn 11 analogue): after an unanticipated real shock `q̄ → q̄′` with money
constant at `m̄` (`p(0) = m̄`), the no-bubble equilibrium jumps at once to the new steady state:
`e(t) = m̄ + q̄′` and `q(t) = q̄′`. -/
theorem ct_real_shock (qbar' mbar : ℝ) (e q : ℝ → ℝ) (h : CTPermShock P qbar' mbar mbar e q)
    (t : ℝ) (ht : 0 ≤ t) : e t = mbar + qbar' ∧ q t = qbar' := by
  obtain ⟨he, hq, -⟩ := ct_perm_shock_path P qbar' mbar mbar e q h t ht
  simp only [sub_self, zero_mul, mul_zero, zero_div, add_zero] at he hq
  exact ⟨he, by linarith⟩

end ObstfeldRogoff.NominalRigidities.DornbuschContinuousTime
