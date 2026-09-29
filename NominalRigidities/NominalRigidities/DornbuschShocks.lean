/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NominalRigidities.DornbuschModel

/-!
# Unanticipated shocks in the Dornbusch model: overshooting and interest rates

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §9.2.2–9.2.5,
pp. 613–621, and Exercise 1, p. 657.

An unanticipated shock at date 0 is modelled as two regimes. Before the shock the economy is in
its (flexible-price) steady state, which fixes the predetermined price level `p_0`. After the
shock the economy follows the reduced system (7)–(8) with the new money path and satisfies the
no-bubble condition. By `DornbuschModel.no_bubble_iff_dev_zero` this places it on the new
saddle path, so every impact effect is linear algebra in `(q_0, e_0)`.

The master result (`shock_impact`, `shock_exists_unique`): if the shock moves the flexible-price
price level `e^flex_0 − q̄` above the predetermined `p_0` by `Δ`, then
`q_0 − q̄ = e_0 − ...` jumps by `Δ(1+ψδη)/D` and `e_0 − e^flex_0 = Δ(1−φδ)/D`. Corollaries:

* permanent money shocks: overshooting iff `φδ < 1`, the exact path, output, the impact interest
  rate, the money-market check of p. 614 and long-run neutrality (T6, (11)–(12), (17));
* real shocks, fn 11 (T7);
* general money processes (18)–(21), amplification `1/(1−κ) > 1 ⟺ φδ < 1` and its reading as
  a conditional variance on a finite state space (T8);
* money-growth shocks (22)–(23) and the positive impact response of the nominal rate (T9);
* the real-interest relations (24), (25) and fn 17 (T10);
* Exercise 1 (disinflation), both readings of its money path, and the level jump that disinflates
  with no slump.
-/

namespace ObstfeldRogoff.NominalRigidities.DornbuschShocks

open Filter Topology DornbuschModel DornbuschModel.DornbuschParams

variable (P : DornbuschParams)

/-! ## The master impact theorem -/

/-- O&R §9.2.2–9.2.4, pp. 613 and 618: an equilibrium after an unanticipated shock at date 0.
The post-shock economy solves (7)–(8) with money path `m` and equilibrium real exchange rate `q̄`,
the price level `p_0 = e_0 − q_0` is predetermined at `p0` (eq. (12) and its generalisation
`q_0 = e_0 − p^flex_0`, p. 618), and the no-bubble condition holds. -/
def ShockEqm (qbar : ℝ) (m : ℕ → ℝ) (p0 : ℝ) (e q : ℕ → ℝ) : Prop :=
  Reduced P qbar m e q ∧ e 0 - q 0 = p0 ∧ NoBubble P e

/-- O&R (17), (20): solving `(1 − κ) x = Δ` gives `x = Δ(1+ψδη)/D`. -/
theorem solve_one_sub_κ (x Δ : ℝ) (h : (1 - P.κ) * x = Δ) :
    x = Δ * (1 + P.ψ * P.δ * P.η) / P.D := by
  rw [P.one_sub_κ, div_mul_eq_mul_div, div_eq_iff P.slope_denom_pos.ne'] at h
  rw [eq_div_iff P.D_pos.ne']
  linarith

/-- O&R (17): `κ · Δ(1+ψδη)/D = Δ(1−φδ)/D`. -/
theorem κ_mul_impact (Δ : ℝ) :
    P.κ * (Δ * (1 + P.ψ * P.δ * P.η) / P.D) = Δ * (1 - P.φ * P.δ) / P.D := by
  rw [← P.κ_mul]
  ring

/-- O&R (17), (20): `(1 − κ) · Δ(1+ψδη)/D = Δ`. -/
theorem one_sub_κ_mul_impact (Δ : ℝ) :
    (1 - P.κ) * (Δ * (1 + P.ψ * P.δ * P.η) / P.D) = Δ := by
  have hD := P.D_pos.ne'
  have hA := P.slope_denom_pos.ne'
  rw [P.one_sub_κ]
  set A := 1 + P.ψ * P.δ * P.η
  field_simp

/-- O&R (20), p. 618, master impact theorem: in any post-shock equilibrium, with
`Δ = (e^flex_0 − q̄) − p_0` the shock to the flexible-price price level,
`q_0 − q̄ = Δ(1+ψδη)/D` and `e_0 − e^flex_0 = Δ(1−φδ)/D`. -/
theorem shock_impact (qbar : ℝ) (m : ℕ → ℝ) (p0 : ℝ) (e q : ℕ → ℝ)
    (hm : Summable fun s ↦ P.r ^ s * m s) (hs : P.ψ * P.δ < 2) (h : ShockEqm P qbar m p0 e q) :
    q 0 - qbar = (eflex P qbar m 0 - qbar - p0) * (1 + P.ψ * P.δ * P.η) / P.D ∧
      e 0 - eflex P qbar m 0 = (eflex P qbar m 0 - qbar - p0) * (1 - P.φ * P.δ) / P.D := by
  obtain ⟨hr, hp, hb⟩ := h
  have h18 := eighteen P qbar m e q hm hr hs hb 0
  have hq : q 0 - qbar = (eflex P qbar m 0 - qbar - p0) * (1 + P.ψ * P.δ * P.η) / P.D := by
    apply solve_one_sub_κ
    linear_combination h18 - hp
  refine ⟨hq, ?_⟩
  rw [h18, hq, κ_mul_impact]

/-- O&R (13), (21): the post-shock path, `q_t − q̄ = ρ^t (q_0 − q̄)` and
`e_t − e^flex_t = ρ^t (e_0 − e^flex_0)`. -/
theorem shock_path (qbar : ℝ) (m : ℕ → ℝ) (p0 : ℝ) (e q : ℕ → ℝ)
    (hm : Summable fun s ↦ P.r ^ s * m s) (hs : P.ψ * P.δ < 2) (h : ShockEqm P qbar m p0 e q)
    (t : ℕ) : q t - qbar = P.ρ ^ t * (q 0 - qbar) ∧
      e t - eflex P qbar m t = P.ρ ^ t * (e 0 - eflex P qbar m 0) := by
  obtain ⟨hr, -, hb⟩ := h
  refine ⟨q_closed_form P qbar m e q hr t, ?_⟩
  rw [eighteen P qbar m e q hm hr hs hb t, eighteen P qbar m e q hm hr hs hb 0,
    q_closed_form P qbar m e q hr t]
  ring

/-- O&R §9.2.2–9.2.4: for any summable post-shock money path and any predetermined price
level, the post-shock equilibrium exists and is unique. -/
theorem shock_exists_unique (qbar : ℝ) (m : ℕ → ℝ) (p0 : ℝ)
    (hm : Summable fun s ↦ P.r ^ s * m s) (hs : P.ψ * P.δ < 2) :
    ∃! x : (ℕ → ℝ) × (ℕ → ℝ), ShockEqm P qbar m p0 x.1 x.2 := by
  obtain ⟨⟨e, q⟩, ⟨hq0, hr, hb⟩, huniq⟩ := exists_unique_no_bubble P qbar m hm hs
    (qbar + (eflex P qbar m 0 - qbar - p0) * (1 + P.ψ * P.δ * P.η) / P.D)
  refine ⟨(e, q), ⟨hr, ?_, hb⟩, ?_⟩
  · have h18 := eighteen P qbar m e q hm hr hs hb 0
    have h1 := one_sub_κ_mul_impact P (eflex P qbar m 0 - qbar - p0)
    simp only at hq0 h18 ⊢
    rw [hq0] at h18 ⊢
    linear_combination h18 - h1
  · rintro ⟨e', q'⟩ hx
    obtain ⟨hr', hp', hb'⟩ := hx
    apply huniq
    refine ⟨?_, hr', hb'⟩
    have := (shock_impact P qbar m p0 e' q' hm hs ⟨hr', hp', hb'⟩).1
    simp only
    linarith

/-! ## T6: a permanent money shock (overshooting / undershooting) -/

/-- O&R (11)–(12), (17), p. 617: after `m̄ → m̄′` from the steady state (`p_0 = m̄`), the impact
effects are `q_0 − q̄ = Δm(1+ψδη)/D`, `e_0 = m̄ + q̄ + Δm(1+ψδη)/D` (17) and
`e_0 − ē′ = Δm(1−φδ)/D` with `ē′ = m̄′ + q̄`. -/
theorem perm_shock_impact (qbar mbar mbar' : ℝ) (e q : ℕ → ℝ) (hs : P.ψ * P.δ < 2)
    (h : ShockEqm P qbar (fun _ ↦ mbar') mbar e q) :
    q 0 - qbar = (mbar' - mbar) * (1 + P.ψ * P.δ * P.η) / P.D ∧
      e 0 = mbar + qbar + (1 + P.ψ * P.δ * P.η) / (P.φ * P.δ + P.ψ * P.δ * P.η) *
        (mbar' - mbar) ∧
      e 0 - (mbar' + qbar) = (mbar' - mbar) * (1 - P.φ * P.δ) / P.D := by
  have hi := shock_impact P qbar _ mbar e q (summable_const_money P mbar') hs h
  rw [eflex_const] at hi
  have e1 : mbar' + qbar - qbar - mbar = mbar' - mbar := by ring
  rw [e1] at hi
  obtain ⟨-, hp, -⟩ := h
  refine ⟨hi.1, ?_, hi.2⟩
  have : e 0 = q 0 + mbar := by linarith
  rw [this]
  have h2 := hi.1
  unfold D at h2
  rw [div_mul_eq_mul_div, mul_comm (1 + P.ψ * P.δ * P.η) (mbar' - mbar)]
  linarith

/-- O&R p. 614–615, Figs 9.5–9.6, T6: for a money increase `Δm > 0`, the exchange rate
overshoots its new long-run value iff `φδ < 1`, jumps exactly to it iff `φδ = 1`, and
undershoots iff `φδ > 1`. -/
theorem overshooting_iff (qbar mbar mbar' : ℝ) (e q : ℕ → ℝ) (hs : P.ψ * P.δ < 2)
    (h : ShockEqm P qbar (fun _ ↦ mbar') mbar e q) (hΔ : mbar < mbar') :
    (mbar' + qbar < e 0 ↔ P.φ * P.δ < 1) ∧ (e 0 = mbar' + qbar ↔ P.φ * P.δ = 1) ∧
      (e 0 < mbar' + qbar ↔ 1 < P.φ * P.δ) := by
  have hi := (perm_shock_impact P qbar mbar mbar' e q hs h).2.2
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
    · intro h1; exact (sub_pos.1 (this.1 (by linarith)))
    · intro h1; have := this.2 (by linarith); linarith

/-- O&R p. 616: whatever `φδ`, a money increase depreciates the currency on impact,
`e_0 > ē = m̄ + q̄`, and depreciates it in real terms, `q_0 > q̄`. -/
theorem perm_shock_depreciates (qbar mbar mbar' : ℝ) (e q : ℕ → ℝ) (hs : P.ψ * P.δ < 2)
    (h : ShockEqm P qbar (fun _ ↦ mbar') mbar e q) (hΔ : mbar < mbar') :
    mbar + qbar < e 0 ∧ qbar < q 0 := by
  have hi := perm_shock_impact P qbar mbar mbar' e q hs h
  have hpos : 0 < (mbar' - mbar) * (1 + P.ψ * P.δ * P.η) / P.D :=
    div_pos (mul_pos (by linarith) P.slope_denom_pos) P.D_pos
  obtain ⟨-, hp, -⟩ := h
  constructor <;> linarith [hi.1]

/-- O&R p. 617, T6: the transition path after a permanent money shock,
`e_t = m̄′ + q̄ + (1−ψδ)^t (1−φδ)Δm/D` and `q_t − q̄ = (1−ψδ)^t (1+ψδη)Δm/D`. -/
theorem perm_shock_path (qbar mbar mbar' : ℝ) (e q : ℕ → ℝ) (hs : P.ψ * P.δ < 2)
    (h : ShockEqm P qbar (fun _ ↦ mbar') mbar e q) (t : ℕ) :
    e t = mbar' + qbar + P.ρ ^ t * ((1 - P.φ * P.δ) / P.D * (mbar' - mbar)) ∧
      q t - qbar = P.ρ ^ t * ((mbar' - mbar) * (1 + P.ψ * P.δ * P.η) / P.D) := by
  have hi := perm_shock_impact P qbar mbar mbar' e q hs h
  have hp := shock_path P qbar _ mbar e q (summable_const_money P mbar') hs h t
  rw [eflex_const, eflex_const] at hp
  constructor
  · have : e t = mbar' + qbar + P.ρ ^ t * (e 0 - (mbar' + qbar)) := by linarith [hp.2]
    rw [this, hi.2.2]
    ring
  · rw [hp.1, hi.1]

/-- O&R p. 617 (new, exact): after a permanent money shock the price level adjusts
geometrically, `p_t = m̄′ − (1−ψδ)^t (m̄′ − m̄)`, so `p_0 = m̄` and `p` rises monotonically to
`m̄′` when `ψδ ≤ 1` and `Δm > 0`. -/
theorem perm_shock_price_path (qbar mbar mbar' : ℝ) (e q : ℕ → ℝ) (hs : P.ψ * P.δ < 2)
    (h : ShockEqm P qbar (fun _ ↦ mbar') mbar e q) (t : ℕ) :
    e t - q t = mbar' - P.ρ ^ t * (mbar' - mbar) := by
  obtain ⟨he, hq⟩ := perm_shock_path P qbar mbar mbar' e q hs h t
  have hD := P.D_pos.ne'
  have : (1 - P.φ * P.δ) / P.D * (mbar' - mbar) -
      (mbar' - mbar) * (1 + P.ψ * P.δ * P.η) / P.D = -(mbar' - mbar) := by
    field_simp
    unfold D
    ring
  linear_combination he - hq + P.ρ ^ t * this

/-- O&R p. 616, T6: output after a money increase, `y_t − ȳ = δ(q_t − q̄)`, is strictly above its
natural rate at every date when `ψδ < 1` (the book's maintained assumption). -/
theorem perm_shock_output_pos (qbar mbar mbar' : ℝ) (e q : ℕ → ℝ) (hs1 : P.ψ * P.δ < 1)
    (h : ShockEqm P qbar (fun _ ↦ mbar') mbar e q) (hΔ : mbar < mbar') (t : ℕ) :
    0 < P.δ * (q t - qbar) := by
  have hq := (perm_shock_path P qbar mbar mbar' e q (by linarith) h t).2
  rw [hq]
  have hρ : 0 < P.ρ := by unfold ρ; linarith
  exact mul_pos P.δ_pos (mul_pos (pow_pos hρ t)
    (div_pos (mul_pos (by linarith) P.slope_denom_pos) P.D_pos))

/-- O&R p. 612 and p. 616, sharpened: if `1 < ψδ < 2`, output after a money increase is below
its natural rate at date 1 (the adjustment overshoots and oscillates), so "output rises
temporarily" needs the book's assumption `ψδ < 1`. -/
theorem perm_shock_output_oscillates (qbar mbar mbar' : ℝ) (e q : ℕ → ℝ)
    (hs : P.ψ * P.δ < 2) (hs1 : 1 < P.ψ * P.δ)
    (h : ShockEqm P qbar (fun _ ↦ mbar') mbar e q) (hΔ : mbar < mbar') :
    P.δ * (q 1 - qbar) < 0 := by
  have hq := (perm_shock_path P qbar mbar mbar' e q hs h 1).2
  rw [hq, pow_one]
  have hρ : P.ρ < 0 := by unfold ρ; linarith
  exact mul_neg_of_pos_of_neg P.δ_pos (mul_neg_of_neg_of_pos hρ
    (div_pos (mul_pos (by linarith) P.slope_denom_pos) P.D_pos))

/-- O&R p. 615, T6: the impact nominal interest rate `i_1 = e_1 − e_0 = −ψδ(1−φδ)Δm/D`;
for `Δm > 0` it falls below `i* = 0` iff there is overshooting (`φδ < 1`). -/
theorem perm_shock_interest (qbar mbar mbar' : ℝ) (e q : ℕ → ℝ) (hs : P.ψ * P.δ < 2)
    (h : ShockEqm P qbar (fun _ ↦ mbar') mbar e q) :
    e 1 - e 0 = -(P.ψ * P.δ) * (1 - P.φ * P.δ) * (mbar' - mbar) / P.D ∧
      (mbar < mbar' → (e 1 - e 0 < 0 ↔ P.φ * P.δ < 1)) := by
  have h1 := (perm_shock_path P qbar mbar mbar' e q hs h 1).1
  have h0 := (perm_shock_path P qbar mbar mbar' e q hs h 0).1
  have hi : e 1 - e 0 = -(P.ψ * P.δ) * (1 - P.φ * P.δ) * (mbar' - mbar) / P.D := by
    rw [h1, h0]; unfold ρ; ring
  refine ⟨hi, fun hΔ ↦ ?_⟩
  rw [hi, div_neg_iff]
  have hD := P.D_pos
  have hψ := P.ψδ_pos
  have hp : 0 < mbar' - mbar := by linarith
  constructor
  · rintro (⟨-, h2⟩ | ⟨h2, -⟩)
    · linarith
    · by_contra hc
      push Not at hc
      have : 0 ≤ (P.ψ * P.δ) * (P.φ * P.δ - 1) * (mbar' - mbar) :=
        mul_nonneg (mul_nonneg hψ.le (by linarith)) hp.le
      nlinarith
  · intro h2
    right
    refine ⟨?_, hD⟩
    have : 0 < (P.ψ * P.δ) * (1 - P.φ * P.δ) * (mbar' - mbar) :=
      mul_pos (mul_pos hψ (by linarith)) hp
    linarith

/-- O&R p. 614, T6 (the money-market check): at the impact date the new money stock is held,
`m̄′ − p_0 = −η i_1 + φ y_0` with `p_0 = m̄`, `i_1 = e_1 − e_0` and `y_0 = δ(q_0 − q̄)`. -/
theorem perm_shock_money_market (qbar mbar mbar' : ℝ) (e q : ℕ → ℝ) (hs : P.ψ * P.δ < 2)
    (h : ShockEqm P qbar (fun _ ↦ mbar') mbar e q) :
    mbar' - mbar = -P.η * (e 1 - e 0) + P.φ * (P.δ * (q 0 - qbar)) := by
  have hi := (perm_shock_interest P qbar mbar mbar' e q hs h).1
  have hq := (perm_shock_impact P qbar mbar mbar' e q hs h).1
  rw [hi, hq]
  have hD := P.D_pos.ne'
  field_simp
  unfold D
  ring

/-- O&R pp. 614–615: the exchange rate cannot jump straight to its new long-run level unless
`φδ = 1` (or the shock is zero). -/
theorem perm_shock_no_immediate_jump (qbar mbar mbar' : ℝ) (e q : ℕ → ℝ)
    (hs : P.ψ * P.δ < 2) (h : ShockEqm P qbar (fun _ ↦ mbar') mbar e q)
    (hφ : P.φ * P.δ ≠ 1) (hΔ : mbar ≠ mbar') : e 0 ≠ mbar' + qbar := by
  intro h0
  have hi := (perm_shock_impact P qbar mbar mbar' e q hs h).2.2
  rw [h0, sub_self] at hi
  rcases mul_eq_zero.1 ((div_eq_zero_iff.1 hi.symm).resolve_right P.D_pos.ne') with h1 | h1
  · exact hΔ (by linarith)
  · exact hφ (by linarith)

/-- O&R p. 613, T6 (long-run neutrality): after a permanent money shock, `e_t → m̄′ + q̄`,
`q_t → q̄` and `p_t → m̄′`. -/
theorem perm_shock_long_run (qbar mbar mbar' : ℝ) (e q : ℕ → ℝ) (hs : P.ψ * P.δ < 2)
    (h : ShockEqm P qbar (fun _ ↦ mbar') mbar e q) :
    Tendsto e atTop (𝓝 (mbar' + qbar)) ∧ Tendsto q atTop (𝓝 qbar) ∧
      Tendsto (fun t ↦ e t - q t) atTop (𝓝 mbar') := by
  have hρ := tendsto_pow_atTop_nhds_zero_of_abs_lt_one (P.abs_ρ_lt_one hs)
  refine ⟨?_, q_tendsto P qbar _ e q h.1 hs, ?_⟩
  · have := (hρ.mul_const ((1 - P.φ * P.δ) / P.D * (mbar' - mbar))).const_add (mbar' + qbar)
    rw [zero_mul, add_zero] at this
    exact this.congr fun t ↦ (perm_shock_path P qbar mbar mbar' e q hs h t).1.symm
  · have := (hρ.mul_const (mbar' - mbar)).const_sub mbar'
    rw [zero_mul, sub_zero] at this
    exact this.congr fun t ↦ (perm_shock_price_path P qbar mbar mbar' e q hs h t).symm

/-- O&R (17), T6: the permanent-shock equilibrium exists and is unique. -/
theorem perm_shock_exists_unique (qbar mbar mbar' : ℝ) (hs : P.ψ * P.δ < 2) :
    ∃! x : (ℕ → ℝ) × (ℕ → ℝ), ShockEqm P qbar (fun _ ↦ mbar') mbar x.1 x.2 :=
  shock_exists_unique P qbar _ mbar (summable_const_money P mbar') hs

/-! ## T7: a real shock (fn 11) -/

/-- O&R p. 617 and fn 11, T7: after an unanticipated change `q̄ → q̄′` with money constant at
`m̄` (so `p_0 = m̄`), the unique equilibrium jumps at once to the new steady state:
`e_t = m̄ + q̄′` and `q_t = q̄′` for all `t`; the price level stays at `m̄`. -/
theorem real_shock (qbar' mbar : ℝ) (e q : ℕ → ℝ) (hs : P.ψ * P.δ < 2)
    (h : ShockEqm P qbar' (fun _ ↦ mbar) mbar e q) (t : ℕ) :
    e t = mbar + qbar' ∧ q t = qbar' ∧ e t - q t = mbar := by
  have hi := shock_impact P qbar' _ mbar e q (summable_const_money P mbar) hs h
  have hp := shock_path P qbar' _ mbar e q (summable_const_money P mbar) hs h t
  rw [eflex_const] at hi
  rw [eflex_const, eflex_const] at hp
  have e1 : mbar + qbar' - qbar' - mbar = 0 := by ring
  rw [e1, zero_mul, zero_div, zero_mul, zero_div] at hi
  rw [hi.1, hi.2, mul_zero] at hp
  refine ⟨by linarith [hp.2], by linarith [hp.1], by linarith [hp.1, hp.2]⟩

/-- O&R fn 11, T7: the real-shock equilibrium exists and is unique. -/
theorem real_shock_exists_unique (qbar' mbar : ℝ) (hs : P.ψ * P.δ < 2) :
    ∃! x : (ℕ → ℝ) × (ℕ → ℝ), ShockEqm P qbar' (fun _ ↦ mbar) mbar x.1 x.2 :=
  shock_exists_unique P qbar' _ mbar (summable_const_money P mbar) hs

/-! ## T8: general money-supply processes (18)–(21) -/

/-- O&R (19) and p. 618: under flexible prices a money shock moves the exchange rate and the
price level one for one, `(e^flex_0)′ − e^flex_0 = (p^flex_0)′ − p^flex_0`. -/
theorem flex_shock_equal (qbar : ℝ) (m m' : ℕ → ℝ) (t : ℕ) :
    eflex P qbar m' t - eflex P qbar m t = eflex P 0 m' t - eflex P 0 m t := by
  rw [eflex_eq_qbar_add_pflex P qbar m' t, eflex_eq_qbar_add_pflex P qbar m t]
  ring

/-- O&R (20), p. 618: if the economy starts at the flexible-price level of the old money path
(`p_0 = p^flex_0 = e^flex_0 − q̄`) and the money process changes unexpectedly to `m′`, then
`e_0 − e^flex_0 = ((1+ψδη)/(φδ+ψδη)) [(e^flex_0)′ − e^flex_0]`, and `q_0 − q̄` equals the same. -/
theorem twenty (qbar : ℝ) (m m' : ℕ → ℝ) (e q : ℕ → ℝ) (hm' : Summable fun s ↦ P.r ^ s * m' s)
    (hs : P.ψ * P.δ < 2) (h : ShockEqm P qbar m' (eflex P qbar m 0 - qbar) e q) :
    e 0 - eflex P qbar m 0 = (1 + P.ψ * P.δ * P.η) / (P.φ * P.δ + P.ψ * P.δ * P.η) *
        (eflex P qbar m' 0 - eflex P qbar m 0) ∧
      q 0 - qbar = e 0 - eflex P qbar m 0 := by
  have hi := shock_impact P qbar m' _ e q hm' hs h
  have e1 : eflex P qbar m' 0 - qbar - (eflex P qbar m 0 - qbar) =
      eflex P qbar m' 0 - eflex P qbar m 0 := by ring
  rw [e1] at hi
  obtain ⟨-, hp, -⟩ := h
  have hq : q 0 - qbar = e 0 - eflex P qbar m 0 := by linarith
  refine ⟨?_, hq⟩
  rw [← hq, hi.1]
  unfold D
  ring

/-- O&R (21), p. 619: after the shock the exchange rate converges to its (moving) new
flexible-price value at rate `ψδ`: `e_t − (e^flex_t)′ = (1−ψδ)^t [e_0 − (e^flex_0)′]`. -/
theorem twenty_one (qbar : ℝ) (m' : ℕ → ℝ) (p0 : ℝ) (e q : ℕ → ℝ)
    (hm' : Summable fun s ↦ P.r ^ s * m' s) (hs : P.ψ * P.δ < 2)
    (h : ShockEqm P qbar m' p0 e q) (t : ℕ) :
    e t - eflex P qbar m' t = (1 - P.ψ * P.δ) ^ t * (e 0 - eflex P qbar m' 0) :=
  (shock_path P qbar m' p0 e q hm' hs h t).2

/-- O&R p. 619, T8 (impact amplification): the impact multiplier `1/(1−κ) = (1+ψδη)/D`
exceeds one iff `φδ < 1`, so any nonzero disturbance to `e^flex_0` moves `e_0` by MORE than it
moves `e^flex_0` exactly when `φδ < 1`. -/
theorem amplification_iff (qbar : ℝ) (m m' : ℕ → ℝ) (e q : ℕ → ℝ)
    (hm' : Summable fun s ↦ P.r ^ s * m' s) (hs : P.ψ * P.δ < 2)
    (h : ShockEqm P qbar m' (eflex P qbar m 0 - qbar) e q)
    (hΔ : eflex P qbar m' 0 ≠ eflex P qbar m 0) :
    |eflex P qbar m' 0 - eflex P qbar m 0| < |e 0 - eflex P qbar m 0| ↔ P.φ * P.δ < 1 := by
  rw [(twenty P qbar m m' e q hm' hs h).1, abs_mul]
  have hpos : 0 < |eflex P qbar m' 0 - eflex P qbar m 0| := abs_pos.2 (sub_ne_zero.2 hΔ)
  have hD : 0 < P.φ * P.δ + P.ψ * P.δ * P.η := P.D_pos
  rw [abs_of_pos (div_pos P.slope_denom_pos hD)]
  constructor
  · intro h1
    have h2 : 1 < (1 + P.ψ * P.δ * P.η) / (P.φ * P.δ + P.ψ * P.δ * P.η) := by
      by_contra hc
      push Not at hc
      have := mul_le_of_le_one_left hpos.le hc
      linarith
    rw [one_lt_div hD] at h2
    linarith
  · intro h1
    have h2 : 1 < (1 + P.ψ * P.δ * P.η) / (P.φ * P.δ + P.ψ * P.δ * P.η) := by
      rw [one_lt_div hD]; linarith
    exact lt_mul_of_one_lt_left hpos h2

/-- O&R p. 619, T8: the conditional variance reading on a finite state space. If the date-0
disturbance `Δ(s) = (e^flex_0)′(s) − e^flex_0` is random with probabilities `π`, the variance of
the impact exchange-rate change `c·Δ` with `c = (1+ψδη)/D` is `c² Var(Δ)`, which exceeds
`Var(Δ)` iff `φδ < 1` (when `Var(Δ) > 0`). -/
theorem variance_amplification {S : Type} [Fintype S] (π Δ : S → ℝ)
    (hvar : 0 < ∑ s, π s * (Δ s - ∑ s', π s' * Δ s') ^ 2) :
    (∑ s, π s * ((1 + P.ψ * P.δ * P.η) / P.D * Δ s -
        ∑ s', π s' * ((1 + P.ψ * P.δ * P.η) / P.D * Δ s')) ^ 2 =
      ((1 + P.ψ * P.δ * P.η) / P.D) ^ 2 * ∑ s, π s * (Δ s - ∑ s', π s' * Δ s') ^ 2) ∧
    (∑ s, π s * (Δ s - ∑ s', π s' * Δ s') ^ 2 <
        ∑ s, π s * ((1 + P.ψ * P.δ * P.η) / P.D * Δ s -
          ∑ s', π s' * ((1 + P.ψ * P.δ * P.η) / P.D * Δ s')) ^ 2 ↔ P.φ * P.δ < 1) := by
  set c := (1 + P.ψ * P.δ * P.η) / P.D with hc
  set V := ∑ s, π s * (Δ s - ∑ s', π s' * Δ s') ^ 2
  have hmean : ∑ s', π s' * (c * Δ s') = c * ∑ s', π s' * Δ s' := by
    rw [Finset.mul_sum]; congr 1; funext s; ring
  have hV : ∑ s, π s * (c * Δ s - ∑ s', π s' * (c * Δ s')) ^ 2 = c ^ 2 * V := by
    rw [hmean]
    conv_rhs => rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ ↦ by ring
  refine ⟨hV, ?_⟩
  rw [hV]
  have hcpos : 0 < c := div_pos P.slope_denom_pos P.D_pos
  have hD := P.D_pos
  constructor
  · intro h1
    have h2 : 1 < c ^ 2 := by
      by_contra hcon
      push Not at hcon
      have := mul_le_of_le_one_left hvar.le hcon
      linarith
    have h3 : 1 < c := by nlinarith
    rw [hc, one_lt_div hD] at h3
    unfold D at h3
    linarith
  · intro h1
    have h3 : 1 < c := by rw [hc, one_lt_div hD]; unfold D; linarith
    have h2 : 1 < c ^ 2 := by nlinarith
    exact lt_mul_of_one_lt_left hvar h2

/-! ## T9: a money-growth-rate shock (22)–(23) -/

/-- O&R §9.2.5, p. 619: the money path with trend growth, `m_t = m̄ + μ t`. -/
def trend (mbar μ : ℝ) (t : ℕ) : ℝ := mbar + μ * t

/-- O&R (22): the trend money path satisfies the summability hypothesis. -/
theorem summable_trend (mbar μ : ℝ) : Summable fun s ↦ P.r ^ s * trend mbar μ s := by
  have hr : ‖P.r‖ < 1 := by rw [Real.norm_of_nonneg P.r_pos.le]; exact P.r_lt_one
  have h1 := (summable_geometric_of_lt_one P.r_pos.le P.r_lt_one).mul_left mbar
  have h2 := ((hasSum_coe_mul_geometric_of_norm_lt_one hr).summable).mul_left μ
  refine (h1.add h2).congr fun s ↦ ?_
  unfold trend
  ring

/-- O&R (22), p. 620: `Σ_s s r^s = η(1+η)`, hence for `m_t = m̄ + μt` the flexible-price exchange
rate is `e^flex_t = q̄ + m̄ + μ(t + η)`: it runs `ημ` ahead of money. -/
theorem eflex_trend (qbar mbar μ : ℝ) (t : ℕ) :
    eflex P qbar (trend mbar μ) t = qbar + mbar + μ * (t + P.η) := by
  have hr : ‖P.r‖ < 1 := by rw [Real.norm_of_nonneg P.r_pos.le]; exact P.r_lt_one
  have h1 := (summable_geometric_of_lt_one P.r_pos.le P.r_lt_one).mul_left (mbar + μ * t)
  have h2 := ((hasSum_coe_mul_geometric_of_norm_lt_one hr).summable).mul_left μ
  have hs : ∑' s : ℕ, P.r ^ s * trend mbar μ (s + t) =
      ∑' s : ℕ, ((mbar + μ * t) * P.r ^ s + μ * ((s : ℝ) * P.r ^ s)) := by
    congr 1; funext s; unfold trend; push_cast; ring
  have hsum : ∑' s : ℕ, (s : ℝ) * P.r ^ s = P.η * (1 + P.η) := by
    rw [tsum_coe_mul_geometric_of_norm_lt_one hr, P.one_sub_r]
    unfold r
    field_simp [P.one_add_η_pos.ne']
  unfold eflex
  rw [hs, h1.tsum_add h2, tsum_mul_left, tsum_mul_left, P.tsum_r_pow, hsum]
  field_simp [P.one_add_η_pos.ne']
  ring

/-- O&R §9.2.5, p. 619: before the growth shock the economy is in its flexible-price steady
state, `e_t = e^flex_t`, `q_t = q̄`, which solves (7)–(8) with no bubble; the nominal interest
rate is `i* + μ = μ`. -/
theorem trend_steady_state (qbar mbar μ : ℝ) :
    ShockEqm P qbar (trend mbar μ) (mbar + μ * P.η) (eflex P qbar (trend mbar μ)) (fun _ ↦ qbar)
      ∧ ∀ t : ℕ, eflex P qbar (trend mbar μ) (t + 1) - eflex P qbar (trend mbar μ) t = μ := by
  have hm := summable_trend P mbar μ
  have hsol := sol_reduced P qbar _ hm qbar 0
  have e1 : solE P qbar (trend mbar μ) qbar 0 = eflex P qbar (trend mbar μ) := by
    funext t; unfold solE; simp
  have e2 : solQ P qbar qbar = fun _ ↦ qbar := by funext t; unfold solQ; simp
  rw [e1, e2] at hsol
  refine ⟨⟨hsol, ?_, eflex_no_bubble P qbar _⟩, fun t ↦ ?_⟩
  · rw [eflex_trend]; push_cast; ring
  · rw [eflex_trend, eflex_trend]; push_cast; ring

/-- O&R (22), p. 620: a rise in the growth rate from `μ` to `μ′` (with `m_0 = m̄` unchanged)
raises the flexible-price exchange rate at once by `(e^flex_0)′ − e^flex_0 = η(μ′ − μ)`. -/
theorem twenty_two (qbar mbar μ μ' : ℝ) :
    eflex P qbar (trend mbar μ') 0 - eflex P qbar (trend mbar μ) 0 = P.η * (μ' - μ) := by
  rw [eflex_trend, eflex_trend]
  push_cast
  ring

/-- O&R (23), p. 620: after the growth shock the nominal interest rate path is
`i_{t+1} − (i* + μ) = (μ′ − μ) − ψδ(1−ψδ)^t [e_0 − (e^flex_0)′]`. -/
theorem twenty_three (qbar mbar μ μ' : ℝ) (e q : ℕ → ℝ) (hs : P.ψ * P.δ < 2)
    (h : ShockEqm P qbar (trend mbar μ') (mbar + μ * P.η) e q) (t : ℕ) :
    (e (t + 1) - e t) - μ =
      (μ' - μ) - P.ψ * P.δ * (1 - P.ψ * P.δ) ^ t * (e 0 - eflex P qbar (trend mbar μ') 0) := by
  have hm := summable_trend P mbar μ'
  have h1 := (shock_path P qbar _ _ e q hm hs h (t + 1)).2
  have h2 := (shock_path P qbar _ _ e q hm hs h t).2
  have h3 := (trend_steady_state P qbar mbar μ').2 t
  unfold ρ at h1 h2
  rw [pow_succ] at h1
  linear_combination h1 - h2 + h3

/-- O&R p. 620, T9: the impact response of the nominal interest rate to a growth shock is
`i_1 − (i* + μ) = φδ(1+ψδη)(μ′ − μ)/D`, positive when `μ′ > μ`: growth shocks give a POSITIVE
correlation between the nominal rate and the currency's depreciation. -/
theorem growth_shock_impact_interest (qbar mbar μ μ' : ℝ) (e q : ℕ → ℝ)
    (hs : P.ψ * P.δ < 2) (h : ShockEqm P qbar (trend mbar μ') (mbar + μ * P.η) e q) :
    (e 1 - e 0) - μ = P.φ * P.δ * (1 + P.ψ * P.δ * P.η) * (μ' - μ) / P.D ∧
      (μ < μ' → 0 < (e 1 - e 0) - μ) := by
  have hm := summable_trend P mbar μ'
  have h23 := twenty_three P qbar mbar μ μ' e q hs h 0
  have hi := (shock_impact P qbar _ _ e q hm hs h).2
  have e1 : eflex P qbar (trend mbar μ') 0 - qbar - (mbar + μ * P.η) = P.η * (μ' - μ) := by
    rw [eflex_trend]; push_cast; ring
  rw [e1] at hi
  simp only [zero_add, pow_zero, mul_one] at h23
  have key : (e 1 - e 0) - μ = P.φ * P.δ * (1 + P.ψ * P.δ * P.η) * (μ' - μ) / P.D := by
    rw [h23, hi]
    have hD := P.D_pos.ne'
    field_simp
    unfold D
    ring
  refine ⟨key, fun hμ ↦ ?_⟩
  rw [key]
  exact div_pos (mul_pos (mul_pos P.φδ_pos P.slope_denom_pos) (by linarith)) P.D_pos

/-- O&R p. 620, T9: in the long run the trend effect dominates, `i_{t+1} → i* + μ′ = μ′`. -/
theorem growth_shock_long_run_interest (qbar mbar μ μ' : ℝ) (e q : ℕ → ℝ)
    (hs : P.ψ * P.δ < 2) (h : ShockEqm P qbar (trend mbar μ') (mbar + μ * P.η) e q) :
    Tendsto (fun t ↦ e (t + 1) - e t) atTop (𝓝 μ') := by
  have hρ := tendsto_pow_atTop_nhds_zero_of_abs_lt_one (P.abs_ρ_lt_one hs)
  have := ((hρ.const_mul (P.ψ * P.δ)).mul_const
    (e 0 - eflex P qbar (trend mbar μ') 0)).const_sub μ'
  simp only [mul_zero, zero_mul, sub_zero] at this
  refine this.congr fun t ↦ ?_
  have h23 := twenty_three P qbar mbar μ μ' e q hs h t
  unfold ρ
  linarith

/-- O&R p. 620, T9: with overshooting (`φδ < 1`) and `μ′ > μ`, the exchange rate jumps by more
than the flexible-price rate, `e_0 − e^flex_0 > η(μ′ − μ)`. -/
theorem growth_shock_overshoots (qbar mbar μ μ' : ℝ) (e q : ℕ → ℝ) (hs : P.ψ * P.δ < 2)
    (h : ShockEqm P qbar (trend mbar μ') (mbar + μ * P.η) e q) (hφ : P.φ * P.δ < 1)
    (hμ : μ < μ') : P.η * (μ' - μ) < e 0 - eflex P qbar (trend mbar μ) 0 := by
  have hm := summable_trend P mbar μ'
  have hi := (shock_impact P qbar _ _ e q hm hs h).2
  have e1 : eflex P qbar (trend mbar μ') 0 - qbar - (mbar + μ * P.η) = P.η * (μ' - μ) := by
    rw [eflex_trend]; push_cast; ring
  rw [e1] at hi
  have h22 := twenty_two P qbar mbar μ μ'
  have : 0 < P.η * (μ' - μ) * (1 - P.φ * P.δ) / P.D :=
    div_pos (mul_pos (mul_pos P.η_pos (by linarith)) (by linarith)) P.D_pos
  linarith

/-! ## T10: real interest rates (24), (25), fn 17 -/

/-- O&R (24), p. 620: in the structural model with `i* = p* = ȳ = 0`, the real interest rate
`i_{t+1} − (p_{t+1} − p_t)` equals `−ψδ(e_t + p* − p_t − q̄)`: a currency that is appreciated in
real terms has a high real interest rate. -/
theorem twenty_four (qbar : ℝ) (m e p y i : ℕ → ℝ)
    (h : Structural P 0 (fun _ ↦ 0) (fun _ ↦ qbar) 0 m e p y i) (t : ℕ) :
    i (t + 1) - (p (t + 1) - p t) = -(P.ψ * P.δ) * (e t + 0 - p t - qbar) := by
  obtain ⟨h1, -, h3, h5⟩ := h t
  unfold ptilde at h5
  rw [h3] at h5
  linear_combination h1 - h5

/-- O&R (24), p. 621: the sign of the real interest rate is the opposite of the real
depreciation gap: `i_{t+1} − Δp_{t+1} > 0 ⟺ q_t < q̄`. -/
theorem real_interest_pos_iff (qbar : ℝ) (m e p y i : ℕ → ℝ)
    (h : Structural P 0 (fun _ ↦ 0) (fun _ ↦ qbar) 0 m e p y i) (t : ℕ) :
    0 < i (t + 1) - (p (t + 1) - p t) ↔ e t - p t < qbar := by
  rw [twenty_four P qbar m e p y i h t]
  have hψ := P.ψδ_pos
  constructor
  · intro h1
    by_contra hc
    push Not at hc
    have : 0 ≤ P.ψ * P.δ * (e t + 0 - p t - qbar) := mul_nonneg hψ.le (by linarith)
    linarith
  · intro h1
    have : 0 < P.ψ * P.δ * (qbar - (e t + 0 - p t)) := mul_pos hψ (by linarith)
    linarith

/-- O&R fn 17, p. 621: with a variable foreign price level and constant `q̄`, the Phillips curve
(5) reads `p_{t+1} − p_t = ψ(y_t − ȳ) + e_{t+1} + p*_{t+1} − e_t − p*_t`. -/
theorem phillips_variable_pstar (qbar ybar : ℝ) (e p y pstar : ℕ → ℝ) (t : ℕ)
    (h5 : p (t + 1) - p t = P.ψ * (y t - ybar) +
      (ptilde e pstar (fun _ ↦ qbar) (t + 1) - ptilde e pstar (fun _ ↦ qbar) t)) :
    p (t + 1) - p t = P.ψ * (y t - ybar) + e (t + 1) + pstar (t + 1) - e t - pstar t := by
  unfold ptilde at h5
  linarith

/-- O&R (25), p. 621 and fn 17: with variable foreign interest rates and prices, UIP (1),
demand (3) and the Phillips curve (5) give the international real-interest differential
`[i_{t+1} − Δp_{t+1}] − [i*_{t+1} − Δp*_{t+1}] = −ψδ(e_t − p_t + p*_t − q̄)`. -/
theorem twenty_five (qbar ybar : ℝ) (e p y i istar pstar : ℕ → ℝ) (t : ℕ)
    (h1 : i (t + 1) = istar (t + 1) + e (t + 1) - e t)
    (h3 : y t = ybar + P.δ * (e t + pstar t - p t - qbar))
    (h5 : p (t + 1) - p t = P.ψ * (y t - ybar) +
      (ptilde e pstar (fun _ ↦ qbar) (t + 1) - ptilde e pstar (fun _ ↦ qbar) t)) :
    (i (t + 1) - (p (t + 1) - p t)) - (istar (t + 1) - (pstar (t + 1) - pstar t)) =
      -(P.ψ * P.δ) * (e t - p t + pstar t - qbar) := by
  have h5' := phillips_variable_pstar P qbar ybar e p y pstar t h5
  rw [h3] at h5'
  linear_combination h1 - h5'

/-! ## Exercise 1: disinflation with sticky prices (p. 657) -/

/-- O&R Ex. 1, p. 657: switching unexpectedly at date 0 from the trend path `m_t = m̄ + μt`
(with the economy in its steady state, so `p_0 = m̄ + ημ`) to a constant money supply `L`:
`q_0 − q̄ = (L − m̄ − ημ)(1+ψδη)/D` and `e_0 − (L + q̄) = (L − m̄ − ημ)(1−φδ)/D`. -/
theorem disinflation_impact (qbar mbar μ L : ℝ) (e q : ℕ → ℝ) (hs : P.ψ * P.δ < 2)
    (h : ShockEqm P qbar (fun _ ↦ L) (mbar + μ * P.η) e q) :
    q 0 - qbar = (L - mbar - μ * P.η) * (1 + P.ψ * P.δ * P.η) / P.D ∧
      e 0 - (L + qbar) = (L - mbar - μ * P.η) * (1 - P.φ * P.δ) / P.D := by
  have hi := shock_impact P qbar _ _ e q (summable_const_money P L) hs h
  rw [eflex_const] at hi
  have e1 : L + qbar - qbar - (mbar + μ * P.η) = L - mbar - μ * P.η := by ring
  rw [e1] at hi
  exact hi

/-- O&R Ex. 1(a), literal reading `m_t − m_{t−1} = 0` for `t ≥ 0` (so `L = m_{−1} = m̄ − μ`):
with `μ > 0` the real exchange rate appreciates on impact, `q_0 − q̄ = −(1+η)μ(1+ψδη)/D < 0`. -/
theorem disinflation_literal_impact (qbar mbar μ : ℝ) (e q : ℕ → ℝ) (hs : P.ψ * P.δ < 2)
    (h : ShockEqm P qbar (fun _ ↦ mbar - μ) (mbar + μ * P.η) e q) (hμ : 0 < μ) :
    q 0 - qbar = -((1 + P.η) * μ) * (1 + P.ψ * P.δ * P.η) / P.D ∧ q 0 - qbar < 0 := by
  have hi := (disinflation_impact P qbar mbar μ (mbar - μ) e q hs h).1
  have e1 : mbar - μ - mbar - μ * P.η = -((1 + P.η) * μ) := by ring
  rw [e1] at hi
  refine ⟨hi, ?_⟩
  have hpos : 0 < (1 + P.η) * μ * (1 + P.ψ * P.δ * P.η) / P.D :=
    div_pos (mul_pos (mul_pos P.one_add_η_pos hμ) P.slope_denom_pos) P.D_pos
  have e2 : -((1 + P.η) * μ) * (1 + P.ψ * P.δ * P.η) / P.D =
      -((1 + P.η) * μ * (1 + P.ψ * P.δ * P.η) / P.D) := by ring
  rw [hi, e2]
  linarith

/-- O&R Ex. 1(a): under the literal reading, with `μ > 0` and `ψδ < 1`, output is below its
natural rate at EVERY date (a prolonged slump), `y_t = δ(q_t − q̄) < 0`, and the real interest
rate `−ψδ(q_t − q̄)` (eq. (24)) is positive at every date. -/
theorem disinflation_slump (qbar mbar μ : ℝ) (e q : ℕ → ℝ) (hs1 : P.ψ * P.δ < 1)
    (h : ShockEqm P qbar (fun _ ↦ mbar - μ) (mbar + μ * P.η) e q) (hμ : 0 < μ) (t : ℕ) :
    P.δ * (q t - qbar) < 0 ∧ 0 < -(P.ψ * P.δ) * (q t - qbar) := by
  have hs : P.ψ * P.δ < 2 := by linarith
  have hq0 := (disinflation_literal_impact P qbar mbar μ e q hs h hμ).2
  have hp := (shock_path P qbar _ _ e q (summable_const_money P (mbar - μ)) hs h t).1
  have hρ : 0 < P.ρ := by unfold ρ; linarith
  have hqt : q t - qbar < 0 := by rw [hp]; exact mul_neg_of_pos_of_neg (pow_pos hρ t) hq0
  constructor
  · exact mul_neg_of_pos_of_neg P.δ_pos hqt
  · have := mul_neg_of_pos_of_neg P.ψδ_pos hqt
    linarith

/-- O&R Ex. 1(a): under the literal reading, with `φδ < 1` and `μ > 0`, the exchange rate
overshoots its new (constant) flexible-price level `m̄ − μ + q̄` DOWNWARD on impact. -/
theorem disinflation_overshoots_down (qbar mbar μ : ℝ) (e q : ℕ → ℝ) (hs : P.ψ * P.δ < 2)
    (h : ShockEqm P qbar (fun _ ↦ mbar - μ) (mbar + μ * P.η) e q) (hμ : 0 < μ)
    (hφ : P.φ * P.δ < 1) : e 0 < mbar - μ + qbar := by
  have hi := (disinflation_impact P qbar mbar μ (mbar - μ) e q hs h).2
  have e1 : mbar - μ - mbar - μ * P.η = -((1 + P.η) * μ) := by ring
  rw [e1] at hi
  have : 0 < (1 + P.η) * μ * (1 - P.φ * P.δ) / P.D :=
    div_pos (mul_pos (mul_pos P.one_add_η_pos hμ) (by linarith)) P.D_pos
  have e2 : -((1 + P.η) * μ) * (1 - P.φ * P.δ) / P.D = -((1 + P.η) * μ * (1 - P.φ * P.δ) / P.D)
    := by ring
  rw [e2] at hi
  linarith

/-- O&R Ex. 1(a): the impact response of the nominal interest rate under the literal reading,
`i_1 − μ = −μ + ψδ(1−φδ)(1+η)μ/D` (its sign is ambiguous). -/
theorem disinflation_interest (qbar mbar μ : ℝ) (e q : ℕ → ℝ) (hs : P.ψ * P.δ < 2)
    (h : ShockEqm P qbar (fun _ ↦ mbar - μ) (mbar + μ * P.η) e q) :
    (e 1 - e 0) - μ = -μ + P.ψ * P.δ * (1 - P.φ * P.δ) * (1 + P.η) * μ / P.D := by
  have hi := (disinflation_impact P qbar mbar μ (mbar - μ) e q hs h).2
  have hp := (shock_path P qbar _ _ e q (summable_const_money P (mbar - μ)) hs h 1).2
  rw [eflex_const, eflex_const, pow_one] at hp
  have e1 : mbar - μ - mbar - μ * P.η = -((1 + P.η) * μ) := by ring
  rw [e1] at hi
  have : e 1 - e 0 = (P.ρ - 1) * (e 0 - (mbar - μ + qbar)) := by linarith
  rw [this, hi]
  unfold ρ
  ring

/-- O&R Ex. 1, the 9.2.5 reading (`m_0 = m̄` unchanged, zero growth after): the same results with
`(1+η)μ` replaced by `ημ`, e.g. `q_0 − q̄ = −ημ(1+ψδη)/D`. -/
theorem disinflation_alt_impact (qbar mbar μ : ℝ) (e q : ℕ → ℝ) (hs : P.ψ * P.δ < 2)
    (h : ShockEqm P qbar (fun _ ↦ mbar) (mbar + μ * P.η) e q) :
    q 0 - qbar = -(P.η * μ) * (1 + P.ψ * P.δ * P.η) / P.D := by
  have hi := (disinflation_impact P qbar mbar μ mbar e q hs h).1
  rw [hi]
  ring

/-- O&R Ex. 1(b): a one-time LEVEL jump `J` in money at date 0 followed by zero growth
(`m_t = m̄ − μ + J` for `t ≥ 0`) leaves output at its natural rate at every date iff
`J = (1+η)μ`, i.e. iff the jump exactly offsets the fall in the flexible-price price level. -/
theorem disinflation_no_slump_iff (qbar mbar μ J : ℝ) (e q : ℕ → ℝ) (hs : P.ψ * P.δ < 2)
    (h : ShockEqm P qbar (fun _ ↦ mbar - μ + J) (mbar + μ * P.η) e q) :
    (∀ t, P.δ * (q t - qbar) = 0) ↔ J = (1 + P.η) * μ := by
  have hi := (disinflation_impact P qbar mbar μ (mbar - μ + J) e q hs h).1
  have hp := fun t ↦ (shock_path P qbar _ _ e q (summable_const_money P (mbar - μ + J))
    hs h t).1
  have hA := P.slope_denom_pos
  have hD := P.D_pos
  constructor
  · intro h0
    have h00 := h0 0
    rcases mul_eq_zero.1 h00 with h1 | h1
    · exact absurd h1 P.δ_pos.ne'
    · rw [hi] at h1
      rcases mul_eq_zero.1 ((div_eq_zero_iff.1 h1).resolve_right hD.ne') with h2 | h2
      · linarith
      · linarith
  · intro hJ t
    rw [hp t, hi, hJ]
    ring

/-- O&R Ex. 1(b): with the level jump `J = (1+η)μ`, the price level is constant from date 0
on (`p_{t+1} = p_t`: inflation is zero at once), the real exchange rate stays at `q̄`, and the
exchange rate stays at its new flexible-price level. A credible disinflation needs a monetary
EXPANSION at the switch date. -/
theorem disinflation_level_jump (qbar mbar μ : ℝ) (e q : ℕ → ℝ) (hs : P.ψ * P.δ < 2)
    (h : ShockEqm P qbar (fun _ ↦ mbar - μ + (1 + P.η) * μ) (mbar + μ * P.η) e q) (t : ℕ) :
    q t = qbar ∧ e t = mbar + μ * P.η + qbar ∧ (e (t + 1) - q (t + 1)) - (e t - q t) = 0 := by
  have hi := disinflation_impact P qbar mbar μ _ e q hs h
  have hm := summable_const_money P (mbar - μ + (1 + P.η) * μ)
  have e1 : mbar - μ + (1 + P.η) * μ - mbar - μ * P.η = 0 := by ring
  rw [e1, zero_mul, zero_div, zero_mul, zero_div] at hi
  have hpath : ∀ s, q s = qbar ∧ e s = mbar + μ * P.η + qbar := by
    intro s
    have hp := shock_path P qbar _ _ e q hm hs h s
    rw [eflex_const, eflex_const, hi.1, mul_zero] at hp
    have h2 := hi.2
    constructor
    · linarith [hp.1]
    · have : e s - (mbar - μ + (1 + P.η) * μ + qbar) = 0 := by rw [hp.2, h2, mul_zero]
      linarith
  obtain ⟨h1, h2⟩ := hpath t
  obtain ⟨h3, h4⟩ := hpath (t + 1)
  refine ⟨h1, h2, ?_⟩
  rw [h1, h2, h3, h4]
  ring

end ObstfeldRogoff.NominalRigidities.DornbuschShocks
