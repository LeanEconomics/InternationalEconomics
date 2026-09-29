/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NominalRigidities.DornbuschShocks
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Extensions of the Dornbusch model: anticipated shocks, pegs, and uncertainty

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §9.2.4 (p. 619),
§9.4.1 (pp. 631–632) and Exercise 2 (p. 657).

* **Exercise 2 (anticipated real depreciation).** With a time-varying equilibrium real exchange
  rate `q̄_t`, the Phillips curve must be taken in its original form (5) (with `p̃_t = e_t − q̄_t`);
  the derived form (7) would put a spurious jump into `q_t − q̄_t` at the date of the change.
  The model with a `q̄` path is EXACTLY the constant-`q̄` model of `DornbuschModel` in the
  variables `x_t = q_t − q̄_t` and fundamentals `q̄_t + m_t`, so the whole saddle-path machinery
  applies. For news at date 0 of a rise `Δ` at date `T ≥ 1`: `x_0 = r^T Δ (1+ψδη)/D`, the
  currency depreciates at once in nominal and real terms, output booms from the news date with
  no break at `T`, and the price level is above `m̄` strictly between `0` and `T` and below
  `m̄` from `T` on. `T = 0` recovers fn 11.
* **Money-demand shocks (T11, p. 631).** Replacing `m` by `m − ε`, the accommodating policy
  `m = m̄ + ε` (a peg) makes the economy coincide exactly with the shock-free one, whatever the
  shock path; conversely a peg forces `m − ε` to be constant. Under a fixed money supply a
  money-demand shock has real effects.
* **Peg plus a real shock (T12, p. 632), SIGN CORRECTED.** Under a peg, a FALL in `q̄` (real
  appreciation) produces a temporary BOOM with rising prices, not the "downward adjustment after
  a period of unemployment" of the text; the unemployment story holds for a RISE in `q̄`.
* **The stochastic Dornbusch model (T13, p. 619, "left as an exercise").** On a finite-state
  event tree (histories `List S`, arbitrary history-dependent transition probabilities, bounded
  adapted money process), with UIP `i_t = E_t e_{t+1} − e_t` and the Phillips curve
  `p_{t+1} − p_t = ψ(y_t − ȳ) + E_t p̃_{t+1} − p̃_t`: the saddle deviation
  `d = e − e^flex − κ(q − q̄)` satisfies `E_t d_{t+1} = d_t / r` EXACTLY, where
  `e^flex_t = q̄ + (1/(1+η)) Σ_j r^j E_t m_{t+j}`. Hence (i) the no-bubble solution EXISTS, is
  bounded, and is UNIQUE (uniqueness holds among no-bubble solutions and among bounded
  solutions, because `|d_t| = r^T |E_t d_{t+T}| → 0`); it is `e = e^flex + κ(q − q̄)` with the
  SAME `κ` as under perfect foresight; (ii) bubble solutions exist, so the selection criterion
  is essential; (iii) price stickiness scales the conditional variance of the exchange rate by
  `((1+ψδη)/D)²`, which exceeds one iff `φδ < 1`.
-/

namespace ObstfeldRogoff.NominalRigidities.DornbuschExtensions

open Filter Topology DornbuschModel DornbuschModel.DornbuschParams DornbuschShocks

variable (P : DornbuschParams)

/-! ## Exercise 2: a time-varying equilibrium real exchange rate -/

/-- O&R (5), (7)–(8) with a time-varying `q̄_t` (Ex. 2): the reduced system implied by the
structural model, `q_{t+1} − q̄_{t+1} = ρ(q_t − q̄_t)` and
`m_t − e_t + q_t = −η(e_{t+1} − e_t) + φδ(q_t − q̄_t)`. -/
def ReducedTV (qbar m e q : ℕ → ℝ) : Prop :=
  ∀ t, q (t + 1) - qbar (t + 1) = P.ρ * (q t - qbar t) ∧
    m t - e t + q t = -P.η * (e (t + 1) - e t) + P.φ * P.δ * (q t - qbar t)

/-- O&R (1)–(5), Ex. 2: with `p* = ȳ = i* = 0` and a `q̄` path, the structural model with the
Phillips curve (5) (`p̃_t = e_t − q̄_t`) implies the reduced system for `q = e − p`. -/
theorem structural_to_reducedTV (qbar m e p y i : ℕ → ℝ)
    (h : Structural P 0 (fun _ ↦ 0) qbar 0 m e p y i) :
    ReducedTV P qbar m e (fun t ↦ e t - p t) := by
  intro t
  obtain ⟨h1, h2, h3, h5⟩ := h t
  unfold ptilde at h5
  rw [h3] at h5 h2
  rw [h1] at h2
  unfold ρ
  constructor
  · linear_combination -h5
  · linear_combination h2

/-- O&R Ex. 2 (flag): using the derived Phillips curve (7) with a moving `q̄_t` instead of (5) is
not innocuous. If both `q_{t+1} − q_t = −ψδ(q_t − q̄_t)` (naive (7)) and the correct law
`q_{t+1} − q̄_{t+1} = ρ(q_t − q̄_t)` hold at `t`, then `q̄_{t+1} = q̄_t`: the two differ exactly
at a date where `q̄` moves. -/
theorem naive_seven_wrong (qbar q : ℕ → ℝ) (t : ℕ)
    (h7 : q (t + 1) - q t = -(P.ψ * P.δ) * (q t - qbar t))
    (h5 : q (t + 1) - qbar (t + 1) = P.ρ * (q t - qbar t)) : qbar (t + 1) = qbar t := by
  unfold ρ at h5
  linarith

/-- O&R Ex. 2 (new, exact): the model with a `q̄` path is the constant-`q̄` model of
`DornbuschModel` (with `q̄ = 0`) in the variables `x_t = q_t − q̄_t` and money `q̄_t + m_t`. -/
theorem reducedTV_iff (qbar m e q : ℕ → ℝ) :
    ReducedTV P qbar m e q ↔ Reduced P 0 (fun t ↦ qbar t + m t) e (fun t ↦ q t - qbar t) := by
  constructor
  · intro h t
    obtain ⟨h1, h2⟩ := h t
    unfold ρ at h1
    constructor
    · linear_combination h1
    · linear_combination h2
  · intro h t
    obtain ⟨h1, h2⟩ := h t
    unfold ρ
    constructor
    · linear_combination h1
    · linear_combination h2

/-- O&R Ex. 2: the anticipated path of `q̄`: `q̄_t = q̄` before `T`, `q̄ + Δ` from `T` on. -/
noncomputable def qstep (qbar Δ : ℝ) (T t : ℕ) : ℝ := if T ≤ t then qbar + Δ else qbar

/-- O&R Ex. 2: `|q̄_t| ≤ |q̄| + |Δ|`. -/
theorem qstep_abs_le (qbar Δ : ℝ) (T t : ℕ) : |qstep qbar Δ T t| ≤ |qbar| + |Δ| := by
  unfold qstep
  split_ifs
  · exact abs_add_le _ _
  · linarith [abs_nonneg Δ]

/-- O&R Ex. 2: the fundamentals `q̄_t + m̄` satisfy the summability hypothesis. -/
theorem summable_step (qbar Δ mbar : ℝ) (T : ℕ) :
    Summable fun s ↦ P.r ^ s * (fun t ↦ qstep qbar Δ T t + mbar) s := by
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one P.r_pos.le P.r_lt_one).mul_left (|qbar| + |Δ| + |mbar|))
    fun s ↦ ?_
  have hb : |qstep qbar Δ T s + mbar| ≤ |qbar| + |Δ| + |mbar| :=
    calc |qstep qbar Δ T s + mbar| ≤ |qstep qbar Δ T s| + |mbar| := abs_add_le _ _
      _ ≤ |qbar| + |Δ| + |mbar| := by linarith [qstep_abs_le qbar Δ T s]
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos P.r_pos, mul_comm (|qbar| + |Δ| + |mbar|)]
  exact mul_le_mul_of_nonneg_left hb (pow_pos P.r_pos s).le

/-- O&R (14): `r (1 + η) = η`. -/
theorem r_mul_one_add : P.r * (1 + P.η) = P.η := by
  unfold r
  field_simp [P.one_add_η_pos.ne']

/-- O&R Ex. 2: from `T` on, the flexible-price exchange rate is `m̄ + q̄ + Δ`. -/
theorem eflex_step_after (qbar Δ mbar : ℝ) (T t : ℕ) (ht : T ≤ t) :
    eflex P 0 (fun t ↦ qstep qbar Δ T t + mbar) t = mbar + qbar + Δ := by
  unfold eflex
  have e1 : (fun s ↦ P.r ^ s * (fun t ↦ qstep qbar Δ T t + mbar) (s + t)) =
      fun s ↦ P.r ^ s * (mbar + qbar + Δ) := by
    funext s
    simp only
    unfold qstep
    split_ifs with hh
    · ring
    · omega
  rw [e1, tsum_mul_right, P.tsum_r_pow]
  field_simp [P.one_add_η_pos.ne']
  ring

/-- O&R Ex. 2: `j` periods before `T`, the flexible-price exchange rate is
`m̄ + q̄ + r^j Δ`: the anticipated change is discounted at `r = η/(1+η)`. -/
theorem eflex_step_before (qbar Δ mbar : ℝ) (T : ℕ) :
    ∀ j t : ℕ, t + j = T →
      eflex P 0 (fun t ↦ qstep qbar Δ T t + mbar) t = mbar + qbar + P.r ^ j * Δ := by
  intro j
  induction j with
  | zero =>
    intro t ht
    rw [eflex_step_after P qbar Δ mbar T t (by omega)]
    ring
  | succ j ih =>
    intro t ht
    have h1 := ih (t + 1) (by omega)
    have h2 := eflex_succ P 0 _ (summable_step P qbar Δ mbar T) t
    have h3 : qstep qbar Δ T t = qbar := by unfold qstep; split_ifs <;> first | rfl | omega
    have h4 := r_mul_one_add P
    rw [h1, h3] at h2
    have h5 : (1 + P.η) * (eflex P 0 (fun t ↦ qstep qbar Δ T t + mbar) t -
        (mbar + qbar + P.r ^ (j + 1) * Δ)) = 0 := by
      rw [pow_succ]
      linear_combination -h2 - P.r ^ j * Δ * h4
    rcases mul_eq_zero.1 h5 with h6 | h6
    · exact absurd h6 P.one_add_η_pos.ne'
    · linarith

/-- O&R Ex. 2: the equilibrium after news at date 0 of a change `Δ` in `q̄` at date `T`. The
economy was in its steady state, so `p_0 = m̄`; afterwards it solves the reduced system with the
`q̄` path and satisfies the no-bubble condition. -/
def AnticipatedEqm (qbar Δ mbar : ℝ) (T : ℕ) (e q : ℕ → ℝ) : Prop :=
  ReducedTV P (qstep qbar Δ T) (fun _ ↦ mbar) e q ∧ e 0 - q 0 = mbar ∧ NoBubble P e

/-- O&R Ex. 2 (new, exact): an anticipated-depreciation equilibrium is a post-shock
equilibrium of the transformed constant-`q̄` model. -/
theorem anticipated_iff_shockEqm (qbar Δ mbar : ℝ) (T : ℕ) (e q : ℕ → ℝ) :
    AnticipatedEqm P qbar Δ mbar T e q ↔
      ShockEqm P 0 (fun t ↦ qstep qbar Δ T t + mbar) (mbar + qstep qbar Δ T 0) e
        (fun t ↦ q t - qstep qbar Δ T t) := by
  unfold AnticipatedEqm ShockEqm
  rw [reducedTV_iff]
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, by simp only; linarith, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, by simp only at h2; linarith, h3⟩

/-- O&R Ex. 2: `x_t = q_t − q̄_t` follows `x_t = ρ^t x_0` at EVERY date, including across `T`:
there is no break when the anticipated change takes effect. -/
theorem anticipated_x_path (qbar Δ mbar : ℝ) (T : ℕ) (e q : ℕ → ℝ)
    (h : AnticipatedEqm P qbar Δ mbar T e q) (t : ℕ) :
    q t - qstep qbar Δ T t = P.ρ ^ t * (q 0 - qstep qbar Δ T 0) :=
  by
    have h1 := q_closed_form P 0 _ e _ ((reducedTV_iff P _ _ e q).1 h.1) t
    simp only [sub_zero] at h1
    exact h1

/-- O&R Ex. 2: for `T ≥ 1`, on the news date the real exchange rate jumps to
`q_0 − q̄ = r^T Δ(1+ψδη)/D`, and the nominal rate depreciates by the same amount,
`e_0 − (m̄ + q̄) = r^T Δ(1+ψδη)/D`. -/
theorem anticipated_impact (qbar Δ mbar : ℝ) (T : ℕ) (hT : 1 ≤ T) (e q : ℕ → ℝ)
    (hs : P.ψ * P.δ < 2) (h : AnticipatedEqm P qbar Δ mbar T e q) :
    q 0 - qbar = P.r ^ T * Δ * (1 + P.ψ * P.δ * P.η) / P.D ∧
      e 0 - (mbar + qbar) = P.r ^ T * Δ * (1 + P.ψ * P.δ * P.η) / P.D := by
  have h0 : qstep qbar Δ T 0 = qbar := by unfold qstep; split_ifs <;> first | rfl | omega
  have hi := (shock_impact P 0 _ _ e _ (summable_step P qbar Δ mbar T) hs
    ((anticipated_iff_shockEqm P qbar Δ mbar T e q).1 h)).1
  rw [eflex_step_before P qbar Δ mbar T T 0 (by omega), h0] at hi
  have e1 : mbar + qbar + P.r ^ T * Δ - 0 - (mbar + qbar) = P.r ^ T * Δ := by ring
  rw [e1, sub_zero] at hi
  obtain ⟨-, hp, -⟩ := h
  exact ⟨hi, by linarith⟩

/-- O&R Ex. 2 and fn 11: if the change is immediate (`T = 0`), the economy jumps at once to the
new steady state, `q_t = q̄ + Δ` and `e_t = m̄ + q̄ + Δ` for all `t`. -/
theorem anticipated_immediate (qbar Δ mbar : ℝ) (e q : ℕ → ℝ) (hs : P.ψ * P.δ < 2)
    (h : AnticipatedEqm P qbar Δ mbar 0 e q) (t : ℕ) :
    q t = qbar + Δ ∧ e t = mbar + qbar + Δ := by
  have hq : ∀ t, qstep qbar Δ 0 t = qbar + Δ := fun t ↦ by
    unfold qstep; split_ifs <;> first | rfl | omega
  have hS := (anticipated_iff_shockEqm P qbar Δ mbar 0 e q).1 h
  have hi := shock_impact P 0 _ _ e _ (summable_step P qbar Δ mbar 0) hs hS
  have hp := shock_path P 0 _ _ e _ (summable_step P qbar Δ mbar 0) hs hS t
  rw [eflex_step_after P qbar Δ mbar 0 0 le_rfl] at hi hp
  rw [eflex_step_after P qbar Δ mbar 0 t (Nat.zero_le t)] at hp
  simp only [hq] at hi hp
  have e1 : mbar + qbar + Δ - 0 - (mbar + (qbar + Δ)) = 0 := by ring
  rw [e1, zero_mul, zero_div, zero_mul, zero_div] at hi
  rw [hi.1, hi.2, mul_zero] at hp
  exact ⟨by linarith [hp.1], by linarith [hp.2]⟩

/-- O&R Ex. 2: with `Δ > 0`, `T ≥ 1` and `ψδ < 1`, output booms from the news date on,
`y_t − ȳ = δ(q_t − q̄_t) > 0` at every date (no break at `T`). -/
theorem anticipated_boom (qbar Δ mbar : ℝ) (T : ℕ) (hT : 1 ≤ T) (e q : ℕ → ℝ)
    (hs1 : P.ψ * P.δ < 1) (h : AnticipatedEqm P qbar Δ mbar T e q) (hΔ : 0 < Δ) (t : ℕ) :
    0 < P.δ * (q t - qstep qbar Δ T t) := by
  have h0 : qstep qbar Δ T 0 = qbar := by unfold qstep; split_ifs <;> first | rfl | omega
  have hi := (anticipated_impact P qbar Δ mbar T hT e q (by linarith) h).1
  rw [anticipated_x_path P qbar Δ mbar T e q h t, h0, hi]
  have hρ : 0 < P.ρ := by unfold ρ; linarith
  exact mul_pos P.δ_pos (mul_pos (pow_pos hρ t) (div_pos (mul_pos (mul_pos
    (pow_pos P.r_pos T) hΔ) P.slope_denom_pos) P.D_pos))

/-- O&R Ex. 2: the price level before the change: if `t + j = T` with `j ≥ 1` then
`p_t − m̄ = Δ(r^j − r^T ρ^t)`. -/
theorem anticipated_price_before (qbar Δ mbar : ℝ) (T : ℕ) (hT : 1 ≤ T) (e q : ℕ → ℝ)
    (hs : P.ψ * P.δ < 2) (h : AnticipatedEqm P qbar Δ mbar T e q) (t j : ℕ) (hj : 1 ≤ j)
    (htj : t + j = T) : (e t - q t) - mbar = Δ * (P.r ^ j - P.r ^ T * P.ρ ^ t) := by
  have hS := (anticipated_iff_shockEqm P qbar Δ mbar T e q).1 h
  have h18 := eighteen P 0 _ e _ (summable_step P qbar Δ mbar T) hS.1 hs hS.2.2 t
  rw [eflex_step_before P qbar Δ mbar T j t htj] at h18
  have hqt : qstep qbar Δ T t = qbar := by unfold qstep; split_ifs <;> first | rfl | omega
  have hx := anticipated_x_path P qbar Δ mbar T e q h t
  have h0 : qstep qbar Δ T 0 = qbar := by unfold qstep; split_ifs <;> first | rfl | omega
  have hi := (anticipated_impact P qbar Δ mbar T hT e q hs h).1
  have hk := one_sub_κ_mul_impact P (P.r ^ T * Δ)
  rw [hqt, h0, hi] at hx
  simp only [hqt, sub_zero] at h18
  linear_combination h18 - (1 - P.κ) * hx - P.ρ ^ t * hk

/-- O&R Ex. 2: the price level from the change on: for `t ≥ T ≥ 1`,
`p_t − m̄ = −r^T ρ^t Δ`. -/
theorem anticipated_price_after (qbar Δ mbar : ℝ) (T : ℕ) (hT : 1 ≤ T) (e q : ℕ → ℝ)
    (hs : P.ψ * P.δ < 2) (h : AnticipatedEqm P qbar Δ mbar T e q) (t : ℕ) (ht : T ≤ t) :
    (e t - q t) - mbar = -(P.r ^ T * P.ρ ^ t * Δ) := by
  have hS := (anticipated_iff_shockEqm P qbar Δ mbar T e q).1 h
  have h18 := eighteen P 0 _ e _ (summable_step P qbar Δ mbar T) hS.1 hs hS.2.2 t
  rw [eflex_step_after P qbar Δ mbar T t ht] at h18
  have hqt : qstep qbar Δ T t = qbar + Δ := by unfold qstep; split_ifs; rfl
  have hx := anticipated_x_path P qbar Δ mbar T e q h t
  have h0 : qstep qbar Δ T 0 = qbar := by unfold qstep; split_ifs <;> first | rfl | omega
  have hi := (anticipated_impact P qbar Δ mbar T hT e q hs h).1
  have hk := one_sub_κ_mul_impact P (P.r ^ T * Δ)
  rw [hqt, h0, hi] at hx
  simp only [hqt, sub_zero] at h18
  linear_combination h18 - (1 - P.κ) * hx - P.ρ ^ t * hk

/-- O&R Ex. 2: with `Δ > 0`, `T ≥ 1` and `ψδ < 1`, the price level starts at `m̄`, is strictly
above `m̄` for `0 < t < T` (inflation during the boom) and strictly below `m̄` from `T` on. -/
theorem anticipated_price_signs (qbar Δ mbar : ℝ) (T : ℕ) (hT : 1 ≤ T) (e q : ℕ → ℝ)
    (hs1 : P.ψ * P.δ < 1) (h : AnticipatedEqm P qbar Δ mbar T e q) (hΔ : 0 < Δ) :
    e 0 - q 0 = mbar ∧ (∀ t, 0 < t → t < T → mbar < e t - q t) ∧
      (∀ t, T ≤ t → e t - q t < mbar) := by
  have hs : P.ψ * P.δ < 2 := by linarith
  have hρ0 : 0 < P.ρ := by unfold ρ; linarith
  have hρ1 : P.ρ ≤ 1 := by unfold ρ; linarith [P.ψδ_pos]
  refine ⟨h.2.1, fun t ht0 htT ↦ ?_, fun t ht ↦ ?_⟩
  · have hp := anticipated_price_before P qbar Δ mbar T hT e q hs h t (T - t) (by omega)
      (by omega)
    have h1 : P.r ^ T < P.r ^ (T - t) :=
      pow_lt_pow_right_of_lt_one₀ P.r_pos P.r_lt_one (by omega)
    have h2 : P.ρ ^ t ≤ 1 := pow_le_one₀ hρ0.le hρ1
    have h3 : P.r ^ T * P.ρ ^ t ≤ P.r ^ T := mul_le_of_le_one_right (pow_pos P.r_pos T).le h2
    have : 0 < Δ * (P.r ^ (T - t) - P.r ^ T * P.ρ ^ t) := mul_pos hΔ (by linarith)
    linarith
  · have hp := anticipated_price_after P qbar Δ mbar T hT e q hs h t ht
    have : 0 < P.r ^ T * P.ρ ^ t * Δ := mul_pos (mul_pos (pow_pos P.r_pos T) (pow_pos hρ0 t)) hΔ
    linarith

/-- O&R Ex. 2: the anticipated-depreciation equilibrium exists and is unique. -/
theorem anticipated_exists_unique (qbar Δ mbar : ℝ) (T : ℕ) (hs : P.ψ * P.δ < 2) :
    ∃! x : (ℕ → ℝ) × (ℕ → ℝ), AnticipatedEqm P qbar Δ mbar T x.1 x.2 := by
  obtain ⟨⟨e, x⟩, hx, huniq⟩ := shock_exists_unique P 0 (fun t ↦ qstep qbar Δ T t + mbar)
    (mbar + qstep qbar Δ T 0) (summable_step P qbar Δ mbar T) hs
  refine ⟨(e, fun t ↦ x t + qstep qbar Δ T t), ?_, ?_⟩
  · change AnticipatedEqm P qbar Δ mbar T e (fun t ↦ x t + qstep qbar Δ T t)
    rw [anticipated_iff_shockEqm]
    have hfun : (fun t ↦ (fun t ↦ x t + qstep qbar Δ T t) t - qstep qbar Δ T t) = x := by
      funext t; ring
    rw [hfun]
    exact hx
  · rintro ⟨e', q'⟩ h'
    change AnticipatedEqm P qbar Δ mbar T e' q' at h'
    rw [anticipated_iff_shockEqm] at h'
    have := huniq (e', fun t ↦ q' t - qstep qbar Δ T t) h'
    simp only [Prod.mk.injEq] at this ⊢
    obtain ⟨h1, h2⟩ := this
    refine ⟨h1, funext fun t ↦ ?_⟩
    have := congrFun h2 t
    linarith

/-! ## T11: money-demand shocks and the case for a peg (p. 631) -/

/-- O&R p. 631: the reduced system with a money-demand shock `ε` in
`m_t − p_t = −ηi_{t+1} + φy_t + ε_t`. -/
def ReducedMD (qbar : ℝ) (m ε e q : ℕ → ℝ) : Prop :=
  ∀ t, q (t + 1) - q t = -(P.ψ * P.δ) * (q t - qbar) ∧
    m t - ε t - e t + q t = -P.η * (e (t + 1) - e t) + P.φ * P.δ * (q t - qbar)

/-- O&R p. 631: a money-demand shock is a money-supply shock of the opposite sign: the model
with `(m, ε)` is the model with money `m − ε`. -/
theorem reducedMD_iff (qbar : ℝ) (m ε e q : ℕ → ℝ) :
    ReducedMD P qbar m ε e q ↔ Reduced P qbar (fun t ↦ m t - ε t) e q := Iff.rfl

/-- O&R p. 631, T11: under the accommodating policy `m_t = m̄ + ε_t` the economy with
money-demand shocks has EXACTLY the solutions of the shock-free economy with money `m̄`,
whatever the shock path. -/
theorem accommodation_iff (qbar mbar : ℝ) (ε e q : ℕ → ℝ) :
    ReducedMD P qbar (fun t ↦ mbar + ε t) ε e q ↔ Reduced P qbar (fun _ ↦ mbar) e q := by
  rw [reducedMD_iff]
  have : (fun t ↦ (fun t ↦ mbar + ε t) t - ε t) = fun _ ↦ mbar := by funext t; ring
  rw [this]

/-- O&R p. 631, T11: starting from the steady state (`p_0 = m̄`), the accommodating policy
insulates the economy completely: the unique no-bubble equilibrium has `e_t = m̄ + q̄`,
`q_t = q̄` (so output stays at `ȳ`) and a constant nominal interest rate `i* = 0`, for ANY
money-demand shock path. -/
theorem accommodation_insulates (qbar mbar : ℝ) (ε e q : ℕ → ℝ) (hs : P.ψ * P.δ < 2)
    (hr : ReducedMD P qbar (fun t ↦ mbar + ε t) ε e q) (hp : e 0 - q 0 = mbar)
    (hb : NoBubble P e) (t : ℕ) :
    e t = mbar + qbar ∧ q t = qbar ∧ e (t + 1) - e t = 0 := by
  have hS : ShockEqm P qbar (fun _ ↦ mbar) mbar e q :=
    ⟨(accommodation_iff P qbar mbar ε e q).1 hr, hp, hb⟩
  obtain ⟨h1, h2, -⟩ := real_shock P qbar mbar e q hs hS t
  obtain ⟨h3, -, -⟩ := real_shock P qbar mbar e q hs hS (t + 1)
  exact ⟨h1, h2, by rw [h1, h3]; ring⟩

/-- O&R p. 631, T11 (converse): holding the exchange rate at `ē = m̄ + q̄` from the steady state
(`q_0 = q̄`) REQUIRES `m_t − ε_t = m̄` at every date, i.e. automatic accommodation of every
money-demand shift. -/
theorem peg_requires_accommodation (qbar mbar : ℝ) (m ε e q : ℕ → ℝ)
    (hr : ReducedMD P qbar m ε e q) (he : ∀ t, e t = mbar + qbar) (hq : q 0 = qbar) (t : ℕ) :
    m t - ε t = mbar ∧ q t = qbar := by
  have hq' := q_closed_form P qbar _ e q ((reducedMD_iff P qbar m ε e q).1 hr) t
  rw [hq, sub_self, mul_zero] at hq'
  obtain ⟨-, h8⟩ := hr t
  rw [he t, he (t + 1)] at h8
  have hqt : q t = qbar := by linarith
  rw [hqt] at h8
  exact ⟨by linarith, hqt⟩

/-- O&R p. 631: under a FIXED money supply, an unanticipated permanent money-demand shift `ε̄`
at date 0 (from the steady state, `p_0 = m̄`) moves the real exchange rate and output on
impact: `q_0 − q̄ = −ε̄(1+ψδη)/D`, so `y_0 ≠ ȳ` whenever `ε̄ ≠ 0`. -/
theorem fixed_money_demand_shock (qbar mbar εbar : ℝ) (e q : ℕ → ℝ) (hs : P.ψ * P.δ < 2)
    (hr : ReducedMD P qbar (fun _ ↦ mbar) (fun _ ↦ εbar) e q) (hp : e 0 - q 0 = mbar)
    (hb : NoBubble P e) :
    q 0 - qbar = -εbar * (1 + P.ψ * P.δ * P.η) / P.D ∧
      (εbar ≠ 0 → P.δ * (q 0 - qbar) ≠ 0) := by
  have hS : ShockEqm P qbar (fun _ ↦ mbar - εbar) mbar e q := ⟨hr, hp, hb⟩
  have hi := (perm_shock_impact P qbar mbar (mbar - εbar) e q hs hS).1
  have e1 : mbar - εbar - mbar = -εbar := by ring
  rw [e1] at hi
  refine ⟨hi, fun hε ↦ ?_⟩
  rw [hi]
  exact mul_ne_zero P.δ_pos.ne' (div_ne_zero (mul_ne_zero (neg_ne_zero.2 hε)
    P.slope_denom_pos.ne') P.D_pos.ne')

/-! ## T12: a peg and a real shock (p. 632), with the sign correction -/

/-- O&R p. 632, T12: under a peg `e_t = ē = m̄ + q̄` with money endogenous, after an
unanticipated change `q̄ → q̄′` with `p_0 = m̄` predetermined (so `q_0 = q̄`):
`q_t − q̄′ = ρ^t(q̄ − q̄′)`, `p_t = m̄ + q̄ − q̄′ − ρ^t(q̄ − q̄′)`, and money must follow
`m_t = p_t + φ y_t` with `y_t = δ(q_t − q̄′)`. -/
theorem peg_real_shock (qbar qbar' mbar : ℝ) (m q : ℕ → ℝ)
    (hr : Reduced P qbar' m (fun _ ↦ mbar + qbar) q) (hq : q 0 = qbar) (t : ℕ) :
    q t - qbar' = P.ρ ^ t * (qbar - qbar') ∧
      (mbar + qbar) - q t = mbar + qbar - qbar' - P.ρ ^ t * (qbar - qbar') ∧
      m t = ((mbar + qbar) - q t) + P.φ * (P.δ * (q t - qbar')) := by
  have h1 := q_closed_form P qbar' m _ q hr t
  rw [hq] at h1
  obtain ⟨-, h8⟩ := hr t
  refine ⟨h1, by linarith, ?_⟩
  simp only [sub_self, mul_zero, zero_add] at h8
  linear_combination h8

/-- O&R p. 632, T12 (CORRECTED): under a peg, a FALL in the equilibrium real exchange rate
(`q̄′ < q̄`, a real appreciation) gives, with `ψδ < 1`, output ABOVE its natural rate at every
date and a strictly RISING price level: a temporary boom with inflation, not the book's
"downward adjustment after a period of unemployment". -/
theorem peg_real_appreciation_boom (qbar qbar' mbar : ℝ) (m q : ℕ → ℝ)
    (hr : Reduced P qbar' m (fun _ ↦ mbar + qbar) q) (hq : q 0 = qbar) (hs1 : P.ψ * P.δ < 1)
    (hfall : qbar' < qbar) (t : ℕ) :
    0 < P.δ * (q t - qbar') ∧ (mbar + qbar) - q t < (mbar + qbar) - q (t + 1) := by
  have hρ : 0 < P.ρ := by unfold ρ; linarith
  have hx : 0 < q t - qbar' := by
    rw [(peg_real_shock P qbar qbar' mbar m q hr hq t).1]
    exact mul_pos (pow_pos hρ t) (by linarith)
  refine ⟨mul_pos P.δ_pos hx, ?_⟩
  obtain ⟨h7, -⟩ := hr t
  have := mul_pos P.ψδ_pos hx
  linarith

/-- O&R p. 632, T12: the book's "unemployment and downward price adjustment" story is correct
for a RISE in `q̄` (a real depreciation): under a peg with `ψδ < 1`, output is below its natural
rate at every date and the price level strictly falls. -/
theorem peg_real_depreciation_slump (qbar qbar' mbar : ℝ) (m q : ℕ → ℝ)
    (hr : Reduced P qbar' m (fun _ ↦ mbar + qbar) q) (hq : q 0 = qbar) (hs1 : P.ψ * P.δ < 1)
    (hrise : qbar < qbar') (t : ℕ) :
    P.δ * (q t - qbar') < 0 ∧ (mbar + qbar) - q (t + 1) < (mbar + qbar) - q t := by
  have hρ : 0 < P.ρ := by unfold ρ; linarith
  have hx : q t - qbar' < 0 := by
    rw [(peg_real_shock P qbar qbar' mbar m q hr hq t).1]
    exact mul_neg_of_pos_of_neg (pow_pos hρ t) (by linarith)
  refine ⟨mul_neg_of_pos_of_neg P.δ_pos hx, ?_⟩
  obtain ⟨h7, -⟩ := hr t
  have := mul_neg_of_pos_of_neg P.ψδ_pos hx
  linarith

/-- O&R p. 632, T12: under the peg the price level converges to `m̄ + q̄ − q̄′`, so a fall in `q̄`
raises the long-run price level (the real appreciation is achieved through the price level). -/
theorem peg_real_shock_long_run (qbar qbar' mbar : ℝ) (m q : ℕ → ℝ)
    (hr : Reduced P qbar' m (fun _ ↦ mbar + qbar) q) (hq : q 0 = qbar) (hs : P.ψ * P.δ < 2) :
    Tendsto (fun t ↦ (mbar + qbar) - q t) atTop (𝓝 (mbar + qbar - qbar')) := by
  have hρ := tendsto_pow_atTop_nhds_zero_of_abs_lt_one (P.abs_ρ_lt_one hs)
  have := (hρ.mul_const (qbar - qbar')).const_sub (mbar + qbar - qbar')
  rw [zero_mul, sub_zero] at this
  exact this.congr fun t ↦ ((peg_real_shock P qbar qbar' mbar m q hr hq t).2.1).symm

/-- O&R p. 632, T12: the peg equilibrium exists: the explicit paths
`q_t = q̄′ + ρ^t(q̄ − q̄′)` and `m_t = ē − q_t + φδ(q_t − q̄′)` solve the model with `e ≡ ē`. -/
theorem peg_real_shock_exists (qbar qbar' mbar : ℝ) :
    Reduced P qbar' (fun t ↦ (mbar + qbar) - (qbar' + P.ρ ^ t * (qbar - qbar')) +
        P.φ * P.δ * ((qbar' + P.ρ ^ t * (qbar - qbar')) - qbar'))
      (fun _ ↦ mbar + qbar) (fun t ↦ qbar' + P.ρ ^ t * (qbar - qbar')) := by
  intro t
  unfold ρ
  constructor
  · simp only
    rw [pow_succ]
    ring
  · simp only
    ring

/-- O&R p. 632, T12 (float versus peg): after a real shock `q̄ → q̄′ ≠ q̄`, output stays at its
natural rate at every date under a float with fixed money (fn 11), but under a peg with
`ψδ < 1` output differs from its natural rate at every date. -/
theorem float_vs_peg (qbar qbar' mbar : ℝ) (e q m q' : ℕ → ℝ) (hs1 : P.ψ * P.δ < 1)
    (hfloat : ShockEqm P qbar' (fun _ ↦ mbar) mbar e q)
    (hpeg : Reduced P qbar' m (fun _ ↦ mbar + qbar) q') (hq : q' 0 = qbar)
    (hne : qbar' ≠ qbar) (t : ℕ) :
    P.δ * (q t - qbar') = 0 ∧ P.δ * (q' t - qbar') ≠ 0 := by
  constructor
  · rw [(real_shock P qbar' mbar e q (by linarith) hfloat t).2.1, sub_self, mul_zero]
  · rw [(peg_real_shock P qbar qbar' mbar m q' hpeg hq t).1]
    have hρ : 0 < P.ρ := by unfold ρ; linarith
    exact mul_ne_zero P.δ_pos.ne' (mul_ne_zero (pow_pos hρ t).ne' (sub_ne_zero.2 hne.symm))

/-! ## T13: the stochastic Dornbusch model on a finite event tree -/

/-- O&R p. 619 ("explicitly stochastic", T13): a finite-state event tree. Nodes are histories
`h : List S` (most recent state first); `prob h s` is the probability of moving from `h` to
`s :: h`. Transition probabilities may depend on the whole history (Markov chains are a special
case). -/
structure EventTree (S : Type) [Fintype S] where
  prob : List S → S → ℝ
  prob_nonneg : ∀ h s, 0 ≤ prob h s
  prob_sum : ∀ h, ∑ s, prob h s = 1

namespace Stochastic

variable {S : Type} [Fintype S] (τ : EventTree S)

/-- O&R p. 619: the conditional expectation `E_t X_{t+1}` at node `h`. -/
def condE (X : List S → ℝ) (h : List S) : ℝ := ∑ s, τ.prob h s * X (s :: h)

/-- O&R p. 619: conditional expectation of an affine function of next-period values, with the
constant `K` known at `h`: if `Z(s::h) = a X(s::h) + K` for all `s` then
`E_h Z = a E_h X + K`. -/
theorem condE_of_eq (a K : ℝ) (X Z : List S → ℝ) (h : List S)
    (hZ : ∀ s, Z (s :: h) = a * X (s :: h) + K) : condE τ Z h = a * condE τ X h + K := by
  unfold condE
  have e1 : ∑ s, τ.prob h s * Z (s :: h) =
      ∑ s, (a * (τ.prob h s * X (s :: h)) + K * τ.prob h s) := by
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    rw [hZ s]
    ring
  rw [e1, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, τ.prob_sum, mul_one]

/-- O&R p. 619: linearity of `E_t` in three processes plus a constant. -/
theorem condE_lin (a b c d : ℝ) (X Y Z : List S → ℝ) (h : List S) :
    condE τ (fun h' ↦ a * X h' + b * Y h' + c * Z h' + d) h =
      a * condE τ X h + b * condE τ Y h + c * condE τ Z h + d := by
  unfold condE
  have e1 : ∑ s, τ.prob h s * (a * X (s :: h) + b * Y (s :: h) + c * Z (s :: h) + d) =
      ∑ s, (a * (τ.prob h s * X (s :: h)) + b * (τ.prob h s * Y (s :: h)) +
        c * (τ.prob h s * Z (s :: h)) + d * τ.prob h s) := by
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    ring
  rw [e1, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, τ.prob_sum,
    mul_one]

/-- O&R p. 619: `|E_h X| ≤ B` when `|X| ≤ B` at every node. -/
theorem condE_abs_le (B : ℝ) (X : List S → ℝ) (hX : ∀ h, |X h| ≤ B) (h : List S) :
    |condE τ X h| ≤ B := by
  unfold condE
  calc |∑ s, τ.prob h s * X (s :: h)| ≤ ∑ s, |τ.prob h s * X (s :: h)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s, τ.prob h s * B := by
        refine Finset.sum_le_sum fun s _ ↦ ?_
        rw [abs_mul, abs_of_nonneg (τ.prob_nonneg h s)]
        exact mul_le_mul_of_nonneg_left (hX _) (τ.prob_nonneg h s)
    _ = B := by rw [← Finset.sum_mul, τ.prob_sum, one_mul]

/-- O&R p. 619: the `j`-step-ahead conditional expectation `E_t X_{t+j}`, defined by iterating
one-step expectations (the law of iterated expectations holds by construction). -/
def ahead : ℕ → (List S → ℝ) → List S → ℝ
  | 0, X, h => X h
  | j + 1, X, h => ∑ s, τ.prob h s * ahead j X (s :: h)

/-- O&R p. 619: `E_t X_{t+j+1} = E_t [E_{t+1} X_{t+j+1}]` (law of iterated expectations). -/
theorem ahead_succ (j : ℕ) (X : List S → ℝ) (h : List S) :
    ahead τ (j + 1) X h = condE τ (ahead τ j X) h := by
  rw [ahead]
  rfl

/-- O&R p. 619: linearity of `E_t X_{t+j}` in three processes plus a constant. -/
theorem ahead_lin (j : ℕ) : ∀ (a b c d : ℝ) (X Y Z : List S → ℝ) (h : List S),
    ahead τ j (fun h' ↦ a * X h' + b * Y h' + c * Z h' + d) h =
      a * ahead τ j X h + b * ahead τ j Y h + c * ahead τ j Z h + d := by
  induction j with
  | zero => intro a b c d X Y Z h; rfl
  | succ j ih =>
    intro a b c d X Y Z h
    rw [ahead_succ, ahead_succ, ahead_succ, ahead_succ]
    rw [← condE_lin]
    unfold condE
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    rw [ih]

/-- O&R p. 619: `|E_t X_{t+j}| ≤ B` when `|X| ≤ B` at every node. -/
theorem ahead_abs_le (B : ℝ) (X : List S → ℝ) (hX : ∀ h, |X h| ≤ B) :
    ∀ j h, |ahead τ j X h| ≤ B := by
  intro j
  induction j with
  | zero => intro h; exact hX h
  | succ j ih => intro h; rw [ahead_succ]; exact condE_abs_le τ B _ ih h

/-- O&R p. 619: if `E_h X_{next} = c X_h` at every node, then `E_t X_{t+j} = c^j X_t`. -/
theorem ahead_eigen (c : ℝ) (X : List S → ℝ) (hX : ∀ h, condE τ X h = c * X h) :
    ∀ j h, ahead τ j X h = c ^ j * X h := by
  intro j
  induction j with
  | zero => intro h; simp [ahead]
  | succ j ih =>
    intro h
    rw [ahead_succ]
    have : condE τ (ahead τ j X) h = c ^ j * condE τ X h := by
      unfold condE
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun s _ ↦ by rw [ih]; ring
    rw [this, hX, pow_succ]
    ring

/-- O&R p. 619, T13: the stochastic Dornbusch model at node `h` (normalisation
`p* = ȳ = i* = 0`): UIP `i_t = E_t e_{t+1} − e_t` (1), money demand (2), aggregate demand (3),
and the Phillips curve with EXPECTED flexible-price inflation,
`p_{t+1} − p_t = ψ y_t + E_t p̃_{t+1} − p̃_t` with `p̃ = e − q̄`; `p_{t+1}` is predetermined
(the same after every state `s`). -/
def StochStructural (qbar : ℝ) (m e p y i : List S → ℝ) : Prop :=
  ∀ h, i h = condE τ e h - e h ∧ m h - p h = -P.η * i h + P.φ * y h ∧
    y h = P.δ * (e h - p h - qbar) ∧
    ∀ s, p (s :: h) - p h = P.ψ * y h + (condE τ (fun h' ↦ e h' - qbar) h - (e h - qbar))

/-- O&R p. 619, T13: the reduced stochastic system. The real exchange rate moves by
`q̂_{t+1} = ρ q̂_t + (e_{t+1} − E_t e_{t+1})` (news), and the money market clears. -/
def StochReduced (qbar : ℝ) (m e q : List S → ℝ) : Prop :=
  ∀ h, (∀ s, q (s :: h) - qbar = P.ρ * (q h - qbar) + (e (s :: h) - condE τ e h)) ∧
    m h - e h + q h = -P.η * (condE τ e h - e h) + P.φ * P.δ * (q h - qbar)

/-- O&R p. 619, T13: the structural stochastic model implies the reduced system for
`q = e − p`. -/
theorem stoch_structural_to_reduced (qbar : ℝ) (m e p y i : List S → ℝ)
    (hS : StochStructural P τ qbar m e p y i) :
    StochReduced P τ qbar m e (fun h ↦ e h - p h) := by
  intro h
  obtain ⟨h1, h2, h3, h5⟩ := hS h
  have hc : condE τ (fun h' ↦ e h' - qbar) h = condE τ e h - qbar :=
    condE_of_eq τ 1 (-qbar) e _ h (fun s ↦ by ring) |>.trans (by ring)
  refine ⟨fun s ↦ ?_, ?_⟩
  · have := h5 s
    rw [hc, h3] at this
    unfold ρ
    linear_combination -this
  · rw [h1, h3] at h2
    linear_combination h2

/-- O&R p. 619, T13 (converse): every solution of the reduced system comes from the structural
model with `p = e − q`, `y = δ(q − q̄)`, `i = E e_{next} − e`. -/
theorem stoch_reduced_to_structural (qbar : ℝ) (m e q : List S → ℝ)
    (hr : StochReduced P τ qbar m e q) :
    StochStructural P τ qbar m e (fun h ↦ e h - q h) (fun h ↦ P.δ * (q h - qbar))
      (fun h ↦ condE τ e h - e h) := by
  intro h
  obtain ⟨h1, h2⟩ := hr h
  have hc : condE τ (fun h' ↦ e h' - qbar) h = condE τ e h - qbar :=
    condE_of_eq τ 1 (-qbar) e _ h (fun s ↦ by ring) |>.trans (by ring)
  refine ⟨rfl, by linear_combination h2, by ring, fun s ↦ ?_⟩
  rw [hc]
  have := h1 s
  unfold ρ at this
  linear_combination -this

/-- O&R p. 619, T13: along any solution the news has mean zero, so `E_t q̂_{t+1} = ρ q̂_t`. -/
theorem condE_q (qbar : ℝ) (m e q : List S → ℝ) (hr : StochReduced P τ qbar m e q)
    (h : List S) : condE τ q h - qbar = P.ρ * (q h - qbar) := by
  have := condE_of_eq τ 1 (qbar + P.ρ * (q h - qbar) - condE τ e h) e q h
    (fun s ↦ by linarith [(hr h).1 s])
  linarith

/-- O&R (19), stochastic version (T13): the flexible-price exchange rate
`e^flex_t = q̄ + (1/(1+η)) Σ_j r^j E_t m_{t+j}`. -/
noncomputable def seflex (qbar : ℝ) (m : List S → ℝ) (h : List S) : ℝ :=
  qbar + 1 / (1 + P.η) * ∑' j : ℕ, P.r ^ j * ahead τ j m h

/-- O&R (19), T13: for bounded money the discounted expected money path is summable. -/
theorem summable_ahead (M : ℝ) (m : List S → ℝ) (hM : ∀ h, |m h| ≤ M) (h : List S) :
    Summable fun j ↦ P.r ^ j * ahead τ j m h := by
  refine Summable.of_norm_bounded
    ((summable_geometric_of_lt_one P.r_pos.le P.r_lt_one).mul_right M) fun j ↦ ?_
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos P.r_pos]
  exact mul_le_mul_of_nonneg_left (ahead_abs_le τ M m hM j h) (pow_pos P.r_pos j).le

/-- O&R (19), T13: `|e^flex − q̄| ≤ M` when `|m| ≤ M`. -/
theorem seflex_abs_le (qbar M : ℝ) (m : List S → ℝ) (hM : ∀ h, |m h| ≤ M) (h : List S) :
    |seflex P τ qbar m h - qbar| ≤ M := by
  have hs := summable_ahead P τ M m hM h
  have hg := (summable_geometric_of_lt_one P.r_pos.le P.r_lt_one).mul_right M
  have hb : ∀ j, |P.r ^ j * ahead τ j m h| ≤ P.r ^ j * M := fun j ↦ by
    rw [abs_mul, abs_pow, abs_of_pos P.r_pos]
    exact mul_le_mul_of_nonneg_left (ahead_abs_le τ M m hM j h) (pow_pos P.r_pos j).le
  have hup := hs.tsum_le_tsum (fun j ↦ (abs_le.1 (hb j)).2) hg
  have hlo := hg.neg.tsum_le_tsum (fun j ↦ (abs_le.1 (hb j)).1) hs
  rw [tsum_neg] at hlo
  rw [tsum_mul_right, P.tsum_r_pow] at hup hlo
  unfold seflex
  rw [add_sub_cancel_left, abs_le]
  have h1 := P.one_add_η_pos
  constructor
  · rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ h1]; linarith
  · rw [div_mul_eq_mul_div, one_mul, div_le_iff₀ h1]; linarith

/-- O&R (19), T13: the stochastic flexible-price exchange rate solves the expectational Cagan
recursion `η E_t e^flex_{t+1} = (1+η) e^flex_t − q̄ − m_t`. -/
theorem seflex_condE (qbar M : ℝ) (m : List S → ℝ) (hM : ∀ h, |m h| ≤ M) (h : List S) :
    P.η * condE τ (seflex P τ qbar m) h = (1 + P.η) * seflex P τ qbar m h - qbar - m h := by
  set G : List S → ℝ := fun h' ↦ ∑' j : ℕ, P.r ^ j * ahead τ j m h' with hG
  have hsf : seflex P τ qbar m = fun h' ↦ 1 / (1 + P.η) * G h' + qbar := by
    funext h'; unfold seflex; rw [hG]; ring
  have hcE : condE τ (seflex P τ qbar m) h = 1 / (1 + P.η) * condE τ G h + qbar := by
    rw [hsf]
    exact condE_of_eq τ (1 / (1 + P.η)) qbar G _ h (fun s ↦ rfl)
  have hG1 : condE τ G h = ∑' j : ℕ, P.r ^ j * ahead τ (j + 1) m h := by
    unfold condE
    rw [hG]
    simp only
    have e1 : ∀ s, τ.prob h s * ∑' j : ℕ, P.r ^ j * ahead τ j m (s :: h) =
        ∑' j : ℕ, τ.prob h s * (P.r ^ j * ahead τ j m (s :: h)) := fun s ↦
      (tsum_mul_left).symm
    simp_rw [e1]
    rw [← Summable.tsum_finsetSum (fun s _ ↦ (summable_ahead P τ M m hM (s :: h)).mul_left _)]
    congr 1
    funext j
    rw [ahead_succ]
    unfold condE
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ ↦ by ring
  have hG0 : G h = m h + P.r * ∑' j : ℕ, P.r ^ j * ahead τ (j + 1) m h := by
    rw [hG]
    simp only
    rw [(summable_ahead P τ M m hM h).tsum_eq_zero_add]
    simp only [pow_zero, one_mul, pow_succ]
    rw [← tsum_mul_left]
    have e0 : ahead τ 0 m h = m h := rfl
    rw [e0]
    congr 1
    exact tsum_congr fun j ↦ by ring
  rw [hcE, hsf]
  simp only
  rw [hG0, ← hG1]
  have h1 := P.one_add_η_pos.ne'
  unfold r
  field_simp
  ring

/-- O&R (16), (18), T13: the stochastic saddle deviation `d = e − e^flex − κ(q − q̄)`. -/
noncomputable def sdev (qbar : ℝ) (m e q : List S → ℝ) (h : List S) : ℝ :=
  e h - seflex P τ qbar m h - P.κ * (q h - qbar)

/-- O&R p. 619, T13 core (new, exact): along ANY solution of the stochastic model the saddle
deviation is an explosive martingale-like process, `E_t d_{t+1} = ((1+η)/η) d_t`. -/
theorem sdev_condE (qbar M : ℝ) (m e q : List S → ℝ) (hM : ∀ h, |m h| ≤ M)
    (hr : StochReduced P τ qbar m e q) (h : List S) :
    condE τ (sdev P τ qbar m e q) h = (1 + P.η) / P.η * sdev P τ qbar m e q h := by
  have hlin := condE_lin τ 1 (-1) (-P.κ) (P.κ * qbar) e (seflex P τ qbar m) q h
  have e1 : (fun h' ↦ 1 * e h' + -1 * seflex P τ qbar m h' + -P.κ * q h' + P.κ * qbar) =
      sdev P τ qbar m e q := by funext h'; unfold sdev; ring
  rw [e1] at hlin
  have hf := seflex_condE P τ qbar M m hM h
  have hq := condE_q P τ qbar m e q hr h
  obtain ⟨-, h8⟩ := hr h
  have hκ := P.κ_mul
  rw [hlin, div_mul_eq_mul_div, eq_div_iff P.η_pos.ne']
  unfold sdev ρ at *
  linear_combination h8 - hf - P.κ * P.η * hq + (q h - qbar) * hκ

/-- O&R p. 619, T13: `E_t d_{t+T} = ((1+η)/η)^T d_t`, equivalently `d_t = r^T E_t d_{t+T}`. -/
theorem sdev_eq_r_pow (qbar M : ℝ) (m e q : List S → ℝ) (hM : ∀ h, |m h| ≤ M)
    (hr : StochReduced P τ qbar m e q) (T : ℕ) (h : List S) :
    sdev P τ qbar m e q h = P.r ^ T * ahead τ T (sdev P τ qbar m e q) h := by
  rw [ahead_eigen τ _ _ (sdev_condE P τ qbar M m e q hM hr) T h, ← mul_assoc,
    P.r_pow_mul_growth_pow, one_mul]

/-- O&R (14), stochastic version (T13): the no-bubble condition at every node,
`lim_{T→∞} r^T E_t e_{t+T} = 0`. -/
def SNoBubble (e : List S → ℝ) : Prop :=
  ∀ h, Tendsto (fun T ↦ P.r ^ T * ahead τ T e h) atTop (𝓝 0)

/-- O&R p. 619, T13: bounded exchange-rate processes satisfy the no-bubble condition. -/
theorem bounded_no_bubble (B : ℝ) (e : List S → ℝ) (hB : ∀ h, |e h| ≤ B) :
    SNoBubble P τ e := by
  intro h
  have hr := (tendsto_pow_atTop_nhds_zero_of_lt_one P.r_pos.le P.r_lt_one).mul_const B
  rw [zero_mul] at hr
  refine squeeze_zero_norm (fun T ↦ ?_) hr
  rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_of_pos P.r_pos]
  exact mul_le_mul_of_nonneg_left (ahead_abs_le τ B e hB T h) (pow_pos P.r_pos T).le

/-- O&R p. 619, T13 (UNIQUENESS, the hard part): along any no-bubble solution the saddle
deviation vanishes at every node, i.e. `e = e^flex + κ(q − q̄)`. Proof: `d_t = r^T E_t d_{t+T}`,
and each of `r^T E_t e_{t+T}`, `r^T E_t e^flex_{t+T}` (bounded) and
`r^T E_t q̂_{t+T} = (rρ)^T q̂_t` tends to zero. -/
theorem sdev_zero_of_no_bubble (qbar M : ℝ) (m e q : List S → ℝ) (hM : ∀ h, |m h| ≤ M)
    (hs : P.ψ * P.δ < 2) (hr : StochReduced P τ qbar m e q) (hb : SNoBubble P τ e)
    (h : List S) : sdev P τ qbar m e q h = 0 := by
  have hdec : ∀ T, P.r ^ T * ahead τ T (sdev P τ qbar m e q) h =
      P.r ^ T * ahead τ T e h - P.r ^ T * ahead τ T (seflex P τ qbar m) h -
        P.κ * ((P.r * P.ρ) ^ T * (q h - qbar)) := by
    intro T
    have hlin := ahead_lin τ T 1 (-1) (-P.κ) (P.κ * qbar) e (seflex P τ qbar m) q h
    have e1 : (fun h' ↦ 1 * e h' + -1 * seflex P τ qbar m h' + -P.κ * q h' + P.κ * qbar) =
        sdev P τ qbar m e q := by funext h'; unfold sdev; ring
    rw [e1] at hlin
    have hq1 := ahead_lin τ T 1 0 0 (-qbar) q q q h
    have e2 : (fun h' ↦ 1 * q h' + 0 * q h' + 0 * q h' + -qbar) = fun h' ↦ q h' - qbar := by
      funext h'; ring
    rw [e2] at hq1
    have hq2 := ahead_eigen τ P.ρ (fun h' ↦ q h' - qbar) (fun h' ↦ by
      have := condE_lin τ 1 0 0 (-qbar) q q q h'
      have e3 : (fun h'' ↦ 1 * q h'' + 0 * q h'' + 0 * q h'' + -qbar) = fun h'' ↦ q h'' - qbar :=
        by funext h''; ring
      rw [e3] at this
      rw [this]
      linarith [condE_q P τ qbar m e q hr h']) T h
    rw [hlin, mul_pow]
    linear_combination P.κ * P.r ^ T * hq1 - P.κ * P.r ^ T * hq2
  have hf : Tendsto (fun T ↦ P.r ^ T * ahead τ T (seflex P τ qbar m) h) atTop (𝓝 0) :=
    bounded_no_bubble P τ (|qbar| + M) _ (fun h' ↦ by
      have := seflex_abs_le P τ qbar M m hM h'
      calc |seflex P τ qbar m h'| = |(seflex P τ qbar m h' - qbar) + qbar| := by ring_nf
        _ ≤ |seflex P τ qbar m h' - qbar| + |qbar| := abs_add_le _ _
        _ ≤ |qbar| + M := by linarith) h
  have hq : Tendsto (fun T ↦ (P.r * P.ρ) ^ T) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one (P.abs_rρ_lt_one hs)
  have hlim := ((hb h).sub hf).sub ((hq.mul_const (q h - qbar)).const_mul P.κ)
  simp only [sub_zero, zero_mul, mul_zero] at hlim
  have hconst : Tendsto (fun _ : ℕ ↦ sdev P τ qbar m e q h) atTop
      (𝓝 (sdev P τ qbar m e q h)) := tendsto_const_nhds
  refine tendsto_nhds_unique hconst (hlim.congr fun T ↦ ?_)
  rw [← hdec T, ← sdev_eq_r_pow P τ qbar M m e q hM hr T h]

/-- O&R p. 619, T13: along a solution with `d ≡ 0`, the real exchange rate responds only to news
about fundamentals: `(1 − κ)(q̂_{t+1} − ρ q̂_t) = e^flex_{t+1} − E_t e^flex_{t+1}`. -/
theorem q_news (qbar : ℝ) (m e q : List S → ℝ) (hr : StochReduced P τ qbar m e q)
    (hd : ∀ h, sdev P τ qbar m e q h = 0) (h : List S) (s : S) :
    (1 - P.κ) * (q (s :: h) - qbar - P.ρ * (q h - qbar)) =
      seflex P τ qbar m (s :: h) - condE τ (seflex P τ qbar m) h := by
  have he : e = fun h' ↦ 1 * seflex P τ qbar m h' + P.κ * q h' + 0 * q h' + (-(P.κ * qbar)) := by
    funext h'
    have := hd h'
    unfold sdev at this
    linarith
  have hce := condE_lin τ 1 P.κ 0 (-(P.κ * qbar)) (seflex P τ qbar m) q q h
  rw [← he] at hce
  have hq := condE_q P τ qbar m e q hr h
  have h1 := (hr h).1 s
  have hes : e (s :: h) = 1 * seflex P τ qbar m (s :: h) + P.κ * q (s :: h) +
      0 * q (s :: h) + (-(P.κ * qbar)) := congrFun he (s :: h)
  linear_combination h1 + hes - hce - P.κ * hq

/-- O&R p. 619, T13: the explicit no-bubble real exchange rate, defined recursively on the event
tree: `q̂_{[]} = q_0 − q̄` and `q̂_{s::h} = ρ q̂_h + (e^flex_{s::h} − E_h e^flex)/(1 − κ)`. -/
noncomputable def sq (qbar : ℝ) (m : List S → ℝ) (q0 : ℝ) : List S → ℝ
  | [] => q0
  | s :: h => qbar + P.ρ * (sq qbar m q0 h - qbar) +
      (seflex P τ qbar m (s :: h) - condE τ (seflex P τ qbar m) h) / (1 - P.κ)

/-- O&R (16), (18), stochastic (T13): the explicit no-bubble exchange rate
`e = e^flex + κ(q − q̄)`. -/
noncomputable def se (qbar : ℝ) (m : List S → ℝ) (q0 : ℝ) (h : List S) : ℝ :=
  seflex P τ qbar m h + P.κ * (sq P τ qbar m q0 h - qbar)

/-- O&R p. 619, T13 (existence, guess-and-verify): the explicit processes solve the stochastic
model, with the SAME saddle slope `κ` as under perfect foresight. -/
theorem sol_reduced (qbar M : ℝ) (m : List S → ℝ) (hM : ∀ h, |m h| ≤ M) (q0 : ℝ) :
    StochReduced P τ qbar m (se P τ qbar m q0) (sq P τ qbar m q0) := by
  have hk := P.one_sub_κ_ne
  have hsq : ∀ h, condE τ (sq P τ qbar m q0) h =
      qbar + P.ρ * (sq P τ qbar m q0 h - qbar) := by
    intro h
    have := condE_of_eq τ (1 / (1 - P.κ)) (qbar + P.ρ * (sq P τ qbar m q0 h - qbar) -
      condE τ (seflex P τ qbar m) h / (1 - P.κ)) (seflex P τ qbar m) (sq P τ qbar m q0) h
      (fun s ↦ by simp only [sq]; ring)
    rw [this]
    field_simp
    ring
  have hse : ∀ h, condE τ (se P τ qbar m q0) h =
      condE τ (seflex P τ qbar m) h + P.κ * P.ρ * (sq P τ qbar m q0 h - qbar) := by
    intro h
    have := condE_lin τ 1 P.κ 0 (-(P.κ * qbar)) (seflex P τ qbar m) (sq P τ qbar m q0)
      (sq P τ qbar m q0) h
    have e1 : (fun h' ↦ 1 * seflex P τ qbar m h' + P.κ * sq P τ qbar m q0 h' +
        0 * sq P τ qbar m q0 h' + -(P.κ * qbar)) = se P τ qbar m q0 := by
      funext h'; unfold se; ring
    rw [e1] at this
    rw [this, hsq]
    ring
  intro h
  refine ⟨fun s ↦ ?_, ?_⟩
  · rw [hse]
    unfold se
    simp only [sq]
    field_simp
    ring
  · rw [hse]
    have hf := seflex_condE P τ qbar M m hM h
    have hκ := P.κ_mul
    unfold se ρ
    linear_combination hf - (sq P τ qbar m q0 h - qbar) * hκ

/-- O&R p. 619, T13: the explicit solution is bounded:
`|q̂_h| ≤ |q_0 − q̄| + 2M/((1−κ)(1−|ρ|))` at every node. -/
theorem sq_bounded (qbar M : ℝ) (m : List S → ℝ) (hM : ∀ h, |m h| ≤ M) (q0 : ℝ)
    (hs : P.ψ * P.δ < 2) : ∀ h, |sq P τ qbar m q0 h - qbar| ≤
      |q0 - qbar| + 2 * M / (1 - P.κ) / (1 - |P.ρ|) := by
  have hk : 0 < 1 - P.κ := by linarith [P.κ_lt_one]
  have hρ := P.abs_ρ_lt_one hs
  have h1ρ : 0 < 1 - |P.ρ| := by linarith
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM [])
  have hC : 0 ≤ 2 * M / (1 - P.κ) := div_nonneg (by linarith) hk.le
  have hnews : ∀ h s, |(seflex P τ qbar m (s :: h) - condE τ (seflex P τ qbar m) h) /
      (1 - P.κ)| ≤ 2 * M / (1 - P.κ) := by
    intro h s
    rw [abs_div, abs_of_pos hk]
    refine div_le_div_of_nonneg_right ?_ hk.le
    have ha := seflex_abs_le P τ qbar M m hM (s :: h)
    have hb : |condE τ (seflex P τ qbar m) h - qbar| ≤ M := by
      have := condE_of_eq τ 1 (-qbar) (seflex P τ qbar m) (fun h' ↦ seflex P τ qbar m h' - qbar)
        h (fun s ↦ by ring)
      have e2 := condE_abs_le τ M _ (seflex_abs_le P τ qbar M m hM) h
      have e3 : 1 * condE τ (seflex P τ qbar m) h + -qbar =
          condE τ (seflex P τ qbar m) h - qbar := by ring
      rw [this, e3] at e2
      exact e2
    calc |seflex P τ qbar m (s :: h) - condE τ (seflex P τ qbar m) h|
        = |(seflex P τ qbar m (s :: h) - qbar) - (condE τ (seflex P τ qbar m) h - qbar)| := by
          ring_nf
      _ ≤ |seflex P τ qbar m (s :: h) - qbar| + |condE τ (seflex P τ qbar m) h - qbar| :=
          abs_sub _ _
      _ ≤ 2 * M := by linarith
  intro h
  induction h with
  | nil => simp only [sq]; linarith [div_nonneg hC h1ρ.le]
  | cons s h ih =>
    simp only [sq]
    set C := 2 * M / (1 - P.κ)
    set x := sq P τ qbar m q0 h - qbar
    have e1 : qbar + P.ρ * x + (seflex P τ qbar m (s :: h) - condE τ (seflex P τ qbar m) h) /
        (1 - P.κ) - qbar = P.ρ * x + (seflex P τ qbar m (s :: h) -
          condE τ (seflex P τ qbar m) h) / (1 - P.κ) := by ring
    rw [e1]
    have hCd : C / (1 - |P.ρ|) * (1 - |P.ρ|) = C := div_mul_cancel₀ C h1ρ.ne'
    calc |P.ρ * x + (seflex P τ qbar m (s :: h) - condE τ (seflex P τ qbar m) h) / (1 - P.κ)|
        ≤ |P.ρ * x| + C := by
          refine (abs_add_le _ _).trans ?_
          linarith [hnews h s]
      _ = |P.ρ| * |x| + C := by rw [abs_mul]
      _ ≤ |P.ρ| * (|q0 - qbar| + C / (1 - |P.ρ|)) + C := by
          gcongr
      _ ≤ |q0 - qbar| + C / (1 - |P.ρ|) := by
          have h2 : |P.ρ| * |q0 - qbar| ≤ |q0 - qbar| :=
            mul_le_of_le_one_left (abs_nonneg _) hρ.le
          nlinarith [div_nonneg hC h1ρ.le]

/-- O&R p. 619, T13: the explicit exchange rate is bounded, hence satisfies the no-bubble
condition. -/
theorem se_bounded (qbar M : ℝ) (m : List S → ℝ) (hM : ∀ h, |m h| ≤ M) (q0 : ℝ)
    (hs : P.ψ * P.δ < 2) : ∃ B, ∀ h, |se P τ qbar m q0 h| ≤ B ∧ |sq P τ qbar m q0 h| ≤ B := by
  set K := |q0 - qbar| + 2 * M / (1 - P.κ) / (1 - |P.ρ|)
  refine ⟨|qbar| + M + |P.κ| * K + (|qbar| + K), fun h ↦ ⟨?_, ?_⟩⟩
  · have h1 : |sq P τ qbar m q0 h - qbar| ≤ K := sq_bounded P τ qbar M m hM q0 hs h
    have h2 := seflex_abs_le P τ qbar M m hM h
    unfold se
    calc |seflex P τ qbar m h + P.κ * (sq P τ qbar m q0 h - qbar)|
        = |(seflex P τ qbar m h - qbar) + qbar + P.κ * (sq P τ qbar m q0 h - qbar)| := by
          ring_nf
      _ ≤ |(seflex P τ qbar m h - qbar) + qbar| + |P.κ * (sq P τ qbar m q0 h - qbar)| :=
          abs_add_le _ _
      _ ≤ (|seflex P τ qbar m h - qbar| + |qbar|) + |P.κ| * |sq P τ qbar m q0 h - qbar| := by
          rw [abs_mul]; gcongr; exact abs_add_le _ _
      _ ≤ (M + |qbar|) + |P.κ| * K := by gcongr
      _ ≤ |qbar| + M + |P.κ| * K + (|qbar| + K) := by
          have : 0 ≤ |qbar| + K := by
            have := abs_nonneg (sq P τ qbar m q0 h - qbar)
            linarith [abs_nonneg qbar]
          linarith
  · have h1 : |sq P τ qbar m q0 h - qbar| ≤ K := sq_bounded P τ qbar M m hM q0 hs h
    have h3 : 0 ≤ |P.κ| * K := mul_nonneg (abs_nonneg _)
      (le_trans (abs_nonneg _) h1)
    calc |sq P τ qbar m q0 h| = |(sq P τ qbar m q0 h - qbar) + qbar| := by ring_nf
      _ ≤ |sq P τ qbar m q0 h - qbar| + |qbar| := abs_add_le _ _
      _ ≤ |qbar| + M + |P.κ| * K + (|qbar| + K) := by
          have := le_trans (abs_nonneg _) (hM [])
          linarith [abs_nonneg qbar]

/-- O&R p. 619, T13: two no-bubble solutions (`d ≡ 0`) with the same initial real exchange rate
coincide at every node of the tree. -/
theorem stoch_unique_of_sdev_zero (qbar : ℝ) (m e q e' q' : List S → ℝ)
    (hr : StochReduced P τ qbar m e q) (hr' : StochReduced P τ qbar m e' q')
    (hd : ∀ h, sdev P τ qbar m e q h = 0) (hd' : ∀ h, sdev P τ qbar m e' q' h = 0)
    (h0 : q [] = q' []) : e = e' ∧ q = q' := by
  have hq : ∀ h, q h = q' h := by
    intro h
    induction h with
    | nil => exact h0
    | cons s h ih =>
      have h1 := q_news P τ qbar m e q hr hd h s
      have h2 := q_news P τ qbar m e' q' hr' hd' h s
      rw [ih] at h1
      have h3 : (1 - P.κ) * (q (s :: h) - q' (s :: h)) = 0 := by linear_combination h1 - h2
      rcases mul_eq_zero.1 h3 with h4 | h4
      · exact absurd h4 P.one_sub_κ_ne
      · linarith
  refine ⟨funext fun h ↦ ?_, funext hq⟩
  have h1 := hd h
  have h2 := hd' h
  unfold sdev at h1 h2
  rw [hq h] at h1
  linarith

/-- O&R p. 619, T13 (existence AND uniqueness): with bounded money and `0 < ψδ < 2`, for every
initial real exchange rate there is exactly one solution of the stochastic Dornbusch model on
the event tree satisfying the no-bubble condition. -/
theorem stoch_exists_unique_no_bubble (qbar M : ℝ) (m : List S → ℝ) (hM : ∀ h, |m h| ≤ M)
    (hs : P.ψ * P.δ < 2) (q0 : ℝ) :
    ∃! x : (List S → ℝ) × (List S → ℝ),
      x.2 [] = q0 ∧ StochReduced P τ qbar m x.1 x.2 ∧ SNoBubble P τ x.1 := by
  obtain ⟨B, hB⟩ := se_bounded P τ qbar M m hM q0 hs
  refine ⟨(se P τ qbar m q0, sq P τ qbar m q0), ⟨rfl, sol_reduced P τ qbar M m hM q0,
    bounded_no_bubble P τ B _ fun h ↦ (hB h).1⟩, ?_⟩
  rintro ⟨e, q⟩ ⟨hq0, hr, hb⟩
  have hd := sdev_zero_of_no_bubble P τ qbar M m e q hM hs hr hb
  have hd' := sdev_zero_of_no_bubble P τ qbar M m _ _ hM hs (sol_reduced P τ qbar M m hM q0)
    (bounded_no_bubble P τ B _ fun h ↦ (hB h).1)
  obtain ⟨h1, h2⟩ := stoch_unique_of_sdev_zero P τ qbar m e q _ _ hr
    (sol_reduced P τ qbar M m hM q0) hd hd' hq0
  simp only [Prod.mk.injEq]
  exact ⟨h1, h2⟩

/-- O&R p. 619, T13 (uniqueness among bounded solutions): with bounded money and
`0 < ψδ < 2`, for every initial real exchange rate there is exactly one BOUNDED solution; the
unstable root `(1+η)/η > 1` rules out every other bounded path. -/
theorem stoch_exists_unique_bounded (qbar M : ℝ) (m : List S → ℝ) (hM : ∀ h, |m h| ≤ M)
    (hs : P.ψ * P.δ < 2) (q0 : ℝ) :
    ∃! x : (List S → ℝ) × (List S → ℝ), x.2 [] = q0 ∧ StochReduced P τ qbar m x.1 x.2 ∧
      ∃ B, ∀ h, |x.1 h| ≤ B ∧ |x.2 h| ≤ B := by
  obtain ⟨B, hB⟩ := se_bounded P τ qbar M m hM q0 hs
  refine ⟨(se P τ qbar m q0, sq P τ qbar m q0), ⟨rfl, sol_reduced P τ qbar M m hM q0, B, hB⟩,
    ?_⟩
  rintro ⟨e, q⟩ ⟨hq0, hr, B', hB'⟩
  have hd := sdev_zero_of_no_bubble P τ qbar M m e q hM hs hr
    (bounded_no_bubble P τ B' e fun h ↦ (hB' h).1)
  have hd' := sdev_zero_of_no_bubble P τ qbar M m _ _ hM hs (sol_reduced P τ qbar M m hM q0)
    (bounded_no_bubble P τ B _ fun h ↦ (hB h).1)
  obtain ⟨h1, h2⟩ := stoch_unique_of_sdev_zero P τ qbar m e q _ _ hr
    (sol_reduced P τ qbar M m hM q0) hd hd' hq0
  simp only [Prod.mk.injEq]
  exact ⟨h1, h2⟩

/-- O&R (18), stochastic (T13): every no-bubble solution satisfies
`e_t = e^flex_t + κ(q_t − q̄)` with `e^flex_t = q̄ + (1/(1+η)) Σ r^j E_t m_{t+j}`. -/
theorem stoch_saddle_form (qbar M : ℝ) (m e q : List S → ℝ) (hM : ∀ h, |m h| ≤ M)
    (hs : P.ψ * P.δ < 2) (hr : StochReduced P τ qbar m e q) (hb : SNoBubble P τ e)
    (h : List S) : e h = seflex P τ qbar m h + P.κ * (q h - qbar) := by
  have := sdev_zero_of_no_bubble P τ qbar M m e q hM hs hr hb h
  unfold sdev at this
  linarith

/-- O&R p. 613 and p. 619, T13: the selection criterion is essential. For every `b ≠ 0` the
process `e + b ((1+η)/η)^t` (a deterministic bubble on top of the no-bubble solution) also
solves the stochastic model, with the same real exchange rate, but violates the no-bubble
condition. -/
theorem stoch_bubble_solutions (qbar M : ℝ) (m : List S → ℝ) (hM : ∀ h, |m h| ≤ M) (q0 : ℝ)
    (hs : P.ψ * P.δ < 2) (b : ℝ) (hb : b ≠ 0) :
    StochReduced P τ qbar m (fun h ↦ se P τ qbar m q0 h + b * ((1 + P.η) / P.η) ^ h.length)
        (sq P τ qbar m q0) ∧
      ¬ SNoBubble P τ (fun h ↦ se P τ qbar m q0 h + b * ((1 + P.η) / P.η) ^ h.length) := by
  set g := (1 + P.η) / P.η
  have hcb : ∀ h, condE τ (fun h' ↦ b * g ^ h'.length) h = g * (b * g ^ h.length) := by
    intro h
    have := condE_of_eq τ 0 (b * g ^ (h.length + 1)) (fun h' ↦ b * g ^ h'.length)
      (fun h' ↦ b * g ^ h'.length) h (fun s ↦ by simp)
    rw [this, pow_succ]
    ring
  have hce : ∀ h, condE τ (fun h' ↦ se P τ qbar m q0 h' + b * g ^ h'.length) h =
      condE τ (se P τ qbar m q0) h + g * (b * g ^ h.length) := by
    intro h
    have := condE_lin τ 1 1 0 0 (se P τ qbar m q0) (fun h' ↦ b * g ^ h'.length)
      (se P τ qbar m q0) h
    simp only [one_mul, zero_mul, add_zero] at this
    rw [this, hcb]
  have hsol := sol_reduced P τ qbar M m hM q0
  refine ⟨fun h ↦ ⟨fun s ↦ ?_, ?_⟩, ?_⟩
  · rw [hce]
    have := (hsol h).1 s
    simp only [List.length_cons]
    rw [pow_succ]
    linear_combination this
  · rw [hce]
    have := (hsol h).2
    have hg : P.η * g = 1 + P.η := by
      simp only [g]; field_simp [P.η_pos.ne']
    linear_combination this + (b * g ^ h.length) * hg
  · intro hnb
    obtain ⟨B, hB⟩ := se_bounded P τ qbar M m hM q0 hs
    have h1 := bounded_no_bubble P τ B _ (fun h ↦ (hB h).1) []
    have hab : ∀ j (h : List S), ahead τ j (fun h' ↦ b * g ^ h'.length) h =
        g ^ j * (b * g ^ h.length) := ahead_eigen τ g _ hcb
    have h2 : ∀ T, P.r ^ T * ahead τ T (fun h ↦ se P τ qbar m q0 h + b * g ^ h.length) [] =
        P.r ^ T * ahead τ T (se P τ qbar m q0) [] + b := by
      intro T
      have := ahead_lin τ T 1 1 0 0 (se P τ qbar m q0) (fun h' ↦ b * g ^ h'.length)
        (se P τ qbar m q0) []
      simp only [one_mul, zero_mul, add_zero] at this
      rw [this, hab, mul_add, ← mul_assoc, P.r_pow_mul_growth_pow]
      simp
    have h3 := (hnb []).congr h2
    have h4 := h1.add_const b
    rw [zero_add] at h4
    exact hb (tendsto_nhds_unique h4 h3)

/-- O&R p. 619, T13 ("price stickiness affects the conditional variance of the exchange rate"):
along the no-bubble solution the exchange-rate news is the flexible-price news scaled by
`1/(1−κ) = (1+ψδη)/D`, so the conditional variance is scaled by `((1+ψδη)/D)²`, which exceeds
one iff `φδ < 1`. -/
theorem stoch_conditional_variance (qbar M : ℝ) (m e q : List S → ℝ) (hM : ∀ h, |m h| ≤ M)
    (hs : P.ψ * P.δ < 2) (hr : StochReduced P τ qbar m e q) (hb : SNoBubble P τ e)
    (h : List S) :
    (∀ s, e (s :: h) - condE τ e h = (1 + P.ψ * P.δ * P.η) / P.D *
      (seflex P τ qbar m (s :: h) - condE τ (seflex P τ qbar m) h)) ∧
    ∑ s, τ.prob h s * (e (s :: h) - condE τ e h) ^ 2 =
      ((1 + P.ψ * P.δ * P.η) / P.D) ^ 2 *
        ∑ s, τ.prob h s * (seflex P τ qbar m (s :: h) - condE τ (seflex P τ qbar m) h) ^ 2 ∧
    (0 < ∑ s, τ.prob h s * (seflex P τ qbar m (s :: h) - condE τ (seflex P τ qbar m) h) ^ 2 →
      (∑ s, τ.prob h s * (seflex P τ qbar m (s :: h) - condE τ (seflex P τ qbar m) h) ^ 2 <
        ∑ s, τ.prob h s * (e (s :: h) - condE τ e h) ^ 2 ↔ P.φ * P.δ < 1)) := by
  have hd := sdev_zero_of_no_bubble P τ qbar M m e q hM hs hr hb
  have hnews : ∀ s, e (s :: h) - condE τ e h = (1 + P.ψ * P.δ * P.η) / P.D *
      (seflex P τ qbar m (s :: h) - condE τ (seflex P τ qbar m) h) := by
    intro s
    have h1 := q_news P τ qbar m e q hr hd h s
    have h2 := (hr h).1 s
    have hx : e (s :: h) - condE τ e h = q (s :: h) - qbar - P.ρ * (q h - qbar) := by linarith
    rw [hx]
    have := solve_one_sub_κ P _ _ h1
    rw [this]
    ring
  set c := (1 + P.ψ * P.δ * P.η) / P.D with hc
  set V := ∑ s, τ.prob h s * (seflex P τ qbar m (s :: h) - condE τ (seflex P τ qbar m) h) ^ 2
  have hV : ∑ s, τ.prob h s * (e (s :: h) - condE τ e h) ^ 2 = c ^ 2 * V := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun s _ ↦ by rw [hnews s]; ring
  refine ⟨hnews, hV, fun hvar ↦ ?_⟩
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

end Stochastic

end ObstfeldRogoff.NominalRigidities.DornbuschExtensions
