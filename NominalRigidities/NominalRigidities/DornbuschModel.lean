/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# The Mundell–Fleming–Dornbusch sticky-price model

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §9.2.1–9.2.4,
pp. 609–619.

The small open economy has uncovered interest parity (1), Cagan money demand (2), aggregate
demand increasing in the real exchange rate (3), the real exchange rate `q = e + p* − p` (4),
demand-determined output and a predetermined price level that adjusts according to the Mussa
Phillips curve (5)/(6). With `p* = ȳ = i* = 0` the model reduces to the linear system (7), (8)
[equivalently (9)] in the real exchange rate `q` and the nominal exchange rate `e`.

Because the model is exactly linear, the phase-diagram analysis of pp. 612–613 can be replaced
by an exact, global statement. Put `r = η/(1+η)`, `ρ = 1 − ψδ`, `κ = (1−φδ)/(1+ψδη)` and let
`e^flex_t = q̄ + (1/(1+η)) Σ_s r^s m_{t+s}` (19). Along ANY solution, `q_t − q̄ = ρ^t (q_0 − q̄)`
and the deviation `d_t = e_t − e^flex_t − κ(q_t − q̄)` from the saddle path obeys
`d_{t+1} = d_t / r` exactly. Consequences proved here:

* the reduction (5) ⇒ (6), (1)–(6) ⇒ (7), (8) ⇔ (9), and the forward form of p. 616 (T1);
* the unique steady state (10) and long-run neutrality (T2);
* the GLOBAL saddle-path theorem (T3): for every `q_0` exactly one `e_0` gives a convergent
  (equivalently bounded, equivalently no-bubble) path, namely the one on the saddle path (16);
  every other `e_0` explodes (`d_0 > 0`) or implodes (`d_0 < 0`); and `κ` is the only slope
  with this property. The no-bubble condition `lim r^T e_T = 0` is thus DERIVED to select
  exactly the saddle path, and `lim r^T e_T = d_0` along every solution;
* the forward solution (14)–(16) for a general summable money path, with existence and
  uniqueness of the no-bubble solution (T4), and (18)–(19);
* the slopes of the `Δe = 0` schedule and the saddle path (T5), p. 614.

Stability: the book assumes `1 > ψδ` (p. 612). Convergence of `q` needs only `0 < ψδ < 2`
(oscillatory for `1 < ψδ < 2`); we use that weaker hypothesis wherever it suffices and prove
that for `ψδ > 2` the real exchange rate diverges from any non-steady-state start.
-/

namespace ObstfeldRogoff.NominalRigidities.DornbuschModel

open Filter Topology

/-- O&R §9.2.1, pp. 609–612: the structural parameters of the Dornbusch model, the
semi-elasticity of money demand `η`, the income elasticity of money demand `φ`, the
real-exchange-rate elasticity of aggregate demand `δ` and the speed of price adjustment `ψ`,
all strictly positive. -/
structure DornbuschParams where
  η : ℝ
  φ : ℝ
  δ : ℝ
  ψ : ℝ
  η_pos : 0 < η
  φ_pos : 0 < φ
  δ_pos : 0 < δ
  ψ_pos : 0 < ψ

namespace DornbuschParams

variable (P : DornbuschParams)

/-- O&R (14), p. 616: the forward discount factor `r = η/(1+η)` of the Cagan-type equation. -/
noncomputable def r : ℝ := P.η / (1 + P.η)

/-- O&R (13), p. 616: the root `ρ = 1 − ψδ` of the real-exchange-rate dynamics. -/
def ρ : ℝ := 1 - P.ψ * P.δ

/-- O&R (16), p. 617: the slope `κ = (1−φδ)/(1+ψδη)` of the saddle path. -/
noncomputable def κ : ℝ := (1 - P.φ * P.δ) / (1 + P.ψ * P.δ * P.η)

/-- O&R (17), p. 617: the denominator `D = φδ + ψδη` of the impact multipliers. -/
def D : ℝ := P.φ * P.δ + P.ψ * P.δ * P.η

/-- O&R §9.2.3: `1 + η > 0`. -/
theorem one_add_η_pos : 0 < 1 + P.η := by linarith [P.η_pos]

/-- O&R §9.2.2: `ψδ > 0`. -/
theorem ψδ_pos : 0 < P.ψ * P.δ := mul_pos P.ψ_pos P.δ_pos

/-- O&R §9.2.2: `φδ > 0`. -/
theorem φδ_pos : 0 < P.φ * P.δ := mul_pos P.φ_pos P.δ_pos

/-- O&R (16), p. 617: the saddle-path denominator `1 + ψδη` is positive. -/
theorem slope_denom_pos : 0 < 1 + P.ψ * P.δ * P.η := by
  have := mul_pos P.ψδ_pos P.η_pos
  linarith

/-- O&R (17), p. 617: `D = φδ + ψδη > 0`. -/
theorem D_pos : 0 < P.D := by
  unfold D
  have := mul_pos P.ψδ_pos P.η_pos
  linarith [P.φδ_pos]

/-- O&R (14), p. 616: `0 < r`. -/
theorem r_pos : 0 < P.r := div_pos P.η_pos P.one_add_η_pos

/-- O&R (14), p. 616: `r < 1`. -/
theorem r_lt_one : P.r < 1 := by
  unfold r
  rw [div_lt_one P.one_add_η_pos]
  linarith

/-- O&R (14), p. 616: `1 − r = 1/(1+η)`. -/
theorem one_sub_r : 1 - P.r = 1 / (1 + P.η) := by
  unfold r
  field_simp [P.one_add_η_pos.ne']
  ring

/-- O&R §9.2.3: the unstable root of (9) is `1/r = (1+η)/η > 1`. -/
theorem one_lt_growth : 1 < (1 + P.η) / P.η := by
  rw [one_lt_div P.η_pos]
  linarith

/-- O&R §9.2.3: `r^T · ((1+η)/η)^T = 1`. -/
theorem r_pow_mul_growth_pow (T : ℕ) : P.r ^ T * ((1 + P.η) / P.η) ^ T = 1 := by
  rw [← mul_pow]
  have : P.r * ((1 + P.η) / P.η) = 1 := by
    unfold r
    field_simp [P.one_add_η_pos.ne', P.η_pos.ne']
  rw [this, one_pow]

/-- O&R (16), p. 617: the defining identity `κ (1 + ψδη) = 1 − φδ`. -/
theorem κ_mul : P.κ * (1 + P.ψ * P.δ * P.η) = 1 - P.φ * P.δ := by
  unfold κ
  exact div_mul_cancel₀ _ P.slope_denom_pos.ne'

/-- O&R (16)–(17): `1 − κ = D/(1+ψδη)`. -/
theorem one_sub_κ : 1 - P.κ = P.D / (1 + P.ψ * P.δ * P.η) := by
  rw [eq_div_iff P.slope_denom_pos.ne', sub_mul, P.κ_mul]
  unfold D
  ring

/-- O&R (17), p. 617: `1/(1−κ) = (1+ψδη)/D`. -/
theorem inv_one_sub_κ : 1 / (1 - P.κ) = (1 + P.ψ * P.δ * P.η) / P.D := by
  rw [P.one_sub_κ, one_div_div]

/-- O&R p. 614: the saddle-path slope satisfies `κ < 1`. -/
theorem κ_lt_one : P.κ < 1 := by
  have h := P.one_sub_κ
  have : 0 < P.D / (1 + P.ψ * P.δ * P.η) := div_pos P.D_pos P.slope_denom_pos
  linarith

/-- O&R (16): `1 − κ ≠ 0`. -/
theorem one_sub_κ_ne : 1 - P.κ ≠ 0 := by linarith [P.κ_lt_one]

/-- O&R p. 612, corrected: `|ρ| < 1` (convergence of `q`) holds iff `0 < ψδ < 2`; with the
parameters positive it needs only `ψδ < 2`, not the book's `ψδ < 1`. -/
theorem abs_ρ_lt_one (hs : P.ψ * P.δ < 2) : |P.ρ| < 1 := by
  unfold ρ
  rw [abs_lt]
  constructor <;> linarith [P.ψδ_pos]

/-- O&R (15)–(16): `|rρ| < 1` under `ψδ < 2`. -/
theorem abs_rρ_lt_one (hs : P.ψ * P.δ < 2) : |P.r * P.ρ| < 1 := by
  rw [abs_mul, abs_of_pos P.r_pos]
  have h1 := P.abs_ρ_lt_one hs
  have h2 := P.r_lt_one
  have h3 := abs_nonneg P.ρ
  nlinarith [P.r_pos]

/-- O&R (15)–(16), p. 617: `1 − rρ = (1+ψδη)/(1+η)`. -/
theorem one_sub_rρ : 1 - P.r * P.ρ = (1 + P.ψ * P.δ * P.η) / (1 + P.η) := by
  unfold r ρ
  field_simp [P.one_add_η_pos.ne']
  ring

/-- O&R (14), p. 616: `Σ_s r^s = 1 + η`. -/
theorem tsum_r_pow : ∑' s : ℕ, P.r ^ s = 1 + P.η := by
  rw [tsum_geometric_of_lt_one P.r_pos.le P.r_lt_one, P.one_sub_r]
  field_simp

/-- O&R (15)→(16), p. 617: `Σ_s (rρ)^s = (1+η)/(1+ψδη)`. -/
theorem tsum_rρ_pow (hs : P.ψ * P.δ < 2) :
    ∑' s : ℕ, (P.r * P.ρ) ^ s = (1 + P.η) / (1 + P.ψ * P.δ * P.η) := by
  rw [tsum_geometric_of_abs_lt_one (P.abs_rρ_lt_one hs), P.one_sub_rρ]
  field_simp

end DornbuschParams

open DornbuschParams

variable (P : DornbuschParams)

/-! ## T1: the structural model and its reduction -/

/-- O&R p. 611: the flexible-output price level `p̃_t = e_t + p*_t − q̄_t`. -/
def ptilde (e pstar qbar : ℕ → ℝ) (t : ℕ) : ℝ := e t + pstar t - qbar t

/-- O&R (1)–(5), pp. 609–611: the structural Dornbusch model with foreign interest rate `i*`,
foreign price level `p*_t`, natural output `ȳ` and equilibrium real exchange rate `q̄_t`
(paths, allowed to vary), money `m`, and endogenous `e, p, y, i`. Output is demand-determined
(`y = y^d`), and the price level `p` is predetermined: `p_{t+1}` is set by (5). -/
def Structural (istar : ℝ) (pstar qbar : ℕ → ℝ) (ybar : ℝ) (m e p y i : ℕ → ℝ) : Prop :=
  ∀ t, i (t + 1) = istar + e (t + 1) - e t ∧
    m t - p t = -P.η * i (t + 1) + P.φ * y t ∧
    y t = ybar + P.δ * (e t + pstar t - p t - qbar t) ∧
    p (t + 1) - p t = P.ψ * (y t - ybar) + (ptilde e pstar qbar (t + 1) - ptilde e pstar qbar t)

/-- O&R (5) ⇒ (6), p. 612: with `p*` and `q̄` constant, the Mussa Phillips curve (5) is
equivalent to `p_{t+1} − p_t = ψ(y_t − ȳ) + e_{t+1} − e_t` (6). -/
theorem phillips_five_iff_six (pstar qbar ybar : ℝ) (e p y : ℕ → ℝ) (t : ℕ) :
    (p (t + 1) - p t = P.ψ * (y t - ybar) +
        (ptilde e (fun _ ↦ pstar) (fun _ ↦ qbar) (t + 1) -
          ptilde e (fun _ ↦ pstar) (fun _ ↦ qbar) t)) ↔
      p (t + 1) - p t = P.ψ * (y t - ybar) + e (t + 1) - e t := by
  unfold ptilde
  constructor <;> intro h <;> linarith

/-- O&R (7), p. 612: from (3), (4), (6), with `p*`, `q̄` constant, the real exchange rate
`q = e + p* − p` obeys `Δq_{t+1} = −ψδ(q_t − q̄)` whatever `i*`, `ȳ` and money are. -/
theorem structural_real_dynamics (istar pstar qbar ybar : ℝ) (m e p y i : ℕ → ℝ)
    (h : Structural P istar (fun _ ↦ pstar) (fun _ ↦ qbar) ybar m e p y i) (t : ℕ) :
    (e (t + 1) + pstar - p (t + 1)) - (e t + pstar - p t) =
      -(P.ψ * P.δ) * ((e t + pstar - p t) - qbar) := by
  obtain ⟨-, -, h3, h5⟩ := h t
  unfold ptilde at h5
  rw [h3] at h5
  linear_combination -h5

/-- O&R (8), p. 612, general constants: (1)–(4) give the money-market equation
`m − e − p* + q = −η(i* + e_{t+1} − e_t) + φ(ȳ + δ(q − q̄))` with `q = e + p* − p`. -/
theorem structural_money_market (istar pstar qbar ybar : ℝ) (m e p y i : ℕ → ℝ)
    (h : Structural P istar (fun _ ↦ pstar) (fun _ ↦ qbar) ybar m e p y i) (t : ℕ) :
    m t - e t - pstar + (e t + pstar - p t) =
      -P.η * (istar + e (t + 1) - e t) + P.φ * (ybar + P.δ * ((e t + pstar - p t) - qbar)) := by
  obtain ⟨h1, h2, h3, -⟩ := h t
  rw [h1, h3] at h2
  linear_combination h2

/-- O&R (7)–(8), p. 612: the reduced Dornbusch system in `(e, q)` under the normalisation
`p* = ȳ = i* = 0`, with constant `q̄` and a money path `m`:
`q_{t+1} − q_t = −ψδ(q_t − q̄)` (7) and `m_t − e_t + q_t = −η(e_{t+1} − e_t) + φδ(q_t − q̄)` (8). -/
def Reduced (qbar : ℝ) (m e q : ℕ → ℝ) : Prop :=
  ∀ t, q (t + 1) - q t = -(P.ψ * P.δ) * (q t - qbar) ∧
    m t - e t + q t = -P.η * (e (t + 1) - e t) + P.φ * P.δ * (q t - qbar)

/-- O&R (1)–(8), pp. 609–612: under `p* = ȳ = i* = 0` and constant `q̄`, the structural model
implies the reduced system for `q = e − p`, with output `y_t = δ(q_t − q̄)` and interest rate
`i_{t+1} = e_{t+1} − e_t`. -/
theorem structural_to_reduced (qbar : ℝ) (m e p y i : ℕ → ℝ)
    (h : Structural P 0 (fun _ ↦ 0) (fun _ ↦ qbar) 0 m e p y i) :
    Reduced P qbar m e (fun t ↦ e t - p t) ∧ (∀ t, y t = P.δ * ((e t - p t) - qbar)) ∧
      ∀ t, i (t + 1) = e (t + 1) - e t := by
  refine ⟨fun t ↦ ⟨?_, ?_⟩, fun t ↦ ?_, fun t ↦ ?_⟩
  · have := structural_real_dynamics P 0 0 qbar 0 m e p y i h t
    simp only [add_zero] at this
    linarith
  · have := structural_money_market P 0 0 qbar 0 m e p y i h t
    simp only [add_zero, sub_zero, zero_add] at this
    linear_combination this
  · obtain ⟨-, -, h3, -⟩ := h t
    rw [h3]
    ring
  · obtain ⟨h1, -⟩ := h t
    linarith

/-- O&R (1)–(8), converse: every solution of the reduced system comes from the structural
model with `p = e − q`, `y = δ(q − q̄)` and `i_{t+1} = e_{t+1} − e_t` (`i_0` is free). So the
reduction loses nothing. -/
theorem reduced_to_structural (qbar i0 : ℝ) (m e q : ℕ → ℝ) (h : Reduced P qbar m e q) :
    Structural P 0 (fun _ ↦ 0) (fun _ ↦ qbar) 0 m e (fun t ↦ e t - q t)
      (fun t ↦ P.δ * (q t - qbar))
      (fun t ↦ Nat.casesOn t i0 (fun s ↦ e (s + 1) - e s)) := by
  intro t
  obtain ⟨h7, h8⟩ := h t
  refine ⟨by simp, ?_, by ring, ?_⟩
  · simp only
    linear_combination h8
  · unfold ptilde
    linear_combination -h7

/-- O&R (9), p. 612: the money-market equation (8) is equivalent to
`Δe_{t+1} = e_t/η − (1−φδ)q_t/η − (φδq̄ + m_t)/η`. -/
theorem money_market_iff_nine (qbar : ℝ) (m e q : ℕ → ℝ) (t : ℕ) :
    (m t - e t + q t = -P.η * (e (t + 1) - e t) + P.φ * P.δ * (q t - qbar)) ↔
      e (t + 1) - e t = e t / P.η - (1 - P.φ * P.δ) * q t / P.η -
        (P.φ * P.δ * qbar + m t) / P.η := by
  have hη := P.η_pos.ne'
  constructor
  · intro h
    field_simp
    linear_combination h
  · intro h
    field_simp at h
    linear_combination h

/-- O&R p. 616: the forward form of (9),
`e_t − q̄ = r(e_{t+1} − q̄) + ((1−φδ)/(1+η))(q_t − q̄) + m_t/(1+η)`. -/
theorem forward_form (qbar : ℝ) (m e q : ℕ → ℝ) (h : Reduced P qbar m e q) (t : ℕ) :
    e t - qbar = P.r * (e (t + 1) - qbar) + (1 - P.φ * P.δ) / (1 + P.η) * (q t - qbar) +
      m t / (1 + P.η) := by
  obtain ⟨-, h8⟩ := h t
  have := P.one_add_η_pos.ne'
  unfold r
  field_simp
  linear_combination -h8

/-! ## T2: the steady state (10) -/

/-- O&R (10), p. 612 and fn 8: with `m ≡ m̄` and `ψδ ≠ 0`, a constant path `(e, q)` solves the
reduced system iff `q = q̄` and `e = m̄ + q̄`; then `p = e − q = m̄`. -/
theorem steady_state_iff (qbar mbar e q : ℝ) :
    Reduced P qbar (fun _ ↦ mbar) (fun _ ↦ e) (fun _ ↦ q) ↔ q = qbar ∧ e = mbar + qbar := by
  constructor
  · intro h
    obtain ⟨h7, h8⟩ := h 0
    have hq : q = qbar := by
      have h7' : P.ψ * P.δ * (q - qbar) = 0 := by linarith
      rcases mul_eq_zero.1 h7' with h0 | h0
      · exact absurd h0 P.ψδ_pos.ne'
      · linarith
    refine ⟨hq, ?_⟩
    subst hq
    linarith
  · rintro ⟨rfl, rfl⟩ t
    constructor <;> ring

/-- O&R p. 613: a permanent money change `m̄ → m̄′` moves the steady-state price level and
exchange rate one for one, `p̄′ − p̄ = ē′ − ē = m̄′ − m̄`, with the real exchange rate
unchanged (long-run neutrality). -/
theorem steady_state_neutral (qbar mbar mbar' : ℝ) :
    ((mbar' + qbar) - qbar) - ((mbar + qbar) - qbar) = mbar' - mbar ∧
      (mbar' + qbar) - (mbar + qbar) = mbar' - mbar := by
  constructor <;> ring

/-- O&R p. 613: in the steady state the nominal interest rate equals `i* = 0`
(`i_{t+1} = e_{t+1} − e_t = 0`), and output is at its natural rate. -/
theorem steady_state_interest (qbar mbar : ℝ) (t : ℕ) :
    (fun _ : ℕ ↦ mbar + qbar) (t + 1) - (fun _ : ℕ ↦ mbar + qbar) t = 0 ∧
      P.δ * (qbar - qbar) = 0 := by
  constructor <;> ring

/-! ## The real exchange rate: (13) -/

/-- O&R (13), p. 616: along any solution, `q_t − q̄ = (1−ψδ)^t (q_0 − q̄)`. -/
theorem q_closed_form (qbar : ℝ) (m e q : ℕ → ℝ) (h : Reduced P qbar m e q) (t : ℕ) :
    q t - qbar = P.ρ ^ t * (q 0 - qbar) := by
  induction t with
  | zero => simp
  | succ n ih =>
    obtain ⟨h7, -⟩ := h n
    rw [pow_succ]
    unfold ρ at *
    linear_combination h7 + (1 - P.ψ * P.δ) * ih

/-- O&R p. 612, corrected: with `0 < ψδ < 2` the real exchange rate converges to `q̄` from
any initial condition (monotonically if `ψδ ≤ 1`, with oscillation if `1 < ψδ < 2`). -/
theorem q_tendsto (qbar : ℝ) (m e q : ℕ → ℝ) (h : Reduced P qbar m e q)
    (hs : P.ψ * P.δ < 2) : Tendsto q atTop (𝓝 qbar) := by
  have h1 : Tendsto (fun t ↦ P.ρ ^ t * (q 0 - qbar) + qbar) atTop (𝓝 (0 * (q 0 - qbar) + qbar))
    := ((tendsto_pow_atTop_nhds_zero_of_abs_lt_one (P.abs_ρ_lt_one hs)).mul_const _).add_const _
  rw [zero_mul, zero_add] at h1
  refine h1.congr fun t ↦ ?_
  have := q_closed_form P qbar m e q h t
  linarith

/-- O&R p. 612: if `ψδ ≤ 1` the adjustment of `q` is monotone: `q_t − q̄` never changes sign
and `|q_{t+1} − q̄| ≤ |q_t − q̄|`. -/
theorem q_monotone_adjustment (qbar : ℝ) (m e q : ℕ → ℝ) (h : Reduced P qbar m e q)
    (h1 : P.ψ * P.δ ≤ 1) (t : ℕ) :
    0 ≤ (q (t + 1) - qbar) * (q t - qbar) ∧ |q (t + 1) - qbar| ≤ |q t - qbar| := by
  obtain ⟨h7, -⟩ := h t
  have hq : q (t + 1) - qbar = (1 - P.ψ * P.δ) * (q t - qbar) := by linear_combination h7
  have hρ0 : 0 ≤ 1 - P.ψ * P.δ := by linarith
  have hρ1 : 1 - P.ψ * P.δ ≤ 1 := by linarith [P.ψδ_pos]
  rw [hq]
  constructor
  · rw [mul_assoc]; exact mul_nonneg hρ0 (mul_self_nonneg _)
  · rw [abs_mul, abs_of_nonneg hρ0]
    exact mul_le_of_le_one_left (abs_nonneg _) hρ1

/-- O&R p. 612: if `1 < ψδ` the adjustment of `q` oscillates: `q_t − q̄` changes sign every
period (unless it is already zero). -/
theorem q_oscillates (qbar : ℝ) (m e q : ℕ → ℝ) (h : Reduced P qbar m e q)
    (h1 : 1 < P.ψ * P.δ) (t : ℕ) (hq0 : q t ≠ qbar) :
    (q (t + 1) - qbar) * (q t - qbar) < 0 := by
  obtain ⟨h7, -⟩ := h t
  have hq : q (t + 1) - qbar = (1 - P.ψ * P.δ) * (q t - qbar) := by linear_combination h7
  rw [hq, mul_assoc]
  exact mul_neg_of_neg_of_pos (by linarith) (mul_self_pos.2 (sub_ne_zero.2 hq0))

/-- O&R p. 612, the boundary of stability: if `ψδ > 2` then `q` does not converge to `q̄`
unless it starts there (`|q_t − q̄| → ∞`). -/
theorem q_diverges (qbar : ℝ) (m e q : ℕ → ℝ) (h : Reduced P qbar m e q)
    (h2 : 2 < P.ψ * P.δ) (hq0 : q 0 ≠ qbar) :
    Tendsto (fun t ↦ |q t - qbar|) atTop atTop := by
  have hρ : 1 < |P.ρ| := by
    unfold ρ
    rw [abs_of_neg (by linarith)]
    linarith
  have hpos : 0 < |q 0 - qbar| := abs_pos.2 (sub_ne_zero.2 hq0)
  have := (tendsto_pow_atTop_atTop_of_one_lt hρ).atTop_mul_const hpos
  refine this.congr fun t ↦ ?_
  rw [q_closed_form P qbar m e q h t, abs_mul, abs_pow]

/-! ## The flexible-price exchange rate (19) and the saddle deviation -/

/-- O&R (19), p. 618: the flexible-price exchange rate
`e^flex_t = q̄ + (1/(1+η)) Σ_{s≥0} r^s m_{t+s}`. -/
noncomputable def eflex (qbar : ℝ) (m : ℕ → ℝ) (t : ℕ) : ℝ :=
  qbar + 1 / (1 + P.η) * ∑' s : ℕ, P.r ^ s * m (s + t)

/-- O&R (14): summability of the discounted money path is inherited by every shift. -/
theorem summable_shift (m : ℕ → ℝ) (hm : Summable fun s ↦ P.r ^ s * m s) (t : ℕ) :
    Summable fun s ↦ P.r ^ s * m (s + t) := by
  have h1 : Summable fun s ↦ P.r ^ (s + t) * m (s + t) := (summable_nat_add_iff t).2 hm
  have h2 := h1.mul_left (P.r ^ t)⁻¹
  refine h2.congr fun s ↦ ?_
  rw [pow_add]
  field_simp [(pow_pos P.r_pos t).ne']

/-- O&R (19): the flexible-price exchange rate solves the forward (Cagan) recursion
`η e^flex_{t+1} = (1+η) e^flex_t − q̄ − m_t`. -/
theorem eflex_succ (qbar : ℝ) (m : ℕ → ℝ) (hm : Summable fun s ↦ P.r ^ s * m s) (t : ℕ) :
    P.η * eflex P qbar m (t + 1) = (1 + P.η) * eflex P qbar m t - qbar - m t := by
  unfold eflex
  have hs := summable_shift P m hm t
  rw [hs.tsum_eq_zero_add]
  simp only [pow_zero, one_mul, zero_add, pow_succ]
  have e1 : ∑' b : ℕ, P.r ^ b * P.r * m (b + 1 + t) =
      P.r * ∑' b : ℕ, P.r ^ b * m (b + (t + 1)) := by
    rw [← tsum_mul_left]
    congr 1
    funext b
    rw [show b + 1 + t = b + (t + 1) by ring]
    ring
  rw [e1]
  have := P.one_add_η_pos.ne'
  unfold r
  field_simp
  ring

/-- O&R (10), (19): with a constant money supply `m̄` the flexible-price exchange rate is
`e^flex = m̄ + q̄`. -/
theorem eflex_const (qbar mbar : ℝ) (t : ℕ) : eflex P qbar (fun _ ↦ mbar) t = mbar + qbar := by
  unfold eflex
  rw [tsum_mul_right, P.tsum_r_pow]
  field_simp [P.one_add_η_pos.ne']
  ring

/-- O&R (14): a constant money supply satisfies the summability hypothesis `Σ r^s |m_s| < ∞`. -/
theorem summable_const_money (mbar : ℝ) : Summable fun s ↦ P.r ^ s * (fun _ : ℕ ↦ mbar) s :=
  (summable_geometric_of_lt_one P.r_pos.le P.r_lt_one).mul_right mbar

/-- O&R (14): the flexible-price path itself satisfies the no-bubble condition,
`r^T e^flex_T → 0`. -/
theorem eflex_no_bubble (qbar : ℝ) (m : ℕ → ℝ) :
    Tendsto (fun T ↦ P.r ^ T * eflex P qbar m T) atTop (𝓝 0) := by
  have hr := tendsto_pow_atTop_nhds_zero_of_lt_one P.r_pos.le P.r_lt_one
  have htail := tendsto_sum_nat_add fun s ↦ P.r ^ s * m s
  have h := (hr.mul_const qbar).add (htail.const_mul (1 / (1 + P.η)))
  simp only [zero_mul, mul_zero, add_zero] at h
  refine h.congr fun T ↦ ?_
  unfold eflex
  rw [mul_add, ← tsum_mul_left, ← tsum_mul_left, ← tsum_mul_left]
  congr 2
  funext s
  rw [pow_add]
  ring

/-- O&R (16), (18): the deviation from the saddle path,
`d_t = e_t − e^flex_t − κ(q_t − q̄)`. -/
noncomputable def dev (qbar : ℝ) (m e q : ℕ → ℝ) (t : ℕ) : ℝ :=
  e t - eflex P qbar m t - P.κ * (q t - qbar)

/-- T3/T4 core recursion (new; the exact form of Fig. 9.4's dynamics): along ANY solution of
(7)–(8), the saddle deviation grows at the unstable root, `d_{t+1} = ((1+η)/η) d_t`. -/
theorem dev_succ (qbar : ℝ) (m e q : ℕ → ℝ) (hm : Summable fun s ↦ P.r ^ s * m s)
    (h : Reduced P qbar m e q) (t : ℕ) :
    dev P qbar m e q (t + 1) = (1 + P.η) / P.η * dev P qbar m e q t := by
  obtain ⟨h7, h8⟩ := h t
  have hf := eflex_succ P qbar m hm t
  have hκ := P.κ_mul
  have key : P.η * dev P qbar m e q (t + 1) = (1 + P.η) * dev P qbar m e q t := by
    unfold dev
    linear_combination h8 - hf - P.κ * P.η * h7 + (q t - qbar) * hκ
  rw [div_mul_eq_mul_div, eq_div_iff P.η_pos.ne']
  linear_combination key

/-- O&R §9.2.3: the deviation after `T` periods, `d_T = ((1+η)/η)^T d_0`. -/
theorem dev_closed_form (qbar : ℝ) (m e q : ℕ → ℝ) (hm : Summable fun s ↦ P.r ^ s * m s)
    (h : Reduced P qbar m e q) (t : ℕ) :
    dev P qbar m e q t = ((1 + P.η) / P.η) ^ t * dev P qbar m e q 0 := by
  induction t with
  | zero => simp
  | succ n ih => rw [dev_succ P qbar m e q hm h n, ih, pow_succ]; ring

/-- O&R §9.2.3: the complete closed form of every solution,
`e_t = e^flex_t + κ ρ^t (q_0 − q̄) + ((1+η)/η)^t d_0`. -/
theorem e_closed_form (qbar : ℝ) (m e q : ℕ → ℝ) (hm : Summable fun s ↦ P.r ^ s * m s)
    (h : Reduced P qbar m e q) (t : ℕ) :
    e t = eflex P qbar m t + P.κ * (P.ρ ^ t * (q 0 - qbar)) +
      ((1 + P.η) / P.η) ^ t * dev P qbar m e q 0 := by
  rw [← dev_closed_form P qbar m e q hm h t, ← q_closed_form P qbar m e q h t]
  unfold dev
  ring

/-- O&R §9.2.3: the saddle-path slope is unique. A slope `k` makes `ê − k q̂` evolve
autonomously at the unstable root `(1+η)/η` from EVERY state `(ê, q̂)` iff `k = κ`
(`ê' = ((1+η)ê − (1−φδ)q̂)/η`, `q̂' = ρ q̂` is the dynamics of (7)–(9) in deviations). -/
theorem saddle_slope_unique (k : ℝ) :
    (∀ ehat qhat : ℝ, ((1 + P.η) * ehat - (1 - P.φ * P.δ) * qhat) / P.η - k * (P.ρ * qhat) =
      (1 + P.η) / P.η * (ehat - k * qhat)) ↔ k = P.κ := by
  have hη := P.η_pos.ne'
  have hd := P.slope_denom_pos.ne'
  constructor
  · intro h
    have h1 := h 0 1
    unfold κ
    unfold ρ at h1
    field_simp at h1
    rw [eq_div_iff hd]
    linear_combination h1
  · rintro rfl ehat qhat
    have hκ := P.κ_mul
    unfold ρ
    field_simp
    linear_combination qhat * hκ

/-- O&R §9.2.3, Supplement C to Ch. 2: `(1, κ)` is the eigenvector of the stable root `ρ`,
so the saddle path is invariant: a point on it maps to a point on it. -/
theorem saddle_path_invariant (qhat : ℝ) :
    ((1 + P.η) * (P.κ * qhat) - (1 - P.φ * P.δ) * qhat) / P.η = P.κ * (P.ρ * qhat) := by
  have := (saddle_slope_unique P P.κ).2 rfl (P.κ * qhat) qhat
  rw [sub_self, mul_zero] at this
  linarith

/-! ## T4: existence and uniqueness of solutions, the no-bubble condition, (14)–(19) -/

/-- O&R §9.2.3: a solution of the first-order system is determined by its initial values: two
solutions with the same `(e_0, q_0)` coincide. -/
theorem reduced_unique_of_init (qbar : ℝ) (m e q e' q' : ℕ → ℝ) (h : Reduced P qbar m e q)
    (h' : Reduced P qbar m e' q') (he : e 0 = e' 0) (hq : q 0 = q' 0) : e = e' ∧ q = q' := by
  have key : ∀ t, e t = e' t ∧ q t = q' t := by
    intro t
    induction t with
    | zero => exact ⟨he, hq⟩
    | succ n ih =>
      obtain ⟨h7, h8⟩ := h n
      obtain ⟨h7', h8'⟩ := h' n
      obtain ⟨ihe, ihq⟩ := ih
      rw [ihe, ihq] at h8
      rw [ihq] at h7
      constructor
      · have : P.η * (e (n + 1) - e' (n + 1)) = 0 := by linear_combination h8 - h8'
        rcases mul_eq_zero.1 this with h0 | h0
        · exact absurd h0 P.η_pos.ne'
        · linarith
      · linarith
  exact ⟨funext fun t ↦ (key t).1, funext fun t ↦ (key t).2⟩

/-- O&R §9.2.3: the explicit solution through `(q_0, d_0)`: `q_t = q̄ + ρ^t(q_0 − q̄)` and
`e_t = e^flex_t + κρ^t(q_0 − q̄) + ((1+η)/η)^t d_0`. -/
noncomputable def solE (qbar : ℝ) (m : ℕ → ℝ) (q0 d0 : ℝ) (t : ℕ) : ℝ :=
  eflex P qbar m t + P.κ * (P.ρ ^ t * (q0 - qbar)) + ((1 + P.η) / P.η) ^ t * d0

/-- O&R (13): the explicit real-exchange-rate path `q_t = q̄ + ρ^t(q_0 − q̄)`. -/
def solQ (qbar q0 : ℝ) (t : ℕ) : ℝ := qbar + P.ρ ^ t * (q0 - qbar)

/-- O&R §9.2.3: the explicit paths solve (7)–(8) for every `(q_0, d_0)`. -/
theorem sol_reduced (qbar : ℝ) (m : ℕ → ℝ) (hm : Summable fun s ↦ P.r ^ s * m s)
    (q0 d0 : ℝ) : Reduced P qbar m (solE P qbar m q0 d0) (solQ P qbar q0) := by
  intro t
  have hf := eflex_succ P qbar m hm t
  have hκ := P.κ_mul
  have hη := P.η_pos.ne'
  unfold solE solQ
  unfold ρ at *
  refine ⟨by ring, ?_⟩
  rw [pow_succ, pow_succ]
  field_simp
  linear_combination hf - (1 - P.ψ * P.δ) ^ t * (q0 - qbar) * hκ

/-- O&R §9.2.3: the initial values of the explicit solution. -/
theorem sol_init (qbar : ℝ) (m : ℕ → ℝ) (q0 d0 : ℝ) :
    solQ P qbar q0 0 = q0 ∧ dev P qbar m (solE P qbar m q0 d0) (solQ P qbar q0) 0 = d0 := by
  unfold solQ dev solE
  constructor
  · simp
  · simp only [pow_zero, one_mul]
    ring

/-- O&R (14), p. 616, sharpened (new): along EVERY solution, `r^T e_T → d_0`. -/
theorem r_pow_e_tendsto (qbar : ℝ) (m e q : ℕ → ℝ) (hm : Summable fun s ↦ P.r ^ s * m s)
    (h : Reduced P qbar m e q) (hs : P.ψ * P.δ < 2) :
    Tendsto (fun T ↦ P.r ^ T * e T) atTop (𝓝 (dev P qbar m e q 0)) := by
  have h1 := eflex_no_bubble P qbar m
  have h2 : Tendsto (fun T ↦ (P.r * P.ρ) ^ T) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_abs_lt_one (P.abs_rρ_lt_one hs)
  have h3 := (h1.add (h2.mul_const (P.κ * (q 0 - qbar)))).add_const (dev P qbar m e q 0)
  simp only [zero_mul, add_zero, zero_add] at h3
  refine h3.congr fun T ↦ ?_
  have hg := P.r_pow_mul_growth_pow T
  rw [e_closed_form P qbar m e q hm h T, mul_pow]
  linear_combination -(dev P qbar m e q 0) * hg

/-- O&R (14), p. 616: the no-bubble condition `lim_{T→∞} r^T e_{t+T} = 0` (stated at `t = 0`;
see `no_bubble_shift` for every `t`). -/
def NoBubble (e : ℕ → ℝ) : Prop := Tendsto (fun T ↦ P.r ^ T * e T) atTop (𝓝 0)

/-- O&R (14): the no-bubble condition at date `t` is equivalent to the one at date `0`. -/
theorem no_bubble_shift (e : ℕ → ℝ) (t : ℕ) :
    NoBubble P e ↔ Tendsto (fun T ↦ P.r ^ T * e (t + T)) atTop (𝓝 0) := by
  unfold NoBubble
  have hrt : P.r ^ t ≠ 0 := (pow_pos P.r_pos t).ne'
  constructor
  · intro h
    have h1 := ((tendsto_add_atTop_iff_nat t).2 h).const_mul (P.r ^ t)⁻¹
    rw [mul_zero] at h1
    refine h1.congr fun T ↦ ?_
    rw [pow_add, add_comm T t]
    field_simp
  · intro h
    have h1 := (h.const_mul (P.r ^ t))
    rw [mul_zero] at h1
    refine (tendsto_add_atTop_iff_nat t).1 (h1.congr fun T ↦ ?_)
    rw [pow_add, add_comm T t]
    ring

/-- O&R (14), p. 616: stating the no-bubble condition on `e_{t+T}` (as the book does) or on
`e_{t+T} − q̄` is equivalent, since `r^T q̄ → 0`. -/
theorem no_bubble_iff_sub_const (e : ℕ → ℝ) (c : ℝ) :
    NoBubble P e ↔ Tendsto (fun T ↦ P.r ^ T * (e T - c)) atTop (𝓝 0) := by
  have hr := (tendsto_pow_atTop_nhds_zero_of_lt_one P.r_pos.le P.r_lt_one).mul_const c
  rw [zero_mul] at hr
  unfold NoBubble
  constructor
  · intro h
    have := h.sub hr
    rw [sub_zero] at this
    exact this.congr fun T ↦ by ring
  · intro h
    have := h.add hr
    rw [add_zero] at this
    exact this.congr fun T ↦ by ring

/-- O&R p. 613 and (14), T3(c)/T4 (new, exact): a solution satisfies the no-bubble condition
iff it lies on the saddle path, `d_0 = 0`. The book's selection criterion is DERIVED to pick out
exactly the saddle path. -/
theorem no_bubble_iff_dev_zero (qbar : ℝ) (m e q : ℕ → ℝ)
    (hm : Summable fun s ↦ P.r ^ s * m s) (h : Reduced P qbar m e q) (hs : P.ψ * P.δ < 2) :
    NoBubble P e ↔ dev P qbar m e q 0 = 0 := by
  have h1 := r_pow_e_tendsto P qbar m e q hm h hs
  constructor
  · intro h2
    exact tendsto_nhds_unique h1 h2
  · intro h2
    rw [h2] at h1
    exact h1

/-- O&R (18), p. 618: every no-bubble solution satisfies `e_t − e^flex_t = κ(q_t − q̄)`
at every date. -/
theorem eighteen (qbar : ℝ) (m e q : ℕ → ℝ) (hm : Summable fun s ↦ P.r ^ s * m s)
    (h : Reduced P qbar m e q) (hs : P.ψ * P.δ < 2) (hb : NoBubble P e) (t : ℕ) :
    e t - eflex P qbar m t = P.κ * (q t - qbar) := by
  have h0 := (no_bubble_iff_dev_zero P qbar m e q hm h hs).1 hb
  have := dev_closed_form P qbar m e q hm h t
  rw [h0, mul_zero] at this
  unfold dev at this
  linarith

/-- O&R (15)→(16), p. 617: the discounted sum of the real-exchange-rate gap along a solution,
`Σ_s r^s (q_{t+s} − q̄) = ((1+η)/(1+ψδη)) (q_t − q̄)`. -/
theorem tsum_r_pow_q (qbar : ℝ) (m e q : ℕ → ℝ) (h : Reduced P qbar m e q)
    (hs : P.ψ * P.δ < 2) (t : ℕ) :
    ∑' s : ℕ, P.r ^ s * (q (s + t) - qbar) =
      (1 + P.η) / (1 + P.ψ * P.δ * P.η) * (q t - qbar) := by
  have e1 : ∀ s, P.r ^ s * (q (s + t) - qbar) = (P.r * P.ρ) ^ s * (q t - qbar) := by
    intro s
    rw [q_closed_form P qbar m e q h (s + t), q_closed_form P qbar m e q h t, pow_add, mul_pow]
    ring
  simp_rw [e1]
  rw [tsum_mul_right, P.tsum_rρ_pow hs]

/-- O&R (14), p. 616: the forward solution. Every no-bubble solution satisfies
`e_t − q̄ = (1/(1+η)) Σ r^s m_{t+s} + ((1−φδ)/(1+η)) Σ r^s (q_{t+s} − q̄)`. -/
theorem forward_solution (qbar : ℝ) (m e q : ℕ → ℝ) (hm : Summable fun s ↦ P.r ^ s * m s)
    (h : Reduced P qbar m e q) (hs : P.ψ * P.δ < 2) (hb : NoBubble P e) (t : ℕ) :
    e t - qbar = 1 / (1 + P.η) * ∑' s : ℕ, P.r ^ s * m (s + t) +
      (1 - P.φ * P.δ) / (1 + P.η) * ∑' s : ℕ, P.r ^ s * (q (s + t) - qbar) := by
  have h18 := eighteen P qbar m e q hm h hs hb t
  rw [tsum_r_pow_q P qbar m e q h hs t]
  have h1 := P.one_add_η_pos.ne'
  have hc : (1 - P.φ * P.δ) / (1 + P.η) *
      ((1 + P.η) / (1 + P.ψ * P.δ * P.η) * (q t - qbar)) = P.κ * (q t - qbar) := by
    unfold κ
    rw [← mul_assoc, div_mul_div_comm, mul_comm (1 - P.φ * P.δ) (1 + P.η),
      mul_div_mul_left _ _ h1]
  unfold eflex at h18
  rw [hc]
  linear_combination h18

/-- O&R (15), p. 616: with money constant at `m̄`, every no-bubble solution satisfies
`e_t − q̄ = m̄ + ((1−φδ)/(1+η)) Σ r^s (q_{t+s} − q̄)`. -/
theorem fifteen (qbar mbar : ℝ) (e q : ℕ → ℝ) (h : Reduced P qbar (fun _ ↦ mbar) e q)
    (hs : P.ψ * P.δ < 2) (hb : NoBubble P e) (t : ℕ) :
    e t - qbar = mbar + (1 - P.φ * P.δ) / (1 + P.η) * ∑' s : ℕ, P.r ^ s * (q (s + t) - qbar) := by
  have hm : Summable fun s ↦ P.r ^ s * (fun _ ↦ mbar) s :=
    (summable_geometric_of_lt_one P.r_pos.le P.r_lt_one).mul_right mbar
  rw [forward_solution P qbar _ e q hm h hs hb t, tsum_mul_right, P.tsum_r_pow]
  field_simp [P.one_add_η_pos.ne']

/-- O&R (16), p. 617: with money constant at `m̄`, every no-bubble solution lies on the saddle
path `e_t = m̄ + q̄ + ((1−φδ)/(1+ψδη))(q_t − q̄)`. -/
theorem sixteen (qbar mbar : ℝ) (e q : ℕ → ℝ) (h : Reduced P qbar (fun _ ↦ mbar) e q)
    (hs : P.ψ * P.δ < 2) (hb : NoBubble P e) (t : ℕ) :
    e t = mbar + qbar + P.κ * (q t - qbar) := by
  have hm : Summable fun s ↦ P.r ^ s * (fun _ ↦ mbar) s :=
    (summable_geometric_of_lt_one P.r_pos.le P.r_lt_one).mul_right mbar
  have := eighteen P qbar _ e q hm h hs hb t
  rw [eflex_const] at this
  linarith

/-- O&R (19), p. 618: `e^flex_t = q̄ + p^flex_t`, where `p^flex_t = (1/(1+η)) Σ r^s m_{t+s}` is
the Cagan flexible-price price level of Ch. 8. -/
theorem eflex_eq_qbar_add_pflex (qbar : ℝ) (m : ℕ → ℝ) (t : ℕ) :
    eflex P qbar m t = qbar + (eflex P 0 m t) := by
  unfold eflex
  ring

/-- O&R (14)–(16), T4 (existence and uniqueness): for a money path with
`Σ r^s |m_s| < ∞` and `0 < ψδ < 2`, for every initial real exchange rate `q_0` there is exactly
one solution `(e, q)` of (7)–(8) satisfying the no-bubble condition. -/
theorem exists_unique_no_bubble (qbar : ℝ) (m : ℕ → ℝ) (hm : Summable fun s ↦ P.r ^ s * m s)
    (hs : P.ψ * P.δ < 2) (q0 : ℝ) :
    ∃! x : (ℕ → ℝ) × (ℕ → ℝ), x.2 0 = q0 ∧ Reduced P qbar m x.1 x.2 ∧ NoBubble P x.1 := by
  refine ⟨(solE P qbar m q0 0, solQ P qbar q0), ⟨(sol_init P qbar m q0 0).1,
    sol_reduced P qbar m hm q0 0, ?_⟩, ?_⟩
  · rw [no_bubble_iff_dev_zero P qbar m _ _ hm (sol_reduced P qbar m hm q0 0) hs]
    exact (sol_init P qbar m q0 0).2
  · rintro ⟨e, q⟩ ⟨hq0, hr, hb⟩
    have hd := (no_bubble_iff_dev_zero P qbar m e q hm hr hs).1 hb
    have hr' := sol_reduced P qbar m hm q0 0
    have hinit := sol_init P qbar m q0 0
    have hqq : q 0 = solQ P qbar q0 0 := by rw [hinit.1]; exact hq0
    have hee : e 0 = solE P qbar m q0 0 0 := by
      have h2 := hinit.2
      unfold dev at hd h2
      rw [hqq] at hd
      linarith
    obtain ⟨h1, h2⟩ := reduced_unique_of_init P qbar m e q _ _ hr hr' hee hqq
    rw [h1, h2]

/-! ## T3: the global saddle-path theorem for a constant money supply -/

/-- O&R p. 613, T3 (exact): with `m ≡ m̄`, the saddle deviation is
`d_t = e_t − (m̄ + q̄) − κ(q_t − q̄)` and every solution is
`e_t = m̄ + q̄ + κρ^t(q_0 − q̄) + ((1+η)/η)^t d_0`. -/
theorem const_money_closed_form (qbar mbar : ℝ) (e q : ℕ → ℝ)
    (h : Reduced P qbar (fun _ ↦ mbar) e q) (t : ℕ) :
    e t = mbar + qbar + P.κ * (P.ρ ^ t * (q 0 - qbar)) +
      ((1 + P.η) / P.η) ^ t * (e 0 - (mbar + qbar) - P.κ * (q 0 - qbar)) := by
  have hm : Summable fun s ↦ P.r ^ s * (fun _ ↦ mbar) s :=
    (summable_geometric_of_lt_one P.r_pos.le P.r_lt_one).mul_right mbar
  have := e_closed_form P qbar _ e q hm h t
  unfold dev at this
  rw [eflex_const, eflex_const] at this
  exact this

/-- O&R p. 613, T3(b): off the saddle path above it (`d_0 > 0`) the exchange rate explodes,
`e_t → +∞`. -/
theorem explodes_of_dev_pos (qbar mbar : ℝ) (e q : ℕ → ℝ)
    (h : Reduced P qbar (fun _ ↦ mbar) e q) (hs : P.ψ * P.δ < 2)
    (hd : 0 < e 0 - (mbar + qbar) - P.κ * (q 0 - qbar)) : Tendsto e atTop atTop := by
  have h1 := (tendsto_pow_atTop_atTop_of_one_lt P.one_lt_growth).atTop_mul_const hd
  have h2 : Tendsto (fun t ↦ mbar + qbar + P.κ * (P.ρ ^ t * (q 0 - qbar))) atTop
      (𝓝 (mbar + qbar + P.κ * (0 * (q 0 - qbar)))) :=
    (((tendsto_pow_atTop_nhds_zero_of_abs_lt_one (P.abs_ρ_lt_one hs)).mul_const _).const_mul
      _).const_add _
  have h3 := h1.atTop_add h2
  refine h3.congr fun t ↦ ?_
  rw [const_money_closed_form P qbar mbar e q h t]
  ring

/-- O&R p. 613, T3(b): off the saddle path below it (`d_0 < 0`) the exchange rate implodes,
`e_t → −∞`. -/
theorem implodes_of_dev_neg (qbar mbar : ℝ) (e q : ℕ → ℝ)
    (h : Reduced P qbar (fun _ ↦ mbar) e q) (hs : P.ψ * P.δ < 2)
    (hd : e 0 - (mbar + qbar) - P.κ * (q 0 - qbar) < 0) : Tendsto e atTop atBot := by
  have h1 := (tendsto_pow_atTop_atTop_of_one_lt P.one_lt_growth).atTop_mul_const_of_neg hd
  have h2 : Tendsto (fun t ↦ mbar + qbar + P.κ * (P.ρ ^ t * (q 0 - qbar))) atTop
      (𝓝 (mbar + qbar + P.κ * (0 * (q 0 - qbar)))) :=
    (((tendsto_pow_atTop_nhds_zero_of_abs_lt_one (P.abs_ρ_lt_one hs)).mul_const _).const_mul
      _).const_add _
  have h3 := h1.atBot_add h2
  refine h3.congr fun t ↦ ?_
  rw [const_money_closed_form P qbar mbar e q h t]
  ring

/-- O&R p. 613, T3(a): with `m ≡ m̄` and `0 < ψδ < 2`, a solution converges to the steady state
`(m̄ + q̄, q̄)` iff it starts on the saddle path (16), `e_0 = m̄ + q̄ + κ(q_0 − q̄)`. -/
theorem converges_iff_on_saddle (qbar mbar : ℝ) (e q : ℕ → ℝ)
    (h : Reduced P qbar (fun _ ↦ mbar) e q) (hs : P.ψ * P.δ < 2) :
    Tendsto e atTop (𝓝 (mbar + qbar)) ↔ e 0 = mbar + qbar + P.κ * (q 0 - qbar) := by
  constructor
  · intro hc
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact not_tendsto_nhds_of_tendsto_atBot
        (implodes_of_dev_neg P qbar mbar e q h hs (by linarith)) _ hc
    · exact not_tendsto_nhds_of_tendsto_atTop
        (explodes_of_dev_pos P qbar mbar e q h hs (by linarith)) _ hc
  · intro h0
    have h2 : Tendsto (fun t ↦ mbar + qbar + P.κ * (P.ρ ^ t * (q 0 - qbar))) atTop
        (𝓝 (mbar + qbar + P.κ * (0 * (q 0 - qbar)))) :=
      (((tendsto_pow_atTop_nhds_zero_of_abs_lt_one (P.abs_ρ_lt_one hs)).mul_const _).const_mul
        _).const_add _
    simp only [zero_mul, mul_zero, add_zero] at h2
    refine h2.congr fun t ↦ ?_
    rw [const_money_closed_form P qbar mbar e q h t, h0]
    ring

/-- O&R p. 613, T3(a'): with `m ≡ m̄`, a solution stays bounded iff it starts on the saddle
path. -/
theorem bounded_iff_on_saddle (qbar mbar : ℝ) (e q : ℕ → ℝ)
    (h : Reduced P qbar (fun _ ↦ mbar) e q) (hs : P.ψ * P.δ < 2) :
    (∃ B, ∀ t, |e t| ≤ B) ↔ e 0 = mbar + qbar + P.κ * (q 0 - qbar) := by
  constructor
  · rintro ⟨B, hB⟩
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · obtain ⟨t, ht⟩ := (tendsto_atBot.1
        (implodes_of_dev_neg P qbar mbar e q h hs (by linarith)) (-B - 1)).exists
      have := neg_abs_le (e t)
      linarith [hB t]
    · obtain ⟨t, ht⟩ := (tendsto_atTop.1
        (explodes_of_dev_pos P qbar mbar e q h hs (by linarith)) (B + 1)).exists
      have := le_abs_self (e t)
      linarith [hB t]
  · intro h0
    refine ⟨|mbar + qbar| + |P.κ| * |q 0 - qbar|, fun t ↦ ?_⟩
    have hz : e 0 - (mbar + qbar) - P.κ * (q 0 - qbar) = 0 := by rw [h0]; ring
    rw [const_money_closed_form P qbar mbar e q h t, hz, mul_zero, add_zero]
    have hρt : |P.ρ ^ t| ≤ 1 := by
      rw [abs_pow]; exact pow_le_one₀ (abs_nonneg _) (P.abs_ρ_lt_one hs).le
    calc |mbar + qbar + P.κ * (P.ρ ^ t * (q 0 - qbar))|
        ≤ |mbar + qbar| + |P.κ * (P.ρ ^ t * (q 0 - qbar))| := abs_add_le _ _
      _ = |mbar + qbar| + |P.κ| * (|P.ρ ^ t| * |q 0 - qbar|) := by rw [abs_mul, abs_mul]
      _ ≤ |mbar + qbar| + |P.κ| * (1 * |q 0 - qbar|) := by
          gcongr
      _ = |mbar + qbar| + |P.κ| * |q 0 - qbar| := by ring

/-- O&R p. 613, T3(c): with `m ≡ m̄`, a solution satisfies the no-bubble condition iff it
starts on the saddle path. -/
theorem no_bubble_iff_on_saddle (qbar mbar : ℝ) (e q : ℕ → ℝ)
    (h : Reduced P qbar (fun _ ↦ mbar) e q) (hs : P.ψ * P.δ < 2) :
    NoBubble P e ↔ e 0 = mbar + qbar + P.κ * (q 0 - qbar) := by
  have hm : Summable fun s ↦ P.r ^ s * (fun _ ↦ mbar) s :=
    (summable_geometric_of_lt_one P.r_pos.le P.r_lt_one).mul_right mbar
  rw [no_bubble_iff_dev_zero P qbar _ e q hm h hs]
  unfold dev
  rw [eflex_const]
  constructor <;> intro h0 <;> linarith

/-- O&R p. 613, T3 (the saddle-path theorem, global and exact): with `m ≡ m̄` and
`0 < ψδ < 2`, for every initial real exchange rate `q_0` there is exactly one initial nominal
exchange rate `e_0` from which the solution converges to the steady state; it is
`e_0 = m̄ + q̄ + κ(q_0 − q̄)` (16). -/
theorem saddle_path_theorem (qbar mbar : ℝ) (hs : P.ψ * P.δ < 2) (q0 : ℝ) :
    ∃! e0 : ℝ, ∃ e q : ℕ → ℝ, e 0 = e0 ∧ q 0 = q0 ∧ Reduced P qbar (fun _ ↦ mbar) e q ∧
      Tendsto e atTop (𝓝 (mbar + qbar)) := by
  have hm : Summable fun s ↦ P.r ^ s * (fun _ ↦ mbar) s :=
    (summable_geometric_of_lt_one P.r_pos.le P.r_lt_one).mul_right mbar
  refine ⟨mbar + qbar + P.κ * (q0 - qbar), ⟨solE P qbar _ q0 0, solQ P qbar q0, ?_, ?_,
    sol_reduced P qbar _ hm q0 0, ?_⟩, ?_⟩
  · unfold solE; rw [eflex_const]; simp
  · unfold solQ; simp
  · rw [converges_iff_on_saddle P qbar mbar _ _ (sol_reduced P qbar _ hm q0 0) hs]
    unfold solE solQ; rw [eflex_const]; simp
  · rintro e0 ⟨e, q, he, hq, hr, hc⟩
    rw [converges_iff_on_saddle P qbar mbar e q hr hs, he, hq] at hc
    exact hc

/-! ## T5: slopes of the schedules in Fig. 9.4 -/

/-- O&R p. 612, Fig. 9.4: with `m ≡ m̄`, `Δe_{t+1} = 0` iff `(q_t, e_t)` lies on the line
`e = m̄ + φδq̄ + (1−φδ)q` (vertical intercept `m̄ + φδq̄`, slope `1 − φδ`). -/
theorem delta_e_zero_iff (qbar mbar : ℝ) (e q : ℕ → ℝ) (h : Reduced P qbar (fun _ ↦ mbar) e q)
    (t : ℕ) : e (t + 1) = e t ↔ e t = mbar + P.φ * P.δ * qbar + (1 - P.φ * P.δ) * q t := by
  obtain ⟨-, h8⟩ := h t
  constructor
  · intro he
    rw [he, sub_self, mul_zero, zero_add] at h8
    linear_combination -h8
  · intro he
    have : P.η * (e (t + 1) - e t) = 0 := by linear_combination h8 + he
    rcases mul_eq_zero.1 this with h0 | h0
    · exact absurd h0 P.η_pos.ne'
    · linarith

/-- O&R p. 612, Fig. 9.4: with `m ≡ m̄`, `Δq_{t+1} = 0` iff `q_t = q̄` (the vertical schedule). -/
theorem delta_q_zero_iff (qbar : ℝ) (m e q : ℕ → ℝ) (h : Reduced P qbar m e q) (t : ℕ) :
    q (t + 1) = q t ↔ q t = qbar := by
  obtain ⟨h7, -⟩ := h t
  constructor
  · intro hq
    rw [hq, sub_self] at h7
    rcases mul_eq_zero.1 h7.symm with h0 | h0
    · exact absurd (neg_eq_zero.1 h0) P.ψδ_pos.ne'
    · linarith
  · intro hq
    rw [hq, sub_self, mul_zero] at h7
    linarith

/-- O&R p. 612: the `Δe = 0` schedule is upward sloping iff `φδ < 1`, and its slope is always
below 45 degrees (`1 − φδ < 1`). -/
theorem delta_e_slope_facts : (0 < 1 - P.φ * P.δ ↔ P.φ * P.δ < 1) ∧ 1 - P.φ * P.δ < 1 := by
  constructor
  · constructor <;> intro h <;> linarith
  · linarith [P.φδ_pos]

/-- O&R p. 614 ("SS is shallower than `Δe = 0`"), T5: `|κ| ≤ |1 − φδ|`, strictly unless
`φδ = 1`. -/
theorem saddle_shallower : |P.κ| ≤ |1 - P.φ * P.δ| ∧
    (P.φ * P.δ ≠ 1 → |P.κ| < |1 - P.φ * P.δ|) := by
  have hd := P.slope_denom_pos
  have h1 : 1 < 1 + P.ψ * P.δ * P.η := by have := mul_pos P.ψδ_pos P.η_pos; linarith
  have hk : |P.κ| = |1 - P.φ * P.δ| / (1 + P.ψ * P.δ * P.η) := by
    unfold κ; rw [abs_div, abs_of_pos hd]
  constructor
  · rw [hk]; exact div_le_self (abs_nonneg _) h1.le
  · intro hne
    rw [hk]
    exact div_lt_self (abs_pos.2 (sub_ne_zero.2 (Ne.symm hne))) h1

/-- O&R pp. 614–615, Figs 9.5–9.6, T5: the saddle path has the sign of `1 − φδ`: upward
sloping iff `φδ < 1`, flat iff `φδ = 1`, downward sloping iff `φδ > 1`. -/
theorem saddle_slope_sign : (0 < P.κ ↔ P.φ * P.δ < 1) ∧ (P.κ = 0 ↔ P.φ * P.δ = 1) ∧
    (P.κ < 0 ↔ 1 < P.φ * P.δ) := by
  have hd := P.slope_denom_pos
  refine ⟨?_, ?_, ?_⟩
  · unfold κ; rw [div_pos_iff_of_pos_right hd]; constructor <;> intro h <;> linarith
  · unfold κ; rw [div_eq_zero_iff]
    constructor
    · rintro (h | h)
      · linarith
      · linarith
    · intro h; left; linarith
  · unfold κ; rw [div_neg_iff]
    constructor
    · rintro (⟨h1, h2⟩ | ⟨h1, -⟩)
      · linarith
      · linarith
    · intro h; right; exact ⟨by linarith, hd⟩

end ObstfeldRogoff.NominalRigidities.DornbuschModel
