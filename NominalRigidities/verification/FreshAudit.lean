import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Order.Monotone.Defs
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Real.Sqrt
set_option autoImplicit false

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The Barro–Gordon loss function

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*,
§9.5, pp. 634–637. The policymaker's loss is `L = (y − k ȳ)² + χ π²` with target
output above the natural rate (`k > 1`).
-/

namespace ObstfeldRogoff.NominalRigidities

/-- The quadratic loss `(y − ky)² + χπ²` (O&R (9.5x), §9.5). -/
def loss (χ k ybar y π : ℝ) : ℝ := (y - k * ybar) ^ 2 + χ * π ^ 2

/-- The loss is nonnegative when `χ ≥ 0`. -/
theorem loss_nonneg {χ : ℝ} (hχ : 0 ≤ χ) (k ybar y π : ℝ) : 0 ≤ loss χ k ybar y π := by
  unfold loss
  have := sq_nonneg (y - k * ybar)
  have := mul_nonneg hχ (sq_nonneg π)
  linarith

/-- Zero inflation at target output gives zero loss (O&R §9.5). -/
theorem loss_at_target (χ k ybar : ℝ) : loss χ k ybar (k * ybar) 0 = 0 := by
  unfold loss
  ring

end ObstfeldRogoff.NominalRigidities

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

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

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

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

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

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

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

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

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The Kydland–Prescott / Barro–Gordon model of monetary credibility

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §9.5.1
(pp. 635–639), §9.5.3 (pp. 644–646) and Exercise 5 (p. 658).

Supply shocks `z` live on a finite state space `S` with probabilities `p` (`p ≥ 0`,
`Σ p = 1`) and conditional mean zero (`E z = 0`); expectations are finite sums `expect p f`.

* (26)–(31): with `y = ȳ − (w − p) − z`, `w = E p` and target `ȳ + k`, the loss is
  `L = (π − πᵉ − z − k)² + χ π²` (`loss_derivation`).
* (32)–(35), one-shot game: the loss is strictly convex in `π` (second derivative
  `2(1 + χ) > 0`), the first-order condition is necessary and sufficient, the best response
  (33) is the unique minimiser, and the rational-expectations equilibrium is **unique**:
  `πᵉ = k/χ`, `π = k/χ + z/(1 + χ)` (`oneShot_eqm_iff`).
* (36), commitment: among **all** state-contingent rules `π : S → ℝ` with `πᵉ = E π`, the
  expected loss is `V_C + χ (E π)² + (1 + χ) E(π − E π − z/(1 + χ))²`, so the rule
  `π = z/(1 + χ)` is optimal, and it is the unique optimum on the support of `p`.
  Loss rankings: `V_C = k² + χσ²/(1 + χ)`, discretion `V_D = V_C + k²/χ`, zero inflation
  `V_0 = k² + σ²`; `V_C ≤ V_0`, `V_C < V_D`, and `V_0 < V_D ↔ σ²/(1 + χ) < k²/χ`.
* §9.5.3, (45)–(48), Alesina's partisan model: unique equilibrium `πᵉ = P/χᴸ`, surprises
  `(1 − P)/χᴸ` and `−P/χᴸ`; a known winner gives no surprise.
* Exercise 5 (central bank secrecy), solved for a general finite distribution of `λ` and then
  for the book's two-point case (`E L = k`, `k − 1/2`, `k + 1` versus `k`).
-/

namespace ObstfeldRogoff.NominalRigidities.BarroGordon

open Finset

variable {S : Type*} [Fintype S]

/-! ## Finite expectations -/

/-- Expectation over a finite state space with probabilities `p` (O&R §9.5.1, the operator
`E_{t−1}` of (27), (34)). -/
def expect (p f : S → ℝ) : ℝ := ∑ s, p s * f s

/-- Linearity of `expect` in sums (O&R §9.5.1). -/
theorem expect_add (p f g : S → ℝ) :
    expect p (fun s => f s + g s) = expect p f + expect p g := by
  unfold expect
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun s _ => by ring

/-- Linearity of `expect` in differences (O&R §9.5.1). -/
theorem expect_sub (p f g : S → ℝ) :
    expect p (fun s => f s - g s) = expect p f - expect p g := by
  unfold expect
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun s _ => by ring

/-- Homogeneity of `expect` (O&R §9.5.1). -/
theorem expect_const_mul (p f : S → ℝ) (c : ℝ) :
    expect p (fun s => c * f s) = c * expect p f := by
  unfold expect
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun s _ => by ring

/-- The expectation of a constant is the constant (O&R §9.5.1). -/
theorem expect_const (p : S → ℝ) (h1 : ∑ s, p s = 1) (c : ℝ) :
    expect p (fun _ => c) = c := by
  unfold expect
  rw [← Finset.sum_mul, h1, one_mul]

/-- Monotonicity of `expect` (O&R §9.5.1). -/
theorem expect_mono (p f g : S → ℝ) (hp : ∀ s, 0 ≤ p s) (hfg : ∀ s, f s ≤ g s) :
    expect p f ≤ expect p g :=
  Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left (hfg s) (hp s)

/-- Nonnegativity of `expect` (O&R §9.5.1). -/
theorem expect_nonneg (p f : S → ℝ) (hp : ∀ s, 0 ≤ p s) (hf : ∀ s, 0 ≤ f s) :
    0 ≤ expect p f :=
  Finset.sum_nonneg fun s _ => mul_nonneg (hp s) (hf s)

/-- A nonnegative function with zero expectation vanishes on the support (O&R §9.5.1). -/
theorem expect_eq_zero_iff (p f : S → ℝ) (hp : ∀ s, 0 ≤ p s) (hf : ∀ s, 0 ≤ f s) :
    expect p f = 0 ↔ ∀ s, 0 < p s → f s = 0 := by
  unfold expect
  rw [Finset.sum_eq_zero_iff_of_nonneg fun s _ => mul_nonneg (hp s) (hf s)]
  constructor
  · intro h s hs
    have := h s (Finset.mem_univ s)
    rcases mul_eq_zero.1 this with h0 | h0
    · exact absurd h0 hs.ne'
    · exact h0
  · intro h s _
    rcases (hp s).lt_or_eq with hs | hs
    · rw [h s hs, mul_zero]
    · rw [← hs, zero_mul]

/-- Two functions that agree on the support have the same expectation (O&R §9.5.1). -/
theorem expect_congr_support (p f g : S → ℝ) (hfg : ∀ s, 0 < p s → f s = g s)
    (hp : ∀ s, 0 ≤ p s) : expect p f = expect p g := by
  unfold expect
  refine Finset.sum_congr rfl fun s _ => ?_
  rcases (hp s).lt_or_eq with hs | hs
  · rw [hfg s hs]
  · rw [← hs, zero_mul, zero_mul]

/-! ## The model, (26)–(31) -/

/-- O&R (31), p. 637: the one-period loss `(π − πᵉ − z − k)² + χπ²`. -/
def bgLoss (χ k π πe z : ℝ) : ℝ := (π - πe - z - k) ^ 2 + χ * π ^ 2

/-- O&R (26)–(31), pp. 636–637: with output `y = ȳ − (w − p) − z` (26), the wage set at the
expected price level `w = E p` (27), inflation `π = p − p₋₁` (28), expected inflation
`πᵉ = E p − p₋₁`, and target output `ȳ + k` (30), the loss (29) `(y − (ȳ + k))² + χπ²` is (31). -/
theorem loss_derivation (ybar k χ z w p pprev : ℝ) :
    ((ybar - (w - p) - z) - (ybar + k)) ^ 2 + χ * (p - pprev) ^ 2 =
      bgLoss χ k (p - pprev) (w - pprev) z := by
  unfold bgLoss
  ring

/-- O&R (33), p. 637: the policymaker's best response `(k + πᵉ + z)/(1 + χ)`. -/
noncomputable def bestResponse (χ k πe z : ℝ) : ℝ := (k + πe + z) / (1 + χ)

/-- O&R (31)–(33): completing the square, `L(π) = (1 + χ)(π − π̂)² + χ(k + πᵉ + z)²/(1 + χ)`
with `π̂` the best response (33). -/
theorem bgLoss_eq_sq (χ k π πe z : ℝ) (hχ : 0 < 1 + χ) :
    bgLoss χ k π πe z = (1 + χ) * (π - bestResponse χ k πe z) ^ 2 +
      χ * (k + πe + z) ^ 2 / (1 + χ) := by
  unfold bgLoss bestResponse
  field_simp
  ring

/-- O&R (53), p. 649: the minimised loss is `χ(k + πᵉ + z)²/(1 + χ)`. -/
theorem bgLoss_bestResponse (χ k πe z : ℝ) (hχ : 0 < 1 + χ) :
    bgLoss χ k (bestResponse χ k πe z) πe z = χ * (k + πe + z) ^ 2 / (1 + χ) := by
  rw [bgLoss_eq_sq χ k _ πe z hχ, sub_self]
  ring

/-- O&R (33): the best response is a global minimiser of the loss (31). -/
theorem bestResponse_isMin (χ k π πe z : ℝ) (hχ : 0 < 1 + χ) :
    bgLoss χ k (bestResponse χ k πe z) πe z ≤ bgLoss χ k π πe z := by
  rw [bgLoss_eq_sq χ k π πe z hχ, bgLoss_bestResponse χ k πe z hχ]
  have := mul_nonneg hχ.le (sq_nonneg (π - bestResponse χ k πe z))
  linarith

/-- O&R (33): the best response is the unique minimiser (strict convexity). -/
theorem eq_bestResponse_of_le (χ k π πe z : ℝ) (hχ : 0 < 1 + χ)
    (h : bgLoss χ k π πe z ≤ bgLoss χ k (bestResponse χ k πe z) πe z) :
    π = bestResponse χ k πe z := by
  rw [bgLoss_eq_sq χ k π πe z hχ, bgLoss_bestResponse χ k πe z hχ] at h
  have h2 : (1 + χ) * (π - bestResponse χ k πe z) ^ 2 ≤ 0 := by linarith
  have h3 : (π - bestResponse χ k πe z) ^ 2 = 0 :=
    le_antisymm (nonpos_of_mul_nonpos_right (by linarith) hχ) (sq_nonneg _)
  exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h3)

/-- O&R (32), p. 637: the derivative of the loss (31) in `π` is
`2(π − πᵉ − z − k) + 2χπ`. -/
theorem hasDerivAt_bgLoss (χ k π πe z : ℝ) :
    HasDerivAt (fun x => bgLoss χ k x πe z) (2 * (π - πe - z - k) + 2 * χ * π) π := by
  have h1 : HasDerivAt (fun x : ℝ => x - πe - z - k) 1 π :=
    ((((hasDerivAt_id π).sub_const πe).sub_const z).sub_const k)
  have h2 := h1.pow 2
  have h3 := ((hasDerivAt_id π).pow 2).const_mul χ
  have h4 := HasDerivAt.add h2 h3
  convert h4 using 1
  · ext x
    simp [bgLoss]
  · simp
    ring

/-- O&R p. 638 ("ignoring second-order conditions"): the derivative of the marginal loss is
`2(1 + χ)`, positive whenever `1 + χ > 0`. -/
theorem hasDerivAt_marginal_bgLoss (χ k π πe z : ℝ) :
    HasDerivAt (fun x => 2 * (x - πe - z - k) + 2 * χ * x) (2 * (1 + χ)) π := by
  have h1 : HasDerivAt (fun x : ℝ => x - πe - z - k) 1 π :=
    ((((hasDerivAt_id π).sub_const πe).sub_const z).sub_const k)
  have h2 := HasDerivAt.add (h1.const_mul 2) ((hasDerivAt_id π).const_mul (2 * χ))
  convert h2 using 1
  · ext x
    simp
  · ring

/-- O&R (32)–(33): the first-order condition holds exactly at the best response. -/
theorem foc_iff (χ k π πe z : ℝ) (hχ : 0 < 1 + χ) :
    2 * (π - πe - z - k) + 2 * χ * π = 0 ↔ π = bestResponse χ k πe z := by
  unfold bestResponse
  rw [eq_div_iff hχ.ne']
  constructor <;> intro h <;> linarith

/-- O&R (32): the first-order condition is necessary and sufficient for a global minimum. -/
theorem isMin_iff_foc (χ k π πe z : ℝ) (hχ : 0 < 1 + χ) :
    (∀ x, bgLoss χ k π πe z ≤ bgLoss χ k x πe z) ↔
      2 * (π - πe - z - k) + 2 * χ * π = 0 := by
  rw [foc_iff χ k π πe z hχ]
  constructor
  · intro h
    exact eq_bestResponse_of_le χ k π πe z hχ (h _)
  · rintro rfl x
    exact bestResponse_isMin χ k x πe z hχ

/-! ## The one-shot game, (34)–(35) -/

/-- O&R §9.5.1.2, pp. 637–638: a one-shot equilibrium is a state-contingent inflation choice
`π` that minimises (31) in every state given `πᵉ`, with rational expectations `πᵉ = E π`. -/
def IsOneShotEqm (p z : S → ℝ) (χ k : ℝ) (π : S → ℝ) (πe : ℝ) : Prop :=
  (∀ s x, bgLoss χ k (π s) πe (z s) ≤ bgLoss χ k x πe (z s)) ∧ πe = expect p π

/-- O&R (34)–(35), p. 638: the one-shot game has a **unique** equilibrium,
`πᵉ = k/χ` and `π = k/χ + z/(1 + χ)` in every state. -/
theorem oneShot_eqm_iff (p z : S → ℝ) (χ k : ℝ) (hχ : 0 < χ) (h1 : ∑ s, p s = 1)
    (hz : expect p z = 0) (π : S → ℝ) (πe : ℝ) :
    IsOneShotEqm p z χ k π πe ↔ πe = k / χ ∧ ∀ s, π s = k / χ + z s / (1 + χ) := by
  have hχ1 : 0 < 1 + χ := by linarith
  have hBR : ∀ e s, bestResponse χ k e (z s) = (k + e) / (1 + χ) + z s / (1 + χ) := by
    intro e s
    unfold bestResponse
    ring
  constructor
  · rintro ⟨hopt, hre⟩
    have hπ : ∀ s, π s = (k + πe) / (1 + χ) + z s / (1 + χ) := fun s =>
      (eq_bestResponse_of_le χ k (π s) πe (z s) hχ1 (hopt s _)).trans (hBR πe s)
    have hE : expect p π = (k + πe) / (1 + χ) := by
      have : expect p π = expect p (fun s => (k + πe) / (1 + χ) + z s * (1 / (1 + χ))) := by
        unfold expect
        exact Finset.sum_congr rfl fun s _ => by rw [hπ s]; ring
      rw [this, expect_add, expect_const p h1]
      have h2 : expect p (fun s => z s * (1 / (1 + χ))) = expect p z * (1 / (1 + χ)) := by
        rw [mul_comm, ← expect_const_mul]
        unfold expect
        exact Finset.sum_congr rfl fun s _ => by ring
      rw [h2, hz]
      ring
    have hpe : πe = k / χ := by
      rw [hE] at hre
      field_simp at hre ⊢
      linarith
    refine ⟨hpe, fun s => ?_⟩
    rw [hπ s, hpe]
    field_simp
    ring
  · rintro ⟨hpe, hπ⟩
    refine ⟨fun s x => ?_, ?_⟩
    · have : π s = bestResponse χ k πe (z s) := by
        rw [hπ s, hBR, hpe]
        field_simp
        ring
      rw [this]
      exact bestResponse_isMin χ k x πe (z s) hχ1
    · have : expect p π = expect p (fun s => k / χ + z s * (1 / (1 + χ))) := by
        unfold expect
        exact Finset.sum_congr rfl fun s _ => by rw [hπ s]; ring
      rw [this, expect_add, expect_const p h1]
      have h2 : expect p (fun s => z s * (1 / (1 + χ))) = expect p z * (1 / (1 + χ)) := by
        rw [mul_comm, ← expect_const_mul]
        unfold expect
        exact Finset.sum_congr rfl fun s _ => by ring
      rw [h2, hz, hpe]
      ring

/-- O&R (34), p. 638: expected inflation `k/χ` rises with the wedge `k`. -/
theorem expInfl_strictMono_k (χ : ℝ) (hχ : 0 < χ) : StrictMono fun k : ℝ => k / χ :=
  fun _ _ h => div_lt_div_of_pos_right h hχ

/-- O&R (34), p. 638: expected inflation `k/χ` falls with the weight `χ` (for `k > 0`). -/
theorem expInfl_strictAntiOn_chi (k : ℝ) (hk : 0 < k) :
    StrictAntiOn (fun χ : ℝ => k / χ) (Set.Ioi 0) :=
  fun _ ha _ _ h => div_lt_div_of_pos_left hk ha h

/-- O&R p. 638: in equilibrium the inflation surprise is `z/(1 + χ)`, and the output gap
`y − ȳ = π − πᵉ − z` is `−χz/(1 + χ)`; the authorities never systematically surprise. -/
theorem oneShot_surprise (χ k z : ℝ) (hχ : 0 < 1 + χ) :
    (k / χ + z / (1 + χ)) - k / χ = z / (1 + χ) ∧
      (k / χ + z / (1 + χ)) - k / χ - z = -(χ * z) / (1 + χ) := by
  refine ⟨by ring, ?_⟩
  field_simp
  ring

/-- O&R p. 638: with `πᵉ = 0` the marginal loss of inflation at `π = 0` is `−2(z + k)`, so for
`z = 0` and `k > 0` zero inflation is not a best response (the intuition for (34)). -/
theorem zero_not_bestResponse (χ k : ℝ) (hk : 0 < k) (hχ : 0 < 1 + χ) :
    ¬ ∀ x, bgLoss χ k 0 0 0 ≤ bgLoss χ k x 0 0 := by
  rw [isMin_iff_foc χ k 0 0 0 hχ]
  intro h
  linarith

/-! ## Commitment, (36) -/

/-- O&R (36), p. 639: expected social loss of a state-contingent rule `π` when expectations are
rational, `πᵉ = E π`. -/
def expLoss (p z : S → ℝ) (χ k : ℝ) (π : S → ℝ) : ℝ :=
  expect p (fun s => bgLoss χ k (π s) (expect p π) (z s))

/-- O&R (36), p. 639: the commitment value `V_C = k² + χσ²/(1 + χ)`. -/
noncomputable def valueCommit (χ k σ2 : ℝ) : ℝ := k ^ 2 + χ * σ2 / (1 + χ)

/-- O&R (35), p. 638: the discretionary value `V_D = k² + k²/χ + χσ²/(1 + χ)`. -/
noncomputable def valueDiscretion (χ k σ2 : ℝ) : ℝ := k ^ 2 + k ^ 2 / χ + χ * σ2 / (1 + χ)

/-- O&R p. 639: the zero-inflation-rule value `V_0 = k² + σ²`. -/
def valueZero (k σ2 : ℝ) : ℝ := k ^ 2 + σ2

/-- O&R (36): the variance of the supply shock, `σ² = E z²` (as `E z = 0`). -/
def varZ (p z : S → ℝ) : ℝ := expect p (fun s => z s ^ 2)

/-- O&R (36), pp. 639–640: the expected loss of any rule decomposes as
`k² + χ(Eπ)² + E(π − Eπ − z)² + χE(π − Eπ)²` (the cross terms vanish by `E z = 0`). -/
theorem expLoss_decomp (p z : S → ℝ) (χ k : ℝ) (h1 : ∑ s, p s = 1) (hz : expect p z = 0)
    (π : S → ℝ) :
    expLoss p z χ k π = k ^ 2 + χ * expect p π ^ 2 +
      expect p (fun s => (π s - expect p π - z s) ^ 2) +
      χ * expect p (fun s => (π s - expect p π) ^ 2) := by
  set a := expect p π with ha
  have key : expLoss p z χ k π = expect p (fun s =>
      ((k ^ 2 + χ * a ^ 2) + ((π s - a - z s) ^ 2 + χ * (π s - a) ^ 2)) +
        ((2 * χ * a - 2 * k) * π s + (-(2 * χ * a - 2 * k) * a) + 2 * k * z s)) := by
    unfold expLoss
    rw [← ha]
    unfold expect bgLoss
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [key]
  simp only [expect_add, expect_const_mul, expect_const p h1]
  rw [hz, ← ha]
  ring

/-- O&R (36): `(g − z)² + χg² = (1 + χ)(g − z/(1 + χ))² + χz²/(1 + χ)`. -/
theorem sq_split (χ g z : ℝ) (hχ : 0 < 1 + χ) :
    (g - z) ^ 2 + χ * g ^ 2 = (1 + χ) * (g - z / (1 + χ)) ^ 2 + χ * z ^ 2 / (1 + χ) := by
  field_simp
  ring

/-- O&R (36), p. 639: the exact excess loss of an arbitrary rule over commitment,
`E L = V_C + χ(Eπ)² + (1 + χ)E(π − Eπ − z/(1 + χ))²`. -/
theorem expLoss_eq_commit_add (p z : S → ℝ) (χ k : ℝ) (hχ : 0 < 1 + χ) (h1 : ∑ s, p s = 1)
    (hz : expect p z = 0) (π : S → ℝ) :
    expLoss p z χ k π = valueCommit χ k (varZ p z) + χ * expect p π ^ 2 +
      (1 + χ) * expect p (fun s => (π s - expect p π - z s / (1 + χ)) ^ 2) := by
  rw [expLoss_decomp p z χ k h1 hz π]
  have : expect p (fun s => (π s - expect p π - z s) ^ 2) +
      χ * expect p (fun s => (π s - expect p π) ^ 2) =
      (1 + χ) * expect p (fun s => (π s - expect p π - z s / (1 + χ)) ^ 2) +
        χ / (1 + χ) * varZ p z := by
    unfold varZ
    rw [← expect_const_mul, ← expect_const_mul, ← expect_const_mul, ← expect_add, ← expect_add]
    congr 1
    funext s
    rw [sq_split χ (π s - expect p π) (z s) hχ]
    ring
  unfold valueCommit
  rw [add_assoc (k ^ 2 + χ * expect p π ^ 2), this]
  field_simp
  ring

/-- O&R (36): the commitment rule `π = z/(1 + χ)`. -/
noncomputable def commitRule (χ : ℝ) (z : S → ℝ) : S → ℝ := fun s => z s / (1 + χ)

/-- O&R (36): the commitment rule has mean zero. -/
theorem expect_commitRule (p z : S → ℝ) (χ : ℝ) (hz : expect p z = 0) :
    expect p (commitRule χ z) = 0 := by
  have : expect p (commitRule χ z) = expect p (fun s => (1 / (1 + χ)) * z s) := by
    unfold expect commitRule
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [this, expect_const_mul, hz, mul_zero]

/-- O&R (36): the commitment rule attains `V_C = k² + χσ²/(1 + χ)`. -/
theorem expLoss_commitRule (p z : S → ℝ) (χ k : ℝ) (hχ : 0 < 1 + χ) (h1 : ∑ s, p s = 1)
    (hz : expect p z = 0) :
    expLoss p z χ k (commitRule χ z) = valueCommit χ k (varZ p z) := by
  rw [expLoss_eq_commit_add p z χ k hχ h1 hz, expect_commitRule p z χ hz]
  have : expect p (fun s => (commitRule χ z s - 0 - z s / (1 + χ)) ^ 2) = 0 := by
    unfold expect commitRule
    simp
  rw [this]
  ring

/-- O&R (36), p. 639: the commitment rule minimises `E L` among **all** rules `π : S → ℝ`
subject to `πᵉ = E π` (`χ ≥ 0`). -/
theorem commitRule_optimal (p z : S → ℝ) (χ k : ℝ) (hχ : 0 ≤ χ) (hp : ∀ s, 0 ≤ p s)
    (h1 : ∑ s, p s = 1) (hz : expect p z = 0) (π : S → ℝ) :
    expLoss p z χ k (commitRule χ z) ≤ expLoss p z χ k π := by
  have hχ1 : 0 < 1 + χ := by linarith
  rw [expLoss_commitRule p z χ k hχ1 h1 hz, expLoss_eq_commit_add p z χ k hχ1 h1 hz]
  have h2 := expect_nonneg p (fun s => (π s - expect p π - z s / (1 + χ)) ^ 2) hp
    fun s => sq_nonneg _
  have h3 := mul_nonneg hχ (sq_nonneg (expect p π))
  have h4 := mul_nonneg hχ1.le h2
  linarith

/-- O&R (36): the commitment optimum is unique on the support of the shock distribution:
`E L(π) = V_C` iff `π = z/(1 + χ)` in every state of positive probability (`χ > 0`). -/
theorem commitRule_unique (p z : S → ℝ) (χ k : ℝ) (hχ : 0 < χ) (hp : ∀ s, 0 ≤ p s)
    (h1 : ∑ s, p s = 1) (hz : expect p z = 0) (π : S → ℝ) :
    expLoss p z χ k π = valueCommit χ k (varZ p z) ↔
      ∀ s, 0 < p s → π s = z s / (1 + χ) := by
  have hχ1 : 0 < 1 + χ := by linarith
  rw [expLoss_eq_commit_add p z χ k hχ1 h1 hz]
  set f := fun s => (π s - expect p π - z s / (1 + χ)) ^ 2
  have h2 := expect_nonneg p f hp fun s => sq_nonneg _
  have h3 := mul_nonneg hχ.le (sq_nonneg (expect p π))
  constructor
  · intro h
    have hA : χ * expect p π ^ 2 = 0 := by nlinarith
    have hB : expect p f = 0 := by nlinarith
    have ha : expect p π = 0 := by
      rcases mul_eq_zero.1 hA with h0 | h0
      · exact absurd h0 hχ.ne'
      · exact pow_eq_zero_iff two_ne_zero |>.1 h0
    intro s hs
    have := (expect_eq_zero_iff p f hp fun s => sq_nonneg _).1 hB s hs
    simp only [f, ha, sub_zero] at this
    exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 this)
  · intro h
    have hπ : expect p π = expect p (commitRule χ z) :=
      expect_congr_support p π (commitRule χ z) (fun s hs => h s hs) hp
    rw [expect_commitRule p z χ hz] at hπ
    have hB : expect p f = 0 := by
      refine (expect_eq_zero_iff p f hp fun s => sq_nonneg _).2 fun s hs => ?_
      simp only [f, hπ, h s hs]
      ring
    rw [hπ, hB]
    ring

/-- O&R (35): the discretionary equilibrium policy, as a rule. -/
noncomputable def discretionRule (χ k : ℝ) (z : S → ℝ) : S → ℝ := fun s => k / χ + z s / (1 + χ)

/-- O&R (35): the discretionary equilibrium has expected social loss
`V_D = k² + k²/χ + χσ²/(1 + χ)`. -/
theorem expLoss_discretion (p z : S → ℝ) (χ k : ℝ) (hχ : 0 < χ) (h1 : ∑ s, p s = 1)
    (hz : expect p z = 0) :
    expLoss p z χ k (discretionRule χ k z) = valueDiscretion χ k (varZ p z) := by
  have hχ1 : 0 < 1 + χ := by linarith
  have hE : expect p (discretionRule χ k z) = k / χ := by
    have : expect p (discretionRule χ k z) =
        expect p (fun s => k / χ + (1 / (1 + χ)) * z s) := by
      unfold expect discretionRule
      exact Finset.sum_congr rfl fun s _ => by ring
    rw [this, expect_add, expect_const p h1, expect_const_mul, hz, mul_zero, add_zero]
  rw [expLoss_eq_commit_add p z χ k hχ1 h1 hz, hE]
  have : expect p (fun s => (discretionRule χ k z s - k / χ - z s / (1 + χ)) ^ 2) = 0 := by
    unfold expect discretionRule
    simp
  rw [this]
  unfold valueCommit valueDiscretion
  field_simp
  ring

/-- O&R p. 639: the zero-inflation rule has expected loss `V_0 = k² + σ²`. -/
theorem expLoss_zero (p z : S → ℝ) (χ k : ℝ) (h1 : ∑ s, p s = 1) (hz : expect p z = 0) :
    expLoss p z χ k (fun _ => 0) = valueZero k (varZ p z) := by
  rw [expLoss_decomp p z χ k h1 hz, expect_const p h1]
  unfold valueZero varZ expect
  simp only [sub_zero, zero_sub, even_two, Even.neg_pow, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, mul_zero, add_zero, Finset.sum_const_zero]

/-- O&R p. 639: commitment beats the zero-inflation rule, `V_0 − V_C = σ²/(1 + χ) ≥ 0`. -/
theorem valueZero_sub_valueCommit (χ k σ2 : ℝ) (hχ : 0 < 1 + χ) :
    valueZero k σ2 - valueCommit χ k σ2 = σ2 / (1 + χ) := by
  unfold valueZero valueCommit
  field_simp
  ring

/-- O&R (35)–(36): discretion costs exactly `k²/χ` more than commitment. -/
theorem valueDiscretion_sub_valueCommit (χ k σ2 : ℝ) :
    valueDiscretion χ k σ2 - valueCommit χ k σ2 = k ^ 2 / χ := by
  unfold valueDiscretion valueCommit
  ring

/-- O&R p. 639: `V_C < V_D` whenever there is an inflation bias (`k ≠ 0`, `χ > 0`). -/
theorem valueCommit_lt_valueDiscretion (χ k σ2 : ℝ) (hχ : 0 < χ) (hk : k ≠ 0) :
    valueCommit χ k σ2 < valueDiscretion χ k σ2 := by
  have := valueDiscretion_sub_valueCommit χ k σ2
  have : 0 < k ^ 2 / χ := div_pos (by positivity) hχ
  linarith

/-- O&R p. 639: the zero-inflation rule beats discretion iff `σ²/(1 + χ) < k²/χ`. -/
theorem valueZero_lt_valueDiscretion_iff (χ k σ2 : ℝ) (hχ : 0 < 1 + χ) :
    valueZero k σ2 < valueDiscretion χ k σ2 ↔ σ2 / (1 + χ) < k ^ 2 / χ := by
  have h1 := valueZero_sub_valueCommit χ k σ2 hχ
  have h2 := valueDiscretion_sub_valueCommit χ k σ2
  constructor <;> intro h <;> linarith

/-- O&R p. 637 (time inconsistency): if wage setters believe `πᵉ = 0`, the ex post optimum is
`(k + z)/(1 + χ)`, which differs from the commitment rule `z/(1 + χ)` whenever `k ≠ 0`; the
announced rule strictly loses ex post. -/
theorem commitRule_time_inconsistent (χ k z : ℝ) (hχ : 0 < 1 + χ) (hk : k ≠ 0) :
    bestResponse χ k 0 z ≠ z / (1 + χ) ∧
      bgLoss χ k (bestResponse χ k 0 z) 0 z < bgLoss χ k (z / (1 + χ)) 0 z := by
  have hne : bestResponse χ k 0 z ≠ z / (1 + χ) := by
    unfold bestResponse
    intro h
    rw [div_left_inj' hχ.ne'] at h
    exact hk (by linarith)
  refine ⟨hne, ?_⟩
  rcases (bestResponse_isMin χ k (z / (1 + χ)) 0 z hχ).lt_or_eq with h | h
  · exact h
  · exact absurd (eq_bestResponse_of_le χ k _ 0 z hχ h.ge) hne.symm

/-! ## Partisan political business cycles, §9.5.3, (45)–(48) -/

/-- O&R (45), p. 645: the liberal policymaker's loss `−(π − πᵉ − k) + (χᴸ/2)π²`. -/
noncomputable def liberalLoss (χL k π πe : ℝ) : ℝ := -(π - πe - k) + χL / 2 * π ^ 2

/-- O&R (45): completing the square around `1/χᴸ`. -/
theorem liberalLoss_eq (χL k π πe : ℝ) (hχ : 0 < χL) :
    liberalLoss χL k π πe = liberalLoss χL k (1 / χL) πe + χL / 2 * (π - 1 / χL) ^ 2 := by
  unfold liberalLoss
  field_simp
  ring

/-- O&R (47), p. 645: `1/χᴸ` is the liberals' unique best response, whatever `πᵉ`. -/
theorem liberal_isMin_iff (χL k π πe : ℝ) (hχ : 0 < χL) :
    (∀ x, liberalLoss χL k π πe ≤ liberalLoss χL k x πe) ↔ π = 1 / χL := by
  constructor
  · intro h
    have h2 := h (1 / χL)
    rw [liberalLoss_eq χL k π πe hχ] at h2
    have h3 : χL / 2 * (π - 1 / χL) ^ 2 ≤ 0 := by linarith
    have h4 : (π - 1 / χL) ^ 2 = 0 :=
      le_antisymm (nonpos_of_mul_nonpos_right h3 (by positivity)) (sq_nonneg _)
    exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h4)
  · rintro rfl x
    rw [liberalLoss_eq χL k x πe hχ]
    have : 0 ≤ χL / 2 * (x - 1 / χL) ^ 2 := by positivity
    linarith

/-- O&R (46), p. 645: the conservatives' loss `π²` has the unique minimiser `0`. -/
theorem conservative_isMin_iff (π : ℝ) : (∀ x : ℝ, π ^ 2 ≤ x ^ 2) ↔ π = 0 := by
  constructor
  · intro h
    have := h 0
    exact pow_eq_zero_iff two_ne_zero |>.1 (le_antisymm (by simpa using this) (sq_nonneg _))
  · rintro rfl x
    simp [sq_nonneg]

/-- O&R (47)–(48), p. 645: the election equilibrium with liberal win probability `P`: each
party plays its best response and expectations are rational, `πᵉ = Pπᴸ + (1 − P)πᶜ`. -/
def IsPartisanEqm (P χL k πL πC πe : ℝ) : Prop :=
  (∀ x, liberalLoss χL k πL πe ≤ liberalLoss χL k x πe) ∧ (∀ x : ℝ, πC ^ 2 ≤ x ^ 2) ∧
    πe = P * πL + (1 - P) * πC

/-- O&R (47)–(48): the election equilibrium is unique: `πᴸ = 1/χᴸ`, `πᶜ = 0`, `πᵉ = P/χᴸ`. -/
theorem partisan_eqm_iff (P χL k πL πC πe : ℝ) (hχ : 0 < χL) :
    IsPartisanEqm P χL k πL πC πe ↔ πL = 1 / χL ∧ πC = 0 ∧ πe = P / χL := by
  unfold IsPartisanEqm
  rw [liberal_isMin_iff χL k πL πe hχ, conservative_isMin_iff]
  constructor
  · rintro ⟨rfl, rfl, rfl⟩
    exact ⟨rfl, rfl, by ring⟩
  · rintro ⟨rfl, rfl, rfl⟩
    exact ⟨rfl, rfl, by ring⟩

/-- O&R (48), p. 645: with win probability `1/2`, `πᵉ = 1/(2χᴸ)`. -/
theorem partisan_half (χL : ℝ) : (1 / 2 : ℝ) / χL = 1 / (2 * χL) := by
  rw [div_div]

/-- O&R p. 645: the output surprise `π − πᵉ` is `(1 − P)/χᴸ > 0` if liberals win and
`−P/χᴸ < 0` if conservatives win; it is zero on average. -/
theorem partisan_surprises (P χL : ℝ) :
    1 / χL - P / χL = (1 - P) / χL ∧ 0 - P / χL = -(P / χL) ∧
      P * (1 / χL - P / χL) + (1 - P) * (0 - P / χL) = 0 := by
  refine ⟨by ring, by ring, by ring⟩

/-- O&R p. 645: when the winner is known in advance (`P = 1` or `P = 0`) there is no
surprise, so output is at its natural rate under either party. -/
theorem partisan_known_winner (χL : ℝ) :
    1 / χL - (1 : ℝ) / χL = 0 ∧ (0 : ℝ) - 0 / χL = 0 := by
  constructor <;> ring

/-- O&R p. 645: with an uncertain election (`0 < P < 1`) both surprises are nonzero, with
signs: a liberal win raises output, a conservative win lowers it. -/
theorem partisan_surprise_signs (P χL : ℝ) (hχ : 0 < χL) (hP0 : 0 < P) (hP1 : P < 1) :
    0 < (1 - P) / χL ∧ -(P / χL) < 0 :=
  ⟨div_pos (by linarith) hχ, neg_neg_of_pos (div_pos hP0 hχ)⟩

/-! ## Exercise 5: central bank secrecy -/

/-- O&R Exercise 5, p. 658: the loss `−λ(π − πᵉ − k) + π²/2`. -/
noncomputable def secrecyLoss (k lam π πe : ℝ) : ℝ := -lam * (π - πe - k) + π ^ 2 / 2

/-- O&R Ex. 5: completing the square, `L(π) = L(λ) + (π − λ)²/2`. -/
theorem secrecyLoss_eq (k lam π πe : ℝ) :
    secrecyLoss k lam π πe = secrecyLoss k lam lam πe + (π - lam) ^ 2 / 2 := by
  unfold secrecyLoss
  ring

/-- O&R Ex. 5: `λ` is the unique best response, whatever `πᵉ`. -/
theorem secrecy_isMin_iff (k lam π πe : ℝ) :
    (∀ x, secrecyLoss k lam π πe ≤ secrecyLoss k lam x πe) ↔ π = lam := by
  constructor
  · intro h
    have h2 := h lam
    rw [secrecyLoss_eq k lam π πe] at h2
    have h4 : (π - lam) ^ 2 = 0 := le_antisymm (by linarith) (sq_nonneg _)
    exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h4)
  · rintro rfl x
    rw [secrecyLoss_eq k π x πe]
    have := sq_nonneg (x - π)
    linarith

/-- O&R Ex. 5(a): the one-shot equilibrium with random `λ` observed by the bank only. -/
def IsSecrecyEqm (p lam : S → ℝ) (k : ℝ) (π : S → ℝ) (πe : ℝ) : Prop :=
  (∀ s x, secrecyLoss k (lam s) (π s) πe ≤ secrecyLoss k (lam s) x πe) ∧ πe = expect p π

/-- O&R Ex. 5(a): the equilibrium is unique: `π = λ` and `πᵉ = E λ`. -/
theorem secrecy_eqm_iff (p lam : S → ℝ) (k : ℝ) (π : S → ℝ) (πe : ℝ) :
    IsSecrecyEqm p lam k π πe ↔ (∀ s, π s = lam s) ∧ πe = expect p lam := by
  unfold IsSecrecyEqm
  simp only [secrecy_isMin_iff]
  constructor
  · rintro ⟨h, rfl⟩
    exact ⟨h, by rw [show π = lam from funext h]⟩
  · rintro ⟨h, rfl⟩
    exact ⟨h, by rw [show π = lam from funext h]⟩

/-- O&R Ex. 5(a): equilibrium expected loss `k m + m²/2 − Var λ/2` where `m = E λ`,
`Var λ = E λ² − m²`. -/
theorem secrecy_eqm_loss (p lam : S → ℝ) (k : ℝ) :
    expect p (fun s => secrecyLoss k (lam s) (lam s) (expect p lam)) =
      k * expect p lam + expect p lam ^ 2 / 2 -
        (expect p (fun s => lam s ^ 2) - expect p lam ^ 2) / 2 := by
  have : expect p (fun s => secrecyLoss k (lam s) (lam s) (expect p lam)) =
      expect p (fun s => (-(1 / 2 : ℝ)) * lam s ^ 2 + (expect p lam + k) * lam s) := by
    unfold expect secrecyLoss
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [this, expect_add, expect_const_mul, expect_const_mul]
  ring

/-- O&R Ex. 5(b): with `πᵉ = 0` imposed (`E π = 0`), the expected loss of a committed rule is
`k m − Var λ/2 + E(π − (λ − m))²/2`. -/
theorem secrecy_commit_loss (p lam : S → ℝ) (k : ℝ) (h1 : ∑ s, p s = 1) (π : S → ℝ)
    (hπ : expect p π = 0) :
    expect p (fun s => secrecyLoss k (lam s) (π s) 0) =
      k * expect p lam - (expect p (fun s => lam s ^ 2) - expect p lam ^ 2) / 2 +
        expect p (fun s => (π s - (lam s - expect p lam)) ^ 2) / 2 := by
  set m := expect p lam with hm
  have e1 : expect p (fun s => secrecyLoss k (lam s) (π s) 0) =
      expect p (fun s => k * lam s + (-1 : ℝ) * (lam s * π s) + (1 / 2 : ℝ) * π s ^ 2) := by
    unfold expect secrecyLoss
    exact Finset.sum_congr rfl fun s _ => by ring
  have e2 : expect p (fun s => (π s - (lam s - m)) ^ 2) =
      expect p (fun s => π s ^ 2 + (-2 : ℝ) * (lam s * π s) + (2 * m) * π s +
        (lam s ^ 2 + (-2 * m) * lam s + m ^ 2)) := by
    unfold expect
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [e1, e2]
  simp only [expect_add, expect_const_mul, expect_const p h1]
  rw [hπ, ← hm]
  ring

/-- O&R Ex. 5(b): the optimal committed rule with `πᵉ = 0` is `π = λ − E λ`, with loss
`k m − Var λ/2`; it is unique on the support. -/
theorem secrecy_commit_optimal (p lam : S → ℝ) (k : ℝ) (hp : ∀ s, 0 ≤ p s)
    (h1 : ∑ s, p s = 1) (π : S → ℝ) (hπ : expect p π = 0) :
    k * expect p lam - (expect p (fun s => lam s ^ 2) - expect p lam ^ 2) / 2 ≤
        expect p (fun s => secrecyLoss k (lam s) (π s) 0) ∧
      (expect p (fun s => secrecyLoss k (lam s) (π s) 0) =
          k * expect p lam - (expect p (fun s => lam s ^ 2) - expect p lam ^ 2) / 2 ↔
        ∀ s, 0 < p s → π s = lam s - expect p lam) := by
  rw [secrecy_commit_loss p lam k h1 π hπ]
  have hn := expect_nonneg p (fun s => (π s - (lam s - expect p lam)) ^ 2) hp
    fun s => sq_nonneg _
  refine ⟨by linarith, ?_⟩
  constructor
  · intro h
    have h0 : expect p (fun s => (π s - (lam s - expect p lam)) ^ 2) = 0 := by linarith
    intro s hs
    have := (expect_eq_zero_iff p _ hp fun s => sq_nonneg _).1 h0 s hs
    exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 this)
  · intro h
    have h0 : expect p (fun s => (π s - (lam s - expect p lam)) ^ 2) = 0 :=
      (expect_eq_zero_iff p _ hp fun s => sq_nonneg _).2 fun s hs => by rw [h s hs]; ring
    rw [h0]
    ring

/-- O&R Ex. 5(b): the rule `λ − E λ` does satisfy the constraint `E π = 0`. -/
theorem secrecy_commit_rule_mean (p lam : S → ℝ) (h1 : ∑ s, p s = 1) :
    expect p (fun s => lam s - expect p lam) = 0 := by
  rw [expect_sub, expect_const p h1, sub_self]

/-- O&R Ex. 5(b): the constraint `πᵉ = 0` does not bind: for **any** rule with rational
`πᵉ = E π`, the expected loss is at least `k m − Var λ/2`. -/
theorem secrecy_unconstrained_bound (p lam : S → ℝ) (k : ℝ) (hp : ∀ s, 0 ≤ p s)
    (h1 : ∑ s, p s = 1) (π : S → ℝ) :
    k * expect p lam - (expect p (fun s => lam s ^ 2) - expect p lam ^ 2) / 2 ≤
      expect p (fun s => secrecyLoss k (lam s) (π s) (expect p π)) := by
  set m := expect p lam with hm
  set a := expect p π with ha
  have e1 : expect p (fun s => secrecyLoss k (lam s) (π s) a) =
      expect p (fun s => (a + k) * lam s + (-1 : ℝ) * (lam s * π s) +
        (1 / 2 : ℝ) * π s ^ 2) := by
    unfold expect secrecyLoss
    exact Finset.sum_congr rfl fun s _ => by ring
  have e2 : expect p (fun s => ((π s - a) - (lam s - m)) ^ 2) =
      expect p (fun s => π s ^ 2 + (-2 : ℝ) * (lam s * π s) + (2 * m - 2 * a) * π s +
        (lam s ^ 2 + (2 * a - 2 * m) * lam s + (a - m) ^ 2)) := by
    unfold expect
    exact Finset.sum_congr rfl fun s _ => by ring
  have hn := expect_nonneg p (fun s => ((π s - a) - (lam s - m)) ^ 2) hp fun s => sq_nonneg _
  rw [e2] at hn
  rw [e1]
  simp only [expect_add, expect_const_mul, expect_const p h1] at hn ⊢
  rw [← hm] at hn ⊢
  nlinarith [sq_nonneg a]

/-- O&R Ex. 5(c): if `λ` is revealed before `πᵉ` is set, the equilibrium in each state has
`πᵉ = π = λ`. -/
def IsRevealEqm (lam : S → ℝ) (k : ℝ) (π πe : S → ℝ) : Prop :=
  ∀ s, (∀ x, secrecyLoss k (lam s) (π s) (πe s) ≤ secrecyLoss k (lam s) x (πe s)) ∧
    πe s = π s

omit [Fintype S] in
/-- O&R Ex. 5(c): the revealing equilibrium is unique: `π = πᵉ = λ`. -/
theorem reveal_eqm_iff (lam : S → ℝ) (k : ℝ) (π πe : S → ℝ) :
    IsRevealEqm lam k π πe ↔ ∀ s, π s = lam s ∧ πe s = lam s := by
  unfold IsRevealEqm
  simp only [secrecy_isMin_iff]
  constructor
  · intro h s
    exact ⟨(h s).1, (h s).2.trans (h s).1⟩
  · intro h s
    exact ⟨(h s).1, (h s).2.trans (h s).1.symm⟩

/-- O&R Ex. 5(c): the ex ante (`t − 2`) loss is `k m + E λ²/2` under revelation, and
secrecy is better by exactly `Var λ = E λ² − m² ≥ 0`. -/
theorem reveal_vs_secrecy (p lam : S → ℝ) (k : ℝ) (hp : ∀ s, 0 ≤ p s) (h1 : ∑ s, p s = 1) :
    expect p (fun s => secrecyLoss k (lam s) (lam s) (lam s)) =
        k * expect p lam + expect p (fun s => lam s ^ 2) / 2 ∧
      expect p (fun s => secrecyLoss k (lam s) (lam s) (lam s)) -
          expect p (fun s => secrecyLoss k (lam s) (lam s) (expect p lam)) =
        expect p (fun s => lam s ^ 2) - expect p lam ^ 2 ∧
      0 ≤ expect p (fun s => lam s ^ 2) - expect p lam ^ 2 := by
  have e1 : expect p (fun s => secrecyLoss k (lam s) (lam s) (lam s)) =
      expect p (fun s => k * lam s + (1 / 2 : ℝ) * lam s ^ 2) := by
    unfold expect secrecyLoss
    exact Finset.sum_congr rfl fun s _ => by ring
  have hv : expect p (fun s => lam s ^ 2) - expect p lam ^ 2 =
      expect p (fun s => (lam s - expect p lam) ^ 2) := by
    have : expect p (fun s => (lam s - expect p lam) ^ 2) = expect p (fun s =>
        lam s ^ 2 + (-2 * expect p lam) * lam s + expect p lam ^ 2) := by
      unfold expect
      exact Finset.sum_congr rfl fun s _ => by ring
    rw [this, expect_add, expect_add, expect_const_mul, expect_const p h1]
    ring
  have e2 := secrecy_eqm_loss p lam k
  rw [e1, expect_add, expect_const_mul, expect_const_mul] at *
  refine ⟨by ring, by rw [e2]; ring, ?_⟩
  rw [hv]
  exact expect_nonneg p _ hp fun s => sq_nonneg _

/-- O&R Ex. 5, the book's case: `λ ∈ {0, 2}` with probability `1/2` each (indexed by `Bool`). -/
def lamTwo : Bool → ℝ := fun b => if b then 2 else 0

/-- O&R Ex. 5: the uniform distribution on the two states. -/
noncomputable def pHalf : Bool → ℝ := fun _ => 1 / 2

/-- O&R Ex. 5: `pHalf` sums to one. -/
theorem pHalf_sum : ∑ b, pHalf b = 1 := by
  simp [pHalf]

/-- O&R Ex. 5(a)–(c), the book's numbers: `E λ = 1`, `E λ² = 2`, so the one-shot loss is `k`,
the best committed rule (`π = λ − 1`) gives `k − 1/2`, revelation gives `k + 1`. -/
theorem secrecy_two_point (k : ℝ) :
    expect pHalf lamTwo = 1 ∧ expect pHalf (fun b => lamTwo b ^ 2) = 2 ∧
      expect pHalf (fun b => secrecyLoss k (lamTwo b) (lamTwo b) (expect pHalf lamTwo)) = k ∧
      expect pHalf (fun b => secrecyLoss k (lamTwo b) (lamTwo b - 1) 0) = k - 1 / 2 ∧
      expect pHalf (fun b => secrecyLoss k (lamTwo b) (lamTwo b) (lamTwo b)) = k + 1 := by
  have hm : expect pHalf lamTwo = 1 := by
    simp [expect, pHalf, lamTwo]
  refine ⟨hm, ?_, ?_, ?_, ?_⟩
  · simp [expect, pHalf, lamTwo]
    norm_num
  · rw [hm]
    simp [expect, pHalf, lamTwo, secrecyLoss]
    ring
  · simp [expect, pHalf, lamTwo, secrecyLoss]
    ring
  · simp [expect, pHalf, lamTwo, secrecyLoss]
    ring

end ObstfeldRogoff.NominalRigidities.BarroGordon

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Reputational equilibria in the Barro–Gordon model

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §9.5.1.4
(pp. 639–641), eqs. (37)–(39) and footnotes 28–29.

The repeated game is modelled on **histories**. A history is the list (newest first) of past
triples `(π, πᵉ, s)` (inflation, expected inflation, shock state). Shocks are iid on a finite
state space `S` with probabilities `p` and `E z = 0`; the deterministic game of (38) is the
case `S = Unit`, `z = 0`. Private expectations are a function `ε` of the history; the
central bank's strategy `σ h s` chooses inflation after seeing the history and the current
shock. The expected present value (37) of the loss from a history `h` is the limit of the
`N`-period expected costs `truncCost N h`, defined recursively over the event tree, which
are nondecreasing in `N` (losses are nonnegative), so every strategy either has a finite
expected present value or an infinite one (`truncCost_tendsto_or_atTop`).

An equilibrium (`IsReputationEqm`) requires rational expectations at **every** history and
optimality of `σ` against **every** alternative strategy at **every** history.

* A general verification theorem: a bounded `W` satisfying the Bellman equality for `σ` and
  the Bellman inequality for all actions is the value of `σ` and a lower bound for every
  strategy (`truncCost_lower`, `tendsto_truncCost_of_bellman_eq`).
* (38)/(39) trigger strategies with an arbitrary target `π̄` (T16–T18): the trigger
  equilibrium exists **iff** `(k − χπ̄)²/(1 + χ) ≤ β/(1 − β)·(k²/χ − χπ̄²)`
  (`trigger_eqm_iff`), i.e. iff `π̄ ∈ [π̲(β), k/χ]` with
  `π̲(β) = k(χ − β(1 + 2χ))/(χ(χ + β))` (`trigger_eqm_iff_bounds`). Zero inflation (with the
  commitment rule `z/(1 + χ)` on the path under shocks) is sustainable iff
  `β ≥ χ/(1 + 2χ)` (`trigger_zero_iff`, `trigger_deterministic_iff` for (38)); negative
  rates iff `β > χ/(1 + 2χ)`; `π̲(β) → −k/χ` as `β → 1`; the one-shot outcome is always an
  equilibrium (p. 641 multiplicity).
* Footnote 29, one-period punishments: exact sustainable set
  `[k(χ − β(1 + χ))/(χ(χ + β(1 + χ))), k/χ]`, which always contains rates below `k/χ`.
* Finite horizon (pp. 640–641, T19): in every subgame-perfect equilibrium of the `T`-period
  game, `πᵉ = k/χ` and `π = k/χ + z/(1 + χ)` at every history (backward induction), and this
  profile is an equilibrium.
-/

namespace ObstfeldRogoff.NominalRigidities.ReputationEquilibria

open Filter Topology
open ObstfeldRogoff.NominalRigidities.BarroGordon

variable {S : Type*} [Fintype S]

/-- O&R §9.5.1.4: a history, the list (newest first) of past `(π, πᵉ, shock state)`. -/
abbrev Hist (S : Type*) := List (ℝ × ℝ × S)

/-- O&R (37), p. 639: the `N`-period expected discounted loss from history `h` when
expectations follow `ε` and the bank follows `σ`, computed recursively over the event tree
of iid shocks. -/
noncomputable def truncCost (p z : S → ℝ) (β χ k : ℝ) (ε : Hist S → ℝ)
    (σ : Hist S → S → ℝ) : ℕ → Hist S → ℝ
  | 0, _ => 0
  | N + 1, h => ∑ s, p s * (bgLoss χ k (σ h s) (ε h) (z s) +
      β * truncCost p z β χ k ε σ N ((σ h s, ε h, s) :: h))

/-- O&R (37): the Bellman operator: expected current loss of the action rule `a` at `h`
plus the discounted continuation value `W`. -/
noncomputable def bellman (p z : S → ℝ) (β χ k : ℝ) (ε : Hist S → ℝ) (W : Hist S → ℝ)
    (h : Hist S) (a : S → ℝ) : ℝ :=
  ∑ s, p s * (bgLoss χ k (a s) (ε h) (z s) + β * W ((a s, ε h, s) :: h))

/-- O&R (37): one step of the recursion is the Bellman operator applied to the shorter
horizon. -/
theorem truncCost_succ (p z : S → ℝ) (β χ k : ℝ) (ε : Hist S → ℝ) (σ : Hist S → S → ℝ)
    (N : ℕ) (h : Hist S) :
    truncCost p z β χ k ε σ (N + 1) h =
      bellman p z β χ k ε (truncCost p z β χ k ε σ N) h (σ h) := rfl

/-- O&R (37): the Bellman operator is an expectation. -/
theorem bellman_eq_expect (p z : S → ℝ) (β χ k : ℝ) (ε W : Hist S → ℝ) (h : Hist S)
    (a : S → ℝ) :
    bellman p z β χ k ε W h a =
      expect p (fun s => bgLoss χ k (a s) (ε h) (z s) + β * W ((a s, ε h, s) :: h)) := rfl

/-- O&R (37): the expected present value of the loss from `h` is `J`: the truncated costs
converge to `J`. -/
def HasExpPV (p z : S → ℝ) (β χ k : ℝ) (ε : Hist S → ℝ) (σ : Hist S → S → ℝ) (h : Hist S)
    (J : ℝ) : Prop :=
  Tendsto (fun N => truncCost p z β χ k ε σ N h) atTop (𝓝 J)

/-- O&R §9.5.1.4 (38)–(39): a reputational equilibrium: expectations are rational at every
history, and at every history the bank's strategy has a finite expected present value of
loss that no alternative strategy beats. -/
def IsReputationEqm (p z : S → ℝ) (β χ k : ℝ) (ε : Hist S → ℝ) (σ : Hist S → S → ℝ) :
    Prop :=
  (∀ h, ε h = expect p (σ h)) ∧
    ∀ h, ∃ J, HasExpPV p z β χ k ε σ h J ∧
      ∀ σ' J', HasExpPV p z β χ k ε σ' h J' → J ≤ J'

/-! ## General theory: monotonicity and verification -/

/-- O&R (37): nonnegative losses make the truncated costs nondecreasing in the horizon. -/
theorem truncCost_le_succ (p z : S → ℝ) (β χ k : ℝ) (hp : ∀ s, 0 ≤ p s) (hβ : 0 ≤ β)
    (hχ : 0 ≤ χ) (ε : Hist S → ℝ) (σ : Hist S → S → ℝ) :
    ∀ N h, truncCost p z β χ k ε σ N h ≤ truncCost p z β χ k ε σ (N + 1) h := by
  intro N
  induction N with
  | zero =>
    intro h
    simp only [truncCost, mul_zero, add_zero]
    exact Finset.sum_nonneg fun s _ =>
      mul_nonneg (hp s) (add_nonneg (sq_nonneg _) (mul_nonneg hχ (sq_nonneg _)))
  | succ N ih =>
    intro h
    rw [truncCost_succ, truncCost_succ (N := N + 1)]
    exact Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left
      (add_le_add_right (mul_le_mul_of_nonneg_left (ih _) hβ) _) (hp s)

/-- O&R (37): every strategy has either a finite expected present value of loss or an
infinite one (monotone convergence). -/
theorem truncCost_tendsto_or_atTop (p z : S → ℝ) (β χ k : ℝ) (hp : ∀ s, 0 ≤ p s)
    (hβ : 0 ≤ β) (hχ : 0 ≤ χ) (ε : Hist S → ℝ) (σ : Hist S → S → ℝ) (h : Hist S) :
    Tendsto (fun N => truncCost p z β χ k ε σ N h) atTop atTop ∨
      ∃ J, HasExpPV p z β χ k ε σ h J :=
  tendsto_atTop_of_monotone
    (monotone_nat_of_le_succ fun N => truncCost_le_succ p z β χ k hp hβ hχ ε σ N h)

/-- O&R (37), verification (lower bound): if `W ≤ W̄` and `W` satisfies the Bellman
inequality for every action rule, then every strategy's `N`-period cost is at least
`W h − βᴺ W̄`. -/
theorem truncCost_lower (p z : S → ℝ) (β χ k : ℝ) (hp : ∀ s, 0 ≤ p s) (h1 : ∑ s, p s = 1)
    (hβ : 0 ≤ β) (ε W : Hist S → ℝ) (Wbar : ℝ) (hW : ∀ h, W h ≤ Wbar)
    (hbell : ∀ h a, W h ≤ bellman p z β χ k ε W h a) (σ : Hist S → S → ℝ) :
    ∀ N h, W h - β ^ N * Wbar ≤ truncCost p z β χ k ε σ N h := by
  intro N
  induction N with
  | zero =>
    intro h
    simp only [pow_zero, one_mul, truncCost]
    linarith [hW h]
  | succ N ih =>
    intro h
    have hb := hbell h (σ h)
    have key : bellman p z β χ k ε W h (σ h) - β ^ (N + 1) * Wbar =
        ∑ s, p s * (bgLoss χ k (σ h s) (ε h) (z s) +
          β * (W ((σ h s, ε h, s) :: h) - β ^ N * Wbar)) := by
      have e : β ^ (N + 1) * Wbar = ∑ s, p s * (β * (β ^ N * Wbar)) := by
        rw [← Finset.sum_mul, h1]
        ring
      rw [e, bellman, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun s _ => by ring
    rw [truncCost_succ]
    have : ∑ s, p s * (bgLoss χ k (σ h s) (ε h) (z s) +
          β * (W ((σ h s, ε h, s) :: h) - β ^ N * Wbar)) ≤
        bellman p z β χ k ε (truncCost p z β χ k ε σ N) h (σ h) :=
      Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left
        (add_le_add_right (mul_le_mul_of_nonneg_left (ih _) hβ) _) (hp s)
    linarith

/-- O&R (37), verification (evaluation): if `|W| ≤ W̄` and `W` satisfies the Bellman equality
for `σ`, then `|truncCost N h − W h| ≤ βᴺ W̄`. -/
theorem truncCost_eval (p z : S → ℝ) (β χ k : ℝ) (hp : ∀ s, 0 ≤ p s) (h1 : ∑ s, p s = 1)
    (hβ : 0 ≤ β) (ε W : Hist S → ℝ) (Wbar : ℝ) (hW : ∀ h, |W h| ≤ Wbar)
    (σ : Hist S → S → ℝ) (heq : ∀ h, bellman p z β χ k ε W h (σ h) = W h) :
    ∀ N h, |truncCost p z β χ k ε σ N h - W h| ≤ β ^ N * Wbar := by
  intro N
  induction N with
  | zero =>
    intro h
    simpa [truncCost] using hW h
  | succ N ih =>
    intro h
    have key : truncCost p z β χ k ε σ (N + 1) h - W h =
        ∑ s, p s * (β * (truncCost p z β χ k ε σ N ((σ h s, ε h, s) :: h) -
          W ((σ h s, ε h, s) :: h))) := by
      rw [truncCost_succ, ← heq h, bellman, bellman, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun s _ => by ring
    rw [key]
    calc |∑ s, p s * (β * (truncCost p z β χ k ε σ N ((σ h s, ε h, s) :: h) -
          W ((σ h s, ε h, s) :: h)))|
        ≤ ∑ s, |p s * (β * (truncCost p z β χ k ε σ N ((σ h s, ε h, s) :: h) -
          W ((σ h s, ε h, s) :: h)))| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ s, p s * (β * (β ^ N * Wbar)) := by
        refine Finset.sum_le_sum fun s _ => ?_
        rw [abs_mul, abs_mul, abs_of_nonneg (hp s), abs_of_nonneg hβ]
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (ih _) hβ) (hp s)
      _ = β ^ (N + 1) * Wbar := by
        rw [← Finset.sum_mul, h1]
        ring

/-- O&R (37): a bounded solution of the Bellman equality for `σ` is `σ`'s expected present
value of loss (`0 ≤ β < 1`). -/
theorem tendsto_truncCost_of_bellman_eq (p z : S → ℝ) (β χ k : ℝ) (hp : ∀ s, 0 ≤ p s)
    (h1 : ∑ s, p s = 1) (hβ : 0 ≤ β) (hβ1 : β < 1) (ε W : Hist S → ℝ) (Wbar : ℝ)
    (hW : ∀ h, |W h| ≤ Wbar) (σ : Hist S → S → ℝ)
    (heq : ∀ h, bellman p z β χ k ε W h (σ h) = W h) (h : Hist S) :
    HasExpPV p z β χ k ε σ h (W h) := by
  have hev := truncCost_eval p z β χ k hp h1 hβ ε W Wbar hW σ heq
  have hlim : Tendsto (fun N : ℕ => β ^ N * Wbar) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ hβ1).mul_const Wbar
  have hlo : Tendsto (fun N : ℕ => W h - β ^ N * Wbar) atTop (𝓝 (W h)) := by
    simpa using hlim.const_sub (W h)
  have hhi : Tendsto (fun N : ℕ => W h + β ^ N * Wbar) atTop (𝓝 (W h)) := by
    simpa using hlim.const_add (W h)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hhi (fun N => ?_) (fun N => ?_)
  · have := (abs_le.1 (hev N h)).1
    linarith
  · have := (abs_le.1 (hev N h)).2
    linarith

/-- O&R (37): under the Bellman inequality, no strategy has an expected present value of
loss below `W h` (`0 ≤ β < 1`). -/
theorem le_of_hasExpPV_of_bellman_le (p z : S → ℝ) (β χ k : ℝ) (hp : ∀ s, 0 ≤ p s)
    (h1 : ∑ s, p s = 1) (hβ : 0 ≤ β) (hβ1 : β < 1) (ε W : Hist S → ℝ) (Wbar : ℝ)
    (hW : ∀ h, W h ≤ Wbar) (hbell : ∀ h a, W h ≤ bellman p z β χ k ε W h a)
    (σ : Hist S → S → ℝ) (h : Hist S) (J : ℝ) (hJ : HasExpPV p z β χ k ε σ h J) :
    W h ≤ J := by
  have hlim : Tendsto (fun N : ℕ => β ^ N * Wbar) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hβ hβ1).mul_const Wbar
  have hlo : Tendsto (fun N : ℕ => W h - β ^ N * Wbar) atTop (𝓝 (W h)) := by
    simpa using hlim.const_sub (W h)
  exact le_of_tendsto_of_tendsto' hlo hJ fun N =>
    truncCost_lower p z β χ k hp h1 hβ ε W Wbar hW hbell σ N h

/-- O&R §9.5.1.4, verification theorem: rational expectations, a bounded `W`, the Bellman
equality for `σ` and the Bellman inequality for all action rules make `(ε, σ)` a
reputational equilibrium. -/
theorem isReputationEqm_of_bellman (p z : S → ℝ) (β χ k : ℝ) (hp : ∀ s, 0 ≤ p s)
    (h1 : ∑ s, p s = 1) (hβ : 0 ≤ β) (hβ1 : β < 1) (ε W : Hist S → ℝ) (Wbar : ℝ)
    (hW : ∀ h, |W h| ≤ Wbar) (σ : Hist S → S → ℝ) (hre : ∀ h, ε h = expect p (σ h))
    (heq : ∀ h, bellman p z β χ k ε W h (σ h) = W h)
    (hbell : ∀ h a, W h ≤ bellman p z β χ k ε W h a) :
    IsReputationEqm p z β χ k ε σ := by
  refine ⟨hre, fun h => ⟨W h,
    tendsto_truncCost_of_bellman_eq p z β χ k hp h1 hβ hβ1 ε W Wbar hW σ heq h,
    fun σ' J' hJ' => ?_⟩⟩
  exact le_of_hasExpPV_of_bellman_le p z β χ k hp h1 hβ hβ1 ε W Wbar
    (fun g => (abs_le.1 (hW g)).2) hbell σ' h J' hJ'

/-- O&R §9.5.1.4: a strategy is not an equilibrium strategy if at some history some
alternative strategy has a strictly smaller expected present value of loss. -/
theorem not_isReputationEqm_of_better (p z : S → ℝ) (β χ k : ℝ) (ε : Hist S → ℝ)
    (σ σ' : Hist S → S → ℝ) (h : Hist S) (J J' : ℝ) (hJ : HasExpPV p z β χ k ε σ h J)
    (hJ' : HasExpPV p z β χ k ε σ' h J') (hlt : J' < J) :
    ¬ IsReputationEqm p z β χ k ε σ := by
  rintro ⟨_, hopt⟩
  obtain ⟨J0, hJ0, hle⟩ := hopt h
  have := tendsto_nhds_unique hJ0 hJ
  have := hle σ' J' hJ'
  linarith

/-! ## One-shot deviations at the initial history -/

/-- O&R p. 640: the strategy that plays the action rule `d` at the empty history and follows
`σ` everywhere else. -/
def rootDev (d : S → ℝ) (σ : Hist S → S → ℝ) : Hist S → S → ℝ
  | [], s => d s
  | x :: t, s => σ (x :: t) s

/-- O&R p. 640: the value function equal to `A` at the empty history and to `W` elsewhere. -/
def rootVal (A : ℝ) (W : Hist S → ℝ) : Hist S → ℝ
  | [] => A
  | x :: t => W (x :: t)

/-- O&R p. 640: if `W` solves the Bellman equality for `σ`, then deviating to `d` at the
empty history and following `σ` afterwards has expected present value `bellman W [] d`. -/
theorem hasExpPV_rootDev (p z : S → ℝ) (β χ k : ℝ) (hp : ∀ s, 0 ≤ p s)
    (h1 : ∑ s, p s = 1) (hβ : 0 ≤ β) (hβ1 : β < 1) (ε W : Hist S → ℝ) (Wbar : ℝ)
    (hW : ∀ h, |W h| ≤ Wbar) (σ : Hist S → S → ℝ)
    (heq : ∀ h, bellman p z β χ k ε W h (σ h) = W h) (d : S → ℝ) :
    HasExpPV p z β χ k ε (rootDev d σ) [] (bellman p z β χ k ε W [] d) := by
  set A := bellman p z β χ k ε W [] d
  have hW' : ∀ h, |rootVal A W h| ≤ Wbar + |A| := by
    intro h
    cases h with
    | nil =>
      simp only [rootVal]
      linarith [abs_nonneg (W []), hW []]
    | cons x t =>
      simp only [rootVal]
      linarith [hW (x :: t), abs_nonneg A]
  have heq' : ∀ h, bellman p z β χ k ε (rootVal A W) h (rootDev d σ h) = rootVal A W h := by
    intro h
    cases h with
    | nil => rfl
    | cons x t => exact heq (x :: t)
  exact tendsto_truncCost_of_bellman_eq p z β χ k hp h1 hβ hβ1 ε (rootVal A W) (Wbar + |A|)
    hW' (rootDev d σ) heq' []

/-! ## Stage losses -/

/-- O&R p. 640: the minimised one-period loss given expectations `e` and shock `zz`,
`χ(k + e + zz)²/(1 + χ)`. -/
noncomputable def minLoss (χ k e zz : ℝ) : ℝ := χ * (k + e + zz) ^ 2 / (1 + χ)

/-- O&R p. 640: every action loses at least `minLoss`. -/
theorem minLoss_le (χ k a e zz : ℝ) (hχ : 0 < 1 + χ) : minLoss χ k e zz ≤ bgLoss χ k a e zz := by
  have := bestResponse_isMin χ k a e zz hχ
  rwa [bgLoss_bestResponse χ k e zz hχ] at this

/-- O&R (39): the on-path loss of the trigger rule with target `π̄`: `π = π̄ + z/(1 + χ)`. -/
noncomputable def onLoss (χ k πbar zz : ℝ) : ℝ := bgLoss χ k (πbar + zz / (1 + χ)) πbar zz

/-- O&R p. 640 and (39): the one-period gain from cheating, `onLoss − minLoss`, is
`(k − χπ̄)²/(1 + χ)`, **independent of the shock** (for `π̄ = 0`, the book's `k²/(1 + χ)`). -/
theorem onLoss_sub_minLoss (χ k πbar zz : ℝ) (hχ : 0 < 1 + χ) :
    onLoss χ k πbar zz - minLoss χ k πbar zz = (k - χ * πbar) ^ 2 / (1 + χ) := by
  unfold onLoss minLoss bgLoss
  field_simp
  ring

/-- O&R (39): the expected on-path loss, `k² + χπ̄² + χσ²/(1 + χ)`. -/
noncomputable def valueOn (χ k σ2 πbar : ℝ) : ℝ := k ^ 2 + χ * πbar ^ 2 + χ * σ2 / (1 + χ)

/-- O&R (39): `E onLoss = k² + χπ̄² + χσ²/(1 + χ)`. -/
theorem expect_onLoss (p z : S → ℝ) (χ k πbar : ℝ) (hχ : 0 < 1 + χ) (h1 : ∑ s, p s = 1)
    (hz : expect p z = 0) :
    expect p (fun s => onLoss χ k πbar (z s)) = valueOn χ k (varZ p z) πbar := by
  unfold expect at hz ⊢
  unfold valueOn varZ expect
  have : ∑ s, p s * onLoss χ k πbar (z s) = ∑ s, (p s * (k ^ 2 + χ * πbar ^ 2) +
      (2 * k * χ + 2 * χ * πbar) / (1 + χ) * (p s * z s) +
        χ / (1 + χ) * (p s * z s ^ 2)) := by
    refine Finset.sum_congr rfl fun s _ => ?_
    unfold onLoss bgLoss
    field_simp
    ring
  rw [this, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum,
    ← Finset.mul_sum, h1, hz]
  ring

/-- O&R (35), fn 28: at `π̄ = k/χ` the on-path value is the discretionary value `V_D`. -/
theorem valueOn_discretion (χ k σ2 : ℝ) (hχ : 0 < χ) :
    valueOn χ k σ2 (k / χ) = valueDiscretion χ k σ2 := by
  unfold valueOn valueDiscretion
  field_simp

/-- O&R p. 640: the per-period punishment cost `V_D − V_on = k²/χ − χπ̄²` (the book's
`k²/χ` at `π̄ = 0`). -/
theorem valueDiscretion_sub_valueOn (χ k σ2 πbar : ℝ) :
    valueDiscretion χ k σ2 - valueOn χ k σ2 πbar = k ^ 2 / χ - χ * πbar ^ 2 := by
  unfold valueDiscretion valueOn
  ring

/-- O&R fn 28: in the punishment phase the best response to `πᵉ = k/χ` is
`k/χ + z/(1 + χ)`, and its loss is the minimum. -/
theorem onLoss_discretion (χ k zz : ℝ) (hχ : 0 < χ) :
    onLoss χ k (k / χ) zz = minLoss χ k (k / χ) zz := by
  have h := onLoss_sub_minLoss χ k (k / χ) zz (by linarith)
  have : k - χ * (k / χ) = 0 := by field_simp; ring
  rw [this] at h
  simp at h
  linarith

/-- O&R p. 640: the best response to `π̄` coincides with the trigger action iff `k = χπ̄`. -/
theorem bestResponse_eq_onPath_iff (χ k πbar zz : ℝ) (hχ : 0 < 1 + χ) :
    bestResponse χ k πbar zz = πbar + zz / (1 + χ) ↔ k = χ * πbar := by
  unfold bestResponse
  rw [div_eq_iff hχ.ne']
  constructor
  · intro h
    field_simp at h
    linarith
  · intro h
    field_simp
    linarith

/-! ## Infinite-punishment trigger strategies, (38)–(39) -/

/-- O&R (38)–(39): no past period had a surprise, `π = πᵉ + z/(1 + χ)` at every past date. -/
def NoSurprise (χ : ℝ) (z : S → ℝ) (h : Hist S) : Prop :=
  ∀ x ∈ h, x.1 = x.2.1 + z x.2.2 / (1 + χ)

omit [Fintype S] in
/-- O&R (38): the empty history has no surprise. -/
theorem noSurprise_nil (χ : ℝ) (z : S → ℝ) : NoSurprise χ z ([] : Hist S) := by
  simp [NoSurprise]

omit [Fintype S] in
/-- O&R (38): extending a history. -/
theorem noSurprise_cons_iff (χ : ℝ) (z : S → ℝ) (x : ℝ × ℝ × S) (h : Hist S) :
    NoSurprise χ z (x :: h) ↔ x.1 = x.2.1 + z x.2.2 / (1 + χ) ∧ NoSurprise χ z h := by
  simp [NoSurprise]

/-- O&R (38)–(39): trigger expectations with target `π̄`: `π̄` after surprise-free histories,
the one-shot level `k/χ` forever after any surprise. -/
noncomputable def trigExp (χ k πbar : ℝ) (z : S → ℝ) (h : Hist S) : ℝ := by
  classical exact if NoSurprise χ z h then πbar else k / χ

/-- O&R (39), fn 28: the bank's trigger strategy: `π̄ + z/(1 + χ)` after surprise-free
histories, the one-shot best response `k/χ + z/(1 + χ)` in punishment. -/
noncomputable def trigCB (χ k πbar : ℝ) (z : S → ℝ) (h : Hist S) (s : S) : ℝ := by
  classical exact if NoSurprise χ z h then πbar + z s / (1 + χ) else k / χ + z s / (1 + χ)

/-- O&R (38): the value of the trigger profile: `V_on/(1 − β)` or `V_D/(1 − β)`. -/
noncomputable def trigVal (p z : S → ℝ) (β χ k πbar : ℝ) (h : Hist S) : ℝ := by
  classical exact if NoSurprise χ z h then valueOn χ k (varZ p z) πbar / (1 - β)
    else valueOn χ k (varZ p z) (k / χ) / (1 - β)

/-- O&R p. 640: the equilibrium condition `gain ≤ β/(1 − β)·punishment cost`. -/
def TriggerCond (χ k β πbar : ℝ) : Prop :=
  (k - χ * πbar) ^ 2 / (1 + χ) ≤ β / (1 - β) * (k ^ 2 / χ - χ * πbar ^ 2)

omit [Fintype S] in
/-- O&R (38)–(39): expectations after a surprise-free history. -/
theorem trigExp_pos (χ k πbar : ℝ) (z : S → ℝ) (h : Hist S) (hns : NoSurprise χ z h) :
    trigExp χ k πbar z h = πbar := by
  unfold trigExp
  simp [hns]

omit [Fintype S] in
/-- O&R (38)–(39): expectations after a surprise. -/
theorem trigExp_neg (χ k πbar : ℝ) (z : S → ℝ) (h : Hist S) (hns : ¬ NoSurprise χ z h) :
    trigExp χ k πbar z h = k / χ := by
  unfold trigExp
  simp [hns]

omit [Fintype S] in
/-- O&R (39): the bank's play after a surprise-free history. -/
theorem trigCB_pos (χ k πbar : ℝ) (z : S → ℝ) (h : Hist S) (hns : NoSurprise χ z h) (s : S) :
    trigCB χ k πbar z h s = πbar + z s / (1 + χ) := by
  unfold trigCB
  simp [hns]

omit [Fintype S] in
/-- O&R fn 28: the bank's play in punishment. -/
theorem trigCB_neg (χ k πbar : ℝ) (z : S → ℝ) (h : Hist S) (hns : ¬ NoSurprise χ z h)
    (s : S) : trigCB χ k πbar z h s = k / χ + z s / (1 + χ) := by
  unfold trigCB
  simp [hns]

/-- O&R (38): the trigger value after a surprise-free history. -/
theorem trigVal_pos (p z : S → ℝ) (β χ k πbar : ℝ) (h : Hist S) (hns : NoSurprise χ z h) :
    trigVal p z β χ k πbar h = valueOn χ k (varZ p z) πbar / (1 - β) := by
  unfold trigVal
  simp [hns]

/-- O&R (38): the trigger value in punishment. -/
theorem trigVal_neg (p z : S → ℝ) (β χ k πbar : ℝ) (h : Hist S) (hns : ¬ NoSurprise χ z h) :
    trigVal p z β χ k πbar h = valueOn χ k (varZ p z) (k / χ) / (1 - β) := by
  unfold trigVal
  simp [hns]

/-- O&R (39): the rule `c + z/(1 + χ)` has mean `c` (as `E z = 0`). -/
theorem expect_const_add_shock (p z : S → ℝ) (χ c : ℝ) (h1 : ∑ s, p s = 1)
    (hz : expect p z = 0) : expect p (fun s => c + z s / (1 + χ)) = c := by
  have : expect p (fun s => c + z s / (1 + χ)) =
      expect p (fun s => c + (1 / (1 + χ)) * z s) := by
    unfold expect
    exact Finset.sum_congr rfl fun s _ => by ring
  rw [this, expect_add, expect_const p h1, expect_const_mul, hz, mul_zero, add_zero]

/-- Pointwise equal integrands have equal expectations (O&R §9.5.1). -/
theorem expect_congr' (p f g : S → ℝ) (hfg : ∀ s, f s = g s) : expect p f = expect p g := by
  rw [funext hfg]

/-- O&R (38): expectations are rational at every history under the trigger profile. -/
theorem trig_rational (p z : S → ℝ) (χ k πbar : ℝ) (h1 : ∑ s, p s = 1) (hz : expect p z = 0)
    (h : Hist S) : trigExp χ k πbar z h = expect p (trigCB χ k πbar z h) := by
  by_cases hns : NoSurprise χ z h
  · rw [trigExp_pos χ k πbar z h hns, funext (trigCB_pos χ k πbar z h hns),
      expect_const_add_shock p z χ πbar h1 hz]
  · rw [trigExp_neg χ k πbar z h hns, funext (trigCB_neg χ k πbar z h hns),
      expect_const_add_shock p z χ _ h1 hz]

/-- Arithmetic behind O&R p. 640: `V/(1 − β) = V + β·V/(1 − β)`. -/
theorem div_one_sub_eq (V β : ℝ) (hβ1 : β < 1) : V / (1 - β) = V + β * (V / (1 - β)) := by
  have : (1 - β) ≠ 0 := by linarith
  field_simp
  ring

/-- O&R (38)–(39): the trigger value satisfies the Bellman equality for the trigger
strategy at every history. -/
theorem trig_bellman_eq (p z : S → ℝ) (β χ k πbar : ℝ) (hχ : 0 < χ) (hβ1 : β < 1)
    (h1 : ∑ s, p s = 1) (hz : expect p z = 0) (h : Hist S) :
    bellman p z β χ k (trigExp χ k πbar z) (trigVal p z β χ k πbar) h
      (trigCB χ k πbar z h) = trigVal p z β χ k πbar h := by
  have hχ1 : 0 < 1 + χ := by linarith
  rw [bellman_eq_expect]
  by_cases hns : NoSurprise χ z h
  · have hpt : ∀ s, bgLoss χ k (trigCB χ k πbar z h s) (trigExp χ k πbar z h) (z s) +
        β * trigVal p z β χ k πbar ((trigCB χ k πbar z h s, trigExp χ k πbar z h, s) :: h) =
        onLoss χ k πbar (z s) + β * (valueOn χ k (varZ p z) πbar / (1 - β)) := by
      intro s
      have hn : NoSurprise χ z ((πbar + z s / (1 + χ), πbar, s) :: h) :=
        (noSurprise_cons_iff χ z _ h).2 ⟨rfl, hns⟩
      rw [trigCB_pos χ k πbar z h hns, trigExp_pos χ k πbar z h hns,
        trigVal_pos p z β χ k πbar _ hn]
      rfl
    rw [expect_congr' p _ _ hpt, expect_add, expect_onLoss p z χ k πbar hχ1 h1 hz,
      expect_const p h1, trigVal_pos p z β χ k πbar h hns]
    exact (div_one_sub_eq _ β hβ1).symm
  · have hpt : ∀ s, bgLoss χ k (trigCB χ k πbar z h s) (trigExp χ k πbar z h) (z s) +
        β * trigVal p z β χ k πbar ((trigCB χ k πbar z h s, trigExp χ k πbar z h, s) :: h) =
        onLoss χ k (k / χ) (z s) + β * (valueOn χ k (varZ p z) (k / χ) / (1 - β)) := by
      intro s
      have hn : ¬ NoSurprise χ z ((trigCB χ k πbar z h s, trigExp χ k πbar z h, s) :: h) :=
        fun hc => hns ((noSurprise_cons_iff χ z _ h).1 hc).2
      rw [trigVal_neg p z β χ k πbar _ hn, trigCB_neg χ k πbar z h hns,
        trigExp_neg χ k πbar z h hns]
      rfl
    rw [expect_congr' p _ _ hpt, expect_add, expect_onLoss p z χ k (k / χ) hχ1 h1 hz,
      expect_const p h1, trigVal_neg p z β χ k πbar h hns]
    exact (div_one_sub_eq _ β hβ1).symm

/-- O&R p. 640: `β·W_D − β·W_on = β/(1 − β)·(k²/χ − χπ̄²)`. -/
theorem beta_val_diff (p z : S → ℝ) (β χ k πbar : ℝ) (hχ : 0 < χ) (hβ1 : β < 1) :
    β * (valueOn χ k (varZ p z) (k / χ) / (1 - β)) -
      β * (valueOn χ k (varZ p z) πbar / (1 - β)) =
      β / (1 - β) * (k ^ 2 / χ - χ * πbar ^ 2) := by
  have hc2 := valueDiscretion_sub_valueOn χ k (varZ p z) πbar
  rw [← valueOn_discretion χ k (varZ p z) hχ] at hc2
  rw [← hc2]
  have : (1 - β) ≠ 0 := by linarith
  field_simp

/-- O&R p. 640: under the condition `gain ≤ β/(1 − β)·cost`, the trigger value satisfies the
Bellman inequality for every action rule at every history (no deviation plan pays). -/
theorem trig_bellman_le (p z : S → ℝ) (β χ k πbar : ℝ) (hχ : 0 < χ) (hβ1 : β < 1)
    (hp : ∀ s, 0 ≤ p s) (h1 : ∑ s, p s = 1) (hz : expect p z = 0)
    (hcond : TriggerCond χ k β πbar) (h : Hist S) (a : S → ℝ) :
    trigVal p z β χ k πbar h ≤
      bellman p z β χ k (trigExp χ k πbar z) (trigVal p z β χ k πbar) h a := by
  have hχ1 : 0 < 1 + χ := by linarith
  rw [bellman_eq_expect]
  by_cases hns : NoSurprise χ z h
  · have hpt : ∀ s, onLoss χ k πbar (z s) + β * (valueOn χ k (varZ p z) πbar / (1 - β)) ≤
        bgLoss χ k (a s) (trigExp χ k πbar z h) (z s) +
          β * trigVal p z β χ k πbar ((a s, trigExp χ k πbar z h, s) :: h) := by
      intro s
      rw [trigExp_pos χ k πbar z h hns]
      by_cases ha : a s = πbar + z s / (1 + χ)
      · have hn : NoSurprise χ z ((a s, πbar, s) :: h) :=
          (noSurprise_cons_iff χ z _ h).2 ⟨ha, hns⟩
        rw [trigVal_pos p z β χ k πbar _ hn, ha]
        rfl
      · have hn : ¬ NoSurprise χ z ((a s, πbar, s) :: h) := fun hc =>
          ha ((noSurprise_cons_iff χ z _ h).1 hc).1
        rw [trigVal_neg p z β χ k πbar _ hn]
        have hm := minLoss_le χ k (a s) πbar (z s) hχ1
        have hg := onLoss_sub_minLoss χ k πbar (z s) hχ1
        have e := beta_val_diff p z β χ k πbar hχ hβ1
        unfold TriggerCond at hcond
        linarith
    calc trigVal p z β χ k πbar h
        = expect p (fun s => onLoss χ k πbar (z s) +
            β * (valueOn χ k (varZ p z) πbar / (1 - β))) := by
          rw [expect_add, expect_onLoss p z χ k πbar hχ1 h1 hz, expect_const p h1,
            trigVal_pos p z β χ k πbar h hns]
          exact div_one_sub_eq _ β hβ1
      _ ≤ _ := expect_mono p _ _ hp hpt
  · have hpt : ∀ s, onLoss χ k (k / χ) (z s) +
        β * (valueOn χ k (varZ p z) (k / χ) / (1 - β)) ≤
        bgLoss χ k (a s) (trigExp χ k πbar z h) (z s) +
          β * trigVal p z β χ k πbar ((a s, trigExp χ k πbar z h, s) :: h) := by
      intro s
      have hn : ¬ NoSurprise χ z ((a s, trigExp χ k πbar z h, s) :: h) := fun hc =>
        hns ((noSurprise_cons_iff χ z _ h).1 hc).2
      rw [trigVal_neg p z β χ k πbar _ hn, trigExp_neg χ k πbar z h hns,
        onLoss_discretion χ k (z s) hχ]
      linarith [minLoss_le χ k (a s) (k / χ) (z s) hχ1]
    calc trigVal p z β χ k πbar h
        = expect p (fun s => onLoss χ k (k / χ) (z s) +
            β * (valueOn χ k (varZ p z) (k / χ) / (1 - β))) := by
          rw [expect_add, expect_onLoss p z χ k (k / χ) hχ1 h1 hz, expect_const p h1,
            trigVal_neg p z β χ k πbar h hns]
          exact div_one_sub_eq _ β hβ1
      _ ≤ _ := expect_mono p _ _ hp hpt

/-- O&R (38)–(39): the trigger value is bounded. -/
theorem trigVal_abs_le (p z : S → ℝ) (β χ k πbar : ℝ) (h : Hist S) :
    |trigVal p z β χ k πbar h| ≤ |valueOn χ k (varZ p z) πbar / (1 - β)| +
      |valueOn χ k (varZ p z) (k / χ) / (1 - β)| := by
  by_cases hns : NoSurprise χ z h
  · rw [trigVal_pos p z β χ k πbar h hns]
    linarith [abs_nonneg (valueOn χ k (varZ p z) (k / χ) / (1 - β))]
  · rw [trigVal_neg p z β χ k πbar h hns]
    linarith [abs_nonneg (valueOn χ k (varZ p z) πbar / (1 - β))]

/-- O&R p. 640: the value of cheating once at the empty history (best response `d` to
`π̄`) and being punished forever: `V_on − gain + β·V_D/(1 − β)`, provided `k ≠ χπ̄`. -/
theorem trig_rootDev_value (p z : S → ℝ) (β χ k πbar : ℝ) (hχ : 0 < χ) (h1 : ∑ s, p s = 1)
    (hz : expect p z = 0) (hne : k ≠ χ * πbar) :
    bellman p z β χ k (trigExp χ k πbar z) (trigVal p z β χ k πbar) []
        (fun s => bestResponse χ k πbar (z s)) =
      valueOn χ k (varZ p z) πbar - (k - χ * πbar) ^ 2 / (1 + χ) +
        β * (valueOn χ k (varZ p z) (k / χ) / (1 - β)) := by
  have hχ1 : 0 < 1 + χ := by linarith
  rw [bellman_eq_expect, trigExp_pos χ k πbar z [] (noSurprise_nil χ z)]
  have hpt : ∀ s, bgLoss χ k (bestResponse χ k πbar (z s)) πbar (z s) +
      β * trigVal p z β χ k πbar ((bestResponse χ k πbar (z s), πbar, s) :: []) =
      (onLoss χ k πbar (z s) - (k - χ * πbar) ^ 2 / (1 + χ)) +
        β * (valueOn χ k (varZ p z) (k / χ) / (1 - β)) := by
    intro s
    have hn : ¬ NoSurprise χ z ((bestResponse χ k πbar (z s), πbar, s) :: []) := by
      rw [noSurprise_cons_iff]
      rintro ⟨hc2, -⟩
      exact hne ((bestResponse_eq_onPath_iff χ k πbar (z s) hχ1).1 hc2)
    rw [trigVal_neg p z β χ k πbar _ hn, ← onLoss_sub_minLoss χ k πbar (z s) hχ1,
      bgLoss_bestResponse χ k πbar (z s) hχ1, minLoss]
    ring
  rw [expect_congr' p _ _ hpt, expect_add, expect_sub, expect_onLoss p z χ k πbar hχ1 h1 hz,
    expect_const p h1, expect_const p h1]

/-- O&R (38)–(39), pp. 639–641, and T17 (exact form): the trigger profile with target `π̄`
is a reputational equilibrium **iff** the one-period cheating gain `(k − χπ̄)²/(1 + χ)` is at
most the discounted punishment cost `β/(1 − β)·(k²/χ − χπ̄²)`. -/
theorem trigger_eqm_iff (p z : S → ℝ) (β χ k πbar : ℝ) (hχ : 0 < χ) (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) (hp : ∀ s, 0 ≤ p s) (h1 : ∑ s, p s = 1) (hz : expect p z = 0) :
    IsReputationEqm p z β χ k (trigExp χ k πbar z) (trigCB χ k πbar z) ↔
      TriggerCond χ k β πbar := by
  set Wbar := |valueOn χ k (varZ p z) πbar / (1 - β)| +
      |valueOn χ k (varZ p z) (k / χ) / (1 - β)|
  constructor
  · intro heqm
    by_contra hc
    unfold TriggerCond at hc
    push Not at hc
    have hne : k ≠ χ * πbar := by
      intro hk
      have e1 : k - χ * πbar = 0 := by rw [hk]; ring
      have e2 : k ^ 2 / χ - χ * πbar ^ 2 = 0 := by rw [hk]; field_simp; ring
      rw [e1, e2] at hc
      simp at hc
    have hdev := hasExpPV_rootDev p z β χ k hp h1 hβ0 hβ1 (trigExp χ k πbar z)
      (trigVal p z β χ k πbar) Wbar (trigVal_abs_le p z β χ k πbar) (trigCB χ k πbar z)
      (trig_bellman_eq p z β χ k πbar hχ hβ1 h1 hz) (fun s => bestResponse χ k πbar (z s))
    have htrig := tendsto_truncCost_of_bellman_eq p z β χ k hp h1 hβ0 hβ1 (trigExp χ k πbar z)
      (trigVal p z β χ k πbar) Wbar (trigVal_abs_le p z β χ k πbar) (trigCB χ k πbar z)
      (trig_bellman_eq p z β χ k πbar hχ hβ1 h1 hz) []
    refine not_isReputationEqm_of_better p z β χ k _ _ _ [] _ _ htrig hdev ?_ heqm
    rw [trig_rootDev_value p z β χ k πbar hχ h1 hz hne,
      trigVal_pos p z β χ k πbar [] (noSurprise_nil χ z)]
    have e := div_one_sub_eq (valueOn χ k (varZ p z) πbar) β hβ1
    have e2 := beta_val_diff p z β χ k πbar hχ hβ1
    linarith
  · intro hcond
    exact isReputationEqm_of_bellman p z β χ k hp h1 hβ0 hβ1 (trigExp χ k πbar z)
      (trigVal p z β χ k πbar) Wbar (trigVal_abs_le p z β χ k πbar) (trigCB χ k πbar z)
      (trig_rational p z χ k πbar h1 hz) (trig_bellman_eq p z β χ k πbar hχ hβ1 h1 hz)
      (trig_bellman_le p z β χ k πbar hχ hβ1 hp h1 hz hcond)

/-! ## The exact sustainable set (T17) -/

/-- T17: the lowest sustainable trigger target, `π̲(β) = k(χ − β(1 + 2χ))/(χ(χ + β))`. -/
noncomputable def lowerBound (χ k β : ℝ) : ℝ := k * (χ - β * (1 + 2 * χ)) / (χ * (χ + β))

/-- An elementary fact used for T17: if `x₀ < k`, then `(k − x)(x − x₀) ≥ 0 ↔ x₀ ≤ x ≤ k`. -/
theorem between_iff (x x0 k : ℝ) (h : x0 < k) :
    0 ≤ (k - x) * (x - x0) ↔ x0 ≤ x ∧ x ≤ k := by
  constructor
  · intro hx
    by_contra hc
    rcases not_and_or.1 hc with h2 | h2
    · push Not at h2
      nlinarith
    · push Not at h2
      nlinarith
  · rintro ⟨h2, h3⟩
    exact mul_nonneg (by linarith) (by linarith)

/-- O&R p. 641 and fn 29, T17: for `k > 0`, `χ > 0`, `0 < β < 1`, the trigger condition holds
iff `π̲(β) ≤ π̄ ≤ k/χ`: the sustainable set is exactly the interval `[π̲(β), k/χ]`. -/
theorem triggerCond_iff_bounds (χ k β πbar : ℝ) (hχ : 0 < χ) (hk : 0 < k) (hβ0 : 0 < β)
    (hβ1 : β < 1) :
    TriggerCond χ k β πbar ↔ lowerBound χ k β ≤ πbar ∧ πbar ≤ k / χ := by
  have hχ1 : 0 < 1 + χ := by linarith
  have hD : 0 < 1 - β := by linarith
  have hcb : 0 < χ + β := by linarith
  set x0 := k * (χ - β * (1 + 2 * χ)) / (χ + β) with hx0
  have hx0k : x0 < k := by
    rw [hx0, div_lt_iff₀ hcb]
    nlinarith [mul_pos hk hβ0, mul_pos (mul_pos hk hβ0) hχ]
  have key : TriggerCond χ k β πbar ↔ 0 ≤ (k - χ * πbar) * (χ * πbar - x0) := by
    unfold TriggerCond
    have e : β / (1 - β) * (k ^ 2 / χ - χ * πbar ^ 2) - (k - χ * πbar) ^ 2 / (1 + χ) =
        (χ + β) / ((1 - β) * χ * (1 + χ)) * ((k - χ * πbar) * (χ * πbar - x0)) := by
      rw [hx0]
      field_simp
      ring
    have hpos : 0 < (χ + β) / ((1 - β) * χ * (1 + χ)) := by positivity
    constructor
    · intro h
      have : 0 ≤ (χ + β) / ((1 - β) * χ * (1 + χ)) * ((k - χ * πbar) * (χ * πbar - x0)) := by
        linarith
      exact (mul_nonneg_iff_of_pos_left hpos).1 this
    · intro h
      have := mul_nonneg hpos.le h
      linarith
  rw [key, between_iff (χ * πbar) x0 k hx0k]
  have e1 : x0 ≤ χ * πbar ↔ lowerBound χ k β ≤ πbar := by
    unfold lowerBound
    rw [hx0, div_le_iff₀ hcb, div_le_iff₀ (by positivity)]
    constructor <;> intro h <;> nlinarith
  have e2 : χ * πbar ≤ k ↔ πbar ≤ k / χ := by
    rw [le_div_iff₀ hχ, mul_comm]
  rw [e1, e2]

/-- O&R (38)–(39), T17: the trigger equilibrium with target `π̄` exists iff
`π̲(β) ≤ π̄ ≤ k/χ`. -/
theorem trigger_eqm_iff_bounds (p z : S → ℝ) (β χ k πbar : ℝ) (hχ : 0 < χ) (hk : 0 < k)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hp : ∀ s, 0 ≤ p s) (h1 : ∑ s, p s = 1)
    (hz : expect p z = 0) :
    IsReputationEqm p z β χ k (trigExp χ k πbar z) (trigCB χ k πbar z) ↔
      lowerBound χ k β ≤ πbar ∧ πbar ≤ k / χ := by
  rw [trigger_eqm_iff p z β χ k πbar hχ hβ0.le hβ1 hp h1 hz,
    triggerCond_iff_bounds χ k β πbar hχ hk hβ0 hβ1]

/-- O&R p. 640 (38): the zero-inflation trigger equilibrium (with the commitment rule
`z/(1 + χ)` on the path when there are shocks, (39)) exists iff `β ≥ χ/(1 + 2χ)`. -/
theorem trigger_zero_iff (p z : S → ℝ) (β χ k : ℝ) (hχ : 0 < χ) (hk : 0 < k) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hp : ∀ s, 0 ≤ p s) (h1 : ∑ s, p s = 1) (hz : expect p z = 0) :
    IsReputationEqm p z β χ k (trigExp χ k 0 z) (trigCB χ k 0 z) ↔ χ / (1 + 2 * χ) ≤ β := by
  rw [trigger_eqm_iff_bounds p z β χ k 0 hχ hk hβ0 hβ1 hp h1 hz]
  have hk' : (0 : ℝ) ≤ k / χ := by positivity
  simp only [hk', and_true]
  unfold lowerBound
  rw [div_le_iff₀ (by positivity), zero_mul, div_le_iff₀ (by positivity)]
  constructor <;> intro h <;> nlinarith

omit [Fintype S] in
/-- O&R (39): on a surprise-free history the zero-target trigger strategy plays the
commitment rule (36). -/
theorem trigCB_zero_eq_commit (χ k : ℝ) (z : S → ℝ) (h : Hist S) (hns : NoSurprise χ z h) :
    trigCB χ k 0 z h = commitRule χ z := by
  classical
  funext s
  simp [trigCB, hns, commitRule]

/-- O&R p. 640: the book's cost and gain at `π̄ = 0`: gain `k²/(1 + χ)`, per-period
punishment `k²/χ`. -/
theorem book_gain_cost (χ k : ℝ) :
    (k - χ * 0) ^ 2 / (1 + χ) = k ^ 2 / (1 + χ) ∧ k ^ 2 / χ - χ * 0 ^ 2 = k ^ 2 / χ := by
  constructor <;> ring

/-- O&R (38), deterministic version (`S = Unit`, `z = 0`): the zero-inflation trigger
equilibrium exists iff `β ≥ χ/(1 + 2χ)`. -/
theorem trigger_deterministic_iff (β χ k : ℝ) (hχ : 0 < χ) (hk : 0 < k) (hβ0 : 0 < β)
    (hβ1 : β < 1) :
    IsReputationEqm (fun _ : Unit => 1) (fun _ => 0) β χ k (trigExp χ k 0 fun _ => 0)
      (trigCB χ k 0 fun _ => 0) ↔ χ / (1 + 2 * χ) ≤ β :=
  trigger_zero_iff _ _ β χ k hχ hk hβ0 hβ1 (fun _ => zero_le_one) (by simp)
    (by simp [expect])

/-- O&R p. 641: the one-shot outcome `π̄ = k/χ` is always a trigger equilibrium. -/
theorem trigger_oneShot_eqm (p z : S → ℝ) (β χ k : ℝ) (hχ : 0 < χ) (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) (hp : ∀ s, 0 ≤ p s) (h1 : ∑ s, p s = 1) (hz : expect p z = 0) :
    IsReputationEqm p z β χ k (trigExp χ k (k / χ) z) (trigCB χ k (k / χ) z) := by
  rw [trigger_eqm_iff p z β χ k _ hχ hβ0 hβ1 hp h1 hz]
  unfold TriggerCond
  have e1 : k - χ * (k / χ) = 0 := by field_simp; ring
  have e2 : k ^ 2 / χ - χ * (k / χ) ^ 2 = 0 := by field_simp; ring
  rw [e1, e2]
  simp

/-- T17 / fn 29: `π̲(β) < k/χ` for every `β > 0`, so a rate below the one-shot level is
always sustainable. -/
theorem lowerBound_lt (χ k β : ℝ) (hχ : 0 < χ) (hk : 0 < k) (hβ0 : 0 < β) :
    lowerBound χ k β < k / χ := by
  unfold lowerBound
  rw [div_lt_div_iff₀ (by positivity) hχ]
  nlinarith [mul_pos hk hβ0, mul_pos (mul_pos hk hβ0) hχ, mul_pos hχ hχ]

/-- T17: `π̲(β) > −k/χ` for `β < 1`. -/
theorem neg_lt_lowerBound (χ k β : ℝ) (hχ : 0 < χ) (hk : 0 < k) (hβ0 : 0 ≤ β) (hβ1 : β < 1) :
    -(k / χ) < lowerBound χ k β := by
  have hcb : 0 < χ + β := by linarith
  have : lowerBound χ k β + k / χ = 2 * k * (1 - β) / (χ + β) := by
    unfold lowerBound
    field_simp
    ring
  have : 0 < 2 * k * (1 - β) / (χ + β) := div_pos (by nlinarith) hcb
  linarith

/-- T17: `π̲(β) → −k/χ` as `β → 1`. -/
theorem lowerBound_tendsto (χ k : ℝ) (hχ : 0 < χ) :
    Tendsto (lowerBound χ k) (𝓝 1) (𝓝 (-(k / χ))) := by
  have hc : ContinuousAt (lowerBound χ k) 1 := by
    unfold lowerBound
    have : χ * (χ + 1) ≠ 0 := by positivity
    fun_prop (disch := assumption)
  have : lowerBound χ k 1 = -(k / χ) := by
    unfold lowerBound
    field_simp
    ring
  rw [← this]
  exact hc.tendsto

/-- O&R p. 641 ("even negative expected inflation rates are sustainable"), T17: some negative
target is sustainable iff `β > χ/(1 + 2χ)`. -/
theorem negative_sustainable_iff (p z : S → ℝ) (β χ k : ℝ) (hχ : 0 < χ) (hk : 0 < k)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hp : ∀ s, 0 ≤ p s) (h1 : ∑ s, p s = 1)
    (hz : expect p z = 0) :
    (∃ πbar < 0, IsReputationEqm p z β χ k (trigExp χ k πbar z) (trigCB χ k πbar z)) ↔
      χ / (1 + 2 * χ) < β := by
  have hlb : lowerBound χ k β < 0 ↔ χ / (1 + 2 * χ) < β := by
    unfold lowerBound
    rw [div_lt_iff₀ (by positivity), zero_mul, div_lt_iff₀ (by positivity)]
    constructor <;> intro h <;> nlinarith
  rw [← hlb]
  constructor
  · rintro ⟨πbar, hneg, heq⟩
    rw [trigger_eqm_iff_bounds p z β χ k πbar hχ hk hβ0 hβ1 hp h1 hz] at heq
    linarith [heq.1]
  · intro h
    refine ⟨lowerBound χ k β, h, ?_⟩
    rw [trigger_eqm_iff_bounds p z β χ k _ hχ hk hβ0 hβ1 hp h1 hz]
    exact ⟨le_rfl, (lowerBound_lt χ k β hχ hk hβ0).le⟩

/-- O&R p. 641 (multiplicity): once zero inflation is sustainable, so is every rate in
`[0, k/χ]` (indeed in `[π̲(β), k/χ]`), including the one-shot rate. -/
theorem trigger_multiplicity (p z : S → ℝ) (β χ k πbar : ℝ) (hχ : 0 < χ) (hk : 0 < k)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hp : ∀ s, 0 ≤ p s) (h1 : ∑ s, p s = 1)
    (hz : expect p z = 0)
    (h0 : IsReputationEqm p z β χ k (trigExp χ k 0 z) (trigCB χ k 0 z))
    (hπ0 : 0 ≤ πbar) (hπ1 : πbar ≤ k / χ) :
    IsReputationEqm p z β χ k (trigExp χ k πbar z) (trigCB χ k πbar z) := by
  rw [trigger_eqm_iff_bounds p z β χ k 0 hχ hk hβ0 hβ1 hp h1 hz] at h0
  rw [trigger_eqm_iff_bounds p z β χ k πbar hχ hk hβ0 hβ1 hp h1 hz]
  exact ⟨h0.1.trans hπ0, hπ1⟩

/-! ## One-period punishments (fn 29) -/

/-- O&R fn 29: the last period had no surprise (vacuous at the initial history). -/
def LastOK (χ : ℝ) (z : S → ℝ) : Hist S → Prop
  | [] => True
  | x :: _ => x.1 = x.2.1 + z x.2.2 / (1 + χ)

/-- O&R fn 29: expectations with a one-period punishment interval. -/
noncomputable def exp1 (χ k πbar : ℝ) (z : S → ℝ) (h : Hist S) : ℝ := by
  classical exact if LastOK χ z h then πbar else k / χ

/-- O&R fn 29: the bank's strategy with one-period punishments. -/
noncomputable def cb1 (χ k πbar : ℝ) (z : S → ℝ) (h : Hist S) (s : S) : ℝ := by
  classical exact if LastOK χ z h then πbar + z s / (1 + χ) else k / χ + z s / (1 + χ)

/-- O&R fn 29: the value of the one-period-punishment profile: `W_N = V_on/(1 − β)` in the
normal state and `W_P = V_D + βW_N` in the punishment state. -/
noncomputable def val1 (p z : S → ℝ) (β χ k πbar : ℝ) (h : Hist S) : ℝ := by
  classical exact if LastOK χ z h then valueOn χ k (varZ p z) πbar / (1 - β)
    else valueOn χ k (varZ p z) (k / χ) + β * (valueOn χ k (varZ p z) πbar / (1 - β))

/-- O&R fn 29: the one-period condition `gain ≤ β·(k²/χ − χπ̄²)`. -/
def OnePeriodCond (χ k β πbar : ℝ) : Prop :=
  (k - χ * πbar) ^ 2 / (1 + χ) ≤ β * (k ^ 2 / χ - χ * πbar ^ 2)

omit [Fintype S] in
/-- O&R fn 29: the last entry of an extended history. -/
theorem lastOK_cons_iff (χ : ℝ) (z : S → ℝ) (a e : ℝ) (s : S) (h : Hist S) :
    LastOK χ z ((a, e, s) :: h) ↔ a = e + z s / (1 + χ) := Iff.rfl

omit [Fintype S] in
/-- O&R fn 29: the initial history counts as normal. -/
theorem lastOK_nil (χ : ℝ) (z : S → ℝ) : LastOK χ z ([] : Hist S) := trivial

omit [Fintype S] in
/-- O&R fn 29: expectations in the normal state. -/
theorem exp1_pos (χ k πbar : ℝ) (z : S → ℝ) (h : Hist S) (hl : LastOK χ z h) :
    exp1 χ k πbar z h = πbar := by
  unfold exp1
  simp [hl]

omit [Fintype S] in
/-- O&R fn 29: expectations in the punishment state. -/
theorem exp1_neg (χ k πbar : ℝ) (z : S → ℝ) (h : Hist S) (hl : ¬ LastOK χ z h) :
    exp1 χ k πbar z h = k / χ := by
  unfold exp1
  simp [hl]

omit [Fintype S] in
/-- O&R fn 29: the bank's play in the normal state. -/
theorem cb1_pos (χ k πbar : ℝ) (z : S → ℝ) (h : Hist S) (hl : LastOK χ z h) (s : S) :
    cb1 χ k πbar z h s = πbar + z s / (1 + χ) := by
  unfold cb1
  simp [hl]

omit [Fintype S] in
/-- O&R fn 29: the bank's play in the punishment state. -/
theorem cb1_neg (χ k πbar : ℝ) (z : S → ℝ) (h : Hist S) (hl : ¬ LastOK χ z h) (s : S) :
    cb1 χ k πbar z h s = k / χ + z s / (1 + χ) := by
  unfold cb1
  simp [hl]

/-- O&R fn 29: the value in the normal state. -/
theorem val1_pos (p z : S → ℝ) (β χ k πbar : ℝ) (h : Hist S) (hl : LastOK χ z h) :
    val1 p z β χ k πbar h = valueOn χ k (varZ p z) πbar / (1 - β) := by
  unfold val1
  simp [hl]

/-- O&R fn 29: the value in the punishment state. -/
theorem val1_neg (p z : S → ℝ) (β χ k πbar : ℝ) (h : Hist S) (hl : ¬ LastOK χ z h) :
    val1 p z β χ k πbar h =
      valueOn χ k (varZ p z) (k / χ) + β * (valueOn χ k (varZ p z) πbar / (1 - β)) := by
  unfold val1
  simp [hl]

/-- O&R fn 29: rational expectations at every history. -/
theorem one_rational (p z : S → ℝ) (χ k πbar : ℝ) (h1 : ∑ s, p s = 1) (hz : expect p z = 0)
    (h : Hist S) : exp1 χ k πbar z h = expect p (cb1 χ k πbar z h) := by
  by_cases hl : LastOK χ z h
  · rw [exp1_pos χ k πbar z h hl, funext (cb1_pos χ k πbar z h hl),
      expect_const_add_shock p z χ πbar h1 hz]
  · rw [exp1_neg χ k πbar z h hl, funext (cb1_neg χ k πbar z h hl),
      expect_const_add_shock p z χ _ h1 hz]

/-- O&R fn 29: the one-period value satisfies the Bellman equality. -/
theorem one_bellman_eq (p z : S → ℝ) (β χ k πbar : ℝ) (hχ : 0 < χ) (hβ1 : β < 1)
    (h1 : ∑ s, p s = 1) (hz : expect p z = 0) (h : Hist S) :
    bellman p z β χ k (exp1 χ k πbar z) (val1 p z β χ k πbar) h (cb1 χ k πbar z h) =
      val1 p z β χ k πbar h := by
  have hχ1 : 0 < 1 + χ := by linarith
  rw [bellman_eq_expect]
  by_cases hl : LastOK χ z h
  · have hpt : ∀ s, bgLoss χ k (cb1 χ k πbar z h s) (exp1 χ k πbar z h) (z s) +
        β * val1 p z β χ k πbar ((cb1 χ k πbar z h s, exp1 χ k πbar z h, s) :: h) =
        onLoss χ k πbar (z s) + β * (valueOn χ k (varZ p z) πbar / (1 - β)) := by
      intro s
      rw [cb1_pos χ k πbar z h hl, exp1_pos χ k πbar z h hl,
        val1_pos p z β χ k πbar _ ((lastOK_cons_iff χ z _ _ s h).2 rfl)]
      rfl
    rw [expect_congr' p _ _ hpt, expect_add, expect_onLoss p z χ k πbar hχ1 h1 hz,
      expect_const p h1, val1_pos p z β χ k πbar h hl]
    exact (div_one_sub_eq _ β hβ1).symm
  · have hpt : ∀ s, bgLoss χ k (cb1 χ k πbar z h s) (exp1 χ k πbar z h) (z s) +
        β * val1 p z β χ k πbar ((cb1 χ k πbar z h s, exp1 χ k πbar z h, s) :: h) =
        onLoss χ k (k / χ) (z s) + β * (valueOn χ k (varZ p z) πbar / (1 - β)) := by
      intro s
      rw [cb1_neg χ k πbar z h hl, exp1_neg χ k πbar z h hl,
        val1_pos p z β χ k πbar _ ((lastOK_cons_iff χ z _ _ s h).2 rfl)]
      rfl
    rw [expect_congr' p _ _ hpt, expect_add, expect_onLoss p z χ k (k / χ) hχ1 h1 hz,
      expect_const p h1, val1_neg p z β χ k πbar h hl]

/-- O&R fn 29: under the one-period condition, the Bellman inequality holds for every
action rule. -/
theorem one_bellman_le (p z : S → ℝ) (β χ k πbar : ℝ) (hχ : 0 < χ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hp : ∀ s, 0 ≤ p s) (h1 : ∑ s, p s = 1) (hz : expect p z = 0)
    (hcond : OnePeriodCond χ k β πbar) (h : Hist S) (a : S → ℝ) :
    val1 p z β χ k πbar h ≤
      bellman p z β χ k (exp1 χ k πbar z) (val1 p z β χ k πbar) h a := by
  have hχ1 : 0 < 1 + χ := by linarith
  have hD : 0 < 1 - β := by linarith
  rw [bellman_eq_expect]
  set VN := valueOn χ k (varZ p z) πbar
  set VD := valueOn χ k (varZ p z) (k / χ)
  have hc2 : VD - VN = k ^ 2 / χ - χ * πbar ^ 2 := by
    have := valueDiscretion_sub_valueOn χ k (varZ p z) πbar
    rwa [← valueOn_discretion χ k (varZ p z) hχ] at this
  have hgain : 0 ≤ (k - χ * πbar) ^ 2 / (1 + χ) := by positivity
  unfold OnePeriodCond at hcond
  have hPN : VD + β * (VN / (1 - β)) - VN / (1 - β) = VD - VN := by
    field_simp
    ring
  have hVDN : 0 ≤ VD - VN := by
    rw [hc2]
    by_contra hneg
    push Not at hneg
    nlinarith
  by_cases hl : LastOK χ z h
  · have hpt : ∀ s, onLoss χ k πbar (z s) + β * (VN / (1 - β)) ≤
        bgLoss χ k (a s) (exp1 χ k πbar z h) (z s) +
          β * val1 p z β χ k πbar ((a s, exp1 χ k πbar z h, s) :: h) := by
      intro s
      rw [exp1_pos χ k πbar z h hl]
      by_cases ha : a s = πbar + z s / (1 + χ)
      · rw [val1_pos p z β χ k πbar _ ((lastOK_cons_iff χ z _ _ s h).2 ha), ha]
        rfl
      · have hn : ¬ LastOK χ z ((a s, πbar, s) :: h) := ha
        rw [val1_neg p z β χ k πbar _ hn]
        have hm := minLoss_le χ k (a s) πbar (z s) hχ1
        have hg := onLoss_sub_minLoss χ k πbar (z s) hχ1
        have : β * (VD + β * (VN / (1 - β))) - β * (VN / (1 - β)) = β * (VD - VN) := by
          rw [← hPN]
          ring
        rw [hc2] at this
        linarith
    calc val1 p z β χ k πbar h
        = expect p (fun s => onLoss χ k πbar (z s) + β * (VN / (1 - β))) := by
          rw [expect_add, expect_onLoss p z χ k πbar hχ1 h1 hz, expect_const p h1,
            val1_pos p z β χ k πbar h hl]
          exact div_one_sub_eq _ β hβ1
      _ ≤ _ := expect_mono p _ _ hp hpt
  · have hpt : ∀ s, onLoss χ k (k / χ) (z s) + β * (VN / (1 - β)) ≤
        bgLoss χ k (a s) (exp1 χ k πbar z h) (z s) +
          β * val1 p z β χ k πbar ((a s, exp1 χ k πbar z h, s) :: h) := by
      intro s
      rw [exp1_neg χ k πbar z h hl, onLoss_discretion χ k (z s) hχ]
      have hm := minLoss_le χ k (a s) (k / χ) (z s) hχ1
      by_cases ha : a s = k / χ + z s / (1 + χ)
      · rw [val1_pos p z β χ k πbar _ ((lastOK_cons_iff χ z _ _ s h).2 ha)]
        linarith
      · have hn : ¬ LastOK χ z ((a s, k / χ, s) :: h) := ha
        rw [val1_neg p z β χ k πbar _ hn]
        have : 0 ≤ β * (VD + β * (VN / (1 - β)) - VN / (1 - β)) := by
          rw [hPN]
          exact mul_nonneg hβ0.le hVDN
        nlinarith
    calc val1 p z β χ k πbar h
        = expect p (fun s => onLoss χ k (k / χ) (z s) + β * (VN / (1 - β))) := by
          rw [expect_add, expect_onLoss p z χ k (k / χ) hχ1 h1 hz, expect_const p h1,
            val1_neg p z β χ k πbar h hl]
      _ ≤ _ := expect_mono p _ _ hp hpt

/-- O&R fn 29: the one-period value is bounded. -/
theorem val1_abs_le (p z : S → ℝ) (β χ k πbar : ℝ) (h : Hist S) :
    |val1 p z β χ k πbar h| ≤ |valueOn χ k (varZ p z) πbar / (1 - β)| +
      |valueOn χ k (varZ p z) (k / χ) + β * (valueOn χ k (varZ p z) πbar / (1 - β))| := by
  by_cases hl : LastOK χ z h
  · rw [val1_pos p z β χ k πbar h hl]
    linarith [abs_nonneg (valueOn χ k (varZ p z) (k / χ) +
      β * (valueOn χ k (varZ p z) πbar / (1 - β)))]
  · rw [val1_neg p z β χ k πbar h hl]
    linarith [abs_nonneg (valueOn χ k (varZ p z) πbar / (1 - β))]

/-- O&R fn 29: cheating once at the empty history, then one period of punishment and back
to normal: value `V_on − gain + β(V_D + β·V_on/(1 − β))`, provided `k ≠ χπ̄`. -/
theorem one_rootDev_value (p z : S → ℝ) (β χ k πbar : ℝ) (hχ : 0 < χ) (h1 : ∑ s, p s = 1)
    (hz : expect p z = 0) (hne : k ≠ χ * πbar) :
    bellman p z β χ k (exp1 χ k πbar z) (val1 p z β χ k πbar) []
        (fun s => bestResponse χ k πbar (z s)) =
      valueOn χ k (varZ p z) πbar - (k - χ * πbar) ^ 2 / (1 + χ) +
        β * (valueOn χ k (varZ p z) (k / χ) + β * (valueOn χ k (varZ p z) πbar / (1 - β))) := by
  have hχ1 : 0 < 1 + χ := by linarith
  rw [bellman_eq_expect, exp1_pos χ k πbar z [] (lastOK_nil χ z)]
  have hpt : ∀ s, bgLoss χ k (bestResponse χ k πbar (z s)) πbar (z s) +
      β * val1 p z β χ k πbar ((bestResponse χ k πbar (z s), πbar, s) :: []) =
      (onLoss χ k πbar (z s) - (k - χ * πbar) ^ 2 / (1 + χ)) +
        β * (valueOn χ k (varZ p z) (k / χ) + β * (valueOn χ k (varZ p z) πbar / (1 - β))) := by
    intro s
    have hn : ¬ LastOK χ z ((bestResponse χ k πbar (z s), πbar, s) :: []) := fun hc2 =>
      hne ((bestResponse_eq_onPath_iff χ k πbar (z s) hχ1).1 hc2)
    rw [val1_neg p z β χ k πbar _ hn, ← onLoss_sub_minLoss χ k πbar (z s) hχ1,
      bgLoss_bestResponse χ k πbar (z s) hχ1, minLoss]
    ring
  rw [expect_congr' p _ _ hpt, expect_add, expect_sub, expect_onLoss p z χ k πbar hχ1 h1 hz,
    expect_const p h1, expect_const p h1]

/-- O&R fn 29 (exact form): with a one-period punishment interval, the profile with target
`π̄` is a reputational equilibrium iff `(k − χπ̄)²/(1 + χ) ≤ β(k²/χ − χπ̄²)`. -/
theorem onePeriod_eqm_iff (p z : S → ℝ) (β χ k πbar : ℝ) (hχ : 0 < χ) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hp : ∀ s, 0 ≤ p s) (h1 : ∑ s, p s = 1) (hz : expect p z = 0) :
    IsReputationEqm p z β χ k (exp1 χ k πbar z) (cb1 χ k πbar z) ↔
      OnePeriodCond χ k β πbar := by
  set Wbar := |valueOn χ k (varZ p z) πbar / (1 - β)| +
      |valueOn χ k (varZ p z) (k / χ) + β * (valueOn χ k (varZ p z) πbar / (1 - β))|
  constructor
  · intro heqm
    by_contra hc
    unfold OnePeriodCond at hc
    push Not at hc
    have hne : k ≠ χ * πbar := by
      intro hk
      have e1 : k - χ * πbar = 0 := by rw [hk]; ring
      have e2 : k ^ 2 / χ - χ * πbar ^ 2 = 0 := by rw [hk]; field_simp; ring
      rw [e1, e2] at hc
      simp at hc
    have hdev := hasExpPV_rootDev p z β χ k hp h1 hβ0.le hβ1 (exp1 χ k πbar z)
      (val1 p z β χ k πbar) Wbar (val1_abs_le p z β χ k πbar) (cb1 χ k πbar z)
      (one_bellman_eq p z β χ k πbar hχ hβ1 h1 hz) (fun s => bestResponse χ k πbar (z s))
    have htrig := tendsto_truncCost_of_bellman_eq p z β χ k hp h1 hβ0.le hβ1
      (exp1 χ k πbar z) (val1 p z β χ k πbar) Wbar (val1_abs_le p z β χ k πbar)
      (cb1 χ k πbar z) (one_bellman_eq p z β χ k πbar hχ hβ1 h1 hz) []
    refine not_isReputationEqm_of_better p z β χ k _ _ _ [] _ _ htrig hdev ?_ heqm
    rw [one_rootDev_value p z β χ k πbar hχ h1 hz hne,
      val1_pos p z β χ k πbar [] (lastOK_nil χ z)]
    have hc2 := valueDiscretion_sub_valueOn χ k (varZ p z) πbar
    rw [← valueOn_discretion χ k (varZ p z) hχ] at hc2
    have hD : (1 - β) ≠ 0 := by linarith
    have e : valueOn χ k (varZ p z) πbar / (1 - β) -
        (valueOn χ k (varZ p z) πbar - (k - χ * πbar) ^ 2 / (1 + χ) +
          β * (valueOn χ k (varZ p z) (k / χ) +
            β * (valueOn χ k (varZ p z) πbar / (1 - β)))) =
        (k - χ * πbar) ^ 2 / (1 + χ) - β * (k ^ 2 / χ - χ * πbar ^ 2) := by
      rw [← hc2]
      field_simp
      ring
    linarith
  · intro hcond
    exact isReputationEqm_of_bellman p z β χ k hp h1 hβ0.le hβ1 (exp1 χ k πbar z)
      (val1 p z β χ k πbar) Wbar (val1_abs_le p z β χ k πbar) (cb1 χ k πbar z)
      (one_rational p z χ k πbar h1 hz) (one_bellman_eq p z β χ k πbar hχ hβ1 h1 hz)
      (one_bellman_le p z β χ k πbar hχ hβ0 hβ1 hp h1 hz hcond)

/-- O&R fn 29: the lowest target sustainable with one-period punishments,
`k(χ − β(1 + χ))/(χ(χ + β(1 + χ)))`. -/
noncomputable def lowerBound1 (χ k β : ℝ) : ℝ :=
  k * (χ - β * (1 + χ)) / (χ * (χ + β * (1 + χ)))

/-- O&R fn 29 (exact sustainable set): with one-period punishments the profile with target
`π̄` is an equilibrium iff `lowerBound1 ≤ π̄ ≤ k/χ`. -/
theorem onePeriod_eqm_iff_bounds (p z : S → ℝ) (β χ k πbar : ℝ) (hχ : 0 < χ) (hk : 0 < k)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hp : ∀ s, 0 ≤ p s) (h1 : ∑ s, p s = 1)
    (hz : expect p z = 0) :
    IsReputationEqm p z β χ k (exp1 χ k πbar z) (cb1 χ k πbar z) ↔
      lowerBound1 χ k β ≤ πbar ∧ πbar ≤ k / χ := by
  rw [onePeriod_eqm_iff p z β χ k πbar hχ hβ0 hβ1 hp h1 hz]
  have hχ1 : 0 < 1 + χ := by linarith
  have hcb : 0 < χ + β * (1 + χ) := by positivity
  set x0 := k * (χ - β * (1 + χ)) / (χ + β * (1 + χ)) with hx0
  have hx0k : x0 < k := by
    rw [hx0, div_lt_iff₀ hcb]
    nlinarith [mul_pos hβ0 hχ1]
  have key : OnePeriodCond χ k β πbar ↔ 0 ≤ (k - χ * πbar) * (χ * πbar - x0) := by
    unfold OnePeriodCond
    have e : β * (k ^ 2 / χ - χ * πbar ^ 2) - (k - χ * πbar) ^ 2 / (1 + χ) =
        (χ + β * (1 + χ)) / (χ * (1 + χ)) * ((k - χ * πbar) * (χ * πbar - x0)) := by
      rw [hx0]
      field_simp
      ring
    have hpos : 0 < (χ + β * (1 + χ)) / (χ * (1 + χ)) := by positivity
    constructor
    · intro h
      have : 0 ≤ (χ + β * (1 + χ)) / (χ * (1 + χ)) * ((k - χ * πbar) * (χ * πbar - x0)) := by
        linarith
      exact (mul_nonneg_iff_of_pos_left hpos).1 this
    · intro h
      have := mul_nonneg hpos.le h
      linarith
  rw [key, between_iff (χ * πbar) x0 k hx0k]
  have e1 : x0 ≤ χ * πbar ↔ lowerBound1 χ k β ≤ πbar := by
    unfold lowerBound1
    rw [hx0, div_le_iff₀ hcb, div_le_iff₀ (by positivity)]
    constructor <;> intro h <;> nlinarith
  have e2 : χ * πbar ≤ k ↔ πbar ≤ k / χ := by
    rw [le_div_iff₀ hχ, mul_comm]
  rw [e1, e2]

/-- O&R fn 29: even with a one-period punishment interval, some expected inflation rate
strictly below the one-shot level `k/χ` is always sustainable (`0 < β < 1`). -/
theorem onePeriod_below_oneShot (p z : S → ℝ) (β χ k : ℝ) (hχ : 0 < χ) (hk : 0 < k)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hp : ∀ s, 0 ≤ p s) (h1 : ∑ s, p s = 1)
    (hz : expect p z = 0) :
    ∃ πbar < k / χ, IsReputationEqm p z β χ k (exp1 χ k πbar z) (cb1 χ k πbar z) := by
  have hχ1 : 0 < 1 + χ := by linarith
  have hlt : lowerBound1 χ k β < k / χ := by
    unfold lowerBound1
    rw [div_lt_div_iff₀ (by positivity) hχ]
    nlinarith [mul_pos (mul_pos hk hβ0) hχ1, mul_pos hχ hχ]
  refine ⟨lowerBound1 χ k β, hlt, ?_⟩
  rw [onePeriod_eqm_iff_bounds p z β χ k _ hχ hk hβ0 hβ1 hp h1 hz]
  exact ⟨le_rfl, hlt.le⟩

/-! ## Finite horizon: unravelling (pp. 640–641, T19) -/

/-- O&R pp. 640–641: a subgame-perfect equilibrium of the `T`-period game: at every history
of length `< T`, expectations are rational and `σ` minimises the expected loss over the
remaining `T − length` periods against every alternative strategy. -/
def IsFiniteEqm (p z : S → ℝ) (β χ k : ℝ) (T : ℕ) (ε : Hist S → ℝ) (σ : Hist S → S → ℝ) :
    Prop :=
  ∀ h : Hist S, h.length < T → ε h = expect p (σ h) ∧
    ∀ σ', truncCost p z β χ k ε σ (T - h.length) h ≤ truncCost p z β χ k ε σ' (T - h.length) h

/-- O&R pp. 640–641: the value of `j` periods of one-shot play, `V_D(1 + β + ⋯ + β^{j−1})`. -/
noncomputable def staticVal (p z : S → ℝ) (β χ k : ℝ) (j : ℕ) : ℝ :=
  valueDiscretion χ k (varZ p z) * ∑ i ∈ Finset.range j, β ^ i

/-- O&R pp. 640–641: if play is the one-shot equilibrium at every history of length in
`[len h, len h + j)`, then the `j`-period cost from `h` is `staticVal j`. -/
theorem truncCost_static (p z : S → ℝ) (β χ k : ℝ) (hχ : 0 < χ) (hp : ∀ s, 0 ≤ p s)
    (h1 : ∑ s, p s = 1) (hz : expect p z = 0) (ε : Hist S → ℝ) (σ : Hist S → S → ℝ) :
    ∀ j (h : Hist S), (∀ g : Hist S, h.length ≤ g.length → g.length < h.length + j →
      ε g = k / χ ∧ ∀ s, 0 < p s → σ g s = k / χ + z s / (1 + χ)) →
      truncCost p z β χ k ε σ j h = staticVal p z β χ k j := by
  have hχ1 : 0 < 1 + χ := by linarith
  intro j
  induction j with
  | zero => intro h _; simp [truncCost, staticVal]
  | succ j ih =>
    intro h hst
    obtain ⟨he, hs⟩ := hst h le_rfl (by omega)
    have hcont : ∀ s, truncCost p z β χ k ε σ j ((σ h s, ε h, s) :: h) =
        staticVal p z β χ k j := fun s =>
      ih _ fun g hg1 hg2 => hst g (by simp at hg1; omega) (by simp at hg2; omega)
    rw [truncCost_succ, bellman_eq_expect]
    have : expect p (fun s => bgLoss χ k (σ h s) (ε h) (z s) +
        β * truncCost p z β χ k ε σ j ((σ h s, ε h, s) :: h)) =
        expect p (fun s => onLoss χ k (k / χ) (z s) + β * staticVal p z β χ k j) := by
      refine expect_congr_support p _ _ (fun s hps => ?_) hp
      rw [hcont s, he, hs s hps]
      rfl
    rw [this, expect_add, expect_onLoss p z χ k (k / χ) hχ1 h1 hz, expect_const p h1,
      valueOn_discretion χ k _ hχ]
    unfold staticVal
    rw [Finset.sum_range_succ', pow_zero, Finset.mul_sum, Finset.mul_sum]
    simp only [pow_succ]
    rw [mul_add, mul_one, Finset.mul_sum]
    rw [add_comm]
    congr 1
    exact Finset.sum_congr rfl fun i _ => by ring

/-- O&R pp. 640–641: with one-shot expectations `k/χ` at every history, no strategy can do
better than `staticVal`. -/
theorem truncCost_ge_static (p z : S → ℝ) (β χ k : ℝ) (hχ : 0 < χ) (hβ : 0 ≤ β)
    (hp : ∀ s, 0 ≤ p s) (h1 : ∑ s, p s = 1) (hz : expect p z = 0) (σ : Hist S → S → ℝ) :
    ∀ j h, staticVal p z β χ k j ≤ truncCost p z β χ k (fun _ => k / χ) σ j h := by
  have hχ1 : 0 < 1 + χ := by linarith
  intro j
  induction j with
  | zero => intro h; simp [truncCost, staticVal]
  | succ j ih =>
    intro h
    rw [truncCost_succ, bellman_eq_expect]
    have hlow : staticVal p z β χ k (j + 1) =
        expect p (fun s => onLoss χ k (k / χ) (z s) + β * staticVal p z β χ k j) := by
      rw [expect_add, expect_onLoss p z χ k (k / χ) hχ1 h1 hz, expect_const p h1,
        valueOn_discretion χ k _ hχ]
      unfold staticVal
      rw [Finset.sum_range_succ', pow_zero, mul_add, mul_one, Finset.mul_sum, Finset.mul_sum,
        Finset.mul_sum, add_comm]
      congr 1
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hlow]
    refine expect_mono p _ _ hp fun s => ?_
    have := minLoss_le χ k (σ h s) (k / χ) (z s) hχ1
    rw [← onLoss_discretion χ k (z s) hχ] at this
    have := mul_le_mul_of_nonneg_left (ih ((σ h s, k / χ, s) :: h)) hβ
    linarith

/-- O&R pp. 640–641 (T19, existence): one-shot play `πᵉ = k/χ`, `π = k/χ + z/(1 + χ)` at
every history is a subgame-perfect equilibrium of the `T`-period game. -/
theorem finite_static_eqm (p z : S → ℝ) (β χ k : ℝ) (hχ : 0 < χ) (hβ : 0 ≤ β)
    (hp : ∀ s, 0 ≤ p s) (h1 : ∑ s, p s = 1) (hz : expect p z = 0) (T : ℕ) :
    IsFiniteEqm p z β χ k T (fun _ => k / χ) (fun _ s => k / χ + z s / (1 + χ)) := by
  intro h _
  refine ⟨?_, fun σ' => ?_⟩
  · have : expect p (fun s => k / χ + z s / (1 + χ)) =
        expect p (fun s => k / χ + (1 / (1 + χ)) * z s) := by
      unfold expect
      exact Finset.sum_congr rfl fun s _ => by ring
    rw [this, expect_add, expect_const p h1, expect_const_mul, hz, mul_zero, add_zero]
  · rw [truncCost_static p z β χ k hχ hp h1 hz _ _ _ h fun g _ _ => ⟨rfl, fun _ _ => rfl⟩]
    exact truncCost_ge_static p z β χ k hχ hβ hp h1 hz σ' _ h

/-- O&R pp. 640–641 (T19, uniqueness: the trigger equilibrium unravels): in **every**
subgame-perfect equilibrium of the `T`-period game, at every history with periods left,
`πᵉ = k/χ` and `π = k/χ + z/(1 + χ)` in every state of positive probability. -/
theorem finite_eqm_unique (p z : S → ℝ) (β χ k : ℝ) (hχ : 0 < χ) (hp : ∀ s, 0 ≤ p s)
    (h1 : ∑ s, p s = 1) (hz : expect p z = 0) (T : ℕ) (ε : Hist S → ℝ)
    (σ : Hist S → S → ℝ) (heqm : IsFiniteEqm p z β χ k T ε σ) :
    ∀ h : Hist S, h.length < T →
      ε h = k / χ ∧ ∀ s, 0 < p s → σ h s = k / χ + z s / (1 + χ) := by
  have hχ1 : 0 < 1 + χ := by linarith
  -- `Q m`: the claim holds at every history with at most `m` periods remaining.
  suffices hQ : ∀ m, ∀ g : Hist S, T - m ≤ g.length → g.length < T →
      ε g = k / χ ∧ ∀ s, 0 < p s → σ g s = k / χ + z s / (1 + χ) from
    fun h hh => hQ T h (by omega) hh
  intro m
  induction m with
  | zero => intro g hg1 hg2; omega
  | succ m ih =>
    intro h hh1 hh2
    by_cases hlen : T - m ≤ h.length
    · exact ih h hlen hh2
    have hlenEq : h.length + 1 + m = T := by omega
    have hstat : ∀ g : Hist S, h.length + 1 ≤ g.length → g.length < h.length + 1 + m →
        ε g = k / χ ∧ ∀ s, 0 < p s → σ g s = k / χ + z s / (1 + χ) :=
      fun g hg1 hg2 => ih g (by omega) (by omega)
    obtain ⟨hre, hopt⟩ := heqm h hh2
    have hTm : T - h.length = m + 1 := by omega
    -- the cost of any rule `a` at `h`, followed by `σ`
    have hcost : ∀ a : S → ℝ,
        truncCost p z β χ k ε (fun g s => if g.length = h.length then a s else σ g s)
          (T - h.length) h =
        expect p (fun s => bgLoss χ k (a s) (ε h) (z s) + β * staticVal p z β χ k m) := by
      intro a
      rw [hTm, truncCost_succ, bellman_eq_expect]
      congr 1
      funext s
      simp only [↓reduceIte]
      congr 2
      refine truncCost_static p z β χ k hχ hp h1 hz ε _ m _ fun g hg1 hg2 => ?_
      simp only [List.length_cons] at hg1 hg2
      obtain ⟨he, hs⟩ := hstat g hg1 hg2
      refine ⟨he, fun s' hs' => ?_⟩
      have : g.length ≠ h.length := by omega
      simp only [this, ↓reduceIte]
      exact hs s' hs'
    have hσ : truncCost p z β χ k ε σ (T - h.length) h =
        expect p (fun s => bgLoss χ k (σ h s) (ε h) (z s) + β * staticVal p z β χ k m) := by
      rw [hTm, truncCost_succ, bellman_eq_expect]
      congr 1
      funext s
      congr 2
      refine truncCost_static p z β χ k hχ hp h1 hz ε σ m _ fun g hg1 hg2 => ?_
      simp only [List.length_cons] at hg1 hg2
      exact hstat g hg1 hg2
    have hmin : ∀ a : S → ℝ, expect p (fun s => bgLoss χ k (σ h s) (ε h) (z s)) ≤
        expect p (fun s => bgLoss χ k (a s) (ε h) (z s)) := by
      intro a
      have := hopt (fun g s => if g.length = h.length then a s else σ g s)
      rw [hσ, hcost a, expect_add, expect_add, expect_const p h1] at this
      linarith
    have hbr : ∀ s, 0 < p s → σ h s = bestResponse χ k (ε h) (z s) := by
      intro s0 hs0
      classical
      have hle := hmin (fun s => if s = s0 then bestResponse χ k (ε h) (z s0) else σ h s)
      have hdiff : expect p (fun s => bgLoss χ k (σ h s) (ε h) (z s)) -
          expect p (fun s => bgLoss χ k
            (if s = s0 then bestResponse χ k (ε h) (z s0) else σ h s) (ε h) (z s)) =
          p s0 * (bgLoss χ k (σ h s0) (ε h) (z s0) -
            bgLoss χ k (bestResponse χ k (ε h) (z s0)) (ε h) (z s0)) := by
        rw [← expect_sub]
        unfold expect
        rw [Finset.sum_eq_single s0]
        · simp
        · intro b _ hb
          simp [hb]
        · intro hn
          exact absurd (Finset.mem_univ s0) hn
      have hneg : p s0 * (bgLoss χ k (σ h s0) (ε h) (z s0) -
          bgLoss χ k (bestResponse χ k (ε h) (z s0)) (ε h) (z s0)) ≤ 0 := by linarith
      exact eq_bestResponse_of_le χ k _ _ _ hχ1
        (sub_nonpos.1 (nonpos_of_mul_nonpos_right hneg hs0))
    have hE : expect p (fun s => bestResponse χ k (ε h) (z s)) = (k + ε h) / (1 + χ) := by
      have : expect p (fun s => bestResponse χ k (ε h) (z s)) =
          expect p (fun s => (k + ε h) / (1 + χ) + (1 / (1 + χ)) * z s) := by
        unfold expect bestResponse
        exact Finset.sum_congr rfl fun s _ => by ring
      rw [this, expect_add, expect_const p h1, expect_const_mul, hz, mul_zero, add_zero]
    have h2 : ε h = (k + ε h) / (1 + χ) := by
      rw [← hE]
      exact hre.trans (expect_congr_support p _ _ hbr hp)
    have hpe : ε h = k / χ := by
      rw [eq_div_iff hχ1.ne'] at h2
      rw [eq_div_iff hχ.ne']
      linarith
    refine ⟨hpe, fun s hs => ?_⟩
    rw [hbr s hs, hpe]
    unfold bestResponse
    field_simp
    ring

end ObstfeldRogoff.NominalRigidities.ReputationEquilibria

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Institutional resolutions: the conservative central banker and the Walsh contract

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §9.5.2
(pp. 641–644), eqs. (40)–(44), Exercise 4 (p. 658) and the application "Central bank
independence and inflation" (pp. 646–647).

* (40)–(41): a banker with weight `c = χᶜᴮ > 0` produces the unique equilibrium
  `πᵉ = k/c`, `π = k/c + z/(1 + c)`; society's expected loss is
  `L(c) = k² + χk²/c² + (c² + χ)σ²/(1 + c)²`, with
  `L′(c) = 2σ²(c − χ)/(1 + c)³ − 2χk²/c³`.
* Rogoff's theorem (p. 642), in full: for `k > 0`, `σ² > 0`, `L` has a **unique** global
  minimiser `c*` on `(0, ∞)`, and `χ < c* < ∞`; `L` is strictly decreasing on `(0, c*]` and
  strictly increasing on `[c*, ∞)` (the unimodality proof goes through the strictly
  increasing function `h(c) = (c − χ)c³/(1 + c)³` and the intermediate value theorem);
  `c*` is characterised by `σ²h(c*) = χk²` and increases with `k²/σ²`;
  `L(c*) < L(χ) = V_D` and `L(c*) < lim_{c→∞} L = k² + σ²`, but `L(c) > V_C` for every `c`.
  Degenerate cases: `k = 0` gives `c* = χ`; `σ² = 0` gives `L` strictly decreasing with
  infimum `k²` not attained ("`χᶜᴮ = ∞`").
* Walsh (42)–(44): the linear contract `2ωπ` shifts the equilibrium to
  `πᵉ = (k − ω)/χ`, `π = (k − ω)/χ + z/(1 + χ)`; society's loss is `V_C + (k − ω)²/χ`, so
  `ω = k` is the unique optimal contract and implements the commitment rule (36).
* Exercise 4: with a random weight `λ` on the bonus (`E λ = 1`, `Var λ = σ_λ²`, `λ`
  uncorrelated with `z`): unique equilibrium, expected social loss
  `k² + (k − ω)²/χ + χσ_z²/(1 + χ) + ω²σ_λ²/(1 + χ)`, unique optimum
  `ω* = k(1 + χ)/(1 + χ + χσ_λ²) < k`.
* CBI regression (p. 646): the slope's t-ratio `6.02/2.35` exceeds the 5% critical value
  `2.131` (15 degrees of freedom), so "significant" is correct.
-/

namespace ObstfeldRogoff.NominalRigidities.CentralBankDelegation

open Filter Topology Set
open ObstfeldRogoff.NominalRigidities.BarroGordon

variable {S : Type*} [Fintype S]

/-! ## The conservative central banker, (40)–(41) -/

/-- O&R (40)–(41), pp. 641–642: with a banker of weight `c > 0` the one-shot equilibrium is
unique: `πᵉ = k/c` and `π = k/c + z/(1 + c)`. -/
theorem conservative_eqm_iff (p z : S → ℝ) (c k : ℝ) (hc : 0 < c) (h1 : ∑ s, p s = 1)
    (hz : expect p z = 0) (π : S → ℝ) (πe : ℝ) :
    IsOneShotEqm p z c k π πe ↔ πe = k / c ∧ ∀ s, π s = k / c + z s / (1 + c) :=
  oneShot_eqm_iff p z c k hc h1 hz π πe

/-- O&R p. 642: society's expected loss when the banker has weight `c`,
`L(c) = k² + χk²/c² + (c² + χ)σ²/(1 + c)²`. -/
noncomputable def socialLoss (χ k σ2 c : ℝ) : ℝ :=
  k ^ 2 + χ * k ^ 2 / c ^ 2 + (c ^ 2 + χ) * σ2 / (1 + c) ^ 2

/-- O&R (41), p. 642: society's expected loss (31) under the banker's equilibrium policy is
`socialLoss`. -/
theorem expLoss_conservative (p z : S → ℝ) (χ k c : ℝ) (hc : 0 < c) (h1 : ∑ s, p s = 1)
    (hz : expect p z = 0) :
    expLoss p z χ k (discretionRule c k z) = socialLoss χ k (varZ p z) c := by
  have hc1 : 0 < 1 + c := by linarith
  have hE : expect p (discretionRule c k z) = k / c := by
    have : expect p (discretionRule c k z) =
        expect p (fun s => k / c + (1 / (1 + c)) * z s) := by
      unfold expect discretionRule
      exact Finset.sum_congr rfl fun s _ => by ring
    rw [this, expect_add, expect_const p h1, expect_const_mul, hz, mul_zero, add_zero]
  rw [expLoss_decomp p z χ k h1 hz, hE]
  have e1 : expect p (fun s => (discretionRule c k z s - k / c - z s) ^ 2) =
      c ^ 2 / (1 + c) ^ 2 * varZ p z := by
    unfold varZ
    rw [← expect_const_mul]
    unfold expect discretionRule
    refine Finset.sum_congr rfl fun s _ => ?_
    field_simp
    ring
  have e2 : expect p (fun s => (discretionRule c k z s - k / c) ^ 2) =
      1 / (1 + c) ^ 2 * varZ p z := by
    unfold varZ
    rw [← expect_const_mul]
    unfold expect discretionRule
    refine Finset.sum_congr rfl fun s _ => ?_
    field_simp
    ring
  rw [e1, e2]
  unfold socialLoss
  field_simp
  ring

/-- O&R p. 642: society's own weight (`c = χ`) reproduces discretion, `L(χ) = V_D`. -/
theorem socialLoss_self (χ k σ2 : ℝ) (hχ : 0 < χ) :
    socialLoss χ k σ2 χ = valueDiscretion χ k σ2 := by
  unfold socialLoss valueDiscretion
  have : (0 : ℝ) < 1 + χ := by linarith
  field_simp
  ring

/-- O&R p. 642: the derivative `L′(c) = 2σ²(c − χ)/(1 + c)³ − 2χk²/c³` for `c > 0`. -/
theorem hasDerivAt_socialLoss (χ k σ2 c : ℝ) (hc : 0 < c) :
    HasDerivAt (socialLoss χ k σ2)
      (2 * σ2 * (c - χ) / (1 + c) ^ 3 - 2 * χ * k ^ 2 / c ^ 3) c := by
  have hc1 : 0 < 1 + c := by linarith
  have hA : HasDerivAt (fun x : ℝ => χ * k ^ 2 / x ^ 2)
      (-(χ * k ^ 2 * (2 * c)) / (c ^ 2) ^ 2) c :=
    ((hasDerivAt_const c (χ * k ^ 2)).div (hasDerivAt_pow 2 c)
      (pow_ne_zero 2 hc.ne')).congr_deriv (by norm_num)
  have hn : HasDerivAt (fun x : ℝ => (x ^ 2 + χ) * σ2) ((2 * c) * σ2) c :=
    (((hasDerivAt_pow 2 c).add_const χ).mul_const σ2).congr_deriv (by norm_num)
  have hd : HasDerivAt (fun x : ℝ => (1 + x) ^ 2) (2 * (1 + c)) c :=
    (((hasDerivAt_id' c).const_add 1).fun_pow 2).congr_deriv (by norm_num)
  have hB := hn.div hd (pow_ne_zero 2 hc1.ne')
  have h := (hA.const_add (k ^ 2)).add hB
  exact h.congr_deriv (by field_simp; ring)

/-- O&R p. 642: the sign function `g(c) = σ²(c − χ)c³ − χk²(1 + c)³`, with
`L′(c) = 2g(c)/(c³(1 + c)³)`. -/
noncomputable def signFn (χ k σ2 c : ℝ) : ℝ := σ2 * (c - χ) * c ^ 3 - χ * k ^ 2 * (1 + c) ^ 3

/-- O&R p. 642: `L′(c) = 2g(c)/(c³(1 + c)³)`. -/
theorem deriv_eq_signFn (χ k σ2 c : ℝ) (hc : 0 < c) :
    2 * σ2 * (c - χ) / (1 + c) ^ 3 - 2 * χ * k ^ 2 / c ^ 3 =
      2 * signFn χ k σ2 c / (c ^ 3 * (1 + c) ^ 3) := by
  have hc1 : 0 < 1 + c := by linarith
  unfold signFn
  field_simp

/-- O&R p. 642 (the envelope heuristic): `L′(χ) = −2k²/χ² < 0`, so raising the banker's
weight above society's is first-order beneficial. -/
theorem deriv_at_chi (χ k σ2 : ℝ) (hχ : 0 < χ) :
    2 * σ2 * (χ - χ) / (1 + χ) ^ 3 - 2 * χ * k ^ 2 / χ ^ 3 = -(2 * k ^ 2 / χ ^ 2) := by
  field_simp
  ring

/-- The unimodality proof (T20): `h(c) = (c − χ)c³/(1 + c)³`. -/
noncomputable def hFn (χ c : ℝ) : ℝ := (c - χ) * (c / (1 + c)) ^ 3

/-- T20: `h` is strictly increasing on `[χ, ∞)` (product of the nonnegative increasing `c − χ`
and the positive strictly increasing `(c/(1 + c))³`). -/
theorem hFn_strictMonoOn (χ : ℝ) (hχ : 0 < χ) : StrictMonoOn (hFn χ) (Ici χ) := by
  intro a ha b hb hab
  simp only [mem_Ici] at ha hb
  have ha0 : 0 < a := lt_of_lt_of_le hχ ha
  have hb0 : 0 < b := by linarith
  have hq : a / (1 + a) < b / (1 + b) := by
    rw [div_lt_div_iff₀ (by linarith) (by linarith)]
    nlinarith
  have hqa : 0 < a / (1 + a) := div_pos ha0 (by linarith)
  have h3 : (a / (1 + a)) ^ 3 < (b / (1 + b)) ^ 3 := by
    exact pow_lt_pow_left₀ hq hqa.le (by norm_num)
  unfold hFn
  calc (a - χ) * (a / (1 + a)) ^ 3 ≤ (a - χ) * (b / (1 + b)) ^ 3 :=
        mul_le_mul_of_nonneg_left h3.le (by linarith)
    _ < (b - χ) * (b / (1 + b)) ^ 3 :=
        mul_lt_mul_of_pos_right (by linarith) (by positivity)

/-- T20: `g(c) = (1 + c)³(σ²h(c) − χk²)`. -/
theorem signFn_eq_hFn (χ k σ2 c : ℝ) (hc : 0 < c) :
    signFn χ k σ2 c = (1 + c) ^ 3 * (σ2 * hFn χ c - χ * k ^ 2) := by
  have hc1 : 0 < 1 + c := by linarith
  unfold signFn hFn
  field_simp

/-- T20: `h` is continuous on `[0, ∞)`. -/
theorem hFn_continuousOn (χ : ℝ) : ContinuousOn (hFn χ) (Ici 0) := by
  unfold hFn
  refine ContinuousOn.mul (continuousOn_id.sub continuousOn_const) ?_
  refine ContinuousOn.pow (ContinuousOn.div continuousOn_id
    (continuousOn_const.add continuousOn_id) fun x hx => ?_) 3
  simp only [mem_Ici] at hx
  change (1 : ℝ) + x ≠ 0
  have : 0 < 1 + x := by linarith
  exact this.ne'

/-- T20 (existence of the optimum's characterisation): for `k > 0`, `σ² > 0` there is
`c* > χ` with `σ²h(c*) = χk²`. -/
theorem exists_root (χ k σ2 : ℝ) (hχ : 0 < χ) (hk : 0 < k) (hσ : 0 < σ2) :
    ∃ cstar, χ < cstar ∧ σ2 * hFn χ cstar = χ * k ^ 2 := by
  set c1 := 1 + χ + 8 * χ * k ^ 2 / σ2 with hc1
  have hq : 0 < 8 * χ * k ^ 2 / σ2 := by positivity
  have hχc1 : χ ≤ c1 := by linarith
  have hcont : ContinuousOn (hFn χ) (Icc χ c1) :=
    (hFn_continuousOn χ).mono fun x hx => by simp only [mem_Icc] at hx; simp; linarith
  have hlow : hFn χ χ = 0 := by simp [hFn]
  have hhigh : χ * k ^ 2 / σ2 ≤ hFn χ c1 := by
    unfold hFn
    have h1 : (1 : ℝ) ≤ c1 := by linarith
    have h2 : 1 / 2 ≤ c1 / (1 + c1) := by
      rw [div_le_div_iff₀ (by norm_num) (by linarith)]
      linarith
    have h3 : (1 / 2 : ℝ) ^ 3 ≤ (c1 / (1 + c1)) ^ 3 := pow_le_pow_left₀ (by norm_num) h2 3
    have h4 : c1 - χ = 1 + 8 * χ * k ^ 2 / σ2 := by rw [hc1]; ring
    rw [h4]
    have h5 : 8 * (χ * k ^ 2 / σ2) = 8 * χ * k ^ 2 / σ2 := by ring
    nlinarith [h3, hq]
  obtain ⟨c, hc, hcv⟩ := intermediate_value_Icc hχc1 hcont
    (show χ * k ^ 2 / σ2 ∈ Icc (hFn χ χ) (hFn χ c1) from ⟨by rw [hlow]; positivity, hhigh⟩)
  refine ⟨c, ?_, ?_⟩
  · rcases (mem_Icc.1 hc).1.lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h, hlow] at hcv
      have : 0 < χ * k ^ 2 / σ2 := by positivity
      linarith
  · rw [hcv]
    field_simp

/-- T20: on `(0, c*)` the derivative is negative. -/
theorem signFn_neg (χ k σ2 cstar c : ℝ) (hχ : 0 < χ) (hk : 0 < k) (hσ : 0 ≤ σ2)
    (hstar : χ < cstar) (hroot : σ2 * hFn χ cstar = χ * k ^ 2) (hc : 0 < c)
    (hcs : c < cstar) : signFn χ k σ2 c < 0 := by
  rcases le_or_gt c χ with h | h
  · unfold signFn
    have : σ2 * (c - χ) * c ^ 3 ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hσ (by linarith))
        (by positivity)
    have : 0 < χ * k ^ 2 * (1 + c) ^ 3 := by positivity
    linarith
  · rw [signFn_eq_hFn χ k σ2 c hc]
    have hh := hFn_strictMonoOn χ hχ (mem_Ici.2 h.le) (mem_Ici.2 hstar.le) hcs
    have hσ' : 0 < σ2 := by
      rcases hσ.lt_or_eq with h' | h'
      · exact h'
      · rw [← h'] at hroot
        have : 0 < χ * k ^ 2 := by positivity
        linarith
    have : σ2 * hFn χ c - χ * k ^ 2 < 0 := by nlinarith
    exact mul_neg_of_pos_of_neg (by positivity) this

/-- T20: on `(c*, ∞)` the derivative is positive. -/
theorem signFn_pos (χ k σ2 cstar c : ℝ) (hχ : 0 < χ) (hσ : 0 < σ2) (hstar : χ < cstar)
    (hroot : σ2 * hFn χ cstar = χ * k ^ 2) (hcs : cstar < c) : 0 < signFn χ k σ2 c := by
  have hc : 0 < c := by linarith
  rw [signFn_eq_hFn χ k σ2 c hc]
  have hh := hFn_strictMonoOn χ hχ (mem_Ici.2 hstar.le) (mem_Ici.2 (by linarith)) hcs
  have : 0 < σ2 * hFn χ c - χ * k ^ 2 := by nlinarith
  positivity

/-- T20: `L` is continuous on `(0, ∞)`. -/
theorem socialLoss_continuousOn (χ k σ2 : ℝ) : ContinuousOn (socialLoss χ k σ2) (Ioi 0) :=
  fun c hc => (hasDerivAt_socialLoss χ k σ2 c hc).continuousAt.continuousWithinAt

/-- O&R p. 642, Rogoff (1985b), unimodality: `L` is strictly decreasing on `(0, c*]`. -/
theorem socialLoss_strictAntiOn (χ k σ2 cstar : ℝ) (hχ : 0 < χ) (hk : 0 < k) (hσ : 0 ≤ σ2)
    (hstar : χ < cstar) (hroot : σ2 * hFn χ cstar = χ * k ^ 2) :
    StrictAntiOn (socialLoss χ k σ2) (Ioc 0 cstar) := by
  refine strictAntiOn_of_deriv_neg (convex_Ioc 0 cstar)
    ((socialLoss_continuousOn χ k σ2).mono Ioc_subset_Ioi_self) fun c hc => ?_
  rw [interior_Ioc] at hc
  rw [(hasDerivAt_socialLoss χ k σ2 c hc.1).deriv, deriv_eq_signFn χ k σ2 c hc.1]
  have := signFn_neg χ k σ2 cstar c hχ hk hσ hstar hroot hc.1 hc.2
  have : 0 < c ^ 3 * (1 + c) ^ 3 := by have := hc.1; positivity
  exact div_neg_of_neg_of_pos (by linarith) this

/-- O&R p. 642, Rogoff (1985b), unimodality: `L` is strictly increasing on `[c*, ∞)`. -/
theorem socialLoss_strictMonoOn (χ k σ2 cstar : ℝ) (hχ : 0 < χ) (hσ : 0 < σ2)
    (hstar : χ < cstar) (hroot : σ2 * hFn χ cstar = χ * k ^ 2) :
    StrictMonoOn (socialLoss χ k σ2) (Ici cstar) := by
  refine strictMonoOn_of_deriv_pos (convex_Ici cstar)
    ((socialLoss_continuousOn χ k σ2).mono fun x hx => ?_) fun c hc => ?_
  · simp only [mem_Ici] at hx
    simp only [mem_Ioi]
    linarith
  · rw [interior_Ici] at hc
    have hc0 : 0 < c := by simp only [mem_Ioi] at hc; linarith
    rw [(hasDerivAt_socialLoss χ k σ2 c hc0).deriv, deriv_eq_signFn χ k σ2 c hc0]
    have := signFn_pos χ k σ2 cstar c hχ hσ hstar hroot hc
    have : 0 < c ^ 3 * (1 + c) ^ 3 := by positivity
    positivity

/-- O&R p. 642, Rogoff's theorem (T20): for `k > 0` and `σ² > 0` the optimal degree of
conservatism exists, is unique and strictly exceeds society's: there is `c* > χ` with
`L(c*) < L(c)` for every other `c > 0`, characterised by `σ²(c* − χ)c*³ = χk²(1 + c*)³`. -/
theorem rogoff_optimal (χ k σ2 : ℝ) (hχ : 0 < χ) (hk : 0 < k) (hσ : 0 < σ2) :
    ∃ cstar, χ < cstar ∧ σ2 * (cstar - χ) * cstar ^ 3 = χ * k ^ 2 * (1 + cstar) ^ 3 ∧
      ∀ c, 0 < c → c ≠ cstar → socialLoss χ k σ2 cstar < socialLoss χ k σ2 c := by
  obtain ⟨cstar, hstar, hroot⟩ := exists_root χ k σ2 hχ hk hσ
  have hc0 : 0 < cstar := by linarith
  refine ⟨cstar, hstar, ?_, fun c hc hne => ?_⟩
  · have := signFn_eq_hFn χ k σ2 cstar hc0
    rw [hroot, sub_self, mul_zero] at this
    unfold signFn at this
    linarith
  · rcases lt_or_gt_of_ne hne with h | h
    · exact socialLoss_strictAntiOn χ k σ2 cstar hχ hk hσ.le hstar hroot ⟨hc, h.le⟩
        ⟨hc0, le_rfl⟩ h
    · exact socialLoss_strictMonoOn χ k σ2 cstar hχ hσ hstar hroot (mem_Ici.2 le_rfl)
        (mem_Ici.2 h.le) h

/-- O&R p. 642 (T20): the optimal weight is the unique global minimiser of `L` on
`(0, ∞)`. -/
theorem rogoff_existsUnique (χ k σ2 : ℝ) (hχ : 0 < χ) (hk : 0 < k) (hσ : 0 < σ2) :
    ∃! cstar, 0 < cstar ∧ ∀ c, 0 < c → socialLoss χ k σ2 cstar ≤ socialLoss χ k σ2 c := by
  obtain ⟨cstar, hstar, -, hmin⟩ := rogoff_optimal χ k σ2 hχ hk hσ
  refine ⟨cstar, ⟨by linarith, fun c hc => ?_⟩, fun c' ⟨hc', hle⟩ => ?_⟩
  · rcases eq_or_ne c cstar with h | h
    · rw [h]
    · exact (hmin c hc h).le
  · by_contra hne
    have := hmin c' hc' hne
    have := hle cstar (by linarith)
    linarith

/-- O&R p. 642 (T20): any minimiser satisfies the first-order characterisation
`σ²h(c) = χk²` and exceeds `χ`. -/
theorem minimizer_char (χ k σ2 c : ℝ) (hχ : 0 < χ) (hk : 0 < k) (hσ : 0 < σ2) (hc : 0 < c)
    (hmin : ∀ c', 0 < c' → socialLoss χ k σ2 c ≤ socialLoss χ k σ2 c') :
    χ < c ∧ σ2 * hFn χ c = χ * k ^ 2 := by
  obtain ⟨cstar, hstar, -, hopt⟩ := rogoff_optimal χ k σ2 hχ hk hσ
  have hceq : c = cstar := by
    by_contra hne
    have := hopt c hc hne
    have := hmin cstar (by linarith)
    linarith
  obtain ⟨c2, hc2, hroot⟩ := exists_root χ k σ2 hχ hk hσ
  have hc2eq : c2 = cstar := by
    by_contra hne
    have h2 := hopt c2 (by linarith) hne
    -- `c2` is also a minimiser: it is the turning point of the unimodal `L`
    rcases lt_or_gt_of_ne hne with h | h
    · have := socialLoss_strictMonoOn χ k σ2 c2 hχ hσ hc2 hroot (mem_Ici.2 le_rfl)
        (mem_Ici.2 h.le) h
      linarith
    · have := socialLoss_strictAntiOn χ k σ2 c2 hχ hk hσ.le hc2 hroot
        ⟨by linarith, h.le⟩ ⟨by linarith, le_rfl⟩ h
      linarith
  rw [hceq, ← hc2eq]
  exact ⟨hc2, hroot⟩

/-- O&R p. 642 (T20): the optimal banker is strictly better than one with society's own
weight: `L(c*) < L(χ) = V_D`. -/
theorem rogoff_beats_discretion (χ k σ2 : ℝ) (hχ : 0 < χ) (hk : 0 < k) (hσ : 0 < σ2) :
    ∃ cstar, χ < cstar ∧ socialLoss χ k σ2 cstar < valueDiscretion χ k σ2 := by
  obtain ⟨cstar, hstar, -, hmin⟩ := rogoff_optimal χ k σ2 hχ hk hσ
  exact ⟨cstar, hstar, by
    rw [← socialLoss_self χ k σ2 hχ]
    exact hmin χ hχ hstar.ne⟩

/-- O&R p. 642: as `c → ∞` (a pure inflation targeter) the loss tends to `k² + σ²`. -/
theorem socialLoss_tendsto_atTop (χ k σ2 : ℝ) :
    Tendsto (socialLoss χ k σ2) atTop (𝓝 (k ^ 2 + σ2)) := by
  set G : ℝ → ℝ := fun u => k ^ 2 + χ * k ^ 2 * u ^ 2 + σ2 * ((1 + χ * u ^ 2) / (1 + u) ^ 2)
  have hG : ContinuousAt G 0 := by
    have : (1 + (0 : ℝ)) ^ 2 ≠ 0 := by norm_num
    fun_prop (disch := assumption)
  have hG0 : G 0 = k ^ 2 + σ2 := by simp [G]
  have hlim : Tendsto (fun c : ℝ => G c⁻¹) atTop (𝓝 (k ^ 2 + σ2)) := by
    rw [← hG0]
    exact hG.tendsto.comp tendsto_inv_atTop_zero
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with c hc
  simp only [G, socialLoss]
  field_simp
  ring

/-- O&R p. 642: the optimal banker also beats the pure inflation targeter:
`L(c*) < k² + σ²`. -/
theorem rogoff_beats_infinite (χ k σ2 : ℝ) (hχ : 0 < χ) (hk : 0 < k) (hσ : 0 < σ2) :
    ∃ cstar, χ < cstar ∧ socialLoss χ k σ2 cstar < k ^ 2 + σ2 := by
  obtain ⟨cstar, hstar, hroot⟩ := exists_root χ k σ2 hχ hk hσ
  have hmono := socialLoss_strictMonoOn χ k σ2 cstar hχ hσ hstar hroot
  refine ⟨cstar, hstar, ?_⟩
  have h1 : socialLoss χ k σ2 cstar < socialLoss χ k σ2 (cstar + 1) :=
    hmono (mem_Ici.2 le_rfl) (mem_Ici.2 (by linarith)) (by linarith)
  have h2 : socialLoss χ k σ2 (cstar + 1) ≤ k ^ 2 + σ2 := by
    refine ge_of_tendsto (socialLoss_tendsto_atTop χ k σ2) ?_
    filter_upwards [eventually_ge_atTop (cstar + 1)] with c hc
    rcases hc.lt_or_eq with h | h
    · exact (hmono (mem_Ici.2 (by linarith)) (mem_Ici.2 (by linarith)) h).le
    · rw [h]
  linarith

/-- O&R p. 642: no conservative banker attains the commitment value:
`L(c) ≥ V_C + χk²/c² > V_C` (`k > 0`). -/
theorem socialLoss_gt_commit (χ k σ2 c : ℝ) (hχ : 0 < χ) (hk : 0 < k) (hσ : 0 ≤ σ2)
    (hc : 0 < c) : valueCommit χ k σ2 + χ * k ^ 2 / c ^ 2 ≤ socialLoss χ k σ2 c ∧
      valueCommit χ k σ2 < socialLoss χ k σ2 c := by
  have hχ1 : 0 < 1 + χ := by linarith
  have hc1 : 0 < 1 + c := by linarith
  have key : socialLoss χ k σ2 c - (valueCommit χ k σ2 + χ * k ^ 2 / c ^ 2) =
      σ2 * (c - χ) ^ 2 / ((1 + χ) * (1 + c) ^ 2) := by
    unfold socialLoss valueCommit
    field_simp
    ring
  have h1 : 0 ≤ σ2 * (c - χ) ^ 2 / ((1 + χ) * (1 + c) ^ 2) := by positivity
  have h2 : 0 < χ * k ^ 2 / c ^ 2 := by positivity
  constructor <;> linarith

/-- O&R p. 642: with no inflation bias (`k = 0`) society's own weight is the unique optimum
(`σ² > 0`). -/
theorem no_bias_optimum (χ σ2 c : ℝ) (hχ : 0 < χ) (hσ : 0 < σ2) (hc : 0 < c) (hne : c ≠ χ) :
    socialLoss χ 0 σ2 χ < socialLoss χ 0 σ2 c := by
  have hχ1 : 0 < 1 + χ := by linarith
  have hc1 : 0 < 1 + c := by linarith
  have key : socialLoss χ 0 σ2 c - socialLoss χ 0 σ2 χ =
      σ2 * (c - χ) ^ 2 / ((1 + χ) * (1 + c) ^ 2) := by
    unfold socialLoss
    field_simp
    ring
  have : 0 < σ2 * (c - χ) ^ 2 / ((1 + χ) * (1 + c) ^ 2) := by
    have : 0 < (c - χ) ^ 2 := by positivity
    positivity
  linarith

/-- O&R p. 642: with no supply shocks (`σ² = 0`) and `k > 0`, the loss is strictly
decreasing in the banker's weight, always above `k²`, and tends to `k²`: the optimum is
"`χᶜᴮ = ∞`" (not attained). -/
theorem no_shock_limit (χ k : ℝ) (hχ : 0 < χ) (hk : 0 < k) :
    StrictAntiOn (socialLoss χ k 0) (Ioi 0) ∧ (∀ c, 0 < c → k ^ 2 < socialLoss χ k 0 c) ∧
      Tendsto (socialLoss χ k 0) atTop (𝓝 (k ^ 2)) := by
  refine ⟨fun a ha b _ hab => ?_, fun c hc => ?_, by
    simpa using socialLoss_tendsto_atTop χ k 0⟩
  · simp only [mem_Ioi] at ha
    unfold socialLoss
    simp only [mul_zero, zero_div, add_zero]
    have : χ * k ^ 2 / b ^ 2 < χ * k ^ 2 / a ^ 2 :=
      div_lt_div_of_pos_left (by positivity) (by positivity) (by nlinarith)
    linarith
  · unfold socialLoss
    simp only [mul_zero, zero_div, add_zero]
    have : 0 < χ * k ^ 2 / c ^ 2 := by positivity
    linarith

/-- O&R p. 642 (T20, comparative statics): the optimal weight rises with `k²/σ²`: if
`σ₁²h(c₁) = χk₁²` and `σ₂²h(c₂) = χk₂²` with `c₁, c₂ ≥ χ` and `k₁²/σ₁² < k₂²/σ₂²`, then
`c₁ < c₂`. -/
theorem optimum_mono_ratio (χ k1 k2 s1 s2 c1 c2 : ℝ) (hχ : 0 < χ) (hs1 : 0 < s1)
    (hs2 : 0 < s2) (hc1 : χ ≤ c1) (hc2 : χ ≤ c2) (hr1 : s1 * hFn χ c1 = χ * k1 ^ 2)
    (hr2 : s2 * hFn χ c2 = χ * k2 ^ 2) (hratio : k1 ^ 2 / s1 < k2 ^ 2 / s2) : c1 < c2 := by
  have e1 : hFn χ c1 = χ * (k1 ^ 2 / s1) := by
    field_simp
    linarith
  have e2 : hFn χ c2 = χ * (k2 ^ 2 / s2) := by
    field_simp
    linarith
  have hlt : hFn χ c1 < hFn χ c2 := by
    rw [e1, e2]
    exact mul_lt_mul_of_pos_left hratio hχ
  by_contra hle
  push Not at hle
  rcases hle.lt_or_eq with h | h
  · have := hFn_strictMonoOn χ hχ (mem_Ici.2 hc2) (mem_Ici.2 hc1) h
    linarith
  · rw [h] at hlt
    exact lt_irrefl _ hlt

/-! ## The Walsh contract, (42)–(44) -/

/-- O&R (42), p. 643: the banker's loss with the linear inflation penalty `2ωπ`. -/
def walshLoss (χ k ω π πe z : ℝ) : ℝ := bgLoss χ k π πe z + 2 * ω * π

/-- O&R (42): the contract term is equivalent to lowering the wedge to `k − ω`:
`L_W(π) = L(π; k − ω) + 2ω(πᵉ + z + k) − ω²`, a constant shift. -/
theorem walshLoss_eq (χ k ω π πe z : ℝ) :
    walshLoss χ k ω π πe z = bgLoss χ (k - ω) π πe z + (2 * ω * (πe + z + k) - ω ^ 2) := by
  unfold walshLoss bgLoss
  ring

/-- O&R (43)–(44), p. 643: the one-shot equilibrium under the Walsh contract is unique:
`πᵉ = (k − ω)/χ`, `π = (k − ω)/χ + z/(1 + χ)`. -/
theorem walsh_eqm_iff (p z : S → ℝ) (χ k ω : ℝ) (hχ : 0 < χ) (h1 : ∑ s, p s = 1)
    (hz : expect p z = 0) (π : S → ℝ) (πe : ℝ) :
    ((∀ s x, walshLoss χ k ω (π s) πe (z s) ≤ walshLoss χ k ω x πe (z s)) ∧
        πe = expect p π) ↔
      πe = (k - ω) / χ ∧ ∀ s, π s = (k - ω) / χ + z s / (1 + χ) := by
  have : (∀ s x, walshLoss χ k ω (π s) πe (z s) ≤ walshLoss χ k ω x πe (z s)) ↔
      ∀ s x, bgLoss χ (k - ω) (π s) πe (z s) ≤ bgLoss χ (k - ω) x πe (z s) := by
    simp only [walshLoss_eq, add_le_add_iff_right]
  rw [this]
  exact oneShot_eqm_iff p z χ (k - ω) hχ h1 hz π πe

/-- O&R (44): society's expected loss under the Walsh contract is `V_C + (k − ω)²/χ`. -/
theorem walsh_social_loss (p z : S → ℝ) (χ k ω : ℝ) (hχ : 0 < χ) (h1 : ∑ s, p s = 1)
    (hz : expect p z = 0) :
    expLoss p z χ k (discretionRule χ (k - ω) z) =
      valueCommit χ k (varZ p z) + (k - ω) ^ 2 / χ := by
  have hχ1 : 0 < 1 + χ := by linarith
  have hE : expect p (discretionRule χ (k - ω) z) = (k - ω) / χ := by
    have : expect p (discretionRule χ (k - ω) z) =
        expect p (fun s => (k - ω) / χ + (1 / (1 + χ)) * z s) := by
      unfold expect discretionRule
      exact Finset.sum_congr rfl fun s _ => by ring
    rw [this, expect_add, expect_const p h1, expect_const_mul, hz, mul_zero, add_zero]
  rw [expLoss_eq_commit_add p z χ k hχ1 h1 hz, hE]
  have : expect p (fun s => (discretionRule χ (k - ω) z s - (k - ω) / χ - z s / (1 + χ)) ^ 2)
      = 0 := by
    unfold expect discretionRule
    simp
  rw [this]
  field_simp
  ring

/-- O&R p. 643: `ω = k` is the unique optimal linear contract; it attains the commitment
value `V_C` and implements the commitment rule (36). -/
theorem walsh_optimal (p z : S → ℝ) (χ k ω : ℝ) (hχ : 0 < χ) (h1 : ∑ s, p s = 1)
    (hz : expect p z = 0) :
    expLoss p z χ k (discretionRule χ (k - k) z) = valueCommit χ k (varZ p z) ∧
      discretionRule χ (k - k) z = commitRule χ z ∧
      (ω ≠ k → valueCommit χ k (varZ p z) < expLoss p z χ k (discretionRule χ (k - ω) z)) := by
  refine ⟨?_, ?_, fun hne => ?_⟩
  · rw [walsh_social_loss p z χ k k hχ h1 hz]
    simp
  · funext s
    simp [discretionRule, commitRule]
  · rw [walsh_social_loss p z χ k ω hχ h1 hz]
    have : 0 < (k - ω) ^ 2 / χ := div_pos (by
      have : k - ω ≠ 0 := sub_ne_zero.2 (Ne.symm hne)
      positivity) hχ
    linarith

/-! ## Exercise 4: a random weight on the bonus -/

/-- O&R Ex. 4, p. 658: the banker's loss `L + 2λωπ`. -/
def walshLossLam (χ k ω lam π πe z : ℝ) : ℝ := bgLoss χ k π πe z + 2 * lam * ω * π

/-- O&R Ex. 4(a): the banker's best response given `λ` is that of a wedge `k − λω`. -/
theorem walshLossLam_eq (χ k ω lam π πe z : ℝ) :
    walshLossLam χ k ω lam π πe z =
      bgLoss χ (k - lam * ω) π πe z + (2 * lam * ω * (πe + z + k) - (lam * ω) ^ 2) := by
  unfold walshLossLam bgLoss
  ring

/-- O&R Ex. 4(a): the one-shot equilibrium is unique: `πᵉ = (k − ω)/χ` and
`π = (k − ω)/χ + (z − (λ − 1)ω)/(1 + χ)` (with `E λ = 1`). -/
theorem ex4_eqm_iff (p z lam : S → ℝ) (χ k ω : ℝ) (hχ : 0 < χ) (h1 : ∑ s, p s = 1)
    (hz : expect p z = 0) (hlam : expect p lam = 1) (π : S → ℝ) (πe : ℝ) :
    ((∀ s x, walshLossLam χ k ω (lam s) (π s) πe (z s) ≤ walshLossLam χ k ω (lam s) x πe (z s))
        ∧ πe = expect p π) ↔
      πe = (k - ω) / χ ∧ ∀ s, π s = (k - ω) / χ + (z s - (lam s - 1) * ω) / (1 + χ) := by
  have hχ1 : 0 < 1 + χ := by linarith
  have hopt : (∀ s x, walshLossLam χ k ω (lam s) (π s) πe (z s) ≤
      walshLossLam χ k ω (lam s) x πe (z s)) ↔
      ∀ s, π s = bestResponse χ (k - lam s * ω) πe (z s) := by
    simp only [walshLossLam_eq, add_le_add_iff_right]
    constructor
    · intro h s
      exact eq_bestResponse_of_le χ _ _ _ _ hχ1 (h s _)
    · intro h s x
      rw [h s]
      exact bestResponse_isMin χ _ x πe (z s) hχ1
  rw [hopt]
  have hE : ∀ e, expect p (fun s => bestResponse χ (k - lam s * ω) e (z s)) =
      (k - ω + e) / (1 + χ) := by
    intro e
    have : expect p (fun s => bestResponse χ (k - lam s * ω) e (z s)) =
        expect p (fun s => (k + e) / (1 + χ) + ((1 / (1 + χ)) * z s +
          (-(ω / (1 + χ))) * lam s)) := by
      unfold expect bestResponse
      exact Finset.sum_congr rfl fun s _ => by ring
    rw [this, expect_add, expect_add, expect_const p h1, expect_const_mul, expect_const_mul, hz,
      hlam]
    ring
  constructor
  · rintro ⟨hπ, hre⟩
    have h2 : πe = (k - ω + πe) / (1 + χ) :=
      hre.trans ((congrArg (expect p) (funext hπ)).trans (hE πe))
    have hpe : πe = (k - ω) / χ := by
      rw [eq_div_iff hχ1.ne'] at h2
      rw [eq_div_iff hχ.ne']
      linarith
    refine ⟨hpe, fun s => ?_⟩
    rw [hπ s, hpe]
    unfold bestResponse
    field_simp
    ring
  · rintro ⟨hpe, hπ⟩
    have hbr : ∀ s, π s = bestResponse χ (k - lam s * ω) πe (z s) := by
      intro s
      rw [hπ s, hpe]
      unfold bestResponse
      field_simp
      ring
    refine ⟨hbr, ?_⟩
    rw [show π = fun s => bestResponse χ (k - lam s * ω) πe (z s) from funext hbr, hE, hpe]
    field_simp
    ring

/-- O&R Ex. 4(b): with `E λ = 1`, `Var λ = σ_λ²` and `E[λz] = 0` (λ uncorrelated with `z`),
society's expected loss is `k² + (k − ω)²/χ + χσ_z²/(1 + χ) + ω²σ_λ²/(1 + χ)`. -/
theorem ex4_social_loss (p z lam : S → ℝ) (χ k ω : ℝ) (hχ : 0 < χ) (h1 : ∑ s, p s = 1)
    (hz : expect p z = 0) (hlam : expect p lam = 1)
    (hcov : expect p (fun s => z s * lam s) = 0) :
    expLoss p z χ k (fun s => (k - ω) / χ + (z s - (lam s - 1) * ω) / (1 + χ)) =
      k ^ 2 + (k - ω) ^ 2 / χ + χ * varZ p z / (1 + χ) +
        ω ^ 2 * expect p (fun s => (lam s - 1) ^ 2) / (1 + χ) := by
  have hχ1 : 0 < 1 + χ := by linarith
  set π : S → ℝ := fun s => (k - ω) / χ + (z s - (lam s - 1) * ω) / (1 + χ)
  have hE : expect p π = (k - ω) / χ := by
    unfold expect at hz hlam ⊢
    have : ∑ s, p s * π s = ∑ s, (p s * ((k - ω) / χ + ω / (1 + χ)) +
        1 / (1 + χ) * (p s * z s) + (-(ω / (1 + χ))) * (p s * lam s)) :=
      Finset.sum_congr rfl fun s _ => by simp only [π]; ring
    rw [this, Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.sum_mul,
      ← Finset.mul_sum, ← Finset.mul_sum, h1, hz, hlam]
    ring
  rw [expLoss_decomp p z χ k h1 hz, hE]
  have hV : expect p (fun s => (lam s - 1) ^ 2) =
      expect p (fun s => lam s ^ 2) - 2 * expect p lam + 1 := by
    have : expect p (fun s => (lam s - 1) ^ 2) = expect p (fun s => lam s ^ 2 +
        ((-2) * lam s + 1)) := by
      unfold expect
      exact Finset.sum_congr rfl fun s _ => by ring
    rw [this, expect_add, expect_add, expect_const_mul, expect_const p h1]
    ring
  have e1 : expect p (fun s => (π s - (k - ω) / χ - z s) ^ 2) =
      (χ ^ 2 * varZ p z + ω ^ 2 * expect p (fun s => (lam s - 1) ^ 2)) / (1 + χ) ^ 2 := by
    have : expect p (fun s => (π s - (k - ω) / χ - z s) ^ 2) =
        expect p (fun s => (χ ^ 2 / (1 + χ) ^ 2) * z s ^ 2 +
          ((2 * χ * ω / (1 + χ) ^ 2) * (z s * lam s) +
            ((-(2 * χ * ω / (1 + χ) ^ 2)) * z s +
              (ω ^ 2 / (1 + χ) ^ 2) * (lam s - 1) ^ 2))) := by
      unfold expect
      refine Finset.sum_congr rfl fun s _ => ?_
      simp only [π]
      field_simp
      ring
    rw [this, expect_add, expect_add, expect_add, expect_const_mul, expect_const_mul,
      expect_const_mul, expect_const_mul, hcov, hz]
    unfold varZ
    field_simp
    ring
  have e2 : expect p (fun s => (π s - (k - ω) / χ) ^ 2) =
      (varZ p z + ω ^ 2 * expect p (fun s => (lam s - 1) ^ 2)) / (1 + χ) ^ 2 := by
    have : expect p (fun s => (π s - (k - ω) / χ) ^ 2) =
        expect p (fun s => (1 / (1 + χ) ^ 2) * z s ^ 2 +
          ((-(2 * ω / (1 + χ) ^ 2)) * (z s * lam s) +
            ((2 * ω / (1 + χ) ^ 2) * z s +
              (ω ^ 2 / (1 + χ) ^ 2) * (lam s - 1) ^ 2))) := by
      unfold expect
      refine Finset.sum_congr rfl fun s _ => ?_
      simp only [π]
      field_simp
      ring
    rw [this, expect_add, expect_add, expect_add, expect_const_mul, expect_const_mul,
      expect_const_mul, expect_const_mul, hcov, hz]
    unfold varZ
    field_simp
    ring
  rw [e1, e2]
  field_simp
  ring

/-- O&R Ex. 4(c): the ω-dependent part of the loss, `(k − ω)²/χ + ω²σ_λ²/(1 + χ)`, equals
its minimum plus `A(ω − ω*)²` with `ω* = k(1 + χ)/(1 + χ + χσ_λ²)` and
`A = (1 + χ + χσ_λ²)/(χ(1 + χ))`. -/
theorem ex4_complete_square (χ k ω sl : ℝ) (hχ : 0 < χ) (hsl : 0 ≤ sl) :
    (k - ω) ^ 2 / χ + ω ^ 2 * sl / (1 + χ) =
      ((k - k * (1 + χ) / (1 + χ + χ * sl)) ^ 2 / χ +
        (k * (1 + χ) / (1 + χ + χ * sl)) ^ 2 * sl / (1 + χ)) +
      (1 + χ + χ * sl) / (χ * (1 + χ)) * (ω - k * (1 + χ) / (1 + χ + χ * sl)) ^ 2 := by
  have hχ1 : 0 < 1 + χ := by linarith
  have hD : 0 < 1 + χ + χ * sl := by positivity
  field_simp
  ring

/-- O&R Ex. 4(c): `ω* = k(1 + χ)/(1 + χ + χσ_λ²)` is the unique minimiser of the expected
social loss over `ω`, and it corrects the inflation bias only partially: `ω* < k` iff
`σ_λ² > 0` (for `k > 0`). -/
theorem ex4_optimal (χ k sl : ℝ) (hχ : 0 < χ) (hsl : 0 ≤ sl) (hk : 0 < k) :
    (∀ ω, ω ≠ k * (1 + χ) / (1 + χ + χ * sl) →
      (k - k * (1 + χ) / (1 + χ + χ * sl)) ^ 2 / χ +
          (k * (1 + χ) / (1 + χ + χ * sl)) ^ 2 * sl / (1 + χ) <
        (k - ω) ^ 2 / χ + ω ^ 2 * sl / (1 + χ)) ∧
      (k * (1 + χ) / (1 + χ + χ * sl) < k ↔ 0 < sl) := by
  have hχ1 : 0 < 1 + χ := by linarith
  have hD : 0 < 1 + χ + χ * sl := by positivity
  refine ⟨fun ω hne => ?_, ?_⟩
  · rw [ex4_complete_square χ k ω sl hχ hsl]
    have : 0 < (1 + χ + χ * sl) / (χ * (1 + χ)) *
        (ω - k * (1 + χ) / (1 + χ + χ * sl)) ^ 2 := by
      have : ω - k * (1 + χ) / (1 + χ + χ * sl) ≠ 0 := sub_ne_zero.2 hne
      positivity
    linarith
  · rw [div_lt_iff₀ hD]
    constructor
    · intro h
      have : 0 < k * χ * sl := by nlinarith
      exact pos_of_mul_pos_right this (by positivity)
    · intro h
      nlinarith [mul_pos (mul_pos hk hχ) h]

/-! ## Application: central bank independence and inflation (p. 646) -/

/-- O&R p. 646: the CBI slope `−6.02` (s.e. `2.35`) has t-ratio in `(2.56, 2.57)`, above the
two-sided 5% critical value `2.131` of Student's t with `17 − 2 = 15` degrees of freedom, so
the slope is significant with the hypothesised (negative) sign. -/
theorem cbi_slope_significant :
    (2.131 : ℝ) < 6.02 / 2.35 ∧ (6.02 : ℝ) / 2.35 < 2.57 ∧ (2.56 : ℝ) < 6.02 / 2.35 ∧
      (-6.02 : ℝ) < 0 := by
  norm_num

end ObstfeldRogoff.NominalRigidities.CentralBankDelegation

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Pegging the exchange rate: the escape clause and multiple equilibria

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §9.5.4
(pp. 648–653), eqs. (49)–(58), footnotes 38–40 and Figure 9.12 (after Obstfeld 1996b).

With PPP, inflation is depreciation. The government minimises
`(y − ȳ − k)² + χπ² + C(π)` with output `y = ȳ + (π − πᵉ) − z` (49)–(50) and fixed
realignment costs `C = c̄` (devaluation), `c̲` (revaluation), `0` (peg). Write
`w = k + πᵉ + z`, `s̄ = √(c̄(1 + χ))`, `s̲ = √(c̲(1 + χ))`.

* (51)–(56), T23: `L^FIX − L^FLEX = w²/(1 + χ)`; the escape-clause rule "devalue to
  `w/(1 + χ)` iff `w > s̄` (i.e. `z > z̄`), revalue iff `w < −s̲` (`z < z̲`), else peg" is
  optimal against **every** `π`, and is the unique optimum off the two indifference points.
* (57)–(58), T24: with `z` uniform on `[−Z, Z]` the expected depreciation is the genuine
  integral `Eπ = (1/2Z)∫ π(k + πᵉ + z) dz`, and it equals the book's formula (58) with the
  clamped thresholds of fn 38, for **every** `πᵉ`. Regimes: both thresholds interior
  (`Eπ = (k + πᵉ)/(1 + χ) − (c̄ − c̲)/(4Z)`, a parallel shift of the free-float line),
  revaluation choked off (`Eπ = ((k + πᵉ + Z)² − s̄²)/(4Z(1 + χ))`, strictly convex), free
  float (`Eπ = (k + πᵉ)/(1 + χ)`); the book's three slopes (p. 652) and
  `dz̄/dπᵉ = dz̲/dπᵉ = −1` (p. 651) are verified. `Eπ` is continuous in `πᵉ`.
* T25: on the book's domain (`πᵉ ≥ −i*` with both thresholds interior at `−i*`), there are
  **at most three** equilibria `πᵉ = Eπ`; sufficient conditions for **exactly three**
  (strict fn 40 is needed: with equality the convex regime has no equilibrium below `k/χ`);
  that configuration also forces `s̄ > 2χZ` (a branch steeper than 45°); an equilibrium
  exists for every parameter configuration (over all `πᵉ`, fn 38).
* Corrections. (i) Fig. 9.12 draws the low equilibrium on the flat branch below the
  free-float line; that requires `c̄ > c̲` (with `c̄ = c̲` the branch *is* the free-float
  line). But three equilibria as such do **not** need `c̄ > c̲`: an explicit example with
  `c̄ = c̲` has three. (ii) Fn 40 characterises equilibria of the free-float *regime*, not
  the value `πᵉ = k/χ`: with `c̄ = c̲`, `πᵉ = k/χ` can be an equilibrium although fn 40
  fails.
-/

namespace ObstfeldRogoff.NominalRigidities.EscapeClausePeg

open Set MeasureTheory intervalIntegral
open ObstfeldRogoff.NominalRigidities.BarroGordon

/-! ## The government's problem, (49)–(56) -/

/-- O&R (49), p. 648: the fixed cost of a parity change: `c̄` for a devaluation (`π > 0`),
`c̲` for a revaluation (`π < 0`), `0` if the peg is kept. -/
noncomputable def realignCost (cbar cund π : ℝ) : ℝ :=
  if 0 < π then cbar else if π < 0 then cund else 0

/-- O&R (49)–(50): the government's loss `(π − πᵉ − z − k)² + χπ² + C(π)`. -/
noncomputable def pegLoss (χ k cbar cund π πe z : ℝ) : ℝ :=
  bgLoss χ k π πe z + realignCost cbar cund π

/-- O&R (49)–(50), pp. 648–649: with `y = ȳ + (π − πᵉ) − z` and target `ȳ + k`, the loss
(49) is `pegLoss`. -/
theorem pegLoss_derivation (ybar k χ cbar cund π πe z : ℝ) :
    ((ybar + (π - πe) - z) - (ybar + k)) ^ 2 + χ * π ^ 2 + realignCost cbar cund π =
      pegLoss χ k cbar cund π πe z := by
  unfold pegLoss bgLoss
  ring

/-- O&R (52), p. 649: under the flexible response (51) output is
`ȳ + (k − χπᵉ − χz)/(1 + χ)`. -/
theorem output_flex (χ k πe z : ℝ) (hχ : 0 < 1 + χ) :
    bestResponse χ k πe z - πe - z = (k - χ * πe - χ * z) / (1 + χ) := by
  unfold bestResponse
  field_simp
  ring

/-- O&R (53)–(54), p. 649: `L^FLEX = χ(k + πᵉ + z)²/(1 + χ)`, `L^FIX = (k + z + πᵉ)²`, and
`L^FIX − L^FLEX = (k + πᵉ + z)²/(1 + χ) ≥ 0`. -/
theorem fix_sub_flex (χ k πe z : ℝ) (hχ : 0 < 1 + χ) :
    bgLoss χ k (bestResponse χ k πe z) πe z = χ * (k + πe + z) ^ 2 / (1 + χ) ∧
      bgLoss χ k 0 πe z = (k + z + πe) ^ 2 ∧
      bgLoss χ k 0 πe z - bgLoss χ k (bestResponse χ k πe z) πe z =
        (k + πe + z) ^ 2 / (1 + χ) := by
  refine ⟨bgLoss_bestResponse χ k πe z hχ, by unfold bgLoss; ring, ?_⟩
  rw [bgLoss_bestResponse χ k πe z hχ]
  unfold bgLoss
  field_simp
  ring

/-- O&R (55)–(56): the realignment thresholds `s = √(c(1 + χ))`. -/
noncomputable def thr (χ c : ℝ) : ℝ := Real.sqrt (c * (1 + χ))

/-- O&R (55)–(56): `s² = c(1 + χ)`. -/
theorem thr_sq (χ c : ℝ) (hc : 0 ≤ c) (hχ : 0 < 1 + χ) : thr χ c ^ 2 = c * (1 + χ) :=
  Real.sq_sqrt (mul_nonneg hc hχ.le)

/-- O&R (55)–(56): `s ≥ 0`. -/
theorem thr_nonneg (χ c : ℝ) : 0 ≤ thr χ c := Real.sqrt_nonneg _

/-- O&R (55)–(56), p. 650: the escape-clause policy as a function of `w = k + πᵉ + z`:
devalue to `w/(1 + χ)` if `w > s̄`, revalue to `w/(1 + χ)` if `w < −s̲`, else peg. -/
noncomputable def govPolicy (χ sb su w : ℝ) : ℝ :=
  if sb < w then w / (1 + χ) else if w < -su then w / (1 + χ) else 0

/-- O&R (55), p. 650: devaluation happens exactly when `z > z̄ = s̄ − k − πᵉ`. -/
theorem devalue_iff (sb k πe z : ℝ) : sb < k + πe + z ↔ sb - k - πe < z := by
  constructor <;> intro h <;> linarith

/-- O&R (56), p. 650: revaluation happens exactly when `z < z̲ = −s̲ − k − πᵉ`. -/
theorem revalue_iff (su k πe z : ℝ) : k + πe + z < -su ↔ z < -su - k - πe := by
  constructor <;> intro h <;> linarith

/-- O&R p. 650: the devaluation criterion `L^FIX − L^FLEX > c̄` is `w > s̄` (for `w ≥ 0`). -/
theorem devalue_criterion (χ cbar w : ℝ) (hχ : 0 < 1 + χ) (hc : 0 ≤ cbar) (hw : 0 ≤ w) :
    cbar < w ^ 2 / (1 + χ) ↔ thr χ cbar < w := by
  rw [lt_div_iff₀ hχ, ← thr_sq χ cbar hc hχ]
  exact pow_lt_pow_iff_left₀ (thr_nonneg χ cbar) hw two_ne_zero

/-- O&R (31), (50): the loss in terms of `w = k + πᵉ + z`, `(π − w)² + χπ²`. -/
theorem bgLoss_expand (χ k π πe z : ℝ) :
    bgLoss χ k π πe z = (π - (k + πe + z)) ^ 2 + χ * π ^ 2 := by
  unfold bgLoss
  ring

/-- O&R (51)–(56), T23: the escape-clause rule is optimal against every inflation rate. -/
theorem govPolicy_optimal (χ k cbar cund πe z : ℝ) (hχ : 0 < χ) (hcb : 0 ≤ cbar)
    (hcu : 0 ≤ cund) (π : ℝ) :
    pegLoss χ k cbar cund (govPolicy χ (thr χ cbar) (thr χ cund) (k + πe + z)) πe z ≤
      pegLoss χ k cbar cund π πe z := by
  have hχ1 : 0 < 1 + χ := by linarith
  set w := k + πe + z with hw
  set sb := thr χ cbar
  set su := thr χ cund
  have hsb := thr_sq χ cbar hcb hχ1
  have hsu := thr_sq χ cund hcu hχ1
  have hsb0 : 0 ≤ sb := thr_nonneg χ cbar
  have hsu0 : 0 ≤ su := thr_nonneg χ cund
  have hmin : ∀ x, χ * w ^ 2 / (1 + χ) ≤ bgLoss χ k x πe z := fun x => by
    have := bestResponse_isMin χ k x πe z hχ1
    rwa [bgLoss_bestResponse χ k πe z hχ1] at this
  have hflex : bgLoss χ k (w / (1 + χ)) πe z = χ * w ^ 2 / (1 + χ) :=
    bgLoss_bestResponse χ k πe z hχ1
  have hzero : bgLoss χ k 0 πe z = w ^ 2 := by rw [bgLoss_expand χ k]; ring
  have hpos : ∀ x, 0 < x → w ≤ 0 → w ^ 2 ≤ bgLoss χ k x πe z := fun x hx hw0 => by
    rw [bgLoss_expand χ k]
    nlinarith [mul_nonneg hχ.le (sq_nonneg x)]
  have hneg : ∀ x, x < 0 → 0 ≤ w → w ^ 2 ≤ bgLoss χ k x πe z := fun x hx hw0 => by
    rw [bgLoss_expand χ k]
    nlinarith [mul_nonneg hχ.le (sq_nonneg x)]
  have hdiff : w ^ 2 - χ * w ^ 2 / (1 + χ) = w ^ 2 / (1 + χ) := by
    field_simp
    ring
  have hc_π : ∀ x, 0 < x → realignCost cbar cund x = cbar := fun x hx => by
    simp [realignCost, hx]
  have hc_n : ∀ x, x < 0 → realignCost cbar cund x = cund := fun x hx => by
    simp [realignCost, hx, not_lt.2 hx.le]
  have hc_0 : realignCost cbar cund 0 = 0 := by simp [realignCost]
  have hcost_nonneg : ∀ x, 0 ≤ realignCost cbar cund x := fun x => by
    unfold realignCost
    split_ifs <;> linarith
  unfold pegLoss govPolicy
  split_ifs with h1 h2
  · -- devaluation branch: `w > s̄`
    have hw0 : 0 < w := lt_of_le_of_lt hsb0 h1
    have hwsq : cbar * (1 + χ) < w ^ 2 := by rw [← hsb]; nlinarith
    have hcb' : cbar < w ^ 2 / (1 + χ) := by rw [lt_div_iff₀ hχ1]; linarith
    rw [hflex, hc_π _ (div_pos hw0 hχ1)]
    rcases lt_trichotomy π 0 with hπ | hπ | hπ
    · rw [hc_n π hπ]
      linarith [hneg π hπ hw0.le]
    · rw [hπ, hzero, hc_0]
      linarith
    · rw [hc_π π hπ]
      linarith [hmin π]
  · -- revaluation branch: `w < −s̲`
    have hw0 : w < 0 := by linarith
    have hwsq : cund * (1 + χ) < w ^ 2 := by rw [← hsu]; nlinarith
    have hcu' : cund < w ^ 2 / (1 + χ) := by rw [lt_div_iff₀ hχ1]; linarith
    rw [hflex, hc_n _ (div_neg_of_neg_of_pos hw0 hχ1)]
    rcases lt_trichotomy π 0 with hπ | hπ | hπ
    · rw [hc_n π hπ]
      linarith [hmin π]
    · rw [hπ, hzero, hc_0]
      linarith
    · rw [hc_π π hπ]
      linarith [hpos π hπ hw0.le]
  · -- peg branch: `−s̲ ≤ w ≤ s̄`
    push Not at h1 h2
    rw [hzero, hc_0, add_zero]
    rcases lt_trichotomy π 0 with hπ | hπ | hπ
    · rw [hc_n π hπ]
      rcases le_or_gt 0 w with hw0 | hw0
      · linarith [hneg π hπ hw0, hcost_nonneg π]
      · have hwsq : w ^ 2 ≤ cund * (1 + χ) := by rw [← hsu]; nlinarith
        have : w ^ 2 / (1 + χ) ≤ cund := by rw [div_le_iff₀ hχ1]; linarith
        linarith [hmin π]
    · rw [hπ, hzero, hc_0]
      linarith
    · rw [hc_π π hπ]
      rcases le_or_gt w 0 with hw0 | hw0
      · linarith [hpos π hπ hw0]
      · have hwsq : w ^ 2 ≤ cbar * (1 + χ) := by rw [← hsb]; nlinarith
        have : w ^ 2 / (1 + χ) ≤ cbar := by rw [div_le_iff₀ hχ1]; linarith
        linarith [hmin π]

/-- O&R (55)–(56), T23: away from the two indifference points `w = s̄`, `w = −s̲`, the
escape-clause rule is the **unique** optimum. -/
theorem govPolicy_unique (χ k cbar cund πe z : ℝ) (hχ : 0 < χ) (hcb : 0 ≤ cbar)
    (hcu : 0 ≤ cund) (hne1 : k + πe + z ≠ thr χ cbar) (hne2 : k + πe + z ≠ -thr χ cund)
    (π : ℝ)
    (hπ : pegLoss χ k cbar cund π πe z ≤
      pegLoss χ k cbar cund (govPolicy χ (thr χ cbar) (thr χ cund) (k + πe + z)) πe z) :
    π = govPolicy χ (thr χ cbar) (thr χ cund) (k + πe + z) := by
  have hχ1 : 0 < 1 + χ := by linarith
  set w := k + πe + z with hw
  set sb := thr χ cbar
  set su := thr χ cund
  have hsb := thr_sq χ cbar hcb hχ1
  have hsu := thr_sq χ cund hcu hχ1
  have hsb0 : 0 ≤ sb := thr_nonneg χ cbar
  have hsu0 : 0 ≤ su := thr_nonneg χ cund
  have hflex : bgLoss χ k (w / (1 + χ)) πe z = χ * w ^ 2 / (1 + χ) :=
    bgLoss_bestResponse χ k πe z hχ1
  have hzero : bgLoss χ k 0 πe z = w ^ 2 := by rw [bgLoss_expand χ k]; ring
  have hmin : ∀ x, χ * w ^ 2 / (1 + χ) ≤ bgLoss χ k x πe z := fun x => by
    have := bestResponse_isMin χ k x πe z hχ1
    rwa [bgLoss_bestResponse χ k πe z hχ1] at this
  have hbr : ∀ x, bgLoss χ k x πe z ≤ χ * w ^ 2 / (1 + χ) → x = w / (1 + χ) := fun x hx => by
    have := eq_bestResponse_of_le χ k x πe z hχ1 (by rwa [bgLoss_bestResponse χ k πe z hχ1])
    rw [this]
    rfl
  have hpos : ∀ x, 0 < x → w ≤ 0 → w ^ 2 < bgLoss χ k x πe z := fun x hx hw0 => by
    rw [bgLoss_expand χ k]
    nlinarith [mul_pos hχ (pow_pos hx 2)]
  have hneg : ∀ x, x < 0 → 0 ≤ w → w ^ 2 < bgLoss χ k x πe z := fun x hx hw0 => by
    rw [bgLoss_expand χ k]
    nlinarith [mul_pos hχ (pow_pos (neg_pos.2 hx) 2)]
  have hdiff : w ^ 2 - χ * w ^ 2 / (1 + χ) = w ^ 2 / (1 + χ) := by
    field_simp
    ring
  have hc_π : ∀ x, 0 < x → realignCost cbar cund x = cbar := fun x hx => by
    simp [realignCost, hx]
  have hc_n : ∀ x, x < 0 → realignCost cbar cund x = cund := fun x hx => by
    simp [realignCost, hx, not_lt.2 hx.le]
  have hc_0 : realignCost cbar cund 0 = 0 := by simp [realignCost]
  unfold pegLoss at hπ
  unfold govPolicy at hπ ⊢
  split_ifs at hπ ⊢ with h1 h2
  · have hw0 : 0 < w := lt_of_le_of_lt hsb0 h1
    have hwsq : cbar * (1 + χ) < w ^ 2 := by rw [← hsb]; nlinarith
    have hcb' : cbar < w ^ 2 / (1 + χ) := by rw [lt_div_iff₀ hχ1]; linarith
    rw [hflex, hc_π _ (div_pos hw0 hχ1)] at hπ
    rcases lt_trichotomy π 0 with hp | hp | hp
    · rw [hc_n π hp] at hπ
      linarith [hneg π hp hw0.le]
    · rw [hp, hzero, hc_0] at hπ
      linarith
    · rw [hc_π π hp] at hπ
      exact hbr π (by linarith)
  · have hw0 : w < 0 := by linarith
    have hwsq : cund * (1 + χ) < w ^ 2 := by rw [← hsu]; nlinarith
    have hcu' : cund < w ^ 2 / (1 + χ) := by rw [lt_div_iff₀ hχ1]; linarith
    rw [hflex, hc_n _ (div_neg_of_neg_of_pos hw0 hχ1)] at hπ
    rcases lt_trichotomy π 0 with hp | hp | hp
    · rw [hc_n π hp] at hπ
      exact hbr π (by linarith)
    · rw [hp, hzero, hc_0] at hπ
      linarith
    · rw [hc_π π hp] at hπ
      linarith [hpos π hp hw0.le]
  · push Not at h1 h2
    have h1' : w < sb := lt_of_le_of_ne h1 hne1
    have h2' : -su < w := lt_of_le_of_ne h2 (Ne.symm hne2)
    rw [hzero, hc_0, add_zero] at hπ
    rcases lt_trichotomy π 0 with hp | hp | hp
    · rw [hc_n π hp] at hπ
      rcases le_or_gt 0 w with hw0 | hw0
      · linarith [hneg π hp hw0, hcu]
      · have hwsq : w ^ 2 < cund * (1 + χ) := by rw [← hsu]; nlinarith
        have : w ^ 2 / (1 + χ) < cund := by rw [div_lt_iff₀ hχ1]; linarith
        linarith [hmin π]
    · exact hp
    · rw [hc_π π hp] at hπ
      rcases le_or_gt w 0 with hw0 | hw0
      · linarith [hpos π hp hw0, hcb]
      · have hwsq : w ^ 2 < cbar * (1 + χ) := by rw [← hsb]; nlinarith
        have : w ^ 2 / (1 + χ) < cbar := by rw [div_lt_iff₀ hχ1]; linarith
        linarith [hmin π]

/-- O&R p. 650: the escape-clause policy is nondecreasing in `w` (needed for integrability). -/
theorem govPolicy_monotone (χ sb su : ℝ) (hχ : 0 < 1 + χ) (hsb : 0 ≤ sb) (hsu : 0 ≤ su) :
    Monotone (govPolicy χ sb su) := by
  intro a b hab
  unfold govPolicy
  split_ifs <;>
    first
    | linarith
    | exact (div_le_div_iff_of_pos_right hχ).2 hab
    | exact div_nonneg (by linarith) hχ.le
    | exact div_nonpos_of_nonpos_of_nonneg (by linarith) hχ.le

/-! ## Expected depreciation, (57)–(58) -/

/-- O&R (57)–(58), p. 650: expected depreciation with `z` uniform on `[−Z, Z]`,
`Eπ = (1/2Z)∫_{−Z}^{Z} π(k + πᵉ + z) dz`. -/
noncomputable def expDep (χ k cbar cund Z πe : ℝ) : ℝ :=
  1 / (2 * Z) * ∫ z in (-Z)..Z, govPolicy χ (thr χ cbar) (thr χ cund) (k + πe + z)

/-- O&R fn 38, p. 650: the clamped devaluation threshold `max(min(s̄ − w₀, Z), −Z)`. -/
noncomputable def zbarC (sb w0 Z : ℝ) : ℝ := max (min (sb - w0) Z) (-Z)

/-- O&R fn 38, p. 650: the clamped revaluation threshold `min(max(−s̲ − w₀, −Z), Z)`. -/
noncomputable def zundC (su w0 Z : ℝ) : ℝ := min (max (-su - w0) (-Z)) Z

/-- Integration tool for (58): functions agreeing on the open interval have the same
integral. -/
theorem integral_congr_Ioo {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (h : EqOn f g (Ioo a b)) :
    ∫ x in a..b, f x = ∫ x in a..b, g x := by
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab,
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  exact setIntegral_congr_fun measurableSet_Ioo h

/-- Integration tool for (58): `∫_a^b (w₀ + z)/(1 + χ) dz = ((w₀ + b)² − (w₀ + a)²)/(2(1 + χ))`. -/
theorem integral_linear (w0 χ a b : ℝ) (hχ : 0 < 1 + χ) :
    ∫ z in a..b, (w0 + z) / (1 + χ) = ((w0 + b) ^ 2 - (w0 + a) ^ 2) / (2 * (1 + χ)) := by
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add intervalIntegrable_const
    intervalIntegrable_id, intervalIntegral.integral_const, integral_id, smul_eq_mul]
  field_simp
  ring

/-- O&R (58), p. 650, for **every** `πᵉ` (T24): with `w₀ = k + πᵉ` and the clamped thresholds
`z̄, z̲` of fn 38, `∫_{−Z}^{Z} π dz = ((2Z − (z̄ − z̲))w₀ − (z̄² − z̲²)/2)/(1 + χ)`. -/
theorem integral_govPolicy (χ sb su Z w0 : ℝ) (hχ : 0 < 1 + χ) (hsb : 0 ≤ sb) (hsu : 0 ≤ su)
    (hZ : 0 < Z) :
    ∫ z in (-Z)..Z, govPolicy χ sb su (w0 + z) =
      ((2 * Z - (zbarC sb w0 Z - zundC su w0 Z)) * w0 -
        (zbarC sb w0 Z ^ 2 - zundC su w0 Z ^ 2) / 2) / (1 + χ) := by
  set zb := zbarC sb w0 Z with hzb
  set zu := zundC su w0 Z with hzu
  have h1 : -Z ≤ zu := le_min (le_max_right _ _) (by linarith)
  have h3 : zb ≤ Z := max_le (min_le_right _ _) (by linarith)
  have h2 : zu ≤ zb := by
    rw [hzb, hzu, zbarC, zundC]
    simp only [min_def, max_def]
    split_ifs <;> linarith
  have hmono : Monotone fun z => govPolicy χ sb su (w0 + z) :=
    (govPolicy_monotone χ sb su hχ hsb hsu).comp fun a b h => add_le_add_right h w0
  have hint : ∀ a b, IntervalIntegrable (fun z => govPolicy χ sb su (w0 + z)) volume a b :=
    fun a b => hmono.intervalIntegrable
  rw [← integral_add_adjacent_intervals (hint (-Z) zu) (hint zu Z),
    ← integral_add_adjacent_intervals (hint zu zb) (hint zb Z)]
  have eA : ∫ z in (-Z)..zu, govPolicy χ sb su (w0 + z) =
      ∫ z in (-Z)..zu, (w0 + z) / (1 + χ) := by
    refine integral_congr_Ioo h1 fun z hz => ?_
    have hlt : z < max (-su - w0) (-Z) := lt_of_lt_of_le hz.2 (min_le_left _ _)
    have hw : w0 + z < -su := by
      rcases lt_max_iff.1 hlt with h | h
      · linarith
      · linarith [hz.1]
    have hn : ¬ sb < w0 + z := by linarith
    simp only [govPolicy, hn, hw, ↓reduceIte]
  have eB : ∫ z in zu..zb, govPolicy χ sb su (w0 + z) = ∫ _ in zu..zb, (0 : ℝ) := by
    refine integral_congr_Ioo h2 fun z hz => ?_
    have hz1 : -Z < z := lt_of_le_of_lt h1 hz.1
    have hz2 : z < Z := lt_of_lt_of_le hz.2 h3
    have hup : z < sb - w0 := by
      rcases lt_max_iff.1 hz.2 with h | h
      · rcases lt_min_iff.1 h with ⟨h', -⟩
        exact h'
      · linarith
    have hlo : -su - w0 < z := by
      rcases min_lt_iff.1 hz.1 with h | h
      · exact (max_lt_iff.1 h).1
      · linarith
    have hn1 : ¬ sb < w0 + z := by linarith
    have hn2 : ¬ w0 + z < -su := by linarith
    simp only [govPolicy, hn1, hn2, ↓reduceIte]
  have eC : ∫ z in zb..Z, govPolicy χ sb su (w0 + z) = ∫ z in zb..Z, (w0 + z) / (1 + χ) := by
    refine integral_congr_Ioo h3 fun z hz => ?_
    have hw : sb < w0 + z := by
      have : min (sb - w0) Z < z := lt_of_le_of_lt (le_max_left _ _) hz.1
      rcases min_lt_iff.1 this with h | h
      · linarith
      · linarith [hz.2]
    simp only [govPolicy, hw, ↓reduceIte]
  rw [eA, eB, eC, integral_linear w0 χ _ _ hχ, integral_linear w0 χ _ _ hχ,
    intervalIntegral.integral_zero]
  field_simp
  ring

/-- O&R (58), p. 650: the book's formula
`Eπ = (1/(1 + χ))[(1 − (z̄ − z̲)/(2Z))(k + πᵉ) − (z̄² − z̲²)/(4Z)]` (thresholds clamped as in
fn 38), valid for every `πᵉ`. -/
theorem expDep_eq (χ k cbar cund Z πe : ℝ) (hχ : 0 < 1 + χ) (hZ : 0 < Z) :
    expDep χ k cbar cund Z πe =
      1 / (1 + χ) * ((1 - (zbarC (thr χ cbar) (k + πe) Z - zundC (thr χ cund) (k + πe) Z) /
        (2 * Z)) * (k + πe) - (zbarC (thr χ cbar) (k + πe) Z ^ 2 -
          zundC (thr χ cund) (k + πe) Z ^ 2) / (4 * Z)) := by
  unfold expDep
  rw [integral_govPolicy χ _ _ Z (k + πe) hχ (thr_nonneg χ cbar) (thr_nonneg χ cund) hZ]
  field_simp
  ring

/-- O&R (58): expected depreciation is continuous in `πᵉ`. -/
theorem expDep_continuous (χ k cbar cund Z : ℝ) (hχ : 0 < 1 + χ) (hZ : 0 < Z) :
    Continuous (expDep χ k cbar cund Z) := by
  have : expDep χ k cbar cund Z = fun πe =>
      1 / (1 + χ) * ((1 - (zbarC (thr χ cbar) (k + πe) Z - zundC (thr χ cund) (k + πe) Z) /
        (2 * Z)) * (k + πe) - (zbarC (thr χ cbar) (k + πe) Z ^ 2 -
          zundC (thr χ cund) (k + πe) Z ^ 2) / (4 * Z)) :=
    funext fun πe => expDep_eq χ k cbar cund Z πe hχ hZ
  rw [this]
  unfold zbarC zundC
  fun_prop

/-- O&R p. 652, T24, regime A (both thresholds interior, `s̄ − Z ≤ k + πᵉ ≤ Z − s̲`):
`Eπ = (k + πᵉ)/(1 + χ) − (c̄ − c̲)/(4Z)`, the free-float line shifted by `(c̄ − c̲)/(4Z)`. -/
theorem expDep_regimeA (χ k cbar cund Z πe : ℝ) (hχ : 0 < 1 + χ) (hZ : 0 < Z)
    (hcb : 0 ≤ cbar) (hcu : 0 ≤ cund) (hA1 : thr χ cbar - Z ≤ k + πe)
    (hA2 : k + πe ≤ Z - thr χ cund) :
    expDep χ k cbar cund Z πe = (k + πe) / (1 + χ) - (cbar - cund) / (4 * Z) := by
  have hsb0 := thr_nonneg χ cbar
  have hsu0 := thr_nonneg χ cund
  rw [expDep_eq χ k cbar cund Z πe hχ hZ]
  have e1 : zbarC (thr χ cbar) (k + πe) Z = thr χ cbar - (k + πe) := by
    unfold zbarC
    rw [min_eq_left (by linarith), max_eq_left (by linarith)]
  have e2 : zundC (thr χ cund) (k + πe) Z = -thr χ cund - (k + πe) := by
    unfold zundC
    rw [max_eq_left (by linarith), min_eq_left (by linarith)]
  rw [e1, e2]
  have h1 := thr_sq χ cbar hcb hχ
  have h2 := thr_sq χ cund hcu hχ
  have hc : cbar - cund = (thr χ cbar ^ 2 - thr χ cund ^ 2) / (1 + χ) := by
    rw [h1, h2]
    field_simp
  rw [hc]
  field_simp
  ring

/-- O&R p. 652, T24, regime M (revaluation choked off, `Z − s̲ ≤ k + πᵉ ≤ Z + s̄`, with
`k + πᵉ ≥ s̄ − Z`): `Eπ = ((k + πᵉ + Z)² − s̄²)/(4Z(1 + χ))`. -/
theorem expDep_regimeM (χ k cbar cund Z πe : ℝ) (hχ : 0 < 1 + χ) (hZ : 0 < Z)
    (hM0 : thr χ cbar - Z ≤ k + πe) (hM1 : Z - thr χ cund ≤ k + πe)
    (hM2 : k + πe ≤ Z + thr χ cbar) :
    expDep χ k cbar cund Z πe = ((k + πe + Z) ^ 2 - thr χ cbar ^ 2) / (4 * Z * (1 + χ)) := by
  rw [expDep_eq χ k cbar cund Z πe hχ hZ]
  have e1 : zbarC (thr χ cbar) (k + πe) Z = thr χ cbar - (k + πe) := by
    unfold zbarC
    rw [min_eq_left (by linarith), max_eq_left (by linarith)]
  have e2 : zundC (thr χ cund) (k + πe) Z = -Z := by
    unfold zundC
    rw [max_eq_right (by linarith), min_eq_left (by linarith)]
  rw [e1, e2]
  field_simp
  ring

/-- O&R p. 652, T24, free-float regime (`k + πᵉ ≥ Z + s̄`): `Eπ = (k + πᵉ)/(1 + χ)`. -/
theorem expDep_float (χ k cbar cund Z πe : ℝ) (hχ : 0 < 1 + χ) (hZ : 0 < Z)
    (hF : Z + thr χ cbar ≤ k + πe) :
    expDep χ k cbar cund Z πe = (k + πe) / (1 + χ) := by
  have hsu0 := thr_nonneg χ cund
  have hsb0 := thr_nonneg χ cbar
  rw [expDep_eq χ k cbar cund Z πe hχ hZ]
  have e1 : zbarC (thr χ cbar) (k + πe) Z = -Z := by
    unfold zbarC
    rw [min_eq_left (by linarith), max_eq_right (by linarith)]
  have e2 : zundC (thr χ cund) (k + πe) Z = -Z := by
    unfold zundC
    rw [max_eq_right (by linarith), min_eq_left (by linarith)]
  rw [e1, e2]
  field_simp
  ring

/-- O&R fn 38 (T24): if `k + πᵉ ≤ −Z − s̲` the government always revalues:
`Eπ = (k + πᵉ)/(1 + χ)`. -/
theorem expDep_alwaysRevalue (χ k cbar cund Z πe : ℝ) (hχ : 0 < 1 + χ) (hZ : 0 < Z)
    (hR : k + πe ≤ -Z - thr χ cund) :
    expDep χ k cbar cund Z πe = (k + πe) / (1 + χ) := by
  have hsu0 := thr_nonneg χ cund
  have hsb0 := thr_nonneg χ cbar
  rw [expDep_eq χ k cbar cund Z πe hχ hZ]
  have e1 : zbarC (thr χ cbar) (k + πe) Z = Z := by
    unfold zbarC
    rw [min_eq_right (by linarith), max_eq_left (by linarith)]
  have e2 : zundC (thr χ cund) (k + πe) Z = Z := by
    unfold zundC
    rw [max_eq_left (by linarith), min_eq_right (by linarith)]
  rw [e1, e2]
  field_simp
  ring

/-- O&R p. 652 (slopes): in the interior of regime A, `dEπ/dπᵉ = 1/(1 + χ)`. -/
theorem hasDerivAt_expDep_A (χ k cbar cund Z πe : ℝ) (hχ : 0 < 1 + χ) (hZ : 0 < Z)
    (hcb : 0 ≤ cbar) (hcu : 0 ≤ cund) (hA1 : thr χ cbar - Z < k + πe)
    (hA2 : k + πe < Z - thr χ cund) :
    HasDerivAt (expDep χ k cbar cund Z) (1 / (1 + χ)) πe := by
  have hev : (fun x => (k + x) / (1 + χ) - (cbar - cund) / (4 * Z)) =ᶠ[nhds πe]
      expDep χ k cbar cund Z := by
    have : Ioo (thr χ cbar - Z - k) (Z - thr χ cund - k) ∈ nhds πe :=
      Ioo_mem_nhds (by linarith) (by linarith)
    filter_upwards [this] with x hx
    rw [expDep_regimeA χ k cbar cund Z x hχ hZ hcb hcu (by linarith [hx.1])
      (by linarith [hx.2])]
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev.symm
  have := (((hasDerivAt_id' πe).const_add k).div_const (1 + χ)).sub_const
    ((cbar - cund) / (4 * Z))
  exact this

/-- O&R p. 652 (slopes): in the interior of regime M,
`dEπ/dπᵉ = (1/(1 + χ))(1/2 + (k + πᵉ)/(2Z))`. -/
theorem hasDerivAt_expDep_M (χ k cbar cund Z πe : ℝ) (hχ : 0 < 1 + χ) (hZ : 0 < Z)
    (hM0 : thr χ cbar - Z < k + πe) (hM1 : Z - thr χ cund < k + πe)
    (hM2 : k + πe < Z + thr χ cbar) :
    HasDerivAt (expDep χ k cbar cund Z) (1 / (1 + χ) * (1 / 2 + (k + πe) / (2 * Z))) πe := by
  have hev : (fun x => ((k + x + Z) ^ 2 - thr χ cbar ^ 2) / (4 * Z * (1 + χ))) =ᶠ[nhds πe]
      expDep χ k cbar cund Z := by
    have : Ioo (max (thr χ cbar - Z - k) (Z - thr χ cund - k)) (Z + thr χ cbar - k) ∈
        nhds πe := Ioo_mem_nhds (max_lt (by linarith) (by linarith)) (by linarith)
    filter_upwards [this] with x hx
    have := max_lt_iff.1 hx.1
    rw [expDep_regimeM χ k cbar cund Z x hχ hZ (by linarith) (by linarith)
      (by linarith [hx.2])]
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev.symm
  have h := ((((hasDerivAt_id' πe).const_add k).add_const Z).fun_pow 2).sub_const
    (thr χ cbar ^ 2) |>.div_const (4 * Z * (1 + χ))
  convert h using 1
  field_simp
  ring

/-- O&R p. 652 (slopes): in the interior of the free-float regime, `dEπ/dπᵉ = 1/(1 + χ)`. -/
theorem hasDerivAt_expDep_float (χ k cbar cund Z πe : ℝ) (hχ : 0 < 1 + χ) (hZ : 0 < Z)
    (hF : Z + thr χ cbar < k + πe) :
    HasDerivAt (expDep χ k cbar cund Z) (1 / (1 + χ)) πe := by
  have hev : (fun x => (k + x) / (1 + χ)) =ᶠ[nhds πe] expDep χ k cbar cund Z := by
    have : Ioi (Z + thr χ cbar - k) ∈ nhds πe := Ioi_mem_nhds (by linarith)
    filter_upwards [this] with x hx
    rw [expDep_float χ k cbar cund Z x hχ hZ (by simp only [mem_Ioi] at hx; linarith)]
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev.symm
  exact ((hasDerivAt_id' πe).const_add k).div_const (1 + χ)

/-! ## Equilibria, T25 -/

/-- O&R p. 651: rational expectations, `πᵉ = Eπ(πᵉ)`: the zeros of `G(πᵉ) = Eπ − πᵉ`. -/
noncomputable def gapFn (χ k cbar cund Z πe : ℝ) : ℝ := expDep χ k cbar cund Z πe - πe

/-- T25: the quadratic of regime M, `q(πᵉ) = ((k + πᵉ + Z)² − s̄²)/(4Z(1 + χ)) − πᵉ`, written
as `α x² + β x + γ` with `α = 1/(4Z(1 + χ)) > 0`. -/
theorem quad_M_form (χ k sb Z x : ℝ) (hχ : 0 < 1 + χ) (hZ : 0 < Z) :
    ((k + x + Z) ^ 2 - sb ^ 2) / (4 * Z * (1 + χ)) - x =
      1 / (4 * Z * (1 + χ)) * x ^ 2 + (2 * (k + Z) / (4 * Z * (1 + χ)) - 1) * x +
        ((k + Z) ^ 2 - sb ^ 2) / (4 * Z * (1 + χ)) := by
  field_simp
  ring

/-- T25: a quadratic with positive leading coefficient and roots `r₁ < r₂` factors as
`α(x − r₁)(x − r₂)`. -/
theorem quad_factor (α β γ r1 r2 : ℝ) (hr : r1 < r2) (h1 : α * r1 ^ 2 + β * r1 + γ = 0)
    (h2 : α * r2 ^ 2 + β * r2 + γ = 0) (x : ℝ) :
    α * x ^ 2 + β * x + γ = α * (x - r1) * (x - r2) := by
  have hb : β = -α * (r1 + r2) := by
    have : (r1 - r2) * (α * (r1 + r2) + β) = 0 := by linear_combination h1 - h2
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h (by linarith)
    · linarith
  have hc : γ = α * r1 * r2 := by
    rw [hb] at h1
    linarith
  rw [hb, hc]
  ring

/-- O&R pp. 651–652 (T25, at most three equilibria): on the book's domain `πᵉ ≥ π_L`
(with `s̄ − Z < k + π_L < Z − s̲`, "`z̲ > −Z` and `z̄ < Z` at `πᵉ = −i*`"), the equation
`πᵉ = Eπ(πᵉ)` has at most three solutions. -/
theorem at_most_three (χ k cbar cund Z πL : ℝ) (hχ : 0 < χ) (hZ : 0 < Z) (hcb : 0 ≤ cbar)
    (hcu : 0 ≤ cund) (hL1 : thr χ cbar - Z < k + πL) (hL2 : k + πL < Z - thr χ cund)
    (x1 x2 x3 x4 : ℝ) (h0 : πL ≤ x1) (h12 : x1 < x2) (h23 : x2 < x3) (h34 : x3 < x4) :
    ¬ (gapFn χ k cbar cund Z x1 = 0 ∧ gapFn χ k cbar cund Z x2 = 0 ∧
      gapFn χ k cbar cund Z x3 = 0 ∧ gapFn χ k cbar cund Z x4 = 0) := by
  have hχ1 : 0 < 1 + χ := by linarith
  have hsb0 := thr_nonneg χ cbar
  have hsu0 := thr_nonneg χ cund
  set a := Z - thr χ cund - k with ha
  set b := Z + thr χ cbar - k with hb
  have hab : a ≤ b := by linarith
  -- the three pieces
  have hGA : ∀ x, πL ≤ x → x ≤ a →
      gapFn χ k cbar cund Z x = (k + x) / (1 + χ) - (cbar - cund) / (4 * Z) - x := by
    intro x hx1 hx2
    unfold gapFn
    rw [expDep_regimeA χ k cbar cund Z x hχ1 hZ hcb hcu (by linarith) (by linarith)]
  have hGM : ∀ x, a ≤ x → x ≤ b → gapFn χ k cbar cund Z x =
      ((k + x + Z) ^ 2 - thr χ cbar ^ 2) / (4 * Z * (1 + χ)) - x := by
    intro x hx1 hx2
    unfold gapFn
    rw [expDep_regimeM χ k cbar cund Z x hχ1 hZ (by linarith) (by linarith) (by linarith)]
  have hGF : ∀ x, b ≤ x → gapFn χ k cbar cund Z x = (k + x) / (1 + χ) - x := by
    intro x hx
    unfold gapFn
    rw [expDep_float χ k cbar cund Z x hχ1 hZ (by linarith)]
  rintro ⟨g1, g2, g3, g4⟩
  -- at most one zero in `[π_L, a]` and in `[b, ∞)` (strictly decreasing lines)
  have hx2a : a < x2 := by
    by_contra h
    push Not at h
    rw [hGA x1 h0 (by linarith)] at g1
    rw [hGA x2 (by linarith) h] at g2
    have e : ((k + x1) / (1 + χ) - (cbar - cund) / (4 * Z) - x1) -
        ((k + x2) / (1 + χ) - (cbar - cund) / (4 * Z) - x2) = (x2 - x1) * (χ / (1 + χ)) := by
      field_simp
      ring
    have : 0 < (x2 - x1) * (χ / (1 + χ)) := mul_pos (by linarith) (div_pos hχ hχ1)
    linarith
  have hx3b : x3 < b := by
    by_contra h
    push Not at h
    rw [hGF x3 h] at g3
    rw [hGF x4 (by linarith)] at g4
    have e : ((k + x3) / (1 + χ) - x3) - ((k + x4) / (1 + χ) - x4) =
        (x4 - x3) * (χ / (1 + χ)) := by
      field_simp
      ring
    have : 0 < (x4 - x3) * (χ / (1 + χ)) := mul_pos (by linarith) (div_pos hχ hχ1)
    linarith
  set α := 1 / (4 * Z * (1 + χ)) with hα
  set β := 2 * (k + Z) / (4 * Z * (1 + χ)) - 1
  set γ := ((k + Z) ^ 2 - thr χ cbar ^ 2) / (4 * Z * (1 + χ))
  have hαpos : 0 < α := by positivity
  have hq : ∀ x, a ≤ x → x ≤ b → gapFn χ k cbar cund Z x = α * x ^ 2 + β * x + γ :=
    fun x h1 h2 => by rw [hGM x h1 h2, quad_M_form χ k (thr χ cbar) Z x hχ1 hZ]
  have q2 := g2
  have q3 := g3
  rw [hq x2 hx2a.le (by linarith)] at q2
  rw [hq x3 (by linarith) hx3b.le] at q3
  have hfac := quad_factor α β γ x2 x3 h23 q2 q3
  rcases le_or_gt x1 a with hx1 | hx1
  · -- `G(a) ≤ 0` from the decreasing first piece, but `q(a) = α(a − x₂)(a − x₃) > 0`
    have hGa : gapFn χ k cbar cund Z a ≤ 0 := by
      rw [hGA a (by linarith) le_rfl]
      rw [hGA x1 h0 hx1] at g1
      have : (a - x1) * (χ / (1 + χ)) ≥ 0 := mul_nonneg (by linarith) (div_pos hχ hχ1).le
      have e : (k + a) / (1 + χ) - (cbar - cund) / (4 * Z) - a =
          ((k + x1) / (1 + χ) - (cbar - cund) / (4 * Z) - x1) - (a - x1) * (χ / (1 + χ)) := by
        field_simp
        ring
      linarith
    rw [hq a le_rfl hab, hfac a] at hGa
    have : 0 < α * (a - x2) * (a - x3) := by
      have := mul_pos_of_neg_of_neg (show a - x2 < 0 by linarith) (show a - x3 < 0 by linarith)
      rw [mul_assoc]
      exact mul_pos hαpos this
    linarith
  · -- three zeros of the strictly convex quadratic
    have q1 := g1
    rw [hq x1 hx1.le (by linarith), hfac x1] at q1
    have : 0 < α * (x1 - x2) * (x1 - x3) := by
      have := mul_pos_of_neg_of_neg (show x1 - x2 < 0 by linarith) (show x1 - x3 < 0 by linarith)
      rw [mul_assoc]
      exact mul_pos hαpos this
    linarith

/-- O&R p. 652 (T25): the gap `G = Eπ − πᵉ` is continuous. -/
theorem gapFn_continuous (χ k cbar cund Z : ℝ) (hχ : 0 < 1 + χ) (hZ : 0 < Z) :
    Continuous (gapFn χ k cbar cund Z) :=
  (expDep_continuous χ k cbar cund Z hχ hZ).sub continuous_id

/-- O&R p. 652 (T25): on regime A the gap is `χ(π₁ − πᵉ)/(1 + χ)`, where
`π₁ = (k − (1 + χ)(c̄ − c̲)/(4Z))/χ` is the flat-branch equilibrium (equilibrium 1). -/
theorem gapFn_regimeA (χ k cbar cund Z πe : ℝ) (hχ : 0 < χ) (hZ : 0 < Z) (hcb : 0 ≤ cbar)
    (hcu : 0 ≤ cund) (hA1 : thr χ cbar - Z ≤ k + πe) (hA2 : k + πe ≤ Z - thr χ cund) :
    gapFn χ k cbar cund Z πe =
      χ * ((k - (1 + χ) * ((cbar - cund) / (4 * Z))) / χ - πe) / (1 + χ) := by
  have hχ1 : 0 < 1 + χ := by linarith
  unfold gapFn
  rw [expDep_regimeA χ k cbar cund Z πe hχ1 hZ hcb hcu hA1 hA2]
  field_simp
  ring

/-- O&R p. 652 (T25): on the free-float regime the gap is `(k − χπᵉ)/(1 + χ)`. -/
theorem gapFn_float (χ k cbar cund Z πe : ℝ) (hχ : 0 < 1 + χ) (hZ : 0 < Z)
    (hF : Z + thr χ cbar ≤ k + πe) :
    gapFn χ k cbar cund Z πe = (k - χ * πe) / (1 + χ) := by
  unfold gapFn
  rw [expDep_float χ k cbar cund Z πe hχ hZ hF]
  field_simp
  ring

/-- O&R p. 652, fn 40 (T25), corrected reading: an equilibrium in the free-float regime
(`z̄ ≤ −Z`, devaluation for every shock) exists iff `(1 + χ)k/χ − Z ≥ s̄`, and it is then
`πᵉ = k/χ`, the one-shot level (34). -/
theorem float_eqm_iff (χ k cbar cund Z : ℝ) (hχ : 0 < χ) (hZ : 0 < Z) :
    (∃ πe, Z + thr χ cbar ≤ k + πe ∧ gapFn χ k cbar cund Z πe = 0) ↔
      thr χ cbar ≤ (1 + χ) * k / χ - Z := by
  have hχ1 : 0 < 1 + χ := by linarith
  have e : (1 + χ) * k / χ = k + k / χ := by
    field_simp
    ring
  rw [e]
  constructor
  · rintro ⟨πe, hF, hG⟩
    rw [gapFn_float χ k cbar cund Z πe hχ1 hZ hF, div_eq_zero_iff] at hG
    rcases hG with hG | hG
    · have : πe = k / χ := by field_simp; linarith
      rw [this] at hF
      linarith
    · linarith
  · intro h
    refine ⟨k / χ, by linarith, ?_⟩
    rw [gapFn_float χ k cbar cund Z _ hχ1 hZ (by linarith)]
    field_simp
    ring

/-- O&R p. 652 (T25): any free-float-regime equilibrium is `πᵉ = k/χ`. -/
theorem float_eqm_eq (χ k cbar cund Z πe : ℝ) (hχ : 0 < χ) (hZ : 0 < Z)
    (hF : Z + thr χ cbar ≤ k + πe) (hG : gapFn χ k cbar cund Z πe = 0) : πe = k / χ := by
  have hχ1 : 0 < 1 + χ := by linarith
  rw [gapFn_float χ k cbar cund Z πe hχ1 hZ hF, div_eq_zero_iff] at hG
  rcases hG with hG | hG
  · field_simp
    linarith
  · linarith

/-- O&R Fig. 9.12 correction (T25): an equilibrium on the flat branch (regime A) strictly
below the one-shot level `k/χ` requires `c̄ > c̲`. -/
theorem flat_branch_below_needs_cbar_gt (χ k cbar cund Z πe : ℝ) (hχ : 0 < χ) (hZ : 0 < Z)
    (hcb : 0 ≤ cbar) (hcu : 0 ≤ cund) (hA1 : thr χ cbar - Z ≤ k + πe)
    (hA2 : k + πe ≤ Z - thr χ cund) (hG : gapFn χ k cbar cund Z πe = 0)
    (hlow : πe < k / χ) : cund < cbar := by
  have hχ1 : 0 < 1 + χ := by linarith
  unfold gapFn at hG
  rw [expDep_regimeA χ k cbar cund Z πe hχ1 hZ hcb hcu hA1 hA2] at hG
  have h1 : χ * πe < k := by rwa [lt_div_iff₀ hχ, mul_comm] at hlow
  have h2 : (cbar - cund) / (4 * Z) = (k - χ * πe) / (1 + χ) := by
    field_simp
    field_simp at hG
    linarith
  have h3 : 0 < (cbar - cund) / (4 * Z) := by rw [h2]; exact div_pos (by linarith) hχ1
  have := (div_pos_iff_of_pos_right (by positivity : (0 : ℝ) < 4 * Z)).1 h3
  linarith

/-- O&R Fig. 9.12 correction: with symmetric costs `c̄ = c̲` the flat branch coincides with
the free-float line `(k + πᵉ)/(1 + χ)`. -/
theorem symmetric_flat_is_float (χ k c Z πe : ℝ) (hχ : 0 < 1 + χ) (hZ : 0 < Z) (hc : 0 ≤ c)
    (hA1 : thr χ c - Z ≤ k + πe) (hA2 : k + πe ≤ Z - thr χ c) :
    expDep χ k c c Z πe = (k + πe) / (1 + χ) := by
  rw [expDep_regimeA χ k c c Z πe hχ hZ hc hc hA1 hA2]
  ring

/-- O&R pp. 651–652, T25 (exactly three equilibria, the Fig. 9.12 configuration): on the
book's domain, if `G(π_L) > 0`, the flat-branch point `π₁` lies in the interior regime A,
and fn 40 holds **strictly**, then there are exactly three equilibria `π₁ < π₂ < k/χ`, with
`π₂` in the convex regime. -/
theorem exactly_three (χ k cbar cund Z πL : ℝ) (hχ : 0 < χ) (hZ : 0 < Z) (hcb : 0 ≤ cbar)
    (hcu : 0 ≤ cund) (hL1 : thr χ cbar - Z < k + πL) (hL2 : k + πL < Z - thr χ cund)
    (hGL : 0 < gapFn χ k cbar cund Z πL)
    (hπ1 : k + (k - (1 + χ) * ((cbar - cund) / (4 * Z))) / χ < Z - thr χ cund)
    (hfn40 : Z + thr χ cbar < k + k / χ) :
    ∃ π2, Z - thr χ cund - k < π2 ∧ π2 < Z + thr χ cbar - k ∧
      πL < (k - (1 + χ) * ((cbar - cund) / (4 * Z))) / χ ∧
      (k - (1 + χ) * ((cbar - cund) / (4 * Z))) / χ < π2 ∧ π2 < k / χ ∧
      gapFn χ k cbar cund Z ((k - (1 + χ) * ((cbar - cund) / (4 * Z))) / χ) = 0 ∧
      gapFn χ k cbar cund Z π2 = 0 ∧ gapFn χ k cbar cund Z (k / χ) = 0 ∧
      ∀ x, πL ≤ x → gapFn χ k cbar cund Z x = 0 →
        x = (k - (1 + χ) * ((cbar - cund) / (4 * Z))) / χ ∨ x = π2 ∨ x = k / χ := by
  have hχ1 : 0 < 1 + χ := by linarith
  have hsb0 := thr_nonneg χ cbar
  have hsu0 := thr_nonneg χ cund
  set π1 := (k - (1 + χ) * ((cbar - cund) / (4 * Z))) / χ with hπ1def
  set a := Z - thr χ cund - k with ha
  set b := Z + thr χ cbar - k with hb
  have hGA : ∀ x, πL ≤ x → x ≤ a → gapFn χ k cbar cund Z x = χ * (π1 - x) / (1 + χ) :=
    fun x h1 h2 => gapFn_regimeA χ k cbar cund Z x hχ hZ hcb hcu (by linarith) (by linarith)
  have hL1' : πL < π1 := by
    rw [hGA πL le_rfl (by linarith)] at hGL
    have := (div_pos_iff_of_pos_right hχ1).1 hGL
    have := (mul_pos_iff_of_pos_left hχ).1 this
    linarith
  have hπ1a : π1 < a := by linarith
  have hG1 : gapFn χ k cbar cund Z π1 = 0 := by
    rw [hGA π1 hL1'.le hπ1a.le]
    simp
  have hGa : gapFn χ k cbar cund Z a < 0 := by
    rw [hGA a (by linarith) le_rfl]
    exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hχ (by linarith)) hχ1
  have hbk : b < k / χ := by linarith
  have hGb : 0 < gapFn χ k cbar cund Z b := by
    rw [gapFn_float χ k cbar cund Z b hχ1 hZ (by linarith)]
    have : χ * b < k := by rwa [lt_div_iff₀ hχ, mul_comm] at hbk
    exact div_pos (by linarith) hχ1
  have hab : a ≤ b := by linarith
  obtain ⟨π2, hπ2, hG2⟩ := intermediate_value_Icc hab
    (gapFn_continuous χ k cbar cund Z hχ1 hZ).continuousOn
    (show (0 : ℝ) ∈ Icc (gapFn χ k cbar cund Z a) (gapFn χ k cbar cund Z b) from
      ⟨hGa.le, hGb.le⟩)
  have ha2 : a < π2 := by
    rcases (mem_Icc.1 hπ2).1.lt_or_eq with h | h
    · exact h
    · rw [← h] at hG2
      linarith
  have hb2 : π2 < b := by
    rcases (mem_Icc.1 hπ2).2.lt_or_eq with h | h
    · exact h
    · rw [h] at hG2
      linarith
  have hG3 : gapFn χ k cbar cund Z (k / χ) = 0 := by
    rw [gapFn_float χ k cbar cund Z _ hχ1 hZ (by linarith)]
    field_simp
    ring
  refine ⟨π2, ha2, hb2, hL1', by linarith, by linarith, hG1, hG2, hG3, fun x hx hGx => ?_⟩
  by_contra hne
  push Not at hne
  obtain ⟨n1, n2, n3⟩ := hne
  rcases lt_or_gt_of_ne n1 with h1 | h1
  · exact at_most_three χ k cbar cund Z πL hχ hZ hcb hcu hL1 hL2 x π1 π2 (k / χ) hx h1
      (by linarith) (by linarith) ⟨hGx, hG1, hG2, hG3⟩
  rcases lt_or_gt_of_ne n2 with h2 | h2
  · exact at_most_three χ k cbar cund Z πL hχ hZ hcb hcu hL1 hL2 π1 x π2 (k / χ) hL1'.le h1
      h2 (by linarith) ⟨hG1, hGx, hG2, hG3⟩
  rcases lt_or_gt_of_ne n3 with h3 | h3
  · exact at_most_three χ k cbar cund Z πL hχ hZ hcb hcu hL1 hL2 π1 π2 x (k / χ) hL1'.le
      (by linarith) h2 h3 ⟨hG1, hG2, hGx, hG3⟩
  · exact at_most_three χ k cbar cund Z πL hχ hZ hcb hcu hL1 hL2 π1 π2 (k / χ) x hL1'.le
      (by linarith) (by linarith) h3 ⟨hG1, hG2, hG3, hGx⟩

/-- O&R Fig. 9.12 (T25): in the three-equilibrium configuration of `exactly_three`, the
costs must be asymmetric, `c̄ > c̲` (the book never states this). -/
theorem exactly_three_needs_cbar_gt (χ k cbar cund Z : ℝ) (hχ : 0 < χ) (hZ : 0 < Z)
    (hπ1 : k + (k - (1 + χ) * ((cbar - cund) / (4 * Z))) / χ < Z - thr χ cund)
    (hfn40 : Z + thr χ cbar < k + k / χ) : cund < cbar := by
  have hχ1 : 0 < 1 + χ := by linarith
  have hsb := thr_nonneg χ cbar
  have hsu0 := thr_nonneg χ cund
  have h : (k - (1 + χ) * ((cbar - cund) / (4 * Z))) / χ < k / χ := by linarith
  rw [div_lt_div_iff_of_pos_right hχ] at h
  have h2 : 0 < (1 + χ) * ((cbar - cund) / (4 * Z)) := by linarith
  have h3 := (mul_pos_iff_of_pos_left hχ1).1 h2
  have := (div_pos_iff_of_pos_right (by positivity : (0 : ℝ) < 4 * Z)).1 h3
  linarith

/-- O&R p. 652, fn 40, with exact equality: if `k + k/χ = Z + s̄` and the gap is negative at
the start `a` of the convex regime, then the convex regime `[a, k/χ)` contains **no**
equilibrium (so there are only two): strict fn 40 is needed for three. -/
theorem fn40_equality_two (χ k cbar cund Z x : ℝ) (hχ : 0 < χ) (hZ : 0 < Z)
    (hL : thr χ cbar - Z ≤ Z - thr χ cund)
    (heq : k + k / χ = Z + thr χ cbar)
    (hGa : gapFn χ k cbar cund Z (Z - thr χ cund - k) < 0)
    (hx1 : Z - thr χ cund - k ≤ x) (hx2 : x < k / χ) : gapFn χ k cbar cund Z x ≠ 0 := by
  have hχ1 : 0 < 1 + χ := by linarith
  set a := Z - thr χ cund - k
  set b := k / χ
  have hbk : Z + thr χ cbar - k = b := by linarith
  have hGM : ∀ y, a ≤ y → y ≤ b → gapFn χ k cbar cund Z y =
      1 / (4 * Z * (1 + χ)) * y ^ 2 + (2 * (k + Z) / (4 * Z * (1 + χ)) - 1) * y +
        ((k + Z) ^ 2 - thr χ cbar ^ 2) / (4 * Z * (1 + χ)) := by
    intro y h1 h2
    unfold gapFn
    rw [expDep_regimeM χ k cbar cund Z y hχ1 hZ (by linarith) (by linarith) (by linarith),
      quad_M_form χ k (thr χ cbar) Z y hχ1 hZ]
  have hχb : χ * b = k := by
    simp only [b]
    field_simp
  have hGb : gapFn χ k cbar cund Z b = 0 := by
    rw [gapFn_float χ k cbar cund Z b hχ1 hZ (by linarith), hχb, sub_self, zero_div]
  intro hx
  have hax : a < x := by
    rcases hx1.lt_or_eq with h | h
    · exact h
    · rw [← h] at hx; linarith
  have hab : a ≤ b := by linarith
  have qx := hx
  have qb := hGb
  rw [hGM x hx1 hx2.le] at qx
  rw [hGM b hab le_rfl] at qb
  have hfac := quad_factor _ _ _ x b hx2 qx qb a
  have hqa := hGa
  rw [hGM a le_rfl hab, hfac] at hqa
  have : 0 < 1 / (4 * Z * (1 + χ)) * (a - x) * (a - b) := by
    have := mul_pos_of_neg_of_neg (show a - x < 0 by linarith) (show a - b < 0 by linarith)
    rw [mul_assoc]
    exact mul_pos (by positivity) this
  linarith

/-- O&R fn 38 (T25, general existence): for `k > 0`, over all `πᵉ ∈ ℝ` (thresholds clamped)
an equilibrium `πᵉ = Eπ` always exists. -/
theorem eqm_exists (χ k cbar cund Z : ℝ) (hχ : 0 < χ) (hZ : 0 < Z) (hk : 0 < k) :
    ∃ πe, gapFn χ k cbar cund Z πe = 0 := by
  have hχ1 : 0 < 1 + χ := by linarith
  have hsb0 := thr_nonneg χ cbar
  have hsu0 := thr_nonneg χ cund
  set lo := -Z - thr χ cund - k
  set hi := max (k / χ) (Z + thr χ cbar - k)
  have hkχ : 0 < k / χ := div_pos hk hχ
  have hlohi : lo ≤ hi := le_trans (by linarith) (le_max_left _ _)
  have hGlo : 0 ≤ gapFn χ k cbar cund Z lo := by
    unfold gapFn
    rw [expDep_alwaysRevalue χ k cbar cund Z lo hχ1 hZ (by linarith)]
    have : (k + lo) / (1 + χ) - lo = (k - χ * lo) / (1 + χ) := by field_simp; ring
    rw [this]
    exact div_nonneg (by nlinarith) hχ1.le
  have hGhi : gapFn χ k cbar cund Z hi ≤ 0 := by
    have hhi : Z + thr χ cbar ≤ k + hi := by
      have := le_max_right (k / χ) (Z + thr χ cbar - k)
      linarith
    rw [gapFn_float χ k cbar cund Z hi hχ1 hZ hhi]
    have h1 : k / χ ≤ hi := le_max_left _ _
    have : k ≤ χ * hi := by rwa [div_le_iff₀ hχ, mul_comm] at h1
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) hχ1.le
  obtain ⟨πe, -, h⟩ := intermediate_value_Icc' hlohi
    (gapFn_continuous χ k cbar cund Z hχ1 hZ).continuousOn
    (show (0 : ℝ) ∈ Icc (gapFn χ k cbar cund Z hi) (gapFn χ k cbar cund Z lo) from
      ⟨hGhi, hGlo⟩)
  exact ⟨πe, h⟩

/-- O&R p. 651: while `z̄` is interior (`−Z < s̄ − k − πᵉ < Z`), `dz̄/dπᵉ = −1`. -/
theorem hasDerivAt_zbarC (sb k Z πe : ℝ) (h1 : -Z < sb - (k + πe)) (h2 : sb - (k + πe) < Z) :
    HasDerivAt (fun x => zbarC sb (k + x) Z) (-1) πe := by
  have hev : (fun x => sb - (k + x)) =ᶠ[nhds πe] fun x => zbarC sb (k + x) Z := by
    have : Ioo (sb - k - Z) (sb - k + Z) ∈ nhds πe := Ioo_mem_nhds (by linarith) (by linarith)
    filter_upwards [this] with x hx
    unfold zbarC
    rw [min_eq_left (by linarith [hx.1]), max_eq_left (by linarith [hx.2])]
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev.symm
  have := ((hasDerivAt_id' πe).const_add k).const_sub sb
  simpa using this

/-- O&R p. 651: while `z̲` is interior (`−Z < −s̲ − k − πᵉ < Z`), `dz̲/dπᵉ = −1`. -/
theorem hasDerivAt_zundC (su k Z πe : ℝ) (h1 : -Z < -su - (k + πe))
    (h2 : -su - (k + πe) < Z) :
    HasDerivAt (fun x => zundC su (k + x) Z) (-1) πe := by
  have hev : (fun x => -su - (k + x)) =ᶠ[nhds πe] fun x => zundC su (k + x) Z := by
    have : Ioo (-su - k - Z) (-su - k + Z) ∈ nhds πe := Ioo_mem_nhds (by linarith) (by linarith)
    filter_upwards [this] with x hx
    unfold zundC
    rw [max_eq_left (by linarith [hx.2]), min_eq_left (by linarith [hx.1])]
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev.symm
  have := ((hasDerivAt_id' πe).const_add k).const_sub (-su)
  simpa using this

/-- O&R Fig. 9.12 (T25): the convex branch has a segment steeper than the 45° line (slope of
`Eπ` above `1` at its top end `k + πᵉ = Z + s̄`) iff `s̄ > 2χZ`. -/
theorem steep_iff (χ sb Z : ℝ) (hχ : 0 < 1 + χ) (hZ : 0 < Z) :
    1 < 1 / (1 + χ) * (1 / 2 + (Z + sb) / (2 * Z)) ↔ 2 * χ * Z < sb := by
  rw [show 1 / (1 + χ) * (1 / 2 + (Z + sb) / (2 * Z)) = (2 * Z + sb) / (2 * Z * (1 + χ)) by
    field_simp; ring, lt_div_iff₀ (by positivity)]
  constructor <;> intro h <;> nlinarith

/-- O&R Fig. 9.12 (T25): in the three-equilibrium configuration of `exactly_three` the convex
branch must cross the 45° line from below, which forces `s̄ > 2χZ`. -/
theorem exactly_three_needs_steep (χ k cbar cund Z πL : ℝ) (hχ : 0 < χ) (hZ : 0 < Z)
    (hcb : 0 ≤ cbar) (hcu : 0 ≤ cund) (hL1 : thr χ cbar - Z < k + πL)
    (hL2 : k + πL < Z - thr χ cund)
    (hπ1 : k + (k - (1 + χ) * ((cbar - cund) / (4 * Z))) / χ < Z - thr χ cund)
    (hfn40 : Z + thr χ cbar < k + k / χ) : 2 * χ * Z < thr χ cbar := by
  have hχ1 : 0 < 1 + χ := by linarith
  have hsb0 := thr_nonneg χ cbar
  have hsu0 := thr_nonneg χ cund
  set a := Z - thr χ cund - k
  set b := Z + thr χ cbar - k
  set π1 := (k - (1 + χ) * ((cbar - cund) / (4 * Z))) / χ
  have hab : a ≤ b := by linarith
  have hGa : gapFn χ k cbar cund Z a < 0 := by
    rw [gapFn_regimeA χ k cbar cund Z a hχ hZ hcb hcu (by linarith) (by linarith)]
    exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hχ (by linarith)) hχ1
  have hbk : b < k / χ := by linarith
  have hGb : 0 < gapFn χ k cbar cund Z b := by
    rw [gapFn_float χ k cbar cund Z b hχ1 hZ (by linarith)]
    have : χ * b < k := by rwa [lt_div_iff₀ hχ, mul_comm] at hbk
    exact div_pos (by linarith) hχ1
  have hGM : ∀ y, a ≤ y → y ≤ b → gapFn χ k cbar cund Z y =
      1 / (4 * Z * (1 + χ)) * y ^ 2 + (2 * (k + Z) / (4 * Z * (1 + χ)) - 1) * y +
        ((k + Z) ^ 2 - thr χ cbar ^ 2) / (4 * Z * (1 + χ)) := by
    intro y h1 h2
    unfold gapFn
    rw [expDep_regimeM χ k cbar cund Z y hχ1 hZ (by linarith) (by linarith) (by linarith),
      quad_M_form χ k (thr χ cbar) Z y hχ1 hZ]
  rw [hGM a le_rfl hab] at hGa
  rw [hGM b hab le_rfl] at hGb
  set α := 1 / (4 * Z * (1 + χ))
  set β := 2 * (k + Z) / (4 * Z * (1 + χ)) - 1
  have hαpos : 0 < α := by positivity
  have hdiff : 0 < (b - a) * (α * (a + b) + β) := by nlinarith
  have hba : 0 < b - a := by
    rcases hab.lt_or_eq with h | h
    · linarith
    · rw [h, sub_self, zero_mul] at hdiff
      exact absurd hdiff (lt_irrefl 0)
  have hpos : 0 < α * (a + b) + β := (mul_pos_iff_of_pos_left hba).1 hdiff
  have hslope : 0 < 2 * α * b + β := by nlinarith
  have e : 2 * α * b + β = (2 * Z + thr χ cbar) / (2 * Z * (1 + χ)) - 1 := by
    simp only [α, β, b]
    field_simp
    ring
  rw [e, sub_pos, lt_div_iff₀ (by positivity)] at hslope
  nlinarith

/-! ## Two counterexamples to readings of Fig. 9.12 and fn 40 -/

/-- The threshold in the examples: `√(3/10 · 6/5) = 3/5`. -/
theorem thr_example : thr (1 / 5) (3 / 10) = 3 / 5 := by
  unfold thr
  rw [show (3 / 10 : ℝ) * (1 + 1 / 5) = (3 / 5) ^ 2 by norm_num]
  exact Real.sqrt_sq (by norm_num)

/-- Correction to Fig. 9.12 (T25): three equilibria do **not** require `c̄ > c̲`. With
`χ = 1/5`, `Z = 1`, `k = 27/100` and `c̄ = c̲ = 3/10` (`s̄ = s̲ = 3/5`) there are three
equilibria `π₁ < π₂ < π₃ = k/χ = 27/20` on the book's domain `πᵉ ≥ −27/100`; the low ones
lie on the convex branch, not on a flat branch below the free-float line. -/
theorem three_eqm_symmetric_costs :
    ∃ x1 x2 x3 : ℝ, -27 / 100 ≤ x1 ∧ x1 < x2 ∧ x2 < x3 ∧
      gapFn (1 / 5) (27 / 100) (3 / 10) (3 / 10) 1 x1 = 0 ∧
      gapFn (1 / 5) (27 / 100) (3 / 10) (3 / 10) 1 x2 = 0 ∧
      gapFn (1 / 5) (27 / 100) (3 / 10) (3 / 10) 1 x3 = 0 := by
  have hM : ∀ x : ℝ, 13 / 100 ≤ x → x ≤ 133 / 100 →
      gapFn (1 / 5) (27 / 100) (3 / 10) (3 / 10) 1 x =
        ((27 / 100 + x + 1) ^ 2 - (3 / 5) ^ 2) / (4 * 1 * (1 + 1 / 5)) - x := by
    intro x h1 h2
    unfold gapFn
    rw [expDep_regimeM (1 / 5) (27 / 100) (3 / 10) (3 / 10) 1 x (by norm_num) (by norm_num)
      (by rw [thr_example]; linarith) (by rw [thr_example]; linarith)
      (by rw [thr_example]; linarith), thr_example]
  have hcont := (gapFn_continuous (1 / 5) (27 / 100) (3 / 10) (3 / 10) 1 (by norm_num)
    (by norm_num)).continuousOn (s := Icc (13 / 100) (11 / 10))
  have hcont2 := (gapFn_continuous (1 / 5) (27 / 100) (3 / 10) (3 / 10) 1 (by norm_num)
    (by norm_num)).continuousOn (s := Icc (11 / 10) (13 / 10))
  have g1 := hM (13 / 100) (by norm_num) (by norm_num)
  have g2 := hM (11 / 10) (by norm_num) (by norm_num)
  have g3 := hM (13 / 10) (by norm_num) (by norm_num)
  norm_num at g1 g2 g3
  obtain ⟨x1, hx1, hg1⟩ := intermediate_value_Icc' (by norm_num) hcont
    (show (0 : ℝ) ∈ Icc (gapFn (1 / 5) (27 / 100) (3 / 10) (3 / 10) 1 (11 / 10))
      (gapFn (1 / 5) (27 / 100) (3 / 10) (3 / 10) 1 (13 / 100)) by
        rw [g1, g2]; norm_num)
  obtain ⟨x2, hx2, hg2⟩ := intermediate_value_Icc (by norm_num) hcont2
    (show (0 : ℝ) ∈ Icc (gapFn (1 / 5) (27 / 100) (3 / 10) (3 / 10) 1 (11 / 10))
      (gapFn (1 / 5) (27 / 100) (3 / 10) (3 / 10) 1 (13 / 10)) by
        rw [g2, g3]; norm_num)
  have hx12 : x1 < x2 := by
    rcases (mem_Icc.1 hx1).2.lt_or_eq with h | h
    · exact lt_of_lt_of_le h (mem_Icc.1 hx2).1
    · rw [h, g2] at hg1
      norm_num at hg1
  have hG3 : gapFn (1 / 5) (27 / 100) (3 / 10) (3 / 10) 1 (27 / 20) = 0 := by
    rw [gapFn_float (1 / 5) (27 / 100) (3 / 10) (3 / 10) 1 (27 / 20) (by norm_num)
      (by norm_num) (by rw [thr_example]; norm_num)]
    norm_num
  refine ⟨x1, x2, 27 / 20, by linarith [(mem_Icc.1 hx1).1], hx12,
    by linarith [(mem_Icc.1 hx2).2], hg1, hg2, hG3⟩

/-- The threshold in the second example: `√(1/8 · 2) = 1/2`. -/
theorem thr_example2 : thr 1 (1 / 8) = 1 / 2 := by
  unfold thr
  rw [show (1 / 8 : ℝ) * (1 + 1) = (1 / 2) ^ 2 by norm_num]
  exact Real.sqrt_sq (by norm_num)

/-- Correction to fn 40 (T25): fn 40 is not necessary for `πᵉ = k/χ` to be an equilibrium.
With `χ = 1`, `Z = 1`, `k = 1/4`, `c̄ = c̲ = 1/8` (`s̄ = s̲ = 1/2`), `πᵉ = k/χ = 1/4` is an
equilibrium (in regime A, where the government sometimes pegs), although
`(1 + χ)k/χ − Z = −1/2 < s̄`. -/
theorem fn40_not_necessary :
    gapFn 1 (1 / 4) (1 / 8) (1 / 8) 1 ((1 / 4) / 1) = 0 ∧
      (1 + 1) * (1 / 4) / 1 - 1 < thr 1 (1 / 8) := by
  refine ⟨?_, by rw [thr_example2]; norm_num⟩
  unfold gapFn
  rw [symmetric_flat_is_float 1 (1 / 4) (1 / 8) 1 _ (by norm_num) (by norm_num) (by norm_num)
    (by rw [thr_example2]; norm_num) (by rw [thr_example2]; norm_num)]
  norm_num


end ObstfeldRogoff.NominalRigidities.EscapeClausePeg

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Pegs, floats and the optimal exchange-rate feedback rule (Poole)

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §9.4.1,
pp. 631–632, and Exercise 3, pp. 657–658.

The stochastic small open economy of Exercise 3 (all of `p*`, `i*`, `ȳ`, `q̄` normalised to 0):
* UIP `i_{t+1} = E_t e_{t+1} − e_t`;
* Lucas supply `y_t = θ (p_t − E_{t−1} p_t)`;
* goods demand `y_t = δ (e_t − p_t) + ε_t`;
* money market `m_t − p_t = −η i_{t+1} + φ y_t + v_t`.

**Stochastic structure.** The shocks `(ε_t, v_t)` are iid over a finite state space `S`
with probabilities `prob`; the only moment assumptions used are `E ε = E v = 0` and
`E ε v = 0` (the book's normality and independence are used only through these).
A history is a list of realised states, newest first; every endogenous variable is a
function of the history (an event tree). `E_{t−1}` at the node `h` is the average over the
next state `s`, and `E_t` at the node `s :: h` averages over the state after that. So
the equilibrium concept is the full history-dependent rational-expectations equilibrium,
with no minimal-state-variable restriction imposed a priori.

**No-bubble condition.** The only selection device is that the price level is bounded
on the tree (`Bounded p`).

Main results.
* Under the feedback rule `m − m̄ = Φ (e − ē)` (with `ē = m̄`), the expected price level
  obeys `E_{t−1} x_{t+1} = λ x_t` with `λ = (η + 1 − Φ)/η`. On a finite event tree a
  bounded solution of this is identically zero once `|λ| > 1`, which holds exactly when
  `Φ < 1` or `Φ > 1 + 2η`. In that region the equilibrium is unique among bounded ones and
  output is `y = θ ((η − Φ) ε − δ v)/((η − Φ)(θ + δ) + δ (1 + φ θ))`.
* For `1 < Φ < 1 + 2η` there are bounded sunspot equilibria with different output.
* Float (`Φ = 0`, part (a)), peg (part (b)), the Poole ranking (part (c)).
* Part (d): with `u = η − Φ` the conditional output variance is
  `θ² (u² σ_ε² + δ² σ_v²)/(u (θ + δ) + δ (1 + φ θ))²`. Cauchy–Schwarz gives its exact
  global minimum and the unique minimiser `u* = (θ + δ) δ σ_v²/((1 + φ θ) σ_ε²)`, so
  `Φ* = η − u* < η`. The peg is only the limit `Φ → −∞`: the book's `Φ → ∞` (p. 632) and
  "between 0 and ∞" (Ex. 3(d)) have the wrong sign.
-/

namespace ObstfeldRogoff.NominalRigidities.PooleRegimeChoice

open Finset Filter Topology

/-- O&R Exercise 3, p. 657: the structural parameters `θ` (supply slope), `δ` (demand
elasticity to the real exchange rate), `η` (interest semi-elasticity of money demand),
`φ` (income elasticity of money demand), all positive. -/
structure PooleParams where
  θ : ℝ
  δ : ℝ
  η : ℝ
  φ : ℝ
  θ_pos : 0 < θ
  δ_pos : 0 < δ
  η_pos : 0 < η
  φ_pos : 0 < φ

/-- O&R Exercise 3, p. 657: iid shocks on a finite state space. `eps` is the goods-demand
shock `ε`, `v` the money-demand shock; both have mean zero and are uncorrelated. -/
structure PooleShocks (S : Type) [Fintype S] where
  prob : S → ℝ
  eps : S → ℝ
  v : S → ℝ
  prob_nonneg : ∀ s, 0 ≤ prob s
  prob_sum : ∑ s, prob s = 1
  eps_mean : ∑ s, prob s * eps s = 0
  v_mean : ∑ s, prob s * v s = 0
  eps_v_uncorr : ∑ s, prob s * (eps s * v s) = 0

variable {S : Type} [Fintype S]

/-- O&R Exercise 3, p. 657: the expectation of a function of the current state. -/
def expect (Sh : PooleShocks S) (f : S → ℝ) : ℝ := ∑ s, Sh.prob s * f s

/-- O&R Exercise 3, p. 657: the variance `σ_ε²` of the goods-demand shock. -/
def sigE2 (Sh : PooleShocks S) : ℝ := expect Sh fun s => Sh.eps s ^ 2

/-- O&R Exercise 3, p. 657: the variance `σ_v²` of the money-demand shock. -/
def sigV2 (Sh : PooleShocks S) : ℝ := expect Sh fun s => Sh.v s ^ 2

/-- O&R Exercise 3, p. 657: the conditional expectation at the node `h` of a variable on the
event tree, averaging over the next state (`E_{t−1}` of a date-`t` variable). -/
def nodeEx (Sh : PooleShocks S) (f : List S → ℝ) (h : List S) : ℝ :=
  ∑ s, Sh.prob s * f (s :: h)

/-- The no-bubble condition used throughout (O&R p. 658 hint): a variable on the event tree
is bounded. -/
def Bounded (f : List S → ℝ) : Prop := ∃ M, ∀ h, |f h| ≤ M

/-- O&R Exercise 3, p. 657: a rational-expectations equilibrium on the event tree under a
policy relating `(m_t, e_t)`. At every node `s :: h` (current state `s`, past history `h`)
UIP, supply, goods demand, money demand and the policy hold. -/
def IsEqm (P : PooleParams) (Sh : PooleShocks S) (policy : ℝ → ℝ → Prop)
    (p e y m i : List S → ℝ) : Prop :=
  ∀ (s : S) (h : List S),
    i (s :: h) = nodeEx Sh e (s :: h) - e (s :: h) ∧
    y (s :: h) = P.θ * (p (s :: h) - nodeEx Sh p h) ∧
    y (s :: h) = P.δ * (e (s :: h) - p (s :: h)) + Sh.eps s ∧
    m (s :: h) - p (s :: h) = -P.η * i (s :: h) + P.φ * y (s :: h) + Sh.v s ∧
    policy (m (s :: h)) (e (s :: h))

/-- O&R Exercise 3(a), p. 658: the fixed money supply `m_t = m̄`. -/
def floatPolicy (mbar : ℝ) : ℝ → ℝ → Prop := fun m _ => m = mbar

/-- O&R Exercise 3(b), p. 658: the peg `e_t = ē = m̄`, money adjusting. -/
def pegPolicy (mbar : ℝ) : ℝ → ℝ → Prop := fun _ e => e = mbar

/-- O&R p. 632 and Exercise 3(d): the feedback rule `m_t − m̄ = Φ (e_t − ē)` with `ē = m̄`. -/
def feedbackPolicy (mbar Φ : ℝ) : ℝ → ℝ → Prop := fun m e => m = mbar + Φ * (e - mbar)

/-- O&R Exercise 3(d): the denominator `u (θ + δ) + δ (1 + φ θ)` of the equilibrium output
formula, as a function of `u = η − Φ`. -/
def den (P : PooleParams) (u : ℝ) : ℝ := u * (P.θ + P.δ) + P.δ * (1 + P.φ * P.θ)

/-- O&R Exercise 3(d): equilibrium output in state `s` under the rule `Φ`. -/
noncomputable def outputMSV (P : PooleParams) (Sh : PooleShocks S) (Φ : ℝ) (s : S) : ℝ :=
  P.θ * ((P.η - Φ) * Sh.eps s - P.δ * Sh.v s) / den P (P.η - Φ)

/-- O&R Exercise 3(d): equilibrium price level in state `s` under the rule `Φ`. -/
noncomputable def pMSV (P : PooleParams) (Sh : PooleShocks S) (mbar Φ : ℝ) (s : S) : ℝ :=
  mbar + outputMSV P Sh Φ s / P.θ

/-- O&R Exercise 3(d): equilibrium exchange rate in state `s` under the rule `Φ`. -/
noncomputable def eMSV (P : PooleParams) (Sh : PooleShocks S) (mbar Φ : ℝ) (s : S) : ℝ :=
  pMSV P Sh mbar Φ s + (outputMSV P Sh Φ s - Sh.eps s) / P.δ

/-- O&R Exercise 3(d): equilibrium money supply in state `s` under the rule `Φ`. -/
noncomputable def mMSV (P : PooleParams) (Sh : PooleShocks S) (mbar Φ : ℝ) (s : S) : ℝ :=
  mbar + Φ * (eMSV P Sh mbar Φ s - mbar)

/-- O&R Exercise 3(d): equilibrium nominal interest rate in state `s` under the rule `Φ`. -/
noncomputable def iMSV (P : PooleParams) (Sh : PooleShocks S) (mbar Φ : ℝ) (s : S) : ℝ :=
  mbar - eMSV P Sh mbar Φ s

/-- A variable on the event tree that depends only on the current state (value `d` at the
root, before any shock). Used to build the stationary equilibria of O&R Exercise 3. -/
def onHead (d : ℝ) (g : S → ℝ) : List S → ℝ
  | [] => d
  | s :: _ => g s

/-! ### Expectation algebra -/

/-- Linearity of the expectation (O&R Exercise 3 background). -/
theorem expect_add (Sh : PooleShocks S) (f g : S → ℝ) :
    expect Sh (fun s => f s + g s) = expect Sh f + expect Sh g := by
  unfold expect
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun s _ => by ring

/-- Linearity of the expectation (O&R Exercise 3 background). -/
theorem expect_sub (Sh : PooleShocks S) (f g : S → ℝ) :
    expect Sh (fun s => f s - g s) = expect Sh f - expect Sh g := by
  unfold expect
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun s _ => by ring

/-- Homogeneity of the expectation (O&R Exercise 3 background). -/
theorem expect_const_mul (Sh : PooleShocks S) (c : ℝ) (f : S → ℝ) :
    expect Sh (fun s => c * f s) = c * expect Sh f := by
  unfold expect
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun s _ => by ring

/-- Division by a constant commutes with the expectation (O&R Exercise 3 background). -/
theorem expect_div_const (Sh : PooleShocks S) (c : ℝ) (f : S → ℝ) :
    expect Sh (fun s => f s / c) = expect Sh f / c := by
  unfold expect
  rw [div_eq_mul_inv, Finset.sum_mul]
  exact Finset.sum_congr rfl fun s _ => by ring

/-- The expectation of a constant (O&R Exercise 3 background). -/
theorem expect_const (Sh : PooleShocks S) (c : ℝ) : expect Sh (fun _ => c) = c := by
  unfold expect
  rw [← Finset.sum_mul, Sh.prob_sum, one_mul]

/-- `E ε = 0` (O&R Exercise 3, p. 657). -/
theorem expect_eps (Sh : PooleShocks S) : expect Sh (fun s => Sh.eps s) = 0 := Sh.eps_mean

/-- `E v = 0` (O&R Exercise 3, p. 657). -/
theorem expect_v (Sh : PooleShocks S) : expect Sh (fun s => Sh.v s) = 0 := Sh.v_mean

/-- The node expectation is the expectation over the next state (O&R Exercise 3). -/
theorem nodeEx_eq_expect (Sh : PooleShocks S) (f : List S → ℝ) (h : List S) :
    nodeEx Sh f h = expect Sh (fun s => f (s :: h)) := rfl

/-- A bounded variable has a bounded conditional expectation (O&R Exercise 3). -/
theorem abs_nodeEx_le (Sh : PooleShocks S) (f : List S → ℝ) (M : ℝ) (hM : ∀ g, |f g| ≤ M)
    (h : List S) : |nodeEx Sh f h| ≤ M := by
  unfold nodeEx
  calc |∑ s, Sh.prob s * f (s :: h)| ≤ ∑ s, |Sh.prob s * f (s :: h)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s, Sh.prob s * M := by
        refine Finset.sum_le_sum fun s _ => ?_
        rw [abs_mul, abs_of_nonneg (Sh.prob_nonneg s)]
        exact mul_le_mul_of_nonneg_left (hM _) (Sh.prob_nonneg s)
    _ = M := by rw [← Finset.sum_mul, Sh.prob_sum, one_mul]

/-- The node expectation of a variable depending only on the current state (O&R Ex. 3). -/
theorem nodeEx_onHead (Sh : PooleShocks S) (d : ℝ) (g : S → ℝ) (h : List S) :
    nodeEx Sh (onHead d g) h = expect Sh g := rfl

omit [Fintype S] in
/-- A variable depending only on the current state is bounded (O&R Exercise 3). -/
theorem bounded_onHead [Finite S] (d : ℝ) (g : S → ℝ) : Bounded (onHead d g) := by
  have := Fintype.ofFinite S
  refine ⟨|d| + ∑ s, |g s|, fun h => ?_⟩
  have hsum : 0 ≤ ∑ s, |g s| := Finset.sum_nonneg fun s _ => abs_nonneg _
  cases h with
  | nil => simp only [onHead]; linarith
  | cons s _ =>
    simp only [onHead]
    have := Finset.single_le_sum (f := fun s => |g s|) (fun s _ => abs_nonneg (g s))
      (Finset.mem_univ s)
    linarith [abs_nonneg d]

/-! ### Bounded solutions of the expected-level recursion on the event tree -/

/-- The no-bubble lemma on a finite event tree: a bounded `x` with `E_{t−1} x_{t+1} = λ x_t`
at every node and `|λ| > 1` is identically zero (O&R p. 658; the stochastic counterpart
of the no-bubble argument of §9.2.3). -/
theorem tree_eigen_bounded_zero (Sh : PooleShocks S) (x : List S → ℝ) (lam : ℝ)
    (hlam : 1 < |lam|) (hx : ∀ h, nodeEx Sh x h = lam * x h) (hb : Bounded x) :
    ∀ h, x h = 0 := by
  obtain ⟨M, hM⟩ := hb
  have key : ∀ n : ℕ, ∀ h, |x h| * |lam| ^ n ≤ M := by
    intro n
    induction n with
    | zero => intro h; simpa using hM h
    | succ n ih =>
      intro h
      have hmul : nodeEx Sh (fun g => x g * |lam| ^ n) h = nodeEx Sh x h * |lam| ^ n := by
        unfold nodeEx
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun s _ => by ring
      have hbound := abs_nodeEx_le Sh (fun g => x g * |lam| ^ n) M
        (fun g => by rw [abs_mul, abs_pow, abs_abs]; exact ih g) h
      rw [hmul, hx, abs_mul, abs_mul, abs_pow, abs_abs] at hbound
      calc |x h| * |lam| ^ (n + 1) = |lam| * |x h| * |lam| ^ n := by ring
        _ ≤ M := hbound
  intro h
  by_contra hne
  have hpos : 0 < |x h| := abs_pos.mpr hne
  have ht : Tendsto (fun n : ℕ => |x h| * |lam| ^ n) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt hlam).const_mul_atTop hpos
  obtain ⟨n, hn⟩ := (ht.eventually_gt_atTop M).exists
  exact absurd (key n h) (not_le.mpr hn)

/-- O&R p. 632 / Ex. 3(d): the root `λ = (η + 1 − Φ)/η` of the expected-level recursion is
outside the unit circle exactly when `Φ < 1` or `Φ > 1 + 2η` (the determinacy region). -/
theorem one_lt_abs_lambda_iff {η Φ : ℝ} (hη : 0 < η) :
    1 < |(η + 1 - Φ) / η| ↔ Φ < 1 ∨ 1 + 2 * η < Φ := by
  rw [abs_div, abs_of_pos hη, lt_div_iff₀ hη, one_mul, lt_abs]
  constructor
  · rintro (h | h)
    · left; linarith
    · right; linarith
  · rintro (h | h)
    · left; linarith
    · right; linarith

/-- O&R p. 632 / Ex. 3(d): the root `λ` is strictly inside the unit circle exactly when
`1 < Φ < 1 + 2η` (the indeterminacy region). -/
theorem abs_lambda_lt_one_iff {η Φ : ℝ} (hη : 0 < η) :
    |(η + 1 - Φ) / η| < 1 ↔ 1 < Φ ∧ Φ < 1 + 2 * η := by
  rw [abs_div, abs_of_pos hη, div_lt_iff₀ hη, one_mul, abs_lt]
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> linarith
  · rintro ⟨h1, h2⟩; constructor <;> linarith

/-! ### Expected levels in any equilibrium -/

/-- O&R Exercise 3: in any equilibrium (any policy) expected output is zero,
`E_{t−1} y_t = 0`, because output responds only to price surprises. -/
theorem eqm_nodeEx_y {P : PooleParams} {Sh : PooleShocks S} {policy : ℝ → ℝ → Prop}
    {p e y m i : List S → ℝ} (hE : IsEqm P Sh policy p e y m i) (h : List S) :
    nodeEx Sh y h = 0 := by
  have hf : (fun s => y (s :: h)) = fun s => P.θ * (p (s :: h) - nodeEx Sh p h) :=
    funext fun s => (hE s h).2.1
  have h1 : expect Sh (fun s => y (s :: h)) =
      expect Sh (fun s => P.θ * (p (s :: h) - nodeEx Sh p h)) := congrArg _ hf
  simp only [expect_const_mul, expect_sub, expect_const] at h1
  rw [nodeEx_eq_expect, h1, nodeEx_eq_expect, sub_self, mul_zero]

/-- O&R Exercise 3: in any equilibrium (any policy) `E_{t−1} e_t = E_{t−1} p_t`, i.e. the
expected real exchange rate is at its (normalised) long-run value 0. -/
theorem eqm_nodeEx_e {P : PooleParams} {Sh : PooleShocks S} {policy : ℝ → ℝ → Prop}
    {p e y m i : List S → ℝ} (hE : IsEqm P Sh policy p e y m i) (h : List S) :
    nodeEx Sh e h = nodeEx Sh p h := by
  have hf : (fun s => y (s :: h)) =
      fun s => P.δ * (e (s :: h) - p (s :: h)) + Sh.eps s :=
    funext fun s => (hE s h).2.2.1
  have h1 : expect Sh (fun s => y (s :: h)) =
      expect Sh (fun s => P.δ * (e (s :: h) - p (s :: h)) + Sh.eps s) := congrArg _ hf
  simp only [expect_add, expect_const_mul, expect_sub, expect_eps] at h1
  have hy : expect Sh (fun s => y (s :: h)) = 0 := eqm_nodeEx_y hE h
  rw [hy, add_zero] at h1
  have hd : P.δ ≠ 0 := P.δ_pos.ne'
  have h2 : expect Sh (fun s => e (s :: h)) - expect Sh (fun s => p (s :: h)) = 0 := by
    rcases mul_eq_zero.mp h1.symm with h3 | h3
    · exact absurd h3 hd
    · exact h3
  rw [nodeEx_eq_expect, nodeEx_eq_expect]
  linarith

/-- O&R p. 632 / Ex. 3(d): under the feedback rule the expected price level
`c_h = E_{t−1} p_t` satisfies `η (E_{t−1} c_{t+1} − m̄) = (η + 1 − Φ)(c_t − m̄)`. -/
theorem feedback_level_recursion {P : PooleParams} {Sh : PooleShocks S} {mbar Φ : ℝ}
    {p e y m i : List S → ℝ} (hE : IsEqm P Sh (feedbackPolicy mbar Φ) p e y m i)
    (h : List S) :
    P.η * (nodeEx Sh (nodeEx Sh p) h - mbar) = (P.η + 1 - Φ) * (nodeEx Sh p h - mbar) := by
  have hmon : (fun s => m (s :: h) - p (s :: h)) = fun s =>
      -P.η * (nodeEx Sh p (s :: h) - e (s :: h)) + P.φ * y (s :: h) + Sh.v s := by
    funext s
    rw [(hE s h).2.2.2.1, (hE s h).1, eqm_nodeEx_e hE (s :: h)]
  have hpol : (fun s => m (s :: h)) = fun s => mbar + Φ * (e (s :: h) - mbar) :=
    funext fun s => (hE s h).2.2.2.2
  have h1 : expect Sh (fun s => m (s :: h) - p (s :: h)) = expect Sh (fun s =>
      -P.η * (nodeEx Sh p (s :: h) - e (s :: h)) + P.φ * y (s :: h) + Sh.v s) :=
    congrArg _ hmon
  have h2 : expect Sh (fun s => m (s :: h)) =
      expect Sh (fun s => mbar + Φ * (e (s :: h) - mbar)) := congrArg _ hpol
  simp only [expect_add, expect_sub, expect_const_mul, expect_const, expect_v] at h1 h2
  have hy : expect Sh (fun s => y (s :: h)) = 0 := eqm_nodeEx_y hE h
  have he : expect Sh (fun s => e (s :: h)) = expect Sh (fun s => p (s :: h)) :=
    eqm_nodeEx_e hE h
  rw [hy, he] at h1
  rw [he] at h2
  rw [nodeEx_eq_expect Sh (nodeEx Sh p), nodeEx_eq_expect Sh p]
  linear_combination h1 - h2

/-- O&R p. 632 / Ex. 3(d): in the determinacy region `Φ < 1` or `Φ > 1 + 2η`, every
equilibrium with a bounded price level has `E_{t−1} p_t = m̄` at every node. -/
theorem feedback_expected_price_eq {P : PooleParams} {Sh : PooleShocks S} {mbar Φ : ℝ}
    (hdet : Φ < 1 ∨ 1 + 2 * P.η < Φ) {p e y m i : List S → ℝ}
    (hE : IsEqm P Sh (feedbackPolicy mbar Φ) p e y m i) (hb : Bounded p) (h : List S) :
    nodeEx Sh p h = mbar := by
  have hη := P.η_pos
  have hx : ∀ g, nodeEx Sh (fun g' => nodeEx Sh p g' - mbar) g =
      (P.η + 1 - Φ) / P.η * (nodeEx Sh p g - mbar) := by
    intro g
    have hr := feedback_level_recursion hE g
    have hsub : nodeEx Sh (fun g' => nodeEx Sh p g' - mbar) g =
        nodeEx Sh (nodeEx Sh p) g - mbar := by
      rw [nodeEx_eq_expect, expect_sub, expect_const]
      rfl
    rw [hsub]
    field_simp
    linear_combination hr
  obtain ⟨M, hM⟩ := hb
  have hbx : Bounded (fun g => nodeEx Sh p g - mbar) := by
    refine ⟨M + |mbar|, fun g => ?_⟩
    have := abs_nodeEx_le Sh p M hM g
    calc |nodeEx Sh p g - mbar| ≤ |nodeEx Sh p g| + |mbar| := abs_sub _ _
      _ ≤ M + |mbar| := by linarith
  have := tree_eigen_bounded_zero Sh _ _ ((one_lt_abs_lambda_iff hη).mpr hdet) hx hbx h
  linarith

/-- O&R Exercise 3(d): the reduced form at one node. Given the equilibrium equations at
`s :: h`, output satisfies `y · den = θ ((η − Φ) ε − δ v + δ w)`, where
`w = η (E_t e_{t+1} − m̄) − (η + 1 − Φ)(E_{t−1} p_t − m̄)` is the expectation-revision
(sunspot) term. -/
theorem feedback_node_reduced_form (P : PooleParams) (mbar Φ ε v y p e m i X c : ℝ)
    (hi : i = X - e) (hs : y = P.θ * (p - c)) (hg : y = P.δ * (e - p) + ε)
    (hm : m - p = -P.η * i + P.φ * y + v) (hpol : m = mbar + Φ * (e - mbar)) :
    y * den P (P.η - Φ) = P.θ * ((P.η - Φ) * ε - P.δ * v +
      P.δ * (P.η * (X - mbar) - (P.η + 1 - Φ) * (c - mbar))) := by
  unfold den
  linear_combination (P.δ * (P.η - Φ + 1)) * hs + (P.θ * (P.η - Φ)) * hg +
    (-P.θ * P.δ) * hm + (P.θ * P.δ) * hpol + (P.θ * P.δ * P.η) * hi

/-- O&R Exercise 3(d), uniqueness: in the determinacy region and away from the pole
`den = 0`, every equilibrium with a bounded price level coincides at every node with the
stationary solution `(pMSV, eMSV, outputMSV, mMSV, iMSV)` of the current state. -/
theorem feedback_eqm_unique {P : PooleParams} {Sh : PooleShocks S} {mbar Φ : ℝ}
    (hdet : Φ < 1 ∨ 1 + 2 * P.η < Φ) (hden : den P (P.η - Φ) ≠ 0)
    {p e y m i : List S → ℝ} (hE : IsEqm P Sh (feedbackPolicy mbar Φ) p e y m i)
    (hb : Bounded p) (s : S) (h : List S) :
    y (s :: h) = outputMSV P Sh Φ s ∧ p (s :: h) = pMSV P Sh mbar Φ s ∧
      e (s :: h) = eMSV P Sh mbar Φ s ∧ m (s :: h) = mMSV P Sh mbar Φ s ∧
      i (s :: h) = iMSV P Sh mbar Φ s := by
  obtain ⟨hi, hs, hg, hm, hpol⟩ := hE s h
  have hc : nodeEx Sh p h = mbar := feedback_expected_price_eq hdet hE hb h
  have hX : nodeEx Sh e (s :: h) = mbar := by
    rw [eqm_nodeEx_e hE (s :: h)]
    exact feedback_expected_price_eq hdet hE hb (s :: h)
  have hred := feedback_node_reduced_form P mbar Φ (Sh.eps s) (Sh.v s) _ _ _ _ _ _ _
    hi hs hg hm hpol
  rw [hX, hc] at hred
  have hy : y (s :: h) = outputMSV P Sh Φ s := by
    unfold outputMSV
    rw [eq_div_iff hden, hred]
    ring
  have hθ := P.θ_pos.ne'
  have hδ := P.δ_pos.ne'
  have hp : p (s :: h) = pMSV P Sh mbar Φ s := by
    unfold pMSV
    rw [← hy, hs, hc]
    field_simp
    ring
  have he : e (s :: h) = eMSV P Sh mbar Φ s := by
    unfold eMSV
    rw [← hp, ← hy, hg]
    field_simp
    ring
  refine ⟨hy, hp, he, ?_, ?_⟩
  · unfold mMSV
    rw [← he]
    exact hpol
  · unfold iMSV
    rw [← he, hi, hX]

/-- O&R Exercise 3(d): the stationary solution has zero-mean output. -/
theorem expect_outputMSV (P : PooleParams) (Sh : PooleShocks S) (Φ : ℝ) :
    expect Sh (outputMSV P Sh Φ) = 0 := by
  have : outputMSV P Sh Φ = fun s =>
      (P.θ * (P.η - Φ) / den P (P.η - Φ)) * Sh.eps s +
        (-(P.θ * P.δ) / den P (P.η - Φ)) * Sh.v s := by
    funext s
    unfold outputMSV
    ring
  rw [this, expect_add, expect_const_mul, expect_const_mul, expect_eps, expect_v]
  ring

/-- O&R Exercise 3(d): the stationary solution has `E p = m̄`. -/
theorem expect_pMSV (P : PooleParams) (Sh : PooleShocks S) (mbar Φ : ℝ) :
    expect Sh (pMSV P Sh mbar Φ) = mbar := by
  have : pMSV P Sh mbar Φ = fun s => mbar + outputMSV P Sh Φ s / P.θ := rfl
  rw [this, expect_add, expect_const, expect_div_const, expect_outputMSV, zero_div, add_zero]

/-- O&R Exercise 3(d): the stationary solution has `E e = m̄`. -/
theorem expect_eMSV (P : PooleParams) (Sh : PooleShocks S) (mbar Φ : ℝ) :
    expect Sh (eMSV P Sh mbar Φ) = mbar := by
  have : eMSV P Sh mbar Φ = fun s =>
      pMSV P Sh mbar Φ s + (outputMSV P Sh Φ s - Sh.eps s) / P.δ := rfl
  rw [this, expect_add, expect_div_const, expect_sub, expect_eps, expect_outputMSV]
  have h2 := expect_pMSV P Sh mbar Φ
  simp only [h2, sub_zero, zero_div, add_zero]

/-- O&R Exercise 3(d), existence: away from the pole the stationary solution, placed on the
event tree, is an equilibrium with bounded variables (whatever `Φ`). -/
theorem feedback_eqm_exists (P : PooleParams) (Sh : PooleShocks S) (mbar Φ : ℝ)
    (hden : den P (P.η - Φ) ≠ 0) :
    IsEqm P Sh (feedbackPolicy mbar Φ) (onHead mbar (pMSV P Sh mbar Φ))
      (onHead mbar (eMSV P Sh mbar Φ)) (onHead 0 (outputMSV P Sh Φ))
      (onHead mbar (mMSV P Sh mbar Φ)) (onHead 0 (iMSV P Sh mbar Φ)) := by
  intro s h
  have hθ := P.θ_pos.ne'
  have hδ := P.δ_pos.ne'
  simp only [onHead, nodeEx_onHead, expect_eMSV, expect_pMSV]
  have hY : outputMSV P Sh Φ s * den P (P.η - Φ) =
      P.θ * ((P.η - Φ) * Sh.eps s - P.δ * Sh.v s) := by
    unfold outputMSV
    exact div_mul_cancel₀ _ hden
  refine ⟨rfl, ?_, ?_, ?_, rfl⟩
  · unfold pMSV
    field_simp
    ring
  · unfold eMSV
    field_simp
    ring
  · unfold iMSV mMSV eMSV pMSV
    unfold den at hY
    field_simp
    linear_combination (-1 : ℝ) * hY

/-! ### Moments of the equilibrium output -/

/-- O&R Exercise 3: `E (α ε + β v)² = α² σ_ε² + β² σ_v²` (uncorrelated shocks). -/
theorem expect_sq_comb (Sh : PooleShocks S) (α β : ℝ) :
    expect Sh (fun s => (α * Sh.eps s + β * Sh.v s) ^ 2) =
      α ^ 2 * sigE2 Sh + β ^ 2 * sigV2 Sh := by
  have hf : (fun s => (α * Sh.eps s + β * Sh.v s) ^ 2) = fun s =>
      α ^ 2 * Sh.eps s ^ 2 + (2 * α * β) * (Sh.eps s * Sh.v s) + β ^ 2 * Sh.v s ^ 2 := by
    funext s
    ring
  have hc : expect Sh (fun s => Sh.eps s * Sh.v s) = 0 := Sh.eps_v_uncorr
  rw [hf, expect_add, expect_add, expect_const_mul, expect_const_mul, expect_const_mul, hc]
  unfold sigE2 sigV2
  ring

/-- O&R Exercise 3(d): the one-period conditional variance of output as a function of
`u = η − Φ`: `θ² (u² σ_ε² + δ² σ_v²)/(u (θ + δ) + δ (1 + φ θ))²`. -/
noncomputable def outputVar (P : PooleParams) (a b u : ℝ) : ℝ :=
  P.θ ^ 2 * (u ^ 2 * a + P.δ ^ 2 * b) / den P u ^ 2

/-- O&R Exercise 3(a): the conditional output variance under the float (`u = η`). -/
noncomputable def floatVar (P : PooleParams) (a b : ℝ) : ℝ := outputVar P a b P.η

/-- O&R Exercise 3(b): the conditional output variance under the peg,
`θ² σ_ε²/(θ + δ)²`. -/
noncomputable def pegVar (P : PooleParams) (a : ℝ) : ℝ := P.θ ^ 2 * a / (P.θ + P.δ) ^ 2

/-- O&R Exercise 3(d): the variance-minimising `u* = (θ + δ) δ σ_v²/((1 + φ θ) σ_ε²)`. -/
noncomputable def optimalU (P : PooleParams) (a b : ℝ) : ℝ :=
  (P.θ + P.δ) * P.δ * b / ((1 + P.φ * P.θ) * a)

/-- O&R Exercise 3(d): the optimal feedback coefficient `Φ* = η − u*`. -/
noncomputable def optimalPhi (P : PooleParams) (a b : ℝ) : ℝ := P.η - optimalU P a b

/-- O&R Exercise 3(d): the minimal conditional output variance
`θ² σ_ε² σ_v²/((θ + δ)² σ_v² + (1 + φ θ)² σ_ε²)`. -/
noncomputable def minVar (P : PooleParams) (a b : ℝ) : ℝ :=
  P.θ ^ 2 * a * b / ((P.θ + P.δ) ^ 2 * b + (1 + P.φ * P.θ) ^ 2 * a)

/-- O&R Exercise 3(d): the stationary output has conditional variance `outputVar`. -/
theorem expect_outputMSV_sq (P : PooleParams) (Sh : PooleShocks S) (Φ : ℝ) :
    expect Sh (fun s => outputMSV P Sh Φ s ^ 2) =
      outputVar P (sigE2 Sh) (sigV2 Sh) (P.η - Φ) := by
  have hf : (fun s => outputMSV P Sh Φ s ^ 2) = fun s =>
      ((P.θ * (P.η - Φ) / den P (P.η - Φ)) * Sh.eps s +
        (-(P.θ * P.δ) / den P (P.η - Φ)) * Sh.v s) ^ 2 := by
    funext s
    unfold outputMSV
    ring
  rw [hf, expect_sq_comb]
  unfold outputVar
  ring

/-- O&R Exercise 3(d): in the determinacy region, in every bounded equilibrium,
`E_{t−1} y_t = 0` and `E_{t−1} y_t² = outputVar (η − Φ)` at every node. -/
theorem feedback_output_moments {P : PooleParams} {Sh : PooleShocks S} {mbar Φ : ℝ}
    (hdet : Φ < 1 ∨ 1 + 2 * P.η < Φ) (hden : den P (P.η - Φ) ≠ 0)
    {p e y m i : List S → ℝ} (hE : IsEqm P Sh (feedbackPolicy mbar Φ) p e y m i)
    (hb : Bounded p) (h : List S) :
    nodeEx Sh y h = 0 ∧
      nodeEx Sh (fun g => y g ^ 2) h = outputVar P (sigE2 Sh) (sigV2 Sh) (P.η - Φ) := by
  refine ⟨eqm_nodeEx_y hE h, ?_⟩
  rw [← expect_outputMSV_sq, nodeEx_eq_expect]
  unfold expect
  exact Finset.sum_congr rfl fun s _ => by
    dsimp only
    rw [(feedback_eqm_unique hdet hden hE hb s h).1]

/-! ### Part (a): the float -/

/-- O&R Exercise 3(a): a fixed money supply is the feedback rule with `Φ = 0`. -/
theorem floatPolicy_eq (mbar : ℝ) : floatPolicy mbar = feedbackPolicy mbar 0 := by
  funext m e
  simp [floatPolicy, feedbackPolicy]

/-- O&R Exercise 3: `den u > 0` for `u ≥ 0`. -/
theorem den_pos (P : PooleParams) {u : ℝ} (hu : 0 ≤ u) : 0 < den P u := by
  unfold den
  have := P.θ_pos
  have := P.δ_pos
  have := P.φ_pos
  positivity

/-- O&R Exercise 3(a): under the float every equilibrium with a bounded price level has
output `y = θ (η ε − δ v)/D₃` with `D₃ = δ (1 + η) + θ (η + φ δ)`, and the hint of the
book holds: `E_t e_{t+1} = E_t p_{t+1} = m̄` at every node. -/
theorem float_eqm_unique {P : PooleParams} {Sh : PooleShocks S} {mbar : ℝ}
    {p e y m i : List S → ℝ} (hE : IsEqm P Sh (floatPolicy mbar) p e y m i)
    (hb : Bounded p) (s : S) (h : List S) :
    y (s :: h) = P.θ * (P.η * Sh.eps s - P.δ * Sh.v s) /
        (P.δ * (1 + P.η) + P.θ * (P.η + P.φ * P.δ)) ∧
      nodeEx Sh e (s :: h) = mbar ∧ nodeEx Sh p (s :: h) = mbar := by
  rw [floatPolicy_eq] at hE
  have hdet : (0 : ℝ) < 1 ∨ 1 + 2 * P.η < 0 := Or.inl one_pos
  have hden : den P (P.η - 0) ≠ 0 := (den_pos P (by linarith [P.η_pos])).ne'
  have hp := feedback_expected_price_eq hdet hE hb (s :: h)
  refine ⟨?_, by rw [eqm_nodeEx_e hE]; exact hp, hp⟩
  rw [(feedback_eqm_unique hdet hden hE hb s h).1]
  unfold outputMSV den
  congr 1 <;> ring

/-- O&R Exercise 3(a): the float's conditional output variance,
`θ² (η² σ_ε² + δ² σ_v²)/D₃²`. -/
theorem floatVar_eq (P : PooleParams) (a b : ℝ) :
    floatVar P a b = P.θ ^ 2 * (P.η ^ 2 * a + P.δ ^ 2 * b) /
      (P.δ * (1 + P.η) + P.θ * (P.η + P.φ * P.δ)) ^ 2 := by
  unfold floatVar outputVar den
  congr 1
  ring

/-- O&R Exercise 3(a): under the float, in every equilibrium with a bounded price level,
`E_{t−1} y_t² = θ² (η² σ_ε² + δ² σ_v²)/D₃²` at every node. -/
theorem float_output_var {P : PooleParams} {Sh : PooleShocks S} {mbar : ℝ}
    {p e y m i : List S → ℝ} (hE : IsEqm P Sh (floatPolicy mbar) p e y m i)
    (hb : Bounded p) (h : List S) :
    nodeEx Sh (fun g => y g ^ 2) h = floatVar P (sigE2 Sh) (sigV2 Sh) := by
  rw [floatPolicy_eq] at hE
  have hden : den P (P.η - 0) ≠ 0 := (den_pos P (by linarith [P.η_pos])).ne'
  have := (feedback_output_moments (Or.inl one_pos) hden hE hb h).2
  rw [sub_zero] at this
  exact this

/-! ### Part (b): the peg -/

/-- O&R Exercise 3(b) and p. 631: under the peg every equilibrium (no boundedness needed)
has `y = θ ε/(θ + δ)`, `p = m̄ + ε/(θ + δ)`, `i = 0` and money
`m = m̄ + (1 + φ θ) ε/(θ + δ) + v`: money-demand shocks are fully accommodated and have no
real effect. -/
theorem peg_eqm_unique {P : PooleParams} {Sh : PooleShocks S} {mbar : ℝ}
    {p e y m i : List S → ℝ} (hE : IsEqm P Sh (pegPolicy mbar) p e y m i)
    (s : S) (h : List S) :
    y (s :: h) = P.θ * Sh.eps s / (P.θ + P.δ) ∧
      p (s :: h) = mbar + Sh.eps s / (P.θ + P.δ) ∧ e (s :: h) = mbar ∧ i (s :: h) = 0 ∧
      m (s :: h) = mbar + (1 + P.φ * P.θ) * Sh.eps s / (P.θ + P.δ) + Sh.v s := by
  have hpeg : ∀ s' h', e (s' :: h') = mbar := fun s' h' => (hE s' h').2.2.2.2
  have hEe : ∀ g, nodeEx Sh e g = mbar := by
    intro g
    rw [nodeEx_eq_expect]
    simp only [hpeg, expect_const]
  have hc : nodeEx Sh p h = mbar := by rw [← eqm_nodeEx_e hE h, hEe]
  obtain ⟨hi, hs, hg, hm, _⟩ := hE s h
  rw [hEe, hpeg] at hi
  rw [hc] at hs
  rw [hpeg] at hg
  have hθδ : P.θ + P.δ ≠ 0 := by linarith [P.θ_pos, P.δ_pos]
  have hy : y (s :: h) = P.θ * Sh.eps s / (P.θ + P.δ) := by
    rw [eq_div_iff hθδ]
    linear_combination P.δ * hs + P.θ * hg
  have hp : p (s :: h) = mbar + Sh.eps s / (P.θ + P.δ) := by
    field_simp
    linear_combination hg - hs
  have hi0 : i (s :: h) = 0 := by rw [hi, sub_self]
  refine ⟨hy, hp, hpeg s h, hi0, ?_⟩
  rw [hi0, hy, hp] at hm
  field_simp
  field_simp at hm
  linear_combination hm

/-- O&R Exercise 3(b): the announced money path is consistent: `E_{t−1} m_t = m̄`. -/
theorem peg_expected_money {P : PooleParams} {Sh : PooleShocks S} {mbar : ℝ}
    {p e y m i : List S → ℝ} (hE : IsEqm P Sh (pegPolicy mbar) p e y m i) (h : List S) :
    nodeEx Sh m h = mbar := by
  have hf : (fun s => m (s :: h)) = fun s =>
      mbar + ((1 + P.φ * P.θ) / (P.θ + P.δ)) * Sh.eps s + Sh.v s := by
    funext s
    rw [(peg_eqm_unique hE s h).2.2.2.2]
    ring
  rw [nodeEx_eq_expect, hf, expect_add, expect_add, expect_const, expect_const_mul, expect_eps,
    expect_v]
  ring

/-- O&R Exercise 3(b), existence: the peg allocation is an equilibrium. -/
theorem peg_eqm_exists (P : PooleParams) (Sh : PooleShocks S) (mbar : ℝ) :
    IsEqm P Sh (pegPolicy mbar) (onHead mbar fun s => mbar + Sh.eps s / (P.θ + P.δ))
      (onHead mbar fun _ => mbar) (onHead 0 fun s => P.θ * Sh.eps s / (P.θ + P.δ))
      (onHead mbar fun s => mbar + (1 + P.φ * P.θ) * Sh.eps s / (P.θ + P.δ) + Sh.v s)
      (onHead 0 fun _ => 0) := by
  intro s h
  have hθδ : P.θ + P.δ ≠ 0 := by linarith [P.θ_pos, P.δ_pos]
  simp only [onHead, nodeEx_onHead, expect_const]
  have hEp : expect Sh (fun s => mbar + Sh.eps s / (P.θ + P.δ)) = mbar := by
    rw [expect_add, expect_const, expect_div_const, expect_eps, zero_div, add_zero]
  rw [hEp]
  refine ⟨by ring, ?_, ?_, ?_, rfl⟩
  · field_simp
    ring
  · field_simp
    ring
  · field_simp
    ring

/-- O&R Exercise 3(b): under the peg `E_{t−1} y_t² = θ² σ_ε²/(θ + δ)²`, independent of
the money-demand variance. -/
theorem peg_output_var {P : PooleParams} {Sh : PooleShocks S} {mbar : ℝ}
    {p e y m i : List S → ℝ} (hE : IsEqm P Sh (pegPolicy mbar) p e y m i) (h : List S) :
    nodeEx Sh (fun g => y g ^ 2) h = pegVar P (sigE2 Sh) := by
  have hf : (fun s => y (s :: h) ^ 2) = fun s =>
      (P.θ / (P.θ + P.δ) * Sh.eps s + 0 * Sh.v s) ^ 2 := by
    funext s
    rw [(peg_eqm_unique hE s h).1]
    ring
  rw [nodeEx_eq_expect, hf, expect_sq_comb]
  unfold pegVar
  rw [div_pow]
  ring

/-! ### Part (c): Poole's comparison -/

/-- O&R Exercise 3(c): `D₃ = den η > η (θ + δ)`. -/
theorem den_eta_gt (P : PooleParams) : P.η * (P.θ + P.δ) < den P P.η := by
  unfold den
  have := P.δ_pos
  have := P.φ_pos
  have := P.θ_pos
  have : 0 < P.δ * (1 + P.φ * P.θ) := by positivity
  linarith

/-- O&R Exercise 3(c): the exact Poole criterion. The peg is at least as good as the float
iff `σ_ε² (D₃² − η² (θ + δ)²) ≤ (θ + δ)² δ² σ_v²`. -/
theorem peg_le_float_iff (P : PooleParams) (a b : ℝ) :
    pegVar P a ≤ floatVar P a b ↔
      a * (den P P.η ^ 2 - P.η ^ 2 * (P.θ + P.δ) ^ 2) ≤ (P.θ + P.δ) ^ 2 * P.δ ^ 2 * b := by
  have hθ := P.θ_pos
  have hA : 0 < P.θ + P.δ := by linarith [P.δ_pos]
  have hD : 0 < den P P.η := den_pos P P.η_pos.le
  unfold pegVar floatVar outputVar
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hθ2 : 0 < P.θ ^ 2 := by positivity
  constructor
  · intro h
    nlinarith
  · intro h
    nlinarith

/-- O&R Exercise 3(c): the peg is strictly better than the float as soon as
`σ_ε²/σ_v²` is below an explicit positive threshold; in particular as `σ_ε²/σ_v² → 0`. -/
theorem peg_lt_float_of_small_ratio (P : PooleParams) :
    ∃ rbar > 0, ∀ a b : ℝ, 0 ≤ a → a < rbar * b → pegVar P a < floatVar P a b := by
  have hθ := P.θ_pos
  have hA : 0 < P.θ + P.δ := by linarith [P.δ_pos]
  have hδ := P.δ_pos
  have hD : 0 < den P P.η := den_pos P P.η_pos.le
  have hgap : 0 < den P P.η ^ 2 - P.η ^ 2 * (P.θ + P.δ) ^ 2 := by
    have h1 := den_eta_gt P
    have h2 : 0 < P.η * (P.θ + P.δ) := mul_pos P.η_pos hA
    nlinarith
  refine ⟨(P.θ + P.δ) ^ 2 * P.δ ^ 2 / (den P P.η ^ 2 - P.η ^ 2 * (P.θ + P.δ) ^ 2),
    by positivity, fun a b ha hab => ?_⟩
  have hkey : a * (den P P.η ^ 2 - P.η ^ 2 * (P.θ + P.δ) ^ 2) <
      (P.θ + P.δ) ^ 2 * P.δ ^ 2 * b := by
    rw [div_mul_eq_mul_div, lt_div_iff₀ hgap] at hab
    linarith
  unfold pegVar floatVar outputVar
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  have hθ2 : 0 < P.θ ^ 2 := by positivity
  nlinarith

/-- O&R Exercise 3(c): with only money-demand shocks (`σ_ε² = 0 < σ_v²`) the peg is
strictly better. -/
theorem peg_lt_float_of_eps_zero (P : PooleParams) {b : ℝ} (hb : 0 < b) :
    pegVar P 0 < floatVar P 0 b := by
  have hD : 0 < den P P.η := den_pos P P.η_pos.le
  have := P.θ_pos
  have := P.δ_pos
  unfold pegVar floatVar outputVar
  simp only [mul_zero, zero_div, zero_add]
  positivity

/-- O&R Exercise 3(c): with only goods-demand shocks (`σ_v² = 0 < σ_ε²`) the float is
strictly better. -/
theorem float_lt_peg_of_v_zero (P : PooleParams) {a : ℝ} (ha : 0 < a) :
    floatVar P a 0 < pegVar P a := by
  have hA : 0 < P.θ + P.δ := by linarith [P.θ_pos, P.δ_pos]
  have hD : 0 < den P P.η := den_pos P P.η_pos.le
  have h1 := den_eta_gt P
  have hθ := P.θ_pos
  unfold pegVar floatVar outputVar
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  have h2 : 0 < P.η * (P.θ + P.δ) := mul_pos P.η_pos hA
  have h3 : (P.η * (P.θ + P.δ)) ^ 2 < den P P.η ^ 2 := by nlinarith
  have hθ2 : 0 < P.θ ^ 2 := by positivity
  have h4 := mul_lt_mul_of_pos_left h3 (mul_pos hθ2 ha)
  nlinarith [h4]

/-! ### Part (d): the optimal feedback rule -/

/-- O&R Exercise 3(d), the Cauchy–Schwarz identity behind the optimum:
`(u² a + δ² b)((θ+δ)² b + (1+φθ)² a) − a b den(u)² = (u a (1+φθ) − δ b (θ+δ))²`. -/
theorem optimum_identity (P : PooleParams) (a b u : ℝ) :
    (u ^ 2 * a + P.δ ^ 2 * b) * ((P.θ + P.δ) ^ 2 * b + (1 + P.φ * P.θ) ^ 2 * a) -
        a * b * den P u ^ 2 =
      (u * a * (1 + P.φ * P.θ) - P.δ * b * (P.θ + P.δ)) ^ 2 := by
  unfold den
  ring

/-- O&R Exercise 3(d): for `σ_ε² > 0`, `σ_v² ≥ 0`, every admissible rule (away from the pole)
has conditional output variance at least `minVar`. -/
theorem minVar_le_outputVar (P : PooleParams) {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (u : ℝ)
    (hden : den P u ≠ 0) : minVar P a b ≤ outputVar P a b u := by
  have hθ := P.θ_pos
  have hC : 0 < 1 + P.φ * P.θ := by have := P.φ_pos; positivity
  have hQ : 0 < (P.θ + P.δ) ^ 2 * b + (1 + P.φ * P.θ) ^ 2 * a := by positivity
  have hD2 : 0 < den P u ^ 2 := by positivity
  unfold minVar outputVar
  rw [div_le_div_iff₀ hQ hD2]
  have hid := optimum_identity P a b u
  have hθ2 : 0 ≤ P.θ ^ 2 := by positivity
  nlinarith [mul_nonneg hθ2 (sq_nonneg (u * a * (1 + P.φ * P.θ) - P.δ * b * (P.θ + P.δ)))]

/-- O&R Exercise 3(d): the variance equals `minVar` exactly at `u = u*`. -/
theorem outputVar_eq_minVar_iff (P : PooleParams) {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b)
    (u : ℝ) (hden : den P u ≠ 0) : outputVar P a b u = minVar P a b ↔ u = optimalU P a b := by
  have hθ := P.θ_pos
  have hC : 0 < 1 + P.φ * P.θ := by have := P.φ_pos; positivity
  have hQ : 0 < (P.θ + P.δ) ^ 2 * b + (1 + P.φ * P.θ) ^ 2 * a := by positivity
  have hD2 : 0 < den P u ^ 2 := by positivity
  have hid := optimum_identity P a b u
  unfold minVar outputVar optimalU
  rw [div_eq_div_iff hD2.ne' hQ.ne', eq_div_iff (by positivity)]
  have hθ2 : 0 < P.θ ^ 2 := by positivity
  constructor
  · intro h
    have h1 : P.θ ^ 2 * (u * a * (1 + P.φ * P.θ) - P.δ * b * (P.θ + P.δ)) ^ 2 = 0 := by
      linear_combination h - P.θ ^ 2 * hid
    have h2 := (mul_eq_zero.mp h1).resolve_left hθ2.ne'
    have h3 := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2
    linear_combination h3
  · intro h
    have h3 : u * a * (1 + P.φ * P.θ) - P.δ * b * (P.θ + P.δ) = 0 := by
      linear_combination h
    have h4 := hid
    rw [h3] at h4
    linear_combination P.θ ^ 2 * h4

/-- O&R Exercise 3(d): `u* ≥ 0`, so the optimal rule is admissible (`den u* > 0`). -/
theorem optimalU_nonneg (P : PooleParams) {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) :
    0 ≤ optimalU P a b := by
  unfold optimalU
  have := P.θ_pos
  have := P.δ_pos
  have := P.φ_pos
  positivity

/-- O&R Exercise 3(d): the optimal rule attains `minVar`. -/
theorem outputVar_optimalU (P : PooleParams) {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) :
    outputVar P a b (optimalU P a b) = minVar P a b :=
  (outputVar_eq_minVar_iff P ha hb _ (den_pos P (optimalU_nonneg P ha hb)).ne').mpr rfl

/-- O&R Exercise 3(d), existence and uniqueness of the optimal feedback rule: for
`σ_ε² > 0`, `σ_v² ≥ 0` there is exactly one admissible `Φ` minimising the conditional output
variance over all admissible `Φ'`, namely `Φ* = η − u*`. -/
theorem exists_unique_optimal_rule (P : PooleParams) {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) :
    ∃! Φ, den P (P.η - Φ) ≠ 0 ∧
      ∀ Φ', den P (P.η - Φ') ≠ 0 → outputVar P a b (P.η - Φ) ≤ outputVar P a b (P.η - Φ') := by
  have hadm : den P (P.η - optimalPhi P a b) ≠ 0 := by
    unfold optimalPhi
    rw [sub_sub_cancel]
    exact (den_pos P (optimalU_nonneg P ha hb)).ne'
  refine ⟨optimalPhi P a b, ⟨hadm, fun Φ' hΦ' => ?_⟩, ?_⟩
  · unfold optimalPhi
    rw [sub_sub_cancel, outputVar_optimalU P ha hb]
    exact minVar_le_outputVar P ha hb _ hΦ'
  · rintro Φ ⟨hΦ, hmin⟩
    have h1 := hmin (optimalPhi P a b) hadm
    have h2 : outputVar P a b (P.η - optimalPhi P a b) = minVar P a b := by
      unfold optimalPhi
      rw [sub_sub_cancel, outputVar_optimalU P ha hb]
    have h3 := minVar_le_outputVar P ha hb _ hΦ
    have h4 : outputVar P a b (P.η - Φ) = minVar P a b := by linarith
    have h5 := (outputVar_eq_minVar_iff P ha hb _ hΦ).mp h4
    unfold optimalPhi
    linarith

/-- O&R Exercise 3(d), closed form of the optimal rule:
`Φ* = η − (θ + δ) δ σ_v²/((1 + φ θ) σ_ε²)`. -/
theorem optimalPhi_eq (P : PooleParams) (a b : ℝ) :
    optimalPhi P a b = P.η - (P.θ + P.δ) * P.δ * b / ((1 + P.φ * P.θ) * a) := rfl

/-- O&R Exercise 3(d), sign correction: with `σ_ε², σ_v² > 0`, `Φ* < η`; the optimal
coefficient is never "between 0 and ∞" in the book's sense unless `u* < η`. -/
theorem optimalPhi_lt_eta (P : PooleParams) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    optimalPhi P a b < P.η := by
  unfold optimalPhi optimalU
  have := P.θ_pos
  have := P.δ_pos
  have := P.φ_pos
  have : 0 < (P.θ + P.δ) * P.δ * b / ((1 + P.φ * P.θ) * a) := by positivity
  linarith

/-- O&R Exercise 3(d): `Φ* < 0` (leaning *against* the float's direction: money rises when
the currency appreciates) exactly when `u* > η`. -/
theorem optimalPhi_neg_iff (P : PooleParams) (a b : ℝ) :
    optimalPhi P a b < 0 ↔ P.η < optimalU P a b := by
  unfold optimalPhi
  constructor <;> intro h <;> linarith

/-- O&R Exercise 3(d): the optimum is strictly better than the peg when both shocks are
present. -/
theorem minVar_lt_pegVar (P : PooleParams) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    minVar P a b < pegVar P a := by
  have hθ := P.θ_pos
  have hA : 0 < P.θ + P.δ := by linarith [P.δ_pos]
  have hC : 0 < 1 + P.φ * P.θ := by have := P.φ_pos; positivity
  unfold minVar pegVar
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  have h1 : 0 < P.θ ^ 2 * a * ((1 + P.φ * P.θ) ^ 2 * a) := by positivity
  nlinarith

/-- O&R Exercise 3(d): the optimum is at least as good as the float, with equality iff
`u* = η`, i.e. iff `η (1 + φ θ) σ_ε² = (θ + δ) δ σ_v²` (then the float is optimal). -/
theorem minVar_le_floatVar (P : PooleParams) {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) :
    minVar P a b ≤ floatVar P a b ∧
      (floatVar P a b = minVar P a b ↔ P.η = optimalU P a b) :=
  ⟨minVar_le_outputVar P ha hb _ (den_pos P P.η_pos.le).ne',
    outputVar_eq_minVar_iff P ha hb _ (den_pos P P.η_pos.le).ne'⟩

/-- O&R Exercise 3(d): the pole of the output formula, `den (η − Φ) = 0` iff
`Φ = η + δ (1 + φ θ)/(θ + δ)`; there the equilibrium fails to exist (see
`feedback_no_eqm_at_pole`). -/
theorem den_eq_zero_iff (P : PooleParams) (Φ : ℝ) :
    den P (P.η - Φ) = 0 ↔ Φ = P.η + P.δ * (1 + P.φ * P.θ) / (P.θ + P.δ) := by
  have hA : P.θ + P.δ ≠ 0 := by linarith [P.θ_pos, P.δ_pos]
  unfold den
  constructor
  · intro h
    field_simp
    linear_combination -h
  · intro h
    rw [h]
    field_simp
    ring

/-- O&R Exercise 3(d): at the pole, in the determinacy region, no bounded equilibrium exists
as soon as some state has `(η − Φ) ε ≠ δ v`. -/
theorem feedback_no_eqm_at_pole {P : PooleParams} {Sh : PooleShocks S} {mbar Φ : ℝ}
    (hdet : Φ < 1 ∨ 1 + 2 * P.η < Φ) (hpole : den P (P.η - Φ) = 0) (s : S)
    (hs : (P.η - Φ) * Sh.eps s ≠ P.δ * Sh.v s) {p e y m i : List S → ℝ}
    (hE : IsEqm P Sh (feedbackPolicy mbar Φ) p e y m i) (hb : Bounded p) : False := by
  obtain ⟨hi, hsu, hg, hm, hpol⟩ := hE s []
  have hc : nodeEx Sh p [] = mbar := feedback_expected_price_eq hdet hE hb []
  have hX : nodeEx Sh e [s] = mbar := by
    rw [eqm_nodeEx_e hE [s]]
    exact feedback_expected_price_eq hdet hE hb [s]
  have hred := feedback_node_reduced_form P mbar Φ (Sh.eps s) (Sh.v s) _ _ _ _ _ _ _
    hi hsu hg hm hpol
  rw [hX, hc, hpole, mul_zero] at hred
  have h1 : (P.η - Φ) * Sh.eps s - P.δ * Sh.v s = 0 := by
    have := (mul_eq_zero.mp (by linear_combination -hred : P.θ *
      ((P.η - Φ) * Sh.eps s - P.δ * Sh.v s) = 0)).resolve_left P.θ_pos.ne'
    exact this
  exact hs (by linear_combination h1)

/-- The limit lemma used for "the peg is a limit": `(α u + β)/(A u + B) → α/A` along any
filter on which `u⁻¹ → 0` and `u ≠ 0` eventually (O&R Exercise 3(d)). -/
theorem tendsto_linear_ratio {l : Filter ℝ} (hl : Tendsto (fun u : ℝ => u⁻¹) l (𝓝 0))
    (hne : ∀ᶠ u in l, u ≠ 0) (α β A B : ℝ) (hA : A ≠ 0) :
    Tendsto (fun u => (α * u + β) / (A * u + B)) l (𝓝 (α / A)) := by
  have hc : ContinuousAt (fun t : ℝ => (α + β * t) / (A + B * t)) 0 := by
    apply ContinuousAt.div (by fun_prop) (by fun_prop)
    simpa using hA
  have h1 := hc.tendsto.comp hl
  have h0 : (α + β * 0) / (A + B * 0) = α / A := by simp
  rw [h0] at h1
  refine h1.congr' (hne.mono fun u hu => ?_)
  simp only [Function.comp_apply]
  rw [show α + β * u⁻¹ = (α * u + β) / u by field_simp,
    show A + B * u⁻¹ = (A * u + B) / u by field_simp, div_div_div_cancel_right₀ hu]

/-- The limit lemma for variances: `(a u² + b)/(A u + B)² → a/A²` along any filter on which
`u⁻¹ → 0` and `u ≠ 0` eventually (O&R Exercise 3(d)). -/
theorem tendsto_quadratic_ratio {l : Filter ℝ} (hl : Tendsto (fun u : ℝ => u⁻¹) l (𝓝 0))
    (hne : ∀ᶠ u in l, u ≠ 0) (a b A B : ℝ) (hA : A ≠ 0) :
    Tendsto (fun u => (a * u ^ 2 + b) / (A * u + B) ^ 2) l (𝓝 (a / A ^ 2)) := by
  have hc : ContinuousAt (fun t : ℝ => (a + b * t ^ 2) / (A + B * t) ^ 2) 0 := by
    apply ContinuousAt.div (by fun_prop) (by fun_prop)
    simpa using hA
  have h1 := hc.tendsto.comp hl
  have h0 : (a + b * 0 ^ 2) / (A + B * 0) ^ 2 = a / A ^ 2 := by simp
  rw [h0] at h1
  refine h1.congr' (hne.mono fun u hu => ?_)
  simp only [Function.comp_apply]
  rw [show a + b * u⁻¹ ^ 2 = (a * u ^ 2 + b) / u ^ 2 by field_simp,
    show (A + B * u⁻¹) ^ 2 = (A * u + B) ^ 2 / u ^ 2 by field_simp,
    div_div_div_cancel_right₀ (pow_ne_zero 2 hu)]

/-- O&R Exercise 3(d): `η − Φ → +∞` as `Φ → −∞`. -/
theorem tendsto_eta_sub_atBot (η : ℝ) : Tendsto (fun Φ : ℝ => η - Φ) atBot atTop :=
  tendsto_atBot_atTop.2 fun b => ⟨η - b, fun Φ hΦ => by linarith⟩

/-- O&R Exercise 3(d): `η − Φ → −∞` as `Φ → +∞`. -/
theorem tendsto_eta_sub_atTop (η : ℝ) : Tendsto (fun Φ : ℝ => η - Φ) atTop atBot :=
  tendsto_atTop_atBot.2 fun b => ⟨η - b, fun Φ hΦ => by linarith⟩

/-- O&R Exercise 3(d), "the peg is only a limit": as `Φ → −∞` the conditional output
variance tends to the peg's `θ² σ_ε²/(θ + δ)²`. -/
theorem outputVar_tendsto_peg_atBot (P : PooleParams) (a b : ℝ) :
    Tendsto (fun Φ => outputVar P a b (P.η - Φ)) atBot (𝓝 (pegVar P a)) := by
  have hA : P.θ + P.δ ≠ 0 := by linarith [P.θ_pos, P.δ_pos]
  have h := tendsto_quadratic_ratio tendsto_inv_atTop_zero
    (eventually_ne_atTop 0) (P.θ ^ 2 * a) (P.θ ^ 2 * (P.δ ^ 2 * b)) (P.θ + P.δ)
    (P.δ * (1 + P.φ * P.θ)) hA
  have h2 := h.comp (tendsto_eta_sub_atBot P.η)
  unfold pegVar
  refine h2.congr fun Φ => ?_
  simp only [Function.comp_apply]
  unfold outputVar den
  ring

/-- O&R Exercise 3(d): as `Φ → +∞` (i.e. through the pole) the variance also tends to the
peg value. -/
theorem outputVar_tendsto_peg_atTop (P : PooleParams) (a b : ℝ) :
    Tendsto (fun Φ => outputVar P a b (P.η - Φ)) atTop (𝓝 (pegVar P a)) := by
  have hA : P.θ + P.δ ≠ 0 := by linarith [P.θ_pos, P.δ_pos]
  have h := tendsto_quadratic_ratio tendsto_inv_atBot_zero
    (eventually_ne_atBot 0) (P.θ ^ 2 * a) (P.θ ^ 2 * (P.δ ^ 2 * b)) (P.θ + P.δ)
    (P.δ * (1 + P.φ * P.θ)) hA
  have h2 := h.comp (tendsto_eta_sub_atTop P.η)
  unfold pegVar
  refine h2.congr fun Φ => ?_
  simp only [Function.comp_apply]
  unfold outputVar den
  ring

/-- O&R Exercise 3(d): the equilibrium output itself converges, state by state, to the peg's
output `θ ε/(θ + δ)` as `Φ → −∞`. -/
theorem outputMSV_tendsto_peg (P : PooleParams) (Sh : PooleShocks S) (s : S) :
    Tendsto (fun Φ => outputMSV P Sh Φ s) atBot (𝓝 (P.θ * Sh.eps s / (P.θ + P.δ))) := by
  have hA : P.θ + P.δ ≠ 0 := by linarith [P.θ_pos, P.δ_pos]
  have h := tendsto_linear_ratio tendsto_inv_atTop_zero (eventually_ne_atTop 0)
    (P.θ * Sh.eps s) (-(P.θ * P.δ * Sh.v s)) (P.θ + P.δ) (P.δ * (1 + P.φ * P.θ)) hA
  have h2 := h.comp (tendsto_eta_sub_atBot P.η)
  refine h2.congr fun Φ => ?_
  simp only [Function.comp_apply]
  unfold outputMSV den
  ring

/-- O&R Exercise 3(d): with `σ_ε² = 0 < σ_v²` no admissible rule is optimal: the infimum
(zero, the peg's value) is approached but never attained by a finite `Φ`. -/
theorem no_optimal_rule_of_eps_zero (P : PooleParams) {b : ℝ} (hb : 0 < b) :
    ¬∃ u, den P u ≠ 0 ∧ ∀ u', den P u' ≠ 0 → outputVar P 0 b u ≤ outputVar P 0 b u' := by
  rintro ⟨u, hu, hmin⟩
  have hA : 0 < P.θ + P.δ := by linarith [P.θ_pos, P.δ_pos]
  have hθ := P.θ_pos
  have hδ := P.δ_pos
  set D := den P u with hD
  have hC : 0 < P.δ * (1 + P.φ * P.θ) := by have := P.φ_pos; positivity
  set u' := (2 * |D| + 1 - P.δ * (1 + P.φ * P.θ)) / (P.θ + P.δ) with hu'
  have hdu' : den P u' = 2 * |D| + 1 := by
    unfold den
    rw [hu']
    field_simp
    ring
  have hpos : 0 < 2 * |D| + 1 := by positivity
  have h1 := hmin u' (by rw [hdu']; exact hpos.ne')
  unfold outputVar at h1
  rw [hdu', ← hD] at h1
  simp only [mul_zero, zero_add] at h1
  have hD2 : 0 < D ^ 2 := by positivity
  rw [div_le_div_iff₀ hD2 (by positivity)] at h1
  have hk : 0 < P.θ ^ 2 * (P.δ ^ 2 * b) := by positivity
  have h2 : D ^ 2 < (2 * |D| + 1) ^ 2 := by
    have := sq_abs D
    nlinarith [abs_nonneg D]
  nlinarith

/-- O&R Exercise 3(d), a feedback rule never reproduces the peg: in the determinacy region
and away from the pole, if a bounded equilibrium has `e ≡ m̄` then
`(θ + δ) v + (1 + φ θ) ε = 0` in every state, a degenerate shock structure. -/
theorem feedback_peg_only_limit {P : PooleParams} {Sh : PooleShocks S} {mbar Φ : ℝ}
    (hdet : Φ < 1 ∨ 1 + 2 * P.η < Φ) (hden : den P (P.η - Φ) ≠ 0)
    {p e y m i : List S → ℝ} (hE : IsEqm P Sh (feedbackPolicy mbar Φ) p e y m i)
    (hb : Bounded p) (hpeg : ∀ s h, e (s :: h) = mbar) (s : S) :
    (P.θ + P.δ) * Sh.v s + (1 + P.φ * P.θ) * Sh.eps s = 0 := by
  have hu := feedback_eqm_unique hdet hden hE hb s []
  have he : eMSV P Sh mbar Φ s = mbar := by rw [← hu.2.2.1, hpeg]
  have hY : outputMSV P Sh Φ s * den P (P.η - Φ) =
      P.θ * ((P.η - Φ) * Sh.eps s - P.δ * Sh.v s) := by
    unfold outputMSV
    exact div_mul_cancel₀ _ hden
  have hθ := P.θ_pos.ne'
  have hδ := P.δ_pos.ne'
  unfold eMSV pMSV at he
  field_simp at he
  unfold den at hY
  have h3 : P.θ * P.δ * ((P.θ + P.δ) * Sh.v s + (1 + P.φ * P.θ) * Sh.eps s) = 0 := by
    linear_combination (P.θ + P.δ) * hY +
      (-(P.η - Φ) * (P.θ + P.δ) - P.δ * (1 + P.φ * P.θ)) * he
  rcases mul_eq_zero.mp h3 with h4 | h4
  · exact absurd h4 (mul_ne_zero hθ hδ)
  · exact h4

/-- O&R Exercise 3: `σ_v² ≥ 0`. -/
theorem sigV2_nonneg (Sh : PooleShocks S) : 0 ≤ sigV2 Sh := by
  unfold sigV2 expect
  exact Finset.sum_nonneg fun s _ => mul_nonneg (Sh.prob_nonneg s) (sq_nonneg _)

/-- O&R Exercise 3(d), optimality at the level of equilibria: if `σ_ε² > 0`, then in the
determinacy region every bounded equilibrium under any admissible rule has conditional output
variance at least `minVar` at every node, with equality iff `Φ = Φ*`. -/
theorem feedback_eqm_var_ge_min {P : PooleParams} {Sh : PooleShocks S} (ha : 0 < sigE2 Sh)
    {mbar Φ : ℝ} (hdet : Φ < 1 ∨ 1 + 2 * P.η < Φ) (hden : den P (P.η - Φ) ≠ 0)
    {p e y m i : List S → ℝ} (hE : IsEqm P Sh (feedbackPolicy mbar Φ) p e y m i)
    (hb : Bounded p) (h : List S) :
    minVar P (sigE2 Sh) (sigV2 Sh) ≤ nodeEx Sh (fun g => y g ^ 2) h ∧
      (nodeEx Sh (fun g => y g ^ 2) h = minVar P (sigE2 Sh) (sigV2 Sh) ↔
        Φ = optimalPhi P (sigE2 Sh) (sigV2 Sh)) := by
  rw [(feedback_output_moments hdet hden hE hb h).2]
  refine ⟨minVar_le_outputVar P ha (sigV2_nonneg Sh) _ hden, ?_⟩
  rw [outputVar_eq_minVar_iff P ha (sigV2_nonneg Sh) _ hden]
  unfold optimalPhi
  constructor <;> intro h' <;> linarith

/-- O&R Exercise 3(d): the stationary equilibrium under `Φ*` exists and attains `minVar` at
every node (whether or not `Φ*` is in the determinacy region). -/
theorem optimal_rule_eqm_attains (P : PooleParams) (Sh : PooleShocks S) (ha : 0 < sigE2 Sh)
    (mbar : ℝ) (h : List S) :
    IsEqm P Sh (feedbackPolicy mbar (optimalPhi P (sigE2 Sh) (sigV2 Sh)))
      (onHead mbar (pMSV P Sh mbar (optimalPhi P (sigE2 Sh) (sigV2 Sh))))
      (onHead mbar (eMSV P Sh mbar (optimalPhi P (sigE2 Sh) (sigV2 Sh))))
      (onHead 0 (outputMSV P Sh (optimalPhi P (sigE2 Sh) (sigV2 Sh))))
      (onHead mbar (mMSV P Sh mbar (optimalPhi P (sigE2 Sh) (sigV2 Sh))))
      (onHead 0 (iMSV P Sh mbar (optimalPhi P (sigE2 Sh) (sigV2 Sh)))) ∧
    nodeEx Sh (fun g => onHead 0 (outputMSV P Sh (optimalPhi P (sigE2 Sh) (sigV2 Sh))) g ^ 2) h
      = minVar P (sigE2 Sh) (sigV2 Sh) := by
  have hadm : den P (P.η - optimalPhi P (sigE2 Sh) (sigV2 Sh)) ≠ 0 := by
    unfold optimalPhi
    rw [sub_sub_cancel]
    exact (den_pos P (optimalU_nonneg P ha (sigV2_nonneg Sh))).ne'
  refine ⟨feedback_eqm_exists P Sh mbar _ hadm, ?_⟩
  change expect Sh (fun s => outputMSV P Sh (optimalPhi P (sigE2 Sh) (sigV2 Sh)) s ^ 2) = _
  rw [expect_outputMSV_sq]
  unfold optimalPhi
  rw [sub_sub_cancel]
  exact outputVar_optimalU P ha (sigV2_nonneg Sh)

/-! ### The sign of the optimal coefficient (O&R p. 632 and Ex. 3(d) flags) -/

/-- O&R p. 632: as the ratio `σ_ε²/σ_v²` of real to monetary shock variances tends to zero,
the optimal coefficient `Φ* = η − (θ+δ) δ/((1+φθ) r)` tends to `−∞` (not `+∞`). -/
theorem optimalPhi_tendsto_atBot (P : PooleParams) :
    Tendsto (fun r : ℝ => P.η - (P.θ + P.δ) * P.δ / ((1 + P.φ * P.θ) * r)) (𝓝[>] 0)
      atBot := by
  have hK : 0 < (P.θ + P.δ) * P.δ / (1 + P.φ * P.θ) := by
    have := P.θ_pos
    have := P.δ_pos
    have := P.φ_pos
    positivity
  have h := tendsto_inv_nhdsGT_zero.const_mul_atTop hK
  refine tendsto_atBot.2 fun c => (h.eventually_ge_atTop (P.η - c)).mono fun r hr => ?_
  have he : (P.θ + P.δ) * P.δ / ((1 + P.φ * P.θ) * r) =
      (P.θ + P.δ) * P.δ / (1 + P.φ * P.θ) * r⁻¹ := by
    simp only [div_eq_mul_inv, mul_inv]
    ring
  rw [he]
  linarith

/-- O&R p. 632: the optimal coefficient as a function of the variance ratio `r = σ_ε²/σ_v²`
(an identity for all `a, b`, including the junk value `b = 0`). -/
theorem optimalPhi_eq_ratio (P : PooleParams) (a b : ℝ) :
    optimalPhi P a b = P.η - (P.θ + P.δ) * P.δ / ((1 + P.φ * P.θ) * (a / b)) := by
  unfold optimalPhi optimalU
  congr 1
  rw [mul_div_assoc', div_div_eq_mul_div]

/-- O&R p. 632, the book's claim is false: `Φ*` does NOT tend to `+∞` as `σ_ε²/σ_v² → 0`. -/
theorem optimalPhi_not_tendsto_atTop (P : PooleParams) :
    ¬Tendsto (fun r : ℝ => P.η - (P.θ + P.δ) * P.δ / ((1 + P.φ * P.θ) * r)) (𝓝[>] 0)
      atTop :=
  fun h => (optimalPhi_tendsto_atBot P).not_tendsto disjoint_atBot_atTop h

/-- The survey's counterexample parameters `θ = 1.1, δ = 0.6, η = 2, φ = 0.5` (O&R Ex. 3). -/
noncomputable def signExample : PooleParams :=
  ⟨1.1, 0.6, 2, 0.5, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- O&R Ex. 3(d) flag: with `σ_ε = 0.7`, `σ_v = 4` (so `σ_ε² = 0.49`, `σ_v² = 16`) the optimal
coefficient is about `−19.49`: negative, so not "between 0 (float) and ∞ (peg)". -/
theorem signExample_optimalPhi :
    -19.5 < optimalPhi signExample 0.49 16 ∧ optimalPhi signExample 0.49 16 < -19 := by
  unfold optimalPhi optimalU signExample
  norm_num

/-- Parameters `θ = δ = φ = 1`, `η = 3` for the indeterminacy example (O&R Ex. 3). -/
noncomputable def indetExample : PooleParams :=
  ⟨1, 1, 3, 1, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- O&R Ex. 3(d), a new finding: with `σ_ε² = σ_v² = 1` the optimal coefficient is `Φ* = 2`,
inside the indeterminacy region `1 < Φ < 1 + 2η = 7`, where bounded sunspot equilibria with
different output exist (`sunspot_eqm`). -/
theorem indetExample_optimalPhi :
    optimalPhi indetExample 1 1 = 2 ∧ 1 < optimalPhi indetExample 1 1 ∧
      optimalPhi indetExample 1 1 < 1 + 2 * indetExample.η := by
  unfold optimalPhi optimalU indetExample
  norm_num

/-- O&R Ex. 3(d): the optimal rule is in the indeterminacy region exactly when `u* < η − 1`
(for `σ_ε² > 0`, `σ_v² ≥ 0`). -/
theorem optimalPhi_indeterminate_iff (P : PooleParams) {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) :
    (1 < optimalPhi P a b ∧ optimalPhi P a b < 1 + 2 * P.η) ↔ optimalU P a b < P.η - 1 := by
  have h0 := optimalU_nonneg P ha hb
  have hη := P.η_pos
  unfold optimalPhi
  constructor
  · rintro ⟨h1, _⟩
    linarith
  · intro h
    constructor <;> linarith

/-! ### Sunspot equilibria in the indeterminacy region -/

/-- O&R Ex. 3(d): the root `λ = (η + 1 − Φ)/η` of the expected-level recursion. -/
noncomputable def sunLam (P : PooleParams) (Φ : ℝ) : ℝ := (P.η + 1 - Φ) / P.η

/-- O&R Ex. 3(d): the sunspot component of the expected price level,
`x_{s :: h} = λ x_h + w_s`, `x_{[]} = 0`. -/
def sunspotLevel (lam : ℝ) (w : S → ℝ) : List S → ℝ
  | [] => 0
  | s :: h => lam * sunspotLevel lam w h + w s

/-- O&R Ex. 3(d): output in a sunspot equilibrium, in which the money-demand shock is
effectively `v − η w`. -/
noncomputable def ySun (P : PooleParams) (Sh : PooleShocks S) (Φ : ℝ) (w : S → ℝ)
    (s : S) : ℝ :=
  P.θ * ((P.η - Φ) * Sh.eps s - P.δ * (Sh.v s - P.η * w s)) / den P (P.η - Φ)

/-- O&R Ex. 3(d): the price level in a sunspot equilibrium. -/
noncomputable def pSun (P : PooleParams) (Sh : PooleShocks S) (mbar Φ : ℝ) (w : S → ℝ) :
    List S → ℝ
  | [] => mbar
  | s :: h => mbar + sunspotLevel (sunLam P Φ) w h + ySun P Sh Φ w s / P.θ

/-- O&R Ex. 3(d): the exchange rate in a sunspot equilibrium. -/
noncomputable def eSun (P : PooleParams) (Sh : PooleShocks S) (mbar Φ : ℝ) (w : S → ℝ) :
    List S → ℝ
  | [] => mbar
  | s :: h => pSun P Sh mbar Φ w (s :: h) + (ySun P Sh Φ w s - Sh.eps s) / P.δ

/-- O&R Ex. 3(d): the money supply in a sunspot equilibrium (the feedback rule). -/
noncomputable def mSun (P : PooleParams) (Sh : PooleShocks S) (mbar Φ : ℝ) (w : S → ℝ)
    (g : List S) : ℝ :=
  mbar + Φ * (eSun P Sh mbar Φ w g - mbar)

/-- O&R Ex. 3(d): the nominal interest rate in a sunspot equilibrium (UIP). -/
noncomputable def iSun (P : PooleParams) (Sh : PooleShocks S) (mbar Φ : ℝ) (w : S → ℝ)
    (g : List S) : ℝ :=
  nodeEx Sh (eSun P Sh mbar Φ w) g - eSun P Sh mbar Φ w g

/-- O&R Ex. 3(d): sunspot output has mean zero when `E w = 0`. -/
theorem expect_ySun (P : PooleParams) (Sh : PooleShocks S) (Φ : ℝ) {w : S → ℝ}
    (hw : expect Sh w = 0) : expect Sh (ySun P Sh Φ w) = 0 := by
  have hf : ySun P Sh Φ w = fun s =>
      (P.θ * (P.η - Φ) / den P (P.η - Φ)) * Sh.eps s +
        (-(P.θ * P.δ) / den P (P.η - Φ)) * Sh.v s +
        (P.θ * P.δ * P.η / den P (P.η - Φ)) * w s := by
    funext s
    unfold ySun
    ring
  rw [hf, expect_add, expect_add, expect_const_mul, expect_const_mul, expect_const_mul,
    expect_eps, expect_v, hw]
  ring

/-- O&R Ex. 3(d): `E_{t−1} p_t = m̄ + x_h` in the sunspot equilibrium. -/
theorem nodeEx_pSun (P : PooleParams) (Sh : PooleShocks S) (mbar Φ : ℝ) {w : S → ℝ}
    (hw : expect Sh w = 0) (h : List S) :
    nodeEx Sh (pSun P Sh mbar Φ w) h = mbar + sunspotLevel (sunLam P Φ) w h := by
  rw [nodeEx_eq_expect]
  simp only [pSun]
  rw [expect_add, expect_const, expect_div_const, expect_ySun P Sh Φ hw, zero_div, add_zero]

/-- O&R Ex. 3(d): `E_{t−1} e_t = m̄ + x_h` in the sunspot equilibrium. -/
theorem nodeEx_eSun (P : PooleParams) (Sh : PooleShocks S) (mbar Φ : ℝ) {w : S → ℝ}
    (hw : expect Sh w = 0) (h : List S) :
    nodeEx Sh (eSun P Sh mbar Φ w) h = mbar + sunspotLevel (sunLam P Φ) w h := by
  rw [nodeEx_eq_expect]
  simp only [eSun, pSun]
  rw [expect_add, expect_add, expect_const, expect_div_const, expect_div_const, expect_sub,
    expect_eps, expect_ySun P Sh Φ hw]
  ring

/-- O&R Ex. 3(d): for `|λ| < 1` the sunspot level is bounded by `Σ|w|/(1 − |λ|)`. -/
theorem abs_sunspotLevel_le {lam : ℝ} (hlam : |lam| < 1) (w : S → ℝ) (h : List S) :
    |sunspotLevel lam w h| ≤ (∑ s, |w s|) / (1 - |lam|) := by
  have hpos : 0 < 1 - |lam| := by linarith
  have hW : 0 ≤ ∑ s, |w s| := Finset.sum_nonneg fun s _ => abs_nonneg _
  induction h with
  | nil => simp only [sunspotLevel, abs_zero]; positivity
  | cons s h ih =>
    simp only [sunspotLevel]
    have hs := Finset.single_le_sum (f := fun s => |w s|) (fun s _ => abs_nonneg (w s))
      (Finset.mem_univ s)
    have h1 : |lam * sunspotLevel lam w h + w s| ≤ |lam| * |sunspotLevel lam w h| + |w s| := by
      rw [← abs_mul]
      exact abs_add_le _ _
    have h2 : |lam| * |sunspotLevel lam w h| ≤ |lam| * ((∑ s, |w s|) / (1 - |lam|)) :=
      mul_le_mul_of_nonneg_left ih (abs_nonneg _)
    have h3 : |lam| * ((∑ s, |w s|) / (1 - |lam|)) + ∑ s, |w s| =
        (∑ s, |w s|) / (1 - |lam|) := by
      field_simp
      ring
    linarith

/-- O&R Ex. 3(d): for any `Φ` away from the pole and any mean-zero sunspot `w`, the sunspot
allocation is an equilibrium on the event tree. -/
theorem sunspot_isEqm (P : PooleParams) (Sh : PooleShocks S) (mbar Φ : ℝ)
    (hden : den P (P.η - Φ) ≠ 0) {w : S → ℝ} (hw : expect Sh w = 0) :
    IsEqm P Sh (feedbackPolicy mbar Φ) (pSun P Sh mbar Φ w) (eSun P Sh mbar Φ w)
      (onHead 0 (ySun P Sh Φ w)) (mSun P Sh mbar Φ w) (iSun P Sh mbar Φ w) := by
  intro s h
  have hθ := P.θ_pos.ne'
  have hδ := P.δ_pos.ne'
  have hη := P.η_pos.ne'
  have hY : ySun P Sh Φ w s * den P (P.η - Φ) =
      P.θ * ((P.η - Φ) * Sh.eps s - P.δ * (Sh.v s - P.η * w s)) := by
    unfold ySun
    exact div_mul_cancel₀ _ hden
  refine ⟨rfl, ?_, ?_, ?_, rfl⟩
  · rw [nodeEx_pSun P Sh mbar Φ hw]
    simp only [onHead, pSun]
    field_simp
    ring
  · simp only [onHead, eSun]
    field_simp
    ring
  · unfold mSun iSun
    rw [nodeEx_eSun P Sh mbar Φ hw]
    simp only [onHead, eSun, pSun, sunspotLevel]
    unfold sunLam
    unfold den at hY
    field_simp
    linear_combination (-1 : ℝ) * hY

/-- O&R Ex. 3(d), indeterminacy: for `1 < Φ < 1 + 2η` the sunspot equilibrium has a bounded
price level and exchange rate, so the no-bubble condition does not select a unique
equilibrium there. -/
theorem sunspot_bounded (P : PooleParams) (Sh : PooleShocks S) (mbar Φ : ℝ)
    (hind : 1 < Φ ∧ Φ < 1 + 2 * P.η) (w : S → ℝ) :
    Bounded (pSun P Sh mbar Φ w) ∧ Bounded (eSun P Sh mbar Φ w) := by
  have hlam : |sunLam P Φ| < 1 := (abs_lambda_lt_one_iff P.η_pos).mpr hind
  set B := (∑ s, |w s|) / (1 - |sunLam P Φ|)
  have hB : 0 ≤ B := by
    have : 0 < 1 - |sunLam P Φ| := by linarith
    have hW : 0 ≤ ∑ s, |w s| := Finset.sum_nonneg fun s _ => abs_nonneg _
    positivity
  have hYb : ∀ s, |ySun P Sh Φ w s / P.θ| ≤ ∑ s', |ySun P Sh Φ w s' / P.θ| := fun s =>
    Finset.single_le_sum (f := fun s => |ySun P Sh Φ w s / P.θ|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ s)
  have hZb : ∀ s, |(ySun P Sh Φ w s - Sh.eps s) / P.δ| ≤
      ∑ s', |(ySun P Sh Φ w s' - Sh.eps s') / P.δ| := fun s =>
    Finset.single_le_sum (f := fun s => |(ySun P Sh Φ w s - Sh.eps s) / P.δ|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ s)
  have hS1 : 0 ≤ ∑ s', |ySun P Sh Φ w s' / P.θ| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hS2 : 0 ≤ ∑ s', |(ySun P Sh Φ w s' - Sh.eps s') / P.δ| :=
    Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hp : ∀ g, |pSun P Sh mbar Φ w g| ≤ |mbar| + B + ∑ s', |ySun P Sh Φ w s' / P.θ| := by
    intro g
    cases g with
    | nil => simp only [pSun]; linarith
    | cons s h =>
      simp only [pSun]
      have h1 := abs_sunspotLevel_le hlam w h
      have h2 := hYb s
      calc |mbar + sunspotLevel (sunLam P Φ) w h + ySun P Sh Φ w s / P.θ|
          ≤ |mbar + sunspotLevel (sunLam P Φ) w h| + |ySun P Sh Φ w s / P.θ| :=
            abs_add_le _ _
        _ ≤ |mbar| + |sunspotLevel (sunLam P Φ) w h| + |ySun P Sh Φ w s / P.θ| := by
            linarith [abs_add_le mbar (sunspotLevel (sunLam P Φ) w h)]
        _ ≤ _ := by linarith
  refine ⟨⟨_, hp⟩, ⟨|mbar| + B + ∑ s', |ySun P Sh Φ w s' / P.θ| +
    ∑ s', |(ySun P Sh Φ w s' - Sh.eps s') / P.δ|, fun g => ?_⟩⟩
  cases g with
  | nil => simp only [eSun]; linarith
  | cons s h =>
    simp only [eSun]
    have h1 := hp (s :: h)
    have h2 := hZb s
    calc |pSun P Sh mbar Φ w (s :: h) + (ySun P Sh Φ w s - Sh.eps s) / P.δ|
        ≤ |pSun P Sh mbar Φ w (s :: h)| + |(ySun P Sh Φ w s - Sh.eps s) / P.δ| :=
          abs_add_le _ _
      _ ≤ _ := by linarith

/-- O&R Ex. 3(d): sunspot output differs from the stationary output by `θ δ η w/den`, so it
differs in every state where `w ≠ 0`. -/
theorem ySun_sub_outputMSV (P : PooleParams) (Sh : PooleShocks S) (Φ : ℝ) (w : S → ℝ)
    (s : S) (hden : den P (P.η - Φ) ≠ 0) :
    ySun P Sh Φ w s - outputMSV P Sh Φ s = P.θ * P.δ * P.η * w s / den P (P.η - Φ) ∧
      (w s ≠ 0 → ySun P Sh Φ w s ≠ outputMSV P Sh Φ s) := by
  have he : ySun P Sh Φ w s - outputMSV P Sh Φ s =
      P.θ * P.δ * P.η * w s / den P (P.η - Φ) := by
    unfold ySun outputMSV
    ring
  refine ⟨he, fun hws hEq => ?_⟩
  rw [hEq, sub_self] at he
  have hθ := P.θ_pos.ne'
  have hδ := P.δ_pos.ne'
  have hη := P.η_pos.ne'
  have := (div_eq_zero_iff.mp he.symm).resolve_right hden
  simp [hθ, hδ, hη, hws] at this

/-! ### The determinacy boundary: history-dependent sunspots for `|λ| ≤ 1` -/

/-- O&R Ex. 3(d): `|λ| ≤ 1` exactly when `1 ≤ Φ ≤ 1 + 2η` (the closed indeterminacy region,
including the boundary `Φ = 1` (`λ = 1`) and `Φ = 1 + 2η` (`λ = −1`)). -/
theorem abs_lambda_le_one_iff {η Φ : ℝ} (hη : 0 < η) :
    |(η + 1 - Φ) / η| ≤ 1 ↔ 1 ≤ Φ ∧ Φ ≤ 1 + 2 * η := by
  rw [abs_div, abs_of_pos hη, div_le_iff₀ hη, one_mul, abs_le]
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> linarith
  · rintro ⟨h1, h2⟩; constructor <;> linarith

/-- O&R Ex. 3(d): the sunspot component of the expected price level with a history-dependent
revision, `x_{s :: h} = λ x_h + w_s(h)`, `x_{[]} = 0`. -/
def sunspotLevelH (lam : ℝ) (w : S → List S → ℝ) : List S → ℝ
  | [] => 0
  | s :: h => lam * sunspotLevelH lam w h + w s h

/-- O&R Ex. 3(d): output at node `s :: h` in a sunspot equilibrium with revision `w_s(h)`. -/
noncomputable def ySunH (P : PooleParams) (Sh : PooleShocks S) (Φ : ℝ) (w : S → List S → ℝ)
    (s : S) (h : List S) : ℝ :=
  P.θ * ((P.η - Φ) * Sh.eps s - P.δ * (Sh.v s - P.η * w s h)) / den P (P.η - Φ)

/-- O&R Ex. 3(d): sunspot output as a variable on the event tree. -/
noncomputable def ySunTree (P : PooleParams) (Sh : PooleShocks S) (Φ : ℝ)
    (w : S → List S → ℝ) : List S → ℝ
  | [] => 0
  | s :: h => ySunH P Sh Φ w s h

/-- O&R Ex. 3(d): the price level in a history-dependent sunspot equilibrium. -/
noncomputable def pSunH (P : PooleParams) (Sh : PooleShocks S) (mbar Φ : ℝ)
    (w : S → List S → ℝ) : List S → ℝ
  | [] => mbar
  | s :: h => mbar + sunspotLevelH (sunLam P Φ) w h + ySunH P Sh Φ w s h / P.θ

/-- O&R Ex. 3(d): the exchange rate in a history-dependent sunspot equilibrium. -/
noncomputable def eSunH (P : PooleParams) (Sh : PooleShocks S) (mbar Φ : ℝ)
    (w : S → List S → ℝ) : List S → ℝ
  | [] => mbar
  | s :: h => pSunH P Sh mbar Φ w (s :: h) + (ySunH P Sh Φ w s h - Sh.eps s) / P.δ

/-- O&R Ex. 3(d): money (the feedback rule) in a history-dependent sunspot equilibrium. -/
noncomputable def mSunH (P : PooleParams) (Sh : PooleShocks S) (mbar Φ : ℝ)
    (w : S → List S → ℝ) (g : List S) : ℝ :=
  mbar + Φ * (eSunH P Sh mbar Φ w g - mbar)

/-- O&R Ex. 3(d): the interest rate (UIP) in a history-dependent sunspot equilibrium. -/
noncomputable def iSunH (P : PooleParams) (Sh : PooleShocks S) (mbar Φ : ℝ)
    (w : S → List S → ℝ) (g : List S) : ℝ :=
  nodeEx Sh (eSunH P Sh mbar Φ w) g - eSunH P Sh mbar Φ w g

/-- O&R Ex. 3(d): with mean-zero revisions, sunspot output has conditional mean zero. -/
theorem expect_ySunH (P : PooleParams) (Sh : PooleShocks S) (Φ : ℝ) {w : S → List S → ℝ}
    (hw : ∀ h, expect Sh (fun s => w s h) = 0) (h : List S) :
    expect Sh (fun s => ySunH P Sh Φ w s h) = 0 := by
  have hf : (fun s => ySunH P Sh Φ w s h) = fun s =>
      (P.θ * (P.η - Φ) / den P (P.η - Φ)) * Sh.eps s +
        (-(P.θ * P.δ) / den P (P.η - Φ)) * Sh.v s +
        (P.θ * P.δ * P.η / den P (P.η - Φ)) * w s h := by
    funext s
    unfold ySunH
    ring
  rw [hf, expect_add, expect_add, expect_const_mul, expect_const_mul, expect_const_mul,
    expect_eps, expect_v, hw h]
  ring

/-- O&R Ex. 3(d): `E_{t−1} p_t = m̄ + x_h` in the history-dependent sunspot equilibrium. -/
theorem nodeEx_pSunH (P : PooleParams) (Sh : PooleShocks S) (mbar Φ : ℝ)
    {w : S → List S → ℝ} (hw : ∀ h, expect Sh (fun s => w s h) = 0) (h : List S) :
    nodeEx Sh (pSunH P Sh mbar Φ w) h = mbar + sunspotLevelH (sunLam P Φ) w h := by
  rw [nodeEx_eq_expect]
  simp only [pSunH]
  rw [expect_add, expect_const, expect_div_const, expect_ySunH P Sh Φ hw, zero_div, add_zero]

/-- O&R Ex. 3(d): `E_{t−1} e_t = m̄ + x_h` in the history-dependent sunspot equilibrium. -/
theorem nodeEx_eSunH (P : PooleParams) (Sh : PooleShocks S) (mbar Φ : ℝ)
    {w : S → List S → ℝ} (hw : ∀ h, expect Sh (fun s => w s h) = 0) (h : List S) :
    nodeEx Sh (eSunH P Sh mbar Φ w) h = mbar + sunspotLevelH (sunLam P Φ) w h := by
  rw [nodeEx_eq_expect]
  simp only [eSunH, pSunH]
  rw [expect_add, expect_add, expect_const, expect_div_const, expect_div_const, expect_sub,
    expect_eps, expect_ySunH P Sh Φ hw]
  ring

/-- O&R Ex. 3(d): for any `Φ` away from the pole and any mean-zero history-dependent revision
`w`, the sunspot allocation is an equilibrium on the event tree. -/
theorem sunspotH_isEqm (P : PooleParams) (Sh : PooleShocks S) (mbar Φ : ℝ)
    (hden : den P (P.η - Φ) ≠ 0) {w : S → List S → ℝ}
    (hw : ∀ h, expect Sh (fun s => w s h) = 0) :
    IsEqm P Sh (feedbackPolicy mbar Φ) (pSunH P Sh mbar Φ w) (eSunH P Sh mbar Φ w)
      (ySunTree P Sh Φ w) (mSunH P Sh mbar Φ w) (iSunH P Sh mbar Φ w) := by
  intro s h
  have hθ := P.θ_pos.ne'
  have hδ := P.δ_pos.ne'
  have hη := P.η_pos.ne'
  have hY : ySunH P Sh Φ w s h * den P (P.η - Φ) =
      P.θ * ((P.η - Φ) * Sh.eps s - P.δ * (Sh.v s - P.η * w s h)) := by
    unfold ySunH
    exact div_mul_cancel₀ _ hden
  refine ⟨rfl, ?_, ?_, ?_, rfl⟩
  · rw [nodeEx_pSunH P Sh mbar Φ hw]
    simp only [ySunTree, pSunH]
    field_simp
    ring
  · simp only [ySunTree, eSunH]
    field_simp
    ring
  · unfold mSunH iSunH
    rw [nodeEx_eSunH P Sh mbar Φ hw]
    simp only [ySunTree, eSunH, pSunH, sunspotLevelH]
    unfold sunLam
    unfold den at hY
    field_simp
    linear_combination (-1 : ℝ) * hY

/-- O&R Ex. 3(d): a bounded "martingale-type" sunspot level,
`x_{s :: h} = λ x_h + (1 − |x_h|) g_s`, `x_{[]} = 0`. -/
noncomputable def boundedLevel (lam : ℝ) (g : S → ℝ) : List S → ℝ
  | [] => 0
  | s :: h => lam * boundedLevel lam g h + (1 - |boundedLevel lam g h|) * g s

/-- O&R Ex. 3(d): the history-dependent revision `w_s(h) = (1 − |x_h|) g_s` generating
`boundedLevel`. -/
noncomputable def martRev (lam : ℝ) (g : S → ℝ) (s : S) (h : List S) : ℝ :=
  (1 - |boundedLevel lam g h|) * g s

omit [Fintype S] in
/-- O&R Ex. 3(d): for `|λ| ≤ 1` and `|g| ≤ 1` the level stays in `[−1, 1]` at every node. -/
theorem abs_boundedLevel_le {lam : ℝ} (hlam : |lam| ≤ 1) {g : S → ℝ} (hg : ∀ s, |g s| ≤ 1)
    (h : List S) : |boundedLevel lam g h| ≤ 1 := by
  induction h with
  | nil => simp [boundedLevel]
  | cons s h ih =>
    simp only [boundedLevel]
    have h0 : 0 ≤ 1 - |boundedLevel lam g h| := by linarith
    calc |lam * boundedLevel lam g h + (1 - |boundedLevel lam g h|) * g s|
        ≤ |lam| * |boundedLevel lam g h| + (1 - |boundedLevel lam g h|) * |g s| := by
          refine (abs_add_le _ _).trans ?_
          rw [abs_mul, abs_mul, abs_of_nonneg h0]
      _ ≤ 1 * |boundedLevel lam g h| + (1 - |boundedLevel lam g h|) * 1 := by
          have := abs_nonneg (boundedLevel lam g h)
          have := mul_le_mul_of_nonneg_right hlam this
          have := mul_le_mul_of_nonneg_left (hg s) h0
          linarith
      _ = 1 := by ring

omit [Fintype S] in
/-- O&R Ex. 3(d): `boundedLevel` is the sunspot level generated by the revisions `martRev`. -/
theorem sunspotLevelH_martRev (lam : ℝ) (g : S → ℝ) (h : List S) :
    sunspotLevelH lam (martRev lam g) h = boundedLevel lam g h := by
  induction h with
  | nil => rfl
  | cons s h ih =>
    simp only [sunspotLevelH, boundedLevel, martRev, ih]

/-- O&R Ex. 3(d): the revisions `martRev` have conditional mean zero when `E g = 0`. -/
theorem expect_martRev (Sh : PooleShocks S) (lam : ℝ) {g : S → ℝ} (hg : expect Sh g = 0)
    (h : List S) : expect Sh (fun s => martRev lam g s h) = 0 := by
  unfold martRev
  rw [expect_const_mul, hg, mul_zero]

/-- O&R Ex. 3(d), the boundary settled (and the whole closed region): for
`1 ≤ Φ ≤ 1 + 2η` — including `Φ = 1` (`λ = 1`) and `Φ = 1 + 2η` (`λ = −1`) — away from the
pole, every mean-zero `g` with `|g| ≤ 1` yields an equilibrium with bounded price level and
exchange rate whose output at the first node is `outputMSV + θ δ η g/den`. -/
theorem boundary_sunspot_eqm (P : PooleParams) (Sh : PooleShocks S) (mbar Φ : ℝ)
    (hreg : 1 ≤ Φ ∧ Φ ≤ 1 + 2 * P.η) (hden : den P (P.η - Φ) ≠ 0) {g : S → ℝ}
    (hg0 : expect Sh g = 0) (hg1 : ∀ s, |g s| ≤ 1) :
    IsEqm P Sh (feedbackPolicy mbar Φ) (pSunH P Sh mbar Φ (martRev (sunLam P Φ) g))
      (eSunH P Sh mbar Φ (martRev (sunLam P Φ) g)) (ySunTree P Sh Φ (martRev (sunLam P Φ) g))
      (mSunH P Sh mbar Φ (martRev (sunLam P Φ) g))
      (iSunH P Sh mbar Φ (martRev (sunLam P Φ) g)) ∧
    Bounded (pSunH P Sh mbar Φ (martRev (sunLam P Φ) g)) ∧
    Bounded (eSunH P Sh mbar Φ (martRev (sunLam P Φ) g)) ∧
    ∀ s, ySunTree P Sh Φ (martRev (sunLam P Φ) g) [s] =
      outputMSV P Sh Φ s + P.θ * P.δ * P.η * g s / den P (P.η - Φ) := by
  have hlam : |sunLam P Φ| ≤ 1 := (abs_lambda_le_one_iff P.η_pos).mpr hreg
  set w := martRev (sunLam P Φ) g
  have hw : ∀ h, expect Sh (fun s => w s h) = 0 := expect_martRev Sh _ hg0
  have hwb : ∀ s h, |w s h| ≤ 1 := by
    intro s h
    have h1 := abs_boundedLevel_le hlam hg1 h
    have h0 : 0 ≤ 1 - |boundedLevel (sunLam P Φ) g h| := by linarith
    simp only [w, martRev]
    rw [abs_mul, abs_of_nonneg h0]
    have h2 : (1 - |boundedLevel (sunLam P Φ) g h|) * |g s| ≤ 1 * 1 :=
      mul_le_mul (by linarith [abs_nonneg (boundedLevel (sunLam P Φ) g h)]) (hg1 s)
        (abs_nonneg _) (by norm_num)
    linarith
  have hθ := P.θ_pos
  have hδ := P.δ_pos
  set K := ∑ s, |outputMSV P Sh Φ s| + |P.θ * P.δ * P.η / den P (P.η - Φ)|
  have hyb : ∀ s h, |ySunH P Sh Φ w s h| ≤ K := by
    intro s h
    have he : ySunH P Sh Φ w s h =
        outputMSV P Sh Φ s + P.θ * P.δ * P.η / den P (P.η - Φ) * w s h := by
      unfold ySunH outputMSV
      ring
    rw [he]
    have h1 := Finset.single_le_sum (f := fun s => |outputMSV P Sh Φ s|)
      (fun _ _ => abs_nonneg _) (Finset.mem_univ s)
    have h2 : |P.θ * P.δ * P.η / den P (P.η - Φ) * w s h| ≤
        |P.θ * P.δ * P.η / den P (P.η - Φ)| := by
      rw [abs_mul]
      have := hwb s h
      have := abs_nonneg (P.θ * P.δ * P.η / den P (P.η - Φ))
      nlinarith
    calc _ ≤ |outputMSV P Sh Φ s| + |P.θ * P.δ * P.η / den P (P.η - Φ) * w s h| :=
          abs_add_le _ _
      _ ≤ K := by simp only [K]; linarith
  have hlev : ∀ h, |sunspotLevelH (sunLam P Φ) w h| ≤ 1 := fun h => by
    simp only [w]
    rw [sunspotLevelH_martRev]
    exact abs_boundedLevel_le hlam hg1 h
  have hK : 0 ≤ K := by
    have := Finset.sum_nonneg (s := Finset.univ) fun s _ => abs_nonneg (outputMSV P Sh Φ s)
    have := abs_nonneg (P.θ * P.δ * P.η / den P (P.η - Φ))
    simp only [K]
    linarith
  have hE : ∑ s, |Sh.eps s| ≥ 0 := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hp : ∀ x, |pSunH P Sh mbar Φ w x| ≤ |mbar| + 1 + K / P.θ := by
    intro x
    cases x with
    | nil =>
      simp only [pSunH]
      have : 0 ≤ K / P.θ := by positivity
      linarith
    | cons s h =>
      simp only [pSunH]
      have h1 := hlev h
      have h2 : |ySunH P Sh Φ w s h / P.θ| ≤ K / P.θ := by
        rw [abs_div, abs_of_pos hθ]
        exact div_le_div_of_nonneg_right (hyb s h) hθ.le
      calc _ ≤ |mbar + sunspotLevelH (sunLam P Φ) w h| + |ySunH P Sh Φ w s h / P.θ| :=
            abs_add_le _ _
        _ ≤ |mbar| + |sunspotLevelH (sunLam P Φ) w h| + |ySunH P Sh Φ w s h / P.θ| := by
            linarith [abs_add_le mbar (sunspotLevelH (sunLam P Φ) w h)]
        _ ≤ _ := by linarith
  refine ⟨sunspotH_isEqm P Sh mbar Φ hden hw, ⟨_, hp⟩,
    ⟨|mbar| + 1 + K / P.θ + (K + ∑ s, |Sh.eps s|) / P.δ, fun x => ?_⟩, fun s => ?_⟩
  · have hq : 0 ≤ (K + ∑ s, |Sh.eps s|) / P.δ := by positivity
    cases x with
    | nil =>
      simp only [eSunH]
      have : 0 ≤ K / P.θ := by positivity
      linarith
    | cons s h =>
      simp only [eSunH]
      have h1 := hp (s :: h)
      have h3 := Finset.single_le_sum (f := fun s => |Sh.eps s|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ s)
      have h2 : |(ySunH P Sh Φ w s h - Sh.eps s) / P.δ| ≤ (K + ∑ s, |Sh.eps s|) / P.δ := by
        rw [abs_div, abs_of_pos hδ]
        refine div_le_div_of_nonneg_right ?_ hδ.le
        have := abs_sub (ySunH P Sh Φ w s h) (Sh.eps s)
        have := hyb s h
        linarith
      calc _ ≤ |pSunH P Sh mbar Φ w (s :: h)| + |(ySunH P Sh Φ w s h - Sh.eps s) / P.δ| :=
            abs_add_le _ _
        _ ≤ _ := by linarith
  · simp only [ySunTree, ySunH, w, martRev, boundedLevel, abs_zero, sub_zero, one_mul]
    unfold outputMSV
    ring

/-- O&R Ex. 3(d), the exact determinacy result: away from the pole, and provided the state
space carries some nonzero mean-zero variable, output is the same in every bounded
equilibrium (it equals `outputMSV`) if and only if `Φ < 1` or `Φ > 1 + 2η`. On the boundary
`Φ = 1`, `Φ = 1 + 2η` the equilibrium is indeterminate. -/
theorem bounded_eqm_output_unique_iff (P : PooleParams) (Sh : PooleShocks S) (mbar Φ : ℝ)
    (hden : den P (P.η - Φ) ≠ 0) (hnd : ∃ g : S → ℝ, expect Sh g = 0 ∧ ∃ s, g s ≠ 0) :
    (∀ p e y m i : List S → ℝ, IsEqm P Sh (feedbackPolicy mbar Φ) p e y m i → Bounded p →
      ∀ s h, y (s :: h) = outputMSV P Sh Φ s) ↔ (Φ < 1 ∨ 1 + 2 * P.η < Φ) := by
  constructor
  · intro hu
    by_contra hdet
    push Not at hdet
    obtain ⟨g, hg0, s0, hs0⟩ := hnd
    set c := 1 + ∑ s, |g s|
    have hc : 0 < c := by
      have := Finset.sum_nonneg (s := Finset.univ) fun s _ => abs_nonneg (g s)
      simp only [c]
      linarith
    have hg0' : expect Sh (fun s => g s / c) = 0 := by rw [expect_div_const, hg0, zero_div]
    have hg1' : ∀ s, |g s / c| ≤ 1 := by
      intro s
      rw [abs_div, abs_of_pos hc, div_le_one hc]
      have := Finset.single_le_sum (f := fun s => |g s|) (fun _ _ => abs_nonneg _)
        (Finset.mem_univ s)
      simp only [c]
      linarith
    obtain ⟨hE, hb, _, hy⟩ :=
      boundary_sunspot_eqm P Sh mbar Φ ⟨hdet.1, hdet.2⟩ hden hg0' hg1'
    have h1 := hu _ _ _ _ _ hE hb s0 []
    rw [hy s0] at h1
    have h2 : P.θ * P.δ * P.η * (g s0 / c) / den P (P.η - Φ) = 0 := by linarith
    have hθ := P.θ_pos.ne'
    have hδ := P.δ_pos.ne'
    have hη := P.η_pos.ne'
    rcases div_eq_zero_iff.mp h2 with h3 | h3
    · simp [hθ, hδ, hη, hs0, hc.ne'] at h3
    · exact hden h3
  · intro hdet p e y m i hE hb s h
    exact (feedback_eqm_unique hdet hden hE hb s h).1

/-- O&R Ex. 3(d): at the boundary `Φ = 1` (`λ = 1`) bounded sunspot equilibria exist. -/
theorem sunspot_at_phi_one (P : PooleParams) (Sh : PooleShocks S) (mbar : ℝ)
    (hden : den P (P.η - 1) ≠ 0) {g : S → ℝ} (hg0 : expect Sh g = 0)
    (hg1 : ∀ s, |g s| ≤ 1) :
    sunLam P 1 = 1 ∧ IsEqm P Sh (feedbackPolicy mbar 1)
      (pSunH P Sh mbar 1 (martRev (sunLam P 1) g)) (eSunH P Sh mbar 1 (martRev (sunLam P 1) g))
      (ySunTree P Sh 1 (martRev (sunLam P 1) g)) (mSunH P Sh mbar 1 (martRev (sunLam P 1) g))
      (iSunH P Sh mbar 1 (martRev (sunLam P 1) g)) ∧
    Bounded (pSunH P Sh mbar 1 (martRev (sunLam P 1) g)) := by
  have hη := P.η_pos
  obtain ⟨h1, h2, _, _⟩ := boundary_sunspot_eqm P Sh mbar 1 ⟨le_refl _, by linarith⟩ hden hg0 hg1
  refine ⟨?_, h1, h2⟩
  unfold sunLam
  field_simp
  ring

/-- O&R Ex. 3(d): at the boundary `Φ = 1 + 2η` (`λ = −1`) bounded sunspot equilibria exist. -/
theorem sunspot_at_phi_one_add_two_eta (P : PooleParams) (Sh : PooleShocks S) (mbar : ℝ)
    (hden : den P (P.η - (1 + 2 * P.η)) ≠ 0) {g : S → ℝ} (hg0 : expect Sh g = 0)
    (hg1 : ∀ s, |g s| ≤ 1) :
    sunLam P (1 + 2 * P.η) = -1 ∧ IsEqm P Sh (feedbackPolicy mbar (1 + 2 * P.η))
      (pSunH P Sh mbar (1 + 2 * P.η) (martRev (sunLam P (1 + 2 * P.η)) g))
      (eSunH P Sh mbar (1 + 2 * P.η) (martRev (sunLam P (1 + 2 * P.η)) g))
      (ySunTree P Sh (1 + 2 * P.η) (martRev (sunLam P (1 + 2 * P.η)) g))
      (mSunH P Sh mbar (1 + 2 * P.η) (martRev (sunLam P (1 + 2 * P.η)) g))
      (iSunH P Sh mbar (1 + 2 * P.η) (martRev (sunLam P (1 + 2 * P.η)) g)) ∧
    Bounded (pSunH P Sh mbar (1 + 2 * P.η) (martRev (sunLam P (1 + 2 * P.η)) g)) := by
  have hη := P.η_pos
  obtain ⟨h1, h2, _, _⟩ :=
    boundary_sunspot_eqm P Sh mbar (1 + 2 * P.η) ⟨by linarith, le_refl _⟩ hden hg0 hg1
  refine ⟨?_, h1, h2⟩
  unfold sunLam
  field_simp
  ring

end ObstfeldRogoff.NominalRigidities.PooleRegimeChoice

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# International monetary policy coordination: Nash versus the planner

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §9.5.5,
pp. 654–657, including the exercise of footnote 42 ("solve for the levels of monetary
growth in both the Nash and planner solutions").

Home and Foreign output gaps are
`y − ȳ = a₁ (Δm − E_{t−1}Δm) + a₂ (Δm* − E_{t−1}Δm*) + ε` and
`y* − ȳ = a₁ (Δm* − E_{t−1}Δm*) + a₂ (Δm − E_{t−1}Δm) + ε*`,
and the losses are `L = (y − ȳ)² + χ (Δm)²`, `L* = (y* − ȳ)² + χ (Δm*)²`, with `χ > 0`.

**Stochastic structure.** The shocks `(ε, ε*)` live on a finite state space with mean zero
(`E_{t−1} ε = E_{t−1} ε* = 0`). Policies are state-contingent money growth rates
`Δm, Δm* : S → ℝ`, chosen after the shock, taking the expectations `E_{t−1}Δm`,
`E_{t−1}Δm*` (formed before the shock) as given; rational expectations require these to
equal the means of the chosen policies (a one-shot-game equilibrium, as in the book).

Main results.
* First-order conditions are necessary and sufficient, both for each country's best
  response and for the planner (the objectives are strictly convex quadratics).
* Expected money growth is zero in both the Nash and the planner solution (no inflation bias
  without a wedge, footnote 42).
* The Nash equilibrium is unique iff `(a₁² + χ)² ≠ a₁² a₂²`, with a closed form; when the
  determinant vanishes equilibria are not unique. The planner's solution always exists, is
  unique, and has a closed form (its determinant is positive).
* With symmetric shocks and weights, Nash responds with coefficient `a₁/(a₁² + a₁a₂ + χ)` and
  the planner with `(a₁ + a₂)/((a₁ + a₂)² + χ)`; the planner responds more strongly iff
  `a₂ > 0` (the difference is exactly `χ a₂` over positive denominators).
* The planner's expected weighted loss never exceeds Nash's, strictly if `a₂ ≠ 0` and a
  shock hits with positive probability.
* With `χ = 0`, both outputs can be stabilised exactly iff `a₁² ≠ a₂²`, and then Nash
  already does so ("two instruments, two targets").
-/

namespace ObstfeldRogoff.NominalRigidities.PolicyCoordination

open Finset

/-- O&R §9.5.5, p. 654: the spillover coefficients `a₁` (own money surprise) and `a₂`
(foreign money surprise) and the weight `χ > 0` on money growth in the loss. -/
structure CoordParams where
  a1 : ℝ
  a2 : ℝ
  χ : ℝ
  χ_pos : 0 < χ

/-- O&R §9.5.5, p. 655: Home and Foreign shocks on a finite state space, with mean zero. -/
structure CoordShocks (S : Type) [Fintype S] where
  prob : S → ℝ
  eps : S → ℝ
  epsF : S → ℝ
  prob_nonneg : ∀ s, 0 ≤ prob s
  prob_sum : ∑ s, prob s = 1
  eps_mean : ∑ s, prob s * eps s = 0
  epsF_mean : ∑ s, prob s * epsF s = 0

variable {S : Type} [Fintype S]

/-- The expectation of a state-contingent variable (O&R §9.5.5). -/
def expect (Sh : CoordShocks S) (f : S → ℝ) : ℝ := ∑ s, Sh.prob s * f s

/-- O&R §9.5.5, p. 654: the Home output gap given expectations `Em, EmF`, money growth
`M, MF` and the Home shock `e`. -/
def homeGap (P : CoordParams) (Em EmF M MF e : ℝ) : ℝ :=
  P.a1 * (M - Em) + P.a2 * (MF - EmF) + e

/-- O&R §9.5.5, p. 655: the Foreign output gap. -/
def foreignGap (P : CoordParams) (Em EmF M MF eF : ℝ) : ℝ :=
  P.a1 * (MF - EmF) + P.a2 * (M - Em) + eF

/-- O&R §9.5.5, p. 655: the Home loss `(y − ȳ)² + χ (Δm)²`. -/
def homeLoss (P : CoordParams) (Em EmF M MF e : ℝ) : ℝ :=
  homeGap P Em EmF M MF e ^ 2 + P.χ * M ^ 2

/-- O&R §9.5.5, p. 655: the Foreign loss `(y* − ȳ)² + χ (Δm*)²`. -/
def foreignLoss (P : CoordParams) (Em EmF M MF eF : ℝ) : ℝ :=
  foreignGap P Em EmF M MF eF ^ 2 + P.χ * MF ^ 2

/-- O&R §9.5.5, p. 656: the planner's objective `x L + (1 − x) L*` (weight `w`). -/
def welfare (P : CoordParams) (w Em EmF M MF e eF : ℝ) : ℝ :=
  w * homeLoss P Em EmF M MF e + (1 - w) * foreignLoss P Em EmF M MF eF

/-- O&R §9.5.5, p. 655: a (one-shot-game) Nash equilibrium in state-contingent money
growth: in every state each country's choice is a best response to the other's, given
rational expectations `E_{t−1}Δm = E M`, `E_{t−1}Δm* = E MF`. -/
def IsNash (P : CoordParams) (Sh : CoordShocks S) (M MF : S → ℝ) : Prop :=
  ∀ s, (∀ x, homeLoss P (expect Sh M) (expect Sh MF) (M s) (MF s) (Sh.eps s) ≤
      homeLoss P (expect Sh M) (expect Sh MF) x (MF s) (Sh.eps s)) ∧
    (∀ x, foreignLoss P (expect Sh M) (expect Sh MF) (M s) (MF s) (Sh.epsF s) ≤
      foreignLoss P (expect Sh M) (expect Sh MF) (M s) x (Sh.epsF s))

/-- O&R §9.5.5, p. 656: the planner's solution with weight `w`: in every state the pair
`(M s, MF s)` minimises `w L + (1 − w) L*`, given rational expectations. -/
def IsPlanner (P : CoordParams) (Sh : CoordShocks S) (w : ℝ) (M MF : S → ℝ) : Prop :=
  ∀ s x xF, welfare P w (expect Sh M) (expect Sh MF) (M s) (MF s) (Sh.eps s) (Sh.epsF s) ≤
    welfare P w (expect Sh M) (expect Sh MF) x xF (Sh.eps s) (Sh.epsF s)

/-! ### Expectation algebra -/

/-- The expectation of an affine combination (O&R §9.5.5 background). -/
theorem expect_affine (Sh : CoordShocks S) (f g k l : S → ℝ) (c1 c2 c3 c4 c5 : ℝ) :
    ∑ s, Sh.prob s * (c1 * f s + c2 * g s + c3 * k s + c4 * l s + c5) =
      c1 * expect Sh f + c2 * expect Sh g + c3 * expect Sh k + c4 * expect Sh l + c5 := by
  unfold expect
  have h : ∀ s, Sh.prob s * (c1 * f s + c2 * g s + c3 * k s + c4 * l s + c5) =
      c1 * (Sh.prob s * f s) + c2 * (Sh.prob s * g s) + c3 * (Sh.prob s * k s) +
        c4 * (Sh.prob s * l s) + c5 * Sh.prob s := fun s => by ring
  rw [Finset.sum_congr rfl fun s _ => h s]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Sh.prob_sum, mul_one]

/-! ### Best responses -/

/-- O&R p. 655: the exact expansion of the Home loss around `x₀`. -/
theorem homeLoss_sub (P : CoordParams) (Em EmF MF e x0 x : ℝ) :
    homeLoss P Em EmF x MF e - homeLoss P Em EmF x0 MF e =
      2 * (x - x0) * (P.a1 * homeGap P Em EmF x0 MF e + P.χ * x0) +
        (P.a1 ^ 2 + P.χ) * (x - x0) ^ 2 := by
  unfold homeLoss homeGap
  ring

/-- O&R p. 655: the exact expansion of the Foreign loss around `x₀`. -/
theorem foreignLoss_sub (P : CoordParams) (Em EmF M eF x0 x : ℝ) :
    foreignLoss P Em EmF M x eF - foreignLoss P Em EmF M x0 eF =
      2 * (x - x0) * (P.a1 * foreignGap P Em EmF M x0 eF + P.χ * x0) +
        (P.a1 ^ 2 + P.χ) * (x - x0) ^ 2 := by
  unfold foreignLoss foreignGap
  ring

/-- O&R p. 655: Home's first-order condition `a₁ (y − ȳ) + χ Δm = 0` is necessary and
sufficient for a best response. -/
theorem home_best_response_iff (P : CoordParams) (Em EmF MF e x0 : ℝ) :
    (∀ x, homeLoss P Em EmF x0 MF e ≤ homeLoss P Em EmF x MF e) ↔
      P.a1 * homeGap P Em EmF x0 MF e + P.χ * x0 = 0 := by
  have hK : 0 < P.a1 ^ 2 + P.χ := by have := P.χ_pos; positivity
  constructor
  · intro h
    by_contra hF
    set F := P.a1 * homeGap P Em EmF x0 MF e + P.χ * x0
    have h1 := homeLoss_sub P Em EmF MF e x0 (x0 - F / (P.a1 ^ 2 + P.χ))
    have h2 := h (x0 - F / (P.a1 ^ 2 + P.χ))
    have h3 : 2 * (x0 - F / (P.a1 ^ 2 + P.χ) - x0) * F +
        (P.a1 ^ 2 + P.χ) * (x0 - F / (P.a1 ^ 2 + P.χ) - x0) ^ 2 =
          -(F ^ 2 / (P.a1 ^ 2 + P.χ)) := by
      field_simp
      ring
    have h4 : 0 < F ^ 2 / (P.a1 ^ 2 + P.χ) := by positivity
    linarith
  · intro hF x
    have h1 := homeLoss_sub P Em EmF MF e x0 x
    rw [hF, mul_zero, zero_add] at h1
    nlinarith [sq_nonneg (x - x0)]

/-- O&R p. 655: Foreign's first-order condition is necessary and sufficient. -/
theorem foreign_best_response_iff (P : CoordParams) (Em EmF M eF x0 : ℝ) :
    (∀ x, foreignLoss P Em EmF M x0 eF ≤ foreignLoss P Em EmF M x eF) ↔
      P.a1 * foreignGap P Em EmF M x0 eF + P.χ * x0 = 0 := by
  have hK : 0 < P.a1 ^ 2 + P.χ := by have := P.χ_pos; positivity
  constructor
  · intro h
    by_contra hF
    set F := P.a1 * foreignGap P Em EmF M x0 eF + P.χ * x0
    have h1 := foreignLoss_sub P Em EmF M eF x0 (x0 - F / (P.a1 ^ 2 + P.χ))
    have h2 := h (x0 - F / (P.a1 ^ 2 + P.χ))
    have h3 : 2 * (x0 - F / (P.a1 ^ 2 + P.χ) - x0) * F +
        (P.a1 ^ 2 + P.χ) * (x0 - F / (P.a1 ^ 2 + P.χ) - x0) ^ 2 =
          -(F ^ 2 / (P.a1 ^ 2 + P.χ)) := by
      field_simp
      ring
    have h4 : 0 < F ^ 2 / (P.a1 ^ 2 + P.χ) := by positivity
    linarith
  · intro hF x
    have h1 := foreignLoss_sub P Em EmF M eF x0 x
    rw [hF, mul_zero, zero_add] at h1
    nlinarith [sq_nonneg (x - x0)]

/-- O&R p. 655: a Nash equilibrium is exactly a profile satisfying both first-order
conditions in every state. -/
theorem nash_iff_foc (P : CoordParams) (Sh : CoordShocks S) (M MF : S → ℝ) :
    IsNash P Sh M MF ↔ ∀ s,
      P.a1 * homeGap P (expect Sh M) (expect Sh MF) (M s) (MF s) (Sh.eps s) + P.χ * M s = 0 ∧
      P.a1 * foreignGap P (expect Sh M) (expect Sh MF) (M s) (MF s) (Sh.epsF s) +
        P.χ * MF s = 0 := by
  unfold IsNash
  simp only [home_best_response_iff, foreign_best_response_iff]

/-- O&R fn 42: in any Nash equilibrium expected money growth is zero in both countries. -/
theorem nash_expect_zero {P : CoordParams} {Sh : CoordShocks S} {M MF : S → ℝ}
    (hN : IsNash P Sh M MF) : expect Sh M = 0 ∧ expect Sh MF = 0 := by
  rw [nash_iff_foc] at hN
  have hχ := P.χ_pos.ne'
  have h1 : ∑ s, Sh.prob s * ((P.a1 ^ 2 + P.χ) * M s + (P.a1 * P.a2) * MF s +
      P.a1 * Sh.eps s + 0 * Sh.epsF s +
        (-(P.a1 * (P.a1 * expect Sh M + P.a2 * expect Sh MF)))) = 0 := by
    refine Finset.sum_eq_zero fun s _ => ?_
    have := (hN s).1
    unfold homeGap at this
    rw [show (P.a1 ^ 2 + P.χ) * M s + (P.a1 * P.a2) * MF s + P.a1 * Sh.eps s + 0 * Sh.epsF s +
      -(P.a1 * (P.a1 * expect Sh M + P.a2 * expect Sh MF)) = 0 by linear_combination this,
      mul_zero]
  have h2 : ∑ s, Sh.prob s * ((P.a1 * P.a2) * M s + (P.a1 ^ 2 + P.χ) * MF s +
      0 * Sh.eps s + P.a1 * Sh.epsF s +
        (-(P.a1 * (P.a1 * expect Sh MF + P.a2 * expect Sh M)))) = 0 := by
    refine Finset.sum_eq_zero fun s _ => ?_
    have := (hN s).2
    unfold foreignGap at this
    rw [show (P.a1 * P.a2) * M s + (P.a1 ^ 2 + P.χ) * MF s + 0 * Sh.eps s + P.a1 * Sh.epsF s +
      -(P.a1 * (P.a1 * expect Sh MF + P.a2 * expect Sh M)) = 0 by linear_combination this,
      mul_zero]
  rw [expect_affine] at h1 h2
  have he : expect Sh Sh.eps = 0 := Sh.eps_mean
  have heF : expect Sh Sh.epsF = 0 := Sh.epsF_mean
  rw [he, heF] at h1 h2
  constructor
  · have : P.χ * expect Sh M = 0 := by linear_combination h1
    exact (mul_eq_zero.mp this).resolve_left hχ
  · have : P.χ * expect Sh MF = 0 := by linear_combination h2
    exact (mul_eq_zero.mp this).resolve_left hχ

/-- O&R p. 655 and fn 42: Nash equilibria are exactly the zero-mean solutions of the linear
system `(a₁² + χ) Δm + a₁a₂ Δm* = −a₁ ε`, `a₁a₂ Δm + (a₁² + χ) Δm* = −a₁ ε*`. -/
theorem nash_iff_system (P : CoordParams) (Sh : CoordShocks S) (M MF : S → ℝ) :
    IsNash P Sh M MF ↔ expect Sh M = 0 ∧ expect Sh MF = 0 ∧ ∀ s,
      (P.a1 ^ 2 + P.χ) * M s + P.a1 * P.a2 * MF s = -(P.a1 * Sh.eps s) ∧
      P.a1 * P.a2 * M s + (P.a1 ^ 2 + P.χ) * MF s = -(P.a1 * Sh.epsF s) := by
  constructor
  · intro hN
    obtain ⟨h0, h0F⟩ := nash_expect_zero hN
    rw [nash_iff_foc] at hN
    refine ⟨h0, h0F, fun s => ?_⟩
    have h1 := (hN s).1
    have h2 := (hN s).2
    unfold homeGap at h1
    unfold foreignGap at h2
    rw [h0, h0F] at h1 h2
    constructor
    · linear_combination h1
    · linear_combination h2
  · rintro ⟨h0, h0F, hs⟩
    rw [nash_iff_foc]
    intro s
    unfold homeGap foreignGap
    rw [h0, h0F]
    constructor
    · linear_combination (hs s).1
    · linear_combination (hs s).2

/-- O&R fn 42: the Nash determinant `(a₁² + χ)² − a₁² a₂²`. -/
def nashDet (P : CoordParams) : ℝ := (P.a1 ^ 2 + P.χ) ^ 2 - (P.a1 * P.a2) ^ 2

/-- O&R fn 42: Home's Nash money growth `−a₁ ((a₁² + χ) ε − a₁a₂ ε*)/det`. -/
noncomputable def nashM (P : CoordParams) (Sh : CoordShocks S) (s : S) : ℝ :=
  -(P.a1 * ((P.a1 ^ 2 + P.χ) * Sh.eps s - P.a1 * P.a2 * Sh.epsF s)) / nashDet P

/-- O&R fn 42: Foreign's Nash money growth `−a₁ ((a₁² + χ) ε* − a₁a₂ ε)/det`. -/
noncomputable def nashMF (P : CoordParams) (Sh : CoordShocks S) (s : S) : ℝ :=
  -(P.a1 * ((P.a1 ^ 2 + P.χ) * Sh.epsF s - P.a1 * P.a2 * Sh.eps s)) / nashDet P

/-- O&R fn 42: the closed form has zero mean. -/
theorem expect_nashM (P : CoordParams) (Sh : CoordShocks S) :
    expect Sh (nashM P Sh) = 0 ∧ expect Sh (nashMF P Sh) = 0 := by
  have he : expect Sh Sh.eps = 0 := Sh.eps_mean
  have heF : expect Sh Sh.epsF = 0 := Sh.epsF_mean
  set c1 := -(P.a1 * (P.a1 ^ 2 + P.χ)) / nashDet P
  set c2 := P.a1 * (P.a1 * P.a2) / nashDet P
  constructor
  · have hs : ∀ s, Sh.prob s * nashM P Sh s = Sh.prob s *
        (c1 * Sh.eps s + c2 * Sh.epsF s + 0 * Sh.eps s + 0 * Sh.eps s + 0) := fun s => by
      unfold nashM
      ring
    unfold expect
    rw [Finset.sum_congr rfl fun s _ => hs s, expect_affine, he, heF]
    ring
  · have hs : ∀ s, Sh.prob s * nashMF P Sh s = Sh.prob s *
        (c1 * Sh.epsF s + c2 * Sh.eps s + 0 * Sh.eps s + 0 * Sh.eps s + 0) := fun s => by
      unfold nashMF
      ring
    unfold expect
    rw [Finset.sum_congr rfl fun s _ => hs s, expect_affine, he, heF]
    ring

/-- O&R fn 42, Nash existence, uniqueness and closed form: when `(a₁² + χ)² ≠ a₁² a₂²` a
profile is a Nash equilibrium iff it equals `(nashM, nashMF)` in every state. -/
theorem nash_iff_closed_form {P : CoordParams} {Sh : CoordShocks S} (hdet : nashDet P ≠ 0)
    (M MF : S → ℝ) :
    IsNash P Sh M MF ↔ ∀ s, M s = nashM P Sh s ∧ MF s = nashMF P Sh s := by
  rw [nash_iff_system]
  constructor
  · rintro ⟨_, _, hs⟩ s
    obtain ⟨h1, h2⟩ := hs s
    unfold nashM nashMF
    unfold nashDet at hdet ⊢
    constructor
    · rw [eq_div_iff hdet]
      linear_combination (P.a1 ^ 2 + P.χ) * h1 - P.a1 * P.a2 * h2
    · rw [eq_div_iff hdet]
      linear_combination (P.a1 ^ 2 + P.χ) * h2 - P.a1 * P.a2 * h1
  · intro hs
    have hM : M = nashM P Sh := funext fun s => (hs s).1
    have hMF : MF = nashMF P Sh := funext fun s => (hs s).2
    subst hM hMF
    refine ⟨(expect_nashM P Sh).1, (expect_nashM P Sh).2, fun s => ?_⟩
    unfold nashM nashMF nashDet
    unfold nashDet at hdet
    constructor
    · rw [mul_div_assoc', mul_div_assoc', ← add_div, div_eq_iff hdet]
      ring
    · rw [mul_div_assoc', mul_div_assoc', ← add_div, div_eq_iff hdet]
      ring

/-- O&R fn 42: the closed form is a Nash equilibrium (existence) when the determinant is
nonzero. -/
theorem nash_exists {P : CoordParams} (Sh : CoordShocks S) (hdet : nashDet P ≠ 0) :
    IsNash P Sh (nashM P Sh) (nashMF P Sh) :=
  (nash_iff_closed_form hdet _ _).mpr fun _ => ⟨rfl, rfl⟩

/-- O&R p. 655, the determinant condition is sharp: if `(a₁² + χ)² = a₁² a₂²` then adding
any zero-mean `g` along the kernel direction `(1, c)`, `c = ±1`, to a Nash equilibrium gives
another Nash equilibrium, so uniqueness fails as soon as a nonzero zero-mean `g` exists. -/
theorem nash_nonunique_of_det_zero {P : CoordParams} {Sh : CoordShocks S}
    (hdet : nashDet P = 0) {M MF : S → ℝ} (hN : IsNash P Sh M MF) {g : S → ℝ}
    (hg : expect Sh g = 0) :
    ∃ c : ℝ, (c = 1 ∨ c = -1) ∧ IsNash P Sh (fun s => M s + g s) (fun s => MF s + c * g s) := by
  rw [nash_iff_system] at hN
  obtain ⟨h0, h0F, hs⟩ := hN
  have hfac : (P.a1 ^ 2 + P.χ - P.a1 * P.a2) * (P.a1 ^ 2 + P.χ + P.a1 * P.a2) = 0 := by
    unfold nashDet at hdet
    linear_combination hdet
  have hEg : ∀ c : ℝ, expect Sh (fun s => MF s + c * g s) = 0 ∧
      expect Sh (fun s => M s + g s) = 0 := by
    intro c
    unfold expect at h0 h0F hg ⊢
    constructor
    · change ∑ s, Sh.prob s * (MF s + c * g s) = 0
      have : ∑ s, Sh.prob s * (MF s + c * g s) =
          ∑ s, Sh.prob s * MF s + c * ∑ s, Sh.prob s * g s := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun s _ => by ring
      rw [this, h0F, hg]
      ring
    · change ∑ s, Sh.prob s * (M s + g s) = 0
      have : ∑ s, Sh.prob s * (M s + g s) = ∑ s, Sh.prob s * M s + ∑ s, Sh.prob s * g s := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun s _ => by ring
      rw [this, h0, hg]
      ring
  rcases mul_eq_zero.mp hfac with hk | hk
  · refine ⟨-1, Or.inr rfl, ?_⟩
    rw [nash_iff_system]
    refine ⟨(hEg (-1)).2, (hEg (-1)).1, fun s => ⟨?_, ?_⟩⟩
    · linear_combination (hs s).1 + g s * hk
    · linear_combination (hs s).2 - g s * hk
  · refine ⟨1, Or.inl rfl, ?_⟩
    rw [nash_iff_system]
    refine ⟨(hEg 1).2, (hEg 1).1, fun s => ⟨?_, ?_⟩⟩
    · linear_combination (hs s).1 + g s * hk
    · linear_combination (hs s).2 + g s * hk

/-! ### The planner -/

/-- O&R p. 656: the planner's first-order condition with respect to `Δm` (divided by 2). -/
def plannerFOC1 (P : CoordParams) (w Em EmF M MF e eF : ℝ) : ℝ :=
  w * (P.a1 * homeGap P Em EmF M MF e + P.χ * M) + (1 - w) * P.a2 * foreignGap P Em EmF M MF eF

/-- O&R p. 656: the planner's first-order condition with respect to `Δm*` (divided by 2). -/
def plannerFOC2 (P : CoordParams) (w Em EmF M MF e eF : ℝ) : ℝ :=
  w * P.a2 * homeGap P Em EmF M MF e + (1 - w) * (P.a1 * foreignGap P Em EmF M MF eF + P.χ * MF)

/-- O&R p. 656: the quadratic part of the planner's objective. -/
def plannerQ (P : CoordParams) (w d dF : ℝ) : ℝ :=
  w * ((P.a1 * d + P.a2 * dF) ^ 2 + P.χ * d ^ 2) +
    (1 - w) * ((P.a2 * d + P.a1 * dF) ^ 2 + P.χ * dF ^ 2)

/-- O&R p. 656: the exact expansion of the planner's objective around `(M, MF)`. -/
theorem welfare_sub (P : CoordParams) (w Em EmF M MF e eF x xF : ℝ) :
    welfare P w Em EmF x xF e eF - welfare P w Em EmF M MF e eF =
      2 * ((x - M) * plannerFOC1 P w Em EmF M MF e eF +
        (xF - MF) * plannerFOC2 P w Em EmF M MF e eF) + plannerQ P w (x - M) (xF - MF) := by
  unfold welfare homeLoss foreignLoss plannerFOC1 plannerFOC2 plannerQ homeGap foreignGap
  ring

/-- O&R p. 656: for `0 < w < 1` the quadratic part is positive definite. -/
theorem plannerQ_pos (P : CoordParams) {w : ℝ} (hw0 : 0 < w) (hw1 : w < 1) {d dF : ℝ}
    (hd : d ≠ 0 ∨ dF ≠ 0) : 0 < plannerQ P w d dF := by
  have hχ := P.χ_pos
  have h1w : 0 < 1 - w := by linarith
  unfold plannerQ
  have h1 : 0 ≤ w * (P.a1 * d + P.a2 * dF) ^ 2 := by positivity
  have h2 : 0 ≤ (1 - w) * (P.a2 * d + P.a1 * dF) ^ 2 := by positivity
  rcases hd with hd | hd
  · have : 0 < w * (P.χ * d ^ 2) := by positivity
    have : 0 ≤ (1 - w) * (P.χ * dF ^ 2) := by positivity
    nlinarith
  · have : 0 ≤ w * (P.χ * d ^ 2) := by positivity
    have : 0 < (1 - w) * (P.χ * dF ^ 2) := by positivity
    nlinarith

/-- O&R p. 656: the planner's first-order conditions are necessary and sufficient for a
state-by-state optimum (for `0 < w < 1`). -/
theorem planner_state_iff (P : CoordParams) {w : ℝ} (hw0 : 0 < w) (hw1 : w < 1)
    (Em EmF M MF e eF : ℝ) :
    (∀ x xF, welfare P w Em EmF M MF e eF ≤ welfare P w Em EmF x xF e eF) ↔
      plannerFOC1 P w Em EmF M MF e eF = 0 ∧ plannerFOC2 P w Em EmF M MF e eF = 0 := by
  constructor
  · intro h
    by_contra hF
    set F1 := plannerFOC1 P w Em EmF M MF e eF
    set F2 := plannerFOC2 P w Em EmF M MF e eF
    have hne : F1 ≠ 0 ∨ F2 ≠ 0 := by
      by_contra h'
      push Not at h'
      exact hF h'
    have hq := plannerQ_pos P hw0 hw1 hne
    have hS : 0 < F1 ^ 2 + F2 ^ 2 := by
      rcases hne with h' | h'
      · have := pow_pos (abs_pos.mpr h') 2
        rw [sq_abs] at this
        nlinarith [sq_nonneg F2]
      · have := pow_pos (abs_pos.mpr h') 2
        rw [sq_abs] at this
        nlinarith [sq_nonneg F1]
    set τ := (F1 ^ 2 + F2 ^ 2) / plannerQ P w F1 F2
    have h1 := welfare_sub P w Em EmF M MF e eF (M - τ * F1) (MF - τ * F2)
    have h2 := h (M - τ * F1) (MF - τ * F2)
    have hQτ : plannerQ P w (M - τ * F1 - M) (MF - τ * F2 - MF) =
        τ ^ 2 * plannerQ P w F1 F2 := by
      unfold plannerQ
      ring
    rw [hQτ] at h1
    have h3 : 2 * ((M - τ * F1 - M) * F1 + (MF - τ * F2 - MF) * F2) +
        τ ^ 2 * plannerQ P w F1 F2 = -((F1 ^ 2 + F2 ^ 2) ^ 2 / plannerQ P w F1 F2) := by
      simp only [τ]
      field_simp
      ring
    have h4 : 0 < (F1 ^ 2 + F2 ^ 2) ^ 2 / plannerQ P w F1 F2 := by positivity
    linarith
  · rintro ⟨h1, h2⟩ x xF
    have h := welfare_sub P w Em EmF M MF e eF x xF
    rw [h1, h2] at h
    have hq : 0 ≤ plannerQ P w (x - M) (xF - MF) := by
      by_cases hd : x - M ≠ 0 ∨ xF - MF ≠ 0
      · exact (plannerQ_pos P hw0 hw1 hd).le
      · push Not at hd
        rw [hd.1, hd.2]
        unfold plannerQ
        simp
    linarith

/-- O&R p. 656: the planner's solution is exactly a profile satisfying both first-order
conditions in every state. -/
theorem planner_iff_foc (P : CoordParams) (Sh : CoordShocks S) {w : ℝ} (hw0 : 0 < w)
    (hw1 : w < 1) (M MF : S → ℝ) :
    IsPlanner P Sh w M MF ↔ ∀ s,
      plannerFOC1 P w (expect Sh M) (expect Sh MF) (M s) (MF s) (Sh.eps s) (Sh.epsF s) = 0 ∧
      plannerFOC2 P w (expect Sh M) (expect Sh MF) (M s) (MF s) (Sh.eps s) (Sh.epsF s) = 0 := by
  unfold IsPlanner
  exact forall_congr' fun s => planner_state_iff P hw0 hw1 _ _ _ _ _ _

/-- O&R fn 42: in the planner's solution expected money growth is zero in both countries. -/
theorem planner_expect_zero {P : CoordParams} {Sh : CoordShocks S} {w : ℝ} (hw0 : 0 < w)
    (hw1 : w < 1) {M MF : S → ℝ} (hP : IsPlanner P Sh w M MF) :
    expect Sh M = 0 ∧ expect Sh MF = 0 := by
  rw [planner_iff_foc P Sh hw0 hw1] at hP
  have hχ := P.χ_pos
  set Em := expect Sh M
  set EmF := expect Sh MF
  have h1 : ∑ s, Sh.prob s * ((w * (P.a1 ^ 2 + P.χ) + (1 - w) * P.a2 ^ 2) * M s +
      (P.a1 * P.a2) * MF s + (w * P.a1) * Sh.eps s + ((1 - w) * P.a2) * Sh.epsF s +
        (-(w * P.a1 * (P.a1 * Em + P.a2 * EmF) + (1 - w) * P.a2 * (P.a1 * EmF + P.a2 * Em)))) =
      0 := by
    refine Finset.sum_eq_zero fun s _ => ?_
    have := (hP s).1
    unfold plannerFOC1 homeGap foreignGap at this
    rw [show (w * (P.a1 ^ 2 + P.χ) + (1 - w) * P.a2 ^ 2) * M s + (P.a1 * P.a2) * MF s +
      (w * P.a1) * Sh.eps s + ((1 - w) * P.a2) * Sh.epsF s +
      (-(w * P.a1 * (P.a1 * Em + P.a2 * EmF) + (1 - w) * P.a2 * (P.a1 * EmF + P.a2 * Em))) = 0
      by linear_combination this, mul_zero]
  have h2 : ∑ s, Sh.prob s * ((P.a1 * P.a2) * M s +
      (w * P.a2 ^ 2 + (1 - w) * (P.a1 ^ 2 + P.χ)) * MF s + (w * P.a2) * Sh.eps s +
        ((1 - w) * P.a1) * Sh.epsF s +
        (-(w * P.a2 * (P.a1 * Em + P.a2 * EmF) + (1 - w) * P.a1 * (P.a1 * EmF + P.a2 * Em)))) =
      0 := by
    refine Finset.sum_eq_zero fun s _ => ?_
    have := (hP s).2
    unfold plannerFOC2 homeGap foreignGap at this
    rw [show (P.a1 * P.a2) * M s + (w * P.a2 ^ 2 + (1 - w) * (P.a1 ^ 2 + P.χ)) * MF s +
      (w * P.a2) * Sh.eps s + ((1 - w) * P.a1) * Sh.epsF s +
      (-(w * P.a2 * (P.a1 * Em + P.a2 * EmF) + (1 - w) * P.a1 * (P.a1 * EmF + P.a2 * Em))) = 0
      by linear_combination this, mul_zero]
  rw [expect_affine] at h1 h2
  have he : expect Sh Sh.eps = 0 := Sh.eps_mean
  have heF : expect Sh Sh.epsF = 0 := Sh.epsF_mean
  rw [he, heF] at h1 h2
  have h1w : 0 < 1 - w := by linarith
  constructor
  · have : (w * P.χ) * Em = 0 := by linear_combination h1
    exact (mul_eq_zero.mp this).resolve_left (by positivity)
  · have : ((1 - w) * P.χ) * EmF = 0 := by linear_combination h2
    exact (mul_eq_zero.mp this).resolve_left (by positivity)

/-- O&R fn 42: the planner's (1,1) coefficient `w (a₁² + χ) + (1 − w) a₂²`. -/
def pH11 (P : CoordParams) (w : ℝ) : ℝ := w * (P.a1 ^ 2 + P.χ) + (1 - w) * P.a2 ^ 2

/-- O&R fn 42: the planner's (2,2) coefficient `w a₂² + (1 − w)(a₁² + χ)`. -/
def pH22 (P : CoordParams) (w : ℝ) : ℝ := w * P.a2 ^ 2 + (1 - w) * (P.a1 ^ 2 + P.χ)

/-- O&R fn 42: the planner's determinant. -/
def plannerDet (P : CoordParams) (w : ℝ) : ℝ := pH11 P w * pH22 P w - (P.a1 * P.a2) ^ 2

/-- O&R fn 42: the planner's determinant is positive for `0 < w < 1` (strict convexity):
it equals `w(1−w)(a₁² − a₂²)² + (1−w)χ(w a₁² + (1−w)a₂²) + wχ(w a₂² + (1−w)a₁²) +
w(1−w)χ²`. -/
theorem plannerDet_pos (P : CoordParams) {w : ℝ} (hw0 : 0 < w) (hw1 : w < 1) :
    0 < plannerDet P w := by
  have hχ := P.χ_pos
  have h1w : 0 < 1 - w := by linarith
  have hid : plannerDet P w = w * (1 - w) * (P.a1 ^ 2 - P.a2 ^ 2) ^ 2 +
      (1 - w) * P.χ * (w * P.a1 ^ 2 + (1 - w) * P.a2 ^ 2) +
      w * P.χ * (w * P.a2 ^ 2 + (1 - w) * P.a1 ^ 2) + w * (1 - w) * P.χ ^ 2 := by
    unfold plannerDet pH11 pH22
    ring
  rw [hid]
  positivity

/-- O&R fn 42: Home's planner money growth `−(H₂₂ r₁ − a₁a₂ r₂)/det` with
`r₁ = w a₁ ε + (1−w) a₂ ε*`, `r₂ = w a₂ ε + (1−w) a₁ ε*`. -/
noncomputable def plannerM (P : CoordParams) (Sh : CoordShocks S) (w : ℝ) (s : S) : ℝ :=
  -(pH22 P w * (w * P.a1 * Sh.eps s + (1 - w) * P.a2 * Sh.epsF s) -
    P.a1 * P.a2 * (w * P.a2 * Sh.eps s + (1 - w) * P.a1 * Sh.epsF s)) / plannerDet P w

/-- O&R fn 42: Foreign's planner money growth `−(H₁₁ r₂ − a₁a₂ r₁)/det`. -/
noncomputable def plannerMF (P : CoordParams) (Sh : CoordShocks S) (w : ℝ) (s : S) : ℝ :=
  -(pH11 P w * (w * P.a2 * Sh.eps s + (1 - w) * P.a1 * Sh.epsF s) -
    P.a1 * P.a2 * (w * P.a1 * Sh.eps s + (1 - w) * P.a2 * Sh.epsF s)) / plannerDet P w

/-- O&R fn 42: the planner's closed form has zero mean. -/
theorem expect_plannerM (P : CoordParams) (Sh : CoordShocks S) (w : ℝ) :
    expect Sh (plannerM P Sh w) = 0 ∧ expect Sh (plannerMF P Sh w) = 0 := by
  have he : expect Sh Sh.eps = 0 := Sh.eps_mean
  have heF : expect Sh Sh.epsF = 0 := Sh.epsF_mean
  constructor
  · have hs : ∀ s, Sh.prob s * plannerM P Sh w s = Sh.prob s *
        ((-(pH22 P w * (w * P.a1) - P.a1 * P.a2 * (w * P.a2)) / plannerDet P w) * Sh.eps s +
          (-(pH22 P w * ((1 - w) * P.a2) - P.a1 * P.a2 * ((1 - w) * P.a1)) / plannerDet P w) *
            Sh.epsF s + 0 * Sh.eps s + 0 * Sh.eps s + 0) := fun s => by
      unfold plannerM
      ring
    unfold expect
    rw [Finset.sum_congr rfl fun s _ => hs s, expect_affine, he, heF]
    ring
  · have hs : ∀ s, Sh.prob s * plannerMF P Sh w s = Sh.prob s *
        ((-(pH11 P w * (w * P.a2) - P.a1 * P.a2 * (w * P.a1)) / plannerDet P w) * Sh.eps s +
          (-(pH11 P w * ((1 - w) * P.a1) - P.a1 * P.a2 * ((1 - w) * P.a2)) / plannerDet P w) *
            Sh.epsF s + 0 * Sh.eps s + 0 * Sh.eps s + 0) := fun s => by
      unfold plannerMF
      ring
    unfold expect
    rw [Finset.sum_congr rfl fun s _ => hs s, expect_affine, he, heF]
    ring

/-- O&R fn 42, the planner's solution exists, is unique and has the closed form
`(plannerM, plannerMF)` (for `0 < w < 1`). -/
theorem planner_iff_closed_form {P : CoordParams} {Sh : CoordShocks S} {w : ℝ} (hw0 : 0 < w)
    (hw1 : w < 1) (M MF : S → ℝ) :
    IsPlanner P Sh w M MF ↔ ∀ s, M s = plannerM P Sh w s ∧ MF s = plannerMF P Sh w s := by
  have hdet := (plannerDet_pos P hw0 hw1).ne'
  have hD' : plannerDet P w = (w * (P.a1 ^ 2 + P.χ) + (1 - w) * P.a2 ^ 2) *
      (w * P.a2 ^ 2 + (1 - w) * (P.a1 ^ 2 + P.χ)) - (P.a1 * P.a2) ^ 2 := rfl
  constructor
  · intro hP s
    obtain ⟨h0, h0F⟩ := planner_expect_zero hw0 hw1 hP
    rw [planner_iff_foc P Sh hw0 hw1] at hP
    have h1 := (hP s).1
    have h2 := (hP s).2
    rw [h0, h0F] at h1 h2
    simp only [plannerFOC1, plannerFOC2, homeGap, foreignGap] at h1 h2
    unfold plannerM plannerMF pH11 pH22
    constructor
    · rw [eq_div_iff hdet, hD']
      linear_combination (w * P.a2 ^ 2 + (1 - w) * (P.a1 ^ 2 + P.χ)) * h1 -
        P.a1 * P.a2 * h2
    · rw [eq_div_iff hdet, hD']
      linear_combination (w * (P.a1 ^ 2 + P.χ) + (1 - w) * P.a2 ^ 2) * h2 -
        P.a1 * P.a2 * h1
  · intro hs
    have hM : M = plannerM P Sh w := funext fun s => (hs s).1
    have hMF : MF = plannerMF P Sh w := funext fun s => (hs s).2
    subst hM hMF
    rw [planner_iff_foc P Sh hw0 hw1]
    intro s
    rw [(expect_plannerM P Sh w).1, (expect_plannerM P Sh w).2]
    have k1 : plannerM P Sh w s * plannerDet P w =
        -((w * P.a2 ^ 2 + (1 - w) * (P.a1 ^ 2 + P.χ)) *
          (w * P.a1 * Sh.eps s + (1 - w) * P.a2 * Sh.epsF s) -
          P.a1 * P.a2 * (w * P.a2 * Sh.eps s + (1 - w) * P.a1 * Sh.epsF s)) := by
      unfold plannerM
      exact div_mul_cancel₀ _ hdet
    have k2 : plannerMF P Sh w s * plannerDet P w =
        -((w * (P.a1 ^ 2 + P.χ) + (1 - w) * P.a2 ^ 2) *
          (w * P.a2 * Sh.eps s + (1 - w) * P.a1 * Sh.epsF s) -
          P.a1 * P.a2 * (w * P.a1 * Sh.eps s + (1 - w) * P.a2 * Sh.epsF s)) := by
      unfold plannerMF
      exact div_mul_cancel₀ _ hdet
    constructor
    · have : plannerFOC1 P w 0 0 (plannerM P Sh w s) (plannerMF P Sh w s) (Sh.eps s)
          (Sh.epsF s) * plannerDet P w = 0 := by
        unfold plannerFOC1 homeGap foreignGap
        linear_combination (w * (P.a1 ^ 2 + P.χ) + (1 - w) * P.a2 ^ 2) * k1 +
          (P.a1 * P.a2) * k2 + (w * P.a1 * Sh.eps s + (1 - w) * P.a2 * Sh.epsF s) * hD'
      exact (mul_eq_zero.mp this).resolve_right hdet
    · have : plannerFOC2 P w 0 0 (plannerM P Sh w s) (plannerMF P Sh w s) (Sh.eps s)
          (Sh.epsF s) * plannerDet P w = 0 := by
        unfold plannerFOC2 homeGap foreignGap
        linear_combination (P.a1 * P.a2) * k1 +
          (w * P.a2 ^ 2 + (1 - w) * (P.a1 ^ 2 + P.χ)) * k2 +
          (w * P.a2 * Sh.eps s + (1 - w) * P.a1 * Sh.epsF s) * hD'
      exact (mul_eq_zero.mp this).resolve_right hdet

/-- O&R fn 42: the closed form is the planner's solution (existence). -/
theorem planner_exists (P : CoordParams) (Sh : CoordShocks S) {w : ℝ} (hw0 : 0 < w)
    (hw1 : w < 1) : IsPlanner P Sh w (plannerM P Sh w) (plannerMF P Sh w) :=
  (planner_iff_closed_form hw0 hw1 _ _).mpr fun _ => ⟨rfl, rfl⟩

/-- O&R p. 656: the planner's and Nash's first-order conditions differ exactly by the
spillover terms `(1 − w) a₂ (y* − ȳ)` and `w a₂ (y − ȳ)`, so they coincide when `a₂ = 0`. -/
theorem plannerFOC_eq_nashFOC (P : CoordParams) (w Em EmF M MF e eF : ℝ) :
    plannerFOC1 P w Em EmF M MF e eF = w * (P.a1 * homeGap P Em EmF M MF e + P.χ * M) +
        (1 - w) * P.a2 * foreignGap P Em EmF M MF eF ∧
      plannerFOC2 P w Em EmF M MF e eF =
        (1 - w) * (P.a1 * foreignGap P Em EmF M MF eF + P.χ * MF) +
          w * P.a2 * homeGap P Em EmF M MF e := by
  unfold plannerFOC1 plannerFOC2
  constructor <;> ring

/-! ### Symmetric shocks: the response coefficients -/

/-- O&R p. 656: the Nash response coefficient with symmetric shocks, `a₁/(a₁² + a₁a₂ + χ)`. -/
noncomputable def nashCoef (P : CoordParams) : ℝ := P.a1 / (P.a1 ^ 2 + P.a1 * P.a2 + P.χ)

/-- O&R p. 656: the planner's response coefficient with symmetric shocks and `w = 1/2`,
`(a₁ + a₂)/((a₁ + a₂)² + χ)`. -/
noncomputable def plannerCoef (P : CoordParams) : ℝ :=
  (P.a1 + P.a2) / ((P.a1 + P.a2) ^ 2 + P.χ)

/-- O&R p. 656: with symmetric shocks `ε* = ε`, the symmetric profile
`Δm = Δm* = −a₁ ε/(a₁² + a₁a₂ + χ)` is a Nash equilibrium. -/
theorem nash_symmetric {P : CoordParams} {Sh : CoordShocks S}
    (hsym : ∀ s, Sh.epsF s = Sh.eps s) (hd : P.a1 ^ 2 + P.a1 * P.a2 + P.χ ≠ 0) :
    IsNash P Sh (fun s => -(nashCoef P * Sh.eps s)) (fun s => -(nashCoef P * Sh.eps s)) := by
  have he : expect Sh (fun s => -(nashCoef P * Sh.eps s)) = 0 := by
    have hs : ∀ s, Sh.prob s * -(nashCoef P * Sh.eps s) = Sh.prob s *
        (-nashCoef P * Sh.eps s + 0 * Sh.eps s + 0 * Sh.eps s + 0 * Sh.eps s + 0) :=
      fun s => by ring
    unfold expect
    rw [Finset.sum_congr rfl fun s _ => hs s, expect_affine]
    have h0 : expect Sh Sh.eps = 0 := Sh.eps_mean
    rw [h0]
    ring
  rw [nash_iff_system]
  refine ⟨he, he, fun s => ?_⟩
  have hx : nashCoef P * (P.a1 ^ 2 + P.a1 * P.a2 + P.χ) = P.a1 := by
    unfold nashCoef
    exact div_mul_cancel₀ _ hd
  rw [hsym s]
  constructor
  · linear_combination (-Sh.eps s) * hx
  · linear_combination (-Sh.eps s) * hx

/-- O&R p. 656: with symmetric shocks and equal weights the planner sets
`Δm = Δm* = −(a₁ + a₂) ε/((a₁ + a₂)² + χ)`. -/
theorem planner_symmetric {P : CoordParams} {Sh : CoordShocks S}
    (hsym : ∀ s, Sh.epsF s = Sh.eps s) :
    IsPlanner P Sh (1 / 2) (fun s => -(plannerCoef P * Sh.eps s))
      (fun s => -(plannerCoef P * Sh.eps s)) := by
  have hχ := P.χ_pos
  have hD : 0 < (P.a1 + P.a2) ^ 2 + P.χ := by positivity
  have he : expect Sh (fun s => -(plannerCoef P * Sh.eps s)) = 0 := by
    have hs : ∀ s, Sh.prob s * -(plannerCoef P * Sh.eps s) = Sh.prob s *
        (-plannerCoef P * Sh.eps s + 0 * Sh.eps s + 0 * Sh.eps s + 0 * Sh.eps s + 0) :=
      fun s => by ring
    unfold expect
    rw [Finset.sum_congr rfl fun s _ => hs s, expect_affine]
    have h0 : expect Sh Sh.eps = 0 := Sh.eps_mean
    rw [h0]
    ring
  rw [planner_iff_foc P Sh (by norm_num) (by norm_num)]
  intro s
  rw [he]
  unfold plannerFOC1 plannerFOC2 homeGap foreignGap plannerCoef
  rw [hsym s]
  constructor
  · field_simp
    ring
  · field_simp
    ring

/-- O&R p. 656: the planner's minus Nash's response coefficient is exactly
`χ a₂/(((a₁ + a₂)² + χ)(a₁² + a₁a₂ + χ))`. -/
theorem plannerCoef_sub_nashCoef (P : CoordParams) (hd : P.a1 ^ 2 + P.a1 * P.a2 + P.χ ≠ 0) :
    plannerCoef P - nashCoef P =
      P.χ * P.a2 / (((P.a1 + P.a2) ^ 2 + P.χ) * (P.a1 ^ 2 + P.a1 * P.a2 + P.χ)) := by
  have hχ := P.χ_pos
  have hD : (P.a1 + P.a2) ^ 2 + P.χ ≠ 0 := by positivity
  unfold plannerCoef nashCoef
  rw [div_sub_div _ _ hD hd]
  congr 1
  ring

/-- O&R p. 656 ("higher or lower levels of monetary expansion"): with `a₁ > 0`,
`a₁ + a₂ > 0`, the planner's response coefficient exceeds Nash's iff `a₂ > 0`, equals it
iff `a₂ = 0`, and is smaller iff `a₂ < 0`. -/
theorem planner_response_compare (P : CoordParams) (ha1 : 0 < P.a1) (ha12 : 0 < P.a1 + P.a2) :
    (nashCoef P < plannerCoef P ↔ 0 < P.a2) ∧ (nashCoef P = plannerCoef P ↔ P.a2 = 0) ∧
      (plannerCoef P < nashCoef P ↔ P.a2 < 0) := by
  have hχ := P.χ_pos
  have hd : 0 < P.a1 ^ 2 + P.a1 * P.a2 + P.χ := by nlinarith
  have hD : 0 < (P.a1 + P.a2) ^ 2 + P.χ := by positivity
  have hdiff := plannerCoef_sub_nashCoef P hd.ne'
  have hpos : 0 < ((P.a1 + P.a2) ^ 2 + P.χ) * (P.a1 ^ 2 + P.a1 * P.a2 + P.χ) := by positivity
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · intro h
      have h1 : 0 < P.χ * P.a2 / (((P.a1 + P.a2) ^ 2 + P.χ) * (P.a1 ^ 2 + P.a1 * P.a2 + P.χ)) := by
        linarith
      have h2 := (div_pos_iff_of_pos_right hpos).mp h1
      exact pos_of_mul_pos_right h2 hχ.le
    · intro h
      have : 0 < P.χ * P.a2 / (((P.a1 + P.a2) ^ 2 + P.χ) * (P.a1 ^ 2 + P.a1 * P.a2 + P.χ)) := by
        positivity
      linarith
  · constructor
    · intro h
      have h1 : P.χ * P.a2 / (((P.a1 + P.a2) ^ 2 + P.χ) * (P.a1 ^ 2 + P.a1 * P.a2 + P.χ)) = 0 := by
        linarith
      rcases div_eq_zero_iff.mp h1 with h2 | h2
      · exact (mul_eq_zero.mp h2).resolve_left hχ.ne'
      · exact absurd h2 hpos.ne'
    · intro h
      rw [h, mul_zero, zero_div] at hdiff
      linarith
  · constructor
    · intro h
      have h1 : P.χ * P.a2 / (((P.a1 + P.a2) ^ 2 + P.χ) * (P.a1 ^ 2 + P.a1 * P.a2 + P.χ)) < 0 := by
        linarith
      have h2 := (div_neg_iff.mp h1)
      rcases h2 with ⟨_, h3⟩ | ⟨h3, _⟩
      · exact absurd h3 (not_lt.mpr hpos.le)
      · by_contra h4
        push Not at h4
        have := mul_nonneg hχ.le h4
        linarith
    · intro h
      have : P.χ * P.a2 / (((P.a1 + P.a2) ^ 2 + P.χ) * (P.a1 ^ 2 + P.a1 * P.a2 + P.χ)) < 0 :=
        div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hχ h) hpos
      linarith

/-! ### Welfare: the planner beats Nash -/

/-- O&R p. 656: the planner's expected objective `E[w L + (1 − w) L*]` of a profile. -/
def expWelfare (P : CoordParams) (Sh : CoordShocks S) (w : ℝ) (M MF : S → ℝ) : ℝ :=
  ∑ s, Sh.prob s *
    welfare P w (expect Sh M) (expect Sh MF) (M s) (MF s) (Sh.eps s) (Sh.epsF s)

/-- O&R p. 656: the planner's expected weighted loss never exceeds that of any Nash
equilibrium. -/
theorem planner_le_nash {P : CoordParams} {Sh : CoordShocks S} {w : ℝ} (hw0 : 0 < w)
    (hw1 : w < 1) {Mp MFp Mn MFn : S → ℝ} (hP : IsPlanner P Sh w Mp MFp)
    (hN : IsNash P Sh Mn MFn) : expWelfare P Sh w Mp MFp ≤ expWelfare P Sh w Mn MFn := by
  obtain ⟨hp0, hpF0⟩ := planner_expect_zero hw0 hw1 hP
  obtain ⟨hn0, hnF0⟩ := nash_expect_zero hN
  unfold expWelfare
  rw [hp0, hpF0, hn0, hnF0]
  refine Finset.sum_le_sum fun s _ => mul_le_mul_of_nonneg_left ?_ (Sh.prob_nonneg s)
  have := hP s (Mn s) (MFn s)
  rw [hp0, hpF0] at this
  exact this

/-- O&R p. 656: the gain from coordination is strict when there are spillovers (`a₂ ≠ 0`)
and some state of positive probability has a nonzero shock. -/
theorem planner_lt_nash {P : CoordParams} {Sh : CoordShocks S} {w : ℝ} (hw0 : 0 < w)
    (hw1 : w < 1) (ha2 : P.a2 ≠ 0) {Mp MFp Mn MFn : S → ℝ} (hP : IsPlanner P Sh w Mp MFp)
    (hN : IsNash P Sh Mn MFn) (s0 : S) (hp : 0 < Sh.prob s0)
    (hshock : Sh.eps s0 ≠ 0 ∨ Sh.epsF s0 ≠ 0) :
    expWelfare P Sh w Mp MFp < expWelfare P Sh w Mn MFn := by
  obtain ⟨hp0, hpF0⟩ := planner_expect_zero hw0 hw1 hP
  obtain ⟨hn0, hnF0⟩ := nash_expect_zero hN
  have hχ := P.χ_pos
  have h1w : 0 < 1 - w := by linarith
  have hle : ∀ s, welfare P w 0 0 (Mp s) (MFp s) (Sh.eps s) (Sh.epsF s) ≤
      welfare P w 0 0 (Mn s) (MFn s) (Sh.eps s) (Sh.epsF s) := by
    intro s
    have := hP s (Mn s) (MFn s)
    rw [hp0, hpF0] at this
    exact this
  have hlt : welfare P w 0 0 (Mp s0) (MFp s0) (Sh.eps s0) (Sh.epsF s0) <
      welfare P w 0 0 (Mn s0) (MFn s0) (Sh.eps s0) (Sh.epsF s0) := by
    refine lt_of_le_of_ne (hle s0) fun heq => ?_
    have hmin : ∀ x xF, welfare P w 0 0 (Mn s0) (MFn s0) (Sh.eps s0) (Sh.epsF s0) ≤
        welfare P w 0 0 x xF (Sh.eps s0) (Sh.epsF s0) := by
      intro x xF
      have := hP s0 x xF
      rw [hp0, hpF0] at this
      linarith
    obtain ⟨hF1, hF2⟩ := (planner_state_iff P hw0 hw1 _ _ _ _ _ _).mp hmin
    have hn := (nash_iff_foc P Sh Mn MFn).mp hN s0
    rw [hn0, hnF0] at hn
    simp only [plannerFOC1, plannerFOC2] at hF1 hF2
    obtain ⟨hn1, hn2⟩ := hn
    set Y := homeGap P 0 0 (Mn s0) (MFn s0) (Sh.eps s0)
    set YF := foreignGap P 0 0 (Mn s0) (MFn s0) (Sh.epsF s0)
    have hYF : YF = 0 := by
      have : ((1 - w) * P.a2) * YF = 0 := by linear_combination hF1 - w * hn1
      exact (mul_eq_zero.mp this).resolve_left (mul_ne_zero h1w.ne' ha2)
    have hY : Y = 0 := by
      have : (w * P.a2) * Y = 0 := by linear_combination hF2 - (1 - w) * hn2
      exact (mul_eq_zero.mp this).resolve_left (mul_ne_zero hw0.ne' ha2)
    have hM : Mn s0 = 0 := by
      have : P.χ * Mn s0 = 0 := by linear_combination hn1 - P.a1 * hY
      exact (mul_eq_zero.mp this).resolve_left hχ.ne'
    have hMF : MFn s0 = 0 := by
      have : P.χ * MFn s0 = 0 := by linear_combination hn2 - P.a1 * hYF
      exact (mul_eq_zero.mp this).resolve_left hχ.ne'
    have he : Sh.eps s0 = 0 := by
      have := hY
      simp only [Y, homeGap, hM, hMF] at this
      linarith
    have heF : Sh.epsF s0 = 0 := by
      have := hYF
      simp only [YF, foreignGap, hM, hMF] at this
      linarith
    rcases hshock with h | h
    · exact h he
    · exact h heF
  unfold expWelfare
  rw [hp0, hpF0, hn0, hnF0]
  exact Finset.sum_lt_sum (fun s _ => mul_le_mul_of_nonneg_left (hle s) (Sh.prob_nonneg s))
    ⟨s0, Finset.mem_univ _, mul_lt_mul_of_pos_left hlt hp⟩

/-! ### No weight on money growth: two instruments, two targets -/

/-- O&R p. 655: with `χ = 0`, both outputs can be stabilised exactly for every pair of shocks
iff `a₁² ≠ a₂²` (the two instruments are linearly independent). -/
theorem two_instruments_iff (a1 a2 : ℝ) :
    (∀ e eF : ℝ, ∃ x xF : ℝ, a1 * x + a2 * xF + e = 0 ∧ a2 * x + a1 * xF + eF = 0) ↔
      a1 ^ 2 ≠ a2 ^ 2 := by
  constructor
  · intro h hsq
    have hfac : (a1 - a2) * (a1 + a2) = 0 := by linear_combination hsq
    rcases mul_eq_zero.mp hfac with h1 | h1
    · obtain ⟨x, xF, hx1, hx2⟩ := h 0 1
      have : a1 = a2 := by linarith
      subst this
      linarith
    · obtain ⟨x, xF, hx1, hx2⟩ := h 1 1
      have : a2 = -a1 := by linarith
      subst this
      linarith
  · intro hsq e eF
    have hd : a1 ^ 2 - a2 ^ 2 ≠ 0 := sub_ne_zero.mpr hsq
    refine ⟨(a2 * eF - a1 * e) / (a1 ^ 2 - a2 ^ 2), (a2 * e - a1 * eF) / (a1 ^ 2 - a2 ^ 2),
      ?_, ?_⟩
    · field_simp
      ring
    · field_simp
      ring

/-- O&R p. 655: with `χ = 0` a country's best response closes its own output gap exactly
(`a₁ ≠ 0`): `x₀` minimises `(a₁ x + c)²` iff `a₁ x₀ + c = 0`. Hence with `χ = 0` every Nash
equilibrium puts both outputs at `ȳ` with zero loss, which no planner can improve on. -/
theorem zero_chi_best_response_iff {a1 : ℝ} (ha1 : a1 ≠ 0) (c x0 : ℝ) :
    (∀ x, (a1 * x0 + c) ^ 2 ≤ (a1 * x + c) ^ 2) ↔ a1 * x0 + c = 0 := by
  constructor
  · intro h
    have h1 := h (-c / a1)
    rw [show a1 * (-c / a1) + c = 0 by field_simp; ring] at h1
    have h2 : (a1 * x0 + c) ^ 2 = 0 := le_antisymm (by simpa using h1) (sq_nonneg _)
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2
  · intro h x
    rw [h]
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow]
    exact sq_nonneg _

end ObstfeldRogoff.NominalRigidities.PolicyCoordination

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

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

set_option linter.style.longLine false
#print axioms ObstfeldRogoff.NominalRigidities.loss
#print axioms ObstfeldRogoff.NominalRigidities.loss_nonneg
#print axioms ObstfeldRogoff.NominalRigidities.loss_at_target
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschModel.DornbuschParams
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschModel.DornbuschParams.mk
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschModel.DornbuschParams.η
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschModel.DornbuschParams.φ
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschModel.DornbuschParams.δ
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschModel.DornbuschParams.ψ
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschModel.DornbuschParams.η_pos
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschModel.DornbuschParams.φ_pos
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschModel.DornbuschParams.δ_pos
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschModel.DornbuschParams.ψ_pos
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschModel.DornbuschParams.r
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschModel.DornbuschParams.ρ
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschModel.DornbuschParams.κ
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschModel.DornbuschParams.D
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschModel.DornbuschParams.one_add_η_pos
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschModel.DornbuschParams.ψδ_pos
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschModel.DornbuschParams.φδ_pos
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschModel.DornbuschParams.slope_denom_pos
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschModel.DornbuschParams.D_pos
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschModel.DornbuschParams.r_pos
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschModel.DornbuschParams.r_lt_one
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschModel.DornbuschParams.one_sub_r
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschModel.DornbuschParams.one_lt_growth
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschModel.DornbuschParams.r_pow_mul_growth_pow
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschModel.DornbuschParams.κ_mul
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschModel.DornbuschParams.one_sub_κ
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschModel.DornbuschParams.inv_one_sub_κ
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschModel.DornbuschParams.κ_lt_one
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschModel.DornbuschParams.one_sub_κ_ne
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschModel.DornbuschParams.abs_ρ_lt_one
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschModel.DornbuschParams.abs_rρ_lt_one
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschModel.DornbuschParams.one_sub_rρ
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschModel.DornbuschParams.tsum_r_pow
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschModel.DornbuschParams.tsum_rρ_pow
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschModel.ptilde
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschModel.Structural
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschModel.phillips_five_iff_six
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschModel.structural_real_dynamics
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschModel.structural_money_market
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschModel.Reduced
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschModel.structural_to_reduced
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschModel.reduced_to_structural
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschModel.money_market_iff_nine
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschModel.forward_form
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschModel.steady_state_iff
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschModel.steady_state_neutral
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschModel.steady_state_interest
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschModel.q_closed_form
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschModel.q_tendsto
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschModel.q_monotone_adjustment
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschModel.q_oscillates
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschModel.q_diverges
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschModel.eflex
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschModel.summable_shift
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschModel.eflex_succ
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschModel.eflex_const
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschModel.summable_const_money
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschModel.eflex_no_bubble
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschModel.dev
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschModel.dev_succ
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschModel.dev_closed_form
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschModel.e_closed_form
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschModel.saddle_slope_unique
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschModel.saddle_path_invariant
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschModel.reduced_unique_of_init
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschModel.solE
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschModel.solQ
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschModel.sol_reduced
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschModel.sol_init
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschModel.r_pow_e_tendsto
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschModel.NoBubble
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschModel.no_bubble_shift
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschModel.no_bubble_iff_sub_const
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschModel.no_bubble_iff_dev_zero
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschModel.eighteen
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschModel.tsum_r_pow_q
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschModel.forward_solution
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschModel.fifteen
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschModel.sixteen
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschModel.eflex_eq_qbar_add_pflex
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschModel.exists_unique_no_bubble
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschModel.const_money_closed_form
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschModel.explodes_of_dev_pos
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschModel.implodes_of_dev_neg
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschModel.converges_iff_on_saddle
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschModel.bounded_iff_on_saddle
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschModel.no_bubble_iff_on_saddle
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschModel.saddle_path_theorem
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschModel.delta_e_zero_iff
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschModel.delta_q_zero_iff
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschModel.delta_e_slope_facts
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschModel.saddle_shallower
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschModel.saddle_slope_sign
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschShocks.ShockEqm
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschShocks.solve_one_sub_κ
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschShocks.κ_mul_impact
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschShocks.one_sub_κ_mul_impact
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschShocks.shock_impact
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschShocks.shock_path
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschShocks.shock_exists_unique
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschShocks.perm_shock_impact
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschShocks.overshooting_iff
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschShocks.perm_shock_depreciates
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschShocks.perm_shock_path
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschShocks.perm_shock_price_path
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschShocks.perm_shock_output_pos
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschShocks.perm_shock_output_oscillates
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschShocks.perm_shock_interest
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschShocks.perm_shock_money_market
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschShocks.perm_shock_no_immediate_jump
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschShocks.perm_shock_long_run
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschShocks.perm_shock_exists_unique
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschShocks.real_shock
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschShocks.real_shock_exists_unique
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschShocks.flex_shock_equal
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschShocks.twenty
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschShocks.twenty_one
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschShocks.amplification_iff
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschShocks.variance_amplification
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschShocks.trend
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschShocks.summable_trend
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschShocks.eflex_trend
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschShocks.trend_steady_state
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschShocks.twenty_two
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschShocks.twenty_three
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschShocks.growth_shock_impact_interest
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschShocks.growth_shock_long_run_interest
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschShocks.growth_shock_overshoots
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschShocks.twenty_four
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschShocks.real_interest_pos_iff
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschShocks.phillips_variable_pstar
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschShocks.twenty_five
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschShocks.disinflation_impact
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschShocks.disinflation_literal_impact
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschShocks.disinflation_slump
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschShocks.disinflation_overshoots_down
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschShocks.disinflation_interest
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschShocks.disinflation_alt_impact
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschShocks.disinflation_no_slump_iff
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschShocks.disinflation_level_jump
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschExtensions.ReducedTV
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschExtensions.structural_to_reducedTV
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschExtensions.naive_seven_wrong
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschExtensions.reducedTV_iff
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschExtensions.qstep
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschExtensions.qstep_abs_le
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschExtensions.summable_step
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschExtensions.r_mul_one_add
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschExtensions.eflex_step_after
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschExtensions.eflex_step_before
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschExtensions.AnticipatedEqm
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschExtensions.anticipated_iff_shockEqm
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschExtensions.anticipated_x_path
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschExtensions.anticipated_impact
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschExtensions.anticipated_immediate
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschExtensions.anticipated_boom
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschExtensions.anticipated_price_before
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschExtensions.anticipated_price_after
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschExtensions.anticipated_price_signs
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschExtensions.anticipated_exists_unique
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschExtensions.ReducedMD
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschExtensions.reducedMD_iff
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschExtensions.accommodation_iff
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschExtensions.accommodation_insulates
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschExtensions.peg_requires_accommodation
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschExtensions.fixed_money_demand_shock
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschExtensions.peg_real_shock
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschExtensions.peg_real_appreciation_boom
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschExtensions.peg_real_depreciation_slump
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschExtensions.peg_real_shock_long_run
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschExtensions.peg_real_shock_exists
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschExtensions.float_vs_peg
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschExtensions.EventTree
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschExtensions.EventTree.mk
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschExtensions.EventTree.prob
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschExtensions.EventTree.prob_nonneg
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschExtensions.EventTree.prob_sum
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschExtensions.Stochastic.condE
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschExtensions.Stochastic.condE_of_eq
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschExtensions.Stochastic.condE_lin
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschExtensions.Stochastic.condE_abs_le
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschExtensions.Stochastic.ahead
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschExtensions.Stochastic.ahead_succ
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschExtensions.Stochastic.ahead_lin
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschExtensions.Stochastic.ahead_abs_le
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschExtensions.Stochastic.ahead_eigen
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschExtensions.Stochastic.StochStructural
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschExtensions.Stochastic.StochReduced
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschExtensions.Stochastic.stoch_structural_to_reduced
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschExtensions.Stochastic.stoch_reduced_to_structural
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschExtensions.Stochastic.condE_q
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschExtensions.Stochastic.seflex
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschExtensions.Stochastic.summable_ahead
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschExtensions.Stochastic.seflex_abs_le
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschExtensions.Stochastic.seflex_condE
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschExtensions.Stochastic.sdev
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschExtensions.Stochastic.sdev_condE
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschExtensions.Stochastic.sdev_eq_r_pow
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschExtensions.Stochastic.SNoBubble
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschExtensions.Stochastic.bounded_no_bubble
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschExtensions.Stochastic.sdev_zero_of_no_bubble
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschExtensions.Stochastic.q_news
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschExtensions.Stochastic.sq
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschExtensions.Stochastic.se
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschExtensions.Stochastic.sol_reduced
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschExtensions.Stochastic.sq_bounded
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschExtensions.Stochastic.se_bounded
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschExtensions.Stochastic.stoch_unique_of_sdev_zero
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschExtensions.Stochastic.stoch_exists_unique_no_bubble
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschExtensions.Stochastic.stoch_exists_unique_bounded
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschExtensions.Stochastic.stoch_saddle_form
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschExtensions.Stochastic.stoch_bubble_solutions
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschExtensions.Stochastic.stoch_conditional_variance
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschContinuousTime.linear_ode_unique
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschContinuousTime.exp_neg_tendsto
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschContinuousTime.exp_growth_tendsto
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschContinuousTime.CTStructural
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschContinuousTime.CTReduced
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschContinuousTime.ct_structural_to_reduced
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschContinuousTime.ct_reduced_to_structural
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschContinuousTime.ctDev
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschContinuousTime.ctDev_deriv
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschContinuousTime.ct_q_closed_form
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschContinuousTime.ct_dev_closed_form
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschContinuousTime.ct_e_closed_form
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschContinuousTime.ct_q_tendsto
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschContinuousTime.ct_q_monotone
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschContinuousTime.ctSolE
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschContinuousTime.ctSolQ
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschContinuousTime.ct_sol_reduced
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschContinuousTime.ct_unique_of_init
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschContinuousTime.ct_explodes
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschContinuousTime.ct_implodes
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschContinuousTime.ct_converges_iff
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschContinuousTime.ct_bounded_iff
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschContinuousTime.ct_discounted_e_tendsto
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschContinuousTime.ct_no_bubble_iff
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschContinuousTime.ct_saddle_path_theorem
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschContinuousTime.ct_saddle_slope_unique
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschContinuousTime.CTPermShock
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschContinuousTime.ct_perm_shock_impact
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschContinuousTime.ct_overshooting_iff
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschContinuousTime.ct_perm_shock_path
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschContinuousTime.ct_perm_shock_output_pos
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschContinuousTime.ct_perm_shock_interest
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschContinuousTime.ct_perm_shock_long_run
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschContinuousTime.ct_perm_shock_exists_unique
#print axioms ObstfeldRogoff.NominalRigidities.DornbuschContinuousTime.ct_real_shock
#print axioms ObstfeldRogoff.NominalRigidities.BarroGordon.expect
#print axioms ObstfeldRogoff.NominalRigidities.BarroGordon.expect_add
#print axioms ObstfeldRogoff.NominalRigidities.BarroGordon.expect_sub
#print axioms ObstfeldRogoff.NominalRigidities.BarroGordon.expect_const_mul
#print axioms ObstfeldRogoff.NominalRigidities.BarroGordon.expect_const
#print axioms ObstfeldRogoff.NominalRigidities.BarroGordon.expect_mono
#print axioms ObstfeldRogoff.NominalRigidities.BarroGordon.expect_nonneg
#print axioms ObstfeldRogoff.NominalRigidities.BarroGordon.expect_eq_zero_iff
#print axioms ObstfeldRogoff.NominalRigidities.BarroGordon.expect_congr_support
#print axioms ObstfeldRogoff.NominalRigidities.BarroGordon.bgLoss
#print axioms ObstfeldRogoff.NominalRigidities.BarroGordon.loss_derivation
#print axioms ObstfeldRogoff.NominalRigidities.BarroGordon.bestResponse
#print axioms ObstfeldRogoff.NominalRigidities.BarroGordon.bgLoss_eq_sq
#print axioms ObstfeldRogoff.NominalRigidities.BarroGordon.bgLoss_bestResponse
#print axioms ObstfeldRogoff.NominalRigidities.BarroGordon.bestResponse_isMin
#print axioms ObstfeldRogoff.NominalRigidities.BarroGordon.eq_bestResponse_of_le
#print axioms ObstfeldRogoff.NominalRigidities.BarroGordon.hasDerivAt_bgLoss
#print axioms ObstfeldRogoff.NominalRigidities.BarroGordon.hasDerivAt_marginal_bgLoss
#print axioms ObstfeldRogoff.NominalRigidities.BarroGordon.foc_iff
#print axioms ObstfeldRogoff.NominalRigidities.BarroGordon.isMin_iff_foc
#print axioms ObstfeldRogoff.NominalRigidities.BarroGordon.IsOneShotEqm
#print axioms ObstfeldRogoff.NominalRigidities.BarroGordon.oneShot_eqm_iff
#print axioms ObstfeldRogoff.NominalRigidities.BarroGordon.expInfl_strictMono_k
#print axioms ObstfeldRogoff.NominalRigidities.BarroGordon.expInfl_strictAntiOn_chi
#print axioms ObstfeldRogoff.NominalRigidities.BarroGordon.oneShot_surprise
#print axioms ObstfeldRogoff.NominalRigidities.BarroGordon.zero_not_bestResponse
#print axioms ObstfeldRogoff.NominalRigidities.BarroGordon.expLoss
#print axioms ObstfeldRogoff.NominalRigidities.BarroGordon.valueCommit
#print axioms ObstfeldRogoff.NominalRigidities.BarroGordon.valueDiscretion
#print axioms ObstfeldRogoff.NominalRigidities.BarroGordon.valueZero
#print axioms ObstfeldRogoff.NominalRigidities.BarroGordon.varZ
#print axioms ObstfeldRogoff.NominalRigidities.BarroGordon.expLoss_decomp
#print axioms ObstfeldRogoff.NominalRigidities.BarroGordon.sq_split
#print axioms ObstfeldRogoff.NominalRigidities.BarroGordon.expLoss_eq_commit_add
#print axioms ObstfeldRogoff.NominalRigidities.BarroGordon.commitRule
#print axioms ObstfeldRogoff.NominalRigidities.BarroGordon.expect_commitRule
#print axioms ObstfeldRogoff.NominalRigidities.BarroGordon.expLoss_commitRule
#print axioms ObstfeldRogoff.NominalRigidities.BarroGordon.commitRule_optimal
#print axioms ObstfeldRogoff.NominalRigidities.BarroGordon.commitRule_unique
#print axioms ObstfeldRogoff.NominalRigidities.BarroGordon.discretionRule
#print axioms ObstfeldRogoff.NominalRigidities.BarroGordon.expLoss_discretion
#print axioms ObstfeldRogoff.NominalRigidities.BarroGordon.expLoss_zero
#print axioms ObstfeldRogoff.NominalRigidities.BarroGordon.valueZero_sub_valueCommit
#print axioms ObstfeldRogoff.NominalRigidities.BarroGordon.valueDiscretion_sub_valueCommit
#print axioms ObstfeldRogoff.NominalRigidities.BarroGordon.valueCommit_lt_valueDiscretion
#print axioms ObstfeldRogoff.NominalRigidities.BarroGordon.valueZero_lt_valueDiscretion_iff
#print axioms ObstfeldRogoff.NominalRigidities.BarroGordon.commitRule_time_inconsistent
#print axioms ObstfeldRogoff.NominalRigidities.BarroGordon.liberalLoss
#print axioms ObstfeldRogoff.NominalRigidities.BarroGordon.liberalLoss_eq
#print axioms ObstfeldRogoff.NominalRigidities.BarroGordon.liberal_isMin_iff
#print axioms ObstfeldRogoff.NominalRigidities.BarroGordon.conservative_isMin_iff
#print axioms ObstfeldRogoff.NominalRigidities.BarroGordon.IsPartisanEqm
#print axioms ObstfeldRogoff.NominalRigidities.BarroGordon.partisan_eqm_iff
#print axioms ObstfeldRogoff.NominalRigidities.BarroGordon.partisan_half
#print axioms ObstfeldRogoff.NominalRigidities.BarroGordon.partisan_surprises
#print axioms ObstfeldRogoff.NominalRigidities.BarroGordon.partisan_known_winner
#print axioms ObstfeldRogoff.NominalRigidities.BarroGordon.partisan_surprise_signs
#print axioms ObstfeldRogoff.NominalRigidities.BarroGordon.secrecyLoss
#print axioms ObstfeldRogoff.NominalRigidities.BarroGordon.secrecyLoss_eq
#print axioms ObstfeldRogoff.NominalRigidities.BarroGordon.secrecy_isMin_iff
#print axioms ObstfeldRogoff.NominalRigidities.BarroGordon.IsSecrecyEqm
#print axioms ObstfeldRogoff.NominalRigidities.BarroGordon.secrecy_eqm_iff
#print axioms ObstfeldRogoff.NominalRigidities.BarroGordon.secrecy_eqm_loss
#print axioms ObstfeldRogoff.NominalRigidities.BarroGordon.secrecy_commit_loss
#print axioms ObstfeldRogoff.NominalRigidities.BarroGordon.secrecy_commit_optimal
#print axioms ObstfeldRogoff.NominalRigidities.BarroGordon.secrecy_commit_rule_mean
#print axioms ObstfeldRogoff.NominalRigidities.BarroGordon.secrecy_unconstrained_bound
#print axioms ObstfeldRogoff.NominalRigidities.BarroGordon.IsRevealEqm
#print axioms ObstfeldRogoff.NominalRigidities.BarroGordon.reveal_eqm_iff
#print axioms ObstfeldRogoff.NominalRigidities.BarroGordon.reveal_vs_secrecy
#print axioms ObstfeldRogoff.NominalRigidities.BarroGordon.lamTwo
#print axioms ObstfeldRogoff.NominalRigidities.BarroGordon.pHalf
#print axioms ObstfeldRogoff.NominalRigidities.BarroGordon.pHalf_sum
#print axioms ObstfeldRogoff.NominalRigidities.BarroGordon.secrecy_two_point
#print axioms ObstfeldRogoff.NominalRigidities.ReputationEquilibria.Hist
#print axioms ObstfeldRogoff.NominalRigidities.ReputationEquilibria.truncCost
#print axioms ObstfeldRogoff.NominalRigidities.ReputationEquilibria.bellman
#print axioms ObstfeldRogoff.NominalRigidities.ReputationEquilibria.truncCost_succ
#print axioms ObstfeldRogoff.NominalRigidities.ReputationEquilibria.bellman_eq_expect
#print axioms ObstfeldRogoff.NominalRigidities.ReputationEquilibria.HasExpPV
#print axioms ObstfeldRogoff.NominalRigidities.ReputationEquilibria.IsReputationEqm
#print axioms ObstfeldRogoff.NominalRigidities.ReputationEquilibria.truncCost_le_succ
#print axioms ObstfeldRogoff.NominalRigidities.ReputationEquilibria.truncCost_tendsto_or_atTop
#print axioms ObstfeldRogoff.NominalRigidities.ReputationEquilibria.truncCost_lower
#print axioms ObstfeldRogoff.NominalRigidities.ReputationEquilibria.truncCost_eval
#print axioms ObstfeldRogoff.NominalRigidities.ReputationEquilibria.tendsto_truncCost_of_bellman_eq
#print axioms ObstfeldRogoff.NominalRigidities.ReputationEquilibria.le_of_hasExpPV_of_bellman_le
#print axioms ObstfeldRogoff.NominalRigidities.ReputationEquilibria.isReputationEqm_of_bellman
#print axioms ObstfeldRogoff.NominalRigidities.ReputationEquilibria.not_isReputationEqm_of_better
#print axioms ObstfeldRogoff.NominalRigidities.ReputationEquilibria.rootDev
#print axioms ObstfeldRogoff.NominalRigidities.ReputationEquilibria.rootVal
#print axioms ObstfeldRogoff.NominalRigidities.ReputationEquilibria.hasExpPV_rootDev
#print axioms ObstfeldRogoff.NominalRigidities.ReputationEquilibria.minLoss
#print axioms ObstfeldRogoff.NominalRigidities.ReputationEquilibria.minLoss_le
#print axioms ObstfeldRogoff.NominalRigidities.ReputationEquilibria.onLoss
#print axioms ObstfeldRogoff.NominalRigidities.ReputationEquilibria.onLoss_sub_minLoss
#print axioms ObstfeldRogoff.NominalRigidities.ReputationEquilibria.valueOn
#print axioms ObstfeldRogoff.NominalRigidities.ReputationEquilibria.expect_onLoss
#print axioms ObstfeldRogoff.NominalRigidities.ReputationEquilibria.valueOn_discretion
#print axioms ObstfeldRogoff.NominalRigidities.ReputationEquilibria.valueDiscretion_sub_valueOn
#print axioms ObstfeldRogoff.NominalRigidities.ReputationEquilibria.onLoss_discretion
#print axioms ObstfeldRogoff.NominalRigidities.ReputationEquilibria.bestResponse_eq_onPath_iff
#print axioms ObstfeldRogoff.NominalRigidities.ReputationEquilibria.NoSurprise
#print axioms ObstfeldRogoff.NominalRigidities.ReputationEquilibria.noSurprise_nil
#print axioms ObstfeldRogoff.NominalRigidities.ReputationEquilibria.noSurprise_cons_iff
#print axioms ObstfeldRogoff.NominalRigidities.ReputationEquilibria.trigExp
#print axioms ObstfeldRogoff.NominalRigidities.ReputationEquilibria.trigCB
#print axioms ObstfeldRogoff.NominalRigidities.ReputationEquilibria.trigVal
#print axioms ObstfeldRogoff.NominalRigidities.ReputationEquilibria.TriggerCond
#print axioms ObstfeldRogoff.NominalRigidities.ReputationEquilibria.trigExp_pos
#print axioms ObstfeldRogoff.NominalRigidities.ReputationEquilibria.trigExp_neg
#print axioms ObstfeldRogoff.NominalRigidities.ReputationEquilibria.trigCB_pos
#print axioms ObstfeldRogoff.NominalRigidities.ReputationEquilibria.trigCB_neg
#print axioms ObstfeldRogoff.NominalRigidities.ReputationEquilibria.trigVal_pos
#print axioms ObstfeldRogoff.NominalRigidities.ReputationEquilibria.trigVal_neg
#print axioms ObstfeldRogoff.NominalRigidities.ReputationEquilibria.expect_const_add_shock
#print axioms ObstfeldRogoff.NominalRigidities.ReputationEquilibria.expect_congr'
#print axioms ObstfeldRogoff.NominalRigidities.ReputationEquilibria.trig_rational
#print axioms ObstfeldRogoff.NominalRigidities.ReputationEquilibria.div_one_sub_eq
#print axioms ObstfeldRogoff.NominalRigidities.ReputationEquilibria.trig_bellman_eq
#print axioms ObstfeldRogoff.NominalRigidities.ReputationEquilibria.beta_val_diff
#print axioms ObstfeldRogoff.NominalRigidities.ReputationEquilibria.trig_bellman_le
#print axioms ObstfeldRogoff.NominalRigidities.ReputationEquilibria.trigVal_abs_le
#print axioms ObstfeldRogoff.NominalRigidities.ReputationEquilibria.trig_rootDev_value
#print axioms ObstfeldRogoff.NominalRigidities.ReputationEquilibria.trigger_eqm_iff
#print axioms ObstfeldRogoff.NominalRigidities.ReputationEquilibria.lowerBound
#print axioms ObstfeldRogoff.NominalRigidities.ReputationEquilibria.between_iff
#print axioms ObstfeldRogoff.NominalRigidities.ReputationEquilibria.triggerCond_iff_bounds
#print axioms ObstfeldRogoff.NominalRigidities.ReputationEquilibria.trigger_eqm_iff_bounds
#print axioms ObstfeldRogoff.NominalRigidities.ReputationEquilibria.trigger_zero_iff
#print axioms ObstfeldRogoff.NominalRigidities.ReputationEquilibria.trigCB_zero_eq_commit
#print axioms ObstfeldRogoff.NominalRigidities.ReputationEquilibria.book_gain_cost
#print axioms ObstfeldRogoff.NominalRigidities.ReputationEquilibria.trigger_deterministic_iff
#print axioms ObstfeldRogoff.NominalRigidities.ReputationEquilibria.trigger_oneShot_eqm
#print axioms ObstfeldRogoff.NominalRigidities.ReputationEquilibria.lowerBound_lt
#print axioms ObstfeldRogoff.NominalRigidities.ReputationEquilibria.neg_lt_lowerBound
#print axioms ObstfeldRogoff.NominalRigidities.ReputationEquilibria.lowerBound_tendsto
#print axioms ObstfeldRogoff.NominalRigidities.ReputationEquilibria.negative_sustainable_iff
#print axioms ObstfeldRogoff.NominalRigidities.ReputationEquilibria.trigger_multiplicity
#print axioms ObstfeldRogoff.NominalRigidities.ReputationEquilibria.LastOK
#print axioms ObstfeldRogoff.NominalRigidities.ReputationEquilibria.exp1
#print axioms ObstfeldRogoff.NominalRigidities.ReputationEquilibria.cb1
#print axioms ObstfeldRogoff.NominalRigidities.ReputationEquilibria.val1
#print axioms ObstfeldRogoff.NominalRigidities.ReputationEquilibria.OnePeriodCond
#print axioms ObstfeldRogoff.NominalRigidities.ReputationEquilibria.lastOK_cons_iff
#print axioms ObstfeldRogoff.NominalRigidities.ReputationEquilibria.lastOK_nil
#print axioms ObstfeldRogoff.NominalRigidities.ReputationEquilibria.exp1_pos
#print axioms ObstfeldRogoff.NominalRigidities.ReputationEquilibria.exp1_neg
#print axioms ObstfeldRogoff.NominalRigidities.ReputationEquilibria.cb1_pos
#print axioms ObstfeldRogoff.NominalRigidities.ReputationEquilibria.cb1_neg
#print axioms ObstfeldRogoff.NominalRigidities.ReputationEquilibria.val1_pos
#print axioms ObstfeldRogoff.NominalRigidities.ReputationEquilibria.val1_neg
#print axioms ObstfeldRogoff.NominalRigidities.ReputationEquilibria.one_rational
#print axioms ObstfeldRogoff.NominalRigidities.ReputationEquilibria.one_bellman_eq
#print axioms ObstfeldRogoff.NominalRigidities.ReputationEquilibria.one_bellman_le
#print axioms ObstfeldRogoff.NominalRigidities.ReputationEquilibria.val1_abs_le
#print axioms ObstfeldRogoff.NominalRigidities.ReputationEquilibria.one_rootDev_value
#print axioms ObstfeldRogoff.NominalRigidities.ReputationEquilibria.onePeriod_eqm_iff
#print axioms ObstfeldRogoff.NominalRigidities.ReputationEquilibria.lowerBound1
#print axioms ObstfeldRogoff.NominalRigidities.ReputationEquilibria.onePeriod_eqm_iff_bounds
#print axioms ObstfeldRogoff.NominalRigidities.ReputationEquilibria.onePeriod_below_oneShot
#print axioms ObstfeldRogoff.NominalRigidities.ReputationEquilibria.IsFiniteEqm
#print axioms ObstfeldRogoff.NominalRigidities.ReputationEquilibria.staticVal
#print axioms ObstfeldRogoff.NominalRigidities.ReputationEquilibria.truncCost_static
#print axioms ObstfeldRogoff.NominalRigidities.ReputationEquilibria.truncCost_ge_static
#print axioms ObstfeldRogoff.NominalRigidities.ReputationEquilibria.finite_static_eqm
#print axioms ObstfeldRogoff.NominalRigidities.ReputationEquilibria.finite_eqm_unique
#print axioms ObstfeldRogoff.NominalRigidities.CentralBankDelegation.conservative_eqm_iff
#print axioms ObstfeldRogoff.NominalRigidities.CentralBankDelegation.socialLoss
#print axioms ObstfeldRogoff.NominalRigidities.CentralBankDelegation.expLoss_conservative
#print axioms ObstfeldRogoff.NominalRigidities.CentralBankDelegation.socialLoss_self
#print axioms ObstfeldRogoff.NominalRigidities.CentralBankDelegation.hasDerivAt_socialLoss
#print axioms ObstfeldRogoff.NominalRigidities.CentralBankDelegation.signFn
#print axioms ObstfeldRogoff.NominalRigidities.CentralBankDelegation.deriv_eq_signFn
#print axioms ObstfeldRogoff.NominalRigidities.CentralBankDelegation.deriv_at_chi
#print axioms ObstfeldRogoff.NominalRigidities.CentralBankDelegation.hFn
#print axioms ObstfeldRogoff.NominalRigidities.CentralBankDelegation.hFn_strictMonoOn
#print axioms ObstfeldRogoff.NominalRigidities.CentralBankDelegation.signFn_eq_hFn
#print axioms ObstfeldRogoff.NominalRigidities.CentralBankDelegation.hFn_continuousOn
#print axioms ObstfeldRogoff.NominalRigidities.CentralBankDelegation.exists_root
#print axioms ObstfeldRogoff.NominalRigidities.CentralBankDelegation.signFn_neg
#print axioms ObstfeldRogoff.NominalRigidities.CentralBankDelegation.signFn_pos
#print axioms ObstfeldRogoff.NominalRigidities.CentralBankDelegation.socialLoss_continuousOn
#print axioms ObstfeldRogoff.NominalRigidities.CentralBankDelegation.socialLoss_strictAntiOn
#print axioms ObstfeldRogoff.NominalRigidities.CentralBankDelegation.socialLoss_strictMonoOn
#print axioms ObstfeldRogoff.NominalRigidities.CentralBankDelegation.rogoff_optimal
#print axioms ObstfeldRogoff.NominalRigidities.CentralBankDelegation.rogoff_existsUnique
#print axioms ObstfeldRogoff.NominalRigidities.CentralBankDelegation.minimizer_char
#print axioms ObstfeldRogoff.NominalRigidities.CentralBankDelegation.rogoff_beats_discretion
#print axioms ObstfeldRogoff.NominalRigidities.CentralBankDelegation.socialLoss_tendsto_atTop
#print axioms ObstfeldRogoff.NominalRigidities.CentralBankDelegation.rogoff_beats_infinite
#print axioms ObstfeldRogoff.NominalRigidities.CentralBankDelegation.socialLoss_gt_commit
#print axioms ObstfeldRogoff.NominalRigidities.CentralBankDelegation.no_bias_optimum
#print axioms ObstfeldRogoff.NominalRigidities.CentralBankDelegation.no_shock_limit
#print axioms ObstfeldRogoff.NominalRigidities.CentralBankDelegation.optimum_mono_ratio
#print axioms ObstfeldRogoff.NominalRigidities.CentralBankDelegation.walshLoss
#print axioms ObstfeldRogoff.NominalRigidities.CentralBankDelegation.walshLoss_eq
#print axioms ObstfeldRogoff.NominalRigidities.CentralBankDelegation.walsh_eqm_iff
#print axioms ObstfeldRogoff.NominalRigidities.CentralBankDelegation.walsh_social_loss
#print axioms ObstfeldRogoff.NominalRigidities.CentralBankDelegation.walsh_optimal
#print axioms ObstfeldRogoff.NominalRigidities.CentralBankDelegation.walshLossLam
#print axioms ObstfeldRogoff.NominalRigidities.CentralBankDelegation.walshLossLam_eq
#print axioms ObstfeldRogoff.NominalRigidities.CentralBankDelegation.ex4_eqm_iff
#print axioms ObstfeldRogoff.NominalRigidities.CentralBankDelegation.ex4_social_loss
#print axioms ObstfeldRogoff.NominalRigidities.CentralBankDelegation.ex4_complete_square
#print axioms ObstfeldRogoff.NominalRigidities.CentralBankDelegation.ex4_optimal
#print axioms ObstfeldRogoff.NominalRigidities.CentralBankDelegation.cbi_slope_significant
#print axioms ObstfeldRogoff.NominalRigidities.EscapeClausePeg.realignCost
#print axioms ObstfeldRogoff.NominalRigidities.EscapeClausePeg.pegLoss
#print axioms ObstfeldRogoff.NominalRigidities.EscapeClausePeg.pegLoss_derivation
#print axioms ObstfeldRogoff.NominalRigidities.EscapeClausePeg.output_flex
#print axioms ObstfeldRogoff.NominalRigidities.EscapeClausePeg.fix_sub_flex
#print axioms ObstfeldRogoff.NominalRigidities.EscapeClausePeg.thr
#print axioms ObstfeldRogoff.NominalRigidities.EscapeClausePeg.thr_sq
#print axioms ObstfeldRogoff.NominalRigidities.EscapeClausePeg.thr_nonneg
#print axioms ObstfeldRogoff.NominalRigidities.EscapeClausePeg.govPolicy
#print axioms ObstfeldRogoff.NominalRigidities.EscapeClausePeg.devalue_iff
#print axioms ObstfeldRogoff.NominalRigidities.EscapeClausePeg.revalue_iff
#print axioms ObstfeldRogoff.NominalRigidities.EscapeClausePeg.devalue_criterion
#print axioms ObstfeldRogoff.NominalRigidities.EscapeClausePeg.bgLoss_expand
#print axioms ObstfeldRogoff.NominalRigidities.EscapeClausePeg.govPolicy_optimal
#print axioms ObstfeldRogoff.NominalRigidities.EscapeClausePeg.govPolicy_unique
#print axioms ObstfeldRogoff.NominalRigidities.EscapeClausePeg.govPolicy_monotone
#print axioms ObstfeldRogoff.NominalRigidities.EscapeClausePeg.expDep
#print axioms ObstfeldRogoff.NominalRigidities.EscapeClausePeg.zbarC
#print axioms ObstfeldRogoff.NominalRigidities.EscapeClausePeg.zundC
#print axioms ObstfeldRogoff.NominalRigidities.EscapeClausePeg.integral_congr_Ioo
#print axioms ObstfeldRogoff.NominalRigidities.EscapeClausePeg.integral_linear
#print axioms ObstfeldRogoff.NominalRigidities.EscapeClausePeg.integral_govPolicy
#print axioms ObstfeldRogoff.NominalRigidities.EscapeClausePeg.expDep_eq
#print axioms ObstfeldRogoff.NominalRigidities.EscapeClausePeg.expDep_continuous
#print axioms ObstfeldRogoff.NominalRigidities.EscapeClausePeg.expDep_regimeA
#print axioms ObstfeldRogoff.NominalRigidities.EscapeClausePeg.expDep_regimeM
#print axioms ObstfeldRogoff.NominalRigidities.EscapeClausePeg.expDep_float
#print axioms ObstfeldRogoff.NominalRigidities.EscapeClausePeg.expDep_alwaysRevalue
#print axioms ObstfeldRogoff.NominalRigidities.EscapeClausePeg.hasDerivAt_expDep_A
#print axioms ObstfeldRogoff.NominalRigidities.EscapeClausePeg.hasDerivAt_expDep_M
#print axioms ObstfeldRogoff.NominalRigidities.EscapeClausePeg.hasDerivAt_expDep_float
#print axioms ObstfeldRogoff.NominalRigidities.EscapeClausePeg.gapFn
#print axioms ObstfeldRogoff.NominalRigidities.EscapeClausePeg.quad_M_form
#print axioms ObstfeldRogoff.NominalRigidities.EscapeClausePeg.quad_factor
#print axioms ObstfeldRogoff.NominalRigidities.EscapeClausePeg.at_most_three
#print axioms ObstfeldRogoff.NominalRigidities.EscapeClausePeg.gapFn_continuous
#print axioms ObstfeldRogoff.NominalRigidities.EscapeClausePeg.gapFn_regimeA
#print axioms ObstfeldRogoff.NominalRigidities.EscapeClausePeg.gapFn_float
#print axioms ObstfeldRogoff.NominalRigidities.EscapeClausePeg.float_eqm_iff
#print axioms ObstfeldRogoff.NominalRigidities.EscapeClausePeg.float_eqm_eq
#print axioms ObstfeldRogoff.NominalRigidities.EscapeClausePeg.flat_branch_below_needs_cbar_gt
#print axioms ObstfeldRogoff.NominalRigidities.EscapeClausePeg.symmetric_flat_is_float
#print axioms ObstfeldRogoff.NominalRigidities.EscapeClausePeg.exactly_three
#print axioms ObstfeldRogoff.NominalRigidities.EscapeClausePeg.exactly_three_needs_cbar_gt
#print axioms ObstfeldRogoff.NominalRigidities.EscapeClausePeg.fn40_equality_two
#print axioms ObstfeldRogoff.NominalRigidities.EscapeClausePeg.eqm_exists
#print axioms ObstfeldRogoff.NominalRigidities.EscapeClausePeg.hasDerivAt_zbarC
#print axioms ObstfeldRogoff.NominalRigidities.EscapeClausePeg.hasDerivAt_zundC
#print axioms ObstfeldRogoff.NominalRigidities.EscapeClausePeg.steep_iff
#print axioms ObstfeldRogoff.NominalRigidities.EscapeClausePeg.exactly_three_needs_steep
#print axioms ObstfeldRogoff.NominalRigidities.EscapeClausePeg.thr_example
#print axioms ObstfeldRogoff.NominalRigidities.EscapeClausePeg.three_eqm_symmetric_costs
#print axioms ObstfeldRogoff.NominalRigidities.EscapeClausePeg.thr_example2
#print axioms ObstfeldRogoff.NominalRigidities.EscapeClausePeg.fn40_not_necessary
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.PooleParams
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.PooleParams.mk
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.PooleParams.θ
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.PooleParams.δ
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.PooleParams.η
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.PooleParams.φ
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.PooleParams.θ_pos
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.PooleParams.δ_pos
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.PooleParams.η_pos
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.PooleParams.φ_pos
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.PooleShocks
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.PooleShocks.mk
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.PooleShocks.prob
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.PooleShocks.eps
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.PooleShocks.v
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.PooleShocks.prob_nonneg
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.PooleShocks.prob_sum
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.PooleShocks.eps_mean
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.PooleShocks.v_mean
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.PooleShocks.eps_v_uncorr
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.expect
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.sigE2
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.sigV2
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.nodeEx
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.Bounded
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.IsEqm
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.floatPolicy
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.pegPolicy
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.feedbackPolicy
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.den
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.outputMSV
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.pMSV
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.eMSV
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.mMSV
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.iMSV
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.onHead
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.expect_add
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.expect_sub
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.expect_const_mul
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.expect_div_const
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.expect_const
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.expect_eps
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.expect_v
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.nodeEx_eq_expect
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.abs_nodeEx_le
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.nodeEx_onHead
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.bounded_onHead
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.tree_eigen_bounded_zero
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.one_lt_abs_lambda_iff
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.abs_lambda_lt_one_iff
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.eqm_nodeEx_y
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.eqm_nodeEx_e
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.feedback_level_recursion
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.feedback_expected_price_eq
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.feedback_node_reduced_form
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.feedback_eqm_unique
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.expect_outputMSV
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.expect_pMSV
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.expect_eMSV
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.feedback_eqm_exists
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.expect_sq_comb
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.outputVar
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.floatVar
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.pegVar
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.optimalU
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.optimalPhi
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.minVar
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.expect_outputMSV_sq
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.feedback_output_moments
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.floatPolicy_eq
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.den_pos
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.float_eqm_unique
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.floatVar_eq
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.float_output_var
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.peg_eqm_unique
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.peg_expected_money
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.peg_eqm_exists
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.peg_output_var
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.den_eta_gt
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.peg_le_float_iff
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.peg_lt_float_of_small_ratio
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.peg_lt_float_of_eps_zero
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.float_lt_peg_of_v_zero
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.optimum_identity
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.minVar_le_outputVar
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.outputVar_eq_minVar_iff
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.optimalU_nonneg
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.outputVar_optimalU
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.exists_unique_optimal_rule
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.optimalPhi_eq
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.optimalPhi_lt_eta
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.optimalPhi_neg_iff
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.minVar_lt_pegVar
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.minVar_le_floatVar
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.den_eq_zero_iff
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.feedback_no_eqm_at_pole
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.tendsto_linear_ratio
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.tendsto_quadratic_ratio
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.tendsto_eta_sub_atBot
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.tendsto_eta_sub_atTop
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.outputVar_tendsto_peg_atBot
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.outputVar_tendsto_peg_atTop
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.outputMSV_tendsto_peg
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.no_optimal_rule_of_eps_zero
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.feedback_peg_only_limit
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.sigV2_nonneg
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.feedback_eqm_var_ge_min
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.optimal_rule_eqm_attains
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.optimalPhi_tendsto_atBot
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.optimalPhi_eq_ratio
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.optimalPhi_not_tendsto_atTop
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.signExample
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.signExample_optimalPhi
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.indetExample
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.indetExample_optimalPhi
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.optimalPhi_indeterminate_iff
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.sunLam
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.sunspotLevel
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.ySun
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.pSun
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.eSun
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.mSun
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.iSun
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.expect_ySun
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.nodeEx_pSun
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.nodeEx_eSun
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.abs_sunspotLevel_le
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.sunspot_isEqm
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.sunspot_bounded
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.ySun_sub_outputMSV
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.abs_lambda_le_one_iff
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.sunspotLevelH
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.ySunH
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.ySunTree
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.pSunH
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.eSunH
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.mSunH
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.iSunH
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.expect_ySunH
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.nodeEx_pSunH
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.nodeEx_eSunH
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.sunspotH_isEqm
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.boundedLevel
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.martRev
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.abs_boundedLevel_le
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.sunspotLevelH_martRev
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.expect_martRev
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.boundary_sunspot_eqm
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.bounded_eqm_output_unique_iff
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.sunspot_at_phi_one
#print axioms ObstfeldRogoff.NominalRigidities.PooleRegimeChoice.sunspot_at_phi_one_add_two_eta
#print axioms ObstfeldRogoff.NominalRigidities.PolicyCoordination.CoordParams
#print axioms ObstfeldRogoff.NominalRigidities.PolicyCoordination.CoordParams.mk
#print axioms ObstfeldRogoff.NominalRigidities.PolicyCoordination.CoordParams.a1
#print axioms ObstfeldRogoff.NominalRigidities.PolicyCoordination.CoordParams.a2
#print axioms ObstfeldRogoff.NominalRigidities.PolicyCoordination.CoordParams.χ
#print axioms ObstfeldRogoff.NominalRigidities.PolicyCoordination.CoordParams.χ_pos
#print axioms ObstfeldRogoff.NominalRigidities.PolicyCoordination.CoordShocks
#print axioms ObstfeldRogoff.NominalRigidities.PolicyCoordination.CoordShocks.mk
#print axioms ObstfeldRogoff.NominalRigidities.PolicyCoordination.CoordShocks.prob
#print axioms ObstfeldRogoff.NominalRigidities.PolicyCoordination.CoordShocks.eps
#print axioms ObstfeldRogoff.NominalRigidities.PolicyCoordination.CoordShocks.epsF
#print axioms ObstfeldRogoff.NominalRigidities.PolicyCoordination.CoordShocks.prob_nonneg
#print axioms ObstfeldRogoff.NominalRigidities.PolicyCoordination.CoordShocks.prob_sum
#print axioms ObstfeldRogoff.NominalRigidities.PolicyCoordination.CoordShocks.eps_mean
#print axioms ObstfeldRogoff.NominalRigidities.PolicyCoordination.CoordShocks.epsF_mean
#print axioms ObstfeldRogoff.NominalRigidities.PolicyCoordination.expect
#print axioms ObstfeldRogoff.NominalRigidities.PolicyCoordination.homeGap
#print axioms ObstfeldRogoff.NominalRigidities.PolicyCoordination.foreignGap
#print axioms ObstfeldRogoff.NominalRigidities.PolicyCoordination.homeLoss
#print axioms ObstfeldRogoff.NominalRigidities.PolicyCoordination.foreignLoss
#print axioms ObstfeldRogoff.NominalRigidities.PolicyCoordination.welfare
#print axioms ObstfeldRogoff.NominalRigidities.PolicyCoordination.IsNash
#print axioms ObstfeldRogoff.NominalRigidities.PolicyCoordination.IsPlanner
#print axioms ObstfeldRogoff.NominalRigidities.PolicyCoordination.expect_affine
#print axioms ObstfeldRogoff.NominalRigidities.PolicyCoordination.homeLoss_sub
#print axioms ObstfeldRogoff.NominalRigidities.PolicyCoordination.foreignLoss_sub
#print axioms ObstfeldRogoff.NominalRigidities.PolicyCoordination.home_best_response_iff
#print axioms ObstfeldRogoff.NominalRigidities.PolicyCoordination.foreign_best_response_iff
#print axioms ObstfeldRogoff.NominalRigidities.PolicyCoordination.nash_iff_foc
#print axioms ObstfeldRogoff.NominalRigidities.PolicyCoordination.nash_expect_zero
#print axioms ObstfeldRogoff.NominalRigidities.PolicyCoordination.nash_iff_system
#print axioms ObstfeldRogoff.NominalRigidities.PolicyCoordination.nashDet
#print axioms ObstfeldRogoff.NominalRigidities.PolicyCoordination.nashM
#print axioms ObstfeldRogoff.NominalRigidities.PolicyCoordination.nashMF
#print axioms ObstfeldRogoff.NominalRigidities.PolicyCoordination.expect_nashM
#print axioms ObstfeldRogoff.NominalRigidities.PolicyCoordination.nash_iff_closed_form
#print axioms ObstfeldRogoff.NominalRigidities.PolicyCoordination.nash_exists
#print axioms ObstfeldRogoff.NominalRigidities.PolicyCoordination.nash_nonunique_of_det_zero
#print axioms ObstfeldRogoff.NominalRigidities.PolicyCoordination.plannerFOC1
#print axioms ObstfeldRogoff.NominalRigidities.PolicyCoordination.plannerFOC2
#print axioms ObstfeldRogoff.NominalRigidities.PolicyCoordination.plannerQ
#print axioms ObstfeldRogoff.NominalRigidities.PolicyCoordination.welfare_sub
#print axioms ObstfeldRogoff.NominalRigidities.PolicyCoordination.plannerQ_pos
#print axioms ObstfeldRogoff.NominalRigidities.PolicyCoordination.planner_state_iff
#print axioms ObstfeldRogoff.NominalRigidities.PolicyCoordination.planner_iff_foc
#print axioms ObstfeldRogoff.NominalRigidities.PolicyCoordination.planner_expect_zero
#print axioms ObstfeldRogoff.NominalRigidities.PolicyCoordination.pH11
#print axioms ObstfeldRogoff.NominalRigidities.PolicyCoordination.pH22
#print axioms ObstfeldRogoff.NominalRigidities.PolicyCoordination.plannerDet
#print axioms ObstfeldRogoff.NominalRigidities.PolicyCoordination.plannerDet_pos
#print axioms ObstfeldRogoff.NominalRigidities.PolicyCoordination.plannerM
#print axioms ObstfeldRogoff.NominalRigidities.PolicyCoordination.plannerMF
#print axioms ObstfeldRogoff.NominalRigidities.PolicyCoordination.expect_plannerM
#print axioms ObstfeldRogoff.NominalRigidities.PolicyCoordination.planner_iff_closed_form
#print axioms ObstfeldRogoff.NominalRigidities.PolicyCoordination.planner_exists
#print axioms ObstfeldRogoff.NominalRigidities.PolicyCoordination.plannerFOC_eq_nashFOC
#print axioms ObstfeldRogoff.NominalRigidities.PolicyCoordination.nashCoef
#print axioms ObstfeldRogoff.NominalRigidities.PolicyCoordination.plannerCoef
#print axioms ObstfeldRogoff.NominalRigidities.PolicyCoordination.nash_symmetric
#print axioms ObstfeldRogoff.NominalRigidities.PolicyCoordination.planner_symmetric
#print axioms ObstfeldRogoff.NominalRigidities.PolicyCoordination.plannerCoef_sub_nashCoef
#print axioms ObstfeldRogoff.NominalRigidities.PolicyCoordination.planner_response_compare
#print axioms ObstfeldRogoff.NominalRigidities.PolicyCoordination.expWelfare
#print axioms ObstfeldRogoff.NominalRigidities.PolicyCoordination.planner_le_nash
#print axioms ObstfeldRogoff.NominalRigidities.PolicyCoordination.planner_lt_nash
#print axioms ObstfeldRogoff.NominalRigidities.PolicyCoordination.two_instruments_iff
#print axioms ObstfeldRogoff.NominalRigidities.PolicyCoordination.zero_chi_best_response_iff
#print axioms ObstfeldRogoff.NominalRigidities.ExchangeRateFacts.mean
#print axioms ObstfeldRogoff.NominalRigidities.ExchangeRateFacts.cov
#print axioms ObstfeldRogoff.NominalRigidities.ExchangeRateFacts.var
#print axioms ObstfeldRogoff.NominalRigidities.ExchangeRateFacts.sd
#print axioms ObstfeldRogoff.NominalRigidities.ExchangeRateFacts.realRate
#print axioms ObstfeldRogoff.NominalRigidities.ExchangeRateFacts.mean_add
#print axioms ObstfeldRogoff.NominalRigidities.ExchangeRateFacts.mean_const_mul
#print axioms ObstfeldRogoff.NominalRigidities.ExchangeRateFacts.cov_comm
#print axioms ObstfeldRogoff.NominalRigidities.ExchangeRateFacts.var_nonneg
#print axioms ObstfeldRogoff.NominalRigidities.ExchangeRateFacts.cov_add_left
#print axioms ObstfeldRogoff.NominalRigidities.ExchangeRateFacts.var_add_smul
#print axioms ObstfeldRogoff.NominalRigidities.ExchangeRateFacts.var_add
#print axioms ObstfeldRogoff.NominalRigidities.ExchangeRateFacts.cov_sq_le
#print axioms ObstfeldRogoff.NominalRigidities.ExchangeRateFacts.abs_cov_le
#print axioms ObstfeldRogoff.NominalRigidities.ExchangeRateFacts.sd_sq
#print axioms ObstfeldRogoff.NominalRigidities.ExchangeRateFacts.sd_nonneg
#print axioms ObstfeldRogoff.NominalRigidities.ExchangeRateFacts.sd_add_le
#print axioms ObstfeldRogoff.NominalRigidities.ExchangeRateFacts.abs_sd_sub_le
#print axioms ObstfeldRogoff.NominalRigidities.ExchangeRateFacts.abs_sd_real_sub_sd_nominal_le
#print axioms ObstfeldRogoff.NominalRigidities.ExchangeRateFacts.cov_real_nominal
#print axioms ObstfeldRogoff.NominalRigidities.ExchangeRateFacts.corr_real_nominal_ge
#print axioms ObstfeldRogoff.NominalRigidities.ExchangeRateFacts.order_of_magnitude
#print axioms ObstfeldRogoff.NominalRigidities.ExchangeRateFacts.sd_real_of_peg
#print axioms ObstfeldRogoff.NominalRigidities.ExchangeRateFacts.diff_real_rate
#print axioms ObstfeldRogoff.NominalRigidities.ExchangeRateFacts.abs_sd_diff_le
#print axioms ObstfeldRogoff.NominalRigidities.ExchangeRateFacts.ar1_deviation
#print axioms ObstfeldRogoff.NominalRigidities.ExchangeRateFacts.halfLife
#print axioms ObstfeldRogoff.NominalRigidities.ExchangeRateFacts.log_085_bounds
#print axioms ObstfeldRogoff.NominalRigidities.ExchangeRateFacts.halfLife_spec
#print axioms ObstfeldRogoff.NominalRigidities.ExchangeRateFacts.halfLife_unique
#print axioms ObstfeldRogoff.NominalRigidities.ExchangeRateFacts.halfLife_bounds
#print axioms ObstfeldRogoff.NominalRigidities.ExchangeRateFacts.halfLife_gt
#print axioms ObstfeldRogoff.NominalRigidities.ExchangeRateFacts.halfLife_discrete
#print axioms ObstfeldRogoff.NominalRigidities.ExchangeRateFacts.gdFit
#print axioms ObstfeldRogoff.NominalRigidities.ExchangeRateFacts.gd_slope_tstat
#print axioms ObstfeldRogoff.NominalRigidities.ExchangeRateFacts.gd_intercept_tstat
#print axioms ObstfeldRogoff.NominalRigidities.ExchangeRateFacts.gd_elasticity
#print axioms ObstfeldRogoff.NominalRigidities.ExchangeRateFacts.gd_ratio_intercept
#print axioms ObstfeldRogoff.NominalRigidities.ExchangeRateFacts.gd_ratio_reading_inconsistent
#print axioms ObstfeldRogoff.NominalRigidities.ExchangeRateFacts.gd_index_reparam
#print axioms ObstfeldRogoff.NominalRigidities.ExchangeRateFacts.log_ten_bounds
#print axioms ObstfeldRogoff.NominalRigidities.ExchangeRateFacts.gd_index_intercept
#print axioms ObstfeldRogoff.NominalRigidities.ExchangeRateFacts.gd_index_reading_consistent
#print axioms ObstfeldRogoff.NominalRigidities.ExchangeRateFacts.cbiFit
#print axioms ObstfeldRogoff.NominalRigidities.ExchangeRateFacts.cbi_fitted_values
#print axioms ObstfeldRogoff.NominalRigidities.ExchangeRateFacts.cbi_tstats
