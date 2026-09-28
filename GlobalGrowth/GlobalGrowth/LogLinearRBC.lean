/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import GlobalGrowth.BrockMirman
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The log-linear stochastic growth model

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §7.4.3
(pp. 501–507), equations (117)–(135).

* Nonstochastic steady state (121)–(124), with (117) read as `K_{t+1} − K_t = Y_t − C_t` (the
  book prints `K_{t−1}`); (125) exactly.
* The log-linearisations (126) and (128) as **exact partial derivatives** at the steady state.
* The lognormal Euler step (127), with the lognormal moment identity as an explicit hypothesis.
* The method of undetermined coefficients (131)–(135) as an iff: the conjecture solves the
  system for all `(k, e)` iff `a_ck` solves (135) and `a_ce` the p. 506 formula.
* (135) has roots of opposite sign for **every** `α ∈ (0, 1)`; the positive root lies in
  `(α, α/(1 − β))`, gives `0 < λ < 1`, and is the unique stable root (the negative root gives
  `λ > 1/β`); `a_ck` does not depend on `ρ`; `a_ce` is strictly increasing in `ρ` on `ρ ≤ 1`.
* Impulse responses (closed form, convergence to zero) and the corrected p. 506 arithmetic
  (the output effect is 0.1 percent, not "less than 0.04 percent").
-/

namespace ObstfeldRogoff.GlobalGrowth.LogLinearRBC

open Filter Topology

/-! ## The nonstochastic steady state (121)–(124) -/

/-- **(121)–(124)**: with zero depreciation (117) (corrected: `K_{t+1} − K_t = Y_t − C_t`),
`Y = K^α E^{1−α}` (118), the Euler equation (119) and the return (120), a constant path
`(K, C, E)` is a steady state iff `1 + r̄ = 1/β`, `C̄ = Ȳ` and
`α (K̄/Ē)^{α−1} = (1 − β)/β`; then `Ē/K̄ = ((1 − β)/(βα))^{1/(1−α)}` (122) and
`Ȳ/K̄ = (1 − β)/(βα)` (123). -/
theorem steady_state {α β K E C r : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β)
    (hK : 0 < K) (hE : 0 < E) (hC : 0 < C)
    (h117 : K - K = K ^ α * E ^ (1 - α) - C)
    (h119 : 1 / C = β * ((1 + r) / C))
    (h120 : 1 + r = 1 + α * (K / E) ^ (α - 1)) :
    1 + r = 1 / β ∧ C / (K ^ α * E ^ (1 - α)) = 1 ∧
      E / K = ((1 - β) / (β * α)) ^ (1 / (1 - α)) ∧
      K ^ α * E ^ (1 - α) / K = (1 - β) / (β * α) := by
  have h121 : 1 + r = 1 / β := by
    field_simp at h119
    field_simp
    linarith
  have hY : C = K ^ α * E ^ (1 - α) := by linarith
  have hr : α * (K / E) ^ (α - 1) = (1 - β) / β := by
    have : r = 1 / β - 1 := by linarith
    rw [h120] at h121
    field_simp at h121 ⊢
    linarith
  have hKE := div_pos hK hE
  have hEK := div_pos hE hK
  -- (E/K)^{1−α} = (1−β)/(βα)
  have h1 : (E / K) ^ (1 - α) = (1 - β) / (β * α) := by
    have : (K / E) ^ (α - 1) = (E / K) ^ (1 - α) := by
      rw [← inv_div, Real.inv_rpow hEK.le, ← Real.rpow_neg hEK.le]; ring_nf
    rw [← this]
    field_simp at hr ⊢
    linarith
  have h1α : (1 - α) ≠ 0 := by linarith
  refine ⟨h121, by rw [hY, div_self (by positivity)], ?_, ?_⟩
  · rw [← h1, ← Real.rpow_mul hEK.le, mul_one_div_cancel h1α, Real.rpow_one]
  · have : K ^ α * E ^ (1 - α) / K = (E / K) ^ (1 - α) := by
      rw [Real.div_rpow hE.le hK.le]
      rw [show K ^ α = K / K ^ (1 - α) by
        rw [Real.rpow_sub hK, Real.rpow_one]; field_simp]
      field_simp
    rw [this, h1]

/-- **(125)** exactly (no approximation): `log Y = α log K + (1 − α) log E`. -/
theorem log_output {α K E : ℝ} (hK : 0 < K) (hE : 0 < E) :
    Real.log (K ^ α * E ^ (1 - α)) = α * Real.log K + (1 - α) * Real.log E := by
  rw [Real.log_mul (Real.rpow_pos_of_pos hK α).ne' (Real.rpow_pos_of_pos hE _).ne',
    Real.log_rpow hK, Real.log_rpow hE]

/-! ## Log-linearisation as exact derivatives (126), (128)

Write `K = exp(κ + k)`, `C = exp(γ + c)`, `E = exp(ε + e)` with `(κ, γ, ε)` the logs of the
steady state; `(k, c, e)` are log deviations (the book's sans-serif variables). Output (118) is
`exp(α(κ + k) + (1 − α)(ε + e))`. -/

/-- Log deviation of next period's capital from the steady state, from (117)–(118). -/
noncomputable def nextLogCap (α κ γ ε k c e : ℝ) : ℝ :=
  Real.log (Real.exp (κ + k) + Real.exp (α * (κ + k) + (1 - α) * (ε + e)) -
    Real.exp (γ + c)) - κ

/-- Steady-state restrictions in logs: `C̄ = Ȳ` (124) and `Ȳ/K̄ = (1 − β)/(βα)` (123). -/
structure SteadyLogs (α β κ γ ε : ℝ) : Prop where
  α_pos : 0 < α
  α_lt_one : α < 1
  β_pos : 0 < β
  β_lt_one : β < 1
  cons_eq_output : γ = α * κ + (1 - α) * ε
  output_capital : Real.exp (α * κ + (1 - α) * ε - κ) = (1 - β) / (β * α)

/-- At the steady state `k′ = 0`. -/
theorem nextLogCap_zero {α β κ γ ε : ℝ} (hs : SteadyLogs α β κ γ ε) :
    nextLogCap α κ γ ε 0 0 0 = 0 := by
  simp only [nextLogCap, add_zero, hs.cons_eq_output]
  rw [show Real.exp κ + Real.exp (α * κ + (1 - α) * ε) - Real.exp (α * κ + (1 - α) * ε) =
    Real.exp κ by ring, Real.log_exp, sub_self]

/-- A key identity: `exp(y₀) = exp(κ) (1 − β)/(βα)` (output equals `K̄ (1 − β)/(βα)`). -/
theorem exp_output {α β κ γ ε : ℝ} (hs : SteadyLogs α β κ γ ε) :
    Real.exp (α * κ + (1 - α) * ε) = Real.exp κ * ((1 - β) / (β * α)) := by
  rw [← hs.output_capital, ← Real.exp_add]; ring_nf

/-- **(126), coefficient on `k`**: `∂k′/∂k = 1/β` at the steady state. -/
theorem hasDerivAt_nextLogCap_k {α β κ γ ε : ℝ} (hs : SteadyLogs α β κ γ ε) :
    HasDerivAt (fun k => nextLogCap α κ γ ε k 0 0) (1 / β) 0 := by
  have hf : (fun k => nextLogCap α κ γ ε k 0 0) = fun k => Real.log (Real.exp (κ + k) +
      Real.exp (α * (κ + k) + (1 - α) * ε) - Real.exp γ) - κ := by
    funext k; simp [nextLogCap]
  rw [hf]
  have h1 : HasDerivAt (fun k => Real.exp (κ + k)) (Real.exp κ) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_add κ).exp
  have hl : HasDerivAt (fun k => α * (κ + k) + (1 - α) * ε) α 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).const_add κ).const_mul α).add_const ((1 - α) * ε)
  have h2 : HasDerivAt (fun k => Real.exp (α * (κ + k) + (1 - α) * ε))
      (Real.exp (α * κ + (1 - α) * ε) * α) 0 := by
    simpa using hl.exp
  have hin := (h1.add h2).sub_const (Real.exp γ)
  have hpos : 0 < Real.exp (κ + 0) + Real.exp (α * (κ + 0) + (1 - α) * ε) - Real.exp γ := by
    simp only [add_zero, hs.cons_eq_output]; simp [Real.exp_pos]
  have h := (hin.log hpos.ne').sub_const κ
  refine h.congr_deriv ?_
  simp only [Pi.add_apply, add_zero, hs.cons_eq_output, exp_output hs]
  have hb := hs.β_pos.ne'
  have ha := hs.α_pos.ne'
  have he := (Real.exp_pos κ).ne'
  field_simp
  ring

/-- **(126), coefficient on `c`**: `∂k′/∂c = −(1 − β)/(βα)`. -/
theorem hasDerivAt_nextLogCap_c {α β κ γ ε : ℝ} (hs : SteadyLogs α β κ γ ε) :
    HasDerivAt (fun c => nextLogCap α κ γ ε 0 c 0) (-((1 - β) / (β * α))) 0 := by
  have hf : (fun c => nextLogCap α κ γ ε 0 c 0) = fun c => Real.log (Real.exp κ +
      Real.exp (α * κ + (1 - α) * ε) - Real.exp (γ + c)) - κ := by
    funext c; simp [nextLogCap]
  rw [hf]
  have h1 : HasDerivAt (fun c => Real.exp (γ + c)) (Real.exp γ) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_add γ).exp
  have hin := h1.const_sub (Real.exp κ + Real.exp (α * κ + (1 - α) * ε))
  have hpos : 0 < Real.exp κ + Real.exp (α * κ + (1 - α) * ε) - Real.exp (γ + 0) := by
    simp only [add_zero, hs.cons_eq_output]; simp [Real.exp_pos]
  have h := (hin.log hpos.ne').sub_const κ
  refine h.congr_deriv ?_
  simp only [add_zero, hs.cons_eq_output, exp_output hs]
  have hb := hs.β_pos.ne'
  have ha := hs.α_pos.ne'
  have he := (Real.exp_pos κ).ne'
  field_simp
  ring

/-- **(126), coefficient on `e`**: `∂k′/∂e = (1 − α)(1 − β)/(βα)`. -/
theorem hasDerivAt_nextLogCap_e {α β κ γ ε : ℝ} (hs : SteadyLogs α β κ γ ε) :
    HasDerivAt (fun e => nextLogCap α κ γ ε 0 0 e) ((1 - α) * (1 - β) / (β * α)) 0 := by
  have hf : (fun e => nextLogCap α κ γ ε 0 0 e) = fun e => Real.log (Real.exp κ +
      Real.exp (α * κ + (1 - α) * (ε + e)) - Real.exp γ) - κ := by
    funext e; simp [nextLogCap]
  rw [hf]
  have hl : HasDerivAt (fun e => α * κ + (1 - α) * (ε + e)) (1 - α) 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).const_add ε).const_mul (1 - α)).const_add (α * κ)
  have h2 : HasDerivAt (fun e => Real.exp (α * κ + (1 - α) * (ε + e)))
      (Real.exp (α * κ + (1 - α) * ε) * (1 - α)) 0 := by
    simpa using hl.exp
  have hin := (h2.const_add (Real.exp κ)).sub_const (Real.exp γ)
  have hpos : 0 < Real.exp κ + Real.exp (α * κ + (1 - α) * (ε + 0)) - Real.exp γ := by
    simp only [add_zero, hs.cons_eq_output]; simp [Real.exp_pos]
  have h := (hin.log hpos.ne').sub_const κ
  refine h.congr_deriv ?_
  simp only [add_zero, hs.cons_eq_output, exp_output hs]
  have hb := hs.β_pos.ne'
  have ha := hs.α_pos.ne'
  have he := (Real.exp_pos κ).ne'
  field_simp
  ring

/-- Log deviation of the gross return from `1 + r̄ = 1/β`, from (120):
`r̂ = log(1 + α exp((α − 1)(κ + k − ε − e))) − log(1/β)`. -/
noncomputable def logReturnDev (α β κ ε k e : ℝ) : ℝ :=
  Real.log (1 + α * Real.exp ((α - 1) * (κ + k - (ε + e)))) - Real.log (1 / β)

/-- In logs, (120) at the steady state: `α exp((α − 1)(κ − ε)) = (1 − β)/β`. -/
theorem steady_return {α β κ γ ε : ℝ} (hs : SteadyLogs α β κ γ ε) :
    α * Real.exp ((α - 1) * (κ - ε)) = (1 - β) / β := by
  have h := hs.output_capital
  rw [show α * κ + (1 - α) * ε - κ = (α - 1) * (κ - ε) by ring] at h
  rw [h]
  have := hs.α_pos.ne'
  have := hs.β_pos.ne'
  field_simp

/-- **(128), coefficient on `k`**: `∂r̂/∂k = −(1 − α)(1 − β)`. -/
theorem hasDerivAt_logReturnDev_k {α β κ γ ε : ℝ} (hs : SteadyLogs α β κ γ ε) :
    HasDerivAt (fun k => logReturnDev α β κ ε k 0) (-((1 - α) * (1 - β))) 0 := by
  have hl : HasDerivAt (fun k => (α - 1) * (κ + k - (ε + 0))) (α - 1) 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).const_add κ).sub_const (ε + 0)).const_mul (α - 1)
  have hin : HasDerivAt (fun k => 1 + α * Real.exp ((α - 1) * (κ + k - (ε + 0))))
      (α * (Real.exp ((α - 1) * (κ + 0 - (ε + 0))) * (α - 1))) 0 :=
    (((Real.hasDerivAt_exp _).comp 0 hl).const_mul α).const_add 1
  have hsr := steady_return hs
  have hpos : 0 < 1 + α * Real.exp ((α - 1) * (κ + 0 - (ε + 0))) := by
    simp only [add_zero]; rw [hsr]; have := hs.β_pos; have := hs.β_lt_one; positivity
  have h := (hin.log hpos.ne').sub_const (Real.log (1 / β))
  refine h.congr_deriv ?_
  simp only [add_zero]
  rw [show α * (Real.exp ((α - 1) * (κ - ε)) * (α - 1)) =
    (α * Real.exp ((α - 1) * (κ - ε))) * (α - 1) by ring, hsr]
  have := hs.β_pos.ne'
  field_simp
  ring

/-- **(128), coefficient on `e`**: `∂r̂/∂e = (1 − α)(1 − β)`. -/
theorem hasDerivAt_logReturnDev_e {α β κ γ ε : ℝ} (hs : SteadyLogs α β κ γ ε) :
    HasDerivAt (fun e => logReturnDev α β κ ε 0 e) ((1 - α) * (1 - β)) 0 := by
  have hl : HasDerivAt (fun e => (α - 1) * (κ + 0 - (ε + e))) (-(α - 1)) 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).const_add ε).const_sub (κ + 0)).const_mul (α - 1)
  have hin : HasDerivAt (fun e => 1 + α * Real.exp ((α - 1) * (κ + 0 - (ε + e))))
      (α * (Real.exp ((α - 1) * (κ + 0 - (ε + 0))) * (-(α - 1)))) 0 :=
    (((Real.hasDerivAt_exp _).comp 0 hl).const_mul α).const_add 1
  have hsr := steady_return hs
  have hpos : 0 < 1 + α * Real.exp ((α - 1) * (κ + 0 - (ε + 0))) := by
    simp only [add_zero]; rw [hsr]; have := hs.β_pos; have := hs.β_lt_one; positivity
  have h := (hin.log hpos.ne').sub_const (Real.log (1 / β))
  refine h.congr_deriv ?_
  simp only [add_zero]
  rw [show α * (Real.exp ((α - 1) * (κ - ε)) * (-(α - 1))) =
    (α * Real.exp ((α - 1) * (κ - ε))) * (1 - α) by ring, hsr]
  have := hs.β_pos.ne'
  field_simp
  ring

/-! ## The lognormal Euler step (127), (129) -/

/-- **(127)**, p. 504. Let `X = (1 + r̃)/C` take values `X(s) > 0` with probabilities `p(s)`. If
`E X = exp(E log X + V/2)` (the lognormal moment identity, an explicit hypothesis: it holds
when `log X` is normal with variance `V`, and it is the only place lognormality enters), then
the Euler equation `1/C₋₁ = β E X` gives exactly
`E log C − log C₋₁ = log β + V/2 + E log(1 + r̃)`, i.e. `E c − c₋₁ = E r̂ + χ₀` in deviations
from the steady state (`1 + r̄ = 1/β`, `χ₀ = V/2`). -/
theorem lognormal_euler {ι : Type*} [Fintype ι] {p : ι → ℝ} (hp : ∑ s, p s = 1) {β Cm V : ℝ}
    (hβ : 0 < β) {R C : ι → ℝ} (hR : ∀ s, 0 < R s) (hC : ∀ s, 0 < C s)
    (heuler : 1 / Cm = β * ∑ s, p s * (R s / C s))
    (hmgf : ∑ s, p s * (R s / C s) =
      Real.exp (∑ s, p s * Real.log (R s / C s) + V / 2)) :
    ∑ s, p s * Real.log (C s) - Real.log Cm =
      Real.log β + V / 2 + ∑ s, p s * Real.log (R s) ∧
    ∀ Cbar, (∑ s, p s * (Real.log (C s) - Real.log Cbar)) - (Real.log Cm - Real.log Cbar) =
      ∑ s, p s * (Real.log (R s) - Real.log (1 / β)) + V / 2 := by
  have hlog : -Real.log Cm = Real.log β + (∑ s, p s * Real.log (R s / C s) + V / 2) := by
    rw [← Real.log_inv, ← one_div, heuler, hmgf, Real.log_mul hβ.ne' (Real.exp_pos _).ne',
      Real.log_exp]
  have hsplit : ∑ s, p s * Real.log (R s / C s) =
      ∑ s, p s * Real.log (R s) - ∑ s, p s * Real.log (C s) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun s _ => by
      rw [Real.log_div (hR s).ne' (hC s).ne']; ring
  have h1 : ∑ s, p s * Real.log (C s) - Real.log Cm =
      Real.log β + V / 2 + ∑ s, p s * Real.log (R s) := by
    rw [hsplit] at hlog; linarith
  refine ⟨h1, fun Cbar => ?_⟩
  have e0 : ∑ s, p s * (Real.log (C s) - Real.log Cbar) =
      ∑ s, p s * Real.log (C s) - Real.log Cbar := by
    rw [Finset.sum_congr rfl fun s _ => by rw [mul_sub]]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hp, one_mul]
  have e1 : ∑ s, p s * (Real.log (R s) - Real.log (1 / β)) =
      ∑ s, p s * Real.log (R s) + Real.log β := by
    rw [Finset.sum_congr rfl fun s _ => by rw [mul_sub]]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hp, one_mul, one_div, Real.log_inv]
    ring
  rw [e0, e1]
  linarith

/-! ## Undetermined coefficients (130)–(135) -/

/-- The coefficient on `k_t` in (132): `λ = 1/β − (1 − β) a_ck/(βα)`. -/
noncomputable def lam (α β ack : ℝ) : ℝ := 1 / β - (1 - β) * ack / (β * α)

/-- The coefficient on `e_t` in (132): `μ = (1 − α)(1 − β)/(βα) − (1 − β) a_ce/(βα)`. -/
noncomputable def mu (α β ace : ℝ) : ℝ := (1 - α) * (1 - β) / (β * α) - (1 - β) * ace / (β * α)

/-- **(132)**: substituting the conjecture (131) `c = a_ck k + a_ce e` into the linearised
accumulation equation (126) gives `k′ = λ k + μ e`. -/
theorem eq132 {α β ack ace k e : ℝ} :
    1 / β * k - (1 - β) / (β * α) * (ack * k + ace * e) + (1 - α) * (1 - β) / (β * α) * e =
      lam α β ack * k + mu α β ace * e := by
  unfold lam mu; ring

/-- The quadratic (135): `q(a) = −a² + [2α − 1 + β(1 − α)] a + α(1 − α)`. -/
def quad (α β a : ℝ) : ℝ := -a ^ 2 + (2 * α - 1 + β * (1 - α)) * a + α * (1 - α)

/-- The numerator and denominator of the book's `a_ce` formula (p. 506). -/
def aceNum (α β ρ ack : ℝ) : ℝ := -ack * (1 - α) + (1 - α) * (ρ * β * α - (1 - α) * (1 - β))

/-- Denominator of the `a_ce` formula: `βα(ρ − 1)/(1 − β) − [a_ck + (1 − α)(1 − β)]`. -/
noncomputable def aceDen (α β ρ ack : ℝ) : ℝ :=
  β * α / (1 - β) * (ρ - 1) - (ack + (1 - α) * (1 - β))

/-- **(133)–(135), the method of undetermined coefficients, exactly.** With `E_t e_{t+1} = ρ e_t`
(130), the conjecture (131) satisfies the forwarded Euler equation (133)
`a_ck(k′ − k) + a_ce(ρe − e) = (1 − α)(1 − β)(ρe − k′)` (with `k′` from (132)) for **all**
`(k, e)` if and only if `a_ck` solves the quadratic (135) and `a_ce · den = num` (p. 506). -/
theorem undetermined_coefficients {α β ρ ack ace : ℝ} (hα : 0 < α) (hβ0 : 0 < β)
    (hβ1 : β < 1) :
    (∀ k e, ack * (lam α β ack * k + mu α β ace * e - k) + ace * (ρ * e - e) =
      (1 - α) * (1 - β) * (ρ * e - (lam α β ack * k + mu α β ace * e))) ↔
    quad α β ack = 0 ∧ ace * aceDen α β ρ ack = aceNum α β ρ ack := by
  have h1 : (1 - β) ≠ 0 := by linarith
  have hb := hβ0.ne'
  have ha := hα.ne'
  have hkey : ∀ k e, ack * (lam α β ack * k + mu α β ace * e - k) + ace * (ρ * e - e) -
      (1 - α) * (1 - β) * (ρ * e - (lam α β ack * k + mu α β ace * e)) =
      (1 - β) / (β * α) * (quad α β ack * k +
        (ace * aceDen α β ρ ack - aceNum α β ρ ack) * e) := by
    intro k e
    unfold lam mu quad aceNum aceDen
    field_simp
    ring
  have hc : (1 - β) / (β * α) ≠ 0 := div_ne_zero h1 (mul_ne_zero hb ha)
  constructor
  · intro h
    have h10 := hkey 1 0
    have h01 := hkey 0 1
    rw [h 1 0, sub_self] at h10
    rw [h 0 1, sub_self] at h01
    have e1 := (mul_eq_zero.1 h10.symm).resolve_left hc
    have e2 := (mul_eq_zero.1 h01.symm).resolve_left hc
    simp only [mul_one, mul_zero, add_zero, zero_add] at e1 e2
    exact ⟨e1, by linarith⟩
  · rintro ⟨hq, hce⟩ k e
    have := hkey k e
    rw [hq, show ace * aceDen α β ρ ack - aceNum α β ρ ack = 0 by linarith] at this
    linarith [show (1 - β) / (β * α) * (0 * k + 0 * e) = 0 by ring]

/-- The discriminant of (135) is positive. -/
theorem quad_disc_pos {α β : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    0 < (2 * α - 1 + β * (1 - α)) ^ 2 + 4 * (α * (1 - α)) := by
  have := mul_pos hα0 (sub_pos.2 hα1); positivity

/-- The positive (stable) root of (135). -/
noncomputable def ackPos (α β : ℝ) : ℝ :=
  ((2 * α - 1 + β * (1 - α)) + Real.sqrt ((2 * α - 1 + β * (1 - α)) ^ 2 + 4 * (α * (1 - α)))) / 2

/-- The negative (unstable) root of (135). -/
noncomputable def ackNeg (α β : ℝ) : ℝ :=
  ((2 * α - 1 + β * (1 - α)) - Real.sqrt ((2 * α - 1 + β * (1 - α)) ^ 2 + 4 * (α * (1 - α)))) / 2

/-- Factorisation `q(a) = −(a − a₊)(a − a₋)`. -/
theorem quad_factor {α β : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (a : ℝ) :
    quad α β a = -((a - ackPos α β) * (a - ackNeg α β)) := by
  have hs := Real.sq_sqrt (quad_disc_pos (β := β) hα0 hα1).le
  unfold quad ackPos ackNeg
  nlinarith [hs]

/-- **Roots of opposite sign** (p. 506, "for reasonable parameter values"; in fact for every
`α ∈ (0, 1)`): `a₋ < 0 < a₊`, and these are the only roots. -/
theorem roots_opposite_sign {α β : ℝ} (hα0 : 0 < α) (hα1 : α < 1) :
    ackNeg α β < 0 ∧ 0 < ackPos α β ∧ quad α β (ackPos α β) = 0 ∧ quad α β (ackNeg α β) = 0 ∧
      ∀ a, quad α β a = 0 → a = ackPos α β ∨ a = ackNeg α β := by
  set B := 2 * α - 1 + β * (1 - α)
  have hD := quad_disc_pos (β := β) hα0 hα1
  have hsq : |B| < Real.sqrt (B ^ 2 + 4 * (α * (1 - α))) := by
    rw [← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_lt_sqrt (sq_nonneg _) (by have := mul_pos hα0 (sub_pos.2 hα1); linarith)
  have hB1 := neg_abs_le B
  have hB2 := le_abs_self B
  refine ⟨by unfold ackNeg; linarith, by unfold ackPos; linarith, ?_, ?_, fun a ha => ?_⟩
  · rw [quad_factor hα0 hα1]; ring
  · rw [quad_factor hα0 hα1]; ring
  · rw [quad_factor hα0 hα1, neg_eq_zero, mul_eq_zero] at ha
    rcases ha with h | h
    · left; linarith
    · right; linarith

/-- **The stable root lies in `(α, α/(1 − β))`** (stronger than the book). -/
theorem ackPos_bounds {α β : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1) :
    α < ackPos α β ∧ ackPos α β < α / (1 - β) := by
  obtain ⟨hneg, hpos, -, -, -⟩ := roots_opposite_sign (β := β) hα0 hα1
  have h1β : 0 < 1 - β := by linarith
  have qα : quad α β α = α * β * (1 - α) := by unfold quad; ring
  have qb : quad α β (α / (1 - β)) = -(α ^ 2 * β / (1 - β) ^ 2) := by
    unfold quad; field_simp; ring
  have f1 := quad_factor (β := β) hα0 hα1 α
  have f2 := quad_factor (β := β) hα0 hα1 (α / (1 - β))
  have hqα : 0 < quad α β α := by rw [qα]; have := mul_pos hα0 hβ0; nlinarith
  have hqb : quad α β (α / (1 - β)) < 0 := by
    rw [qb]; have : 0 < α ^ 2 * β / (1 - β) ^ 2 := by positivity
    linarith
  have hαb : 0 < α / (1 - β) := div_pos hα0 h1β
  constructor
  · by_contra h
    push Not at h
    nlinarith [f1, hqα, h, hneg]
  · by_contra h
    push Not at h
    nlinarith [f2, hqb, h, hαb, hneg]

/-- **Saddle-path stability** (p. 506): with the positive root, the coefficient on `k` in (132)
satisfies `0 < λ(a₊) < 1`; with the negative root `λ(a₋) > 1/β > 1`. So `a₊` is the unique root
giving a stable solution, and `a_ck` does not depend on `ρ`. -/
theorem saddle_path {α β : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1) :
    0 < lam α β (ackPos α β) ∧ lam α β (ackPos α β) < 1 ∧ 1 / β < lam α β (ackNeg α β) ∧
      ∀ a, quad α β a = 0 → |lam α β a| < 1 → a = ackPos α β := by
  obtain ⟨hneg, -, -, -, hroots⟩ := roots_opposite_sign (β := β) hα0 hα1
  obtain ⟨hl, hu⟩ := ackPos_bounds hα0 hα1 hβ0 hβ1
  have h1β : 0 < 1 - β := by linarith
  have hlam : ∀ a, lam α β a = (α - (1 - β) * a) / (β * α) := fun a => by
    unfold lam; field_simp
  have hba : 0 < β * α := mul_pos hβ0 hα0
  have hA : 0 < lam α β (ackPos α β) := by
    rw [hlam]; apply div_pos _ hba
    have := (lt_div_iff₀ h1β).1 hu; linarith
  have hB : lam α β (ackPos α β) < 1 := by
    rw [hlam, div_lt_one hba]; nlinarith
  have hC : 1 / β < lam α β (ackNeg α β) := by
    rw [hlam, show 1 / β = α / (β * α) by field_simp]
    apply div_lt_div_of_pos_right _ hba
    nlinarith
  refine ⟨hA, hB, hC, fun a ha hlt => ?_⟩
  rcases hroots a ha with h | h
  · exact h
  · exfalso
    rw [h] at hlt
    have h1 : 1 < 1 / β := by rw [lt_div_iff₀ hβ0]; linarith
    have := le_abs_self (lam α β (ackNeg α β))
    linarith

/-- The `a_ce` formula (p. 506): `a_ce = num/den`. -/
noncomputable def aceFormula (α β ρ ack : ℝ) : ℝ := aceNum α β ρ ack / aceDen α β ρ ack

/-- The denominator is negative for every `ρ ≤ 1` when `a_ck > 0` (so the formula has no pole). -/
theorem aceDen_neg {α β ρ ack : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hack : 0 < ack) (hρ : ρ ≤ 1) : aceDen α β ρ ack < 0 := by
  unfold aceDen
  have h1β : 0 < 1 - β := by linarith
  have : β * α / (1 - β) * (ρ - 1) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
  have : 0 ≤ (1 - α) * (1 - β) := mul_nonneg (by linarith) h1β.le
  linarith

/-- **`a_ce` is strictly increasing in `ρ`** (p. 506, "with a bit of algebra"): on `ρ ≤ 1`,
for any `a_ck > α` (in particular the stable root). The cross-multiplied difference is
`(ρ₂ − ρ₁) · β(1 − α)βα[a_ck + (1 − α)(1 − β) − α]/(1 − β)² > 0`. -/
theorem aceFormula_strictMonoOn {α β ack : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) (hack : α < ack) :
    StrictMonoOn (fun ρ => aceFormula α β ρ ack) (Set.Iic 1) := by
  intro ρ₁ h₁ ρ₂ h₂ h12
  have hd1 := aceDen_neg hα0 hα1 hβ0 hβ1 (hα0.trans hack) h₁
  have hd2 := aceDen_neg hα0 hα1 hβ0 hβ1 (hα0.trans hack) h₂
  simp only [aceFormula]
  have h1β : 0 < 1 - β := by linarith
  have key : aceNum α β ρ₂ ack * aceDen α β ρ₁ ack - aceNum α β ρ₁ ack * aceDen α β ρ₂ ack =
      (ρ₂ - ρ₁) * (β * α * (1 - α) * β * (ack + (1 - α) * (1 - β) - α) / (1 - β)) := by
    unfold aceNum aceDen
    field_simp
    ring
  have hpos : 0 < (ρ₂ - ρ₁) *
      (β * α * (1 - α) * β * (ack + (1 - α) * (1 - β) - α) / (1 - β)) := by
    have : 0 < ack + (1 - α) * (1 - β) - α := by nlinarith
    have : 0 < 1 - α := by linarith
    apply mul_pos (by linarith); positivity
  have hdiff : aceNum α β ρ₁ ack / aceDen α β ρ₁ ack - aceNum α β ρ₂ ack / aceDen α β ρ₂ ack =
      -(aceNum α β ρ₂ ack * aceDen α β ρ₁ ack - aceNum α β ρ₁ ack * aceDen α β ρ₂ ack) /
        (aceDen α β ρ₁ ack * aceDen α β ρ₂ ack) := by
    have := hd1.ne
    have := hd2.ne
    field_simp
    ring
  have hDD : 0 < aceDen α β ρ₁ ack * aceDen α β ρ₂ ack := mul_pos_of_neg_of_neg hd1 hd2
  have : aceNum α β ρ₁ ack / aceDen α β ρ₁ ack - aceNum α β ρ₂ ack / aceDen α β ρ₂ ack < 0 := by
    rw [hdiff, key]
    exact div_neg_of_neg_of_pos (by linarith) hDD
  linarith

/-- The stable solution's `a_ce` rises with persistence `ρ`. -/
theorem ace_increasing_in_persistence {α β : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hβ0 : 0 < β)
    (hβ1 : β < 1) : StrictMonoOn (fun ρ => aceFormula α β ρ (ackPos α β)) (Set.Iic 1) :=
  aceFormula_strictMonoOn hα0 hα1 hβ0 hβ1 (ackPos_bounds hα0 hα1 hβ0 hβ1).1

/-! ## Impulse responses -/

/-- Capital response to a one-time innovation `ε` at date 0 from the steady state:
`k₀ = 0`, `k_{t+1} = λ k_t + μ e_t`, with `e_t = ρᵗ ε` (130). -/
noncomputable def impulseK (lamv muv ρ ε : ℝ) : ℕ → ℝ
  | 0 => 0
  | t + 1 => lamv * impulseK lamv muv ρ ε t + muv * (ρ ^ t * ε)

/-- Closed form of the capital impulse response when `λ ≠ ρ`:
`k_t = μ ε (λᵗ − ρᵗ)/(λ − ρ)`. -/
theorem impulseK_closed {lamv muv ρ ε : ℝ} (hne : lamv ≠ ρ) (t : ℕ) :
    impulseK lamv muv ρ ε t = muv * ε * (lamv ^ t - ρ ^ t) / (lamv - ρ) := by
  have h : lamv - ρ ≠ 0 := sub_ne_zero.2 hne
  induction t with
  | zero => simp [impulseK]
  | succ t ih =>
    rw [impulseK, ih]
    field_simp
    ring

/-- **Impulse responses die out** on the saddle path: with `0 ≤ λ < 1` (the stable root,
`saddle_path`) and `|ρ| < 1`, the responses of `e`, `k`, log output `y = αk + (1 − α)e` (125)
and consumption `c = a_ck k + a_ce e` (131) all converge to zero. -/
theorem impulse_tendsto_zero {α lamv muv ρ ε ack ace : ℝ} (hl0 : 0 ≤ lamv) (hl1 : lamv < 1)
    (hρ : |ρ| < 1) :
    Tendsto (fun t => ρ ^ t * ε) atTop (𝓝 0) ∧
      Tendsto (impulseK lamv muv ρ ε) atTop (𝓝 0) ∧
      Tendsto (fun t => α * impulseK lamv muv ρ ε t + (1 - α) * (ρ ^ t * ε)) atTop (𝓝 0) ∧
      Tendsto (fun t => ack * impulseK lamv muv ρ ε t + ace * (ρ ^ t * ε)) atTop (𝓝 0) := by
  have he : Tendsto (fun t => ρ ^ t * ε) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_abs_lt_one hρ).mul_const ε
  have hf : Tendsto (fun t => muv * (ρ ^ (t - 1) * ε)) atTop (𝓝 0) := by
    have : Tendsto (fun t => muv * (ρ ^ t * ε)) atTop (𝓝 0) := by
      simpa using he.const_mul muv
    rw [← tendsto_add_atTop_iff_nat 1]
    simpa using this
  have hk : Tendsto (impulseK lamv muv ρ ε) atTop (𝓝 0) := by
    have := BrockMirman.tendsto_of_linear_recursion (c := 0) hl0 hl1
      (m := impulseK lamv muv ρ ε) (e := fun t => muv * (ρ ^ (t - 1) * ε))
      (fun T => by simp [impulseK]) hf
    simpa using this
  refine ⟨he, hk, ?_, ?_⟩
  · simpa using (hk.const_mul α).add (he.const_mul (1 - α))
  · simpa using (hk.const_mul ack).add (he.const_mul ace)

/-- On impact the capital stock does not move (`k₀ = 0`), so date-0 log output moves by
`(1 − α)ε` only; the internal propagation to date 1 is `α μ ε` (p. 506). -/
theorem impulse_first_periods {α lamv muv ρ ε : ℝ} :
    α * impulseK lamv muv ρ ε 0 + (1 - α) * (ρ ^ 0 * ε) = (1 - α) * ε ∧
      α * impulseK lamv muv ρ ε 1 + (1 - α) * (ρ ^ 1 * ε) = α * muv * ε + (1 - α) * ρ * ε := by
  constructor
  · simp [impulseK]
  · simp [impulseK]; ring

/-! ## The p. 506 arithmetic (corrected) -/

/-- **p. 506 numbers, corrected.** With `K/Y = 3`, a transitory shock raising output by 1% of
which half is saved raises next period's capital by `0.5% of Y = 0.167% of K` (the book's
"well under 1 percent" and "less than 0.2 percent" are right). With a marginal product of
capital of 20%, next period's output rises by `0.2 × 0.5% = 0.1%` of output (equivalently,
capital share `0.2 × 3 = 0.6` times `0.167%`), **not** "less than 0.04 percent": the book
multiplied the percentage change in `K` by the MPK instead of by the capital share. -/
theorem p506_numbers :
    (0.005 : ℝ) / 3 < 0.002 ∧ (0.005 : ℝ) / 3 < 0.01 ∧
      (0.2 : ℝ) * 0.005 = 0.001 ∧ (0.2 * 3 : ℝ) * (0.005 / 3) = 0.001 ∧
      (0.0004 : ℝ) < 0.2 * 0.005 ∧ (0.2 : ℝ) * (0.005 / 3) < 0.0004 := by
  norm_num

end ObstfeldRogoff.GlobalGrowth.LogLinearRBC
