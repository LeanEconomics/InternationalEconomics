/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RealExchangeRate.DFSStatic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
# The current account in the Ricardian model: temporary productivity shocks

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §4.5.4,
pp. 243–248, and end-of-chapter Exercise 7, p. 266.

Bonds are indexed to the real consumption index. The current-account identities (46)–(47),
the Euler equation (48) (derived here as the first-order condition of the two-period slice of
(37)), the steady-state interest rate `r̄ = (1−β)/β` and steady-state consumption (49) are
exact. The response to a one-period, uniform Foreign productivity rise `a* ↦ a*/ν` is the
book's log-linear system: equations (50)–(54), footnote 37 and the two log-differentiated
cutoff conditions are collected as the hypotheses of `TemporaryShock` (the coefficients `4`,
`A′(1/2)` and `1 − β` are justified by exact derivative lemmas below), and (55)–(59), "half the
annuity value" and the Exercise 7 welfare results are derived from them.

Exercise 7: Home's lifetime-utility change is `dU = −A′(1/2)ν̂/(8 − 2A′(1/2))`, positive iff
`A′(1/2) < 0`; Foreign's is `ν̂/2 + ν̂/(2 − A′(1/2)/2) > 0`.
-/

namespace ObstfeldRogoff.RealExchangeRate.DFSCurrentAccount

open ObstfeldRogoff.RealExchangeRate.DFSStatic

/-- The steady-state world real interest rate, O&R p. 244: `r̄ = (1−β)/β`. -/
noncomputable def steadyRate (β : ℝ) : ℝ := (1 - β) / β

/-- The Home current account, O&R (46), p. 243, in units of the real consumption index:
`CA_t = w_t L / P_t + r_t B_t − C_t` (Foreign's (47) is the same map at starred arguments). -/
noncomputable def currentAccount (w L P r B C : ℝ) : ℝ := w * L / P + r * B - C

/-- O&R (46)–(47), p. 243: if bonds are in zero net supply (`B* = −B`) and world spending
equals world labour income (42), `P(C + C*) = wL + w*L*`, then `CA = −CA*`. -/
theorem currentAccount_home_eq_neg_foreign {w wS L LS P r B BS C CS : ℝ} (hP : P ≠ 0)
    (hB : BS = -B) (h42 : P * (C + CS) = w * L + wS * LS) :
    currentAccount w L P r B C = -currentAccount wS LS P r BS CS := by
  unfold currentAccount
  subst hB
  have : C + CS = (w * L + wS * LS) / P := by
    rw [← h42]; field_simp
  have e : w * L / P + wS * LS / P = C + CS := by rw [this]; ring
  linarith

/-- Euler equation (48), O&R p. 244: substituting (46) into (37), the two terms of `U_t` that
involve `B_{t+1} = b` are `log((1+r_t)B_t + y_t − b) + β log((1+r_{t+1})b − B_{t+2} + y_{t+1})`
(with `y = wL/P`); its derivative in `b` is `−1/C_t + β(1+r_{t+1})/C_{t+1}`. -/
theorem euler_objective_hasDerivAt {β r r' B B'' y y' b : ℝ}
    (hC : 0 < (1 + r) * B + y - b) (hC' : 0 < (1 + r') * b - B'' + y') :
    HasDerivAt
      (fun x => Real.log ((1 + r) * B + y - x) + β * Real.log ((1 + r') * x - B'' + y'))
      (-1 / ((1 + r) * B + y - b) + β * ((1 + r') / ((1 + r') * b - B'' + y'))) b := by
  have h1 : HasDerivAt (fun x => (1 + r) * B + y - x) (-1) b := by
    simpa using (hasDerivAt_id b).const_sub ((1 + r) * B + y)
  have h2 : HasDerivAt (fun x => (1 + r') * x - B'' + y') (1 + r') b := by
    have := ((hasDerivAt_id b).const_mul (1 + r')).sub_const B''
    simpa using this.add_const y'
  exact HasDerivAt.add (h1.log hC.ne') ((h2.log hC'.ne').const_mul β)

/-- Euler equation (48), O&R p. 244: the first-order condition
`−1/C_t + β(1+r_{t+1})/C_{t+1} = 0` holds iff `C_{t+1} = (1 + r_{t+1}) β C_t`. -/
theorem euler_foc_iff {β r' C C' : ℝ} (hC : 0 < C) (hC' : 0 < C') :
    -1 / C + β * ((1 + r') / C') = 0 ↔ C' = (1 + r') * β * C := by
  constructor
  · intro h
    field_simp at h
    linarith
  · intro h
    have hk : (1 + r') * β ≠ 0 := by
      intro h0; rw [h, h0, zero_mul] at hC'; exact lt_irrefl 0 hC'
    have h1 : 1 + r' ≠ 0 := left_ne_zero_of_mul hk
    have h2 : β ≠ 0 := right_ne_zero_of_mul hk
    rw [h]
    field_simp
    ring

/-- Steady-state interest rate, O&R p. 244: with constant positive consumption, the Euler
equation (48) holds iff `r = r̄ = (1−β)/β`. -/
theorem steady_rate_iff {β r C : ℝ} (hβ : 0 < β) (hC : 0 < C) :
    C = (1 + r) * β * C ↔ r = steadyRate β := by
  unfold steadyRate
  constructor
  · intro h
    have h1 : (1 + r) * β = 1 := by
      have := congrArg (· / C) h
      field_simp at this
      linarith
    field_simp
    linarith
  · intro h
    rw [h]
    field_simp
    ring

/-- Steady-state consumption, O&R (49), p. 244: in a steady state (`B_{t+1} = B_t = B̄`,
`r = r̄`), (46) gives `C̄ = r̄B̄ + w̄L/P̄`, and with `B̄* = −B̄`, `C̄* = −r̄B̄ + w̄*L*/P̄`. -/
theorem steady_consumption {β w wS L LS P B C CS : ℝ}
    (hCA : currentAccount w L P (steadyRate β) B C = 0)
    (hCAS : currentAccount wS LS P (steadyRate β) (-B) CS = 0) :
    C = steadyRate β * B + w * L / P ∧ CS = -(steadyRate β * B) + wS * LS / P := by
  unfold currentAccount at hCA hCAS
  constructor <;> linarith

/-- O&R (50), p. 245: steady-state wages and prices do not depend on the distribution of
wealth, so between two steady states with the same `w̄L/P̄`, (49) gives exactly
`dC̄ = r̄ dB̄`; starting from `B̄₀ = 0`, `Ĉ̄ = dC̄/C̄₀ = r̄ dB̄/C̄₀`. -/
theorem steady_consumption_change {β y B1 C0 C1 : ℝ} (hC0 : C0 = steadyRate β * 0 + y)
    (hC1 : C1 = steadyRate β * B1 + y) :
    (C1 - C0) / C0 = steadyRate β * B1 / C0 := by
  rw [show C1 - C0 = steadyRate β * B1 by rw [hC1, hC0]; ring]

/-- O&R (51), p. 245: the log of the Euler equation (48),
`log C_{t+1} = log(1 + r_{t+1}) + log β + log C_t`. -/
theorem log_euler {β r C C' : ℝ} (hβ : 0 < β) (hr : 0 < 1 + r) (hC : 0 < C)
    (h : C' = (1 + r) * β * C) :
    Real.log C' = Real.log (1 + r) + Real.log β + Real.log C := by
  rw [h, Real.log_mul (by positivity) hC.ne', Real.log_mul hr.ne' hβ.ne']

/-- O&R (51), p. 245: `d log(1+r)` at `r̄` is `dr/(1+r̄)`. -/
theorem log_one_add_rate_hasDerivAt {β : ℝ} (hβ : 0 < β) :
    HasDerivAt (fun r => Real.log (1 + r)) (1 / (1 + steadyRate β)) (steadyRate β) := by
  have hpos : 0 < 1 + steadyRate β := by
    unfold steadyRate
    rw [show 1 + (1 - β) / β = 1 / β by field_simp; ring]
    positivity
  have h := ((hasDerivAt_id (steadyRate β)).const_add 1).log hpos.ne'
  simpa using h

/-- O&R (51), p. 245: `dr/(1+r̄) = (1−β) r̂` with `r̂ = dr/r̄`, because `r̄/(1+r̄) = 1 − β`. -/
theorem steadyRate_div_one_add {β : ℝ} (hβ : 0 < β) :
    steadyRate β / (1 + steadyRate β) = 1 - β := by
  unfold steadyRate
  field_simp
  ring

/-- O&R p. 245: with `L = L*` and `A(1/2) = 1`, the symmetric initial cutoff is `z̄₀ = 1/2`:
it solves `A(z) = B(z; L*/L)`, and by T20 it is the unique cutoff. -/
theorem symmetric_cutoff {A : ℝ → ℝ} {L : ℝ} (hAc : ContinuousOn A (Set.Icc 0 1))
    (hA : StrictAntiOn A (Set.Icc 0 1)) (hpos : ∀ z ∈ Set.Icc (0 : ℝ) 1, 0 < A z)
    (hL : 0 < L) (hhalf : A (1 / 2) = 1) {z : ℝ} (hz : z ∈ Set.Ioo (0 : ℝ) 1)
    (heq : A z = relWageSchedule (L / L) z) : z = 1 / 2 := by
  have hsol : A (1 / 2) = relWageSchedule (L / L) (1 / 2) := by
    rw [hhalf, relWageSchedule, div_self hL.ne']; norm_num
  obtain ⟨z0, _, huniq⟩ := cutoff_exists_unique hAc hA hpos hL hL
  rw [huniq z ⟨hz, heq⟩, huniq (1 / 2) ⟨by norm_num, hsol⟩]

/-- O&R p. 247: log-differentiating (43) at the symmetric point (`z = 1/2`, `L = L*`):
`d log(z/(1−z)) = 4 dz`. -/
theorem log_odds_hasDerivAt_half :
    HasDerivAt (fun z => Real.log (z / (1 - z))) 4 (1 / 2) := by
  have h1 : HasDerivAt (fun z : ℝ => 1 - z) (-1) (1 / 2) := by
    simpa using (hasDerivAt_id (1 / 2 : ℝ)).const_sub 1
  have h2 : HasDerivAt (fun z : ℝ => z / (1 - z)) 4 (1 / 2) := by
    have := (hasDerivAt_id' (1 / 2 : ℝ)).div h1 (by norm_num)
    convert this using 1
    norm_num
  have h3 := h2.log (by norm_num)
  convert h3 using 1
  norm_num

/-- O&R p. 247: log-differentiating `w/w* = A(z̄)/ν` at `z̄ = 1/2`, `ν = 1`, with `A(1/2) = 1`:
`d log A(z̄) = A′(1/2) dz̄` and `d log(1/ν) = −ν̂`, so `ŵ − ŵ* = −ν̂ + A′(1/2) dz̄`. -/
theorem log_relProductivity_hasDerivAt_half {A : ℝ → ℝ} {A1 : ℝ}
    (hA : HasDerivAt A A1 (1 / 2)) (hhalf : A (1 / 2) = 1) :
    HasDerivAt (fun z => Real.log (A z)) A1 (1 / 2) ∧
      HasDerivAt (fun ν => Real.log (1 / ν)) (-1) 1 := by
  constructor
  · have h := hA.log (by rw [hhalf]; norm_num)
    rw [hhalf, div_one] at h
    exact h
  · have h := (hasDerivAt_inv (x := (1 : ℝ)) one_ne_zero).log (by norm_num)
    simpa using h

/-- Lifetime utility on the path of §4.5.4.2, O&R (37), p. 244: consumption `c₀` in the shock
period, then the new steady-state level `c̄` forever: `U = log c₀ + Σ_{s≥1} β^s log c̄`. -/
noncomputable def shockPathUtility (β c0 cbar : ℝ) : ℝ :=
  Real.log c0 + ∑' s : ℕ, β ^ (s + 1) * Real.log cbar

/-- O&R Exercise 7, p. 266: `Σ_{s≥1} β^s = β/(1−β) = 1/r̄`, so
`U = log c₀ + (1/r̄) log c̄` and the utility change is exactly
`dU = d log C + d log C̄ / r̄` (log differences). -/
theorem shockPathUtility_eq {β c0 cbar : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    shockPathUtility β c0 cbar = Real.log c0 + Real.log cbar / steadyRate β := by
  unfold shockPathUtility steadyRate
  have hs : ∑' s : ℕ, β ^ (s + 1) * Real.log cbar = β / (1 - β) * Real.log cbar := by
    simp_rw [pow_succ, mul_assoc]
    rw [tsum_mul_right, tsum_geometric_of_lt_one hβ0.le hβ1]
    have : (1 - β) ≠ 0 := by linarith
    field_simp
  rw [hs]
  have : (1 - β) ≠ 0 := by linarith
  field_simp

/-- The log-linear system of O&R §4.5.4.2, pp. 245–247, for an unexpected one-period Foreign
productivity rise `a* ↦ a*/ν` from the symmetric steady state (`L = L*`, `A(1/2) = 1`,
`z̄₀ = 1/2`, `B̄₀ = 0`). Hats are percentage deviations; `dB` is `dB̄/C̄₀`; `A1 = A′(1/2)`,
`ν = ν̂`. The fields are the book's equations (50)–(54), footnote 37's differential of (46),
and the log-differentials of `w/w* = A(z̄)/ν` and of (43). -/
structure TemporaryShock where
  β : ℝ
  A1 : ℝ
  ν : ℝ
  C : ℝ
  CS : ℝ
  Cbar : ℝ
  CSbar : ℝ
  r : ℝ
  w : ℝ
  wS : ℝ
  P : ℝ
  dz : ℝ
  dB : ℝ
  β_pos : 0 < β
  β_lt_one : β < 1
  eq50 : Cbar = (1 - β) / β * dB
  eq50S : CSbar = -((1 - β) / β * dB)
  eq51 : Cbar = (1 - β) * r + C
  eq52 : CSbar = (1 - β) * r + CS
  eq53 : (C + CS) / 2 = (w + wS) / 2 - P
  eq54 : P = (w + wS) / 2 - ν / 2
  fn37 : dB = w - P - C
  cutoffA : w - wS = -ν + A1 * dz
  cutoff43 : w - wS = 4 * dz

namespace TemporaryShock

/-- O&R p. 244: `1 + r̄ = 1/β > 0` along the system's discount factor. -/
theorem one_add_steadyRate_pos (s : TemporaryShock) : 0 < 1 + steadyRate s.β := by
  have hβ := s.β_pos
  have hβ1 := s.β_lt_one
  have : 0 < steadyRate s.β := div_pos (by linarith) hβ
  linarith

/-- O&R p. 246: world consumption rises by the percentage increase in world productivity,
`(Ĉ + Ĉ*)/2 = ν̂/2`. -/
theorem world_consumption (s : TemporaryShock) : (s.C + s.CS) / 2 = s.ν / 2 := by
  have := s.eq53; have := s.eq54; linarith

/-- O&R p. 246: adding (51) and (52) with `dC̄ + dC̄* = 0`, `2(1−β) r̂ = −(Ĉ + Ĉ*) = −ν̂`. -/
theorem rate_relation (s : TemporaryShock) : (1 - s.β) * s.r = -s.ν / 2 := by
  have h1 := s.eq50; have h2 := s.eq50S; have h3 := s.eq51; have h4 := s.eq52
  have hw := s.world_consumption
  linarith

/-- O&R (55), p. 246: the world real interest rate falls, `r̂ = −ν̂/(2(1−β))`. -/
theorem eq55 (s : TemporaryShock) : s.r = -s.ν / (2 * (1 - s.β)) := by
  have hb : 2 * (1 - s.β) ≠ 0 := by linarith [s.β_lt_one]
  rw [eq_div_iff hb]
  linear_combination 2 * s.rate_relation

/-- O&R (56), p. 247: `dB̄/C̄₀ = (ŵ − ŵ* + ν̂)/2 − Ĉ`. -/
theorem eq56 (s : TemporaryShock) : s.dB = (s.w - s.wS + s.ν) / 2 - s.C := by
  have := s.fn37; have := s.eq54; linarith

/-- O&R p. 247: combining the two log-differentiated cutoff conditions,
`(4 − A′(1/2)) dz̄ = −ν̂`. -/
theorem cutoff_relation (s : TemporaryShock) : s.dz * (4 - s.A1) = -s.ν := by
  linear_combination s.cutoffA - s.cutoff43

/-- O&R p. 247: the cutoff moves by `dz̄ = −ν̂/(4 − A′(1/2))`. -/
theorem cutoff_change (s : TemporaryShock) (hA : s.A1 ≠ 4) : s.dz = -s.ν / (4 - s.A1) := by
  have h4 : (4 - s.A1) ≠ 0 := sub_ne_zero.mpr (Ne.symm hA)
  rw [eq_div_iff h4]
  exact s.cutoff_relation

/-- O&R (57), p. 247: `ŵ − ŵ* = −ν̂/(1 − A′(1/2)/4)`: Home's relative wage falls, but by less
than `ν̂` when `A′(1/2) < 0`. -/
theorem eq57 (s : TemporaryShock) (hA : s.A1 ≠ 4) :
    s.w - s.wS = -s.ν / (1 - s.A1 / 4) := by
  have h4' : (1 - s.A1 / 4) ≠ 0 := by
    intro h; apply hA; linarith
  rw [eq_div_iff h4']
  linear_combination (1 - s.A1 / 4) * s.cutoff43 + s.cutoff_relation

/-- O&R p. 248 (first display): substituting (51) and (57) into (56),
`dB̄/C̄₀ = −A′(1/2)ν̂/(8 − 2A′(1/2)) − Ĉ̄ + (1−β) r̂`. -/
theorem eq58_pre (s : TemporaryShock) (hA : s.A1 ≠ 4) :
    s.dB = -s.A1 * s.ν / (8 - 2 * s.A1) - s.Cbar + (1 - s.β) * s.r := by
  have h56 := s.eq56
  have h51 := s.eq51
  have h8 : (8 - 2 * s.A1) ≠ 0 := by intro h; apply hA; linarith
  have e : (s.w - s.wS + s.ν) / 2 = -s.A1 * s.ν / (8 - 2 * s.A1) := by
    rw [eq_div_iff h8]
    linear_combination (4 - s.A1) * s.cutoff43 + 4 * s.cutoff_relation
  linarith

/-- O&R p. 248: `(1 + r̄) dB̄/C̄₀ = (ŵ − ŵ*)/2`. -/
theorem bond_relation (s : TemporaryShock) : s.dB * (1 + steadyRate s.β) = (s.w - s.wS) / 2 := by
  have h56 := s.eq56
  have h51 := s.eq51
  have h50 := s.eq50
  have hr := s.rate_relation
  unfold steadyRate
  linarith

/-- O&R (58), p. 248: `dB̄/C̄₀ = −ν̂/((1 + r̄)[2 − A′(1/2)/2])`. -/
theorem eq58 (s : TemporaryShock) (hA : s.A1 ≠ 4) :
    s.dB = -s.ν / ((1 + steadyRate s.β) * (2 - s.A1 / 2)) := by
  have h2 : (2 - s.A1 / 2) ≠ 0 := by intro h; apply hA; linarith
  have hden : (1 + steadyRate s.β) * (2 - s.A1 / 2) ≠ 0 :=
    mul_ne_zero s.one_add_steadyRate_pos.ne' h2
  rw [eq_div_iff hden]
  linear_combination (2 - s.A1 / 2) * s.bond_relation + (1 / 4) * (4 - s.A1) * s.cutoff43 +
    s.cutoff_relation

/-- O&R (58), p. 248: for `ν̂ > 0` and `A′(1/2) < 4` (in particular `A′ < 0`), Home runs a
current-account deficit, and Foreign the matching surplus `dB̄*/C̄₀ = −dB̄/C̄₀ > 0`. -/
theorem current_account_deficit (s : TemporaryShock) (hA : s.A1 < 4) (hν : 0 < s.ν) :
    s.dB < 0 ∧ 0 < -s.dB := by
  rw [s.eq58 hA.ne]
  have hr := s.one_add_steadyRate_pos
  have h2 : 0 < 2 - s.A1 / 2 := by linarith
  have : 0 < s.ν / ((1 + steadyRate s.β) * (2 - s.A1 / 2)) := by positivity
  constructor <;> rw [neg_div] <;> linarith

/-- O&R (59), p. 248: long-run consumption changes
`Ĉ̄* = r̄ν̂/((1 + r̄)[2 − A′(1/2)/2]) = −Ĉ̄`. -/
theorem eq59 (s : TemporaryShock) (hA : s.A1 ≠ 4) :
    s.CSbar = steadyRate s.β * s.ν / ((1 + steadyRate s.β) * (2 - s.A1 / 2)) ∧
      s.CSbar = -s.Cbar := by
  constructor
  · rw [s.eq50S, s.eq58 hA]
    unfold steadyRate
    ring
  · rw [s.eq50S, s.eq50]

/-- O&R p. 248, "half the annuity value": Foreign's long-run consumption gain is half the
annuity value `r̄X/(1+r̄)` of its one-period relative income gain `X = ŵ* − ŵ` (the annuity
value of a one-off gain `X` at date `t` is the constant flow from `t` on with the same
present value). -/
theorem half_annuity (s : TemporaryShock) (hA : s.A1 ≠ 4) :
    s.CSbar = 1 / 2 * (steadyRate s.β / (1 + steadyRate s.β)) * (s.wS - s.w) := by
  rw [(s.eq59 hA).1, show s.wS - s.w = -(s.w - s.wS) by ring, s.eq57 hA,
    show (2 - s.A1 / 2) = 2 * (1 - s.A1 / 4) by ring]
  have h4' : (1 - s.A1 / 4) ≠ 0 := by
    intro h; apply hA; linarith
  have hr := s.one_add_steadyRate_pos.ne'
  field_simp

/-- Home's welfare change, O&R Exercise 7, p. 266: with `U = log C + (1/r̄) log C̄`
(`shockPathUtility_eq`), `dU = Ĉ + Ĉ̄/r̄ = −A′(1/2)ν̂/(8 − 2A′(1/2))`. -/
theorem home_welfare (s : TemporaryShock) (hA : s.A1 ≠ 4) :
    s.C + s.Cbar / steadyRate s.β = -s.A1 * s.ν / (8 - 2 * s.A1) := by
  have hpre := s.eq58_pre hA
  have h51 := s.eq51
  have hβ := s.β_pos
  have hrne : steadyRate s.β ≠ 0 := (div_pos (by linarith [s.β_lt_one]) hβ).ne'
  have e : s.Cbar / steadyRate s.β = s.dB := by
    rw [s.eq50, show (1 - s.β) / s.β = steadyRate s.β from rfl]
    field_simp
  rw [e]
  linarith

/-- O&R Exercise 7, p. 266 (and p. 248): for `ν̂ > 0` and `A′(1/2) < 4`, the temporary Foreign
productivity rise raises Home's lifetime utility iff `A′(1/2) < 0`; in particular it does so
under the book's assumption `A′ < 0`. -/
theorem home_welfare_pos_iff (s : TemporaryShock) (hA : s.A1 < 4) (hν : 0 < s.ν) :
    0 < s.C + s.Cbar / steadyRate s.β ↔ s.A1 < 0 := by
  rw [s.home_welfare hA.ne]
  have h8 : 0 < 8 - 2 * s.A1 := by linarith
  rw [lt_div_iff₀ h8, zero_mul]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith

/-- Foreign's welfare change, O&R p. 248 and Exercise 7:
`dU* = Ĉ* + Ĉ̄*/r̄ = ν̂/2 + ν̂/(2 − A′(1/2)/2)`. -/
theorem foreign_welfare (s : TemporaryShock) (hA : s.A1 ≠ 4) :
    s.CS + s.CSbar / steadyRate s.β = s.ν / 2 + s.ν / (2 - s.A1 / 2) := by
  have hw := s.world_consumption
  have hH := s.home_welfare hA
  have h2 : (2 - s.A1 / 2) ≠ 0 := by intro h; apply hA; linarith
  have e : s.CSbar / steadyRate s.β = -(s.Cbar / steadyRate s.β) := by
    rw [(s.eq59 hA).2, neg_div]
  have e2 : s.ν / 2 + s.ν / (2 - s.A1 / 2) = s.ν - -s.A1 * s.ν / (8 - 2 * s.A1) := by
    have h4 : (4 - s.A1) ≠ 0 := sub_ne_zero.mpr (Ne.symm hA)
    have h8 : (8 - 2 * s.A1) ≠ 0 := by intro h; apply hA; linarith
    rw [eq_sub_iff_add_eq, div_add_div _ _ two_ne_zero h2,
      div_add_div _ _ (mul_ne_zero two_ne_zero h2) h8,
      div_eq_iff (mul_ne_zero (mul_ne_zero two_ne_zero h2) h8)]
    ring
  rw [e, e2]
  linarith

/-- O&R p. 248: Foreign is better off, `dU* > 0`, for `ν̂ > 0` and `A′(1/2) < 4`. -/
theorem foreign_welfare_pos (s : TemporaryShock) (hA : s.A1 < 4) (hν : 0 < s.ν) :
    0 < s.CS + s.CSbar / steadyRate s.β := by
  rw [s.foreign_welfare hA.ne]
  have h2 : 0 < 2 - s.A1 / 2 := by linarith
  positivity

end TemporaryShock

end ObstfeldRogoff.RealExchangeRate.DFSCurrentAccount
