/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import MoneyExchangeRates.MoneyInUtility
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.PSeries

/-!
# Speculative bubbles in the money-in-the-utility model

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §8.3.5
(pp. 538–546) and Exercise 2 (pp. 599–600).

With `u = log C + v(M/P)` (45), `(1+r)β = 1` and money growing at `1 + μ`, real balances obey
(46): `(β/(1+μ)) m_{t+1} = m_t(1 − C̄v'(m_t))`. We prove:

* **equilibrium ⟺ (46) + the individual TVC** (`equilibrium_iff`): a price path supports the
  equilibrium plan (optimal for the household, via `MoneyInUtility.isOptimal_iff`) iff (46)
  holds at every date and `liminf β^T m_T = 0` (fn 31);
* **the log case with money growth** (Fig. 8.2): the explicit saddle-path solution; paths below
  the steady state reach NEGATIVE real balances in finite time (so they are infeasible, not
  merely divergent); `β^T m_T = β^T m̄ + (1+μ)^T(m_0 − m̄)`; the steady state is the UNIQUE
  equilibrium when `μ ≥ 0` and is an equilibrium whenever `1 + μ > β`; but when
  `β < 1 + μ < 1` EVERY `m_0 ≥ m̄` is an equilibrium (a correction: the book's TVC argument
  needs `μ ≥ 0`);
* (48) and **(49) ⟺ (50)**; for general concave `v` with constant money, deflationary paths
  grow geometrically and `β^T m_T = m_0 Π(1 − C̄v'(m_s))`, so **the TVC holds iff
  `Σ v'(m_t) = ∞`** (`tvc_iff_not_summable`). If `v` is bounded above the sum is finite and
  deflations are ruled out (fn 32, made precise); so too for `v = log`. **Counterexamples**:
  `v = am + log m` and the logarithmic-integral utility `v(m) = ∫₀^m dt/log(t+e)`
  (`v' ≈ 1/log m`) are strictly concave, increasing and unbounded, and admit GENUINE
  deflationary-bubble equilibria (`linlog_deflation_equilibrium`,
  `logInt_deflation_equilibrium`);
* **hyperinflations** (§8.3.5.4): fn 34 (`(54) ⇒ v(0+) = −∞`), its sharpened contrapositive
  (`v` bounded below ⇒ (52)), and a counterexample to the converse
  (`v = −log(1 + log(1 + 1/m))`); the precise Fig. 8.3: for every collapse date `T` a unique
  initial price level, converging to the steady state as `T → ∞` (`backOrbit_*`); and
  asymptotic hyperinflation with no collapse date when `C̄v' < 1` everywhere;
* **fractional backing** (§8.3.5.5): every positive path starting below the steady state falls
  to zero, hence below any floor `M̄/P^MIN`;
* **Exercise 2**: the first-order conditions of the transactions-technology models (a) and (c)
  derived from optimality, the dynamics and steady state (b), and (d): deflations are ruled
  out (`g` bounded) while hyperinflations are not (`g(0+)` finite gives (52)).
-/

namespace ObstfeldRogoff.MoneyExchangeRates.MonetaryBubbles

open Real Filter Topology Set
open ObstfeldRogoff.MoneyExchangeRates.MoneyInUtility

/-! ## The difference equation for real balances (46) -/

/-- With `(1+r)β = 1` the user cost of money is `1 − β P_s/P_{s+1}` (O&R p. 538). -/
theorem userCost_of_beta {r β : ℝ} {P : ℕ → ℝ} (hβr : (1 + r) * β = 1) (s : ℕ) :
    userCost r P s = 1 - β * (P s / P (s + 1)) := by
  have hβ : β = (1 + r)⁻¹ := by
    have h1 : 1 + r ≠ 0 := by intro h; rw [h, zero_mul] at hβr; exact zero_ne_one hβr
    field_simp; linarith
  unfold userCost
  rw [hβ]
  ring

/-- **The dynamics of real balances (46)**, O&R p. 538: with money growing at the gross rate
`1 + μ` (`N_{s+1} = (1+μ)N_s`, `N_s` the money brought into date `s`) and real balances
`m_s = N_{s+1}/P_s`, the money-demand condition `h(m_s) = 1 − β P_s/P_{s+1}` holds iff
`(β/(1+μ)) m_{s+1} = m_s (1 − h(m_s))`. For MIU preferences `h = C̄ v'`; in Exercise 2
`h = Y g'`. -/
theorem bubble_dynamics_iff {β μ : ℝ} {N P : ℕ → ℝ} {h : ℝ → ℝ} (hμ : 0 < 1 + μ)
    (hN : ∀ s, 0 < N s) (hP : ∀ s, 0 < P s) (hgrowth : ∀ s, N (s + 1) = (1 + μ) * N s)
    (s : ℕ) :
    h (N (s + 1) / P s) = 1 - β * (P s / P (s + 1)) ↔
      β / (1 + μ) * (N (s + 1 + 1) / P (s + 1)) =
        N (s + 1) / P s * (1 - h (N (s + 1) / P s)) := by
  have hPs := (hP s).ne'
  have hPs1 := (hP (s + 1)).ne'
  have hm : 0 < N (s + 1) / P s := div_pos (hN _) (hP s)
  have key : β / (1 + μ) * (N (s + 1 + 1) / P (s + 1)) =
      N (s + 1) / P s * (β * (P s / P (s + 1))) := by
    rw [hgrowth (s + 1)]; field_simp
  rw [key]
  constructor
  · intro h1; rw [h1]; ring
  · intro h1
    have := mul_left_cancel₀ hm.ne' h1
    linarith

/-! ## Equilibrium: the Euler equation plus the transversality condition -/

/-- The individual transversality condition of fn 31, O&R p. 542, in its exact (liminf) form:
`liminf β^T m_T ≤ 0` (with constant consumption `C̄`). -/
def BubbleTVC (β : ℝ) (m : ℕ → ℝ) : Prop := ∀ ε > 0, ∃ᶠ T in atTop, β ^ T * m T < ε

/-- Along the candidate equilibrium plan (constant consumption `C̄ = Ȳ + rB_0`, bonds constant,
transfers (43) rebating seignorage), financial wealth is `(1+r)B_0 + N_s/P_s` (O&R §8.3.4–8.3.5). -/
theorem candidate_wealth {r Ybar B0 : ℝ} {N P : ℕ → ℝ} (hr : 0 < 1 + r) (hP : ∀ s, 0 < P s)
    (s : ℕ) :
    wealth r ((1 + r) * B0 + N 0 / P 0) (fun s => Ybar + (N (s + 1) - N s) / P s) (userCost r P)
      (fun _ => Ybar + r * B0) (fun s => N (s + 1) / P s) s = (1 + r) * B0 + N s / P s := by
  induction s with
  | zero => rfl
  | succ s ih =>
    rw [wealth_succ, ih]
    have hPs := (hP s).ne'
    have hPs1 := (hP (s + 1)).ne'
    unfold userCost
    field_simp
    ring

/-- **Equilibrium ⟺ (46) and the transversality condition** (O&R §8.3.5.1 and §8.3.5.3, made
exact). Consider the small open economy with `u = log C + v(M/P)` (45), `v` concave and
differentiable, `(1+r)β = 1`, `0 < β < 1`, constant output `Ȳ`, initial bonds `B_0`, zero
government spending and seignorage rebated as transfers (43), and money growing at `1 + μ`.
A positive price path `P` supports the equilibrium plan (constant consumption `C̄ = Ȳ + rB_0`,
real balances `m_s = N_{s+1}/P_s`) — i.e. that plan is OPTIMAL for the household at those
prices — iff real balances satisfy (46) at every date and the individual TVC (fn 31)
`liminf β^T m_T = 0` holds. (Summability of lifetime utility is assumed.) -/
theorem equilibrium_iff {v v' : ℝ → ℝ} {β r μ Ybar B0 : ℝ} {N P : ℕ → ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (hβr : (1 + r) * β = 1) (hμ : 0 < 1 + μ) (hC : 0 < Ybar + r * B0)
    (hN : ∀ s, 0 < N s) (hP : ∀ s, 0 < P s) (hgrowth : ∀ s, N (s + 1) = (1 + μ) * N s)
    (hv : ConcaveOn ℝ (Set.Ioi 0) v) (hv' : ∀ k, 0 < k → HasDerivAt v (v' k) k)
    (hsum : Summable (fun s => β ^ s * (Real.log (Ybar + r * B0) + v (N (s + 1) / P s)))) :
    IsOptimal (fun c k => Real.log c + v k) β r ((1 + r) * B0 + N 0 / P 0)
        (fun s => Ybar + (N (s + 1) - N s) / P s) (userCost r P) (fun _ => Ybar + r * B0)
        (fun s => N (s + 1) / P s) ↔
      (∀ s, β / (1 + μ) * (N (s + 1 + 1) / P (s + 1)) =
        N (s + 1) / P s * (1 - (Ybar + r * B0) * v' (N (s + 1) / P s))) ∧
      BubbleTVC β (fun s => N (s + 1) / P s) := by
  set Cbar := Ybar + r * B0 with hCbar
  have hr : 0 < 1 + r := by
    by_contra h; push Not at h; nlinarith
  have hd : (1 + r)⁻¹ = β := by field_simp; linarith
  have hwealth : ∀ T, (1 + r)⁻¹ ^ T * wealth r ((1 + r) * B0 + N 0 / P 0)
      (fun s => Ybar + (N (s + 1) - N s) / P s) (userCost r P) (fun _ => Cbar)
      (fun s => N (s + 1) / P s) T =
        (1 + r) * B0 * β ^ T + β ^ T * (N (T + 1) / P T) / (1 + μ) := by
    intro T
    rw [candidate_wealth hr hP T, hd, hgrowth T]
    have := (hP T).ne'
    field_simp
  have hβT : Tendsto (fun T : ℕ => (1 + r) * B0 * β ^ T) atTop (𝓝 0) := by
    have := (tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).const_mul ((1 + r) * B0)
    rwa [mul_zero] at this
  have hmpos : ∀ T, 0 < β ^ T * (N (T + 1) / P T) / (1 + μ) := fun T => by
    have := hN (T + 1); have := hP T; positivity
  rw [logSeparable_isOptimal_iff hβ0 hr hv hv']
  constructor
  · rintro ⟨_, _, hmo, htvc⟩
    refine ⟨fun s => ?_, fun ε hε => ?_⟩
    · have h1 := hmo s
      rw [userCost_of_beta hβr] at h1
      refine (bubble_dynamics_iff (h := fun k => Cbar * v' k) hμ hN hP hgrowth s).1 ?_
      rw [h1]
      field_simp
    · have h2 := htvc (ε / (1 + μ) / 2) (by positivity)
      have h3 := hβT.eventually (gt_mem_nhds (show (0 : ℝ) < ε / (1 + μ) / 2 by positivity))
      have h4 := hβT.eventually (lt_mem_nhds (show -(ε / (1 + μ) / 2) < 0 by
        have : 0 < ε / (1 + μ) / 2 := by positivity
        linarith))
      refine (h2.and_eventually (h3.and h4)).mono fun T ⟨hT, _, hT4⟩ => ?_
      rw [hwealth T] at hT
      have : β ^ T * (N (T + 1) / P T) / (1 + μ) < ε / (1 + μ) := by linarith
      rwa [div_lt_div_iff_of_pos_right hμ] at this
  · rintro ⟨hdyn, htvc⟩
    refine ⟨⟨fun _ => hC, fun s => div_pos (hN _) (hP s), hsum, fun ε hε => ?_⟩,
      fun _ => by rw [hβr, one_mul], fun s => ?_, fun ε hε => ?_⟩
    · filter_upwards [hβT.eventually (lt_mem_nhds (show -ε < 0 by linarith))] with T hT
      rw [hwealth T]
      linarith [hmpos T]
    · have h1 := (bubble_dynamics_iff (h := fun k => Cbar * v' k) hμ hN hP hgrowth s).2 (hdyn s)
      rw [userCost_of_beta hβr, ← h1]
      field_simp
    · have h2 := htvc (ε * (1 + μ) / 2) (by positivity)
      have h3 := hβT.eventually (gt_mem_nhds (show (0 : ℝ) < ε / 2 by positivity))
      refine (h2.and_eventually h3).mono fun T ⟨hT, hT3⟩ => ?_
      rw [hwealth T]
      have : β ^ T * (N (T + 1) / P T) / (1 + μ) < ε / 2 := by
        rw [div_lt_iff₀ hμ]; linarith
      linarith

/-! ## The logarithmic case (Figure 8.2), with money growth -/

/-- The steady-state level of real balances, O&R p. 539: `M/P‾ = C̄/(1 − β/(1+μ))`. -/
noncomputable def mbar (β μ Cbar : ℝ) : ℝ := Cbar / (1 - β / (1 + μ))

/-- **(46) for `v = log`**, O&R p. 539: `(β/(1+μ)) m_{t+1} = m_t(1 − C̄/m_t)` iff
`m_{t+1} = ((1+μ)/β)(m_t − C̄)`. -/
theorem log_dynamics_iff {β μ Cbar m0 m1 : ℝ} (hβ : 0 < β) (hμ : 0 < 1 + μ) (hm0 : 0 < m0) :
    β / (1 + μ) * m1 = m0 * (1 - Cbar * m0⁻¹) ↔ m1 = (1 + μ) / β * (m0 - Cbar) := by
  constructor <;> intro h
  · field_simp at h ⊢; linarith
  · rw [h]; field_simp

/-- **The saddle-path solution of the log case**, O&R Fig. 8.2: every solution of
`m_{t+1} = ((1+μ)/β)(m_t − C̄)` is `m_t = M/P‾ + ((1+μ)/β)^t (m_0 − M/P‾)`. -/
theorem log_orbit {β μ Cbar : ℝ} {m : ℕ → ℝ} (hβ : 0 < β) (hμ : 0 < 1 + μ) (hβμ : β < 1 + μ)
    (hdyn : ∀ t, m (t + 1) = (1 + μ) / β * (m t - Cbar)) (t : ℕ) :
    m t = mbar β μ Cbar + ((1 + μ) / β) ^ t * (m 0 - mbar β μ Cbar) := by
  have h1 : 1 + μ - β ≠ 0 := by linarith
  have hm : mbar β μ Cbar = Cbar * (1 + μ) / (1 + μ - β) := by
    unfold mbar
    rw [show 1 - β / (1 + μ) = (1 + μ - β) / (1 + μ) by field_simp]
    field_simp
  have hfix : (1 + μ) / β * (mbar β μ Cbar - Cbar) = mbar β μ Cbar := by
    rw [hm]
    field_simp
    ring
  induction t with
  | zero => simp
  | succ t ih =>
    rw [hdyn t, ih, pow_succ]
    linear_combination hfix

/-- **(a) Hyperinflationary paths are infeasible in the log case**, O&R p. 539 (made precise):
with `1 + μ > β`, a solution starting below the steady state reaches NEGATIVE real balances in
finite time, so every solution with positive real balances at all dates starts at or above
`M/P‾`. -/
theorem log_no_hyperinflation {β μ Cbar : ℝ} {m : ℕ → ℝ} (hβ : 0 < β) (hμ : 0 < 1 + μ)
    (hβμ : β < 1 + μ) (hdyn : ∀ t, m (t + 1) = (1 + μ) / β * (m t - Cbar))
    (hpos : ∀ t, 0 < m t) : mbar β μ Cbar ≤ m 0 := by
  by_contra hlt
  push Not at hlt
  have hlam : 1 < (1 + μ) / β := (one_lt_div hβ).2 hβμ
  obtain ⟨t, ht⟩ := ((tendsto_pow_atTop_atTop_of_one_lt hlam).eventually
    (eventually_gt_atTop (mbar β μ Cbar / (mbar β μ Cbar - m 0)))).exists
  have hd : 0 < mbar β μ Cbar - m 0 := by linarith
  have h1 := log_orbit hβ hμ hβμ hdyn t
  have h2 := hpos t
  rw [div_lt_iff₀ hd] at ht
  nlinarith

/-- **(b) The TVC along deflationary paths**, O&R pp. 542–543 with money growth:
`β^T m_T = β^T M/P‾ + (1+μ)^T (m_0 − M/P‾)`. -/
theorem log_discounted_balances {β μ Cbar : ℝ} {m : ℕ → ℝ} (hβ : 0 < β) (hμ : 0 < 1 + μ)
    (hβμ : β < 1 + μ) (hdyn : ∀ t, m (t + 1) = (1 + μ) / β * (m t - Cbar)) (T : ℕ) :
    β ^ T * m T = β ^ T * mbar β μ Cbar + (1 + μ) ^ T * (m 0 - mbar β μ Cbar) := by
  rw [log_orbit hβ hμ hβμ hdyn T, div_pow]
  have := pow_pos hβ T
  field_simp

/-- **(c) Uniqueness for `μ ≥ 0`**, O&R pp. 539–543 (made precise): with nonnegative money
growth, the only positive solution of the log-case dynamics that satisfies the individual TVC
is the steady state `m_t = M/P‾` for all `t`. -/
theorem log_unique_of_nonneg_growth {β μ Cbar : ℝ} {m : ℕ → ℝ} (hβ : 0 < β) (hμ0 : 0 ≤ μ)
    (hβμ : β < 1 + μ) (hC : 0 < Cbar) (hdyn : ∀ t, m (t + 1) = (1 + μ) / β * (m t - Cbar))
    (hpos : ∀ t, 0 < m t) (htvc : BubbleTVC β m) : ∀ t, m t = mbar β μ Cbar := by
  have hμ : 0 < 1 + μ := by linarith
  have hge := log_no_hyperinflation hβ hμ hβμ hdyn hpos
  have heq : m 0 = mbar β μ Cbar := by
    by_contra hne
    have hgt : 0 < m 0 - mbar β μ Cbar := by
      rcases lt_or_gt_of_ne hne with h | h
      · linarith
      · linarith
    obtain ⟨T, hT⟩ := (htvc (m 0 - mbar β μ Cbar) hgt).exists
    rw [log_discounted_balances hβ hμ hβμ hdyn T] at hT
    have h1 : 0 ≤ β ^ T * mbar β μ Cbar := by
      have : β / (1 + μ) < 1 := (div_lt_one hμ).2 hβμ
      exact mul_nonneg (pow_pos hβ T).le (div_pos hC (by linarith)).le
    have h2 : 1 ≤ (1 + μ) ^ T := one_le_pow₀ (by linarith)
    nlinarith
  intro t
  rw [log_orbit hβ hμ hβμ hdyn t, heq, sub_self, mul_zero, add_zero]

/-- **(d) Deflationary bubbles when `β < 1 + μ < 1`** (a correction to O&R pp. 541–543, whose
argument assumes constant money): with money shrinking at a rate below the rate of time
preference, EVERY initial real balance `m_0 ≥ M/P‾` generates a positive path satisfying the
individual TVC, `β^T m_T → 0`. -/
theorem log_deflation_tvc {β μ Cbar : ℝ} {m : ℕ → ℝ} (hβ : 0 < β) (hβμ : β < 1 + μ)
    (hμ1 : 1 + μ < 1) (hC : 0 < Cbar) (hdyn : ∀ t, m (t + 1) = (1 + μ) / β * (m t - Cbar))
    (hm0 : mbar β μ Cbar ≤ m 0) :
    (∀ t, 0 < m t) ∧ Tendsto (fun T => β ^ T * m T) atTop (𝓝 0) := by
  have hμ : 0 < 1 + μ := by linarith
  have hmbar : 0 < mbar β μ Cbar := by
    unfold mbar
    have : β / (1 + μ) < 1 := (div_lt_one hμ).2 hβμ
    exact div_pos hC (by linarith)
  have hlam : 1 ≤ (1 + μ) / β := by rw [le_div_iff₀ hβ]; linarith
  refine ⟨fun t => ?_, ?_⟩
  · rw [log_orbit hβ hμ hβμ hdyn t]
    have := one_le_pow₀ hlam (n := t)
    nlinarith
  · have h1 : Tendsto (fun T : ℕ => β ^ T * mbar β μ Cbar + (1 + μ) ^ T * (m 0 - mbar β μ Cbar))
        atTop (𝓝 (0 * mbar β μ Cbar + 0 * (m 0 - mbar β μ Cbar))) :=
      ((tendsto_pow_atTop_nhds_zero_of_lt_one hβ.le (by linarith)).mul_const _).add
        ((tendsto_pow_atTop_nhds_zero_of_lt_one hμ.le hμ1).mul_const _)
    simp only [zero_mul, add_zero] at h1
    exact h1.congr fun T => (log_discounted_balances hβ hμ hβμ hdyn T).symm

/-- The log-case dynamics are (46) for `v = log` (O&R p. 539), as a statement about a price path
through `m_s = N_{s+1}/P_s`. -/
theorem log_dynamics_path {β μ Cbar : ℝ} {N P : ℕ → ℝ} (hβ : 0 < β) (hμ : 0 < 1 + μ)
    (hN : ∀ s, 0 < N s) (hP : ∀ s, 0 < P s) :
    (∀ s, β / (1 + μ) * (N (s + 1 + 1) / P (s + 1)) =
        N (s + 1) / P s * (1 - Cbar * (N (s + 1) / P s)⁻¹)) ↔
      ∀ s, N (s + 1 + 1) / P (s + 1) = (1 + μ) / β * (N (s + 1) / P s - Cbar) :=
  forall_congr' fun s => log_dynamics_iff hβ hμ (div_pos (hN _) (hP s))

/-- **Existence: the steady state is an equilibrium** (O&R p. 539 and p. 538, log case): with
`1 + μ > β` the constant real-balance path `M/P_s = M/P‾` (price level `P_s = N_{s+1}/M/P‾`,
growing at `1 + μ`) is an equilibrium. -/
theorem log_steady_state_equilibrium {β r μ Ybar B0 : ℝ} {N : ℕ → ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (hβr : (1 + r) * β = 1) (hβμ : β < 1 + μ) (hC : 0 < Ybar + r * B0)
    (hN : ∀ s, 0 < N s) (hgrowth : ∀ s, N (s + 1) = (1 + μ) * N s) :
    IsOptimal (fun c k => Real.log c + Real.log k) β r
      ((1 + r) * B0 + N 0 / (N 1 / mbar β μ (Ybar + r * B0)))
      (fun s => Ybar + (N (s + 1) - N s) / (N (s + 1) / mbar β μ (Ybar + r * B0)))
      (userCost r (fun s => N (s + 1) / mbar β μ (Ybar + r * B0))) (fun _ => Ybar + r * B0)
      (fun s => N (s + 1) / (N (s + 1) / mbar β μ (Ybar + r * B0))) := by
  have hμ : 0 < 1 + μ := by linarith
  set mb := mbar β μ (Ybar + r * B0) with hmb
  have hmb0 : 0 < mb := by
    have : β / (1 + μ) < 1 := (div_lt_one hμ).2 hβμ
    exact div_pos hC (by linarith)
  have hP : ∀ s, 0 < N (s + 1) / mb := fun s => div_pos (hN _) hmb0
  have hm : ∀ s, N (s + 1) / (N (s + 1) / mb) = mb := fun s => by
    have := (hN (s + 1)).ne'; field_simp
  have hsum : Summable (fun s => β ^ s * (Real.log (Ybar + r * B0) +
      Real.log (N (s + 1) / (N (s + 1) / mb)))) := by
    simp only [hm]
    exact (summable_geometric_of_lt_one hβ0.le hβ1).mul_right _
  refine (equilibrium_iff (v' := fun k => k⁻¹) hβ0 hβ1 hβr hμ hC hN hP hgrowth
    strictConcaveOn_log_Ioi.concaveOn (fun k hk => Real.hasDerivAt_log hk.ne') hsum).2 ⟨?_, ?_⟩
  · intro s
    simp only [hm]
    rw [(log_dynamics_iff hβ0 hμ hmb0)]
    have h1 : 1 + μ - β ≠ 0 := by linarith
    have hm' : mb = (Ybar + r * B0) * (1 + μ) / (1 + μ - β) := by
      rw [hmb]; unfold mbar
      rw [show 1 - β / (1 + μ) = (1 + μ - β) / (1 + μ) by field_simp]
      field_simp
    rw [hm']
    field_simp
    ring
  · intro ε hε
    simp only [hm]
    exact ((tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).mul_const mb |>.eventually
      (gt_mem_nhds (by rw [zero_mul]; exact hε))).frequently

/-- **Uniqueness for `μ ≥ 0`**, O&R §8.3.5 (made precise, log case): if money grows at a
nonnegative rate, the ONLY equilibrium price path is the steady state `M/P_s = M/P‾`:
hyperinflationary paths reach negative real balances and deflationary paths violate the
individual transversality condition. -/
theorem log_equilibrium_unique {β r μ Ybar B0 : ℝ} {N P : ℕ → ℝ} (hβ0 : 0 < β) (hβ1 : β < 1)
    (hβr : (1 + r) * β = 1) (hμ0 : 0 ≤ μ) (hC : 0 < Ybar + r * B0) (hN : ∀ s, 0 < N s)
    (hP : ∀ s, 0 < P s) (hgrowth : ∀ s, N (s + 1) = (1 + μ) * N s)
    (hopt : IsOptimal (fun c k => Real.log c + Real.log k) β r ((1 + r) * B0 + N 0 / P 0)
        (fun s => Ybar + (N (s + 1) - N s) / P s) (userCost r P) (fun _ => Ybar + r * B0)
        (fun s => N (s + 1) / P s)) :
    ∀ s, N (s + 1) / P s = mbar β μ (Ybar + r * B0) := by
  have hμ : 0 < 1 + μ := by linarith
  have hβμ : β < 1 + μ := by linarith
  have hsum := hopt.1.2.2.1
  obtain ⟨hdyn, htvc⟩ := (equilibrium_iff (v' := fun k => k⁻¹) hβ0 hβ1 hβr hμ hC hN hP hgrowth
    strictConcaveOn_log_Ioi.concaveOn (fun k hk => Real.hasDerivAt_log hk.ne') hsum).1 hopt
  exact log_unique_of_nonneg_growth (m := fun s => N (s + 1) / P s) hβ0 hμ0 hβμ hC
    ((log_dynamics_path hβ0 hμ hN hP).1 hdyn) (fun s => div_pos (hN _) (hP s)) htvc

/-- **A continuum of deflationary equilibria when `β < 1 + μ < 1`** (a correction to O&R
§8.3.5.3, whose TVC argument needs `μ ≥ 0`): for every `m_0 ≥ M/P‾` the price path
`P_s = N_{s+1}/m_s`, `m_s = M/P‾ + ((1+μ)/β)^s (m_0 − M/P‾)`, is an equilibrium. -/
theorem log_equilibria_multiple {β r μ Ybar B0 m0 : ℝ} {N : ℕ → ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (hβr : (1 + r) * β = 1) (hβμ : β < 1 + μ) (hμ1 : 1 + μ < 1)
    (hC : 0 < Ybar + r * B0) (hN : ∀ s, 0 < N s) (hgrowth : ∀ s, N (s + 1) = (1 + μ) * N s)
    (hm0 : mbar β μ (Ybar + r * B0) ≤ m0) :
    let m : ℕ → ℝ := fun s => mbar β μ (Ybar + r * B0) +
      ((1 + μ) / β) ^ s * (m0 - mbar β μ (Ybar + r * B0))
    IsOptimal (fun c k => Real.log c + Real.log k) β r ((1 + r) * B0 + N 0 / (N 1 / m 0))
      (fun s => Ybar + (N (s + 1) - N s) / (N (s + 1) / m s))
      (userCost r (fun s => N (s + 1) / m s)) (fun _ => Ybar + r * B0)
      (fun s => N (s + 1) / (N (s + 1) / m s)) := by
  intro m
  have hμ : 0 < 1 + μ := by linarith
  set Cbar := Ybar + r * B0 with hCbar
  set mb := mbar β μ Cbar with hmb
  have hlam : 1 ≤ (1 + μ) / β := by rw [le_div_iff₀ hβ0]; linarith
  have hmb0 : 0 < mb := by
    have : β / (1 + μ) < 1 := (div_lt_one hμ).2 hβμ
    exact div_pos hC (by linarith)
  have hdynm : ∀ t, m (t + 1) = (1 + μ) / β * (m t - Cbar) := by
    have h1 : 1 + μ - β ≠ 0 := by linarith
    have hm' : mb = Cbar * (1 + μ) / (1 + μ - β) := by
      rw [hmb]; unfold mbar
      rw [show 1 - β / (1 + μ) = (1 + μ - β) / (1 + μ) by field_simp]
      field_simp
    intro t
    simp only [m, pow_succ]
    rw [← hmb, hm']
    field_simp
    ring
  obtain ⟨hpos, hlim⟩ := log_deflation_tvc (m := m) hβ0 hβμ hμ1 hC hdynm (by simp [m]; linarith)
  have hmlow : ∀ t, mb ≤ m t := fun t => by
    have := one_le_pow₀ hlam (n := t)
    simp only [m]
    nlinarith
  have hmup : ∀ t, m t ≤ m0 * ((1 + μ) / β) ^ t := fun t => by
    have := one_le_pow₀ hlam (n := t)
    simp only [m]
    nlinarith
  have hP : ∀ s, 0 < N (s + 1) / m s := fun s => div_pos (hN _) (hpos s)
  have hmm : ∀ s, N (s + 1) / (N (s + 1) / m s) = m s := fun s => by
    have := (hN (s + 1)).ne'; have := (hpos s).ne'; field_simp
  have hsum : Summable (fun s => β ^ s * (Real.log Cbar + Real.log (N (s + 1) / (N (s + 1) /
      m s)))) := by
    simp only [hmm]
    have hβn : ‖β‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos hβ0]; exact hβ1
    set K := |Real.log Cbar| + |Real.log mb| + |Real.log m0| with hK
    refine Summable.of_norm_bounded (g := fun s => K * β ^ s + Real.log ((1 + μ) / β) *
      ((s : ℝ) ^ 1 * β ^ s)) (((summable_geometric_of_lt_one hβ0.le hβ1).mul_left K).add
      ((summable_pow_mul_geometric_of_norm_lt_one 1 hβn).mul_left _)) fun s => ?_
    have hms := hpos s
    have hl1 : Real.log mb ≤ Real.log (m s) := Real.log_le_log hmb0 (hmlow s)
    have hl2 : Real.log (m s) ≤ Real.log m0 + s * Real.log ((1 + μ) / β) := by
      have hm0' : 0 < m0 := by linarith
      calc Real.log (m s) ≤ Real.log (m0 * ((1 + μ) / β) ^ s) :=
            Real.log_le_log hms (hmup s)
        _ = _ := by rw [Real.log_mul hm0'.ne' (by positivity), Real.log_pow]
    have hll : 0 ≤ Real.log ((1 + μ) / β) := Real.log_nonneg hlam
    have hβs := pow_pos hβ0 s
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hβs, pow_one]
    have habs : |Real.log Cbar + Real.log (m s)| ≤ K + s * Real.log ((1 + μ) / β) := by
      have e1 := abs_le.1 (le_refl |Real.log Cbar|)
      rw [abs_le]
      constructor
      · have := neg_abs_le (Real.log Cbar)
        have := neg_abs_le (Real.log mb)
        have := abs_nonneg (Real.log m0)
        have : 0 ≤ (s : ℝ) * Real.log ((1 + μ) / β) := mul_nonneg (Nat.cast_nonneg s) hll
        linarith
      · have := le_abs_self (Real.log Cbar)
        have := le_abs_self (Real.log m0)
        have := abs_nonneg (Real.log mb)
        linarith
    nlinarith
  refine (equilibrium_iff (v' := fun k => k⁻¹) hβ0 hβ1 hβr hμ hC hN hP hgrowth
    strictConcaveOn_log_Ioi.concaveOn (fun k hk => Real.hasDerivAt_log hk.ne') hsum).2 ⟨?_, ?_⟩
  · intro s
    simp only [hmm]
    rw [log_dynamics_iff hβ0 hμ (hpos s)]
    exact hdynm s
  · intro ε hε
    simp only [hmm]
    exact (hlim.eventually (gt_mem_nhds hε)).frequently

/-! ## Steady states and the iterated money Euler equation (48)–(50) -/

/-- **Steady states of (46)**, O&R p. 539: a constant level `m̄ > 0` solves (46) iff
`C̄v'(m̄) = 1 − β/(1+μ)`. -/
theorem steady_state_iff {β μ Cbar mb : ℝ} {v' : ℝ → ℝ} (hmb : 0 < mb) :
    β / (1 + μ) * mb = mb * (1 - Cbar * v' mb) ↔ Cbar * v' mb = 1 - β / (1 + μ) := by
  constructor
  · intro h
    have := mul_left_cancel₀ hmb.ne' (show mb * (β / (1 + μ)) = mb * (1 - Cbar * v' mb) by
      linarith)
    linarith
  · intro h; rw [h]; ring

/-- O&R p. 539: for strictly concave `v` (`C̄v'` strictly decreasing) there is at most one steady
state; for `v = log` it is `M/P‾ = C̄/(1 − β/(1+μ))`, which is positive iff `1 + μ > β`. -/
theorem steady_state_unique {β μ Cbar m1 m2 : ℝ} {v' : ℝ → ℝ}
    (hanti : StrictAntiOn (fun k => Cbar * v' k) (Set.Ioi 0)) (h1 : 0 < m1) (h2 : 0 < m2)
    (hs1 : Cbar * v' m1 = 1 - β / (1 + μ)) (hs2 : Cbar * v' m2 = 1 - β / (1 + μ)) : m1 = m2 :=
  hanti.injOn h1 h2 (hs1.trans hs2.symm)

/-- The log steady state is positive iff `1 + μ > β` (O&R p. 539 and fn 27). -/
theorem mbar_pos_iff {β μ Cbar : ℝ} (hμ : 0 < 1 + μ) (hC : 0 < Cbar) :
    0 < mbar β μ Cbar ↔ β < 1 + μ := by
  unfold mbar
  rw [div_pos_iff]
  constructor
  · rintro (⟨_, h⟩ | ⟨h, _⟩)
    · rwa [sub_pos, div_lt_one hμ] at h
    · linarith
  · intro h
    exact Or.inl ⟨hC, by rwa [sub_pos, div_lt_one hμ]⟩

/-- **The iterated money Euler equation (48)**, O&R p. 541: with constant `M̄` and `C̄`, (47)
`1/(P_t C̄) = v'(M̄/P_t)/P_t + β/(P_{t+1} C̄)` implies, for every horizon `T`,
`1/(P_0 C̄) = Σ_{s<T} β^s v'(M̄/P_s)/P_s + β^T/(P_T C̄)`. -/
theorem iterated_money_euler {β Cbar M : ℝ} {v' : ℝ → ℝ} {P : ℕ → ℝ}
    (h47 : ∀ s, 1 / (P s * Cbar) = v' (M / P s) / P s + β / (P (s + 1) * Cbar)) (T : ℕ) :
    1 / (P 0 * Cbar) = ∑ s ∈ Finset.range T, β ^ s * (v' (M / P s) / P s) +
      β ^ T / (P T * Cbar) := by
  induction T with
  | zero => simp
  | succ T ih =>
    have e : β ^ T / (P T * Cbar) = β ^ T * (1 / (P T * Cbar)) := by ring
    rw [Finset.sum_range_succ, ih, e, h47 T, pow_succ]
    ring

/-- **(49) holds iff the transversality condition (50) holds**, O&R p. 542: when marginal utility
of money is nonnegative, the infinite-horizon money Euler equation
`1/(P_0 C̄) = Σ_s β^s v'(M̄/P_s)/P_s` holds exactly when `β^T/(P_T C̄) → 0`. -/
theorem money_euler_limit_iff {β Cbar M : ℝ} {v' : ℝ → ℝ} {P : ℕ → ℝ} (hβ : 0 ≤ β)
    (hP : ∀ s, 0 < P s) (hnn : ∀ s, 0 ≤ v' (M / P s))
    (h47 : ∀ s, 1 / (P s * Cbar) = v' (M / P s) / P s + β / (P (s + 1) * Cbar)) :
    HasSum (fun s => β ^ s * (v' (M / P s) / P s)) (1 / (P 0 * Cbar)) ↔
      Tendsto (fun T => β ^ T / (P T * Cbar)) atTop (𝓝 0) := by
  have hnn' : ∀ s, 0 ≤ β ^ s * (v' (M / P s) / P s) := fun s =>
    mul_nonneg (pow_nonneg hβ s) (div_nonneg (hnn s) (hP s).le)
  rw [hasSum_iff_tendsto_nat_of_nonneg hnn']
  have hid := iterated_money_euler h47
  constructor
  · intro h
    have := (tendsto_const_nhds (x := 1 / (P 0 * Cbar))).sub h
    rw [sub_self] at this
    exact this.congr fun T => by have := hid T; linarith
  · intro h
    have := (tendsto_const_nhds (x := 1 / (P 0 * Cbar))).sub h
    rw [sub_zero] at this
    exact this.congr fun T => by have := hid T; linarith

/-! ## General `v`, constant money: the transversality condition and deflations (§8.3.5.3) -/

/-- **Deflationary paths grow at least geometrically**, O&R p. 542: along a positive solution of
(46) with constant money, `β m_{t+1} = m_t(1 − h(m_t))` (`h = C̄v'`, antitone because `v` is
concave), starting where `h(m_0) < 1 − β` (above the steady state), real balances never fall
below `m_0` and grow by at least the factor `λ₀ = (1 − h(m_0))/β > 1` every period. -/
theorem deflation_growth {β : ℝ} {h : ℝ → ℝ} {m : ℕ → ℝ} (hβ : 0 < β) (hpos : ∀ t, 0 < m t)
    (hdyn : ∀ t, β * m (t + 1) = m t * (1 - h (m t))) (hanti : AntitoneOn h (Set.Ioi 0))
    (hm0 : h (m 0) < 1 - β) (t : ℕ) :
    m 0 ≤ m t ∧ (1 - h (m 0)) / β * m t ≤ m (t + 1) := by
  have hlam : 1 < (1 - h (m 0)) / β := by rw [one_lt_div hβ]; linarith
  have key : ∀ t, m 0 ≤ m t → (1 - h (m 0)) / β * m t ≤ m (t + 1) := by
    intro t ht
    have h1 : h (m t) ≤ h (m 0) := hanti (hpos 0) (hpos t) ht
    have h2 := hdyn t
    rw [div_mul_eq_mul_div, div_le_iff₀ hβ]
    nlinarith [hpos t]
  have hge : ∀ t, m 0 ≤ m t := by
    intro t
    induction t with
    | zero => exact le_rfl
    | succ t ih =>
      have := key t ih
      nlinarith [hpos t]
  exact ⟨hge t, key t (hge t)⟩

/-- **The discounted real balances as a product**, O&R (48)–(50) with constant `C̄` and `M̄`:
`β^T m_T = m_0 Π_{s<T}(1 − h(m_s))`. -/
theorem discounted_product {β : ℝ} {h : ℝ → ℝ} {m : ℕ → ℝ}
    (hdyn : ∀ t, β * m (t + 1) = m t * (1 - h (m t))) (T : ℕ) :
    β ^ T * m T = m 0 * ∏ s ∈ Finset.range T, (1 - h (m s)) := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Finset.prod_range_succ, pow_succ, mul_assoc, hdyn T, ← mul_assoc, ih]
    ring

/-- Upper exponential bound for a product of factors `1 − a_s` with `0 ≤ a_s ≤ 1`:
`Π_{s<T}(1 − a_s) ≤ exp(−Σ_{s<T} a_s)` (used for O&R (50)). -/
theorem prod_le_exp_neg_sum {a : ℕ → ℝ} (ha1 : ∀ s, a s ≤ 1) (T : ℕ) :
    ∏ s ∈ Finset.range T, (1 - a s) ≤ Real.exp (-∑ s ∈ Finset.range T, a s) := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Finset.prod_range_succ, Finset.sum_range_succ, neg_add, Real.exp_add]
    have h1 : 1 - a T ≤ Real.exp (-a T) := by linarith [Real.add_one_le_exp (-a T)]
    have h2 : 0 ≤ 1 - a T := by linarith [ha1 T]
    have h3 : 0 ≤ ∏ s ∈ Finset.range T, (1 - a s) :=
      Finset.prod_nonneg fun s _ => by linarith [ha1 s]
    exact mul_le_mul ih h1 h2 (Real.exp_pos _).le

/-- Lower exponential bound: if `0 ≤ a_s ≤ 1 − β` with `0 < β`, then
`exp(−(1/β) Σ_{s<T} a_s) ≤ Π_{s<T}(1 − a_s)` (used for O&R (50)). -/
theorem exp_neg_sum_le_prod {β : ℝ} (hβ : 0 < β) {a : ℕ → ℝ} (ha0 : ∀ s, 0 ≤ a s)
    (ha1 : ∀ s, a s ≤ 1 - β) (T : ℕ) :
    Real.exp (-(1 / β) * ∑ s ∈ Finset.range T, a s) ≤ ∏ s ∈ Finset.range T, (1 - a s) := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [Finset.prod_range_succ, Finset.sum_range_succ, mul_add, Real.exp_add]
    have hpos : 0 < 1 - a T := by linarith [ha1 T]
    have h1 : Real.exp (-(1 / β) * a T) ≤ 1 - a T := by
      have e1 : 1 + a T / (1 - a T) ≤ Real.exp (a T / (1 - a T)) := by
        linarith [Real.add_one_le_exp (a T / (1 - a T))]
      have e2 : a T / (1 - a T) ≤ a T / β :=
        div_le_div_of_nonneg_left (ha0 T) hβ (by linarith [ha1 T])
      have e3 : Real.exp (a T / (1 - a T)) ≤ Real.exp (a T / β) := Real.exp_le_exp.2 e2
      have e4 : 1 + a T / (1 - a T) = 1 / (1 - a T) := by field_simp; ring
      have e5 : 1 / (1 - a T) ≤ Real.exp (a T / β) := by linarith
      rw [div_le_iff₀ hpos] at e5
      have e6 : Real.exp (-(1 / β) * a T) * Real.exp (a T / β) = 1 := by
        rw [← Real.exp_add]; simp; ring_nf
      nlinarith [Real.exp_pos (-(1 / β) * a T)]
    exact mul_le_mul ih h1 (Real.exp_pos _).le
      (Finset.prod_nonneg fun s _ => by linarith [ha1 s])

/-- **The exact transversality criterion for deflations** (O&R (50) and fn 32, made precise):
along a positive deflationary solution of (46) with constant money (`h = C̄v' ≥ 0`, antitone,
`h(m_0) < 1 − β`), the individual TVC `liminf β^T m_T = 0` holds IF AND ONLY IF
`Σ_t h(m_t) = ∞`, i.e. iff `Σ_t v'(m_t)` diverges. When it holds, `β^T m_T → 0`. -/
theorem tvc_iff_not_summable {β : ℝ} {h : ℝ → ℝ} {m : ℕ → ℝ} (hβ : 0 < β)
    (hpos : ∀ t, 0 < m t) (hdyn : ∀ t, β * m (t + 1) = m t * (1 - h (m t)))
    (hanti : AntitoneOn h (Set.Ioi 0)) (hnn : ∀ x, 0 < x → 0 ≤ h x) (hm0 : h (m 0) < 1 - β) :
    BubbleTVC β m ↔ ¬ Summable (fun t => h (m t)) := by
  have ha1 : ∀ t, h (m t) ≤ 1 - β := fun t =>
    (hanti (hpos 0) (hpos t) (deflation_growth hβ hpos hdyn hanti hm0 t).1).trans hm0.le
  have ha0 : ∀ t, 0 ≤ h (m t) := fun t => hnn _ (hpos t)
  constructor
  · intro htvc hsum
    set S := ∑' t, h (m t) with hS
    have hlow : ∀ T, m 0 * Real.exp (-(1 / β) * S) ≤ β ^ T * m T := by
      intro T
      rw [discounted_product hdyn T]
      have h1 := exp_neg_sum_le_prod hβ ha0 ha1 T
      have h2 : ∑ s ∈ Finset.range T, h (m s) ≤ S := hsum.sum_le_tsum _ fun s _ => ha0 s
      have h3 : Real.exp (-(1 / β) * S) ≤ Real.exp (-(1 / β) * ∑ s ∈ Finset.range T, h (m s)) :=
        Real.exp_le_exp.2 (by
          have : 0 < 1 / β := by positivity
          nlinarith)
      exact mul_le_mul_of_nonneg_left (h3.trans h1) (hpos 0).le
    have hε : 0 < m 0 * Real.exp (-(1 / β) * S) := mul_pos (hpos 0) (Real.exp_pos _)
    obtain ⟨T, hT⟩ := (htvc _ hε).exists
    linarith [hlow T]
  · intro hns ε hε
    have hdiv := (not_summable_iff_tendsto_nat_atTop_of_nonneg ha0).1 hns
    have hexp : Tendsto (fun T => m 0 * Real.exp (-∑ s ∈ Finset.range T, h (m s))) atTop
        (𝓝 (m 0 * 0)) :=
      (Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hdiv)).const_mul _
    rw [mul_zero] at hexp
    refine (hexp.eventually (gt_mem_nhds hε)).mono (fun T hT => ?_) |>.frequently
    rw [discounted_product hdyn T]
    have := prod_le_exp_neg_sum (fun t => (ha1 t).trans (by linarith)) T
    calc m 0 * ∏ s ∈ Finset.range T, (1 - h (m s))
        ≤ m 0 * Real.exp (-∑ s ∈ Finset.range T, h (m s)) :=
          mul_le_mul_of_nonneg_left this (hpos 0).le
      _ < ε := hT

/-- The tangent-line inequality for a concave function of one variable (copied from the
`SmallOpenEconomyDynamics` project's `ConsumptionOptimality` so that this project builds on its
own; used for fn 32, O&R p. 542). -/
theorem concave_le_tangent' {f : ℝ → ℝ} {S : Set ℝ} (hf : ConcaveOn ℝ S f) {x y d : ℝ}
    (hx : x ∈ S) (hy : y ∈ S) (hd : HasDerivAt f d x) : f y ≤ f x + d * (y - x) := by
  rcases lt_trichotomy y x with hyx | rfl | hxy
  · have h := hf.le_slope_of_hasDerivAt hy hx hyx hd
    rw [slope_def_field, le_div_iff₀ (by linarith)] at h
    linarith
  · simp
  · have h := hf.slope_le_of_hasDerivAt hx hy hxy hd
    rw [slope_def_field, div_le_iff₀ (by linarith)] at h
    linarith

/-- **Footnote 32, made precise**, O&R p. 542: if `v` is concave, increasing and BOUNDED ABOVE,
then along a positive deflationary path with constant money `Σ_t v'(m_t) < ∞`: the telescoping
bound `v'(m_{t+1})(m_{t+1} − m_t) ≤ v(m_{t+1}) − v(m_t)` with `m_{t+1} − m_t ≥ (λ₀ − 1)m_0`. -/
theorem summable_deriv_of_bounded {β Cbar V : ℝ} {v v' : ℝ → ℝ} {m : ℕ → ℝ} (hβ : 0 < β)
    (hpos : ∀ t, 0 < m t)
    (hdyn : ∀ t, β * m (t + 1) = m t * (1 - Cbar * v' (m t)))
    (hv : ConcaveOn ℝ (Set.Ioi 0) v) (hv' : ∀ k, 0 < k → HasDerivAt v (v' k) k)
    (hanti : AntitoneOn (fun k => Cbar * v' k) (Set.Ioi 0)) (hnn : ∀ k, 0 < k → 0 ≤ v' k)
    (hV : ∀ k, 0 < k → v k ≤ V) (hm0 : Cbar * v' (m 0) < 1 - β) :
    Summable (fun t => v' (m t)) := by
  set lam := (1 - Cbar * v' (m 0)) / β with hlam
  have hlam1 : 1 < lam := by rw [hlam, one_lt_div hβ]; linarith
  set δ := (lam - 1) * m 0 with hδ
  have hδ0 : 0 < δ := mul_pos (by linarith) (hpos 0)
  have hgr := deflation_growth (h := fun k => Cbar * v' k) hβ hpos hdyn hanti hm0
  have hstep : ∀ t, δ ≤ m (t + 1) - m t := fun t => by
    have h1 := (hgr t).2
    have h2 := (hgr t).1
    rw [← hlam] at h1
    nlinarith
  have hterm : ∀ t, v' (m (t + 1)) ≤ (v (m (t + 1)) - v (m t)) / δ := fun t => by
    rw [le_div_iff₀ hδ0]
    have h1 := concave_le_tangent' hv (hpos (t + 1)) (hpos t) (hv' _ (hpos (t + 1)))
    have h2 := hstep t
    have h3 := hnn _ (hpos (t + 1))
    nlinarith
  have hbound : ∀ n, ∑ t ∈ Finset.range n, v' (m (t + 1)) ≤ (V - v (m 0)) / δ := by
    intro n
    calc ∑ t ∈ Finset.range n, v' (m (t + 1))
        ≤ ∑ t ∈ Finset.range n, (v (m (t + 1)) - v (m t)) / δ := Finset.sum_le_sum fun t _ =>
          hterm t
      _ = (v (m n) - v (m 0)) / δ := by
          rw [← Finset.sum_div, Finset.sum_range_sub (fun t => v (m t))]
      _ ≤ (V - v (m 0)) / δ := by
          have := hV _ (hpos n)
          exact div_le_div_of_nonneg_right (by linarith) hδ0.le
  have hs : Summable (fun t => v' (m (t + 1))) :=
    summable_of_sum_range_le (fun t => hnn _ (hpos _)) hbound
  exact (summable_nat_add_iff 1).1 hs

/-- **Deflationary bubbles are ruled out when `v` is bounded above** (O&R p. 542 and fn 32,
constant money): the individual TVC fails along every positive deflationary solution of (46). -/
theorem bounded_rules_out_deflation {β Cbar V : ℝ} {v v' : ℝ → ℝ} {m : ℕ → ℝ} (hβ : 0 < β)
    (hC : 0 < Cbar) (hpos : ∀ t, 0 < m t)
    (hdyn : ∀ t, β * m (t + 1) = m t * (1 - Cbar * v' (m t)))
    (hv : ConcaveOn ℝ (Set.Ioi 0) v) (hv' : ∀ k, 0 < k → HasDerivAt v (v' k) k)
    (hanti : AntitoneOn (fun k => Cbar * v' k) (Set.Ioi 0)) (hnn : ∀ k, 0 < k → 0 ≤ v' k)
    (hV : ∀ k, 0 < k → v k ≤ V) (hm0 : Cbar * v' (m 0) < 1 - β) : ¬ BubbleTVC β m := by
  rw [tvc_iff_not_summable (h := fun k => Cbar * v' k) hβ hpos hdyn hanti
    (fun k hk => mul_nonneg hC.le (hnn k hk)) hm0, not_not]
  exact (summable_deriv_of_bounded hβ hpos hdyn hv hv' hanti hnn hV hm0).mul_left Cbar

/-- **The log case satisfies `Σ 1/m_t < ∞`** (O&R fn 32: "true even for some standard cases in
which `v` isn't bounded above, for example the logarithmic case"): with constant money and
`v = log`, the TVC fails along every positive deflationary path. -/
theorem log_rules_out_deflation {β Cbar : ℝ} {m : ℕ → ℝ} (hβ : 0 < β) (hC : 0 < Cbar)
    (hpos : ∀ t, 0 < m t) (hdyn : ∀ t, β * m (t + 1) = m t * (1 - Cbar * (m t)⁻¹))
    (hm0 : Cbar * (m 0)⁻¹ < 1 - β) : ¬ BubbleTVC β m := by
  have hanti : AntitoneOn (fun k : ℝ => Cbar * k⁻¹) (Set.Ioi 0) := fun x hx y hy hxy =>
    mul_le_mul_of_nonneg_left (inv_anti₀ hx hxy) hC.le
  rw [tvc_iff_not_summable (h := fun k => Cbar * k⁻¹) hβ hpos hdyn hanti
    (fun k hk => mul_nonneg hC.le (inv_pos.2 hk).le) hm0, not_not]
  set lam := (1 - Cbar * (m 0)⁻¹) / β with hlam
  have hlam1 : 1 < lam := by rw [hlam, one_lt_div hβ]; linarith
  have hgr := deflation_growth (h := fun k => Cbar * k⁻¹) hβ hpos hdyn hanti hm0
  have hgeo : ∀ t, m 0 * lam ^ t ≤ m t := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      have := (hgr t).2
      rw [← hlam] at this
      rw [pow_succ]
      nlinarith [hlam1]
  have hq : lam⁻¹ < 1 := inv_lt_one_of_one_lt₀ hlam1
  refine Summable.of_nonneg_of_le (fun t => mul_nonneg hC.le (inv_pos.2 (hpos t)).le)
    (fun t => ?_) (((summable_geometric_of_lt_one (by positivity) hq).mul_left
      (Cbar * (m 0)⁻¹)))
  have h1 : (m t)⁻¹ ≤ (m 0 * lam ^ t)⁻¹ := inv_anti₀ (by have := hpos 0; positivity) (hgeo t)
  rw [mul_inv] at h1
  calc Cbar * (m t)⁻¹ ≤ Cbar * ((m 0)⁻¹ * (lam ^ t)⁻¹) := mul_le_mul_of_nonneg_left h1 hC.le
    _ = _ := by rw [inv_pow]; ring

/-! ### A deflationary-bubble equilibrium with unbounded concave `v` -/

/-- **Counterexample to "the TVC rules out deflations" for unbounded `v`** (O&R p. 542, fn 32):
`v(m) = a m + log m` (`a > 0`) is strictly increasing, concave and unbounded above; its
derivative `a + 1/m ≥ a` is not summable along any path, so by `tvc_iff_not_summable` the TVC
holds along every deflationary path. Concavity. -/
theorem linlog_concaveOn {a : ℝ} (ha : 0 ≤ a) :
    ConcaveOn ℝ (Set.Ioi 0) (fun k => a * k + Real.log k) :=
  ((concaveOn_id (convex_Ioi 0)).smul ha).add strictConcaveOn_log_Ioi.concaveOn

/-- `v(m) = a m + log m` is unbounded above (O&R fn 32 counterexample). -/
theorem linlog_unbounded {a : ℝ} (ha : 0 < a) (K : ℝ) : ∃ k, 0 < k ∧ K < a * k + Real.log k := by
  refine ⟨max 1 (K / a + 1), lt_of_lt_of_le one_pos (le_max_left _ _), ?_⟩
  have h1 : 1 ≤ max 1 (K / a + 1) := le_max_left _ _
  have h2 : K / a + 1 ≤ max 1 (K / a + 1) := le_max_right _ _
  have h3 : 0 ≤ Real.log (max 1 (K / a + 1)) := Real.log_nonneg h1
  have h4 : K < a * (K / a + 1) := by field_simp; linarith
  nlinarith

/-- The saddle-path solution `m_s = m̄ + κ^s (m_0 − m̄)` of an affine difference equation
`m_{s+1} − m̄ = κ(m_s − m̄)` (O&R Fig. 8.2). -/
noncomputable def affinePath (mb κ m0 : ℝ) (s : ℕ) : ℝ := mb + κ ^ s * (m0 - mb)

/-- **A deflationary bubble IS an equilibrium when `v = a m + log m`** (constant money,
`μ = 0`): with `C̄ = Ȳ + rB_0`, `1 − C̄a > β` and steady state `m̄ = C̄/(1 − C̄a − β)`, EVERY
`m_0 ≥ m̄` generates an equilibrium price path `P_s = M̄/m_s`,
`m_s = m̄ + ((1 − C̄a)/β)^s (m_0 − m̄)`; for `m_0 > m̄` the price level falls to zero. So the
book's conclusion (p. 543) needs `v` bounded above (or `Σ v'(m_t) < ∞`); it fails for this
unbounded concave `v`.
Context: O&R §8.3.5, pp. 538–546. -/
theorem linlog_deflation_equilibrium {a β r Ybar B0 Cbar Mbar m0 : ℝ} (ha : 0 < a)
    (hβ0 : 0 < β) (hβ1 : β < 1) (hβr : (1 + r) * β = 1) (hCbar : Ybar + r * B0 = Cbar)
    (hC : 0 < Cbar) (hstab : β < 1 - Cbar * a) (hM : 0 < Mbar)
    (hm0 : Cbar / (1 - Cbar * a - β) ≤ m0) :
    IsOptimal (fun c k => Real.log c + (a * k + Real.log k)) β r
      ((1 + r) * B0 + Mbar / (Mbar / affinePath (Cbar / (1 - Cbar * a - β))
        ((1 - Cbar * a) / β) m0 0))
      (fun s => Ybar + (Mbar - Mbar) / (Mbar / affinePath (Cbar / (1 - Cbar * a - β))
        ((1 - Cbar * a) / β) m0 s))
      (userCost r (fun s => Mbar / affinePath (Cbar / (1 - Cbar * a - β))
        ((1 - Cbar * a) / β) m0 s)) (fun _ => Cbar)
      (fun s => Mbar / (Mbar / affinePath (Cbar / (1 - Cbar * a - β))
        ((1 - Cbar * a) / β) m0 s)) := by
  set mb := Cbar / (1 - Cbar * a - β) with hmbdef
  set κ := (1 - Cbar * a) / β with hκ
  set m := affinePath mb κ m0 with hmdef
  have hden : 0 < 1 - Cbar * a - β := by linarith
  have hmb0 : 0 < mb := div_pos hC hden
  have hκ1 : 1 ≤ κ := by rw [hκ, le_div_iff₀ hβ0]; linarith
  have hq0 : 0 ≤ 1 - Cbar * a := by linarith
  have hq1 : 1 - Cbar * a < 1 := by nlinarith
  have e : β * κ = 1 - Cbar * a := by rw [hκ]; field_simp
  have hmb' : mb * (1 - Cbar * a - β) = Cbar := by rw [hmbdef]; field_simp
  have hmlow : ∀ t, mb ≤ m t := fun t => by
    have := one_le_pow₀ hκ1 (n := t); simp only [hmdef, affinePath]; nlinarith
  have hmup : ∀ t, m t ≤ m0 * κ ^ t := fun t => by
    have := one_le_pow₀ hκ1 (n := t); simp only [hmdef, affinePath]; nlinarith
  have hpos : ∀ t, 0 < m t := fun t => lt_of_lt_of_le hmb0 (hmlow t)
  have hm0' : 0 < m0 := lt_of_lt_of_le hmb0 hm0
  have hmm : ∀ s, Mbar / (Mbar / m s) = m s := fun s => by
    have := (hpos s).ne'; field_simp
  have hβm : ∀ T, β ^ T * m T = β ^ T * mb + (1 - Cbar * a) ^ T * (m0 - mb) := fun T => by
    simp only [hmdef, affinePath]
    rw [mul_add, ← mul_assoc, ← mul_pow, e]
  have hN : ∀ s : ℕ, 0 < (fun _ => Mbar) s := fun _ => hM
  have hP : ∀ s, 0 < Mbar / m s := fun s => div_pos hM (hpos s)
  have hsum : Summable (fun s => β ^ s * (Real.log (Ybar + r * B0) + (a * (Mbar / (Mbar / m s)) +
      Real.log (Mbar / (Mbar / m s))))) := by
    simp only [hmm, hCbar]
    have hβn : ‖β‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos hβ0]; exact hβ1
    have hA : Summable (fun s => a * (β ^ s * m s)) := by
      simp only [hβm]
      exact ((((summable_geometric_of_lt_one hβ0.le hβ1).mul_right mb).add
        ((summable_geometric_of_lt_one hq0 hq1).mul_right (m0 - mb))).mul_left a)
    set K := |Real.log Cbar| + |Real.log mb| + |Real.log m0| with hK
    have hB : Summable (fun s => β ^ s * (Real.log Cbar + Real.log (m s))) := by
      refine Summable.of_norm_bounded (g := fun s => K * β ^ s + Real.log κ *
        ((s : ℝ) ^ 1 * β ^ s)) (((summable_geometric_of_lt_one hβ0.le hβ1).mul_left K).add
        ((summable_pow_mul_geometric_of_norm_lt_one 1 hβn).mul_left _)) fun s => ?_
      have hl1 : Real.log mb ≤ Real.log (m s) := Real.log_le_log hmb0 (hmlow s)
      have hl2 : Real.log (m s) ≤ Real.log m0 + s * Real.log κ := by
        calc Real.log (m s) ≤ Real.log (m0 * κ ^ s) := Real.log_le_log (hpos s) (hmup s)
          _ = _ := by rw [Real.log_mul hm0'.ne' (by positivity), Real.log_pow]
      have hll : 0 ≤ Real.log κ := Real.log_nonneg hκ1
      have hβs := pow_pos hβ0 s
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos hβs, pow_one]
      have habs : |Real.log Cbar + Real.log (m s)| ≤ K + s * Real.log κ := by
        rw [abs_le]
        have := neg_abs_le (Real.log Cbar)
        have := neg_abs_le (Real.log mb)
        have := abs_nonneg (Real.log m0)
        have := le_abs_self (Real.log Cbar)
        have := le_abs_self (Real.log m0)
        have := abs_nonneg (Real.log mb)
        have : 0 ≤ (s : ℝ) * Real.log κ := mul_nonneg (Nat.cast_nonneg s) hll
        constructor <;> linarith
      nlinarith
    convert hA.add hB using 1
    funext s
    ring
  have key := equilibrium_iff (μ := 0) (N := fun _ => Mbar) (P := fun s => Mbar / m s)
    (v' := fun k => a + k⁻¹) hβ0 hβ1 hβr (by norm_num) (hCbar ▸ hC) hN hP (fun _ => by ring)
    (linlog_concaveOn ha.le)
    (fun k hk => (((hasDerivAt_id k).const_mul a).add (Real.hasDerivAt_log hk.ne')).congr_deriv
      (by simp)) hsum
  simp only [hCbar] at key
  refine key.2 ⟨fun s => ?_, fun ε hε => ?_⟩
  · simp only [hmm, add_zero, div_one]
    have hX := (hpos s).ne'
    have hR : m s * (1 - Cbar * (a + (m s)⁻¹)) = m s * (1 - Cbar * a) - Cbar := by
      field_simp; ring
    rw [hR]
    simp only [hmdef, affinePath, pow_succ]
    linear_combination (κ ^ s * (m0 - mb)) * e - hmb'
  · simp only [hmm]
    have h1 : Tendsto (fun T : ℕ => β ^ T * mb + (1 - Cbar * a) ^ T * (m0 - mb)) atTop
        (𝓝 (0 * mb + 0 * (m0 - mb))) :=
      ((tendsto_pow_atTop_nhds_zero_of_lt_one hβ0.le hβ1).mul_const _).add
        ((tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const _)
    simp only [zero_mul, add_zero] at h1
    exact ((h1.congr fun T => (hβm T).symm).eventually (gt_mem_nhds hε)).frequently

/-! ### The survey's counterexample `v'(m) = 1/log(m + e)` -/

/-- The integrand `1/log(t + e)` of the logarithmic-integral utility (fn 32 counterexample).
Context: O&R §8.3.5, pp. 538–546. -/
noncomputable def logIntDeriv (t : ℝ) : ℝ := 1 / Real.log (t + Real.exp 1)

/-- A logarithmic-integral utility of money, `v(m) = ∫₀^m dt/log(t + e)`, whose marginal utility
`1/log(m + e)` behaves like `1/log m` (the counterexample to fn 32, O&R p. 542). -/
noncomputable def logIntUtility (m : ℝ) : ℝ := ∫ t in (0 : ℝ)..m, logIntDeriv t

/-- `log(t + e) ≥ 1` for `t ≥ 0`.
Context: O&R §8.3.5, pp. 538–546. -/
theorem one_le_log_add_exp {t : ℝ} (ht : 0 ≤ t) : 1 ≤ Real.log (t + Real.exp 1) := by
  rw [Real.le_log_iff_exp_le (by positivity)]
  linarith

/-- `1/log(t + e)` is continuous on `(0, ∞)` (indeed on `t > 1 − e`).
Context: O&R §8.3.5, pp. 538–546. -/
theorem logIntDeriv_continuousOn : ContinuousOn logIntDeriv (Set.Ioi (1 - Real.exp 1)) := by
  intro t ht
  simp only [Set.mem_Ioi] at ht
  have h1 : 1 < t + Real.exp 1 := by linarith
  have h2 : 0 < Real.log (t + Real.exp 1) := Real.log_pos h1
  have h3 : t + Real.exp 1 ≠ 0 := by linarith
  have hc : ContinuousAt (fun x : ℝ => x + Real.exp 1) t := continuousAt_id.add continuousAt_const
  have hl : ContinuousAt (fun x : ℝ => Real.log (x + Real.exp 1)) t := hc.log h3
  exact (continuousAt_const.div hl h2.ne').continuousWithinAt

/-- **`v' (m) = 1/log(m + e)`** for the logarithmic-integral utility (FTC).
Context: O&R §8.3.5, pp. 538–546. -/
theorem logIntUtility_hasDerivAt {m : ℝ} (hm : 0 < m) :
    HasDerivAt logIntUtility (logIntDeriv m) m := by
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have hsub : Set.uIcc 0 m ⊆ Set.Ioi (1 - Real.exp 1) := by
    intro x hx
    rw [Set.uIcc_of_le hm.le] at hx
    simp only [Set.mem_Ioi]
    have := Real.add_one_le_exp 1
    linarith [hx.1]
  have hint : IntervalIntegrable logIntDeriv MeasureTheory.volume 0 m :=
    (logIntDeriv_continuousOn.mono hsub).intervalIntegrable
  have hm' : m ∈ Set.Ioi (1 - Real.exp 1) := by
    simp only [Set.mem_Ioi]; have := Real.add_one_le_exp 1; linarith
  exact intervalIntegral.integral_hasDerivAt_right hint
    (logIntDeriv_continuousOn.stronglyMeasurableAtFilter isOpen_Ioi m hm')
    (logIntDeriv_continuousOn.continuousAt (isOpen_Ioi.mem_nhds hm'))

/-- `1/log(t + e)` lies in `(0, 1]` for `t ≥ 0`.
Context: O&R §8.3.5, pp. 538–546. -/
theorem logIntDeriv_mem {t : ℝ} (ht : 0 ≤ t) : 0 < logIntDeriv t ∧ logIntDeriv t ≤ 1 := by
  have h1 := one_le_log_add_exp ht
  unfold logIntDeriv
  exact ⟨by positivity, by rw [div_le_one (by linarith)]; exact h1⟩

/-- `1/log(t + e)` is strictly decreasing on `[0, ∞)`.
Context: O&R §8.3.5, pp. 538–546. -/
theorem logIntDeriv_strictAntiOn : StrictAntiOn logIntDeriv (Set.Ici 0) := by
  intro x hx y hy hxy
  simp only [Set.mem_Ici] at hx hy
  have h1 := one_le_log_add_exp hx
  have h2 : Real.log (x + Real.exp 1) < Real.log (y + Real.exp 1) :=
    Real.log_lt_log (by positivity) (by linarith)
  unfold logIntDeriv
  exact one_div_lt_one_div_of_lt (by linarith) h2

/-- **The logarithmic-integral utility is strictly increasing and strictly concave**, with
`0 ≤ v(m) ≤ m` for `m ≥ 0`.
Context: O&R §8.3.5, pp. 538–546. -/
theorem logIntUtility_props :
    StrictConcaveOn ℝ (Set.Ioi 0) logIntUtility ∧ StrictMonoOn logIntUtility (Set.Ioi 0) ∧
      ∀ m, 0 ≤ m → 0 ≤ logIntUtility m ∧ logIntUtility m ≤ m := by
  have hcont : ContinuousOn logIntUtility (Set.Ioi 0) :=
    fun m hm => (logIntUtility_hasDerivAt hm).continuousAt.continuousWithinAt
  have hder : ∀ m, 0 < m → deriv logIntUtility m = logIntDeriv m :=
    fun m hm => (logIntUtility_hasDerivAt hm).deriv
  refine ⟨StrictAntiOn.strictConcaveOn_of_deriv (convex_Ioi 0) hcont ?_, ?_, fun m hm => ?_⟩
  · intro x hx y hy hxy
    rw [interior_Ioi] at hx hy
    rw [hder x hx, hder y hy]
    exact logIntDeriv_strictAntiOn (Set.mem_Ici.2 (le_of_lt hx)) (Set.mem_Ici.2 (le_of_lt hy)) hxy
  · refine strictMonoOn_of_deriv_pos (convex_Ioi 0) hcont fun x hx => ?_
    rw [interior_Ioi] at hx
    rw [hder x hx]
    exact (logIntDeriv_mem (le_of_lt hx)).1
  · have hsub : Set.uIcc 0 m ⊆ Set.Ioi (1 - Real.exp 1) := by
      intro x hx
      rw [Set.uIcc_of_le hm] at hx
      simp only [Set.mem_Ioi]
      have := Real.add_one_le_exp 1
      linarith [hx.1]
    have hint : IntervalIntegrable logIntDeriv MeasureTheory.volume 0 m :=
      (logIntDeriv_continuousOn.mono hsub).intervalIntegrable
    constructor
    · exact intervalIntegral.integral_nonneg hm fun t ht => (logIntDeriv_mem ht.1).1.le
    · have := intervalIntegral.integral_mono_on hm hint
        (intervalIntegrable_const (c := (1 : ℝ))) fun t ht => (logIntDeriv_mem ht.1).2
      unfold logIntUtility
      simpa using this

/-- The deflationary orbit of (46) with constant money: `m_{t+1} = m_t(1 − h(m_t))/β`.
Context: O&R §8.3.5, pp. 538–546. -/
noncomputable def deflOrbit (β : ℝ) (h : ℝ → ℝ) (m0 : ℝ) (t : ℕ) : ℝ :=
  (fun x => x * (1 - h x) / β)^[t] m0

/-- The orbit satisfies (46) with constant money.
Context: O&R §8.3.5, pp. 538–546. -/
theorem deflOrbit_succ {β : ℝ} (hβ : 0 < β) (h : ℝ → ℝ) (m0 : ℝ) (t : ℕ) :
    β * deflOrbit β h m0 (t + 1) = deflOrbit β h m0 t * (1 - h (deflOrbit β h m0 t)) := by
  simp only [deflOrbit]
  rw [Function.iterate_succ_apply']
  field_simp

/-- **The fn 32 counterexample with `v'(m) = 1/log(m + e)`** (O&R p. 542, made precise):
`v(m) = ∫₀^m dt/log(t+e)` is strictly increasing and strictly concave, and with constant money,
`0 < β < 1`, `C̄ > 0`, any `m_0` with `C̄/log(m_0 + e) < 1 − β` starts a positive deflationary
path of (46) along which `Σ v'(m_t) = ∞`; so the individual TVC HOLDS (`β^T m_T → 0`
frequently, `tvc_iff_not_summable`). The proof uses the growth bound `m_t ≤ m_0 β^{−t}`, hence
`v'(m_t) ≥ 1/(log(m_0 + e) + t log(1/β))`, which is not summable. -/
theorem logInt_deflation_tvc {β Cbar m0 : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hC : 0 < Cbar)
    (hm00 : 0 < m0) (hm0 : Cbar * logIntDeriv m0 < 1 - β) :
    (∀ t, 0 < deflOrbit β (fun x => Cbar * logIntDeriv x) m0 t) ∧
      ¬ Summable (fun t => Cbar * logIntDeriv (deflOrbit β (fun x => Cbar * logIntDeriv x) m0 t)) ∧
      BubbleTVC β (deflOrbit β (fun x => Cbar * logIntDeriv x) m0) := by
  set h : ℝ → ℝ := fun x => Cbar * logIntDeriv x with hh
  set m := deflOrbit β h m0 with hm
  have hdyn := deflOrbit_succ hβ0 h m0
  have hanti : AntitoneOn h (Set.Ioi 0) := fun x hx y hy hxy =>
    mul_le_mul_of_nonneg_left (logIntDeriv_strictAntiOn.antitoneOn (Set.mem_Ici.2 (le_of_lt hx))
      (Set.mem_Ici.2 (le_of_lt hy)) hxy) hC.le
  have hnn : ∀ x, 0 < x → 0 ≤ h x := fun x hx =>
    mul_nonneg hC.le (logIntDeriv_mem (le_of_lt hx)).1.le
  -- positivity and monotonicity of the orbit
  have hstep : ∀ t, m0 ≤ m t → m t ≤ m (t + 1) := by
    intro t ht
    have h1 : h (m t) ≤ h m0 := hanti hm00 (lt_of_lt_of_le hm00 ht) ht
    have h2 := hdyn t
    have hmt : 0 < m t := lt_of_lt_of_le hm00 ht
    have : β ≤ 1 - h (m t) := by linarith
    nlinarith
  have hge : ∀ t, m0 ≤ m t := by
    intro t
    induction t with
    | zero => simp [hm, deflOrbit]
    | succ t ih => exact ih.trans (hstep t ih)
  have hpos : ∀ t, 0 < m t := fun t => lt_of_lt_of_le hm00 (hge t)
  have hm0' : h (m 0) < 1 - β := by simpa [hm, deflOrbit] using hm0
  -- the growth bound `m_t ≤ m_0 β^{-t}`
  have hup : ∀ t, m t ≤ m0 * (β⁻¹) ^ t := by
    intro t
    induction t with
    | zero => simp [hm, deflOrbit]
    | succ t ih =>
      have h2 := hdyn t
      have h3 := hnn _ (hpos t)
      have : m (t + 1) ≤ m t / β := by
        rw [le_div_iff₀ hβ0]; nlinarith [hpos t]
      calc m (t + 1) ≤ m t / β := this
        _ ≤ m0 * β⁻¹ ^ t / β := div_le_div_of_nonneg_right ih hβ0.le
        _ = m0 * β⁻¹ ^ (t + 1) := by rw [pow_succ]; field_simp
  set L0 := Real.log (m0 + Real.exp 1) with hL0
  set ell := Real.log β⁻¹ with hell
  have hell0 : 0 < ell := Real.log_pos (one_lt_inv_iff₀.2 ⟨hβ0, hβ1⟩)
  have hL01 : 1 ≤ L0 := one_le_log_add_exp hm00.le
  have hlow : ∀ t, Cbar * (1 / (L0 + t * ell)) ≤ h (m t) := by
    intro t
    have hbt : 1 ≤ β⁻¹ ^ t := one_le_pow₀ (one_le_inv_iff₀.2 ⟨hβ0, hβ1.le⟩)
    have h1 : m t + Real.exp 1 ≤ (m0 + Real.exp 1) * β⁻¹ ^ t := by
      have := hup t; nlinarith [Real.exp_pos 1]
    have h2 : Real.log (m t + Real.exp 1) ≤ L0 + t * ell := by
      calc Real.log (m t + Real.exp 1) ≤ Real.log ((m0 + Real.exp 1) * β⁻¹ ^ t) :=
            Real.log_le_log (by have := hpos t; positivity) h1
        _ = L0 + t * ell := by
            rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
    have h3 : 0 < Real.log (m t + Real.exp 1) := by
      linarith [one_le_log_add_exp (hpos t).le]
    simp only [hh, logIntDeriv]
    exact mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le h3 h2) hC.le
  have hns : ¬ Summable (fun t => h (m t)) := by
    intro hs
    have hharm : ¬ Summable (fun t : ℕ => 1 / ((t : ℝ) + 1)) := by
      have := Real.not_summable_natCast_inv
      rwa [← summable_nat_add_iff 1, show (fun n : ℕ => ((↑(n + 1) : ℝ))⁻¹) =
        fun t : ℕ => 1 / ((t : ℝ) + 1) by funext t; push_cast; rw [one_div]] at this
    apply hharm
    refine Summable.of_nonneg_of_le (fun t => by positivity) (fun t => ?_)
      (hs.mul_left ((L0 + ell) / Cbar))
    have h1 := hlow t
    have h2 : L0 + t * ell ≤ (L0 + ell) * (t + 1) := by
      have : (0 : ℝ) ≤ t := Nat.cast_nonneg t
      nlinarith
    have h3 : 1 / ((L0 + ell) * (t + 1)) ≤ 1 / (L0 + t * ell) :=
      one_div_le_one_div_of_le (by have : (0 : ℝ) ≤ t := Nat.cast_nonneg t; positivity) h2
    have h4 : 1 / ((t : ℝ) + 1) = (L0 + ell) * (1 / ((L0 + ell) * (t + 1))) := by
      field_simp
    rw [h4]
    calc (L0 + ell) * (1 / ((L0 + ell) * (t + 1))) ≤ (L0 + ell) * (1 / (L0 + t * ell)) :=
          mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = (L0 + ell) / Cbar * (Cbar * (1 / (L0 + t * ell))) := by field_simp
      _ ≤ (L0 + ell) / Cbar * h (m t) := mul_le_mul_of_nonneg_left h1 (by positivity)
  exact ⟨hpos, hns, (tvc_iff_not_summable hβ0 hpos hdyn hanti hnn hm0').2 hns⟩

/-- The logarithmic-integral utility is unbounded above (as it must be, by
`bounded_rules_out_deflation`, since the TVC holds along its deflationary paths).
Context: O&R §8.3.5, pp. 538–546. -/
theorem logIntUtility_unbounded (V : ℝ) : ∃ k, 0 < k ∧ V < logIntUtility k := by
  by_contra hcon
  push Not at hcon
  set m0 := Real.exp 2 with hm0
  have hm00 : 0 < m0 := Real.exp_pos 2
  have hlog : 2 < Real.log (m0 + Real.exp 1) := by
    rw [Real.lt_log_iff_exp_lt (by positivity)]
    linarith [Real.exp_pos 1]
  have hm0' : 1 * logIntDeriv m0 < 1 - 1 / 2 := by
    unfold logIntDeriv
    rw [one_mul, div_lt_iff₀ (by linarith)]
    linarith
  obtain ⟨hpos, -, htvc⟩ := logInt_deflation_tvc (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num) one_pos hm00 hm0'
  have hanti : AntitoneOn (fun k => 1 * logIntDeriv k) (Set.Ioi 0) := fun x hx y hy hxy => by
    simp only [one_mul]
    exact logIntDeriv_strictAntiOn.antitoneOn (Set.mem_Ici.2 (le_of_lt hx))
      (Set.mem_Ici.2 (le_of_lt hy)) hxy
  exact bounded_rules_out_deflation (by norm_num) one_pos hpos
    (deflOrbit_succ (by norm_num) _ m0) logIntUtility_props.1.concaveOn
    (fun k hk => logIntUtility_hasDerivAt hk) hanti
    (fun k hk => (logIntDeriv_mem (le_of_lt hk)).1.le) hcon (by simpa [deflOrbit] using hm0') htvc

/-- The telescoping lower bound `Σ_{t<s} 1/(L₀ + tℓ) ≥ (log(L₀ + sℓ) − log L₀)/ℓ`.
Context: O&R §8.3.5, pp. 538–546. -/
theorem sum_inv_linear_ge {L0 ell : ℝ} (hL0 : 0 < L0) (hell : 0 < ell) (s : ℕ) :
    (Real.log (L0 + s * ell) - Real.log L0) / ell ≤
      ∑ t ∈ Finset.range s, 1 / (L0 + t * ell) := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Finset.sum_range_succ]
    have ha : 0 < L0 + s * ell := by have : (0 : ℝ) ≤ s := Nat.cast_nonneg s; positivity
    have hstep : Real.log (L0 + (s + 1 : ℕ) * ell) - Real.log (L0 + s * ell) ≤
        ell / (L0 + s * ell) := by
      rw [← Real.log_div (by push_cast; positivity) ha.ne']
      have := Real.log_le_sub_one_of_pos (show 0 < (L0 + (s + 1 : ℕ) * ell) / (L0 + s * ell) by
        push_cast; positivity)
      have e : (L0 + (s + 1 : ℕ) * ell) / (L0 + s * ell) - 1 = ell / (L0 + s * ell) := by
        push_cast; field_simp; ring
      linarith
    have h2 : (Real.log (L0 + (s + 1 : ℕ) * ell) - Real.log L0) / ell =
        (Real.log (L0 + s * ell) - Real.log L0) / ell +
          (Real.log (L0 + (s + 1 : ℕ) * ell) - Real.log (L0 + s * ell)) / ell := by ring
    have h3 : (Real.log (L0 + (s + 1 : ℕ) * ell) - Real.log (L0 + s * ell)) / ell ≤
        1 / (L0 + s * ell) := by
      rw [div_le_iff₀ hell]
      calc _ ≤ ell / (L0 + s * ell) := hstep
        _ = 1 / (L0 + s * ell) * ell := by ring
    linarith

/-- **The fn 32 counterexample is a genuine equilibrium** (constant money, `μ = 0`): with
`u = log C + ∫₀^{M/P} dt/log(t+e)`, `(1+r)β = 1`, `C̄ = Ȳ + rB_0 > log(1/β)` and
`C̄/log(m_0 + e) < 1 − β`, the deflationary price path `P_s = M̄/m_s` (`m` the orbit of (46)
from `m_0`) is an equilibrium: the household's plan is optimal (lifetime utility is finite
because `β^s m_s ≤ m_0 (L₀/(L₀ + s log(1/β)))^{C̄/log(1/β)}` with exponent above one). So a
strictly concave, increasing `v` with `v' ≈ 1/log m` admits speculative deflations.
Context: O&R §8.3.5, pp. 538–546. -/
theorem logInt_deflation_equilibrium {β r Ybar B0 Cbar Mbar m0 : ℝ} (hβ0 : 0 < β)
    (hβ1 : β < 1) (hβr : (1 + r) * β = 1) (hCbar : Ybar + r * B0 = Cbar) (hC : 0 < Cbar)
    (hCell : Real.log β⁻¹ < Cbar) (hM : 0 < Mbar) (hm00 : 0 < m0)
    (hm0 : Cbar * logIntDeriv m0 < 1 - β) :
    IsOptimal (fun c k => Real.log c + logIntUtility k) β r
      ((1 + r) * B0 + Mbar / (Mbar / deflOrbit β (fun x => Cbar * logIntDeriv x) m0 0))
      (fun s => Ybar + (Mbar - Mbar) / (Mbar / deflOrbit β (fun x => Cbar * logIntDeriv x) m0 s))
      (userCost r (fun s => Mbar / deflOrbit β (fun x => Cbar * logIntDeriv x) m0 s))
      (fun _ => Cbar)
      (fun s => Mbar / (Mbar / deflOrbit β (fun x => Cbar * logIntDeriv x) m0 s)) := by
  set h : ℝ → ℝ := fun x => Cbar * logIntDeriv x with hh
  set m := deflOrbit β h m0 with hm
  obtain ⟨hpos, hns, htvc⟩ := logInt_deflation_tvc hβ0 hβ1 hC hm00 hm0
  have hdyn := deflOrbit_succ hβ0 h m0
  have hmm : ∀ s, Mbar / (Mbar / m s) = m s := fun s => by
    have := (hpos s).ne'; field_simp
  have hN : ∀ s : ℕ, 0 < (fun _ => Mbar) s := fun _ => hM
  have hP : ∀ s, 0 < Mbar / m s := fun s => div_pos hM (hpos s)
  -- summability of lifetime utility
  set L0 := Real.log (m0 + Real.exp 1) with hL0
  set ell := Real.log β⁻¹ with hell
  have hell0 : 0 < ell := Real.log_pos (one_lt_inv_iff₀.2 ⟨hβ0, hβ1⟩)
  have hL01 : 1 ≤ L0 := one_le_log_add_exp hm00.le
  set p := Cbar / ell with hp
  have hp1 : 1 < p := by rw [hp, one_lt_div hell0]; exact hCell
  have hle1 : ∀ t, h (m t) ≤ 1 := fun t => by
    have hanti : h (m t) ≤ h m0 := by
      have hge : m0 ≤ m t := by
        induction t with
        | zero => simp [hm, deflOrbit]
        | succ t ih =>
          have h2 := hdyn t
          have h1 : h (m t) ≤ h m0 := mul_le_mul_of_nonneg_left
            (logIntDeriv_strictAntiOn.antitoneOn (Set.mem_Ici.2 hm00.le)
              (Set.mem_Ici.2 (le_of_lt (hpos t))) ih) hC.le
          have : β ≤ 1 - h (m t) := by linarith
          nlinarith [hpos t]
      exact mul_le_mul_of_nonneg_left (logIntDeriv_strictAntiOn.antitoneOn
        (Set.mem_Ici.2 hm00.le) (Set.mem_Ici.2 (le_of_lt (hpos t))) hge) hC.le
    linarith
  have hup : ∀ t, m t ≤ m0 * (β⁻¹) ^ t := by
    intro t
    induction t with
    | zero => simp [hm, deflOrbit]
    | succ t ih =>
      have h2 := hdyn t
      have h3 : 0 ≤ h (m t) := mul_nonneg hC.le (logIntDeriv_mem (hpos t).le).1.le
      have : m (t + 1) ≤ m t / β := by
        rw [le_div_iff₀ hβ0]; nlinarith [hpos t]
      calc m (t + 1) ≤ m t / β := this
        _ ≤ m0 * β⁻¹ ^ t / β := div_le_div_of_nonneg_right ih hβ0.le
        _ = m0 * β⁻¹ ^ (t + 1) := by rw [pow_succ]; field_simp
  have hlow : ∀ t, Cbar * (1 / (L0 + t * ell)) ≤ h (m t) := by
    intro t
    have hbt : 1 ≤ β⁻¹ ^ t := one_le_pow₀ (one_le_inv_iff₀.2 ⟨hβ0, hβ1.le⟩)
    have h1 : m t + Real.exp 1 ≤ (m0 + Real.exp 1) * β⁻¹ ^ t := by
      have := hup t; nlinarith [Real.exp_pos 1]
    have h2 : Real.log (m t + Real.exp 1) ≤ L0 + t * ell := by
      calc Real.log (m t + Real.exp 1) ≤ Real.log ((m0 + Real.exp 1) * β⁻¹ ^ t) :=
            Real.log_le_log (by have := hpos t; positivity) h1
        _ = L0 + t * ell := by
            rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
    have h3 : 0 < Real.log (m t + Real.exp 1) := by
      linarith [one_le_log_add_exp (hpos t).le]
    simp only [hh, logIntDeriv]
    exact mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le h3 h2) hC.le
  set c := min L0 ell with hc
  have hc0 : 0 < c := lt_min (by linarith) hell0
  have hbound : ∀ s, β ^ s * m s ≤ m0 * (L0 / c) ^ p * (((s + 1 : ℕ) : ℝ) ^ p)⁻¹ := by
    intro s
    rw [discounted_product hdyn s]
    have h1 := prod_le_exp_neg_sum hle1 s
    have h2 : Cbar * ((Real.log (L0 + s * ell) - Real.log L0) / ell) ≤
        ∑ t ∈ Finset.range s, h (m t) := by
      calc Cbar * ((Real.log (L0 + s * ell) - Real.log L0) / ell)
          ≤ Cbar * ∑ t ∈ Finset.range s, 1 / (L0 + t * ell) :=
            mul_le_mul_of_nonneg_left (sum_inv_linear_ge (by linarith) hell0 s) hC.le
        _ = ∑ t ∈ Finset.range s, Cbar * (1 / (L0 + t * ell)) := by rw [Finset.mul_sum]
        _ ≤ _ := Finset.sum_le_sum fun t _ => hlow t
    have hX : 0 < L0 + s * ell := by have : (0 : ℝ) ≤ s := Nat.cast_nonneg s; positivity
    have h3 : Real.exp (-∑ t ∈ Finset.range s, h (m t)) ≤ (L0 / (L0 + s * ell)) ^ p := by
      rw [rpow_def_of_pos (div_pos (by linarith) hX), Real.log_div (by linarith) hX.ne']
      apply Real.exp_le_exp.2
      have : Cbar * ((Real.log (L0 + s * ell) - Real.log L0) / ell) =
          (Real.log (L0 + s * ell) - Real.log L0) * p := by rw [hp]; field_simp
      linarith
    have h4 : (L0 / (L0 + s * ell)) ^ p ≤ (L0 / c) ^ p * (((s + 1 : ℕ) : ℝ) ^ p)⁻¹ := by
      have hcs : c * ((s + 1 : ℕ) : ℝ) ≤ L0 + s * ell := by
        push_cast
        have h5 : c ≤ L0 := min_le_left _ _
        have h6 : c ≤ ell := min_le_right _ _
        have : (0 : ℝ) ≤ s := Nat.cast_nonneg s
        nlinarith
      have h7 : L0 / (L0 + s * ell) ≤ L0 / (c * ((s + 1 : ℕ) : ℝ)) :=
        div_le_div_of_nonneg_left (by linarith) (by positivity) hcs
      calc (L0 / (L0 + s * ell)) ^ p ≤ (L0 / (c * ((s + 1 : ℕ) : ℝ))) ^ p :=
            rpow_le_rpow (by positivity) h7 (by linarith)
        _ = (L0 / c) ^ p * (((s + 1 : ℕ) : ℝ) ^ p)⁻¹ := by
            rw [div_mul_eq_div_div, div_rpow (by positivity) (by positivity), div_eq_mul_inv]
    calc m 0 * ∏ t ∈ Finset.range s, (1 - h (m t)) ≤ m 0 * Real.exp (-∑ t ∈ Finset.range s,
          h (m t)) := mul_le_mul_of_nonneg_left h1 (hpos 0).le
      _ ≤ m 0 * ((L0 / c) ^ p * (((s + 1 : ℕ) : ℝ) ^ p)⁻¹) :=
          mul_le_mul_of_nonneg_left (h3.trans h4) (hpos 0).le
      _ = m0 * (L0 / c) ^ p * (((s + 1 : ℕ) : ℝ) ^ p)⁻¹ := by simp [hm, deflOrbit]; ring
  have hps : Summable (fun s : ℕ => (((s + 1 : ℕ) : ℝ) ^ p)⁻¹) :=
    (summable_nat_add_iff 1).2 (Real.summable_nat_rpow_inv.2 hp1)
  have hbm : Summable (fun s => β ^ s * m s) :=
    Summable.of_nonneg_of_le (fun s => mul_nonneg (pow_pos hβ0 s).le (hpos s).le) hbound
      (hps.mul_left _)
  have hsum : Summable (fun s => β ^ s * (Real.log (Ybar + r * B0) +
      logIntUtility (Mbar / (Mbar / m s)))) := by
    simp only [hmm, hCbar, mul_add]
    refine ((summable_geometric_of_lt_one hβ0.le hβ1).mul_right _).add ?_
    refine Summable.of_nonneg_of_le (fun s => mul_nonneg (pow_pos hβ0 s).le
      (logIntUtility_props.2.2 _ (hpos s).le).1) (fun s => ?_) hbm
    exact mul_le_mul_of_nonneg_left (logIntUtility_props.2.2 _ (hpos s).le).2 (pow_pos hβ0 s).le
  have key := equilibrium_iff (μ := 0) (N := fun _ => Mbar) (P := fun s => Mbar / m s)
    (v := logIntUtility) (v' := logIntDeriv) hβ0 hβ1 hβr (by norm_num) (hCbar ▸ hC) hN hP
    (fun _ => by ring) logIntUtility_props.1.concaveOn (fun k hk => logIntUtility_hasDerivAt hk)
    hsum
  simp only [hCbar] at key
  refine key.2 ⟨fun s => ?_, fun ε hε => ?_⟩
  · simp only [hmm, add_zero, div_one]
    exact hdyn s
  · simp only [hmm]
    exact htvc ε hε

/-! ## Speculative hyperinflations: (52), (54) and footnote 34 (§8.3.5.4) -/

/-- **Footnote 34**, O&R p. 545: if (54) holds in the form `m v'(m) ≥ c₀ > 0` for all small
`m`, then `lim_{m→0} v(m) = −∞`. (The book's proof, made quantitative: along `m_k = y/2^k`,
concavity gives `v(m_{k+1}) ≤ v(m_k) − c₀/2`.) -/
theorem fn34_tendsto_atBot {v v' : ℝ → ℝ} {c0 δ : ℝ} (hc0 : 0 < c0) (hδ : 0 < δ)
    (hv : ConcaveOn ℝ (Set.Ioi 0) v) (hmono : MonotoneOn v (Set.Ioi 0))
    (hv' : ∀ k, 0 < k → HasDerivAt v (v' k) k) (h54 : ∀ x, 0 < x → x < δ → c0 ≤ x * v' x) :
    Tendsto v (𝓝[>] 0) atBot := by
  set y := δ / 2 with hydef
  have hy : 0 < y := by positivity
  have hstep : ∀ k : ℕ, v (y / 2 ^ k) ≤ v y - k * (c0 / 2) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hx : 0 < y / 2 ^ k := by positivity
      have hxy : y / 2 ^ k ≤ y := div_le_self hy.le (one_le_pow₀ (by norm_num))
      have hxδ : y / 2 ^ k < δ := by linarith
      have h1 := concave_le_tangent' hv hx (show (0 : ℝ) < y / 2 ^ k / 2 by positivity)
        (hv' _ hx)
      have h2 := h54 _ hx hxδ
      rw [pow_succ, ← div_div]
      push_cast
      nlinarith
  rw [tendsto_atBot]
  intro b
  obtain ⟨k, hk⟩ := exists_nat_gt ((v y - b) / (c0 / 2))
  have hk' : v y - k * (c0 / 2) < b := by
    rw [div_lt_iff₀ (by positivity)] at hk; linarith
  filter_upwards [Ioo_mem_nhdsGT (show (0 : ℝ) < y / 2 ^ k by positivity)] with x hx
  exact (hmono hx.1 (show (0 : ℝ) < y / 2 ^ k by positivity) hx.2.le).trans
    ((hstep k).trans hk'.le)

/-- **Footnote 34 sharpened** (its contrapositive, quantitative): if `v` is concave,
nondecreasing and BOUNDED BELOW near zero, then (52) holds: `m v'(m) → 0` as `m → 0`. Indeed
`0 ≤ m v'(m) ≤ v(m) − inf v`.
Context: O&R §8.3.5, pp. 538–546. -/
theorem fn34_sharpened {v v' : ℝ → ℝ} {L : ℝ} (hv : ConcaveOn ℝ (Set.Ioi 0) v)
    (hv' : ∀ k, 0 < k → HasDerivAt v (v' k) k) (hnn : ∀ k, 0 < k → 0 ≤ v' k)
    (hL : ∀ k, 0 < k → L ≤ v k) : Tendsto (fun x => x * v' x) (𝓝[>] 0) (𝓝 0) := by
  set S := v '' Set.Ioi 0 with hS
  have hne : S.Nonempty := ⟨v 1, 1, Set.mem_Ioi.2 one_pos, rfl⟩
  have hbdd : BddBelow S := ⟨L, by rintro _ ⟨k, hk, rfl⟩; exact hL k hk⟩
  set ℓ := sInf S with hℓ
  have hℓle : ∀ k, 0 < k → ℓ ≤ v k := fun k hk => csInf_le hbdd ⟨k, hk, rfl⟩
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun ε hε => ?_⟩
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact lt_of_lt_of_le ha (mul_nonneg (le_of_lt hx) (hnn x hx))
  · obtain ⟨_, ⟨y0, hy0, rfl⟩, hy0lt⟩ := exists_lt_of_csInf_lt hne
      (show ℓ < ℓ + ε / 2 by linarith)
    filter_upwards [Ioo_mem_nhdsGT hy0] with x hx
    obtain ⟨hx0, hxy0⟩ := hx
    have hvx : v x ≤ v y0 := by
      have := concave_le_tangent' hv hy0 hx0 (hv' y0 hy0)
      have := hnn y0 hy0
      nlinarith
    have hd := hnn x hx0
    set y := min (x / 2) (ε / (4 * (v' x + 1))) with hydef
    have hy0' : 0 < y := lt_min (by positivity) (by positivity)
    have hyx : y < x := lt_of_le_of_lt (min_le_left _ _) (by linarith)
    have htan := concave_le_tangent' hv hx0 hy0' (hv' x hx0)
    have hℓy := hℓle y hy0'
    have h1 : v' x * (x - y) < ε / 2 := by nlinarith
    have h2 : v' x * y ≤ ε / 4 := by
      have hy2 : y ≤ ε / (4 * (v' x + 1)) := min_le_right _ _
      have : v' x * y ≤ v' x * (ε / (4 * (v' x + 1))) := mul_le_mul_of_nonneg_left hy2 hd
      have h3 : v' x * (ε / (4 * (v' x + 1))) ≤ ε / 4 := by
        rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
      linarith
    nlinarith

/-- The slowly diverging function `L(m) = log(1 + 1/m)` used in the counterexample to the
converse of footnote 34.
Context: O&R §8.3.5, pp. 538–546. -/
noncomputable def slowLog (m : ℝ) : ℝ := Real.log (1 + m⁻¹)

/-- `L(m) = log(1 + 1/m) ≥ 0` for `m > 0`.
Context: O&R §8.3.5, pp. 538–546. -/
theorem slowLog_nonneg {m : ℝ} (hm : 0 < m) : 0 ≤ slowLog m :=
  Real.log_nonneg (by have := inv_pos.2 hm; linarith)

/-- `L'(m) = −1/(m(m+1))`.
Context: O&R §8.3.5, pp. 538–546. -/
theorem slowLog_hasDerivAt {m : ℝ} (hm : 0 < m) :
    HasDerivAt slowLog (-1 / (m * (m + 1))) m := by
  have h1 : 0 < 1 + m⁻¹ := by have := inv_pos.2 hm; linarith
  have h := ((hasDerivAt_inv hm.ne').const_add 1).log h1.ne'
  refine h.congr_deriv ?_
  field_simp

/-- The counterexample to the converse of footnote 34: `v(m) = −log(1 + log(1 + 1/m))`.
Context: O&R §8.3.5, pp. 538–546. -/
noncomputable def vSlow (m : ℝ) : ℝ := -Real.log (1 + slowLog m)

/-- `v'(m) = 1/((1 + L(m)) m (m+1))` for the counterexample.
Context: O&R §8.3.5, pp. 538–546. -/
theorem vSlow_hasDerivAt {m : ℝ} (hm : 0 < m) :
    HasDerivAt vSlow (1 / ((1 + slowLog m) * m * (m + 1))) m := by
  have hL := slowLog_nonneg hm
  have h := ((slowLog_hasDerivAt hm).const_add 1).log (by linarith)
  refine h.neg.congr_deriv ?_
  field_simp

/-- **The converse of footnote 34 fails** (O&R p. 545, "necessary (but not sufficient)"):
`v(m) = −log(1 + log(1 + 1/m))` is strictly increasing and concave on `(0, ∞)`, satisfies (52),
`m v'(m) → 0`, and yet `v(m) → −∞` as `m → 0`. -/
theorem vSlow_counterexample :
    StrictMonoOn vSlow (Set.Ioi 0) ∧ ConcaveOn ℝ (Set.Ioi 0) vSlow ∧
      Tendsto (fun m => m * (1 / ((1 + slowLog m) * m * (m + 1)))) (𝓝[>] 0) (𝓝 0) ∧
      Tendsto vSlow (𝓝[>] 0) atBot := by
  have hder : ∀ m, 0 < m → deriv vSlow m = 1 / ((1 + slowLog m) * m * (m + 1)) :=
    fun m hm => (vSlow_hasDerivAt hm).deriv
  have hcont : ContinuousOn vSlow (Set.Ioi 0) :=
    fun m hm => (vSlow_hasDerivAt hm).continuousAt.continuousWithinAt
  -- `g(m) = (1 + L(m)) m (m+1)` is strictly increasing
  set g : ℝ → ℝ := fun m => (1 + slowLog m) * (m * (m + 1)) with hg
  have hgd : ∀ m, 0 < m → HasDerivAt g ((1 + slowLog m) * (2 * m + 1) - 1) m := by
    intro m hm
    have h1 := ((slowLog_hasDerivAt hm).const_add 1).mul
      (((hasDerivAt_id m).mul ((hasDerivAt_id m).add_const 1)))
    refine h1.congr_deriv ?_
    simp only [Pi.mul_apply, id]
    field_simp
    ring
  have hgmono : StrictMonoOn g (Set.Ioi 0) := by
    refine strictMonoOn_of_deriv_pos (convex_Ioi 0)
      (fun m hm => (hgd m hm).continuousAt.continuousWithinAt) (fun m hm => ?_)
    rw [interior_Ioi] at hm
    rw [(hgd m hm).deriv]
    have := slowLog_nonneg hm
    have hm' : (0 : ℝ) < m := hm
    nlinarith
  have hgpos : ∀ m, 0 < m → 0 < g m := fun m hm => by
    have := slowLog_nonneg hm; simp only [hg]; positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine strictMonoOn_of_deriv_pos (convex_Ioi 0) hcont (fun m hm => ?_)
    rw [interior_Ioi] at hm
    rw [hder m hm]
    have := slowLog_nonneg hm
    have hm' : (0 : ℝ) < m := hm
    positivity
  · refine AntitoneOn.concaveOn_of_deriv (convex_Ioi 0) hcont
      (fun m hm => by
        rw [interior_Ioi] at hm
        exact (vSlow_hasDerivAt hm).differentiableAt.differentiableWithinAt)
      (fun x hx y hy hxy => ?_)
    rw [interior_Ioi] at hx hy
    rw [hder x hx, hder y hy]
    have h1 := hgmono.monotoneOn hx hy hxy
    have hgx := hgpos x hx
    simp only [hg] at h1 hgx
    rw [show (1 + slowLog x) * x * (x + 1) = (1 + slowLog x) * (x * (x + 1)) by ring,
      show (1 + slowLog y) * y * (y + 1) = (1 + slowLog y) * (y * (y + 1)) by ring]
    exact one_div_le_one_div_of_le hgx h1
  · have hL : Tendsto slowLog (𝓝[>] 0) atTop :=
      Real.tendsto_log_atTop.comp (tendsto_atTop_add_const_left _ 1 tendsto_inv_nhdsGT_zero)
    have hinv : Tendsto (fun m => 1 / (1 + slowLog m)) (𝓝[>] 0) (𝓝 0) := by
      have := tendsto_inv_atTop_zero.comp (tendsto_atTop_add_const_left _ 1 hL)
      simpa [Function.comp_def, one_div] using this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hinv ?_ ?_
    · filter_upwards [self_mem_nhdsWithin] with m hm
      have := slowLog_nonneg hm
      have hm' : (0 : ℝ) < m := hm
      positivity
    · filter_upwards [self_mem_nhdsWithin] with m hm
      have := slowLog_nonneg hm
      have hm' : (0 : ℝ) < m := hm
      rw [show m * (1 / ((1 + slowLog m) * m * (m + 1))) = 1 / ((1 + slowLog m) * (m + 1)) by
        field_simp]
      apply one_div_le_one_div_of_le (by positivity)
      nlinarith
  · have hL : Tendsto slowLog (𝓝[>] 0) atTop :=
      Real.tendsto_log_atTop.comp (tendsto_atTop_add_const_left _ 1 tendsto_inv_nhdsGT_zero)
    exact tendsto_neg_atTop_atBot.comp
      (Real.tendsto_log_atTop.comp (tendsto_atTop_add_const_left _ 1 hL))

/-! ### Hyperinflationary paths (Figure 8.3) and fractional backing (§8.3.5.5) -/

/-- The forward map of (46): `φ(m) = ((1+μ)/β) m (1 − h(m))` with `h = C̄v'` (O&R Fig. 8.3);
`λ = (1+μ)/β`. -/
noncomputable def phiMap (lam : ℝ) (h : ℝ → ℝ) (m : ℝ) : ℝ := lam * m * (1 - h m)

/-- On `[m*, ∞)`, where `h(m*) = 1` (i.e. `C̄v'(m*) = 1`, condition (53)), the map `φ` is strictly
increasing (O&R Fig. 8.3). -/
theorem phiMap_strictMonoOn {lam mstar : ℝ} {h : ℝ → ℝ} (hlam : 0 < lam) (hms : 0 < mstar)
    (hanti : StrictAntiOn h (Set.Ioi 0)) (hstar : h mstar = 1) :
    StrictMonoOn (phiMap lam h) (Set.Ici mstar) := by
  intro x hx y hy hxy
  simp only [Set.mem_Ici] at hx hy
  have hx0 : 0 < x := lt_of_lt_of_le hms hx
  have hy0 : 0 < y := lt_of_lt_of_le hms hy
  have h1 : h y < h x := hanti hx0 hy0 hxy
  have h2 : h x ≤ 1 := by
    rcases hx.lt_or_eq with hlt | heq
    · exact (hanti hms hx0 hlt).le.trans hstar.le
    · rw [← heq, hstar]
  unfold phiMap
  have : 0 ≤ 1 - h x := by linarith
  have e1 : x * (1 - h x) ≤ y * (1 - h x) := mul_le_mul_of_nonneg_right hxy.le this
  have e2 : y * (1 - h x) < y * (1 - h y) := mul_lt_mul_of_pos_left (by linarith) hy0
  calc lam * x * (1 - h x) = lam * (x * (1 - h x)) := by ring
    _ < lam * (y * (1 - h y)) := mul_lt_mul_of_pos_left (e1.trans_lt e2) hlam
    _ = lam * y * (1 - h y) := by ring

/-- **Every point of `[0, m̄]` has a unique preimage in `[m*, m̄]`** (IVT; O&R Fig. 8.3). -/
theorem phiMap_preimage {lam mstar mb : ℝ} {h : ℝ → ℝ} (hlam : 0 < lam) (hms : 0 < mstar)
    (hlt : mstar < mb) (hcont : ContinuousOn h (Set.Ioi 0)) (hanti : StrictAntiOn h (Set.Ioi 0))
    (hstar : h mstar = 1) (hbar : lam * (1 - h mb) = 1) {y : ℝ} (hy : y ∈ Set.Icc 0 mb) :
    ∃! x, x ∈ Set.Icc mstar mb ∧ phiMap lam h x = y := by
  have hφs : phiMap lam h mstar = 0 := by simp [phiMap, hstar]
  have hφb : phiMap lam h mb = mb := by
    simp only [phiMap]; linear_combination mb * hbar
  have hc : ContinuousOn (phiMap lam h) (Set.Icc mstar mb) := by
    have : ContinuousOn h (Set.Icc mstar mb) :=
      hcont.mono fun x hx => lt_of_lt_of_le hms hx.1
    exact ((continuousOn_const.mul continuousOn_id).mul (continuousOn_const.sub this))
  obtain ⟨x, hx, hφx⟩ := intermediate_value_Icc hlt.le hc (by rw [hφs, hφb]; exact hy)
  refine ⟨x, ⟨hx, hφx⟩, fun x' ⟨hx', hφx'⟩ => ?_⟩
  exact (phiMap_strictMonoOn hlam hms hanti hstar).injOn hx'.1 hx.1 (hφx'.trans hφx.symm)

/-- The chosen preimage in `[m*, m̄]` (O&R Fig. 8.3). -/
noncomputable def phiPre (lam : ℝ) (h : ℝ → ℝ) (mstar mb y : ℝ) : ℝ :=
  Classical.epsilon (fun x => x ∈ Set.Icc mstar mb ∧ phiMap lam h x = y)

/-- The backward orbit `b_0 = m*`, `b_{k+1} = φ^{−1}(b_k)`: `b_{T−1}` is the initial real
balance from which the economy reaches `m*` at date `T − 1` and money becomes worthless at `T`
(O&R (53) and Fig. 8.3). -/
noncomputable def backOrbit (lam : ℝ) (h : ℝ → ℝ) (mstar mb : ℝ) : ℕ → ℝ
  | 0 => mstar
  | k + 1 => phiPre lam h mstar mb (backOrbit lam h mstar mb k)

/-- **Hyperinflationary paths (Figure 8.3), made precise**: under (52)-type assumptions — `h = C̄v'`
continuous and strictly decreasing, `h(m*) = 1` for some `0 < m* < m̄` (condition (53)) and
`λ(1 − h(m̄)) = 1` (the steady state) — the backward orbit satisfies `b_k ∈ [m*, m̄)`,
`φ(b_{k+1}) = b_k`, and is strictly increasing. So for every `T ≥ 1` the initial real balance
`b_{T−1}` leads to `m_{T−1} = m*` and `m_T = φ(m*) = 0`: the price level becomes infinite at `T`.
Context: O&R §8.3.5, pp. 538–546. -/
theorem backOrbit_spec {lam mstar mb : ℝ} {h : ℝ → ℝ} (hlam : 0 < lam) (hms : 0 < mstar)
    (hlt : mstar < mb) (hcont : ContinuousOn h (Set.Ioi 0)) (hanti : StrictAntiOn h (Set.Ioi 0))
    (hstar : h mstar = 1) (hbar : lam * (1 - h mb) = 1) (k : ℕ) :
    backOrbit lam h mstar mb k ∈ Set.Ico mstar mb ∧
      phiMap lam h (backOrbit lam h mstar mb (k + 1)) = backOrbit lam h mstar mb k ∧
      backOrbit lam h mstar mb k < backOrbit lam h mstar mb (k + 1) := by
  have hφb : phiMap lam h mb = mb := by
    simp only [phiMap]; linear_combination mb * hbar
  have hmono := phiMap_strictMonoOn hlam hms hanti hstar
  have hstep : ∀ y, y ∈ Set.Ico mstar mb → phiPre lam h mstar mb y ∈ Set.Icc mstar mb ∧
      phiMap lam h (phiPre lam h mstar mb y) = y := by
    intro y hy
    have hex := (phiMap_preimage hlam hms hlt hcont hanti hstar hbar
      ⟨hms.le.trans hy.1, hy.2.le⟩).exists
    exact Classical.epsilon_spec hex
  have hin : ∀ k, backOrbit lam h mstar mb k ∈ Set.Ico mstar mb := by
    intro k
    induction k with
    | zero => exact ⟨le_rfl, hlt⟩
    | succ k ih =>
      obtain ⟨⟨h1, h2⟩, h3⟩ := hstep _ ih
      have hb1 : backOrbit lam h mstar mb (k + 1) =
          phiPre lam h mstar mb (backOrbit lam h mstar mb k) := rfl
      refine ⟨h1, lt_of_le_of_ne h2 fun heq => ?_⟩
      rw [← hb1, heq, hφb] at h3
      exact absurd h3.symm (ne_of_lt ih.2)
  refine ⟨hin k, (hstep _ (hin k)).2, ?_⟩
  -- strict increase
  induction k with
  | zero =>
    have h1 := (hstep _ (hin 0)).1
    rcases h1.1.lt_or_eq with hlt' | heq
    · exact hlt'
    · exfalso
      have h3 := (hstep _ (hin 0)).2
      rw [← heq] at h3
      simp only [backOrbit, phiMap, hstar, sub_self, mul_zero] at h3
      linarith
  | succ k ih =>
    have h1 := (hstep _ (hin k)).2
    have h2 := (hstep _ (hin (k + 1))).2
    have hk1 := hin (k + 1)
    have hk2 := hin (k + 2)
    by_contra hle
    push Not at hle
    have := hmono.monotoneOn (show backOrbit lam h mstar mb (k + 2) ∈ Set.Ici mstar from hk2.1)
      (show backOrbit lam h mstar mb (k + 1) ∈ Set.Ici mstar from hk1.1) hle
    simp only [backOrbit] at h1 h2 this ih ⊢
    linarith

/-- **The collapse date** (O&R (53)): starting from `b_k` the forward orbit of (46) reaches `m*`
(where `C̄v'(m*) = 1`) after `k` periods and zero real balances (`P = ∞`) after `k + 1`. -/
theorem backOrbit_iterate {lam mstar mb : ℝ} {h : ℝ → ℝ} (hlam : 0 < lam) (hms : 0 < mstar)
    (hlt : mstar < mb) (hcont : ContinuousOn h (Set.Ioi 0)) (hanti : StrictAntiOn h (Set.Ioi 0))
    (hstar : h mstar = 1) (hbar : lam * (1 - h mb) = 1) (k : ℕ) :
    (phiMap lam h)^[k] (backOrbit lam h mstar mb k) = mstar ∧
      (phiMap lam h)^[k + 1] (backOrbit lam h mstar mb k) = 0 := by
  have hspec := backOrbit_spec hlam hms hlt hcont hanti hstar hbar
  have h1 : ∀ k, (phiMap lam h)^[k] (backOrbit lam h mstar mb k) = mstar := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Function.iterate_succ_apply, (hspec k).2.1, ih]
  refine ⟨h1 k, ?_⟩
  rw [Function.iterate_succ_apply', h1 k]
  simp [phiMap, hstar]

/-- **Uniqueness of the initial price level for each collapse date** (O&R Fig. 8.3): if an
initial real balance `x ∈ [m*, m̄]` keeps the orbit in `[m*, m̄]` and reaches `m*` after exactly
`k` periods, then `x = b_k`. -/
theorem backOrbit_unique {lam mstar mb : ℝ} {h : ℝ → ℝ} (hlam : 0 < lam) (hms : 0 < mstar)
    (hlt : mstar < mb) (hcont : ContinuousOn h (Set.Ioi 0)) (hanti : StrictAntiOn h (Set.Ioi 0))
    (hstar : h mstar = 1) (hbar : lam * (1 - h mb) = 1) (k : ℕ) :
    ∀ x, (∀ j, j ≤ k → (phiMap lam h)^[j] x ∈ Set.Icc mstar mb) →
      (phiMap lam h)^[k] x = mstar → x = backOrbit lam h mstar mb k := by
  have hspec := backOrbit_spec hlam hms hlt hcont hanti hstar hbar
  have hmono := phiMap_strictMonoOn hlam hms hanti hstar
  induction k with
  | zero => intro x _ hx; simpa [backOrbit] using hx
  | succ k ih =>
    intro x hin hx
    have h1 : phiMap lam h x = backOrbit lam h mstar mb k := by
      refine ih (phiMap lam h x) (fun j hj => ?_) ?_
      · have := hin (j + 1) (by omega)
        rwa [Function.iterate_succ_apply] at this
      · rwa [Function.iterate_succ_apply] at hx
    have hx0 := hin 0 (Nat.zero_le _)
    simp only [Function.iterate_zero, id] at hx0
    exact hmono.injOn hx0.1 ((hspec (k + 1)).1.1)
      (h1.trans ((hspec k).2.1).symm)

/-- **`m_0^{(T)} ↑ m̄`** (O&R Fig. 8.3: the later the collapse date, the closer the initial price
level to the steady state): the backward orbit converges to the steady state `m̄`. -/
theorem backOrbit_tendsto {lam mstar mb : ℝ} {h : ℝ → ℝ} (hlam : 0 < lam) (hms : 0 < mstar)
    (hlt : mstar < mb) (hcont : ContinuousOn h (Set.Ioi 0)) (hanti : StrictAntiOn h (Set.Ioi 0))
    (hstar : h mstar = 1) (hbar : lam * (1 - h mb) = 1) :
    Tendsto (backOrbit lam h mstar mb) atTop (𝓝 mb) := by
  have hspec := backOrbit_spec hlam hms hlt hcont hanti hstar hbar
  set b := backOrbit lam h mstar mb with hb
  have hmono : Monotone b := monotone_nat_of_le_succ fun k => (hspec k).2.2.le
  have hbdd : BddAbove (Set.range b) := ⟨mb, by rintro _ ⟨k, rfl⟩; exact (hspec k).1.2.le⟩
  have hlim := tendsto_atTop_ciSup hmono hbdd
  set L := ⨆ k, b k with hL
  have hLle : L ≤ mb := ciSup_le fun k => (hspec k).1.2.le
  have hLge : mstar ≤ L := (hspec 0).1.1.trans (le_ciSup hbdd 0)
  have hL0 : 0 < L := lt_of_lt_of_le hms hLge
  -- `φ(b_{k+1}) = b_k` passes to the limit: `φ(L) = L`
  have hcφ : ContinuousAt (phiMap lam h) L := by
    have : ContinuousAt h L := hcont.continuousAt (Ioi_mem_nhds hL0)
    exact ((continuousAt_const.mul continuousAt_id).mul (continuousAt_const.sub this))
  have h1 : Tendsto (fun k => phiMap lam h (b (k + 1))) atTop (𝓝 (phiMap lam h L)) :=
    hcφ.tendsto.comp ((tendsto_add_atTop_iff_nat 1).2 hlim)
  have h2 : Tendsto (fun k => phiMap lam h (b (k + 1))) atTop (𝓝 L) :=
    hlim.congr fun k => ((hspec k).2.1).symm
  have hfix : phiMap lam h L = L := tendsto_nhds_unique h1 h2
  have hhL : h L = h mb := by
    unfold phiMap at hfix
    have : lam * (1 - h L) = 1 := by
      have := mul_right_cancel₀ hL0.ne' (by linarith : lam * (1 - h L) * L = 1 * L)
      linarith
    have := mul_left_cancel₀ hlam.ne' (show lam * (1 - h L) = lam * (1 - h mb) by linarith)
    linarith
  have : L = mb := hanti.injOn hL0 (lt_trans hms hlt) hhL
  rwa [this] at hlim

/-- **Asymptotic hyperinflation and fractional backing** (O&R §8.3.5.4–8.3.5.5, made precise):
with `h = C̄v'` continuous and strictly decreasing and the steady state `λ(1 − h(m̄)) = 1`, every
solution of (46) that stays positive and starts below `m̄` is strictly decreasing and
converges to zero. In particular it falls below any floor `M̄/P^MIN > 0` in finite time, so a
credible floor rules out every hyperinflationary path. -/
theorem hyperinflation_tendsto_zero {lam mb : ℝ} {h : ℝ → ℝ} {m : ℕ → ℝ} (hlam : 0 < lam)
    (hmb : 0 < mb) (hcont : ContinuousOn h (Set.Ioi 0)) (hanti : StrictAntiOn h (Set.Ioi 0))
    (hbar : lam * (1 - h mb) = 1) (hpos : ∀ t, 0 < m t)
    (hdyn : ∀ t, m (t + 1) = phiMap lam h (m t)) (hm0 : m 0 < mb) :
    StrictAnti m ∧ Tendsto m atTop (𝓝 0) := by
  have hdec : ∀ t, m t < mb → m (t + 1) < m t := by
    intro t ht
    have h1 : h mb < h (m t) := hanti (hpos t) hmb ht
    rw [hdyn t]
    unfold phiMap
    have e : lam * (1 - h (m t)) = 1 - lam * (h (m t) - h mb) := by linear_combination hbar
    have e2 : 0 < lam * (h (m t) - h mb) := mul_pos hlam (by linarith)
    have e3 : lam * (1 - h (m t)) < 1 := by linarith
    have := hpos t
    calc lam * m t * (1 - h (m t)) = m t * (lam * (1 - h (m t))) := by ring
      _ < m t * 1 := mul_lt_mul_of_pos_left e3 this
      _ = m t := mul_one _
  have hbelow : ∀ t, m t < mb := by
    intro t
    induction t with
    | zero => exact hm0
    | succ t ih => exact (hdec t ih).trans ih
  have hanti' : StrictAnti m := strictAnti_nat_of_succ_lt fun t => hdec t (hbelow t)
  refine ⟨hanti', ?_⟩
  have hbdd : BddBelow (Set.range m) := ⟨0, by rintro _ ⟨t, rfl⟩; exact (hpos t).le⟩
  have hlim := tendsto_atTop_ciInf hanti'.antitone hbdd
  set L := ⨅ t, m t with hL
  have hL0 : 0 ≤ L := le_ciInf fun t => (hpos t).le
  rcases hL0.lt_or_eq with hLpos | hLz
  · exfalso
    have hcφ : ContinuousAt (phiMap lam h) L := by
      have : ContinuousAt h L := hcont.continuousAt (Ioi_mem_nhds hLpos)
      exact ((continuousAt_const.mul continuousAt_id).mul (continuousAt_const.sub this))
    have h1 : Tendsto (fun t => phiMap lam h (m t)) atTop (𝓝 (phiMap lam h L)) :=
      hcφ.tendsto.comp hlim
    have h2 : Tendsto (fun t => phiMap lam h (m t)) atTop (𝓝 L) :=
      ((tendsto_add_atTop_iff_nat 1).2 hlim).congr fun t => hdyn t
    have hfix : phiMap lam h L = L := tendsto_nhds_unique h1 h2
    have hhL : h L = h mb := by
      unfold phiMap at hfix
      have : lam * (1 - h L) = 1 := by
        have := mul_right_cancel₀ hLpos.ne' (by linarith : lam * (1 - h L) * L = 1 * L)
        linarith
      have := mul_left_cancel₀ hlam.ne' (show lam * (1 - h L) = lam * (1 - h mb) by linarith)
      linarith
    have hLm : L = mb := hanti.injOn hLpos hmb hhL
    have : L ≤ m 0 := ciInf_le hbdd 0
    linarith
  · rw [← hLz] at hlim
    exact hlim

/-- **A credible floor on the value of money rules out hyperinflation** (O&R §8.3.5.5): under the
assumptions of `hyperinflation_tendsto_zero`, for every floor `m_min > 0` there is a date at
which real balances fall below it. -/
theorem backing_rules_out_hyperinflation {lam mb mmin : ℝ} {h : ℝ → ℝ} {m : ℕ → ℝ}
    (hlam : 0 < lam) (hmb : 0 < mb) (hcont : ContinuousOn h (Set.Ioi 0))
    (hanti : StrictAntiOn h (Set.Ioi 0)) (hbar : lam * (1 - h mb) = 1) (hpos : ∀ t, 0 < m t)
    (hdyn : ∀ t, m (t + 1) = phiMap lam h (m t)) (hm0 : m 0 < mb) (hmin : 0 < mmin) :
    ∃ T, m T < mmin :=
  ((hyperinflation_tendsto_zero hlam hmb hcont hanti hbar hpos hdyn hm0).2.eventually
    (gt_mem_nhds hmin)).exists

/-- **Hyperinflation without a collapse date** (O&R pp. 543–544, the case the book omits): if
`h = C̄v' < 1` everywhere (e.g. `C̄v'(0+) < 1`), there is no `m*`, and every initial real balance
`0 < m_0 < m̄` generates a positive path that falls to zero asymptotically, with no finite date
at which money becomes worthless. -/
theorem hyperinflation_asymptotic {lam mb m0 : ℝ} {h : ℝ → ℝ} (hlam : 0 < lam) (hmb : 0 < mb)
    (hcont : ContinuousOn h (Set.Ioi 0)) (hanti : StrictAntiOn h (Set.Ioi 0))
    (hbar : lam * (1 - h mb) = 1) (hlt1 : ∀ x, 0 < x → h x < 1) (hm00 : 0 < m0)
    (hm0 : m0 < mb) :
    ∃ m : ℕ → ℝ, m 0 = m0 ∧ (∀ t, m (t + 1) = phiMap lam h (m t)) ∧ (∀ t, 0 < m t) ∧
      StrictAnti m ∧ Tendsto m atTop (𝓝 0) := by
  set m : ℕ → ℝ := fun t => (phiMap lam h)^[t] m0 with hm
  have hdyn : ∀ t, m (t + 1) = phiMap lam h (m t) := fun t => by
    simp only [hm]; rw [Function.iterate_succ_apply']
  have hpos : ∀ t, 0 < m t := by
    intro t
    induction t with
    | zero => simpa [hm] using hm00
    | succ t ih =>
      rw [hdyn t]
      unfold phiMap
      have := hlt1 _ ih
      have : 0 < 1 - h (m t) := by linarith
      positivity
  obtain ⟨h1, h2⟩ := hyperinflation_tendsto_zero hlam hmb hcont hanti hbar hpos hdyn
    (by simpa [hm] using hm0)
  exact ⟨m, by simp [hm], hdyn, hpos, h1, h2⟩

/-- **Utility is finite along paths on which `v` stays bounded** (O&R p. 545: finite utility of
the barter limit requires `v(0+) > −∞`): if `L ≤ v(m_t) ≤ U` for all `t` and `0 ≤ β < 1`, then
`Σβ^t(log C̄ + v(m_t))` converges. -/
theorem utility_summable_of_bounded {β Cbar L U : ℝ} {v : ℝ → ℝ} {m : ℕ → ℝ} (hβ0 : 0 ≤ β)
    (hβ1 : β < 1) (hL : ∀ t, L ≤ v (m t)) (hU : ∀ t, v (m t) ≤ U) :
    Summable (fun t => β ^ t * (Real.log Cbar + v (m t))) := by
  refine Summable.of_norm_bounded (g := fun t => (|Real.log Cbar| + |L| + |U|) * β ^ t)
    ((summable_geometric_of_lt_one hβ0 hβ1).mul_left _) fun t => ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hβ0 t), mul_comm]
  refine mul_le_mul_of_nonneg_right ?_ (pow_nonneg hβ0 t)
  have h1 := hL t
  have h2 := hU t
  rw [abs_le]
  constructor
  · linarith [neg_abs_le (Real.log Cbar), neg_abs_le L, abs_nonneg U]
  · linarith [le_abs_self (Real.log Cbar), le_abs_self U, abs_nonneg L]

/-! ## Exercise 2: transactions technologies instead of money in the utility function -/

/-- Wealth when the period expenditure needed to finance consumption `C` with real balances `m`
is `E_s(C, m)` (Exercise 2, O&R pp. 599–600): `A_{s+1} = (1+r)(A_s + y_s − E_s(C_s, m_s))`. -/
noncomputable def wealthE (r A0 : ℝ) (y : ℕ → ℝ) (E : ℕ → ℝ → ℝ → ℝ) (C m : ℕ → ℝ) : ℕ → ℝ
  | 0 => A0
  | s + 1 => (1 + r) * (wealthE r A0 y E C m s + y s - E s (C s) (m s))

/-- An admissible plan in the transactions-technology model: positive consumption and real
balances, summable utility `Σβ^s u(C_s)` (O&R Exercise 2's (33) replacement) and no Ponzi
scheme. -/
def AdmissibleE (u : ℝ → ℝ) (β r A0 : ℝ) (y : ℕ → ℝ) (E : ℕ → ℝ → ℝ → ℝ) (C m : ℕ → ℝ) :
    Prop :=
  (∀ s, 0 < C s) ∧ (∀ s, 0 < m s) ∧ Summable (fun s => β ^ s * u (C s)) ∧
    NoPonzi r (wealthE r A0 y E C m)

/-- An optimal plan in the transactions-technology model (Exercise 2).
Context: O&R §8.3.5, pp. 538–546. -/
def IsOptimalE (u : ℝ → ℝ) (β r A0 : ℝ) (y : ℕ → ℝ) (E : ℕ → ℝ → ℝ → ℝ) (C m : ℕ → ℝ) :
    Prop :=
  AdmissibleE u β r A0 y E C m ∧ ∀ C' m', AdmissibleE u β r A0 y E C' m' →
    ∑' s, β ^ s * u (C' s) ≤ ∑' s, β ^ s * u (C s)

/-- **Finite perturbations of an optimal plan** (the tool for Exercise 2's first-order
conditions): if a family of plans differs from the optimum only on a finite set `S` of dates,
leaves the wealth path unchanged from some date on, and stays positive for small `ε`, then the
utility of the perturbed dates has a local maximum at `ε = 0`.
Context: O&R §8.3.5, pp. 538–546. -/
theorem localMax_of_optimalE {u : ℝ → ℝ} {β r A0 : ℝ} {y : ℕ → ℝ} {E : ℕ → ℝ → ℝ → ℝ}
    {C m : ℕ → ℝ} (hopt : IsOptimalE u β r A0 y E C m) (S : Finset ℕ) (DC Dm : ℝ → ℕ → ℝ)
    (hoffC : ∀ ε t, t ∉ S → DC ε t = C t)
    (h0 : ∀ t, t ∈ S → DC 0 t = C t)
    (hgood : ∀ᶠ ε in 𝓝 (0 : ℝ), (∀ t, 0 < DC ε t) ∧ (∀ t, 0 < Dm ε t) ∧
      ∀ᶠ T in atTop, wealthE r A0 y E (DC ε) (Dm ε) T = wealthE r A0 y E C m T) :
    IsLocalMax (fun ε => ∑ t ∈ S, β ^ t * u (DC ε t)) 0 := by
  obtain ⟨⟨_, _, hsum, hnp⟩, hmax⟩ := hopt
  filter_upwards [hgood] with ε ⟨hC, hm, hw⟩
  obtain ⟨h1, h2⟩ := tsum_eq_add_of_eqOn_compl hsum S (g := fun t => β ^ t * u (DC ε t))
    fun t ht => by simp only [hoffC ε t ht]
  have hadm : AdmissibleE u β r A0 y E (DC ε) (Dm ε) :=
    ⟨hC, hm, h1, noPonzi_congr hnp hw⟩
  have hle := hmax _ _ hadm
  rw [h2, Finset.sum_sub_distrib] at hle
  have : ∑ t ∈ S, β ^ t * u (DC 0 t) = ∑ t ∈ S, β ^ t * u (C t) :=
    Finset.sum_congr rfl fun t ht => by rw [h0 t ht]
  linarith

/-- Plans agreeing before date `k` have the same wealth at `k` (Exercise 2).
Context: O&R §8.3.5, pp. 538–546. -/
theorem wealthE_congr_before {r A0 : ℝ} {y : ℕ → ℝ} {E : ℕ → ℝ → ℝ → ℝ} {C m C' m' : ℕ → ℝ}
    {k : ℕ} (hC : ∀ t, t < k → C t = C' t) (hm : ∀ t, t < k → m t = m' t) :
    wealthE r A0 y E C m k = wealthE r A0 y E C' m' k := by
  have key : ∀ n, n ≤ k → wealthE r A0 y E C m n = wealthE r A0 y E C' m' n := by
    intro n
    induction n with
    | zero => intro _; rfl
    | succ n ih =>
      intro hn
      simp only [wealthE]
      rw [ih (by omega), hC n (by omega), hm n (by omega)]
  exact key k le_rfl

/-- Plans with the same period expenditure have the same wealth (Exercise 2).
Context: O&R §8.3.5, pp. 538–546. -/
theorem wealthE_congr_expenditure {r A0 : ℝ} {y : ℕ → ℝ} {E : ℕ → ℝ → ℝ → ℝ}
    {C m C' m' : ℕ → ℝ} (h : ∀ t, E t (C' t) (m' t) = E t (C t) (m t)) (T : ℕ) :
    wealthE r A0 y E C' m' T = wealthE r A0 y E C m T := by
  induction T with
  | zero => rfl
  | succ T ih => simp only [wealthE]; rw [ih, h T]

/-- Plans that agree from date `k` on, with equal wealth at `k`, have equal wealth afterwards.
Context: O&R §8.3.5, pp. 538–546. -/
theorem wealthE_congr_after {r A0 : ℝ} {y : ℕ → ℝ} {E : ℕ → ℝ → ℝ → ℝ} {C m C' m' : ℕ → ℝ}
    {k : ℕ} (hk : wealthE r A0 y E C m k = wealthE r A0 y E C' m' k)
    (hC : ∀ s, k ≤ s → C s = C' s) (hm : ∀ s, k ≤ s → m s = m' s) (n : ℕ) :
    wealthE r A0 y E C m (k + n) = wealthE r A0 y E C' m' (k + n) := by
  induction n with
  | zero => exact hk
  | succ n ih =>
    rw [← add_assoc]
    simp only [wealthE]
    rw [ih, hC _ (by omega), hm _ (by omega)]

/-- **Exercise 2(a), the money first-order condition** (O&R p. 600): with the budget
`B_{t+1} + M_t/P_t = (1+r)B_t + M_{t−1}/P_t + Y g(M_t/P_t) − C_t − T_t`, i.e. period expenditure
`C + ι m − Y g(m)`, at an optimum `Y g'(m_s) = ι_s = i_{s+1}/(1 + i_{s+1})` (given `u' > 0`).
Proof: hold `ε` more real balances and adjust consumption to keep expenditure unchanged. -/
theorem ex2_money_foc {u u' g g' : ℝ → ℝ} {β r A0 Y : ℝ} {y ι C m : ℕ → ℝ} (hβ : 0 < β)
    (hu : ∀ c, 0 < c → HasDerivAt u (u' c) c) (hu' : ∀ c, 0 < c → 0 < u' c)
    (hg : ∀ k, 0 < k → HasDerivAt g (g' k) k)
    (hopt : IsOptimalE u β r A0 y (fun s c k => c + ι s * k - Y * g k) C m) (s : ℕ) :
    Y * g' (m s) = ι s := by
  have hC := hopt.1.1
  have hm := hopt.1.2.1
  set DC : ℝ → ℕ → ℝ := fun ε t =>
    if t = s then C s - ι s * ε + Y * (g (m s + ε) - g (m s)) else C t with hDC
  set Dm : ℝ → ℕ → ℝ := fun ε t => if t = s then m s + ε else m t with hDm
  have hg0 : HasDerivAt g (g' (m s)) (m s + 0) := by rw [add_zero]; exact hg _ (hm s)
  have h1 : HasDerivAt (fun ε => g (m s + ε)) (g' (m s)) 0 := hg0.comp_const_add (m s) 0
  have hcontg : ContinuousAt (fun ε => g (m s + ε)) 0 := h1.continuousAt
  have hev1 : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < C s - ι s * ε + Y * (g (m s + ε) - g (m s)) := by
    have hc : ContinuousAt (fun ε => C s - ι s * ε + Y * (g (m s + ε) - g (m s))) 0 :=
      ((continuousAt_const.sub (continuousAt_const.mul continuousAt_id)).add
        (continuousAt_const.mul (hcontg.sub continuousAt_const)))
    exact hc.eventually (lt_mem_nhds (by simpa using hC s))
  have hev2 : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < m s + ε :=
    ((continuous_const.add continuous_id).continuousAt (x := 0)).eventually
      (lt_mem_nhds (by simpa using hm s))
  have hloc := localMax_of_optimalE hopt {s} DC Dm
    (fun ε t ht => by simp only [Finset.mem_singleton] at ht; simp [hDC, ht])
    (fun t ht => by simp only [Finset.mem_singleton] at ht; subst ht; simp [hDC])
    (by
      filter_upwards [hev1, hev2] with ε h1 h2
      refine ⟨fun t => ?_, fun t => ?_, Filter.Eventually.of_forall fun T =>
        wealthE_congr_expenditure (fun t => ?_) T⟩
      · by_cases ht : t = s
        · subst ht; simpa [hDC] using h1
        · simpa [hDC, ht] using hC t
      · by_cases ht : t = s
        · subst ht; simpa [hDm] using h2
        · simpa [hDm, ht] using hm t
      · by_cases ht : t = s
        · subst ht; simp [hDC, hDm]; ring
        · simp [hDC, hDm, ht])
  simp only [Finset.sum_singleton, hDC, ↓reduceIte] at hloc
  have hin : HasDerivAt (fun ε => C s - ι s * ε + Y * (g (m s + ε) - g (m s)))
      (-ι s + Y * g' (m s)) 0 :=
    (((hasDerivAt_const (0 : ℝ) (C s)).sub ((hasDerivAt_id (0 : ℝ)).const_mul (ι s))).add
      ((h1.sub_const (g (m s))).const_mul Y)).congr_deriv (by ring)
  have hU : HasDerivAt u (u' (C s)) (C s - ι s * 0 + Y * (g (m s + 0) - g (m s))) := by
    simpa using hu _ (hC s)
  have hd := ((hU.comp (0 : ℝ) hin).const_mul (β ^ s))
  have h0 := hloc.hasDerivAt_eq_zero hd
  have hb := pow_pos hβ s
  have hu0 := hu' _ (hC s)
  have : u' (C s) * (-ι s + Y * g' (m s)) = 0 := by
    have := (mul_eq_zero.1 h0).resolve_left hb.ne'
    linarith
  have := (mul_eq_zero.1 this).resolve_left hu0.ne'
  linarith

/-- **Exercise 2(a) and 2(c), the consumption Euler equation** (O&R p. 600): if period
expenditure is `C w_s(m) + F_s(m)` with `w > 0` (`w = 1` in part (a), `w = 1/g(m)` in part (c)),
then at an optimum `u'(C_s)/w_s = (1+r)β u'(C_{s+1})/w_{s+1}`. Proof: spend `ε` less at `s` and
`(1+r)ε` more at `s + 1`. -/
theorem euler_of_optimalE {u u' : ℝ → ℝ} {β r A0 : ℝ} {y : ℕ → ℝ} {w F : ℕ → ℝ → ℝ}
    {C m : ℕ → ℝ} (hβ : 0 < β) (hu : ∀ c, 0 < c → HasDerivAt u (u' c) c)
    (hw : ∀ s, 0 < w s (m s))
    (hopt : IsOptimalE u β r A0 y (fun s c k => c * w s k + F s k) C m) (s : ℕ) :
    u' (C s) / w s (m s) = (1 + r) * β * (u' (C (s + 1)) / w (s + 1) (m (s + 1))) := by
  have hC := hopt.1.1
  set a := (w s (m s))⁻¹ with ha
  set b := (1 + r) * (w (s + 1) (m (s + 1)))⁻¹ with hb
  set DC : ℝ → ℕ → ℝ := fun ε t =>
    if t = s then C s + ε * (-a) else if t = s + 1 then C (s + 1) + ε * b else C t with hDC
  have hne : s + 1 ≠ s := Nat.succ_ne_self s
  have hDs : ∀ ε, DC ε s = C s + ε * (-a) := fun ε => by simp [hDC]
  have hDs1 : ∀ ε, DC ε (s + 1) = C (s + 1) + ε * b := fun ε => by simp [hDC]
  have hoff : ∀ ε t, t ∉ ({s, s + 1} : Finset ℕ) → DC ε t = C t := fun ε t ht => by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ht
    simp [hDC, ht.1, ht.2]
  have hwe : ∀ ε n, wealthE r A0 y (fun s c k => c * w s k + F s k) (DC ε) m (s + 2 + n) =
      wealthE r A0 y (fun s c k => c * w s k + F s k) C m (s + 2 + n) := by
    intro ε n
    refine wealthE_congr_after ?_ (fun t ht => hoff ε t (by simp; omega)) (fun _ _ => rfl) n
    have hbef : wealthE r A0 y (fun s c k => c * w s k + F s k) (DC ε) m s =
        wealthE r A0 y (fun s c k => c * w s k + F s k) C m s :=
      wealthE_congr_before (fun t ht => hoff ε t (by simp; omega)) (fun _ _ => rfl)
    rw [show s + 2 = s + 1 + 1 by ring]
    simp only [wealthE]
    rw [hbef, hDs, hDs1]
    have h1 := (hw s).ne'
    have h2 := (hw (s + 1)).ne'
    rw [ha, hb]
    field_simp
    ring
  have hev1 : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < C s + ε * (-a) :=
    ((by fun_prop : Continuous fun ε : ℝ => C s + ε * (-a)).tendsto 0).eventually
      (lt_mem_nhds (by simpa using hC s))
  have hev2 : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < C (s + 1) + ε * b :=
    ((by fun_prop : Continuous fun ε : ℝ => C (s + 1) + ε * b).tendsto 0).eventually
      (lt_mem_nhds (by simpa using hC (s + 1)))
  have hloc := localMax_of_optimalE hopt {s, s + 1} DC (fun _ => m) hoff
    (fun t ht => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl
      · rw [hDs]; ring
      · rw [hDs1]; ring)
    (by
      filter_upwards [hev1, hev2] with ε h1 h2
      refine ⟨fun t => ?_, hopt.1.2.1, ?_⟩
      · by_cases ht : t = s
        · rw [ht, hDs]; exact h1
        by_cases ht1 : t = s + 1
        · rw [ht1, hDs1]; exact h2
        rw [hoff ε t (by simp [ht, ht1])]
        exact hC t
      · filter_upwards [eventually_ge_atTop (s + 2)] with T hT
        obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hT
        exact hwe ε n)
  simp only [Finset.sum_pair hne.symm, hDs, hDs1] at hloc
  have hA : HasDerivAt (fun ε => β ^ s * u (C s + ε * (-a))) (β ^ s * (u' (C s) * (-a))) 0 := by
    have h1 : HasDerivAt (fun ε : ℝ => C s + ε * (-a)) (-a) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const (-a)).const_add (C s)
    have h2 : HasDerivAt u (u' (C s)) (C s + 0 * (-a)) := by simpa using hu _ (hC s)
    exact (h2.comp (0 : ℝ) h1).const_mul _
  have hB : HasDerivAt (fun ε => β ^ (s + 1) * u (C (s + 1) + ε * b))
      (β ^ (s + 1) * (u' (C (s + 1)) * b)) 0 := by
    have h1 : HasDerivAt (fun ε : ℝ => C (s + 1) + ε * b) b 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const b).const_add (C (s + 1))
    have h2 : HasDerivAt u (u' (C (s + 1))) (C (s + 1) + 0 * b) := by
      simpa using hu _ (hC (s + 1))
    exact (h2.comp (0 : ℝ) h1).const_mul _
  have h0 := hloc.hasDerivAt_eq_zero (hA.add hB)
  rw [pow_succ] at h0
  have hβs : 0 < β ^ s := pow_pos hβ s
  have h3 : β ^ s * (u' (C s) * a - (1 + r) * β * (u' (C (s + 1)) *
      (w (s + 1) (m (s + 1)))⁻¹)) = 0 := by
    rw [hb] at h0; linarith
  have := (mul_eq_zero.1 h3).resolve_left hβs.ne'
  rw [ha] at this
  simp only [div_eq_mul_inv]
  linarith

/-- **Exercise 2(c), the money first-order condition** (O&R p. 600, "don't expect a neat
solution"): with `P_t C_t = X_t g(M_t/P_t)`, real expenditure is `C/g(m) + ι m`, and at an
optimum `ι_s g(m_s)² = g'(m_s) C_s`, i.e. `i/(1+i) = C g'(m)/g(m)²`. -/
theorem ex2c_money_foc {u u' g g' : ℝ → ℝ} {β r A0 : ℝ} {y ι C m : ℕ → ℝ} (hβ : 0 < β)
    (hu : ∀ c, 0 < c → HasDerivAt u (u' c) c) (hu' : ∀ c, 0 < c → 0 < u' c)
    (hg : ∀ k, 0 < k → HasDerivAt g (g' k) k) (hgpos : ∀ k, 0 < k → 0 < g k)
    (hopt : IsOptimalE u β r A0 y (fun s c k => c / g k + ι s * k) C m) (s : ℕ) :
    ι s * g (m s) ^ 2 = g' (m s) * C s := by
  have hC := hopt.1.1
  have hm := hopt.1.2.1
  have hgs := hgpos _ (hm s)
  set K := C s / g (m s) with hK
  set DC : ℝ → ℕ → ℝ := fun ε t =>
    if t = s then g (m s + ε) * (K - ι s * ε) else C t with hDC
  set Dm : ℝ → ℕ → ℝ := fun ε t => if t = s then m s + ε else m t with hDm
  have hg0 : HasDerivAt g (g' (m s)) (m s + 0) := by rw [add_zero]; exact hg _ (hm s)
  have h1 : HasDerivAt (fun ε => g (m s + ε)) (g' (m s)) 0 := hg0.comp_const_add (m s) 0
  have hin : HasDerivAt (fun ε => g (m s + ε) * (K - ι s * ε))
      (g' (m s) * K - g (m s) * ι s) 0 := by
    have h2 : HasDerivAt (fun ε : ℝ => K - ι s * ε) (-ι s) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).const_mul (ι s)).const_sub K
    exact (h1.mul h2).congr_deriv (by simp; ring)
  have hev1 : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < g (m s + ε) * (K - ι s * ε) :=
    hin.continuousAt.eventually (lt_mem_nhds (by
      simp only [add_zero, mul_zero, sub_zero, hK]; field_simp; exact hC s))
  have hev2 : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < m s + ε :=
    ((continuous_const.add continuous_id).continuousAt (x := 0)).eventually
      (lt_mem_nhds (by simpa using hm s))
  have hloc := localMax_of_optimalE hopt {s} DC Dm
    (fun ε t ht => by simp only [Finset.mem_singleton] at ht; simp [hDC, ht])
    (fun t ht => by
      simp only [Finset.mem_singleton] at ht; subst ht
      simp only [hDC, ↓reduceIte, add_zero, mul_zero, sub_zero, hK]; field_simp)
    (by
      filter_upwards [hev1, hev2] with ε h1 h2
      refine ⟨fun t => ?_, fun t => ?_, Filter.Eventually.of_forall fun T =>
        wealthE_congr_expenditure (fun t => ?_) T⟩
      · by_cases ht : t = s
        · subst ht; simpa [hDC] using h1
        · simpa [hDC, ht] using hC t
      · by_cases ht : t = s
        · subst ht; simpa [hDm] using h2
        · simpa [hDm, ht] using hm t
      · by_cases ht : t = s
        · subst ht
          have := (hgpos _ h2).ne'
          simp only [hDC, hDm, ↓reduceIte, hK]
          field_simp
          ring
        · simp [hDC, hDm, ht])
  simp only [Finset.sum_singleton, hDC, ↓reduceIte] at hloc
  have hU : HasDerivAt u (u' (C s)) (g (m s + 0) * (K - ι s * 0)) := by
    have : g (m s + 0) * (K - ι s * 0) = C s := by
      simp only [add_zero, mul_zero, sub_zero, hK]; field_simp
    rw [this]; exact hu _ (hC s)
  have h0 := hloc.hasDerivAt_eq_zero ((hU.comp (0 : ℝ) hin).const_mul (β ^ s))
  have hb := pow_pos hβ s
  have hu0 := hu' _ (hC s)
  have h3 : u' (C s) * (g' (m s) * K - g (m s) * ι s) = 0 :=
    (mul_eq_zero.1 h0).resolve_left hb.ne'
  have h4 := (mul_eq_zero.1 h3).resolve_left hu0.ne'
  rw [hK] at h4
  field_simp at h4
  linarith

/-- **Exercise 2(b): constant consumption** (O&R p. 600): with `(1+r)β = 1` and `u'` strictly
decreasing, the Euler equation of part (a) forces `C_s = C_0` for all `s`. -/
theorem ex2_constant_consumption {u' : ℝ → ℝ} {β r : ℝ} {C : ℕ → ℝ} (hβr : (1 + r) * β = 1)
    (hC : ∀ s, 0 < C s) (hanti : StrictAntiOn u' (Set.Ioi 0))
    (he : ∀ s, u' (C s) / 1 = (1 + r) * β * (u' (C (s + 1)) / 1)) (s : ℕ) : C s = C 0 := by
  induction s with
  | zero => rfl
  | succ s ih =>
    have h := he s
    rw [hβr, one_mul, div_one, div_one] at h
    rw [← ih]
    exact (hanti.injOn (hC (s + 1)) (hC s) h.symm)

/-- **Exercise 2(b): the dynamics of real balances** (O&R p. 600): with `(1+r)β = 1` and money
growing at `1 + μ`, the money condition `Y g'(m_s) = ι_s` of part (a) is
`(β/(1+μ)) m_{s+1} = m_s (1 − Y g'(m_s))` — (46) with `C̄v'` replaced by `Yg'`. -/
theorem ex2_dynamics_iff {g' : ℝ → ℝ} {β r μ Y : ℝ} {N P : ℕ → ℝ} (hβr : (1 + r) * β = 1)
    (hμ : 0 < 1 + μ) (hN : ∀ s, 0 < N s) (hP : ∀ s, 0 < P s)
    (hgrowth : ∀ s, N (s + 1) = (1 + μ) * N s) (s : ℕ) :
    Y * g' (N (s + 1) / P s) = userCost r P s ↔
      β / (1 + μ) * (N (s + 1 + 1) / P (s + 1)) =
        N (s + 1) / P s * (1 - Y * g' (N (s + 1) / P s)) := by
  rw [userCost_of_beta hβr]
  exact bubble_dynamics_iff (h := fun k => Y * g' k) hμ hN hP hgrowth s

/-- **Exercise 2(b): the no-bubble path** (O&R p. 600): if `Y g'(m̄) = 1 − β/(1+μ)`, the price
level `P_s = N_{s+1}/m̄` (inflation `μ`) satisfies the money condition at every date, and `m̄` is
the unique such level when `g'` is strictly decreasing. -/
theorem ex2_steady_state {g' : ℝ → ℝ} {β r μ Y mb : ℝ} {N : ℕ → ℝ} (hβr : (1 + r) * β = 1)
    (hμ : 0 < 1 + μ) (hN : ∀ s, 0 < N s) (hgrowth : ∀ s, N (s + 1) = (1 + μ) * N s)
    (hmb : 0 < mb) (hss : Y * g' mb = 1 - β / (1 + μ)) :
    (∀ s, Y * g' (N (s + 1) / (N (s + 1) / mb)) = userCost r (fun s => N (s + 1) / mb) s) ∧
    (∀ s, N (s + 1 + 1) / mb = (1 + μ) * (N (s + 1) / mb)) ∧
    (StrictAntiOn (fun k => Y * g' k) (Set.Ioi 0) →
      ∀ m', 0 < m' → Y * g' m' = 1 - β / (1 + μ) → m' = mb) := by
  refine ⟨fun s => ?_, fun s => by rw [hgrowth (s + 1)]; ring, fun hanti m' hm' h => ?_⟩
  · have h1 := (hN (s + 1)).ne'
    have h2 := (hN (s + 1 + 1)).ne'
    rw [userCost_of_beta hβr, show N (s + 1) / (N (s + 1) / mb) = mb by field_simp, hss,
      hgrowth (s + 1)]
    field_simp
  · exact hanti.injOn hm' hmb (h.trans hss.symm)

/-- **Exercise 2(d), deflations are ruled out** (O&R p. 600, `μ = 0`): if the transactions
technology `g` is concave, nondecreasing and bounded above (`g → 1`), the individual TVC fails
along every positive deflationary path of `β m_{t+1} = m_t(1 − Y g'(m_t))`
(`bounded_rules_out_deflation` with `C̄v'` replaced by `Yg'`). -/
theorem ex2_no_deflation {β Y V : ℝ} {g g' : ℝ → ℝ} {m : ℕ → ℝ} (hβ : 0 < β) (hY : 0 < Y)
    (hpos : ∀ t, 0 < m t) (hdyn : ∀ t, β * m (t + 1) = m t * (1 - Y * g' (m t)))
    (hg : ConcaveOn ℝ (Set.Ioi 0) g) (hg' : ∀ k, 0 < k → HasDerivAt g (g' k) k)
    (hnn : ∀ k, 0 < k → 0 ≤ g' k) (hV : ∀ k, 0 < k → g k ≤ V)
    (hm0 : Y * g' (m 0) < 1 - β) : ¬ BubbleTVC β m := by
  have hanti : AntitoneOn (fun k => Y * g' k) (Set.Ioi 0) := by
    intro x hx y hy hxy
    rcases hxy.lt_or_eq with hlt | heq
    · have h1 := hg.slope_le_of_hasDerivAt hx hy hlt (hg' x hx)
      have h2 := hg.le_slope_of_hasDerivAt hx hy hlt (hg' y hy)
      exact mul_le_mul_of_nonneg_left (h2.trans h1) hY.le
    · rw [heq]
  exact bounded_rules_out_deflation hβ hY hpos hdyn hg hg' hanti hnn hV hm0

/-- **Exercise 2(d), hyperinflations cannot be ruled out** (O&R p. 600): since `g ≥ 0`
(so `g(0+) > −∞`), condition (52) holds, `m g'(m) → 0` as `m → 0` (`fn34_sharpened`), which is
exactly what allows speculative hyperinflations in Figure 8.3. -/
theorem ex2_hyperinflation_possible {g g' : ℝ → ℝ} (hg : ConcaveOn ℝ (Set.Ioi 0) g)
    (hg' : ∀ k, 0 < k → HasDerivAt g (g' k) k) (hnn : ∀ k, 0 < k → 0 ≤ g' k)
    (hg0 : ∀ k, 0 < k → 0 ≤ g k) : Tendsto (fun x => x * g' x) (𝓝[>] 0) (𝓝 0) :=
  fn34_sharpened hg hg' hnn hg0

/-- **`equilibrium_iff` without a summability hypothesis, `v` bounded along the path** (O&R
§8.3.5): if `L ≤ v(m_s) ≤ U` for all `s` (e.g. `v` bounded below with real balances bounded
above), lifetime utility is automatically finite and the equilibrium characterisation holds. -/
theorem equilibrium_iff_of_bounded {v v' : ℝ → ℝ} {β r μ Ybar B0 L Ub : ℝ} {N P : ℕ → ℝ}
    (hβ0 : 0 < β) (hβ1 : β < 1) (hβr : (1 + r) * β = 1) (hμ : 0 < 1 + μ)
    (hC : 0 < Ybar + r * B0) (hN : ∀ s, 0 < N s) (hP : ∀ s, 0 < P s)
    (hgrowth : ∀ s, N (s + 1) = (1 + μ) * N s) (hv : ConcaveOn ℝ (Set.Ioi 0) v)
    (hv' : ∀ k, 0 < k → HasDerivAt v (v' k) k) (hL : ∀ s, L ≤ v (N (s + 1) / P s))
    (hU : ∀ s, v (N (s + 1) / P s) ≤ Ub) :
    IsOptimal (fun c k => Real.log c + v k) β r ((1 + r) * B0 + N 0 / P 0)
        (fun s => Ybar + (N (s + 1) - N s) / P s) (userCost r P) (fun _ => Ybar + r * B0)
        (fun s => N (s + 1) / P s) ↔
      (∀ s, β / (1 + μ) * (N (s + 1 + 1) / P (s + 1)) =
        N (s + 1) / P s * (1 - (Ybar + r * B0) * v' (N (s + 1) / P s))) ∧
      BubbleTVC β (fun s => N (s + 1) / P s) :=
  equilibrium_iff hβ0 hβ1 hβr hμ hC hN hP hgrowth hv hv'
    (utility_summable_of_bounded (m := fun s => N (s + 1) / P s) hβ0.le hβ1 hL hU)

/-- **`equilibrium_iff` for real balances bounded away from zero and above** (O&R §8.3.5): with
`v` nondecreasing and `0 < m_lo ≤ m_s ≤ m_hi`, no summability hypothesis is needed. -/
theorem equilibrium_iff_of_balances_bounded {v v' : ℝ → ℝ} {β r μ Ybar B0 mlo mhi : ℝ}
    {N P : ℕ → ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) (hβr : (1 + r) * β = 1) (hμ : 0 < 1 + μ)
    (hC : 0 < Ybar + r * B0) (hN : ∀ s, 0 < N s) (hP : ∀ s, 0 < P s)
    (hgrowth : ∀ s, N (s + 1) = (1 + μ) * N s) (hv : ConcaveOn ℝ (Set.Ioi 0) v)
    (hv' : ∀ k, 0 < k → HasDerivAt v (v' k) k) (hmono : MonotoneOn v (Set.Ioi 0))
    (hlo0 : 0 < mlo) (hlo : ∀ s, mlo ≤ N (s + 1) / P s) (hhi : ∀ s, N (s + 1) / P s ≤ mhi) :
    IsOptimal (fun c k => Real.log c + v k) β r ((1 + r) * B0 + N 0 / P 0)
        (fun s => Ybar + (N (s + 1) - N s) / P s) (userCost r P) (fun _ => Ybar + r * B0)
        (fun s => N (s + 1) / P s) ↔
      (∀ s, β / (1 + μ) * (N (s + 1 + 1) / P (s + 1)) =
        N (s + 1) / P s * (1 - (Ybar + r * B0) * v' (N (s + 1) / P s))) ∧
      BubbleTVC β (fun s => N (s + 1) / P s) :=
  equilibrium_iff_of_bounded hβ0 hβ1 hβr hμ hC hN hP hgrowth hv hv' (L := v mlo) (Ub := v mhi)
    (fun s => hmono hlo0 (lt_of_lt_of_le hlo0 (hlo s)) (hlo s))
    (fun s => hmono (lt_of_lt_of_le hlo0 (hlo s)) (lt_of_lt_of_le hlo0 ((hlo s).trans (hhi s)))
      (hhi s))

end ObstfeldRogoff.MoneyExchangeRates.MonetaryBubbles
