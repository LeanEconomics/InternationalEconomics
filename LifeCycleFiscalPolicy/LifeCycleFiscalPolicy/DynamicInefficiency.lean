/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Dynamic inefficiency

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*,
Appendix 3A, pp. 191–195. Output per efficiency unit of labour is `f(k)`, and
efficiency labour grows at `1 + z = (1 + n)(1 + g)`. Capital per efficiency unit
obeys `k_{t+1} = (k_t + f(k_t) − c_t)/(1 + z)`.

* **Steady-state consumption and the golden rule** (O&R (3.77)–(3.78)): steady-state
  consumption is `c̄ = f(k̄) − zk̄`. For concave `f` it is maximised where
  `f'(k̄) = r̄ = z`.
* **Pareto inefficiency when `r̄ < z`** (pp. 192–193). If `f'(k̄) < z`, cut capital once
  to some `k < k̄` with `f'(k) ≤ z` (one always exists nearby) and hold it there. Total
  consumption is strictly higher on the first date and at least as high on every
  later date, so everyone can be made better off. If instead `f'(k̄) > z`, raising
  capital requires lower consumption on the first date.
* **Ponzi games** (§3A.2.1): debt rolled over at rate `r` shrinks relative to output
  growing at `z` iff `r < z`.
* **Bubbles** (§3A.2.2): a paper asset whose price rises at `r` stays affordable to
  the young forever when `r ≤ z` (given an affordable start), but not when `r > z`.
* **The empirical criterion** (§3A.3): `r > z` iff the profit share `rK/Y` exceeds the
  investment share `zK/Y`.

The converse — that `r̄ > z` rules out every Pareto improvement (Cass 1972) — is
deferred by the book to Chapter 7 and is not formalised here.
-/

namespace ObstfeldRogoff.LifeCycleFiscalPolicy.DynamicInefficiency

open Set Filter Topology

/-- Steady-state consumption per efficiency unit `c̄ = f(k̄) − zk̄`, O&R (3.77). -/
def steadyConsumption (f : ℝ → ℝ) (z k : ℝ) : ℝ := f k - z * k

/-- The law of motion `k_{t+1} = (k_t + f(k_t) − c_t)/(1 + z)` holds with constant `k` iff
consumption is `c̄ = f(k) − zk` (O&R p. 192). -/
theorem steady_state_iff {f : ℝ → ℝ} {z k c : ℝ} (hz : 0 < 1 + z) :
    k = (k + f k - c) / (1 + z) ↔ c = steadyConsumption f z k := by
  unfold steadyConsumption
  rw [eq_div_iff hz.ne']
  constructor <;> intro h <;> linarith

/-- Consumption on the transition date: moving capital from `k` today to `k'` next period leaves
`c = k + f(k) − (1 + z)k'` for consumption (O&R p. 192). -/
def transitionConsumption (f : ℝ → ℝ) (z k k' : ℝ) : ℝ := k + f k - (1 + z) * k'

/-- **The golden rule**, O&R (3.78), p. 192: for concave differentiable `f`, capital with
`f'(k_G) = z` maximises steady-state consumption. -/
theorem golden_rule_max {f f' : ℝ → ℝ} {z kG : ℝ} (hconc : ConcaveOn ℝ (Ioi 0) f)
    (hd : ∀ k, 0 < k → HasDerivAt f (f' k) k) (hkG : 0 < kG) (hG : f' kG = z) {k : ℝ}
    (hk : 0 < k) : steadyConsumption f z k ≤ steadyConsumption f z kG := by
  unfold steadyConsumption
  rcases lt_trichotomy k kG with hlt | rfl | hgt
  · have h := hconc.le_slope_of_hasDerivAt hk hkG hlt (hd kG hkG)
    rw [slope_def_field, le_div_iff₀ (by linarith), hG] at h
    linarith
  · exact le_rfl
  · have h := hconc.slope_le_of_hasDerivAt hkG hk hgt (hd kG hkG)
    rw [slope_def_field, div_le_iff₀ (by linarith), hG] at h
    linarith

/-- **The golden rule is a stationary point**, O&R (3.78): `dc̄/dk = f'(k) − z`, zero iff
`f'(k) = z`. -/
theorem hasDerivAt_steadyConsumption {f : ℝ → ℝ} {z k d : ℝ} (hd : HasDerivAt f d k) :
    HasDerivAt (steadyConsumption f z) (d - z) k := by
  unfold steadyConsumption
  have h2 : HasDerivAt (fun y => z * y) z k := by simpa using (hasDerivAt_id k).const_mul z
  exact HasDerivAt.sub hd h2

/-- **Lower capital raises steady-state consumption when `f' ≤ z` there**: for concave `f`, if
`k < k̄` and `f'(k) ≤ z`, then `c̄(k) ≥ c̄(k̄)`. -/
theorem steadyConsumption_ge_of_lower {f f' : ℝ → ℝ} {z k kbar : ℝ}
    (hconc : ConcaveOn ℝ (Ioi 0) f) (hd : ∀ k, 0 < k → HasDerivAt f (f' k) k) (hk : 0 < k)
    (hlt : k < kbar) (hfk : f' k ≤ z) :
    steadyConsumption f z kbar ≤ steadyConsumption f z k := by
  unfold steadyConsumption
  have h := hconc.slope_le_of_hasDerivAt hk (hk.trans hlt) hlt (hd k hk)
  rw [slope_def_field, div_le_iff₀ (by linarith)] at h
  nlinarith

/-- **The transition date gains**, O&R pp. 192–193: cutting capital from `k̄` to `k < k̄` raises
consumption on the transition date above its steady-state level by `(1 + z)(k̄ − k) > 0`. -/
theorem transition_gain {f : ℝ → ℝ} {z k kbar : ℝ} (hz : 0 < 1 + z) (hlt : k < kbar) :
    transitionConsumption f z kbar k - steadyConsumption f z kbar = (1 + z) * (kbar - k) ∧
      steadyConsumption f z kbar < transitionConsumption f z kbar k := by
  unfold transitionConsumption steadyConsumption
  constructor
  · ring
  · nlinarith

/-- **Near an inefficient steady state there is a better capital level**: if `f'` is continuous at
`k̄ > 0` and `f'(k̄) < z`, some `0 < k < k̄` has `f'(k) < z`. -/
theorem exists_lower_capital {f' : ℝ → ℝ} {z kbar : ℝ} (hkbar : 0 < kbar)
    (hcont : ContinuousAt f' kbar) (hineff : f' kbar < z) :
    ∃ k, 0 < k ∧ k < kbar ∧ f' k < z := by
  have hev : ∀ᶠ k in 𝓝 kbar, f' k < z := hcont.eventually (gt_mem_nhds hineff)
  have hev' : ∀ᶠ k in 𝓝[<] kbar, f' k < z ∧ 0 < k :=
    (hev.filter_mono nhdsWithin_le_nhds).and
      ((lt_mem_nhds hkbar : ∀ᶠ k in 𝓝 kbar, 0 < k).filter_mono nhdsWithin_le_nhds)
  obtain ⟨k, ⟨hfk, hk0⟩, hklt⟩ := (hev'.and self_mem_nhdsWithin).exists
  exact ⟨k, hk0, hklt, hfk⟩

/-- **Dynamic inefficiency implies Pareto inefficiency**, O&R pp. 192–193: if `f` is concave and
differentiable with `f'` continuous at the steady state and `f'(k̄) = r̄ < z`, there is a feasible
capital path — cut to some `k < k̄` once and hold it there — along which total consumption is
strictly higher on the transition date and at least as high on every later date. -/
theorem pareto_improvement_of_dynamically_inefficient {f f' : ℝ → ℝ} {z kbar : ℝ}
    (hz : 0 < 1 + z) (hconc : ConcaveOn ℝ (Ioi 0) f) (hd : ∀ k, 0 < k → HasDerivAt f (f' k) k)
    (hkbar : 0 < kbar) (hcont : ContinuousAt f' kbar) (hineff : f' kbar < z) :
    ∃ k, 0 < k ∧ k < kbar ∧
      steadyConsumption f z kbar < transitionConsumption f z kbar k ∧
      steadyConsumption f z kbar ≤ steadyConsumption f z k := by
  obtain ⟨k, hk0, hklt, hfk⟩ := exists_lower_capital hkbar hcont hineff
  exact ⟨k, hk0, hklt, (transition_gain hz hklt).2,
    steadyConsumption_ge_of_lower hconc hd hk0 hklt hfk.le⟩

/-- **With `r̄ > z` more capital costs the transition date**, O&R p. 193: moving capital up to
`k' > k̄` lowers first-date consumption below its steady-state level. -/
theorem transition_loss_of_more_capital {f : ℝ → ℝ} {z kbar k' : ℝ} (hz : 0 < 1 + z)
    (hgt : kbar < k') : transitionConsumption f z kbar k' < steadyConsumption f z kbar := by
  unfold transitionConsumption steadyConsumption
  nlinarith

/-- **With `r̄ > z` less capital costs later generations**: if `f'(k̄) = r̄ > z` and `f` is concave,
steady-state consumption at any lower capital level `k < k̄` is strictly below that at `k̄`. -/
theorem steadyConsumption_lt_of_lower_efficient {f f' : ℝ → ℝ} {z k kbar : ℝ}
    (hconc : ConcaveOn ℝ (Ioi 0) f) (hd : ∀ k, 0 < k → HasDerivAt f (f' k) k) (hk : 0 < k)
    (hlt : k < kbar) (hfk : z < f' kbar) :
    steadyConsumption f z k < steadyConsumption f z kbar := by
  unfold steadyConsumption
  have h := hconc.le_slope_of_hasDerivAt hk (hk.trans hlt) hlt (hd kbar (hk.trans hlt))
  rw [slope_def_field, le_div_iff₀ (by linarith)] at h
  nlinarith

/-! ### Ponzi games and bubbles (O&R §3A.2) -/

/-- **Ponzi debt shrinks relative to output iff `r < z`**, O&R p. 194: debt `D(1 + r)^t` rolled
over at rate `r`, relative to output `Y₀(1 + z)^t`, tends to zero when `r < z`. -/
theorem ponzi_ratio_tendsto_zero {r z D Y0 : ℝ} (hr : 0 < 1 + r) (hrz : r < z) :
    Tendsto (fun t : ℕ => D * (1 + r) ^ t / (Y0 * (1 + z) ^ t)) atTop (𝓝 0) := by
  have hz : 0 < 1 + z := by linarith
  have hq0 : 0 ≤ (1 + r) / (1 + z) := div_nonneg hr.le hz.le
  have hq1 : (1 + r) / (1 + z) < 1 := (div_lt_one hz).2 (by linarith)
  have e : (fun t : ℕ => D * (1 + r) ^ t / (Y0 * (1 + z) ^ t)) =
      fun t => D / Y0 * ((1 + r) / (1 + z)) ^ t := by
    funext t
    rw [div_pow, mul_div_mul_comm]
  rw [e]
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).const_mul (D / Y0)

/-- **Ponzi debt does not shrink when `r ≥ z`**: for `D, Y₀ > 0` the debt–output ratio stays at
least `D/Y₀`. -/
theorem ponzi_ratio_ge {r z D Y0 : ℝ} (hz : 0 < 1 + z) (hrz : z ≤ r) (hD : 0 < D) (hY : 0 < Y0)
    (t : ℕ) : D / Y0 ≤ D * (1 + r) ^ t / (Y0 * (1 + z) ^ t) := by
  have h1 : 1 ≤ ((1 + r) / (1 + z)) ^ t := one_le_pow₀ ((one_le_div hz).2 (by linarith))
  have e : D * (1 + r) ^ t / (Y0 * (1 + z) ^ t) = D / Y0 * ((1 + r) / (1 + z)) ^ t := by
    rw [div_pow, mul_div_mul_comm]
  rw [e]
  exact le_mul_of_one_le_right (div_pos hD hY).le h1

/-- **Bubbles are sustainable when `r ≤ z`**, O&R p. 194: if the price of a paper asset rises at `r`
(`p_t = (1 + r)^t p₀`) and the young's saving grows at `z` (`S_t = (1 + z)^t S₀`), an affordable
start `p₀D ≤ S₀` keeps the asset affordable forever. -/
theorem bubble_affordable {r z p0 D S0 : ℝ} (hr : 0 < 1 + r) (hrz : r ≤ z) (hp : 0 ≤ p0 * D)
    (h0 : p0 * D ≤ S0) (t : ℕ) : (1 + r) ^ t * p0 * D ≤ (1 + z) ^ t * S0 := by
  have hpow : (1 + r) ^ t ≤ (1 + z) ^ t := pow_le_pow_left₀ hr.le (by linarith) t
  have hS0 : 0 ≤ S0 := hp.trans h0
  calc (1 + r) ^ t * p0 * D = (1 + r) ^ t * (p0 * D) := by ring
    _ ≤ (1 + z) ^ t * (p0 * D) := mul_le_mul_of_nonneg_right hpow hp
    _ ≤ (1 + z) ^ t * S0 := mul_le_mul_of_nonneg_left h0 (pow_nonneg (by linarith) t)

/-- **Bubbles burst when `r > z`**, O&R p. 194: for any positive initial value `p₀D > 0`, there is a
date at which the asset's value exceeds the young's saving. -/
theorem bubble_unaffordable {r z p0 D S0 : ℝ} (hz : 0 < 1 + z) (hrz : z < r)
    (hp : 0 < p0 * D) : ∃ t : ℕ, (1 + z) ^ t * S0 < (1 + r) ^ t * p0 * D := by
  have hq : 1 < (1 + r) / (1 + z) := (one_lt_div hz).2 (by linarith)
  obtain ⟨t, ht⟩ := (tendsto_pow_atTop_atTop_of_one_lt hq).eventually_gt_atTop (S0 / (p0 * D))
    |>.exists
  refine ⟨t, ?_⟩
  have hzt : 0 < (1 + z) ^ t := pow_pos hz t
  rw [div_pow, div_lt_div_iff₀ hp hzt] at ht
  nlinarith

/-- **The profit-share criterion**, O&R §3A.3, p. 194: with positive capital and output,
`r > z` iff the profit share `rK/Y` exceeds the investment share `zK/Y`. So a steady state is
dynamically inefficient iff profits are a smaller share of output than investment. -/
theorem efficiency_iff_profit_share {r z K Y : ℝ} (hK : 0 < K) (hY : 0 < Y) :
    z < r ↔ z * K / Y < r * K / Y := by
  rw [div_lt_div_iff_of_pos_right hY]
  exact (mul_lt_mul_iff_of_pos_right hK).symm

end ObstfeldRogoff.LifeCycleFiscalPolicy.DynamicInefficiency
