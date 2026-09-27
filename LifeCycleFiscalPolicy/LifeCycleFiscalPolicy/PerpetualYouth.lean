/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Infinitely lived overlapping generations (Weil 1989) and perpetual youth (Blanchard 1985)

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §3.7.3–§3.7.6,
pp. 181–191, and Chapter 3 Exercises 3 and 5, pp. 195–197.

Weil's small open economy: each vintage `v` lives forever with utility `Σ β^{s-t} log c^v_s`
(O&R (3.61)); population grows as `N_t = (1 + n) N_{t-1}`, `N_0 = 1`; newborns hold no financial
wealth (O&R (3.63)). We formalise

* the vintage budget constraint (3.62) from the flow constraint and no-Ponzi, and the log-utility
  consumption function (3.64) from (3.62) and the Euler equation;
* the vintage weights (3.65), aggregate consumption (3.66) and the generational-turnover law
  (3.67) — making explicit the book's implicit assumption that all vintages share the same
  after-tax income path, hence the same human wealth;
* the combined law of motion (3.68)–(3.69), its stability condition `(1 + r) β < 1 + n`, the
  steady state (3.70)–(3.71) and footnotes 49 and 52 (both need `n > 0`; at `n = 0` steady-state
  consumption is identically zero);
* the transitory shock (3.72), trend growth (3.73) and the claim that faster growth lowers the
  long-run asset/output ratio (proved via a partial-fraction decomposition);
* §3.7.6: the unit-tilt case `(1 + r) β = 1`, and debt as net wealth (3.74)–(3.75);
* Exercise 3 (Blanchard perpetual youth, parts (a)–(f)) and Exercise 5 (arbitrary debt paths).

Paths from date `t` are indexed by the offset `k = s - t`, and present values carry explicit
`HasSum` hypotheses.
-/

namespace ObstfeldRogoff.LifeCycleFiscalPolicy.PerpetualYouth

open Filter Topology Finset

/-! ## Budget constraint and consumption function, (3.62) and (3.64) -/

/-- Discounted telescoping behind the vintage budget constraint O&R (3.62), p. 182: if assets
obey the flow constraint `b_{k+1} = R b_k + x_k - c_k` with gross return `R > 0` and discount
factor `ρ = R⁻¹`, then for every horizon `T`,
`Σ_{k<T} ρ^k (c_k - x_k) = R b_0 - R ρ^T b_T`. -/
theorem perpetual_finite_budget {R ρ : ℝ} (hRρ : R * ρ = 1) {b x c : ℕ → ℝ}
    (hflow : ∀ k, b (k + 1) = R * b k + x k - c k) (T : ℕ) :
    ∑ k ∈ range T, ρ ^ k * (c k - x k) = R * b 0 - R * ρ ^ T * b T := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [sum_range_succ, ih]
    linear_combination ρ ^ T * hflow T + ρ ^ T * b (T + 1) * hRρ

/-- The vintage intertemporal budget constraint O&R (3.62), p. 182, derived from the flow
constraint and the no-Ponzi condition `ρ^T b_T → 0`: the present value of consumption equals
`R b_0` plus the present value of after-tax income `x`. (With `R = 1 + r` this is (3.62); with
`R = (1 + r)/φ` it is the Blanchard budget constraint of Exercise 3(c), p. 196.) -/
theorem perpetual_ibc_of_flow {R ρ : ℝ} (hRρ : R * ρ = 1) {b x c : ℕ → ℝ}
    (hflow : ∀ k, b (k + 1) = R * b k + x k - c k) {X C : ℝ}
    (hX : HasSum (fun k => ρ ^ k * x k) X) (hC : HasSum (fun k => ρ ^ k * c k) C)
    (hNP : Tendsto (fun T => ρ ^ T * b T) atTop (𝓝 0)) :
    C = R * b 0 + X := by
  have h1 : Tendsto (fun T => ∑ k ∈ range T, ρ ^ k * (c k - x k)) atTop (𝓝 (C - X)) := by
    have := (hC.sub hX).tendsto_sum_nat
    simpa [mul_sub] using this
  have h2 : Tendsto (fun T => ∑ k ∈ range T, ρ ^ k * (c k - x k)) atTop
      (𝓝 (R * b 0 - R * 0)) := by
    have : Tendsto (fun T => R * b 0 - R * (ρ ^ T * b T)) atTop (𝓝 (R * b 0 - R * 0)) :=
      tendsto_const_nhds.sub (hNP.const_mul R)
    refine this.congr fun T => ?_
    rw [perpetual_finite_budget hRρ hflow T]
    ring
  have := tendsto_nhds_unique h1 h2
  linarith

/-- Consumption out of wealth under geometric Euler dynamics, O&R (3.64), p. 182: if the
discounted consumption path satisfies `ρ c_{k+1} = δ c_k` with `0 ≤ δ < 1`, and the present
value of consumption is `W`, then `c_0 = (1 - δ) W`. -/
theorem perpetual_consumption_of_euler {ρ δ W : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ < 1) {c : ℕ → ℝ}
    (heuler : ∀ k, ρ * c (k + 1) = δ * c k) (hW : HasSum (fun k => ρ ^ k * c k) W) :
    c 0 = (1 - δ) * W := by
  have hpow : ∀ k, ρ ^ k * c k = c 0 * δ ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      linear_combination ρ ^ k * heuler k + δ * ih
  have hG : HasSum (fun k => ρ ^ k * c k) (c 0 * (1 - δ)⁻¹) := by
    simp_rw [hpow]
    exact (hasSum_geometric_of_lt_one hδ0 hδ1).mul_left (c 0)
  have hne : (1 - δ) ≠ 0 := by linarith
  rw [hW.unique hG]
  field_simp

/-- The Weil consumption function O&R (3.64), p. 182, derived: under the flow constraint
`b_{k+1} = (1 + r) b_k + (y_k - τ_k) - c_k`, no-Ponzi, and the log-utility Euler equation
`c_{k+1} = (1 + r) β c_k`, consumption is
`c_0 = (1 - β) [(1 + r) b_0 + Σ (1 + r)^{-k} (y_k - τ_k)]`. -/
theorem weil_consumption_function {r β : ℝ} (hr : 0 < 1 + r) (hβ0 : 0 ≤ β) (hβ1 : β < 1)
    {b x c : ℕ → ℝ} (hflow : ∀ k, b (k + 1) = (1 + r) * b k + x k - c k)
    (heuler : ∀ k, c (k + 1) = (1 + r) * β * c k) {X C : ℝ}
    (hX : HasSum (fun k => ((1 + r)⁻¹) ^ k * x k) X)
    (hC : HasSum (fun k => ((1 + r)⁻¹) ^ k * c k) C)
    (hNP : Tendsto (fun T => ((1 + r)⁻¹) ^ T * b T) atTop (𝓝 0)) :
    c 0 = (1 - β) * ((1 + r) * b 0 + X) := by
  have hRρ : (1 + r) * (1 + r)⁻¹ = 1 := mul_inv_cancel₀ hr.ne'
  rw [← perpetual_ibc_of_flow hRρ hflow hX hC hNP]
  refine perpetual_consumption_of_euler hβ0 hβ1 (fun k => ?_) hC
  rw [heuler k]
  field_simp

/-! ## Aggregation over vintages, (3.65)–(3.67) -/

/-- Size of vintage `v` in Weil's economy, O&R p. 183: vintage `0` has `N_0 = 1` member and
vintage `v ≥ 1` has `N_v - N_{v-1} = n (1 + n)^{v-1}` members. -/
def vintageSize (n : ℝ) : ℕ → ℝ
  | 0 => 1
  | v + 1 => n * (1 + n) ^ v

/-- Aggregate per capita value of a vintage-indexed variable on date `t`, O&R (3.65), p. 183:
`(x^0 + n x^1 + ... + n (1 + n)^{t-1} x^t) / (1 + n)^t`. -/
noncomputable def vintageAgg (n : ℝ) (t : ℕ) (x : ℕ → ℝ) : ℝ :=
  (∑ v ∈ range (t + 1), vintageSize n v * x v) / (1 + n) ^ t

/-- Population accounting behind O&R (3.65), p. 183: the vintages alive on date `t` sum to the
total population `N_t = (1 + n)^t`. -/
theorem sum_vintageSize (n : ℝ) (t : ℕ) :
    ∑ v ∈ range (t + 1), vintageSize n v = (1 + n) ^ t := by
  induction t with
  | zero => simp [vintageSize]
  | succ t ih =>
    rw [sum_range_succ, ih]
    simp only [vintageSize]
    ring

/-- The vintage weights of O&R (3.65), p. 183, sum to one, so the aggregate of a variable that
is the same for every vintage is that common value. -/
theorem vintageAgg_const {n : ℝ} (hn : 0 < 1 + n) (t : ℕ) (a : ℝ) :
    vintageAgg n t (fun _ => a) = a := by
  have : (1 + n) ^ t ≠ 0 := pow_ne_zero _ hn.ne'
  unfold vintageAgg
  rw [← sum_mul, sum_vintageSize]
  field_simp

/-- Linearity of the aggregation (3.65), O&R p. 183 ("the preceding linear aggregation
procedure can be applied to any other variable"). -/
theorem vintageAgg_affine {n : ℝ} (hn : 0 < 1 + n) (t : ℕ) (p q : ℝ) (x y : ℕ → ℝ) :
    vintageAgg n t (fun v => p * x v + q * y v) = p * vintageAgg n t x + q * vintageAgg n t y := by
  unfold vintageAgg
  have : (1 + n) ^ t ≠ 0 := pow_ne_zero _ hn.ne'
  field_simp
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun v _ => ?_
  ring

/-- The aggregate depends only on the vintages alive on date `t` (O&R (3.65), p. 183). -/
theorem vintageAgg_congr {n : ℝ} {t : ℕ} {x y : ℕ → ℝ} (h : ∀ v ≤ t, x v = y v) :
    vintageAgg n t x = vintageAgg n t y := by
  unfold vintageAgg
  congr 1
  refine sum_congr rfl fun v hv => ?_
  rw [h v (Nat.lt_succ_iff.mp (mem_range.mp hv))]

/-- Aggregation of the consumption functions (3.64) with vintage-specific human wealth `H^v`,
O&R p. 183: `c_t = (1 - β) [(1 + r) b^P_t + H_t]` where `H_t` is aggregate human wealth. -/
theorem weil_aggregate_consumption_general {n r β : ℝ} (hn : 0 < 1 + n) {t : ℕ}
    {c b H : ℕ → ℝ} (hc : ∀ v ≤ t, c v = (1 - β) * ((1 + r) * b v + H v)) :
    vintageAgg n t c = (1 - β) * ((1 + r) * vintageAgg n t b + vintageAgg n t H) := by
  rw [vintageAgg_congr hc]
  have := vintageAgg_affine hn t ((1 - β) * (1 + r)) (1 - β) b H
  rw [show (fun v => (1 - β) * ((1 + r) * b v + H v))
      = fun v => (1 - β) * (1 + r) * b v + (1 - β) * H v from funext fun v => by ring, this]
  ring

/-- Aggregate consumption O&R (3.66), p. 183. The book leaves implicit that every vintage has
the same output and tax path, hence the same human wealth `H = Σ (1 + r)^{-(s-t)} (y_s - τ_s)`;
under that assumption `c_t = (1 - β) [(1 + r) b^P_t + H]`. -/
theorem weil_aggregate_consumption {n r β H : ℝ} (hn : 0 < 1 + n) {t : ℕ} {c b : ℕ → ℝ}
    (hc : ∀ v ≤ t, c v = (1 - β) * ((1 + r) * b v + H)) :
    vintageAgg n t c = (1 - β) * ((1 + r) * vintageAgg n t b + H) := by
  rw [weil_aggregate_consumption_general (H := fun _ => H) hn hc, vintageAgg_const hn]

/-- Aggregate private asset accumulation O&R (3.67), p. 184. If each vintage alive on date `t`
accumulates `b^v_{t+1} = (1 + r) b^v_t + y_t - τ_t - c^v_t` and the newborn vintage `t + 1`
holds no financial wealth (O&R (3.63)), then per capita assets obey
`b^P_{t+1} = [(1 + r) b^P_t + y_t - τ_t - c_t] / (1 + n)`. -/
theorem weil_aggregate_accumulation {n r y τ : ℝ} (hn : 0 < 1 + n) {t : ℕ}
    {b b' c : ℕ → ℝ} (hacc : ∀ v ≤ t, b' v = (1 + r) * b v + y - τ - c v)
    (hnew : b' (t + 1) = 0) :
    vintageAgg n (t + 1) b' =
      ((1 + r) * vintageAgg n t b + y - τ - vintageAgg n t c) / (1 + n) := by
  have hsplit : vintageAgg n (t + 1) b' = vintageAgg n t b' / (1 + n) := by
    have : (1 + n) ^ t ≠ 0 := pow_ne_zero _ hn.ne'
    unfold vintageAgg
    rw [sum_range_succ (fun v => vintageSize n v * b' v) (t + 1), hnew, mul_zero, add_zero,
      pow_succ]
    field_simp
  have hmid : vintageAgg n t b' =
      vintageAgg n t (fun v => (1 + r) * b v + (-1) * c v) + (y - τ) := by
    rw [vintageAgg_congr (y := fun v => (1 + r) * b v + (-1) * c v + (y - τ) * 1)
      (fun v hv => by rw [hacc v hv]; ring)]
    have h1 := vintageAgg_affine hn t 1 (y - τ) (fun v => (1 + r) * b v + (-1) * c v)
      (fun _ => 1)
    simp only [one_mul, vintageAgg_const hn] at h1
    rw [h1, mul_one]
  rw [hsplit, hmid, vintageAgg_affine hn]
  ring

/-- The combined law of motion O&R (3.68), p. 184: substituting (3.66) into (3.67),
`b^P_{t+1} = [(1 + r) β / (1 + n)] b^P_t + [y_t - τ_t - (1 - β) H_t] / (1 + n)`. -/
theorem weil_law_of_motion {n r β y τ H bP bP' c : ℝ} (hn : 0 < 1 + n)
    (hc : c = (1 - β) * ((1 + r) * bP + H)) (hb : bP' = ((1 + r) * bP + y - τ - c) / (1 + n)) :
    bP' = (1 + r) * β / (1 + n) * bP + (y - τ - (1 - β) * H) / (1 + n) := by
  rw [hb, hc]
  field_simp
  ring

/-! ## Constant output: dynamics and steady state, (3.69)–(3.71) -/

/-- Present value of a constant stream, used in O&R (3.69), p. 184: for `r > 0`,
`Σ_{k ≥ 0} (1 + r)^{-k} ȳ = (1 + r) ȳ / r`. -/
theorem weil_hasSum_const {r : ℝ} (hr : 0 < r) (ybar : ℝ) :
    HasSum (fun k : ℕ => ((1 + r)⁻¹) ^ k * ybar) ((1 + r) / r * ybar) := by
  have h0 : 0 ≤ (1 + r)⁻¹ := by positivity
  have h1 : (1 + r)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have h := (hasSum_geometric_of_lt_one h0 h1).mul_right ybar
  have e : 1 - (1 + r)⁻¹ = r / (1 + r) := by
    have : (1 + r) ≠ 0 := by linarith
    field_simp
    ring
  rwa [e, inv_div] at h

/-- Slope of the Weil law of motion (3.69), O&R p. 184: `(1 + r) β / (1 + n)`. -/
noncomputable def weilSlope (r β n : ℝ) : ℝ := (1 + r) * β / (1 + n)

/-- Intercept of the Weil law of motion (3.69), O&R p. 184: `[(1 + r) β - 1] ȳ / (r (1 + n))`. -/
noncomputable def weilIntercept (r β n ybar : ℝ) : ℝ := ((1 + r) * β - 1) * ybar / (r * (1 + n))

/-- Steady-state net foreign assets O&R (3.70), p. 185:
`b̄ = [(1 + r) β - 1] ȳ / ([(1 + n) - (1 + r) β] r)`. -/
noncomputable def weilSteadyB (r β n ybar : ℝ) : ℝ :=
  ((1 + r) * β - 1) * ybar / (((1 + n) - (1 + r) * β) * r)

/-- Steady-state consumption O&R (3.71), p. 186: `c̄ = (r - n) b̄ + ȳ`. -/
noncomputable def weilSteadyC (r β n ybar : ℝ) : ℝ := (r - n) * weilSteadyB r β n ybar + ybar

/-- The law of motion O&R (3.69), p. 184: with `τ = 0`, `b^P = b` and constant output `ȳ`,
(3.68) becomes `b_{t+1} = [(1 + r) β / (1 + n)] b_t + [(1 + r) β - 1] ȳ / (r (1 + n))`. -/
theorem weil_law_of_motion_const {n r β ybar b b' c : ℝ} (hn : 0 < 1 + n) (hr : 0 < r)
    (hc : c = (1 - β) * ((1 + r) * b + (1 + r) / r * ybar))
    (hb : b' = ((1 + r) * b + ybar - 0 - c) / (1 + n)) :
    b' = weilSlope r β n * b + weilIntercept r β n ybar := by
  rw [weil_law_of_motion hn hc hb, weilSlope, weilIntercept]
  field_simp
  ring

/-- Solution of a linear difference equation (used for Figure 3.9, O&R p. 185): if
`b_{k+1} = a b_k + q` and `x̄ = a x̄ + q`, then `b_k - x̄ = a^k (b_0 - x̄)`. -/
theorem weil_affine_iterate {a q xbar : ℝ} {b : ℕ → ℝ} (hb : ∀ k, b (k + 1) = a * b k + q)
    (hfix : xbar = a * xbar + q) (k : ℕ) : b k - xbar = a ^ k * (b 0 - xbar) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [hb k, pow_succ]
    linear_combination a * ih - hfix

/-- `b̄` of (3.70) is the fixed point of (3.69), O&R p. 185 (given `r ≠ 0` and
`(1 + n) ≠ (1 + r) β`). -/
theorem weilSteadyB_fixed {r β n ybar : ℝ} (hn : 0 < 1 + n) (hr : r ≠ 0)
    (hstab : (1 + r) * β ≠ 1 + n) :
    weilSteadyB r β n ybar =
      weilSlope r β n * weilSteadyB r β n ybar + weilIntercept r β n ybar := by
  have h1 : (1 + n) - (1 + r) * β ≠ 0 := sub_ne_zero.mpr (Ne.symm hstab)
  unfold weilSteadyB weilSlope weilIntercept
  field_simp
  ring

/-- Uniqueness of the steady state (3.70), O&R p. 185: any fixed point of (3.69) equals `b̄`. -/
theorem weilSteadyB_unique {r β n ybar x : ℝ} (hn : 0 < 1 + n) (hr : r ≠ 0)
    (hstab : (1 + r) * β ≠ 1 + n) (hx : x = weilSlope r β n * x + weilIntercept r β n ybar) :
    x = weilSteadyB r β n ybar := by
  have h1 : (1 + n) - (1 + r) * β ≠ 0 := sub_ne_zero.mpr (Ne.symm hstab)
  unfold weilSlope weilIntercept at hx
  unfold weilSteadyB
  field_simp at hx
  rw [eq_div_iff (mul_ne_zero h1 hr)]
  linear_combination hx

/-- Stability of the Weil dynamics, O&R p. 184 ("existence and stability of the steady state
follow from the assumption ... `(1 + r) β / (1 + n) < 1`"): if `(1 + r) β < 1 + n` then every
path of (3.69) converges to `b̄`. -/
theorem weil_converges {r β n ybar : ℝ} (hn : 0 < 1 + n) (hr0 : 0 < 1 + r) (hr : r ≠ 0)
    (hβ : 0 ≤ β) (hstab : (1 + r) * β < 1 + n) {b : ℕ → ℝ}
    (hb : ∀ k, b (k + 1) = weilSlope r β n * b k + weilIntercept r β n ybar) :
    Tendsto b atTop (𝓝 (weilSteadyB r β n ybar)) := by
  have hfix := weilSteadyB_fixed (ybar := ybar) hn hr hstab.ne
  have ha0 : 0 ≤ weilSlope r β n := by unfold weilSlope; positivity
  have ha1 : weilSlope r β n < 1 := by unfold weilSlope; rw [div_lt_one hn]; exact hstab
  have hlim := (tendsto_pow_atTop_nhds_zero_of_lt_one ha0 ha1).mul_const
    (b 0 - weilSteadyB r β n ybar)
  have := hlim.add_const (weilSteadyB r β n ybar)
  rw [zero_mul, zero_add] at this
  refine this.congr fun k => ?_
  rw [← weil_affine_iterate hb hfix k]
  ring

/-- Instability when the stability condition fails, O&R p. 184 and footnote 49: if
`(1 + r) β > 1 + n` (so the slope exceeds one) and `b_0 ≠ b̄`, the path of (3.69) does not
converge to `b̄`. -/
theorem weil_not_converges {r β n ybar : ℝ} (hn : 0 < 1 + n) (hr : r ≠ 0)
    (hunst : 1 + n < (1 + r) * β) {b : ℕ → ℝ}
    (hb : ∀ k, b (k + 1) = weilSlope r β n * b k + weilIntercept r β n ybar)
    (h0 : b 0 ≠ weilSteadyB r β n ybar) :
    ¬ Tendsto b atTop (𝓝 (weilSteadyB r β n ybar)) := by
  intro hT
  have hfix := weilSteadyB_fixed (ybar := ybar) hn hr hunst.ne'
  have ha1 : 1 ≤ weilSlope r β n := by
    unfold weilSlope; rw [le_div_iff₀ hn]; linarith
  set e := |b 0 - weilSteadyB r β n ybar| with he
  have hepos : 0 < e := abs_pos.mpr (sub_ne_zero.mpr h0)
  have hev : ∀ᶠ k in atTop, |b k - weilSteadyB r β n ybar| < e := by
    have := (Metric.tendsto_atTop.mp hT) e hepos
    obtain ⟨N, hN⟩ := this
    exact eventually_atTop.mpr ⟨N, fun k hk => by simpa [Real.dist_eq] using hN k hk⟩
  obtain ⟨k, hk⟩ := hev.exists
  rw [weil_affine_iterate hb hfix k, abs_mul, abs_of_nonneg (by positivity)] at hk
  have : 1 ≤ weilSlope r β n ^ k := one_le_pow₀ ha1
  nlinarith

/-- Stability is automatic for a debtor, O&R p. 185: if `(1 + r) β < 1` and `n ≥ 0` then
`(1 + r) β < 1 + n`. -/
theorem weil_stable_of_impatient {r β n : ℝ} (himp : (1 + r) * β < 1) (hn : 0 ≤ n) :
    (1 + r) * β < 1 + n := by linarith

/-- Sign of the steady state, O&R p. 185: under the stability condition and `r > 0`, `ȳ > 0`,
`b̄ > 0` iff `(1 + r) β > 1`. -/
theorem weilSteadyB_pos_iff {r β n ybar : ℝ} (hr : 0 < r) (hy : 0 < ybar)
    (hstab : (1 + r) * β < 1 + n) :
    0 < weilSteadyB r β n ybar ↔ 1 < (1 + r) * β := by
  have hd : 0 < ((1 + n) - (1 + r) * β) * r := mul_pos (by linarith) hr
  unfold weilSteadyB
  rw [div_pos_iff_of_pos_right hd]
  constructor
  · intro h
    by_contra hc
    push Not at hc
    nlinarith
  · intro h
    exact mul_pos (by linarith) hy

/-- Steady-state consumption O&R (3.71), p. 186: at a steady state of the current-account
constraint `b = [(1 + r) b + ȳ - c] / (1 + n)`, consumption is `c = (r - n) b + ȳ`. -/
theorem weil_steady_consumption {r n ybar b c : ℝ} (hn : 0 < 1 + n)
    (hss : b = ((1 + r) * b + ybar - c) / (1 + n)) : c = (r - n) * b + ybar := by
  field_simp at hss
  linarith

/-- Consistency of (3.71) with the consumption function (3.66), O&R p. 186: at `b̄`,
`(1 - β) [(1 + r) b̄ + (1 + r) ȳ / r] = (r - n) b̄ + ȳ`. -/
theorem weilSteadyC_eq_consumption_function {r β n ybar : ℝ} (hr : r ≠ 0)
    (hstab : (1 + r) * β ≠ 1 + n) :
    (1 - β) * ((1 + r) * weilSteadyB r β n ybar + (1 + r) / r * ybar) =
      weilSteadyC r β n ybar := by
  have h1 : (1 + n) - (1 + r) * β ≠ 0 := sub_ne_zero.mpr (Ne.symm hstab)
  have hB : weilSteadyB r β n ybar * ((1 + n) - (1 + r) * β) * r = ((1 + r) * β - 1) * ybar := by
    unfold weilSteadyB
    field_simp
  unfold weilSteadyC
  generalize weilSteadyB r β n ybar = B at hB ⊢
  field_simp
  linear_combination hB

/-- Footnote 52, O&R p. 186: substituting (3.70) into (3.71),
`c̄ = n (1 + r) (1 - β) ȳ / ([(1 + n) - (1 + r) β] r)`. -/
theorem weilSteadyC_closed {r β n ybar : ℝ} (hr : r ≠ 0) (hstab : (1 + r) * β ≠ 1 + n) :
    weilSteadyC r β n ybar = n * (1 + r) * (1 - β) * ybar / (((1 + n) - (1 + r) * β) * r) := by
  have h1 : (1 + n) - (1 + r) * β ≠ 0 := sub_ne_zero.mpr (Ne.symm hstab)
  unfold weilSteadyC weilSteadyB
  field_simp
  ring

/-- Footnote 52 corrected, O&R p. 186: `dc̄/dȳ = n (1 + r) (1 - β) / ([(1 + n) - (1 + r) β] r)`. -/
theorem weilSteadyC_hasDerivAt {r β n : ℝ} (hr : r ≠ 0) (hstab : (1 + r) * β ≠ 1 + n)
    (ybar : ℝ) :
    HasDerivAt (fun y => weilSteadyC r β n y)
      (n * (1 + r) * (1 - β) / (((1 + n) - (1 + r) * β) * r)) ybar := by
  have hfun : (fun y => weilSteadyC r β n y) =
      fun y => (n * (1 + r) * (1 - β) / (((1 + n) - (1 + r) * β) * r)) * y := by
    funext y
    rw [weilSteadyC_closed hr hstab]
    ring
  rw [hfun]
  simpa using (hasDerivAt_id ybar).const_mul
    (n * (1 + r) * (1 - β) / (((1 + n) - (1 + r) * β) * r))

/-- Footnote 52 corrected, O&R p. 186: under stability, `r > 0` and `β < 1`, the slope
`dc̄/dȳ` is positive iff `n > 0`. (The book's "`dc̄/dȳ > 0`" also needs `n > 0`.) -/
theorem weilSteadyC_slope_pos_iff {r β n : ℝ} (hr : 0 < r) (hβ : β < 1)
    (hstab : (1 + r) * β < 1 + n) :
    0 < n * (1 + r) * (1 - β) / (((1 + n) - (1 + r) * β) * r) ↔ 0 < n := by
  have hd : 0 < ((1 + n) - (1 + r) * β) * r := mul_pos (by linarith) hr
  have hk : 0 < (1 + r) * (1 - β) := mul_pos (by linarith) (by linarith)
  rw [div_pos_iff_of_pos_right hd, mul_assoc]
  exact ⟨fun h => pos_of_mul_pos_left h hk.le, fun h => mul_pos h hk⟩

/-- Without population growth steady-state consumption vanishes, O&R footnote 52 (p. 186)
corrected: at `n = 0`, `c̄ = 0` for every `ȳ` (the whole of human wealth is mortgaged). -/
theorem weilSteadyC_zero_growth {r β ybar : ℝ} (hr : r ≠ 0) (hstab : (1 + r) * β ≠ 1 + 0) :
    weilSteadyC r β 0 ybar = 0 := by
  rw [weilSteadyC_closed hr hstab]
  ring

/-- Footnote 49, O&R p. 184, made precise: if `(1 + r) β > 1 + n` the formal "steady state" has
negative consumption, provided `n > 0`, `r > 0`, `β < 1` and `ȳ > 0` (at `n = 0` it is zero). -/
theorem weilSteadyC_neg_of_unstable {r β n ybar : ℝ} (hr : 0 < r) (hβ : β < 1) (hn : 0 < n)
    (hy : 0 < ybar) (hunst : 1 + n < (1 + r) * β) : weilSteadyC r β n ybar < 0 := by
  rw [weilSteadyC_closed hr.ne' hunst.ne']
  apply div_neg_of_pos_of_neg
  · have : 0 < 1 - β := by linarith
    have : 0 < 1 + r := by linarith
    positivity
  · exact mul_neg_of_neg_of_pos (by linarith) hr

/-- A permanent rise in output, O&R §3.7.5, p. 186: if `(1 + r) β < 1` (and `r > 0`, `n ≥ 0`),
raising `ȳ` to `ȳ' > ȳ` lowers `b̄`. -/
theorem weilSteadyB_falls {r β n ybar ybar' : ℝ} (hr : 0 < r) (hn : 0 ≤ n)
    (himp : (1 + r) * β < 1) (hy : ybar < ybar') :
    weilSteadyB r β n ybar' < weilSteadyB r β n ybar := by
  have hd : 0 < ((1 + n) - (1 + r) * β) * r := mul_pos (by linarith) hr
  unfold weilSteadyB
  rw [div_lt_div_iff_of_pos_right hd]
  nlinarith

/-- A permanent rise in output raises steady-state consumption, O&R p. 186 and footnote 52:
under stability with `r > 0`, `β < 1` and `n > 0`, `ȳ < ȳ'` implies `c̄(ȳ) < c̄(ȳ')`. -/
theorem weilSteadyC_rises {r β n ybar ybar' : ℝ} (hr : 0 < r) (hβ : β < 1) (hn : 0 < n)
    (hstab : (1 + r) * β < 1 + n) (hy : ybar < ybar') :
    weilSteadyC r β n ybar < weilSteadyC r β n ybar' := by
  have hd : 0 < ((1 + n) - (1 + r) * β) * r := mul_pos (by linarith) hr
  have hk : 0 < n * (1 + r) * (1 - β) := by
    have : 0 < 1 - β := by linarith
    have : 0 < 1 + r := by linarith
    positivity
  rw [weilSteadyC_closed hr.ne' hstab.ne, weilSteadyC_closed hr.ne' hstab.ne,
    div_lt_div_iff_of_pos_right hd]
  nlinarith

/-! ## Transitory output shock, (3.72) -/

/-- Human wealth under the transitory shock path (3.72), O&R p. 187: if output is `ȳ'` on
date `t` and `ȳ` afterwards, its present value is `(1 + r) ȳ / r + (ȳ' - ȳ)`. -/
theorem weil_hasSum_transitory {r : ℝ} (hr : 0 < r) (ybar ybar' : ℝ) :
    HasSum (fun k : ℕ => ((1 + r)⁻¹) ^ k * (if k = 0 then ybar' else ybar))
      ((1 + r) / r * ybar + (ybar' - ybar)) := by
  have h := (weil_hasSum_const hr ybar).add (hasSum_ite_eq 0 (ybar' - ybar))
  convert h using 1
  funext k
  split_ifs with hk
  · subst hk; ring
  · simp

/-- The transitory shock O&R (3.72), p. 187: starting from `b_t = b̄` with the output path
(3.72), `b_{t+1} = b̄ + β (ȳ' - ȳ) / (1 + n)`. -/
theorem weil_transitory_jump {n r β ybar ybar' H c b' : ℝ} (hn : 0 < 1 + n) (hr : 0 < r)
    (hstab : (1 + r) * β ≠ 1 + n)
    (hH : HasSum (fun k : ℕ => ((1 + r)⁻¹) ^ k * (if k = 0 then ybar' else ybar)) H)
    (hc : c = (1 - β) * ((1 + r) * weilSteadyB r β n ybar + H))
    (hb : b' = ((1 + r) * weilSteadyB r β n ybar + ybar' - c) / (1 + n)) :
    b' = weilSteadyB r β n ybar + β * (ybar' - ybar) / (1 + n) := by
  have hfix := weilSteadyB_fixed (ybar := ybar) hn hr.ne' hstab
  rw [hH.unique (weil_hasSum_transitory hr ybar ybar')] at hc
  unfold weilSlope weilIntercept at hfix
  rw [hb, hc]
  generalize weilSteadyB r β n ybar = B at hfix ⊢
  field_simp at hfix ⊢
  linear_combination (-1) * hfix

/-- Monotone return after a transitory shock, O&R p. 187: under stability with `β > 0`, a path
of (3.69) that starts above `b̄` stays above it and falls strictly every period. -/
theorem weil_transitory_return {r β n ybar : ℝ} (hn : 0 < 1 + n) (hr0 : 0 < 1 + r)
    (hr : r ≠ 0) (hβ : 0 < β) (hstab : (1 + r) * β < 1 + n) {b : ℕ → ℝ}
    (hb : ∀ k, b (k + 1) = weilSlope r β n * b k + weilIntercept r β n ybar)
    (h0 : weilSteadyB r β n ybar < b 0) (k : ℕ) :
    weilSteadyB r β n ybar < b (k + 1) ∧ b (k + 1) < b k := by
  have hfix := weilSteadyB_fixed (ybar := ybar) hn hr hstab.ne
  have ha0 : 0 < weilSlope r β n := by unfold weilSlope; positivity
  have ha1 : weilSlope r β n < 1 := by unfold weilSlope; rw [div_lt_one hn]; exact hstab
  have e1 := weil_affine_iterate hb hfix (k + 1)
  have e0 := weil_affine_iterate hb hfix k
  have hp : 0 < weilSlope r β n ^ k := pow_pos ha0 k
  have hd : 0 < b 0 - weilSteadyB r β n ybar := by linarith
  rw [pow_succ] at e1
  constructor
  · nlinarith [mul_pos (mul_pos hp ha0) hd]
  · nlinarith [mul_pos (mul_pos hp (sub_pos.mpr ha1)) hd]

/-! ## Trend output growth, (3.73) -/

/-- Human wealth with growing output, O&R p. 188: if `y_{t+k} = (1 + g)^k y_t` with
`0 ≤ 1 + g` and `g < r`, then `Σ (1 + r)^{-k} y_{t+k} = (1 + r) y_t / (r - g)`. -/
theorem weil_hasSum_growth {r g : ℝ} (hg : 0 ≤ 1 + g) (hgr : g < r) (y : ℝ) :
    HasSum (fun k : ℕ => ((1 + r)⁻¹) ^ k * ((1 + g) ^ k * y)) ((1 + r) / (r - g) * y) := by
  have hr : 0 < 1 + r := by linarith
  have hq0 : 0 ≤ (1 + g) / (1 + r) := div_nonneg hg hr.le
  have hq1 : (1 + g) / (1 + r) < 1 := by rw [div_lt_one hr]; linarith
  have h := (hasSum_geometric_of_lt_one hq0 hq1).mul_right y
  have e : 1 - (1 + g) / (1 + r) = (r - g) / (1 + r) := by
    field_simp
    ring
  rw [e, inv_div] at h
  convert h using 1
  funext k
  rw [div_pow, div_eq_mul_inv, inv_pow]
  ring

/-- The growth law of motion, O&R p. 188: with `c_t = (1 - β)[(1 + r) b_t + (1 + r) y_t/(r - g)]`
and `b_{t+1} = [(1 + r) b_t + y_t - c_t]/(1 + n)`,
`b_{t+1} = [(1 + r) β/(1 + n)] b_t + [((1 + r) β - (1 + g))/((1 + n)(r - g))] y_t`. -/
theorem weil_growth_law {n r β g y b b' c : ℝ} (hn : 0 < 1 + n) (hgr : g < r)
    (hc : c = (1 - β) * ((1 + r) * b + (1 + r) / (r - g) * y))
    (hb : b' = ((1 + r) * b + y - c) / (1 + n)) :
    b' = (1 + r) * β / (1 + n) * b + ((1 + r) * β - (1 + g)) / ((1 + n) * (r - g)) * y := by
  have : r - g ≠ 0 := by linarith
  rw [hb, hc]
  field_simp
  ring

/-- The asset/output law of motion O&R (3.73), p. 188: dividing by `y_{t+1} = (1 + g) y_t`,
`b_{t+1}/y_{t+1} = [(1 + r) β/((1 + n)(1 + g))] b_t/y_t
  + ((1 + r) β - (1 + g))/((1 + n)(1 + g)(r - g))`. -/
theorem weil_growth_ratio_law {n r β g y b b' c : ℝ} (hn : 0 < 1 + n) (hgr : g < r)
    (hg : 0 < 1 + g) (hy : y ≠ 0)
    (hc : c = (1 - β) * ((1 + r) * b + (1 + r) / (r - g) * y))
    (hb : b' = ((1 + r) * b + y - c) / (1 + n)) :
    b' / ((1 + g) * y) = (1 + r) * β / ((1 + n) * (1 + g)) * (b / y)
      + ((1 + r) * β - (1 + g)) / ((1 + n) * (1 + g) * (r - g)) := by
  have : r - g ≠ 0 := by linarith
  rw [weil_growth_law hn hgr hc hb]
  field_simp

/-- Steady-state net-foreign-asset/output ratio of (3.73), O&R p. 188:
`((1 + r) β - (1 + g)) / ([(1 + n)(1 + g) - (1 + r) β] (r - g))`. -/
noncomputable def growthSteadyRatio (r β n g : ℝ) : ℝ :=
  ((1 + r) * β - (1 + g)) / (((1 + n) * (1 + g) - (1 + r) * β) * (r - g))

/-- The ratio `growthSteadyRatio` is the fixed point of (3.73), O&R p. 188. -/
theorem growthSteadyRatio_fixed {r β n g : ℝ} (hn : 0 < 1 + n) (hg : 0 < 1 + g) (hgr : g < r)
    (hstab : (1 + r) * β ≠ (1 + n) * (1 + g)) :
    growthSteadyRatio r β n g = (1 + r) * β / ((1 + n) * (1 + g)) * growthSteadyRatio r β n g
      + ((1 + r) * β - (1 + g)) / ((1 + n) * (1 + g) * (r - g)) := by
  have h1 : (1 + n) * (1 + g) - (1 + r) * β ≠ 0 := sub_ne_zero.mpr (Ne.symm hstab)
  have h2 : r - g ≠ 0 := by linarith
  have hNG : (1 + n) * (1 + g) ≠ 0 := mul_ne_zero hn.ne' hg.ne'
  unfold growthSteadyRatio
  rw [div_mul_div_comm, div_add_div _ _ (mul_ne_zero hNG (mul_ne_zero h1 h2))
    (mul_ne_zero hNG h2), div_eq_div_iff (mul_ne_zero h1 h2)
    (mul_ne_zero (mul_ne_zero hNG (mul_ne_zero h1 h2)) (mul_ne_zero hNG h2))]
  ring

/-- Sign of the long-run asset/output ratio, O&R p. 188: under the stability condition
`(1 + r) β < (1 + n)(1 + g)` and `g < r`, net foreign assets are positive iff
`β (1 + r) > 1 + g`. -/
theorem growthSteadyRatio_pos_iff {r β n g : ℝ} (hgr : g < r)
    (hstab : (1 + r) * β < (1 + n) * (1 + g)) :
    0 < growthSteadyRatio r β n g ↔ 1 + g < (1 + r) * β := by
  have hd : 0 < ((1 + n) * (1 + g) - (1 + r) * β) * (r - g) :=
    mul_pos (by linarith) (by linarith)
  unfold growthSteadyRatio
  rw [div_pos_iff_of_pos_right hd, sub_pos]

/-- Partial-fraction form of the long-run asset/output ratio (O&R p. 188), with
`A = (1 + r) β`: `[n A/((1 + n)(1 + g) - A) - ((1 + r) - A)/(r - g)] / ((1 + n)(1 + r) - A)`. -/
theorem growthSteadyRatio_partial_fractions {r β n g : ℝ}
    (h1 : (1 + n) * (1 + g) - (1 + r) * β ≠ 0) (h2 : r - g ≠ 0)
    (h3 : (1 + n) * (1 + r) - (1 + r) * β ≠ 0) :
    growthSteadyRatio r β n g =
      (n * ((1 + r) * β) / ((1 + n) * (1 + g) - (1 + r) * β)
        - ((1 + r) - (1 + r) * β) / (r - g)) / ((1 + n) * (1 + r) - (1 + r) * β) := by
  unfold growthSteadyRatio
  rw [div_sub_div _ _ h1 h2, div_div, div_eq_div_iff (mul_ne_zero h1 h2)
    (mul_ne_zero (mul_ne_zero h1 h2) h3)]
  ring

/-- "A rise in the growth rate `g` always lowers the economy's long-run net-foreign-asset-to-output
ratio", O&R p. 188 (no proof in the book). Proved for `n ≥ 0`, `0 < β < 1`, `r > -1`, on the
region where (3.73) is stable (`(1 + r) β < (1 + n)(1 + g)`) and `g < r`: the ratio is strictly
decreasing in `g`. No case split on the sign of `β (1 + r) - (1 + g)` is needed. -/
theorem growthSteadyRatio_strictAntiOn {r β n : ℝ} (hn : 0 ≤ n) (hβ0 : 0 < β) (hβ1 : β < 1)
    (hr : 0 < 1 + r) :
    StrictAntiOn (growthSteadyRatio r β n)
      {g | (1 + r) * β < (1 + n) * (1 + g) ∧ g < r} := by
  intro g1 hg1 g2 hg2 hlt
  obtain ⟨hs1, hr1⟩ := hg1
  obtain ⟨hs2, hr2⟩ := hg2
  have hA : 0 < (1 + r) * β := mul_pos hr hβ0
  have hRA : 0 < (1 + r) - (1 + r) * β := by nlinarith
  have hD : 0 < (1 + n) * (1 + r) - (1 + r) * β := by nlinarith
  have hu1 : 0 < (1 + n) * (1 + g1) - (1 + r) * β := by linarith
  have hu12 : (1 + n) * (1 + g1) - (1 + r) * β ≤ (1 + n) * (1 + g2) - (1 + r) * β := by
    nlinarith
  rw [growthSteadyRatio_partial_fractions hu1.ne' (by linarith) hD.ne',
    growthSteadyRatio_partial_fractions (by linarith) (by linarith) hD.ne',
    div_lt_div_iff_of_pos_right hD]
  have t1 : n * ((1 + r) * β) / ((1 + n) * (1 + g2) - (1 + r) * β) ≤
      n * ((1 + r) * β) / ((1 + n) * (1 + g1) - (1 + r) * β) :=
    div_le_div_of_nonneg_left (by positivity) hu1 hu12
  have t2 : ((1 + r) - (1 + r) * β) / (r - g1) < ((1 + r) - (1 + r) * β) / (r - g2) :=
    div_lt_div_of_pos_left hRA (by linarith) (by linarith)
  linarith

/-! ## §3.7.6.1 Temporary shocks with `(1 + r) β = 1` -/

/-- O&R p. 189: when `(1 + r) β = 1`, the law of motion (3.69) is `b_{t+1} = b_t / (1 + n)`. -/
theorem weil_unit_tilt_law {r β n ybar : ℝ} (htilt : (1 + r) * β = 1) (b : ℝ) :
    weilSlope r β n * b + weilIntercept r β n ybar = b / (1 + n) := by
  unfold weilSlope weilIntercept
  rw [htilt]
  ring

/-- O&R p. 189: with `(1 + r) β = 1` the steady state is `b̄ = 0` and `c̄ = ȳ`. -/
theorem weil_unit_tilt_steady {r β n ybar : ℝ} (htilt : (1 + r) * β = 1) :
    weilSteadyB r β n ybar = 0 ∧ weilSteadyC r β n ybar = ybar := by
  have h0 : weilSteadyB r β n ybar = 0 := by unfold weilSteadyB; rw [htilt]; ring
  exact ⟨h0, by unfold weilSteadyC; rw [h0]; ring⟩

/-- O&R p. 189: with `(1 + r) β = 1` and zero population growth, `b_{t+1} = b_t`, so a
transitory shock has permanent effects on foreign assets. -/
theorem weil_unit_tilt_zero_growth {r β ybar : ℝ} (htilt : (1 + r) * β = 1) {b : ℕ → ℝ}
    (hb : ∀ k, b (k + 1) = weilSlope r β 0 * b k + weilIntercept r β 0 ybar) (k : ℕ) :
    b k = b 0 := by
  induction k with
  | zero => rfl
  | succ k ih => rw [hb k, weil_unit_tilt_law htilt, ih]; ring

/-- The impact effect of a transitory shock, O&R p. 190: consumption on the shock date rises by
`(1 - β)(ȳ' - ȳ)` relative to the no-shock path, whatever the population growth rate (`n` does
not enter). Holds for any `b_t`, not only under `(1 + r) β = 1`. -/
theorem weil_transitory_consumption_jump {r β ybar ybar' b H H' : ℝ} (hr : 0 < r)
    (hH : HasSum (fun k : ℕ => ((1 + r)⁻¹) ^ k * ybar) H)
    (hH' : HasSum (fun k : ℕ => ((1 + r)⁻¹) ^ k * (if k = 0 then ybar' else ybar)) H') :
    (1 - β) * ((1 + r) * b + H') - (1 - β) * ((1 + r) * b + H) = (1 - β) * (ybar' - ybar) := by
  rw [hH.unique (weil_hasSum_const hr ybar), hH'.unique (weil_hasSum_transitory hr ybar ybar')]
  ring

/-! ## §3.7.6.2 Government debt, (3.74)–(3.75) -/

/-- The uniform tax that holds per capita debt at `d̄`, O&R (3.75), p. 190: in the per capita
government constraint (3.74) `b^G_{t+1} = [(1 + r) b^G_t + τ_t - g_t]/(1 + n)`, the level
`b^G = -d̄` is maintained iff `τ = (r - n) d̄ + g`. -/
theorem weil_debt_tax {n r d τ g : ℝ} (hn : 0 < 1 + n) :
    -d = ((1 + r) * -d + τ - g) / (1 + n) ↔ τ = (r - n) * d + g := by
  rw [eq_div_iff hn.ne']
  constructor <;> intro h <;> linarith

/-- Consumption with a constant government debt, O&R p. 191: with `b^P = b + d̄` and taxes
(3.75), `c_t = (1 - β)[(1 + r)(b_t + n d̄/r) + Σ (1 + r)^{-(s-t)} (y_s - g_s)]`. -/
theorem weil_debt_consumption {n r β d b c Hyτ Hyg : ℝ} {y τ g : ℕ → ℝ} (hr : 0 < r)
    (hτ : ∀ k, τ k = (r - n) * d + g k)
    (hyτ : HasSum (fun k => ((1 + r)⁻¹) ^ k * (y k - τ k)) Hyτ)
    (hyg : HasSum (fun k => ((1 + r)⁻¹) ^ k * (y k - g k)) Hyg)
    (hc : c = (1 - β) * ((1 + r) * (b + d) + Hyτ)) :
    c = (1 - β) * ((1 + r) * (b + n * d / r) + Hyg) := by
  have h := hyg.sub (weil_hasSum_const hr ((r - n) * d))
  have e : Hyτ = Hyg - (1 + r) / r * ((r - n) * d) := by
    refine hyτ.unique ?_
    convert h using 1
    funext k
    rw [hτ k]
    ring
  rw [hc, e]
  field_simp
  ring

/-- Debt is net wealth iff `n > 0`, O&R p. 191: raising per capita debt from `d̄` to `d̄'` raises
consumption by `(1 - β)(1 + r) n (d̄' - d̄)/r`. -/
theorem weil_debt_consumption_change (n r β b d d' H : ℝ) (hr : r ≠ 0) :
    (1 - β) * ((1 + r) * (b + n * d' / r) + H) - (1 - β) * ((1 + r) * (b + n * d / r) + H)
      = (1 - β) * (1 + r) * n * (d' - d) / r := by
  field_simp
  ring

/-- Ricardian equivalence exactly at `n = 0`, O&R p. 191: with `β < 1`, `r > 0`, consumption
`(1 - β)[(1 + r)(b + n d̄/r) + H]` is independent of the debt level `d̄` iff `n = 0`. -/
theorem weil_ricardian_iff {n r β b H : ℝ} (hr : 0 < r) (hβ : β < 1) :
    (∀ d : ℝ, (1 - β) * ((1 + r) * (b + n * d / r) + H) =
        (1 - β) * ((1 + r) * (b + n * 0 / r) + H)) ↔ n = 0 := by
  constructor
  · intro h
    have h1 := h 1
    have e := weil_debt_consumption_change n r β b 0 1 H hr.ne'
    rw [h1, sub_self] at e
    have hk : (1 - β) * (1 + r) ≠ 0 := mul_ne_zero (by linarith) (by linarith)
    have h2 : (1 - β) * (1 + r) * n * (1 - 0) / r = 0 := e.symm
    rw [div_eq_zero_iff, sub_zero, mul_one] at h2
    rcases h2 with h2 | h2
    · rcases mul_eq_zero.mp h2 with h3 | h3
      · exact absurd h3 hk
      · exact h3
    · exact absurd h2 hr.ne'
  · rintro rfl d
    simp

/-! ## Exercise 5: arbitrary debt paths -/

/-- Exercise 5, O&R p. 197 (Weil model with an arbitrary non-Ponzi debt path `d`). With
`b^P = b + d_t`, taxes from (3.74) with `b^G = -d`, namely
`τ_s = g_s + (1 + r) d_s - (1 + n) d_{s+1}`, and a summable discounted debt path,
`c_t = (1 - β)[(1 + r) b_t + Σ (1 + r)^{-(s-t)}(y_s - g_s) + n Σ (1 + r)^{-(s-t)} d_{s+1}]`. -/
theorem weil_debt_path_consumption {n r β b c Hyτ Hyg S0 : ℝ} {y τ g d : ℕ → ℝ}
    (hr : 0 < 1 + r) (hτ : ∀ k, τ k = g k + (1 + r) * d k - (1 + n) * d (k + 1))
    (hd : HasSum (fun k => ((1 + r)⁻¹) ^ k * d k) S0)
    (hyτ : HasSum (fun k => ((1 + r)⁻¹) ^ k * (y k - τ k)) Hyτ)
    (hyg : HasSum (fun k => ((1 + r)⁻¹) ^ k * (y k - g k)) Hyg)
    (hc : c = (1 - β) * ((1 + r) * (b + d 0) + Hyτ)) :
    HasSum (fun k => ((1 + r)⁻¹) ^ k * d (k + 1)) ((1 + r) * (S0 - d 0)) ∧
      c = (1 - β) * ((1 + r) * b + Hyg + n * ∑' k, ((1 + r)⁻¹) ^ k * d (k + 1)) := by
  have hr0 : (1 + r) ≠ 0 := hr.ne'
  have hS1 : HasSum (fun k => ((1 + r)⁻¹) ^ k * d (k + 1)) ((1 + r) * (S0 - d 0)) := by
    have h := (hasSum_nat_add_iff' 1).mpr hd
    simp only [range_one, sum_singleton, pow_zero, one_mul] at h
    convert h.mul_left (1 + r) using 1
    funext k
    rw [pow_succ]
    field_simp
  refine ⟨hS1, ?_⟩
  have e : Hyτ = Hyg - (1 + r) * S0 + (1 + n) * ((1 + r) * (S0 - d 0)) := by
    refine hyτ.unique ?_
    convert (hyg.sub (hd.mul_left (1 + r))).add (hS1.mul_left (1 + n)) using 1
    funext k
    rw [hτ k]
    ring
  rw [hS1.tsum_eq, hc, e]
  ring

/-- Exercise 5, O&R p. 197, in the book's form:
`c_t = (1 - β){(1 + r)(n/r) d_t + Σ (1 + r)^{-(s-t)} ((1 + r)/r) n (d_{s+1} - d_s)
  + (1 + r) b_t + Σ (1 + r)^{-(s-t)} (y_s - g_s)}` (verified; needs `r ≠ 0`). -/
theorem weil_debt_path_consumption_book {n r β b c Hyτ Hyg S0 : ℝ} {y τ g d : ℕ → ℝ}
    (hr : 0 < r) (hτ : ∀ k, τ k = g k + (1 + r) * d k - (1 + n) * d (k + 1))
    (hd : HasSum (fun k => ((1 + r)⁻¹) ^ k * d k) S0)
    (hyτ : HasSum (fun k => ((1 + r)⁻¹) ^ k * (y k - τ k)) Hyτ)
    (hyg : HasSum (fun k => ((1 + r)⁻¹) ^ k * (y k - g k)) Hyg)
    (hc : c = (1 - β) * ((1 + r) * (b + d 0) + Hyτ)) :
    c = (1 - β) * ((1 + r) * (n / r) * d 0
      + ∑' k, ((1 + r)⁻¹) ^ k * ((1 + r) / r * n * (d (k + 1) - d k))
      + (1 + r) * b + Hyg) := by
  obtain ⟨hS1, hcons⟩ := weil_debt_path_consumption (by linarith) hτ hd hyτ hyg hc
  have hdiff : HasSum (fun k => ((1 + r)⁻¹) ^ k * ((1 + r) / r * n * (d (k + 1) - d k)))
      ((1 + r) / r * n * ((1 + r) * (S0 - d 0) - S0)) := by
    convert (hS1.sub hd).mul_left ((1 + r) / r * n) using 1
    funext k
    ring
  rw [hcons, hS1.tsum_eq, hdiff.tsum_eq]
  field_simp
  ring

/-! ## Exercise 3: Blanchard (1985) perpetual youth

Timing (consistent with parts (c)–(e) of the exercise): `b^v_t` is what an individual of age
`a = t - v` carried out of date `t - 1` as an annuity; survivors are paid `(1 + r)/φ` per unit.
With cohort masses `φ^a`, aggregate private net foreign assets at the start of `t` (the savings
of everyone alive at `t - 1`, including those who then died) are `B_t = (Σ_a φ^a b_t(a))/φ`,
while `C_t = Σ_a φ^a c_t(a)` and `Y_t - T_t = Σ_a φ^a (y - τ) = (y - τ)/(1 - φ)`. -/

/-- Exercise 3(a), O&R p. 196: with a unit cohort born each period and survival probability
`φ`, the cohort of age `a` has mass `φ^a` and total population is `1/(1 - φ)`. -/
theorem blanchard_population {φ : ℝ} (h0 : 0 ≤ φ) (h1 : φ < 1) :
    HasSum (fun a : ℕ => φ ^ a) (1 / (1 - φ)) := by
  rw [one_div]
  exact hasSum_geometric_of_lt_one h0 h1

/-- Exercise 3(b), O&R p. 196: an insurer that holds a saver's `b ≠ 0` at the world rate and
pays gross `R` to the fraction `φ > 0` who survive makes zero profit iff `R = (1 + r)/φ`. -/
theorem blanchard_annuity_zero_profit {φ r R b : ℝ} (hφ : 0 < φ) (hb : b ≠ 0) :
    (1 + r) * b - φ * (R * b) = 0 ↔ R = (1 + r) / φ := by
  rw [eq_div_iff hφ.ne']
  constructor
  · intro h
    have : ((1 + r) - R * φ) * b = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with h' | h'
    · linarith
    · exact absurd h' hb
  · intro h
    linear_combination (-b) * h

/-- Exercise 3(c), O&R p. 196: with the annuity return `(1 + r)/φ`, the flow constraint
`b_{k+1} = ((1 + r)/φ) b_k + (y_k - τ_k) - c_k` and no-Ponzi give the budget constraint
`Σ (φ/(1 + r))^k c_k = ((1 + r)/φ) b_0 + Σ (φ/(1 + r))^k (y_k - τ_k)`. -/
theorem blanchard_budget {φ r : ℝ} (hφ : 0 < φ) (hr : 0 < 1 + r) {b x c : ℕ → ℝ}
    (hflow : ∀ k, b (k + 1) = (1 + r) / φ * b k + x k - c k) {X C : ℝ}
    (hX : HasSum (fun k => (φ / (1 + r)) ^ k * x k) X)
    (hC : HasSum (fun k => (φ / (1 + r)) ^ k * c k) C)
    (hNP : Tendsto (fun T => (φ / (1 + r)) ^ T * b T) atTop (𝓝 0)) :
    C = (1 + r) / φ * b 0 + X := by
  have hRρ : (1 + r) / φ * (φ / (1 + r)) = 1 := by field_simp
  exact perpetual_ibc_of_flow hRρ hflow hX hC hNP

/-- Exercise 3(c)–(d), O&R p. 196: with log utility the Euler equation is
`c_{k+1} = (1 + r) β c_k` (effective discount `φ β`, return `(1 + r)/φ`), and the individual
consumption function is `c_0 = (1 - φ β) [((1 + r)/φ) b_0 + Σ (φ/(1 + r))^k (y_k - τ_k)]`. -/
theorem blanchard_consumption_function {φ r β : ℝ} (hφ : 0 < φ) (hr : 0 < 1 + r)
    (hδ0 : 0 ≤ φ * β) (hδ1 : φ * β < 1) {b x c : ℕ → ℝ}
    (hflow : ∀ k, b (k + 1) = (1 + r) / φ * b k + x k - c k)
    (heuler : ∀ k, c (k + 1) = (1 + r) * β * c k) {X C : ℝ}
    (hX : HasSum (fun k => (φ / (1 + r)) ^ k * x k) X)
    (hC : HasSum (fun k => (φ / (1 + r)) ^ k * c k) C)
    (hNP : Tendsto (fun T => (φ / (1 + r)) ^ T * b T) atTop (𝓝 0)) :
    c 0 = (1 - φ * β) * ((1 + r) / φ * b 0 + X) := by
  rw [← blanchard_budget hφ hr hflow hX hC hNP]
  refine perpetual_consumption_of_euler hδ0 hδ1 (fun k => ?_) hC
  rw [heuler k]
  field_simp

/-- Blanchard human wealth for constant after-tax income, Exercise 3(e), O&R p. 196: for
`0 ≤ φ < 1 + r`, `Σ (φ/(1 + r))^k x = (1 + r) x / (1 + r - φ)`. -/
theorem blanchard_hasSum_const {φ r : ℝ} (hφ : 0 ≤ φ) (hφr : φ < 1 + r) (x : ℝ) :
    HasSum (fun k : ℕ => (φ / (1 + r)) ^ k * x) ((1 + r) / (1 + r - φ) * x) := by
  have hr : 0 < 1 + r := by linarith
  have h0 : 0 ≤ φ / (1 + r) := div_nonneg hφ hr.le
  have h1 : φ / (1 + r) < 1 := by rw [div_lt_one hr]; exact hφr
  have h := (hasSum_geometric_of_lt_one h0 h1).mul_right x
  have e : 1 - φ / (1 + r) = (1 + r - φ) / (1 + r) := by field_simp
  rwa [e, inv_div] at h

/-- Exercise 3(d), O&R p. 196: aggregate private assets obey
`B_{t+1} = (1 + r) B_t + Y_t - T_t - C_t`. Here each age-`a` individual carries
`b'(a + 1) = ((1 + r)/φ) b(a) + x - c(a)` into `t + 1`, newborns carry nothing (`b'(0) = 0`),
`Σ φ^a b(a) = φ B_t`, `Σ φ^a c(a) = C_t` and `Y_t - T_t = x/(1 - φ)`; the conclusion is
`Σ φ^a b'(a) = φ [(1 + r) B_t + x/(1 - φ) - C_t]`, i.e. `B_{t+1} = (1 + r) B_t + Y - T - C`. -/
theorem blanchard_aggregate_accumulation {φ r x Bs Cs : ℝ} (hφ0 : 0 < φ) (hφ1 : φ < 1)
    {b b' c : ℕ → ℝ} (hB : HasSum (fun a => φ ^ a * b a) Bs)
    (hC : HasSum (fun a => φ ^ a * c a) Cs)
    (hflow : ∀ a, b' (a + 1) = (1 + r) / φ * b a + x - c a) (hnew : b' 0 = 0) :
    HasSum (fun a => φ ^ a * b' a) (φ * ((1 + r) * (Bs / φ) + x * (1 - φ)⁻¹ - Cs)) := by
  rw [← hasSum_nat_add_iff' 1]
  simp only [range_one, sum_singleton, pow_zero, hnew, mul_zero, sub_zero]
  have h := ((hB.mul_left (1 + r)).add
    ((hasSum_geometric_of_lt_one hφ0.le hφ1).mul_left (φ * x))).sub (hC.mul_left φ)
  convert h using 1
  · funext a
    rw [hflow a, pow_succ]
    field_simp
  · field_simp

/-- Exercise 3(e), aggregate consumption, O&R p. 196: aggregating the consumption functions
`c(a) = (1 - φ β)[((1 + r)/φ) b(a) + (1 + r) x/(1 + r - φ)]` gives
`C = (1 - φ β)[(1 + r) B + (1 + r)(Y - T)/(1 + r - φ)]` with `B = Bs/φ`, `Y - T = x/(1 - φ)`. -/
theorem blanchard_aggregate_consumption {φ r β x Bs : ℝ} (hφ0 : 0 < φ) (hφ1 : φ < 1)
    {b c : ℕ → ℝ} (hB : HasSum (fun a => φ ^ a * b a) Bs)
    (hc : ∀ a, c a = (1 - φ * β) * ((1 + r) / φ * b a + (1 + r) / (1 + r - φ) * x)) :
    HasSum (fun a => φ ^ a * c a)
      ((1 - φ * β) * ((1 + r) * (Bs / φ) + (1 + r) / (1 + r - φ) * (x * (1 - φ)⁻¹))) := by
  have h := (hB.mul_left ((1 - φ * β) * ((1 + r) / φ))).add
    ((hasSum_geometric_of_lt_one hφ0.le hφ1).mul_left ((1 - φ * β) * ((1 + r) / (1 + r - φ) * x)))
  convert h using 1
  · funext a
    rw [hc a]
    ring
  · ring

/-- Exercise 3(e), O&R p. 196 (verified): with constant `Y` and `T`,
`B_{t+1} = φ β (1 + r) B_t + φ [((1 + r) β - 1)/(1 + r - φ)] (Y - T)`. Stated with
`φ B_{t+1} = Σ φ^a b'(a)`, `B_t = Bs/φ` and `Y - T = x/(1 - φ)`. -/
theorem blanchard_law_of_motion {φ r β x Bs : ℝ} (hφ0 : 0 < φ) (hφ1 : φ < 1) (hφr : φ < 1 + r)
    {b b' c : ℕ → ℝ} (hB : HasSum (fun a => φ ^ a * b a) Bs)
    (hc : ∀ a, c a = (1 - φ * β) * ((1 + r) / φ * b a + (1 + r) / (1 + r - φ) * x))
    (hflow : ∀ a, b' (a + 1) = (1 + r) / φ * b a + x - c a) (hnew : b' 0 = 0) :
    HasSum (fun a => φ ^ a * b' a)
      (φ * (φ * β * (1 + r) * (Bs / φ)
        + φ * (((1 + r) * β - 1) / (1 + r - φ)) * (x * (1 - φ)⁻¹))) := by
  have hC := blanchard_aggregate_consumption hφ0 hφ1 hB hc (β := β)
  convert blanchard_aggregate_accumulation hφ0 hφ1 hB hC hflow hnew using 1
  have : 1 + r - φ ≠ 0 := by linarith
  have : 1 - φ ≠ 0 := by linarith
  field_simp
  ring

/-- Steady-state national net foreign assets with public debt `D`, Exercise 3(f), O&R p. 197:
the household assets `B^P` solve the steady state of 3(e) with `Y - T = Y - r D`, and national
assets are `B = B^P - D`. -/
noncomputable def blanchardSteadyB (r β φ Y D : ℝ) : ℝ :=
  φ * ((1 + r) * β - 1) / (1 + r - φ) * (Y - r * D) / (1 - φ * β * (1 + r)) - D

/-- Exercise 3(f), O&R p. 197: a uniform tax `τ = r D (1 - φ)` on a population of `1/(1 - φ)`
raises total taxes `T = r D`, which is exactly what keeps `B^G = -D` constant with `G = 0` in
`B^G_{t+1} = (1 + r) B^G_t + T - G`. -/
theorem blanchard_debt_tax {φ r D : ℝ} (hφ : φ < 1) :
    r * D * (1 - φ) * (1 - φ)⁻¹ = r * D ∧
      (-D = (1 + r) * -D + r * D * (1 - φ) * (1 - φ)⁻¹ - 0) := by
  have : 1 - φ ≠ 0 := by linarith
  have e : r * D * (1 - φ) * (1 - φ)⁻¹ = r * D := by field_simp
  exact ⟨e, by rw [e]; ring⟩

/-- Exercise 3(f), O&R p. 197: `B^P = blanchardSteadyB + D` is the steady state of the private
law of motion 3(e) with `Y - T = Y - r D`. -/
theorem blanchardSteadyB_private_fixed {r β φ Y D : ℝ} (hφr : φ < 1 + r)
    (hstab : φ * β * (1 + r) < 1) :
    blanchardSteadyB r β φ Y D + D = φ * β * (1 + r) * (blanchardSteadyB r β φ Y D + D)
      + φ * (((1 + r) * β - 1) / (1 + r - φ)) * (Y - r * D) := by
  have h1 : 1 + r - φ ≠ 0 := by linarith
  have h2 : 1 - φ * β * (1 + r) ≠ 0 := by linarith
  unfold blanchardSteadyB
  have e1 : φ * ((1 + r) * β - 1) = φ * β * (1 + r) - φ := by ring
  have e3 : φ * (((1 + r) * β - 1) / (1 + r - φ)) = (φ * β * (1 + r) - φ) / (1 + r - φ) := by
    rw [← e1]; ring
  rw [e1, e3]
  generalize φ * β * (1 + r) = a at h2 ⊢
  field_simp
  ring

/-- Exercise 3(f), O&R p. 197: effect of debt on steady-state national net foreign assets,
`B̄(D) = B̄(0) - [(1 + r)(1 - φ)(1 - φ β) / ((1 + r - φ)(1 - φ β (1 + r)))] D`. -/
theorem blanchardSteadyB_debt {r β φ Y D : ℝ} (hφr : φ < 1 + r) (hstab : φ * β * (1 + r) < 1) :
    blanchardSteadyB r β φ Y D = blanchardSteadyB r β φ Y 0
      - (1 + r) * (1 - φ) * (1 - φ * β) / ((1 + r - φ) * (1 - φ * β * (1 + r))) * D := by
  have h1 : 1 + r - φ ≠ 0 := by linarith
  have h2 : 1 - φ * β * (1 + r) ≠ 0 := by linarith
  unfold blanchardSteadyB
  have e1 : φ * ((1 + r) * β - 1) = φ * β * (1 + r) - φ := by ring
  have e2 : (1 + r) * (1 - φ) * (1 - φ * β) = (1 - φ) * ((1 + r) - φ * β * (1 + r)) := by ring
  rw [e1, e2]
  generalize φ * β * (1 + r) = a at h2 ⊢
  field_simp
  ring

/-- Exercise 3(f), O&R p. 197: with `0 < φ < 1`, `r > 0` and stability
`φ β (1 + r) < 1`, public debt `D > 0` lowers steady-state national net foreign assets, and
hence steady-state consumption `C̄ = r B̄ + Y` (from `B = (1 + r) B + Y - C` with `G = 0`). -/
theorem blanchard_debt_lowers {r β φ Y D : ℝ} (hr : 0 < r) (hφ0 : 0 < φ) (hφ1 : φ < 1)
    (hstab : φ * β * (1 + r) < 1) (hD : 0 < D) :
    blanchardSteadyB r β φ Y D < blanchardSteadyB r β φ Y 0 ∧
      r * blanchardSteadyB r β φ Y D + Y < r * blanchardSteadyB r β φ Y 0 + Y := by
  have hφr : φ < 1 + r := by linarith
  have hk : 0 < (1 + r) * (1 - φ) * (1 - φ * β) / ((1 + r - φ) * (1 - φ * β * (1 + r))) := by
    have : 0 < 1 - φ * β := by nlinarith
    have : 0 < 1 + r - φ := by linarith
    have : 0 < 1 - φ * β * (1 + r) := by linarith
    have : 0 < 1 - φ := by linarith
    have : 0 < 1 + r := by linarith
    positivity
  have h1 : blanchardSteadyB r β φ Y D < blanchardSteadyB r β φ Y 0 := by
    rw [blanchardSteadyB_debt hφr hstab]
    nlinarith
  exact ⟨h1, by nlinarith⟩

/-- Exercise 3(f), O&R p. 197: steady-state national consumption, `C̄ = r B̄ + Y`, from the
national constraint `B = (1 + r) B + Y - C` (private plus government, `G = 0`). -/
theorem blanchard_steady_consumption {r B Y C : ℝ} (h : B = (1 + r) * B + Y - C) :
    C = r * B + Y := by linarith

/-- Exercise 3(f), O&R p. 197: in the representative-agent limit `φ = 1`, debt leaves steady
state national assets unchanged (Ricardian equivalence). -/
theorem blanchardSteadyB_ricardian {r β Y D : ℝ} (hr : 0 < r) (hstab : 1 * β * (1 + r) < 1) :
    blanchardSteadyB r β 1 Y D = blanchardSteadyB r β 1 Y 0 := by
  rw [blanchardSteadyB_debt (by linarith) hstab]
  ring

end ObstfeldRogoff.LifeCycleFiscalPolicy.PerpetualYouth
