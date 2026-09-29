/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RealExchangeRate.CESIndex
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Consumption dynamics, the price level and the consumption-based real interest rate

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §4.4
(pp. 225–235, eqs. (24)–(36), footnote 30) and Exercises 3 and 4 (p. 265).

Time is indexed relative to the planning date: index `s` stands for date `t + s`, so `P 0` is
`P_t`. The world interest rate `r` on tradables is constant, `1 + r > 0`, and
`d = (1+r)⁻¹` is the tradables discount factor. We prove:

* the consumption-based real rate (25), `1 + r^C_{s+1} = (1+r)P_s/P_{s+1}`, the Euler
  equation (26), and the telescoping formula `R^C_{t,s} = P_s/((1+r)^{s−t} P_t)`;
* the real-consumption budget (27) from (24), with explicit summability;
* the isoelastic consumption function (28) and its price-level form (29), and the p. 232 claim
  that future prices `P_s` have no wealth effect;
* the national budget (30), deriving footnote 30's capital-value formula from
  `K_{s+1} = K_s + I_s` and an **explicit transversality condition** `(1+r)^{−T} K_T → 0`,
  and the tradables-only budget (32);
* the Euler equations (33), (34), the tradables consumption function (35), the current account
  (36), and the p. 235 claim that a rising price index with `σ > θ` raises initial tradables
  consumption above its constant-`P` level (and lowers it when `σ < θ`);
* Exercise 3 (the real-consumption versions of the budget, the consumption function and the
  current account) and Exercise 4 (a) and (b).

Present values carry explicit `Summable` hypotheses; nothing relies on the junk value of `tsum`.
-/

namespace ObstfeldRogoff.RealExchangeRate.ConsumptionDynamics

open Real Filter Topology Finset
open ObstfeldRogoff.RealExchangeRate.CESIndex

/-- The gross consumption-based real interest rate (25), O&R p. 230:
`1 + r^C_{s+1} = (1+r) P_s / P_{s+1}`. -/
noncomputable def grossRealRate (r : ℝ) (P : ℕ → ℝ) (s : ℕ) : ℝ := (1 + r) * P s / P (s + 1)

/-- The market discount factor for real consumption, O&R p. 231:
`R^C_{t,t+n} = ∏_{v=t+1}^{t+n} (1 + r^C_v)⁻¹`, with `R^C_{t,t} = 1`. -/
noncomputable def realDiscount (r : ℝ) (P : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∏ v ∈ Finset.range n, (grossRealRate r P v)⁻¹

/-- `R^C_{t,t} = 1`, O&R p. 231. -/
theorem realDiscount_zero (r : ℝ) (P : ℕ → ℝ) : realDiscount r P 0 = 1 := by
  simp [realDiscount]

/-- The consumption-based real rate is positive for positive prices and `1 + r > 0`,
O&R (25), p. 230. -/
theorem grossRealRate_pos {r : ℝ} {P : ℕ → ℝ} (hr : 0 < 1 + r) (hP : ∀ s, 0 < P s) (s : ℕ) :
    0 < grossRealRate r P s := by
  unfold grossRealRate
  have := hP s; have := hP (s + 1); positivity

/-- Telescoping of the real discount factor, O&R p. 230:
`R^C_{t,t+n} = P_{t+n} / ((1+r)^n P_t)`. -/
theorem realDiscount_eq {r : ℝ} {P : ℕ → ℝ} (hr : 1 + r ≠ 0) (hP : ∀ s, P s ≠ 0) (n : ℕ) :
    realDiscount r P n = ((1 + r)⁻¹) ^ n * (P n / P 0) := by
  induction n with
  | zero => simp [realDiscount, hP 0]
  | succ n ih =>
    unfold realDiscount at ih ⊢
    rw [prod_range_succ, ih, grossRealRate]
    have := hP n; have := hP (n + 1); have := hP 0
    field_simp
    linear_combination (-(1 + r)⁻¹ ^ n) * (mul_inv_cancel₀ hr)

/-- The real discount factor is positive, O&R p. 231. -/
theorem realDiscount_pos {r : ℝ} {P : ℕ → ℝ} (hr : 0 < 1 + r) (hP : ∀ s, 0 < P s) (n : ℕ) :
    0 < realDiscount r P n :=
  prod_pos fun v _ => inv_pos.mpr (grossRealRate_pos hr hP v)

/-- The Euler equation (26), O&R p. 230: `u′(C_s)/P_s = (1+r)β u′(C_{s+1})/P_{s+1}` is
equivalent to `u′(C_s) = (1 + r^C_{s+1}) β u′(C_{s+1})`. -/
theorem euler_real_rate {r β u0 u1 : ℝ} {P : ℕ → ℝ} {s : ℕ} (hP0 : P s ≠ 0)
    (hP1 : P (s + 1) ≠ 0) :
    u0 / P s = (1 + r) * β * (u1 / P (s + 1)) ↔ u0 = grossRealRate r P s * β * u1 := by
  unfold grossRealRate
  constructor
  · intro h
    rw [div_eq_iff hP0] at h
    rw [h]; field_simp
  · intro h
    rw [h]; field_simp

/-- The real-consumption budget (27) from (24), O&R pp. 229–231: if
`∑ (1+r)^{−s} P_s C_s = (1+r)Q_t + ∑ (1+r)^{−s} Y_s` (with `Y_s = w_s L_s − G_s` and both series
summable), then the real series are summable and
`∑ R^C_{t,s} C_s = (1+r)Q_t/P_t + ∑ R^C_{t,s} Y_s/P_s`. -/
theorem real_budget {r Q : ℝ} {P C Y : ℕ → ℝ} (hr : 0 < 1 + r) (hP : ∀ s, 0 < P s)
    (hC : Summable fun s => ((1 + r)⁻¹) ^ s * (P s * C s))
    (hY : Summable fun s => ((1 + r)⁻¹) ^ s * Y s)
    (h24 : ∑' s, ((1 + r)⁻¹) ^ s * (P s * C s) = (1 + r) * Q + ∑' s, ((1 + r)⁻¹) ^ s * Y s) :
    Summable (fun s => realDiscount r P s * C s) ∧
    Summable (fun s => realDiscount r P s * (Y s / P s)) ∧
    ∑' s, realDiscount r P s * C s
      = (1 + r) * Q / P 0 + ∑' s, realDiscount r P s * (Y s / P s) := by
  have hP' : ∀ s, P s ≠ 0 := fun s => (hP s).ne'
  have eC : (fun s => realDiscount r P s * C s)
      = fun s => (P 0)⁻¹ * (((1 + r)⁻¹) ^ s * (P s * C s)) := by
    funext s; rw [realDiscount_eq hr.ne' hP']; field_simp
  have eY : (fun s => realDiscount r P s * (Y s / P s))
      = fun s => (P 0)⁻¹ * (((1 + r)⁻¹) ^ s * Y s) := by
    funext s; rw [realDiscount_eq hr.ne' hP']; have := hP' s; field_simp
  refine ⟨eC ▸ hC.mul_left _, eY ▸ hY.mul_left _, ?_⟩
  rw [eC, eY, tsum_mul_left, tsum_mul_left, h24]
  field_simp

/-- Iterating the isoelastic Euler equation (33), O&R p. 231 (as in §2.2.2):
`C_s = (R^C_{t,s})^{−σ} β^{σ(s−t)} C_t`. -/
theorem consumption_path_of_euler {r σ β : ℝ} {P C : ℕ → ℝ} (hr : 0 < 1 + r)
    (hP : ∀ s, 0 < P s)
    (hE : ∀ s, C (s + 1) = grossRealRate r P s ^ σ * β ^ σ * C s) (n : ℕ) :
    C n = realDiscount r P n ^ (-σ) * (β ^ σ) ^ n * C 0 := by
  induction n with
  | zero => simp [realDiscount_zero]
  | succ n ih =>
    have hg := grossRealRate_pos hr hP n
    have hR := realDiscount_pos hr hP n
    have hstep : realDiscount r P (n + 1) = realDiscount r P n * (grossRealRate r P n)⁻¹ := by
      unfold realDiscount; rw [prod_range_succ]
    rw [hE n, ih, hstep, mul_rpow hR.le (inv_pos.mpr hg).le, inv_rpow hg.le, rpow_neg hg.le,
      inv_inv, pow_succ]
    ring

/-- The isoelastic consumption function (28), O&R p. 231, for any real wealth `W` on the
right of the budget: if `C_s = (R^C_{t,s})^{−σ} β^{σ(s−t)} C_t` and `∑ R^C_{t,s} C_s = W`, with
`∑ (R^C_{t,s})^{1−σ} β^{σ(s−t)}` summable, then `C_t = W / ∑ (R^C_{t,s})^{1−σ} β^{σ(s−t)}`. -/
theorem consumption_of_budget {r σ β W : ℝ} {P C : ℕ → ℝ} (hr : 0 < 1 + r)
    (hP : ∀ s, 0 < P s) (hβ : 0 < β)
    (hpath : ∀ n, C n = realDiscount r P n ^ (-σ) * (β ^ σ) ^ n * C 0)
    (hsum : Summable fun n => realDiscount r P n ^ (1 - σ) * (β ^ σ) ^ n)
    (hW : ∑' n, realDiscount r P n * C n = W) :
    C 0 = W / ∑' n, realDiscount r P n ^ (1 - σ) * (β ^ σ) ^ n := by
  have hterm : ∀ n, realDiscount r P n * C n
      = realDiscount r P n ^ (1 - σ) * (β ^ σ) ^ n * C 0 := by
    intro n
    have hR := realDiscount_pos hr hP n
    rw [hpath n, sub_eq_add_neg, rpow_add hR, rpow_one]
    ring
  have hden : 0 < ∑' n, realDiscount r P n ^ (1 - σ) * (β ^ σ) ^ n := by
    refine hsum.tsum_pos (fun n => ?_) 0 ?_
    · have := realDiscount_pos hr hP n; positivity
    · have := realDiscount_pos hr hP 0; positivity
  rw [← hW, tsum_congr hterm, tsum_mul_right]
  field_simp

/-- The consumption function (28), O&R p. 231: combining (24) with the isoelastic Euler
equation (33), `C_t = [(1+r)Q_t/P_t + ∑ R^C_{t,s}(w_sL_s − G_s)/P_s] /
∑ (R^C_{t,s})^{1−σ} β^{σ(s−t)}`. -/
theorem consumption_function {r σ β Q : ℝ} {P C Y : ℕ → ℝ} (hr : 0 < 1 + r)
    (hP : ∀ s, 0 < P s) (hβ : 0 < β)
    (hE : ∀ s, C (s + 1) = grossRealRate r P s ^ σ * β ^ σ * C s)
    (hC : Summable fun s => ((1 + r)⁻¹) ^ s * (P s * C s))
    (hY : Summable fun s => ((1 + r)⁻¹) ^ s * Y s)
    (hsum : Summable fun n => realDiscount r P n ^ (1 - σ) * (β ^ σ) ^ n)
    (h24 : ∑' s, ((1 + r)⁻¹) ^ s * (P s * C s) = (1 + r) * Q + ∑' s, ((1 + r)⁻¹) ^ s * Y s) :
    C 0 = ((1 + r) * Q / P 0 + ∑' s, realDiscount r P s * (Y s / P s))
      / ∑' n, realDiscount r P n ^ (1 - σ) * (β ^ σ) ^ n :=
  consumption_of_budget hr hP hβ (consumption_path_of_euler hr hP hE) hsum
    (real_budget hr hP hC hY h24).2.2

/-- The consumption function in price-level form (29), O&R p. 232:
`C_t = [(1+r)Q_t + ∑ (1+r)^{−(s−t)}(w_sL_s − G_s)] /
(P_t ∑ [(1+r)^{s−t} P_t/P_s]^{σ−1} β^{σ(s−t)})`. -/
theorem consumption_function_price_form {r σ β Q : ℝ} {P C Y : ℕ → ℝ} (hr : 0 < 1 + r)
    (hP : ∀ s, 0 < P s) (hβ : 0 < β)
    (hE : ∀ s, C (s + 1) = grossRealRate r P s ^ σ * β ^ σ * C s)
    (hC : Summable fun s => ((1 + r)⁻¹) ^ s * (P s * C s))
    (hY : Summable fun s => ((1 + r)⁻¹) ^ s * Y s)
    (hsum : Summable fun n => ((1 + r) ^ n * (P 0 / P n)) ^ (σ - 1) * (β ^ σ) ^ n)
    (h24 : ∑' s, ((1 + r)⁻¹) ^ s * (P s * C s) = (1 + r) * Q + ∑' s, ((1 + r)⁻¹) ^ s * Y s) :
    C 0 = ((1 + r) * Q + ∑' s, ((1 + r)⁻¹) ^ s * Y s)
      / (P 0 * ∑' n, ((1 + r) ^ n * (P 0 / P n)) ^ (σ - 1) * (β ^ σ) ^ n) := by
  have hP' : ∀ s, P s ≠ 0 := fun s => (hP s).ne'
  have eR : ∀ n, realDiscount r P n ^ (1 - σ) = ((1 + r) ^ n * (P 0 / P n)) ^ (σ - 1) := by
    intro n
    have hx : 0 < (1 + r) ^ n * (P 0 / P n) := by have := hP n; have := hP 0; positivity
    have e : realDiscount r P n = ((1 + r) ^ n * (P 0 / P n))⁻¹ := by
      rw [realDiscount_eq hr.ne' hP', inv_pow]; have := hP' n; have := hP' 0; field_simp
    rw [e, inv_rpow hx.le, ← rpow_neg hx.le, neg_sub]
  have hsum' : Summable fun n => realDiscount r P n ^ (1 - σ) * (β ^ σ) ^ n := by
    simp_rw [eR]; exact hsum
  have h := consumption_function hr hP hβ hE hC hY hsum' h24
  simp_rw [eR] at h
  have eY : (fun s => realDiscount r P s * (Y s / P s))
      = fun s => (P 0)⁻¹ * (((1 + r)⁻¹) ^ s * Y s) := by
    funext s; rw [realDiscount_eq hr.ne' hP']; have := hP' s; field_simp
  rw [h, eY, tsum_mul_left]
  have := hP 0
  field_simp

/-- No wealth effect of future price levels, O&R p. 232: the real wealth in the numerator of
(28), `(1+r)Q_t/P_t + ∑ R^C_{t,s} Y_s/P_s`, depends on the price path only through `P_t`. -/
theorem real_wealth_independent_of_future_prices {r Q : ℝ} {P P' Y : ℕ → ℝ} (hr : 0 < 1 + r)
    (hP : ∀ s, 0 < P s) (hP' : ∀ s, 0 < P' s) (h0 : P 0 = P' 0) :
    (1 + r) * Q / P 0 + ∑' s, realDiscount r P s * (Y s / P s)
      = (1 + r) * Q / P' 0 + ∑' s, realDiscount r P' s * (Y s / P' s) := by
  have e : ∀ (P : ℕ → ℝ), (∀ s, 0 < P s) → (fun s => realDiscount r P s * (Y s / P s))
      = fun s => (P 0)⁻¹ * (((1 + r)⁻¹) ^ s * Y s) := by
    intro P hP
    funext s
    rw [realDiscount_eq hr.ne' (fun s => (hP s).ne')]
    have := (hP s).ne'; have := (hP 0).ne'
    field_simp
  rw [e P hP, e P' hP', h0]

/-- Footnote 30, O&R pp. 232–233: with `K_{s+1} = K_s + I_s`, the finite-horizon value of
capital telescopes, `∑_{s<T} (1+r)^{−(s+1)}(rK_s − I_s) = K_t − (1+r)^{−T} K_{t+T}`. -/
theorem capital_partial_sum {r : ℝ} {K I : ℕ → ℝ} (hr : 1 + r ≠ 0)
    (hK : ∀ s, K (s + 1) = K s + I s) (T : ℕ) :
    ∑ s ∈ range T, ((1 + r)⁻¹) ^ (s + 1) * (r * K s - I s)
      = K 0 - ((1 + r)⁻¹) ^ T * K T := by
  induction T with
  | zero => simp
  | succ T ih =>
    rw [sum_range_succ, ih, show I T = K (T + 1) - K T by rw [hK T]; ring, pow_succ]
    linear_combination (((1 + r)⁻¹) ^ T * K T) * (inv_mul_cancel₀ hr)

/-- Footnote 30, O&R pp. 232–233: the capital stock equals the present value of future capital
income less investment, `K_t = ∑_{s≥t} (1+r)^{−(s−t+1)}(rK_s − I_s)`. The book leaves implicit
the **transversality condition** `(1+r)^{−T} K_T → 0`, which is assumed here, together with
summability of the series. -/
theorem capital_eq_present_value {r : ℝ} {K I : ℕ → ℝ} (hr : 1 + r ≠ 0)
    (hK : ∀ s, K (s + 1) = K s + I s)
    (hTV : Tendsto (fun T => ((1 + r)⁻¹) ^ T * K T) atTop (𝓝 0))
    (hS : Summable fun s => ((1 + r)⁻¹) ^ (s + 1) * (r * K s - I s)) :
    ∑' s, ((1 + r)⁻¹) ^ (s + 1) * (r * K s - I s) = K 0 := by
  refine (hS.hasSum_iff_tendsto_nat.mpr ?_).tsum_eq
  have h : Tendsto (fun T => K 0 - ((1 + r)⁻¹) ^ T * K T) atTop (𝓝 (K 0 - 0)) :=
    tendsto_const_nhds.sub hTV
  rw [sub_zero] at h
  exact h.congr fun T => (capital_partial_sum hr hK T).symm

/-- The national budget constraint (30), O&R p. 233: from (24) with `Q_t = B_t + K_t`, the
zero-profit identity `Y_T + pY_N = rK + wL`, `K_{s+1} = K_s + I_s` and transversality,
`∑ (1+r)^{−(s−t)} P_s C_s = (1+r)B_t + ∑ (1+r)^{−(s−t)}(Y_T + pY_N − I − G)`. -/
theorem national_budget {r B0 : ℝ} {PC w L G YT p YN K I : ℕ → ℝ} (hr : 1 + r ≠ 0)
    (hK : ∀ s, K (s + 1) = K s + I s)
    (hTV : Tendsto (fun T => ((1 + r)⁻¹) ^ T * K T) atTop (𝓝 0))
    (hS : Summable fun s => ((1 + r)⁻¹) ^ (s + 1) * (r * K s - I s))
    (hY : Summable fun s => ((1 + r)⁻¹) ^ s * (w s * L s - G s))
    (hGDP : ∀ s, YT s + p s * YN s = r * K s + w s * L s)
    (h24 : ∑' s, ((1 + r)⁻¹) ^ s * PC s
      = (1 + r) * (B0 + K 0) + ∑' s, ((1 + r)⁻¹) ^ s * (w s * L s - G s)) :
    Summable (fun s => ((1 + r)⁻¹) ^ s * (YT s + p s * YN s - I s - G s)) ∧
    ∑' s, ((1 + r)⁻¹) ^ s * PC s
      = (1 + r) * B0 + ∑' s, ((1 + r)⁻¹) ^ s * (YT s + p s * YN s - I s - G s) := by
  have e : (fun s => ((1 + r)⁻¹) ^ s * (YT s + p s * YN s - I s - G s))
      = fun s => (1 + r) * (((1 + r)⁻¹) ^ (s + 1) * (r * K s - I s))
          + ((1 + r)⁻¹) ^ s * (w s * L s - G s) := by
    funext s
    rw [pow_succ]
    linear_combination (((1 + r)⁻¹) ^ s) * hGDP s
      + (-(((1 + r)⁻¹) ^ s * (r * K s - I s))) * (mul_inv_cancel₀ hr)
  refine ⟨e ▸ (hS.mul_left _).add hY, ?_⟩
  rw [e, (hS.mul_left _).tsum_add hY, tsum_mul_left, capital_eq_present_value hr hK hTV hS, h24]
  ring

/-- The tradables-only intertemporal budget (32), O&R p. 233: with `PC = C_T + pC_N`
((14), (21)), nontradables market clearing (31) `C_N + G_N = Y_N` and `G = G_T + pG_N`, the
national budget (30) becomes `∑ (1+r)^{−(s−t)}(C_T + I + G_T) = (1+r)B_t + ∑ (1+r)^{−(s−t)} Y_T`.
-/
theorem tradables_budget {r B0 : ℝ} {P C CT CN p YT YN I G GT GN : ℕ → ℝ}
    (hPC : ∀ s, P s * C s = CT s + p s * CN s) (hN : ∀ s, CN s + GN s = YN s)
    (hG : ∀ s, G s = GT s + p s * GN s)
    (hA : Summable fun s => ((1 + r)⁻¹) ^ s * (P s * C s))
    (hB : Summable fun s => ((1 + r)⁻¹) ^ s * (YT s + p s * YN s - I s - G s))
    (hYT : Summable fun s => ((1 + r)⁻¹) ^ s * YT s)
    (h30 : ∑' s, ((1 + r)⁻¹) ^ s * (P s * C s)
      = (1 + r) * B0 + ∑' s, ((1 + r)⁻¹) ^ s * (YT s + p s * YN s - I s - G s)) :
    Summable (fun s => ((1 + r)⁻¹) ^ s * (CT s + I s + GT s)) ∧
    ∑' s, ((1 + r)⁻¹) ^ s * (CT s + I s + GT s)
      = (1 + r) * B0 + ∑' s, ((1 + r)⁻¹) ^ s * YT s := by
  have e : (fun s => ((1 + r)⁻¹) ^ s * (CT s + I s + GT s))
      = fun s => ((1 + r)⁻¹) ^ s * (P s * C s)
          - ((1 + r)⁻¹) ^ s * (YT s + p s * YN s - I s - G s) + ((1 + r)⁻¹) ^ s * YT s := by
    funext s
    linear_combination (-((1 + r)⁻¹) ^ s) * hPC s + (-(((1 + r)⁻¹) ^ s * p s)) * hN s
      + (-((1 + r)⁻¹) ^ s) * hG s
  refine ⟨e ▸ (hA.sub hB).add hYT, ?_⟩
  rw [e, (hA.sub hB).tsum_add hYT, hA.tsum_sub hB, h30]
  ring

/-- The isoelastic Euler equation (33), O&R p. 234: with `u′(C) = C^{−1/σ}`, the Euler equation
(26) `C_s^{−1/σ} = (1 + r^C_{s+1}) β C_{s+1}^{−1/σ}` is equivalent to
`C_{s+1} = [(1+r)P_s/P_{s+1}]^σ β^σ C_s` (for positive consumption). -/
theorem euler_isoelastic {r σ β : ℝ} {P C : ℕ → ℝ} (hσ : 0 < σ) (hr : 0 < 1 + r)
    (hP : ∀ s, 0 < P s) (hβ : 0 < β) (hC : ∀ s, 0 < C s) (s : ℕ) :
    C s ^ (-1 / σ) = grossRealRate r P s * β * C (s + 1) ^ (-1 / σ) ↔
      C (s + 1) = grossRealRate r P s ^ σ * β ^ σ * C s := by
  have hg := grossRealRate_pos hr hP s
  have h0 := hC s
  have h1 := hC (s + 1)
  have e : -1 / σ * -σ = 1 := by field_simp
  have hinv : ∀ x : ℝ, 0 < x → (x ^ (-1 / σ)) ^ (-σ) = x := by
    intro x hx; rw [← rpow_mul hx.le, e, rpow_one]
  constructor
  · intro h
    have h' := congrArg (fun x => x ^ (-σ)) h
    rw [hinv _ h0, mul_rpow (by positivity) (by positivity), hinv _ h1,
      mul_rpow hg.le hβ.le, rpow_neg hg.le, rpow_neg hβ.le] at h'
    rw [h']
    have := rpow_pos_of_pos hg σ
    have := rpow_pos_of_pos hβ σ
    field_simp
  · intro h
    rw [h, mul_rpow (by positivity) h0.le, mul_rpow (by positivity) (by positivity),
      ← rpow_mul hg.le, ← rpow_mul hβ.le]
    have e2 : σ * (-1 / σ) = -1 := by field_simp
    rw [e2, rpow_neg_one, rpow_neg_one]
    field_simp

/-- The Euler equation for tradables (34), O&R p. 234: combining (33) with the CES demand
(22) `C_T = γ P^θ C`, `C_{T,s+1} = (P_s/P_{s+1})^{σ−θ} (1+r)^σ β^σ C_{T,s}`. -/
theorem euler_tradables {r σ θ β γ : ℝ} {P C CT : ℕ → ℝ} (hr : 0 < 1 + r)
    (hP : ∀ s, 0 < P s) (hβ : 0 < β)
    (hE : ∀ s, C (s + 1) = grossRealRate r P s ^ σ * β ^ σ * C s)
    (h22 : ∀ s, CT s = γ * P s ^ θ * C s) (s : ℕ) :
    CT (s + 1) = (P s / P (s + 1)) ^ (σ - θ) * ((1 + r) ^ σ * β ^ σ) * CT s := by
  have h0 := hP s
  have h1 := hP (s + 1)
  rw [h22, h22, hE, grossRealRate, mul_div_assoc, mul_rpow hr.le (by positivity),
    rpow_sub (by positivity), div_rpow h0.le h1.le, div_rpow h0.le h1.le]
  have := rpow_pos_of_pos h0 θ
  have := rpow_pos_of_pos h1 θ
  have := rpow_pos_of_pos h1 σ
  field_simp

/-- Iterating the tradables Euler equation (34), O&R p. 234:
`C_{T,s} = [(1+r)^σ β^σ]^{s−t} (P_t/P_s)^{σ−θ} C_{T,t}`. -/
theorem tradables_consumption_path {r σ θ β : ℝ} {P CT : ℕ → ℝ} (hP : ∀ s, 0 < P s)
    (h34 : ∀ s, CT (s + 1) = (P s / P (s + 1)) ^ (σ - θ) * ((1 + r) ^ σ * β ^ σ) * CT s)
    (n : ℕ) : CT n = ((1 + r) ^ σ * β ^ σ) ^ n * (P 0 / P n) ^ (σ - θ) * CT 0 := by
  induction n with
  | zero => simp [(hP 0).ne']
  | succ n ih =>
    have h0 := hP 0; have hn := hP n; have hn1 := hP (n + 1)
    have e : (P 0 / P (n + 1)) ^ (σ - θ)
        = (P 0 / P n) ^ (σ - θ) * (P n / P (n + 1)) ^ (σ - θ) := by
      rw [← mul_rpow (by positivity) (by positivity)]
      congr 1
      field_simp
    rw [h34, ih, e, pow_succ]
    ring

/-- The tradables consumption function (35), O&R p. 234: iterating (34) and substituting in the
tradables budget `∑ (1+r)^{−(s−t)} C_{T,s} = W` (the book's
`W = (1+r)B_t + ∑ (1+r)^{−(s−t)}(Y_T − I − G_T)` from (32)),
`C_{T,t} = W / ∑ [(1+r)^{σ−1}β^σ]^{s−t} (P_t/P_s)^{σ−θ}`. -/
theorem tradables_consumption_function {r σ θ β W : ℝ} {P CT : ℕ → ℝ} (hr : 0 < 1 + r)
    (hP : ∀ s, 0 < P s) (hβ : 0 < β)
    (h34 : ∀ s, CT (s + 1) = (P s / P (s + 1)) ^ (σ - θ) * ((1 + r) ^ σ * β ^ σ) * CT s)
    (hsum : Summable fun s => ((1 + r) ^ (σ - 1) * β ^ σ) ^ s * (P 0 / P s) ^ (σ - θ))
    (hW : ∑' s, ((1 + r)⁻¹) ^ s * CT s = W) :
    CT 0 = W / ∑' s, ((1 + r) ^ (σ - 1) * β ^ σ) ^ s * (P 0 / P s) ^ (σ - θ) := by
  have hpath := tradables_consumption_path hP h34
  have hd : (1 + r)⁻¹ * ((1 + r) ^ σ * β ^ σ) = (1 + r) ^ (σ - 1) * β ^ σ := by
    rw [rpow_sub_one hr.ne']; ring
  have hterm : ∀ n, ((1 + r)⁻¹) ^ n * CT n
      = ((1 + r) ^ (σ - 1) * β ^ σ) ^ n * (P 0 / P n) ^ (σ - θ) * CT 0 := by
    intro n
    rw [hpath n, ← hd, mul_pow]
    ring
  have hden : 0 < ∑' s, ((1 + r) ^ (σ - 1) * β ^ σ) ^ s * (P 0 / P s) ^ (σ - θ) := by
    refine hsum.tsum_pos (fun n => ?_) 0 ?_
    · have := hP n; have := hP 0; positivity
    · have := hP 0; positivity
  rw [← hW, tsum_congr hterm, tsum_mul_right]
  field_simp

/-- The current account (36), O&R p. 234: `CA_t = B_{t+1} − B_t = rB_t + Y_T + pY_N − C_T − pC_N
− I − G` reduces to `rB_t + Y_T − C_T − I − G_T` under (31) and `G = G_T + pG_N`. -/
theorem current_account_tradables {r B0 B1 YT p YN CT CN I G GT GN : ℝ}
    (hCA : B1 - B0 = r * B0 + YT + p * YN - CT - p * CN - I - G) (hN : CN + GN = YN)
    (hG : G = GT + p * GN) :
    B1 - B0 = r * B0 + YT - CT - I - GT := by
  rw [hCA, hG, ← hN]; ring

/-- The p. 235 claim, O&R: if the price index rises over time (`P_t ≤ P_s` for all `s`, strictly
for some `s`) and `σ > θ`, initial tradables consumption from (35) strictly exceeds its
constant-`P` level `W / ∑ x^{s−t}`, `x = (1+r)^{σ−1}β^σ` (for positive wealth `W`). -/
theorem tradables_consumption_gt_constant_price {σ θ x W : ℝ} {P : ℕ → ℝ} {s0 : ℕ}
    (hσθ : θ < σ) (hx : 0 < x) (hW : 0 < W) (hP : ∀ s, 0 < P s) (hmono : ∀ s, P 0 ≤ P s)
    (hstrict : P 0 < P s0) (hsumP : Summable fun s => x ^ s * (P 0 / P s) ^ (σ - θ))
    (hgeo : Summable fun s : ℕ => x ^ s) :
    W / ∑' s : ℕ, x ^ s < W / ∑' s, x ^ s * (P 0 / P s) ^ (σ - θ) := by
  have hle : ∀ s, x ^ s * (P 0 / P s) ^ (σ - θ) ≤ x ^ s := by
    intro s
    have h := rpow_le_one (div_pos (hP 0) (hP s)).le ((div_le_one (hP s)).mpr (hmono s))
      (sub_nonneg.mpr hσθ.le)
    have := pow_pos hx s
    nlinarith
  have hlt : x ^ s0 * (P 0 / P s0) ^ (σ - θ) < x ^ s0 := by
    have h := rpow_lt_one (div_pos (hP 0) (hP s0)).le ((div_lt_one (hP s0)).mpr hstrict)
      (sub_pos.mpr hσθ)
    have := pow_pos hx s0
    nlinarith
  have hden : 0 < ∑' s, x ^ s * (P 0 / P s) ^ (σ - θ) := by
    refine hsumP.tsum_pos (fun n => ?_) 0 ?_
    · have := hP n; have := hP 0; positivity
    · have := hP 0; positivity
  exact div_lt_div_of_pos_left hW hden (hsumP.tsum_lt_tsum hle hlt hgeo)

/-- The p. 235 converse, O&R: if the price index rises over time and `θ > σ`, "the
intratemporal substitution effect wins out": initial tradables consumption from (35) is strictly
below its constant-`P` level. -/
theorem tradables_consumption_lt_constant_price {σ θ x W : ℝ} {P : ℕ → ℝ} {s0 : ℕ}
    (hσθ : σ < θ) (hx : 0 < x) (hW : 0 < W) (hP : ∀ s, 0 < P s) (hmono : ∀ s, P 0 ≤ P s)
    (hstrict : P 0 < P s0) (hsumP : Summable fun s => x ^ s * (P 0 / P s) ^ (σ - θ))
    (hgeo : Summable fun s : ℕ => x ^ s) :
    W / ∑' s, x ^ s * (P 0 / P s) ^ (σ - θ) < W / ∑' s : ℕ, x ^ s := by
  have hle : ∀ s, x ^ s ≤ x ^ s * (P 0 / P s) ^ (σ - θ) := by
    intro s
    have h := one_le_rpow_of_pos_of_le_one_of_nonpos (div_pos (hP 0) (hP s))
      ((div_le_one (hP s)).mpr (hmono s)) (sub_nonpos.mpr hσθ.le)
    have := pow_pos hx s
    nlinarith
  have hlt : x ^ s0 < x ^ s0 * (P 0 / P s0) ^ (σ - θ) := by
    have h := one_lt_rpow_of_pos_of_lt_one_of_neg (div_pos (hP 0) (hP s0))
      ((div_lt_one (hP s0)).mpr hstrict) (sub_neg.mpr hσθ)
    have := pow_pos hx s0
    nlinarith
  have hden : 0 < ∑' s : ℕ, x ^ s :=
    hgeo.tsum_pos (fun n => (pow_pos hx n).le) 0 (by simp)
  exact div_lt_div_of_pos_left hW hden (hgeo.tsum_lt_tsum hle hlt hsumP)

/-- Exercise 3, O&R p. 265 (identity): with `1 + r^C_t = (1+r)P_{t−1}/P_t`,
`(1 + r^C_t) B_t / P_{t−1} = (1+r) B_t / P_t`. -/
theorem ex3_gross_rate_identity {r Pm P0 B : ℝ} (hPm : Pm ≠ 0) (hP0 : P0 ≠ 0) :
    (1 + r) * Pm / P0 * B / Pm = (1 + r) * B / P0 := by
  field_simp

/-- Exercise 3, O&R p. 265: retracing (27) from the national budget (30) instead of (24),
`∑ R^C_{t,s} C_s = (1 + r^C_t)B_t/P_{t−1} + ∑ R^C_{t,s}(Y_T + pY_N − I − G)_s/P_s`, where
`X_s = Y_{T,s} + p_sY_{N,s} − I_s − G_s` and `Pm = P_{t−1}`. -/
theorem ex3_alternative_budget {r B0 Pm : ℝ} {P C X : ℕ → ℝ} (hr : 0 < 1 + r)
    (hP : ∀ s, 0 < P s) (hPm : 0 < Pm)
    (hC : Summable fun s => ((1 + r)⁻¹) ^ s * (P s * C s))
    (hX : Summable fun s => ((1 + r)⁻¹) ^ s * X s)
    (h30 : ∑' s, ((1 + r)⁻¹) ^ s * (P s * C s) = (1 + r) * B0 + ∑' s, ((1 + r)⁻¹) ^ s * X s) :
    ∑' s, realDiscount r P s * C s
      = (1 + r) * Pm / P 0 * B0 / Pm + ∑' s, realDiscount r P s * (X s / P s) := by
  rw [ex3_gross_rate_identity hPm.ne' (hP 0).ne']
  exact (real_budget hr hP hC hX h30).2.2

/-- Exercise 3, O&R p. 265: the alternative consumption function parallel to Chapter 2's
(25), `C_t = [(1 + r^C_t)B_t/P_{t−1} + ∑ R^C_{t,s} X_s/P_s] / ∑ β^{σ(s−t)} (R^C_{t,s})^{1−σ}`. -/
theorem ex3_alternative_consumption {r σ β B0 Pm : ℝ} {P C X : ℕ → ℝ} (hr : 0 < 1 + r)
    (hP : ∀ s, 0 < P s) (hPm : 0 < Pm) (hβ : 0 < β)
    (hE : ∀ s, C (s + 1) = grossRealRate r P s ^ σ * β ^ σ * C s)
    (hC : Summable fun s => ((1 + r)⁻¹) ^ s * (P s * C s))
    (hX : Summable fun s => ((1 + r)⁻¹) ^ s * X s)
    (hsum : Summable fun n => realDiscount r P n ^ (1 - σ) * (β ^ σ) ^ n)
    (h30 : ∑' s, ((1 + r)⁻¹) ^ s * (P s * C s) = (1 + r) * B0 + ∑' s, ((1 + r)⁻¹) ^ s * X s) :
    C 0 = ((1 + r) * Pm / P 0 * B0 / Pm + ∑' s, realDiscount r P s * (X s / P s))
      / ∑' n, realDiscount r P n ^ (1 - σ) * (β ^ σ) ^ n :=
  consumption_of_budget hr hP hβ (consumption_path_of_euler hr hP hE) hsum
    (ex3_alternative_budget hr hP hPm hC hX h30)

/-- Exercise 3, O&R p. 265: the current account in real-consumption units, parallel to
Chapter 2's (26): from `B_{t+1} − B_t = rB_t + X_t − P_tC_t`,
`B_{t+1}/P_t − B_t/P_{t−1} = r^C_t B_t/P_{t−1} + X_t/P_t − C_t`. -/
theorem ex3_real_current_account {r B0 B1 X C0 P0 Pm : ℝ} (hP0 : P0 ≠ 0) (hPm : Pm ≠ 0)
    (hCA : B1 - B0 = r * B0 + X - P0 * C0) :
    B1 / P0 - B0 / Pm = ((1 + r) * Pm / P0 - 1) * (B0 / Pm) + X / P0 - C0 := by
  have hB1 : B1 = (1 + r) * B0 + X - P0 * C0 := by linarith
  rw [hB1]
  field_simp
  ring

/-- `P(p)/p` is the CES price index with the weights swapped, evaluated at `1/p`
(used in Exercise 4, O&R p. 265):
`[γ + (1−γ)p^{1−θ}]^{1/(1−θ)}/p = [(1−γ) + γ (1/p)^{1−θ}]^{1/(1−θ)}`. -/
theorem ex4_price_div_eq {γ θ p : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hθ1 : θ ≠ 1) (hp : 0 < p) :
    cesPrice γ θ p / p = cesPrice (1 - γ) θ p⁻¹ := by
  have hθm' : 1 - θ ≠ 0 := sub_ne_zero.mpr (Ne.symm hθ1)
  have hD := cesDenom_pos (θ := θ) hγ0 hγ1 hp
  unfold cesDenom at hD
  have hq := rpow_pos_of_pos hp (1 - θ)
  have hpe : p = (p ^ (1 - θ)) ^ (1 / (1 - θ)) := by
    rw [← rpow_mul hp.le, mul_one_div_cancel hθm', rpow_one]
  unfold cesPrice
  calc (γ + (1 - γ) * p ^ (1 - θ)) ^ (1 / (1 - θ)) / p
      = (γ + (1 - γ) * p ^ (1 - θ)) ^ (1 / (1 - θ)) / (p ^ (1 - θ)) ^ (1 / (1 - θ)) := by
        rw [← hpe]
    _ = ((γ + (1 - γ) * p ^ (1 - θ)) / p ^ (1 - θ)) ^ (1 / (1 - θ)) :=
        (div_rpow hD.le hq.le _).symm
    _ = _ := by
        rw [inv_rpow hp.le]
        congr 1
        field_simp
        ring

/-- `p/P(p)` is strictly increasing in `p` (used in Exercise 4, O&R p. 265): real consumption
per unit of nontradables, `C/C_N = (p/P)^θ/(1−γ)` by (22), rises with `p`. -/
theorem ex4_ratio_strictMonoOn {γ θ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hθ1 : θ ≠ 1) :
    StrictMonoOn (fun p => p / cesPrice γ θ p) (Set.Ioi 0) := by
  intro a ha b hb hab
  simp only [Set.mem_Ioi] at ha hb
  have h1γ0 : 0 < 1 - γ := by linarith
  have h1γ1 : 1 - γ < 1 := by linarith
  have ea : a / cesPrice γ θ a = (cesPrice (1 - γ) θ a⁻¹)⁻¹ := by
    rw [← ex4_price_div_eq hγ0 hγ1 hθ1 ha, inv_div]
  have eb : b / cesPrice γ θ b = (cesPrice (1 - γ) θ b⁻¹)⁻¹ := by
    rw [← ex4_price_div_eq hγ0 hγ1 hθ1 hb, inv_div]
  simp only
  rw [ea, eb]
  have hlt : cesPrice (1 - γ) θ b⁻¹ < cesPrice (1 - γ) θ a⁻¹ :=
    cesPrice_strictMonoOn h1γ0 h1γ1 hθ1 (inv_pos.mpr hb) (inv_pos.mpr ha)
      (inv_strictAnti₀ ha hab)
  exact (inv_lt_inv₀ (cesPrice_pos h1γ0 h1γ1 (inv_pos.mpr ha))
    (cesPrice_pos h1γ0 h1γ1 (inv_pos.mpr hb))).mpr hlt

/-- The quantity `(p/P)^θ P^σ`, proportional (by (22)) to `P^σ C / C_N`, which the Euler
equation (33) with `β(1+r) = 1` holds constant (Exercise 4, O&R p. 265). -/
noncomputable def ex4Invariant (γ θ σ p : ℝ) : ℝ := (p / cesPrice γ θ p) ^ θ * cesPrice γ θ p ^ σ

/-- The Exercise 4 invariant is strictly increasing in `p` for `θ, σ > 0` (O&R p. 265). -/
theorem ex4Invariant_strictMonoOn {γ θ σ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hθ : 0 < θ)
    (hθ1 : θ ≠ 1) (hσ : 0 < σ) : StrictMonoOn (ex4Invariant γ θ σ) (Set.Ioi 0) := by
  intro a ha b hb hab
  have ha' : (0 : ℝ) < a := ha
  have hb' : (0 : ℝ) < b := hb
  have hPa := cesPrice_pos (θ := θ) hγ0 hγ1 ha'
  have hPb := cesPrice_pos (θ := θ) hγ0 hγ1 hb'
  have h1 : (a / cesPrice γ θ a) ^ θ < (b / cesPrice γ θ b) ^ θ :=
    rpow_lt_rpow (div_pos ha' hPa).le (ex4_ratio_strictMonoOn hγ0 hγ1 hθ1 ha hb hab) hθ
  have h2 : cesPrice γ θ a ^ σ < cesPrice γ θ b ^ σ :=
    rpow_lt_rpow hPa.le (cesPrice_strictMonoOn hγ0 hγ1 hθ1 ha hb hab) hσ
  unfold ex4Invariant
  have := rpow_pos_of_pos hPa σ
  have := rpow_pos_of_pos (div_pos hb' hPb) θ
  calc (a / cesPrice γ θ a) ^ θ * cesPrice γ θ a ^ σ
      < (b / cesPrice γ θ b) ^ θ * cesPrice γ θ a ^ σ := by gcongr
    _ < (b / cesPrice γ θ b) ^ θ * cesPrice γ θ b ^ σ := by gcongr

/-- Exercise 4, O&R p. 265: along an equilibrium path with nontradable supply `N_s = C_{N,s}`,
the demand (22) `C_N = (1−γ)(p/P)^{−θ}C` and the Euler equation (33) with `β(1+r) = 1` imply
that `N_s (p_s/P_s)^θ P_s^σ` is constant over time. -/
theorem ex4_invariant_step {γ θ σ β r : ℝ} {p C N : ℕ → ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hr : 0 < 1 + r) (hβ : 0 < β) (hβr : β * (1 + r) = 1) (hp : ∀ s, 0 < p s)
    (h22N : ∀ s, N s = (1 - γ) * (p s / cesPrice γ θ (p s)) ^ (-θ) * C s)
    (hE : ∀ s, C (s + 1) = grossRealRate r (fun s => cesPrice γ θ (p s)) s ^ σ * β ^ σ * C s)
    (s : ℕ) : N (s + 1) * ex4Invariant γ θ σ (p (s + 1)) = N s * ex4Invariant γ θ σ (p s) := by
  have hP : ∀ s, 0 < cesPrice γ θ (p s) := fun s => cesPrice_pos hγ0 hγ1 (hp s)
  have key : ∀ s, N s * ex4Invariant γ θ σ (p s) = (1 - γ) * (C s * cesPrice γ θ (p s) ^ σ) := by
    intro s
    have hx := div_pos (hp s) (hP s)
    rw [h22N s, ex4Invariant, rpow_neg hx.le]
    have := rpow_pos_of_pos hx θ
    field_simp
  rw [key, key, hE, grossRealRate, mul_div_assoc,
    mul_rpow hr.le (div_pos (hP s) (hP (s + 1))).le, div_rpow (hP s).le (hP (s + 1)).le]
  have e1 : (1 + r) ^ σ * β ^ σ = 1 := by
    rw [← mul_rpow hr.le hβ.le, mul_comm, hβr, one_rpow]
  have := rpow_pos_of_pos (hP (s + 1)) σ
  field_simp
  linear_combination (C s * cesPrice γ θ (p s) ^ σ * (1 - γ)) * e1

/-- Exercise 4(a), O&R p. 265: with `β(1+r) = 1` and a constant net endowment of nontradables
`Y_N − G_N = N̄ > 0`, equilibrium (22) + (33) forces the relative price `p`, real consumption
`C` and tradables consumption `C_T` to be constant over time. -/
theorem ex4a_constant {γ θ σ β r Nbar : ℝ} {p C CT : ℕ → ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hθ : 0 < θ) (hθ1 : θ ≠ 1) (hσ : 0 < σ) (hr : 0 < 1 + r) (hβ : 0 < β)
    (hβr : β * (1 + r) = 1) (hNbar : 0 < Nbar) (hp : ∀ s, 0 < p s)
    (h22T : ∀ s, CT s = γ * cesPrice γ θ (p s) ^ θ * C s)
    (h22N : ∀ s, Nbar = (1 - γ) * (p s / cesPrice γ θ (p s)) ^ (-θ) * C s)
    (hE : ∀ s, C (s + 1) = grossRealRate r (fun s => cesPrice γ θ (p s)) s ^ σ * β ^ σ * C s)
    (s : ℕ) : p s = p 0 ∧ C s = C 0 ∧ CT s = CT 0 := by
  have hinv : ∀ s, ex4Invariant γ θ σ (p s) = ex4Invariant γ θ σ (p 0) := by
    intro s
    induction s with
    | zero => rfl
    | succ n ih =>
      have h := ex4_invariant_step (N := fun _ => Nbar) hγ0 hγ1 hr hβ hβr hp h22N hE n
      rw [← ih]
      exact mul_left_cancel₀ hNbar.ne' h
  have hps : p s = p 0 :=
    (ex4Invariant_strictMonoOn hγ0 hγ1 hθ hθ1 hσ).injOn (hp s) (hp 0) (hinv s)
  have hCs : C s = C 0 := by
    have h := (h22N s).symm.trans (h22N 0)
    rw [hps] at h
    have hx := div_pos (hp 0) (cesPrice_pos (θ := θ) hγ0 hγ1 (hp 0))
    have : 0 < (1 - γ) * (p 0 / cesPrice γ θ (p 0)) ^ (-θ) :=
      mul_pos (by linarith) (rpow_pos_of_pos hx _)
    exact mul_left_cancel₀ this.ne' h
  refine ⟨hps, hCs, ?_⟩
  rw [h22T s, h22T 0, hps, hCs]

/-- Exercise 4(a), O&R p. 265: the constant level of tradables consumption is
`C_T = [r/(1+r)] [(1+r)B_t + ∑ (1+r)^{−(s−t)}(Y_T − I − G_T)_s]`, exactly the tradables
analogue of Chapter 2's consumption function (10) (for `r > 0`). -/
theorem ex4a_level {r B0 cbar : ℝ} {X : ℕ → ℝ} (hr : 0 < r)
    (h32 : ∑' s : ℕ, ((1 + r)⁻¹) ^ s * cbar = (1 + r) * B0 + ∑' s, ((1 + r)⁻¹) ^ s * X s) :
    cbar = r / (1 + r) * ((1 + r) * B0 + ∑' s, ((1 + r)⁻¹) ^ s * X s) := by
  have hd0 : 0 ≤ (1 + r)⁻¹ := inv_nonneg.mpr (by linarith)
  have hd1 : (1 + r)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  rw [← h32, tsum_mul_right, tsum_geometric_of_lt_one hd0 hd1]
  have : (1 : ℝ) + r ≠ 0 := by linarith
  have : r ≠ 0 := hr.ne'
  field_simp
  simp [this]

/-- Exercise 4(b), O&R p. 265: suppose it becomes known that the nontradable net supply rises
permanently from `N₁` to `N₂ > N₁` after date `t + T` (index `T`). With `β(1+r) = 1`:
the relative price is constant except between `T` and `T+1`, where it falls, as does `P`;
tradables consumption jumps by the factor `(P_T/P_{T+1})^{σ−θ}`, upward iff `σ > θ`. -/
theorem ex4b_step {γ θ σ β r N1 N2 : ℝ} {T : ℕ} {p C CT N : ℕ → ℝ} (hγ0 : 0 < γ)
    (hγ1 : γ < 1) (hθ : 0 < θ) (hθ1 : θ ≠ 1) (hσ : 0 < σ) (hr : 0 < 1 + r) (hβ : 0 < β)
    (hβr : β * (1 + r) = 1) (hN1 : 0 < N1) (hN12 : N1 < N2) (hp : ∀ s, 0 < p s)
    (hC : ∀ s, 0 < C s) (hN : ∀ s, N s = if s ≤ T then N1 else N2)
    (h22T : ∀ s, CT s = γ * cesPrice γ θ (p s) ^ θ * C s)
    (h22N : ∀ s, N s = (1 - γ) * (p s / cesPrice γ θ (p s)) ^ (-θ) * C s)
    (hE : ∀ s, C (s + 1) = grossRealRate r (fun s => cesPrice γ θ (p s)) s ^ σ * β ^ σ * C s) :
    (∀ s, s ≠ T → p (s + 1) = p s) ∧ p (T + 1) < p T ∧
    cesPrice γ θ (p (T + 1)) < cesPrice γ θ (p T) ∧
    CT (T + 1) = (cesPrice γ θ (p T) / cesPrice γ θ (p (T + 1))) ^ (σ - θ) * CT T ∧
    (θ < σ → CT T < CT (T + 1)) ∧ (σ < θ → CT (T + 1) < CT T) := by
  have hmono := ex4Invariant_strictMonoOn hγ0 hγ1 hθ hθ1 hσ
  have hstep := ex4_invariant_step hγ0 hγ1 hr hβ hβr hp h22N hE
  have hI : ∀ s, 0 < ex4Invariant γ θ σ (p s) := by
    intro s
    have hP := cesPrice_pos (θ := θ) hγ0 hγ1 (hp s)
    unfold ex4Invariant
    have := rpow_pos_of_pos (div_pos (hp s) hP) θ
    have := rpow_pos_of_pos hP σ
    positivity
  have hflat : ∀ s, s ≠ T → p (s + 1) = p s := by
    intro s hs
    have hNs : N (s + 1) = N s := by
      rw [hN, hN]
      rcases lt_or_gt_of_ne hs with h | h
      · simp [show s ≤ T by omega, show s + 1 ≤ T by omega]
      · simp [show ¬ s ≤ T by omega, show ¬ s + 1 ≤ T by omega]
    have hNpos : 0 < N s := by rw [hN]; split_ifs <;> linarith
    have h := hstep s
    rw [hNs] at h
    exact hmono.injOn (hp (s + 1)) (hp s) (mul_left_cancel₀ hNpos.ne' h)
  have hdrop : p (T + 1) < p T := by
    have h := hstep T
    have hNT : N T = N1 := by rw [hN]; simp
    have hNT1 : N (T + 1) = N2 := by rw [hN]; simp
    rw [hNT, hNT1] at h
    have hlt : ex4Invariant γ θ σ (p (T + 1)) < ex4Invariant γ θ σ (p T) := by
      have h1 := hI T
      have h2 := hI (T + 1)
      nlinarith
    exact (hmono.lt_iff_lt (hp (T + 1)) (hp T)).mp hlt
  have hPdrop := cesPrice_strictMonoOn hγ0 hγ1 hθ1 (hp (T + 1)) (hp T) hdrop
  have hPpos : ∀ s, 0 < cesPrice γ θ (p s) := fun s => cesPrice_pos hγ0 hγ1 (hp s)
  have e1 : (1 + r) ^ σ * β ^ σ = 1 := by
    rw [← mul_rpow hr.le hβ.le, mul_comm, hβr, one_rpow]
  have hjump : CT (T + 1)
      = (cesPrice γ θ (p T) / cesPrice γ θ (p (T + 1))) ^ (σ - θ) * CT T := by
    have h := euler_tradables (P := fun s => cesPrice γ θ (p s)) hr hPpos hβ hE h22T T
    rw [h, e1, mul_one]
  have hbase : 1 < cesPrice γ θ (p T) / cesPrice γ θ (p (T + 1)) :=
    (one_lt_div (hPpos (T + 1))).mpr hPdrop
  have hCT : 0 < CT T := by
    rw [h22T]; have := rpow_pos_of_pos (hPpos T) θ; have := hC T; positivity
  refine ⟨hflat, hdrop, hPdrop, hjump, fun h => ?_, fun h => ?_⟩
  · rw [hjump]
    have := one_lt_rpow hbase (sub_pos.mpr h)
    nlinarith
  · rw [hjump]
    have := rpow_lt_one_of_one_lt_of_neg hbase (sub_neg.mpr h)
    nlinarith

/-- Exercise 4(b), O&R p. 265: starting from a zero-current-account steady state with constant
tradable net output `X̄ = Y_T − I − G_T`, if the new tradables consumption path never falls below
its date-`t` level and strictly exceeds it at some date (the case `σ > θ` of `ex4b_step`), the
date-`t` current account (36), `rB_t + X̄ − C_{T,t}`, is in surplus. -/
theorem ex4b_current_account_surplus {r B0 Xbar : ℝ} {c : ℕ → ℝ} {T : ℕ} (hr : 0 < r)
    (hge : ∀ s, c 0 ≤ c s) (hlt : c 0 < c T)
    (hc : Summable fun s => ((1 + r)⁻¹) ^ s * c s)
    (h32 : ∑' s, ((1 + r)⁻¹) ^ s * c s = (1 + r) * B0 + ∑' s : ℕ, ((1 + r)⁻¹) ^ s * Xbar) :
    0 < r * B0 + Xbar - c 0 := by
  have hd0 : 0 ≤ (1 + r)⁻¹ := inv_nonneg.mpr (by linarith)
  have hd1 : (1 + r)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hdpos : 0 < (1 + r)⁻¹ := inv_pos.mpr (by linarith)
  have hgeo := summable_geometric_of_lt_one hd0 hd1
  have hlt' : ∑' s : ℕ, ((1 + r)⁻¹) ^ s * c 0 < ∑' s, ((1 + r)⁻¹) ^ s * c s :=
    (hgeo.mul_right _).tsum_lt_tsum
      (fun s => mul_le_mul_of_nonneg_left (hge s) (pow_nonneg hd0 s))
      (mul_lt_mul_of_pos_left hlt (pow_pos hdpos T)) hc
  rw [h32, tsum_mul_right, tsum_mul_right, tsum_geometric_of_lt_one hd0 hd1] at hlt'
  have e : (1 - (1 + r)⁻¹)⁻¹ = (1 + r) / r := by
    have : (1 : ℝ) + r ≠ 0 := by linarith
    have : r ≠ 0 := hr.ne'
    field_simp
    simp [this]
  rw [e] at hlt'
  have h1r : 0 < (1 + r) / r := div_pos (by linarith) hr
  have : (1 + r) / r * c 0 < (1 + r) / r * (r * B0 + Xbar) := by
    have : (1 + r) * B0 = (1 + r) / r * (r * B0) := by field_simp
    nlinarith
  nlinarith [(mul_lt_mul_iff_right₀ h1r).mp this]

end ObstfeldRogoff.RealExchangeRate.ConsumptionDynamics
