/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StickyPriceModels.ReduxLogLinear
import StickyPriceModels.ReduxSteadyState
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The redux model: money shocks with preset prices

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §10.1.7
(pp. 674–683), §10.1.8.1 (pp. 683–684), p. 688 (country size) and Exercise 1 (p. 713).

* **No overshooting, EXACTLY (T13)**: for ANY permanent money shock after which the economy is
  in a flexible-price steady state from date 2, money demand (14), the Euler equation (13) and
  Fisher parity force `i₂ = δ` in each country exactly (`nominal_rate_exact`); with exact
  uncovered interest parity (real bonds + PPP, `uip_exact`) the exchange rate jumps at once to
  its long-run value, `𝓔₁ = 𝓔₂` (`no_overshooting_exact`). The linear version (58)–(60)
  (`mm_no_overshooting`) and the forward solution (61) under a no-bubble condition, with
  existence and uniqueness (`forward_solution_unique`, `forward_solution_exists`).
* **The GG schedule and the closed forms (62)–(68) (T14)** and **world aggregates (69)–(74)
  (T15)**: the full short-run/long-run linear system (`MoneyShockEqm`) has exactly one
  solution for every `m, m*` (`moneyShock_iff`), namely `e = [δ(1+θ)+2θ](m−m*)/D` (65),
  `c − c* = δ(θ²−1)(m−m*)/D` (66), `b̄ = 2(1−n)(θ−1)(m−m*)/(δ(1+θ)+2)` (67), (68),
  `cᵂ = mᵂ = yᵂ` (72), `r = −((1+δ)/δ)mᵂ` (73), and (74).
* **Comparative statics (T14)**: `e/(m−m*)` equals 1 at `θ = 1`, lies in `(0,1)` for `θ > 1`, is
  strictly decreasing in `θ` and tends to 0; the GG slope tends to 0 ("horizontal"); the
  short-run terms-of-trade effect exceeds the long-run one, their ratio being `O(δ)`; the CA
  effect falls with `n`. **(65) corrected**: `e < m − m*` iff `m − m* > 0` (for a contraction the
  inequality reverses); in general `|e| < |m − m*|`.
* **p. 688 corrected**: country size DOES enter the current account (67); the size-free object
  is the per-capita differential `b̄ − b̄* = b̄/(1−n)`.
* **The nominal interest rate is unchanged (T15)**: `î = 0` in each country after any permanent
  shock (`nominal_rate_unchanged`), the linear shadow of `nominal_rate_exact`.
* **Temporary shocks (fn 16, T16)**: effects are those of a permanent shock scaled by
  `δ/(1+δ)`, and the Home currency ends PERMANENTLY APPRECIATED, `e_t = −(c − c*) < 0` for
  `t ≥ 2` (not stated in the book).
* **Money growth (Exercise 1)**: `1 + ī = (1+δ)(1+μ)`, (26′), (37′), the MM′ schedule
  `e = ν(1+ī)/ī − (c−c*)` and the solution `e = [δ(1+θ)+2θ]ν(1+ī)/(ī D)`, and the variant with
  the growth change from date 2 (intercept `ν/ī`).
* **The equiproportionate shock, EXACTLY (10.1.8.1, T19)**: in the nonlinear model with preset
  prices, `M → μM`, `M* → μM*` has a unique equilibrium: `𝓔₁ = 𝓔₀`, `B₂ = 0`,
  `C₁ = C₁* = y₁ = y₁* = μȳ₀`, `i₂ = δ`, `1 + r₂ = (1+δ)/μ` (`equiproportionate_unique`,
  `equiproportionate_exists`). Output is demand-determined only while price ≥ marginal cost,
  `μ ≤ (θ/(θ−1))^{1/2}`; on that range the exact utility gain
  `log μ − ((θ−1)/(2θ))(μ² − 1)` is positive for `μ > 1` and has derivative `1/θ` at `μ = 1`.
-/

namespace ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks

open Real Filter Topology ReduxPrimitives ReduxLogLinear ReduxSteadyState

/-! ## No overshooting, exactly (T13) -/

/-- **The nominal interest rate after a permanent money shock is exactly `δ`** (T13; the exact
content of O&R (58)–(60), p. 678). Suppose money is permanently changed, `M₂ = M₁`, and from
date 2 the economy is in a steady state (constant prices, `i₃ = δ`). Money demand (14) at dates
1 and 2, the Euler equation (13) `C₂ = β(1+r₂)C₁`, Fisher parity
`1 + i₂ = (P₂/P₁)(1 + r₂)` and `β(1+δ) = 1` force `i₂ = δ`. -/
theorem nominal_rate_exact {β δ χ M P1 P2 C1 C2 r2 i2 : ℝ} (hβ : 0 < β) (hδ : 0 < δ)
    (hβδ : β * (1 + δ) = 1) (hχ : 0 < χ) (hM : 0 < M) (hP1 : 0 < P1) (hP2 : 0 < P2)
    (hC1 : 0 < C1) (hi2 : 0 < i2) (hr2 : 0 < 1 + r2)
    (hmd1 : M / P1 = χ * C1 * ((1 + i2) / i2)) (hmd2 : M / P2 = χ * C2 * ((1 + δ) / δ))
    (heuler : C2 = β * (1 + r2) * C1) (hfisher : 1 + i2 = P2 / P1 * (1 + r2)) : i2 = δ := by
  rw [heuler] at hmd2
  rw [div_eq_iff hP1.ne'] at hmd1
  rw [div_eq_iff hP2.ne'] at hmd2
  have a1 : M * i2 = χ * C1 * ((1 + i2) * P1) := by
    rw [hmd1]; field_simp
  have a2 : M * δ = χ * C1 * (1 + r2) * P2 * (β * (1 + δ)) := by
    rw [hmd2]; field_simp
  have hfis : (1 + i2) * P1 = P2 * (1 + r2) := by
    rw [hfisher]; field_simp
  rw [hfis] at a1
  rw [hβδ, mul_one] at a2
  have : M * (i2 - δ) = 0 := by linear_combination a1 - a2
  have := (mul_eq_zero.1 this).resolve_left hM.ne'
  linarith

/-- **Exact uncovered interest parity** (O&R p. 663 and p. 677): with a real bond in units of the
common consumption basket and PPP `𝓔 = P/P*` (7), the two Fisher relations
`1 + i = (P₂/P₁)(1 + r)` and `1 + i* = (P₂*/P₁*)(1 + r)` give `1 + i = (𝓔₂/𝓔₁)(1 + i*)`. -/
theorem uip_exact {P1 P2 Ps1 Ps2 r i is : ℝ} (hP1 : 0 < P1) (hPs1 : 0 < Ps1) (hPs2 : 0 < Ps2)
    (hf : 1 + i = P2 / P1 * (1 + r)) (hfs : 1 + is = Ps2 / Ps1 * (1 + r)) :
    1 + i = (P2 / Ps2) / (P1 / Ps1) * (1 + is) := by
  rw [hf, hfs]
  field_simp

/-- **No overshooting, EXACTLY** (T13; O&R p. 678 "the exchange rate jumps immediately to its new
long-run equilibrium"): if both nominal rates equal `δ` (`nominal_rate_exact`) then exact UIP
forces `𝓔₁ = 𝓔₂`, the long-run rate. The book's result is not an artefact of linearisation. -/
theorem no_overshooting_exact {δ P1 P2 Ps1 Ps2 r : ℝ} (hδ : 0 < δ) (hP1 : 0 < P1)
    (hPs1 : 0 < Ps1) (hPs2 : 0 < Ps2) (hf : 1 + δ = P2 / P1 * (1 + r))
    (hfs : 1 + δ = Ps2 / Ps1 * (1 + r)) : P1 / Ps1 = P2 / Ps2 := by
  have h := uip_exact hP1 hPs1 hPs2 hf hfs
  have h1 : (P2 / Ps2) / (P1 / Ps1) = 1 := by
    have : (1 + δ) * ((P2 / Ps2) / (P1 / Ps1) - 1) = 0 := by linarith
    have := (mul_eq_zero.1 this).resolve_left (by linarith)
    linarith
  have hne : P1 / Ps1 ≠ 0 := (div_pos hP1 hPs1).ne'
  field_simp at h1
  field_simp
  linarith

/-! ## The MM schedule (58)–(61) -/

/-- **The MM schedule and no overshooting in the linear model** (O&R (58)–(60), pp. 677–678):
with `m̄ − m̄* = m − m*` (53), `ē = (m − m*) − (c − c*)` ((52) with (57)) and the date-1 money
differential (58) `m − m* − e = c − c* − (ē − e)/δ`, the exchange rate jumps at once to its
long-run level: `e = ē = (m − m*) − (c − c*)` (60). -/
theorem mm_no_overshooting {δ x dc e eb : ℝ} (hδ : 0 < δ) (h58 : x - e = dc - (eb - e) / δ)
    (h59 : eb = x - dc) : e = eb ∧ e = x - dc := by
  have h : (eb - e) * (1 + 1 / δ) = 0 := by
    rw [h59] at h58 ⊢
    field_simp at h58 ⊢
    linarith
  have := (mul_eq_zero.1 h).resolve_right (by positivity)
  constructor <;> linarith

/-- The iterated MM recursion (O&R (39), (61)): with `q = 1/(1+a)`,
`e_t = q^N e_{t+N} + Σ_{j<N} a q^{j+1} (x_{t+j} − k)`. -/
theorem mm_iterate {a k : ℝ} (ha : 0 < a) {x ez : ℕ → ℝ}
    (hrec : ∀ t, x t - ez t = k - (ez (t + 1) - ez t) / a) (t N : ℕ) :
    ez t = (1 + a)⁻¹ ^ N * ez (t + N) +
      ∑ j ∈ Finset.range N, a * (1 + a)⁻¹ ^ (j + 1) * (x (t + j) - k) := by
  have hstep : ∀ s, ez s = (1 + a)⁻¹ * ez (s + 1) + a * (1 + a)⁻¹ * (x s - k) := by
    intro s
    have h := hrec s
    have : (1 + a) ≠ 0 := by linarith
    field_simp at h ⊢
    linarith
  induction N with
  | zero => simp
  | succ N ih =>
    rw [ih, Finset.sum_range_succ, hstep (t + N), show t + (N + 1) = t + N + 1 by ring]
    ring

/-- **The forward solution (61) is the ONLY no-bubble solution** (O&R p. 678; T13): if
`x_t − e_t = k − (e_{t+1} − e_t)/a` for all `t` (eq. (39) with `x = m − m*`, `k = c − c*`
constant by (57), `a = δ`), the no-bubble condition `(1+a)^{−T} e_T → 0` holds and
`Σ (1+a)^{−s} |x_s| < ∞`, then `e_t = −k + (a/(1+a)) Σ_{j≥0} (1+a)^{−j} x_{t+j}`. -/
theorem forward_solution_unique {a k : ℝ} (ha : 0 < a) {x ez : ℕ → ℝ}
    (hrec : ∀ t, x t - ez t = k - (ez (t + 1) - ez t) / a)
    (hnb : Tendsto (fun T => (1 + a)⁻¹ ^ T * ez T) atTop (𝓝 0))
    (hx : Summable (fun s => (1 + a)⁻¹ ^ s * x s)) (t : ℕ) :
    ez t = -k + a / (1 + a) * ∑' j, (1 + a)⁻¹ ^ j * x (t + j) := by
  set q := (1 + a)⁻¹ with hq
  have hq0 : 0 < q := inv_pos.2 (by linarith)
  have hq1 : q < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hqa : q * (1 + a) = 1 := inv_mul_cancel₀ (by linarith)
  -- the shifted discounted sequence is summable
  have hxs : Summable (fun j => q ^ j * x (t + j)) := by
    have h1 := (summable_nat_add_iff t).2 hx
    have h2 := h1.mul_left ((1 + a) ^ t)
    refine h2.congr fun j => ?_
    simp only [hq]
    rw [add_comm j t, pow_add]
    have : (1 + a) ^ t * (1 + a)⁻¹ ^ t = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ (by linarith), one_pow]
    linear_combination (1 + a)⁻¹ ^ j * x (t + j) * this
  have hgeo : Summable (fun j : ℕ => q ^ j) := summable_geometric_of_lt_one hq0.le hq1
  -- the bubble term vanishes
  have hb : Tendsto (fun N => q ^ N * ez (t + N)) atTop (𝓝 0) := by
    have h1 := (tendsto_add_atTop_iff_nat t).2 hnb
    have h2 := h1.const_mul ((1 + a) ^ t)
    rw [mul_zero] at h2
    refine h2.congr fun N => ?_
    simp only [hq]
    rw [add_comm N t, pow_add]
    have : (1 + a) ^ t * (1 + a)⁻¹ ^ t = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ (by linarith), one_pow]
    linear_combination (1 + a)⁻¹ ^ N * ez (t + N) * this
  -- the finite sums converge
  have hs : Tendsto (fun N => ∑ j ∈ Finset.range N, a * q ^ (j + 1) * (x (t + j) - k)) atTop
      (𝓝 (a * q * ∑' j, q ^ j * x (t + j) - a * q * k * ∑' j : ℕ, q ^ j)) := by
    have h1 := (hxs.hasSum.mul_left (a * q)).tendsto_sum_nat
    have h2 := (hgeo.hasSum.mul_left (a * q * k)).tendsto_sum_nat
    refine (h1.sub h2).congr fun N => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hlim := hb.add hs
  rw [zero_add] at hlim
  have hconst : Tendsto (fun N => (1 + a)⁻¹ ^ N * ez (t + N) +
      ∑ j ∈ Finset.range N, a * (1 + a)⁻¹ ^ (j + 1) * (x (t + j) - k)) atTop (𝓝 (ez t)) := by
    refine tendsto_const_nhds.congr fun N => ?_
    exact mm_iterate ha hrec t N
  have heq := tendsto_nhds_unique hconst hlim
  rw [heq, tsum_geometric_of_lt_one hq0.le hq1]
  have e1 : a * q * k * (1 - q)⁻¹ = k := by
    have : 1 - q = a * q := by linarith
    rw [this]
    field_simp
  have e2 : a * q = a / (1 + a) := by rw [hq, div_eq_mul_inv]
  rw [e1, e2]
  ring

/-- **The forward solution (61) solves the MM recursion and has no bubble** (O&R p. 678; T13,
existence): `e_t = −k + (a/(1+a)) Σ_{j≥0} (1+a)^{−j} x_{t+j}` satisfies (39) at every date and
`(1+a)^{−T} e_T → 0`. -/
theorem forward_solution_exists {a k : ℝ} (ha : 0 < a) {x : ℕ → ℝ}
    (hx : Summable (fun s => (1 + a)⁻¹ ^ s * x s)) :
    let ez : ℕ → ℝ := fun t => -k + a / (1 + a) * ∑' j, (1 + a)⁻¹ ^ j * x (t + j)
    (∀ t, x t - ez t = k - (ez (t + 1) - ez t) / a) ∧
      Tendsto (fun T => (1 + a)⁻¹ ^ T * ez T) atTop (𝓝 0) := by
  intro ez
  set q := (1 + a)⁻¹ with hq
  have hq0 : 0 < q := inv_pos.2 (by linarith)
  have hq1 : q < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hqa : q * (1 + a) = 1 := inv_mul_cancel₀ (by linarith)
  have hxs : ∀ t, Summable (fun j => q ^ j * x (t + j)) := by
    intro t
    have h1 := (summable_nat_add_iff t).2 hx
    have h2 := h1.mul_left ((1 + a) ^ t)
    refine h2.congr fun j => ?_
    simp only [hq]
    rw [add_comm j t, pow_add]
    have : (1 + a) ^ t * (1 + a)⁻¹ ^ t = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ (by linarith), one_pow]
    linear_combination (1 + a)⁻¹ ^ j * x (t + j) * this
  -- the one-step split of the tail sums
  have hsplit : ∀ t, ∑' j, q ^ j * x (t + j) = x t + q * ∑' j, q ^ j * x (t + 1 + j) := by
    intro t
    rw [(hxs t).tsum_eq_zero_add]
    simp only [pow_zero, one_mul, add_zero]
    congr 1
    rw [← tsum_mul_left]
    refine tsum_congr fun j => ?_
    rw [pow_succ, show t + (j + 1) = t + 1 + j by ring]
    ring
  refine ⟨fun t => ?_, ?_⟩
  · simp only [ez]
    rw [hsplit t]
    have : (1 + a) ≠ 0 := by linarith
    have hq' : q = 1 / (1 + a) := by rw [hq, one_div]
    rw [hq']
    field_simp
    ring
  · -- `q^T e_T = −k q^T + (a/(1+a)) Σ_j q^{T+j} x_{T+j}`, a tail of a convergent series
    have htail : Tendsto (fun T : ℕ => ∑' j : ℕ, q ^ (j + T) * x (j + T)) atTop (𝓝 0) :=
      tendsto_sum_nat_add (fun s => q ^ s * x s)
    have hgeo : Tendsto (fun T : ℕ => q ^ T) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hq0.le hq1
    have h := (hgeo.const_mul (-k)).add (htail.const_mul (a / (1 + a)))
    rw [mul_zero, mul_zero, add_zero] at h
    refine h.congr fun T => ?_
    simp only [ez]
    have e : ∑' j : ℕ, q ^ (j + T) * x (j + T) = q ^ T * ∑' j, q ^ j * x (T + j) := by
      rw [← tsum_mul_left]
      refine tsum_congr fun j => ?_
      rw [pow_add, add_comm j T]
      ring
    rw [e]
    ring

/-- **(60) as a special case of (61)**: for a permanent differential `x_t = m − m*` for all `t`,
the forward solution is `e_t = (m − m*) − (c − c*)` at every date (O&R p. 678). -/
theorem forward_solution_const {a k X : ℝ} (ha : 0 < a) :
    -k + a / (1 + a) * ∑' j : ℕ, (1 + a)⁻¹ ^ j * X = X - k := by
  have hq0 : 0 < (1 + a)⁻¹ := inv_pos.2 (by linarith)
  have hq1 : (1 + a)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  rw [tsum_mul_right, tsum_geometric_of_lt_one hq0.le hq1]
  have : (1 + a) ≠ 0 := by linarith
  have : 1 - (1 + a)⁻¹ = a / (1 + a) := by field_simp; ring
  rw [this]
  field_simp
  ring

/-! ## The GG schedule (62)–(64) -/

/-- **The GG schedule (64)**, O&R p. 679 (T14): from the short-run current accounts (62)
`b̄/(1−n) = (y − y*) − (c − c*) − e`, the output differential (63) `y − y* = θe`, the long-run
consumption differential (45) and (57), `e = [δ(1+θ) + 2θ](c − c*)/(δ(θ² − 1))`. -/
theorem gg_schedule {θ δ n y ys c cs e b cb cbs : ℝ} (hθ : 1 < θ) (hδ : 0 < δ) (hn1 : n < 1)
    (h63 : y - ys = θ * e) (h62 : b / (1 - n) = (y - ys) - (c - cs) - e)
    (h45 : cb - cbs = (1 + θ) * δ * b / (2 * θ * (1 - n))) (h57 : cb - cbs = c - cs) :
    e = (δ * (1 + θ) + 2 * θ) * (c - cs) / (δ * (θ ^ 2 - 1)) := by
  have hn : 1 - n ≠ 0 := by linarith
  have hθ0 : θ ≠ 0 := by linarith
  have hsq : θ ^ 2 - 1 ≠ 0 := by nlinarith
  have hb : b / (1 - n) = 2 * θ * (c - cs) / ((1 + θ) * δ) := by
    rw [← h57, h45]; field_simp
  rw [hb, h63] at h62
  have h1 : (1 + θ) * δ ≠ 0 := by positivity
  field_simp at h62 ⊢
  nlinarith [h62]

/-! ## The full money-shock system and its unique solution (65)–(74) (T14, T15) -/

/-- The short-run (date 1) unknowns of O&R §10.1.7 (pp. 675–683): `c, c*, y, y*, p, p*, e`,
world consumption `cᵂ`, the real interest rate `r` (between dates 1 and 2, in `dr/r̄` units) and
the current account `b̄` (which becomes the long-run net foreign asset position). -/
structure ShortVars where
  c : ℝ
  cs : ℝ
  y : ℝ
  ys : ℝ
  p : ℝ
  ps : ℝ
  e : ℝ
  cW : ℝ
  r : ℝ
  b : ℝ

/-- **The money-shock system**, O&R pp. 675–683: preset `p(h) = p*(f) = 0` in (27)–(28), world
demand (30)–(31), (32), the Euler equations (35)–(36) linking date 1 to the long run, the date-1
money demands (37)–(38) with date-2 prices at their long-run values, the current account (55),
and the long-run system (`SteadyLinear`) at `b̄` with a permanent shock `m̄ = m`, `m̄* = m*`
(53). The labour–leisure conditions (33)–(34) do not bind in the short run (p. 675). -/
structure MoneyShockEqm (L : ReduxLinear) (m ms : ℝ) (u : ShortVars) (v : SteadyVars) : Prop where
  eq27 : u.p = L.n * 0 + (1 - L.n) * (u.e + 0)
  eq28 : u.ps = L.n * (0 - u.e) + (1 - L.n) * 0
  eq30 : u.y = L.θ * (u.p - 0) + u.cW
  eq31 : u.ys = L.θ * (u.ps - 0) + u.cW
  eq32 : u.cW = L.n * u.c + (1 - L.n) * u.cs
  eq35 : v.c = u.c + L.δ / (1 + L.δ) * u.r
  eq36 : v.cs = u.cs + L.δ / (1 + L.δ) * u.r
  eq37 : m - u.p = u.c - u.r / (1 + L.δ) - (v.p - u.p) / L.δ
  eq38 : ms - u.ps = u.cs - u.r / (1 + L.δ) - (v.ps - u.ps) / L.δ
  eq55 : u.b = u.y - u.c - (1 - L.n) * u.e
  longrun : SteadyLinear L u.b m ms v

/-- The closed-form short-run solution, O&R (65)–(67), (70)–(74), pp. 681–683, with
`mᵂ = n m + (1−n) m*`. -/
noncomputable def shortRunSolution (L : ReduxLinear) (m ms : ℝ) : ShortVars where
  e := (L.δ * (1 + L.θ) + 2 * L.θ) * (m - ms) / L.D
  c := L.n * m + (1 - L.n) * ms + (1 - L.n) * (L.δ * (L.θ ^ 2 - 1) * (m - ms) / L.D)
  cs := L.n * m + (1 - L.n) * ms - L.n * (L.δ * (L.θ ^ 2 - 1) * (m - ms) / L.D)
  y := L.n * m + (1 - L.n) * ms +
    (1 - L.n) * L.θ * ((L.δ * (1 + L.θ) + 2 * L.θ) * (m - ms) / L.D)
  ys := L.n * m + (1 - L.n) * ms - L.n * L.θ * ((L.δ * (1 + L.θ) + 2 * L.θ) * (m - ms) / L.D)
  p := (1 - L.n) * ((L.δ * (1 + L.θ) + 2 * L.θ) * (m - ms) / L.D)
  ps := -(L.n * ((L.δ * (1 + L.θ) + 2 * L.θ) * (m - ms) / L.D))
  cW := L.n * m + (1 - L.n) * ms
  r := -((1 + L.δ) / L.δ) * (L.n * m + (1 - L.n) * ms)
  b := 2 * (1 - L.n) * (L.θ - 1) * (m - ms) / L.E

/-- The key short-run relations of any solution (used for `moneyShock_iff`): `m − p = c`,
`m* − p* = c*` (the MM relations with `î = 0`), `cᵂ = −δr/(1+δ)` (70) and the long-run
consumption differential (45) with (57). -/
theorem MoneyShockEqm.relations {L : ReduxLinear} {m ms : ℝ} {u : ShortVars}
    {v : SteadyVars} (h : MoneyShockEqm L m ms u v) :
    m - u.p = u.c ∧ ms - u.ps = u.cs ∧ u.cW = -(L.δ / (1 + L.δ) * u.r) ∧
      u.c - u.cs = (1 + L.θ) * L.δ * u.b / (2 * L.θ * (1 - L.n)) := by
  have hδ := L.hδ
  have hδ1 : (1 + L.δ) ≠ 0 := by linarith
  obtain ⟨hdiff, -, -, hcW, -⟩ := steadyLinear_consequences h.longrun
  have h50 := h.longrun.eq50
  have h51 := h.longrun.eq51
  have h35 := h.eq35
  have h36 := h.eq36
  have hmp : m - u.p = u.c := by
    have h37 := h.eq37
    rw [h50, h35] at h37
    have : (m - u.p - u.c) * (1 + 1 / L.δ) = 0 := by
      have e : (m - u.p - u.c) * (1 + 1 / L.δ) = (m - u.p) - (u.c - u.r / (1 + L.δ) -
          (m - (u.c + L.δ / (1 + L.δ) * u.r) - u.p) / L.δ) := by field_simp; ring
      rw [e]; linarith
    have := (mul_eq_zero.1 this).resolve_right (by positivity)
    linarith
  have hmps : ms - u.ps = u.cs := by
    have h38 := h.eq38
    rw [h51, h36] at h38
    have : (ms - u.ps - u.cs) * (1 + 1 / L.δ) = 0 := by
      have e : (ms - u.ps - u.cs) * (1 + 1 / L.δ) = (ms - u.ps) - (u.cs - u.r / (1 + L.δ) -
          (ms - (u.cs + L.δ / (1 + L.δ) * u.r) - u.ps) / L.δ) := by field_simp; ring
      rw [e]; linarith
    have := (mul_eq_zero.1 this).resolve_right (by positivity)
    linarith
  refine ⟨hmp, hmps, ?_, ?_⟩
  · have hw : L.n * v.c + (1 - L.n) * v.cs = 0 := by
      rw [← h.longrun.eq32]; exact hcW
    rw [h35, h36] at hw
    rw [h.eq32]
    linarith
  · rw [← hdiff, h35, h36]
    ring

/-- **The money-shock system has exactly one solution** (T14, T15; O&R (60)–(74), pp. 678–683):
`MoneyShockEqm` holds IF AND ONLY IF the short-run variables are `shortRunSolution` and the
long-run variables are `steadySolution` at the implied `b̄`. -/
theorem moneyShock_iff (L : ReduxLinear) (m ms : ℝ) (u : ShortVars) (v : SteadyVars) :
    MoneyShockEqm L m ms u v ↔
      u = shortRunSolution L m ms ∧ v = steadySolution L (shortRunSolution L m ms).b m ms := by
  have hθ := L.hθ
  have hθ0 : L.θ ≠ 0 := by linarith
  have hδ := L.hδ
  have hn1 : 1 - L.n ≠ 0 := by linarith [L.hn1]
  have hD := L.D_pos.ne'
  have hE := L.E_pos.ne'
  have hδ1 : (1 + L.δ) ≠ 0 := by linarith
  constructor
  · intro h
    obtain ⟨hmp, hmps, hcW, hdc⟩ := h.relations
    have h27 := h.eq27
    have h28 := h.eq28
    have h30 := h.eq30
    have h31 := h.eq31
    have h32 := h.eq32
    have h55 := h.eq55
    have hv := (steadyLinear_iff L u.b m ms v).1 h.longrun
    rcases u with ⟨c, cs, y, ys, p, ps, e, cW, r, b⟩
    simp only at hmp hmps hcW hdc h27 h28 h30 h31 h32 h55 hv ⊢
    have hp : p = (1 - L.n) * e := by linarith
    have hps : ps = -(L.n * e) := by linarith
    -- world aggregates (72)–(73)
    have hcW' : cW = L.n * m + (1 - L.n) * ms := by
      rw [h32]; rw [hp] at hmp; rw [hps] at hmps; linear_combination -L.n * hmp - (1 - L.n) * hmps
    have hr : r = -((1 + L.δ) / L.δ) * (L.n * m + (1 - L.n) * ms) := by
      rw [hcW'] at hcW
      field_simp at hcW ⊢
      linarith
    -- MM (60) and GG (64)
    have hMM : e = (m - ms) - (c - cs) := by rw [hp] at hmp; rw [hps] at hmps; linarith
    have hca : b = (1 - L.n) * ((L.θ - 1) * e - (c - cs)) := by
      linear_combination h55 + h30 + L.θ * hp + h32
    have hdc' : c - cs = L.δ * (L.θ ^ 2 - 1) * (m - ms) / L.D := by
      rw [hca, hMM] at hdc
      have key : (c - cs) * L.D = L.δ * (L.θ ^ 2 - 1) * (m - ms) := by
        unfold ReduxLinear.D
        field_simp at hdc
        linear_combination hdc
      field_simp
      linarith
    have he : e = (L.δ * (1 + L.θ) + 2 * L.θ) * (m - ms) / L.D := by
      rw [hMM, hdc']
      unfold ReduxLinear.D
      field_simp
      ring
    have hb : b = 2 * (1 - L.n) * (L.θ - 1) * (m - ms) / L.E := by
      rw [hca, he, hdc']
      unfold ReduxLinear.D ReduxLinear.E
      field_simp
      ring
    have hc : c = L.n * m + (1 - L.n) * ms +
        (1 - L.n) * (L.δ * (L.θ ^ 2 - 1) * (m - ms) / L.D) := by
      rw [← hcW', ← hdc', h32]; ring
    have hcs : cs = L.n * m + (1 - L.n) * ms - L.n * (L.δ * (L.θ ^ 2 - 1) * (m - ms) / L.D) := by
      rw [← hcW', ← hdc', h32]; ring
    refine ⟨?_, ?_⟩
    · simp only [shortRunSolution, ShortVars.mk.injEq]
      refine ⟨hc, hcs, ?_, ?_, ?_, ?_, he, hcW', hr, hb⟩
      · rw [h30, hp, hcW', he]; ring
      · rw [h31, hps, hcW', he]; ring
      · rw [hp, he]
      · rw [hps, he]
    · rw [hv, hb]; rfl
  · rintro ⟨rfl, rfl⟩
    have hE' : L.δ * (1 + L.θ) + 2 ≠ 0 := L.E_pos.ne'
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, (steadyLinear_iff L _ m ms _).2 rfl⟩ <;>
      simp only [steadySolution, shortRunSolution, ReduxLinear.D, ReduxLinear.E] <;>
      field_simp <;> ring

/-- **Existence and uniqueness of the money-shock equilibrium** (T14): for every `m, m*`. -/
theorem moneyShock_existsUnique (L : ReduxLinear) (m ms : ℝ) :
    ∃! w : ShortVars × SteadyVars, MoneyShockEqm L m ms w.1 w.2 := by
  refine ⟨(shortRunSolution L m ms, steadySolution L (shortRunSolution L m ms).b m ms),
    (moneyShock_iff L m ms _ _).2 ⟨rfl, rfl⟩, fun w hw => ?_⟩
  obtain ⟨h1, h2⟩ := (moneyShock_iff L m ms w.1 w.2).1 hw
  exact Prod.ext h1 h2

/-- **The closed forms (65)–(68)**, O&R p. 681 (T14): any solution has
`e = [δ(1+θ)+2θ](m−m*)/(θδ(1+θ)+2θ)` (65), `c − c* = δ(θ²−1)(m−m*)/(θδ(1+θ)+2θ)` (66),
`b̄ = 2(1−n)(θ−1)(m−m*)/(δ(1+θ)+2)` (67), `p̄(h) − ē − p̄*(f) = δ(θ−1)(m−m*)/(θδ(1+θ)+2θ)` (68),
and the exchange rate jumps to its long-run level, `e = ē` (60). -/
theorem moneyShock_closed_forms {L : ReduxLinear} {m ms : ℝ} {u : ShortVars} {v : SteadyVars}
    (h : MoneyShockEqm L m ms u v) :
    u.e = (L.δ * (1 + L.θ) + 2 * L.θ) * (m - ms) / L.D ∧
    u.c - u.cs = L.δ * (L.θ ^ 2 - 1) * (m - ms) / L.D ∧
    u.b = 2 * (1 - L.n) * (L.θ - 1) * (m - ms) / L.E ∧
    v.ph - v.e - v.pf = L.δ * (L.θ - 1) * (m - ms) / L.D ∧ u.e = v.e := by
  obtain ⟨rfl, rfl⟩ := (moneyShock_iff L m ms u v).1 h
  have hθ0 : L.θ ≠ 0 := by linarith [L.hθ]
  have hn1 : 1 - L.n ≠ 0 := by linarith [L.hn1]
  have hE' : L.δ * (1 + L.θ) + 2 ≠ 0 := L.E_pos.ne'
  simp only [steadySolution, shortRunSolution, ReduxLinear.D, ReduxLinear.E]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> (try trivial) <;> field_simp <;> ring

/-- **World aggregates (69)–(74)**, O&R pp. 682–683 (T15): `cᵂ = −δr/(1+δ)` (70),
`cᵂ = mᵂ = yᵂ` (72), `r = −((1+δ)/δ)mᵂ` (73), `y = mᵂ + (1−n)θe`, and (74)
`y = [δ(1+θ) + 2(n(1−θ)+θ)]m/(δ(1+θ)+2) + 2(1−n)(1−θ)m*/(δ(1+θ)+2)`. -/
theorem moneyShock_world {L : ReduxLinear} {m ms : ℝ} {u : ShortVars} {v : SteadyVars}
    (h : MoneyShockEqm L m ms u v) :
    u.cW = -(L.δ / (1 + L.δ) * u.r) ∧ u.cW = L.n * m + (1 - L.n) * ms ∧
    L.n * u.y + (1 - L.n) * u.ys = u.cW ∧
    u.r = -((1 + L.δ) / L.δ) * (L.n * m + (1 - L.n) * ms) ∧
    u.y = L.n * m + (1 - L.n) * ms + (1 - L.n) * L.θ * u.e ∧
    u.y = (L.δ * (1 + L.θ) + 2 * (L.n * (1 - L.θ) + L.θ)) / L.E * m +
      2 * (1 - L.n) * (1 - L.θ) / L.E * ms := by
  have hcW := h.relations.2.2.1
  obtain ⟨rfl, rfl⟩ := (moneyShock_iff L m ms u v).1 h
  have hθ0 : L.θ ≠ 0 := by linarith [L.hθ]
  have hE' : L.δ * (1 + L.θ) + 2 ≠ 0 := L.E_pos.ne'
  refine ⟨hcW, rfl, ?_, rfl, ?_, ?_⟩ <;>
    simp only [shortRunSolution, ReduxLinear.D, ReduxLinear.E] <;> field_simp <;> ring

/-- **(74): a Foreign monetary expansion lowers Home output**, O&R p. 683: the coefficient on
`m*` in (74) is `2(1−n)(1−θ)/(δ(1+θ)+2) < 0` for `θ > 1`. -/
theorem foreign_money_lowers_home_output (L : ReduxLinear) :
    2 * (1 - L.n) * (1 - L.θ) / L.E < 0 := by
  have := L.E_pos
  have h1 : 0 < 1 - L.n := by linarith [L.hn1]
  have h2 : 1 - L.θ < 0 := by linarith [L.hθ]
  apply div_neg_of_neg_of_pos _ this
  nlinarith

/-! ## Comparative statics (T14), the (65) sign condition and country size (p. 688) -/

/-- The exchange-rate response per unit of relative money, `e/(m − m*)` in (65), O&R p. 681. -/
noncomputable def exchangeRateCoef (θ δ : ℝ) : ℝ :=
  (δ * (1 + θ) + 2 * θ) / (θ * (δ * (1 + θ) + 2))

/-- **At `θ = 1` the exchange rate moves one-for-one** (O&R p. 681). -/
theorem exchangeRateCoef_one {δ : ℝ} (hδ : 0 < δ) : exchangeRateCoef 1 δ = 1 := by
  unfold exchangeRateCoef
  have : δ * (1 + 1) + 2 ≠ 0 := by positivity
  field_simp

/-- **(65): the currency depreciates less than proportionally**, O&R p. 681 (T14): for `θ > 1`,
`0 < e/(m − m*) < 1`. -/
theorem exchangeRateCoef_mem {θ δ : ℝ} (hθ : 1 < θ) (hδ : 0 < δ) :
    0 < exchangeRateCoef θ δ ∧ exchangeRateCoef θ δ < 1 := by
  unfold exchangeRateCoef
  have hden : 0 < θ * (δ * (1 + θ) + 2) := by
    have : 0 < θ := by linarith
    positivity
  constructor
  · exact div_pos (by nlinarith) hden
  · rw [div_lt_one hden]
    have : 0 < (θ - 1) * (δ * (1 + θ)) := mul_pos (by linarith) (by positivity)
    nlinarith

/-- **The exchange-rate response falls as goods become closer substitutes**, O&R p. 680 (T14):
`e/(m − m*)` is strictly decreasing in `θ > 0`. -/
theorem exchangeRateCoef_strictAntiOn {δ : ℝ} (hδ : 0 < δ) :
    StrictAntiOn (fun θ => exchangeRateCoef θ δ) (Set.Ioi 0) := by
  intro a ha b hb hab
  simp only [exchangeRateCoef]
  have ha0 : (0 : ℝ) < a := ha
  have hb0 : (0 : ℝ) < b := hb
  have hda : 0 < a * (δ * (1 + a) + 2) := by positivity
  have hdb : 0 < b * (δ * (1 + b) + 2) := by positivity
  rw [div_lt_div_iff₀ hdb hda]
  have key : (δ * (1 + a) + 2 * a) * (b * (δ * (1 + b) + 2)) -
      (δ * (1 + b) + 2 * b) * (a * (δ * (1 + a) + 2)) =
      (b - a) * (δ ^ 2 * (a + b) + δ * (δ + 2) + (δ + 2) * δ * a * b) := by ring
  have hpos : 0 < (b - a) * (δ ^ 2 * (a + b) + δ * (δ + 2) + (δ + 2) * δ * a * b) := by
    apply mul_pos (by linarith); positivity
  linarith

/-- **As `θ → ∞` the exchange-rate response vanishes**, O&R p. 680 (T14). -/
theorem exchangeRateCoef_tendsto {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun θ => exchangeRateCoef θ δ) atTop (𝓝 0) := by
  have h1 : Tendsto (fun θ : ℝ => δ * θ⁻¹ + (δ + 2)) atTop (𝓝 (δ * 0 + (δ + 2))) :=
    (tendsto_inv_atTop_zero.const_mul δ).add_const _
  have h2 : Tendsto (fun θ : ℝ => (δ * (1 + θ) + 2)⁻¹) atTop (𝓝 0) := by
    apply tendsto_inv_atTop_zero.comp
    exact tendsto_atTop_add_const_right _ _ ((tendsto_id.const_mul_atTop hδ).atTop_add
      tendsto_const_nhds |>.congr (fun θ => by simp; ring))
  have h := h1.mul h2
  rw [mul_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with θ hθ
  unfold exchangeRateCoef
  have : δ * (1 + θ) + 2 ≠ 0 := by positivity
  field_simp
  ring

/-- **The GG schedule becomes horizontal as `θ → ∞`**, O&R p. 680 (T14): its slope
`[δ(1+θ)+2θ]/(δ(θ²−1))` tends to `0`. -/
theorem gg_slope_tendsto {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun θ : ℝ => (δ * (1 + θ) + 2 * θ) / (δ * (θ ^ 2 - 1))) atTop (𝓝 0) := by
  have hinv : Tendsto (fun θ : ℝ => θ⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hup : Tendsto (fun θ : ℝ => 4 / (3 * δ) * (δ * θ⁻¹ * θ⁻¹ + (δ + 2) * θ⁻¹)) atTop
      (𝓝 (4 / (3 * δ) * (δ * 0 * 0 + (δ + 2) * 0))) :=
    (((hinv.const_mul δ).mul hinv).add (hinv.const_mul (δ + 2))).const_mul _
  simp only [mul_zero, add_zero] at hup
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [eventually_gt_atTop 2] with θ hθ
    have hθ0 : 0 < θ := by linarith
    have hsq : 0 < θ ^ 2 - 1 := by nlinarith
    exact div_nonneg (by positivity) (mul_pos hδ hsq).le
  · filter_upwards [eventually_gt_atTop 2] with θ hθ
    have hθ0 : 0 < θ := by linarith
    have hsq : 0 < θ ^ 2 - 1 := by nlinarith
    have hden : 0 < δ * (θ ^ 2 - 1) := mul_pos hδ hsq
    rw [div_le_iff₀ hden]
    have e : 4 / (3 * δ) * (δ * θ⁻¹ * θ⁻¹ + (δ + 2) * θ⁻¹) * (δ * (θ ^ 2 - 1)) =
        4 / 3 * (δ + (δ + 2) * θ) * (θ ^ 2 - 1) / θ ^ 2 := by field_simp
    rw [e, le_div_iff₀ (by positivity)]
    have hN : 0 < δ + (δ + 2) * θ := by positivity
    have h4 : 0 < θ ^ 2 - 4 := by nlinarith
    have e2 : δ * (1 + θ) + 2 * θ = δ + (δ + 2) * θ := by ring
    rw [e2]
    nlinarith [mul_pos hN h4]

/-- **(65) corrected: the sign condition** (O&R p. 681 writes `e < m − m*` "because `θ > 1`"; this
needs `m − m* > 0`): for `θ > 1`, with `e` given by (65), `e < m − m* ⟺ m − m* > 0`, and
`|e| < |m − m*|` whenever `m ≠ m*`. -/
theorem eq65_sign {θ δ X : ℝ} (hθ : 1 < θ) (hδ : 0 < δ) :
    (exchangeRateCoef θ δ * X < X ↔ 0 < X) ∧ (X ≠ 0 → |exchangeRateCoef θ δ * X| < |X|) := by
  obtain ⟨h0, h1⟩ := exchangeRateCoef_mem hθ hδ
  refine ⟨⟨fun h => by nlinarith, fun h => by nlinarith⟩, fun hX => ?_⟩
  rw [abs_mul, abs_of_pos h0]
  have := abs_pos.2 hX
  nlinarith

/-- **The short-run terms-of-trade effect dominates**, O&R p. 682 (T14): the long-run effect (68)
is `δ(θ−1)/(δ(1+θ)+2θ)` times the short-run effect `e` (65) in absolute value; this ratio lies in
`[0, 1)` and is below `δ/2`, i.e. of the order of the interest rate. -/
theorem tot_ratio_bounds {θ δ : ℝ} (hθ : 1 ≤ θ) (hδ : 0 < δ) :
    0 ≤ δ * (θ - 1) / (δ * (1 + θ) + 2 * θ) ∧ δ * (θ - 1) / (δ * (1 + θ) + 2 * θ) < 1 ∧
      δ * (θ - 1) / (δ * (1 + θ) + 2 * θ) < δ / 2 := by
  have hden : 0 < δ * (1 + θ) + 2 * θ := by nlinarith
  refine ⟨div_nonneg (by nlinarith) hden.le, by rw [div_lt_one hden]; nlinarith, ?_⟩
  rw [div_lt_iff₀ hden]
  nlinarith [mul_pos hδ (show 0 < δ * (1 + θ) + 2 by positivity)]

/-- **The larger the country, the smaller the current-account effect** (O&R p. 681): for
`m > m*` and `θ > 1`, `b̄ = 2(1−n)(θ−1)(m−m*)/(δ(1+θ)+2)` is strictly decreasing in `n`. -/
theorem ca_strictAnti_in_n {θ δ X : ℝ} (hθ : 1 < θ) (hδ : 0 < δ) (hX : 0 < X) :
    StrictAnti (fun n : ℝ => 2 * (1 - n) * (θ - 1) * X / (δ * (1 + θ) + 2)) := by
  intro a b hab
  have hE : 0 < δ * (1 + θ) + 2 := by positivity
  apply div_lt_div_of_pos_right _ hE
  have : 0 < (θ - 1) * X := mul_pos (by linarith) hX
  nlinarith

/-- **p. 688 corrected** (T14/T22): contrary to "country size `n` did not enter into the results
… for … the current account", the current account (67) depends on `n` (`ca_strictAnti_in_n`);
the size-free object is the per-capita differential `b̄ − b̄* = b̄/(1−n) = 2(θ−1)(m−m*)/E`. The
exchange rate (65), relative consumption (66) and the terms of trade (68) are indeed
independent of `n`: they coincide for any two size parameters. -/
theorem country_size_correction (L L' : ReduxLinear) (hθ : L.θ = L'.θ) (hδ : L.δ = L'.δ)
    (m ms : ℝ) :
    (shortRunSolution L m ms).e = (shortRunSolution L' m ms).e ∧
    (shortRunSolution L m ms).c - (shortRunSolution L m ms).cs =
      (shortRunSolution L' m ms).c - (shortRunSolution L' m ms).cs ∧
    (shortRunSolution L m ms).b / (1 - L.n) = (shortRunSolution L' m ms).b / (1 - L'.n) ∧
    (L.n ≠ L'.n → m ≠ ms → (shortRunSolution L m ms).b ≠ (shortRunSolution L' m ms).b) := by
  have hn1 : 1 - L.n ≠ 0 := by linarith [L.hn1]
  have hn1' : 1 - L'.n ≠ 0 := by linarith [L'.hn1]
  have hE : L.E = L'.E := by unfold ReduxLinear.E; rw [hθ, hδ]
  have hD : L.D = L'.D := by unfold ReduxLinear.D; rw [hθ, hδ]
  have hE0 := L.E_pos.ne'
  refine ⟨by simp only [shortRunSolution]; rw [hθ, hδ, hD], ?_, ?_, fun hn hm => ?_⟩
  · simp only [shortRunSolution]; rw [hθ, hδ, hD]; ring
  · simp only [shortRunSolution]; rw [hθ, hE]; field_simp
  · intro heq
    have hdiff : (shortRunSolution L m ms).b - (shortRunSolution L' m ms).b =
        2 * (L'.θ - 1) * (m - ms) * (L'.n - L.n) / L'.E := by
      simp only [shortRunSolution]; rw [hθ, hE]; ring
    rw [heq, sub_self] at hdiff
    have hE0' := L'.E_pos.ne'
    have hθ1 : L'.θ - 1 ≠ 0 := by linarith [L'.hθ]
    have hX : m - ms ≠ 0 := sub_ne_zero.2 hm
    have hnn : L'.n - L.n ≠ 0 := sub_ne_zero.2 (Ne.symm hn)
    have : 2 * (L'.θ - 1) * (m - ms) * (L'.n - L.n) / L'.E ≠ 0 := by positivity
    exact this hdiff.symm

/-! ## The nominal interest rate is unchanged (T15) -/

/-- The log-deviation of the gross nominal rate (O&R p. 665 Fisher relation, T15): along
`P_{t+1}/P_t = e^{τ Δp}` and `r = δ(1 + τ r̂)`, `d log(1 + i) = Δp + δ r̂/(1+δ)` at `τ = 0`. This
is the `î` of `nominal_rate_unchanged`. -/
theorem linearise_nominal_rate {δ dp rh : ℝ} (hδ : 0 < δ) :
    HasDerivAt (fun τ => Real.log (Real.exp (τ * dp) * (1 + δ * (1 + τ * rh))))
      (dp + δ * rh / (1 + δ)) 0 := by
  have h1 : HasDerivAt (fun τ => 1 + δ * (1 + τ * rh)) (δ * rh) 0 := by
    have := (((hasDerivAt_id (0 : ℝ)).mul_const rh).const_add 1).const_mul δ
    simpa using this.const_add 1
  have h2 := h1.log (by simp; linarith)
  have e : (fun τ => Real.log (Real.exp (τ * dp) * (1 + δ * (1 + τ * rh)))) =ᶠ[𝓝 0]
      fun τ => τ * dp + Real.log (1 + δ * (1 + τ * rh)) := by
    have hev : ∀ᶠ τ in 𝓝 (0 : ℝ), 0 < 1 + δ * (1 + τ * rh) :=
      h1.continuousAt.eventually (lt_mem_nhds (by simp; linarith))
    filter_upwards [hev] with τ hτ
    rw [Real.log_mul (Real.exp_pos _).ne' hτ.ne', Real.log_exp]
  have h3 := ((hasDerivAt_id (0 : ℝ)).mul_const dp).add h2
  have h4 := h3.congr_of_eventuallyEq e
  convert h4 using 1
  simp

/-- **The nominal interest rate does not change after a permanent shock** (T15; new): in each
country, the Euler equation (35) `c̄ = c + δr/(1+δ)`, date-1 money demand (37) and long-run money
demand `m − p̄ = c̄` ((50) with `m̄ = m`) imply `î = δr/(1+δ) + (p̄ − p) = 0`. The argument uses
nothing about the source of the shock, so it covers p. 699 ("the nominal interest rate doesn't
change") for productivity and government-spending shocks too. -/
theorem nominal_rate_unchanged {δ m p pb c cb r : ℝ} (hδ : 0 < δ)
    (h35 : cb = c + δ / (1 + δ) * r) (h37 : m - p = c - r / (1 + δ) - (pb - p) / δ)
    (h50 : pb = m - cb) : δ * r / (1 + δ) + (pb - p) = 0 := by
  have hδ1 : (1 + δ) ≠ 0 := by linarith
  have key : (δ * r / (1 + δ) + (pb - p)) * (1 + 1 / δ) = 0 := by
    have e : (δ * r / (1 + δ) + (pb - p)) * (1 + 1 / δ) =
        (m - p) - (c - r / (1 + δ) - (pb - p) / δ) + (δ / (1 + δ) * r + c - cb) +
        (pb - (m - cb)) := by field_simp; ring
    rw [e]
    linarith
  have := (mul_eq_zero.1 key).resolve_right (by positivity)
  exact this

/-! ## Temporary money shocks (fn 16, T16) -/

/-- Solving MM (forward form) and GG together: if `e = (x_eff) − (c − c*)` and
`e = G (c − c*)` with `G = [δ(1+θ)+2θ]/(δ(θ²−1))`, then `c − c* = δ(θ²−1) x_eff/D` and
`e = [δ(1+θ)+2θ] x_eff/D` (O&R (65)–(66), fn 16, Ex. 1). -/
theorem solve_mm_gg (L : ReduxLinear) {xe dc e : ℝ} (hmm : e = xe - dc)
    (hgg : e = (L.δ * (1 + L.θ) + 2 * L.θ) * dc / (L.δ * (L.θ ^ 2 - 1))) :
    dc = L.δ * (L.θ ^ 2 - 1) * xe / L.D ∧ e = (L.δ * (1 + L.θ) + 2 * L.θ) * xe / L.D := by
  have hθ := L.hθ
  have hδ := L.hδ
  have hsq : L.δ * (L.θ ^ 2 - 1) ≠ 0 := by
    have : 0 < L.θ ^ 2 - 1 := by nlinarith
    positivity
  have hD := L.D_pos.ne'
  have h2 : (xe - dc) * (L.δ * (L.θ ^ 2 - 1)) = (L.δ * (1 + L.θ) + 2 * L.θ) * dc := by
    rw [hmm] at hgg; rw [hgg]
    have : L.θ ^ 2 - 1 ≠ 0 := by nlinarith
    have := hδ.ne'
    field_simp
  have key : dc * L.D = L.δ * (L.θ ^ 2 - 1) * xe := by
    unfold ReduxLinear.D
    linear_combination -h2
  have hdc : dc = L.δ * (L.θ ^ 2 - 1) * xe / L.D := by field_simp; linarith
  refine ⟨hdc, ?_⟩
  rw [hmm, hdc]
  unfold ReduxLinear.D
  have : L.θ * (L.δ * (1 + L.θ) + 2) ≠ 0 := by
    have : 0 < L.θ := by linarith
    positivity
  field_simp
  ring

/-- **Temporary money shocks** (O&R fn 16, p. 681; T16): with a one-period Home expansion
`m₁ = m`, `m_s = 0` for `s ≥ 2`, `m* ≡ 0`, the forward MM equation (39) with no bubbles and the
unchanged GG schedule give `e₁ = (δ/(1+δ))[δ(1+θ)+2θ]m/D` and
`c − c* = (δ/(1+δ))δ(θ²−1)m/D`: the permanent-shock effects scaled by `δ/(1+δ) < 1`. From date 2
on the exchange rate is `e_t = −(c − c*)`. (Book date `t` is index `t − 1` here.) -/
theorem temporary_shock (L : ReduxLinear) {m dc : ℝ} {x ez : ℕ → ℝ} (hx0 : x 0 = m)
    (hxs : ∀ t, x (t + 1) = 0) (hrec : ∀ t, x t - ez t = dc - (ez (t + 1) - ez t) / L.δ)
    (hnb : Tendsto (fun T => (1 + L.δ)⁻¹ ^ T * ez T) atTop (𝓝 0))
    (hgg : ez 0 = (L.δ * (1 + L.θ) + 2 * L.θ) * dc / (L.δ * (L.θ ^ 2 - 1))) :
    ez 0 = L.δ / (1 + L.δ) * ((L.δ * (1 + L.θ) + 2 * L.θ) * m / L.D) ∧
    dc = L.δ / (1 + L.δ) * (L.δ * (L.θ ^ 2 - 1) * m / L.D) ∧ ∀ t, ez (t + 1) = -dc := by
  have hδ := L.hδ
  have hsum : Summable (fun s => (1 + L.δ)⁻¹ ^ s * x s) := by
    refine summable_of_ne_finset_zero (s := {0}) fun s hs => ?_
    simp only [Finset.mem_singleton] at hs
    obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hs
    rw [hxs t, mul_zero]
  have h0 := forward_solution_unique hδ hrec hnb hsum 0
  have hs0 : ∑' j, (1 + L.δ)⁻¹ ^ j * x (0 + j) = m := by
    rw [tsum_eq_single 0 (fun j hj => by
      obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
      rw [zero_add, hxs t, mul_zero])]
    simp [hx0]
  rw [hs0] at h0
  have hlater : ∀ t, ez (t + 1) = -dc := by
    intro t
    have h := forward_solution_unique hδ hrec hnb hsum (t + 1)
    have : ∑' j, (1 + L.δ)⁻¹ ^ j * x (t + 1 + j) = 0 := by
      have : ∀ j, (1 + L.δ)⁻¹ ^ j * x (t + 1 + j) = 0 := fun j => by
        rw [show t + 1 + j = (t + j) + 1 by ring, hxs, mul_zero]
      rw [tsum_congr this, tsum_zero]
    rw [this, mul_zero, add_zero] at h
    exact h
  obtain ⟨hdc, he⟩ := solve_mm_gg L (xe := L.δ / (1 + L.δ) * m) (by linarith) hgg
  refine ⟨?_, ?_, hlater⟩
  · rw [he]; ring
  · rw [hdc]; ring

/-- **After a temporary Home expansion the Home currency is PERMANENTLY APPRECIATED** (T16; not
stated in the book): in the setting of `temporary_shock`, for `m > 0` and `θ > 1`, the exchange
rate from date 2 on is `e_t = −(c − c*) < 0`, while on impact it depreciates, `e₁ > 0`. -/
theorem temporary_shock_appreciation (L : ReduxLinear) {m dc : ℝ} {x ez : ℕ → ℝ} (hm : 0 < m)
    (hx0 : x 0 = m) (hxs : ∀ t, x (t + 1) = 0)
    (hrec : ∀ t, x t - ez t = dc - (ez (t + 1) - ez t) / L.δ)
    (hnb : Tendsto (fun T => (1 + L.δ)⁻¹ ^ T * ez T) atTop (𝓝 0))
    (hgg : ez 0 = (L.δ * (1 + L.θ) + 2 * L.θ) * dc / (L.δ * (L.θ ^ 2 - 1))) :
    0 < ez 0 ∧ ∀ t, ez (t + 1) < 0 := by
  obtain ⟨he, hdc, hlater⟩ := temporary_shock L hx0 hxs hrec hnb hgg
  have hδ := L.hδ
  have hθ := L.hθ
  have hD := L.D_pos
  have hsq : 0 < L.θ ^ 2 - 1 := by nlinarith
  refine ⟨by rw [he]; positivity, fun t => ?_⟩
  rw [hlater t]
  have : 0 < dc := by rw [hdc]; positivity
  linarith

/-- The temporary-shock effects are strictly smaller than the permanent ones (O&R fn 16): the
scaling factor `δ/(1+δ)` lies in `(0, 1)`. -/
theorem temporary_scaling_lt_one {δ : ℝ} (hδ : 0 < δ) : 0 < δ / (1 + δ) ∧ δ / (1 + δ) < 1 :=
  ⟨by positivity, by rw [div_lt_one (by linarith)]; linarith⟩

/-! ## Exercise 1: money growth -/

/-- **Ex. 1(a): the steady-state nominal rate with money growth**, O&R p. 713: with steady
inflation `P_{t+1}/P_t = 1 + μ` and `r = δ`, Fisher parity gives `1 + ī = (1+δ)(1+μ)`. -/
theorem ex1_nominal_rate {δ μ i P P1 : ℝ} (hinfl : P1 / P = 1 + μ)
    (hfisher : 1 + i = P1 / P * (1 + δ)) : 1 + i = (1 + δ) * (1 + μ) := by
  rw [hfisher, hinfl]; ring

/-- **Ex. 1(a): (26′)**: steady-state real balances `χȳ₀(1+ī)/ī` FALL as money growth rises
(the real side is superneutral, so only the `(1+ī)/ī` factor moves): for `0 < ī < ī'`,
`χȳ₀(1+ī')/ī' < χȳ₀(1+ī)/ī`. -/
theorem ex1_real_balances_fall {χ y i i' : ℝ} (hχ : 0 < χ) (hy : 0 < y) (hi : 0 < i)
    (hii : i < i') : χ * y * ((1 + i') / i') < χ * y * ((1 + i) / i) := by
  apply mul_lt_mul_of_pos_left _ (by positivity)
  have hi' : 0 < i' := lt_trans hi hii
  rw [div_lt_div_iff₀ hi' hi]
  nlinarith

/-- **Ex. 1(a): (37′)** (T10 with money growth): around a trend with inflation `μ ≥ 0` and
`r = δ`, so `1 + ī = (1+μ)(1+δ)`, the term `log((1+i)/i)` of money demand has derivative
`−Δp/ī − δ r̂/((1+δ) ī)` along `P_{t+1}/P_t = (1+μ)e^{τΔp}`, `r = δ(1 + τ r̂)`. -/
theorem linearise_37_growth {δ μ dp rh : ℝ} (hδ : 0 < δ) (hμ : 0 ≤ μ) :
    HasDerivAt (fun τ => Real.log (((1 + μ) * Real.exp (τ * dp) * (1 + δ * (1 + τ * rh))) /
      ((1 + μ) * Real.exp (τ * dp) * (1 + δ * (1 + τ * rh)) - 1)))
      (-(dp / ((1 + μ) * (1 + δ) - 1)) -
        δ * rh / ((1 + δ) * ((1 + μ) * (1 + δ) - 1))) 0 := by
  set g : ℝ → ℝ := fun τ => (1 + μ) * Real.exp (τ * dp) * (1 + δ * (1 + τ * rh)) with hg
  have hgd : HasDerivAt g ((1 + μ) * (dp * (1 + δ) + δ * rh)) 0 := by
    have h1 := ((hasDerivAt_id (0 : ℝ)).mul_const dp).exp
    have h2 : HasDerivAt (fun τ => 1 + δ * (1 + τ * rh)) (δ * rh) 0 := by
      have := (((hasDerivAt_id (0 : ℝ)).mul_const rh).const_add 1).const_mul δ
      simpa using this.const_add 1
    have h3 := (h1.const_mul (1 + μ)).mul h2
    have e : g = (fun x => (1 + μ) * Real.exp (id x * dp)) * (fun τ => 1 + δ * (1 + τ * rh)) := by
      funext τ; simp [hg]
    rw [e]
    convert h3 using 1
    simp
    ring
  have hg0 : g 0 = (1 + μ) * (1 + δ) := by simp [hg]
  have hi : 0 < (1 + μ) * (1 + δ) - 1 := by nlinarith
  have hnum := hgd.log (by rw [hg0]; positivity)
  have hden := (hgd.sub_const 1).log (by rw [hg0]; linarith)
  have hev : ∀ᶠ τ in 𝓝 (0 : ℝ), 1 < g τ :=
    hgd.continuousAt.eventually (lt_mem_nhds (by rw [hg0]; linarith))
  have hcongr : (fun τ => Real.log (g τ / (g τ - 1))) =ᶠ[𝓝 0]
      fun τ => Real.log (g τ) - Real.log (g τ - 1) := by
    filter_upwards [hev] with τ hτ
    rw [Real.log_div (by linarith) (by linarith)]
  have hfin := (hnum.sub hden).congr_of_eventuallyEq hcongr
  convert hfin using 1
  rw [hg0]
  have : (1 + δ) ≠ 0 := by linarith
  have : (1 + μ) ≠ 0 := by linarith
  have := hi.ne'
  field_simp
  ring

/-- **Ex. 1(a): (39′)**, O&R p. 713: subtracting the growth versions of (37′) and (38′),
`m − p = c − δr/((1+δ)ī) − (p_{t+1} − p_t)/ī` and its Foreign twin, and using PPP (29), gives
`m − m* − e = c − c* − (e_{t+1} − e_t)/ī`: (39) with `δ` replaced by `ī`, so the forward
solution (61′) is `forward_solution_unique` at rate `ī`. -/
theorem eq39_growth {δ i m ms p ps p1 ps1 c cs r e e1 : ℝ}
    (h37 : m - p = c - δ * r / ((1 + δ) * i) - (p1 - p) / i)
    (h38 : ms - ps = cs - δ * r / ((1 + δ) * i) - (ps1 - ps) / i)
    (h29 : e = p - ps) (h29' : e1 = p1 - ps1) :
    m - ms - e = c - cs - (e1 - e) / i := by
  rw [h29, h29']
  have : (p1 - ps1 - (p - ps)) / i = (p1 - p) / i - (ps1 - ps) / i := by ring
  rw [this]
  linarith

/-- The discounted sums behind Ex. 1(b): for `a > 0`,
`(a/(1+a)) Σ_{j≥0} (1+a)^{−j}(1+j) = (1+a)/a` and `(a/(1+a)) Σ_{j≥0} (1+a)^{−j} j = 1/a`. -/
theorem ex1_sums {a : ℝ} (ha : 0 < a) :
    a / (1 + a) * ∑' j : ℕ, (1 + a)⁻¹ ^ j * ((j : ℝ) + 1) = (1 + a) / a ∧
      a / (1 + a) * ∑' j : ℕ, (1 + a)⁻¹ ^ j * (j : ℝ) = 1 / a := by
  set q := (1 + a)⁻¹ with hq
  have hq0 : 0 < q := inv_pos.2 (by linarith)
  have hq1 : q < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hnorm : ‖q‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos hq0]; exact hq1
  have hA : HasSum (fun j : ℕ => (j : ℝ) * q ^ j) (q / (1 - q) ^ 2) :=
    hasSum_coe_mul_geometric_of_norm_lt_one hnorm
  have hB : HasSum (fun j : ℕ => q ^ j) (1 - q)⁻¹ := hasSum_geometric_of_lt_one hq0.le hq1
  have h1q : 1 - q = a / (1 + a) := by rw [hq]; field_simp; ring
  have hA' : ∑' j : ℕ, q ^ j * (j : ℝ) = q / (1 - q) ^ 2 := by
    rw [← hA.tsum_eq]; exact tsum_congr fun j => by ring
  have hAB : ∑' j : ℕ, q ^ j * ((j : ℝ) + 1) = q / (1 - q) ^ 2 + (1 - q)⁻¹ := by
    rw [← hA.tsum_eq, ← hB.tsum_eq, ← hA.summable.tsum_add hB.summable]
    exact tsum_congr fun j => by ring
  have : (1 + a) ≠ 0 := by linarith
  have := ha.ne'
  refine ⟨?_, ?_⟩
  · rw [hAB, h1q, hq]; field_simp
  · rw [hA', h1q, hq]; field_simp

/-- **Ex. 1(b): a permanent rise in Home money growth from date 1**, O&R p. 713. With
`ν = log((1+μ')/(1+μ))` and the new growth applying from date 1 (`m_t = tν`, index `t − 1`
here: `x_t = (t+1)ν`), the forward MM′ equation at rate `ī` gives
`e₁ = ν(1+ī)/ī − (c − c*)`; with the unchanged GG schedule,
`e = [δ(1+θ)+2θ]ν(1+ī)/(ī D) > 0`, `c − c* = δ(θ²−1)ν(1+ī)/(ī D) > 0` for `ν > 0`. -/
theorem ex1_growth_shock (L : ReduxLinear) {i ν dc : ℝ} (hi : 0 < i) {x ez : ℕ → ℝ}
    (hx : ∀ t, x t = ((t : ℝ) + 1) * ν)
    (hrec : ∀ t, x t - ez t = dc - (ez (t + 1) - ez t) / i)
    (hnb : Tendsto (fun T => (1 + i)⁻¹ ^ T * ez T) atTop (𝓝 0))
    (hgg : ez 0 = (L.δ * (1 + L.θ) + 2 * L.θ) * dc / (L.δ * (L.θ ^ 2 - 1))) :
    ez 0 = ν * (1 + i) / i - dc ∧
    dc = L.δ * (L.θ ^ 2 - 1) * (ν * (1 + i) / i) / L.D ∧
    ez 0 = (L.δ * (1 + L.θ) + 2 * L.θ) * (ν * (1 + i) / i) / L.D := by
  have hq0 : 0 < (1 + i)⁻¹ := inv_pos.2 (by linarith)
  have hq1 : (1 + i)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hnorm : ‖(1 + i)⁻¹‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos hq0]; exact hq1
  have hsumA : Summable (fun j : ℕ => ((j : ℝ) + 1) * (1 + i)⁻¹ ^ j) := by
    have hA := (hasSum_coe_mul_geometric_of_norm_lt_one hnorm).summable
    have hB := summable_geometric_of_lt_one hq0.le hq1
    exact (hA.add hB).congr fun j => by ring
  have hsum : Summable (fun s => (1 + i)⁻¹ ^ s * x s) :=
    (hsumA.mul_right ν).congr fun s => by rw [hx s]; ring
  have h0 := forward_solution_unique hi hrec hnb hsum 0
  have hs : ∑' j, (1 + i)⁻¹ ^ j * x (0 + j) = ν * ∑' j : ℕ, (1 + i)⁻¹ ^ j * ((j : ℝ) + 1) := by
    rw [← tsum_mul_left]
    exact tsum_congr fun j => by rw [zero_add, hx j]; ring
  rw [hs] at h0
  have hmm : ez 0 = ν * (1 + i) / i - dc := by
    rw [h0]
    have := (ex1_sums hi).1
    have e : i / (1 + i) * (ν * ∑' j : ℕ, (1 + i)⁻¹ ^ j * ((j : ℝ) + 1)) =
      ν * (i / (1 + i) * ∑' j : ℕ, (1 + i)⁻¹ ^ j * ((j : ℝ) + 1)) := by ring
    rw [e, this]
    ring
  obtain ⟨hdc, he⟩ := solve_mm_gg L hmm hgg
  exact ⟨hmm, hdc, he⟩

/-- **Ex. 1(b), timing variant** (flag): if the new growth rate first applies to `M₂/M₁`
(`m₁ = 0`, `x_t = tν`), the MM′ intercept is `ν/ī` instead of `ν(1+ī)/ī`: `e₁ = ν/ī − (c − c*)`.
The signs of all effects are unchanged. -/
theorem ex1_growth_shock_late {i ν dc : ℝ} (hi : 0 < i) {x ez : ℕ → ℝ}
    (hx : ∀ t, x t = (t : ℝ) * ν)
    (hrec : ∀ t, x t - ez t = dc - (ez (t + 1) - ez t) / i)
    (hnb : Tendsto (fun T => (1 + i)⁻¹ ^ T * ez T) atTop (𝓝 0)) :
    ez 0 = ν / i - dc := by
  have hq0 : 0 < (1 + i)⁻¹ := inv_pos.2 (by linarith)
  have hq1 : (1 + i)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hnorm : ‖(1 + i)⁻¹‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos hq0]; exact hq1
  have hsumA : Summable (fun j : ℕ => (j : ℝ) * (1 + i)⁻¹ ^ j) :=
    (hasSum_coe_mul_geometric_of_norm_lt_one hnorm).summable
  have hsum : Summable (fun s => (1 + i)⁻¹ ^ s * x s) :=
    (hsumA.mul_right ν).congr fun s => by rw [hx s]; ring
  have h0 := forward_solution_unique hi hrec hnb hsum 0
  have hs : ∑' j, (1 + i)⁻¹ ^ j * x (0 + j) = ν * ∑' j : ℕ, (1 + i)⁻¹ ^ j * (j : ℝ) := by
    rw [← tsum_mul_left]
    exact tsum_congr fun j => by rw [zero_add, hx j]; ring
  rw [hs] at h0
  rw [h0]
  have := (ex1_sums hi).2
  have e : i / (1 + i) * (ν * ∑' j : ℕ, (1 + i)⁻¹ ^ j * (j : ℝ)) =
    ν * (i / (1 + i) * ∑' j : ℕ, (1 + i)⁻¹ ^ j * (j : ℝ)) := by ring
  rw [e, this]
  ring

/-- **Ex. 1(b): the current account improves** (O&R p. 713): with `b̄/(1−n) = 2θ(c−c*)/((1+θ)δ)`
((45) with (57)), a rise in Home money growth (`c − c* > 0`) gives a Home surplus `b̄ > 0`. -/
theorem ex1_current_account (L : ReduxLinear) {b dc : ℝ}
    (h : b / (1 - L.n) = 2 * L.θ * dc / ((1 + L.θ) * L.δ)) (hdc : 0 < dc) : 0 < b := by
  have hn : 0 < 1 - L.n := by linarith [L.hn1]
  have hθ : 0 < L.θ := by linarith [L.hθ]
  have hpos : 0 < 2 * L.θ * dc / ((1 + L.θ) * L.δ) := by have := L.hδ; positivity
  rw [← h] at hpos
  exact (div_pos_iff_of_pos_right hn).1 hpos

/-! ## The equiproportionate money shock, exactly (10.1.8.1, T19) -/

/-- The bloc price index at equal bloc prices is that price (O&R (5), (22)). -/
theorem blocPriceIndex_self {θ n a : ℝ} (hθ : θ ≠ 1) (ha : 0 < a) :
    blocPriceIndex θ n a a = a := by
  unfold blocPriceIndex
  rw [show n * a ^ (1 - θ) + (1 - n) * a ^ (1 - θ) = a ^ (1 - θ) by ring, ← rpow_mul ha.le]
  have : (1 - θ) * (1 / (1 - θ)) = 1 := by
    have : 1 - θ ≠ 0 := sub_ne_zero.2 (Ne.symm hθ)
    field_simp
  rw [this, rpow_one]

/-- The date-1 unknowns of the nonlinear sticky-price economy after an unanticipated money shock,
O&R §10.1.7–§10.1.8 (pp. 674–684): the exchange rate `𝓔₁`, price levels `P₁, P₁*`, consumption,
output, the current account `B₂`, the real rate `r₂`, the nominal rates `i₂, i₂*`, date-2 price
levels `P₂, P₂*` and the long-run real allocation (a steady state from date 2 on, T9). -/
structure Date1Vars where
  E1 : ℝ
  P1 : ℝ
  Ps1 : ℝ
  C1 : ℝ
  Cs1 : ℝ
  y1 : ℝ
  ys1 : ℝ
  B2 : ℝ
  r2 : ℝ
  i2 : ℝ
  is2 : ℝ
  P2 : ℝ
  Ps2 : ℝ
  lr : Allocation

/-- **The nonlinear equilibrium after an unanticipated equiproportionate money shock**,
O&R §10.1.7–§10.1.8.1 (pp. 674–684). Starting from the symmetric steady state with price levels
`P₀, P₀*` (so the preset goods prices are `p(h) = P₀`, `p*(f) = P₀*`, eq. (22)), money becomes
`μM₀`, `μM₀*` permanently at date 1. Date 1: the price indexes (5)–(6), world demand (10) (output
demand-determined at preset prices), the current account (54) from `B₁ = 0`, the Euler equations
(13) into the long run, money demand (14), Fisher parity; from date 2: a flexible-price steady
state (T9, `flexible_path_is_steady`) with long-run money demand (26). EXACTLY, T9 indexes that
steady state by `B̄ = (1 + r₂)B₂/(1 + δ)` (the date-2 budget pays `r₂`, not `δ`, on `B₂`); the
book's "`b_t = b̄` for all `t ≥ 2`" (p. 677) is its first-order version (`longrun_assets`). -/
structure IsEquiEqm (M : ReduxParams) (P0 Ps0 M0 Ms0 μ : ℝ) (w : Date1Vars) : Prop where
  E1_pos : 0 < w.E1
  C1_pos : 0 < w.C1
  Cs1_pos : 0 < w.Cs1
  i2_pos : 0 < w.i2
  is2_pos : 0 < w.is2
  P2_pos : 0 < w.P2
  Ps2_pos : 0 < w.Ps2
  r2_pos : 0 < 1 + w.r2
  price : w.P1 = blocPriceIndex M.θ M.n P0 (w.E1 * Ps0)
  price_star : w.Ps1 = blocPriceIndex M.θ M.n (P0 / w.E1) Ps0
  demand : w.y1 = cesDemand M.θ P0 w.P1 (worldConsumption M.n w.C1 w.Cs1)
  demand_star : w.ys1 = cesDemand M.θ Ps0 w.Ps1 (worldConsumption M.n w.C1 w.Cs1)
  ca : w.B2 = P0 / w.P1 * w.y1 - w.C1
  euler : w.lr.C = M.β * (1 + w.r2) * w.C1
  euler_star : w.lr.Cs = M.β * (1 + w.r2) * w.Cs1
  money : μ * M0 / w.P1 = M.χ * w.C1 * ((1 + w.i2) / w.i2)
  money_star : μ * Ms0 / w.Ps1 = M.χ * w.Cs1 * ((1 + w.is2) / w.is2)
  fisher : 1 + w.i2 = w.P2 / w.P1 * (1 + w.r2)
  fisher_star : 1 + w.is2 = w.Ps2 / w.Ps1 * (1 + w.r2)
  longrun : IsSteadyState M ((1 + w.r2) * w.B2 / (1 + M.δ)) w.lr
  money2 : μ * M0 / w.P2 = M.χ * w.lr.C * ((1 + M.δ) / M.δ)
  money2_star : μ * Ms0 / w.Ps2 = M.χ * w.lr.Cs * ((1 + M.δ) / M.δ)

/-- **The equiproportionate shock: the equilibrium is unique and is what the book says, EXACTLY**
(O&R §10.1.8.1, pp. 683–684; T19). In any equilibrium: `i₂ = i₂* = δ` (the nominal rate is
unchanged), `𝓔₁ = 𝓔₀` (no exchange-rate or terms-of-trade effect), `B₂ = 0` (no current account),
`P₁ = P₀`, `C₁ = C₁* = y₁ = y₁* = μȳ₀`, `1 + r₂ = (1+δ)/μ`, `P₂ = μP₀`, and the long run is the
initial symmetric steady state. The proof is exact (no linearisation): `nominal_rate_exact` and
exact UIP give `𝓔₁ = 𝓔₂`; long-run money demand makes `𝓔₂/𝓔₀ = C̄*/C̄`; the current account has
the sign of `𝓔₁/𝓔₀ − 1`; and in a steady state `B̄ > 0 ⟺ C̄ > C̄*` (T7). -/
theorem equiproportionate_unique {M : ReduxParams} {P0 Ps0 M0 Ms0 μ : ℝ} {w : Date1Vars}
    (hP0 : 0 < P0) (hPs0 : 0 < Ps0) (hM0 : 0 < M0) (hMs0 : 0 < Ms0) (hμ : 0 < μ)
    (h26 : M0 / P0 = M.χ * (1 + M.δ) / M.δ * M.ybar0)
    (h26s : Ms0 / Ps0 = M.χ * (1 + M.δ) / M.δ * M.ybar0)
    (h : IsEquiEqm M P0 Ps0 M0 Ms0 μ w) :
    w.i2 = M.δ ∧ w.is2 = M.δ ∧ w.E1 = P0 / Ps0 ∧ w.B2 = 0 ∧ w.P1 = P0 ∧ w.Ps1 = Ps0 ∧
      w.C1 = μ * M.ybar0 ∧ w.Cs1 = μ * M.ybar0 ∧ w.y1 = μ * M.ybar0 ∧ w.ys1 = μ * M.ybar0 ∧
      1 + w.r2 = (1 + M.δ) / μ ∧ w.P2 = μ * P0 ∧ w.lr = symmetricSteady M := by
  have hθ := M.hθ
  have hθ1 : M.θ ≠ 1 := by linarith
  have hn0 := M.hn0
  have hn1 := M.hn1
  have hδ := M.δ_pos
  have hχ := M.hχ
  have hy0 := M.ybar0_pos
  have hβ := M.hβ0
  have hβδ := M.β_mul_one_add_δ
  have hP1 : 0 < w.P1 := by
    rw [h.price]; exact blocPriceIndex_pos hn0 hn1 hP0 (mul_pos h.E1_pos hPs0)
  have hPs1 : 0 < w.Ps1 := by
    rw [h.price_star]; exact blocPriceIndex_pos hn0 hn1 (div_pos hP0 h.E1_pos) hPs0
  have hlrC := h.longrun.static.C_pos
  have hlrCs := h.longrun.static.Cs_pos
  -- (a) nominal rates are exactly `δ`
  have hi2 : w.i2 = M.δ := nominal_rate_exact hβ hδ hβδ hχ (mul_pos hμ hM0) hP1 h.P2_pos
    h.C1_pos h.i2_pos h.r2_pos h.money h.money2 h.euler h.fisher
  have his2 : w.is2 = M.δ := nominal_rate_exact hβ hδ hβδ hχ (mul_pos hμ hMs0) hPs1 h.Ps2_pos
    h.Cs1_pos h.is2_pos h.r2_pos h.money_star h.money2_star h.euler_star h.fisher_star
  -- (b) exact UIP: `𝓔₁ = P₁/P₁* = P₂/P₂*`
  have hppp : w.P1 = w.E1 * w.Ps1 := by
    rw [h.price, h.price_star]; exact bloc_ppp hθ1 hn0 hn1 hP0 hPs0 h.E1_pos
  have hE12 : w.P1 / w.Ps1 = w.P2 / w.Ps2 := by
    have hf := h.fisher; have hfs := h.fisher_star
    rw [hi2] at hf; rw [his2] at hfs
    exact no_overshooting_exact hδ hP1 hPs1 h.Ps2_pos hf hfs
  -- (c) consumption from money demand
  have hM0' : M0 = M.χ * (1 + M.δ) / M.δ * M.ybar0 * P0 := by field_simp at h26 ⊢; linarith
  have hMs0' : Ms0 = M.χ * (1 + M.δ) / M.δ * M.ybar0 * Ps0 := by field_simp at h26s ⊢; linarith
  have hk : M.χ * ((1 + M.δ) / M.δ) ≠ 0 := by positivity
  have hC1 : w.C1 = μ * M.ybar0 * (P0 / w.P1) := by
    have e1 : w.C1 = μ * M0 / w.P1 / (M.χ * ((1 + M.δ) / M.δ)) := by
      rw [eq_div_iff hk, h.money, hi2]; ring
    rw [e1, hM0']; field_simp
  have hCs1 : w.Cs1 = μ * M.ybar0 * (Ps0 / w.Ps1) := by
    have e1 : w.Cs1 = μ * Ms0 / w.Ps1 / (M.χ * ((1 + M.δ) / M.δ)) := by
      rw [eq_div_iff hk, h.money_star, his2]; ring
    rw [e1, hMs0']; field_simp
  have hC2 : w.lr.C = μ * M.ybar0 * (P0 / w.P2) := by
    have e1 : w.lr.C = μ * M0 / w.P2 / (M.χ * ((1 + M.δ) / M.δ)) := by
      rw [eq_div_iff hk, h.money2]; ring
    rw [e1, hM0']; field_simp
  have hCs2 : w.lr.Cs = μ * M.ybar0 * (Ps0 / w.Ps2) := by
    have e1 : w.lr.Cs = μ * Ms0 / w.Ps2 / (M.χ * ((1 + M.δ) / M.δ)) := by
      rw [eq_div_iff hk, h.money2_star]; ring
    rw [e1, hMs0']; field_simp
  -- (d) the relative prices `α = P₀/P₁`, `α* = P₀*/P₁*`
  set a := P0 / w.P1 with ha
  set as := Ps0 / w.Ps1 with has
  have hapos : 0 < a := div_pos hP0 hP1
  have haspos : 0 < as := div_pos hPs0 hPs1
  have hidx : M.n * a ^ (1 - M.θ) + (1 - M.n) * as ^ (1 - M.θ) = 1 := by
    have := bloc_relative_price_sum hθ1 hn0 hn1 hP0 hPs0 h.E1_pos
    rw [← h.price, ← h.price_star] at this
    exact this
  have hsum : M.n * a * a ^ (-M.θ) + (1 - M.n) * as * as ^ (-M.θ) = 1 := by
    rw [mul_assoc, mul_assoc, ces_price_mul_demand hapos, ces_price_mul_demand haspos]
    exact hidx
  -- (e) the long-run exchange rate: `α* C̄ = α C̄*`
  have hcross : as * w.lr.C = a * w.lr.Cs := by
    rw [has, ha, hC2, hCs2]
    have h2 := hE12
    have := h.P2_pos.ne'
    have := h.Ps2_pos.ne'
    have := hP1.ne'
    have := hPs1.ne'
    field_simp at h2 ⊢
    linear_combination h2
  -- (f) the current account has the sign of `α* − α`
  have hy1e : w.y1 = a ^ (-M.θ) * (μ * M.ybar0 * (M.n * a + (1 - M.n) * as)) := by
    rw [h.demand]; unfold cesDemand worldConsumption; rw [← ha, hC1, hCs1]; ring
  have hB2 : w.B2 = μ * M.ybar0 * a * (1 - M.n) * as * (a ^ (-M.θ) - as ^ (-M.θ)) := by
    rw [h.ca, ← ha, hy1e, hC1]
    linear_combination (μ * M.ybar0 * a) * hsum
  have hneg : -M.θ < 0 := by linarith
  have hαeq : a = as := by
    rcases lt_trichotomy a as with hlt | heq | hgt
    · exfalso
      have hB : 0 < w.B2 := by
        rw [hB2]
        have := rpow_lt_rpow_of_neg hapos hlt hneg
        have h1 : 0 < 1 - M.n := by linarith
        have : 0 < a ^ (-M.θ) - as ^ (-M.θ) := by linarith
        positivity
      have hlt2 := (steady_C_gt_iff h.longrun).2 (by
        have := h.r2_pos; have : 0 < 1 + M.δ := by linarith
        positivity)
      have e1 := mul_lt_mul_of_pos_left hlt2 hapos
      have e2 := mul_lt_mul_of_pos_right hlt hlrC
      linarith
    · exact heq
    · exfalso
      have hB : w.B2 < 0 := by
        rw [hB2]
        have := rpow_lt_rpow_of_neg haspos hgt hneg
        have h1 : 0 < 1 - M.n := by linarith
        have : a ^ (-M.θ) - as ^ (-M.θ) < 0 := by linarith
        have hp : 0 < μ * M.ybar0 * a * (1 - M.n) * as := by positivity
        exact mul_neg_of_pos_of_neg hp this
      have hle : w.lr.C ≤ w.lr.Cs := by
        by_contra hc
        push Not at hc
        have h3 := (steady_C_gt_iff h.longrun).1 hc
        have h4 : (1 + w.r2) * w.B2 / (1 + M.δ) < 0 :=
          div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg h.r2_pos hB) (by linarith)
        linarith
      have e1 := mul_le_mul_of_nonneg_left hle hapos.le
      have e2 := mul_lt_mul_of_pos_right hgt hlrC
      linarith
  -- (g) hence `α = α* = 1`
  have ha1 : a = 1 := by
    rw [← hαeq] at hidx
    have h1 : a ^ (1 - M.θ) = 1 := by linarith
    have hne : (1 - M.θ) ≠ 0 := by linarith
    have := (rpow_left_inj hapos.le zero_le_one hne).1 (by rw [h1, one_rpow])
    exact this
  have has1 : as = 1 := by rw [← hαeq]; exact ha1
  have hP1eq : w.P1 = P0 := by
    rw [ha] at ha1; field_simp at ha1; linarith
  have hPs1eq : w.Ps1 = Ps0 := by
    rw [has] at has1; field_simp at has1; linarith
  have hE1 : w.E1 = P0 / Ps0 := by
    rw [hP1eq, hPs1eq] at hppp
    field_simp; linarith
  have hC1' : w.C1 = μ * M.ybar0 := by rw [hC1, ha1, mul_one]
  have hCs1' : w.Cs1 = μ * M.ybar0 := by rw [hCs1, has1, mul_one]
  have hX1 : worldConsumption M.n w.C1 w.Cs1 = μ * M.ybar0 := by
    unfold worldConsumption; rw [hC1', hCs1']; ring
  have hy1 : w.y1 = μ * M.ybar0 := by
    rw [h.demand, hX1, hP1eq, cesDemand_at_index M.θ hP0.ne']
  have hys1 : w.ys1 = μ * M.ybar0 := by
    rw [h.demand_star, hX1, hPs1eq, cesDemand_at_index M.θ hPs0.ne']
  have hB20 : w.B2 = 0 := by
    rw [h.ca, hy1, hC1', hP1eq, div_self hP0.ne']; ring
  have hlr : w.lr = symmetricSteady M := by
    have := h.longrun; rw [hB20, mul_zero, zero_div] at this
    exact (isSteadyState_zero_iff M w.lr).1 this
  have hr2 : 1 + w.r2 = (1 + M.δ) / μ := by
    have he := h.euler
    rw [hlr, hC1'] at he
    simp only [symmetricSteady] at he
    have hk2 : M.ybar0 * ((1 + w.r2) * μ - (1 + M.δ)) = 0 := by
      linear_combination (-(1 + M.δ)) * he - (1 + w.r2) * μ * M.ybar0 * hβδ
    have := (mul_eq_zero.1 hk2).resolve_left hy0.ne'
    rw [eq_div_iff hμ.ne']
    linarith
  have hP2 : w.P2 = μ * P0 := by
    have hc := hC2
    rw [hlr] at hc
    simp only [symmetricSteady] at hc
    have := h.P2_pos.ne'
    have e : M.ybar0 * w.P2 = μ * M.ybar0 * P0 := by
      calc M.ybar0 * w.P2 = μ * M.ybar0 * (P0 / w.P2) * w.P2 := by rw [← hc]
        _ = μ * M.ybar0 * P0 := by field_simp
    have hk3 : M.ybar0 * (w.P2 - μ * P0) = 0 := by linear_combination e
    have := (mul_eq_zero.1 hk3).resolve_left hy0.ne'
    linarith
  exact ⟨hi2, his2, hE1, hB20, hP1eq, hPs1eq, hC1', hCs1', hy1, hys1, hr2, hP2, hlr⟩

/-- **The long-run asset position: exact versus first order** (O&R p. 677, "`b_t = b̄` for all
`t ≥ 2`"): after the date-1 current account `B₂`, the flexible-price steady state from date 2 is
indexed EXACTLY by `B̄ = (1 + r₂)B₂/(1 + δ)` (`flexible_path_is_steady`, T9), not by `B₂`. Along
`B₂ = τ b̄ C̄₀`, `r₂ = δ(1 + τ r̂)`, the two agree to first order: `dB̄/dτ = b̄ C̄₀` at `τ = 0`. -/
theorem longrun_assets {δ b rh C0 : ℝ} (hδ : 0 < δ) :
    HasDerivAt (fun τ => (1 + δ * (1 + τ * rh)) * (τ * b * C0) / (1 + δ)) (b * C0) 0 := by
  have h1 : HasDerivAt (fun τ => 1 + δ * (1 + τ * rh)) (δ * rh) 0 := by
    have := (((hasDerivAt_id (0 : ℝ)).mul_const rh).const_add 1).const_mul δ
    simpa using this.const_add 1
  have h2 : HasDerivAt (fun τ : ℝ => τ * b * C0) (b * C0) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const b).mul_const C0
  have h := (h1.mul h2).div_const (1 + δ)
  convert h using 1
  have : (1 + δ) ≠ 0 := by linarith
  simp
  field_simp

/-- The equilibrium of the equiproportionate shock (T19), O&R pp. 683–684. -/
noncomputable def equiSolution (M : ReduxParams) (P0 Ps0 μ : ℝ) : Date1Vars where
  E1 := P0 / Ps0
  P1 := P0
  Ps1 := Ps0
  C1 := μ * M.ybar0
  Cs1 := μ * M.ybar0
  y1 := μ * M.ybar0
  ys1 := μ * M.ybar0
  B2 := 0
  r2 := (1 + M.δ) / μ - 1
  i2 := M.δ
  is2 := M.δ
  P2 := μ * P0
  Ps2 := μ * Ps0
  lr := symmetricSteady M

/-- **Existence for the equiproportionate shock** (T19): `equiSolution` satisfies every
equilibrium condition of `IsEquiEqm`. Together with `equiproportionate_unique` the nonlinear
sticky-price equilibrium exists and is unique for every `μ > 0`. -/
theorem equiproportionate_exists {M : ReduxParams} {P0 Ps0 M0 Ms0 μ : ℝ} (hP0 : 0 < P0)
    (hPs0 : 0 < Ps0) (hμ : 0 < μ) (h26 : M0 / P0 = M.χ * (1 + M.δ) / M.δ * M.ybar0)
    (h26s : Ms0 / Ps0 = M.χ * (1 + M.δ) / M.δ * M.ybar0) :
    IsEquiEqm M P0 Ps0 M0 Ms0 μ (equiSolution M P0 Ps0 μ) := by
  have hθ1 : M.θ ≠ 1 := by linarith [M.hθ]
  have hδ := M.δ_pos
  have hy0 := M.ybar0_pos
  have hβδ := M.β_mul_one_add_δ
  have hsym : IsSteadyState M ((1 + ((1 + M.δ) / μ - 1)) * 0 / (1 + M.δ)) (symmetricSteady M) := by
    rw [mul_zero, zero_div]; exact (isSteadyState_zero_iff M (symmetricSteady M)).2 rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hsym, ?_,
    ?_⟩ <;> simp only [equiSolution, symmetricSteady]
  · positivity
  · positivity
  · positivity
  · exact hδ
  · exact hδ
  · positivity
  · positivity
  · ring_nf; positivity
  · rw [div_mul_cancel₀ _ hPs0.ne', blocPriceIndex_self hθ1 hP0]
  · rw [div_div_eq_mul_div, mul_div_cancel_left₀ _ hP0.ne', blocPriceIndex_self hθ1 hPs0]
  · rw [cesDemand_at_index M.θ hP0.ne']; unfold worldConsumption; ring
  · rw [cesDemand_at_index M.θ hPs0.ne']; unfold worldConsumption; ring
  · rw [div_self hP0.ne']; ring
  · have : (1 + ((1 + M.δ) / μ - 1)) = (1 + M.δ) / μ := by ring
    rw [this]; field_simp; linarith
  · have : (1 + ((1 + M.δ) / μ - 1)) = (1 + M.δ) / μ := by ring
    rw [this]; field_simp; linarith
  · have hM0 : M0 = M.χ * (1 + M.δ) / M.δ * M.ybar0 * P0 := by field_simp at h26 ⊢; linarith
    rw [hM0]; field_simp
  · have hMs0 : Ms0 = M.χ * (1 + M.δ) / M.δ * M.ybar0 * Ps0 := by
      field_simp at h26s ⊢; linarith
    rw [hMs0]; field_simp
  · rw [mul_div_cancel_right₀ _ hP0.ne']; field_simp; ring
  · rw [mul_div_cancel_right₀ _ hPs0.ne']; field_simp; ring
  · have hM0 : M0 = M.χ * (1 + M.δ) / M.δ * M.ybar0 * P0 := by field_simp at h26 ⊢; linarith
    rw [hM0]; field_simp
  · have hMs0 : Ms0 = M.χ * (1 + M.δ) / M.δ * M.ybar0 * Ps0 := by
      field_simp at h26s ⊢; linarith
    rw [hMs0]; field_simp

/-- **Output is demand-determined only up to a bound** (O&R p. 674 and p. 688; T19–T20): at the
equiproportionate equilibrium a Home producer is willing to meet demand at the preset price iff
the real price per unit of marginal utility covers the marginal disutility of effort,
`(p(h)/P₁)/C₁ ≥ κ y₁`, which with `p(h) = P₁`, `C₁ = y₁ = μȳ₀` and `κȳ₀² = (θ−1)/θ` is exactly
`μ ≤ (θ/(θ−1))^{1/2}`. The book's "small shocks" hides this bound. -/
theorem equiproportionate_demand_bound (M : ReduxParams) {μ : ℝ} (hμ : 0 < μ) :
    M.κ * (μ * M.ybar0) ≤ 1 / (μ * M.ybar0) ↔ μ ≤ Real.sqrt (M.θ / (M.θ - 1)) := by
  have hy0 := M.ybar0_pos
  have hθ := M.hθ
  have hk := M.κ_mul_ybar0_sq
  have hθ1 : 0 < M.θ - 1 := by linarith
  rw [le_div_iff₀ (by positivity), Real.le_sqrt hμ.le (by positivity)]
  have e : M.κ * (μ * M.ybar0) * (μ * M.ybar0) = μ ^ 2 * ((M.θ - 1) / M.θ) := by
    rw [← hk]; ring
  rw [e, le_div_iff₀ hθ1]
  constructor
  · intro h
    have : μ ^ 2 * (M.θ - 1) ≤ M.θ := by
      have hθ0 : 0 < M.θ := by linarith
      rw [mul_div_assoc'] at h
      rwa [div_le_one hθ0] at h
    linarith
  · intro h
    have hθ0 : 0 < M.θ := by linarith
    rw [mul_div_assoc', div_le_one hθ0]
    linarith

/-- The exact period-1 utility gain of the equiproportionate shock, O&R §10.1.8.1 (T19):
`log μ − ((θ−1)/(2θ))(μ² − 1)`. -/
noncomputable def equiGain (θ μ : ℝ) : ℝ := Real.log μ - (θ - 1) / (2 * θ) * (μ ^ 2 - 1)

/-- **The real-utility change of the equiproportionate shock** (T19): with `C₁ = y₁ = μȳ₀` and the
initial `C = y = ȳ₀`, `[log C₁ − (κ/2)y₁²] − [log ȳ₀ − (κ/2)ȳ₀²] = log μ − ((θ−1)/(2θ))(μ²−1)`.
Later periods are unchanged (the long run is the initial steady state, `equiproportionate_unique`),
so this is the whole change in `Uᴿ` (p. 684). -/
theorem equiGain_eq (M : ReduxParams) {μ : ℝ} (hμ : 0 < μ) :
    (Real.log (μ * M.ybar0) - M.κ / 2 * (μ * M.ybar0) ^ 2) -
      (Real.log M.ybar0 - M.κ / 2 * M.ybar0 ^ 2) = equiGain M.θ μ := by
  have hy0 := M.ybar0_pos
  have hk := M.κ_mul_ybar0_sq
  have hθ0 : M.θ ≠ 0 := by linarith [M.hθ]
  unfold equiGain
  rw [Real.log_mul hμ.ne' hy0.ne']
  have e : M.κ / 2 * (μ * M.ybar0) ^ 2 - M.κ / 2 * M.ybar0 ^ 2 =
      (M.κ * M.ybar0 ^ 2) / 2 * (μ ^ 2 - 1) := by ring
  have : Real.log μ + Real.log M.ybar0 - M.κ / 2 * (μ * M.ybar0) ^ 2 -
      (Real.log M.ybar0 - M.κ / 2 * M.ybar0 ^ 2) =
      Real.log μ - (M.κ / 2 * (μ * M.ybar0) ^ 2 - M.κ / 2 * M.ybar0 ^ 2) := by ring
  rw [this, e, hk]
  field_simp

/-- **The equiproportionate expansion raises welfare, exactly** (O&R p. 683, "must raise welfare
in both countries"; T19): the gain is strictly increasing on `(0, (θ/(θ−1))^{1/2}]` and strictly
positive for `1 < μ ≤ (θ/(θ−1))^{1/2}`, i.e. on the whole range where output is
demand-determined (`equiproportionate_demand_bound`). -/
theorem equiGain_pos {θ μ : ℝ} (hθ : 1 < θ) (hμ1 : 1 < μ) (hμb : μ ≤ Real.sqrt (θ / (θ - 1))) :
    0 < equiGain θ μ ∧
      StrictMonoOn (equiGain θ) (Set.Ioc 0 (Real.sqrt (θ / (θ - 1)))) := by
  have hk : 0 < (θ - 1) / θ := div_pos (by linarith) (by linarith)
  have hplan : plannerOutput ((θ - 1) / θ) = Real.sqrt (θ / (θ - 1)) := by
    unfold plannerOutput; congr 1; field_simp
  have hmono := planner_strictMonoOn hk
  rw [hplan] at hmono
  have hrel : ∀ x, equiGain θ x = plannerObjective ((θ - 1) / θ) x + (θ - 1) / (2 * θ) := by
    intro x; unfold equiGain plannerObjective
    have : θ ≠ 0 := by linarith
    field_simp; ring
  have hstrict : StrictMonoOn (equiGain θ) (Set.Ioc 0 (Real.sqrt (θ / (θ - 1)))) := by
    intro a ha b hb hab
    rw [hrel a, hrel b]
    linarith [hmono ha hb hab]
  refine ⟨?_, hstrict⟩
  have h1mem : (1 : ℝ) ∈ Set.Ioc 0 (Real.sqrt (θ / (θ - 1))) :=
    ⟨one_pos, by linarith⟩
  have hμmem : μ ∈ Set.Ioc 0 (Real.sqrt (θ / (θ - 1))) := ⟨by linarith, hμb⟩
  have := hstrict h1mem hμmem hμ1
  have h0 : equiGain θ 1 = 0 := by simp [equiGain]
  linarith

/-- **First order: the welfare effect is `mᵂ/θ`** (T19 recovers (76), O&R p. 685): the
derivative of the exact gain at `μ = 1` is `1/θ`, so a proportional expansion `dμ = mᵂ` raises
`Uᴿ` by `mᵂ/θ`. -/
theorem equiGain_hasDerivAt_one {θ : ℝ} (hθ : θ ≠ 0) : HasDerivAt (equiGain θ) (1 / θ) 1 := by
  have h1 := Real.hasDerivAt_log (one_ne_zero (α := ℝ))
  have h2 : HasDerivAt (fun μ : ℝ => μ ^ 2 - 1) (2 * 1) 1 := by
    simpa using (hasDerivAt_pow 2 (1 : ℝ)).sub_const 1
  have h := h1.sub (h2.const_mul ((θ - 1) / (2 * θ)))
  convert h using 1
  · funext y; simp only [equiGain, Pi.sub_apply]
  · field_simp; ring

/-- **Real balances in the equiproportionate shock** (O&R p. 683 "real balances must rise in the
short run"; fn 19): at the equilibrium `M₁/P₁ = μ M₀/P₀` (up for `μ > 1`) and
`M₂/P₂ = M₀/P₀` (unchanged from date 2). -/
theorem equiproportionate_real_balances {P0 M0 μ : ℝ} (hP0 : 0 < P0) (hμ : 0 < μ) :
    μ * M0 / P0 = μ * (M0 / P0) ∧ μ * M0 / (μ * P0) = M0 / P0 := by
  refine ⟨by ring, ?_⟩
  field_simp

end ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks
