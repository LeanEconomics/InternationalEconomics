/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import SmallOpenEconomyDynamics.FundamentalCurrentAccount
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Trend productivity growth and the debt–output ratio

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*,
Appendix 2A, pp. 116–120, and Supplement B (steady-state condition), pp. 722–726.

Output is `Y = A K^α` with `0 < α < 1` and productivity growing so that output
grows at rate `g`, with `0 < g < r`. Investment is `I = (αg/r)Y` and government
spending is `G = ςY`, so net output `Y − I − G = nY` with
`n = 1 − αg/r − ς`. Consumption grows at the gross rate
`γ = (1 + r)^σ β^σ = 1 − ϑ`.

* **The current account (2.74)**: `CA_t = −ϑB_t − ((g + ϑ)/(r − g)) n Y_t`, from the
  tilted fundamental equation (2.20).
* **The debt–output ratio (2.75)** `b = B/Y` obeys the linear difference equation
  `b_{s+1} = (γ/(1 + g)) b_s − ((1 + g − γ)/((1 + g)(r − g))) n`. Its fixed point is
  **(2.76)** `b̄ = −n/(r − g)`. The ratio converges to `b̄` if `γ < 1 + g` and diverges
  from it if `γ > 1 + g`.
* **Below `b̄` consumption would be negative** (p. 119): `C/Y = (r + ϑ)(b − b̄)`.
* **The book's numbers** (p. 119): `r = 0.08`, `g = 0.05`, `α = 0.4`, `ς = 0.3` give
  `b̄ = −15` and a steady-state trade surplus of 45 percent of GDP.
* **The world interest rate (2.77)** `1 + r = (1 + g*)^{1/σ}/β` in a world growing at
  `g*`. With `β = 0.96`, `σ = 1`, `r = 0.08`, this gives `g* = 0.0368`. A fraction
  `(g − g*)/(1 + g) ≈ 1.26%` of the gap to `b̄` closes each year, and the half-life
  is 55 years (p. 120).
* **Supplement B**: with an endogenous discount factor `β(C)`, a steady state
  requires `β(C̄)(1 + r) = 1`. With constant `β` this forces `β(1 + r) = 1`.
-/

namespace ObstfeldRogoff.SmallOpenEconomyDynamics.TrendGrowth

open PresentValue FundamentalCurrentAccount Filter Topology

/-! ### Technology (O&R pp. 116–117) -/

/-- With the marginal product of capital equal to `r`, `αY = rK`: the capital–output ratio is
`α/r` (O&R p. 116). -/
theorem capital_output {α A K r : ℝ} (hK : 0 < K) (hmpk : α * A * K ^ (α - 1) = r) :
    α * (A * K ^ α) = r * K := by
  rw [← hmpk, Real.rpow_sub hK, Real.rpow_one]
  field_simp

/-- **Investment is a constant share of output**, O&R p. 117: if capital grows at rate `g`
(`K_{s+1} = (1 + g)K_s`) and `αY_s = rK_s`, then `I_s = K_{s+1} − K_s = (αg/r)Y_s`. -/
theorem investment_share {α g r K K' Y : ℝ} (hr : r ≠ 0) (hK' : K' = (1 + g) * K)
    (hY : α * Y = r * K) : K' - K = α * g / r * Y := by
  rw [hK', show α * g / r * Y = g * (α * Y) / r by ring, hY]
  field_simp
  ring

/-- **Capital grows at the rate of output growth**: if `αA_sK_s^{α−1} = r` at both dates and
`A_{s+1} = (1 + g)^{1−α}A_s`, then `K_{s+1} = (1 + g)K_s` (O&R p. 116). -/
theorem capital_growth {α g r A A' K K' : ℝ} (hα : α < 1) (hg : -1 < g) (hK : 0 < K)
    (hK' : 0 < K') (hA : 0 < A) (hαpos : 0 < α) (hmpk : α * A * K ^ (α - 1) = r)
    (hmpk' : α * A' * K' ^ (α - 1) = r) (hA' : A' = (1 + g) ^ (1 - α) * A) :
    K' = (1 + g) * K := by
  have h1g : 0 < 1 + g := by linarith
  have hne : α - 1 ≠ 0 := by linarith
  -- both sides have the same (α − 1)-th power
  have e : K' ^ (α - 1) = ((1 + g) * K) ^ (α - 1) := by
    rw [Real.mul_rpow h1g.le hK.le]
    have hpow : (1 + g) ^ (α - 1) * (1 + g) ^ (1 - α) = 1 := by
      rw [← Real.rpow_add h1g, show α - 1 + (1 - α) = 0 by ring, Real.rpow_zero]
    have h2 : α * A * ((1 + g) ^ (1 - α) * K' ^ (α - 1)) = α * A * K ^ (α - 1) := by
      rw [hmpk, ← hmpk', hA']; ring
    have h3 : (1 + g) ^ (1 - α) * K' ^ (α - 1) = K ^ (α - 1) := by
      have hαA : α * A ≠ 0 := (mul_pos hαpos hA).ne'
      exact mul_left_cancel₀ hαA (by linarith [h2])
    calc K' ^ (α - 1) = (1 + g) ^ (α - 1) * ((1 + g) ^ (1 - α) * K' ^ (α - 1)) := by
          rw [← mul_assoc, hpow, one_mul]
      _ = (1 + g) ^ (α - 1) * K ^ (α - 1) := by rw [h3]
  have := congrArg (fun x : ℝ => x ^ (α - 1)⁻¹) e
  rwa [← Real.rpow_mul hK'.le, ← Real.rpow_mul (mul_pos h1g hK).le, mul_inv_cancel₀ hne,
    Real.rpow_one, Real.rpow_one] at this

/-! ### The current account and the debt–output ratio -/

/-- **The current account with trend growth**, O&R (2.74), p. 117. Output grows at rate `g < r`,
investment is `(αg/r)Y` and government spending `ςY`. If consumption follows the tilted rule
(2.16), then `CA₀ = −ϑB₀ − ((g + ϑ)/(r − g)) (1 − αg/r − ς) Y₀`. -/
theorem current_account_trend {r g α ς ϑ B0 Y0 C0 : ℝ} (hr : 0 < r) (hg : -1 < g) (hgr : g < r)
    (hC : C0 = (r + ϑ) / (1 + r) *
      wealth r B0 (fun s => (1 + g) ^ s * Y0) (fun s => ς * ((1 + g) ^ s * Y0))
        (fun s => α * g / r * ((1 + g) ^ s * Y0))) :
    currentAccount r B0 C0 (fun s => (1 + g) ^ s * Y0) (fun s => ς * ((1 + g) ^ s * Y0))
        (fun s => α * g / r * ((1 + g) ^ s * Y0)) =
      -ϑ * B0 - (g + ϑ) / (r - g) * (1 - α * g / r - ς) * Y0 := by
  have hr1 : (1 : ℝ) + r ≠ 0 := by linarith
  have hrg : r - g ≠ 0 := by linarith
  have hrne : r ≠ 0 := hr.ne'
  have hnet : (fun s : ℕ => (1 + g) ^ s * Y0 - ς * ((1 + g) ^ s * Y0) -
      α * g / r * ((1 + g) ^ s * Y0)) = fun s => (1 + g) ^ s * ((1 - α * g / r - ς) * Y0) := by
    funext s; ring
  have hW : wealth r B0 (fun s => (1 + g) ^ s * Y0) (fun s => ς * ((1 + g) ^ s * Y0))
      (fun s => α * g / r * ((1 + g) ^ s * Y0)) =
      (1 + r) * B0 + (1 + r) / (r - g) * ((1 - α * g / r - ς) * Y0) := by
    unfold wealth
    rw [hnet, pv_geometric hg hgr]
  unfold currentAccount
  rw [hC, hW]
  simp only [pow_zero, one_mul]
  field_simp
  ring

/-- **The debt–output ratio difference equation**, O&R (2.75), p. 117: if at every date
`B_{s+1} − B_s = −ϑB_s − ((g + ϑ)/(r − g)) n Y_s` (eq. (2.74) applied at date `s`) and
`Y_{s+1} = (1 + g)Y_s`, then with `γ = 1 − ϑ`,
`B_{s+1}/Y_{s+1} = (γ/(1 + g)) B_s/Y_s − ((1 + g − γ)/((1 + g)(r − g))) n`. -/
theorem debt_ratio_recursion {r g ϑ n : ℝ} (hg : -1 < g) (hgr : g < r) {B Y : ℕ → ℝ}
    (hY0 : ∀ s, 0 < Y s) (hY : ∀ s, Y (s + 1) = (1 + g) * Y s)
    (hCA : ∀ s, B (s + 1) - B s = -ϑ * B s - (g + ϑ) / (r - g) * n * Y s) (s : ℕ) :
    B (s + 1) / Y (s + 1) =
      (1 - ϑ) / (1 + g) * (B s / Y s) - (1 + g - (1 - ϑ)) / ((1 + g) * (r - g)) * n := by
  have h1g : (1 : ℝ) + g ≠ 0 := by linarith
  have hrg : r - g ≠ 0 := by linarith
  have hYs := (hY0 s).ne'
  have hB : B (s + 1) = (1 - ϑ) * B s - (g + ϑ) / (r - g) * n * Y s := by linarith [hCA s]
  rw [hB, hY s]
  field_simp
  ring

/-- **The steady-state debt–output ratio**, O&R (2.76), p. 117: `b̄ = −(1 − ς − αg/r)/(r − g)` is a
fixed point of (2.75), and the only one when `γ ≠ 1 + g`. -/
theorem steady_debt_ratio {r g γ n b : ℝ} (hg : -1 < g) (hgr : g < r) (hγ : γ ≠ 1 + g) :
    b = γ / (1 + g) * b - (1 + g - γ) / ((1 + g) * (r - g)) * n ↔ b = -n / (r - g) := by
  have h1g : (1 : ℝ) + g ≠ 0 := by linarith
  have hrg : r - g ≠ 0 := by linarith
  have hγ' : 1 + g - γ ≠ 0 := sub_ne_zero.2 (Ne.symm hγ)
  constructor
  · intro h
    field_simp at h ⊢
    have : (1 + g - γ) * (b * (r - g) + n) = 0 := by linear_combination h
    have := (mul_eq_zero.1 this).resolve_left hγ'
    linarith
  · intro h
    rw [h]
    field_simp
    ring

/-- **Deviations from the steady state decay geometrically**: if `b` obeys (2.75), then
`b_s − b̄ = (γ/(1 + g))^s (b₀ − b̄)` (O&R p. 120 and Figure 2.12). -/
theorem debt_ratio_deviation {r g γ n : ℝ} (hg : -1 < g) (hgr : g < r) {b : ℕ → ℝ}
    (hb : ∀ s, b (s + 1) = γ / (1 + g) * b s - (1 + g - γ) / ((1 + g) * (r - g)) * n)
    (s : ℕ) : b s - (-n / (r - g)) = (γ / (1 + g)) ^ s * (b 0 - (-n / (r - g))) := by
  have h1g : (1 : ℝ) + g ≠ 0 := by linarith
  have hrg : r - g ≠ 0 := by linarith
  induction s with
  | zero => simp
  | succ s ih =>
    rw [hb s, pow_succ]
    have e : γ / (1 + g) * b s - (1 + g - γ) / ((1 + g) * (r - g)) * n - -n / (r - g) =
        γ / (1 + g) * (b s - -n / (r - g)) := by
      field_simp
      ring
    rw [e, ih]
    ring

/-- **Stability** (O&R p. 117): if `0 ≤ γ < 1 + g`, the debt–output ratio converges to `b̄` from
any initial value. -/
theorem debt_ratio_tendsto {r g γ n : ℝ} (hg : -1 < g) (hgr : g < r) (hγ0 : 0 ≤ γ)
    (hγ : γ < 1 + g) {b : ℕ → ℝ}
    (hb : ∀ s, b (s + 1) = γ / (1 + g) * b s - (1 + g - γ) / ((1 + g) * (r - g)) * n) :
    Tendsto b atTop (𝓝 (-n / (r - g))) := by
  have h1g : (0 : ℝ) < 1 + g := by linarith
  have hq0 : 0 ≤ γ / (1 + g) := div_nonneg hγ0 h1g.le
  have hq1 : γ / (1 + g) < 1 := (div_lt_one h1g).2 hγ
  have hdev : Tendsto (fun s => (γ / (1 + g)) ^ s * (b 0 - -n / (r - g))) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const (b 0 - -n / (r - g))
  have e : b = fun s => -n / (r - g) + (γ / (1 + g)) ^ s * (b 0 - -n / (r - g)) := by
    funext s
    linarith [debt_ratio_deviation hg hgr hb s]
  rw [e]
  simpa using tendsto_const_nhds.add hdev

/-- **Instability** (O&R p. 119): if `γ > 1 + g`, any initial ratio other than `b̄` diverges from
it. -/
theorem debt_ratio_diverges {r g γ n : ℝ} (hg : -1 < g) (hgr : g < r) (hγ : 1 + g < γ)
    {b : ℕ → ℝ}
    (hb : ∀ s, b (s + 1) = γ / (1 + g) * b s - (1 + g - γ) / ((1 + g) * (r - g)) * n)
    (h0 : b 0 ≠ -n / (r - g)) :
    Tendsto (fun s => |b s - (-n / (r - g))|) atTop atTop := by
  have h1g : (0 : ℝ) < 1 + g := by linarith
  have hq1 : 1 < γ / (1 + g) := (one_lt_div h1g).2 hγ
  have hd : 0 < |b 0 - -n / (r - g)| := abs_pos.2 (sub_ne_zero.2 h0)
  have e : (fun s => |b s - (-n / (r - g))|) =
      fun s => (γ / (1 + g)) ^ s * |b 0 - -n / (r - g)| := by
    funext s
    rw [debt_ratio_deviation hg hgr hb s, abs_mul, abs_pow,
      abs_of_pos (by linarith : (0 : ℝ) < γ / (1 + g))]
  rw [e]
  exact (tendsto_pow_atTop_atTop_of_one_lt hq1).atTop_mul_const hd

/-- **Knife edge** (O&R p. 119): if `γ = 1 + g`, the debt–output ratio stays at its initial
value. -/
theorem debt_ratio_constant {r g n : ℝ} (hg : -1 < g) {b : ℕ → ℝ}
    (hb : ∀ s, b (s + 1) = (1 + g) / (1 + g) * b s -
      (1 + g - (1 + g)) / ((1 + g) * (r - g)) * n) (s : ℕ) : b s = b 0 := by
  have h1g : (1 : ℝ) + g ≠ 0 := by linarith
  induction s with
  | zero => rfl
  | succ s ih => rw [hb s, div_self h1g, sub_self, zero_div, zero_mul, sub_zero, one_mul, ih]

/-- **Consumption–output ratio**, O&R p. 118: under (2.16) with net output `nY` growing at `g`,
`C/Y = (r + ϑ)[B/Y + n/(r − g)] = (r + ϑ)(b − b̄)`. -/
theorem consumption_output_ratio {r g α ς ϑ B0 Y0 C0 : ℝ} (hr : 0 < r) (hg : -1 < g)
    (hgr : g < r) (hY0 : 0 < Y0)
    (hC : C0 = (r + ϑ) / (1 + r) *
      wealth r B0 (fun s => (1 + g) ^ s * Y0) (fun s => ς * ((1 + g) ^ s * Y0))
        (fun s => α * g / r * ((1 + g) ^ s * Y0))) :
    C0 / Y0 = (r + ϑ) * (B0 / Y0 - (-(1 - α * g / r - ς) / (r - g))) := by
  have hr1 : (1 : ℝ) + r ≠ 0 := by linarith
  have hrg : r - g ≠ 0 := by linarith
  have hnet : (fun s : ℕ => (1 + g) ^ s * Y0 - ς * ((1 + g) ^ s * Y0) -
      α * g / r * ((1 + g) ^ s * Y0)) = fun s => (1 + g) ^ s * ((1 - α * g / r - ς) * Y0) := by
    funext s; ring
  rw [hC]
  unfold wealth
  rw [hnet, pv_geometric hg hgr]
  have := hY0.ne'
  field_simp
  ring

/-- **Debt below `b̄` is infeasible**, O&R p. 119: if `r + ϑ > 0` (i.e. `γ < 1 + r`), an
asset–output ratio below `b̄` would require negative consumption. -/
theorem consumption_neg_below_steady {r g α ς ϑ B0 Y0 C0 : ℝ} (hr : 0 < r) (hg : -1 < g)
    (hgr : g < r) (hY0 : 0 < Y0) (hrϑ : 0 < r + ϑ)
    (hC : C0 = (r + ϑ) / (1 + r) *
      wealth r B0 (fun s => (1 + g) ^ s * Y0) (fun s => ς * ((1 + g) ^ s * Y0))
        (fun s => α * g / r * ((1 + g) ^ s * Y0)))
    (hbelow : B0 / Y0 < -(1 - α * g / r - ς) / (r - g)) : C0 < 0 := by
  have h := consumption_output_ratio hr hg hgr hY0 hC
  have hneg : C0 / Y0 < 0 := by rw [h]; exact mul_neg_of_pos_of_neg hrϑ (by linarith)
  by_contra hc
  push Not at hc
  linarith [div_nonneg hc hY0.le]

/-- The steady-state ratio is minus the present value of net output relative to current output:
`−b̄ = (1/((1 + r)Y_t)) Σ ((1 + g)/(1 + r))^{s−t} n Y_t = n/(r − g)` (O&R p. 118). -/
theorem steady_ratio_eq_pv {r g n Y0 : ℝ} (hg : -1 < g) (hgr : g < r) (hY0 : 0 < Y0) :
    pv r (fun s => (1 + g) ^ s * (n * Y0)) / ((1 + r) * Y0) = n / (r - g) := by
  rw [pv_geometric hg hgr]
  have : (1 : ℝ) + r ≠ 0 := by linarith
  have : r - g ≠ 0 := by linarith
  have := hY0.ne'
  field_simp

/-- **The consumption–output ratio vanishes** (O&R p. 118): if consumption grows at gross rate
`γ < 1 + g`, then `C_s/Y_s → 0`. -/
theorem consumption_output_tendsto_zero {g γ C0 Y0 : ℝ} (hg : -1 < g) (hγ0 : 0 ≤ γ)
    (hγ : γ < 1 + g) (hY0 : 0 < Y0) :
    Tendsto (fun s : ℕ => γ ^ s * C0 / ((1 + g) ^ s * Y0)) atTop (𝓝 0) := by
  have h1g : (0 : ℝ) < 1 + g := by linarith
  have hq0 : 0 ≤ γ / (1 + g) := div_nonneg hγ0 h1g.le
  have hq1 : γ / (1 + g) < 1 := (div_lt_one h1g).2 hγ
  have e : (fun s : ℕ => γ ^ s * C0 / ((1 + g) ^ s * Y0)) =
      fun s => (γ / (1 + g)) ^ s * (C0 / Y0) := by
    funext s
    rw [div_pow]
    have := hY0.ne'
    have : (1 + g) ^ s ≠ 0 := pow_ne_zero _ h1g.ne'
    field_simp
  rw [e]
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).mul_const (C0 / Y0)

/-! ### The book's numbers (O&R pp. 119–120) -/

/-- **The steady-state debt–output ratio is −15**, O&R p. 119: `r = 0.08`, `g = 0.05`, `α = 0.4`,
`ς = 0.3`. -/
theorem numerical_steady_ratio :
    -(1 - (0.4 : ℝ) * 0.05 / 0.08 - 0.3) / (0.08 - 0.05) = -15 := by norm_num

/-- **The steady-state trade surplus is 45 percent of GDP**, O&R p. 119: `TB/Y = −(r − g) b̄`. -/
theorem numerical_trade_surplus : -((0.08 : ℝ) - 0.05) * (-15) = 0.45 := by norm_num

/-- In a steady state with a constant asset–output ratio, `CA = gB` and the trade balance is
`TB = CA − rB = −(r − g)B` (O&R p. 119). -/
theorem steady_trade_balance {r g B : ℝ} : g * B - r * B = -(r - g) * B := by ring

/-- **The world interest rate**, O&R (2.77), p. 119: if the world is a closed economy growing at
`g*`, consumption grows at the rate of output, `(1 + r)^σ β^σ = 1 + g*`, so
`1 + r = (1 + g*)^{1/σ}/β`. -/
theorem world_interest_rate {r β σ gs : ℝ} (hr : 0 < 1 + r) (hβ : 0 < β) (hσ : 0 < σ)
    (h : (1 + r) ^ σ * β ^ σ = 1 + gs) :
    1 + r = (1 + gs) ^ (1 / σ) / β := by
  rw [← h, ← Real.mul_rpow hr.le hβ.le, ← Real.rpow_mul (mul_pos hr hβ).le,
    mul_one_div_cancel hσ.ne', Real.rpow_one]
  field_simp

/-- **World growth `g* = 3.68%`**, O&R p. 119: with `β = 0.96`, `σ = 1` and `r = 0.08`,
`1 + g* = β(1 + r)`. -/
theorem numerical_world_growth : (0.96 : ℝ) * (1 + 0.08) - 1 = 0.0368 := by norm_num

/-- **Convergence at the world growth rate**, O&R p. 120: with `γ = 1 + g*`, each period closes the
fraction `1 − (1 + g*)/(1 + g) = (g − g*)/(1 + g)` of the gap to `b̄`. -/
theorem fraction_closed {g gs : ℝ} (hg : -1 < g) : 1 - (1 + gs) / (1 + g) = (g - gs) / (1 + g) := by
  have : (1 : ℝ) + g ≠ 0 := by linarith
  field_simp
  ring

/-- **1.26 percent a year**, O&R p. 120: with `g = 0.05` and `g* = 0.0368` the fraction closed each
year is `0.0132/1.05 ≈ 0.01257`. -/
theorem numerical_fraction_closed :
    (0.0125 : ℝ) < (0.05 - 0.0368) / (1 + 0.05) ∧
      ((0.05 : ℝ) - 0.0368) / (1 + 0.05) < 0.0126 := by
  constructor
  · rw [lt_div_iff₀ (by norm_num)]; norm_num
  · rw [div_lt_iff₀ (by norm_num)]; norm_num

/-- **A half-life of 55 years**, O&R p. 120: after 54 years more than half the gap remains, after 55
years less than half. -/
theorem numerical_half_life :
    (1 / 2 : ℝ) < ((1 + 0.0368) / (1 + 0.05)) ^ 54 ∧
      ((1 + 0.0368) / (1 + 0.05)) ^ 55 < (1 / 2 : ℝ) := by
  norm_num

/-! ### Supplement B: endogenous discounting (O&R pp. 722–726) -/

/-- **The Uzawa steady-state condition**, O&R SB(3)–(4), p. 724: if the marginal value of wealth
obeys `J'(W_t) = β(C_t)(1 + r) J'(W_{t+1})` and wealth is constant with `J'(W̄) ≠ 0`, then
`β(C̄)(1 + r) = 1`. -/
theorem uzawa_steady_state {βC r dJ : ℝ} (hdJ : dJ ≠ 0) (h : dJ = βC * (1 + r) * dJ) :
    βC * (1 + r) = 1 := by
  have : (βC * (1 + r) - 1) * dJ = 0 := by linarith
  have := (mul_eq_zero.1 this).resolve_right hdJ
  linarith

end ObstfeldRogoff.SmallOpenEconomyDynamics.TrendGrowth
