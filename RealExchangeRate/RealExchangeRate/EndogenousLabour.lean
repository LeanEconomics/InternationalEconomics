/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RealExchangeRate.ConsumptionDynamics

/-!
# Endogenous labour supply: leisure as a nontraded good

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, Appendix 4A
(pp. 258–260, eqs. (67)–(68)) and Exercise 5 (p. 265).

Leisure `L̄ − L` plays the role of the nontraded good, with the wage `w` (in tradables) as its
price, so the CES price index is `P = [γ + (1−γ) w^{1−θ}]^{1/(1−θ)}`. We prove:

* `w^{1−θ} = (P^{1−θ} − γ)/(1−γ)` and the leisure demand `L̄ − L = C_T ((1−γ)/γ) w^{−θ}` implied
  by (22);
* the rewritten labour income `wL − G_T = wL̄ − (P^{1−θ}/γ − 1) C_T − G_T`;
* (67): solving the tradables budget with endogenous labour supply and the Euler equation (34)
  gives `C_{T,t} = γ P_t^θ C_t` with `C_t` the consumption function (29) evaluated at full income
  `wL̄ − G_T`, i.e. (67) is (22); and the form (68);
* Exercise 5: the same formula (67) derived instead from (29), (22) and (33).
-/

namespace ObstfeldRogoff.RealExchangeRate.EndogenousLabour

open Real Filter Topology
open ObstfeldRogoff.RealExchangeRate.CESIndex ObstfeldRogoff.RealExchangeRate.ConsumptionDynamics

/-- Appendix 4A, O&R p. 258: with leisure priced at the wage, the price index
`P = [γ + (1−γ) w^{1−θ}]^{1/(1−θ)}` satisfies `w^{1−θ} = (P^{1−θ} − γ)/(1−γ)`. -/
theorem wage_rpow_eq {γ θ w : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hθ1 : θ ≠ 1) (hw : 0 < w) :
    w ^ (1 - θ) = (cesPrice γ θ w ^ (1 - θ) - γ) / (1 - γ) := by
  rw [cesPrice_rpow_one_sub hγ0 hγ1 hw hθ1]
  have : (1 - γ) ≠ 0 := by linarith
  field_simp
  ring

/-- Appendix 4A, O&R p. 258: the implication of (22) for leisure. If `C_T = γ P^θ C` and
leisure demand is `L̄ − L = (1−γ)(w/P)^{−θ} C`, then `L̄ − L = C_T ((1−γ)/γ) w^{−θ}`. -/
theorem leisure_demand {γ θ w P C CT Lbar L : ℝ} (hγ0 : 0 < γ) (hw : 0 < w) (hP : 0 < P)
    (h22T : CT = γ * P ^ θ * C) (h22N : Lbar - L = (1 - γ) * (w / P) ^ (-θ) * C) :
    Lbar - L = CT * ((1 - γ) / γ) * w ^ (-θ) := by
  rw [h22N, h22T, div_rpow hw.le hP.le, rpow_neg hP.le, rpow_neg hw.le]
  have := rpow_pos_of_pos hP θ
  have := rpow_pos_of_pos hw θ
  field_simp

/-- Appendix 4A, O&R p. 258: using the leisure demand and `w^{1−θ} = (P^{1−θ} − γ)/(1−γ)`,
labour income net of government spending is `wL − G_T = wL̄ − (P^{1−θ}/γ − 1) C_T − G_T`. -/
theorem labour_income_rewrite {γ θ w CT Lbar L GT : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hθ1 : θ ≠ 1) (hw : 0 < w) (hleis : Lbar - L = CT * ((1 - γ) / γ) * w ^ (-θ)) :
    w * L - GT = w * Lbar - (cesPrice γ θ w ^ (1 - θ) / γ - 1) * CT - GT := by
  have hww : w * w ^ (-θ) = w ^ (1 - θ) := by
    rw [sub_eq_add_neg, rpow_add hw, rpow_one]
  have hL : w * L = w * Lbar - CT * ((1 - γ) / γ) * (w * w ^ (-θ)) := by
    have : L = Lbar - CT * ((1 - γ) / γ) * w ^ (-θ) := by linarith
    rw [this]; ring
  rw [hL, hww, wage_rpow_eq hγ0 hγ1 hθ1 hw]
  have : (1 - γ) ≠ 0 := by linarith
  field_simp

/-- Appendix 4A, eq. (67), O&R pp. 258–259: with leisure as the nontraded good, the tradables
budget `∑ (1+r)^{−(s−t)} C_{T,s} = (1+r)Q_t + ∑ (1+r)^{−(s−t)}(w_sL_s − G_{T,s})`, the leisure
demand implied by (22), the Euler equation (34) and `P_s = [γ + (1−γ)w_s^{1−θ}]^{1/(1−θ)}` give
`C_{T,t} = γ P_t^θ · [(1+r)Q_t + ∑ (1+r)^{−(s−t)}(w_sL̄ − G_{T,s})] /
(P_t ∑ [(1+r)^{s−t} P_t/P_s]^{σ−1} β^{σ(s−t)})`, i.e. `γ P_t^θ C_t` with `C_t` the consumption
function (29) at full income `wL̄ − G_T`: (67) is the same as (22). -/
theorem tradables_consumption_67 {γ θ σ β r Q Lbar : ℝ} {w L GT CT P : ℕ → ℝ}
    (hγ0 : 0 < γ) (hγ1 : γ < 1) (hθ1 : θ ≠ 1) (hr : 0 < 1 + r) (hβ : 0 < β)
    (hw : ∀ s, 0 < w s) (hPdef : ∀ s, P s = cesPrice γ θ (w s))
    (hleis : ∀ s, Lbar - L s = CT s * ((1 - γ) / γ) * w s ^ (-θ))
    (h34 : ∀ s, CT (s + 1) = (P s / P (s + 1)) ^ (σ - θ) * ((1 + r) ^ σ * β ^ σ) * CT s)
    (hCT : Summable fun s => ((1 + r)⁻¹) ^ s * CT s)
    (hY : Summable fun s => ((1 + r)⁻¹) ^ s * (w s * L s - GT s))
    (hYbar : Summable fun s => ((1 + r)⁻¹) ^ s * (w s * Lbar - GT s))
    (hD : Summable fun n => ((1 + r) ^ n * (P 0 / P n)) ^ (σ - 1) * (β ^ σ) ^ n)
    (hbud : ∑' s, ((1 + r)⁻¹) ^ s * CT s
      = (1 + r) * Q + ∑' s, ((1 + r)⁻¹) ^ s * (w s * L s - GT s)) :
    CT 0 = γ * P 0 ^ θ * (((1 + r) * Q + ∑' s, ((1 + r)⁻¹) ^ s * (w s * Lbar - GT s))
      / (P 0 * ∑' n, ((1 + r) ^ n * (P 0 / P n)) ^ (σ - 1) * (β ^ σ) ^ n)) := by
  have hP : ∀ s, 0 < P s := fun s => by rw [hPdef]; exact cesPrice_pos hγ0 hγ1 (hw s)
  have hrw : ∀ s, w s * L s - GT s
      = (w s * Lbar - GT s) - (P s ^ (1 - θ) / γ - 1) * CT s := by
    intro s
    rw [hPdef, labour_income_rewrite hγ0 hγ1 hθ1 (hw s) (hleis s)]
    ring
  -- the budget with leisure valued at the wage
  have eA : (fun s => ((1 + r)⁻¹) ^ s * (P s ^ (1 - θ) / γ * CT s))
      = fun s => ((1 + r)⁻¹) ^ s * CT s + ((1 + r)⁻¹) ^ s * (w s * Lbar - GT s)
          - ((1 + r)⁻¹) ^ s * (w s * L s - GT s) := by
    funext s
    rw [hrw s]
    ring
  have hA : ∑' s, ((1 + r)⁻¹) ^ s * (P s ^ (1 - θ) / γ * CT s)
      = (1 + r) * Q + ∑' s, ((1 + r)⁻¹) ^ s * (w s * Lbar - GT s) := by
    rw [eA, (hCT.add hYbar).tsum_sub hY, hCT.tsum_add hYbar, hbud]
    ring
  -- each term of the left side, using the Euler equation (34)
  have hpath := tradables_consumption_path hP h34
  have hterm : ∀ n, ((1 + r)⁻¹) ^ n * (P n ^ (1 - θ) / γ * CT n)
      = P 0 ^ (1 - θ) / γ * (((1 + r) ^ n * (P 0 / P n)) ^ (σ - 1) * (β ^ σ) ^ n) * CT 0 := by
    intro n
    have h0 := hP 0
    have hn := hP n
    have hu : 0 < P 0 / P n := div_pos h0 hn
    have ha : 0 < (1 + r) ^ n := pow_pos hr n
    have e1 : P n ^ (1 - θ) = P 0 ^ (1 - θ) / (P 0 / P n) ^ (1 - θ) := by
      rw [div_rpow h0.le hn.le]
      have := rpow_pos_of_pos h0 (1 - θ)
      have := rpow_pos_of_pos hn (1 - θ)
      field_simp
    have e2 : (P 0 / P n) ^ (σ - 1) = (P 0 / P n) ^ (σ - θ) / (P 0 / P n) ^ (1 - θ) := by
      rw [← rpow_sub hu]; ring_nf
    have e3 : ((1 + r) ^ n * (P 0 / P n)) ^ (σ - 1)
        = ((1 + r) ^ n) ^ σ / (1 + r) ^ n * (P 0 / P n) ^ (σ - 1) := by
      rw [mul_rpow ha.le hu.le, rpow_sub_one ha.ne']
    have e4 : ((1 + r) ^ σ * β ^ σ) ^ n = ((1 + r) ^ n) ^ σ * (β ^ σ) ^ n := by
      rw [mul_pow, rpow_pow_comm hr.le]
    rw [hpath n, e1, e3, e2, e4, inv_pow]
    have := rpow_pos_of_pos hu (1 - θ)
    field_simp
  have hden : 0 < ∑' n, ((1 + r) ^ n * (P 0 / P n)) ^ (σ - 1) * (β ^ σ) ^ n := by
    refine hD.tsum_pos (fun n => ?_) 0 ?_
    · have := hP n; have := hP 0; positivity
    · have := hP 0; positivity
  rw [tsum_congr hterm, tsum_mul_right, tsum_mul_left] at hA
  rw [← hA]
  set D := ∑' n, ((1 + r) ^ n * (P 0 / P n)) ^ (σ - 1) * (β ^ σ) ^ n with hDdef
  have h0 := hP 0
  have e5 : P 0 ^ (1 - θ) = P 0 / P 0 ^ θ := by rw [rpow_sub h0, rpow_one]
  rw [e5]
  have := rpow_pos_of_pos h0 θ
  field_simp

/-- Appendix 4A, eq. (68), O&R p. 259: with the wage given by the factor-price frontier
`w_s = w(r, A_s)` and `P_s = P[w(r, A_s)]`, equilibrium tradables consumption is
`C_{T,t} = γ {1/P[w(r,A_t)]}^{1−θ} [(1+r)Q_t + ∑ (1+r)^{−(s−t)}(w(r,A_s)L̄ − G_{T,s})] /
∑ {(1+r)^{s−t} P[w(r,A_t)]/P[w(r,A_s)]}^{σ−1} β^{σ(s−t)}`. -/
theorem tradables_consumption_68 {γ θ σ β r Q Lbar : ℝ} {wf : ℝ → ℝ → ℝ}
    {A L GT CT P : ℕ → ℝ}
    (hγ0 : 0 < γ) (hγ1 : γ < 1) (hθ1 : θ ≠ 1) (hr : 0 < 1 + r) (hβ : 0 < β)
    (hw : ∀ s, 0 < wf r (A s)) (hPdef : ∀ s, P s = cesPrice γ θ (wf r (A s)))
    (hleis : ∀ s, Lbar - L s = CT s * ((1 - γ) / γ) * wf r (A s) ^ (-θ))
    (h34 : ∀ s, CT (s + 1) = (P s / P (s + 1)) ^ (σ - θ) * ((1 + r) ^ σ * β ^ σ) * CT s)
    (hCT : Summable fun s => ((1 + r)⁻¹) ^ s * CT s)
    (hY : Summable fun s => ((1 + r)⁻¹) ^ s * (wf r (A s) * L s - GT s))
    (hYbar : Summable fun s => ((1 + r)⁻¹) ^ s * (wf r (A s) * Lbar - GT s))
    (hD : Summable fun n => ((1 + r) ^ n * (P 0 / P n)) ^ (σ - 1) * (β ^ σ) ^ n)
    (hbud : ∑' s, ((1 + r)⁻¹) ^ s * CT s
      = (1 + r) * Q + ∑' s, ((1 + r)⁻¹) ^ s * (wf r (A s) * L s - GT s)) :
    CT 0 = γ * (1 / P 0) ^ (1 - θ)
      * (((1 + r) * Q + ∑' s, ((1 + r)⁻¹) ^ s * (wf r (A s) * Lbar - GT s))
        / ∑' n, ((1 + r) ^ n * (P 0 / P n)) ^ (σ - 1) * (β ^ σ) ^ n) := by
  rw [tradables_consumption_67 (w := fun s => wf r (A s)) hγ0 hγ1 hθ1 hr hβ hw hPdef hleis h34
    hCT hY hYbar hD hbud]
  have h0 : 0 < P 0 := by rw [hPdef]; exact cesPrice_pos hγ0 hγ1 (hw 0)
  set W := (1 + r) * Q + ∑' s, ((1 + r)⁻¹) ^ s * (wf r (A s) * Lbar - GT s) with hWdef
  set D := ∑' n, ((1 + r) ^ n * (P 0 / P n)) ^ (σ - 1) * (β ^ σ) ^ n with hDdef
  rw [one_div, inv_rpow h0.le, ← rpow_neg h0.le, neg_sub, rpow_sub_one h0.ne']
  field_simp

/-- Exercise 5, O&R p. 265: an alternative derivation of (67) from (29), (22) and (33). With
spending `P_sC_s = C_{T,s} + w_s(L̄ − L_s)` (leisure bought at the wage), the tradables budget
becomes the real-consumption budget (24) at full income `w_sL̄ − G_{T,s}`; the isoelastic Euler
equation (33) then gives `C_t` by (29), and (22) gives `C_{T,t} = γ P_t^θ C_t`, which is (67). -/
theorem exercise5_tradables_consumption {γ θ σ β r Q Lbar : ℝ} {w L GT CT C P : ℕ → ℝ}
    (hr : 0 < 1 + r) (hβ : 0 < β) (hP : ∀ s, 0 < P s)
    (hPC : ∀ s, P s * C s = CT s + w s * (Lbar - L s))
    (hE : ∀ s, C (s + 1) = grossRealRate r P s ^ σ * β ^ σ * C s)
    (h22 : ∀ s, CT s = γ * P s ^ θ * C s)
    (hCT : Summable fun s => ((1 + r)⁻¹) ^ s * CT s)
    (hY : Summable fun s => ((1 + r)⁻¹) ^ s * (w s * L s - GT s))
    (hYbar : Summable fun s => ((1 + r)⁻¹) ^ s * (w s * Lbar - GT s))
    (hD : Summable fun n => ((1 + r) ^ n * (P 0 / P n)) ^ (σ - 1) * (β ^ σ) ^ n)
    (hbud : ∑' s, ((1 + r)⁻¹) ^ s * CT s
      = (1 + r) * Q + ∑' s, ((1 + r)⁻¹) ^ s * (w s * L s - GT s)) :
    CT 0 = γ * P 0 ^ θ * (((1 + r) * Q + ∑' s, ((1 + r)⁻¹) ^ s * (w s * Lbar - GT s))
      / (P 0 * ∑' n, ((1 + r) ^ n * (P 0 / P n)) ^ (σ - 1) * (β ^ σ) ^ n)) := by
  have e : (fun s => ((1 + r)⁻¹) ^ s * (P s * C s))
      = fun s => ((1 + r)⁻¹) ^ s * CT s + ((1 + r)⁻¹) ^ s * (w s * Lbar - GT s)
          - ((1 + r)⁻¹) ^ s * (w s * L s - GT s) := by
    funext s
    rw [hPC s]
    ring
  have hPCs : Summable fun s => ((1 + r)⁻¹) ^ s * (P s * C s) := e ▸ (hCT.add hYbar).sub hY
  have h24 : ∑' s, ((1 + r)⁻¹) ^ s * (P s * C s)
      = (1 + r) * Q + ∑' s, ((1 + r)⁻¹) ^ s * (w s * Lbar - GT s) := by
    rw [e, (hCT.add hYbar).tsum_sub hY, hCT.tsum_add hYbar, hbud]
    ring
  rw [h22 0, consumption_function_price_form hr hP hβ hE hPCs hYbar hD h24]

end ObstfeldRogoff.RealExchangeRate.EndogenousLabour
