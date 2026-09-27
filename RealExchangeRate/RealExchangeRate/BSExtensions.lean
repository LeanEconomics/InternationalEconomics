/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RealExchangeRate.BalassaSamuelson
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Extensions of the Balassa–Samuelson model: more factors, immobile capital, exercises

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §4.2.4,
pp. 214–216, and Chapter 4 Exercises 1, 2 and 6, pp. 264–266.

* T7 (§4.2.4): with a third factor (skilled labour) and two tradables sharing the capital
  share `μ_KT`, the tradables zero-profit conditions (a linear system in `ŵ_L, ŵ_S`) have the
  unique solution `ŵ_L = ŵ_S = Â_T/(1 − μ_KT)` when the two tradables differ in skill
  intensity (nonsingular system), so `p̂ = [(μ_LN + μ_SN)/(1 − μ_KT)]Â_T − Â_N`. With
  internationally immobile capital and two tradables, `r̂ = ŵ = Â_T` provided `μ_K1 ≠ μ_K2`
  (and the solution is not unique when `μ_K1 = μ_K2`), so `p̂ = Â_T − Â_N`. These are stated
  as the linear systems the book derives from total differentials.
* Exercise 1: with labour-augmenting progress `F(K_T, E_T L_T)` the wage is exactly
  `w = E_T w₀(r)`, so `ŵ = Ê_T` replaces `Â_T/μ_LT`, `p̂ = μ_LN Ê_T − Â_N`, and the
  labour-reallocation bracket of (18) is unchanged.
* Exercise 2: a rise in `r` lowers `k_T`, `w` and `k_N`; `p` falls iff `μ_LN > μ_LT`.
* Exercise 6: optimal schooling `T* = α/(r + π)`, the relative wage
  `h/w = A⁻¹ e^α ((r + π)/α)^α`, `∂ log w/∂α = log(α/(r + π))` (so `w` rises with `α` iff
  `α > r + π`), `w` increasing in `A`, decreasing in `r` and `π`, and `p` increasing in `w`.
-/

namespace ObstfeldRogoff.RealExchangeRate.BSExtensions

open Filter Topology Set CRSProduction BalassaSamuelson

/-- T7 three factors, O&R §4.2.4, p. 215: when both tradables have capital share `μ_KT`,
`(ŵ_L, ŵ_S) = (Â_T/(1 − μ_KT), Â_T/(1 − μ_KT))` solves the tradables zero-profit system
`Â_T = μ_Li ŵ_L + μ_Si ŵ_S` (`i = 1, 2`, with `p̂_T = r̂ = 0`). -/
theorem threeFactor_solves {μL1 μS1 μL2 μS2 μKT AT : ℝ} (h1 : μL1 + μS1 = 1 - μKT)
    (h2 : μL2 + μS2 = 1 - μKT) (hK : μKT < 1) :
    AT = μL1 * (AT / (1 - μKT)) + μS1 * (AT / (1 - μKT)) ∧
      AT = μL2 * (AT / (1 - μKT)) + μS2 * (AT / (1 - μKT)) := by
  have hne : 1 - μKT ≠ 0 := by linarith
  constructor
  · rw [← add_mul, h1]; field_simp
  · rw [← add_mul, h2]; field_simp

/-- T7 three factors, uniqueness, O&R §4.2.4, p. 215: if the system is nonsingular
(`μ_L1 μ_S2 − μ_S1 μ_L2 ≠ 0`, i.e. the tradables differ in skill intensity), every solution
has `ŵ_L = ŵ_S = Â_T/(1 − μ_KT)`. -/
theorem threeFactor_unique {μL1 μS1 μL2 μS2 μKT AT wL wS : ℝ} (h1 : μL1 + μS1 = 1 - μKT)
    (h2 : μL2 + μS2 = 1 - μKT) (hK : μKT < 1) (hdet : μL1 * μS2 - μS1 * μL2 ≠ 0)
    (e1 : AT = μL1 * wL + μS1 * wS) (e2 : AT = μL2 * wL + μS2 * wS) :
    wL = AT / (1 - μKT) ∧ wS = AT / (1 - μKT) := by
  obtain ⟨c1, c2⟩ := threeFactor_solves (AT := AT) h1 h2 hK
  set c := AT / (1 - μKT)
  have u : (wL - c) * (μL1 * μS2 - μS1 * μL2) = 0 := by
    linear_combination μS2 * c1 - μS1 * c2 - μS2 * e1 + μS1 * e2
  have v : (wS - c) * (μL1 * μS2 - μS1 * μL2) = 0 := by
    linear_combination μL2 * e1 - μL2 * c1 - μL1 * e2 + μL1 * c2
  exact ⟨sub_eq_zero.1 ((mul_eq_zero.1 u).resolve_right hdet),
    sub_eq_zero.1 ((mul_eq_zero.1 v).resolve_right hdet)⟩

/-- T7 three factors, the price of nontradables, O&R §4.2.4, p. 215: substituting into the
nontradables zero-profit condition `p̂ + Â_N = μ_LN ŵ_L + μ_SN ŵ_S` gives
`p̂ = [(μ_LN + μ_SN)/(1 − μ_KT)] Â_T − Â_N`. -/
theorem threeFactor_price {μL1 μS1 μL2 μS2 μKT μLN μSN AT AN wL wS phat : ℝ}
    (h1 : μL1 + μS1 = 1 - μKT) (h2 : μL2 + μS2 = 1 - μKT) (hK : μKT < 1)
    (hdet : μL1 * μS2 - μS1 * μL2 ≠ 0) (e1 : AT = μL1 * wL + μS1 * wS)
    (e2 : AT = μL2 * wL + μS2 * wS) (eN : phat + AN = μLN * wL + μSN * wS) :
    phat = (μLN + μSN) / (1 - μKT) * AT - AN := by
  obtain ⟨hL, hS⟩ := threeFactor_unique h1 h2 hK hdet e1 e2
  rw [hL, hS] at eN
  have hne : 1 - μKT ≠ 0 := by linarith
  field_simp
  field_simp at eN
  linarith

/-- T7 three factors, Harrod–Balassa–Samuelson sign, O&R §4.2.4, p. 215, corrected as in
T4: if `(μ_LN + μ_SN)/(1 − μ_KT) ≥ 1`, `Â_T ≥ 0` and `Â_T > Â_N`, then `p̂ > 0`. -/
theorem threeFactor_hbs {μKT μLN μSN AT AN : ℝ} (hK : μKT < 1)
    (hle : 1 - μKT ≤ μLN + μSN) (hA : 0 ≤ AT) (hfaster : AN < AT) :
    0 < (μLN + μSN) / (1 - μKT) * AT - AN :=
  bs_price_rises (by linarith) hle hA hfaster

/-- T7 immobile capital, O&R §4.2.4, p. 216: with two tradables sharing productivity growth
`Â_T`, `Â_T = μ_Ki r̂ + μ_Li ŵ` (`μ_Ki + μ_Li = 1`) and `μ_K1 ≠ μ_K2`, the unique solution is
`r̂ = ŵ = Â_T`. -/
theorem immobileCapital_unique {μK1 μL1 μK2 μL2 AT rhat what : ℝ} (h1 : μK1 + μL1 = 1)
    (h2 : μK2 + μL2 = 1) (hne : μK1 ≠ μK2) (e1 : AT = μK1 * rhat + μL1 * what)
    (e2 : AT = μK2 * rhat + μL2 * what) : rhat = AT ∧ what = AT := by
  have huv : (μK1 - μK2) * (rhat - what) = 0 := by
    linear_combination e2 - e1 - what * (h1 - h2)
  have hrw : rhat = what := sub_eq_zero.1 ((mul_eq_zero.1 huv).resolve_left (sub_ne_zero.2 hne))
  have : what = AT := by
    rw [hrw] at e1; linear_combination -e1 - what * h1
  exact ⟨hrw.trans this, this⟩

/-- T7 immobile capital, degenerate case, O&R §4.2.4, p. 216 ("except in degenerate cases"):
if `μ_K1 = μ_K2 = μ_K` the system has other solutions, e.g. `(Â_T + μ_L, Â_T − μ_K)`. -/
theorem immobileCapital_degenerate {μK μL AT : ℝ} (h : μK + μL = 1) :
    AT = μK * (AT + μL) + μL * (AT - μK) := by
  linear_combination (-AT) * h

/-- T7 immobile capital, the price of nontradables, O&R §4.2.4, p. 216:
`p̂ = μ_KN r̂ + μ_LN ŵ − Â_N = Â_T − Â_N`. -/
theorem immobileCapital_price {μK1 μL1 μK2 μL2 μKN μLN AT AN rhat what phat : ℝ}
    (h1 : μK1 + μL1 = 1) (h2 : μK2 + μL2 = 1) (hN : μKN + μLN = 1) (hne : μK1 ≠ μK2)
    (e1 : AT = μK1 * rhat + μL1 * what) (e2 : AT = μK2 * rhat + μL2 * what)
    (eN : phat + AN = μKN * rhat + μLN * what) : phat = AT - AN := by
  obtain ⟨hr, hw⟩ := immobileCapital_unique h1 h2 hne e1 e2
  rw [hr, hw] at eN
  linear_combination eN + AT * hN

/-- Exercise 1, O&R p. 264: with labour-augmenting technology `Y_T = F(K_T, E_T L_T)` the
tradables sector earns zero maximum profit at the wage `w = E_T w₀(r)`, `w₀(r) = w(r, 1)`:
`E L f(K/(E L)) ≤ rK + E w₀ L` for all `K ≥ 0`, `L > 0`, with equality iff capital per
efficiency unit is `k(1, r)`. -/
theorem ex1_zero_max_profit (F : IntensiveTech) {E r K L : ℝ} (hE : 0 < E) (hr : 0 < r)
    (hK : 0 ≤ K) (hL : 0 < L) :
    E * L * F.f (K / (E * L)) ≤ r * K + E * F.wage 1 r * L ∧
      (E * L * F.f (K / (E * L)) = r * K + E * F.wage 1 r * L ↔
        K / (E * L) = F.kstar 1 r) := by
  obtain ⟨hk, hfoc⟩ := F.kstar_foc one_pos hr
  have hw : 1 * F.mpl (F.kstar 1 r) = F.wage 1 r := rfl
  have hEL : 0 < E * L := mul_pos hE hL
  have e : r * K + E * F.wage 1 r * L = r * K + F.wage 1 r * (E * L) := by ring
  have e' : E * L * F.f (K / (E * L)) = 1 * ((E * L) * F.f (K / (E * L))) := by ring
  rw [e, e']
  exact ⟨F.crs_profit_le one_pos hk hfoc hw hK hEL, F.crs_profit_eq_iff one_pos hk hfoc hw hK hEL⟩

/-- Exercise 1, O&R p. 264: along a path of labour-augmenting progress `E_T(t)`, the wage
`w = E_T w₀(r)` grows at exactly `ŵ = Ê_T` (replacing `Â_T/μ_LT` of (8)). -/
theorem ex1_wage_hat (F : IntensiveTech) {E : ℝ → ℝ} {E' t r : ℝ} (hE : HasDerivAt E E' t)
    (hE0 : 0 < E t) (hr : 0 < r) :
    HasDerivAt (fun s => Real.log (E s * F.wage 1 r)) (E' / E t) t := by
  have hw := F.wage_pos one_pos hr
  refine ((hE.mul_const (F.wage 1 r)).log (mul_pos hE0 hw).ne').congr_deriv ?_
  field_simp

/-- Exercise 1 and O&R (9), p. 208: for any differentiable wage path `W(t)`, the nontraded
price `p = c(r, W)/A_N` satisfies `p̂ = μ_LN ŵ − Â_N` exactly, with
`μ_LN = W/(c g(k_N))`. With `W = E_T w₀(r)` this gives `p̂ = μ_LN Ê_T − Â_N`. -/
theorem priceN_wage_path (G : IntensiveTech) {r : ℝ} {W AN : ℝ → ℝ} {W' AN' t : ℝ}
    (hW : HasDerivAt W W' t) (hN : HasDerivAt AN AN' t) (hr : 0 < r) (hW0 : 0 < W t)
    (hN0 : 0 < AN t) :
    HasDerivAt (fun s => Real.log (unitCost G r (W s) / AN s))
      (W t / (unitCost G r (W t) * G.f (kN G r (W t))) * (W' / W t) - AN' / AN t) t := by
  have hC := unitCost_path_hasDerivAt G (hasDerivAt_const t r) hW hr hW0
  obtain ⟨hc, _, _⟩ := unitCost_foc G hr hW0
  have hg := G.f_pos (kN_spec G hr hW0).1
  refine ((hC.div hN hN0.ne').log (div_pos hc hN0).ne').congr_deriv ?_
  simp only [Pi.div_apply]
  field_simp
  ring

/-- Exercise 1 with O&R (17)–(18), §4.3.2, pp. 224–225: the steady-state labour movement into
nontradables. From `L̂_N = Ĉ_N − α k̂_N`, `Ĉ_N = Ẑ − (γθ + 1 − γ)p̂`, `Ẑ = ψ_L ŵ` and Cobb–Douglas
nontradables `p̂ = (1 − α)ŵ`, `k̂_N = ŵ`, one gets
`L̂_N = {ψ_L − (1 − α)(γθ + 1 − γ) − α} ŵ`. With Hicks-neutral progress `ŵ = Â_T/μ_LT`; with
labour-augmenting progress `ŵ = Ê_T`: the bracket, hence the sign condition for a labour
exodus from tradables, is the same. -/
theorem ex1_labour_reallocation {α γ θ ψL what phat Zhat CNhat kNhat LNhat : ℝ}
    (hL : LNhat = CNhat - α * kNhat) (hC : CNhat = Zhat - (γ * θ + 1 - γ) * phat)
    (hZ : Zhat = ψL * what) (hp : phat = (1 - α) * what) (hk : kNhat = what) :
    LNhat = (ψL - (1 - α) * (γ * θ + 1 - γ) - α) * what := by
  rw [hL, hC, hZ, hp, hk]; ring

/-- Exercise 2, O&R p. 265: a rise in the world interest rate lowers the tradables capital
intensity `k_T`, the wage `w`, and the nontradables capital intensity `k_N`. -/
theorem ex2_rise_in_r (F G : IntensiveTech) {AT r1 r2 : ℝ} (hAT : 0 < AT) (hr1 : 0 < r1)
    (h : r1 < r2) :
    F.kstar AT r2 < F.kstar AT r1 ∧ F.wage AT r2 < F.wage AT r1 ∧
      kN G r2 (F.wage AT r2) < kN G r1 (F.wage AT r1) := by
  have hr2 : 0 < r2 := lt_trans hr1 h
  have hk := F.kstar_strictAntiOn_r hAT (show r1 ∈ Ioi (0 : ℝ) from hr1)
    (show r2 ∈ Ioi (0 : ℝ) from hr2) h
  have hw := F.wage_strictAntiOn_r hAT (show r1 ∈ Ioi (0 : ℝ) from hr1)
    (show r2 ∈ Ioi (0 : ℝ) from hr2) h
  have hw1 := F.wage_pos hAT hr1
  have hw2 := F.wage_pos hAT hr2
  refine ⟨hk, hw, ?_⟩
  have hratio : F.wage AT r2 / r2 < F.wage AT r1 / r1 := by
    rw [div_lt_div_iff₀ hr2 hr1]; nlinarith
  exact G.wrInv_strictMonoOn (div_pos hw2 hr2) (div_pos hw1 hr1) hratio

/-- Exercise 2, O&R p. 265 (and p. 209): the equilibrium relative price of nontradables is
locally decreasing in `r` — its derivative is negative — iff `μ_LN > μ_LT`. -/
theorem ex2_price_falls_iff (F G : IntensiveTech) {AT AN r D : ℝ} (hr : 0 < r) (hAT : 0 < AT)
    (hAN : 0 < AN) (hD : HasDerivAt (fun ρ => Real.log (eqmPrice F G ρ AT AN)) D r) :
    D < 0 ↔ muLT F r AT < muLN F G r AT := by
  have h := logPrice_hat_r F G (R := id) (hasDerivAt_id r) hr hAT hAN
  rw [hD.unique h, ← r_elasticity_neg_iff (muLT_pos F hr hAT)]
  simp only [id]
  have : 0 < 1 / r := by positivity
  constructor <;> intro h <;> nlinarith

/-- Exercise 6(a), O&R p. 266: lifetime earnings of the educated, discounted at `ρ = r + π`,
`∫_T^∞ e^{−ρt} A T^α h dt = e^{−ρT} A T^α h/ρ`. -/
theorem ex6_lifetime_earnings {ρ A α h T : ℝ} (hρ : 0 < ρ) :
    ∫ t in Ioi T, Real.exp (-ρ * t) * (A * T ^ α * h) =
      Real.exp (-ρ * T) * (A * T ^ α * h) / ρ := by
  rw [MeasureTheory.integral_mul_const, integral_exp_mul_Ioi (by linarith) T]
  field_simp

/-- Exercise 6(b), O&R p. 266: the first-order condition for schooling. The log of the
educated earnings factor `e^{−ρT}T^α` has derivative `α/T − ρ`, which vanishes iff
`T = α/ρ`. -/
theorem ex6_foc {ρ α T : ℝ} (hT : 0 < T) (hρ : 0 < ρ) :
    HasDerivAt (fun x => -ρ * x + α * Real.log x) (-ρ + α / T) T ∧
      (-ρ + α / T = 0 ↔ T = α / ρ) := by
  refine ⟨?_, ?_⟩
  · have h1 : HasDerivAt (fun x => -ρ * x) (-ρ) T := by
      simpa using (hasDerivAt_id T).const_mul (-ρ)
    have h2 := (Real.hasDerivAt_log hT.ne').const_mul α
    exact (h1.add h2).congr_deriv (by field_simp)
  · constructor
    · intro h; field_simp at h ⊢; linarith
    · intro h
      have hα : α ≠ 0 := by intro h0; rw [h0, zero_div] at h; linarith
      rw [h, div_div_eq_mul_div, mul_div_cancel_left₀ ρ hα]; ring

/-- Exercise 6(b), O&R p. 266: `T* = α/(r + π)` is the unique optimal schooling length —
for every other `T > 0`, the value `e^{−ρT}AT^αh/ρ − w/ρ` is strictly smaller. -/
theorem ex6_optimal_schooling {ρ α A h w T : ℝ} (hρ : 0 < ρ) (hα : 0 < α) (hAh : 0 < A * h)
    (hT : 0 < T) (hne : T ≠ α / ρ) :
    Real.exp (-ρ * T) * A * T ^ α * h / ρ - w / ρ <
      Real.exp (-ρ * (α / ρ)) * A * (α / ρ) ^ α * h / ρ - w / ρ := by
  have hTs : 0 < α / ρ := div_pos hα hρ
  have key : Real.exp (-ρ * T) * T ^ α < Real.exp (-ρ * (α / ρ)) * (α / ρ) ^ α := by
    rw [Real.rpow_def_of_pos hT, Real.rpow_def_of_pos hTs, ← Real.exp_add, ← Real.exp_add,
      Real.exp_lt_exp]
    have hx : 0 < ρ * T / α := div_pos (mul_pos hρ hT) hα
    have hx1 : ρ * T / α ≠ 1 := by
      intro h1; apply hne; field_simp at h1 ⊢; linarith
    have hlog := Real.log_lt_sub_one_of_pos hx hx1
    have hsplit : Real.log (ρ * T / α) = Real.log T - Real.log (α / ρ) := by
      rw [← Real.log_div hT.ne' hTs.ne']; congr 1; field_simp
    rw [hsplit] at hlog
    have : α * (Real.log T - Real.log (α / ρ)) < α * (ρ * T / α - 1) :=
      mul_lt_mul_of_pos_left hlog hα
    have e : α * (ρ * T / α - 1) = ρ * T - α := by field_simp
    have e2 : -ρ * (α / ρ) = -α := by field_simp
    rw [e2]; nlinarith
  have := mul_lt_mul_of_pos_right key hAh
  have hdiv := div_lt_div_of_pos_right this hρ
  have r1 : Real.exp (-ρ * T) * A * T ^ α * h / ρ = Real.exp (-ρ * T) * T ^ α * (A * h) / ρ := by
    ring
  have r2 : Real.exp (-ρ * (α / ρ)) * A * (α / ρ) ^ α * h / ρ
      = Real.exp (-ρ * (α / ρ)) * (α / ρ) ^ α * (A * h) / ρ := by ring
  rw [r1, r2]; linarith

/-- Exercise 6(c), O&R p. 266: if the educated and the uneducated are indifferent,
`e^{−ρT*}AT*^α h/ρ = w/ρ` at `T* = α/ρ`, then `h/w = A⁻¹ e^α (ρ/α)^α`. -/
theorem ex6_relative_wage {ρ α A h w : ℝ} (hρ : 0 < ρ) (hα : 0 < α) (hA : 0 < A) (hw : 0 < w)
    (hindiff : Real.exp (-ρ * (α / ρ)) * A * (α / ρ) ^ α * h / ρ = w / ρ) :
    h / w = A⁻¹ * Real.exp α * (ρ / α) ^ α := by
  have e2 : -ρ * (α / ρ) = -α := by field_simp
  rw [e2, div_left_inj' hρ.ne', Real.div_rpow hα.le hρ.le] at hindiff
  rw [Real.div_rpow hρ.le hα.le]
  have hαα : 0 < α ^ α := Real.rpow_pos_of_pos hα α
  have hρα : 0 < ρ ^ α := Real.rpow_pos_of_pos hρ α
  have hexp : Real.exp (-α) * Real.exp α = 1 := by rw [← Real.exp_add]; simp
  rw [div_eq_iff hw.ne', ← hindiff]
  field_simp
  linear_combination (-h) * hexp

/-- The unskilled wage implied by Exercise 6(c), O&R p. 266:
`w = h A e^{−α} (α/ρ)^α` with `ρ = r + π`. -/
noncomputable def skillWage (h A α ρ : ℝ) : ℝ := h * A * Real.exp (-α) * (α / ρ) ^ α

/-- Exercise 6(d), O&R p. 266: `∂ log w/∂α = log(α/(r + π))`. -/
theorem ex6_dlogw_dalpha {h A α ρ : ℝ} (hh : 0 < h) (hA : 0 < A) (hα : 0 < α) (hρ : 0 < ρ) :
    HasDerivAt (fun a => Real.log (skillWage h A a ρ)) (Real.log (α / ρ)) α := by
  have hg : HasDerivAt (fun a => Real.log h + Real.log A + -a + a * (Real.log a - Real.log ρ))
      (0 + 0 + -1 + (1 * (Real.log α - Real.log ρ) + α * α⁻¹)) α := by
    have h1 : HasDerivAt (fun a : ℝ => Real.log h) 0 α := hasDerivAt_const α _
    have h2 : HasDerivAt (fun a : ℝ => Real.log A) 0 α := hasDerivAt_const α _
    have h3 : HasDerivAt (fun a : ℝ => -a) (-1) α := (hasDerivAt_id α).neg
    have h4 : HasDerivAt (fun a : ℝ => Real.log a - Real.log ρ) α⁻¹ α :=
      (Real.hasDerivAt_log hα.ne').sub_const (Real.log ρ)
    exact ((h1.add h2).add h3).add ((hasDerivAt_id α).mul h4)
  have hv : (0 : ℝ) + 0 + -1 + (1 * (Real.log α - Real.log ρ) + α * α⁻¹)
      = Real.log (α / ρ) := by
    rw [Real.log_div hα.ne' hρ.ne']; field_simp; ring
  rw [hv] at hg
  refine hg.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hα] with a ha
  have ha' : (0 : ℝ) < a := ha
  unfold skillWage
  rw [Real.log_mul (by positivity) (Real.rpow_pos_of_pos (div_pos ha' hρ) a).ne',
    Real.log_mul (by positivity) (Real.exp_pos _).ne', Real.log_mul hh.ne' hA.ne',
    Real.log_exp, Real.log_rpow (div_pos ha' hρ), Real.log_div ha'.ne' hρ.ne']

/-- Exercise 6(d), O&R p. 266: the unskilled wage rises with the schooling elasticity `α`
exactly when `α > r + π` (the book's "you may assume" condition is also necessary). -/
theorem ex6_w_increasing_in_alpha_iff {α ρ : ℝ} (hα : 0 < α) (hρ : 0 < ρ) :
    0 < Real.log (α / ρ) ↔ ρ < α := by
  rw [Real.log_pos_iff (div_pos hα hρ).le, one_lt_div hρ]

/-- Exercise 6(d), O&R p. 266: the unskilled wage is strictly increasing in schooling
productivity `A`. -/
theorem ex6_w_strictMono_A {h α ρ : ℝ} (hh : 0 < h) (hα : 0 < α) (hρ : 0 < ρ) :
    StrictMono fun A => skillWage h A α ρ := by
  intro A1 A2 hA
  unfold skillWage
  have : 0 < h * Real.exp (-α) * (α / ρ) ^ α :=
    mul_pos (mul_pos hh (Real.exp_pos _)) (Real.rpow_pos_of_pos (div_pos hα hρ) α)
  nlinarith

/-- Exercise 6(d), O&R p. 266: the unskilled wage is strictly decreasing in the death
probability `π` (through `ρ = r + π`). -/
theorem ex6_w_strictAnti_pi {h A α r : ℝ} (hh : 0 < h) (hA : 0 < A) (hα : 0 < α) (hr : 0 < r) :
    StrictAntiOn (fun π => skillWage h A α (r + π)) (Ici 0) := by
  intro π1 hπ1 π2 hπ2 hlt
  have hπ1' : (0 : ℝ) ≤ π1 := hπ1
  have hρ1 : 0 < r + π1 := by linarith
  have hρ2 : 0 < r + π2 := by linarith
  have hq : α / (r + π2) < α / (r + π1) := div_lt_div_of_pos_left hα hρ1 (by linarith)
  have hpow := Real.rpow_lt_rpow (div_pos hα hρ2).le hq hα
  unfold skillWage
  have : 0 < h * A * Real.exp (-α) := mul_pos (mul_pos hh hA) (Real.exp_pos _)
  exact mul_lt_mul_of_pos_left hpow this

/-- Exercise 6(d), O&R p. 266: with the skilled wage given by a tradables factor-price
frontier `h = h(r)` (O&R (6), strictly decreasing), the unskilled wage is strictly decreasing
in `r`. -/
theorem ex6_w_strictAnti_r (T : IntensiveTech) {AS A α π : ℝ} (hAS : 0 < AS) (hA : 0 < A)
    (hα : 0 < α) (hπ : 0 ≤ π) :
    StrictAntiOn (fun r => skillWage (T.wage AS r) A α (r + π)) (Ioi 0) := by
  intro r1 hr1 r2 hr2 hlt
  have hr1' : (0 : ℝ) < r1 := hr1
  have hr2' : (0 : ℝ) < r2 := hr2
  have hh := T.wage_strictAntiOn_r hAS hr1 hr2 hlt
  have hh2 := T.wage_pos hAS hr2'
  have hq : α / (r2 + π) < α / (r1 + π) := div_lt_div_of_pos_left hα (by linarith) (by linarith)
  have hpow := Real.rpow_lt_rpow (div_pos hα (by linarith)).le hq hα
  have hp2 : 0 < (α / (r2 + π)) ^ α := Real.rpow_pos_of_pos (div_pos hα (by linarith)) α
  have hc : 0 < A * Real.exp (-α) := mul_pos hA (Real.exp_pos _)
  unfold skillWage
  dsimp only
  have e : ∀ x y : ℝ, x * A * Real.exp (-α) * y = (A * Real.exp (-α)) * (x * y) := by
    intros; ring
  rw [e, e]
  apply mul_lt_mul_of_pos_left _ hc
  exact mul_lt_mul hh hpow.le hp2 (T.wage_pos hAS hr1').le

/-- Exercise 6(e), O&R p. 266: given `r`, the relative price of nontradables is strictly
increasing in the unskilled wage, so it is higher where `w` is higher (high `A`, low `π`, or
high `α` when `α > r + π`). -/
theorem ex6e_price_increasing_in_w (G : IntensiveTech) {r AN w1 w2 : ℝ} (hr : 0 < r)
    (hAN : 0 < AN) (hw1 : 0 < w1) (hlt : w1 < w2) :
    unitCost G r w1 / AN < unitCost G r w2 / AN :=
  div_lt_div_of_pos_right (unitCost_strictMonoOn_w G hr hw1
    (show w2 ∈ Ioi (0 : ℝ) from lt_trans hw1 hlt) hlt) hAN

end ObstfeldRogoff.RealExchangeRate.BSExtensions
