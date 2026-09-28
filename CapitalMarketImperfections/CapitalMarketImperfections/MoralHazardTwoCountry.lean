/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import CapitalMarketImperfections.MoralHazardSmallCountry

/-!
# Moral hazard in international lending: the two-country model

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §6.4.2
(pp. 413–415), equations (50)–(53), Fig. 6.12 and footnote 67.

Two countries of equal population; a fraction `s ∈ [0, 1)` of each are savers, the rest
entrepreneurs with the technology of §6.4.1. Home agents have date-1 endowment `y`, Foreign
agents `y*`. `I`, `I*` are investment per entrepreneur. The world gross rate `R = 1 + r` is
endogenous, and world saving equals investment: `IS`, `(1 − s)(I + I*) = y + y*`.

* **The rate function (52).** In the borrowing regime `I > y`, the IC and ZP conditions (50)–(51)
  hold iff `R = ρ(I, y) = π'(I)Z/(1 + π'(I)(I − y)/π(I))`. We prove `∂ρ/∂y > 0` and the formula
  and sign of `∂ρ/∂I` in fn 67. The book assumes both countries borrow and never proves that an
  equilibrium exists; we extend `ρ` by `π'(I)Z` when `I ≤ y` (self-financed first best, which is
  what an entrepreneur with `y ≥ Ī` does), prove the extension continuous and strictly decreasing
  in `I`, and prove that **a two-country equilibrium exists and is unique** for all `y, y* > 0`.
* **Allocation.** If `y > y*` then `I > I*`, and Foreign is always in the borrowing regime; the
  equilibrium is efficient (equal marginal products, maximal expected world output) **iff**
  `y = y*`, and otherwise expected world output is strictly below the full-information level.
  `ρρ` is upward sloping and misses `IS` at the first-best point `A`.
* **Correction of p. 415.** The book says a "perverse" flow of savings from poor Foreign to rich
  Home "can occur". In this model it cannot: the richer country is always a strict net lender.
  (At a common `R`, capital inflows per unit of investment `Φ(I)/I = (π(I)/I)(Z/R − 1/π'(I))` are
  a product of two positive decreasing functions.)
-/

namespace ObstfeldRogoff.CapitalMarketImperfections.MoralHazardTwoCountry

open Set MoralHazardSmallCountry

/-- The rate function (52), O&R p. 414: `ρ(I, y) = π'(I)Z / (1 + π'(I)(I − y)/π(I))`. -/
noncomputable def rho (T : SuccessProb) (Z y I : ℝ) : ℝ :=
  T.dprob I * Z / (1 + T.dprob I * (I - y) / T.prob I)

/-- The ZP-wedge `max(I − y, 0)/π(max(I, y))`: equal to `(I − y)/π(I)` when `I > y` and to `0`
when `I ≤ y` (written so that it is visibly continuous for `y > 0`). -/
noncomputable def extTerm (T : SuccessProb) (y I : ℝ) : ℝ := max (I - y) 0 / T.prob (max I y)

/-- The extended rate function `Z / (1/π'(I) + max(I − y, 0)/π(I))`: equal to `ρ(I, y)` in the
borrowing regime `I > y` and to `π'(I)Z` (the first-best condition (44)) when `I ≤ y`. -/
noncomputable def rhoExt (T : SuccessProb) (Z y I : ℝ) : ℝ := Z / (1 / T.dprob I + extTerm T y I)

/-- A two-country equilibrium (O&R p. 413–414): positive investments, each country's
entrepreneurs at their optimal response to the common gross rate `R` (`rhoExt = R`), and
world saving equal to world investment (`IS`). -/
def IsEqm (T : SuccessProb) (Z s y ys R I Is : ℝ) : Prop :=
  0 < I ∧ 0 < Is ∧ rhoExt T Z y I = R ∧ rhoExt T Z ys Is = R ∧ (1 - s) * (I + Is) = y + ys

/-! ## The extended rate function -/

/-- `extTerm = 0` when `I ≤ y`. -/
theorem extTerm_of_le (T : SuccessProb) {y I : ℝ} (h : I ≤ y) : extTerm T y I = 0 := by
  unfold extTerm; rw [max_eq_right (by linarith)]; simp

/-- `extTerm = (I − y)/π(I)` when `y < I`. -/
theorem extTerm_of_lt (T : SuccessProb) {y I : ℝ} (h : y < I) :
    extTerm T y I = (I - y) / T.prob I := by
  unfold extTerm; rw [max_eq_left (by linarith), max_eq_left h.le]

/-- `extTerm ≥ 0` for `y > 0`. -/
theorem extTerm_nonneg (T : SuccessProb) {y I : ℝ} (hy : 0 < y) : 0 ≤ extTerm T y I := by
  unfold extTerm
  have : 0 < T.prob (max I y) := T.prob_pos (lt_of_lt_of_le hy (le_max_right I y))
  positivity

/-- The denominator `1/π'(I) + extTerm` is positive on `[0, ∞)`. -/
theorem den_pos (T : SuccessProb) {y I : ℝ} (hy : 0 < y) (hI : 0 ≤ I) :
    0 < 1 / T.dprob I + extTerm T y I := by
  have := T.dprob_pos I hI
  have := extTerm_nonneg T (I := I) hy
  positivity

/-- For `I ≤ y` the extended rate is the full-information `π'(I)Z`. -/
theorem rhoExt_of_le (T : SuccessProb) {Z y I : ℝ} (hI : 0 ≤ I) (h : I ≤ y) :
    rhoExt T Z y I = T.dprob I * Z := by
  unfold rhoExt; rw [extTerm_of_le T h, add_zero]
  have := (T.dprob_pos I hI).ne'
  field_simp

/-- For `I > y` the extended rate is the book's `ρ(I, y)`, (52), O&R p. 414. -/
theorem rhoExt_of_lt (T : SuccessProb) {Z y I : ℝ} (hy : 0 ≤ y) (h : y < I) :
    rhoExt T Z y I = rho T Z y I := by
  have hI : 0 < I := lt_of_le_of_lt hy h
  have hd := (T.dprob_pos I hI.le).ne'
  have hp := (T.prob_pos hI).ne'
  unfold rhoExt rho; rw [extTerm_of_lt T h]
  field_simp

/-- **Derivation of (52)**, O&R p. 414: in the borrowing regime `y < I`, the incentive and
zero-profit conditions (50)–(51) hold at gross rate `R` iff `R = ρ(I, y)`. -/
theorem rho_eq_iff_eqmGap (T : SuccessProb) {Z R y I : ℝ} (hy : 0 ≤ y) (h : y < I) :
    rhoExt T Z y I = R ↔ eqmGap T Z R y I = 0 := by
  have hI : 0 < I := lt_of_le_of_lt hy h
  have hd := T.dprob_pos I hI.le
  have hp := T.prob_pos hI
  have hden : 0 < 1 / T.dprob I + (I - y) / T.prob I := by
    have : 0 < I - y := by linarith
    positivity
  unfold rhoExt eqmGap icCurve zpCurve
  rw [extTerm_of_lt T h, div_eq_iff hden.ne']
  have e : R * (1 / T.dprob I + (I - y) / T.prob I) = R / T.dprob I + R * (I - y) / T.prob I := by
    ring
  rw [e]
  constructor <;> intro h' <;> linarith

/-- The extended rate at `I = 0` is `π'(0)Z`. -/
theorem rhoExt_zero (T : SuccessProb) {Z y : ℝ} (hy : 0 < y) : rhoExt T Z y 0 = T.dprob 0 * Z :=
  rhoExt_of_le T le_rfl hy.le

/-- The extended rate is positive. -/
theorem rhoExt_pos (T : SuccessProb) {Z y I : ℝ} (hZ : 0 < Z) (hy : 0 < y) (hI : 0 ≤ I) :
    0 < rhoExt T Z y I :=
  div_pos hZ (den_pos T hy hI)

/-- `extTerm` is weakly increasing in `I` on `[0, ∞)` (for `y > 0`). -/
theorem extTerm_mono (T : SuccessProb) {y I J : ℝ} (hy : 0 < y) (hIJ : I ≤ J) :
    extTerm T y I ≤ extTerm T y J := by
  rcases le_or_gt I y with h | h
  · rw [extTerm_of_le T h]; exact extTerm_nonneg T hy
  · rw [extTerm_of_lt T h, extTerm_of_lt T (lt_of_lt_of_le h hIJ)]
    rcases hIJ.lt_or_eq with h' | h'
    · have := zpCurve_strictMonoOn T one_pos hy.le (show I ∈ Ioi (0 : ℝ) from hy.trans h)
        (show J ∈ Ioi (0 : ℝ) from (hy.trans h).trans h') h'
      unfold zpCurve at this
      simpa using this.le
    · rw [h']

/-- **The extended rate is strictly decreasing in investment** (O&R fn 67: `∂ρ/∂I < 0`, here in
derivative-free form and across the regime boundary). -/
theorem rhoExt_strictAntiOn (T : SuccessProb) {Z y : ℝ} (hZ : 0 < Z) (hy : 0 < y) :
    StrictAntiOn (rhoExt T Z y) (Ici 0) := by
  intro I hI J hJ hIJ
  have hI0 : (0 : ℝ) ≤ I := hI
  have hdI := T.dprob_pos I hI0
  have hdJ := T.dprob_pos J (le_trans hI0 hIJ.le)
  have h1 : 1 / T.dprob I < 1 / T.dprob J :=
    one_div_lt_one_div_of_lt hdJ (T.dprob_strictAnti hI hJ hIJ)
  have h2 := extTerm_mono T hy hIJ.le
  unfold rhoExt
  exact div_lt_div_of_pos_left hZ (den_pos T hy hI0) (by linarith)

/-- **The extended rate is continuous** on `[0, ∞)` for `y > 0`. -/
theorem rhoExt_continuousOn (T : SuccessProb) (Z : ℝ) {y : ℝ} (hy : 0 < y) :
    ContinuousOn (rhoExt T Z y) (Ici 0) := by
  have hmax : ContinuousOn (fun I : ℝ => max I y) (Ici 0) :=
    (continuous_id.max continuous_const).continuousOn
  have hp : ContinuousOn (fun I => T.prob (max I y)) (Ici 0) :=
    T.continuousOn_prob.comp hmax (fun I _ => mem_Ici.2 (le_trans hy.le (le_max_right I y)))
  have hext : ContinuousOn (extTerm T y) (Ici 0) := by
    unfold extTerm
    exact ((continuous_id.sub continuous_const).max continuous_const).continuousOn.div hp
      (fun I _ => (T.prob_pos (lt_of_lt_of_le hy (le_max_right I y))).ne')
  unfold rhoExt
  apply continuousOn_const.div
  · exact (continuousOn_const.div T.dprob_continuousOn
      (fun I hI => (T.dprob_pos I hI).ne')).add hext
  · intro I hI; exact (den_pos T hy hI).ne'

/-- `extTerm` is weakly decreasing in wealth, strictly when `y < I` and `y < y'`. -/
theorem extTerm_anti_wealth (T : SuccessProb) {y y' I : ℝ} (hy : 0 < y) (hyy : y ≤ y') :
    extTerm T y' I ≤ extTerm T y I ∧ (y < I → y < y' → extTerm T y' I < extTerm T y I) := by
  have hy' : 0 < y' := lt_of_lt_of_le hy hyy
  constructor
  · rcases le_or_gt I y' with h | h
    · rw [extTerm_of_le T h]; exact extTerm_nonneg T hy
    · have hyI : y < I := lt_of_le_of_lt hyy h
      rw [extTerm_of_lt T h, extTerm_of_lt T hyI]
      have := T.prob_pos (hy.trans hyI)
      exact div_le_div_of_nonneg_right (by linarith) this.le
  · intro hyI hlt
    rcases le_or_gt I y' with h | h
    · rw [extTerm_of_le T h, extTerm_of_lt T hyI]
      have := T.prob_pos (hy.trans hyI)
      have : 0 < I - y := by linarith
      positivity
    · rw [extTerm_of_lt T h, extTerm_of_lt T hyI]
      have := T.prob_pos (hy.trans hyI)
      exact div_lt_div_of_pos_right (by linarith) this

/-- **The rate function rises with wealth** (O&R p. 414, `∂ρ/∂y > 0`): `ρ(I, y) ≤ ρ(I, y')` for
`y ≤ y'`, strictly when `y < I`. -/
theorem rhoExt_mono_wealth (T : SuccessProb) {Z y y' I : ℝ} (hZ : 0 < Z) (hy : 0 < y)
    (hyy : y ≤ y') (hI : 0 ≤ I) :
    rhoExt T Z y I ≤ rhoExt T Z y' I ∧ (y < I → y < y' → rhoExt T Z y I < rhoExt T Z y' I) := by
  have hy' : 0 < y' := lt_of_lt_of_le hy hyy
  obtain ⟨h1, h2⟩ := extTerm_anti_wealth T (I := I) hy hyy
  unfold rhoExt
  refine ⟨div_le_div_of_nonneg_left hZ.le (den_pos T hy' hI) (by linarith), ?_⟩
  intro hyI hlt
  exact div_lt_div_of_pos_left hZ (den_pos T hy' hI) (by linarith [h2 hyI hlt])

/-! ## Footnote 67: derivatives of `ρ` -/

/-- `ρ(I, y) = π'(I)Zπ(I)/(π(I) + π'(I)(I − y))` for `I > 0`. -/
theorem rho_eq_quot (T : SuccessProb) (Z y : ℝ) {I : ℝ} (hI : 0 < I) :
    rho T Z y I = T.dprob I * Z * T.prob I / (T.prob I + T.dprob I * (I - y)) := by
  have hp := (T.prob_pos hI).ne'
  unfold rho
  rw [one_add_div hp, div_div_eq_mul_div]

/-- **Footnote 67**, O&R p. 414: `∂ρ/∂I = [π''π²Z + π'²(π'(I − y) − π)Z]/[π + π'(I − y)]²`, when
`π'` has derivative `π''(I) = d2` at `I` and `y < I`. -/
theorem rho_hasDerivAt_I (T : SuccessProb) (Z : ℝ) {y I d2 : ℝ} (hy : 0 ≤ y) (hyI : y < I)
    (hd2 : HasDerivAt T.dprob d2 I) :
    HasDerivAt (rho T Z y)
      ((d2 * T.prob I ^ 2 * Z + T.dprob I ^ 2 * (T.dprob I * (I - y) - T.prob I) * Z) /
        (T.prob I + T.dprob I * (I - y)) ^ 2) I := by
  have hI : 0 < I := lt_of_le_of_lt hy hyI
  have hp := T.prob_pos hI
  have hd := T.dprob_pos I hI.le
  have hden : T.prob I + T.dprob I * (I - y) ≠ 0 := by
    have : 0 < I - y := by linarith
    positivity
  have hπ := T.hasDerivAt I hI.le
  have hN : HasDerivAt (fun x => T.dprob x * Z * T.prob x)
      (d2 * Z * T.prob I + T.dprob I * Z * T.dprob I) I := (hd2.mul_const Z).mul hπ
  have hD : HasDerivAt (fun x => T.prob x + T.dprob x * (x - y))
      (T.dprob I + (d2 * (I - y) + T.dprob I * 1)) I :=
    hπ.add (hd2.mul ((hasDerivAt_id' I).sub_const y))
  have hq := hN.div hD hden
  have hev : (fun x => T.dprob x * Z * T.prob x / (T.prob x + T.dprob x * (x - y))) =ᶠ[nhds I]
      rho T Z y := by
    filter_upwards [Ioi_mem_nhds hI] with x hx
    exact (rho_eq_quot T Z y hx).symm
  refine (hq.congr_of_eventuallyEq hev.symm).congr_deriv ?_
  field_simp
  ring

/-- **Footnote 67: `∂ρ/∂I < 0`**, since `π'' ≤ 0` and `π'(I)(I − y) < π(I)` (fn 66). -/
theorem rho_deriv_I_neg (T : SuccessProb) {Z y I d2 : ℝ} (hZ : 0 < Z) (hy : 0 ≤ y) (hyI : y < I)
    (hd2 : HasDerivAt T.dprob d2 I) :
    (d2 * T.prob I ^ 2 * Z + T.dprob I ^ 2 * (T.dprob I * (I - y) - T.prob I) * Z) /
      (T.prob I + T.dprob I * (I - y)) ^ 2 < 0 := by
  have hI : 0 < I := lt_of_le_of_lt hy hyI
  have hp := T.prob_pos hI
  have hd := T.dprob_pos I hI.le
  have hd2n := T.d2_nonpos hI.le hd2
  have h66 := T.mul_dprob_lt_prob hI
  have hden : 0 < (T.prob I + T.dprob I * (I - y)) ^ 2 := by
    have : 0 < I - y := by linarith
    positivity
  apply div_neg_of_neg_of_pos _ hden
  have a1 : d2 * T.prob I ^ 2 * Z ≤ 0 := by
    have := mul_nonpos_of_nonpos_of_nonneg hd2n (pow_pos hp 2).le
    nlinarith
  have a2 : T.dprob I * (I - y) - T.prob I < 0 := by nlinarith
  have a3 : T.dprob I ^ 2 * (T.dprob I * (I - y) - T.prob I) * Z < 0 := by
    have := mul_neg_of_pos_of_neg (pow_pos hd 2) a2
    nlinarith
  linarith

/-- `∂ρ/∂y = π'(I)²Zπ(I)/[π + π'(I − y)]² > 0`, O&R p. 414. -/
theorem rho_hasDerivAt_y (T : SuccessProb) {Z y I : ℝ} (hI : 0 < I)
    (hden : T.prob I + T.dprob I * (I - y) ≠ 0) :
    HasDerivAt (fun y' => rho T Z y' I)
      (T.dprob I ^ 2 * Z * T.prob I / (T.prob I + T.dprob I * (I - y)) ^ 2) y := by
  have hfun : (fun y' => rho T Z y' I) =
      fun y' => T.dprob I * Z * T.prob I / (T.prob I + T.dprob I * (I - y')) := by
    funext y'; exact rho_eq_quot T Z y' hI
  rw [hfun]
  have hD : HasDerivAt (fun y' => T.prob I + T.dprob I * (I - y')) (T.dprob I * (-1)) y := by
    have := ((hasDerivAt_id' y).const_sub I).const_mul (T.dprob I)
    exact this.const_add (T.prob I)
  have := (hasDerivAt_const y (T.dprob I * Z * T.prob I)).div hD hden
  refine this.congr_deriv ?_
  field_simp
  ring

/-! ## What `rhoExt = R` means for a country -/

/-- **Each country's investment is its optimal response to `R`** (O&R p. 414): `rhoExt(I, y) = R`
iff either the country is in the borrowing regime (`y < I`, `y < Ī(R)`) and `I` is the crossing
of its IC and ZP curves, i.e. its optimal incentive-compatible contract investment; or it
self-finances the first best, `I = Ī(R) ≤ y`. -/
theorem rhoExt_eq_iff (T : SuccessProb) {Z R y I : ℝ} (hZ : 0 < Z) (hy : 0 < y) (hI : 0 < I) :
    rhoExt T Z y I = R ↔
      (y < I ∧ R < T.dprob y * Z ∧ eqmGap T Z R y I = 0) ∨ (I ≤ y ∧ T.dprob I * Z = R) := by
  constructor
  · intro h
    rcases le_or_gt I y with hle | hlt
    · right; exact ⟨hle, by rw [← h, rhoExt_of_le T hI.le hle]⟩
    · left
      refine ⟨hlt, ?_, (rho_eq_iff_eqmGap T hy.le hlt).1 h⟩
      have hp := T.prob_pos hI
      have hd := T.dprob_pos I hI.le
      have hlt1 : R < T.dprob I * Z := by
        rw [← h]; unfold rhoExt
        rw [extTerm_of_lt T hlt]
        have : 0 < (I - y) / T.prob I := by
          have : 0 < I - y := by linarith
          positivity
        rw [div_lt_iff₀ (by positivity)]
        have e : T.dprob I * Z * (1 / T.dprob I + (I - y) / T.prob I) =
            Z + T.dprob I * Z * ((I - y) / T.prob I) := by field_simp
        rw [e]; nlinarith [mul_pos (mul_pos hd hZ) this]
      have := T.dprob_strictAnti (mem_Ici.2 hy.le) (mem_Ici.2 hI.le) hlt
      nlinarith
  · rintro (⟨hlt, _, hg⟩ | ⟨hle, hR⟩)
    · exact (rho_eq_iff_eqmGap T hy.le hlt).2 hg
    · rw [rhoExt_of_le T hI.le hle, hR]

/-- In the borrowing regime the country is a small-country `Setting` (with `Y₁ = y`, `E = 0`)
whose equilibrium investment is `I`, so by `Setting.optimal_contract_exists_unique` its
entrepreneurs' unique optimal contract induces `I` (O&R p. 414, (50)–(51)). -/
theorem borrowing_country_setting (T : SuccessProb) {Z R y I : ℝ} (hR : 0 < R) (hy : 0 < y)
    (hyR : R < T.dprob y * Z) (hg : eqmGap T Z R y I = 0) :
    ∃ S : Setting, S.T = T ∧ S.Z = Z ∧ S.R = R ∧ S.Y₁ = y ∧ S.E = 0 ∧
      eqmGap S.T S.Z S.R S.w I = 0 := by
  refine ⟨⟨T, Z, R, y, 0, hR, hy.le, le_rfl, by simpa using hy, by simpa using hyR⟩,
    rfl, rfl, rfl, rfl, rfl, ?_⟩
  simpa [Setting.w] using hg

/-- **A self-financing country invests `Ī(R)`** (the first best): if `π'(I)Z = R` with
`0 < I ≤ y`, then with no loan the entrepreneur's unique optimal investment is `I`, and no
contract meeting lenders' participation gives him more. -/
theorem selfFinance_first_best (T : SuccessProb) {Z R y I : ℝ} (hZ : 0 < Z) (hI : 0 < I)
    (hIy : I ≤ y) (hR : T.dprob I * Z = R) :
    IsBestResponse T Z R y 0 ⟨0, 0, 0⟩ I ∧ (∀ J, IsBestResponse T Z R y 0 ⟨0, 0, 0⟩ J → J = I) ∧
      ∀ (c : Contract) (J : ℝ), 0 ≤ J → R * c.D ≤ T.prob J * c.PZ + (1 - T.prob J) * c.P0 →
        borrowerPayoff T Z R y 0 c J ≤ borrowerPayoff T Z R y 0 ⟨0, 0, 0⟩ I := by
  have hstake : stake Z ⟨0, 0, 0⟩ = Z := by simp [stake]
  obtain ⟨hb, hu⟩ := bestResponse_of_foc (T := T) (R := R) (Y₁ := y) (E := 0)
    (c := ⟨0, 0, 0⟩) (by rw [hstake]; exact hZ) (by simp only; linarith) hI.le
    (by rw [hstake]; exact hR)
  have hmin : min (y + (⟨0, 0, 0⟩ : Contract).D) I = I := by simp only; simp [hIy]
  rw [hmin] at hb hu
  refine ⟨hb, hu, ?_⟩
  intro c J hJ hpart
  have h1 : borrowerPayoff T Z R y 0 c J ≤ netOutput T Z R y J := by
    unfold borrowerPayoff netOutput; nlinarith
  have hval : borrowerPayoff T Z R y 0 ⟨0, 0, 0⟩ I = netOutput T Z R y I := by
    unfold borrowerPayoff netOutput; simp only; ring
  rw [hval]
  rcases eq_or_ne J I with h | h
  · subst h; exact h1
  · have := efficient_investment_maximises (Y₁ := y) hZ hI.le hR hJ h
    linarith

/-! ## Existence and uniqueness of the two-country equilibrium -/

/-- **Existence and uniqueness of the two-country equilibrium** (O&R p. 414–415, Fig. 6.12;
asserted but never proved in the book): for any endowments `y, y* > 0` and saver share
`s < 1` (economically `s ∈ [0, 1)`), there is exactly one `(R, I, I*)` with each country at its
optimal response to `R` and world saving equal to world investment. -/
theorem eqm_exists_unique (T : SuccessProb) {Z s y ys : ℝ} (hZ : 0 < Z) (hs1 : s < 1)
    (hy : 0 < y) (hys : 0 < ys) :
    ∃! x : ℝ × ℝ × ℝ, IsEqm T Z s y ys x.1 x.2.1 x.2.2 := by
  have h1s : 0 < 1 - s := by linarith
  set K := (y + ys) / (1 - s) with hK
  have hKpos : 0 < K := by positivity
  set H : ℝ → ℝ := fun I => rhoExt T Z y I - rhoExt T Z ys (K - I) with hH
  have anti_y := rhoExt_strictAntiOn T hZ hy
  have anti_ys := rhoExt_strictAntiOn T hZ hys
  have Hanti : StrictAntiOn H (Icc 0 K) := by
    intro I hI J hJ hIJ
    have a := anti_y (mem_Ici.2 hI.1) (mem_Ici.2 hJ.1) hIJ
    have b := anti_ys (mem_Ici.2 (by linarith [hJ.2] : (0 : ℝ) ≤ K - J))
      (mem_Ici.2 (by linarith [hI.2] : (0 : ℝ) ≤ K - I)) (by linarith : K - J < K - I)
    simp only [hH]
    linarith
  have Hcont : ContinuousOn H (Icc 0 K) := by
    apply ContinuousOn.sub
    · exact (rhoExt_continuousOn T Z hy).mono (fun x hx => mem_Ici.2 hx.1)
    · exact (rhoExt_continuousOn T Z hys).comp (continuousOn_const.sub continuousOn_id)
        (fun x hx => mem_Ici.2 (by linarith [hx.2]))
  have H0 : 0 < H 0 := by
    simp only [hH, sub_zero]
    rw [rhoExt_zero T hy, ← rhoExt_zero T (Z := Z) hys]
    have := anti_ys (mem_Ici.2 le_rfl) (mem_Ici.2 hKpos.le) hKpos
    linarith
  have HK : H K < 0 := by
    simp only [hH, sub_self]
    rw [rhoExt_zero T hys, ← rhoExt_zero T (Z := Z) hy]
    have := anti_y (mem_Ici.2 le_rfl) (mem_Ici.2 hKpos.le) hKpos
    linarith
  obtain ⟨I, hI, hHI⟩ := intermediate_value_Icc' hKpos.le Hcont ⟨HK.le, H0.le⟩
  have hI0 : 0 < I := by
    rcases hI.1.lt_or_eq with h | h
    · exact h
    · rw [← h] at hHI; linarith
  have hIK : I < K := by
    rcases hI.2.lt_or_eq with h | h
    · exact h
    · rw [h] at hHI; linarith
  have hIS : ∀ a b : ℝ, (1 - s) * (a + b) = y + ys ↔ b = K - a := by
    intro a b
    rw [hK]
    constructor
    · intro h; field_simp; linarith
    · intro h; rw [h]; field_simp; ring
  refine ⟨(rhoExt T Z y I, I, K - I), ⟨hI0, by linarith, rfl, ?_, (hIS _ _).2 rfl⟩, ?_⟩
  · simp only [hH] at hHI; linarith
  · rintro ⟨R', I', Is'⟩ ⟨hI', hIs', hR1, hR2, hIS'⟩
    simp only at hI' hIs' hR1 hR2 hIS'
    have hIs'eq := (hIS _ _).1 hIS'
    have hI'K : I' ≤ K := by linarith
    have hHI' : H I' = 0 := by
      simp only [hH]; rw [hR1, ← hIs'eq, hR2]; ring
    have hII : I' = I := by
      by_contra hne
      rcases lt_or_gt_of_ne hne with h | h
      · have := Hanti ⟨hI'.le, hI'K⟩ hI h; linarith
      · have := Hanti hI ⟨hI'.le, hI'K⟩ h; linarith
    rw [hII] at hR1 hIs'eq
    rw [← hR1, hII, hIs'eq]

/-- The equilibrium rate lies in `(0, π'(0)Z)`. -/
theorem eqm_R_bounds (T : SuccessProb) {Z s y ys R I Is : ℝ} (hZ : 0 < Z) (hy : 0 < y)
    (h : IsEqm T Z s y ys R I Is) : 0 < R ∧ R < T.dprob 0 * Z := by
  obtain ⟨hI, _, hR, _⟩ := h
  refine ⟨hR ▸ rhoExt_pos T hZ hy hI.le, ?_⟩
  rw [← hR, ← rhoExt_zero T (Z := Z) hy]
  exact rhoExt_strictAntiOn T hZ hy (mem_Ici.2 le_rfl) (mem_Ici.2 hI.le) hI

/-- In an equilibrium with both countries borrowing (the book's assumption, p. 414) the common
rate satisfies (52)–(53): `R = ρ(I, y) = ρ(I*, y*)`. -/
theorem eqm_book_form (T : SuccessProb) {Z s y ys R I Is : ℝ} (hy : 0 < y) (hys : 0 < ys)
    (h : IsEqm T Z s y ys R I Is) (hyI : y < I) (hysI : ys < Is) :
    R = rho T Z y I ∧ R = rho T Z ys Is ∧ rho T Z y I = rho T Z ys Is := by
  obtain ⟨_, _, h1, h2, _⟩ := h
  rw [rhoExt_of_lt T hy.le hyI] at h1
  rw [rhoExt_of_lt T hys.le hysI] at h2
  exact ⟨h1.symm, h2.symm, h1.trans h2.symm⟩

/-! ## The allocation of investment -/

/-- The equilibrium is symmetric under relabelling the countries. -/
theorem IsEqm.swap {T : SuccessProb} {Z s y ys R I Is : ℝ} (h : IsEqm T Z s y ys R I Is) :
    IsEqm T Z s ys y R Is I := by
  obtain ⟨a, b, c, d, e⟩ := h
  exact ⟨b, a, d, c, by linarith⟩

/-- **The richer country invests more** (O&R p. 415, Fig. 6.12, point `B`): `y > y*` implies
`I > I*`. -/
theorem richer_invests_more (T : SuccessProb) {Z s y ys R I Is : ℝ} (hZ : 0 < Z) (hs0 : 0 ≤ s)
    (hys : 0 < ys) (hyy : ys < y) (h : IsEqm T Z s y ys R I Is) : Is < I := by
  obtain ⟨hI, hIs, h1, h2, hIS⟩ := h
  have hy : 0 < y := hys.trans hyy
  by_contra hle
  push Not at hle
  -- `ρ(I, y) ≥ ρ(I*, y) ≥ ρ(I*, y*)`, with equality forcing `I = I*` and `I* ≤ y*`
  have a : rhoExt T Z y Is ≤ rhoExt T Z y I :=
    (rhoExt_strictAntiOn T hZ hy).antitoneOn (mem_Ici.2 hI.le) (mem_Ici.2 hIs.le) hle
  obtain ⟨b, bstrict⟩ := rhoExt_mono_wealth T (I := Is) hZ hys hyy.le hIs.le
  have hIsle : Is ≤ ys := by
    by_contra hh; push Not at hh
    have := bstrict hh hyy
    linarith
  have hIeq : I = Is := by
    rcases hle.lt_or_eq with hl | hl
    · have := rhoExt_strictAntiOn T hZ hy (mem_Ici.2 hI.le) (mem_Ici.2 hIs.le) hl
      linarith
    · exact hl
  rw [hIeq] at hIS
  nlinarith

/-- **The poorer country always borrows** (`I* > y*`) when `y > y*`: were Foreign to self-finance
at `Ī(R)`, Home — investing more — would face a strictly lower rate. -/
theorem poorer_country_borrows (T : SuccessProb) {Z s y ys R I Is : ℝ} (hZ : 0 < Z) (hs0 : 0 ≤ s)
    (hys : 0 < ys) (hyy : ys < y) (h : IsEqm T Z s y ys R I Is) : ys < Is := by
  have hlt := richer_invests_more T hZ hs0 hys hyy h
  obtain ⟨hI, hIs, h1, h2, _⟩ := h
  have hy : 0 < y := hys.trans hyy
  by_contra hle
  push Not at hle
  rw [rhoExt_of_le T hIs.le hle] at h2
  -- `R = π'(I*)Z > π'(I)Z ≥ ρ(I, y) = R`
  have hd := T.dprob_strictAnti (mem_Ici.2 hIs.le) (mem_Ici.2 hI.le) hlt
  have hρ : rhoExt T Z y I ≤ T.dprob I * Z := by
    unfold rhoExt
    have := extTerm_nonneg T (I := I) hy
    have hdI := T.dprob_pos I hI.le
    rw [div_le_iff₀ (den_pos T hy hI.le)]
    have e : T.dprob I * Z * (1 / T.dprob I + extTerm T y I) =
        Z + T.dprob I * Z * extTerm T y I := by field_simp
    rw [e]; nlinarith [mul_nonneg (mul_pos hdI hZ).le this]
  nlinarith

/-- **Correction of O&R p. 415: the richer country is always a strict net lender.** The book
asserts that "a seemingly perverse flow of savings from Foreign to Home can occur". In this model
it cannot: if `y > y*`, Home's investment per capita `(1 − s)I` is strictly below its saving `y`
(and so Foreign borrows). In the borrowing regime `y = I − Φ(I)` with `Φ(I)/I` a product of the
decreasing positive functions `π(I)/I` and `Z/R − 1/π'(I)`, so `y/I` rises with `I`. -/
theorem richer_country_lends (T : SuccessProb) {Z s y ys R I Is : ℝ} (hZ : 0 < Z) (hs0 : 0 ≤ s)
    (hs1 : s < 1) (hys : 0 < ys) (hyy : ys < y) (h : IsEqm T Z s y ys R I Is) :
    (1 - s) * I < y ∧ ys < (1 - s) * Is := by
  have hlt := richer_invests_more T hZ hs0 hys hyy h
  have hbor := poorer_country_borrows T hZ hs0 hys hyy h
  obtain ⟨hR0, _⟩ := eqm_R_bounds T hZ (hys.trans hyy) h
  obtain ⟨hI, hIs, h1, h2, hIS⟩ := h
  have hy : 0 < y := hys.trans hyy
  suffices hmain : (1 - s) * I < y by
    refine ⟨hmain, by linarith⟩
  rcases le_or_gt I y with hle | hgt
  · -- Home self-finances
    rcases hs0.lt_or_eq with hs | hs
    · nlinarith
    · rw [← hs] at hIS ⊢
      have : I ≠ y := by intro hh; rw [hh] at hIS; linarith
      have := lt_of_le_of_ne hle this
      linarith
  · -- both borrow: compare `y/I` and `y*/I*`
    have hbr : R < T.dprob y * Z ∧ eqmGap T Z R y I = 0 := by
      rcases (rhoExt_eq_iff T hZ hy hI).1 h1 with ⟨_, hh, hg⟩ | ⟨hh, _⟩
      · exact ⟨hh, hg⟩
      · exact absurd hh (not_le.2 hgt)
    have gH := hbr.2
    have gF := (rho_eq_iff_eqmGap T hys.le hbor).1 h2
    have fH := eqm_inflow T hR0 hI gH
    have fF := eqm_inflow T hR0 hIs gF
    unfold inflowFn at fH fF
    obtain ⟨_, hRI⟩ := equilibrium_bounds T hR0 hy.le hbr.1 hI gH
    have hdI := T.dprob_pos I hI.le
    have hdIs := T.dprob_pos Is hIs.le
    have hpI := T.prob_pos hI
    have hpIs := T.prob_pos hIs
    -- the second factor is positive at `I` and larger at `I*`
    have f2pos : 0 < Z / R - 1 / T.dprob I := by
      rw [sub_pos, div_lt_div_iff₀ hdI hR0]; linarith
    have f2le : Z / R - 1 / T.dprob I ≤ Z / R - 1 / T.dprob Is := by
      have := (T.dprob_strictAnti (mem_Ici.2 hIs.le) (mem_Ici.2 hI.le) hlt).le
      have : 1 / T.dprob Is ≤ 1 / T.dprob I := one_div_le_one_div_of_le hdI this
      linarith
    -- the average product falls: `I π(I*) > I* π(I)`
    have havg := T.avg_prob_strictAnti hIs hlt
    -- `Φ(I) I* < Φ(I*) I`
    have key : (T.prob I * (Z / R - 1 / T.dprob I)) * Is <
        (T.prob Is * (Z / R - 1 / T.dprob Is)) * I := by
      have s1 : T.prob I * Is * (Z / R - 1 / T.dprob I) <
          T.prob Is * I * (Z / R - 1 / T.dprob I) := by
        apply mul_lt_mul_of_pos_right _ f2pos; linarith
      have s2 : T.prob Is * I * (Z / R - 1 / T.dprob I) ≤
          T.prob Is * I * (Z / R - 1 / T.dprob Is) :=
        mul_le_mul_of_nonneg_left f2le (by positivity)
      nlinarith
    rw [← fH, ← fF] at key
    -- so `y* I < y I*`, and with `IS` this is `(1 − s) I < y`
    have hcross : ys * I < y * Is := by nlinarith
    have h1s : 0 < 1 - s := by linarith
    have : (1 - s) * I * (I + Is) < y * (I + Is) := by
      have e : (1 - s) * I * (I + Is) = (y + ys) * I := by rw [mul_right_comm, hIS]
      rw [e]; nlinarith
    exact lt_of_mul_lt_mul_right this (by linarith)

/-- **The rate functions at the first-best point `A`** (O&R p. 414–415): with `y > y*`, at the
full-information allocation `I = I* = (y + y*)/(2(1 − s))` Home's rate strictly exceeds
Foreign's, so `ρρ` cannot intersect `IS` at `A`. -/
theorem rho_at_A (T : SuccessProb) {Z s y ys : ℝ} (hZ : 0 < Z) (hs0 : 0 ≤ s) (hs1 : s < 1)
    (hys : 0 < ys) (hyy : ys < y) :
    rhoExt T Z ys ((y + ys) / (2 * (1 - s))) < rhoExt T Z y ((y + ys) / (2 * (1 - s))) := by
  have h1s : 0 < 1 - s := by linarith
  have hA : ys < (y + ys) / (2 * (1 - s)) := by
    rw [lt_div_iff₀ (by linarith)]; nlinarith
  exact (rhoExt_mono_wealth T hZ hys hyy.le (div_pos (by linarith) (by linarith)).le).2 hA hyy

/-- **The `ρρ` locus is upward sloping** (O&R p. 414, (53), Fig. 6.12): along
`ρ(I, y) = ρ(I*, y*)` a higher `I` goes with a higher `I*`. -/
theorem rhoRho_upward (T : SuccessProb) {Z y ys I₁ I₂ J₁ J₂ : ℝ} (hZ : 0 < Z) (hy : 0 < y)
    (hys : 0 < ys) (hI₁ : 0 ≤ I₁) (hJ₁ : 0 ≤ J₁) (hJ₂ : 0 ≤ J₂)
    (h₁ : rhoExt T Z y I₁ = rhoExt T Z ys J₁) (h₂ : rhoExt T Z y I₂ = rhoExt T Z ys J₂)
    (hlt : I₁ < I₂) : J₁ < J₂ := by
  have a := rhoExt_strictAntiOn T hZ hy (mem_Ici.2 hI₁) (mem_Ici.2 (by linarith)) hlt
  by_contra hle
  push Not at hle
  have b := (rhoExt_strictAntiOn T hZ hys).antitoneOn (mem_Ici.2 hJ₂) (mem_Ici.2 hJ₁) hle
  linarith

/-- With equal endowments the equilibrium is symmetric, `I = I*`. -/
theorem eqm_symmetric (T : SuccessProb) {Z s y R I Is : ℝ} (hZ : 0 < Z) (hy : 0 < y)
    (h : IsEqm T Z s y y R I Is) : I = Is := by
  obtain ⟨hI, hIs, h1, h2, _⟩ := h
  by_contra hne
  rcases lt_or_gt_of_ne hne with hl | hl
  · have := rhoExt_strictAntiOn T hZ hy (mem_Ici.2 hI.le) (mem_Ici.2 hIs.le) hl; linarith
  · have := rhoExt_strictAntiOn T hZ hy (mem_Ici.2 hIs.le) (mem_Ici.2 hI.le) hl; linarith

/-! ## Efficiency and the output loss -/

/-- **Expected world output is maximised by equal investment** (O&R p. 413): for `I, I* ≥ 0` with
`I + I* = K`, `π(I) + π(I*) ≤ 2π(K/2)`, with equality iff `I = I*`. -/
theorem world_output_le (T : SuccessProb) {I Is K : ℝ} (hI : 0 ≤ I) (hIs : 0 ≤ Is)
    (hK : I + Is = K) :
    T.prob I + T.prob Is ≤ 2 * T.prob (K / 2) ∧
      (T.prob I + T.prob Is = 2 * T.prob (K / 2) ↔ I = Is) := by
  have hm : (I + Is) / 2 = K / 2 := by rw [hK]
  constructor
  · rcases eq_or_ne I Is with h | h
    · rw [← hm, h]; ring_nf; rfl
    · have := T.prob_midpoint_lt hI hIs h; rw [hm] at this; linarith
  · constructor
    · intro heq
      by_contra h
      have := T.prob_midpoint_lt hI hIs h; rw [hm] at this; linarith
    · intro h; rw [← hm, h]; ring_nf

/-- **The full-information equilibrium is `A`** (O&R p. 413): with full information both
countries invest where `π'(I)Z = R`, so `I = I* = (y + y*)/(2(1 − s))`. -/
theorem fullInfo_eqm (T : SuccessProb) {Z s y ys R I Is : ℝ} (hZ : 0 < Z) (hs1 : s < 1)
    (hI : 0 ≤ I) (hIs : 0 ≤ Is) (h1 : T.dprob I * Z = R) (h2 : T.dprob Is * Z = R)
    (hIS : (1 - s) * (I + Is) = y + ys) :
    I = Is ∧ I = (y + ys) / (2 * (1 - s)) := by
  have hII : I = Is := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hl | hl
    · have := T.dprob_strictAnti (mem_Ici.2 hI) (mem_Ici.2 hIs) hl; nlinarith
    · have := T.dprob_strictAnti (mem_Ici.2 hIs) (mem_Ici.2 hI) hl; nlinarith
  refine ⟨hII, ?_⟩
  have h1s : 0 < 1 - s := by linarith
  rw [eq_div_iff (by positivity)]
  rw [← hII] at hIS
  linarith

/-- **Efficiency iff equal wealth** (O&R p. 415: "only with an equal distribution of initial
wealth among entrepreneurs worldwide would the world economy attain efficient investment"): in
the equilibrium, marginal products are equalised (`I = I*`) iff `y = y*`. -/
theorem eqm_efficient_iff (T : SuccessProb) {Z s y ys R I Is : ℝ} (hZ : 0 < Z) (hs0 : 0 ≤ s)
    (hy : 0 < y) (hys : 0 < ys) (h : IsEqm T Z s y ys R I Is) :
    (T.dprob I = T.dprob Is ↔ y = ys) ∧ (I = Is ↔ y = ys) := by
  have hII : I = Is ↔ y = ys := by
    constructor
    · intro hI
      by_contra hne
      rcases lt_or_gt_of_ne hne with hl | hl
      · have := richer_invests_more T hZ hs0 hy hl h.swap; linarith
      · have := richer_invests_more T hZ hs0 hys hl h; linarith
    · intro he
      rw [← he] at h
      exact eqm_symmetric T hZ hy h
  refine ⟨?_, hII⟩
  rw [← hII]
  constructor
  · intro hd
    by_contra hne
    rcases lt_or_gt_of_ne hne with hl | hl
    · have := T.dprob_strictAnti (mem_Ici.2 h.1.le) (mem_Ici.2 h.2.1.le) hl; linarith
    · have := T.dprob_strictAnti (mem_Ici.2 h.2.1.le) (mem_Ici.2 h.1.le) hl; linarith
  · intro hI; rw [hI]

/-- **The output loss** (O&R p. 415: "with unequal entrepreneurial wealth, expected world output
therefore is lower than under full information"): if `y ≠ y*`, expected world output
`Z(π(I) + π(I*))` (per entrepreneur pair) is strictly below its full-information value
`2Zπ((y + y*)/(2(1 − s)))`. -/
theorem output_loss (T : SuccessProb) {Z s y ys R I Is : ℝ} (hZ : 0 < Z) (hs0 : 0 ≤ s)
    (hs1 : s < 1) (hy : 0 < y) (hys : 0 < ys) (hne : y ≠ ys) (h : IsEqm T Z s y ys R I Is) :
    Z * (T.prob I + T.prob Is) < Z * (2 * T.prob ((y + ys) / (2 * (1 - s)))) := by
  have hIne : I ≠ Is := fun hI => hne ((eqm_efficient_iff T hZ hs0 hy hys h).2.1 hI)
  obtain ⟨hI, hIs, _, _, hIS⟩ := h
  have h1s : 0 < 1 - s := by linarith
  have hK : I + Is = (y + ys) / (1 - s) := by rw [eq_div_iff h1s.ne']; linarith
  obtain ⟨hle, hiff⟩ := world_output_le T hI.le hIs.le hK
  have hlt : T.prob I + T.prob Is < 2 * T.prob ((y + ys) / (1 - s) / 2) :=
    lt_of_le_of_ne hle (fun he => hIne (hiff.1 he))
  have e : (y + ys) / (1 - s) / 2 = (y + ys) / (2 * (1 - s)) := by field_simp
  rw [e] at hlt
  exact mul_lt_mul_of_pos_left hlt hZ


/-! ## Exercise 4(b) completed: the full tax equilibrium (p. 427)

Each entrepreneur (wealth `y > 0`) takes the success tax `τ` as given and faces payoff `Z − τ`;
the government budget is `π(I)τ = D` (debt service `D = D^G` per entrepreneur). By
`rhoExt_eq_iff`, the entrepreneur's optimal response to `R` is `rhoExt(Z − τ, y, I) = R`, covering
both the borrowing regime (`I > y`) and self-financing (`I ≤ y`). We show the equilibria are
exactly the solutions of `Γ(I) = D` for the **debt capacity**
`Γ(I) = π(I)(Z − R[1/π'(I) + max(I − y, 0)/π(I)])`, a continuous function with `Γ(0) = 0` and
`Γ ≤ 0` from `Ī` on. Hence: an equilibrium exists iff `D ≤ D_max = max Γ`; for `0 < D < D_max`
there are **at least two** equilibria (a debt-overhang trap with low investment beside the
normal one); the normal equilibrium falls as `D` rises; and it switches from the borrowing to
the self-financing regime as `D` crosses `D_sw = max_{[y, Ī]} Γ ≥ Γ(y) = π(y)(Z − R/π'(y))`. -/

/-- The denominator `1/π'(I) + extTerm` is continuous on `[0, ∞)` (`y > 0`). -/
theorem den_continuousOn (T : SuccessProb) {y : ℝ} (hy : 0 < y) :
    ContinuousOn (fun I => 1 / T.dprob I + extTerm T y I) (Ici 0) := by
  have hmax : ContinuousOn (fun I : ℝ => max I y) (Ici 0) :=
    (continuous_id.max continuous_const).continuousOn
  have hp : ContinuousOn (fun I => T.prob (max I y)) (Ici 0) :=
    T.continuousOn_prob.comp hmax (fun I _ => mem_Ici.2 (le_trans hy.le (le_max_right I y)))
  have hext : ContinuousOn (extTerm T y) (Ici 0) := by
    unfold extTerm
    exact ((continuous_id.sub continuous_const).max continuous_const).continuousOn.div hp
      (fun I _ => (T.prob_pos (lt_of_lt_of_le hy (le_max_right I y))).ne')
  exact (continuousOn_const.div T.dprob_continuousOn (fun I hI => (T.dprob_pos I hI).ne')).add
    hext

/-- The debt capacity `Γ(I) = π(I)(Z − R·[1/π'(I) + extTerm])`: the debt service compatible with
investment `I` at rate `R` (Exercise 4(b)). -/
noncomputable def debtCapacity (T : SuccessProb) (Z R y I : ℝ) : ℝ :=
  T.prob I * (Z - R * (1 / T.dprob I + extTerm T y I))

/-- **Exercise 4(b): equilibrium ⇔ `Γ(I) = D`.** With the tax `τ = D/π(I)` balancing the budget,
`I > 0` is an equilibrium (each entrepreneur's optimal response to `R` given `τ`) iff
`Γ(I) = D`. -/
theorem ex4b_eqm_iff_capacity (T : SuccessProb) {Z R y D I : ℝ} (hy : 0 < y) (hI : 0 < I) :
    rhoExt T (Z - D / T.prob I) y I = R ↔ debtCapacity T Z R y I = D := by
  have hp := T.prob_pos hI
  have hden := den_pos T (I := I) hy hI.le
  unfold rhoExt debtCapacity
  rw [div_eq_iff hden.ne']
  constructor
  · intro h
    have : Z - R * (1 / T.dprob I + extTerm T y I) = D / T.prob I := by linarith
    rw [this]; field_simp
  · intro h
    have : D / T.prob I = Z - R * (1 / T.dprob I + extTerm T y I) := by
      rw [← h]; field_simp
    linarith

/-- In an Exercise 4(b) equilibrium the entrepreneur's net success payoff `Z − τ` is positive,
and his response is classified by `rhoExt_eq_iff` (borrowing regime or self-financing). -/
theorem ex4b_eqm_regimes (T : SuccessProb) {Z R y D I : ℝ} (hR : 0 < R) (hy : 0 < y)
    (hI : 0 < I) (h : rhoExt T (Z - D / T.prob I) y I = R) :
    0 < Z - D / T.prob I ∧
      ((y < I ∧ R < T.dprob y * (Z - D / T.prob I) ∧
          eqmGap T (Z - D / T.prob I) R y I = 0) ∨
        (I ≤ y ∧ T.dprob I * (Z - D / T.prob I) = R)) := by
  have hZ' : 0 < Z - D / T.prob I := by
    have hden := den_pos T (I := I) hy hI.le
    unfold rhoExt at h
    by_contra hh; push Not at hh
    have : (Z - D / T.prob I) / (1 / T.dprob I + extTerm T y I) ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg hh hden.le
    linarith
  exact ⟨hZ', (rhoExt_eq_iff T hZ' hy hI).1 h⟩

/-- `Γ` is continuous on `[0, ∞)`. -/
theorem debtCapacity_continuousOn (T : SuccessProb) (Z R : ℝ) {y : ℝ} (hy : 0 < y) :
    ContinuousOn (debtCapacity T Z R y) (Ici 0) := by
  unfold debtCapacity
  exact T.continuousOn_prob.mul (continuousOn_const.sub
    (continuousOn_const.mul (den_continuousOn T hy)))

/-- `Γ(0) = 0`. -/
theorem debtCapacity_zero (T : SuccessProb) (Z R y : ℝ) : debtCapacity T Z R y 0 = 0 := by
  simp [debtCapacity, T.prob_zero]

/-- `Γ ≤ 0` from the first-best level on: for `I ≥ Ī` (`π'(Ī)Z = R`) no debt can be serviced. -/
theorem debtCapacity_nonpos (T : SuccessProb) {Z R y Ibar I : ℝ} (hR : 0 < R) (hy : 0 < y)
    (hIb : 0 ≤ Ibar) (hIbar : T.dprob Ibar * Z = R) (hI : Ibar ≤ I) :
    debtCapacity T Z R y I ≤ 0 := by
  have hI0 : 0 ≤ I := hIb.trans hI
  have hd := T.dprob_pos I hI0
  have hdle := T.dprob_le_of_le hIb hI
  have hext := extTerm_nonneg T (I := I) hy
  have hp := T.prob_nonneg hI0
  unfold debtCapacity
  apply mul_nonpos_of_nonneg_of_nonpos hp
  have : Z ≤ R * (1 / T.dprob I) := by
    rw [mul_one_div, le_div_iff₀ hd]; nlinarith
  nlinarith

/-- `Γ(y) = π(y)(Z − R/π'(y))`, positive in the borrowing regime `y < Ī`. -/
theorem debtCapacity_at_wealth (T : SuccessProb) {Z R y : ℝ} (hy : 0 < y)
    (hyR : R < T.dprob y * Z) :
    debtCapacity T Z R y y = T.prob y * (Z - R / T.dprob y) ∧ 0 < debtCapacity T Z R y y := by
  have hd := T.dprob_pos y hy.le
  have h1 : debtCapacity T Z R y y = T.prob y * (Z - R / T.dprob y) := by
    unfold debtCapacity; rw [extTerm_of_le T le_rfl]; ring
  refine ⟨h1, ?_⟩
  rw [h1]
  have : 0 < Z - R / T.dprob y := by rw [sub_pos, div_lt_iff₀ hd]; linarith
  exact mul_pos (T.prob_pos hy) this

/-- **Exercise 4(b): existence iff the debt is within capacity.** In the borrowing regime
`0 < y < Ī`, there is `D_max ≥ Γ(y) > 0` (the maximum of `Γ`) such that for every `D > 0` an
equilibrium exists iff `D ≤ D_max`. Every equilibrium has `I < Ī`. -/
theorem ex4b_existence (T : SuccessProb) {Z R y Ibar : ℝ} (hR : 0 < R) (hy : 0 < y)
    (hIb : 0 < Ibar) (hIbar : T.dprob Ibar * Z = R) (hyR : R < T.dprob y * Z) :
    ∃ Imax ∈ Icc 0 Ibar, debtCapacity T Z R y y ≤ debtCapacity T Z R y Imax ∧
      (∀ I, 0 ≤ I → debtCapacity T Z R y I ≤ debtCapacity T Z R y Imax) ∧
      ∀ D, 0 < D → ((∃ I, 0 < I ∧ debtCapacity T Z R y I = D) ↔
        D ≤ debtCapacity T Z R y Imax) := by
  have hcont := debtCapacity_continuousOn T Z R hy
  obtain ⟨Imax, hImax, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 hIb.le)
    (hcont.mono (fun x hx => mem_Ici.2 hx.1))
  have hyIb : y < Ibar := by
    by_contra h; push Not at h
    have := T.dprob_le_of_le hIb.le h
    have hZ : 0 < Z := by
      have := T.dprob_pos y hy.le
      by_contra h'; push Not at h'; nlinarith
    nlinarith
  obtain ⟨_, hGy⟩ := debtCapacity_at_wealth T hy hyR
  have hglob : ∀ I, 0 ≤ I → debtCapacity T Z R y I ≤ debtCapacity T Z R y Imax := by
    intro I hI
    rcases le_or_gt I Ibar with h | h
    · exact hmax ⟨hI, h⟩
    · have := debtCapacity_nonpos T hR hy hIb.le hIbar h.le
      have := hmax ⟨hy.le, hyIb.le⟩
      simp only [Set.mem_ofPred_eq] at this
      linarith
  refine ⟨Imax, hImax, hglob y hy.le, hglob, ?_⟩
  intro D hD
  constructor
  · rintro ⟨I, hI, hG⟩; rw [← hG]; exact hglob I hI.le
  · intro hle
    obtain ⟨I, hI, hIG⟩ := intermediate_value_Icc hImax.1
      (hcont.mono (fun x hx => mem_Ici.2 hx.1))
      ⟨by rw [debtCapacity_zero]; exact hD.le, hle⟩
    refine ⟨I, ?_, hIG⟩
    rcases hI.1.lt_or_eq with h | h
    · exact h
    · rw [← h, debtCapacity_zero] at hIG; linarith

/-- **Exercise 4(b): multiplicity (a debt-overhang trap).** If `0 < D < Γ(I₀)` for some `I₀ ≥ 0`
(e.g. `I₀ = y`, `D < π(y)(Z − R/π'(y))`), there are at least two equilibria `I₁ < I₀ < I₂`. -/
theorem ex4b_two_equilibria (T : SuccessProb) {Z R y Ibar D I₀ : ℝ} (hR : 0 < R) (hy : 0 < y)
    (hIb : 0 < Ibar) (hIbar : T.dprob Ibar * Z = R) (hI₀ : 0 ≤ I₀) (hD : 0 < D)
    (hDI : D < debtCapacity T Z R y I₀) :
    ∃ I₁ I₂, 0 < I₁ ∧ I₁ < I₀ ∧ I₀ < I₂ ∧ I₂ < Ibar ∧
      debtCapacity T Z R y I₁ = D ∧ debtCapacity T Z R y I₂ = D := by
  have hcont := debtCapacity_continuousOn T Z R hy
  have hI₀b : I₀ < Ibar := by
    by_contra h; push Not at h
    have := debtCapacity_nonpos T hR hy hIb.le hIbar h
    linarith
  obtain ⟨I₁, hI₁, hG₁⟩ := intermediate_value_Icc hI₀
    (hcont.mono (fun x hx => mem_Ici.2 hx.1)) ⟨by rw [debtCapacity_zero]; exact hD.le, hDI.le⟩
  obtain ⟨I₂, hI₂, hG₂⟩ := intermediate_value_Icc' hI₀b.le
    (hcont.mono (fun x hx => mem_Ici.2 (hI₀.trans hx.1)))
    ⟨(debtCapacity_nonpos T hR hy hIb.le hIbar le_rfl).trans hD.le, hDI.le⟩
  refine ⟨I₁, I₂, ?_, ?_, ?_, ?_, hG₁, hG₂⟩
  · rcases hI₁.1.lt_or_eq with h | h
    · exact h
    · rw [← h, debtCapacity_zero] at hG₁; linarith
  · rcases hI₁.2.lt_or_eq with h | h
    · exact h
    · rw [h] at hG₁; linarith
  · rcases hI₂.1.lt_or_eq with h | h
    · exact h
    · rw [← h] at hG₂; linarith
  · rcases hI₂.2.lt_or_eq with h | h
    · exact h
    · rw [h] at hG₂; linarith [debtCapacity_nonpos T hR hy hIb.le hIbar le_rfl]

/-- **Exercise 4(b): the normal equilibrium falls with the debt.** For `0 < D < D'`, every
equilibrium `I'` at debt `D'` lies strictly below some equilibrium at debt `D`; so the largest
(normal) equilibrium is strictly decreasing in the debt (the overhang). -/
theorem ex4b_normal_eqm_decreasing (T : SuccessProb) {Z R y Ibar D D' I' : ℝ} (hR : 0 < R)
    (hy : 0 < y) (hIb : 0 < Ibar) (hIbar : T.dprob Ibar * Z = R) (hD : 0 < D) (hDD : D < D')
    (hI' : 0 ≤ I') (hG' : debtCapacity T Z R y I' = D') :
    ∃ I, I' < I ∧ I < Ibar ∧ debtCapacity T Z R y I = D := by
  have hcont := debtCapacity_continuousOn T Z R hy
  have hI'b : I' < Ibar := by
    by_contra h; push Not at h
    have := debtCapacity_nonpos T hR hy hIb.le hIbar h
    linarith
  obtain ⟨I, hI, hG⟩ := intermediate_value_Icc' hI'b.le
    (hcont.mono (fun x hx => mem_Ici.2 (hI'.trans hx.1)))
    ⟨(debtCapacity_nonpos T hR hy hIb.le hIbar le_rfl).trans hD.le, by rw [hG']; exact hDD.le⟩
  refine ⟨I, ?_, ?_, hG⟩
  · rcases hI.1.lt_or_eq with h | h
    · exact h
    · rw [← h] at hG; linarith
  · rcases hI.2.lt_or_eq with h | h
    · exact h
    · rw [h] at hG; linarith [debtCapacity_nonpos T hR hy hIb.le hIbar le_rfl]

/-- **Exercise 4(b): the regime switch.** Let `D_sw = max_{[y, Ī]} Γ` (which is at least
`Γ(y) = π(y)(Z − R/π'(y))`). If `D < D_sw` (and `D > 0`) there is an equilibrium in the borrowing
regime `I > y`; if `D > D_sw`, every equilibrium is in the self-financing regime `I < y`. -/
theorem ex4b_regime_switch (T : SuccessProb) {Z R y Ibar : ℝ} (hR : 0 < R) (hy : 0 < y)
    (hIb : 0 < Ibar) (hIbar : T.dprob Ibar * Z = R) (hyR : R < T.dprob y * Z) :
    ∃ Isw ∈ Icc y Ibar, debtCapacity T Z R y y ≤ debtCapacity T Z R y Isw ∧
      (∀ D, 0 < D → D < debtCapacity T Z R y Isw →
        ∃ I, y < I ∧ debtCapacity T Z R y I = D) ∧
      (∀ D I, debtCapacity T Z R y Isw < D → 0 < I → debtCapacity T Z R y I = D → I < y) := by
  have hcont := debtCapacity_continuousOn T Z R hy
  have hyIb : y < Ibar := by
    by_contra h; push Not at h
    have := T.dprob_le_of_le hIb.le h
    have hZ : 0 < Z := by
      have := T.dprob_pos y hy.le
      by_contra h'; push Not at h'; nlinarith
    nlinarith
  obtain ⟨Isw, hIsw, hmax⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.2 hyIb.le)
    (hcont.mono (fun x hx => mem_Ici.2 (hy.le.trans hx.1)))
  have hmax' : ∀ I ∈ Icc y Ibar, debtCapacity T Z R y I ≤ debtCapacity T Z R y Isw :=
    fun I hI => hmax hI
  refine ⟨Isw, hIsw, hmax' y ⟨le_rfl, hyIb.le⟩, ?_, ?_⟩
  · intro D hD hDl
    obtain ⟨I₁, I₂, _, _, h3, _, _, hG₂⟩ :=
      ex4b_two_equilibria T hR hy hIb hIbar (hy.le.trans hIsw.1) hD hDl
    exact ⟨I₂, lt_of_le_of_lt hIsw.1 h3, hG₂⟩
  · intro D I hD hI hG
    by_contra h; push Not at h
    rcases le_or_gt I Ibar with h' | h'
    · have := hmax' I ⟨h, h'⟩; linarith
    · have := debtCapacity_nonpos T hR hy hIb.le hIbar h'.le
      have := hmax' y ⟨le_rfl, hyIb.le⟩
      obtain ⟨_, hGy⟩ := debtCapacity_at_wealth T hy hyR
      linarith

/-- For `D ≤ R y` there is at most one equilibrium in the borrowing regime (the effective wealth
`y − D/R` is nonnegative, so the text's uniqueness argument applies). -/
theorem ex4b_borrowing_unique (T : SuccessProb) {Z R y D I J : ℝ} (hR : 0 < R) (hy : 0 < y)
    (hD : D ≤ R * y) (hI : y < I) (hJ : y < J) (hGI : debtCapacity T Z R y I = D)
    (hGJ : debtCapacity T Z R y J = D) : I = J := by
  have hI0 : 0 < I := hy.trans hI
  have hJ0 : 0 < J := hy.trans hJ
  have toGap : ∀ K, y < K → debtCapacity T Z R y K = D → eqmGap T Z R (y - D / R) K = 0 := by
    intro K hK hG
    have hK0 : 0 < K := hy.trans hK
    have h1 := (ex4b_eqm_iff_capacity T hy hK0).2 hG
    rw [rho_eq_iff_eqmGap T hy.le hK] at h1
    exact (ex4b_overhang_equivalence T hR hK0).1 h1
  have hw : 0 ≤ y - D / R := by
    rw [sub_nonneg, div_le_iff₀ hR]; linarith
  have gI := toGap I hI hGI
  have gJ := toGap J hJ hGJ
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have := eqmGap_strictAntiOn T Z hR hw (show I ∈ Ioi (0 : ℝ) from hI0)
      (show J ∈ Ioi (0 : ℝ) from hJ0) h
    linarith
  · have := eqmGap_strictAntiOn T Z hR hw (show J ∈ Ioi (0 : ℝ) from hJ0)
      (show I ∈ Ioi (0 : ℝ) from hI0) h
    linarith

/-! ## Foreign government debt to Home (p. 415)

Foreign's government owes `d > 0` per Foreign entrepreneur to Home at date 2 and services it by
taxing successful Foreign firms, `τ = d/π(I*)` (the mechanism of Exercise 4(b)). Date-1
resources are unaffected, so `IS` is unchanged, and Home's rate function is unchanged (Home agents
have linear date-2 utility; the receipt is lump sum). Foreign's rate function becomes
`ρ_d(I*) = rhoExt(Z − d/π(I*), y*, I*)`. We prove the book's claim — `ρρ` shifts up and in every
debt equilibrium Foreign invests less, Home more, and the world rate is lower than without debt
— but also that the equilibrium is **no longer unique**: for all small `d > 0` there are at
least two equilibria (one a debt trap with low Foreign investment), and for large `d` none. -/

/-- Foreign's rate function with debt service `d`. -/
noncomputable def rhoDebt (T : SuccessProb) (Z ys d Is : ℝ) : ℝ :=
  rhoExt T (Z - d / T.prob Is) ys Is

/-- An equilibrium with Foreign debt `d` (O&R p. 415). -/
def IsEqmDebt (T : SuccessProb) (Z s y ys d R I Is : ℝ) : Prop :=
  0 < R ∧ 0 < I ∧ 0 < Is ∧ rhoExt T Z y I = R ∧ rhoDebt T Z ys d Is = R ∧
    (1 - s) * (I + Is) = y + ys

/-- **`ρρ` shifts up** (O&R p. 415): debt lowers Foreign's rate at every `I* > 0`. -/
theorem rhoDebt_lt (T : SuccessProb) {Z ys d Is : ℝ} (hys : 0 < ys) (hd : 0 < d) (hIs : 0 < Is) :
    rhoDebt T Z ys d Is < rhoExt T Z ys Is := by
  unfold rhoDebt rhoExt
  have := T.prob_pos hIs
  exact div_lt_div_of_pos_right (by have : 0 < d / T.prob Is := by positivity
                                    linarith) (den_pos T hys hIs.le)

/-- **Debt depresses Foreign investment** (O&R p. 415): comparing any equilibrium with debt
`d > 0` to the equilibrium without debt, Foreign invests strictly less, Home strictly more, and
the world interest rate is strictly lower. -/
theorem debt_depresses_foreign (T : SuccessProb) {Z s y ys d R I Is R₀ I₀ Is₀ : ℝ}
    (hZ : 0 < Z) (hy : 0 < y) (hys : 0 < ys) (hd : 0 < d) (hs1 : s < 1)
    (h : IsEqmDebt T Z s y ys d R I Is) (h₀ : IsEqm T Z s y ys R₀ I₀ Is₀) :
    Is < Is₀ ∧ I₀ < I ∧ R < R₀ := by
  obtain ⟨_, hI, hIs, h1, h2, hIS⟩ := h
  obtain ⟨hI₀, hIs₀, h1₀, h2₀, hIS₀⟩ := h₀
  have h1s : (1 - s) ≠ 0 := by linarith
  have hsum : I + Is = I₀ + Is₀ := by
    have := hIS.trans hIS₀.symm
    exact mul_left_cancel₀ h1s this
  have hIsl : Is < Is₀ := by
    by_contra hle; push Not at hle
    have hIle : I ≤ I₀ := by linarith
    have a : R₀ ≤ R := by
      rw [← h1, ← h1₀]
      exact (rhoExt_strictAntiOn T hZ hy).antitoneOn (mem_Ici.2 hI.le) (mem_Ici.2 hI₀.le) hIle
    have b : R < R₀ := by
      rw [← h2, ← h2₀]
      calc rhoDebt T Z ys d Is < rhoExt T Z ys Is := rhoDebt_lt T hys hd hIs
        _ ≤ rhoExt T Z ys Is₀ := (rhoExt_strictAntiOn T hZ hys).antitoneOn
            (mem_Ici.2 hIs₀.le) (mem_Ici.2 hIs.le) hle
    linarith
  have hIg : I₀ < I := by linarith
  refine ⟨hIsl, hIg, ?_⟩
  rw [← h1, ← h1₀]
  exact rhoExt_strictAntiOn T hZ hy (mem_Ici.2 hI₀.le) (mem_Ici.2 hI.le) hIg

/-- **Large debt: no equilibrium.** If `d ≥ Zπ(K)` with `K = (y + y*)/(1 − s)`, Foreign's net
success payoff is negative at every feasible `I*` and no equilibrium exists. -/
theorem debt_no_eqm_of_large (T : SuccessProb) {Z s y ys d R I Is : ℝ} (hZ : 0 < Z)
    (hys : 0 < ys) (hs1 : s < 1) (hd : Z * T.prob ((y + ys) / (1 - s)) ≤ d) :
    ¬ IsEqmDebt T Z s y ys d R I Is := by
  rintro ⟨hR, hI, hIs, _, h2, hIS⟩
  have h1s : 0 < 1 - s := by linarith
  have hK : Is < (y + ys) / (1 - s) := by
    rw [lt_div_iff₀ h1s]; nlinarith
  have hp := T.prob_pos hIs
  have hpK := T.prob_strictMonoOn (mem_Ici.2 hIs.le) (mem_Ici.2 (hIs.le.trans hK.le)) hK
  have hneg : Z - d / T.prob Is < 0 := by
    rw [sub_neg, lt_div_iff₀ hp]
    nlinarith
  have : rhoDebt T Z ys d Is < 0 := by
    unfold rhoDebt rhoExt
    exact div_neg_of_neg_of_pos hneg (den_pos T hys hIs.le)
  linarith

/-- **Multiplicity with debt** (correcting the uniqueness implicit on O&R p. 415): if at some
`I₁* ∈ (0, K)` Foreign's debt-adjusted rate exceeds Home's rate at `K − I₁*`, there are at least
two equilibria, one with `I* < I₁*` (a debt trap) and one with `I* > I₁*`. -/
theorem debt_two_equilibria (T : SuccessProb) {Z s y ys d Is₁ : ℝ} (hZ : 0 < Z) (hy : 0 < y)
    (hys : 0 < ys) (hd : 0 < d) (hs1 : s < 1) (hIs₁ : 0 < Is₁)
    (hIs₁K : Is₁ < (y + ys) / (1 - s))
    (hgap : rhoExt T Z y ((y + ys) / (1 - s) - Is₁) < rhoDebt T Z ys d Is₁) :
    ∃ R₁ I₁ Js₁ R₂ I₂ Js₂, IsEqmDebt T Z s y ys d R₁ I₁ Js₁ ∧ IsEqmDebt T Z s y ys d R₂ I₂ Js₂ ∧
      Js₁ < Is₁ ∧ Is₁ < Js₂ := by
  have h1s : 0 < 1 - s := by linarith
  set K := (y + ys) / (1 - s) with hK
  set G : ℝ → ℝ := fun x => rhoDebt T Z ys d x - rhoExt T Z y (K - x) with hG
  have hGc : ContinuousOn G (Icc 0 K ∩ Ioi 0) := by
    have hpc : ContinuousOn T.prob (Ioi 0) := T.continuousOn_prob.mono Ioi_subset_Ici_self
    have hdebt : ContinuousOn (rhoDebt T Z ys d) (Ioi 0) := by
      unfold rhoDebt rhoExt
      exact (continuousOn_const.sub (continuousOn_const.div hpc
        (fun x hx => (T.prob_pos hx).ne'))).div
        ((den_continuousOn T hys).mono Ioi_subset_Ici_self)
        (fun x hx => (den_pos T hys (le_of_lt hx)).ne')
    exact (hdebt.mono inter_subset_right).sub ((rhoExt_continuousOn T Z hy).comp
      (continuousOn_const.sub continuousOn_id) (fun x hx => mem_Ici.2 (by linarith [hx.1.2])))
  have hG1 : 0 < G Is₁ := by simp only [hG]; linarith
  -- a lower point where Foreign's net payoff vanishes: `π(ε) = d/Z`
  have hpos : 0 < Z - d / T.prob Is₁ := by
    have hr := rhoExt_pos T hZ hy (show 0 ≤ K - Is₁ by linarith)
    by_contra hh; push Not at hh
    have : rhoDebt T Z ys d Is₁ ≤ 0 := by
      unfold rhoDebt rhoExt
      exact div_nonpos_of_nonpos_of_nonneg hh (den_pos T hys hIs₁.le).le
    linarith
  have hp1 := T.prob_pos hIs₁
  have hdZ : d / Z < T.prob Is₁ := by
    rw [div_lt_iff₀ hZ]
    have : d / T.prob Is₁ < Z := by linarith
    rw [div_lt_iff₀ hp1] at this; linarith
  obtain ⟨ε, hε, hεv⟩ := intermediate_value_Icc hIs₁.le
    (T.continuousOn_prob.mono (fun x hx => mem_Ici.2 hx.1))
    ⟨by rw [T.prob_zero]; positivity, hdZ.le⟩
  have hε0 : 0 < ε := by
    rcases hε.1.lt_or_eq with h | h
    · exact h
    · rw [← h, T.prob_zero] at hεv; have : 0 < d / Z := by positivity
      linarith
  have hGε : G ε < 0 := by
    simp only [hG]
    have : rhoDebt T Z ys d ε = 0 := by
      unfold rhoDebt rhoExt; rw [hεv]; field_simp; simp
    rw [this]
    have := rhoExt_pos T hZ hy (show 0 ≤ K - ε by linarith [hε.2])
    linarith
  have hGK : G K < 0 := by
    simp only [hG, sub_self]
    have a := rhoDebt_lt T (Z := Z) hys hd (show 0 < K by linarith)
    have b := rhoExt_strictAntiOn T hZ hys (mem_Ici.2 le_rfl) (mem_Ici.2 (by linarith : (0:ℝ) ≤ K))
      (show (0 : ℝ) < K by linarith)
    rw [rhoExt_zero T hys] at b
    rw [rhoExt_zero T hy]
    linarith
  have hεIs : ε < Is₁ := by
    rcases hε.2.lt_or_eq with h | h
    · exact h
    · rw [h] at hGε; linarith
  obtain ⟨J₁, hJ₁, hGJ₁⟩ := intermediate_value_Icc hεIs.le
    (hGc.mono (fun x hx => ⟨⟨hε0.le.trans hx.1, by linarith [hx.2]⟩, hε0.trans_le hx.1⟩))
    ⟨hGε.le, hG1.le⟩
  obtain ⟨J₂, hJ₂, hGJ₂⟩ := intermediate_value_Icc' hIs₁K.le
    (hGc.mono (fun x hx => ⟨⟨hIs₁.le.trans hx.1, hx.2⟩, hIs₁.trans_le hx.1⟩))
    ⟨hGK.le, hG1.le⟩
  have hJ₁lt : J₁ < Is₁ := by
    rcases hJ₁.2.lt_or_eq with h | h
    · exact h
    · rw [h] at hGJ₁; linarith
  have hJ₁pos : 0 < J₁ := by
    rcases hJ₁.1.lt_or_eq with h | h
    · exact hε0.trans h
    · rw [← h] at hGJ₁; linarith
  have hJ₂gt : Is₁ < J₂ := by
    rcases hJ₂.1.lt_or_eq with h | h
    · exact h
    · rw [← h] at hGJ₂; linarith
  have hJ₂K : J₂ < K := by
    rcases hJ₂.2.lt_or_eq with h | h
    · exact h
    · rw [h] at hGJ₂; linarith
  have mk : ∀ J, 0 < J → J < K → G J = 0 →
      IsEqmDebt T Z s y ys d (rhoExt T Z y (K - J)) (K - J) J := by
    intro J hJ hJK hGJ
    refine ⟨rhoExt_pos T hZ hy (by linarith), by linarith, hJ, rfl, ?_, ?_⟩
    · simp only [hG] at hGJ; linarith
    · rw [hK]; field_simp; ring
  exact ⟨_, _, _, _, _, _, mk J₁ hJ₁pos (hJ₁lt.trans hIs₁K) hGJ₁,
    mk J₂ (hIs₁.trans hJ₂gt) hJ₂K hGJ₂, hJ₁lt, hJ₂gt⟩

/-- **Every small debt produces multiple equilibria** (O&R p. 415, corrected): given the
no-debt equilibrium `(R₀, I₀, I*₀)`, there is `d̄ > 0` such that for every `d ∈ (0, d̄)` there
are at least two equilibria with debt. -/
theorem small_debt_multiple_equilibria (T : SuccessProb) {Z s y ys R₀ I₀ Is₀ : ℝ} (hZ : 0 < Z)
    (hy : 0 < y) (hys : 0 < ys) (hs1 : s < 1) (h₀ : IsEqm T Z s y ys R₀ I₀ Is₀) :
    ∃ dbar, 0 < dbar ∧ ∀ d, 0 < d → d < dbar →
      ∃ R₁ I₁ Js₁ R₂ I₂ Js₂, IsEqmDebt T Z s y ys d R₁ I₁ Js₁ ∧
        IsEqmDebt T Z s y ys d R₂ I₂ Js₂ ∧ Js₁ ≠ Js₂ := by
  obtain ⟨hI₀, hIs₀, h1, h2, hIS⟩ := h₀
  have h1s : 0 < 1 - s := by linarith
  set K := (y + ys) / (1 - s) with hK
  have hsumK : I₀ + Is₀ = K := by rw [hK, eq_div_iff h1s.ne']; linarith
  set Is₁ := Is₀ / 2 with hIs₁
  have hIs₁pos : 0 < Is₁ := by positivity
  -- the no-debt gap at `I*₁` is positive
  have a : rhoExt T Z ys Is₀ < rhoExt T Z ys Is₁ :=
    rhoExt_strictAntiOn T hZ hys (mem_Ici.2 hIs₁pos.le) (mem_Ici.2 hIs₀.le) (by linarith)
  have b : rhoExt T Z y (K - Is₁) < rhoExt T Z y I₀ :=
    rhoExt_strictAntiOn T hZ hy (mem_Ici.2 hI₀.le) (mem_Ici.2 (by linarith)) (by linarith)
  set gap := rhoExt T Z ys Is₁ - rhoExt T Z y (K - Is₁) with hgap
  have hgpos : 0 < gap := by rw [hgap]; linarith
  have hp := T.prob_pos hIs₁pos
  have hden := den_pos T (I := Is₁) hys hIs₁pos.le
  refine ⟨T.prob Is₁ * (1 / T.dprob Is₁ + extTerm T ys Is₁) * gap, by positivity, ?_⟩
  intro d hd hdl
  have key : rhoExt T Z y (K - Is₁) < rhoDebt T Z ys d Is₁ := by
    have e : rhoDebt T Z ys d Is₁ = rhoExt T Z ys Is₁ -
        d / (T.prob Is₁ * (1 / T.dprob Is₁ + extTerm T ys Is₁)) := by
      unfold rhoDebt rhoExt; field_simp
    rw [e]
    have : d / (T.prob Is₁ * (1 / T.dprob Is₁ + extTerm T ys Is₁)) < gap := by
      rw [div_lt_iff₀ (by positivity)]; linarith
    linarith
  obtain ⟨R₁, I₁, J₁, R₂, I₂, J₂, e₁, e₂, hl, hr⟩ :=
    debt_two_equilibria T hZ hy hys hd hs1 hIs₁pos (by linarith) key
  exact ⟨R₁, I₁, J₁, R₂, I₂, J₂, e₁, e₂, by linarith⟩

/-- On any set where Foreign's debt-adjusted rate is strictly decreasing there is at most one
equilibrium (the sense in which the "normal" equilibrium is unique). -/
theorem debt_eqm_unique_on (T : SuccessProb) {Z s y ys d : ℝ} {A : Set ℝ} (hZ : 0 < Z)
    (hy : 0 < y) (hs1 : s < 1) (hA : StrictAntiOn (rhoDebt T Z ys d) A)
    {R I Is R' I' Is' : ℝ} (h : IsEqmDebt T Z s y ys d R I Is)
    (h' : IsEqmDebt T Z s y ys d R' I' Is') (hIs : Is ∈ A) (hIs' : Is' ∈ A) :
    Is = Is' ∧ I = I' ∧ R = R' := by
  obtain ⟨_, hI, _, h1, h2, hIS⟩ := h
  obtain ⟨_, hI', _, h1', h2', hIS'⟩ := h'
  have h1s : (1 - s) ≠ 0 := by linarith
  have hsum : I + Is = I' + Is' := mul_left_cancel₀ h1s (hIS.trans hIS'.symm)
  have hIseq : Is = Is' := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hl | hl
    · have a := hA hIs hIs' hl
      have b := rhoExt_strictAntiOn T hZ hy (mem_Ici.2 hI'.le) (mem_Ici.2 hI.le)
        (by linarith : I' < I)
      linarith
    · have a := hA hIs' hIs hl
      have b := rhoExt_strictAntiOn T hZ hy (mem_Ici.2 hI.le) (mem_Ici.2 hI'.le)
        (by linarith : I < I')
      linarith
  have hIeq : I = I' := by linarith
  exact ⟨hIseq, hIeq, by rw [← h1, ← h1', hIeq]⟩

end ObstfeldRogoff.CapitalMarketImperfections.MoralHazardTwoCountry
