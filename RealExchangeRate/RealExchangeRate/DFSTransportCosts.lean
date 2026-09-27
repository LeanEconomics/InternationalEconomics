/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# Transport costs and nontraded goods in the Ricardian model

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §4.5.5,
pp. 249–255.

A fraction `κ ∈ (0,1)` of any good shipped abroad melts in transit. Home produces the goods with
`w/w* < A(z)/(1−κ)`, Foreign those with `w/w* > (1−κ)A(z)`; the goods between the cutoffs
`z^F < z^H` are nontraded. Prices are the cheaper of domestic cost and import (CIF) cost.

* the cutoff ordering `z^F < z^H`, and nontradability of the band `(z^F, z^H)`;
* (64), the cutoff link `(1−κ)A(z^F) = A(z^H)/(1−κ)`, and for `A(z) = e^{1−2z}` (65)–(66);
* the real-exchange-rate formula for `P/P*` (from (60), using interval integrals);
* fn 41 made precise: `B̃` is strictly increasing iff `1 + log(1−κ)(1 + TB·a*(1)/L*) > 0`;
* the transfer effect (p. 255): a higher trade balance lowers `B̃`, so `w/w*` falls and both
  cutoffs move right;
* T26 (p. 254): `p(z)/p*(z) = max(1−κ, min(wa(z)/(w*a*(z)), 1/(1−κ)))` for every good, so it
  rises weakly with `w/w*` for every `z`. The book's four-class partition omits a fifth class
  for large shocks (Home exports that become Foreign exports), where the ratio jumps from `1−κ`
  to `1/(1−κ)`; the conclusion holds regardless;
* the κ > 0 Foreign productivity rise (p. 255, "you can verify"): `w/w*` falls by less than the
  factor `ν`, Home's and Foreign's real wages rise weakly on every good, Home's terms of trade
  improve.
-/

namespace ObstfeldRogoff.RealExchangeRate.DFSTransportCosts

open Set

/-- Home's price of a good with transport costs, O&R p. 250: the cheaper of the domestic cost
`w a` and the import (CIF) cost `w* a*/(1−κ)`. -/
noncomputable def homePrice (κ a aS w wS : ℝ) : ℝ := min (a * w) (aS * wS / (1 - κ))

/-- Foreign's price of a good with transport costs, O&R p. 250: the cheaper of `w a/(1−κ)`
(imported from Home) and the domestic cost `w* a*`. -/
noncomputable def foreignPrice (κ a aS w wS : ℝ) : ℝ := min (a * w / (1 - κ)) (aS * wS)

/-- O&R p. 249: Home's own production is (weakly) cheaper than importing,
`w a ≤ w* a*/(1−κ)`, iff `w/w* ≤ A/(1−κ)` with `A = a*/a`. -/
theorem home_produces_iff {κ a aS w wS : ℝ} (hκ : κ < 1) (ha : 0 < a) (hwS : 0 < wS) :
    a * w ≤ aS * wS / (1 - κ) ↔ w / wS ≤ aS / a / (1 - κ) := by
  have h1 : 0 < 1 - κ := by linarith
  rw [le_div_iff₀ h1, div_div, div_le_div_iff₀ hwS (mul_pos ha h1)]
  constructor <;> intro h <;> linarith

/-- O&R p. 249: Foreign's own production is (weakly) cheaper than importing,
`w* a* ≤ w a/(1−κ)`, iff `(1−κ)A ≤ w/w*`. -/
theorem foreign_produces_iff {κ a aS w wS : ℝ} (hκ : κ < 1) (ha : 0 < a) (hwS : 0 < wS) :
    aS * wS ≤ a * w / (1 - κ) ↔ (1 - κ) * (aS / a) ≤ w / wS := by
  have h1 : 0 < 1 - κ := by linarith
  rw [le_div_iff₀ h1, mul_div_assoc', div_le_div_iff₀ ha hwS]
  constructor <;> intro h <;> linarith

/-- Cutoff ordering, O&R pp. 249–252 (Figure 4.11): with `κ ∈ (0,1)` and `A` strictly decreasing
and positive, the cutoffs defined by `w/w* = A(z^H)/(1−κ)` and `w/w* = (1−κ)A(z^F)` satisfy
the link `(1−κ)A(z^F) = A(z^H)/(1−κ)` (fn 40) and `z^F < z^H`. -/
theorem cutoff_order {A : ℝ → ℝ} {s : Set ℝ} {κ ω zF zH : ℝ} (hA : StrictAntiOn A s)
    (hF : zF ∈ s) (hH : zH ∈ s) (hApos : 0 < A zF) (hκ0 : 0 < κ) (hκ1 : κ < 1)
    (hωH : ω = A zH / (1 - κ)) (hωF : ω = (1 - κ) * A zF) :
    (1 - κ) * A zF = A zH / (1 - κ) ∧ zF < zH := by
  have h1 : 0 < 1 - κ := by linarith
  have link : (1 - κ) * A zF = A zH / (1 - κ) := by rw [← hωF, hωH]
  refine ⟨link, ?_⟩
  have hAH : A zH = (1 - κ) * ((1 - κ) * A zF) := by
    rw [link]; field_simp
  have hlt : A zH < A zF := by
    rw [hAH]
    have : (1 - κ) * (1 - κ) < 1 := by nlinarith
    nlinarith
  by_contra hcon
  push Not at hcon
  rcases hcon.lt_or_eq with h | h
  · exact absurd (hA hH hF h) (not_lt.mpr hlt.le)
  · rw [h] at hlt; exact lt_irrefl _ hlt

/-- Nontraded band, O&R p. 250: for `z^F < z < z^H`, `(1−κ)A(z) < w/w* < A(z)/(1−κ)`, so each
country produces `z` more cheaply than it could import it. -/
theorem nontraded_band {A : ℝ → ℝ} {s : Set ℝ} {κ ω zF zH z : ℝ} (hA : StrictAntiOn A s)
    (hF : zF ∈ s) (hH : zH ∈ s) (hz : z ∈ s) (hκ1 : κ < 1)
    (hωH : ω = A zH / (1 - κ)) (hωF : ω = (1 - κ) * A zF) (hzF : zF < z) (hzH : z < zH) :
    (1 - κ) * A z < ω ∧ ω < A z / (1 - κ) := by
  have h1 : 0 < 1 - κ := by linarith
  constructor
  · rw [hωF]; exact mul_lt_mul_of_pos_left (hA hF hz hzF) h1
  · rw [hωH]; exact div_lt_div_of_pos_right (hA hz hH hzH) h1

/-- O&R (61)–(64), pp. 251–252: world spending equals world income (61), Home output is
demanded on `[0, z^H]` by Home and on `[0, z^F]` by Foreign (62), `TB = wL − PC` (63), and the
numeraire is good 1 delivered in Foreign, so `w* = 1/a*(1)`. Then
`w/w* = {−(z^H − z^F)TB/(L*/a*(1)) + z^F}(L*/L)/(1 − z^H)` (64). -/
theorem relWage_transport {w wS L LS P PS C CS TB zF zH aS1 : ℝ} (hL : 0 < L)
    (haS1 : 0 < aS1) (hwS : wS = 1 / aS1) (hzH : zH < 1)
    (h61 : P * C + PS * CS = w * L + wS * LS) (h62 : w * L = zH * (P * C) + zF * (PS * CS))
    (h63 : TB = w * L - P * C) (hLS : 0 < LS) :
    w / wS = (-(zH - zF) * TB / (LS / aS1) + zF) * (LS / L) / (1 - zH) := by
  have h1 : (1 - zH) ≠ 0 := by linarith
  have key : w * L * (1 - zH) = -(zH - zF) * TB + zF * (wS * LS) := by
    have hPS : PS * CS = w * L + wS * LS - P * C := by linarith
    rw [hPS] at h62
    have hPC : P * C = w * L - TB := by linarith
    rw [hPC] at h62
    linear_combination h62
  rw [hwS] at key ⊢
  field_simp
  field_simp at key
  linear_combination key

/-- The example productivity schedule of O&R p. 252: `A(z) = exp(1 − 2z)`. -/
noncomputable def expA (z : ℝ) : ℝ := Real.exp (1 - 2 * z)

/-- O&R p. 252: `A(z) = exp(1 − 2z)` is strictly decreasing. -/
theorem expA_strictAnti : StrictAnti expA := by
  intro x y hxy
  unfold expA
  exact Real.exp_lt_exp.mpr (by linarith)

/-- O&R (65), p. 252: for `A(z) = exp(1 − 2z)` (scaled by any `σ > 0`, e.g. `σ = 1/ν` after a
uniform Foreign productivity change), the cutoff link `(1−κ)σA(z^F) = σA(z^H)/(1−κ)` holds iff
`z^H = z^F − log(1−κ)`. -/
theorem cutoff_link_exp {κ σ zF zH : ℝ} (hκ1 : κ < 1) (hσ : 0 < σ) :
    (1 - κ) * (σ * expA zF) = σ * expA zH / (1 - κ) ↔ zH = zF - Real.log (1 - κ) := by
  have h1 : 0 < 1 - κ := by linarith
  have key : (1 - κ) * (σ * expA zF) = σ * expA zH / (1 - κ) ↔
      Real.exp (2 * Real.log (1 - κ) + (1 - 2 * zF)) = Real.exp (1 - 2 * zH) := by
    rw [Real.exp_add, show 2 * Real.log (1 - κ) = Real.log (1 - κ) + Real.log (1 - κ) by ring,
      Real.exp_add, Real.exp_log h1]
    unfold expA
    rw [eq_div_iff h1.ne']
    constructor
    · intro h; nlinarith [h]
    · intro h; rw [← h]; ring
  rw [key, Real.exp_eq_exp]
  constructor <;> intro h <;> linarith

/-- O&R (65), p. 252: the cutoffs are interior (`z^F ≥ 0`, `z^H ≤ 1`) only if the band
`z^H − z^F = −log(1−κ)` has width at most one, i.e. `κ ≤ 1 − e^{−1}`. -/
theorem interior_cutoffs_bound {κ zF zH : ℝ} (hκ1 : κ < 1) (hF : 0 ≤ zF) (hH : zH ≤ 1)
    (h65 : zH = zF - Real.log (1 - κ)) : κ ≤ 1 - Real.exp (-1) := by
  have h1 : 0 < 1 - κ := by linarith
  have : -1 ≤ Real.log (1 - κ) := by linarith
  have := Real.exp_le_exp.mpr this
  rw [Real.exp_log h1] at this
  linarith

/-- O&R (66), p. 252: the schedule `B̃(z) = {log(1−κ)TB/(L*/a*(1)) + z}(L*/L)/[1 + log(1−κ) − z]`,
written with `K = L*/a*(1)` and `lam = L*/L`. -/
noncomputable def Btilde (κ TB K lam z : ℝ) : ℝ :=
  (Real.log (1 - κ) * TB / K + z) * lam / (1 + Real.log (1 - κ) - z)

/-- O&R (66), p. 252: substituting (65), `z^H = z^F − log(1−κ)`, into (64) gives
`w/w* = B̃(z^F)`. -/
theorem relWage_eq_Btilde {κ TB K lam zF zH ω : ℝ}
    (h64 : ω = (-(zH - zF) * TB / K + zF) * lam / (1 - zH))
    (h65 : zH = zF - Real.log (1 - κ)) : ω = Btilde κ TB K lam zF := by
  rw [h64, h65, Btilde, show -(zF - Real.log (1 - κ) - zF) = Real.log (1 - κ) by ring,
    show 1 - (zF - Real.log (1 - κ)) = 1 + Real.log (1 - κ) - zF by ring]

/-- O&R fn 41, p. 252: for `z₁, z₂ < 1 + log(1−κ)` (so that `z^H < 1`), with `c = log(1−κ)`,
`B̃(z₂) − B̃(z₁) = lam (z₂ − z₁)(1 + c(1 + TB/K)) / ((1 + c − z₁)(1 + c − z₂))`. -/
theorem Btilde_sub {κ TB K lam z1 z2 : ℝ} (hK : K ≠ 0) (h1 : z1 < 1 + Real.log (1 - κ))
    (h2 : z2 < 1 + Real.log (1 - κ)) :
    Btilde κ TB K lam z2 - Btilde κ TB K lam z1 =
      lam * (z2 - z1) * (1 + Real.log (1 - κ) * (1 + TB / K)) /
        ((1 + Real.log (1 - κ) - z1) * (1 + Real.log (1 - κ) - z2)) := by
  unfold Btilde
  have d1 : (1 + Real.log (1 - κ) - z1) ≠ 0 := by linarith
  have d2 : (1 + Real.log (1 - κ) - z2) ≠ 0 := by linarith
  field_simp
  ring

/-- O&R fn 41, p. 252 ("κ small enough"), made precise: with `L*/L > 0` and `K = L*/a*(1) > 0`,
`B̃` is strictly increasing on `z < 1 + log(1−κ)` iff
`1 + log(1−κ)(1 + TB·a*(1)/L*) > 0` (here `TB/K = TB·a*(1)/L*`). -/
theorem Btilde_strictMonoOn_iff {κ TB K lam : ℝ} (hK : 0 < K) (hlam : 0 < lam) :
    StrictMonoOn (Btilde κ TB K lam) (Iio (1 + Real.log (1 - κ))) ↔
      0 < 1 + Real.log (1 - κ) * (1 + TB / K) := by
  set c := Real.log (1 - κ) with hc
  constructor
  · intro hmono
    by_contra hcon
    push Not at hcon
    have hz1 : c ∈ Iio (1 + c) := by simp
    have hz2 : c + 1 / 2 ∈ Iio (1 + c) := by simp only [mem_Iio]; linarith
    have hlt := hmono hz1 hz2 (by linarith)
    have hs := Btilde_sub (TB := TB) (lam := lam) hK.ne' (lt_add_of_pos_left c one_pos)
      (show c + 1 / 2 < 1 + c by linarith)
    rw [← hc] at hs
    have hden : 0 < (1 + c - c) * (1 + c - (c + 1 / 2)) := by
      rw [show (1 + c - c) * (1 + c - (c + 1 / 2)) = 1 / 2 by ring]; norm_num
    have hnum : lam * (c + 1 / 2 - c) * (1 + c * (1 + TB / K)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by nlinarith) hcon
    have : lam * (c + 1 / 2 - c) * (1 + c * (1 + TB / K)) /
        ((1 + c - c) * (1 + c - (c + 1 / 2))) ≤ 0 := div_nonpos_of_nonpos_of_nonneg hnum hden.le
    linarith
  · intro hcond x hx y hy hxy
    have hs := Btilde_sub (κ := κ) (TB := TB) (lam := lam) hK.ne' hx hy
    have d1 : 0 < 1 + c - x := by simp only [mem_Iio] at hx; linarith
    have d2 : 0 < 1 + c - y := by simp only [mem_Iio] at hy; linarith
    have hyx : 0 < y - x := by linarith
    have : 0 < lam * (y - x) * (1 + c * (1 + TB / K)) / ((1 + c - x) * (1 + c - y)) := by
      positivity
    linarith

/-- The transfer effect on the schedule, O&R p. 255: with `κ ∈ (0,1)`, a higher Home trade
balance lowers `B̃` at every `z < 1 + log(1−κ)`. -/
theorem Btilde_lt_of_TB_lt {κ TB TB' K lam z : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1) (hK : 0 < K)
    (hlam : 0 < lam) (hz : z < 1 + Real.log (1 - κ)) (hTB : TB < TB') :
    Btilde κ TB' K lam z < Btilde κ TB K lam z := by
  unfold Btilde
  have hc : Real.log (1 - κ) < 0 := Real.log_neg (by linarith) (by linarith)
  have hd : 0 < 1 + Real.log (1 - κ) - z := by linarith
  apply div_lt_div_of_pos_right _ hd
  apply mul_lt_mul_of_pos_right _ hlam
  have : Real.log (1 - κ) * TB' / K < Real.log (1 - κ) * TB / K :=
    div_lt_div_of_pos_right (mul_lt_mul_of_neg_left hTB hc) hK
  linarith

/-- The Keynesian transfer effect, O&R p. 255 (Figure 4.12): for `A(z) = exp(1−2z)`, if the
Home trade balance rises from `TB` to `TB'` and `B̃(·; TB)` is increasing (fn 41's condition),
the equilibrium cutoffs `(1−κ)A(z^F) = B̃(z^F)` move right, `z^F < z^F'` and
`z^H < z^H'` (with `z^H = z^F − log(1−κ)`), and the relative Home wage
`w/w* = (1−κ)A(z^F)` falls. -/
theorem transfer_effect {κ TB TB' K lam zF zF' : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1) (hK : 0 < K)
    (hlam : 0 < lam) (hTB : TB < TB') (hcond : 0 < 1 + Real.log (1 - κ) * (1 + TB / K))
    (hzF : zF < 1 + Real.log (1 - κ)) (hzF' : zF' < 1 + Real.log (1 - κ))
    (heq : (1 - κ) * expA zF = Btilde κ TB K lam zF)
    (heq' : (1 - κ) * expA zF' = Btilde κ TB' K lam zF') :
    zF < zF' ∧ zF - Real.log (1 - κ) < zF' - Real.log (1 - κ) ∧
      (1 - κ) * expA zF' < (1 - κ) * expA zF := by
  have h1 : 0 < 1 - κ := by linarith
  have hmono := (Btilde_strictMonoOn_iff (κ := κ) (TB := TB) hK hlam).2 hcond
  have hlt : zF < zF' := by
    by_contra hcon
    push Not at hcon
    have e1 : expA zF ≤ expA zF' := expA_strictAnti.antitone hcon
    have e2 : Btilde κ TB K lam zF' ≤ Btilde κ TB K lam zF := hmono.monotoneOn hzF' hzF hcon
    have e3 := Btilde_lt_of_TB_lt hκ0 hκ1 hK hlam hzF' hTB
    have e4 : (1 - κ) * expA zF ≤ (1 - κ) * expA zF' := mul_le_mul_of_nonneg_left e1 h1.le
    linarith
  exact ⟨hlt, by linarith, mul_lt_mul_of_pos_left (expA_strictAnti hlt) h1⟩

/-- A rise in relative Foreign labour with transport costs, O&R p. 253 (Figure 4.13): with
`TB = 0`, `A(z) = exp(1−2z)` and `L*/L` rising from `lam` to `lam'`, the cutoff `z^F` falls and
the relative Home wage `w/w* = (1−κ)A(z^F)` rises (`B̃` shifts inward). -/
theorem labour_rise_transport {κ K lam lam' zF zF' : ℝ} (hκ1 : κ < 1) (hK : 0 < K)
    (hlam : 0 < lam) (hlam' : lam < lam') (hzF : zF ∈ Ioo 0 (1 + Real.log (1 - κ)))
    (hzF' : zF' ∈ Ioo 0 (1 + Real.log (1 - κ)))
    (heq : (1 - κ) * expA zF = Btilde κ 0 K lam zF)
    (heq' : (1 - κ) * expA zF' = Btilde κ 0 K lam' zF') :
    zF' < zF ∧ (1 - κ) * expA zF < (1 - κ) * expA zF' := by
  have h1 : 0 < 1 - κ := by linarith
  have hcond : 0 < 1 + Real.log (1 - κ) * (1 + 0 / K) := by
    rw [zero_div, add_zero, mul_one]; linarith [hzF.1, hzF.2]
  have hmono := (Btilde_strictMonoOn_iff (κ := κ) (TB := 0) hK hlam).2 hcond
  have hlt : zF' < zF := by
    by_contra hcon
    push Not at hcon
    have e1 : expA zF' ≤ expA zF := expA_strictAnti.antitone hcon
    have e2 : Btilde κ 0 K lam zF ≤ Btilde κ 0 K lam zF' :=
      hmono.monotoneOn hzF.2 hzF'.2 hcon
    have e3 : Btilde κ 0 K lam zF' < Btilde κ 0 K lam' zF' := by
      unfold Btilde
      have hd : 0 < 1 + Real.log (1 - κ) - zF' := by linarith [hzF'.2]
      rw [mul_zero, zero_div, zero_add]
      exact div_lt_div_of_pos_right (mul_lt_mul_of_pos_left hlam' hzF'.1) hd
    have e4 : (1 - κ) * expA zF' ≤ (1 - κ) * expA zF := mul_le_mul_of_nonneg_left e1 h1.le
    linarith
  exact ⟨hlt, mul_lt_mul_of_pos_left (expA_strictAnti hlt) h1⟩

/-- A uniform Foreign productivity rise with transport costs, O&R p. 255 ("You can verify"):
with `TB = 0`, `A(z) = exp(1−2z)` and `a* ↦ a*/ν`, `ν > 1` (so `A ↦ A/ν`, and (65) is unchanged
by `cutoff_link_exp`), the new cutoff `z^F'` solving `(1−κ)A(z^F')/ν = B̃(z^F')` satisfies
`z^F' < z^F`, and the relative Home wage falls by less than the factor `ν`:
`ω/ν < ω' < ω` with `ω = (1−κ)A(z^F)`, `ω' = (1−κ)A(z^F')/ν`. -/
theorem productivity_rise_transport {κ K lam ν zF zF' : ℝ} (hκ1 : κ < 1) (hK : 0 < K)
    (hlam : 0 < lam) (hν : 1 < ν) (hzF : zF ∈ Ioo 0 (1 + Real.log (1 - κ)))
    (hzF' : zF' ∈ Ioo 0 (1 + Real.log (1 - κ)))
    (heq : (1 - κ) * expA zF = Btilde κ 0 K lam zF)
    (heq' : (1 - κ) * expA zF' / ν = Btilde κ 0 K lam zF') :
    zF' < zF ∧ (1 - κ) * expA zF / ν < (1 - κ) * expA zF' / ν ∧
      (1 - κ) * expA zF' / ν < (1 - κ) * expA zF := by
  have h1 : 0 < 1 - κ := by linarith
  have hν0 : 0 < ν := by linarith
  have hcond : 0 < 1 + Real.log (1 - κ) * (1 + 0 / K) := by
    rw [zero_div, add_zero, mul_one]; linarith [hzF.1, hzF.2]
  have hmono := (Btilde_strictMonoOn_iff (κ := κ) (TB := 0) hK hlam).2 hcond
  have hlt : zF' < zF := by
    by_contra hcon
    push Not at hcon
    have e1 : expA zF' ≤ expA zF := expA_strictAnti.antitone hcon
    have e2 : Btilde κ 0 K lam zF ≤ Btilde κ 0 K lam zF' :=
      hmono.monotoneOn hzF.2 hzF'.2 hcon
    have hpos : 0 < (1 - κ) * expA zF' := mul_pos h1 (Real.exp_pos _)
    have e3 : (1 - κ) * expA zF' / ν < (1 - κ) * expA zF' := div_lt_self hpos hν
    have e4 : (1 - κ) * expA zF' ≤ (1 - κ) * expA zF := mul_le_mul_of_nonneg_left e1 h1.le
    linarith
  have hA : (1 - κ) * expA zF < (1 - κ) * expA zF' :=
    mul_lt_mul_of_pos_left (expA_strictAnti hlt) h1
  refine ⟨hlt, div_lt_div_of_pos_right hA hν0, ?_⟩
  rw [heq, heq']
  exact hmono hzF'.2 hzF.2 hlt

/-- O&R pp. 250–255: Home's real wage in Home prices with transport costs,
`w/p = max (1/a) ((1−κ)(w/w*)/a*)`. -/
theorem homeRealWage_eq {κ a aS w wS : ℝ} (hκ1 : κ < 1) (ha : 0 < a) (haS : 0 < aS)
    (hw : 0 < w) (hwS : 0 < wS) :
    w / homePrice κ a aS w wS = max (1 / a) ((1 - κ) * (w / wS) / aS) := by
  have h1 : 0 < 1 - κ := by linarith
  unfold homePrice
  have e : w / (aS * wS / (1 - κ)) = (1 - κ) * (w / wS) / aS := by field_simp
  rcases le_total (a * w) (aS * wS / (1 - κ)) with h | h
  · rw [min_eq_left h]
    have : (1 - κ) * (w / wS) / aS ≤ 1 / a := by
      rw [← e, div_le_div_iff₀ (by positivity) ha]
      nlinarith
    rw [max_eq_left this]
    field_simp
  · rw [min_eq_right h, e]
    have : 1 / a ≤ (1 - κ) * (w / wS) / aS := by
      rw [← e, div_le_div_iff₀ ha (by positivity)]
      nlinarith
    rw [max_eq_right this]

/-- O&R pp. 250–255: Foreign's real wage in Foreign prices with transport costs,
`w*/p* = max ((1−κ)(w*/w)/a) (1/a*)`. -/
theorem foreignRealWage_eq {κ a aS w wS : ℝ} (hκ1 : κ < 1) (ha : 0 < a) (haS : 0 < aS)
    (hw : 0 < w) (hwS : 0 < wS) :
    wS / foreignPrice κ a aS w wS = max ((1 - κ) * (wS / w) / a) (1 / aS) := by
  have h1 : 0 < 1 - κ := by linarith
  unfold foreignPrice
  have e : wS / (a * w / (1 - κ)) = (1 - κ) * (wS / w) / a := by field_simp
  rcases le_total (a * w / (1 - κ)) (aS * wS) with h | h
  · rw [min_eq_left h, e]
    have : 1 / aS ≤ (1 - κ) * (wS / w) / a := by
      rw [← e, div_le_div_iff₀ haS (by positivity)]
      nlinarith
    rw [max_eq_left this]
  · rw [min_eq_right h]
    have : (1 - κ) * (wS / w) / a ≤ 1 / aS := by
      rw [← e, div_le_div_iff₀ (by positivity) haS]
      nlinarith
    rw [max_eq_right this]
    field_simp

/-- O&R p. 255: after the Foreign productivity rise `a* ↦ a*/ν` with `w/w* ≤ ν · w'/w*'`
(`productivity_rise_transport`), Home's real wage rises weakly in terms of every good. -/
theorem productivity_rise_home_realWage {κ a aS w wS w' wS' ν : ℝ} (hκ1 : κ < 1)
    (ha : 0 < a) (haS : 0 < aS) (hν : 0 < ν) (hw : 0 < w) (hwS : 0 < wS) (hw' : 0 < w')
    (hwS' : 0 < wS') (hless : w / wS ≤ ν * (w' / wS')) :
    w / homePrice κ a aS w wS ≤ w' / homePrice κ a (aS / ν) w' wS' := by
  have h1 : 0 < 1 - κ := by linarith
  rw [homeRealWage_eq hκ1 ha haS hw hwS, homeRealWage_eq hκ1 ha (by positivity) hw' hwS']
  have e : (1 - κ) * (w' / wS') / (aS / ν) = (1 - κ) * (ν * (w' / wS')) / aS := by
    field_simp
  rw [e]
  exact max_le_max le_rfl
    (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hless h1.le) haS.le)

/-- O&R p. 255: after the Foreign productivity rise `a* ↦ a*/ν`, `ν ≥ 1`, with `w/w*` falling,
Foreign's real wage rises weakly in terms of every good. -/
theorem productivity_rise_foreign_realWage {κ a aS w wS w' wS' ν : ℝ} (hκ1 : κ < 1)
    (ha : 0 < a) (haS : 0 < aS) (hν : 1 ≤ ν) (hw : 0 < w) (hwS : 0 < wS) (hw' : 0 < w')
    (hwS' : 0 < wS') (hfall : w' / wS' ≤ w / wS) :
    wS / foreignPrice κ a aS w wS ≤ wS' / foreignPrice κ a (aS / ν) w' wS' := by
  have h1 : 0 < 1 - κ := by linarith
  rw [foreignRealWage_eq hκ1 ha haS hw hwS, foreignRealWage_eq hκ1 ha (by positivity) hw' hwS']
  have hr : wS / w ≤ wS' / w' := by
    rw [div_le_div_iff₀ hw hw']; rw [div_le_div_iff₀ hwS' hwS] at hfall; linarith
  have e : 1 / (aS / ν) = ν / aS := by field_simp
  rw [e]
  exact max_le_max (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hr h1.le) ha.le)
    (div_le_div_of_nonneg_right hν haS.le)

/-- O&R p. 255: Home's terms of trade improve after the Foreign productivity rise: for any good
Home exports (price `w a₁`) and any good Foreign exports (price `w* a*₂`, which becomes
`w*' a*₂/ν`), the relative price of Home's export rises when `w/w* < ν · w'/w*'`. -/
theorem productivity_rise_termsOfTrade {a1 aS2 w wS w' wS' ν : ℝ} (ha1 : 0 < a1)
    (haS2 : 0 < aS2) (hν : 0 < ν) (hwS : 0 < wS) (hwS' : 0 < wS')
    (hless : w / wS < ν * (w' / wS')) :
    a1 * w / (aS2 * wS) < a1 * w' / (aS2 / ν * wS') := by
  have e1 : a1 * w / (aS2 * wS) = a1 / aS2 * (w / wS) := by field_simp
  have e2 : a1 * w' / (aS2 / ν * wS') = a1 / aS2 * (ν * (w' / wS')) := by field_simp
  rw [e1, e2]
  exact mul_lt_mul_of_pos_left hless (div_pos ha1 haS2)

/-- T26 (O&R p. 254), the key formula: for every good, the Home–Foreign price ratio is the
relative Home cost `x = w a/(w* a*)` clamped to `[1−κ, 1/(1−κ)]`:
`p/p* = max (1−κ) (min x (1/(1−κ)))`. (Home exports: `1−κ`; nontraded: `x`; Foreign exports:
`1/(1−κ)`.) -/
theorem priceRatio_eq {κ a aS w wS : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (ha : 0 < a)
    (haS : 0 < aS) (hw : 0 < w) (hwS : 0 < wS) :
    homePrice κ a aS w wS / foreignPrice κ a aS w wS =
      max (1 - κ) (min (a * w / (aS * wS)) (1 / (1 - κ))) := by
  have h1 : 0 < 1 - κ := by linarith
  have hm : 0 < aS * wS := by positivity
  set m := aS * wS with hmdef
  set x := a * w / m with hxdef
  have hx : 0 < x := by positivity
  have hax : a * w = x * m := by rw [hxdef]; field_simp
  have eH : homePrice κ a aS w wS = min x (1 / (1 - κ)) * m := by
    unfold homePrice
    rw [min_mul_of_nonneg _ _ hm.le, hax, ← hmdef]
    congr 1
    ring
  have eF : foreignPrice κ a aS w wS = min (x / (1 - κ)) 1 * m := by
    unfold foreignPrice
    rw [min_mul_of_nonneg _ _ hm.le, hax, ← hmdef]
    congr 1
    · ring
    · ring
  rw [eH, eF, mul_div_mul_right _ _ hm.ne']
  have hq : 1 - κ ≤ 1 / (1 - κ) := by
    rw [le_div_iff₀ h1]; nlinarith
  rcases le_total x (1 - κ) with hx1 | hx1
  · rw [min_eq_left (hx1.trans hq), min_eq_left ((div_le_one h1).2 hx1), max_eq_left hx1]
    field_simp
  · rcases le_total x (1 / (1 - κ)) with hx2 | hx2
    · rw [min_eq_left hx2, min_eq_right ((one_le_div h1).2 hx1), max_eq_right hx1, div_one]
    · rw [min_eq_right hx2, min_eq_right ((one_le_div h1).2 hx1), max_eq_right hq, div_one]

/-- T26, O&R p. 254 (Figure 4.13): whenever the relative Home wage rises (as after a rise in
`L*/L`, `labour_rise_transport`), `p(z)′/p*(z)′ ≥ p(z)/p*(z)` for EVERY good `z`, in
whichever class it falls (including the fifth class the book omits). -/
theorem priceRatio_mono {κ a aS w wS w' wS' : ℝ} (hκ0 : 0 ≤ κ) (hκ1 : κ < 1) (ha : 0 < a)
    (haS : 0 < aS) (hw : 0 < w) (hwS : 0 < wS) (hw' : 0 < w') (hwS' : 0 < wS')
    (hrise : w / wS ≤ w' / wS') :
    homePrice κ a aS w wS / foreignPrice κ a aS w wS ≤
      homePrice κ a aS w' wS' / foreignPrice κ a aS w' wS' := by
  rw [priceRatio_eq hκ0 hκ1 ha haS hw hwS, priceRatio_eq hκ0 hκ1 ha haS hw' hwS']
  have e1 : a * w / (aS * wS) = a / aS * (w / wS) := by field_simp
  have e2 : a * w' / (aS * wS') = a / aS * (w' / wS') := by field_simp
  rw [e1, e2]
  exact max_le_max le_rfl
    (min_le_min_right _ (mul_le_mul_of_nonneg_left hrise (div_pos ha haS).le))

/-- The fifth class omitted by O&R p. 254: a good Home exported before the shock
(`x ≤ 1−κ`) that Foreign exports afterwards (`x' ≥ 1/(1−κ)`); its price ratio jumps from
`1−κ` to `1/(1−κ)`. -/
theorem fifth_class_priceRatio {κ a aS w wS w' wS' : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1)
    (ha : 0 < a) (haS : 0 < aS) (hw : 0 < w) (hwS : 0 < wS) (hw' : 0 < w') (hwS' : 0 < wS')
    (hbefore : a * w / (aS * wS) ≤ 1 - κ) (hafter : 1 / (1 - κ) ≤ a * w' / (aS * wS')) :
    homePrice κ a aS w wS / foreignPrice κ a aS w wS = 1 - κ ∧
      homePrice κ a aS w' wS' / foreignPrice κ a aS w' wS' = 1 / (1 - κ) ∧
      1 - κ < 1 / (1 - κ) := by
  have h1 : 0 < 1 - κ := by linarith
  have hq : 1 - κ < 1 / (1 - κ) := by
    rw [lt_div_iff₀ h1]; nlinarith
  refine ⟨?_, ?_, hq⟩
  · rw [priceRatio_eq hκ0.le hκ1 ha haS hw hwS, min_eq_left (hbefore.trans hq.le),
      max_eq_left hbefore]
  · rw [priceRatio_eq hκ0.le hκ1 ha haS hw' hwS', min_eq_right hafter, max_eq_right hq.le]

/-- O&R p. 254: the fifth class is empty for small shocks: it requires the relative Home wage
to rise by at least the factor `1/(1−κ)²`. -/
theorem fifth_class_requires_large_shock {κ a aS w wS w' wS' : ℝ} (hκ1 : κ < 1)
    (ha : 0 < a) (haS : 0 < aS) (hw : 0 < w) (hwS : 0 < wS) (hw' : 0 < w') (hwS' : 0 < wS')
    (hbefore : a * w / (aS * wS) ≤ 1 - κ) (hafter : 1 / (1 - κ) ≤ a * w' / (aS * wS')) :
    1 / (1 - κ) ^ 2 ≤ (w' / wS') / (w / wS) := by
  have h1 : 0 < 1 - κ := by linarith
  have hx : 0 < a * w / (aS * wS) := by positivity
  have e : (w' / wS') / (w / wS) = (a * w' / (aS * wS')) / (a * w / (aS * wS)) := by
    field_simp
  rw [e]
  calc 1 / (1 - κ) ^ 2 = (1 / (1 - κ)) / (1 - κ) := by field_simp
    _ ≤ (a * w' / (aS * wS')) / (1 - κ) := div_le_div_of_nonneg_right hafter h1.le
    _ ≤ (a * w' / (aS * wS')) / (a * w / (aS * wS)) :=
        div_le_div_of_nonneg_left (by positivity) hx hbefore

/-- O&R (60), p. 250: `log(x/(1−κ)) = log x − log(1−κ)`, used to write the CIF import prices in
the log price indices. -/
theorem log_cif {κ x : ℝ} (hκ1 : κ < 1) (hx : 0 < x) :
    Real.log (x / (1 - κ)) = Real.log x - Real.log (1 - κ) := by
  have h1 : 0 < 1 - κ := by linarith
  exact Real.log_div hx.ne' h1.ne'

/-- Home's log price index, O&R (60), p. 250, with `f z = log(w a(z))`, `g z = log(w* a*(z))`:
`log P = ∫₀^{z^H} f + ∫_{z^H}^1 (g − log(1−κ))`. -/
noncomputable def logHomePriceIndex (κ zH : ℝ) (f g : ℝ → ℝ) : ℝ :=
  (∫ z in (0 : ℝ)..zH, f z) + ∫ z in zH..1, (g z - Real.log (1 - κ))

/-- Foreign's log price index, O&R (60), p. 250:
`log P* = ∫₀^{z^F} (f − log(1−κ)) + ∫_{z^F}^1 g`. -/
noncomputable def logForeignPriceIndex (κ zF : ℝ) (f g : ℝ → ℝ) : ℝ :=
  (∫ z in (0 : ℝ)..zF, (f z - Real.log (1 - κ))) + ∫ z in zF..1, g z

/-- The real exchange rate, O&R p. 251:
`log(P/P*) = ∫_{z^F}^{z^H} log[w a(z)/(w* a*(z))] dz + [z^F − (1 − z^H)] log(1−κ)`
(for `f, g` integrable on `[0,1]` and `z^F, z^H ∈ [0,1]`). -/
theorem log_realExchangeRate {κ zF zH : ℝ} {f g : ℝ → ℝ}
    (hf : IntervalIntegrable f MeasureTheory.volume 0 1)
    (hg : IntervalIntegrable g MeasureTheory.volume 0 1)
    (hF : zF ∈ Icc (0 : ℝ) 1) (hH : zH ∈ Icc (0 : ℝ) 1) :
    logHomePriceIndex κ zH f g - logForeignPriceIndex κ zF f g =
      (∫ z in zF..zH, (f z - g z)) + (zF - (1 - zH)) * Real.log (1 - κ) := by
  have sub : ∀ {h : ℝ → ℝ}, IntervalIntegrable h MeasureTheory.volume 0 1 →
      ∀ {x y : ℝ}, x ∈ Icc (0 : ℝ) 1 → y ∈ Icc (0 : ℝ) 1 →
        IntervalIntegrable h MeasureTheory.volume x y := by
    intro h hh x y hx hy
    refine hh.mono_set (uIcc_subset_uIcc ?_ ?_)
    · exact Icc_subset_uIcc hx
    · exact Icc_subset_uIcc hy
  have h0 : (0 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨le_rfl, zero_le_one⟩
  have h1 : (1 : ℝ) ∈ Icc (0 : ℝ) 1 := ⟨zero_le_one, le_rfl⟩
  have hc : ∀ x y : ℝ, IntervalIntegrable (fun _ : ℝ => Real.log (1 - κ))
      MeasureTheory.volume x y := fun _ _ => intervalIntegrable_const
  unfold logHomePriceIndex logForeignPriceIndex
  rw [intervalIntegral.integral_sub (sub hg hH h1) (hc _ _),
    intervalIntegral.integral_sub (sub hf h0 hF) (hc _ _),
    intervalIntegral.integral_sub (sub hf hF hH) (sub hg hF hH),
    intervalIntegral.integral_const, intervalIntegral.integral_const,
    ← intervalIntegral.integral_interval_sub_left (sub hf h0 hH) (sub hf h0 hF),
    ← intervalIntegral.integral_add_adjacent_intervals (sub hg hF hH) (sub hg hH h1)]
  simp only [smul_eq_mul]
  ring

end ObstfeldRogoff.RealExchangeRate.DFSTransportCosts
