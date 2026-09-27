/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The static Dornbusch–Fischer–Samuelson Ricardian model

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §4.5.1–4.5.3,
pp. 235–243.

A continuum of goods `z ∈ [0,1]`; Home needs `a(z)` units of labour per unit of good `z`,
Foreign `a*(z)`. The relative productivity schedule is `A(z) = a*(z)/a(z)` (41), assumed
continuous, strictly decreasing and positive on `[0,1]`. Equal spending shares (40) are taken
as the primitive: Home's share of world spending is the measure `z̄` of the goods it produces.

* (43): goods-market clearing gives `w/w* = B(z̄; L*/L) = z̄/(1−z̄) · L*/L`;
* T20: a unique cutoff `z̄ ∈ (0,1)` with `A(z̄) = B(z̄; L*/L)` (intermediate value theorem on
  `h(z) = A(z)(1−z)L − zL*`);
* statics: a rise in `L*/L` lowers `z̄` and raises `w/w*`; a uniform fall `a* ↦ a*/ν` lowers
  `w/w*` by less than the factor `ν`;
* (44)–(45) with free trade the price of a good is its lowest unit cost, and real wages in
  terms of every good respond as described on pp. 240–243.

A small imprecision (p. 241): the book says Foreign's real wage falls strictly on every
relocated good `z ∈ (z̄', z̄]`; at the old cutoff good `z = z̄` it is unchanged (there
`wa(z̄) = w*a*(z̄)`), so the fall is strict only on `(z̄', z̄)`.
-/

namespace ObstfeldRogoff.RealExchangeRate.DFSStatic

open Set

/-- Relative Home labour productivity schedule, O&R (41), p. 238: `A(z) = a*(z)/a(z)`. -/
noncomputable def relProductivity (a aS : ℝ → ℝ) (z : ℝ) : ℝ := aS z / a z

/-- O&R (41), p. 238: if Home's requirement `a` is strictly increasing and Foreign's `a*` is
strictly decreasing (both positive), then `A = a*/a` is strictly decreasing. -/
theorem relProductivity_strictAntiOn {a aS : ℝ → ℝ} {s : Set ℝ} (ha : StrictMonoOn a s)
    (haS : StrictAntiOn aS s) (hapos : ∀ z ∈ s, 0 < a z) (haSpos : ∀ z ∈ s, 0 < aS z) :
    StrictAntiOn (relProductivity a aS) s := by
  intro x hx y hy hxy
  unfold relProductivity
  have h1 := ha hx hy hxy
  have h2 := haS hx hy hxy
  have hax := hapos x hx
  have hay := hapos y hy
  have hbx := haSpos x hx
  have hby := haSpos y hy
  rw [div_lt_div_iff₀ hay hax]
  nlinarith

/-- Pattern of specialisation, O&R p. 238: good `z` is cheaper to make in Home,
`w a(z) < w* a*(z)`, iff `w/w* < A(z) = a*(z)/a(z)`. -/
theorem home_cheaper_iff {a aS w wS : ℝ} (ha : 0 < a) (hwS : 0 < wS) :
    a * w < aS * wS ↔ w / wS < aS / a := by
  rw [div_lt_div_iff₀ hwS ha]
  constructor <;> intro h <;> linarith

/-- The relative-wage schedule, O&R (43), p. 240: `B(z; L*/L) = z/(1−z) · (L*/L)`,
written with `lam = L*/L`. -/
noncomputable def relWageSchedule (lam z : ℝ) : ℝ := z / (1 - z) * lam

/-- O&R (42)–(43), pp. 239–240: world spending equals world labour income,
`P(C + C*) = wL + w*L*` (42); with equal spending shares (40), Home's revenue from the goods
`[0, z]` is `z P C + z P C*`. Clearing of the Home-goods market then gives
`w/w* = B(z; L*/L)` (43). -/
theorem relWage_of_market_clearing {P C CS w wS L LS z : ℝ} (hwS : 0 < wS) (hL : 0 < L)
    (hz : z < 1) (h42 : P * (C + CS) = w * L + wS * LS)
    (hclear : w * L = z * (P * C) + z * (P * CS)) :
    w / wS = relWageSchedule (LS / L) z := by
  unfold relWageSchedule
  have h1 : (1 - z) ≠ 0 := by linarith
  have key : w * L * (1 - z) = z * (wS * LS) := by
    have : w * L = z * (w * L + wS * LS) := by rw [← h42]; linarith
    linarith
  field_simp
  linarith

/-- O&R (43), p. 240: `B(·; L*/L)` is strictly increasing on `[0,1)` ("upward-sloping"). -/
theorem relWageSchedule_strictMonoOn {lam : ℝ} (hlam : 0 < lam) :
    StrictMonoOn (relWageSchedule lam) (Ico 0 1) := by
  intro x hx y hy hxy
  unfold relWageSchedule
  have hx1 : 0 < 1 - x := by linarith [hx.2]
  have hy1 : 0 < 1 - y := by linarith [hy.2]
  have : x / (1 - x) < y / (1 - y) := by
    rw [div_lt_div_iff₀ hx1 hy1]
    nlinarith
  exact mul_lt_mul_of_pos_right this hlam

/-- O&R p. 240 (Figure 4.10): at an interior `z`, `B(z; L*/L)` is strictly increasing in
`L*/L`, so a rise in relative Foreign labour shifts the schedule inward. -/
theorem relWageSchedule_lt_of_lam_lt {lam lam' z : ℝ} (hz : z ∈ Ioo 0 1) (h : lam < lam') :
    relWageSchedule lam z < relWageSchedule lam' z := by
  unfold relWageSchedule
  have : 0 < z / (1 - z) := div_pos hz.1 (by linarith [hz.2])
  exact mul_lt_mul_of_pos_left h this

/-- The cutoff gap used for T20 (O&R p. 240): `h(z) = A(z)(1−z)L − zL*`; on `(0,1)` its zeros
are exactly the intersections `A(z) = B(z; L*/L)`. -/
def cutoffGap (A : ℝ → ℝ) (L LS z : ℝ) : ℝ := A z * (1 - z) * L - z * LS

/-- O&R p. 240: on `(0,1)`, `h(z) = 0` iff `A(z) = B(z; L*/L)`. -/
theorem cutoffGap_eq_zero_iff {A : ℝ → ℝ} {L LS z : ℝ} (hL : 0 < L) (hz : z ∈ Ioo 0 1) :
    cutoffGap A L LS z = 0 ↔ A z = relWageSchedule (LS / L) z := by
  unfold cutoffGap relWageSchedule
  have h1 : (1 - z) ≠ 0 := by linarith [hz.2]
  have hL' : L ≠ 0 := hL.ne'
  constructor
  · intro h
    field_simp
    linarith
  · intro h
    field_simp at h
    linarith

/-- O&R p. 240: with `A` strictly decreasing and positive on `[0,1]`, the cutoff gap `h` is
strictly decreasing on `[0,1]`. -/
theorem cutoffGap_strictAntiOn {A : ℝ → ℝ} {L LS : ℝ} (hA : StrictAntiOn A (Icc 0 1))
    (hpos : ∀ z ∈ Icc (0 : ℝ) 1, 0 < A z) (hL : 0 < L) (hLS : 0 < LS) :
    StrictAntiOn (cutoffGap A L LS) (Icc 0 1) := by
  intro x hx y hy hxy
  unfold cutoffGap
  have hAxy := hA hx hy hxy
  have hAy := hpos y hy
  have hx1 : 0 < 1 - x := by linarith [hy.2]
  have hy1 : 0 ≤ 1 - y := by linarith [hy.2]
  have e1 : A y * (1 - y) ≤ A y * (1 - x) := mul_le_mul_of_nonneg_left (by linarith) hAy.le
  have e2 : A y * (1 - x) < A x * (1 - x) := mul_lt_mul_of_pos_right hAxy hx1
  have e3 : A y * (1 - y) * L < A x * (1 - x) * L := mul_lt_mul_of_pos_right (by linarith) hL
  have e4 : x * LS < y * LS := mul_lt_mul_of_pos_right hxy hLS
  linarith

/-- T20, O&R p. 240 (Figure 4.9): if `A` is continuous, strictly decreasing and positive on
`[0,1]` and `L, L* > 0`, there is a unique cutoff `z̄ ∈ (0,1)` with `A(z̄) = B(z̄; L*/L)`;
the equilibrium relative wage is `w/w* = A(z̄)`. -/
theorem cutoff_exists_unique {A : ℝ → ℝ} {L LS : ℝ} (hAc : ContinuousOn A (Icc 0 1))
    (hA : StrictAntiOn A (Icc 0 1)) (hpos : ∀ z ∈ Icc (0 : ℝ) 1, 0 < A z) (hL : 0 < L)
    (hLS : 0 < LS) : ∃! z, z ∈ Ioo (0 : ℝ) 1 ∧ A z = relWageSchedule (LS / L) z := by
  have hcont : ContinuousOn (cutoffGap A L LS) (Icc 0 1) := by
    unfold cutoffGap
    fun_prop
  have h0 : cutoffGap A L LS 0 = A 0 * L := by unfold cutoffGap; ring
  have h1 : cutoffGap A L LS 1 = -LS := by unfold cutoffGap; ring
  have hA0 : 0 < A 0 := hpos 0 ⟨le_rfl, zero_le_one⟩
  have hmem : (0 : ℝ) ∈ Icc (cutoffGap A L LS 1) (cutoffGap A L LS 0) := by
    rw [h0, h1]
    constructor
    · linarith
    · positivity
  obtain ⟨z, hz, hz0⟩ := intermediate_value_Icc' zero_le_one hcont hmem
  have hzne0 : z ≠ 0 := by
    rintro rfl
    rw [h0] at hz0
    have : 0 < A 0 * L := by positivity
    linarith
  have hzne1 : z ≠ 1 := by
    rintro rfl
    rw [h1] at hz0
    linarith
  have hzI : z ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne hz.1 (Ne.symm hzne0), lt_of_le_of_ne hz.2 hzne1⟩
  refine ⟨z, ⟨hzI, (cutoffGap_eq_zero_iff hL hzI).1 hz0⟩, ?_⟩
  rintro y ⟨hyI, hy⟩
  have hy0 : cutoffGap A L LS y = 0 := (cutoffGap_eq_zero_iff hL hyI).2 hy
  exact (cutoffGap_strictAntiOn hA hpos hL hLS).injOn (Ioo_subset_Icc_self hyI) hz
    (by rw [hy0, hz0])

/-- O&R p. 239: with `w/w* = A(z̄)`, a good `z ∈ [0,1]` is (weakly) cheaper at Home,
`w/w* ≤ A(z)`, iff `z ≤ z̄`: Home produces exactly `[0, z̄]`. -/
theorem home_produces_iff {A : ℝ → ℝ} {z zbar : ℝ} (hA : StrictAntiOn A (Icc 0 1))
    (hz : z ∈ Icc (0 : ℝ) 1) (hzbar : zbar ∈ Icc (0 : ℝ) 1) : A zbar ≤ A z ↔ z ≤ zbar :=
  hA.le_iff_ge hzbar hz

/-- Comparative statics, O&R p. 240 (Figure 4.10): a rise in relative Foreign labour supply
`L*/L` (from `lam` to `lam'`) lowers the cutoff and raises the relative Home wage:
`z̄' < z̄` and `w/w* = A(z̄) < A(z̄') = w'/w*'`. -/
theorem labour_rise_statics {A : ℝ → ℝ} {lam lam' z z' : ℝ} (hA : StrictAntiOn A (Icc 0 1))
    (hlam : 0 < lam) (hlam' : lam < lam') (hz : z ∈ Ioo (0 : ℝ) 1) (hz' : z' ∈ Ioo (0 : ℝ) 1)
    (heq : A z = relWageSchedule lam z) (heq' : A z' = relWageSchedule lam' z') :
    z' < z ∧ A z < A z' := by
  have hlt : z' < z := by
    by_contra hcon
    push Not at hcon
    have h1 : A z' ≤ A z := hA.antitoneOn (Ioo_subset_Icc_self hz) (Ioo_subset_Icc_self hz') hcon
    have h2 : relWageSchedule lam z ≤ relWageSchedule lam z' :=
      (relWageSchedule_strictMonoOn hlam).monotoneOn ⟨hz.1.le, hz.2⟩ ⟨hz'.1.le, hz'.2⟩ hcon
    have h3 := relWageSchedule_lt_of_lam_lt hz' hlam'
    linarith
  exact ⟨hlt, hA (Ioo_subset_Icc_self hz') (Ioo_subset_Icc_self hz) hlt⟩

/-- Comparative statics, O&R p. 242: a uniform proportional fall in Foreign unit labour
requirements, `a*(z) ↦ a*(z)/ν` with `ν > 1`, shifts `A` down to `A/ν`. The new cutoff `z̄'`
(solving `A(z̄')/ν = B(z̄'; L*/L)`) satisfies `z̄' < z̄`, and the relative Home wage falls, but by
less than the factor `ν`: `A(z̄)/ν < A(z̄')/ν < A(z̄)`. -/
theorem productivity_rise_statics {A : ℝ → ℝ} {ν lam z z' : ℝ}
    (hA : StrictAntiOn A (Icc 0 1)) (hpos : ∀ z ∈ Icc (0 : ℝ) 1, 0 < A z) (hν : 1 < ν)
    (hlam : 0 < lam) (hz : z ∈ Ioo (0 : ℝ) 1) (hz' : z' ∈ Ioo (0 : ℝ) 1)
    (heq : A z = relWageSchedule lam z) (heq' : A z' / ν = relWageSchedule lam z') :
    z' < z ∧ A z / ν < A z' / ν ∧ A z' / ν < A z := by
  have hν0 : 0 < ν := by linarith
  have hlt : z' < z := by
    by_contra hcon
    push Not at hcon
    have h1 : A z' ≤ A z := hA.antitoneOn (Ioo_subset_Icc_self hz) (Ioo_subset_Icc_self hz') hcon
    have h2 : relWageSchedule lam z ≤ relWageSchedule lam z' :=
      (relWageSchedule_strictMonoOn hlam).monotoneOn ⟨hz.1.le, hz.2⟩ ⟨hz'.1.le, hz'.2⟩ hcon
    have hAz' := hpos z' (Ioo_subset_Icc_self hz')
    have h3 : A z' / ν < A z' := div_lt_self hAz' hν
    linarith
  have hAlt : A z < A z' := hA (Ioo_subset_Icc_self hz') (Ioo_subset_Icc_self hz) hlt
  refine ⟨hlt, div_lt_div_of_pos_right hAlt hν0, ?_⟩
  rw [heq, heq']
  exact relWageSchedule_strictMonoOn hlam ⟨hz'.1.le, hz'.2⟩ ⟨hz.1.le, hz.2⟩ hlt

/-- Free-trade price of a good, O&R (44)–(45), p. 241: with no transport costs the good is
made where it is cheapest, so its price is `min (a w) (a* w*)` (`a`, `aS` are the unit labour
requirements for this good). -/
noncomputable def freeTradePrice (a aS w wS : ℝ) : ℝ := min (a * w) (aS * wS)

/-- O&R (44), p. 241: for a good Home produces (`w/w* ≤ A = a*/a`), `p = a w`. -/
theorem freeTradePrice_home {a aS w wS : ℝ} (ha : 0 < a) (hwS : 0 < wS)
    (h : w / wS ≤ aS / a) : freeTradePrice a aS w wS = a * w := by
  unfold freeTradePrice
  rw [div_le_div_iff₀ hwS ha] at h
  exact min_eq_left (by linarith)

/-- O&R (45), p. 241: for a good Foreign produces (`A = a*/a ≤ w/w*`), `p = a* w*`. -/
theorem freeTradePrice_foreign {a aS w wS : ℝ} (ha : 0 < a) (hwS : 0 < wS)
    (h : aS / a ≤ w / wS) : freeTradePrice a aS w wS = aS * wS := by
  unfold freeTradePrice
  rw [div_le_div_iff₀ ha hwS] at h
  exact min_eq_right (by linarith)

/-- O&R pp. 240–242: Home's real wage in terms of a good, `w/p = max (1/a) ((w/w*)/a*)`. -/
theorem homeRealWage_eq {a aS w wS : ℝ} (ha : 0 < a) (haS : 0 < aS) (hw : 0 < w)
    (hwS : 0 < wS) : w / freeTradePrice a aS w wS = max (1 / a) (w / wS / aS) := by
  unfold freeTradePrice
  rcases le_total (a * w) (aS * wS) with h | h
  · rw [min_eq_left h]
    have : w / wS / aS ≤ 1 / a := by
      rw [div_div, div_le_div_iff₀ (by positivity) ha]
      linarith
    rw [max_eq_left this]
    field_simp
  · rw [min_eq_right h]
    have : 1 / a ≤ w / wS / aS := by
      rw [div_div, div_le_div_iff₀ ha (by positivity)]
      linarith
    rw [max_eq_right this]
    field_simp

/-- O&R pp. 240–242: Foreign's real wage in terms of a good,
`w*/p = max ((w*/w)/a) (1/a*)`. -/
theorem foreignRealWage_eq {a aS w wS : ℝ} (ha : 0 < a) (haS : 0 < aS) (hw : 0 < w)
    (hwS : 0 < wS) : wS / freeTradePrice a aS w wS = max (wS / w / a) (1 / aS) := by
  unfold freeTradePrice
  rcases le_total (a * w) (aS * wS) with h | h
  · rw [min_eq_left h]
    have : 1 / aS ≤ wS / w / a := by
      rw [div_div, div_le_div_iff₀ haS (by positivity)]
      linarith
    rw [max_eq_left this]
    field_simp
  · rw [min_eq_right h]
    have : wS / w / a ≤ 1 / aS := by
      rw [div_div, div_le_div_iff₀ (by positivity) haS]
      linarith
    rw [max_eq_right this]
    field_simp

/-- T21(a), O&R (44), p. 241: after a rise in `L*/L` (so `w'/w*' > w/w*`), Home's real wage
is unchanged in terms of every good Home still produces (`w'/w*' ≤ A = a*/a`). -/
theorem labour_rise_home_realWage_own {a aS w wS w' wS' : ℝ} (ha : 0 < a) (haS : 0 < aS)
    (hw : 0 < w) (hwS : 0 < wS) (hw' : 0 < w') (hwS' : 0 < wS')
    (hrise : w / wS < w' / wS') (hhome : w' / wS' ≤ aS / a) :
    w' / freeTradePrice a aS w' wS' = w / freeTradePrice a aS w wS := by
  rw [homeRealWage_eq ha haS hw hwS, homeRealWage_eq ha haS hw' hwS']
  have e : aS / a / aS = 1 / a := by field_simp
  have h1 : w' / wS' / aS ≤ 1 / a := by
    rw [← e]; exact div_le_div_of_nonneg_right hhome haS.le
  have h2 : w / wS / aS ≤ 1 / a := by
    rw [← e]; exact div_le_div_of_nonneg_right (by linarith) haS.le
  rw [max_eq_left h1, max_eq_left h2]

/-- T21(b), O&R p. 241: after a rise in `L*/L`, Home's real wage rises strictly in terms of
every good Foreign produces afterwards (`A = a*/a < w'/w*'`): both the goods Foreign kept and
the goods relocated from Home. -/
theorem labour_rise_home_realWage_other {a aS w wS w' wS' : ℝ} (ha : 0 < a) (haS : 0 < aS)
    (hw : 0 < w) (hwS : 0 < wS) (hw' : 0 < w') (hwS' : 0 < wS')
    (hrise : w / wS < w' / wS') (hforeign : aS / a < w' / wS') :
    w / freeTradePrice a aS w wS < w' / freeTradePrice a aS w' wS' := by
  rw [homeRealWage_eq ha haS hw hwS, homeRealWage_eq ha haS hw' hwS']
  have e : aS / a / aS = 1 / a := by field_simp
  have h1 : 1 / a < w' / wS' / aS := by
    rw [← e]; exact div_lt_div_of_pos_right hforeign haS
  have h2 : w / wS / aS < w' / wS' / aS := div_lt_div_of_pos_right hrise haS
  exact lt_of_lt_of_le (max_lt h1 h2) (le_max_right _ _)

/-- T21(c), O&R p. 241: after a rise in `L*/L`, Foreign's real wage falls strictly in terms of
every good Home still produces (`w'/w*' ≤ A = a*/a`). -/
theorem labour_rise_foreign_realWage_homeGoods {a aS w wS w' wS' : ℝ} (ha : 0 < a)
    (haS : 0 < aS) (hw : 0 < w) (hwS : 0 < wS) (hw' : 0 < w') (hwS' : 0 < wS')
    (hrise : w / wS < w' / wS') (hhome : w' / wS' ≤ aS / a) :
    wS' / freeTradePrice a aS w' wS' < wS / freeTradePrice a aS w wS := by
  rw [foreignRealWage_eq ha haS hw hwS, foreignRealWage_eq ha haS hw' hwS']
  have hr : wS' / w' < wS / w := by
    rw [div_lt_div_iff₀ hw' hw]; rw [div_lt_div_iff₀ hwS hwS'] at hrise; linarith
  have h1 : 1 / aS ≤ wS' / w' / a := by
    rw [div_le_div_iff₀ hwS' ha] at hhome
    rw [div_div, div_le_div_iff₀ haS (by positivity)]
    linarith
  rw [max_eq_left h1]
  exact lt_of_lt_of_le (div_lt_div_of_pos_right hr ha) (le_max_left _ _)

/-- T21(d), O&R (45), p. 241: after a rise in `L*/L`, Foreign's real wage is unchanged in
terms of the goods Foreign already produced (`A = a*/a ≤ w/w*`). -/
theorem labour_rise_foreign_realWage_own {a aS w wS w' wS' : ℝ} (ha : 0 < a) (haS : 0 < aS)
    (hwS : 0 < wS) (hwS' : 0 < wS')
    (hrise : w / wS < w' / wS') (hforeign : aS / a ≤ w / wS) :
    wS' / freeTradePrice a aS w' wS' = wS / freeTradePrice a aS w wS := by
  rw [freeTradePrice_foreign ha hwS hforeign, freeTradePrice_foreign ha hwS' (by linarith)]
  field_simp

/-- T21(e), O&R p. 242: after a rise in `L*/L`, Foreign's real wage falls strictly in terms of
the relocated goods that Home produced strictly more cheaply before (`w/w* < A`) and Foreign
produces afterwards (`A ≤ w'/w*'`). (At the old cutoff good itself, `w/w* = A`, it is
unchanged: the book's strict inequality on `(z̄', z̄]` fails at `z̄`.) -/
theorem labour_rise_foreign_realWage_relocated {a aS w wS w' wS' : ℝ} (ha : 0 < a)
    (haS : 0 < aS) (hw : 0 < w) (hwS : 0 < wS) (hwS' : 0 < wS')
    (hbefore : w / wS < aS / a) (hafter : aS / a ≤ w' / wS') :
    wS' / freeTradePrice a aS w' wS' < wS / freeTradePrice a aS w wS := by
  rw [freeTradePrice_foreign ha hwS' hafter, freeTradePrice_home ha hwS hbefore.le]
  rw [div_lt_div_iff₀ hwS ha] at hbefore
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- O&R p. 242 ("Show this result"): after the Foreign productivity rise `a* ↦ a*/ν` (with the
relative Home wage falling by less than the factor `ν`, `w/w* ≤ ν · w'/w*'`), Home's real wage
rises weakly in terms of every good. -/
theorem productivity_rise_home_realWage {a aS w wS w' wS' ν : ℝ} (ha : 0 < a)
    (haS : 0 < aS) (hν : 0 < ν) (hw : 0 < w) (hwS : 0 < wS) (hw' : 0 < w') (hwS' : 0 < wS')
    (hless : w / wS ≤ ν * (w' / wS')) :
    w / freeTradePrice a aS w wS ≤ w' / freeTradePrice a (aS / ν) w' wS' := by
  rw [homeRealWage_eq ha haS hw hwS, homeRealWage_eq ha (by positivity) hw' hwS']
  have e : w' / wS' / (aS / ν) = ν * (w' / wS') / aS := by field_simp
  rw [e]
  exact max_le_max le_rfl (div_le_div_of_nonneg_right hless haS.le)

/-- O&R p. 242: after the Foreign productivity rise `a* ↦ a*/ν`, `ν ≥ 1`, with the relative
Home wage falling (`w'/w*' ≤ w/w*`), Foreign's real wage rises weakly in terms of every good. -/
theorem productivity_rise_foreign_realWage {a aS w wS w' wS' ν : ℝ} (ha : 0 < a)
    (haS : 0 < aS) (hν : 1 ≤ ν) (hw : 0 < w) (hwS : 0 < wS) (hw' : 0 < w') (hwS' : 0 < wS')
    (hfall : w' / wS' ≤ w / wS) :
    wS / freeTradePrice a aS w wS ≤ wS' / freeTradePrice a (aS / ν) w' wS' := by
  rw [foreignRealWage_eq ha haS hw hwS, foreignRealWage_eq ha (by positivity) hw' hwS']
  have hr : wS / w ≤ wS' / w' := by
    rw [div_le_div_iff₀ hw hw']; rw [div_le_div_iff₀ hwS' hwS] at hfall; linarith
  have e : 1 / (aS / ν) = ν / aS := by field_simp
  rw [e]
  exact max_le_max (div_le_div_of_nonneg_right hr ha.le)
    (div_le_div_of_nonneg_right hν haS.le)

end ObstfeldRogoff.RealExchangeRate.DFSStatic
