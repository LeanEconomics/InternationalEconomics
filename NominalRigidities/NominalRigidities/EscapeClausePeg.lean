/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import NominalRigidities.BarroGordon
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.Order.IntermediateValue

/-!
# Pegging the exchange rate: the escape clause and multiple equilibria

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §9.5.4
(pp. 648–653), eqs. (49)–(58), footnotes 38–40 and Figure 9.12 (after Obstfeld 1996b).

With PPP, inflation is depreciation. The government minimises
`(y − ȳ − k)² + χπ² + C(π)` with output `y = ȳ + (π − πᵉ) − z` (49)–(50) and fixed
realignment costs `C = c̄` (devaluation), `c̲` (revaluation), `0` (peg). Write
`w = k + πᵉ + z`, `s̄ = √(c̄(1 + χ))`, `s̲ = √(c̲(1 + χ))`.

* (51)–(56), T23: `L^FIX − L^FLEX = w²/(1 + χ)`; the escape-clause rule "devalue to
  `w/(1 + χ)` iff `w > s̄` (i.e. `z > z̄`), revalue iff `w < −s̲` (`z < z̲`), else peg" is
  optimal against **every** `π`, and is the unique optimum off the two indifference points.
* (57)–(58), T24: with `z` uniform on `[−Z, Z]` the expected depreciation is the genuine
  integral `Eπ = (1/2Z)∫ π(k + πᵉ + z) dz`, and it equals the book's formula (58) with the
  clamped thresholds of fn 38, for **every** `πᵉ`. Regimes: both thresholds interior
  (`Eπ = (k + πᵉ)/(1 + χ) − (c̄ − c̲)/(4Z)`, a parallel shift of the free-float line),
  revaluation choked off (`Eπ = ((k + πᵉ + Z)² − s̄²)/(4Z(1 + χ))`, strictly convex), free
  float (`Eπ = (k + πᵉ)/(1 + χ)`); the book's three slopes (p. 652) and
  `dz̄/dπᵉ = dz̲/dπᵉ = −1` (p. 651) are verified. `Eπ` is continuous in `πᵉ`.
* T25: on the book's domain (`πᵉ ≥ −i*` with both thresholds interior at `−i*`), there are
  **at most three** equilibria `πᵉ = Eπ`; sufficient conditions for **exactly three**
  (strict fn 40 is needed: with equality the convex regime has no equilibrium below `k/χ`);
  that configuration also forces `s̄ > 2χZ` (a branch steeper than 45°); an equilibrium
  exists for every parameter configuration (over all `πᵉ`, fn 38).
* Corrections. (i) Fig. 9.12 draws the low equilibrium on the flat branch below the
  free-float line; that requires `c̄ > c̲` (with `c̄ = c̲` the branch *is* the free-float
  line). But three equilibria as such do **not** need `c̄ > c̲`: an explicit example with
  `c̄ = c̲` has three. (ii) Fn 40 characterises equilibria of the free-float *regime*, not
  the value `πᵉ = k/χ`: with `c̄ = c̲`, `πᵉ = k/χ` can be an equilibrium although fn 40
  fails.
-/

namespace ObstfeldRogoff.NominalRigidities.EscapeClausePeg

open Set MeasureTheory intervalIntegral
open ObstfeldRogoff.NominalRigidities.BarroGordon

/-! ## The government's problem, (49)–(56) -/

/-- O&R (49), p. 648: the fixed cost of a parity change: `c̄` for a devaluation (`π > 0`),
`c̲` for a revaluation (`π < 0`), `0` if the peg is kept. -/
noncomputable def realignCost (cbar cund π : ℝ) : ℝ :=
  if 0 < π then cbar else if π < 0 then cund else 0

/-- O&R (49)–(50): the government's loss `(π − πᵉ − z − k)² + χπ² + C(π)`. -/
noncomputable def pegLoss (χ k cbar cund π πe z : ℝ) : ℝ :=
  bgLoss χ k π πe z + realignCost cbar cund π

/-- O&R (49)–(50), pp. 648–649: with `y = ȳ + (π − πᵉ) − z` and target `ȳ + k`, the loss
(49) is `pegLoss`. -/
theorem pegLoss_derivation (ybar k χ cbar cund π πe z : ℝ) :
    ((ybar + (π - πe) - z) - (ybar + k)) ^ 2 + χ * π ^ 2 + realignCost cbar cund π =
      pegLoss χ k cbar cund π πe z := by
  unfold pegLoss bgLoss
  ring

/-- O&R (52), p. 649: under the flexible response (51) output is
`ȳ + (k − χπᵉ − χz)/(1 + χ)`. -/
theorem output_flex (χ k πe z : ℝ) (hχ : 0 < 1 + χ) :
    bestResponse χ k πe z - πe - z = (k - χ * πe - χ * z) / (1 + χ) := by
  unfold bestResponse
  field_simp
  ring

/-- O&R (53)–(54), p. 649: `L^FLEX = χ(k + πᵉ + z)²/(1 + χ)`, `L^FIX = (k + z + πᵉ)²`, and
`L^FIX − L^FLEX = (k + πᵉ + z)²/(1 + χ) ≥ 0`. -/
theorem fix_sub_flex (χ k πe z : ℝ) (hχ : 0 < 1 + χ) :
    bgLoss χ k (bestResponse χ k πe z) πe z = χ * (k + πe + z) ^ 2 / (1 + χ) ∧
      bgLoss χ k 0 πe z = (k + z + πe) ^ 2 ∧
      bgLoss χ k 0 πe z - bgLoss χ k (bestResponse χ k πe z) πe z =
        (k + πe + z) ^ 2 / (1 + χ) := by
  refine ⟨bgLoss_bestResponse χ k πe z hχ, by unfold bgLoss; ring, ?_⟩
  rw [bgLoss_bestResponse χ k πe z hχ]
  unfold bgLoss
  field_simp
  ring

/-- O&R (55)–(56): the realignment thresholds `s = √(c(1 + χ))`. -/
noncomputable def thr (χ c : ℝ) : ℝ := Real.sqrt (c * (1 + χ))

/-- O&R (55)–(56): `s² = c(1 + χ)`. -/
theorem thr_sq (χ c : ℝ) (hc : 0 ≤ c) (hχ : 0 < 1 + χ) : thr χ c ^ 2 = c * (1 + χ) :=
  Real.sq_sqrt (mul_nonneg hc hχ.le)

/-- O&R (55)–(56): `s ≥ 0`. -/
theorem thr_nonneg (χ c : ℝ) : 0 ≤ thr χ c := Real.sqrt_nonneg _

/-- O&R (55)–(56), p. 650: the escape-clause policy as a function of `w = k + πᵉ + z`:
devalue to `w/(1 + χ)` if `w > s̄`, revalue to `w/(1 + χ)` if `w < −s̲`, else peg. -/
noncomputable def govPolicy (χ sb su w : ℝ) : ℝ :=
  if sb < w then w / (1 + χ) else if w < -su then w / (1 + χ) else 0

/-- O&R (55), p. 650: devaluation happens exactly when `z > z̄ = s̄ − k − πᵉ`. -/
theorem devalue_iff (sb k πe z : ℝ) : sb < k + πe + z ↔ sb - k - πe < z := by
  constructor <;> intro h <;> linarith

/-- O&R (56), p. 650: revaluation happens exactly when `z < z̲ = −s̲ − k − πᵉ`. -/
theorem revalue_iff (su k πe z : ℝ) : k + πe + z < -su ↔ z < -su - k - πe := by
  constructor <;> intro h <;> linarith

/-- O&R p. 650: the devaluation criterion `L^FIX − L^FLEX > c̄` is `w > s̄` (for `w ≥ 0`). -/
theorem devalue_criterion (χ cbar w : ℝ) (hχ : 0 < 1 + χ) (hc : 0 ≤ cbar) (hw : 0 ≤ w) :
    cbar < w ^ 2 / (1 + χ) ↔ thr χ cbar < w := by
  rw [lt_div_iff₀ hχ, ← thr_sq χ cbar hc hχ]
  exact pow_lt_pow_iff_left₀ (thr_nonneg χ cbar) hw two_ne_zero

/-- O&R (31), (50): the loss in terms of `w = k + πᵉ + z`, `(π − w)² + χπ²`. -/
theorem bgLoss_expand (χ k π πe z : ℝ) :
    bgLoss χ k π πe z = (π - (k + πe + z)) ^ 2 + χ * π ^ 2 := by
  unfold bgLoss
  ring

/-- O&R (51)–(56), T23: the escape-clause rule is optimal against every inflation rate. -/
theorem govPolicy_optimal (χ k cbar cund πe z : ℝ) (hχ : 0 < χ) (hcb : 0 ≤ cbar)
    (hcu : 0 ≤ cund) (π : ℝ) :
    pegLoss χ k cbar cund (govPolicy χ (thr χ cbar) (thr χ cund) (k + πe + z)) πe z ≤
      pegLoss χ k cbar cund π πe z := by
  have hχ1 : 0 < 1 + χ := by linarith
  set w := k + πe + z with hw
  set sb := thr χ cbar
  set su := thr χ cund
  have hsb := thr_sq χ cbar hcb hχ1
  have hsu := thr_sq χ cund hcu hχ1
  have hsb0 : 0 ≤ sb := thr_nonneg χ cbar
  have hsu0 : 0 ≤ su := thr_nonneg χ cund
  have hmin : ∀ x, χ * w ^ 2 / (1 + χ) ≤ bgLoss χ k x πe z := fun x => by
    have := bestResponse_isMin χ k x πe z hχ1
    rwa [bgLoss_bestResponse χ k πe z hχ1] at this
  have hflex : bgLoss χ k (w / (1 + χ)) πe z = χ * w ^ 2 / (1 + χ) :=
    bgLoss_bestResponse χ k πe z hχ1
  have hzero : bgLoss χ k 0 πe z = w ^ 2 := by rw [bgLoss_expand χ k]; ring
  have hpos : ∀ x, 0 < x → w ≤ 0 → w ^ 2 ≤ bgLoss χ k x πe z := fun x hx hw0 => by
    rw [bgLoss_expand χ k]
    nlinarith [mul_nonneg hχ.le (sq_nonneg x)]
  have hneg : ∀ x, x < 0 → 0 ≤ w → w ^ 2 ≤ bgLoss χ k x πe z := fun x hx hw0 => by
    rw [bgLoss_expand χ k]
    nlinarith [mul_nonneg hχ.le (sq_nonneg x)]
  have hdiff : w ^ 2 - χ * w ^ 2 / (1 + χ) = w ^ 2 / (1 + χ) := by
    field_simp
    ring
  have hc_π : ∀ x, 0 < x → realignCost cbar cund x = cbar := fun x hx => by
    simp [realignCost, hx]
  have hc_n : ∀ x, x < 0 → realignCost cbar cund x = cund := fun x hx => by
    simp [realignCost, hx, not_lt.2 hx.le]
  have hc_0 : realignCost cbar cund 0 = 0 := by simp [realignCost]
  have hcost_nonneg : ∀ x, 0 ≤ realignCost cbar cund x := fun x => by
    unfold realignCost
    split_ifs <;> linarith
  unfold pegLoss govPolicy
  split_ifs with h1 h2
  · -- devaluation branch: `w > s̄`
    have hw0 : 0 < w := lt_of_le_of_lt hsb0 h1
    have hwsq : cbar * (1 + χ) < w ^ 2 := by rw [← hsb]; nlinarith
    have hcb' : cbar < w ^ 2 / (1 + χ) := by rw [lt_div_iff₀ hχ1]; linarith
    rw [hflex, hc_π _ (div_pos hw0 hχ1)]
    rcases lt_trichotomy π 0 with hπ | hπ | hπ
    · rw [hc_n π hπ]
      linarith [hneg π hπ hw0.le]
    · rw [hπ, hzero, hc_0]
      linarith
    · rw [hc_π π hπ]
      linarith [hmin π]
  · -- revaluation branch: `w < −s̲`
    have hw0 : w < 0 := by linarith
    have hwsq : cund * (1 + χ) < w ^ 2 := by rw [← hsu]; nlinarith
    have hcu' : cund < w ^ 2 / (1 + χ) := by rw [lt_div_iff₀ hχ1]; linarith
    rw [hflex, hc_n _ (div_neg_of_neg_of_pos hw0 hχ1)]
    rcases lt_trichotomy π 0 with hπ | hπ | hπ
    · rw [hc_n π hπ]
      linarith [hmin π]
    · rw [hπ, hzero, hc_0]
      linarith
    · rw [hc_π π hπ]
      linarith [hpos π hπ hw0.le]
  · -- peg branch: `−s̲ ≤ w ≤ s̄`
    push Not at h1 h2
    rw [hzero, hc_0, add_zero]
    rcases lt_trichotomy π 0 with hπ | hπ | hπ
    · rw [hc_n π hπ]
      rcases le_or_gt 0 w with hw0 | hw0
      · linarith [hneg π hπ hw0, hcost_nonneg π]
      · have hwsq : w ^ 2 ≤ cund * (1 + χ) := by rw [← hsu]; nlinarith
        have : w ^ 2 / (1 + χ) ≤ cund := by rw [div_le_iff₀ hχ1]; linarith
        linarith [hmin π]
    · rw [hπ, hzero, hc_0]
      linarith
    · rw [hc_π π hπ]
      rcases le_or_gt w 0 with hw0 | hw0
      · linarith [hpos π hπ hw0]
      · have hwsq : w ^ 2 ≤ cbar * (1 + χ) := by rw [← hsb]; nlinarith
        have : w ^ 2 / (1 + χ) ≤ cbar := by rw [div_le_iff₀ hχ1]; linarith
        linarith [hmin π]

/-- O&R (55)–(56), T23: away from the two indifference points `w = s̄`, `w = −s̲`, the
escape-clause rule is the **unique** optimum. -/
theorem govPolicy_unique (χ k cbar cund πe z : ℝ) (hχ : 0 < χ) (hcb : 0 ≤ cbar)
    (hcu : 0 ≤ cund) (hne1 : k + πe + z ≠ thr χ cbar) (hne2 : k + πe + z ≠ -thr χ cund)
    (π : ℝ)
    (hπ : pegLoss χ k cbar cund π πe z ≤
      pegLoss χ k cbar cund (govPolicy χ (thr χ cbar) (thr χ cund) (k + πe + z)) πe z) :
    π = govPolicy χ (thr χ cbar) (thr χ cund) (k + πe + z) := by
  have hχ1 : 0 < 1 + χ := by linarith
  set w := k + πe + z with hw
  set sb := thr χ cbar
  set su := thr χ cund
  have hsb := thr_sq χ cbar hcb hχ1
  have hsu := thr_sq χ cund hcu hχ1
  have hsb0 : 0 ≤ sb := thr_nonneg χ cbar
  have hsu0 : 0 ≤ su := thr_nonneg χ cund
  have hflex : bgLoss χ k (w / (1 + χ)) πe z = χ * w ^ 2 / (1 + χ) :=
    bgLoss_bestResponse χ k πe z hχ1
  have hzero : bgLoss χ k 0 πe z = w ^ 2 := by rw [bgLoss_expand χ k]; ring
  have hmin : ∀ x, χ * w ^ 2 / (1 + χ) ≤ bgLoss χ k x πe z := fun x => by
    have := bestResponse_isMin χ k x πe z hχ1
    rwa [bgLoss_bestResponse χ k πe z hχ1] at this
  have hbr : ∀ x, bgLoss χ k x πe z ≤ χ * w ^ 2 / (1 + χ) → x = w / (1 + χ) := fun x hx => by
    have := eq_bestResponse_of_le χ k x πe z hχ1 (by rwa [bgLoss_bestResponse χ k πe z hχ1])
    rw [this]
    rfl
  have hpos : ∀ x, 0 < x → w ≤ 0 → w ^ 2 < bgLoss χ k x πe z := fun x hx hw0 => by
    rw [bgLoss_expand χ k]
    nlinarith [mul_pos hχ (pow_pos hx 2)]
  have hneg : ∀ x, x < 0 → 0 ≤ w → w ^ 2 < bgLoss χ k x πe z := fun x hx hw0 => by
    rw [bgLoss_expand χ k]
    nlinarith [mul_pos hχ (pow_pos (neg_pos.2 hx) 2)]
  have hdiff : w ^ 2 - χ * w ^ 2 / (1 + χ) = w ^ 2 / (1 + χ) := by
    field_simp
    ring
  have hc_π : ∀ x, 0 < x → realignCost cbar cund x = cbar := fun x hx => by
    simp [realignCost, hx]
  have hc_n : ∀ x, x < 0 → realignCost cbar cund x = cund := fun x hx => by
    simp [realignCost, hx, not_lt.2 hx.le]
  have hc_0 : realignCost cbar cund 0 = 0 := by simp [realignCost]
  unfold pegLoss at hπ
  unfold govPolicy at hπ ⊢
  split_ifs at hπ ⊢ with h1 h2
  · have hw0 : 0 < w := lt_of_le_of_lt hsb0 h1
    have hwsq : cbar * (1 + χ) < w ^ 2 := by rw [← hsb]; nlinarith
    have hcb' : cbar < w ^ 2 / (1 + χ) := by rw [lt_div_iff₀ hχ1]; linarith
    rw [hflex, hc_π _ (div_pos hw0 hχ1)] at hπ
    rcases lt_trichotomy π 0 with hp | hp | hp
    · rw [hc_n π hp] at hπ
      linarith [hneg π hp hw0.le]
    · rw [hp, hzero, hc_0] at hπ
      linarith
    · rw [hc_π π hp] at hπ
      exact hbr π (by linarith)
  · have hw0 : w < 0 := by linarith
    have hwsq : cund * (1 + χ) < w ^ 2 := by rw [← hsu]; nlinarith
    have hcu' : cund < w ^ 2 / (1 + χ) := by rw [lt_div_iff₀ hχ1]; linarith
    rw [hflex, hc_n _ (div_neg_of_neg_of_pos hw0 hχ1)] at hπ
    rcases lt_trichotomy π 0 with hp | hp | hp
    · rw [hc_n π hp] at hπ
      exact hbr π (by linarith)
    · rw [hp, hzero, hc_0] at hπ
      linarith
    · rw [hc_π π hp] at hπ
      linarith [hpos π hp hw0.le]
  · push Not at h1 h2
    have h1' : w < sb := lt_of_le_of_ne h1 hne1
    have h2' : -su < w := lt_of_le_of_ne h2 (Ne.symm hne2)
    rw [hzero, hc_0, add_zero] at hπ
    rcases lt_trichotomy π 0 with hp | hp | hp
    · rw [hc_n π hp] at hπ
      rcases le_or_gt 0 w with hw0 | hw0
      · linarith [hneg π hp hw0, hcu]
      · have hwsq : w ^ 2 < cund * (1 + χ) := by rw [← hsu]; nlinarith
        have : w ^ 2 / (1 + χ) < cund := by rw [div_lt_iff₀ hχ1]; linarith
        linarith [hmin π]
    · exact hp
    · rw [hc_π π hp] at hπ
      rcases le_or_gt w 0 with hw0 | hw0
      · linarith [hpos π hp hw0, hcb]
      · have hwsq : w ^ 2 < cbar * (1 + χ) := by rw [← hsb]; nlinarith
        have : w ^ 2 / (1 + χ) < cbar := by rw [div_lt_iff₀ hχ1]; linarith
        linarith [hmin π]

/-- O&R p. 650: the escape-clause policy is nondecreasing in `w` (needed for integrability). -/
theorem govPolicy_monotone (χ sb su : ℝ) (hχ : 0 < 1 + χ) (hsb : 0 ≤ sb) (hsu : 0 ≤ su) :
    Monotone (govPolicy χ sb su) := by
  intro a b hab
  unfold govPolicy
  split_ifs <;>
    first
    | linarith
    | exact (div_le_div_iff_of_pos_right hχ).2 hab
    | exact div_nonneg (by linarith) hχ.le
    | exact div_nonpos_of_nonpos_of_nonneg (by linarith) hχ.le

/-! ## Expected depreciation, (57)–(58) -/

/-- O&R (57)–(58), p. 650: expected depreciation with `z` uniform on `[−Z, Z]`,
`Eπ = (1/2Z)∫_{−Z}^{Z} π(k + πᵉ + z) dz`. -/
noncomputable def expDep (χ k cbar cund Z πe : ℝ) : ℝ :=
  1 / (2 * Z) * ∫ z in (-Z)..Z, govPolicy χ (thr χ cbar) (thr χ cund) (k + πe + z)

/-- O&R fn 38, p. 650: the clamped devaluation threshold `max(min(s̄ − w₀, Z), −Z)`. -/
noncomputable def zbarC (sb w0 Z : ℝ) : ℝ := max (min (sb - w0) Z) (-Z)

/-- O&R fn 38, p. 650: the clamped revaluation threshold `min(max(−s̲ − w₀, −Z), Z)`. -/
noncomputable def zundC (su w0 Z : ℝ) : ℝ := min (max (-su - w0) (-Z)) Z

/-- Integration tool for (58): functions agreeing on the open interval have the same
integral. -/
theorem integral_congr_Ioo {f g : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (h : EqOn f g (Ioo a b)) :
    ∫ x in a..b, f x = ∫ x in a..b, g x := by
  rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab,
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  exact setIntegral_congr_fun measurableSet_Ioo h

/-- Integration tool for (58): `∫_a^b (w₀ + z)/(1 + χ) dz = ((w₀ + b)² − (w₀ + a)²)/(2(1 + χ))`. -/
theorem integral_linear (w0 χ a b : ℝ) (hχ : 0 < 1 + χ) :
    ∫ z in a..b, (w0 + z) / (1 + χ) = ((w0 + b) ^ 2 - (w0 + a) ^ 2) / (2 * (1 + χ)) := by
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add intervalIntegrable_const
    intervalIntegrable_id, intervalIntegral.integral_const, integral_id, smul_eq_mul]
  field_simp
  ring

/-- O&R (58), p. 650, for **every** `πᵉ` (T24): with `w₀ = k + πᵉ` and the clamped thresholds
`z̄, z̲` of fn 38, `∫_{−Z}^{Z} π dz = ((2Z − (z̄ − z̲))w₀ − (z̄² − z̲²)/2)/(1 + χ)`. -/
theorem integral_govPolicy (χ sb su Z w0 : ℝ) (hχ : 0 < 1 + χ) (hsb : 0 ≤ sb) (hsu : 0 ≤ su)
    (hZ : 0 < Z) :
    ∫ z in (-Z)..Z, govPolicy χ sb su (w0 + z) =
      ((2 * Z - (zbarC sb w0 Z - zundC su w0 Z)) * w0 -
        (zbarC sb w0 Z ^ 2 - zundC su w0 Z ^ 2) / 2) / (1 + χ) := by
  set zb := zbarC sb w0 Z with hzb
  set zu := zundC su w0 Z with hzu
  have h1 : -Z ≤ zu := le_min (le_max_right _ _) (by linarith)
  have h3 : zb ≤ Z := max_le (min_le_right _ _) (by linarith)
  have h2 : zu ≤ zb := by
    rw [hzb, hzu, zbarC, zundC]
    simp only [min_def, max_def]
    split_ifs <;> linarith
  have hmono : Monotone fun z => govPolicy χ sb su (w0 + z) :=
    (govPolicy_monotone χ sb su hχ hsb hsu).comp fun a b h => add_le_add_right h w0
  have hint : ∀ a b, IntervalIntegrable (fun z => govPolicy χ sb su (w0 + z)) volume a b :=
    fun a b => hmono.intervalIntegrable
  rw [← integral_add_adjacent_intervals (hint (-Z) zu) (hint zu Z),
    ← integral_add_adjacent_intervals (hint zu zb) (hint zb Z)]
  have eA : ∫ z in (-Z)..zu, govPolicy χ sb su (w0 + z) =
      ∫ z in (-Z)..zu, (w0 + z) / (1 + χ) := by
    refine integral_congr_Ioo h1 fun z hz => ?_
    have hlt : z < max (-su - w0) (-Z) := lt_of_lt_of_le hz.2 (min_le_left _ _)
    have hw : w0 + z < -su := by
      rcases lt_max_iff.1 hlt with h | h
      · linarith
      · linarith [hz.1]
    have hn : ¬ sb < w0 + z := by linarith
    simp only [govPolicy, hn, hw, ↓reduceIte]
  have eB : ∫ z in zu..zb, govPolicy χ sb su (w0 + z) = ∫ _ in zu..zb, (0 : ℝ) := by
    refine integral_congr_Ioo h2 fun z hz => ?_
    have hz1 : -Z < z := lt_of_le_of_lt h1 hz.1
    have hz2 : z < Z := lt_of_lt_of_le hz.2 h3
    have hup : z < sb - w0 := by
      rcases lt_max_iff.1 hz.2 with h | h
      · rcases lt_min_iff.1 h with ⟨h', -⟩
        exact h'
      · linarith
    have hlo : -su - w0 < z := by
      rcases min_lt_iff.1 hz.1 with h | h
      · exact (max_lt_iff.1 h).1
      · linarith
    have hn1 : ¬ sb < w0 + z := by linarith
    have hn2 : ¬ w0 + z < -su := by linarith
    simp only [govPolicy, hn1, hn2, ↓reduceIte]
  have eC : ∫ z in zb..Z, govPolicy χ sb su (w0 + z) = ∫ z in zb..Z, (w0 + z) / (1 + χ) := by
    refine integral_congr_Ioo h3 fun z hz => ?_
    have hw : sb < w0 + z := by
      have : min (sb - w0) Z < z := lt_of_le_of_lt (le_max_left _ _) hz.1
      rcases min_lt_iff.1 this with h | h
      · linarith
      · linarith [hz.2]
    simp only [govPolicy, hw, ↓reduceIte]
  rw [eA, eB, eC, integral_linear w0 χ _ _ hχ, integral_linear w0 χ _ _ hχ,
    intervalIntegral.integral_zero]
  field_simp
  ring

/-- O&R (58), p. 650: the book's formula
`Eπ = (1/(1 + χ))[(1 − (z̄ − z̲)/(2Z))(k + πᵉ) − (z̄² − z̲²)/(4Z)]` (thresholds clamped as in
fn 38), valid for every `πᵉ`. -/
theorem expDep_eq (χ k cbar cund Z πe : ℝ) (hχ : 0 < 1 + χ) (hZ : 0 < Z) :
    expDep χ k cbar cund Z πe =
      1 / (1 + χ) * ((1 - (zbarC (thr χ cbar) (k + πe) Z - zundC (thr χ cund) (k + πe) Z) /
        (2 * Z)) * (k + πe) - (zbarC (thr χ cbar) (k + πe) Z ^ 2 -
          zundC (thr χ cund) (k + πe) Z ^ 2) / (4 * Z)) := by
  unfold expDep
  rw [integral_govPolicy χ _ _ Z (k + πe) hχ (thr_nonneg χ cbar) (thr_nonneg χ cund) hZ]
  field_simp
  ring

/-- O&R (58): expected depreciation is continuous in `πᵉ`. -/
theorem expDep_continuous (χ k cbar cund Z : ℝ) (hχ : 0 < 1 + χ) (hZ : 0 < Z) :
    Continuous (expDep χ k cbar cund Z) := by
  have : expDep χ k cbar cund Z = fun πe =>
      1 / (1 + χ) * ((1 - (zbarC (thr χ cbar) (k + πe) Z - zundC (thr χ cund) (k + πe) Z) /
        (2 * Z)) * (k + πe) - (zbarC (thr χ cbar) (k + πe) Z ^ 2 -
          zundC (thr χ cund) (k + πe) Z ^ 2) / (4 * Z)) :=
    funext fun πe => expDep_eq χ k cbar cund Z πe hχ hZ
  rw [this]
  unfold zbarC zundC
  fun_prop

/-- O&R p. 652, T24, regime A (both thresholds interior, `s̄ − Z ≤ k + πᵉ ≤ Z − s̲`):
`Eπ = (k + πᵉ)/(1 + χ) − (c̄ − c̲)/(4Z)`, the free-float line shifted by `(c̄ − c̲)/(4Z)`. -/
theorem expDep_regimeA (χ k cbar cund Z πe : ℝ) (hχ : 0 < 1 + χ) (hZ : 0 < Z)
    (hcb : 0 ≤ cbar) (hcu : 0 ≤ cund) (hA1 : thr χ cbar - Z ≤ k + πe)
    (hA2 : k + πe ≤ Z - thr χ cund) :
    expDep χ k cbar cund Z πe = (k + πe) / (1 + χ) - (cbar - cund) / (4 * Z) := by
  have hsb0 := thr_nonneg χ cbar
  have hsu0 := thr_nonneg χ cund
  rw [expDep_eq χ k cbar cund Z πe hχ hZ]
  have e1 : zbarC (thr χ cbar) (k + πe) Z = thr χ cbar - (k + πe) := by
    unfold zbarC
    rw [min_eq_left (by linarith), max_eq_left (by linarith)]
  have e2 : zundC (thr χ cund) (k + πe) Z = -thr χ cund - (k + πe) := by
    unfold zundC
    rw [max_eq_left (by linarith), min_eq_left (by linarith)]
  rw [e1, e2]
  have h1 := thr_sq χ cbar hcb hχ
  have h2 := thr_sq χ cund hcu hχ
  have hc : cbar - cund = (thr χ cbar ^ 2 - thr χ cund ^ 2) / (1 + χ) := by
    rw [h1, h2]
    field_simp
  rw [hc]
  field_simp
  ring

/-- O&R p. 652, T24, regime M (revaluation choked off, `Z − s̲ ≤ k + πᵉ ≤ Z + s̄`, with
`k + πᵉ ≥ s̄ − Z`): `Eπ = ((k + πᵉ + Z)² − s̄²)/(4Z(1 + χ))`. -/
theorem expDep_regimeM (χ k cbar cund Z πe : ℝ) (hχ : 0 < 1 + χ) (hZ : 0 < Z)
    (hM0 : thr χ cbar - Z ≤ k + πe) (hM1 : Z - thr χ cund ≤ k + πe)
    (hM2 : k + πe ≤ Z + thr χ cbar) :
    expDep χ k cbar cund Z πe = ((k + πe + Z) ^ 2 - thr χ cbar ^ 2) / (4 * Z * (1 + χ)) := by
  rw [expDep_eq χ k cbar cund Z πe hχ hZ]
  have e1 : zbarC (thr χ cbar) (k + πe) Z = thr χ cbar - (k + πe) := by
    unfold zbarC
    rw [min_eq_left (by linarith), max_eq_left (by linarith)]
  have e2 : zundC (thr χ cund) (k + πe) Z = -Z := by
    unfold zundC
    rw [max_eq_right (by linarith), min_eq_left (by linarith)]
  rw [e1, e2]
  field_simp
  ring

/-- O&R p. 652, T24, free-float regime (`k + πᵉ ≥ Z + s̄`): `Eπ = (k + πᵉ)/(1 + χ)`. -/
theorem expDep_float (χ k cbar cund Z πe : ℝ) (hχ : 0 < 1 + χ) (hZ : 0 < Z)
    (hF : Z + thr χ cbar ≤ k + πe) :
    expDep χ k cbar cund Z πe = (k + πe) / (1 + χ) := by
  have hsu0 := thr_nonneg χ cund
  have hsb0 := thr_nonneg χ cbar
  rw [expDep_eq χ k cbar cund Z πe hχ hZ]
  have e1 : zbarC (thr χ cbar) (k + πe) Z = -Z := by
    unfold zbarC
    rw [min_eq_left (by linarith), max_eq_right (by linarith)]
  have e2 : zundC (thr χ cund) (k + πe) Z = -Z := by
    unfold zundC
    rw [max_eq_right (by linarith), min_eq_left (by linarith)]
  rw [e1, e2]
  field_simp
  ring

/-- O&R fn 38 (T24): if `k + πᵉ ≤ −Z − s̲` the government always revalues:
`Eπ = (k + πᵉ)/(1 + χ)`. -/
theorem expDep_alwaysRevalue (χ k cbar cund Z πe : ℝ) (hχ : 0 < 1 + χ) (hZ : 0 < Z)
    (hR : k + πe ≤ -Z - thr χ cund) :
    expDep χ k cbar cund Z πe = (k + πe) / (1 + χ) := by
  have hsu0 := thr_nonneg χ cund
  have hsb0 := thr_nonneg χ cbar
  rw [expDep_eq χ k cbar cund Z πe hχ hZ]
  have e1 : zbarC (thr χ cbar) (k + πe) Z = Z := by
    unfold zbarC
    rw [min_eq_right (by linarith), max_eq_left (by linarith)]
  have e2 : zundC (thr χ cund) (k + πe) Z = Z := by
    unfold zundC
    rw [max_eq_left (by linarith), min_eq_right (by linarith)]
  rw [e1, e2]
  field_simp
  ring

/-- O&R p. 652 (slopes): in the interior of regime A, `dEπ/dπᵉ = 1/(1 + χ)`. -/
theorem hasDerivAt_expDep_A (χ k cbar cund Z πe : ℝ) (hχ : 0 < 1 + χ) (hZ : 0 < Z)
    (hcb : 0 ≤ cbar) (hcu : 0 ≤ cund) (hA1 : thr χ cbar - Z < k + πe)
    (hA2 : k + πe < Z - thr χ cund) :
    HasDerivAt (expDep χ k cbar cund Z) (1 / (1 + χ)) πe := by
  have hev : (fun x => (k + x) / (1 + χ) - (cbar - cund) / (4 * Z)) =ᶠ[nhds πe]
      expDep χ k cbar cund Z := by
    have : Ioo (thr χ cbar - Z - k) (Z - thr χ cund - k) ∈ nhds πe :=
      Ioo_mem_nhds (by linarith) (by linarith)
    filter_upwards [this] with x hx
    rw [expDep_regimeA χ k cbar cund Z x hχ hZ hcb hcu (by linarith [hx.1])
      (by linarith [hx.2])]
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev.symm
  have := (((hasDerivAt_id' πe).const_add k).div_const (1 + χ)).sub_const
    ((cbar - cund) / (4 * Z))
  exact this

/-- O&R p. 652 (slopes): in the interior of regime M,
`dEπ/dπᵉ = (1/(1 + χ))(1/2 + (k + πᵉ)/(2Z))`. -/
theorem hasDerivAt_expDep_M (χ k cbar cund Z πe : ℝ) (hχ : 0 < 1 + χ) (hZ : 0 < Z)
    (hM0 : thr χ cbar - Z < k + πe) (hM1 : Z - thr χ cund < k + πe)
    (hM2 : k + πe < Z + thr χ cbar) :
    HasDerivAt (expDep χ k cbar cund Z) (1 / (1 + χ) * (1 / 2 + (k + πe) / (2 * Z))) πe := by
  have hev : (fun x => ((k + x + Z) ^ 2 - thr χ cbar ^ 2) / (4 * Z * (1 + χ))) =ᶠ[nhds πe]
      expDep χ k cbar cund Z := by
    have : Ioo (max (thr χ cbar - Z - k) (Z - thr χ cund - k)) (Z + thr χ cbar - k) ∈
        nhds πe := Ioo_mem_nhds (max_lt (by linarith) (by linarith)) (by linarith)
    filter_upwards [this] with x hx
    have := max_lt_iff.1 hx.1
    rw [expDep_regimeM χ k cbar cund Z x hχ hZ (by linarith) (by linarith)
      (by linarith [hx.2])]
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev.symm
  have h := ((((hasDerivAt_id' πe).const_add k).add_const Z).fun_pow 2).sub_const
    (thr χ cbar ^ 2) |>.div_const (4 * Z * (1 + χ))
  convert h using 1
  field_simp
  ring

/-- O&R p. 652 (slopes): in the interior of the free-float regime, `dEπ/dπᵉ = 1/(1 + χ)`. -/
theorem hasDerivAt_expDep_float (χ k cbar cund Z πe : ℝ) (hχ : 0 < 1 + χ) (hZ : 0 < Z)
    (hF : Z + thr χ cbar < k + πe) :
    HasDerivAt (expDep χ k cbar cund Z) (1 / (1 + χ)) πe := by
  have hev : (fun x => (k + x) / (1 + χ)) =ᶠ[nhds πe] expDep χ k cbar cund Z := by
    have : Ioi (Z + thr χ cbar - k) ∈ nhds πe := Ioi_mem_nhds (by linarith)
    filter_upwards [this] with x hx
    rw [expDep_float χ k cbar cund Z x hχ hZ (by simp only [mem_Ioi] at hx; linarith)]
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev.symm
  exact ((hasDerivAt_id' πe).const_add k).div_const (1 + χ)

/-! ## Equilibria, T25 -/

/-- O&R p. 651: rational expectations, `πᵉ = Eπ(πᵉ)`: the zeros of `G(πᵉ) = Eπ − πᵉ`. -/
noncomputable def gapFn (χ k cbar cund Z πe : ℝ) : ℝ := expDep χ k cbar cund Z πe - πe

/-- T25: the quadratic of regime M, `q(πᵉ) = ((k + πᵉ + Z)² − s̄²)/(4Z(1 + χ)) − πᵉ`, written
as `α x² + β x + γ` with `α = 1/(4Z(1 + χ)) > 0`. -/
theorem quad_M_form (χ k sb Z x : ℝ) (hχ : 0 < 1 + χ) (hZ : 0 < Z) :
    ((k + x + Z) ^ 2 - sb ^ 2) / (4 * Z * (1 + χ)) - x =
      1 / (4 * Z * (1 + χ)) * x ^ 2 + (2 * (k + Z) / (4 * Z * (1 + χ)) - 1) * x +
        ((k + Z) ^ 2 - sb ^ 2) / (4 * Z * (1 + χ)) := by
  field_simp
  ring

/-- T25: a quadratic with positive leading coefficient and roots `r₁ < r₂` factors as
`α(x − r₁)(x − r₂)`. -/
theorem quad_factor (α β γ r1 r2 : ℝ) (hr : r1 < r2) (h1 : α * r1 ^ 2 + β * r1 + γ = 0)
    (h2 : α * r2 ^ 2 + β * r2 + γ = 0) (x : ℝ) :
    α * x ^ 2 + β * x + γ = α * (x - r1) * (x - r2) := by
  have hb : β = -α * (r1 + r2) := by
    have : (r1 - r2) * (α * (r1 + r2) + β) = 0 := by linear_combination h1 - h2
    rcases mul_eq_zero.1 this with h | h
    · exact absurd h (by linarith)
    · linarith
  have hc : γ = α * r1 * r2 := by
    rw [hb] at h1
    linarith
  rw [hb, hc]
  ring

/-- O&R pp. 651–652 (T25, at most three equilibria): on the book's domain `πᵉ ≥ π_L`
(with `s̄ − Z < k + π_L < Z − s̲`, "`z̲ > −Z` and `z̄ < Z` at `πᵉ = −i*`"), the equation
`πᵉ = Eπ(πᵉ)` has at most three solutions. -/
theorem at_most_three (χ k cbar cund Z πL : ℝ) (hχ : 0 < χ) (hZ : 0 < Z) (hcb : 0 ≤ cbar)
    (hcu : 0 ≤ cund) (hL1 : thr χ cbar - Z < k + πL) (hL2 : k + πL < Z - thr χ cund)
    (x1 x2 x3 x4 : ℝ) (h0 : πL ≤ x1) (h12 : x1 < x2) (h23 : x2 < x3) (h34 : x3 < x4) :
    ¬ (gapFn χ k cbar cund Z x1 = 0 ∧ gapFn χ k cbar cund Z x2 = 0 ∧
      gapFn χ k cbar cund Z x3 = 0 ∧ gapFn χ k cbar cund Z x4 = 0) := by
  have hχ1 : 0 < 1 + χ := by linarith
  have hsb0 := thr_nonneg χ cbar
  have hsu0 := thr_nonneg χ cund
  set a := Z - thr χ cund - k with ha
  set b := Z + thr χ cbar - k with hb
  have hab : a ≤ b := by linarith
  -- the three pieces
  have hGA : ∀ x, πL ≤ x → x ≤ a →
      gapFn χ k cbar cund Z x = (k + x) / (1 + χ) - (cbar - cund) / (4 * Z) - x := by
    intro x hx1 hx2
    unfold gapFn
    rw [expDep_regimeA χ k cbar cund Z x hχ1 hZ hcb hcu (by linarith) (by linarith)]
  have hGM : ∀ x, a ≤ x → x ≤ b → gapFn χ k cbar cund Z x =
      ((k + x + Z) ^ 2 - thr χ cbar ^ 2) / (4 * Z * (1 + χ)) - x := by
    intro x hx1 hx2
    unfold gapFn
    rw [expDep_regimeM χ k cbar cund Z x hχ1 hZ (by linarith) (by linarith) (by linarith)]
  have hGF : ∀ x, b ≤ x → gapFn χ k cbar cund Z x = (k + x) / (1 + χ) - x := by
    intro x hx
    unfold gapFn
    rw [expDep_float χ k cbar cund Z x hχ1 hZ (by linarith)]
  rintro ⟨g1, g2, g3, g4⟩
  -- at most one zero in `[π_L, a]` and in `[b, ∞)` (strictly decreasing lines)
  have hx2a : a < x2 := by
    by_contra h
    push Not at h
    rw [hGA x1 h0 (by linarith)] at g1
    rw [hGA x2 (by linarith) h] at g2
    have e : ((k + x1) / (1 + χ) - (cbar - cund) / (4 * Z) - x1) -
        ((k + x2) / (1 + χ) - (cbar - cund) / (4 * Z) - x2) = (x2 - x1) * (χ / (1 + χ)) := by
      field_simp
      ring
    have : 0 < (x2 - x1) * (χ / (1 + χ)) := mul_pos (by linarith) (div_pos hχ hχ1)
    linarith
  have hx3b : x3 < b := by
    by_contra h
    push Not at h
    rw [hGF x3 h] at g3
    rw [hGF x4 (by linarith)] at g4
    have e : ((k + x3) / (1 + χ) - x3) - ((k + x4) / (1 + χ) - x4) =
        (x4 - x3) * (χ / (1 + χ)) := by
      field_simp
      ring
    have : 0 < (x4 - x3) * (χ / (1 + χ)) := mul_pos (by linarith) (div_pos hχ hχ1)
    linarith
  set α := 1 / (4 * Z * (1 + χ)) with hα
  set β := 2 * (k + Z) / (4 * Z * (1 + χ)) - 1
  set γ := ((k + Z) ^ 2 - thr χ cbar ^ 2) / (4 * Z * (1 + χ))
  have hαpos : 0 < α := by positivity
  have hq : ∀ x, a ≤ x → x ≤ b → gapFn χ k cbar cund Z x = α * x ^ 2 + β * x + γ :=
    fun x h1 h2 => by rw [hGM x h1 h2, quad_M_form χ k (thr χ cbar) Z x hχ1 hZ]
  have q2 := g2
  have q3 := g3
  rw [hq x2 hx2a.le (by linarith)] at q2
  rw [hq x3 (by linarith) hx3b.le] at q3
  have hfac := quad_factor α β γ x2 x3 h23 q2 q3
  rcases le_or_gt x1 a with hx1 | hx1
  · -- `G(a) ≤ 0` from the decreasing first piece, but `q(a) = α(a − x₂)(a − x₃) > 0`
    have hGa : gapFn χ k cbar cund Z a ≤ 0 := by
      rw [hGA a (by linarith) le_rfl]
      rw [hGA x1 h0 hx1] at g1
      have : (a - x1) * (χ / (1 + χ)) ≥ 0 := mul_nonneg (by linarith) (div_pos hχ hχ1).le
      have e : (k + a) / (1 + χ) - (cbar - cund) / (4 * Z) - a =
          ((k + x1) / (1 + χ) - (cbar - cund) / (4 * Z) - x1) - (a - x1) * (χ / (1 + χ)) := by
        field_simp
        ring
      linarith
    rw [hq a le_rfl hab, hfac a] at hGa
    have : 0 < α * (a - x2) * (a - x3) := by
      have := mul_pos_of_neg_of_neg (show a - x2 < 0 by linarith) (show a - x3 < 0 by linarith)
      rw [mul_assoc]
      exact mul_pos hαpos this
    linarith
  · -- three zeros of the strictly convex quadratic
    have q1 := g1
    rw [hq x1 hx1.le (by linarith), hfac x1] at q1
    have : 0 < α * (x1 - x2) * (x1 - x3) := by
      have := mul_pos_of_neg_of_neg (show x1 - x2 < 0 by linarith) (show x1 - x3 < 0 by linarith)
      rw [mul_assoc]
      exact mul_pos hαpos this
    linarith

/-- O&R p. 652 (T25): the gap `G = Eπ − πᵉ` is continuous. -/
theorem gapFn_continuous (χ k cbar cund Z : ℝ) (hχ : 0 < 1 + χ) (hZ : 0 < Z) :
    Continuous (gapFn χ k cbar cund Z) :=
  (expDep_continuous χ k cbar cund Z hχ hZ).sub continuous_id

/-- O&R p. 652 (T25): on regime A the gap is `χ(π₁ − πᵉ)/(1 + χ)`, where
`π₁ = (k − (1 + χ)(c̄ − c̲)/(4Z))/χ` is the flat-branch equilibrium (equilibrium 1). -/
theorem gapFn_regimeA (χ k cbar cund Z πe : ℝ) (hχ : 0 < χ) (hZ : 0 < Z) (hcb : 0 ≤ cbar)
    (hcu : 0 ≤ cund) (hA1 : thr χ cbar - Z ≤ k + πe) (hA2 : k + πe ≤ Z - thr χ cund) :
    gapFn χ k cbar cund Z πe =
      χ * ((k - (1 + χ) * ((cbar - cund) / (4 * Z))) / χ - πe) / (1 + χ) := by
  have hχ1 : 0 < 1 + χ := by linarith
  unfold gapFn
  rw [expDep_regimeA χ k cbar cund Z πe hχ1 hZ hcb hcu hA1 hA2]
  field_simp
  ring

/-- O&R p. 652 (T25): on the free-float regime the gap is `(k − χπᵉ)/(1 + χ)`. -/
theorem gapFn_float (χ k cbar cund Z πe : ℝ) (hχ : 0 < 1 + χ) (hZ : 0 < Z)
    (hF : Z + thr χ cbar ≤ k + πe) :
    gapFn χ k cbar cund Z πe = (k - χ * πe) / (1 + χ) := by
  unfold gapFn
  rw [expDep_float χ k cbar cund Z πe hχ hZ hF]
  field_simp
  ring

/-- O&R p. 652, fn 40 (T25), corrected reading: an equilibrium in the free-float regime
(`z̄ ≤ −Z`, devaluation for every shock) exists iff `(1 + χ)k/χ − Z ≥ s̄`, and it is then
`πᵉ = k/χ`, the one-shot level (34). -/
theorem float_eqm_iff (χ k cbar cund Z : ℝ) (hχ : 0 < χ) (hZ : 0 < Z) :
    (∃ πe, Z + thr χ cbar ≤ k + πe ∧ gapFn χ k cbar cund Z πe = 0) ↔
      thr χ cbar ≤ (1 + χ) * k / χ - Z := by
  have hχ1 : 0 < 1 + χ := by linarith
  have e : (1 + χ) * k / χ = k + k / χ := by
    field_simp
    ring
  rw [e]
  constructor
  · rintro ⟨πe, hF, hG⟩
    rw [gapFn_float χ k cbar cund Z πe hχ1 hZ hF, div_eq_zero_iff] at hG
    rcases hG with hG | hG
    · have : πe = k / χ := by field_simp; linarith
      rw [this] at hF
      linarith
    · linarith
  · intro h
    refine ⟨k / χ, by linarith, ?_⟩
    rw [gapFn_float χ k cbar cund Z _ hχ1 hZ (by linarith)]
    field_simp
    ring

/-- O&R p. 652 (T25): any free-float-regime equilibrium is `πᵉ = k/χ`. -/
theorem float_eqm_eq (χ k cbar cund Z πe : ℝ) (hχ : 0 < χ) (hZ : 0 < Z)
    (hF : Z + thr χ cbar ≤ k + πe) (hG : gapFn χ k cbar cund Z πe = 0) : πe = k / χ := by
  have hχ1 : 0 < 1 + χ := by linarith
  rw [gapFn_float χ k cbar cund Z πe hχ1 hZ hF, div_eq_zero_iff] at hG
  rcases hG with hG | hG
  · field_simp
    linarith
  · linarith

/-- O&R Fig. 9.12 correction (T25): an equilibrium on the flat branch (regime A) strictly
below the one-shot level `k/χ` requires `c̄ > c̲`. -/
theorem flat_branch_below_needs_cbar_gt (χ k cbar cund Z πe : ℝ) (hχ : 0 < χ) (hZ : 0 < Z)
    (hcb : 0 ≤ cbar) (hcu : 0 ≤ cund) (hA1 : thr χ cbar - Z ≤ k + πe)
    (hA2 : k + πe ≤ Z - thr χ cund) (hG : gapFn χ k cbar cund Z πe = 0)
    (hlow : πe < k / χ) : cund < cbar := by
  have hχ1 : 0 < 1 + χ := by linarith
  unfold gapFn at hG
  rw [expDep_regimeA χ k cbar cund Z πe hχ1 hZ hcb hcu hA1 hA2] at hG
  have h1 : χ * πe < k := by rwa [lt_div_iff₀ hχ, mul_comm] at hlow
  have h2 : (cbar - cund) / (4 * Z) = (k - χ * πe) / (1 + χ) := by
    field_simp
    field_simp at hG
    linarith
  have h3 : 0 < (cbar - cund) / (4 * Z) := by rw [h2]; exact div_pos (by linarith) hχ1
  have := (div_pos_iff_of_pos_right (by positivity : (0 : ℝ) < 4 * Z)).1 h3
  linarith

/-- O&R Fig. 9.12 correction: with symmetric costs `c̄ = c̲` the flat branch coincides with
the free-float line `(k + πᵉ)/(1 + χ)`. -/
theorem symmetric_flat_is_float (χ k c Z πe : ℝ) (hχ : 0 < 1 + χ) (hZ : 0 < Z) (hc : 0 ≤ c)
    (hA1 : thr χ c - Z ≤ k + πe) (hA2 : k + πe ≤ Z - thr χ c) :
    expDep χ k c c Z πe = (k + πe) / (1 + χ) := by
  rw [expDep_regimeA χ k c c Z πe hχ hZ hc hc hA1 hA2]
  ring

/-- O&R pp. 651–652, T25 (exactly three equilibria, the Fig. 9.12 configuration): on the
book's domain, if `G(π_L) > 0`, the flat-branch point `π₁` lies in the interior regime A,
and fn 40 holds **strictly**, then there are exactly three equilibria `π₁ < π₂ < k/χ`, with
`π₂` in the convex regime. -/
theorem exactly_three (χ k cbar cund Z πL : ℝ) (hχ : 0 < χ) (hZ : 0 < Z) (hcb : 0 ≤ cbar)
    (hcu : 0 ≤ cund) (hL1 : thr χ cbar - Z < k + πL) (hL2 : k + πL < Z - thr χ cund)
    (hGL : 0 < gapFn χ k cbar cund Z πL)
    (hπ1 : k + (k - (1 + χ) * ((cbar - cund) / (4 * Z))) / χ < Z - thr χ cund)
    (hfn40 : Z + thr χ cbar < k + k / χ) :
    ∃ π2, Z - thr χ cund - k < π2 ∧ π2 < Z + thr χ cbar - k ∧
      πL < (k - (1 + χ) * ((cbar - cund) / (4 * Z))) / χ ∧
      (k - (1 + χ) * ((cbar - cund) / (4 * Z))) / χ < π2 ∧ π2 < k / χ ∧
      gapFn χ k cbar cund Z ((k - (1 + χ) * ((cbar - cund) / (4 * Z))) / χ) = 0 ∧
      gapFn χ k cbar cund Z π2 = 0 ∧ gapFn χ k cbar cund Z (k / χ) = 0 ∧
      ∀ x, πL ≤ x → gapFn χ k cbar cund Z x = 0 →
        x = (k - (1 + χ) * ((cbar - cund) / (4 * Z))) / χ ∨ x = π2 ∨ x = k / χ := by
  have hχ1 : 0 < 1 + χ := by linarith
  have hsb0 := thr_nonneg χ cbar
  have hsu0 := thr_nonneg χ cund
  set π1 := (k - (1 + χ) * ((cbar - cund) / (4 * Z))) / χ with hπ1def
  set a := Z - thr χ cund - k with ha
  set b := Z + thr χ cbar - k with hb
  have hGA : ∀ x, πL ≤ x → x ≤ a → gapFn χ k cbar cund Z x = χ * (π1 - x) / (1 + χ) :=
    fun x h1 h2 => gapFn_regimeA χ k cbar cund Z x hχ hZ hcb hcu (by linarith) (by linarith)
  have hL1' : πL < π1 := by
    rw [hGA πL le_rfl (by linarith)] at hGL
    have := (div_pos_iff_of_pos_right hχ1).1 hGL
    have := (mul_pos_iff_of_pos_left hχ).1 this
    linarith
  have hπ1a : π1 < a := by linarith
  have hG1 : gapFn χ k cbar cund Z π1 = 0 := by
    rw [hGA π1 hL1'.le hπ1a.le]
    simp
  have hGa : gapFn χ k cbar cund Z a < 0 := by
    rw [hGA a (by linarith) le_rfl]
    exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hχ (by linarith)) hχ1
  have hbk : b < k / χ := by linarith
  have hGb : 0 < gapFn χ k cbar cund Z b := by
    rw [gapFn_float χ k cbar cund Z b hχ1 hZ (by linarith)]
    have : χ * b < k := by rwa [lt_div_iff₀ hχ, mul_comm] at hbk
    exact div_pos (by linarith) hχ1
  have hab : a ≤ b := by linarith
  obtain ⟨π2, hπ2, hG2⟩ := intermediate_value_Icc hab
    (gapFn_continuous χ k cbar cund Z hχ1 hZ).continuousOn
    (show (0 : ℝ) ∈ Icc (gapFn χ k cbar cund Z a) (gapFn χ k cbar cund Z b) from
      ⟨hGa.le, hGb.le⟩)
  have ha2 : a < π2 := by
    rcases (mem_Icc.1 hπ2).1.lt_or_eq with h | h
    · exact h
    · rw [← h] at hG2
      linarith
  have hb2 : π2 < b := by
    rcases (mem_Icc.1 hπ2).2.lt_or_eq with h | h
    · exact h
    · rw [h] at hG2
      linarith
  have hG3 : gapFn χ k cbar cund Z (k / χ) = 0 := by
    rw [gapFn_float χ k cbar cund Z _ hχ1 hZ (by linarith)]
    field_simp
    ring
  refine ⟨π2, ha2, hb2, hL1', by linarith, by linarith, hG1, hG2, hG3, fun x hx hGx => ?_⟩
  by_contra hne
  push Not at hne
  obtain ⟨n1, n2, n3⟩ := hne
  rcases lt_or_gt_of_ne n1 with h1 | h1
  · exact at_most_three χ k cbar cund Z πL hχ hZ hcb hcu hL1 hL2 x π1 π2 (k / χ) hx h1
      (by linarith) (by linarith) ⟨hGx, hG1, hG2, hG3⟩
  rcases lt_or_gt_of_ne n2 with h2 | h2
  · exact at_most_three χ k cbar cund Z πL hχ hZ hcb hcu hL1 hL2 π1 x π2 (k / χ) hL1'.le h1
      h2 (by linarith) ⟨hG1, hGx, hG2, hG3⟩
  rcases lt_or_gt_of_ne n3 with h3 | h3
  · exact at_most_three χ k cbar cund Z πL hχ hZ hcb hcu hL1 hL2 π1 π2 x (k / χ) hL1'.le
      (by linarith) h2 h3 ⟨hG1, hG2, hGx, hG3⟩
  · exact at_most_three χ k cbar cund Z πL hχ hZ hcb hcu hL1 hL2 π1 π2 (k / χ) x hL1'.le
      (by linarith) (by linarith) h3 ⟨hG1, hG2, hG3, hGx⟩

/-- O&R Fig. 9.12 (T25): in the three-equilibrium configuration of `exactly_three`, the
costs must be asymmetric, `c̄ > c̲` (the book never states this). -/
theorem exactly_three_needs_cbar_gt (χ k cbar cund Z : ℝ) (hχ : 0 < χ) (hZ : 0 < Z)
    (hπ1 : k + (k - (1 + χ) * ((cbar - cund) / (4 * Z))) / χ < Z - thr χ cund)
    (hfn40 : Z + thr χ cbar < k + k / χ) : cund < cbar := by
  have hχ1 : 0 < 1 + χ := by linarith
  have hsb := thr_nonneg χ cbar
  have hsu0 := thr_nonneg χ cund
  have h : (k - (1 + χ) * ((cbar - cund) / (4 * Z))) / χ < k / χ := by linarith
  rw [div_lt_div_iff_of_pos_right hχ] at h
  have h2 : 0 < (1 + χ) * ((cbar - cund) / (4 * Z)) := by linarith
  have h3 := (mul_pos_iff_of_pos_left hχ1).1 h2
  have := (div_pos_iff_of_pos_right (by positivity : (0 : ℝ) < 4 * Z)).1 h3
  linarith

/-- O&R p. 652, fn 40, with exact equality: if `k + k/χ = Z + s̄` and the gap is negative at
the start `a` of the convex regime, then the convex regime `[a, k/χ)` contains **no**
equilibrium (so there are only two): strict fn 40 is needed for three. -/
theorem fn40_equality_two (χ k cbar cund Z x : ℝ) (hχ : 0 < χ) (hZ : 0 < Z)
    (hL : thr χ cbar - Z ≤ Z - thr χ cund)
    (heq : k + k / χ = Z + thr χ cbar)
    (hGa : gapFn χ k cbar cund Z (Z - thr χ cund - k) < 0)
    (hx1 : Z - thr χ cund - k ≤ x) (hx2 : x < k / χ) : gapFn χ k cbar cund Z x ≠ 0 := by
  have hχ1 : 0 < 1 + χ := by linarith
  set a := Z - thr χ cund - k
  set b := k / χ
  have hbk : Z + thr χ cbar - k = b := by linarith
  have hGM : ∀ y, a ≤ y → y ≤ b → gapFn χ k cbar cund Z y =
      1 / (4 * Z * (1 + χ)) * y ^ 2 + (2 * (k + Z) / (4 * Z * (1 + χ)) - 1) * y +
        ((k + Z) ^ 2 - thr χ cbar ^ 2) / (4 * Z * (1 + χ)) := by
    intro y h1 h2
    unfold gapFn
    rw [expDep_regimeM χ k cbar cund Z y hχ1 hZ (by linarith) (by linarith) (by linarith),
      quad_M_form χ k (thr χ cbar) Z y hχ1 hZ]
  have hχb : χ * b = k := by
    simp only [b]
    field_simp
  have hGb : gapFn χ k cbar cund Z b = 0 := by
    rw [gapFn_float χ k cbar cund Z b hχ1 hZ (by linarith), hχb, sub_self, zero_div]
  intro hx
  have hax : a < x := by
    rcases hx1.lt_or_eq with h | h
    · exact h
    · rw [← h] at hx; linarith
  have hab : a ≤ b := by linarith
  have qx := hx
  have qb := hGb
  rw [hGM x hx1 hx2.le] at qx
  rw [hGM b hab le_rfl] at qb
  have hfac := quad_factor _ _ _ x b hx2 qx qb a
  have hqa := hGa
  rw [hGM a le_rfl hab, hfac] at hqa
  have : 0 < 1 / (4 * Z * (1 + χ)) * (a - x) * (a - b) := by
    have := mul_pos_of_neg_of_neg (show a - x < 0 by linarith) (show a - b < 0 by linarith)
    rw [mul_assoc]
    exact mul_pos (by positivity) this
  linarith

/-- O&R fn 38 (T25, general existence): for `k > 0`, over all `πᵉ ∈ ℝ` (thresholds clamped)
an equilibrium `πᵉ = Eπ` always exists. -/
theorem eqm_exists (χ k cbar cund Z : ℝ) (hχ : 0 < χ) (hZ : 0 < Z) (hk : 0 < k) :
    ∃ πe, gapFn χ k cbar cund Z πe = 0 := by
  have hχ1 : 0 < 1 + χ := by linarith
  have hsb0 := thr_nonneg χ cbar
  have hsu0 := thr_nonneg χ cund
  set lo := -Z - thr χ cund - k
  set hi := max (k / χ) (Z + thr χ cbar - k)
  have hkχ : 0 < k / χ := div_pos hk hχ
  have hlohi : lo ≤ hi := le_trans (by linarith) (le_max_left _ _)
  have hGlo : 0 ≤ gapFn χ k cbar cund Z lo := by
    unfold gapFn
    rw [expDep_alwaysRevalue χ k cbar cund Z lo hχ1 hZ (by linarith)]
    have : (k + lo) / (1 + χ) - lo = (k - χ * lo) / (1 + χ) := by field_simp; ring
    rw [this]
    exact div_nonneg (by nlinarith) hχ1.le
  have hGhi : gapFn χ k cbar cund Z hi ≤ 0 := by
    have hhi : Z + thr χ cbar ≤ k + hi := by
      have := le_max_right (k / χ) (Z + thr χ cbar - k)
      linarith
    rw [gapFn_float χ k cbar cund Z hi hχ1 hZ hhi]
    have h1 : k / χ ≤ hi := le_max_left _ _
    have : k ≤ χ * hi := by rwa [div_le_iff₀ hχ, mul_comm] at h1
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) hχ1.le
  obtain ⟨πe, -, h⟩ := intermediate_value_Icc' hlohi
    (gapFn_continuous χ k cbar cund Z hχ1 hZ).continuousOn
    (show (0 : ℝ) ∈ Icc (gapFn χ k cbar cund Z hi) (gapFn χ k cbar cund Z lo) from
      ⟨hGhi, hGlo⟩)
  exact ⟨πe, h⟩

/-- O&R p. 651: while `z̄` is interior (`−Z < s̄ − k − πᵉ < Z`), `dz̄/dπᵉ = −1`. -/
theorem hasDerivAt_zbarC (sb k Z πe : ℝ) (h1 : -Z < sb - (k + πe)) (h2 : sb - (k + πe) < Z) :
    HasDerivAt (fun x => zbarC sb (k + x) Z) (-1) πe := by
  have hev : (fun x => sb - (k + x)) =ᶠ[nhds πe] fun x => zbarC sb (k + x) Z := by
    have : Ioo (sb - k - Z) (sb - k + Z) ∈ nhds πe := Ioo_mem_nhds (by linarith) (by linarith)
    filter_upwards [this] with x hx
    unfold zbarC
    rw [min_eq_left (by linarith [hx.1]), max_eq_left (by linarith [hx.2])]
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev.symm
  have := ((hasDerivAt_id' πe).const_add k).const_sub sb
  simpa using this

/-- O&R p. 651: while `z̲` is interior (`−Z < −s̲ − k − πᵉ < Z`), `dz̲/dπᵉ = −1`. -/
theorem hasDerivAt_zundC (su k Z πe : ℝ) (h1 : -Z < -su - (k + πe))
    (h2 : -su - (k + πe) < Z) :
    HasDerivAt (fun x => zundC su (k + x) Z) (-1) πe := by
  have hev : (fun x => -su - (k + x)) =ᶠ[nhds πe] fun x => zundC su (k + x) Z := by
    have : Ioo (-su - k - Z) (-su - k + Z) ∈ nhds πe := Ioo_mem_nhds (by linarith) (by linarith)
    filter_upwards [this] with x hx
    unfold zundC
    rw [max_eq_left (by linarith [hx.2]), min_eq_left (by linarith [hx.1])]
  refine HasDerivAt.congr_of_eventuallyEq ?_ hev.symm
  have := ((hasDerivAt_id' πe).const_add k).const_sub (-su)
  simpa using this

/-- O&R Fig. 9.12 (T25): the convex branch has a segment steeper than the 45° line (slope of
`Eπ` above `1` at its top end `k + πᵉ = Z + s̄`) iff `s̄ > 2χZ`. -/
theorem steep_iff (χ sb Z : ℝ) (hχ : 0 < 1 + χ) (hZ : 0 < Z) :
    1 < 1 / (1 + χ) * (1 / 2 + (Z + sb) / (2 * Z)) ↔ 2 * χ * Z < sb := by
  rw [show 1 / (1 + χ) * (1 / 2 + (Z + sb) / (2 * Z)) = (2 * Z + sb) / (2 * Z * (1 + χ)) by
    field_simp; ring, lt_div_iff₀ (by positivity)]
  constructor <;> intro h <;> nlinarith

/-- O&R Fig. 9.12 (T25): in the three-equilibrium configuration of `exactly_three` the convex
branch must cross the 45° line from below, which forces `s̄ > 2χZ`. -/
theorem exactly_three_needs_steep (χ k cbar cund Z πL : ℝ) (hχ : 0 < χ) (hZ : 0 < Z)
    (hcb : 0 ≤ cbar) (hcu : 0 ≤ cund) (hL1 : thr χ cbar - Z < k + πL)
    (hL2 : k + πL < Z - thr χ cund)
    (hπ1 : k + (k - (1 + χ) * ((cbar - cund) / (4 * Z))) / χ < Z - thr χ cund)
    (hfn40 : Z + thr χ cbar < k + k / χ) : 2 * χ * Z < thr χ cbar := by
  have hχ1 : 0 < 1 + χ := by linarith
  have hsb0 := thr_nonneg χ cbar
  have hsu0 := thr_nonneg χ cund
  set a := Z - thr χ cund - k
  set b := Z + thr χ cbar - k
  set π1 := (k - (1 + χ) * ((cbar - cund) / (4 * Z))) / χ
  have hab : a ≤ b := by linarith
  have hGa : gapFn χ k cbar cund Z a < 0 := by
    rw [gapFn_regimeA χ k cbar cund Z a hχ hZ hcb hcu (by linarith) (by linarith)]
    exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hχ (by linarith)) hχ1
  have hbk : b < k / χ := by linarith
  have hGb : 0 < gapFn χ k cbar cund Z b := by
    rw [gapFn_float χ k cbar cund Z b hχ1 hZ (by linarith)]
    have : χ * b < k := by rwa [lt_div_iff₀ hχ, mul_comm] at hbk
    exact div_pos (by linarith) hχ1
  have hGM : ∀ y, a ≤ y → y ≤ b → gapFn χ k cbar cund Z y =
      1 / (4 * Z * (1 + χ)) * y ^ 2 + (2 * (k + Z) / (4 * Z * (1 + χ)) - 1) * y +
        ((k + Z) ^ 2 - thr χ cbar ^ 2) / (4 * Z * (1 + χ)) := by
    intro y h1 h2
    unfold gapFn
    rw [expDep_regimeM χ k cbar cund Z y hχ1 hZ (by linarith) (by linarith) (by linarith),
      quad_M_form χ k (thr χ cbar) Z y hχ1 hZ]
  rw [hGM a le_rfl hab] at hGa
  rw [hGM b hab le_rfl] at hGb
  set α := 1 / (4 * Z * (1 + χ))
  set β := 2 * (k + Z) / (4 * Z * (1 + χ)) - 1
  have hαpos : 0 < α := by positivity
  have hdiff : 0 < (b - a) * (α * (a + b) + β) := by nlinarith
  have hba : 0 < b - a := by
    rcases hab.lt_or_eq with h | h
    · linarith
    · rw [h, sub_self, zero_mul] at hdiff
      exact absurd hdiff (lt_irrefl 0)
  have hpos : 0 < α * (a + b) + β := (mul_pos_iff_of_pos_left hba).1 hdiff
  have hslope : 0 < 2 * α * b + β := by nlinarith
  have e : 2 * α * b + β = (2 * Z + thr χ cbar) / (2 * Z * (1 + χ)) - 1 := by
    simp only [α, β, b]
    field_simp
    ring
  rw [e, sub_pos, lt_div_iff₀ (by positivity)] at hslope
  nlinarith

/-! ## Two counterexamples to readings of Fig. 9.12 and fn 40 -/

/-- The threshold in the examples: `√(3/10 · 6/5) = 3/5`. -/
theorem thr_example : thr (1 / 5) (3 / 10) = 3 / 5 := by
  unfold thr
  rw [show (3 / 10 : ℝ) * (1 + 1 / 5) = (3 / 5) ^ 2 by norm_num]
  exact Real.sqrt_sq (by norm_num)

/-- Correction to Fig. 9.12 (T25): three equilibria do **not** require `c̄ > c̲`. With
`χ = 1/5`, `Z = 1`, `k = 27/100` and `c̄ = c̲ = 3/10` (`s̄ = s̲ = 3/5`) there are three
equilibria `π₁ < π₂ < π₃ = k/χ = 27/20` on the book's domain `πᵉ ≥ −27/100`; the low ones
lie on the convex branch, not on a flat branch below the free-float line. -/
theorem three_eqm_symmetric_costs :
    ∃ x1 x2 x3 : ℝ, -27 / 100 ≤ x1 ∧ x1 < x2 ∧ x2 < x3 ∧
      gapFn (1 / 5) (27 / 100) (3 / 10) (3 / 10) 1 x1 = 0 ∧
      gapFn (1 / 5) (27 / 100) (3 / 10) (3 / 10) 1 x2 = 0 ∧
      gapFn (1 / 5) (27 / 100) (3 / 10) (3 / 10) 1 x3 = 0 := by
  have hM : ∀ x : ℝ, 13 / 100 ≤ x → x ≤ 133 / 100 →
      gapFn (1 / 5) (27 / 100) (3 / 10) (3 / 10) 1 x =
        ((27 / 100 + x + 1) ^ 2 - (3 / 5) ^ 2) / (4 * 1 * (1 + 1 / 5)) - x := by
    intro x h1 h2
    unfold gapFn
    rw [expDep_regimeM (1 / 5) (27 / 100) (3 / 10) (3 / 10) 1 x (by norm_num) (by norm_num)
      (by rw [thr_example]; linarith) (by rw [thr_example]; linarith)
      (by rw [thr_example]; linarith), thr_example]
  have hcont := (gapFn_continuous (1 / 5) (27 / 100) (3 / 10) (3 / 10) 1 (by norm_num)
    (by norm_num)).continuousOn (s := Icc (13 / 100) (11 / 10))
  have hcont2 := (gapFn_continuous (1 / 5) (27 / 100) (3 / 10) (3 / 10) 1 (by norm_num)
    (by norm_num)).continuousOn (s := Icc (11 / 10) (13 / 10))
  have g1 := hM (13 / 100) (by norm_num) (by norm_num)
  have g2 := hM (11 / 10) (by norm_num) (by norm_num)
  have g3 := hM (13 / 10) (by norm_num) (by norm_num)
  norm_num at g1 g2 g3
  obtain ⟨x1, hx1, hg1⟩ := intermediate_value_Icc' (by norm_num) hcont
    (show (0 : ℝ) ∈ Icc (gapFn (1 / 5) (27 / 100) (3 / 10) (3 / 10) 1 (11 / 10))
      (gapFn (1 / 5) (27 / 100) (3 / 10) (3 / 10) 1 (13 / 100)) by
        rw [g1, g2]; norm_num)
  obtain ⟨x2, hx2, hg2⟩ := intermediate_value_Icc (by norm_num) hcont2
    (show (0 : ℝ) ∈ Icc (gapFn (1 / 5) (27 / 100) (3 / 10) (3 / 10) 1 (11 / 10))
      (gapFn (1 / 5) (27 / 100) (3 / 10) (3 / 10) 1 (13 / 10)) by
        rw [g2, g3]; norm_num)
  have hx12 : x1 < x2 := by
    rcases (mem_Icc.1 hx1).2.lt_or_eq with h | h
    · exact lt_of_lt_of_le h (mem_Icc.1 hx2).1
    · rw [h, g2] at hg1
      norm_num at hg1
  have hG3 : gapFn (1 / 5) (27 / 100) (3 / 10) (3 / 10) 1 (27 / 20) = 0 := by
    rw [gapFn_float (1 / 5) (27 / 100) (3 / 10) (3 / 10) 1 (27 / 20) (by norm_num)
      (by norm_num) (by rw [thr_example]; norm_num)]
    norm_num
  refine ⟨x1, x2, 27 / 20, by linarith [(mem_Icc.1 hx1).1], hx12,
    by linarith [(mem_Icc.1 hx2).2], hg1, hg2, hG3⟩

/-- The threshold in the second example: `√(1/8 · 2) = 1/2`. -/
theorem thr_example2 : thr 1 (1 / 8) = 1 / 2 := by
  unfold thr
  rw [show (1 / 8 : ℝ) * (1 + 1) = (1 / 2) ^ 2 by norm_num]
  exact Real.sqrt_sq (by norm_num)

/-- Correction to fn 40 (T25): fn 40 is not necessary for `πᵉ = k/χ` to be an equilibrium.
With `χ = 1`, `Z = 1`, `k = 1/4`, `c̄ = c̲ = 1/8` (`s̄ = s̲ = 1/2`), `πᵉ = k/χ = 1/4` is an
equilibrium (in regime A, where the government sometimes pegs), although
`(1 + χ)k/χ − Z = −1/2 < s̄`. -/
theorem fn40_not_necessary :
    gapFn 1 (1 / 4) (1 / 8) (1 / 8) 1 ((1 / 4) / 1) = 0 ∧
      (1 + 1) * (1 / 4) / 1 - 1 < thr 1 (1 / 8) := by
  refine ⟨?_, by rw [thr_example2]; norm_num⟩
  unfold gapFn
  rw [symmetric_flat_is_float 1 (1 / 4) (1 / 8) 1 _ (by norm_num) (by norm_num) (by norm_num)
    (by rw [thr_example2]; norm_num) (by rw [thr_example2]; norm_num)]
  norm_num


end ObstfeldRogoff.NominalRigidities.EscapeClausePeg
