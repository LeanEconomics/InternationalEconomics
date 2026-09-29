/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import RealExchangeRate.Model
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# The CES consumption index and the consumption-based price index

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §4.3.2
(pp. 222–223, eqs. (13)–(16), footnotes 13 and 22) and §4.4.1.1 (pp. 226–228, eqs. (20)–(22),
footnotes 25–26), plus Exercise 8(a) (p. 267).

The CES index (13) is
`Ω(C_T, C_N) = [γ^{1/θ} C_T^{(θ−1)/θ} + (1−γ)^{1/θ} C_N^{(θ−1)/θ}]^{θ/(θ−1)}`
with `0 < γ < 1`, `θ > 0`, `θ ≠ 1`. With the traded good as numeraire and `p` the relative
price of nontradables, spending is `Z = C_T + p C_N` (14). We prove:

* the demand functions (16) exhaust the budget and satisfy the relative demand (15);
* the value of the index at the demands (16) is `Z/P` with
  `P = [γ + (1−γ) p^{1−θ}]^{1/(1−θ)}` (20), i.e. (21), and (22);
* **duality**: every bundle with `C_T + p C_N = Z` has `Ω ≤ Z/P` (a tangent-line argument
  based on Bernoulli's inequality, one case for each sign of `(θ−1)/θ`), so `P` is the
  minimum expenditure buying one unit of `Ω` (the definition on p. 227);
* `P` is strictly increasing in `p` and `d log P / d log p = 1 − γ` at `p = 1` (fn 26);
* the Cobb–Douglas limits as `θ → 1`: `P → p^{1−γ}` (p. 228) and
  `Ω → C_T^γ C_N^{1−γ}/(γ^γ (1−γ)^{1−γ})` (fn 22), both from the power-mean limit;
* the elasticity of substitution is `θ` (fn 22) and the Cobb–Douglas MRS (fn 13);
* Exercise 8(a): the Cobb–Douglas price index `p^γ/(γ^γ (1−γ)^{1−γ})`.

Zero consumption of a good: for `θ < 1` both goods are essential and the book's index is `0`
when either argument is `0`, but Lean's `0 ^ y = 0` (for `y ≠ 0`) gives a junk value there,
so the duality theorem requires strictly positive consumption when `θ < 1`.
-/

namespace ObstfeldRogoff.RealExchangeRate.CESIndex

open Real Filter Topology Set

/-- The CES consumption index (13), O&R p. 222:
`[γ^{1/θ} C_T^{(θ−1)/θ} + (1−γ)^{1/θ} C_N^{(θ−1)/θ}]^{θ/(θ−1)}`. -/
noncomputable def cesIndex (γ θ CT CN : ℝ) : ℝ :=
  (γ ^ (1 / θ) * CT ^ ((θ - 1) / θ) + (1 - γ) ^ (1 / θ) * CN ^ ((θ - 1) / θ)) ^ (θ / (θ - 1))

/-- The common denominator `γ + (1−γ) p^{1−θ}` of the demand functions (16), O&R p. 223. -/
noncomputable def cesDenom (γ θ p : ℝ) : ℝ := γ + (1 - γ) * p ^ (1 - θ)

/-- The consumption-based price index (20), O&R p. 227:
`P = [γ + (1−γ) p^{1−θ}]^{1/(1−θ)}`. -/
noncomputable def cesPrice (γ θ p : ℝ) : ℝ := (γ + (1 - γ) * p ^ (1 - θ)) ^ (1 / (1 - θ))

/-- Demand for tradables (16), O&R p. 223: `C_T = γZ/(γ + (1−γ)p^{1−θ})`. -/
noncomputable def cesDemandT (γ θ p Z : ℝ) : ℝ := γ * Z / cesDenom γ θ p

/-- Demand for nontradables (16), O&R p. 223: `C_N = p^{−θ}(1−γ)Z/(γ + (1−γ)p^{1−θ})`. -/
noncomputable def cesDemandN (γ θ p Z : ℝ) : ℝ := p ^ (-θ) * (1 - γ) * Z / cesDenom γ θ p

/-- The denominator of (16) is positive, O&R p. 223. -/
theorem cesDenom_pos {γ θ p : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hp : 0 < p) :
    0 < cesDenom γ θ p := by
  unfold cesDenom
  have := rpow_pos_of_pos hp (1 - θ)
  nlinarith

/-- The price index is the `1/(1−θ)` power of the denominator of (16), O&R (20), p. 227. -/
theorem cesPrice_eq_denom_rpow (γ θ p : ℝ) :
    cesPrice γ θ p = cesDenom γ θ p ^ (1 / (1 - θ)) := rfl

/-- The price index is positive, O&R (20), p. 227. -/
theorem cesPrice_pos {γ θ p : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hp : 0 < p) :
    0 < cesPrice γ θ p :=
  rpow_pos_of_pos (cesDenom_pos hγ0 hγ1 hp) _

/-- `P^{1−θ} = γ + (1−γ)p^{1−θ}`, O&R (20), p. 227. -/
theorem cesPrice_rpow_one_sub {γ θ p : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hp : 0 < p)
    (hθ1 : θ ≠ 1) : cesPrice γ θ p ^ (1 - θ) = γ + (1 - γ) * p ^ (1 - θ) := by
  have h1 : (1 - θ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hθ1)
  have hD := cesDenom_pos (θ := θ) hγ0 hγ1 hp
  unfold cesDenom at hD
  rw [cesPrice, ← rpow_mul hD.le, one_div_mul_cancel h1, rpow_one]

/-- The demands (16) exhaust spending, `C_T + p C_N = Z` (14), O&R p. 223. -/
theorem cesDemand_budget {γ θ p : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hp : 0 < p) (Z : ℝ) :
    cesDemandT γ θ p Z + p * cesDemandN γ θ p Z = Z := by
  have hD := cesDenom_pos (θ := θ) hγ0 hγ1 hp
  have hpp : p * p ^ (-θ) = p ^ (1 - θ) := by
    rw [sub_eq_add_neg, rpow_add hp, rpow_one]
  unfold cesDemandT cesDemandN
  field_simp
  unfold cesDenom
  linear_combination (1 - γ) * Z * hpp

/-- Relative demand (15), O&R p. 222: `γ C_N / ((1−γ) C_T) = p^{−θ}` at the demands (16). -/
theorem cesDemand_ratio {γ θ p Z : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hp : 0 < p) (hZ : Z ≠ 0) :
    γ * cesDemandN γ θ p Z / ((1 - γ) * cesDemandT γ θ p Z) = p ^ (-θ) := by
  have hD := (cesDenom_pos (θ := θ) hγ0 hγ1 hp).ne'
  have h1 : (1 - γ) ≠ 0 := by linarith
  unfold cesDemandT cesDemandN
  field_simp

/-- The demand (16) for tradables as `γ · (Z/D)`, O&R p. 223. -/
theorem cesDemandT_eq (γ θ p Z : ℝ) :
    cesDemandT γ θ p Z = γ * (Z / cesDenom γ θ p) := by
  unfold cesDemandT; ring

/-- The demand (16) for nontradables as `(1−γ) p^{−θ} · (Z/D)`, O&R p. 223. -/
theorem cesDemandN_eq (γ θ p Z : ℝ) :
    cesDemandN γ θ p Z = (1 - γ) * p ^ (-θ) * (Z / cesDenom γ θ p) := by
  unfold cesDemandN; ring

/-- (21), O&R p. 228: the CES index evaluated at the optimal demands (16) equals `Z/P`, with `P`
the price index (20). -/
theorem cesIndex_demand {γ θ p Z : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hθ : 0 < θ) (hθ1 : θ ≠ 1)
    (hp : 0 < p) (hZ : 0 < Z) :
    cesIndex γ θ (cesDemandT γ θ p Z) (cesDemandN γ θ p Z) = Z / cesPrice γ θ p := by
  have hD := cesDenom_pos (θ := θ) hγ0 hγ1 hp
  have hθ0 : θ ≠ 0 := hθ.ne'
  have hθm : θ - 1 ≠ 0 := sub_ne_zero.mpr hθ1
  have hθm' : 1 - θ ≠ 0 := sub_ne_zero.mpr (Ne.symm hθ1)
  have h1γ : 0 < 1 - γ := by linarith
  set D := cesDenom γ θ p with hDdef
  have hm : 0 < Z / D := div_pos hZ hD
  set m := Z / D with hmdef
  set ρ := (θ - 1) / θ with hρ
  have hT : γ ^ (1 / θ) * (γ * m) ^ ρ = γ * m ^ ρ := by
    rw [mul_rpow hγ0.le hm.le, ← mul_assoc, ← rpow_add hγ0]
    have : 1 / θ + ρ = 1 := by rw [hρ]; field_simp; ring
    rw [this, rpow_one]
  have hN : (1 - γ) ^ (1 / θ) * ((1 - γ) * p ^ (-θ) * m) ^ ρ
      = (1 - γ) * p ^ (1 - θ) * m ^ ρ := by
    rw [mul_rpow (by positivity) hm.le, mul_rpow h1γ.le (by positivity), ← rpow_mul hp.le,
      ← mul_assoc, ← mul_assoc, ← rpow_add h1γ]
    have e1 : 1 / θ + ρ = 1 := by rw [hρ]; field_simp; ring
    have e2 : -θ * ρ = 1 - θ := by rw [hρ]; field_simp; ring
    rw [e1, e2, rpow_one]
  unfold cesIndex
  rw [cesDemandT_eq, cesDemandN_eq, ← hmdef, hT, hN]
  have hsum : γ * m ^ ρ + (1 - γ) * p ^ (1 - θ) * m ^ ρ = D * m ^ ρ := by
    rw [hDdef, cesDenom]; ring
  rw [hsum, mul_rpow hD.le (by positivity), ← rpow_mul hm.le]
  have e3 : ρ * (θ / (θ - 1)) = 1 := by rw [hρ]; field_simp
  rw [e3, rpow_one, cesPrice_eq_denom_rpow, ← hDdef, div_eq_mul_inv Z, ← rpow_neg hD.le]
  have e4 : D ^ (-(1 / (1 - θ))) = D ^ (θ / (θ - 1)) / D := by
    rw [← rpow_sub_one hD.ne']
    congr 1
    field_simp
    ring
  rw [e4, hmdef]
  field_simp

/-- (22), O&R p. 228: the demands (16) written as `C_T = γ P^θ C` and
`C_N = (1−γ)(p/P)^{−θ} C` with real consumption `C = Z/P`. -/
theorem cesDemand_eq_price_form {γ θ p : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hθ1 : θ ≠ 1)
    (hp : 0 < p) (Z : ℝ) :
    cesDemandT γ θ p Z = γ * cesPrice γ θ p ^ θ * (Z / cesPrice γ θ p) ∧
    cesDemandN γ θ p Z = (1 - γ) * (p / cesPrice γ θ p) ^ (-θ) * (Z / cesPrice γ θ p) := by
  have hD := cesDenom_pos (θ := θ) hγ0 hγ1 hp
  have hP := cesPrice_pos (θ := θ) hγ0 hγ1 hp
  have hθm' : 1 - θ ≠ 0 := sub_ne_zero.mpr (Ne.symm hθ1)
  have key : cesPrice γ θ p ^ θ / cesPrice γ θ p = (cesDenom γ θ p)⁻¹ := by
    rw [← rpow_sub_one hP.ne', cesPrice_eq_denom_rpow, ← rpow_mul hD.le, ← rpow_neg_one]
    congr 1
    field_simp
    ring
  constructor
  · rw [cesDemandT_eq]
    calc γ * (Z / cesDenom γ θ p) = γ * (cesPrice γ θ p ^ θ / cesPrice γ θ p) * Z := by
          rw [key]; ring
      _ = _ := by ring
  · rw [cesDemandN_eq, div_rpow hp.le hP.le, rpow_neg hP.le, div_inv_eq_mul]
    calc (1 - γ) * p ^ (-θ) * (Z / cesDenom γ θ p)
        = (1 - γ) * p ^ (-θ) * (cesPrice γ θ p ^ θ / cesPrice γ θ p) * Z := by
          rw [key]; ring
      _ = _ := by ring

/-- Tangent-line (Bernoulli) bound for a concave power, used for the duality in §4.4.1.1
(O&R p. 227): for `0 ≤ ρ ≤ 1`, `x ≥ 0`, `a > 0`, `x^ρ ≤ a^ρ + ρ a^{ρ−1}(x − a)`. -/
theorem ces_rpow_le_tangent {ρ x a : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hx : 0 ≤ x) (ha : 0 < a) :
    x ^ ρ ≤ a ^ ρ + ρ * a ^ (ρ - 1) * (x - a) := by
  have hs : -1 ≤ x / a - 1 := by have := div_nonneg hx ha.le; linarith
  have hb := rpow_one_add_le_one_add_mul_self hs hρ0 hρ1
  rw [add_sub_cancel, div_rpow hx ha.le] at hb
  have haρ := rpow_pos_of_pos ha ρ
  rw [div_le_iff₀ haρ] at hb
  rw [rpow_sub_one ha.ne']
  calc x ^ ρ ≤ (1 + ρ * (x / a - 1)) * a ^ ρ := hb
    _ = a ^ ρ + ρ * (a ^ ρ / a) * (x - a) := by field_simp

/-- Tangent-line (Bernoulli) bound for a convex negative power, used for the duality in §4.4.1.1
(O&R p. 227): for `ρ ≤ 0`, `x, a > 0`, `a^ρ + ρ a^{ρ−1}(x − a) ≤ x^ρ`. -/
theorem ces_tangent_le_rpow {ρ x a : ℝ} (hρ : ρ ≤ 0) (hx : 0 < x) (ha : 0 < a) :
    a ^ ρ + ρ * a ^ (ρ - 1) * (x - a) ≤ x ^ ρ := by
  set y := x / a with hy
  have hy0 : 0 < y := div_pos hx ha
  have hs : -1 ≤ 1 / y - 1 := by have := one_div_pos.mpr hy0; linarith
  have hb := one_add_mul_self_le_rpow_one_add hs (p := 1 - ρ) (by linarith)
  rw [add_sub_cancel, one_div, inv_rpow hy0.le, ← rpow_neg hy0.le, neg_sub] at hb
  -- hb : 1 + (1 - ρ) * (1 / y - 1) ≤ y ^ (ρ - 1)
  have hyρ : y ^ ρ = y * y ^ (ρ - 1) := by
    rw [rpow_sub_one hy0.ne']; field_simp
  have h1 : 1 + ρ * (y - 1) ≤ y ^ ρ := by
    rw [hyρ]
    have := mul_le_mul_of_nonneg_left hb hy0.le
    calc 1 + ρ * (y - 1) = y * (1 + (1 - ρ) * (y⁻¹ - 1)) := by field_simp; ring
      _ ≤ _ := this
  have haρ := rpow_pos_of_pos ha ρ
  have hxy : x ^ ρ = y ^ ρ * a ^ ρ := by
    rw [hy, div_rpow hx.le ha.le]; field_simp
  rw [hxy, rpow_sub_one ha.ne']
  calc a ^ ρ + ρ * (a ^ ρ / a) * (x - a) = (1 + ρ * (y - 1)) * a ^ ρ := by
        rw [hy]; field_simp
    _ ≤ y ^ ρ * a ^ ρ := mul_le_mul_of_nonneg_right h1 haρ.le

/-- First-order conditions behind (15)–(16), O&R p. 222: at the demands (16) the marginal
contributions `γ^{1/θ} C_T^{−1/θ}` and `(1−γ)^{1/θ} C_N^{−1/θ}` to the inner CES sum are in the
price ratio `1 : p` (both equal to `(Z/D)^{−1/θ}` times `1`, resp. `p`). -/
theorem cesDemand_foc {γ θ p Z : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hθ : 0 < θ)
    (hp : 0 < p) (hZ : 0 < Z) :
    γ ^ (1 / θ) * cesDemandT γ θ p Z ^ ((θ - 1) / θ - 1)
      = (Z / cesDenom γ θ p) ^ ((θ - 1) / θ - 1) ∧
    (1 - γ) ^ (1 / θ) * cesDemandN γ θ p Z ^ ((θ - 1) / θ - 1)
      = p * (Z / cesDenom γ θ p) ^ ((θ - 1) / θ - 1) := by
  have hD := cesDenom_pos (θ := θ) hγ0 hγ1 hp
  have hm : 0 < Z / cesDenom γ θ p := div_pos hZ hD
  have h1γ : 0 < 1 - γ := by linarith
  have e1 : 1 / θ + ((θ - 1) / θ - 1) = 0 := by field_simp; ring
  have e2 : -θ * ((θ - 1) / θ - 1) = 1 := by field_simp; ring
  constructor
  · rw [cesDemandT_eq, mul_rpow hγ0.le hm.le, ← mul_assoc, ← rpow_add hγ0, e1, rpow_zero,
      one_mul]
  · rw [cesDemandN_eq, mul_rpow (by positivity) hm.le, mul_rpow h1γ.le (by positivity),
      ← rpow_mul hp.le, ← mul_assoc, ← mul_assoc, ← rpow_add h1γ, e1, e2, rpow_zero, rpow_one,
      one_mul]

/-- **Duality (T13)**, O&R §4.4.1.1, pp. 227–228: every bundle `C_T, C_N ≥ 0` costing
`Z = C_T + p C_N > 0` yields at most `Z/P` units of the CES index (13), `P` the price index
(20); equality holds at the demands (16) (`cesIndex_demand`). For `θ < 1` both goods must be
consumed in strictly positive amounts (otherwise Lean's `0 ^ y = 0` is a junk value, see the
module docstring). Proof: tangent-line bounds for `x ↦ x^{(θ−1)/θ}` at the optimum, whose
gradient is proportional to prices (`cesDemand_foc`). -/
theorem cesIndex_le_div_price {γ θ p CT CN : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hθ : 0 < θ)
    (hθ1 : θ ≠ 1) (hp : 0 < p) (hCT : 0 ≤ CT) (hCN : 0 ≤ CN)
    (hint : θ < 1 → 0 < CT ∧ 0 < CN) (hZ : 0 < CT + p * CN) :
    cesIndex γ θ CT CN ≤ (CT + p * CN) / cesPrice γ θ p := by
  set Z := CT + p * CN with hZdef
  have hD := cesDenom_pos (θ := θ) hγ0 hγ1 hp
  have hm : 0 < Z / cesDenom γ θ p := div_pos hZ hD
  have h1γ : 0 < 1 - γ := by linarith
  set xT := cesDemandT γ θ p Z with hxT
  set xN := cesDemandN γ θ p Z with hxN
  have hxT0 : 0 < xT := by rw [hxT, cesDemandT_eq]; positivity
  have hxN0 : 0 < xN := by rw [hxN, cesDemandN_eq]; exact mul_pos (by positivity) hm
  have hbud : xT + p * xN = Z := cesDemand_budget hγ0 hγ1 hp Z
  obtain ⟨hgT, hgN⟩ := cesDemand_foc (θ := θ) hγ0 hγ1 hθ hp hZ
  rw [← hxT] at hgT
  rw [← hxN] at hgN
  set ρ := (θ - 1) / θ with hρ
  set g := (Z / cesDenom γ θ p) ^ (ρ - 1) with hg
  have hval := cesIndex_demand hγ0 hγ1 hθ hθ1 hp hZ
  rw [← hxT, ← hxN] at hval
  unfold cesIndex at hval ⊢
  rw [← hρ] at hval ⊢
  rw [← hval]
  have ha := rpow_pos_of_pos hγ0 (1 / θ)
  have hb := rpow_pos_of_pos h1γ (1 / θ)
  set Astar := γ ^ (1 / θ) * xT ^ ρ + (1 - γ) ^ (1 / θ) * xN ^ ρ with hAstar
  set A := γ ^ (1 / θ) * CT ^ ρ + (1 - γ) ^ (1 / θ) * CN ^ ρ with hA
  have hlin : γ ^ (1 / θ) * (xT ^ ρ + ρ * xT ^ (ρ - 1) * (CT - xT))
      + (1 - γ) ^ (1 / θ) * (xN ^ ρ + ρ * xN ^ (ρ - 1) * (CN - xN)) = Astar := by
    have : γ ^ (1 / θ) * (xT ^ ρ + ρ * xT ^ (ρ - 1) * (CT - xT))
        + (1 - γ) ^ (1 / θ) * (xN ^ ρ + ρ * xN ^ (ρ - 1) * (CN - xN))
        = Astar + ρ * g * ((CT + p * CN) - (xT + p * xN)) := by
      rw [hAstar]
      linear_combination (ρ * (CT - xT)) * hgT + (ρ * (CN - xN)) * hgN
    rw [this, hbud, hZdef, sub_self, mul_zero, add_zero]
  rcases lt_or_gt_of_ne hθ1 with hlt | hgt
  · -- θ < 1: the power `ρ` is negative and the outer exponent is negative
    obtain ⟨hCT', hCN'⟩ := hint hlt
    have hρneg : ρ ≤ 0 := by rw [hρ]; exact div_nonpos_of_nonpos_of_nonneg (by linarith) hθ.le
    have t1 := ces_tangent_le_rpow hρneg hCT' hxT0
    have t2 := ces_tangent_le_rpow hρneg hCN' hxN0
    have key : Astar ≤ A := by
      rw [← hlin, hA]
      exact add_le_add (mul_le_mul_of_nonneg_left t1 ha.le) (mul_le_mul_of_nonneg_left t2 hb.le)
    have hApos : 0 < Astar := by rw [hAstar]; positivity
    exact rpow_le_rpow_of_nonpos hApos key
      (div_nonpos_of_nonneg_of_nonpos hθ.le (by linarith))
  · -- θ > 1: the power `ρ` lies in `(0, 1)` and the outer exponent is positive
    have hρ0 : 0 ≤ ρ := by rw [hρ]; exact div_nonneg (by linarith) hθ.le
    have hρ1 : ρ ≤ 1 := by rw [hρ, div_le_one hθ]; linarith
    have t1 := ces_rpow_le_tangent hρ0 hρ1 hCT hxT0
    have t2 := ces_rpow_le_tangent hρ0 hρ1 hCN hxN0
    have key : A ≤ Astar := by
      rw [← hlin, hA]
      exact add_le_add (mul_le_mul_of_nonneg_left t1 ha.le) (mul_le_mul_of_nonneg_left t2 hb.le)
    have hA0 : 0 ≤ A := by rw [hA]; positivity
    exact rpow_le_rpow hA0 key (div_nonneg hθ.le (by linarith))

/-- The price index is the minimum cost of one unit of real consumption, the definition of
O&R p. 227: any interior bundle with `Ω(C_T, C_N) = 1` costs at least `P`, and the demands (16)
at spending `Z = P` deliver `Ω = 1` at cost exactly `P`. -/
theorem cesPrice_isLeast_cost {γ θ p : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hθ : 0 < θ)
    (hθ1 : θ ≠ 1) (hp : 0 < p) :
    (∀ CT CN : ℝ, 0 < CT → 0 < CN → cesIndex γ θ CT CN = 1 → cesPrice γ θ p ≤ CT + p * CN) ∧
    cesIndex γ θ (cesDemandT γ θ p (cesPrice γ θ p)) (cesDemandN γ θ p (cesPrice γ θ p)) = 1 ∧
    cesDemandT γ θ p (cesPrice γ θ p) + p * cesDemandN γ θ p (cesPrice γ θ p)
      = cesPrice γ θ p := by
  have hP := cesPrice_pos (θ := θ) hγ0 hγ1 hp
  refine ⟨fun CT CN hCT hCN h1 => ?_, ?_, cesDemand_budget hγ0 hγ1 hp _⟩
  · have hZ : 0 < CT + p * CN := by positivity
    have := cesIndex_le_div_price hγ0 hγ1 hθ hθ1 hp hCT.le hCN.le (fun _ => ⟨hCT, hCN⟩) hZ
    rw [h1, le_div_iff₀ hP, one_mul] at this
    exact this
  · rw [cesIndex_demand hγ0 hγ1 hθ hθ1 hp hP, div_self hP.ne']

/-- "Of course, `P` is an increasing function of `p`", O&R p. 227: the CES price index (20) is
strictly increasing in the relative price of nontradables on `p > 0`, for every `θ ≠ 1`. -/
theorem cesPrice_strictMonoOn {γ θ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hθ1 : θ ≠ 1) :
    StrictMonoOn (cesPrice γ θ) (Ioi 0) := by
  intro a ha b hb hab
  simp only [mem_Ioi] at ha hb
  have h1γ : 0 < 1 - γ := by linarith
  rw [cesPrice_eq_denom_rpow, cesPrice_eq_denom_rpow]
  have hDa := cesDenom_pos (θ := θ) hγ0 hγ1 ha
  have hDb := cesDenom_pos (θ := θ) hγ0 hγ1 hb
  rcases lt_or_gt_of_ne hθ1 with hlt | hgt
  · have hpow : a ^ (1 - θ) < b ^ (1 - θ) := rpow_lt_rpow ha.le hab (by linarith)
    have hD : cesDenom γ θ a < cesDenom γ θ b := by
      unfold cesDenom; nlinarith
    exact rpow_lt_rpow hDa.le hD (by apply one_div_pos.mpr; linarith)
  · have hpow : b ^ (1 - θ) < a ^ (1 - θ) := rpow_lt_rpow_of_neg ha hab (by linarith)
    have hD : cesDenom γ θ b < cesDenom γ θ a := by
      unfold cesDenom; nlinarith
    exact rpow_lt_rpow_of_neg hDb hD (by apply one_div_neg.mpr; linarith)

/-- Footnote 26, O&R p. 228: starting from `p = 1`, (20) implies `P̂ = (1−γ) p̂` for every
`θ ≠ 1`, stated exactly as `d log P / dp = 1 − γ` at `p = 1` (where `p̂ = dp/p = dp`). -/
theorem cesPrice_logDeriv_at_one {γ θ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hθ1 : θ ≠ 1) :
    HasDerivAt (fun p => Real.log (cesPrice γ θ p)) (1 - γ) 1 := by
  have hθm' : 1 - θ ≠ 0 := sub_ne_zero.mpr (Ne.symm hθ1)
  have hin : HasDerivAt (fun p : ℝ => γ + (1 - γ) * p ^ (1 - θ))
      ((1 - γ) * ((1 - θ) * (1 : ℝ) ^ (1 - θ - 1))) 1 :=
    ((hasDerivAt_rpow_const (Or.inl one_ne_zero)).const_mul (1 - γ)).const_add γ
  have hlog := (hin.log (by simp)).const_mul (1 / (1 - θ))
  have hev : (fun p => Real.log (cesPrice γ θ p))
      =ᶠ[𝓝 1] fun p => 1 / (1 - θ) * Real.log (γ + (1 - γ) * p ^ (1 - θ)) := by
    filter_upwards [Ioi_mem_nhds one_pos] with p hp
    have hD := cesDenom_pos (θ := θ) hγ0 hγ1 hp
    unfold cesDenom at hD
    rw [cesPrice, Real.log_rpow hD]
  refine (hlog.congr_of_eventuallyEq hev).congr_deriv ?_
  simp only [one_rpow, mul_one]
  field_simp
  ring

/-- Power-mean limit behind footnotes 22 and 26, O&R pp. 222–228: for weights `w, 1 − w > 0` and
`a, b > 0`, `(w a^ρ + (1−w) b^ρ)^{1/ρ} → a^w b^{1−w}` as `ρ → 0`. -/
theorem ces_powerMean_tendsto {w a b : ℝ} (hw0 : 0 < w) (hw1 : w < 1) (ha : 0 < a)
    (hb : 0 < b) :
    Tendsto (fun ρ : ℝ => (w * a ^ ρ + (1 - w) * b ^ ρ) ^ (1 / ρ)) (𝓝[≠] 0)
      (𝓝 (a ^ w * b ^ (1 - w))) := by
  have h1w : 0 < 1 - w := by linarith
  set f : ℝ → ℝ := fun ρ => Real.log (w * a ^ ρ + (1 - w) * b ^ ρ) with hf
  have hin : HasDerivAt (fun ρ : ℝ => w * a ^ ρ + (1 - w) * b ^ ρ)
      (w * (a ^ (0 : ℝ) * Real.log a) + (1 - w) * (b ^ (0 : ℝ) * Real.log b)) 0 :=
    ((hasStrictDerivAt_const_rpow ha 0).hasDerivAt.const_mul w).add
      ((hasStrictDerivAt_const_rpow hb 0).hasDerivAt.const_mul (1 - w))
  have hder := hin.log (by simp)
  simp only [rpow_zero, one_mul, mul_one, add_sub_cancel, div_one] at hder
  have hslope := (Real.continuous_exp.tendsto _).comp (hasDerivAt_iff_tendsto_slope.mp hder)
  have hlim : Real.exp (w * Real.log a + (1 - w) * Real.log b) = a ^ w * b ^ (1 - w) := by
    rw [rpow_def_of_pos ha, rpow_def_of_pos hb, ← Real.exp_add]; ring_nf
  rw [hlim] at hslope
  refine hslope.congr' ?_
  filter_upwards with ρ
  have hpos : 0 < w * a ^ ρ + (1 - w) * b ^ ρ := by positivity
  rw [Function.comp_apply, slope_def_field, rpow_def_of_pos hpos]
  simp only [rpow_zero, mul_one, add_sub_cancel, Real.log_one, sub_zero]
  ring_nf

/-- `θ ↦ 1 − θ` maps a punctured neighbourhood of `1` into one of `0` (for the `θ → 1` limit of
the price index (20), O&R p. 228). -/
theorem ces_tendsto_one_sub_punctured :
    Tendsto (fun θ : ℝ => 1 - θ) (𝓝[≠] 1) (𝓝[≠] 0) := by
  refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
  · have : Tendsto (fun θ : ℝ => 1 - θ) (𝓝 1) (𝓝 (1 - 1)) :=
      tendsto_const_nhds.sub tendsto_id
    rw [sub_self] at this
    exact tendsto_nhdsWithin_of_tendsto_nhds this
  · filter_upwards [self_mem_nhdsWithin] with θ hθ
    exact sub_ne_zero.mpr (Ne.symm hθ)

/-- Cobb–Douglas limit of the price index, O&R p. 228 (and fn 26): as `θ → 1`,
`P = [γ + (1−γ)p^{1−θ}]^{1/(1−θ)} → p^{1−γ}`. -/
theorem cesPrice_tendsto_cobbDouglas {γ p : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hp : 0 < p) :
    Tendsto (fun θ => cesPrice γ θ p) (𝓝[≠] 1) (𝓝 (p ^ (1 - γ))) := by
  have h := (ces_powerMean_tendsto hγ0 hγ1 one_pos hp).comp ces_tendsto_one_sub_punctured
  rw [one_rpow, one_mul] at h
  refine h.congr' ?_
  filter_upwards with θ
  simp [cesPrice]

/-- The Cobb–Douglas limit of (20) is the `CobbDouglasIndex` price of `RealExchangeRate.Model`
with the traded good as numeraire, which justifies the Cobb–Douglas index used in §4.2.3
(O&R p. 228). -/
theorem cesPrice_tendsto_model (c : CobbDouglasIndex) {p : ℝ} (hp : 0 < p) :
    Tendsto (fun θ => cesPrice c.γ θ p) (𝓝[≠] 1) (𝓝 (c.price 1 p)) := by
  rw [CobbDouglasIndex.price_numeraire]
  exact cesPrice_tendsto_cobbDouglas c.γ_pos c.γ_lt_one hp

/-- Footnote 22, O&R pp. 222–223: as `θ → 1` the CES index (13) converges to the Cobb–Douglas
function `C_T^γ C_N^{1−γ} / (γ^γ (1−γ)^{1−γ})` (for `C_T, C_N > 0`). -/
theorem cesIndex_tendsto_cobbDouglas {γ CT CN : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hCT : 0 < CT)
    (hCN : 0 < CN) :
    Tendsto (fun θ => cesIndex γ θ CT CN) (𝓝[≠] 1)
      (𝓝 (CT ^ γ * CN ^ (1 - γ) / (γ ^ γ * (1 - γ) ^ (1 - γ)))) := by
  have h1γ : 0 < 1 - γ := by linarith
  have hρ : Tendsto (fun θ : ℝ => (θ - 1) / θ) (𝓝[≠] 1) (𝓝[≠] 0) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have : Tendsto (fun θ : ℝ => (θ - 1) / θ) (𝓝 1) (𝓝 ((1 - 1) / 1)) :=
        (tendsto_id.sub tendsto_const_nhds).div tendsto_id one_ne_zero
      rw [sub_self, zero_div] at this
      exact tendsto_nhdsWithin_of_tendsto_nhds this
    · filter_upwards [self_mem_nhdsWithin,
        nhdsWithin_le_nhds (Ioi_mem_nhds (zero_lt_one' ℝ))] with θ hθ hθ0
      exact div_ne_zero (sub_ne_zero.mpr hθ) (ne_of_gt hθ0)
  have h := (ces_powerMean_tendsto hγ0 hγ1 (div_pos hCT hγ0) (div_pos hCN h1γ)).comp hρ
  have hval : (CT / γ) ^ γ * (CN / (1 - γ)) ^ (1 - γ)
      = CT ^ γ * CN ^ (1 - γ) / (γ ^ γ * (1 - γ) ^ (1 - γ)) := by
    rw [div_rpow hCT.le hγ0.le, div_rpow hCN.le h1γ.le]; field_simp
  rw [hval] at h
  refine h.congr' ?_
  filter_upwards [nhdsWithin_le_nhds (Ioi_mem_nhds (zero_lt_one' ℝ))] with θ hθ0
  have hθ0' : θ ≠ 0 := ne_of_gt hθ0
  simp only [Function.comp_apply, cesIndex]
  have e1 : 1 / θ = 1 - (θ - 1) / θ := by field_simp; ring
  have eT : γ * (CT / γ) ^ ((θ - 1) / θ) = γ ^ (1 / θ) * CT ^ ((θ - 1) / θ) := by
    rw [e1, rpow_sub hγ0, rpow_one, div_rpow hCT.le hγ0.le]
    have := rpow_pos_of_pos hγ0 ((θ - 1) / θ)
    field_simp
  have eN : (1 - γ) * (CN / (1 - γ)) ^ ((θ - 1) / θ)
      = (1 - γ) ^ (1 / θ) * CN ^ ((θ - 1) / θ) := by
    rw [e1, rpow_sub h1γ, rpow_one, div_rpow hCN.le h1γ.le]
    have := rpow_pos_of_pos h1γ ((θ - 1) / θ)
    field_simp
  rw [eT, eN, one_div_div]

/-- Footnote 22, O&R p. 222: `θ` is the elasticity of substitution,
`d log(C_T/C_N) / d log p = θ`, along the demands (16) (for any spending level `Z ≠ 0`), stated
exactly with `p = e^x`. -/
theorem cesDemand_elasticity {γ θ Z : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hZ : Z ≠ 0) (x : ℝ) :
    HasDerivAt
      (fun x => Real.log (cesDemandT γ θ (Real.exp x) Z / cesDemandN γ θ (Real.exp x) Z)) θ x := by
  have h1γ : 0 < 1 - γ := by linarith
  have hfun : (fun x => Real.log (cesDemandT γ θ (Real.exp x) Z / cesDemandN γ θ (Real.exp x) Z))
      = fun x => Real.log γ - Real.log (1 - γ) + θ * x := by
    funext x
    have hD := (cesDenom_pos (θ := θ) hγ0 hγ1 (Real.exp_pos x)).ne'
    have hq := rpow_pos_of_pos (Real.exp_pos x) (-θ)
    have hratio : cesDemandT γ θ (Real.exp x) Z / cesDemandN γ θ (Real.exp x) Z
        = γ / ((1 - γ) * Real.exp x ^ (-θ)) := by
      unfold cesDemandT cesDemandN
      field_simp
    rw [hratio, Real.log_div hγ0.ne' (by positivity), Real.log_mul h1γ.ne' hq.ne',
      Real.log_rpow (Real.exp_pos x), Real.log_exp]
    ring
  rw [hfun]
  have := ((hasDerivAt_id x).const_mul θ).const_add (Real.log γ - Real.log (1 - γ))
  simpa using this

/-- Footnote 13, O&R p. 217: with `u(C_T, C_N) = G(C_T^γ C_N^{1−γ})`, `G` differentiable with
`G' ≠ 0`, the marginal rate of substitution is `(∂u/∂C_N)/(∂u/∂C_T) = ((1−γ)/γ)(C_T/C_N)`,
which depends only on the consumption ratio (homotheticity). -/
theorem cobbDouglas_mrs {γ CT CN g : ℝ} {G : ℝ → ℝ} (hCT : 0 < CT) (hCN : 0 < CN)
    (hG : HasDerivAt G g (CT ^ γ * CN ^ (1 - γ))) (hg : g ≠ 0) (hγ : γ ≠ 0) :
    ∃ uN uT : ℝ, HasDerivAt (fun c => G (CT ^ γ * c ^ (1 - γ))) uN CN ∧
      HasDerivAt (fun c => G (c ^ γ * CN ^ (1 - γ))) uT CT ∧
      uN / uT = (1 - γ) / γ * (CT / CN) := by
  have hN : HasDerivAt (fun c : ℝ => CT ^ γ * c ^ (1 - γ))
      (CT ^ γ * ((1 - γ) * CN ^ (1 - γ - 1))) CN :=
    (hasDerivAt_rpow_const (Or.inl hCN.ne')).const_mul _
  have hT : HasDerivAt (fun c : ℝ => c ^ γ * CN ^ (1 - γ))
      (γ * CT ^ (γ - 1) * CN ^ (1 - γ)) CT :=
    (hasDerivAt_rpow_const (Or.inl hCT.ne')).mul_const _
  refine ⟨_, _, hG.comp CN hN, hG.comp CT hT, ?_⟩
  rw [rpow_sub_one hCN.ne', rpow_sub_one hCT.ne']
  have := rpow_pos_of_pos hCT γ
  have := rpow_pos_of_pos hCN (1 - γ)
  field_simp

/-- Exercise 8(a), O&R p. 267: with `C = X^γ M^{1−γ}`, `X` the export good priced at `p` in
terms of imports, the consumption-based price index in import units is
`P = p^γ / (γ^γ (1−γ)^{1−γ})`: every bundle with `C = 1` costs at least `P`, and
`X = γP/p`, `M = (1−γ)P` gives `C = 1` at cost exactly `P`. (The exponent `γ` sits on the
export price because the export good carries the weight `γ`.) -/
theorem cobbDouglas_price_exercise8a {γ p : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hp : 0 < p) :
    (∀ X M : ℝ, 0 < X → 0 < M → X ^ γ * M ^ (1 - γ) = 1 →
      p ^ γ / (γ ^ γ * (1 - γ) ^ (1 - γ)) ≤ p * X + M) ∧
    (γ * (p ^ γ / (γ ^ γ * (1 - γ) ^ (1 - γ))) / p) ^ γ
        * ((1 - γ) * (p ^ γ / (γ ^ γ * (1 - γ) ^ (1 - γ)))) ^ (1 - γ) = 1 ∧
    p * (γ * (p ^ γ / (γ ^ γ * (1 - γ) ^ (1 - γ))) / p)
        + (1 - γ) * (p ^ γ / (γ ^ γ * (1 - γ) ^ (1 - γ)))
      = p ^ γ / (γ ^ γ * (1 - γ) ^ (1 - γ)) := by
  have h1γ : 0 < 1 - γ := by linarith
  have hgγ := rpow_pos_of_pos hγ0 γ
  have hg1 := rpow_pos_of_pos h1γ (1 - γ)
  have hpγ := rpow_pos_of_pos hp γ
  refine ⟨fun X M hX hM hC => ?_, ?_, by field_simp; ring⟩
  · have ham := geom_mean_le_arith_mean2_weighted hγ0.le h1γ.le
      (div_pos (mul_pos hp hX) hγ0).le (div_pos hM h1γ).le (by ring : γ + (1 - γ) = 1)
    rw [div_rpow (mul_pos hp hX).le hγ0.le, mul_rpow hp.le hX.le,
      div_rpow hM.le h1γ.le] at ham
    have e : p ^ γ * X ^ γ / γ ^ γ * (M ^ (1 - γ) / (1 - γ) ^ (1 - γ))
        = p ^ γ / (γ ^ γ * (1 - γ) ^ (1 - γ)) * (X ^ γ * M ^ (1 - γ)) := by
      field_simp
    rw [e, hC, mul_one] at ham
    calc _ ≤ γ * (p * X / γ) + (1 - γ) * (M / (1 - γ)) := ham
      _ = p * X + M := by field_simp
  · set P := p ^ γ / (γ ^ γ * (1 - γ) ^ (1 - γ)) with hP
    have hP0 : 0 < P := by positivity
    rw [mul_div_right_comm, mul_rpow (div_pos hγ0 hp).le hP0.le, mul_rpow h1γ.le hP0.le,
      div_rpow hγ0.le hp.le]
    have e : γ ^ γ / p ^ γ * P ^ γ * ((1 - γ) ^ (1 - γ) * P ^ (1 - γ))
        = γ ^ γ * (1 - γ) ^ (1 - γ) / p ^ γ * (P ^ γ * P ^ (1 - γ)) := by ring
    rw [e, ← rpow_add hP0, add_sub_cancel, rpow_one, hP]
    field_simp

end ObstfeldRogoff.RealExchangeRate.CESIndex
