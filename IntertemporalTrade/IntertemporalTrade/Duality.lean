/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.MeanInequalities
import Mathlib.Tactic.FieldSimp

/-!
# Real interest rates and consumption in detail: the dual approach

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §1.3.4
"Real Interest Rates and Consumption in Detail", pp. 39–42. Prices are measured by the market
discount factor `R = 1/(1+r)`, the price of date-2 consumption in date-1 units.

* `ExpenditureSystem` packages a lifetime utility `V(C₁, C₂)` (not assumed additive), an
  expenditure function `E(R, U)` and Hicksian demands, through the minimisation property only.
* Shephard's lemma (1.27) is proved from the minimisation property by the envelope (local
  minimum) argument of footnote 18; the welfare effect (1.28), the Slutsky equation (1.30) and
  the total-effect decomposition (1.31) follow by the chain rule from the budget identity and
  the duality identity (1.29).
* §1.3.4.4 (p. 42): for isoelastic additive utility we construct the expenditure system
  explicitly (proving the Hicksian bundle really is cost-minimising), verify Shephard's lemma,
  the duality identity and the Slutsky equation in closed form, and show the p. 42 formula for
  `dC₁/dR` is equivalent to (1.24) of p. 29.
-/

namespace ObstfeldRogoff.IntertemporalTrade.Duality

open Filter Topology

/-- The dual description of the two-period consumer, O&R §1.3.4.1, p. 39. `V C₁ C₂` is lifetime
utility (any function, additivity is not assumed), `Uset` the attainable utility levels,
`E R U` the expenditure function and `C1H`, `C2H` the Hicksian demands. The fields say exactly
that the Hicksian bundle is positive, attains `U`, costs `E R U`, and that no positive bundle
attaining `U` costs less: `E R U = min {C₁ + R C₂ : V C₁ C₂ ≥ U}` for every price `R > 0`. -/
structure ExpenditureSystem where
  V : ℝ → ℝ → ℝ
  Uset : Set ℝ
  E : ℝ → ℝ → ℝ
  C1H : ℝ → ℝ → ℝ
  C2H : ℝ → ℝ → ℝ
  le_cost : ∀ R U C1 C2, 0 < R → U ∈ Uset → 0 < C1 → 0 < C2 → U ≤ V C1 C2 →
    E R U ≤ C1 + R * C2
  C1H_pos : ∀ R U, 0 < R → U ∈ Uset → 0 < C1H R U
  C2H_pos : ∀ R U, 0 < R → U ∈ Uset → 0 < C2H R U
  attains : ∀ R U, 0 < R → U ∈ Uset → U ≤ V (C1H R U) (C2H R U)
  cost_eq : ∀ R U, 0 < R → U ∈ Uset → E R U = C1H R U + R * C2H R U

/-- Chain rule along a path, the calculus behind O&R (1.28) and (1.30)–(1.31), pp. 40–41: if
`F` has partial derivatives `a`, `b` (jointly, i.e. Fréchet) at `(x, g x)` and `g` has
derivative `g'`, then `t ↦ F (t, g t)` has derivative `a + b g'`. -/
theorem hasDerivAt_along_path {F : ℝ × ℝ → ℝ} {g : ℝ → ℝ} {a b g' x : ℝ}
    (hF : HasFDerivAt F (a • ContinuousLinearMap.fst ℝ ℝ ℝ + b • ContinuousLinearMap.snd ℝ ℝ ℝ)
      (x, g x))
    (hg : HasDerivAt g g' x) :
    HasDerivAt (fun t => F (t, g t)) (a + b * g') x := by
  have hp : HasDerivAt (fun t => (t, g t)) ((1 : ℝ), g') x := (hasDerivAt_id x).prodMk hg
  have h := hF.comp_hasDerivAt x hp
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul, mul_one] at h
  exact h

namespace ExpenditureSystem

/-- Envelope inequality of O&R fn. 18, p. 39: the Hicksian bundle chosen at price `R` still
attains `U` at any other price `R' > 0`, so `E(R', U) ≤ C₁ᴴ(R, U) + R' C₂ᴴ(R, U)`, with
equality at `R' = R`. -/
theorem E_le_hicksian_cost (s : ExpenditureSystem) {R R' U : ℝ} (hR : 0 < R) (hR' : 0 < R')
    (hU : U ∈ s.Uset) : s.E R' U ≤ s.C1H R U + R' * s.C2H R U :=
  s.le_cost R' U _ _ hR' hU (s.C1H_pos R U hR hU) (s.C2H_pos R U hR hU) (s.attains R U hR hU)

/-- Shephard's lemma, O&R (1.27), p. 39: if the expenditure function is differentiable in `R`,
its derivative is the Hicksian demand for date-2 consumption, `E_R(R, U) = C₂ᴴ(R, U)`.
Proof as in fn. 18 (an envelope theorem): `R' ↦ C₁ᴴ(R,U) + R' C₂ᴴ(R,U) − E(R', U)` is
nonnegative near `R` and zero at `R`, so it has a local minimum there. -/
theorem shephard (s : ExpenditureSystem) {R U e : ℝ} (hR : 0 < R) (hU : U ∈ s.Uset)
    (hE : HasDerivAt (fun R' => s.E R' U) e R) : e = s.C2H R U := by
  have hmin : IsLocalMin (fun R' => s.C1H R U + R' * s.C2H R U - s.E R' U) R := by
    filter_upwards [Ioi_mem_nhds hR] with R' hR'
    have h1 := s.E_le_hicksian_cost hR hR' hU
    have h2 := s.cost_eq R U hR hU
    linarith
  have hd : HasDerivAt (fun R' => s.C1H R U + R' * s.C2H R U - s.E R' U)
      (s.C2H R U - e) R := by
    have := (((hasDerivAt_id R).mul_const (s.C2H R U)).const_add (s.C1H R U)).sub hE
    rw [one_mul] at this
    exact this
  have := hmin.hasDerivAt_eq_zero hd
  linarith

/-- O&R p. 39, after (1.27): Shephard's lemma and the budget identity give the Hicksian demand
for date-1 consumption, `C₁ᴴ(R, U) = E(R, U) − R E_R(R, U)`. -/
theorem C1H_eq_E_sub (s : ExpenditureSystem) {R U e : ℝ} (hR : 0 < R) (hU : U ∈ s.Uset)
    (hE : HasDerivAt (fun R' => s.E R' U) e R) : s.C1H R U = s.E R U - R * e := by
  rw [s.shephard hR hU hE, s.cost_eq R U hR hU]
  ring

/-- O&R fn. 18, p. 39: differentiating `C₁ᴴ + R C₂ᴴ = E` in `R` at fixed utility. If the Hicksian
demands have `R`-derivatives `a`, `b`, then `E` is differentiable in `R` with derivative
`a + R b + C₂ᴴ`. -/
theorem hasDerivAt_E_of_hicksian (s : ExpenditureSystem) {R U a b : ℝ} (hR : 0 < R)
    (hU : U ∈ s.Uset) (ha : HasDerivAt (fun R' => s.C1H R' U) a R)
    (hb : HasDerivAt (fun R' => s.C2H R' U) b R) :
    HasDerivAt (fun R' => s.E R' U) (a + R * b + s.C2H R U) R := by
  have h := ha.add ((hasDerivAt_id R).mul hb)
  have hev : (fun R' => s.E R' U) =ᶠ[𝓝 R] fun R' => s.C1H R' U + id R' * s.C2H R' U := by
    filter_upwards [Ioi_mem_nhds hR] with R' hR'
    exact s.cost_eq R' U hR' hU
  refine (h.congr_of_eventuallyEq hev).congr_deriv ?_
  simp only [id]
  ring

/-- O&R fn. 18, p. 39: along a fixed indifference curve `∂C₁ᴴ/∂R + R ∂C₂ᴴ/∂R = 0`, i.e. the
slope `(∂C₁ᴴ/∂R)/(∂C₂ᴴ/∂R)` equals `−R`, minus the marginal rate of substitution. -/
theorem hicksian_tangency (s : ExpenditureSystem) {R U a b : ℝ} (hR : 0 < R)
    (hU : U ∈ s.Uset) (ha : HasDerivAt (fun R' => s.C1H R' U) a R)
    (hb : HasDerivAt (fun R' => s.C2H R' U) b R) : a + R * b = 0 := by
  have := s.shephard hR hU (s.hasDerivAt_E_of_hicksian hR hU ha hb)
  linarith

/-- O&R (1.28), p. 40, the income-cum-wealth effect of an interest-rate change. Suppose the
utility level `Upath R'` of the maximising consumer satisfies `E(R', U(R')) = Y₁ + R' Y₂` near
`R`, `E` is (jointly) differentiable at `(R, U(R))` with partials `E_R`, `E_U`, and `U` is
differentiable at `R`. Then `E_U · dU/dR = Y₂ − C₂ᴴ(R, U)`. -/
theorem welfare_effect (s : ExpenditureSystem) {Upath : ℝ → ℝ} {R eR eU u' Y1 Y2 : ℝ}
    (hR : 0 < R) (hU : Upath R ∈ s.Uset)
    (hE : HasFDerivAt (fun p : ℝ × ℝ => s.E p.1 p.2)
      (eR • ContinuousLinearMap.fst ℝ ℝ ℝ + eU • ContinuousLinearMap.snd ℝ ℝ ℝ) (R, Upath R))
    (hUd : HasDerivAt Upath u' R)
    (hbud : ∀ᶠ R' in 𝓝 R, s.E R' (Upath R') = Y1 + R' * Y2) :
    eU * u' = Y2 - s.C2H R (Upath R) := by
  have h1 := hasDerivAt_along_path hE hUd
  have h2 : HasDerivAt (fun R' => Y1 + R' * Y2) (eR + eU * u') R :=
    h1.congr_of_eventuallyEq (hbud.mono fun R' h => h.symm)
  have h3 : HasDerivAt (fun R' => Y1 + R' * Y2) Y2 R := by
    simpa using ((hasDerivAt_id R).mul_const Y2).const_add Y1
  have h4 := h2.unique h3
  have hpart : HasDerivAt (fun R' => s.E R' (Upath R)) eR R := by
    simpa using hasDerivAt_along_path (g := fun _ => Upath R) hE (hasDerivAt_const R _)
  have h5 := s.shephard hR hU hpart
  rw [← h5]
  linarith

/-- O&R p. 40, after (1.28): when the marginal expenditure cost of utility is positive
(`E_U > 0`), a rise in `R` (a fall in `r`) raises lifetime utility exactly when `Y₂ > C₂`, i.e.
when the country repays on date 2 debts incurred through a date-1 current-account deficit. -/
theorem welfare_rises_iff (s : ExpenditureSystem) {Upath : ℝ → ℝ} {R eR eU u' Y1 Y2 : ℝ}
    (hR : 0 < R) (hU : Upath R ∈ s.Uset)
    (hE : HasFDerivAt (fun p : ℝ × ℝ => s.E p.1 p.2)
      (eR • ContinuousLinearMap.fst ℝ ℝ ℝ + eU • ContinuousLinearMap.snd ℝ ℝ ℝ) (R, Upath R))
    (hUd : HasDerivAt Upath u' R)
    (hbud : ∀ᶠ R' in 𝓝 R, s.E R' (Upath R') = Y1 + R' * Y2) (heU : 0 < eU) :
    0 < u' ↔ s.C2H R (Upath R) < Y2 := by
  have h := s.welfare_effect hR hU hE hUd hbud
  constructor
  · intro hu
    have : 0 < eU * u' := mul_pos heU hu
    linarith
  · intro hc
    have : 0 < eU * u' := by linarith
    exact pos_of_mul_pos_right this heU.le

/-- The Slutsky decomposition, O&R (1.30), p. 41. Let `C1M R W` be Marshallian date-1 demand,
(jointly) differentiable at `(R, E(R,U))` with partials `∂C₁/∂R`, `∂C₁/∂W`; suppose the duality
identity (1.29) `C₁(R', E(R', U)) = C₁ᴴ(R', U)` holds for `R' > 0`, and `E`, `C₁ᴴ` are
differentiable in `R`. Then `∂C₁/∂R = ∂C₁ᴴ/∂R − (∂C₁/∂W) C₂ᴴ`. -/
theorem slutsky (s : ExpenditureSystem) {C1M : ℝ → ℝ → ℝ} {R U e h mR mW : ℝ}
    (hR : 0 < R) (hU : U ∈ s.Uset)
    (hM : HasFDerivAt (fun p : ℝ × ℝ => C1M p.1 p.2)
      (mR • ContinuousLinearMap.fst ℝ ℝ ℝ + mW • ContinuousLinearMap.snd ℝ ℝ ℝ) (R, s.E R U))
    (hE : HasDerivAt (fun R' => s.E R' U) e R)
    (hH : HasDerivAt (fun R' => s.C1H R' U) h R)
    (hdual : ∀ R', 0 < R' → C1M R' (s.E R' U) = s.C1H R' U) :
    mR = h - mW * s.C2H R U := by
  have h1 := hasDerivAt_along_path (g := fun R' => s.E R' U) hM hE
  have h2 : HasDerivAt (fun R' => s.C1H R' U) (mR + mW * e) R := by
    refine h1.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hR] with R' hR'
    exact (hdual R' hR').symm
  have h3 := h2.unique hH
  rw [← s.shephard hR hU hE]
  linarith

/-- The total effect of the interest rate, O&R (1.31), p. 41: with wealth `W₁ = Y₁ + R Y₂`
and `U` the attained utility (`E(R, U) = Y₁ + R Y₂`), under the hypotheses of `slutsky`,
`dC₁/dR = ∂C₁ᴴ/∂R + (∂C₁/∂W)(Y₂ − C₂)`: substitution effect plus the consumption effect of the
wealth-minus-income (terms-of-trade) change. -/
theorem total_effect (s : ExpenditureSystem) {C1M : ℝ → ℝ → ℝ} {R U e h mR mW Y1 Y2 : ℝ}
    (hR : 0 < R) (hU : U ∈ s.Uset) (hW : s.E R U = Y1 + R * Y2)
    (hM : HasFDerivAt (fun p : ℝ × ℝ => C1M p.1 p.2)
      (mR • ContinuousLinearMap.fst ℝ ℝ ℝ + mW • ContinuousLinearMap.snd ℝ ℝ ℝ) (R, s.E R U))
    (hE : HasDerivAt (fun R' => s.E R' U) e R)
    (hH : HasDerivAt (fun R' => s.C1H R' U) h R)
    (hdual : ∀ R', 0 < R' → C1M R' (s.E R' U) = s.C1H R' U) :
    HasDerivAt (fun R' => C1M R' (Y1 + R' * Y2)) (h + mW * (Y2 - s.C2H R U)) R := by
  have hsl := s.slutsky hR hU hM hE hH hdual
  have hg : HasDerivAt (fun R' => Y1 + R' * Y2) Y2 R := by
    simpa using ((hasDerivAt_id R).mul_const Y2).const_add Y1
  rw [hW] at hM
  have h1 := hasDerivAt_along_path (g := fun R' => Y1 + R' * Y2) hM hg
  convert h1 using 1
  rw [hsl]
  ring

end ExpenditureSystem

/-! ## The isoelastic intertemporally additive case (O&R §1.3.4.4, p. 42) -/

namespace Iso

/-- Isoelastic period utility O&R (1.22), p. 28, `u(C) = C^{1−1/σ}/(1 − 1/σ)` (for `σ ≠ 1`; the
Hicksian formula of p. 42 has exponent `σ/(σ−1)`, so the log case is excluded there). -/
noncomputable def u (σ C : ℝ) : ℝ := C ^ (1 - 1 / σ) / (1 - 1 / σ)

/-- The common denominator of O&R p. 42 (and of (1.26), p. 30), `1 + β^σ R^{1−σ}`. -/
noncomputable def D (σ β R : ℝ) : ℝ := 1 + β ^ σ * R ^ (1 - σ)

/-- Hicksian date-1 demand, O&R p. 42: `C₁ᴴ(R, U) = [(1 − 1/σ) U / (1 + β^σ R^{1−σ})]^{σ/(σ−1)}`. -/
noncomputable def C1H (σ β R U : ℝ) : ℝ := ((1 - 1 / σ) * U / D σ β R) ^ (σ / (σ - 1))

/-- Hicksian date-2 demand, from the Euler equation (1.25), p. 30, in terms of `R = 1/(1+r)`:
`C₂ᴴ = β^σ R^{−σ} C₁ᴴ`. -/
noncomputable def C2H (σ β R U : ℝ) : ℝ := β ^ σ * R ^ (-σ) * C1H σ β R U

/-- The isoelastic expenditure function, O&R §1.3.4.1, p. 39, in closed form:
`E(R, U) = (1 + β^σ R^{1−σ}) C₁ᴴ(R, U)`. -/
noncomputable def E (σ β R U : ℝ) : ℝ := D σ β R * C1H σ β R U

/-- Marshallian date-1 demand, O&R p. 40: `C₁(R, W₁) = W₁ / (1 + β^σ R^{1−σ})`. -/
noncomputable def C1M (σ β R W : ℝ) : ℝ := W / D σ β R

/-- Marshallian date-2 demand, from (1.25), p. 30: `C₂(R, W₁) = β^σ R^{−σ} C₁(R, W₁)`. -/
noncomputable def C2M (σ β R W : ℝ) : ℝ := β ^ σ * R ^ (-σ) * C1M σ β R W

/-- The denominator `1 + β^σ R^{1−σ}` of O&R p. 42 is positive. -/
theorem D_pos (σ : ℝ) {β R : ℝ} (hβ : 0 < β) (hR : 0 < R) : 0 < D σ β R := by
  unfold D
  have := Real.rpow_pos_of_pos hβ σ
  have := Real.rpow_pos_of_pos hR (1 - σ)
  positivity

/-- `R · R^{−σ} = R^{1−σ}`, used throughout O&R p. 42. -/
theorem mul_rpow_neg {R : ℝ} (σ : ℝ) (hR : 0 < R) : R * R ^ (-σ) = R ^ (1 - σ) := by
  rw [sub_eq_add_neg, Real.rpow_add hR, Real.rpow_one]

/-- Bernoulli-type tangent inequality behind strict concavity of the isoelastic utility:
for `p < 1`, `p ≠ 0` and `t > 0`, `t^p / p ≤ 1/p + (t − 1)`. -/
theorem rpow_div_le_tangent {p t : ℝ} (hp1 : p < 1) (hp0 : p ≠ 0) (ht : 0 < t) :
    t ^ p / p ≤ 1 / p + (t - 1) := by
  rcases lt_or_gt_of_ne hp0 with hneg | hpos
  · -- `p < 0`: weighted AM–GM with weights `1/(1−p)`, `−p/(1−p)` on `t^p` and `t`.
    have hq : 0 < 1 - p := by linarith
    have hw1 : 0 ≤ 1 / (1 - p) := by positivity
    have hw2 : 0 ≤ -p / (1 - p) := div_nonneg (by linarith) hq.le
    have hamgm := Real.geom_mean_le_arith_mean2_weighted hw1 hw2
      (Real.rpow_pos_of_pos ht p).le ht.le (by field_simp; ring)
    rw [← Real.rpow_mul ht.le, ← Real.rpow_add ht,
      show p * (1 / (1 - p)) + -p / (1 - p) = 0 by field_simp; ring, Real.rpow_zero] at hamgm
    have h2 : 1 - p ≤ t ^ p - p * t := by
      have := mul_le_mul_of_nonneg_left hamgm hq.le
      rw [mul_one] at this
      convert this using 1
      field_simp
      ring
    rw [div_le_iff_of_neg hneg]
    have : (1 / p + (t - 1)) * p = 1 + p * t - p := by field_simp; ring
    rw [this]
    linarith
  · have h := rpow_one_add_le_one_add_mul_self (show (-1 : ℝ) ≤ t - 1 by linarith)
      hpos.le hp1.le
    rw [add_sub_cancel] at h
    rw [div_le_iff₀ hpos]
    have : (1 / p + (t - 1)) * p = 1 + p * (t - 1) := by field_simp
    rw [this]
    exact h

/-- Strict concavity of isoelastic utility in tangent form, for `σ > 0`, `σ ≠ 1`: for
`x, y > 0`, `u(x) ≤ u(y) + u'(y)(x − y)` with `u'(y) = y^{−1/σ}` (O&R p. 30). -/
theorem u_le_tangent {σ x y : ℝ} (hσ : 0 < σ) (hσ1 : σ ≠ 1) (hx : 0 < x) (hy : 0 < y) :
    u σ x ≤ u σ y + y ^ (-1 / σ) * (x - y) := by
  set p := 1 - 1 / σ with hpdef
  have hp1 : p < 1 := by
    have : 0 < 1 / σ := by positivity
    linarith
  have hp0 : p ≠ 0 := by
    intro h
    have h1 : (1 : ℝ) / σ = 1 := by linarith
    exact hσ1 ((div_eq_one_iff_eq hσ.ne').mp h1).symm
  have ht : 0 < x / y := div_pos hx hy
  have key := rpow_div_le_tangent hp1 hp0 ht
  have hxy : x = x / y * y := by field_simp
  have hyp : 0 < y ^ p := Real.rpow_pos_of_pos hy p
  have hexp : y ^ (-1 / σ) = y ^ p / y := by
    rw [← Real.rpow_sub_one hy.ne']
    congr 1
    rw [hpdef]
    ring
  unfold u
  rw [← hpdef, hexp]
  conv_lhs => rw [hxy, Real.mul_rpow ht.le hy.le]
  have := mul_le_mul_of_nonneg_left key hyp.le
  calc (x / y) ^ p * y ^ p / p = y ^ p * ((x / y) ^ p / p) := by ring
    _ ≤ y ^ p * (1 / p + (x / y - 1)) := this
    _ = y ^ p / p + y ^ p / y * (x - y) := by field_simp

/-- The Hicksian demands are positive. -/
theorem C1H_pos {σ β R U : ℝ} (hβ : 0 < β) (hR : 0 < R) (hU : 0 < (1 - 1 / σ) * U) :
    0 < C1H σ β R U :=
  Real.rpow_pos_of_pos (div_pos hU (D_pos σ hβ hR)) _

/-- The date-2 Hicksian demand is positive. -/
theorem C2H_pos {σ β R U : ℝ} (hβ : 0 < β) (hR : 0 < R) (hU : 0 < (1 - 1 / σ) * U) :
    0 < C2H σ β R U := by
  unfold C2H
  have := Real.rpow_pos_of_pos hβ σ
  have := Real.rpow_pos_of_pos hR (-σ)
  have := C1H_pos (σ := σ) hβ hR hU
  positivity

/-- O&R p. 42: `(C₁ᴴ)^{1−1/σ} = (1 − 1/σ) U / (1 + β^σ R^{1−σ})`. -/
theorem C1H_rpow {σ β R U : ℝ} (hσ : 0 < σ) (hσ1 : σ ≠ 1) (hβ : 0 < β) (hR : 0 < R)
    (hU : 0 < (1 - 1 / σ) * U) :
    C1H σ β R U ^ (1 - 1 / σ) = (1 - 1 / σ) * U / D σ β R := by
  unfold C1H
  have hs : σ - 1 ≠ 0 := sub_ne_zero.mpr hσ1
  rw [← Real.rpow_mul (div_pos hU (D_pos σ hβ hR)).le,
    show σ / (σ - 1) * (1 - 1 / σ) = 1 by field_simp, Real.rpow_one]

/-- O&R p. 42: the Hicksian bundle attains exactly the utility level `U`,
`u(C₁ᴴ) + β u(C₂ᴴ) = U` (for `U` of the sign of `1 − 1/σ`, as utilities of positive
consumption are). -/
theorem utility_hicksian {σ β R U : ℝ} (hσ : 0 < σ) (hσ1 : σ ≠ 1) (hβ : 0 < β) (hR : 0 < R)
    (hU : 0 < (1 - 1 / σ) * U) :
    u σ (C1H σ β R U) + β * u σ (C2H σ β R U) = U := by
  have hp0 : 1 - 1 / σ ≠ 0 := by
    intro h
    apply hσ1
    field_simp at h
    linarith
  have hB := Real.rpow_pos_of_pos hβ σ
  have hRs := Real.rpow_pos_of_pos hR (-σ)
  have hC := C1H_pos (σ := σ) hβ hR hU
  have hD := D_pos σ hβ hR
  unfold u C2H
  rw [Real.mul_rpow (by positivity) hC.le, Real.mul_rpow hB.le hRs.le,
    ← Real.rpow_mul hβ.le, ← Real.rpow_mul hR.le, C1H_rpow hσ hσ1 hβ hR hU,
    show σ * (1 - 1 / σ) = σ - 1 by field_simp,
    (show -σ * (1 - 1 / σ) = 1 - σ by field_simp; ring), Real.rpow_sub_one hβ.ne']
  unfold D at hD ⊢
  field_simp

/-- Euler condition at the Hicksian bundle, O&R (1.25), p. 30: `β u'(C₂ᴴ) = R u'(C₁ᴴ)`. -/
theorem euler_hicksian {σ β R U : ℝ} (hσ : 0 < σ) (hβ : 0 < β) (hR : 0 < R)
    (hU : 0 < (1 - 1 / σ) * U) :
    β * C2H σ β R U ^ (-1 / σ) = R * C1H σ β R U ^ (-1 / σ) := by
  have hB := Real.rpow_pos_of_pos hβ σ
  have hRs := Real.rpow_pos_of_pos hR (-σ)
  have hC := C1H_pos (σ := σ) hβ hR hU
  unfold C2H
  rw [Real.mul_rpow (by positivity) hC.le, Real.mul_rpow hB.le hRs.le,
    ← Real.rpow_mul hβ.le, ← Real.rpow_mul hR.le,
    show σ * (-1 / σ) = -1 by field_simp, show -σ * (-1 / σ) = 1 by field_simp,
    Real.rpow_neg_one, Real.rpow_one]
  field_simp

/-- The budget identity for the Hicksian bundle, O&R fn. 18, p. 39:
`C₁ᴴ + R C₂ᴴ = E(R, U)`. -/
theorem cost_hicksian (σ β R U : ℝ) (hR : 0 < R) :
    E σ β R U = C1H σ β R U + R * C2H σ β R U := by
  unfold E C2H D
  rw [← mul_rpow_neg σ hR]
  ring

/-- Cost minimisation, O&R §1.3.4.1, p. 39: every positive bundle giving lifetime utility at
least `U` costs at least `E(R, U)`. (Tangent inequality for the concave `u` plus the Euler
condition at the Hicksian bundle.) -/
theorem le_cost {σ β R U C1 C2 : ℝ} (hσ : 0 < σ) (hσ1 : σ ≠ 1) (hβ : 0 < β) (hR : 0 < R)
    (hU : 0 < (1 - 1 / σ) * U) (hC1 : 0 < C1) (hC2 : 0 < C2)
    (hUle : U ≤ u σ C1 + β * u σ C2) : E σ β R U ≤ C1 + R * C2 := by
  have ha := C1H_pos (σ := σ) hβ hR hU
  have hb := C2H_pos (σ := σ) hβ hR hU
  have t1 := u_le_tangent hσ hσ1 hC1 ha
  have t2 := u_le_tangent hσ hσ1 hC2 hb
  have hut := utility_hicksian hσ hσ1 hβ hR hU
  have heu := euler_hicksian hσ hβ hR hU
  have hm : 0 < C1H σ β R U ^ (-1 / σ) := Real.rpow_pos_of_pos ha _
  rw [cost_hicksian σ β R U hR]
  have h3 : 0 ≤ C1H σ β R U ^ (-1 / σ) *
      ((C1 + R * C2) - (C1H σ β R U + R * C2H σ β R U)) := by
    have := mul_le_mul_of_nonneg_left t2 hβ.le
    nlinarith
  linarith [(mul_nonneg_iff_of_pos_left hm).mp h3]

/-- The isoelastic additive consumer as an `ExpenditureSystem`, O&R §1.3.4.4, p. 42:
`V(C₁, C₂) = u(C₁) + β u(C₂)`, attainable levels `U` with `(1 − 1/σ) U > 0`, and the closed
forms above. -/
noncomputable def system {σ β : ℝ} (hσ : 0 < σ) (hσ1 : σ ≠ 1) (hβ : 0 < β) :
    ExpenditureSystem where
  V C1 C2 := u σ C1 + β * u σ C2
  Uset := {U | 0 < (1 - 1 / σ) * U}
  E := E σ β
  C1H := C1H σ β
  C2H := C2H σ β
  le_cost _ _ _ _ hR hU hC1 hC2 hle := le_cost hσ hσ1 hβ hR hU hC1 hC2 hle
  C1H_pos _ _ hR hU := C1H_pos hβ hR hU
  C2H_pos _ _ hR hU := C2H_pos hβ hR hU
  attains _ _ hR hU := (utility_hicksian hσ hσ1 hβ hR hU).ge
  cost_eq R U hR _ := cost_hicksian σ β R U hR

/-- The price derivative of the denominator of O&R p. 42:
`d/dR (1 + β^σ R^{1−σ}) = β^σ (1 − σ) R^{−σ}`. -/
theorem hasDerivAt_D (σ β : ℝ) {R : ℝ} (hR : 0 < R) :
    HasDerivAt (fun R' => D σ β R') (β ^ σ * ((1 - σ) * R ^ (-σ))) R := by
  have h := ((Real.hasDerivAt_rpow_const (p := 1 - σ) (Or.inl hR.ne')).const_mul
    (β ^ σ)).const_add 1
  rw [show (1 : ℝ) - σ - 1 = -σ by ring] at h
  exact h

/-- The Hicksian substitution effect, O&R p. 42 (first term of the decomposition):
`∂C₁ᴴ/∂R = σ β^σ R^{−σ} C₁ᴴ / (1 + β^σ R^{1−σ})`. -/
theorem hasDerivAt_C1H {σ β R U : ℝ} (hσ : 0 < σ) (hσ1 : σ ≠ 1) (hβ : 0 < β) (hR : 0 < R)
    (hU : 0 < (1 - 1 / σ) * U) :
    HasDerivAt (fun R' => C1H σ β R' U)
      (σ * β ^ σ * R ^ (-σ) * C1H σ β R U / D σ β R) R := by
  have hD := D_pos σ hβ hR
  have hs : σ - 1 ≠ 0 := sub_ne_zero.mpr hσ1
  have hk : 0 < (1 - 1 / σ) * U / D σ β R := div_pos hU hD
  have h := ((hasDerivAt_const R ((1 - 1 / σ) * U)).div (hasDerivAt_D σ β hR)
    hD.ne').rpow_const (p := σ / (σ - 1)) (Or.inl hk.ne')
  convert h using 1
  · rfl
  unfold C1H
  simp only [Pi.div_apply]
  rw [Real.rpow_sub_one hk.ne']
  have hU0 : U ≠ 0 := by
    rintro rfl
    simp at hU
  have hσ0 : σ ≠ 0 := hσ.ne'
  generalize ((1 - 1 / σ) * U / D σ β R) ^ (σ / (σ - 1)) = K
  field_simp
  ring

/-- Shephard's lemma (1.27), p. 39, verified in closed form for isoelastic utility:
`∂E/∂R = C₂ᴴ = β^σ R^{−σ} C₁ᴴ`. -/
theorem shephard_iso {σ β R U : ℝ} (hσ : 0 < σ) (hσ1 : σ ≠ 1) (hβ : 0 < β) (hR : 0 < R)
    (hU : 0 < (1 - 1 / σ) * U) :
    HasDerivAt (fun R' => E σ β R' U) (C2H σ β R U) R := by
  have hD := D_pos σ hβ hR
  have h := (hasDerivAt_D σ β hR).mul (hasDerivAt_C1H hσ hσ1 hβ hR hU)
  convert h using 1
  · rfl
  unfold C2H
  field_simp
  ring

/-- The abstract Shephard lemma applied to the isoelastic `system` returns the closed form:
`C₁ᴴ = E − R E_R` holds for isoelastic utility (O&R p. 39). -/
theorem C1H_eq_E_sub_iso {σ β R U : ℝ} (hσ : 0 < σ) (hσ1 : σ ≠ 1) (hβ : 0 < β) (hR : 0 < R)
    (hU : 0 < (1 - 1 / σ) * U) :
    C1H σ β R U = E σ β R U - R * C2H σ β R U :=
  (system hσ hσ1 hβ).C1H_eq_E_sub (U := U) hR hU (shephard_iso hσ hσ1 hβ hR hU)

/-- The duality identity O&R (1.29), p. 41, in closed form: Marshallian demand at wealth
`E(R, U)` is Hicksian demand at utility `U`, `C₁(R, E(R, U)) = C₁ᴴ(R, U)`. -/
theorem duality_identity_iso (σ : ℝ) {β R U : ℝ} (hβ : 0 < β) (hR : 0 < R) :
    C1M σ β R (E σ β R U) = C1H σ β R U := by
  have hD := D_pos σ hβ hR
  unfold C1M E
  field_simp

/-- The Marshallian demands of O&R p. 40 exhaust wealth, `C₁ + R C₂ = W₁`. -/
theorem marshallian_budget (σ : ℝ) {β R W : ℝ} (hβ : 0 < β) (hR : 0 < R) :
    C1M σ β R W + R * C2M σ β R W = W := by
  have hD := D_pos σ hβ hR
  unfold C2M C1M
  have e : R * (β ^ σ * R ^ (-σ) * (W / D σ β R)) = β ^ σ * (R * R ^ (-σ)) * W / D σ β R := by
    ring
  rw [e, mul_rpow_neg σ hR]
  unfold D at hD ⊢
  field_simp

/-- The Marshallian demand of O&R p. 40 is the consumption function (1.26), p. 30, once
`R = 1/(1+r)`: `W / (1 + β^σ R^{1−σ}) = W / (1 + (1+r)^{σ−1} β^σ)`. -/
theorem C1M_eq_eq26 (σ β W : ℝ) {r : ℝ} (hr : 0 < 1 + r) :
    C1M σ β (1 / (1 + r)) W = W / (1 + (1 + r) ^ (σ - 1) * β ^ σ) := by
  unfold C1M D
  rw [one_div, Real.inv_rpow hr.le, ← Real.rpow_neg hr.le, neg_sub, mul_comm]

/-- Price partial of Marshallian demand at fixed wealth, O&R p. 41:
`∂C₁/∂R = (σ − 1) β^σ R^{−σ} C₁ / (1 + β^σ R^{1−σ})`. -/
theorem hasDerivAt_C1M_R (σ : ℝ) {β R W : ℝ} (hβ : 0 < β) (hR : 0 < R) :
    HasDerivAt (fun R' => C1M σ β R' W)
      ((σ - 1) * β ^ σ * R ^ (-σ) * C1M σ β R W / D σ β R) R := by
  have hD := D_pos σ hβ hR
  have h := (hasDerivAt_const R W).div (hasDerivAt_D σ β hR) hD.ne'
  convert h using 1
  · rfl
  unfold C1M
  field_simp
  ring

/-- Wealth partial of Marshallian demand, O&R p. 41: `∂C₁/∂W₁ = 1 / (1 + β^σ R^{1−σ})`. -/
theorem hasDerivAt_C1M_W (σ : ℝ) {β R W : ℝ} :
    HasDerivAt (fun W' => C1M σ β R W') (1 / D σ β R) W := by
  have h := (hasDerivAt_id W).div_const (D σ β R)
  convert h using 1
  rfl

/-- The Slutsky equation O&R (1.30), p. 41, verified in closed form: at wealth `W₁ = E(R, U)`,
`∂C₁/∂R = ∂C₁ᴴ/∂R − (∂C₁/∂W₁) C₂ᴴ`, with the partials of `hasDerivAt_C1H` and
`hasDerivAt_C1M_W`. -/
theorem slutsky_iso {σ β R U : ℝ} (hβ : 0 < β) (hR : 0 < R) :
    HasDerivAt (fun R' => C1M σ β R' (E σ β R U))
      (σ * β ^ σ * R ^ (-σ) * C1H σ β R U / D σ β R - 1 / D σ β R * C2H σ β R U) R := by
  have h := hasDerivAt_C1M_R σ (W := E σ β R U) hβ hR
  rw [duality_identity_iso σ hβ hR] at h
  convert h using 1
  unfold C2H
  ring

/-- The decomposition (1.31) in the isoelastic case, O&R p. 42 (first display): with
`W₁ = Y₁ + R Y₂`, `C₁ = C₁(R, W₁)` and `C₂ = C₂(R, W₁)`,
`dC₁/dR = σ β^σ R^{−σ} C₁ / (1 + β^σ R^{1−σ}) + (Y₂ − C₂) / (1 + β^σ R^{1−σ})`
(substitution effect plus wealth-minus-income effect). -/
theorem hasDerivAt_C1_total {σ β R Y1 Y2 : ℝ} (hβ : 0 < β) (hR : 0 < R) :
    HasDerivAt (fun R' => C1M σ β R' (Y1 + R' * Y2))
      (σ * β ^ σ * R ^ (-σ) * C1M σ β R (Y1 + R * Y2) / D σ β R +
        (Y2 - C2M σ β R (Y1 + R * Y2)) / D σ β R) R := by
  have hD := D_pos σ hβ hR
  have h := (((hasDerivAt_id R).mul_const Y2).const_add Y1).div (hasDerivAt_D σ β hR) hD.ne'
  convert h using 1
  · rfl
  unfold C2M C1M
  simp only [id]
  field_simp
  ring

/-- O&R p. 42 (second display), after applying the Euler equation (1.25):
`dC₁/dR = (σ − 1) β^σ R^{−σ} C₁ / (1 + β^σ R^{1−σ}) + Y₂ / (1 + β^σ R^{1−σ})`, so the sign of
`σ − 1` decides whether substitution or income effect dominates. -/
theorem hasDerivAt_C1_total_euler {σ β R Y1 Y2 : ℝ} (hβ : 0 < β) (hR : 0 < R) :
    HasDerivAt (fun R' => C1M σ β R' (Y1 + R' * Y2))
      ((σ - 1) * β ^ σ * R ^ (-σ) * C1M σ β R (Y1 + R * Y2) / D σ β R +
        Y2 / D σ β R) R := by
  refine (hasDerivAt_C1_total hβ hR).congr_deriv ?_
  unfold C2M
  ring

/-- O&R p. 42: the `R`-form of the interest-rate effect is equivalent to (1.24), p. 29. Writing
date-1 consumption as a function of `r` through `R = 1/(1+r)` (so `dR/dr = −R²`), with
`C₂ = (1+r)^σ β^σ C₁` from (1.25), the derivative is
`dC₁/dr = [(Y₁ − C₁) − σ C₂/(1+r)] / [1 + r + C₂/C₁]` whenever lifetime wealth is positive. -/
theorem hasDerivAt_C1_r_eq24 {σ β Y1 Y2 r C1 C2 : ℝ} (hβ : 0 < β) (hr : 0 < 1 + r)
    (hW : 0 < Y1 + Y2 / (1 + r))
    (hC1 : C1 = C1M σ β (1 / (1 + r)) (Y1 + 1 / (1 + r) * Y2))
    (hC2 : C2 = (1 + r) ^ σ * β ^ σ * C1) :
    HasDerivAt (fun r' => C1M σ β (1 / (1 + r')) (Y1 + 1 / (1 + r') * Y2))
      (((Y1 - C1) - σ * C2 / (1 + r)) / (1 + r + C2 / C1)) r := by
  have hR : 0 < 1 / (1 + r) := by positivity
  have hF := hasDerivAt_C1_total_euler (σ := σ) (Y1 := Y1) (Y2 := Y2) hβ hR
  have hg : HasDerivAt (fun r' => 1 / (1 + r')) (-1 / (1 + r) ^ 2) r := by
    have := (hasDerivAt_const r (1 : ℝ)).div ((hasDerivAt_id r).const_add 1) hr.ne'
    convert this using 1
    · rfl
    simp only [id]
    ring
  have h := hF.comp r hg
  have hA : (1 / (1 + r)) ^ (-σ) = (1 + r) ^ σ := by
    rw [one_div, Real.inv_rpow hr.le, Real.rpow_neg hr.le, inv_inv]
  have hB : (1 / (1 + r)) ^ (1 - σ) = (1 + r) ^ σ / (1 + r) := by
    rw [one_div, Real.inv_rpow hr.le, ← Real.rpow_neg hr.le, neg_sub,
      Real.rpow_sub_one hr.ne']
  have hP := Real.rpow_pos_of_pos hr σ
  have hBs := Real.rpow_pos_of_pos hβ σ
  have hDp : 0 < 1 + β ^ σ * ((1 + r) ^ σ / (1 + r)) := by positivity
  have hC1pos : 0 < C1 := by
    rw [hC1]
    unfold C1M D
    rw [hB]
    have : Y1 + 1 / (1 + r) * Y2 = Y1 + Y2 / (1 + r) := by ring
    rw [this]
    positivity
  have hratio : C2 / C1 = (1 + r) ^ σ * β ^ σ := by
    rw [hC2]
    field_simp
  convert h using 1
  · rfl
  rw [hratio, hC2]
  rw [hC1]
  unfold C1M D
  rw [hA, hB]
  field_simp
  ring

/-- Joint (Fréchet) differentiability of isoelastic Marshallian demand `C₁(R, W₁) = W₁/D(R)`,
with partials `∂C₁/∂R = (σ − 1) β^σ R^{−σ} C₁/D` and `∂C₁/∂W₁ = 1/D` (O&R p. 41). -/
theorem hasFDerivAt_C1M (σ : ℝ) {β R W : ℝ} (hβ : 0 < β) (hR : 0 < R) :
    HasFDerivAt (fun p : ℝ × ℝ => C1M σ β p.1 p.2)
      (((σ - 1) * β ^ σ * R ^ (-σ) * C1M σ β R W / D σ β R) • ContinuousLinearMap.fst ℝ ℝ ℝ +
        (1 / D σ β R) • ContinuousLinearMap.snd ℝ ℝ ℝ) (R, W) := by
  have hD := D_pos σ hβ hR
  have hinv := ((hasDerivAt_D σ β hR).inv hD.ne').hasFDerivAt.comp (R, W)
    (hasFDerivAt_fst (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := (R, W)))
  have h := (hasFDerivAt_snd (𝕜 := ℝ) (E := ℝ) (F := ℝ) (p := (R, W))).mul hinv
  convert h using 1
  · funext q
    simp [C1M, div_eq_mul_inv]
  · ext
    · simp [C1M]
      field_simp
      ring
    · simp

/-- The abstract decomposition `ExpenditureSystem.total_effect` (O&R (1.31), p. 41) applied to the
isoelastic `system`: at the utility level `U` with `E(R, U) = Y₁ + R Y₂`,
`dC₁/dR = ∂C₁ᴴ/∂R + (∂C₁/∂W₁)(Y₂ − C₂ᴴ)`, with the closed-form partials of p. 42. -/
theorem total_effect_iso {σ β R U Y1 Y2 : ℝ} (hσ : 0 < σ) (hσ1 : σ ≠ 1) (hβ : 0 < β)
    (hR : 0 < R) (hU : 0 < (1 - 1 / σ) * U) (hW : E σ β R U = Y1 + R * Y2) :
    HasDerivAt (fun R' => C1M σ β R' (Y1 + R' * Y2))
      (σ * β ^ σ * R ^ (-σ) * C1H σ β R U / D σ β R +
        1 / D σ β R * (Y2 - C2H σ β R U)) R :=
  (system hσ hσ1 hβ).total_effect (U := U) hR hU hW (hasFDerivAt_C1M σ hβ hR)
    (shephard_iso hσ hσ1 hβ hR hU) (hasDerivAt_C1H hσ hσ1 hβ hR hU)
    (fun _ hR' => duality_identity_iso σ hβ hR')

end Iso

end ObstfeldRogoff.IntertemporalTrade.Duality
