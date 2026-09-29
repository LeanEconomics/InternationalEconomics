/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StickyPriceModels.Model
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.FieldSimp

/-!
# Pricing to market and exchange-rate pass-through

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §10.4.2,
eq. (144), p. 711, and the Application "Pricing to Market and Exchange-Rate Pass-Through",
pp. 711–712; Box 10.2, p. 689 (price exceeds marginal cost).

A Home monopolist with constant marginal cost `w` (Home currency; the linear production
function of §10.4.2) sells in two segmented markets: at Home at price `p`, and abroad at the
Foreign-currency price `p*`, with exchange rate `𝓔` (Home currency per Foreign currency).

Results:
* Separability: with constant marginal cost the two pricing problems are independent
  (necessity and sufficiency); with a strictly convex cost they are not (a counterexample).
* Constant-elasticity demand: the unique optimal price is the markup `θ c/(θ − 1)`
  (necessity and sufficiency, global, via Bernoulli's inequality); the general first-order
  condition and Lerner rule; (144) `p(h) = 𝓔 p*(h) = θ w/(θ − 1)`; LOOP holds iff the two
  elasticities coincide; pass-through is complete (elasticity `−1`, exactly and discretely).
* Linear demand: the unique optimal price `(α/b + c)/2`; pass-through elasticity
  `−c/(α/b + c) ∈ (−1/2, 0)`, strictly weaker as the Home currency depreciates; the demand
  elasticity at the optimum falls as the exporter's currency weakens (p. 712); a Foreign-currency
  price falls less than proportionally after a depreciation (the German-car episode).
* Real markups are invariant to proportional nominal shocks for ANY demand curve absent nominal
  rigidity (p. 712); with a rigid nominal wage, constant elasticity still fixes the markup but
  linear demand does not.
* Producer-currency vs local-currency pricing: pass-through `−1` vs `0`, expenditure switching
  vs markup absorption, the exact bound for meeting demand under LCP, and the envelope
  (second-order loss) result behind menu costs for the exporter.
* Local distribution costs (p. 712, via Ch. 4): incomplete pass-through even with constant
  elasticity, elasticity `−(w/𝓔)/(w/𝓔 + d)`.
-/

namespace ObstfeldRogoff.StickyPriceModels.PassThrough

open Filter Topology Set

/-- Point elasticity `x f'(x)/f(x)` of a function `f` at `x`; applied to the Foreign-currency
price as a function of `𝓔` it is the exchange-rate pass-through elasticity (O&R p. 711). -/
noncomputable def elasticity (f : ℝ → ℝ) (x : ℝ) : ℝ := x * deriv f x / f x

/-- O&R §10.4.2, p. 711: Home-currency profit of a Home firm with constant marginal cost `w`
selling at `p` at Home (demand `DH`) and at Foreign-currency price `pstar` abroad (demand
`DF`), with exchange rate `E`. -/
def segmentedProfit (DH DF : ℝ → ℝ) (w E p pstar : ℝ) : ℝ :=
  (p - w) * DH p + (E * pstar - w) * DF pstar

/-- O&R p. 711: profit `(q − c) A q^{−θ}` under constant-elasticity demand `A q^{−θ}`
with constant marginal cost `c` (all in the currency of the market). -/
noncomputable def ceProfit (A θ c q : ℝ) : ℝ := (q - c) * (A * q ^ (-θ))

/-- O&R (144), p. 711 and p. 710: the monopoly markup price `θ c/(θ − 1)`. -/
noncomputable def ceMarkupPrice (θ c : ℝ) : ℝ := θ * c / (θ - 1)

/-- O&R p. 712: profit `(q − c)(α − b q)` under linear demand `α − b q`. -/
def linProfit (α b c q : ℝ) : ℝ := (q - c) * (α - b * q)

/-- O&R p. 712: the optimal price `(α/b + c)/2` under linear demand. -/
noncomputable def linPrice (α b c : ℝ) : ℝ := (α / b + c) / 2

/-- O&R p. 711 (contrast): total profit with a strictly convex cost `(q_H + q_F)²/2`, Home
demand `a − p`, Foreign demand `1 − q`, `𝓔 = 1`. -/
noncomputable def convexCostProfit (a p q : ℝ) : ℝ :=
  p * (a - p) + q * (1 - q) - (a - p + (1 - q)) ^ 2 / 2

/-- O&R p. 711: Home-currency export profit `(𝓔 q − w) A q^{−θ}` at Foreign-currency price `q`
under constant-elasticity Foreign demand. -/
noncomputable def exportProfit (A θ w E q : ℝ) : ℝ := (E * q - w) * (A * q ^ (-θ))

/-- O&R pp. 674, 711: the Home-currency profit forgone at exchange rate `E` by an exporter whose
Foreign-currency price was preset (local-currency pricing) at the optimum for `E0`. -/
noncomputable def lcpLoss (A θ w E0 E : ℝ) : ℝ :=
  exportProfit A θ w E (ceMarkupPrice θ w / E) - exportProfit A θ w E (ceMarkupPrice θ w / E0)

/-! ## Separability of the two pricing problems -/

/-- O&R p. 711: "because the production function is linear, a firm's pricing decisions in
the two markets are independent": `(p, p*)` maximises total profit over `SH × SF` iff `p`
maximises Home-market profit and `p*` maximises Foreign-market profit. -/
theorem segmented_optimum_iff (DH DF : ℝ → ℝ) (w E : ℝ) (SH SF : Set ℝ) {p q : ℝ}
    (hp : p ∈ SH) (hq : q ∈ SF) :
    (∀ p' ∈ SH, ∀ q' ∈ SF,
        segmentedProfit DH DF w E p' q' ≤ segmentedProfit DH DF w E p q) ↔
      (∀ p' ∈ SH, (p' - w) * DH p' ≤ (p - w) * DH p) ∧
      (∀ q' ∈ SF, (E * q' - w) * DF q' ≤ (E * q - w) * DF q) := by
  unfold segmentedProfit
  constructor
  · intro h
    refine ⟨fun p' hp' => ?_, fun q' hq' => ?_⟩
    · have := h p' hp' q hq
      linarith
    · have := h p hp q' hq'
      linarith
  · rintro ⟨hH, hF⟩ p' hp' q' hq'
    have h1 := hH p' hp'
    have h2 := hF q' hq'
    linarith

/-- O&R p. 711 (contrast): with the strictly convex cost `(q_H + q_F)²/2` the profit gap is the
positive-definite form `(3/2)Δp² + ΔpΔq + (3/2)Δq²` around `((1 + 5a)/8, (5 + a)/8)`. -/
theorem convexCostProfit_gap (a p q : ℝ) :
    convexCostProfit a ((1 + 5 * a) / 8) ((5 + a) / 8) - convexCostProfit a p q =
      3 / 2 * (p - (1 + 5 * a) / 8) ^ 2 + (p - (1 + 5 * a) / 8) * (q - (5 + a) / 8) +
        3 / 2 * (q - (5 + a) / 8) ^ 2 := by
  unfold convexCostProfit
  ring

/-- O&R p. 711 (contrast): with a strictly convex cost the joint optimum exists and is unique:
`(p, q)` maximises total profit iff `p = (1 + 5a)/8` and `q = (5 + a)/8`. -/
theorem convexCost_optimum_iff (a p q : ℝ) :
    (∀ p' q', convexCostProfit a p' q' ≤ convexCostProfit a p q) ↔
      p = (1 + 5 * a) / 8 ∧ q = (5 + a) / 8 := by
  constructor
  · intro h
    have h1 := h ((1 + 5 * a) / 8) ((5 + a) / 8)
    have h2 := convexCostProfit_gap a p q
    have hsq : 3 / 2 * (p - (1 + 5 * a) / 8) ^ 2 + (p - (1 + 5 * a) / 8) * (q - (5 + a) / 8) +
        3 / 2 * (q - (5 + a) / 8) ^ 2 = ((p - (1 + 5 * a) / 8) + (q - (5 + a) / 8)) ^ 2 / 2 +
          (p - (1 + 5 * a) / 8) ^ 2 + (q - (5 + a) / 8) ^ 2 := by ring
    have hp2 : (p - (1 + 5 * a) / 8) ^ 2 = 0 := by
      nlinarith [sq_nonneg ((p - (1 + 5 * a) / 8) + (q - (5 + a) / 8)),
        sq_nonneg (p - (1 + 5 * a) / 8), sq_nonneg (q - (5 + a) / 8)]
    have hq2 : (q - (5 + a) / 8) ^ 2 = 0 := by
      nlinarith [sq_nonneg ((p - (1 + 5 * a) / 8) + (q - (5 + a) / 8)),
        sq_nonneg (p - (1 + 5 * a) / 8), sq_nonneg (q - (5 + a) / 8)]
    constructor
    · nlinarith [pow_eq_zero_iff (n := 2) (a := p - (1 + 5 * a) / 8) two_ne_zero |>.1 hp2]
    · nlinarith [pow_eq_zero_iff (n := 2) (a := q - (5 + a) / 8) two_ne_zero |>.1 hq2]
  · rintro ⟨rfl, rfl⟩ p' q'
    have h2 := convexCostProfit_gap a p' q'
    nlinarith [sq_nonneg ((p' - (1 + 5 * a) / 8) + (q' - (5 + a) / 8)),
      sq_nonneg (p' - (1 + 5 * a) / 8), sq_nonneg (q' - (5 + a) / 8)]

/-- O&R p. 711 (why linearity matters): with a strictly convex cost the optimal Foreign price
depends on the Home demand shifter `a` (strictly increasing in it), so pricing decisions in
the two markets are NOT independent, in contrast with `segmented_optimum_iff`. -/
theorem convexCost_foreign_price_depends_on_home_demand {a a' p q p' q' : ℝ}
    (h : ∀ p₁ q₁, convexCostProfit a p₁ q₁ ≤ convexCostProfit a p q)
    (h' : ∀ p₁ q₁, convexCostProfit a' p₁ q₁ ≤ convexCostProfit a' p' q') (ha : a < a') :
    q < q' := by
  have e := ((convexCost_optimum_iff a p q).1 h).2
  have e' := ((convexCost_optimum_iff a' p' q').1 h').2
  rw [e, e']
  linarith

/-! ## Constant-elasticity demand: the markup rule -/

/-- Bernoulli's inequality in the form used for the markup rule (O&R p. 710):
`θ x − θ + 1 ≤ x^θ` for `θ > 1`, `x > 0`. -/
theorem markup_bernoulli {θ x : ℝ} (hθ : 1 < θ) (hx : 0 < x) : θ * x - θ + 1 ≤ x ^ θ := by
  have h := one_add_mul_self_le_rpow_one_add (s := x - 1) (by linarith) hθ.le
  have e : (1 + (x - 1)) = x := by ring
  rw [e] at h
  linarith

/-- Strict Bernoulli inequality for the markup rule (O&R p. 710): strict unless `x = 1`. -/
theorem markup_bernoulli_strict {θ x : ℝ} (hθ : 1 < θ) (hx : 0 < x) (hx1 : x ≠ 1) :
    θ * x - θ + 1 < x ^ θ := by
  have h := one_add_mul_self_lt_rpow_one_add (s := x - 1) (by linarith) (sub_ne_zero.2 hx1) hθ
  have e : (1 + (x - 1)) = x := by ring
  rw [e] at h
  linarith

/-- O&R p. 710: the markup price is positive. -/
theorem ceMarkupPrice_pos {θ c : ℝ} (hθ : 1 < θ) (hc : 0 < c) : 0 < ceMarkupPrice θ c := by
  have : 0 < θ - 1 := by linarith
  unfold ceMarkupPrice
  positivity

/-- O&R p. 710 / Box 10.2, p. 689: under monopoly price exceeds marginal cost,
`θ c/(θ − 1) > c`. -/
theorem ceMarkupPrice_gt_cost {θ c : ℝ} (hθ : 1 < θ) (hc : 0 < c) : c < ceMarkupPrice θ c := by
  have h1 : 0 < θ - 1 := by linarith
  unfold ceMarkupPrice
  rw [lt_div_iff₀ h1]
  nlinarith

/-- Profit comparison behind the markup rule (O&R p. 710): writing `q = x p°`, the profit at
`q` equals the optimal profit times `(θ x − θ + 1)/x^θ`. -/
theorem ceProfit_ratio {A θ c q : ℝ} (hθ : 1 < θ) (hc : 0 < c) (hq : 0 < q) :
    ceProfit A θ c q = ceProfit A θ c (ceMarkupPrice θ c) *
      ((θ * (q / ceMarkupPrice θ c) - θ + 1) / (q / ceMarkupPrice θ c) ^ θ) := by
  have hp := ceMarkupPrice_pos hθ hc
  have h1 : 0 < θ - 1 := by linarith
  set p := ceMarkupPrice θ c with hpdef
  have hx : 0 < q / p := div_pos hq hp
  have hqx : q = q / p * p := by field_simp
  have hpθ : 0 < p ^ θ := Real.rpow_pos_of_pos hp θ
  have hxθ : 0 < (q / p) ^ θ := Real.rpow_pos_of_pos hx θ
  have hqθ : q ^ θ = (q / p) ^ θ * p ^ θ := by
    rw [← Real.mul_rpow hx.le hp.le, ← hqx]
  have hpc : p - c = c / (θ - 1) := by rw [hpdef, ceMarkupPrice]; field_simp; ring
  have hqc : q - c = c / (θ - 1) * (θ * (q / p) - θ + 1) := by
    rw [hpdef, ceMarkupPrice]; field_simp; ring
  unfold ceProfit
  rw [Real.rpow_neg hq.le, Real.rpow_neg hp.le, hqθ, hqc, hpc]
  field_simp

/-- O&R (144), p. 711 (sufficiency): under constant-elasticity demand `A q^{−θ}` with `θ > 1`
the markup price `θ c/(θ − 1)` maximises profit over all positive prices (global). -/
theorem ceProfit_le_markup {A θ c q : ℝ} (hA : 0 < A) (hθ : 1 < θ) (hc : 0 < c) (hq : 0 < q) :
    ceProfit A θ c q ≤ ceProfit A θ c (ceMarkupPrice θ c) := by
  have hp := ceMarkupPrice_pos hθ hc
  have hx : 0 < q / ceMarkupPrice θ c := div_pos hq hp
  have hpos : 0 < ceProfit A θ c (ceMarkupPrice θ c) := by
    unfold ceProfit
    have := ceMarkupPrice_gt_cost hθ hc
    have := Real.rpow_pos_of_pos hp (-θ)
    have : 0 < ceMarkupPrice θ c - c := by linarith
    positivity
  rw [ceProfit_ratio hθ hc hq]
  apply mul_le_of_le_one_right hpos.le
  rw [div_le_one (Real.rpow_pos_of_pos hx θ)]
  exact markup_bernoulli hθ hx

/-- O&R (144), p. 711 (uniqueness): every other positive price earns strictly less. -/
theorem ceProfit_lt_markup {A θ c q : ℝ} (hA : 0 < A) (hθ : 1 < θ) (hc : 0 < c) (hq : 0 < q)
    (hne : q ≠ ceMarkupPrice θ c) :
    ceProfit A θ c q < ceProfit A θ c (ceMarkupPrice θ c) := by
  have hp := ceMarkupPrice_pos hθ hc
  have hx : 0 < q / ceMarkupPrice θ c := div_pos hq hp
  have hx1 : q / ceMarkupPrice θ c ≠ 1 := by
    intro h
    exact hne ((div_eq_one_iff_eq hp.ne').1 h)
  have hpos : 0 < ceProfit A θ c (ceMarkupPrice θ c) := by
    unfold ceProfit
    have := ceMarkupPrice_gt_cost hθ hc
    have := Real.rpow_pos_of_pos hp (-θ)
    have : 0 < ceMarkupPrice θ c - c := by linarith
    positivity
  rw [ceProfit_ratio hθ hc hq]
  apply mul_lt_of_lt_one_right hpos
  rw [div_lt_one (Real.rpow_pos_of_pos hx θ)]
  exact markup_bernoulli_strict hθ hx hx1

/-- O&R (144), p. 711 (necessity and sufficiency, existence and uniqueness): a positive price
maximises constant-elasticity profit over all positive prices iff it is `θ c/(θ − 1)`. -/
theorem ce_optimal_price_iff {A θ c q : ℝ} (hA : 0 < A) (hθ : 1 < θ) (hc : 0 < c)
    (hq : 0 < q) :
    (∀ q' > 0, ceProfit A θ c q' ≤ ceProfit A θ c q) ↔ q = ceMarkupPrice θ c := by
  constructor
  · intro h
    by_contra hne
    have h1 := ceProfit_lt_markup hA hθ hc hq hne
    have h2 := h _ (ceMarkupPrice_pos hθ hc)
    linarith
  · rintro rfl q' hq'
    exact ceProfit_le_markup hA hθ hc hq'

/-- O&R p. 710 (necessity of the first-order condition for any demand curve): at an interior
local maximum of `(q − c) D(q)` with `D` differentiable, `D(p) + (p − c) D'(p) = 0`. -/
theorem foc_of_isLocalMax {D : ℝ → ℝ} {c p D' : ℝ}
    (hmax : IsLocalMax (fun q => (q - c) * D q) p) (hD : HasDerivAt D D' p) :
    D p + (p - c) * D' = 0 := by
  have h : HasDerivAt (fun q => (q - c) * D q) (1 * D p + (p - c) * D') p :=
    ((hasDerivAt_id' p).sub_const c).mul hD
  have := hmax.hasDerivAt_eq_zero h
  linarith

/-- O&R p. 710 / Box 10.2 (Lerner rule): at an interior local profit maximum with positive
sales and price, the Lerner index `(p − c)/p` equals the inverse demand elasticity
`1/ε`, `ε = −p D'(p)/D(p)`. -/
theorem lerner_rule {D : ℝ → ℝ} {c p D' : ℝ}
    (hmax : IsLocalMax (fun q => (q - c) * D q) p) (hD : HasDerivAt D D' p)
    (hDp : D p ≠ 0) (hp : p ≠ 0) :
    (p - c) / p = 1 / (-(p * D') / D p) := by
  have hfoc := foc_of_isLocalMax hmax hD
  have hD' : D' ≠ 0 := by
    intro h0
    rw [h0] at hfoc
    exact hDp (by linarith)
  have e : D p = -((p - c) * D') := by linarith
  rw [e]
  field_simp

/-- O&R p. 711: constant-elasticity demand `A q^{−θ}` has elasticity `−θ` at every `q > 0`. -/
theorem ce_demand_elasticity {A θ q : ℝ} (hA : A ≠ 0) (hq : 0 < q) :
    elasticity (fun x => A * x ^ (-θ)) q = -θ := by
  have hd : HasDerivAt (fun x => A * x ^ (-θ)) (A * (-θ * q ^ (-θ - 1))) q :=
    (Real.hasDerivAt_rpow_const (Or.inl hq.ne')).const_mul A
  rw [elasticity, hd.deriv, Real.rpow_sub_one hq.ne']
  have : 0 < q ^ (-θ) := Real.rpow_pos_of_pos hq _
  field_simp

/-- Box 10.2, p. 689 / O&R p. 710: under constant elasticity the Lerner index of the markup
price is exactly `1/θ`. -/
theorem ce_lerner_index {θ c : ℝ} (hθ : 1 < θ) (hc : 0 < c) :
    (ceMarkupPrice θ c - c) / ceMarkupPrice θ c = 1 / θ := by
  have h1 : θ - 1 ≠ 0 := by linarith
  have h2 : θ ≠ 0 := by linarith
  unfold ceMarkupPrice
  field_simp
  ring

/-- Box 10.2 / O&R p. 710: the markup factor `θ/(θ − 1)` exceeds one. -/
theorem markup_factor_gt_one {θ : ℝ} (hθ : 1 < θ) : 1 < θ / (θ - 1) := by
  rw [lt_div_iff₀ (by linarith)]
  linarith

/-- O&R p. 710: the markup factor `θ/(θ − 1)` is strictly decreasing in the elasticity. -/
theorem markup_factor_strictAntiOn : StrictAntiOn (fun θ : ℝ => θ / (θ - 1)) (Ioi 1) := by
  intro θ₁ h₁ θ₂ h₂ h
  simp only [mem_Ioi] at h₁ h₂
  simp only
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- O&R p. 710: as goods become perfect substitutes (`θ → ∞`) the markup factor tends to one
(monopoly distortion vanishes). -/
theorem markup_factor_tendsto_one :
    Tendsto (fun θ : ℝ => θ / (θ - 1)) atTop (𝓝 1) := by
  have h1 : Tendsto (fun θ : ℝ => θ + (-1)) atTop atTop :=
    tendsto_atTop_add_const_right _ (-1) tendsto_id
  have h2 : Tendsto (fun θ : ℝ => 1 + (θ + (-1))⁻¹) atTop (𝓝 (1 + 0)) :=
    tendsto_const_nhds.add (tendsto_inv_atTop_zero.comp h1)
  rw [add_zero] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with θ hθ
  have : θ - 1 ≠ 0 := by linarith
  rw [← sub_eq_add_neg, eq_div_iff this, add_mul, inv_mul_cancel₀ this]
  ring

/-- O&R (10) with `Model.cesDemand`: CES demand `(q/P)^{−θ} C` is the constant-elasticity demand
`A q^{−θ}` with `A = P^θ C`. -/
theorem cesDemand_eq_const_elast {θ q P C : ℝ} (hq : 0 < q) (hP : 0 < P) :
    cesDemand θ q P C = P ^ θ * C * q ^ (-θ) := by
  unfold cesDemand
  rw [Real.div_rpow hq.le hP.le, Real.rpow_neg hP.le, div_inv_eq_mul]
  ring

/-- O&R (144), p. 711, with the book's CES demand (10): a positive price maximises
`(q − c)(q/P)^{−θ} C` over positive prices iff it equals `θ c/(θ − 1)`, independent of the
price index `P` and of spending `C`. -/
theorem cesDemand_optimal_price_iff {θ c P C q : ℝ} (hθ : 1 < θ) (hc : 0 < c) (hP : 0 < P)
    (hC : 0 < C) (hq : 0 < q) :
    (∀ q' > 0, (q' - c) * cesDemand θ q' P C ≤ (q - c) * cesDemand θ q P C) ↔
      q = ceMarkupPrice θ c := by
  have hA : 0 < P ^ θ * C := mul_pos (Real.rpow_pos_of_pos hP θ) hC
  rw [← ce_optimal_price_iff hA hθ hc hq]
  constructor
  · intro h q' hq'
    have := h q' hq'
    rw [cesDemand_eq_const_elast hq' hP, cesDemand_eq_const_elast hq hP] at this
    unfold ceProfit
    linarith
  · intro h q' hq'
    have := h q' hq'
    rw [cesDemand_eq_const_elast hq' hP, cesDemand_eq_const_elast hq hP]
    unfold ceProfit at this
    linarith

/-- O&R p. 711: Home-currency export profit is `𝓔` times Foreign-currency profit with the
Foreign-currency marginal cost `w/𝓔`. -/
theorem exportProfit_eq {A θ w E q : ℝ} (hE : E ≠ 0) :
    exportProfit A θ w E q = E * ceProfit A θ (w / E) q := by
  unfold exportProfit ceProfit
  field_simp

/-- O&R p. 711: the markup price at Foreign-currency cost `w/𝓔` is `(θ w/(θ − 1))/𝓔`. -/
theorem ceMarkupPrice_div (θ w E : ℝ) : ceMarkupPrice θ (w / E) = ceMarkupPrice θ w / E := by
  unfold ceMarkupPrice
  ring

/-- O&R (144), p. 711 (necessity and sufficiency): with linear production and constant
elasticities `θH`, `θF` in segmented markets, `(p, p*)` maximises Home-currency profit over
positive prices iff `p = θH w/(θH − 1)` and `p* = (θF w/(θF − 1))/𝓔`. -/
theorem ptm_optimal_prices_iff {AH AF θH θF w E p q : ℝ} (hAH : 0 < AH) (hAF : 0 < AF)
    (hθH : 1 < θH) (hθF : 1 < θF) (hw : 0 < w) (hE : 0 < E) (hp : 0 < p) (hq : 0 < q) :
    (∀ p' > 0, ∀ q' > 0,
        segmentedProfit (fun x => AH * x ^ (-θH)) (fun x => AF * x ^ (-θF)) w E p' q' ≤
          segmentedProfit (fun x => AH * x ^ (-θH)) (fun x => AF * x ^ (-θF)) w E p q) ↔
      p = ceMarkupPrice θH w ∧ q = ceMarkupPrice θF w / E := by
  have hsep := segmented_optimum_iff (fun x => AH * x ^ (-θH)) (fun x => AF * x ^ (-θF)) w E
    (Ioi 0) (Ioi 0) (mem_Ioi.2 hp) (mem_Ioi.2 hq)
  simp only [mem_Ioi] at hsep
  rw [hsep]
  have hH := ce_optimal_price_iff hAH hθH hw hp
  have hF := ce_optimal_price_iff hAF hθF (div_pos hw hE) hq
  rw [ceMarkupPrice_div] at hF
  rw [← hH, ← hF]
  apply and_congr
  · rfl
  · constructor
    · intro h q' hq'
      have := h q' hq'
      have e1 := exportProfit_eq (A := AF) (θ := θF) (w := w) (q := q') hE.ne'
      have e2 := exportProfit_eq (A := AF) (θ := θF) (w := w) (q := q) hE.ne'
      unfold exportProfit at e1 e2
      rw [e1, e2] at this
      exact le_of_mul_le_mul_left this hE
    · intro h q' hq'
      have := mul_le_mul_of_nonneg_left (h q' hq') hE.le
      have e1 := exportProfit_eq (A := AF) (θ := θF) (w := w) (q := q') hE.ne'
      have e2 := exportProfit_eq (A := AF) (θ := θF) (w := w) (q := q) hE.ne'
      unfold exportProfit at e1 e2
      rw [e1, e2]
      exact this

/-- O&R (144), p. 711: with EQUAL elasticities in both markets the discriminating monopolist's
prices satisfy the law of one price, `p(h) = 𝓔 p*(h) = θ w/(θ − 1)`. -/
theorem ptm_loop_of_equal_elasticity (θ w : ℝ) {E : ℝ} (hE : E ≠ 0) :
    ceMarkupPrice θ w = E * (ceMarkupPrice θ w / E) := by
  field_simp

/-- O&R p. 711: "if the constant elasticity of demand is different in the two markets, the
levels of prices will differ": LOOP `p = 𝓔 p*` holds at the optimum iff `θH = θF`. -/
theorem ptm_loop_iff {θH θF w E : ℝ} (hθH : 1 < θH) (hθF : 1 < θF) (hw : 0 < w)
    (hE : E ≠ 0) :
    ceMarkupPrice θH w = E * (ceMarkupPrice θF w / E) ↔ θH = θF := by
  have h1 : θH - 1 ≠ 0 := by linarith
  have h2 : θF - 1 ≠ 0 := by linarith
  rw [mul_div_cancel₀ _ hE]
  unfold ceMarkupPrice
  constructor
  · intro h
    rw [div_eq_div_iff h1 h2] at h
    nlinarith
  · rintro rfl
    rfl

/-! ## Pass-through elasticities -/

/-- Elasticity of `x ↦ u + v/x` (O&R p. 711, the common form of every optimal Foreign-currency
price below): `−(v/x)/(u + v/x)`. -/
theorem elasticity_const_add_div {u v E : ℝ} (hE : E ≠ 0) :
    elasticity (fun x => u + v / x) E = -(v / E) / (u + v / E) := by
  have hd : HasDerivAt (fun x => u + v / x) ((0 * E - v * 1) / E ^ 2) E :=
    ((hasDerivAt_const E v).div (hasDerivAt_id' E) hE).const_add u
  rw [elasticity, hd.deriv]
  field_simp
  ring

/-- O&R p. 711 ("complete exchange-rate pass-through"): under constant elasticity the optimal
Foreign-currency price `(θ w/(θ − 1))/𝓔` has elasticity exactly `−1` with respect to `𝓔`. -/
theorem ce_passThrough_elasticity {θ w E : ℝ} (hθ : 1 < θ) (hw : 0 < w) (hE : 0 < E) :
    elasticity (fun x => ceMarkupPrice θ w / x) E = -1 := by
  have hk := ceMarkupPrice_pos hθ hw
  have e : (fun x => ceMarkupPrice θ w / x) = fun x => 0 + ceMarkupPrice θ w / x := by
    funext x; ring
  have hne : (0 : ℝ) + ceMarkupPrice θ w / E ≠ 0 := by
    rw [zero_add]; exact (div_pos hk hE).ne'
  rw [e, elasticity_const_add_div hE.ne', zero_add]
  field_simp

/-- O&R p. 711 (discrete, exact): under constant elasticity the Foreign-currency price moves
exactly in inverse proportion to `𝓔`: `p*(𝓔') = p*(𝓔)·𝓔/𝓔'`. -/
theorem ce_passThrough_exact (θ w : ℝ) {E E' : ℝ} (hE : E ≠ 0) (hE' : E' ≠ 0) :
    ceMarkupPrice θ w / E' = ceMarkupPrice θ w / E * (E / E') := by
  field_simp

/-- O&R (144): the Home-currency price of exports `𝓔 p*` is independent of `𝓔` under constant
elasticity (the whole exchange-rate change is passed through). -/
theorem ce_home_currency_export_price (θ w : ℝ) {E : ℝ} (hE : E ≠ 0) :
    E * (ceMarkupPrice θ w / E) = θ * w / (θ - 1) := by
  unfold ceMarkupPrice
  field_simp

/-! ## Linear demand: incomplete pass-through -/

/-- O&R p. 712: the linear-demand profit gap is `b (q − (α/b + c)/2)²`. -/
theorem linProfit_gap {α b c : ℝ} (hb : b ≠ 0) (q : ℝ) :
    linProfit α b c (linPrice α b c) - linProfit α b c q = b * (q - linPrice α b c) ^ 2 := by
  unfold linProfit linPrice
  field_simp
  ring

/-- O&R p. 712 (necessity and sufficiency, existence and uniqueness): under linear demand
`α − b q` with `b > 0` a price maximises profit iff it equals `(α/b + c)/2`. -/
theorem lin_optimal_price_iff {α b c q : ℝ} (hb : 0 < b) :
    (∀ q', linProfit α b c q' ≤ linProfit α b c q) ↔ q = linPrice α b c := by
  constructor
  · intro h
    have h1 := h (linPrice α b c)
    have h2 := linProfit_gap hb.ne' (c := c) (α := α) q
    have h3 : b * (q - linPrice α b c) ^ 2 ≤ 0 := by linarith
    have h4 : (q - linPrice α b c) ^ 2 = 0 := by
      have := sq_nonneg (q - linPrice α b c)
      nlinarith
    have := pow_eq_zero_iff (n := 2) two_ne_zero |>.1 h4
    linarith
  · rintro rfl q'
    have h2 := linProfit_gap hb.ne' (c := c) (α := α) q'
    have := mul_nonneg hb.le (sq_nonneg (q' - linPrice α b c))
    linarith

/-- O&R p. 712: when marginal cost is below the choke price (`c < α/b`) the optimal price lies
strictly between cost and the choke price, so sales and the margin are positive. -/
theorem linPrice_bounds {α b c : ℝ} (hc : c < α / b) :
    c < linPrice α b c ∧ linPrice α b c < α / b := by
  unfold linPrice
  constructor <;> linarith

/-- O&R p. 712: the optimal Foreign-currency price under linear demand, `(α/b + w/𝓔)/2`, has
pass-through elasticity `−(w/𝓔)/(α/b + w/𝓔)`. -/
theorem lin_passThrough_elasticity {α b w E : ℝ} (hα : 0 < α) (hb : 0 < b) (hw : 0 < w)
    (hE : 0 < E) :
    elasticity (fun x => linPrice α b (w / x)) E = -(w / E) / (α / b + w / E) := by
  have e : (fun x => linPrice α b (w / x)) = fun x => α / b / 2 + w / 2 / x := by
    funext x; unfold linPrice; ring
  have hpos : 0 < α / b / 2 + w / 2 / E := by positivity
  rw [e, elasticity_const_add_div hE.ne']
  have : 0 < α / b + w / E := by positivity
  field_simp

/-- O&R p. 712 ("pass-through is less than one for one"): with linear demand and positive
sales the pass-through elasticity lies strictly between `−1/2` and `0`; in particular it is
incomplete, and in fact at most one half in absolute value. -/
theorem lin_passThrough_bounds {α b w E : ℝ} (hw : 0 < w) (hE : 0 < E)
    (hc : w / E < α / b) :
    -(1 / 2 : ℝ) < -(w / E) / (α / b + w / E) ∧ -(w / E) / (α / b + w / E) < 0 := by
  have hc0 : 0 < w / E := div_pos hw hE
  have hs : 0 < α / b + w / E := by linarith
  constructor
  · rw [neg_div, neg_lt_neg_iff, div_lt_iff₀ hs]
    linarith
  · rw [neg_div, neg_lt_zero]
    exact div_pos hc0 hs

/-- O&R p. 712 (comparative statics): the size of linear-demand pass-through `c/(α/b + c)`
is strictly increasing in the Foreign-currency marginal cost `c`. -/
theorem lin_passThrough_strictMonoOn_cost {a : ℝ} (ha : 0 < a) :
    StrictMonoOn (fun c : ℝ => c / (a + c)) (Ioi 0) := by
  intro c₁ h₁ c₂ h₂ h
  simp only [mem_Ioi] at h₁ h₂
  simp only
  rw [div_lt_div_iff₀ (by linarith) (by linarith)]
  nlinarith

/-- O&R p. 712: as the exporter's currency depreciates (`𝓔` rises, so `w/𝓔` falls) the size of
linear-demand pass-through strictly falls. -/
theorem lin_passThrough_strictAntiOn_exchange_rate {a w : ℝ} (ha : 0 < a) (hw : 0 < w) :
    StrictAntiOn (fun E : ℝ => w / E / (a + w / E)) (Ioi 0) := by
  intro E₁ h₁ E₂ h₂ h
  simp only [mem_Ioi] at h₁ h₂
  have hlt : w / E₂ < w / E₁ := div_lt_div_of_pos_left hw h₁ h
  exact lin_passThrough_strictMonoOn_cost ha (mem_Ioi.2 (div_pos hw h₂))
    (mem_Ioi.2 (div_pos hw h₁)) hlt

/-- O&R p. 712: the demand elasticity `−q D'(q)/D(q)` of linear demand at the optimal price is
`(α/b + c)/(α/b − c)`. -/
theorem lin_demand_elasticity_at_optimum {α b c : ℝ} (hb : 0 < b) (hc : c < α / b) :
    -elasticity (fun q => α - b * q) (linPrice α b c) = (α / b + c) / (α / b - c) := by
  have hd : HasDerivAt (fun q => α - b * q) (-(b * 1)) (linPrice α b c) :=
    ((hasDerivAt_id' (linPrice α b c)).const_mul b).const_sub α
  have h1 : α / b - c ≠ 0 := by linarith
  have hα : α = b * (α / b) := by field_simp
  rw [elasticity, hd.deriv]
  unfold linPrice
  have hne : α - b * ((α / b + c) / 2) ≠ 0 := by
    rw [hα]
    have : b * (α / b) - b * ((b * (α / b) / b + c) / 2) = b * (α / b - c) / 2 := by
      field_simp; ring
    rw [this]
    positivity
  have e : α - b * ((α / b + c) / 2) = b * (α / b - c) / 2 := by
    conv_lhs => rw [hα]
    field_simp
    ring
  rw [e]
  field_simp

/-- O&R p. 712 ("an appreciation of the dollar may reduce the elasticity of U.S. demand for
imports"): at the linear-demand optimum the demand elasticity exceeds one and is strictly
increasing in the Foreign-currency marginal cost `w/𝓔`, so it falls when the importer's
currency appreciates. -/
theorem lin_optimal_demand_elasticity_props {a : ℝ} (ha : 0 < a) :
    (∀ c ∈ Ioo 0 a, 1 < (a + c) / (a - c)) ∧
      StrictMonoOn (fun c : ℝ => (a + c) / (a - c)) (Ioo 0 a) := by
  constructor
  · rintro c ⟨h0, h1⟩
    rw [lt_div_iff₀ (by linarith)]
    linarith
  · rintro c₁ ⟨h₁, h₁'⟩ c₂ ⟨h₂, h₂'⟩ h
    simp only
    rw [div_lt_div_iff₀ (by linarith) (by linarith)]
    nlinarith

/-- O&R p. 712 (German cars, early 1980s, discrete and exact): with linear demand, when `𝓔`
rises from `E` to `E'` the Foreign-currency price falls, but strictly less than in proportion:
`p(E)·E/E' < p(E') < p(E)`. -/
theorem lin_price_falls_less_than_proportionally {α b w E E' : ℝ} (hα : 0 < α) (hb : 0 < b)
    (hw : 0 < w) (hE : 0 < E) (hEE' : E < E') :
    linPrice α b (w / E) * (E / E') < linPrice α b (w / E') ∧
      linPrice α b (w / E') < linPrice α b (w / E) := by
  have hE' : 0 < E' := by linarith
  have ha : 0 < α / b := div_pos hα hb
  unfold linPrice
  constructor
  · rw [show (α / b + w / E) / 2 * (E / E') = (α / b * E + w) / E' / 2 by field_simp]
    rw [show (α / b + w / E') / 2 = (α / b * E' + w) / E' / 2 by field_simp]
    have : (α / b * E + w) / E' < (α / b * E' + w) / E' := by
      apply div_lt_div_of_pos_right _ hE'
      nlinarith
    linarith
  · have : w / E' < w / E := div_lt_div_of_pos_left hw hE hEE'
    linarith

/-! ## Markups and nominal shocks -/

/-- O&R p. 712 ("monetary shocks will not affect the real markups ... unless there is some type
of nominal rigidity"), Foreign market, ANY demand curve: scaling the Home wage and the exchange
rate by the same `μ > 0` leaves the set of optimal Foreign-currency prices unchanged. -/
theorem foreign_optimum_invariant_to_nominal_scaling (D : ℝ → ℝ) (S : Set ℝ) {w E μ q : ℝ}
    (hμ : 0 < μ) :
    (∀ q' ∈ S, (E * q' - w) * D q' ≤ (E * q - w) * D q) ↔
      (∀ q' ∈ S, (μ * E * q' - μ * w) * D q' ≤ (μ * E * q - μ * w) * D q) := by
  have e : ∀ x, (μ * E * x - μ * w) * D x = μ * ((E * x - w) * D x) := fun x => by ring
  simp only [e]
  constructor
  · intro h q' hq'
    exact mul_le_mul_of_nonneg_left (h q' hq') hμ.le
  · intro h q' hq'
    exact le_of_mul_le_mul_left (h q' hq') hμ

/-- O&R p. 712: under a proportional nominal shock the real (price-over-cost) markup of an
exporter who keeps the optimal Foreign-currency price is unchanged. -/
theorem markup_invariant_to_nominal_scaling {w E μ q : ℝ} (hμ : 0 < μ) :
    μ * E * q / (μ * w) = E * q / w := by
  rw [mul_assoc, mul_div_mul_left _ _ hμ.ne']

/-- O&R p. 712, Home market, ANY demand curve in the real price `p/P`: `p` is an optimal nominal
price when wage and price level are `(w, P)` iff `μ p` is optimal at `(μ w, μ P)`; real prices and
markups are unaffected by monetary shocks absent nominal rigidity. -/
theorem home_optimum_homogeneous (D : ℝ → ℝ) {w P μ p : ℝ} (hμ : 0 < μ) :
    (∀ p' > 0, (p' - w) * D (p' / P) ≤ (p - w) * D (p / P)) ↔
      (∀ p' > 0, (p' - μ * w) * D (p' / (μ * P)) ≤
        (μ * p - μ * w) * D (μ * p / (μ * P))) := by
  have hR : ∀ x, μ * x / (μ * P) = x / P := fun x => mul_div_mul_left x P hμ.ne'
  constructor
  · intro h p' hp'
    have h1 := h (p' / μ) (div_pos hp' hμ)
    have e1 : p' / (μ * P) = p' / μ / P := by rw [div_div]
    have e2 : p' - μ * w = μ * (p' / μ - w) := by field_simp
    have e3 : μ * p - μ * w = μ * (p - w) := by ring
    rw [e1, e2, e3, hR, mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_left h1 hμ.le
  · intro h p' hp'
    have h1 := h (μ * p') (mul_pos hμ hp')
    rw [hR, hR, show μ * p' - μ * w = μ * (p' - w) by ring,
      show μ * p - μ * w = μ * (p - w) by ring, mul_assoc, mul_assoc] at h1
    exact le_of_mul_le_mul_left h1 hμ

/-- O&R pp. 711–712 (nominal wage rigidity, constant elasticity): with the wage `w̄` preset, the
real markup `𝓔 p*/w̄` of the flexible-price exporter is `θ/(θ − 1)` at every exchange rate. -/
theorem ce_markup_invariant_rigid_wage {θ w E : ℝ} (hw : w ≠ 0) (hE : E ≠ 0) :
    E * (ceMarkupPrice θ w / E) / w = θ / (θ - 1) := by
  unfold ceMarkupPrice
  field_simp

/-- O&R p. 712 (nominal wage rigidity, linear demand): with `w̄` preset the real markup
`𝓔 p*/w̄ = (α𝓔/(b w̄) + 1)/2` is strictly increasing in `𝓔`, so a monetary shock that moves the
exchange rate moves the markup (pricing to market). -/
theorem lin_markup_strictMonoOn_rigid_wage {α b w : ℝ} (hα : 0 < α) (hb : 0 < b) (hw : 0 < w) :
    StrictMonoOn (fun E => E * linPrice α b (w / E) / w) (Ioi 0) := by
  intro E₁ h₁ E₂ h₂ h
  simp only [mem_Ioi] at h₁ h₂
  have e : ∀ E, 0 < E → E * linPrice α b (w / E) / w = (α / b * E / w + 1) / 2 := by
    intro E hE
    unfold linPrice
    field_simp
  simp only
  rw [e E₁ h₁, e E₂ h₂]
  have : α / b * E₁ / w < α / b * E₂ / w := by
    apply div_lt_div_of_pos_right _ hw
    exact mul_lt_mul_of_pos_left h (div_pos hα hb)
  linarith

/-! ## Producer-currency vs local-currency pricing -/

/-- O&R pp. 674–675, 711 (producer-currency pricing): with the Home-currency price `p̄` preset,
the Foreign-currency price `p̄/𝓔` has pass-through elasticity exactly `−1`. -/
theorem pcp_passThrough_elasticity {pbar E : ℝ} (hp : 0 < pbar) (hE : 0 < E) :
    elasticity (fun x => pbar / x) E = -1 := by
  have e : (fun x => pbar / x) = fun x => 0 + pbar / x := by funext x; ring
  have hne : (0 : ℝ) + pbar / E ≠ 0 := by rw [zero_add]; exact (div_pos hp hE).ne'
  rw [e, elasticity_const_add_div hE.ne', zero_add]
  have : pbar / E ≠ 0 := (div_pos hp hE).ne'
  field_simp

/-- O&R p. 711 (local-currency pricing): with the Foreign-currency price `q̄` preset, pass-through
to import prices is zero. -/
theorem lcp_passThrough_elasticity (qbar E : ℝ) : elasticity (fun _ => qbar) E = 0 := by
  simp [elasticity]

/-- O&R p. 711 (PCP): with `p̄ = θ w/(θ − 1)` preset in Home currency, the exporter's real markup
is `θ/(θ − 1)` whatever the exchange rate. -/
theorem pcp_markup {θ w E : ℝ} (hw : w ≠ 0) (hE : E ≠ 0) :
    E * (ceMarkupPrice θ w / E) / w = θ / (θ - 1) :=
  ce_markup_invariant_rigid_wage hw hE

/-- O&R p. 711 (LCP): with `q̄ = (θ w/(θ − 1))/𝓔₀` preset in Foreign currency, the real markup at
`𝓔` is `(𝓔/𝓔₀)·θ/(θ − 1)`: a depreciation is absorbed in the markup. -/
theorem lcp_markup {θ w E E0 : ℝ} (hw : w ≠ 0) (hE0 : E0 ≠ 0) :
    E * (ceMarkupPrice θ w / E0) / w = E / E0 * (θ / (θ - 1)) := by
  unfold ceMarkupPrice
  field_simp

/-- O&R pp. 675, 711 (PCP expenditure switching): with the Home-currency price preset, Foreign
sales `A (p̄/𝓔)^{−θ}` are strictly increasing in `𝓔`. (Under LCP they are constant.) -/
theorem pcp_sales_strictMonoOn {A θ pbar : ℝ} (hA : 0 < A) (hθ : 0 < θ) (hp : 0 < pbar) :
    StrictMonoOn (fun E => A * (pbar / E) ^ (-θ)) (Ioi 0) := by
  intro E₁ h₁ E₂ h₂ h
  simp only [mem_Ioi] at h₁ h₂
  simp only
  have hlt : pbar / E₂ < pbar / E₁ := div_lt_div_of_pos_left hp h₁ h
  have := Real.rpow_lt_rpow_of_neg (div_pos hp h₂) hlt (neg_lt_zero.2 hθ)
  exact mul_lt_mul_of_pos_left this hA

/-- O&R p. 674 applied to LCP exporters: at the preset Foreign-currency price `q̄ =
(θ w/(θ − 1))/𝓔₀` the exporter is willing to meet demand (price ≥ marginal cost in Home
currency) iff `𝓔/𝓔₀ ≥ (θ − 1)/θ`: an appreciation of more than the factor `(θ − 1)/θ` makes
marginal sales unprofitable. -/
theorem lcp_meets_demand_iff {θ w E E0 : ℝ} (hθ : 1 < θ) (hw : 0 < w) (hE0 : 0 < E0) :
    w ≤ E * (ceMarkupPrice θ w / E0) ↔ (θ - 1) / θ ≤ E / E0 := by
  have h1 : 0 < θ - 1 := by linarith
  have e : E * (ceMarkupPrice θ w / E0) = w * (θ / (θ - 1) * (E / E0)) := by
    unfold ceMarkupPrice; field_simp
  rw [e, le_mul_iff_one_le_right hw, div_le_iff₀ (by linarith : (0 : ℝ) < θ),
    ← mul_le_mul_iff_of_pos_left h1]
  constructor
  · intro h
    have : θ / (θ - 1) * (E / E0) * (θ - 1) = θ * (E / E0) := by field_simp
    nlinarith
  · intro h
    have : (θ - 1) * (θ / (θ - 1) * (E / E0)) = θ * (E / E0) := by field_simp
    nlinarith

/-- O&R p. 674 (envelope argument), exporter version: the profit forgone by keeping the preset
LCP price is nonnegative at every `𝓔 > 0`. -/
theorem lcpLoss_nonneg {A θ w E0 E : ℝ} (hA : 0 < A) (hθ : 1 < θ) (hw : 0 < w)
    (hE0 : 0 < E0) (hE : 0 < E) : 0 ≤ lcpLoss A θ w E0 E := by
  unfold lcpLoss
  rw [exportProfit_eq hE.ne', exportProfit_eq hE.ne', ← ceMarkupPrice_div]
  have := ceProfit_le_markup hA hθ (div_pos hw hE) (div_pos (ceMarkupPrice_pos hθ hw) hE0)
    (A := A)
  nlinarith

/-- O&R p. 674, exporter version: the forgone profit is strictly positive whenever the exchange
rate differs from the one the price was set for. -/
theorem lcpLoss_pos {A θ w E0 E : ℝ} (hA : 0 < A) (hθ : 1 < θ) (hw : 0 < w)
    (hE0 : 0 < E0) (hE : 0 < E) (hne : E ≠ E0) : 0 < lcpLoss A θ w E0 E := by
  unfold lcpLoss
  rw [exportProfit_eq hE.ne', exportProfit_eq hE.ne', ← ceMarkupPrice_div]
  have hk := ceMarkupPrice_pos hθ hw
  have hq : ceMarkupPrice θ w / E0 ≠ ceMarkupPrice θ (w / E) := by
    rw [ceMarkupPrice_div]
    intro h
    rw [div_eq_div_iff hE0.ne' hE.ne'] at h
    exact hne (mul_left_cancel₀ hk.ne' h)
  have := ceProfit_lt_markup hA hθ (div_pos hw hE) (div_pos hk hE0) hq
  nlinarith

/-- O&R p. 674, exporter version: at the exchange rate the price was set for, nothing is lost. -/
theorem lcpLoss_self (A θ w E0 : ℝ) : lcpLoss A θ w E0 E0 = 0 := by
  simp [lcpLoss]

/-- O&R p. 674 ("the envelope theorem implies that small changes in an individual's price will
have only a second-order impact"), exporter version: the forgone profit has derivative zero at
`𝓔₀`, so it is `o(𝓔 − 𝓔₀)`. -/
theorem lcpLoss_hasDerivAt_zero {A θ w E0 : ℝ} (hA : 0 < A) (hθ : 1 < θ) (hw : 0 < w)
    (hE0 : 0 < E0) : HasDerivAt (lcpLoss A θ w E0) 0 E0 := by
  set k := ceMarkupPrice θ w with hkdef
  have hk : 0 < k := ceMarkupPrice_pos hθ hw
  have h1 : HasDerivAt (fun E => k / E) ((0 * E0 - k * 1) / E0 ^ 2) E0 :=
    (hasDerivAt_const E0 k).div (hasDerivAt_id' E0) hE0.ne'
  have h2 := h1.rpow_const (p := -θ) (Or.inl (div_pos hk hE0).ne')
  have h3 := (((hasDerivAt_id' E0).mul h1).sub_const w).mul (h2.const_mul A)
  have h4 := h3.sub ((((hasDerivAt_id' E0).mul_const (k / E0)).sub_const w).mul_const
    (A * (k / E0) ^ (-θ)))
  obtain ⟨D, hL⟩ : ∃ D, HasDerivAt (lcpLoss A θ w E0) D E0 :=
    ⟨_, by unfold lcpLoss exportProfit; exact h4⟩
  have hmin : IsLocalMin (lcpLoss A θ w E0) E0 := by
    filter_upwards [Ioi_mem_nhds hE0] with E hE
    rw [lcpLoss_self]
    exact lcpLoss_nonneg hA hθ hw hE0 hE
  have h0 := hmin.hasDerivAt_eq_zero hL
  rw [h0] at hL
  exact hL

/-- O&R p. 674 (menu costs), exporter version: for every menu cost `Z > 0` there is a
neighbourhood of `𝓔₀` on which the profit forgone by not repricing is below `Z`, so keeping the
preset LCP price is optimal for small enough exchange-rate shocks. -/
theorem lcp_menu_cost_neighbourhood {A θ w E0 Z : ℝ} (hA : 0 < A) (hθ : 1 < θ) (hw : 0 < w)
    (hE0 : 0 < E0) (hZ : 0 < Z) : ∀ᶠ E in 𝓝 E0, lcpLoss A θ w E0 E < Z := by
  have hc := (lcpLoss_hasDerivAt_zero hA hθ hw hE0).continuousAt
  have : lcpLoss A θ w E0 E0 < Z := by rw [lcpLoss_self]; exact hZ
  exact hc.eventually (gt_mem_nhds this)

/-! ## Local distribution costs -/

/-- O&R p. 712 ("most traded goods contain substantial nontraded inputs, including local
transportation ... retail costs", Ch. 4): with a local-currency distribution cost `d` per unit
and constant-elasticity demand in the retail price, the optimal retail price
`θ(w/𝓔 + d)/(θ − 1)` has pass-through elasticity `−(w/𝓔)/(w/𝓔 + d)`. -/
theorem retail_passThrough_elasticity {θ w d E : ℝ} (hθ : 1 < θ) (hw : 0 < w) (hd : 0 ≤ d)
    (hE : 0 < E) :
    elasticity (fun x => ceMarkupPrice θ (w / x + d)) E = -(w / E) / (w / E + d) := by
  have h1 : 0 < θ - 1 := by linarith
  have e : (fun x => ceMarkupPrice θ (w / x + d)) =
      fun x => θ * d / (θ - 1) + θ * w / (θ - 1) / x := by
    funext x; unfold ceMarkupPrice; ring
  have hpos : 0 < θ * d / (θ - 1) + θ * w / (θ - 1) / E := by
    have : 0 < θ * w / (θ - 1) / E := by
      have : 0 < θ := by linarith
      positivity
    have : 0 ≤ θ * d / (θ - 1) := by
      have : 0 ≤ θ := by linarith
      positivity
    linarith
  rw [e, elasticity_const_add_div hE.ne']
  have : 0 < w / E + d := by have := div_pos hw hE; linarith
  have : θ ≠ 0 := by linarith
  field_simp
  ring

/-- O&R p. 712: with a positive local distribution cost pass-through is incomplete,
`−1 < −(w/𝓔)/(w/𝓔 + d) < 0`; it is complete (`−1`) iff `d = 0`. -/
theorem retail_passThrough_bounds {w d E : ℝ} (hw : 0 < w) (hE : 0 < E) (hd : 0 ≤ d) :
    (-1 ≤ -(w / E) / (w / E + d) ∧ -(w / E) / (w / E + d) < 0) ∧
      (-(w / E) / (w / E + d) = -1 ↔ d = 0) := by
  have hc : 0 < w / E := div_pos hw hE
  have hs : 0 < w / E + d := by linarith
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [neg_div, neg_le_neg_iff, div_le_one hs]
    linarith
  · rw [neg_div, neg_lt_zero]
    exact div_pos hc hs
  · rw [neg_div, neg_inj, div_eq_one_iff_eq hs.ne']
    constructor
    · intro h; linarith
    · intro h; rw [h, add_zero]

end ObstfeldRogoff.StickyPriceModels.PassThrough
