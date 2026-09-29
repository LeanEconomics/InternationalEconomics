import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.FinCases
set_option autoImplicit false

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# CES demand for a differentiated good

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*,
§10.1.1, pp. 661–663. With elasticity of substitution `θ`, demand for a good priced
`p` relative to the price index `P` is `y = (p/P)^{−θ} C`.
-/

namespace ObstfeldRogoff.StickyPriceModels

/-- CES demand `(p/P)^{−θ} C` for a differentiated good (O&R (10.x), §10.1.1). -/
noncomputable def cesDemand (θ p P C : ℝ) : ℝ := (p / P) ^ (-θ) * C

/-- At the price index, demand equals aggregate consumption (O&R §10.1.1). -/
theorem cesDemand_at_index (θ : ℝ) {P : ℝ} (hP : P ≠ 0) (C : ℝ) :
    cesDemand θ P P C = C := by
  simp [cesDemand, div_self hP]

/-- Demand is positive for positive prices and consumption (O&R §10.1.1). -/
theorem cesDemand_pos (θ : ℝ) {p P C : ℝ} (hp : 0 < p) (hP : 0 < P) (hC : 0 < C) :
    0 < cesDemand θ p P C :=
  mul_pos (Real.rpow_pos_of_pos (div_pos hp hP) _) hC

end ObstfeldRogoff.StickyPriceModels

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The two-country redux model: primitives

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §10.1.1–§10.1.4,
pp. 659–669. This module holds everything the later `Redux*` modules share.

* **CES duality** (eqs. (2), (3), fn 4, fn 6): on a finite set of goods with positive weights
  (the within-bloc symmetric version of the continuum `[0, 1]`), for `θ > 1` the price index
  `P = [Σ wᵢ pᵢ^{1−θ}]^{1/(1−θ)}` is the minimum cost of one unit of the index
  `C = [Σ wᵢ cᵢ^{(θ−1)/θ}]^{θ/(θ−1)}` and the demands `cᵢ = (pᵢ/P)^{−θ} C` are the UNIQUE
  cost-minimising (and, for given expenditure, the unique utility-maximising) bundle
  (`ces_expenditure_ge`, `ces_expenditure_eq_iff`, `ces_minimum_cost`, `ces_utility_max`);
  homogeneity and PPP from the law of one price (eqs. (4)–(7)); the bloc forms (5)–(6).
* **World demand** (10)–(11) and the revenue identity used to write the household problem
  as (12): with `y = (p/P)^{−θ} Cᵂ`, real revenue is `y^{(θ−1)/θ} (Cᵂ)^{1/θ}`.
* **The household problem with a genuine infinite horizon** (eqs. (8), (12)–(16), T2). The
  discount factor of (16), never defined in the book, is `R_T = Π_{s=1}^{T} (1 + r_s)^{−1}`
  (`marketDiscount`). Real wealth `W_t = (1 + r_t)B_t + M_{t−1}/P_t` evolves as
  `W_{t+1} = (1 + r_{t+1})(W_t − x_t)` with the period outlay
  `x_t = C_t + ι_t m_t + τ_t − Z_t y_t^{(θ−1)/θ}` (`wealth_of_budget`), `ι` the user cost of money
  and `Z_t = (Cᵂ_t)^{1/θ}`. Admissible plans satisfy the no-Ponzi condition
  `liminf R_T W_T ≥ 0`. We prove: **a plan is optimal IFF it satisfies (13), (14), (15) and the
  transversality condition `liminf R_T W_T ≤ 0`** (`isOptimal_iff`): sufficiency against every
  no-Ponzi rival by concavity; necessity of each first-order condition by one-period
  perturbations; necessity of the TVC by consuming more at date 0. The book's TVC (16) is
  related to ours by an exact identity (`book_tvc_identity`).
* **Aggregation** (17)–(18), fn 8 (T3): per-capita budgets, government budgets and bond-market
  clearing give `Cᵂ = Yᵂ`; the Walras identity from the price index.
* **Steady-state interest and income** (19)–(21) (T4), derived with the TVC.
* Shared parameter bundles: `ReduxParams` (the nonlinear model) and `ReduxLinear` (the
  log-linear model, with `D = θ(δ(1+θ)+2)` and `E = δ(1+θ)+2`).
-/

namespace ObstfeldRogoff.StickyPriceModels.ReduxPrimitives

open Real Filter Topology Set

/-! ## CES duality on a finite set of goods -/

/-- The strict tangent-line inequality for `x ↦ x^ρ`, `0 < ρ < 1` (the strict concavity used in
the CES duality of O&R fn 4 and fn 6, p. 662 and p. 664): for `a > 0`, `x ≥ 0`, `x ≠ a`,
`x^ρ < a^ρ + ρ a^{ρ−1}(x − a)`. -/
theorem rpow_lt_tangent {ρ a x : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (ha : 0 < a) (hx : 0 ≤ x)
    (hxa : x ≠ a) : x ^ ρ < a ^ ρ + ρ * a ^ (ρ - 1) * (x - a) := by
  have hs : -1 ≤ x / a - 1 := by have := div_nonneg hx ha.le; linarith
  have hs' : x / a - 1 ≠ 0 := by
    intro h
    apply hxa
    have : x / a = 1 := by linarith
    field_simp at this
    linarith
  have hb := rpow_one_add_lt_one_add_mul_self hs hs' hρ0 hρ1
  have hx' : x = a * (1 + (x / a - 1)) := by field_simp; ring
  have hpow : x ^ ρ = a ^ ρ * (1 + (x / a - 1)) ^ ρ := by
    conv_lhs => rw [hx']
    rw [mul_rpow ha.le (by linarith)]
  have hapos : 0 < a ^ ρ := rpow_pos_of_pos ha ρ
  have hsub : a ^ (ρ - 1) = a ^ ρ / a := rpow_sub_one ha.ne' ρ
  rw [hpow, hsub]
  have key : a ^ ρ * (1 + ρ * (x / a - 1)) = a ^ ρ + ρ * (a ^ ρ / a) * (x - a) := by
    field_simp
  rw [← key]
  exact mul_lt_mul_of_pos_left hb hapos

/-- The weak tangent-line inequality for `x ↦ x^ρ`, `0 < ρ < 1` (O&R fn 4, p. 662). -/
theorem rpow_le_tangent {ρ a x : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (ha : 0 < a) (hx : 0 ≤ x) :
    x ^ ρ ≤ a ^ ρ + ρ * a ^ (ρ - 1) * (x - a) := by
  rcases eq_or_ne x a with h | h
  · subst h; simp
  · exact (rpow_lt_tangent hρ0 hρ1 ha hx h).le

variable {ι : Type*} [Fintype ι]

/-- The CES consumption index (2), O&R p. 661, on a finite set of goods with weights `w`
(the weights are the masses of the goods; under within-bloc symmetry the two-bloc case is
exact): `C = [Σ wᵢ cᵢ^{(θ−1)/θ}]^{θ/(θ−1)}`. -/
noncomputable def cesQuantityIndex (θ : ℝ) (w c : ι → ℝ) : ℝ :=
  (∑ i, w i * c i ^ ((θ - 1) / θ)) ^ (θ / (θ - 1))

/-- The consumption-based price index (3), O&R p. 661: `P = [Σ wᵢ pᵢ^{1−θ}]^{1/(1−θ)}`. -/
noncomputable def cesPriceIndex (θ : ℝ) (w p : ι → ℝ) : ℝ :=
  (∑ i, w i * p i ^ (1 - θ)) ^ (1 / (1 - θ))

/-- Nominal expenditure `Z = Σ wᵢ pᵢ cᵢ` on a bundle (O&R fn 4, p. 662). -/
def cesExpenditure (w p c : ι → ℝ) : ℝ := ∑ i, w i * p i * c i

/-- The inner sum of the price index is positive (O&R (3), p. 661). -/
theorem cesPrice_sum_pos [Nonempty ι] {θ : ℝ} {w p : ι → ℝ} (hw : ∀ i, 0 < w i)
    (hp : ∀ i, 0 < p i) : 0 < ∑ i, w i * p i ^ (1 - θ) :=
  Finset.sum_pos (fun i _ => mul_pos (hw i) (rpow_pos_of_pos (hp i) _)) Finset.univ_nonempty

/-- The price index is positive (O&R (3), p. 661). -/
theorem cesPriceIndex_pos [Nonempty ι] {θ : ℝ} {w p : ι → ℝ} (hw : ∀ i, 0 < w i)
    (hp : ∀ i, 0 < p i) : 0 < cesPriceIndex θ w p :=
  rpow_pos_of_pos (cesPrice_sum_pos hw hp) _

/-- `P^{1−θ} = Σ wᵢ pᵢ^{1−θ}` (O&R (3), p. 661), for `θ ≠ 1`. -/
theorem cesPriceIndex_rpow [Nonempty ι] {θ : ℝ} (hθ : θ ≠ 1) {w p : ι → ℝ}
    (hw : ∀ i, 0 < w i) (hp : ∀ i, 0 < p i) :
    cesPriceIndex θ w p ^ (1 - θ) = ∑ i, w i * p i ^ (1 - θ) := by
  unfold cesPriceIndex
  rw [← rpow_mul (cesPrice_sum_pos hw hp).le]
  have : 1 / (1 - θ) * (1 - θ) = 1 := by
    have : 1 - θ ≠ 0 := sub_ne_zero.2 (Ne.symm hθ)
    field_simp
  rw [this, rpow_one]

/-- The quantity index raised to `(θ−1)/θ` is the inner sum (O&R (2), p. 661). -/
theorem cesQuantityIndex_rpow {θ : ℝ} (hθ : 1 < θ) {w c : ι → ℝ} (hw : ∀ i, 0 < w i)
    (hc : ∀ i, 0 ≤ c i) :
    cesQuantityIndex θ w c ^ ((θ - 1) / θ) = ∑ i, w i * c i ^ ((θ - 1) / θ) := by
  unfold cesQuantityIndex
  have hS : 0 ≤ ∑ i, w i * c i ^ ((θ - 1) / θ) :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hw i).le (rpow_nonneg (hc i) _)
  rw [← rpow_mul hS]
  have : θ / (θ - 1) * ((θ - 1) / θ) = 1 := by
    have h1 : θ - 1 ≠ 0 := by linarith
    have h2 : θ ≠ 0 := by linarith
    field_simp
  rw [this, rpow_one]

/-- The quantity index of a bundle of strictly positive quantities is positive (O&R (2)). -/
theorem cesQuantityIndex_pos [Nonempty ι] {θ : ℝ} {w c : ι → ℝ} (hw : ∀ i, 0 < w i)
    (hc : ∀ i, 0 < c i) : 0 < cesQuantityIndex θ w c :=
  rpow_pos_of_pos (Finset.sum_pos (fun i _ => mul_pos (hw i) (rpow_pos_of_pos (hc i) _))
    Finset.univ_nonempty) _

/-- `Σ wᵢ (pᵢ/P)^{1−θ} = 1` (O&R (3), p. 661). -/
theorem ces_relative_price_sum [Nonempty ι] {θ : ℝ} (hθ : θ ≠ 1) {w p : ι → ℝ}
    (hw : ∀ i, 0 < w i) (hp : ∀ i, 0 < p i) :
    ∑ i, w i * (p i / cesPriceIndex θ w p) ^ (1 - θ) = 1 := by
  have hP := cesPriceIndex_pos (θ := θ) hw hp
  have hPr := cesPriceIndex_rpow hθ hw hp
  have hPr0 : 0 < cesPriceIndex θ w p ^ (1 - θ) := rpow_pos_of_pos hP _
  simp_rw [div_rpow (hp _).le hP.le, mul_div_assoc']
  rw [← Finset.sum_div, ← hPr, div_self hPr0.ne']

/-- `(x^{−θ} K)^{(θ−1)/θ} = x^{1−θ} K^{(θ−1)/θ}` (O&R fn 6, p. 664). -/
theorem ces_demand_rpow_rho {θ x K : ℝ} (hθ : 1 < θ) (hx : 0 < x) (hK : 0 < K) :
    (x ^ (-θ) * K) ^ ((θ - 1) / θ) = x ^ (1 - θ) * K ^ ((θ - 1) / θ) := by
  rw [mul_rpow (rpow_nonneg hx.le _) hK.le, ← rpow_mul hx.le]
  congr 2
  have : θ ≠ 0 := by linarith
  field_simp
  ring

/-- `(x^{−θ} K)^{(θ−1)/θ − 1} = x · K^{(θ−1)/θ − 1}` (O&R fn 6, p. 664). -/
theorem ces_demand_rpow_rho_sub_one {θ x K : ℝ} (hθ : 1 < θ) (hx : 0 < x) (hK : 0 < K) :
    (x ^ (-θ) * K) ^ ((θ - 1) / θ - 1) = x * K ^ ((θ - 1) / θ - 1) := by
  rw [mul_rpow (rpow_nonneg hx.le _) hK.le, ← rpow_mul hx.le]
  have : -θ * ((θ - 1) / θ - 1) = 1 := by
    have : θ ≠ 0 := by linarith
    field_simp
    ring
  rw [this, rpow_one]

/-- `x · x^{−θ} = x^{1−θ}` (O&R fn 6, p. 664). -/
theorem ces_price_mul_demand {θ x : ℝ} (hx : 0 < x) : x * x ^ (-θ) = x ^ (1 - θ) := by
  rw [sub_eq_add_neg, rpow_add hx, rpow_one]

/-- The CES demand bundle `cᵢ = (pᵢ/P)^{−θ} K` for index level `K` (O&R fn 6, p. 664; built
from `cesDemand` of `StickyPriceModels.Model`). -/
noncomputable def cesDemandBundle (θ : ℝ) (w p : ι → ℝ) (K : ℝ) : ι → ℝ :=
  fun i => cesDemand θ (p i) (cesPriceIndex θ w p) K

/-- Expenditure on the demand bundle is `P K` (O&R fn 6, p. 664). -/
theorem cesExpenditure_demandBundle [Nonempty ι] {θ : ℝ} (hθ : θ ≠ 1) {w p : ι → ℝ}
    (hw : ∀ i, 0 < w i) (hp : ∀ i, 0 < p i) (K : ℝ) :
    cesExpenditure w p (cesDemandBundle θ w p K) = cesPriceIndex θ w p * K := by
  have hP := cesPriceIndex_pos (θ := θ) hw hp
  have hsum := ces_relative_price_sum hθ hw hp
  unfold cesExpenditure cesDemandBundle cesDemand
  have key : ∀ i, w i * p i * ((p i / cesPriceIndex θ w p) ^ (-θ) * K) =
      cesPriceIndex θ w p * K * (w i * (p i / cesPriceIndex θ w p) ^ (1 - θ)) := by
    intro i
    have hq : 0 < p i / cesPriceIndex θ w p := div_pos (hp i) hP
    rw [← ces_price_mul_demand hq]
    field_simp
  simp_rw [key]
  rw [← Finset.mul_sum, hsum, mul_one]

/-- The index of the demand bundle is `K` (O&R fn 6, p. 664). -/
theorem cesQuantityIndex_demandBundle [Nonempty ι] {θ : ℝ} (hθ : 1 < θ) {w p : ι → ℝ}
    (hw : ∀ i, 0 < w i) (hp : ∀ i, 0 < p i) {K : ℝ} (hK : 0 < K) :
    cesQuantityIndex θ w (cesDemandBundle θ w p K) = K := by
  have hP := cesPriceIndex_pos (θ := θ) hw hp
  have hsum := ces_relative_price_sum hθ.ne' hw hp
  unfold cesQuantityIndex cesDemandBundle cesDemand
  have key : ∀ i, w i * ((p i / cesPriceIndex θ w p) ^ (-θ) * K) ^ ((θ - 1) / θ) =
      K ^ ((θ - 1) / θ) * (w i * (p i / cesPriceIndex θ w p) ^ (1 - θ)) := by
    intro i
    rw [ces_demand_rpow_rho hθ (div_pos (hp i) hP) hK]
    ring
  simp_rw [key]
  rw [← Finset.mul_sum, hsum, mul_one, ← rpow_mul hK.le]
  have : (θ - 1) / θ * (θ / (θ - 1)) = 1 := by
    have h1 : θ - 1 ≠ 0 := by linarith
    have h2 : θ ≠ 0 := by linarith
    field_simp
  rw [this, rpow_one]

/-- **CES duality, the cost inequality** (O&R fn 4, p. 662, and fn 6, p. 664; T1): for `θ > 1`,
every strictly positive bundle costs at least `P` times its index, `P · C(c) ≤ Σ wᵢ pᵢ cᵢ`. -/
theorem ces_expenditure_ge [Nonempty ι] {θ : ℝ} (hθ : 1 < θ) {w p c : ι → ℝ}
    (hw : ∀ i, 0 < w i) (hp : ∀ i, 0 < p i) (hc : ∀ i, 0 < c i) :
    cesPriceIndex θ w p * cesQuantityIndex θ w c ≤ cesExpenditure w p c := by
  set P := cesPriceIndex θ w p with hPdef
  set K := cesQuantityIndex θ w c with hKdef
  set ρ := (θ - 1) / θ with hρ
  have hP : 0 < P := cesPriceIndex_pos hw hp
  have hK : 0 < K := cesQuantityIndex_pos hw hc
  have hρ0 : 0 < ρ := div_pos (by linarith) (by linarith)
  have hρ1 : ρ < 1 := by rw [hρ, div_lt_one (by linarith)]; linarith
  set cs := cesDemandBundle θ w p K with hcs
  have hcs_eq : ∀ i, cs i = (p i / P) ^ (-θ) * K := fun i => rfl
  have hcs_pos : ∀ i, 0 < cs i := fun i => by
    rw [hcs_eq]; exact mul_pos (rpow_pos_of_pos (div_pos (hp i) hP) _) hK
  have htan : ∀ i, w i * c i ^ ρ ≤ w i * cs i ^ ρ +
      ρ * K ^ (ρ - 1) / P * (w i * p i * c i - w i * p i * cs i) := by
    intro i
    have t := rpow_le_tangent hρ0 hρ1 (hcs_pos i) (hc i).le
    have h1 : cs i ^ (ρ - 1) = p i / P * K ^ (ρ - 1) := by
      rw [hcs_eq]; exact ces_demand_rpow_rho_sub_one hθ (div_pos (hp i) hP) hK
    rw [h1] at t
    have := mul_le_mul_of_nonneg_left t (hw i).le
    have e : w i * (cs i ^ ρ + ρ * (p i / P * K ^ (ρ - 1)) * (c i - cs i)) =
        w i * cs i ^ ρ + ρ * K ^ (ρ - 1) / P * (w i * p i * c i - w i * p i * cs i) := by
      field_simp
    linarith
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => htan i
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib] at hsum
  have hL : ∑ i, w i * c i ^ ρ = K ^ ρ := (cesQuantityIndex_rpow hθ hw fun i => (hc i).le).symm
  have hR : ∑ i, w i * cs i ^ ρ = K ^ ρ := by
    have := cesQuantityIndex_rpow hθ hw fun i => (hcs_pos i).le
    rw [← this, cesQuantityIndex_demandBundle hθ hw hp hK]
  have hE : ∑ i, w i * p i * cs i = P * K := cesExpenditure_demandBundle hθ.ne' hw hp K
  rw [hL, hR, hE] at hsum
  have hcoef : 0 < ρ * K ^ (ρ - 1) / P := div_pos (mul_pos hρ0 (rpow_pos_of_pos hK _)) hP
  have : 0 ≤ ρ * K ^ (ρ - 1) / P * (∑ i, w i * p i * c i - P * K) := by linarith
  have := (mul_nonneg_iff_of_pos_left hcoef).1 this
  unfold cesExpenditure
  linarith

/-- **CES duality, the equality case** (O&R fn 6, p. 664; T1): for `θ > 1` a strictly positive
bundle costs exactly `P · C(c)` IF AND ONLY IF it is the demand bundle
`cᵢ = (pᵢ/P)^{−θ} C(c)`. -/
theorem ces_expenditure_eq_iff [Nonempty ι] {θ : ℝ} (hθ : 1 < θ) {w p c : ι → ℝ}
    (hw : ∀ i, 0 < w i) (hp : ∀ i, 0 < p i) (hc : ∀ i, 0 < c i) :
    cesExpenditure w p c = cesPriceIndex θ w p * cesQuantityIndex θ w c ↔
      c = cesDemandBundle θ w p (cesQuantityIndex θ w c) := by
  set P := cesPriceIndex θ w p with hPdef
  set K := cesQuantityIndex θ w c with hKdef
  set ρ := (θ - 1) / θ with hρ
  have hP : 0 < P := cesPriceIndex_pos hw hp
  have hK : 0 < K := cesQuantityIndex_pos hw hc
  constructor
  · intro heq
    by_contra hne
    obtain ⟨j, hj⟩ : ∃ j, c j ≠ cesDemandBundle θ w p K j := by
      by_contra h
      push Not at h
      exact hne (funext h)
    have hρ0 : 0 < ρ := div_pos (by linarith) (by linarith)
    have hρ1 : ρ < 1 := by rw [hρ, div_lt_one (by linarith)]; linarith
    set cs := cesDemandBundle θ w p K with hcs
    have hcs_eq : ∀ i, cs i = (p i / P) ^ (-θ) * K := fun i => rfl
    have hcs_pos : ∀ i, 0 < cs i := fun i => by
      rw [hcs_eq]; exact mul_pos (rpow_pos_of_pos (div_pos (hp i) hP) _) hK
    have h1 : ∀ i, cs i ^ (ρ - 1) = p i / P * K ^ (ρ - 1) := fun i => by
      rw [hcs_eq]; exact ces_demand_rpow_rho_sub_one hθ (div_pos (hp i) hP) hK
    have e : ∀ i, w i * (cs i ^ ρ + ρ * (p i / P * K ^ (ρ - 1)) * (c i - cs i)) =
        w i * cs i ^ ρ + ρ * K ^ (ρ - 1) / P * (w i * p i * c i - w i * p i * cs i) := by
      intro i; field_simp
    have htan : ∀ i ∈ Finset.univ, w i * c i ^ ρ ≤ w i * cs i ^ ρ +
        ρ * K ^ (ρ - 1) / P * (w i * p i * c i - w i * p i * cs i) := by
      intro i _
      have t := rpow_le_tangent hρ0 hρ1 (hcs_pos i) (hc i).le
      rw [h1] at t
      have := mul_le_mul_of_nonneg_left t (hw i).le
      linarith [e i]
    have hstrict : ∃ i ∈ Finset.univ, w i * c i ^ ρ < w i * cs i ^ ρ +
        ρ * K ^ (ρ - 1) / P * (w i * p i * c i - w i * p i * cs i) := by
      refine ⟨j, Finset.mem_univ _, ?_⟩
      have t := rpow_lt_tangent hρ0 hρ1 (hcs_pos j) (hc j).le hj
      rw [h1] at t
      have := mul_lt_mul_of_pos_left t (hw j)
      linarith [e j]
    have hsum := Finset.sum_lt_sum htan hstrict
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_sub_distrib] at hsum
    have hL : ∑ i, w i * c i ^ ρ = K ^ ρ :=
      (cesQuantityIndex_rpow hθ hw fun i => (hc i).le).symm
    have hR : ∑ i, w i * cs i ^ ρ = K ^ ρ := by
      have := cesQuantityIndex_rpow hθ hw fun i => (hcs_pos i).le
      rw [← this, cesQuantityIndex_demandBundle hθ hw hp hK]
    have hE : ∑ i, w i * p i * cs i = P * K := cesExpenditure_demandBundle hθ.ne' hw hp K
    have hE' : ∑ i, w i * p i * c i = P * K := heq
    rw [hL, hR, hE, hE'] at hsum
    simp at hsum
  · intro h
    rw [h, cesExpenditure_demandBundle hθ.ne' hw hp]

/-- **The price index is the minimum cost of one unit of the index** (O&R fn 4, p. 662;
"left as an exercise" there; T1(a)): among strictly positive bundles with `C(c) = 1`, the least
expenditure is `P`, and it is attained exactly at the demand bundle `cᵢ = (pᵢ/P)^{−θ}`. -/
theorem ces_minimum_cost [Nonempty ι] {θ : ℝ} (hθ : 1 < θ) {w p : ι → ℝ}
    (hw : ∀ i, 0 < w i) (hp : ∀ i, 0 < p i) :
    IsLeast {Z | ∃ c : ι → ℝ, (∀ i, 0 < c i) ∧ cesQuantityIndex θ w c = 1 ∧
      Z = cesExpenditure w p c} (cesPriceIndex θ w p) ∧
    ∀ c : ι → ℝ, (∀ i, 0 < c i) → cesQuantityIndex θ w c = 1 →
      (cesExpenditure w p c = cesPriceIndex θ w p ↔ c = cesDemandBundle θ w p 1) := by
  have hP := cesPriceIndex_pos (θ := θ) hw hp
  refine ⟨⟨⟨cesDemandBundle θ w p 1, fun i => mul_pos (rpow_pos_of_pos
      (div_pos (hp i) hP) _) one_pos, cesQuantityIndex_demandBundle hθ hw hp one_pos, ?_⟩, ?_⟩, ?_⟩
  · rw [cesExpenditure_demandBundle hθ.ne' hw hp, mul_one]
  · rintro Z ⟨c, hc, h1, rfl⟩
    have := ces_expenditure_ge hθ hw hp hc
    rwa [h1, mul_one] at this
  · intro c hc h1
    have := ces_expenditure_eq_iff hθ hw hp hc
    rwa [h1, mul_one] at this

/-- **Utility maximisation for given expenditure** (O&R fn 6, p. 664; T1(b)): with nominal
expenditure `Z > 0`, every strictly positive bundle with `Σ wᵢ pᵢ cᵢ ≤ Z` has index at most
`Z/P`; the demand bundle `cᵢ = (pᵢ/P)^{−θ} Z/P` costs exactly `Z` and attains `Z/P`, and it is
the only affordable bundle that does. -/
theorem ces_utility_max [Nonempty ι] {θ : ℝ} (hθ : 1 < θ) {w p : ι → ℝ}
    (hw : ∀ i, 0 < w i) (hp : ∀ i, 0 < p i) {Z : ℝ} (hZ : 0 < Z) :
    (∀ c : ι → ℝ, (∀ i, 0 < c i) → cesExpenditure w p c ≤ Z →
      cesQuantityIndex θ w c ≤ Z / cesPriceIndex θ w p) ∧
    cesExpenditure w p (cesDemandBundle θ w p (Z / cesPriceIndex θ w p)) = Z ∧
    cesQuantityIndex θ w (cesDemandBundle θ w p (Z / cesPriceIndex θ w p)) =
      Z / cesPriceIndex θ w p ∧
    ∀ c : ι → ℝ, (∀ i, 0 < c i) → cesExpenditure w p c ≤ Z →
      cesQuantityIndex θ w c = Z / cesPriceIndex θ w p →
      c = cesDemandBundle θ w p (Z / cesPriceIndex θ w p) := by
  have hP := cesPriceIndex_pos (θ := θ) hw hp
  refine ⟨fun c hc hZc => ?_, ?_, cesQuantityIndex_demandBundle hθ hw hp (div_pos hZ hP),
    fun c hc hZc hK => ?_⟩
  · have := ces_expenditure_ge hθ hw hp hc
    rw [le_div_iff₀ hP]
    linarith
  · rw [cesExpenditure_demandBundle hθ.ne' hw hp]
    field_simp
  · have hge := ces_expenditure_ge hθ hw hp hc
    rw [hK] at hge
    have heq : cesExpenditure w p c = cesPriceIndex θ w p * cesQuantityIndex θ w c := by
      rw [hK]
      have : cesPriceIndex θ w p * (Z / cesPriceIndex θ w p) = Z := by field_simp
      linarith
    have := (ces_expenditure_eq_iff hθ hw hp hc).1 heq
    rwa [hK] at this

/-- The relative-demand form of fn 6, O&R p. 664: `c(z') = c(z)(p(z)/p(z'))^θ` along the demand
bundle. -/
theorem cesDemandBundle_ratio [Nonempty ι] {θ : ℝ} {w p : ι → ℝ} (hw : ∀ i, 0 < w i)
    (hp : ∀ i, 0 < p i) (K : ℝ) (i j : ι) :
    cesDemandBundle θ w p K j = cesDemandBundle θ w p K i * (p i / p j) ^ θ := by
  have hP := cesPriceIndex_pos (θ := θ) hw hp
  unfold cesDemandBundle cesDemand
  rw [div_rpow (hp i).le (hp j).le, div_rpow (hp j).le hP.le, div_rpow (hp i).le hP.le,
    rpow_neg (hp j).le, rpow_neg (hp i).le, rpow_neg hP.le]
  have h1 := rpow_pos_of_pos (hp i) θ
  have h2 := rpow_pos_of_pos (hp j) θ
  have h3 := rpow_pos_of_pos hP θ
  field_simp

/-- **Homogeneity of degree one** of the price index (O&R (3), p. 661): `P(λp) = λ P(p)` for
`λ > 0`. -/
theorem cesPriceIndex_smul [Nonempty ι] {θ : ℝ} (hθ : θ ≠ 1) {w p : ι → ℝ}
    (hw : ∀ i, 0 < w i) (hp : ∀ i, 0 < p i) {l : ℝ} (hl : 0 < l) :
    cesPriceIndex θ w (fun i => l * p i) = l * cesPriceIndex θ w p := by
  unfold cesPriceIndex
  have key : ∑ i, w i * (l * p i) ^ (1 - θ) = l ^ (1 - θ) * ∑ i, w i * p i ^ (1 - θ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [mul_rpow hl.le (hp i).le]
    ring
  rw [key, mul_rpow (rpow_nonneg hl.le _) (cesPrice_sum_pos hw hp).le, ← rpow_mul hl.le]
  have : (1 - θ) * (1 / (1 - θ)) = 1 := by
    have : 1 - θ ≠ 0 := sub_ne_zero.2 (Ne.symm hθ)
    field_simp
  rw [this, rpow_one]

/-- **The price index is increasing** in every price (O&R (3), p. 661), for `θ > 1`. -/
theorem cesPriceIndex_mono [Nonempty ι] {θ : ℝ} (hθ : 1 < θ) {w p q : ι → ℝ}
    (hw : ∀ i, 0 < w i) (hp : ∀ i, 0 < p i) (hpq : ∀ i, p i ≤ q i) :
    cesPriceIndex θ w p ≤ cesPriceIndex θ w q := by
  have hq : ∀ i, 0 < q i := fun i => (hp i).trans_le (hpq i)
  unfold cesPriceIndex
  have hle : ∑ i, w i * q i ^ (1 - θ) ≤ ∑ i, w i * p i ^ (1 - θ) :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
      (rpow_le_rpow_of_nonpos (hp i) (hpq i) (by linarith)) (hw i).le
  exact rpow_le_rpow_of_nonpos (cesPrice_sum_pos hw hq) hle
    (by rw [one_div]; exact inv_nonpos.2 (by linarith))

/-- **The law of one price implies PPP** (O&R (4)–(7), pp. 662–663; T1(d)): if `pᵢ = 𝓔 pᵢ*`
for every good, then `P = 𝓔 P*` exactly, and `pᵢ/P = pᵢ*/P*` for every good. -/
theorem ppp_of_loop [Nonempty ι] {θ : ℝ} (hθ : θ ≠ 1) {w ps : ι → ℝ}
    (hw : ∀ i, 0 < w i) (hps : ∀ i, 0 < ps i) {E : ℝ} (hE : 0 < E) :
    cesPriceIndex θ w (fun i => E * ps i) = E * cesPriceIndex θ w ps ∧
    ∀ i, E * ps i / cesPriceIndex θ w (fun i => E * ps i) = ps i / cesPriceIndex θ w ps := by
  have h := cesPriceIndex_smul hθ hw hps hE
  refine ⟨h, fun i => ?_⟩
  rw [h]
  have := (cesPriceIndex_pos (θ := θ) hw hps).ne'
  field_simp

/-! ## The two-bloc price indexes (5)–(7) -/

/-- The bloc form of the price index, O&R (5)–(6), p. 663 and p. 669: with a mass `n` of goods
priced `a` and a mass `1 − n` priced `b` (within-country symmetry),
`[n a^{1−θ} + (1−n) b^{1−θ}]^{1/(1−θ)}`. Home's index is `blocPriceIndex θ n p(h) (𝓔p*(f))`,
Foreign's is `blocPriceIndex θ n (p(h)/𝓔) p*(f)`. -/
noncomputable def blocPriceIndex (θ n a b : ℝ) : ℝ :=
  (n * a ^ (1 - θ) + (1 - n) * b ^ (1 - θ)) ^ (1 / (1 - θ))

/-- The bloc price index is the CES price index with the two weights `(n, 1 − n)` (O&R (5)). -/
theorem blocPriceIndex_eq_ces (θ n a b : ℝ) :
    blocPriceIndex θ n a b = cesPriceIndex θ ![n, 1 - n] ![a, b] := by
  simp [blocPriceIndex, cesPriceIndex, Fin.sum_univ_two]

/-- The bloc price index is positive (O&R (5)). -/
theorem blocPriceIndex_pos {θ n a b : ℝ} (hn0 : 0 < n) (hn1 : n < 1) (ha : 0 < a) (hb : 0 < b) :
    0 < blocPriceIndex θ n a b :=
  rpow_pos_of_pos (add_pos (mul_pos hn0 (rpow_pos_of_pos ha _))
    (mul_pos (by linarith) (rpow_pos_of_pos hb _))) _

/-- `P^{1−θ} = n a^{1−θ} + (1−n) b^{1−θ}` for the bloc index (O&R (5)), `θ ≠ 1`. -/
theorem blocPriceIndex_rpow {θ n a b : ℝ} (hθ : θ ≠ 1) (hn0 : 0 < n) (hn1 : n < 1)
    (ha : 0 < a) (hb : 0 < b) :
    blocPriceIndex θ n a b ^ (1 - θ) = n * a ^ (1 - θ) + (1 - n) * b ^ (1 - θ) := by
  unfold blocPriceIndex
  rw [← rpow_mul (add_pos (mul_pos hn0 (rpow_pos_of_pos ha _))
    (mul_pos (by linarith) (rpow_pos_of_pos hb _))).le]
  have : 1 / (1 - θ) * (1 - θ) = 1 := by
    have : 1 - θ ≠ 0 := sub_ne_zero.2 (Ne.symm hθ)
    field_simp
  rw [this, rpow_one]

/-- **PPP (7) from the bloc indexes (5)–(6)**, O&R p. 663: `P = 𝓔 P*` where
`P = blocPriceIndex θ n p(h) (𝓔 p*(f))` and `P* = blocPriceIndex θ n (p(h)/𝓔) p*(f)`. -/
theorem bloc_ppp {θ n ph pfs E : ℝ} (hθ : θ ≠ 1) (hn0 : 0 < n) (hn1 : n < 1) (hph : 0 < ph)
    (hpfs : 0 < pfs) (hE : 0 < E) :
    blocPriceIndex θ n ph (E * pfs) = E * blocPriceIndex θ n (ph / E) pfs := by
  rw [blocPriceIndex_eq_ces, blocPriceIndex_eq_ces]
  have hw : ∀ i, 0 < (![n, 1 - n] : Fin 2 → ℝ) i := by
    intro i; fin_cases i <;> simp [hn0, hn1]
  have hq : ∀ i, 0 < (![ph / E, pfs] : Fin 2 → ℝ) i := by
    intro i; fin_cases i <;> simp [div_pos hph hE, hpfs]
  rw [← cesPriceIndex_smul hθ hw hq hE]
  congr 1
  funext i
  fin_cases i <;> simp [mul_div_cancel₀ _ hE.ne']

/-- The terms-of-trade normalisation implied by the bloc index and PPP (O&R (5), (7), (22)):
with `π = p(h)/P` and `π* = p*(f)/P*`, `n π^{1−θ} + (1−n) π*^{1−θ} = 1`. -/
theorem bloc_relative_price_sum {θ n ph pfs E : ℝ} (hθ : θ ≠ 1) (hn0 : 0 < n) (hn1 : n < 1)
    (hph : 0 < ph) (hpfs : 0 < pfs) (hE : 0 < E) :
    n * (ph / blocPriceIndex θ n ph (E * pfs)) ^ (1 - θ) +
      (1 - n) * (pfs / blocPriceIndex θ n (ph / E) pfs) ^ (1 - θ) = 1 := by
  have hP := blocPriceIndex_pos (θ := θ) hn0 hn1 hph (mul_pos hE hpfs)
  have hPs := blocPriceIndex_pos (θ := θ) hn0 hn1 (div_pos hph hE) hpfs
  have hppp := bloc_ppp hθ hn0 hn1 hph hpfs hE
  have hPr := blocPriceIndex_rpow hθ hn0 hn1 hph (mul_pos hE hpfs)
  have e : pfs / blocPriceIndex θ n (ph / E) pfs = E * pfs / blocPriceIndex θ n ph (E * pfs) := by
    rw [hppp]; field_simp
  rw [e, div_rpow hph.le hP.le, div_rpow (mul_pos hE hpfs).le hP.le]
  have h0 : 0 < blocPriceIndex θ n ph (E * pfs) ^ (1 - θ) := rpow_pos_of_pos hP _
  field_simp
  linarith

/-! ## World demand and the monopolist's revenue -/

/-- World consumption (11), O&R p. 665: `Cᵂ = n C + (1 − n) C*`. -/
def worldConsumption (n C Cs : ℝ) : ℝ := n * C + (1 - n) * Cs

/-- World consumption is positive when both countries consume (O&R (11)). -/
theorem worldConsumption_pos {n C Cs : ℝ} (hn0 : 0 < n) (hn1 : n < 1) (hC : 0 < C)
    (hCs : 0 < Cs) : 0 < worldConsumption n C Cs := by
  unfold worldConsumption
  have : 0 < 1 - n := by linarith
  positivity

/-- **World demand (10)**, O&R p. 665: when `p(z)/P = p*(z)/P*` (PPP and the law of one price,
`ppp_of_loop`), the population-weighted sum of Home and Foreign CES demands for good `z` is
`(p(z)/P)^{−θ} Cᵂ`. -/
theorem world_demand {θ n p P ps Ps C Cs : ℝ} (hrel : p / P = ps / Ps) :
    n * cesDemand θ p P C + (1 - n) * cesDemand θ ps Ps Cs =
      cesDemand θ p P (worldConsumption n C Cs) := by
  unfold cesDemand worldConsumption
  rw [← hrel]
  ring

/-- **Inverting the demand curve** (O&R p. 665, before (12)): for `Cᵂ > 0`, `y > 0`, `π > 0` and
`θ ≠ 0`, `y = q^{−θ} Cᵂ` iff `q = (y/Cᵂ)^{−1/θ}`. So choosing output `y` given the demand curve
(10) is the same as choosing the relative price `π = p(j)/P` (T2(d)). -/
theorem demand_iff_price {θ q y X : ℝ} (hθ : θ ≠ 0) (hq : 0 < q) (hy : 0 < y) (hX : 0 < X) :
    y = cesDemand θ q 1 X ↔ q = (y / X) ^ (-1 / θ) := by
  unfold cesDemand
  rw [div_one]
  constructor
  · intro h
    rw [h, mul_div_assoc, div_self hX.ne', mul_one, ← rpow_mul hq.le]
    have : -θ * (-1 / θ) = 1 := by field_simp
    rw [this, rpow_one]
  · intro h
    rw [h, ← rpow_mul (div_pos hy hX).le]
    have : -1 / θ * -θ = 1 := by field_simp
    rw [this, rpow_one]
    field_simp

/-- **Real revenue on the demand curve** (O&R p. 665: `p(j)y(j) = P y(j)^{(θ−1)/θ} (Cᵂ)^{1/θ}`):
if `y = q^{−θ} Cᵂ` with `q, y, Cᵂ > 0` and `θ ≠ 0`, then `q y = y^{(θ−1)/θ} (Cᵂ)^{1/θ}`. -/
theorem revenue_on_demand {θ q y X : ℝ} (hθ : θ ≠ 0) (hq : 0 < q) (hy : 0 < y) (hX : 0 < X)
    (hd : y = cesDemand θ q 1 X) : q * y = y ^ ((θ - 1) / θ) * X ^ (1 / θ) := by
  have hq' := (demand_iff_price hθ hq hy hX).1 hd
  rw [hq', div_rpow hy.le hX.le]
  have hy1 : y ^ ((θ - 1) / θ) = y ^ (-1 / θ) * y := by
    rw [← rpow_add_one hy.ne']
    congr 1
    field_simp
    ring
  have hX1 : X ^ (1 / θ) = (X ^ (-1 / θ))⁻¹ := by
    rw [← rpow_neg hX.le]
    congr 1
    ring
  rw [hy1, hX1]
  have := rpow_pos_of_pos hX (-1 / θ)
  field_simp

/-! ## The household's budget: discount factors and wealth -/

/-- **The market discount factor** `R_T = Π_{s=1}^{T} (1 + r_s)^{−1}` of the TVC (16),
O&R p. 666, which the book leaves undefined. Here `r s` is the real rate on bonds held from
`s − 1` to `s` (O&R (8), p. 663), and the problem starts at date `0` (for a problem starting at
date `t` shift the sequences). -/
noncomputable def marketDiscount (r : ℕ → ℝ) (T : ℕ) : ℝ :=
  ∏ s ∈ Finset.range T, (1 + r (s + 1))⁻¹

/-- `R_0 = 1` (O&R (16)). -/
@[simp] theorem marketDiscount_zero (r : ℕ → ℝ) : marketDiscount r 0 = 1 := by
  simp [marketDiscount]

/-- `R_{T+1} = R_T (1 + r_{T+1})^{−1}` (O&R (16)). -/
theorem marketDiscount_succ (r : ℕ → ℝ) (T : ℕ) :
    marketDiscount r (T + 1) = marketDiscount r T * (1 + r (T + 1))⁻¹ := by
  rw [marketDiscount, marketDiscount, Finset.prod_range_succ]

/-- The discount factor is positive when every gross rate is (O&R (16)). -/
theorem marketDiscount_pos {r : ℕ → ℝ} (hr : ∀ t, 0 < 1 + r t) (T : ℕ) :
    0 < marketDiscount r T :=
  Finset.prod_pos fun s _ => inv_pos.2 (hr (s + 1))

/-- With a constant rate the discount factor is geometric (O&R (16), (19)). -/
theorem marketDiscount_const (a : ℝ) (T : ℕ) :
    marketDiscount (fun _ => a) T = (1 + a)⁻¹ ^ T := by
  simp [marketDiscount]

/-- `R_{T+1}(1 + r_{T+1}) = R_T` (O&R (16)). -/
theorem marketDiscount_succ_mul {r : ℕ → ℝ} (hr : ∀ t, 0 < 1 + r t) (T : ℕ) :
    marketDiscount r (T + 1) * (1 + r (T + 1)) = marketDiscount r T := by
  rw [marketDiscount_succ, mul_assoc, inv_mul_cancel₀ (hr (T + 1)).ne', mul_one]

/-- Real financial wealth at the start of each date, O&R (8), p. 663, written as
`W_t = (1 + r_t)B_t + M_{t−1}/P_t`. Given an outlay sequence `x` it evolves as
`W_{t+1} = (1 + r_{t+1})(W_t − x_t)` (see `wealth_of_budget`). -/
noncomputable def wealth (r : ℕ → ℝ) (W0 : ℝ) (x : ℕ → ℝ) : ℕ → ℝ
  | 0 => W0
  | t + 1 => (1 + r (t + 1)) * (wealth r W0 x t - x t)

/-- The law of motion of wealth (O&R (8)). -/
theorem wealth_succ (r : ℕ → ℝ) (W0 : ℝ) (x : ℕ → ℝ) (t : ℕ) :
    wealth r W0 x (t + 1) = (1 + r (t + 1)) * (wealth r W0 x t - x t) := rfl

/-- The user cost of holding real balances from `t` to `t + 1` (O&R p. 666 and Ch. 8 (37)):
`ι_t = 1 − (P_t/P_{t+1})/(1 + r_{t+1})`, which equals `i_{t+1}/(1 + i_{t+1})` under the Fisher
relation of p. 665 (`userCost_eq_fisher`). -/
noncomputable def userCost (r P : ℕ → ℝ) (t : ℕ) : ℝ := 1 - P t / P (t + 1) / (1 + r (t + 1))

/-- **Fisher parity and the user cost**, O&R p. 665: if `1 + i_{t+1} = (P_{t+1}/P_t)(1 + r_{t+1})`
then `ι_t = i_{t+1}/(1 + i_{t+1})`. -/
theorem userCost_eq_fisher {r P : ℕ → ℝ} {i : ℝ} (t : ℕ) (hr : 0 < 1 + r (t + 1))
    (hP : 0 < P t) (hP1 : 0 < P (t + 1)) (hfisher : 1 + i = P (t + 1) / P t * (1 + r (t + 1))) :
    userCost r P t = i / (1 + i) := by
  have hi : i = P (t + 1) / P t * (1 + r (t + 1)) - 1 := by linarith
  subst hi
  unfold userCost
  have := hr.ne'
  have := hP.ne'
  have := hP1.ne'
  field_simp
  ring

/-- **The period budget constraint (8) in wealth form**, O&R p. 663. Money is indexed so that
`N t` is the nominal balance brought INTO date `t` (the book's `M_{t−1}`), real revenue is
`Z_t y_t^{(θ−1)/θ}` (`revenue_on_demand`), and (8) reads
`P_t B_{t+1} + N_{t+1} = P_t(1+r_t)B_t + N_t + P_t Z_t y_t^{(θ−1)/θ} − P_t C_t − P_t τ_t`. Then
`W_t = (1+r_t)B_t + N_t/P_t` follows `wealth` with outlay
`C_t + ι_t m_t + τ_t − Z_t y_t^{(θ−1)/θ}`, where `m_t = N_{t+1}/P_t` (real balances `M_t/P_t`). -/
theorem wealth_of_budget {θ : ℝ} {r P B N Z y C τ : ℕ → ℝ} (hr : ∀ t, 0 < 1 + r t)
    (hP : ∀ t, 0 < P t)
    (hbud : ∀ t, P t * B (t + 1) + N (t + 1) = P t * (1 + r t) * B t + N t +
      P t * (Z t * y t ^ ((θ - 1) / θ)) - P t * C t - P t * τ t) (t : ℕ) :
    (1 + r t) * B t + N t / P t = wealth r ((1 + r 0) * B 0 + N 0 / P 0)
      (fun s => C s + userCost r P s * (N (s + 1) / P s) + τ s - Z s * y s ^ ((θ - 1) / θ)) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [wealth_succ, ← ih]
    have h := hbud t
    have hPs := (hP t).ne'
    have hPs1 := (hP (t + 1)).ne'
    have hrs := (hr (t + 1)).ne'
    unfold userCost
    field_simp
    field_simp at h
    linear_combination (1 + r (t + 1)) * P (t + 1) * h

/-- **Finite-horizon present-value identity**, O&R fn 7, p. 666 ("iterating the period budget
constraint"): `Σ_{s<T} R_s x_s + R_T W_T = W_0`. -/
theorem wealth_pv_identity {r : ℕ → ℝ} (hr : ∀ t, 0 < 1 + r t) (W0 : ℝ) (x : ℕ → ℝ) (T : ℕ) :
    ∑ s ∈ Finset.range T, marketDiscount r s * x s + marketDiscount r T * wealth r W0 x T = W0 := by
  induction T with
  | zero => simp [wealth]
  | succ T ih =>
    rw [Finset.sum_range_succ, wealth_succ]
    have h := marketDiscount_succ_mul hr T
    linear_combination ih + (wealth r W0 x T - x T) * h

/-- Wealth depends on the outlays only through the past: equal wealth at `k` and equal outlays
from `k` on give equal wealth at every later date (O&R (8)). -/
theorem wealth_congr_after {r : ℕ → ℝ} {W0 W0' : ℝ} {x x' : ℕ → ℝ} {k : ℕ}
    (hk : wealth r W0 x k = wealth r W0' x' k) (hx : ∀ s, k ≤ s → x s = x' s) (n : ℕ) :
    wealth r W0 x (k + n) = wealth r W0' x' (k + n) := by
  induction n with
  | zero => exact hk
  | succ n ih => rw [← add_assoc, wealth_succ, wealth_succ, ih, hx _ (by omega)]

/-- Outlays that agree before date `k` give the same wealth at `k` (O&R (8)). -/
theorem wealth_congr_before {r : ℕ → ℝ} {W0 : ℝ} {x x' : ℕ → ℝ} {k : ℕ}
    (hx : ∀ s, s < k → x s = x' s) : wealth r W0 x k = wealth r W0 x' k := by
  have key : ∀ n, n ≤ k → wealth r W0 x n = wealth r W0 x' n := by
    intro n
    induction n with
    | zero => intro _; rfl
    | succ n ih =>
      intro hn
      rw [wealth_succ, wealth_succ, ih (by omega), hx n (by omega)]
  exact key k le_rfl

/-- Spending `ε` more at date `0` lowers discounted wealth `R_T W_T` by exactly `ε` at every
`T ≥ 1` (O&R (8), (16)). -/
theorem wealth_shift_date0 {r : ℕ → ℝ} (hr : ∀ t, 0 < 1 + r t) {W0 ε : ℝ} {x x' : ℕ → ℝ}
    (h0 : x' 0 = x 0 + ε) (hs : ∀ s, s ≠ 0 → x' s = x s) (T : ℕ) :
    marketDiscount r (T + 1) * wealth r W0 x' (T + 1) =
      marketDiscount r (T + 1) * wealth r W0 x (T + 1) - ε := by
  have h1 := wealth_pv_identity hr W0 x (T + 1)
  have h2 := wealth_pv_identity hr W0 x' (T + 1)
  have hsum : ∑ s ∈ Finset.range (T + 1), marketDiscount r s * x' s =
      ∑ s ∈ Finset.range (T + 1), marketDiscount r s * x s + ε := by
    rw [Finset.sum_range_succ', Finset.sum_range_succ' (fun s => marketDiscount r s * x s)]
    have : ∀ s ∈ Finset.range T, marketDiscount r (s + 1) * x' (s + 1) =
        marketDiscount r (s + 1) * x (s + 1) := fun s _ => by rw [hs (s + 1) (by omega)]
    rw [Finset.sum_congr rfl this, h0]
    simp
    ring
  linarith

/-! ## The household problem (12) with a genuine infinite horizon -/

/-- The environment a representative Home agent takes as given in problem (12), O&R p. 665:
preference parameters `β, χ, κ` (eq. (1)), the demand elasticity `θ` (eq. (2)), the path of real
rates `r` (eq. (8)), the user cost of money `uc` (`userCost`), lump-sum taxes `τ` (eq. (8)), the
demand shifter `Z_t = (Cᵂ_t)^{1/θ}` (eq. (10)), and initial real wealth
`W0 = (1 + r_0)B_0 + M_{−1}/P_0`. -/
structure HouseholdEnv where
  β : ℝ
  χ : ℝ
  κ : ℝ
  θ : ℝ
  r : ℕ → ℝ
  uc : ℕ → ℝ
  τ : ℕ → ℝ
  Z : ℕ → ℝ
  W0 : ℝ

/-- A plan for problem (12), O&R p. 665: consumption `C_t`, real balances `m_t = M_t/P_t` and
output `y_t` (equivalently the price, `demand_iff_price`); bonds are then implied by (8). -/
structure HouseholdPlan where
  C : ℕ → ℝ
  m : ℕ → ℝ
  y : ℕ → ℝ

namespace HouseholdEnv

/-- The standing assumptions of O&R §10.1 (pp. 661–665): `β > 0`, `χ > 0`, `κ > 0`, `θ > 1`
(fn 2), gross real rates positive and positive world demand. -/
def Regular (E : HouseholdEnv) : Prop :=
  0 < E.β ∧ 0 < E.χ ∧ 0 < E.κ ∧ 1 < E.θ ∧ (∀ t, 0 < 1 + E.r t) ∧ ∀ t, 0 < E.Z t

/-- The period utility of (1), O&R p. 661: `log C + χ log(M/P) − (κ/2) y²`. -/
noncomputable def periodUtility (E : HouseholdEnv) (c k y : ℝ) : ℝ :=
  Real.log c + E.χ * Real.log k - E.κ / 2 * y ^ 2

/-- Lifetime utility (1), O&R p. 661: `Σ_{s≥0} β^s [log C_s + χ log m_s − (κ/2) y_s²]`. -/
noncomputable def utility (E : HouseholdEnv) (p : HouseholdPlan) : ℝ :=
  ∑' s, E.β ^ s * E.periodUtility (p.C s) (p.m s) (p.y s)

/-- The period outlay of a plan (O&R (8), (12)): consumption, the rental cost of real balances
and taxes, net of real revenue `Z_t y_t^{(θ−1)/θ}`. -/
noncomputable def outlay (E : HouseholdEnv) (p : HouseholdPlan) (t : ℕ) : ℝ :=
  p.C t + E.uc t * p.m t + E.τ t - E.Z t * p.y t ^ ((E.θ - 1) / E.θ)

/-- The wealth path of a plan (O&R (8)). -/
noncomputable def wealthPath (E : HouseholdEnv) (p : HouseholdPlan) : ℕ → ℝ :=
  wealth E.r E.W0 (E.outlay p)

/-- **The no-Ponzi condition** `liminf R_T W_T ≥ 0` (not stated in the book, whose fn 7
presupposes it): for every `ε > 0`, eventually `R_T W_T > −ε`. -/
def NoPonzi (E : HouseholdEnv) (W : ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∀ᶠ T in atTop, -ε < marketDiscount E.r T * W T

/-- **The transversality condition** in its weakest (and, as we prove, exact) form
`liminf R_T W_T ≤ 0` (O&R (16), p. 666): for every `ε > 0`, frequently `R_T W_T < ε`. -/
def Transversality (E : HouseholdEnv) (W : ℕ → ℝ) : Prop :=
  ∀ ε > 0, ∃ᶠ T in atTop, marketDiscount E.r T * W T < ε

/-- An admissible plan (O&R p. 665): strictly positive consumption, real balances and output,
summable lifetime utility, and no Ponzi scheme. -/
def Admissible (E : HouseholdEnv) (p : HouseholdPlan) : Prop :=
  (∀ t, 0 < p.C t) ∧ (∀ t, 0 < p.m t) ∧ (∀ t, 0 < p.y t) ∧
    Summable (fun s => E.β ^ s * E.periodUtility (p.C s) (p.m s) (p.y s)) ∧
    E.NoPonzi (E.wealthPath p)

/-- An optimal plan: admissible and at least as good as every admissible plan (O&R (12)). -/
def IsOptimal (E : HouseholdEnv) (p : HouseholdPlan) : Prop :=
  E.Admissible p ∧ ∀ q, E.Admissible q → E.utility q ≤ E.utility p

/-- The consumption Euler equation (13), O&R p. 665: `C_{t+1} = β(1 + r_{t+1}) C_t`. -/
def EulerCond (E : HouseholdEnv) (p : HouseholdPlan) : Prop :=
  ∀ t, p.C (t + 1) = E.β * (1 + E.r (t + 1)) * p.C t

/-- The money-demand condition (14) in marginal form, O&R p. 665: `χ/m_t = ι_t/C_t`
(see `moneyCond_iff_book`). -/
def MoneyCond (E : HouseholdEnv) (p : HouseholdPlan) : Prop :=
  ∀ t, E.χ / p.m t = E.uc t / p.C t

/-- The labour–leisure condition (15) in marginal form, O&R p. 665:
`κ y_t = Z_t ((θ−1)/θ) y_t^{(θ−1)/θ − 1} / C_t` (see `labourCond_iff_book`). -/
def LabourCond (E : HouseholdEnv) (p : HouseholdPlan) : Prop :=
  ∀ t, E.κ * p.y t = E.Z t * ((E.θ - 1) / E.θ) * p.y t ^ ((E.θ - 1) / E.θ - 1) / p.C t

end HouseholdEnv

/-- **(14) in the book's form**, O&R p. 665: with `ι = i/(1+i)`, `i > 0`, `C, m > 0`, the
marginal condition `χ/m = ι/C` is `m = χ C (1 + i)/i`. -/
theorem moneyCond_iff_book {χ i C m : ℝ} (hi : 0 < i) (hC : 0 < C) (hm : 0 < m) (hχ : 0 < χ) :
    χ / m = i / (1 + i) / C ↔ m = χ * C * ((1 + i) / i) := by
  have := hi.ne'
  have : (1 + i) ≠ 0 := by linarith
  have := hC.ne'
  have := hm.ne'
  constructor
  · intro h; field_simp at h ⊢; linarith
  · intro h; rw [h]; field_simp

/-- **(15) in the book's form**, O&R p. 665: for `y, C, Z, κ > 0` and `θ > 1`, the marginal
condition `κ y = Z ((θ−1)/θ) y^{(θ−1)/θ − 1}/C` is `y^{(θ+1)/θ} = ((θ−1)/(θκ)) Z / C`
(with `Z = (Cᵂ)^{1/θ}` this is (15)). -/
theorem labourCond_iff_book {θ κ y C Z : ℝ} (hθ : 1 < θ) (hκ : 0 < κ) (hy : 0 < y)
    (hC : 0 < C) :
    κ * y = Z * ((θ - 1) / θ) * y ^ ((θ - 1) / θ - 1) / C ↔
      y ^ ((θ + 1) / θ) = (θ - 1) / (θ * κ) * Z / C := by
  have hθ0 : θ ≠ 0 := by linarith
  have hsplit : y ^ ((θ + 1) / θ) = y * y ^ (1 - (θ - 1) / θ) := by
    rw [← rpow_one_add' hy.le]
    · congr 1; field_simp; ring
    · have : 1 + (1 - (θ - 1) / θ) = (θ + 1) / θ := by field_simp; ring
      rw [this]; positivity
  have hinv : y ^ ((θ - 1) / θ - 1) = (y ^ (1 - (θ - 1) / θ))⁻¹ := by
    rw [← rpow_neg hy.le]; congr 1; ring
  have hpos := rpow_pos_of_pos hy (1 - (θ - 1) / θ)
  rw [hsplit, hinv]
  have := hC.ne'
  have := hκ.ne'
  constructor
  · intro h; field_simp at h ⊢; linarith
  · intro h; field_simp at h ⊢; linarith

namespace HouseholdEnv

/-- **Iterated Euler equation** (13): `β^s/C_s = R_s/C_0` (O&R p. 665). -/
theorem discounted_marginal_utility {E : HouseholdEnv} {p : HouseholdPlan}
    (hβ : 0 < E.β) (hr : ∀ t, 0 < 1 + E.r t) (hC : ∀ t, 0 < p.C t) (he : E.EulerCond p)
    (s : ℕ) : E.β ^ s / p.C s = marketDiscount E.r s / p.C 0 := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [marketDiscount_succ, pow_succ, he s]
    have := (hC s).ne'
    have := (hr (s + 1)).ne'
    have := hβ.ne'
    have hC0 := (hC 0).ne'
    rw [div_eq_div_iff (by positivity) hC0] at ih
    field_simp
    linear_combination ih

/-- A finite modification of a summable sequence (copied, with its proof, from the
`MoneyExchangeRates` project's `MoneyInUtility.tsum_eq_add_of_eqOn_compl` so that this project
builds on its own): if `g` agrees with `f` off a finite set `S`, then `g` is summable and
`Σ g = Σ f + Σ_{t∈S} (g t − f t)`. Used for the perturbation arguments of O&R p. 665. -/
theorem tsum_eq_add_of_eqOn_compl {f g : ℕ → ℝ} (hf : Summable f) (S : Finset ℕ)
    (hfg : ∀ t, t ∉ S → g t = f t) :
    Summable g ∧ ∑' t, g t = ∑' t, f t + ∑ t ∈ S, (g t - f t) := by
  have hd : Summable fun t => g t - f t :=
    summable_of_ne_finset_zero (s := S) fun t ht => by rw [hfg t ht, sub_self]
  have hg : g = fun t => f t + (g t - f t) := by funext t; ring
  refine ⟨hg ▸ hf.add hd, ?_⟩
  have h1 : ∑' t, (g t - f t) = ∑ t ∈ S, (g t - f t) :=
    tsum_eq_sum (f := fun t => g t - f t) (s := S) fun t ht => by rw [hfg t ht, sub_self]
  calc ∑' t, g t = ∑' t, (f t + (g t - f t)) := tsum_congr fun t => by ring
    _ = _ := by rw [hf.tsum_add hd, h1]

/-- **The per-period supporting inequality** behind sufficiency (O&R (12)–(15)): at a point where
(14) and (15) hold, for any rival `(C', m', y')` with positive entries,
`u(C', m', y') − u(C, m, y) ≤ (x' − x)/C`, where `x` is the period outlay. -/
theorem period_gain_le {E : HouseholdEnv} (hχ : 0 < E.χ) (hθ : 1 < E.θ) {t : ℕ}
    (hZ : 0 < E.Z t) {c k y c' k' y' : ℝ} (hc : 0 < c) (hk : 0 < k) (hy : 0 < y)
    (hc' : 0 < c') (hk' : 0 < k') (hy' : 0 < y')
    (hmoney : E.χ / k = E.uc t / c)
    (hlab : E.κ * y = E.Z t * ((E.θ - 1) / E.θ) * y ^ ((E.θ - 1) / E.θ - 1) / c) :
    E.periodUtility c' k' y' - E.periodUtility c k y ≤
      ((c' + E.uc t * k' + E.τ t - E.Z t * y' ^ ((E.θ - 1) / E.θ)) -
        (c + E.uc t * k + E.τ t - E.Z t * y ^ ((E.θ - 1) / E.θ))) / c := by
  unfold periodUtility
  set ρ := (E.θ - 1) / E.θ with hρ
  have hρ0 : 0 < ρ := div_pos (by linarith) (by linarith)
  have hρ1 : ρ < 1 := by rw [hρ, div_lt_one (by linarith)]; linarith
  have hlog1 : Real.log c' - Real.log c ≤ (c' - c) / c := by
    rw [← Real.log_div hc'.ne' hc.ne']
    have := Real.log_le_sub_one_of_pos (div_pos hc' hc)
    have e : c' / c - 1 = (c' - c) / c := by field_simp
    linarith
  have hlog2 : Real.log k' - Real.log k ≤ (k' - k) / k := by
    rw [← Real.log_div hk'.ne' hk.ne']
    have := Real.log_le_sub_one_of_pos (div_pos hk' hk)
    have e : k' / k - 1 = (k' - k) / k := by field_simp
    linarith
  have htan := rpow_le_tangent hρ0 hρ1 hy hy'.le
  have hZt := mul_le_mul_of_nonneg_left htan hZ.le
  have hm2 : E.χ * (Real.log k' - Real.log k) ≤ E.uc t * (k' - k) / c := by
    have := mul_le_mul_of_nonneg_left hlog2 hχ.le
    have e : E.χ * ((k' - k) / k) = E.χ / k * (k' - k) := by ring
    rw [e, hmoney] at this
    have e2 : E.uc t / c * (k' - k) = E.uc t * (k' - k) / c := by ring
    linarith
  have hq : -(E.κ / 2 * y' ^ 2) + E.κ / 2 * y ^ 2 ≤ -(E.κ * y) * (y' - y) := by
    have : 0 ≤ E.κ / 2 * (y' - y) ^ 2 := by
      have := sq_nonneg (y' - y)
      have hκ : 0 ≤ E.κ := by
        by_contra hneg
        push Not at hneg
        have h1 : E.κ * y < 0 := mul_neg_of_neg_of_pos hneg hy
        have h2 : 0 < E.Z t * ρ * y ^ (ρ - 1) / c :=
          div_pos (mul_pos (mul_pos hZ hρ0) (rpow_pos_of_pos hy _)) hc
        linarith
      positivity
    nlinarith
  rw [hlab] at hq
  have hq2 : -(E.Z t * ρ * y ^ (ρ - 1) / c) * (y' - y) =
      -(E.Z t * (y ^ ρ + ρ * y ^ (ρ - 1) * (y' - y)) - E.Z t * y ^ ρ) / c := by
    field_simp
    ring
  rw [hq2] at hq
  have hdiv : -(E.Z t * (y ^ ρ + ρ * y ^ (ρ - 1) * (y' - y)) - E.Z t * y ^ ρ) / c ≤
      -(E.Z t * y' ^ ρ - E.Z t * y ^ ρ) / c := by
    apply div_le_div_of_nonneg_right _ hc.le
    linarith
  have e3 : ((c' + E.uc t * k' + E.τ t - E.Z t * y' ^ ρ) -
      (c + E.uc t * k + E.τ t - E.Z t * y ^ ρ)) / c =
      (c' - c) / c + E.uc t * (k' - k) / c + -(E.Z t * y' ^ ρ - E.Z t * y ^ ρ) / c := by
    field_simp
    ring
  rw [e3]
  linarith

/-- **Sufficiency of (13)–(15) and the TVC** (O&R pp. 665–666, T2(a)): for a regular
environment, an admissible plan satisfying the Euler equation (13), the money-demand condition
(14), the labour–leisure condition (15) and the transversality condition is optimal among ALL
admissible (no-Ponzi) plans. Proof: the supporting inequality `period_gain_le`, the iterated
Euler equation and the present-value identity bound the gain of any rival over the first `T`
periods by `(R_T W_T − R_T W'_T)/C_0`; the TVC and the rival's no-Ponzi condition make this
frequently arbitrarily small. -/
theorem isOptimal_of_foc {E : HouseholdEnv} {p : HouseholdPlan} (hreg : E.Regular)
    (hadm : E.Admissible p) (he : E.EulerCond p) (hmo : E.MoneyCond p) (hla : E.LabourCond p)
    (htvc : E.Transversality (E.wealthPath p)) : E.IsOptimal p := by
  obtain ⟨hβ, hχ, _, hθ, hr, hZ⟩ := hreg
  refine ⟨hadm, fun q hq => ?_⟩
  obtain ⟨hC, hm, hy, hsum, -⟩ := hadm
  obtain ⟨hC', hm', hy', hsum', hnp'⟩ := hq
  set lam0 := 1 / p.C 0 with hlam0
  have hlam : 0 < lam0 := div_pos one_pos (hC 0)
  have hterm : ∀ s, E.β ^ s * E.periodUtility (q.C s) (q.m s) (q.y s) -
      E.β ^ s * E.periodUtility (p.C s) (p.m s) (p.y s) ≤
      lam0 * (marketDiscount E.r s * E.outlay q s - marketDiscount E.r s * E.outlay p s) := by
    intro s
    have t := period_gain_le hχ hθ (hZ s) (hC s) (hm s) (hy s) (hC' s) (hm' s) (hy' s)
      (hmo s) (hla s)
    have hb := pow_pos hβ s
    have h2 := mul_le_mul_of_nonneg_left t hb.le
    have hd := discounted_marginal_utility hβ hr hC he s
    have key : E.β ^ s * (((q.C s + E.uc s * q.m s + E.τ s - E.Z s * q.y s ^ ((E.θ - 1) / E.θ)) -
        (p.C s + E.uc s * p.m s + E.τ s - E.Z s * p.y s ^ ((E.θ - 1) / E.θ))) / p.C s) =
        lam0 * (marketDiscount E.r s * E.outlay q s - marketDiscount E.r s * E.outlay p s) := by
      unfold outlay
      rw [hlam0]
      have e : E.β ^ s * ((q.C s + E.uc s * q.m s + E.τ s - E.Z s * q.y s ^ ((E.θ - 1) / E.θ) -
          (p.C s + E.uc s * p.m s + E.τ s - E.Z s * p.y s ^ ((E.θ - 1) / E.θ))) / p.C s) =
          E.β ^ s / p.C s * (q.C s + E.uc s * q.m s + E.τ s - E.Z s * q.y s ^ ((E.θ - 1) / E.θ) -
          (p.C s + E.uc s * p.m s + E.τ s - E.Z s * p.y s ^ ((E.θ - 1) / E.θ))) := by ring
      rw [e, hd]
      ring
    linarith
  have hpartial : ∀ T, ∑ s ∈ Finset.range T,
      (E.β ^ s * E.periodUtility (q.C s) (q.m s) (q.y s) -
        E.β ^ s * E.periodUtility (p.C s) (p.m s) (p.y s)) ≤
      lam0 * (marketDiscount E.r T * E.wealthPath p T -
        marketDiscount E.r T * E.wealthPath q T) := by
    intro T
    have h1 := wealth_pv_identity hr E.W0 (E.outlay p) T
    have h2 := wealth_pv_identity hr E.W0 (E.outlay q) T
    have hle := Finset.sum_le_sum fun s (_ : s ∈ Finset.range T) => hterm s
    unfold wealthPath
    have e : ∑ i ∈ Finset.range T, lam0 * (marketDiscount E.r i * E.outlay q i -
        marketDiscount E.r i * E.outlay p i) =
        lam0 * (marketDiscount E.r T * wealth E.r E.W0 (E.outlay p) T -
        marketDiscount E.r T * wealth E.r E.W0 (E.outlay q) T) := by
      rw [← Finset.mul_sum, Finset.sum_sub_distrib]
      congr 1
      linarith
    rw [e] at hle
    exact hle
  have hlim : Tendsto (fun T => ∑ s ∈ Finset.range T,
      (E.β ^ s * E.periodUtility (q.C s) (q.m s) (q.y s) -
        E.β ^ s * E.periodUtility (p.C s) (p.m s) (p.y s))) atTop
      (𝓝 (E.utility q - E.utility p)) :=
    (hsum'.hasSum.sub hsum.hasSum).tendsto_sum_nat
  by_contra hlt
  push Not at hlt
  set d := E.utility q - E.utility p with hddef
  have hd : 0 < d := by linarith
  set ε := d / (4 * (lam0 + 1)) with hεdef
  have hε : 0 < ε := by positivity
  have hsmall : 2 * lam0 * ε < d := by
    have h4 : ε * (4 * (lam0 + 1)) = d := by rw [hεdef]; field_simp
    nlinarith
  obtain ⟨T, hT3, hT1, hT2⟩ :=
    ((htvc ε hε).and_eventually ((hlim.eventually (lt_mem_nhds hsmall)).and (hnp' ε hε))).exists
  have hP := hpartial T
  have hab : marketDiscount E.r T * E.wealthPath p T -
      marketDiscount E.r T * E.wealthPath q T ≤ 2 * ε := by linarith
  have := mul_le_mul_of_nonneg_left hab hlam.le
  linarith

/-- The derivative of `ε ↦ log(c + ε a)` at `0` is `a/c` (used in the perturbation arguments of
O&R p. 665). -/
theorem hasDerivAt_log_affine {c a : ℝ} (hc : 0 < c) :
    HasDerivAt (fun ε => Real.log (c + ε * a)) (a / c) 0 := by
  have h1 : HasDerivAt (fun ε : ℝ => c + ε * a) a 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const a).const_add c
  have h2 := h1.log (by simp [hc.ne'])
  simpa using h2

/-- Near `0`, `c + ε a` stays positive when `c > 0` (O&R p. 665, perturbations). -/
theorem eventually_pos_affine {c a : ℝ} (hc : 0 < c) :
    ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < c + ε * a :=
  ((by fun_prop : Continuous fun ε : ℝ => c + ε * a).tendsto 0).eventually
    (lt_mem_nhds (by simpa using hc))

/-- The no-Ponzi condition depends only on the tail of the wealth path (O&R p. 666). -/
theorem noPonzi_congr {E : HouseholdEnv} {W W' : ℕ → ℝ} (h : E.NoPonzi W)
    (heq : ∀ᶠ T in atTop, W' T = W T) : E.NoPonzi W' := by
  intro ε hε
  filter_upwards [h ε hε, heq] with T h1 h2
  rw [h2]
  exact h1

/-- **Necessity of the Euler equation (13)**, O&R p. 665 (T2(b)): at an optimal plan,
`C_{t+1} = β(1 + r_{t+1}) C_t`. Proof: consume `ε` less at `t` and `(1 + r_{t+1})ε` more at
`t + 1`; wealth is unchanged from `t + 2` on, so the perturbed plan is admissible, and the
first-order condition of the resulting one-variable problem at `ε = 0` is (13). -/
theorem euler_of_optimal {E : HouseholdEnv} {p : HouseholdPlan} (hβ : 0 < E.β)
    (hopt : E.IsOptimal p) (s : ℕ) : p.C (s + 1) = E.β * (1 + E.r (s + 1)) * p.C s := by
  obtain ⟨⟨hC, hm, hy, hsum, hnp⟩, hmax⟩ := hopt
  set a := 1 + E.r (s + 1) with ha
  let D : ℝ → ℕ → ℝ := fun ε t =>
    if t = s then p.C s + ε * (-1) else if t = s + 1 then p.C (s + 1) + ε * a else p.C t
  let q : ℝ → HouseholdPlan := fun ε => ⟨D ε, p.m, p.y⟩
  have hne : s + 1 ≠ s := Nat.succ_ne_self s
  have hDs : ∀ ε, D ε s = p.C s + ε * (-1) := fun ε => by simp [D]
  have hDs1 : ∀ ε, D ε (s + 1) = p.C (s + 1) + ε * a := fun ε => by simp [D]
  have hoff : ∀ ε t, t ∉ ({s, s + 1} : Finset ℕ) → D ε t = p.C t := fun ε t ht => by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ht
    simp [D, ht.1, ht.2]
  have hout_off : ∀ ε t, t ∉ ({s, s + 1} : Finset ℕ) → E.outlay (q ε) t = E.outlay p t :=
    fun ε t ht => by simp only [outlay, q, hoff ε t ht]
  have hw : ∀ ε n, E.wealthPath (q ε) (s + 2 + n) = E.wealthPath p (s + 2 + n) := by
    intro ε n
    refine wealth_congr_after ?_ (fun t ht => hout_off ε t (by simp; omega)) n
    have hbef : wealth E.r E.W0 (E.outlay (q ε)) s = wealth E.r E.W0 (E.outlay p) s :=
      wealth_congr_before fun t ht => hout_off ε t (by simp; omega)
    rw [show s + 2 = s + 1 + 1 by ring, wealth_succ, wealth_succ (x := E.outlay p), wealth_succ,
      wealth_succ (x := E.outlay p), hbef]
    simp only [outlay, q, hDs, hDs1]
    ring
  have hnpD : ∀ ε, E.NoPonzi (E.wealthPath (q ε)) := fun ε => by
    refine noPonzi_congr hnp ?_
    filter_upwards [eventually_ge_atTop (s + 2)] with T hT
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hT
    exact hw ε n
  have huD : ∀ ε, Summable (fun t => E.β ^ t * E.periodUtility ((q ε).C t) ((q ε).m t)
      ((q ε).y t)) ∧ E.utility (q ε) = E.utility p +
      (E.β ^ s * Real.log (p.C s + ε * (-1)) - E.β ^ s * Real.log (p.C s)) +
      (E.β ^ (s + 1) * Real.log (p.C (s + 1) + ε * a) -
        E.β ^ (s + 1) * Real.log (p.C (s + 1))) := by
    intro ε
    obtain ⟨h1, h2⟩ := tsum_eq_add_of_eqOn_compl hsum {s, s + 1}
      (g := fun t => E.β ^ t * E.periodUtility ((q ε).C t) ((q ε).m t) ((q ε).y t))
      fun t ht => by simp only [q, hoff ε t ht]
    refine ⟨h1, ?_⟩
    unfold utility
    rw [h2, Finset.sum_pair hne.symm]
    simp only [q, hDs, hDs1, periodUtility]
    ring
  have hloc : IsLocalMax (fun ε => E.β ^ s * Real.log (p.C s + ε * (-1)) +
      E.β ^ (s + 1) * Real.log (p.C (s + 1) + ε * a)) 0 := by
    filter_upwards [eventually_pos_affine (a := -1) (hC s),
      eventually_pos_affine (a := a) (hC (s + 1))] with ε h1 h2
    have hpos : ∀ t, 0 < D ε t := fun t => by
      by_cases ht : t = s
      · rw [ht, hDs]; exact h1
      by_cases ht1 : t = s + 1
      · rw [ht1, hDs1]; exact h2
      rw [hoff ε t (by simp [ht, ht1])]
      exact hC t
    have := hmax (q ε) ⟨hpos, hm, hy, (huD ε).1, hnpD ε⟩
    rw [(huD ε).2] at this
    simp only [zero_mul, add_zero]
    linarith
  have hA := (hasDerivAt_log_affine (a := -1) (hC s)).const_mul (E.β ^ s)
  have hB := (hasDerivAt_log_affine (a := a) (hC (s + 1))).const_mul (E.β ^ (s + 1))
  have h0 := hloc.hasDerivAt_eq_zero (hA.add hB)
  have hβs : 0 < E.β ^ s := pow_pos hβ s
  have hCs := (hC s).ne'
  have hCs1 := (hC (s + 1)).ne'
  rw [pow_succ] at h0
  field_simp at h0
  have h3 : E.β ^ s * (E.β * a * p.C s - p.C (s + 1)) = 0 := by linarith
  have := (mul_eq_zero.1 h3).resolve_left hβs.ne'
  linarith

/-- **Necessity of the money-demand condition (14)**, O&R p. 665 (T2(b)): at an optimal plan,
`χ/m_t = ι_t/C_t`. Proof: hold `ε` more real balances and consume `ι_t ε` less; the outlay, hence
the whole wealth path, is unchanged. -/
theorem money_foc_of_optimal {E : HouseholdEnv} {p : HouseholdPlan} (hβ : 0 < E.β)
    (hopt : E.IsOptimal p) (s : ℕ) : E.χ / p.m s = E.uc s / p.C s := by
  obtain ⟨⟨hC, hm, hy, hsum, hnp⟩, hmax⟩ := hopt
  let DC : ℝ → ℕ → ℝ := fun ε t => if t = s then p.C s + ε * (-E.uc s) else p.C t
  let Dm : ℝ → ℕ → ℝ := fun ε t => if t = s then p.m s + ε * 1 else p.m t
  let q : ℝ → HouseholdPlan := fun ε => ⟨DC ε, Dm ε, p.y⟩
  have hout : ∀ ε, E.outlay (q ε) = E.outlay p := fun ε => by
    funext t
    by_cases ht : t = s
    · subst ht; simp [outlay, q, DC, Dm]; ring
    · simp [outlay, q, DC, Dm, ht]
  have hoffC : ∀ ε t, t ∉ ({s} : Finset ℕ) → DC ε t = p.C t := fun ε t ht => by
    simp only [Finset.mem_singleton] at ht; simp [DC, ht]
  have hoffm : ∀ ε t, t ∉ ({s} : Finset ℕ) → Dm ε t = p.m t := fun ε t ht => by
    simp only [Finset.mem_singleton] at ht; simp [Dm, ht]
  have huD : ∀ ε, Summable (fun t => E.β ^ t * E.periodUtility ((q ε).C t) ((q ε).m t)
      ((q ε).y t)) ∧ E.utility (q ε) = E.utility p +
      (E.β ^ s * (Real.log (p.C s + ε * (-E.uc s)) + E.χ * Real.log (p.m s + ε * 1)) -
        E.β ^ s * (Real.log (p.C s) + E.χ * Real.log (p.m s))) := by
    intro ε
    obtain ⟨h1, h2⟩ := tsum_eq_add_of_eqOn_compl hsum {s}
      (g := fun t => E.β ^ t * E.periodUtility ((q ε).C t) ((q ε).m t) ((q ε).y t))
      fun t ht => by simp only [q, hoffC ε t ht, hoffm ε t ht]
    refine ⟨h1, ?_⟩
    unfold utility
    rw [h2, Finset.sum_singleton]
    simp only [q, DC, Dm, ↓reduceIte, periodUtility]
    ring
  have hloc : IsLocalMax (fun ε => E.β ^ s * (Real.log (p.C s + ε * (-E.uc s)) +
      E.χ * Real.log (p.m s + ε * 1))) 0 := by
    filter_upwards [eventually_pos_affine (a := -E.uc s) (hC s),
      eventually_pos_affine (a := 1) (hm s)] with ε h1 h2
    have hposC : ∀ t, 0 < DC ε t := fun t => by
      by_cases ht : t = s
      · subst ht; simpa [DC] using h1
      · simpa [DC, ht] using hC t
    have hposm : ∀ t, 0 < Dm ε t := fun t => by
      by_cases ht : t = s
      · subst ht; simpa [Dm] using h2
      · simpa [Dm, ht] using hm t
    have hnpD : E.NoPonzi (E.wealthPath (q ε)) := by
      unfold wealthPath; rw [hout ε]; exact hnp
    have := hmax (q ε) ⟨hposC, hposm, hy, (huD ε).1, hnpD⟩
    rw [(huD ε).2] at this
    simp only [zero_mul, add_zero]
    linarith
  have hA := ((hasDerivAt_log_affine (a := -E.uc s) (hC s)).add
    ((hasDerivAt_log_affine (a := 1) (hm s)).const_mul E.χ)).const_mul (E.β ^ s)
  have h0 := hloc.hasDerivAt_eq_zero hA
  have hβs : 0 < E.β ^ s := pow_pos hβ s
  have h3 : E.β ^ s * (E.χ / p.m s - E.uc s / p.C s) = 0 := by
    have e : E.β ^ s * (-E.uc s / p.C s + E.χ * (1 / p.m s)) =
      E.β ^ s * (E.χ / p.m s - E.uc s / p.C s) := by ring
    linarith
  have := (mul_eq_zero.1 h3).resolve_left hβs.ne'
  linarith

/-- **Necessity of the labour–leisure condition (15)**, O&R p. 665 (T2(b)): at an optimal plan,
`κ y_t = Z_t ((θ−1)/θ) y_t^{(θ−1)/θ−1}/C_t`. Proof: produce `ε` more and consume the extra
revenue `Z_t((y_t + ε)^{(θ−1)/θ} − y_t^{(θ−1)/θ})`; the outlay is unchanged. -/
theorem labour_foc_of_optimal {E : HouseholdEnv} {p : HouseholdPlan} (hβ : 0 < E.β)
    (hopt : E.IsOptimal p) (s : ℕ) :
    E.κ * p.y s = E.Z s * ((E.θ - 1) / E.θ) * p.y s ^ ((E.θ - 1) / E.θ - 1) / p.C s := by
  obtain ⟨⟨hC, hm, hy, hsum, hnp⟩, hmax⟩ := hopt
  set ρ := (E.θ - 1) / E.θ with hρ
  set g : ℝ → ℝ := fun ε => p.C s + E.Z s * ((p.y s + ε) ^ ρ - p.y s ^ ρ) with hg
  let DC : ℝ → ℕ → ℝ := fun ε t => if t = s then g ε else p.C t
  let Dy : ℝ → ℕ → ℝ := fun ε t => if t = s then p.y s + ε else p.y t
  let q : ℝ → HouseholdPlan := fun ε => ⟨DC ε, p.m, Dy ε⟩
  have hout : ∀ ε, E.outlay (q ε) = E.outlay p := fun ε => by
    funext t
    by_cases ht : t = s
    · subst ht; simp only [outlay, q, DC, Dy, ↓reduceIte, hg]; ring
    · simp [outlay, q, DC, Dy, ht]
  have hoffC : ∀ ε t, t ∉ ({s} : Finset ℕ) → DC ε t = p.C t := fun ε t ht => by
    simp only [Finset.mem_singleton] at ht; simp [DC, ht]
  have hoffy : ∀ ε t, t ∉ ({s} : Finset ℕ) → Dy ε t = p.y t := fun ε t ht => by
    simp only [Finset.mem_singleton] at ht; simp [Dy, ht]
  have huD : ∀ ε, Summable (fun t => E.β ^ t * E.periodUtility ((q ε).C t) ((q ε).m t)
      ((q ε).y t)) ∧ E.utility (q ε) = E.utility p +
      (E.β ^ s * (Real.log (g ε) - E.κ / 2 * (p.y s + ε) ^ 2) -
        E.β ^ s * (Real.log (p.C s) - E.κ / 2 * p.y s ^ 2)) := by
    intro ε
    obtain ⟨h1, h2⟩ := tsum_eq_add_of_eqOn_compl hsum {s}
      (g := fun t => E.β ^ t * E.periodUtility ((q ε).C t) ((q ε).m t) ((q ε).y t))
      fun t ht => by simp only [q, hoffC ε t ht, hoffy ε t ht]
    refine ⟨h1, ?_⟩
    unfold utility
    rw [h2, Finset.sum_singleton]
    simp only [q, DC, Dy, ↓reduceIte, periodUtility]
    ring
  have hpow : HasDerivAt (fun ε => (p.y s + ε) ^ ρ) (ρ * p.y s ^ (ρ - 1)) 0 := by
    have h1 : HasDerivAt (fun ε : ℝ => p.y s + ε) 1 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_add (p.y s)
    have := h1.rpow_const (p := ρ) (Or.inl (by simp [(hy s).ne']))
    simpa using this
  have hgd : HasDerivAt g (E.Z s * (ρ * p.y s ^ (ρ - 1))) 0 := by
    have := (hpow.sub_const (p.y s ^ ρ)).const_mul (E.Z s)
    simpa [hg] using this.const_add (p.C s)
  have hg0 : g 0 = p.C s := by simp [hg]
  have hev1 : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < g ε :=
    hgd.continuousAt.eventually (lt_mem_nhds (by rw [hg0]; exact hC s))
  have hev2 : ∀ᶠ ε in 𝓝 (0 : ℝ), 0 < p.y s + ε * 1 := eventually_pos_affine (hy s)
  have hloc : IsLocalMax (fun ε => E.β ^ s * (Real.log (g ε) - E.κ / 2 * (p.y s + ε) ^ 2)) 0 := by
    filter_upwards [hev1, hev2] with ε h1 h2
    have hposC : ∀ t, 0 < DC ε t := fun t => by
      by_cases ht : t = s
      · subst ht; simpa [DC] using h1
      · simpa [DC, ht] using hC t
    have hposy : ∀ t, 0 < Dy ε t := fun t => by
      by_cases ht : t = s
      · subst ht; simpa [Dy] using h2
      · simpa [Dy, ht] using hy t
    have hnpD : E.NoPonzi (E.wealthPath (q ε)) := by
      unfold wealthPath; rw [hout ε]; exact hnp
    have := hmax (q ε) ⟨hposC, hm, hposy, (huD ε).1, hnpD⟩
    rw [(huD ε).2] at this
    simp only [hg0, add_zero]
    linarith
  have hlogd := hgd.log (by rw [hg0]; exact (hC s).ne')
  rw [hg0] at hlogd
  have hsq : HasDerivAt (fun ε => (p.y s + ε) ^ 2) (2 * p.y s) 0 := by
    have h1 : HasDerivAt (fun ε : ℝ => p.y s + ε) 1 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_add (p.y s)
    have := (hasDerivAt_pow 2 (p.y s + 0)).comp (0 : ℝ) h1
    simpa [Function.comp_def] using this
  have hA := (hlogd.sub (hsq.const_mul (E.κ / 2))).const_mul (E.β ^ s)
  have h0 := hloc.hasDerivAt_eq_zero hA
  have hβs : 0 < E.β ^ s := pow_pos hβ s
  have h3 : E.β ^ s * (E.Z s * ρ * p.y s ^ (ρ - 1) / p.C s - E.κ * p.y s) = 0 := by
    have e : E.β ^ s * (E.Z s * (ρ * p.y s ^ (ρ - 1)) / p.C s - E.κ / 2 * (2 * p.y s)) =
      E.β ^ s * (E.Z s * ρ * p.y s ^ (ρ - 1) / p.C s - E.κ * p.y s) := by ring
    linarith
  have := (mul_eq_zero.1 h3).resolve_left hβs.ne'
  linarith

/-- **Necessity of the transversality condition** (O&R (16), p. 666, and fn 7; T2(c)): at an
optimal plan, `liminf R_T W_T ≤ 0`. Otherwise discounted wealth would eventually exceed some
`ε > 0`, and consuming `ε` more at date `0` would keep the no-Ponzi condition and raise utility
(log utility is strictly increasing). -/
theorem transversality_of_optimal {E : HouseholdEnv} {p : HouseholdPlan}
    (hr : ∀ t, 0 < 1 + E.r t) (hopt : E.IsOptimal p) : E.Transversality (E.wealthPath p) := by
  obtain ⟨⟨hC, hm, hy, hsum, _⟩, hmax⟩ := hopt
  intro ε hε
  by_contra h
  rw [not_frequently] at h
  let C' : ℕ → ℝ := fun t => if t = 0 then p.C 0 + ε else p.C t
  let q : HouseholdPlan := ⟨C', p.m, p.y⟩
  have hoff : ∀ t, t ∉ ({0} : Finset ℕ) → C' t = p.C t := fun t ht => by
    simp only [Finset.mem_singleton] at ht; simp [C', ht]
  obtain ⟨h1, h2⟩ := tsum_eq_add_of_eqOn_compl hsum {0}
    (g := fun t => E.β ^ t * E.periodUtility (q.C t) (q.m t) (q.y t))
    fun t ht => by simp only [q, hoff t ht]
  have hpos : ∀ t, 0 < C' t := fun t => by
    by_cases ht : t = 0
    · subst ht; simp only [C', ↓reduceIte]; linarith [hC 0]
    · simpa [C', ht] using hC t
  have hnp' : E.NoPonzi (E.wealthPath q) := by
    intro e he
    filter_upwards [h, eventually_ge_atTop 1] with T hT hT1
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hT1
    push Not at hT
    have hsh := wealth_shift_date0 (W0 := E.W0) (x := E.outlay p) (x' := E.outlay q) (ε := ε) hr
      (by simp [outlay, q, C']; ring) (fun s hs => by simp [outlay, q, C', hs]) n
    unfold wealthPath at hT ⊢
    rw [hsh]
    linarith
  have hgain := hmax q ⟨hpos, hm, hy, h1, hnp'⟩
  unfold utility at hgain
  rw [h2, Finset.sum_singleton] at hgain
  have hu : Real.log (p.C 0) < Real.log (p.C 0 + ε) :=
    Real.log_lt_log (hC 0) (by linarith)
  simp [q, C', periodUtility] at hgain
  linarith

/-- **Exact characterisation of the household optimum** (O&R (12)–(16), pp. 665–666, T2): in a
regular environment an admissible plan is optimal IF AND ONLY IF it satisfies the Euler equation
(13), the money-demand condition (14), the labour–leisure condition (15) and the transversality
condition. -/
theorem isOptimal_iff {E : HouseholdEnv} {p : HouseholdPlan} (hreg : E.Regular) :
    E.IsOptimal p ↔ E.Admissible p ∧ E.EulerCond p ∧ E.MoneyCond p ∧ E.LabourCond p ∧
      E.Transversality (E.wealthPath p) := by
  constructor
  · intro hopt
    exact ⟨hopt.1, euler_of_optimal hreg.1 hopt, money_foc_of_optimal hreg.1 hopt,
      labour_foc_of_optimal hreg.1 hopt, transversality_of_optimal hreg.2.2.2.2.1 hopt⟩
  · rintro ⟨hadm, he, hmo, hla, htvc⟩
    exact isOptimal_of_foc hreg hadm he hmo hla htvc

end HouseholdEnv

/-! ## The book's transversality condition (16) -/

/-- **The book's TVC (16) versus ours**, O&R p. 666: for any bond path `B`, money path `N`
(`N t` brought into date `t`) and prices `P > 0`, with `m_T = N_{T+1}/P_T`,
`R_T(B_{T+1} + m_T) = R_{T+1}((1+r_{T+1})B_{T+1} + N_{T+1}/P_{T+1}) + R_T ι_T m_T`. So when the
present value of the rental cost of money `R_T ι_T m_T` vanishes, (16) is exactly
`R_{T+1} W_{T+1} → 0` (`book_tvc_iff`). -/
theorem book_tvc_identity {r P B N : ℕ → ℝ} (hr : ∀ t, 0 < 1 + r t) (hP : ∀ t, 0 < P t)
    (T : ℕ) :
    marketDiscount r T * (B (T + 1) + N (T + 1) / P T) =
      marketDiscount r (T + 1) * ((1 + r (T + 1)) * B (T + 1) + N (T + 1) / P (T + 1)) +
      marketDiscount r T * (userCost r P T * (N (T + 1) / P T)) := by
  rw [marketDiscount_succ]
  unfold userCost
  have := (hr (T + 1)).ne'
  have := (hP T).ne'
  have := (hP (T + 1)).ne'
  field_simp
  ring

/-- **(16) is our TVC when rental costs vanish in present value**, O&R p. 666. -/
theorem book_tvc_iff {r P B N : ℕ → ℝ} (hr : ∀ t, 0 < 1 + r t) (hP : ∀ t, 0 < P t)
    (hrent : Tendsto (fun T => marketDiscount r T * (userCost r P T * (N (T + 1) / P T)))
      atTop (𝓝 0)) :
    Tendsto (fun T => marketDiscount r T * (B (T + 1) + N (T + 1) / P T)) atTop (𝓝 0) ↔
      Tendsto (fun T => marketDiscount r (T + 1) *
        ((1 + r (T + 1)) * B (T + 1) + N (T + 1) / P (T + 1))) atTop (𝓝 0) := by
  have hid : ∀ T, marketDiscount r T * (B (T + 1) + N (T + 1) / P T) =
      marketDiscount r (T + 1) * ((1 + r (T + 1)) * B (T + 1) + N (T + 1) / P (T + 1)) +
      marketDiscount r T * (userCost r P T * (N (T + 1) / P T)) :=
    book_tvc_identity hr hP
  constructor
  · intro h
    have := h.sub hrent
    simp only [sub_zero] at this
    refine this.congr fun T => ?_
    rw [hid T]; ring
  · intro h
    have := h.add hrent
    simp only [add_zero] at this
    exact this.congr fun T => (hid T).symm

/-! ## Aggregation: (17)–(18) and Walras's law (T3) -/

/-- **The real budget (54) from (8) and (9)**, O&R p. 663, p. 664 and p. 675: with the government
rebating seigniorage (`0 = τ_t + (M_t − M_{t−1})/P_t`), the nominal budget (8) of a Home agent
becomes `B_{t+1} = (1 + r_t)B_t + (p_t(h)/P_t) y_t − C_t`: money and taxes cancel. -/
theorem real_budget_of_nominal {P B B1 M Mprev r ph y C τ : ℝ} (hP : 0 < P)
    (hbud : P * B1 + M = P * (1 + r) * B + Mprev + ph * y - P * C - P * τ)
    (hgov : 0 = τ + (M - Mprev) / P) : B1 = (1 + r) * B + ph / P * y - C := by
  have := hP.ne'
  field_simp at hgov
  field_simp
  linear_combination hbud + hgov

/-- **Global goods-market clearing (18)**, O&R p. 666 and fn 8: if both countries' real budgets
(54) hold at the common real rate and net foreign assets sum to zero before and after (17),
then `Cᵂ = n (p(h)/P) y + (1 − n)(p*(f)/P*) y* = Yᵂ`. -/
theorem world_goods_market {n r B B1 Bs Bs1 qh y C qf ys Cs : ℝ}
    (hH : B1 = (1 + r) * B + qh * y - C) (hF : Bs1 = (1 + r) * Bs + qf * ys - Cs)
    (h17 : n * B1 + (1 - n) * Bs1 = 0) (h17' : n * B + (1 - n) * Bs = 0) :
    worldConsumption n C Cs = n * qh * y + (1 - n) * qf * ys := by
  unfold worldConsumption
  linear_combination n * hH + (1 - n) * hF - h17 + (1 + r) * h17'

/-- **Walras's law from the price index** (O&R (18), fn 8, and (5)): if relative prices satisfy
the price-index normalisation `n q^{1−θ} + (1−n) q*^{1−θ} = 1` (`bloc_relative_price_sum`) and
outputs are on the world demand curve (10), `y = q^{−θ} Cᵂ`, `y* = q*^{−θ} Cᵂ`, then world real
income equals world demand: `n q y + (1 − n) q* y* = Cᵂ`. -/
theorem walras_identity {θ n q qs X y ys : ℝ} (hq : 0 < q) (hqs : 0 < qs)
    (hsum : n * q ^ (1 - θ) + (1 - n) * qs ^ (1 - θ) = 1) (hy : y = cesDemand θ q 1 X)
    (hys : ys = cesDemand θ qs 1 X) : n * q * y + (1 - n) * qs * ys = X := by
  rw [hy, hys]
  unfold cesDemand
  rw [div_one, div_one]
  have e1 : q * (q ^ (-θ) * X) = q ^ (1 - θ) * X := by
    rw [← mul_assoc, ces_price_mul_demand hq]
  have e2 : qs * (qs ^ (-θ) * X) = qs ^ (1 - θ) * X := by
    rw [← mul_assoc, ces_price_mul_demand hqs]
  calc n * q * (q ^ (-θ) * X) + (1 - n) * qs * (qs ^ (-θ) * X)
      = (n * q ^ (1 - θ) + (1 - n) * qs ^ (1 - θ)) * X := by
        rw [mul_assoc n, mul_assoc (1 - n), e1, e2]; ring
    _ = X := by rw [hsum, one_mul]

/-! ## Steady-state interest rate and income (19)–(21), (26) (T4) -/

/-- The rate of time preference `δ = (1 − β)/β` of (19), O&R p. 667. -/
noncomputable def timePreferenceRate (β : ℝ) : ℝ := (1 - β) / β

/-- `β (1 + δ) = 1` (O&R (19)). -/
theorem beta_mul_one_add_timePreferenceRate {β : ℝ} (hβ : 0 < β) :
    β * (1 + timePreferenceRate β) = 1 := by
  unfold timePreferenceRate
  field_simp
  ring

/-- `δ > 0` for `0 < β < 1` (O&R (19)). -/
theorem timePreferenceRate_pos {β : ℝ} (hβ0 : 0 < β) (hβ1 : β < 1) :
    0 < timePreferenceRate β :=
  div_pos (by linarith) hβ0

/-- **The steady-state real interest rate (19)**, O&R p. 667: if consumption is constant and
positive, the Euler equation (13) forces `r = δ = (1 − β)/β`. -/
theorem steady_state_rate {β r C : ℝ} (hβ : 0 < β) (hC : 0 < C) (he : C = β * (1 + r) * C) :
    r = timePreferenceRate β := by
  unfold timePreferenceRate
  have : β * (1 + r) = 1 := by
    have h := he
    field_simp at h
    nlinarith [hC]
  field_simp
  linarith

/-- **Steady-state income = expenditure (20)**, O&R p. 667, derived exactly as the book describes
(iterate the budget, impose the TVC): if `B_{t+1} = (1 + δ)B_t + I − C` for all `t` with constant
real income `I` and consumption `C`, `δ > 0`, and `B` satisfies both the no-Ponzi condition and
the transversality condition at the discount rate `δ`, then `C = δ B_0 + I` and bonds are constant.
-/
theorem steady_state_budget {δ I C : ℝ} {B : ℕ → ℝ} (hδ : 0 < δ)
    (hbud : ∀ t, B (t + 1) = (1 + δ) * B t + I - C)
    (hnp : ∀ ε > 0, ∀ᶠ T in atTop, -ε < (1 + δ)⁻¹ ^ T * B T)
    (htvc : ∀ ε > 0, ∃ᶠ T in atTop, (1 + δ)⁻¹ ^ T * B T < ε) :
    C = δ * B 0 + I ∧ ∀ t, B t = B 0 := by
  set b := (C - I) / δ with hb
  have hdev : ∀ t, B t - b = (1 + δ) ^ t * (B 0 - b) := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      rw [hbud t, pow_succ]
      have : (1 + δ) * b + I - C = b := by rw [hb]; have := hδ.ne'; field_simp; ring
      linear_combination (1 + δ) * ih + this
  have hd1 : 0 < (1 + δ)⁻¹ := inv_pos.2 (by linarith)
  have hd2 : (1 + δ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hgeo : Tendsto (fun T : ℕ => (1 + δ)⁻¹ ^ T) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one hd1.le hd2
  have hlim : Tendsto (fun T : ℕ => (1 + δ)⁻¹ ^ T * B T) atTop (𝓝 (B 0 - b)) := by
    have h := (hgeo.mul_const b).const_add (B 0 - b)
    simp only [zero_mul, add_zero] at h
    refine h.congr fun T => ?_
    have hT := hdev T
    have hk : (1 + δ)⁻¹ ^ T * (1 + δ) ^ T = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ (by linarith), one_pow]
    have : B T = (1 + δ) ^ T * (B 0 - b) + b := by linarith
    rw [this]
    linear_combination (B 0 - b) * hk.symm
  set L := B 0 - b with hL
  have hL0 : 0 ≤ L := by
    by_contra hneg
    push Not at hneg
    obtain ⟨T, hT1, hT2⟩ := ((hlim.eventually (gt_mem_nhds (show L < L / 2 by linarith))).and
      (hnp (-(L / 2)) (by linarith))).exists
    linarith
  have hL1 : L ≤ 0 := by
    by_contra hpos
    push Not at hpos
    obtain ⟨T, hT1, hT2⟩ := ((htvc (L / 2) (by linarith)).and_eventually
      (hlim.eventually (lt_mem_nhds (show L / 2 < L by linarith)))).exists
    linarith
  have hL00 : B 0 = b := by linarith
  refine ⟨?_, fun t => ?_⟩
  · rw [hL00, hb]; have := hδ.ne'; field_simp; ring
  · have := hdev t
    have hL' : L = 0 := le_antisymm hL1 hL0
    rw [hL', mul_zero] at this
    linarith

/-- **Foreign steady-state income (21)**, O&R p. 667: with `n B + (1 − n) B* = 0` (17), Foreign's
version of (20), `C* = δ B* + I*`, reads `C* = −(n/(1−n)) δ B + I*`. -/
theorem foreign_steady_state_income {n δ B Bs Cs Is : ℝ} (hn1 : n < 1)
    (h17 : n * B + (1 - n) * Bs = 0) (h20 : Cs = δ * Bs + Is) :
    Cs = -(n / (1 - n)) * δ * B + Is := by
  have : (1 - n) ≠ 0 := by linarith
  have hBs : Bs = -(n / (1 - n)) * B := by field_simp; linarith
  rw [h20, hBs]
  ring

/-- **Steady-state real balances (26)**, O&R p. 669: with constant prices the nominal rate equals
the real rate, `i = δ` (fn 9), and (14) gives `M/P = χ (1 + δ) C / δ`. -/
theorem steady_state_real_balances {χ δ C m : ℝ} (h14 : m = χ * C * ((1 + δ) / δ)) :
    m = χ * (1 + δ) / δ * C := by
  rw [h14]; ring

/-! ## Shared parameter bundles -/

/-- The parameters of the nonlinear two-country model of §10.1, O&R pp. 661–667, with the
standing assumptions: `0 < β < 1`, `χ > 0`, `κ > 0`, `θ > 1` (fn 2) and a Home size
`0 < n < 1`. -/
structure ReduxParams where
  β : ℝ
  χ : ℝ
  κ : ℝ
  θ : ℝ
  n : ℝ
  hβ0 : 0 < β
  hβ1 : β < 1
  hχ : 0 < χ
  hκ : 0 < κ
  hθ : 1 < θ
  hn0 : 0 < n
  hn1 : n < 1

namespace ReduxParams

/-- The rate of time preference `δ = (1−β)/β` (O&R (19), p. 667). -/
noncomputable def δ (M : ReduxParams) : ℝ := timePreferenceRate M.β

/-- The monopoly-markup constant `K = (θ−1)/(θκ)` of (15) and (24), O&R p. 665, p. 668. -/
noncomputable def K (M : ReduxParams) : ℝ := (M.θ - 1) / (M.θ * M.κ)

/-- The symmetric steady-state output `ȳ₀ = K^{1/2}` of (24), O&R p. 668. -/
noncomputable def ybar0 (M : ReduxParams) : ℝ := Real.sqrt M.K

/-- `δ > 0` (O&R (19)). -/
theorem δ_pos (M : ReduxParams) : 0 < M.δ := timePreferenceRate_pos M.hβ0 M.hβ1

/-- `β(1 + δ) = 1` (O&R (19)). -/
theorem β_mul_one_add_δ (M : ReduxParams) : M.β * (1 + M.δ) = 1 :=
  beta_mul_one_add_timePreferenceRate M.hβ0

/-- `K > 0` (O&R (24)). -/
theorem K_pos (M : ReduxParams) : 0 < M.K :=
  div_pos (by linarith [M.hθ]) (mul_pos (by linarith [M.hθ]) M.hκ)

/-- `ȳ₀ > 0` (O&R (24)). -/
theorem ybar0_pos (M : ReduxParams) : 0 < M.ybar0 := Real.sqrt_pos.2 M.K_pos

/-- `ȳ₀² = K` (O&R (24)). -/
theorem ybar0_sq (M : ReduxParams) : M.ybar0 ^ 2 = M.K := Real.sq_sqrt M.K_pos.le

/-- `κ ȳ₀² = (θ−1)/θ` (O&R p. 684, used for (75)). -/
theorem κ_mul_ybar0_sq (M : ReduxParams) : M.κ * M.ybar0 ^ 2 = (M.θ - 1) / M.θ := by
  rw [ybar0_sq, K]
  have := M.hκ.ne'
  have : M.θ ≠ 0 := by linarith [M.hθ]
  field_simp

end ReduxParams

/-- The parameters of the log-linearised model, O&R §10.1.5–§10.1.7 (pp. 669–683), with the
standing assumptions `θ > 1`, `δ > 0`, `0 < n < 1`. -/
structure ReduxLinear where
  θ : ℝ
  δ : ℝ
  n : ℝ
  hθ : 1 < θ
  hδ : 0 < δ
  hn0 : 0 < n
  hn1 : n < 1

namespace ReduxLinear

/-- The denominator `D = θδ(1+θ) + 2θ = θ(δ(1+θ) + 2)` of (65), (66), (68), O&R p. 681. -/
def D (L : ReduxLinear) : ℝ := L.θ * (L.δ * (1 + L.θ) + 2)

/-- The denominator `E = δ(1+θ) + 2` of (67) and (74), O&R pp. 681, 683. -/
def E (L : ReduxLinear) : ℝ := L.δ * (1 + L.θ) + 2

/-- `E > 0` (O&R (67)). -/
theorem E_pos (L : ReduxLinear) : 0 < L.E := by
  unfold E; have := L.hδ; have := L.hθ; positivity

/-- `D > 0` (O&R (65)). -/
theorem D_pos (L : ReduxLinear) : 0 < L.D := by
  unfold D; have := L.hδ; have := L.hθ; positivity

/-- `D = θ E` (O&R pp. 681–683). -/
theorem D_eq (L : ReduxLinear) : L.D = L.θ * L.E := rfl

/-- `D = δ(1+θ) + 2θ + δ(θ² − 1)`: the MM and GG slopes combine into `D` (O&R (65)–(66)). -/
theorem D_eq_sum (L : ReduxLinear) :
    L.D = L.δ * (1 + L.θ) + 2 * L.θ + L.δ * (L.θ ^ 2 - 1) := by
  unfold D; ring

end ReduxLinear

end ObstfeldRogoff.StickyPriceModels.ReduxPrimitives

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The redux model: flexible-price steady states

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §10.1.4 and §10.1.6,
pp. 667–669 and p. 671 ("if prices are perfectly flexible … the world economy jumps instantly
to the steady state").

A flexible-price steady state indexed by Home's per-capita net foreign assets `B̄` is a list
`(y, y*, C, C*, π, π*, Cᵂ)` (outputs, consumptions, the relative prices `π = p(h)/P`,
`π* = p*(f)/P*`, world consumption) satisfying world demand (10), the labour–leisure conditions
(15), steady-state income = expenditure (20)–(21), the price index (5) with PPP (7), and (11)
(`IsSteadyState`). We prove:

* **the exact reduction (T5)**: with `K = (θ−1)/(θκ)`, (10) and (15) give `C = Kπ/y`, the budget
  becomes `π(K/y − y) = δB̄`, the price index becomes `Cᵂ = [n y^ρ + (1−n) y*^ρ]^{1/ρ}`,
  `ρ = (θ−1)/θ`, and `n g(y) + (1−n) g(y*) = 0` with the gap function
  `g(y) = K y^{−(θ+1)/θ} − y^{(θ−1)/θ}` (`gapFn`), strictly decreasing from `+∞` to `−∞`;
* **the symmetric steady state (22)–(24), (26) (T6)**: for `B̄ = 0` the steady state exists, is
  unique, and has `y = y* = C = C* = Cᵂ = ȳ₀ = K^{1/2}`, `π = π* = 1`;
* **existence AND uniqueness of the steady state for EVERY `B̄` (T7)** (`exists_unique_steady`).
  This makes precise the book's remark (p. 668) that "there is no simple closed-form solution":
  there is none, but the steady state always exists and is unique. Uniqueness: two solutions
  would move both relative prices `π, π*` in the same direction, contradicting the price index.
  Existence: the intermediate value theorem along the curve `n g(y) + (1−n) g(y*) = 0`, using the
  continuous inverse of `g`. Corollaries for `B̄ > 0`: `y < ȳ₀ < y*`, `C > C*`, and better terms
  of trade `π/π* = (y*/y)^{1/θ} > 1` (the richer country works less and consumes more);
* **the monopoly distortion (25) (T8)**: `log y − (κ/2)y²` has the unique maximiser
  `y^{PLAN} = κ^{−1/2} > ȳ₀`, is strictly increasing below it, and `ȳ₀ → y^{PLAN}` as `θ → ∞`;
* **no transitional dynamics under flexible prices (T9)** (`flexible_path_is_steady`): every
  perfect-foresight flexible-price path from given initial wealth, with the Euler equations,
  Home's budget, the no-Ponzi and the transversality conditions, sits at the unique steady state
  indexed by `B̄ = (1+r₀)B₀/(1+δ)` from date 0 on, with `r_t = δ` for `t ≥ 1` and `B_t = B̄`
  for `t ≥ 1` (the exact version of p. 671 and of "`b_t = b̄` for all `t ≥ 2`", p. 677).
-/

namespace ObstfeldRogoff.StickyPriceModels.ReduxSteadyState

open Real Filter Topology Set ReduxPrimitives

/-! ## Power identities -/

/-- `y^{(θ+1)/θ} = y · y^{1/θ}` (O&R (15)). -/
theorem rpow_succ_div {θ y : ℝ} (hθ : θ ≠ 0) (hy : 0 < y) :
    y ^ ((θ + 1) / θ) = y * y ^ (1 / θ) := by
  rw [show (θ + 1) / θ = 1 + 1 / θ by field_simp, rpow_add hy, rpow_one]

/-- `y^{(θ−1)/θ} = y / y^{1/θ}` (O&R (15), (18)). -/
theorem rpow_pred_div {θ y : ℝ} (hθ : θ ≠ 0) (hy : 0 < y) :
    y ^ ((θ - 1) / θ) = y / y ^ (1 / θ) := by
  rw [show (θ - 1) / θ = 1 + -(1 / θ) by field_simp; ring, rpow_add hy, rpow_one,
    rpow_neg hy.le, ← div_eq_mul_inv]

/-- `y^{−(θ+1)/θ} = 1/(y · y^{1/θ})` (O&R (15)). -/
theorem rpow_neg_succ_div {θ y : ℝ} (hθ : θ ≠ 0) (hy : 0 < y) :
    y ^ (-(θ + 1) / θ) = 1 / (y * y ^ (1 / θ)) := by
  rw [show -(θ + 1) / θ = -((θ + 1) / θ) by ring, rpow_neg hy.le, rpow_succ_div hθ hy,
    ← one_div]

/-- `(y^{1/θ})^θ = y` (O&R (10)). -/
theorem rpow_inv_rpow_self' {θ y : ℝ} (hθ : θ ≠ 0) (hy : 0 < y) : (y ^ (1 / θ)) ^ θ = y := by
  rw [← rpow_mul hy.le, one_div_mul_cancel hθ, rpow_one]

/-! ## The gap function `g` -/

/-- The gap function of the steady-state reduction (T5), O&R pp. 667–668:
`g(y) = K y^{−(θ+1)/θ} − y^{(θ−1)/θ} = y^{−1/θ}(K/y − y)` (`gapFn_eq`). Along the world demand
curve, `(Cᵂ)^{1/θ} g(y)` is steady-state consumption minus real income, `C − π y`. -/
noncomputable def gapFn (θ K y : ℝ) : ℝ := K * y ^ (-(θ + 1) / θ) - y ^ ((θ - 1) / θ)

/-- `g(y) = (K/y − y)/y^{1/θ}` (O&R (15), (20)). -/
theorem gapFn_eq {θ K y : ℝ} (hθ : θ ≠ 0) (hy : 0 < y) :
    gapFn θ K y = (K / y - y) / y ^ (1 / θ) := by
  unfold gapFn
  rw [rpow_neg_succ_div hθ hy, rpow_pred_div hθ hy]
  have := (rpow_pos_of_pos hy (1 / θ)).ne'
  have := hy.ne'
  field_simp

/-- **`g` is strictly decreasing** on `(0, ∞)` (O&R p. 668; T7). -/
theorem gapFn_strictAntiOn {θ K : ℝ} (hθ : 1 < θ) (hK : 0 < K) :
    StrictAntiOn (gapFn θ K) (Ioi 0) := by
  intro a ha b hb hab
  unfold gapFn
  have h1 : b ^ (-(θ + 1) / θ) < a ^ (-(θ + 1) / θ) :=
    rpow_lt_rpow_of_neg ha hab (by
      have : 0 < (θ + 1) / θ := div_pos (by linarith) (by linarith)
      rw [show -(θ + 1) / θ = -((θ + 1) / θ) by ring]; linarith)
  have h2 : a ^ ((θ - 1) / θ) < b ^ ((θ - 1) / θ) :=
    rpow_lt_rpow ha.le hab (div_pos (by linarith) (by linarith))
  nlinarith

/-- `g` is continuous on `(0, ∞)` (O&R p. 668). -/
theorem gapFn_continuousOn (θ K : ℝ) : ContinuousOn (gapFn θ K) (Ioi 0) := by
  unfold gapFn
  refine ContinuousOn.sub (ContinuousOn.mul continuousOn_const ?_) ?_
  · exact fun y hy => (continuousAt_rpow_const y _ (Or.inl (ne_of_gt hy))).continuousWithinAt
  · exact fun y hy => (continuousAt_rpow_const y _ (Or.inl (ne_of_gt hy))).continuousWithinAt

/-- `g(K^{1/2}) = 0` (O&R (24)). -/
theorem gapFn_sqrt {θ K : ℝ} (hθ : θ ≠ 0) (hK : 0 < K) : gapFn θ K (Real.sqrt K) = 0 := by
  have hs := Real.sqrt_pos.2 hK
  rw [gapFn_eq hθ hs]
  have : K / Real.sqrt K - Real.sqrt K = 0 := by
    rw [sub_eq_zero, div_eq_iff hs.ne', ← sq, Real.sq_sqrt hK.le]
  rw [this, zero_div]

/-- The sign of `g`: `g(y) > 0 ⟺ y < K^{1/2}` (O&R p. 668; T7). -/
theorem gapFn_pos_iff {θ K y : ℝ} (hθ : 1 < θ) (hK : 0 < K) (hy : 0 < y) :
    0 < gapFn θ K y ↔ y < Real.sqrt K := by
  have hs := Real.sqrt_pos.2 hK
  constructor
  · intro h
    by_contra hge
    push Not at hge
    rcases hge.lt_or_eq with hlt | heq
    · have := gapFn_strictAntiOn hθ hK hs hy hlt
      rw [gapFn_sqrt (by linarith) hK] at this
      linarith
    · rw [← heq, gapFn_sqrt (by linarith) hK] at h
      exact lt_irrefl _ h
  · intro h
    have := gapFn_strictAntiOn hθ hK hy hs h
    rwa [gapFn_sqrt (by linarith) hK] at this

/-- The sign of `g`: `g(y) < 0 ⟺ y > K^{1/2}` (O&R p. 668; T7). -/
theorem gapFn_neg_iff {θ K y : ℝ} (hθ : 1 < θ) (hK : 0 < K) (hy : 0 < y) :
    gapFn θ K y < 0 ↔ Real.sqrt K < y := by
  have hs := Real.sqrt_pos.2 hK
  constructor
  · intro h
    by_contra hge
    push Not at hge
    rcases hge.lt_or_eq with hlt | heq
    · have := (gapFn_pos_iff hθ hK hy).2 hlt
      linarith
    · rw [heq, gapFn_sqrt (by linarith) hK] at h
      exact lt_irrefl _ h
  · intro h
    have := gapFn_strictAntiOn hθ hK hs hy h
    rwa [gapFn_sqrt (by linarith) hK] at this

/-- `g(y) = 0 ⟺ y = K^{1/2}` (O&R (24)). -/
theorem gapFn_eq_zero_iff {θ K y : ℝ} (hθ : 1 < θ) (hK : 0 < K) (hy : 0 < y) :
    gapFn θ K y = 0 ↔ y = Real.sqrt K := by
  constructor
  · intro h
    rcases lt_trichotomy y (Real.sqrt K) with hlt | heq | hgt
    · have := (gapFn_pos_iff hθ hK hy).2 hlt; linarith
    · exact heq
    · have := (gapFn_neg_iff hθ hK hy).2 hgt; linarith
  · intro h; rw [h]; exact gapFn_sqrt (by linarith) hK

/-- `g` is injective on `(0, ∞)` (O&R p. 668). -/
theorem gapFn_injOn {θ K : ℝ} (hθ : 1 < θ) (hK : 0 < K) : InjOn (gapFn θ K) (Ioi 0) :=
  (gapFn_strictAntiOn hθ hK).injOn

/-- **`g` maps `(0, ∞)` onto `ℝ`** (O&R p. 668; T7): every value is attained. -/
theorem gapFn_surj {θ K : ℝ} (hθ : 1 < θ) (hK : 0 < K) (v : ℝ) :
    ∃ y, 0 < y ∧ gapFn θ K y = v := by
  set ρ := (θ - 1) / θ with hρ
  have hρ0 : 0 < ρ := div_pos (by linarith) (by linarith)
  -- a small point where `g ≥ v`
  set y1 := min 1 (K / (|v| + 2)) with hy1
  have hy1pos : 0 < y1 := lt_min one_pos (div_pos hK (by positivity))
  have hy1le : y1 ≤ 1 := min_le_left _ _
  have hy1le' : y1 ≤ K / (|v| + 2) := min_le_right _ _
  have hg1 : v ≤ gapFn θ K y1 := by
    unfold gapFn
    have ha : y1 ^ (-(θ + 1) / θ) ≥ y1 ^ (-1 : ℝ) := by
      apply rpow_le_rpow_of_exponent_ge hy1pos hy1le
      rw [show -(θ + 1) / θ = -1 - 1 / θ by field_simp; ring]
      have : 0 < 1 / θ := by positivity
      linarith
    have hb : y1 ^ ρ ≤ 1 := rpow_le_one hy1pos.le hy1le hρ0.le
    rw [rpow_neg_one] at ha
    have hc : (|v| + 2) ≤ K * y1⁻¹ := by
      rw [le_div_iff₀ (by positivity : (0:ℝ) < |v| + 2)] at hy1le'
      rw [← div_eq_mul_inv, le_div_iff₀ hy1pos]
      linarith
    have := le_abs_self v
    nlinarith
  -- a large point where `g ≤ v`
  set y2 := (K + |v| + 1) ^ (1 / ρ) with hy2
  have hy2pos : 0 < y2 := rpow_pos_of_pos (by positivity) _
  have hy2one : 1 ≤ y2 := one_le_rpow (by linarith [abs_nonneg v, hK]) (by positivity)
  have hg2 : gapFn θ K y2 ≤ v := by
    unfold gapFn
    have hpow : y2 ^ ρ = K + |v| + 1 := by
      rw [hy2, ← rpow_mul (by positivity), one_div_mul_cancel hρ0.ne', rpow_one]
    have ha : y2 ^ (-(θ + 1) / θ) ≤ 1 :=
      rpow_le_one_of_one_le_of_nonpos hy2one (by
        rw [show -(θ + 1) / θ = -((θ + 1) / θ) by ring]
        have : 0 < (θ + 1) / θ := div_pos (by linarith) (by linarith)
        linarith)
    rw [hpow]
    have := neg_abs_le v
    nlinarith
  have hle : y1 ≤ y2 := hy1le.trans hy2one
  have hcont : ContinuousOn (gapFn θ K) (Icc y1 y2) :=
    (gapFn_continuousOn θ K).mono fun y hy => lt_of_lt_of_le hy1pos hy.1
  obtain ⟨y, hy, hyv⟩ := intermediate_value_Icc' hle hcont ⟨hg2, hg1⟩
  exact ⟨y, lt_of_lt_of_le hy1pos hy.1, hyv⟩

/-- The inverse of the gap function, `g⁻¹ : ℝ → (0, ∞)` (O&R p. 668; T7). It gives Foreign
output as a function of Home output along `n g(y) + (1−n) g(y*) = 0`. -/
noncomputable def gapInv (θ K : ℝ) : ℝ → ℝ := Function.invFunOn (gapFn θ K) (Ioi 0)

/-- `g⁻¹(v) > 0` and `g(g⁻¹(v)) = v` (O&R p. 668). -/
theorem gapInv_spec {θ K : ℝ} (hθ : 1 < θ) (hK : 0 < K) (v : ℝ) :
    0 < gapInv θ K v ∧ gapFn θ K (gapInv θ K v) = v := by
  obtain ⟨y, hy, hyv⟩ := gapFn_surj hθ hK v
  have hmem : v ∈ gapFn θ K '' Ioi 0 := ⟨y, hy, hyv⟩
  exact ⟨Function.invFunOn_mem hmem, Function.invFunOn_eq hmem⟩

/-- `g⁻¹(g(y)) = y` for `y > 0` (O&R p. 668). -/
theorem gapInv_gapFn {θ K y : ℝ} (hθ : 1 < θ) (hK : 0 < K) (hy : 0 < y) :
    gapInv θ K (gapFn θ K y) = y := by
  obtain ⟨h1, h2⟩ := gapInv_spec hθ hK (gapFn θ K y)
  exact gapFn_injOn hθ hK h1 hy h2

/-- `g⁻¹` is strictly decreasing (O&R p. 668). -/
theorem gapInv_strictAnti {θ K : ℝ} (hθ : 1 < θ) (hK : 0 < K) : StrictAnti (gapInv θ K) := by
  intro a b hab
  obtain ⟨ha1, ha2⟩ := gapInv_spec hθ hK a
  obtain ⟨hb1, hb2⟩ := gapInv_spec hθ hK b
  by_contra hle
  push Not at hle
  rcases hle.lt_or_eq with hlt | heq
  · have := gapFn_strictAntiOn hθ hK ha1 hb1 hlt
    rw [ha2, hb2] at this
    linarith
  · have := congrArg (gapFn θ K) heq
    rw [ha2, hb2] at this
    linarith

/-- **`g⁻¹` is continuous** (O&R p. 668; T7): a monotone function whose image `(0, ∞)` is open. -/
theorem gapInv_continuous {θ K : ℝ} (hθ : 1 < θ) (hK : 0 < K) : Continuous (gapInv θ K) := by
  have hneg : Continuous (fun v => -gapInv θ K v) := by
    refine continuous_iff_continuousAt.2 fun a => ?_
    have hmono : MonotoneOn (fun v => -gapInv θ K v) univ :=
      fun x _ y _ hxy => neg_le_neg ((gapInv_strictAnti hθ hK).antitone hxy)
    refine continuousAt_of_monotoneOn_of_image_mem_nhds hmono univ_mem ?_
    have hsub : Iio (0 : ℝ) ⊆ (fun v => -gapInv θ K v) '' univ := by
      intro z hz
      refine ⟨gapFn θ K (-z), mem_univ _, ?_⟩
      simp only
      rw [gapInv_gapFn hθ hK (by simpa using hz)]
      ring
    exact mem_of_superset (Iio_mem_nhds (by simpa using (gapInv_spec hθ hK a).1)) hsub
  have e : gapInv θ K = fun v => -(-gapInv θ K v) := by funext v; ring
  rw [e]
  exact hneg.neg

/-! ## World output and the static equilibrium -/

/-- World real income as a CES aggregate of outputs (T5), O&R (18) with (5):
`Yᵂ = [n y^ρ + (1−n) y*^ρ]^{1/ρ}`, `ρ = (θ−1)/θ`. In equilibrium it equals `Cᵂ`. -/
noncomputable def worldOutputIndex (θ n y ys : ℝ) : ℝ :=
  (n * y ^ ((θ - 1) / θ) + (1 - n) * ys ^ ((θ - 1) / θ)) ^ (θ / (θ - 1))

/-- World output is positive (O&R (18)). -/
theorem worldOutputIndex_pos {θ n y ys : ℝ} (hn0 : 0 < n) (hn1 : n < 1) (hy : 0 < y)
    (hys : 0 < ys) : 0 < worldOutputIndex θ n y ys := by
  unfold worldOutputIndex
  have : 0 < 1 - n := by linarith
  exact rpow_pos_of_pos (by positivity) _

/-- `(Yᵂ)^ρ = n y^ρ + (1−n) y*^ρ` (O&R (18), T5). -/
theorem worldOutputIndex_rpow {θ n y ys : ℝ} (hθ : 1 < θ) (hn0 : 0 < n) (hn1 : n < 1)
    (hy : 0 < y) (hys : 0 < ys) :
    worldOutputIndex θ n y ys ^ ((θ - 1) / θ) =
      n * y ^ ((θ - 1) / θ) + (1 - n) * ys ^ ((θ - 1) / θ) := by
  unfold worldOutputIndex
  have : 0 < 1 - n := by linarith
  rw [← rpow_mul (by positivity)]
  have h : θ / (θ - 1) * ((θ - 1) / θ) = 1 := by
    have : θ - 1 ≠ 0 := by linarith
    have : θ ≠ 0 := by linarith
    field_simp
  rw [h, rpow_one]

/-- World output is symmetric in the two countries (O&R (18)). -/
theorem worldOutputIndex_comm (θ n y ys : ℝ) :
    worldOutputIndex θ n y ys = worldOutputIndex θ (1 - n) ys y := by
  unfold worldOutputIndex
  congr 1
  ring

/-- A snapshot of the real allocation at one date, O&R §10.1.4: outputs `y, y*`, consumptions
`C, C*`, relative prices `q = p(h)/P`, `qs = p*(f)/P*` (the book's `p̄(h)/P̄`, `p̄*(f)/P̄*`) and
world consumption `X = Cᵂ`. -/
structure Allocation where
  y : ℝ
  ys : ℝ
  C : ℝ
  Cs : ℝ
  q : ℝ
  qs : ℝ
  X : ℝ

/-- The static flexible-price equilibrium conditions at one date, O&R pp. 665–667: positivity,
world demand (10) for both goods, the labour–leisure conditions (15), the price index (5) with
PPP (7) (`bloc_relative_price_sum`), and world consumption (11). -/
structure IsStatic (M : ReduxParams) (s : Allocation) : Prop where
  y_pos : 0 < s.y
  ys_pos : 0 < s.ys
  C_pos : 0 < s.C
  Cs_pos : 0 < s.Cs
  q_pos : 0 < s.q
  qs_pos : 0 < s.qs
  X_pos : 0 < s.X
  demand : s.y = cesDemand M.θ s.q 1 s.X
  demand_star : s.ys = cesDemand M.θ s.qs 1 s.X
  labour : s.y ^ ((M.θ + 1) / M.θ) = M.K * s.X ^ (1 / M.θ) / s.C
  labour_star : s.ys ^ ((M.θ + 1) / M.θ) = M.K * s.X ^ (1 / M.θ) / s.Cs
  price_index : M.n * s.q ^ (1 - M.θ) + (1 - M.n) * s.qs ^ (1 - M.θ) = 1
  world : s.X = worldConsumption M.n s.C s.Cs

/-- **A flexible-price steady state indexed by `B̄`**, O&R (19)–(21), p. 667: the static conditions
plus steady-state income = expenditure in both countries, `C = δB̄ + π y` (20) and
`C* = −(n/(1−n))δB̄ + π* y*` (21). -/
structure IsSteadyState (M : ReduxParams) (B : ℝ) (s : Allocation) : Prop where
  static : IsStatic M s
  budget : s.C = M.δ * B + s.q * s.y
  budget_star : s.Cs = -(M.n / (1 - M.n)) * M.δ * B + s.qs * s.ys

namespace IsStatic

variable {M : ReduxParams} {s : Allocation}

/-- From world demand (10): `(Cᵂ)^{1/θ} = π y^{1/θ}` (O&R (10), T5). -/
theorem X_rpow (h : IsStatic M s) : s.X ^ (1 / M.θ) = s.q * s.y ^ (1 / M.θ) := by
  have hθ : M.θ ≠ 0 := by linarith [M.hθ]
  have hX : s.X = s.q ^ M.θ * s.y := by
    rw [h.demand]; unfold cesDemand
    rw [div_one, rpow_neg h.q_pos.le]
    have := (rpow_pos_of_pos h.q_pos M.θ).ne'
    field_simp
  rw [hX, mul_rpow (rpow_nonneg h.q_pos.le _) h.y_pos.le, ← rpow_mul h.q_pos.le,
    mul_one_div_cancel hθ, rpow_one]

/-- The Foreign twin of `X_rpow` (O&R (10)). -/
theorem X_rpow_star (h : IsStatic M s) : s.X ^ (1 / M.θ) = s.qs * s.ys ^ (1 / M.θ) := by
  have hθ : M.θ ≠ 0 := by linarith [M.hθ]
  have hX : s.X = s.qs ^ M.θ * s.ys := by
    rw [h.demand_star]; unfold cesDemand
    rw [div_one, rpow_neg h.qs_pos.le]
    have := (rpow_pos_of_pos h.qs_pos M.θ).ne'
    field_simp
  rw [hX, mul_rpow (rpow_nonneg h.qs_pos.le _) h.ys_pos.le, ← rpow_mul h.qs_pos.le,
    mul_one_div_cancel hθ, rpow_one]

/-- **`C = Kπ/y`** (T5): (10) and (15) give `C y = K π` (O&R (15), p. 665). -/
theorem C_mul_y (h : IsStatic M s) : s.C * s.y = M.K * s.q := by
  have hθ : M.θ ≠ 0 := by linarith [M.hθ]
  have hl := h.labour
  rw [rpow_succ_div hθ h.y_pos, h.X_rpow] at hl
  have := h.C_pos.ne'
  have hp := (rpow_pos_of_pos h.y_pos (1 / M.θ)).ne'
  field_simp at hl
  linarith

/-- The Foreign twin of `C_mul_y` (O&R (15)). -/
theorem Cs_mul_ys (h : IsStatic M s) : s.Cs * s.ys = M.K * s.qs := by
  have hθ : M.θ ≠ 0 := by linarith [M.hθ]
  have hl := h.labour_star
  rw [rpow_succ_div hθ h.ys_pos, h.X_rpow_star] at hl
  have := h.Cs_pos.ne'
  have hp := (rpow_pos_of_pos h.ys_pos (1 / M.θ)).ne'
  field_simp at hl
  linarith

/-- **Excess consumption over income** (T5): `C − π y = π(K/y − y) = (Cᵂ)^{1/θ} g(y)`
(O&R (15), (20)). -/
theorem excess_eq (h : IsStatic M s) :
    s.C - s.q * s.y = s.X ^ (1 / M.θ) * gapFn M.θ M.K s.y := by
  have hθ : M.θ ≠ 0 := by linarith [M.hθ]
  rw [h.X_rpow, gapFn_eq hθ h.y_pos]
  have hC := h.C_mul_y
  have := h.y_pos.ne'
  have := (rpow_pos_of_pos h.y_pos (1 / M.θ)).ne'
  have hC' : s.C = M.K * s.q / s.y := by field_simp; linarith
  rw [hC']
  field_simp

/-- The Foreign twin of `excess_eq` (O&R (15), (21)). -/
theorem excess_eq_star (h : IsStatic M s) :
    s.Cs - s.qs * s.ys = s.X ^ (1 / M.θ) * gapFn M.θ M.K s.ys := by
  have hθ : M.θ ≠ 0 := by linarith [M.hθ]
  rw [h.X_rpow_star, gapFn_eq hθ h.ys_pos]
  have hC := h.Cs_mul_ys
  have := h.ys_pos.ne'
  have := (rpow_pos_of_pos h.ys_pos (1 / M.θ)).ne'
  have hC' : s.Cs = M.K * s.qs / s.ys := by field_simp; linarith
  rw [hC']
  field_simp

/-- **Walras's law at one date** (O&R (18), fn 8): `n(C − π y) + (1−n)(C* − π* y*) = 0`. -/
theorem walras (h : IsStatic M s) :
    M.n * (s.C - s.q * s.y) + (1 - M.n) * (s.Cs - s.qs * s.ys) = 0 := by
  have hw := walras_identity h.q_pos h.qs_pos h.price_index h.demand h.demand_star
  have hX := h.world
  unfold worldConsumption at hX
  linarith

/-- **The gap relation** (T5): `n g(y) + (1−n) g(y*) = 0` (O&R pp. 667–668). -/
theorem gap_relation (h : IsStatic M s) :
    M.n * gapFn M.θ M.K s.y + (1 - M.n) * gapFn M.θ M.K s.ys = 0 := by
  have hw := h.walras
  rw [h.excess_eq, h.excess_eq_star] at hw
  have hX := rpow_pos_of_pos h.X_pos (1 / M.θ)
  have : s.X ^ (1 / M.θ) * (M.n * gapFn M.θ M.K s.y + (1 - M.n) * gapFn M.θ M.K s.ys) = 0 := by
    linarith
  exact (mul_eq_zero.1 this).resolve_left hX.ne'

/-- **The price index as a CES aggregate of outputs** (T5): `Cᵂ = [n y^ρ + (1−n) y*^ρ]^{1/ρ}`
(O&R (5), (10)). -/
theorem X_eq (h : IsStatic M s) : s.X = worldOutputIndex M.θ M.n s.y s.ys := by
  have hθ : M.θ ≠ 0 := by linarith [M.hθ]
  have hθ1 : M.θ - 1 ≠ 0 := by linarith [M.hθ]
  have hq : s.q = s.X ^ (1 / M.θ) / s.y ^ (1 / M.θ) := by
    rw [h.X_rpow]; have := (rpow_pos_of_pos h.y_pos (1 / M.θ)).ne'; field_simp
  have hqs : s.qs = s.X ^ (1 / M.θ) / s.ys ^ (1 / M.θ) := by
    rw [h.X_rpow_star]; have := (rpow_pos_of_pos h.ys_pos (1 / M.θ)).ne'; field_simp
  have key : ∀ z : ℝ, 0 < z → (s.X ^ (1 / M.θ) / z ^ (1 / M.θ)) ^ (1 - M.θ) =
      z ^ ((M.θ - 1) / M.θ) / s.X ^ ((M.θ - 1) / M.θ) := by
    intro z hz
    rw [div_rpow (rpow_nonneg h.X_pos.le _) (rpow_nonneg hz.le _), ← rpow_mul h.X_pos.le,
      ← rpow_mul hz.le]
    have e : 1 / M.θ * (1 - M.θ) = -((M.θ - 1) / M.θ) := by field_simp; ring
    rw [e, rpow_neg h.X_pos.le, rpow_neg hz.le]
    have := (rpow_pos_of_pos h.X_pos ((M.θ - 1) / M.θ)).ne'
    have := (rpow_pos_of_pos hz ((M.θ - 1) / M.θ)).ne'
    field_simp
  have hp := h.price_index
  rw [hq, hqs, key _ h.y_pos, key _ h.ys_pos] at hp
  have hXr := (rpow_pos_of_pos h.X_pos ((M.θ - 1) / M.θ)).ne'
  have hsum : s.X ^ ((M.θ - 1) / M.θ) =
      M.n * s.y ^ ((M.θ - 1) / M.θ) + (1 - M.n) * s.ys ^ ((M.θ - 1) / M.θ) := by
    field_simp at hp; linarith
  unfold worldOutputIndex
  rw [← hsum, ← rpow_mul h.X_pos.le]
  have e : (M.θ - 1) / M.θ * (M.θ / (M.θ - 1)) = 1 := by field_simp
  rw [e, rpow_one]

/-- The terms of trade in terms of outputs: `π/π* = (y*/y)^{1/θ}` (O&R (10), T7). -/
theorem q_div_qs (h : IsStatic M s) : s.q / s.qs = (s.ys / s.y) ^ (1 / M.θ) := by
  have h1 := h.X_rpow
  have h2 := h.X_rpow_star
  rw [div_rpow h.ys_pos.le h.y_pos.le]
  have := (rpow_pos_of_pos h.y_pos (1 / M.θ)).ne'
  have := h.qs_pos.ne'
  field_simp
  linarith

/-- **The static allocation is pinned down by outputs** (T5): `Cᵂ`, `π`, `π*`, `C`, `C*` are
explicit functions of `(y, y*)` (O&R (10), (15), (5)). -/
theorem eq_of_outputs (h : IsStatic M s) :
    s.X = worldOutputIndex M.θ M.n s.y s.ys ∧
    s.q = worldOutputIndex M.θ M.n s.y s.ys ^ (1 / M.θ) / s.y ^ (1 / M.θ) ∧
    s.qs = worldOutputIndex M.θ M.n s.y s.ys ^ (1 / M.θ) / s.ys ^ (1 / M.θ) ∧
    s.C = M.K * s.q / s.y ∧ s.Cs = M.K * s.qs / s.ys := by
  have hX := h.X_eq
  refine ⟨hX, ?_, ?_, ?_, ?_⟩
  · rw [← hX, h.X_rpow]; have := (rpow_pos_of_pos h.y_pos (1 / M.θ)).ne'; field_simp
  · rw [← hX, h.X_rpow_star]; have := (rpow_pos_of_pos h.ys_pos (1 / M.θ)).ne'; field_simp
  · have := h.C_mul_y; have := h.y_pos.ne'; field_simp; linarith
  · have := h.Cs_mul_ys; have := h.ys_pos.ne'; field_simp; linarith

/-- Two static allocations with the same outputs coincide (T5). -/
theorem ext_of_outputs {s' : Allocation} (h : IsStatic M s) (h' : IsStatic M s')
    (hy : s.y = s'.y) (hys : s.ys = s'.ys) : s = s' := by
  obtain ⟨a1, a2, a3, a4, a5⟩ := h.eq_of_outputs
  obtain ⟨b1, b2, b3, b4, b5⟩ := h'.eq_of_outputs
  have hq : s.q = s'.q := by rw [a2, b2, hy, hys]
  have hqs : s.qs = s'.qs := by rw [a3, b3, hy, hys]
  cases s
  cases s'
  simp only at *
  subst hy hys hq hqs
  simp_all

end IsStatic

/-! ## The reduced system and the steady state built from outputs -/

/-- The allocation built from outputs `(y, y*)` (T5): `Cᵂ = Yᵂ(y, y*)`, `π = (Cᵂ)^{1/θ}/y^{1/θ}`,
`π* = (Cᵂ)^{1/θ}/y*^{1/θ}`, `C = Kπ/y`, `C* = Kπ*/y*` (O&R (10), (15), (5)). -/
noncomputable def ofOutputs (M : ReduxParams) (y ys : ℝ) : Allocation where
  y := y
  ys := ys
  X := worldOutputIndex M.θ M.n y ys
  q := worldOutputIndex M.θ M.n y ys ^ (1 / M.θ) / y ^ (1 / M.θ)
  qs := worldOutputIndex M.θ M.n y ys ^ (1 / M.θ) / ys ^ (1 / M.θ)
  C := M.K * (worldOutputIndex M.θ M.n y ys ^ (1 / M.θ) / y ^ (1 / M.θ)) / y
  Cs := M.K * (worldOutputIndex M.θ M.n y ys ^ (1 / M.θ) / ys ^ (1 / M.θ)) / ys

/-- **The reduced steady-state system** (T5), O&R pp. 667–668: positive outputs with
`n g(y) + (1−n) g(y*) = 0` and `(Yᵂ)^{1/θ} g(y) = δB̄`. -/
def ReducedSystem (M : ReduxParams) (B y ys : ℝ) : Prop :=
  0 < y ∧ 0 < ys ∧ M.n * gapFn M.θ M.K y + (1 - M.n) * gapFn M.θ M.K ys = 0 ∧
    worldOutputIndex M.θ M.n y ys ^ (1 / M.θ) * gapFn M.θ M.K y = M.δ * B

/-- **Every solution of the reduced system gives a steady state** (T5, converse direction;
O&R (10), (15), (20), (21), (5), (11)). -/
theorem isSteadyState_ofOutputs {M : ReduxParams} {B y ys : ℝ}
    (hred : ReducedSystem M B y ys) : IsSteadyState M B (ofOutputs M y ys) := by
  obtain ⟨hy, hys, hrel, hB⟩ := hred
  have hθ : M.θ ≠ 0 := by linarith [M.hθ]
  have hθ1 : M.θ - 1 ≠ 0 := by linarith [M.hθ]
  have hn1 : 1 - M.n ≠ 0 := by linarith [M.hn1]
  set X := worldOutputIndex M.θ M.n y ys with hXdef
  have hX : 0 < X := worldOutputIndex_pos M.hn0 M.hn1 hy hys
  have hXr := rpow_pos_of_pos hX (1 / M.θ)
  have hyr := rpow_pos_of_pos hy (1 / M.θ)
  have hysr := rpow_pos_of_pos hys (1 / M.θ)
  have hK := M.K_pos
  set q := X ^ (1 / M.θ) / y ^ (1 / M.θ) with hq
  set qs := X ^ (1 / M.θ) / ys ^ (1 / M.θ) with hqs
  have hqpos : 0 < q := div_pos hXr hyr
  have hqspos : 0 < qs := div_pos hXr hysr
  -- demand
  have hdem : ∀ z : ℝ, 0 < z → z = cesDemand M.θ (X ^ (1 / M.θ) / z ^ (1 / M.θ)) 1 X := by
    intro z hz
    unfold cesDemand
    rw [div_one, div_rpow (rpow_nonneg hX.le _) (rpow_nonneg hz.le _), ← rpow_mul hX.le,
      ← rpow_mul hz.le]
    have e : 1 / M.θ * -M.θ = -1 := by field_simp
    rw [e, rpow_neg_one, rpow_neg_one]
    field_simp
  -- relative price of the index
  have hrel_price : ∀ z : ℝ, 0 < z → (X ^ (1 / M.θ) / z ^ (1 / M.θ)) ^ (1 - M.θ) =
      z ^ ((M.θ - 1) / M.θ) / X ^ ((M.θ - 1) / M.θ) := by
    intro z hz
    rw [div_rpow (rpow_nonneg hX.le _) (rpow_nonneg hz.le _), ← rpow_mul hX.le,
      ← rpow_mul hz.le]
    have e : 1 / M.θ * (1 - M.θ) = -((M.θ - 1) / M.θ) := by field_simp; ring
    rw [e, rpow_neg hX.le, rpow_neg hz.le]
    have := (rpow_pos_of_pos hX ((M.θ - 1) / M.θ)).ne'
    have := (rpow_pos_of_pos hz ((M.θ - 1) / M.θ)).ne'
    field_simp
  -- labour
  have hlab : ∀ z : ℝ, 0 < z →
      z ^ ((M.θ + 1) / M.θ) =
        M.K * X ^ (1 / M.θ) / (M.K * (X ^ (1 / M.θ) / z ^ (1 / M.θ)) / z) := by
    intro z hz
    rw [rpow_succ_div hθ hz]
    have := (rpow_pos_of_pos hz (1 / M.θ)).ne'
    have := hz.ne'
    have := hK.ne'
    field_simp
  -- excess
  have hexc : ∀ z : ℝ, 0 < z → M.K * (X ^ (1 / M.θ) / z ^ (1 / M.θ)) / z -
      X ^ (1 / M.θ) / z ^ (1 / M.θ) * z = X ^ (1 / M.θ) * gapFn M.θ M.K z := by
    intro z hz
    rw [gapFn_eq hθ hz]
    have := (rpow_pos_of_pos hz (1 / M.θ)).ne'
    have := hz.ne'
    field_simp
  have hXrho := worldOutputIndex_rpow M.hθ M.hn0 M.hn1 hy hys
  have hpi : M.n * q ^ (1 - M.θ) + (1 - M.n) * qs ^ (1 - M.θ) = 1 := by
    rw [hq, hqs, hrel_price y hy, hrel_price ys hys]
    have := (rpow_pos_of_pos hX ((M.θ - 1) / M.θ)).ne'
    field_simp
    linarith
  have hbud : M.K * q / y = M.δ * B + q * y := by
    have := hexc y hy; rw [← hq] at this; linarith
  have hbud_star : M.K * qs / ys = -(M.n / (1 - M.n)) * M.δ * B + qs * ys := by
    have h1 := hexc ys hys
    rw [← hqs] at h1
    have h2 : X ^ (1 / M.θ) * gapFn M.θ M.K ys = -(M.n / (1 - M.n)) * M.δ * B := by
      have : gapFn M.θ M.K ys = -(M.n / (1 - M.n)) * gapFn M.θ M.K y := by
        field_simp; linarith
      rw [this]; linear_combination (-(M.n / (1 - M.n))) * hB
    linarith
  have hCpos : 0 < M.K * q / y := div_pos (mul_pos hK hqpos) hy
  have hCspos : 0 < M.K * qs / ys := div_pos (mul_pos hK hqspos) hys
  refine ⟨⟨hy, hys, hCpos, hCspos, hqpos, hqspos, hX, hdem y hy, hdem ys hys, hlab y hy,
    hlab ys hys, hpi, ?_⟩, hbud, hbud_star⟩
  · have hw := walras_identity hqpos hqspos hpi (hdem y hy) (hdem ys hys)
    change X = worldConsumption M.n (M.K * q / y) (M.K * qs / ys)
    unfold worldConsumption
    rw [hbud, hbud_star]
    field_simp
    field_simp at hw
    linarith

/-- **Every steady state solves the reduced system and is built from its outputs** (T5,
O&R pp. 667–668). -/
theorem IsSteadyState.reduced {M : ReduxParams} {B : ℝ} {s : Allocation}
    (h : IsSteadyState M B s) : ReducedSystem M B s.y s.ys ∧ s = ofOutputs M s.y s.ys := by
  have hst := h.static
  have hB : worldOutputIndex M.θ M.n s.y s.ys ^ (1 / M.θ) * gapFn M.θ M.K s.y = M.δ * B := by
    have := hst.excess_eq
    rw [hst.X_eq] at this
    linarith [h.budget]
  refine ⟨⟨hst.y_pos, hst.ys_pos, hst.gap_relation, hB⟩, ?_⟩
  exact hst.ext_of_outputs (isSteadyState_ofOutputs ⟨hst.y_pos, hst.ys_pos,
    hst.gap_relation, hB⟩).static rfl rfl

/-- **The exact steady-state reduction (T5)**, O&R pp. 667–668: an allocation is a steady state
indexed by `B̄` IF AND ONLY IF its outputs solve the reduced two-equation system and every other
variable is the explicit function of outputs given by `ofOutputs` (`C = Kπ/y`,
`π = (Cᵂ/y)^{1/θ}`, `Cᵂ = Yᵂ(y, y*)`). In particular world goods-market clearing (11) and
positivity of consumption are implied. -/
theorem isSteadyState_iff_reduced (M : ReduxParams) (B : ℝ) (s : Allocation) :
    IsSteadyState M B s ↔ ReducedSystem M B s.y s.ys ∧ s = ofOutputs M s.y s.ys := by
  constructor
  · exact fun h => h.reduced
  · rintro ⟨hred, hs⟩
    rw [hs]
    exact isSteadyState_ofOutputs hred

/-- `π(K/y − y) = δB̄` in a steady state (T5; O&R (15), (20)). -/
theorem IsSteadyState.q_mul_gap {M : ReduxParams} {B : ℝ} {s : Allocation}
    (h : IsSteadyState M B s) : s.q * (M.K / s.y - s.y) = M.δ * B := by
  have hC := h.static.C_mul_y
  have hb := h.budget
  have := h.static.y_pos.ne'
  have e : s.q * (M.K / s.y - s.y) = (s.C * s.y) / s.y - s.q * s.y := by rw [hC]; field_simp
  rw [e, mul_div_assoc, div_self this, mul_one]
  linarith

/-- `π*(K/y* − y*) = −(n/(1−n))δB̄` in a steady state (T5; O&R (15), (21)). -/
theorem IsSteadyState.qs_mul_gap {M : ReduxParams} {B : ℝ} {s : Allocation}
    (h : IsSteadyState M B s) : s.qs * (M.K / s.ys - s.ys) = -(M.n / (1 - M.n)) * M.δ * B := by
  have hC := h.static.Cs_mul_ys
  have hb := h.budget_star
  have := h.static.ys_pos.ne'
  have e : s.qs * (M.K / s.ys - s.ys) = (s.Cs * s.ys) / s.ys - s.qs * s.ys := by
    rw [hC]; field_simp
  rw [e, mul_div_assoc, div_self this, mul_one]
  linarith

/-! ## Uniqueness for every `B̄` (T7) -/

/-- Strict monotonicity of `y ↦ K/y − y` (O&R (20)). -/
theorem kgap_strictAnti {K a b : ℝ} (hK : 0 < K) (ha : 0 < a) (hab : a < b) :
    K / b - b < K / a - a := by
  have : K / b < K / a := div_lt_div_of_pos_left hK ha hab
  linarith

/-- The core of uniqueness (T7): two steady states for the same `B̄` cannot have
`y₁ < y₂`. Both relative prices would move in the same direction, contradicting the price index
(5). -/
theorem not_lt_of_steady {M : ReduxParams} {B : ℝ} {s t : Allocation}
    (hs : IsSteadyState M B s) (ht : IsSteadyState M B t) : ¬ s.y < t.y := by
  intro hlt
  have hθ := M.hθ
  have hK := M.K_pos
  have hsst := hs.static
  have htst := ht.static
  -- Foreign outputs move the other way
  have hg : gapFn M.θ M.K t.y < gapFn M.θ M.K s.y :=
    gapFn_strictAntiOn hθ hK hsst.y_pos htst.y_pos hlt
  have hys : t.ys < s.ys := by
    have r1 := hsst.gap_relation
    have r2 := htst.gap_relation
    have hn := M.hn0
    have hn1 : 0 < 1 - M.n := by linarith [M.hn1]
    have hgs : gapFn M.θ M.K s.ys < gapFn M.θ M.K t.ys := by nlinarith
    by_contra hle
    push Not at hle
    rcases hle.lt_or_eq with h1 | h1
    · have := gapFn_strictAntiOn hθ hK hsst.ys_pos htst.ys_pos h1; linarith
    · rw [h1] at hgs; exact lt_irrefl _ hgs
  have hk1 := kgap_strictAnti hK hsst.y_pos hlt
  have hk2 := kgap_strictAnti hK htst.ys_pos hys
  have e1 := hs.q_mul_gap
  have e2 := ht.q_mul_gap
  have f1 := hs.qs_mul_gap
  have f2 := ht.qs_mul_gap
  have hpi1 := hsst.price_index
  have hpi2 := htst.price_index
  have hn := M.hn0
  have hn1 : 0 < 1 - M.n := by linarith [M.hn1]
  have hexp : 1 - M.θ < 0 := by linarith
  have hδ := M.δ_pos
  rcases lt_trichotomy B 0 with hB | hB | hB
  · -- `B̄ < 0`: both relative prices fall from `s` to `t`
    have hsn : M.K / s.y - s.y < 0 := by
      by_contra hc; push Not at hc
      have := mul_nonneg hsst.q_pos.le hc
      nlinarith
    have htn : M.K / t.y - t.y < 0 := by linarith
    have hq : t.q < s.q := by nlinarith [hsst.q_pos, htst.q_pos]
    have htsp : 0 < M.K / t.ys - t.ys := by
      by_contra hc; push Not at hc
      have := mul_nonpos_of_nonneg_of_nonpos htst.qs_pos.le hc
      have : 0 < -(M.n / (1 - M.n)) * M.δ * B := by
        have : 0 < M.n / (1 - M.n) := div_pos hn hn1
        have hh : 0 < M.n / (1 - M.n) * M.δ * (-B) := mul_pos (mul_pos this hδ) (by linarith)
        linarith
      linarith
    have hqs : t.qs < s.qs := by nlinarith [hsst.qs_pos, htst.qs_pos]
    have a1 := rpow_lt_rpow_of_neg htst.q_pos hq hexp
    have a2 := rpow_lt_rpow_of_neg htst.qs_pos hqs hexp
    nlinarith
  · -- `B̄ = 0`: `K/y − y = 0` for both, impossible with `y₁ < y₂`
    subst hB
    have z1 : M.K / s.y - s.y = 0 := by
      have := e1; rw [mul_zero] at this
      exact (mul_eq_zero.1 this).resolve_left hsst.q_pos.ne'
    have z2 : M.K / t.y - t.y = 0 := by
      have := e2; rw [mul_zero] at this
      exact (mul_eq_zero.1 this).resolve_left htst.q_pos.ne'
    linarith
  · -- `B̄ > 0`: both relative prices rise from `s` to `t`
    have htp : 0 < M.K / t.y - t.y := by
      by_contra hc; push Not at hc
      have := mul_nonpos_of_nonneg_of_nonpos htst.q_pos.le hc
      nlinarith
    have hq : s.q < t.q := by nlinarith [hsst.q_pos, htst.q_pos]
    have hssn : M.K / s.ys - s.ys < 0 := by
      by_contra hc; push Not at hc
      have := mul_nonneg hsst.qs_pos.le hc
      have : -(M.n / (1 - M.n)) * M.δ * B < 0 := by
        have : 0 < M.n / (1 - M.n) := div_pos hn hn1
        have hh : 0 < M.n / (1 - M.n) * M.δ * B := mul_pos (mul_pos this hδ) hB
        linarith
      linarith
    have hqs : s.qs < t.qs := by nlinarith [hsst.qs_pos, htst.qs_pos]
    have a1 := rpow_lt_rpow_of_neg hsst.q_pos hq hexp
    have a2 := rpow_lt_rpow_of_neg hsst.qs_pos hqs hexp
    nlinarith

/-- **Uniqueness of the steady state for every `B̄`** (T7; O&R p. 668 makes no claim, and the
log-linearisation around a general `B̄` needs it). -/
theorem steady_unique {M : ReduxParams} {B : ℝ} {s t : Allocation}
    (hs : IsSteadyState M B s) (ht : IsSteadyState M B t) : s = t := by
  have hy : s.y = t.y := by
    rcases lt_trichotomy s.y t.y with h | h | h
    · exact absurd h (not_lt_of_steady hs ht)
    · exact h
    · exact absurd h (not_lt_of_steady ht hs)
  have hys : s.ys = t.ys := by
    have r1 := hs.static.gap_relation
    have r2 := ht.static.gap_relation
    rw [hy] at r1
    have hn1 : 0 < 1 - M.n := by linarith [M.hn1]
    have : gapFn M.θ M.K s.ys = gapFn M.θ M.K t.ys := by
      have : (1 - M.n) * (gapFn M.θ M.K s.ys - gapFn M.θ M.K t.ys) = 0 := by linarith
      have := (mul_eq_zero.1 this).resolve_left hn1.ne'
      linarith
    exact gapFn_injOn M.hθ M.K_pos hs.static.ys_pos ht.static.ys_pos this
  exact hs.static.ext_of_outputs ht.static hy hys

/-! ## Existence for every `B̄` (T7) -/

/-- A lower bound on world output: `(Yᵂ)^{1/θ} ≥ w^{1/(θ−1)} y^{1/θ}` (O&R (18); T7). -/
theorem worldOutputIndex_rpow_ge {θ w y ys : ℝ} (hθ : 1 < θ) (hw0 : 0 < w) (hw1 : w < 1)
    (hy : 0 < y) (hys : 0 < ys) :
    w ^ (1 / (θ - 1)) * y ^ (1 / θ) ≤ worldOutputIndex θ w y ys ^ (1 / θ) := by
  have hθ0 : θ ≠ 0 := by linarith
  have hθ1 : θ - 1 ≠ 0 := by linarith
  have hw1' : 0 < 1 - w := by linarith
  set S := w * y ^ ((θ - 1) / θ) + (1 - w) * ys ^ ((θ - 1) / θ) with hS
  have hSpos : 0 < S := by positivity
  have hle : w * y ^ ((θ - 1) / θ) ≤ S := by
    have : 0 ≤ (1 - w) * ys ^ ((θ - 1) / θ) := by positivity
    linarith
  unfold worldOutputIndex
  rw [← hS, ← rpow_mul hSpos.le]
  have e : θ / (θ - 1) * (1 / θ) = 1 / (θ - 1) := by field_simp
  rw [e]
  have h1 : (w * y ^ ((θ - 1) / θ)) ^ (1 / (θ - 1)) ≤ S ^ (1 / (θ - 1)) :=
    rpow_le_rpow (by positivity) hle (by
      have : 0 < θ - 1 := by linarith
      positivity)
  have h2 : (w * y ^ ((θ - 1) / θ)) ^ (1 / (θ - 1)) = w ^ (1 / (θ - 1)) * y ^ (1 / θ) := by
    rw [mul_rpow hw0.le (rpow_nonneg hy.le _), ← rpow_mul hy.le]
    congr 2
    field_simp
  linarith

/-- **Existence on the creditor side** (T7): for weights `0 < w < 1` and any `b > 0` there are
outputs `y, y* > 0` with `w g(y) + (1−w) g(y*) = 0` and `(Yᵂ)^{1/θ} g(y) = b`. Proof: the
intermediate value theorem for `F(y) = Yᵂ(y, g⁻¹(−(w/(1−w))g(y)))^{1/θ} g(y)` on
`[y₀, K^{1/2}]`, where `F(K^{1/2}) = 0` and `F(y₀) ≥ w^{1/(θ−1)}(K/y₀ − y₀) ≥ b`. -/
theorem exists_reduced_pos {θ K w b : ℝ} (hθ : 1 < θ) (hK : 0 < K) (hw0 : 0 < w) (hw1 : w < 1)
    (hb : 0 < b) : ∃ y ys, 0 < y ∧ 0 < ys ∧ w * gapFn θ K y + (1 - w) * gapFn θ K ys = 0 ∧
      worldOutputIndex θ w y ys ^ (1 / θ) * gapFn θ K y = b := by
  have hθ0 : θ ≠ 0 := by linarith
  have hw1' : 0 < 1 - w := by linarith
  set Y : ℝ → ℝ := fun y => gapInv θ K (-(w / (1 - w)) * gapFn θ K y) with hY
  set F : ℝ → ℝ := fun y => worldOutputIndex θ w y (Y y) ^ (1 / θ) * gapFn θ K y with hF
  have hYpos : ∀ y, 0 < Y y := fun y => (gapInv_spec hθ hK _).1
  have hYrel : ∀ y, w * gapFn θ K y + (1 - w) * gapFn θ K (Y y) = 0 := by
    intro y
    rw [(gapInv_spec hθ hK _).2]
    field_simp
    ring
  set r := Real.sqrt K with hr
  have hrpos : 0 < r := Real.sqrt_pos.2 hK
  set c := w ^ (1 / (θ - 1)) with hc
  have hcpos : 0 < c := rpow_pos_of_pos hw0 _
  set A := b / c with hA
  have hApos : 0 < A := div_pos hb hcpos
  set y0 := K / (A + r) with hy0
  have hy0pos : 0 < y0 := div_pos hK (by positivity)
  have hy0le : y0 ≤ r := by
    rw [hy0, div_le_iff₀ (by positivity)]
    have : K = r * r := by rw [hr, Real.mul_self_sqrt hK.le]
    nlinarith
  -- continuity of `F` on `(0, ∞)`
  have hcont : ∀ y, 0 < y → ContinuousAt F y := by
    intro y hy
    have hg : ContinuousAt (gapFn θ K) y :=
      (gapFn_continuousOn θ K).continuousAt (Ioi_mem_nhds hy)
    have hYc : ContinuousAt Y y :=
      (gapInv_continuous hθ hK).continuousAt.comp (hg.const_mul _)
    have hyρ : ContinuousAt (fun y : ℝ => y ^ ((θ - 1) / θ)) y :=
      continuousAt_rpow_const y _ (Or.inl hy.ne')
    have hYρ : ContinuousAt (fun y => Y y ^ ((θ - 1) / θ)) y :=
      hYc.rpow_const (Or.inl (hYpos y).ne')
    have hS : ContinuousAt (fun y => w * y ^ ((θ - 1) / θ) + (1 - w) * Y y ^ ((θ - 1) / θ)) y :=
      (hyρ.const_mul w).add (hYρ.const_mul (1 - w))
    have hSpos : 0 < w * y ^ ((θ - 1) / θ) + (1 - w) * Y y ^ ((θ - 1) / θ) := by
      have := hYpos y; positivity
    have hX : ContinuousAt (fun y => worldOutputIndex θ w y (Y y)) y :=
      hS.rpow_const (Or.inl hSpos.ne')
    have hX1 : ContinuousAt (fun y => worldOutputIndex θ w y (Y y) ^ (1 / θ)) y :=
      hX.rpow_const (Or.inl (worldOutputIndex_pos hw0 hw1 hy (hYpos y)).ne')
    exact hX1.mul hg
  have hcontOn : ContinuousOn F (Icc y0 r) := fun y hy =>
    (hcont y (lt_of_lt_of_le hy0pos hy.1)).continuousWithinAt
  have hFr : F r = 0 := by simp only [hF, hr, gapFn_sqrt hθ0 hK, mul_zero]
  have hFy0 : b ≤ F y0 := by
    have hlow := worldOutputIndex_rpow_ge hθ hw0 hw1 hy0pos (hYpos y0)
    have hgy0 : gapFn θ K y0 = (K / y0 - y0) / y0 ^ (1 / θ) := gapFn_eq hθ0 hy0pos
    have hpos : 0 < K / y0 - y0 := by
      have : K / y0 = A + r := by rw [hy0]; field_simp
      linarith
    have hgpos : 0 < gapFn θ K y0 := by rw [hgy0]; exact div_pos hpos (rpow_pos_of_pos hy0pos _)
    have hK0 : A ≤ K / y0 - y0 := by
      have : K / y0 = A + r := by rw [hy0]; field_simp
      linarith
    have step : c * (K / y0 - y0) ≤ F y0 := by
      have := mul_le_mul_of_nonneg_right hlow hgpos.le
      have e : c * y0 ^ (1 / θ) * gapFn θ K y0 = c * (K / y0 - y0) := by
        rw [hgy0]; have := (rpow_pos_of_pos hy0pos (1 / θ)).ne'; field_simp
      simp only [hF]
      linarith
    have : b = c * A := by rw [hA]; field_simp
    nlinarith
  obtain ⟨y, hy, hyb⟩ := intermediate_value_Icc' hy0le hcontOn ⟨by rw [hFr]; exact hb.le, hFy0⟩
  exact ⟨y, Y y, lt_of_lt_of_le hy0pos hy.1, hYpos y, hYrel y, hyb⟩

/-- **Existence of the reduced solution for every `B̄`** (T7). For `B̄ > 0` use
`exists_reduced_pos`; for `B̄ < 0` apply it to Foreign (weights swapped); `B̄ = 0` is the
symmetric solution `y = y* = K^{1/2}`. -/
theorem exists_reduced (M : ReduxParams) (B : ℝ) : ∃ y ys, ReducedSystem M B y ys := by
  have hθ := M.hθ
  have hK := M.K_pos
  have hn0 := M.hn0
  have hn1 := M.hn1
  have hn1' : 0 < 1 - M.n := by linarith
  have hδ := M.δ_pos
  rcases lt_trichotomy B 0 with hB | hB | hB
  · obtain ⟨ys, y, hys, hy, hrel, hval⟩ := exists_reduced_pos (w := 1 - M.n)
      (b := -(M.n / (1 - M.n)) * M.δ * B) hθ hK hn1' (by linarith) (by
        have : 0 < M.n / (1 - M.n) := div_pos hn0 hn1'
        have hh : 0 < M.n / (1 - M.n) * M.δ * (-B) := mul_pos (mul_pos this hδ) (by linarith)
        linarith)
    refine ⟨y, ys, hy, hys, by rw [sub_sub_cancel] at hrel; linarith, ?_⟩
    rw [worldOutputIndex_comm]
    have hg : gapFn M.θ M.K y = -((1 - M.n) / M.n) * gapFn M.θ M.K ys := by
      rw [sub_sub_cancel] at hrel
      field_simp
      linarith
    rw [hg]
    have e : worldOutputIndex M.θ (1 - M.n) ys y ^ (1 / M.θ) *
        (-((1 - M.n) / M.n) * gapFn M.θ M.K ys) = -((1 - M.n) / M.n) *
        (worldOutputIndex M.θ (1 - M.n) ys y ^ (1 / M.θ) * gapFn M.θ M.K ys) := by ring
    rw [e, hval]
    field_simp
  · subst hB
    have hs := Real.sqrt_pos.2 hK
    refine ⟨Real.sqrt M.K, Real.sqrt M.K, hs, hs, ?_, ?_⟩
    · rw [gapFn_sqrt (by linarith) hK]; ring
    · rw [gapFn_sqrt (by linarith) hK]; ring
  · obtain ⟨y, ys, hy, hys, hrel, hval⟩ := exists_reduced_pos (w := M.n) (b := M.δ * B)
      hθ hK hn0 hn1 (mul_pos hδ hB)
    exact ⟨y, ys, hy, hys, hrel, hval⟩

/-- **Existence and uniqueness of the flexible-price steady state for EVERY level of net foreign
assets** (T7; this makes precise O&R p. 668, "in general there is no simple closed-form solution
for the steady state"). -/
theorem exists_unique_steady (M : ReduxParams) (B : ℝ) : ∃! s, IsSteadyState M B s := by
  obtain ⟨y, ys, hred⟩ := exists_reduced M B
  exact ⟨ofOutputs M y ys, isSteadyState_ofOutputs hred, fun t ht =>
    steady_unique ht (isSteadyState_ofOutputs hred)⟩

/-- The steady state indexed by `B̄` (T7), defined by choice from `exists_unique_steady`. -/
noncomputable def steadyState (M : ReduxParams) (B : ℝ) : Allocation :=
  (exists_unique_steady M B).choose

/-- `steadyState M B̄` is a steady state (T7). -/
theorem steadyState_spec (M : ReduxParams) (B : ℝ) : IsSteadyState M B (steadyState M B) :=
  (exists_unique_steady M B).choose_spec.1

/-- Any steady state indexed by `B̄` is `steadyState M B̄` (T7). -/
theorem eq_steadyState {M : ReduxParams} {B : ℝ} {s : Allocation} (h : IsSteadyState M B s) :
    s = steadyState M B :=
  steady_unique h (steadyState_spec M B)

/-! ## The symmetric steady state (22)–(24), (26) (T6) -/

/-- The symmetric allocation of (22)–(24), O&R p. 668: `y = y* = C = C* = Cᵂ = ȳ₀` and
`π = π* = 1`. -/
noncomputable def symmetricSteady (M : ReduxParams) : Allocation :=
  ⟨M.ybar0, M.ybar0, M.ybar0, M.ybar0, 1, 1, M.ybar0⟩

/-- **The symmetric steady state (22)–(24)**, O&R p. 668 (T6): with `B̄ = 0` the steady state
exists, is unique, and is `y = y* = C = C* = Cᵂ = ȳ₀ = [(θ−1)/(θκ)]^{1/2}`,
`p(h)/P = p*(f)/P* = 1`. -/
theorem isSteadyState_zero_iff (M : ReduxParams) (s : Allocation) :
    IsSteadyState M 0 s ↔ s = symmetricSteady M := by
  have hθ0 : M.θ ≠ 0 := by linarith [M.hθ]
  have hy := M.ybar0_pos
  have hsym : IsSteadyState M 0 (symmetricSteady M) := by
    refine ⟨⟨hy, hy, hy, hy, one_pos, one_pos, hy, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩ <;>
      simp only [symmetricSteady]
    · simp [cesDemand]
    · simp [cesDemand]
    · rw [rpow_succ_div hθ0 hy]
      have := (rpow_pos_of_pos hy (1 / M.θ)).ne'
      rw [← M.ybar0_sq]
      field_simp
    · rw [rpow_succ_div hθ0 hy]
      have := (rpow_pos_of_pos hy (1 / M.θ)).ne'
      rw [← M.ybar0_sq]
      field_simp
    · simp
    · unfold worldConsumption; ring
    · ring
    · ring
  constructor
  · intro h; exact steady_unique h hsym
  · intro h; rw [h]; exact hsym

/-- **Steady-state real balances (26)**, O&R p. 669: in the symmetric steady state, money demand
(14) with `i = δ` gives `M̄₀/P̄₀ = χ(1+δ)ȳ₀/δ`. -/
theorem symmetric_real_balances (M : ReduxParams) {m : ℝ}
    (h14 : m = M.χ * (symmetricSteady M).C * ((1 + M.δ) / M.δ)) :
    m = M.χ * (1 + M.δ) / M.δ * M.ybar0 := by
  rw [h14]; simp only [symmetricSteady]; ring

/-! ## Corollaries of T7: who works, who consumes -/

/-- **The richer country works less, consumes more and has better terms of trade** (T7
corollaries; O&R p. 672 in the linear model): in the steady state with `B̄ > 0`,
`y < ȳ₀ < y*`, `π/π* > 1` and `C > C*`. -/
theorem steady_creditor {M : ReduxParams} {B : ℝ} {s : Allocation} (h : IsSteadyState M B s)
    (hB : 0 < B) : s.y < M.ybar0 ∧ M.ybar0 < s.ys ∧ 1 < s.q / s.qs ∧ s.Cs < s.C := by
  have hst := h.static
  have hθ := M.hθ
  have hK := M.K_pos
  have hn1' : 0 < 1 - M.n := by linarith [M.hn1]
  have hδ := M.δ_pos
  have hred := h.reduced.1
  obtain ⟨-, -, hrel, hval⟩ := hred
  have hXr := rpow_pos_of_pos
    (worldOutputIndex_pos (θ := M.θ) M.hn0 M.hn1 hst.y_pos hst.ys_pos) (1 / M.θ)
  have hg : 0 < gapFn M.θ M.K s.y := by
    by_contra hc; push Not at hc
    have := mul_nonpos_of_nonneg_of_nonpos hXr.le hc
    nlinarith
  have hgs : gapFn M.θ M.K s.ys < 0 := by nlinarith [M.hn0]
  have h1 := (gapFn_pos_iff hθ hK hst.y_pos).1 hg
  have h2 := (gapFn_neg_iff hθ hK hst.ys_pos).1 hgs
  have hlt : s.y < s.ys := h1.trans h2
  have hq : 1 < s.q / s.qs := by
    rw [hst.q_div_qs]
    exact one_lt_rpow (by rw [one_lt_div hst.y_pos]; exact hlt) (by
      have : 0 < M.θ := by linarith
      positivity)
  refine ⟨h1, h2, hq, ?_⟩
  have hC := hst.C_mul_y
  have hCs := hst.Cs_mul_ys
  have hqq : s.qs < s.q := by rwa [one_lt_div hst.qs_pos] at hq
  have e1 : s.C = M.K * s.q / s.y := by have := hst.y_pos.ne'; field_simp; linarith
  have e2 : s.Cs = M.K * s.qs / s.ys := by have := hst.ys_pos.ne'; field_simp; linarith
  rw [e1, e2]
  have := hst.qs_pos
  have := hst.y_pos
  calc M.K * s.qs / s.ys < M.K * s.qs / s.y :=
        div_lt_div_of_pos_left (mul_pos hK hst.qs_pos) hst.y_pos hlt
    _ < M.K * s.q / s.y := div_lt_div_of_pos_right (mul_lt_mul_of_pos_left hqq hK) hst.y_pos

/-- The debtor mirror of `steady_creditor` (T7): with `B̄ < 0`, `y* < ȳ₀ < y`, `π/π* < 1` and
`C < C*`. -/
theorem steady_debtor {M : ReduxParams} {B : ℝ} {s : Allocation} (h : IsSteadyState M B s)
    (hB : B < 0) : s.ys < M.ybar0 ∧ M.ybar0 < s.y ∧ s.q / s.qs < 1 ∧ s.C < s.Cs := by
  have hst := h.static
  have hθ := M.hθ
  have hK := M.K_pos
  have hn1' : 0 < 1 - M.n := by linarith [M.hn1]
  have hδ := M.δ_pos
  obtain ⟨-, -, hrel, hval⟩ := h.reduced.1
  have hXr := rpow_pos_of_pos
    (worldOutputIndex_pos (θ := M.θ) M.hn0 M.hn1 hst.y_pos hst.ys_pos) (1 / M.θ)
  have hg : gapFn M.θ M.K s.y < 0 := by
    by_contra hc; push Not at hc
    have := mul_nonneg hXr.le hc
    nlinarith
  have hgs : 0 < gapFn M.θ M.K s.ys := by nlinarith [M.hn0]
  have h1 := (gapFn_neg_iff hθ hK hst.y_pos).1 hg
  have h2 := (gapFn_pos_iff hθ hK hst.ys_pos).1 hgs
  have hlt : s.ys < s.y := h2.trans h1
  have hq : s.q / s.qs < 1 := by
    rw [hst.q_div_qs]
    exact rpow_lt_one (div_pos hst.ys_pos hst.y_pos).le
      (by rw [div_lt_one hst.y_pos]; exact hlt) (by
        have : 0 < M.θ := by linarith
        positivity)
  refine ⟨h2, h1, hq, ?_⟩
  have hC := hst.C_mul_y
  have hCs := hst.Cs_mul_ys
  have hqq : s.q < s.qs := by rwa [div_lt_one hst.qs_pos] at hq
  have e1 : s.C = M.K * s.q / s.y := by have := hst.y_pos.ne'; field_simp; linarith
  have e2 : s.Cs = M.K * s.qs / s.ys := by have := hst.ys_pos.ne'; field_simp; linarith
  rw [e1, e2]
  have := hst.q_pos
  calc M.K * s.q / s.y < M.K * s.q / s.ys :=
        div_lt_div_of_pos_left (mul_pos hK hst.q_pos) hst.ys_pos hlt
    _ < M.K * s.qs / s.ys := div_lt_div_of_pos_right (mul_lt_mul_of_pos_left hqq hK) hst.ys_pos

/-- In every steady state, `B̄ > 0 ⟺ C > C*` (T7; used for the exact equiproportionate-shock
result in `ReduxMoneyShocks`). -/
theorem steady_C_gt_iff {M : ReduxParams} {B : ℝ} {s : Allocation} (h : IsSteadyState M B s) :
    s.Cs < s.C ↔ 0 < B := by
  constructor
  · intro hC
    rcases lt_trichotomy B 0 with hB | hB | hB
    · exact absurd hC (not_lt.2 (steady_debtor h hB).2.2.2.le)
    · subst hB
      rw [(isSteadyState_zero_iff M s).1 h] at hC
      exact absurd hC (lt_irrefl _)
    · exact hB
  · intro hB; exact (steady_creditor h hB).2.2.2

/-! ## The monopoly distortion (25) (T8) -/

/-- The planner's objective of (25), O&R p. 668: `log y − (κ/2) y²`. -/
noncomputable def plannerObjective (κ y : ℝ) : ℝ := Real.log y - κ / 2 * y ^ 2

/-- The planner's output `y^{PLAN} = (1/κ)^{1/2}` of (25), O&R p. 668. -/
noncomputable def plannerOutput (κ : ℝ) : ℝ := Real.sqrt (1 / κ)

/-- **The planner's optimum (25)**, O&R p. 668 (T8): `y^{PLAN} = κ^{−1/2}` is the unique maximiser
of `log y − (κ/2)y²` on `(0, ∞)`. -/
theorem planner_max {κ y : ℝ} (hκ : 0 < κ) (hy : 0 < y) :
    plannerObjective κ y ≤ plannerObjective κ (plannerOutput κ) ∧
      (plannerObjective κ y = plannerObjective κ (plannerOutput κ) ↔ y = plannerOutput κ) := by
  set yp := plannerOutput κ with hyp
  have hyp0 : 0 < yp := Real.sqrt_pos.2 (by positivity)
  have hyp2 : yp ^ 2 = 1 / κ := Real.sq_sqrt (by positivity)
  set z := y / yp with hz
  have hz0 : 0 < z := div_pos hy hyp0
  have hy2 : κ / 2 * y ^ 2 = z ^ 2 / 2 := by
    have : y = z * yp := by rw [hz]; field_simp
    rw [this, mul_pow, hyp2]; field_simp
  have hdiff : plannerObjective κ y - plannerObjective κ yp =
      Real.log z - z ^ 2 / 2 + 1 / 2 := by
    unfold plannerObjective
    rw [hz, Real.log_div hy.ne' hyp0.ne', ← hz, hy2, hyp2]
    field_simp
    ring
  have hlog := Real.log_le_sub_one_of_pos hz0
  refine ⟨by nlinarith [sq_nonneg (z - 1)], ⟨fun heq => ?_, fun h => by rw [h]⟩⟩
  by_contra hne
  have hz1 : z ≠ 1 := by
    intro h1; apply hne; rw [hz] at h1; field_simp at h1; linarith
  have hlt := Real.log_lt_sub_one_of_pos hz0 hz1
  nlinarith [sq_nonneg (z - 1)]

/-- **Decentralised output is too low (25)**, O&R p. 668 (T8): `ȳ₀ < y^{PLAN}`. -/
theorem ybar0_lt_plannerOutput (M : ReduxParams) : M.ybar0 < plannerOutput M.κ := by
  unfold ReduxParams.ybar0 plannerOutput ReduxParams.K
  have hκ := M.hκ
  have hθ := M.hθ
  have hθκ : 0 < M.θ * M.κ := mul_pos (by linarith) hκ
  apply Real.sqrt_lt_sqrt (div_pos (by linarith) hθκ).le
  rw [div_lt_div_iff₀ hθκ hκ]
  nlinarith

/-- **Output increases are welfare-improving up to the planner's level** (T8, O&R p. 668): the
objective `log y − (κ/2)y²` is strictly increasing on `(0, y^{PLAN}]`, so every symmetric
output increase from `ȳ₀` up to `y^{PLAN}` is a strict improvement. -/
theorem planner_strictMonoOn {κ : ℝ} (hκ : 0 < κ) :
    StrictMonoOn (plannerObjective κ) (Ioc 0 (plannerOutput κ)) := by
  intro a ha b hb hab
  have ha0 : 0 < a := ha.1
  have hb0 : 0 < b := lt_trans ha0 hab
  have hb2 : κ * b ^ 2 ≤ 1 := by
    have h1 : b ^ 2 ≤ plannerOutput κ ^ 2 := pow_le_pow_left₀ hb0.le hb.2 2
    have h2 : plannerOutput κ ^ 2 = 1 / κ := Real.sq_sqrt (by positivity)
    rw [h2] at h1
    have := mul_le_mul_of_nonneg_left h1 hκ.le
    rwa [mul_one_div_cancel hκ.ne'] at this
  unfold plannerObjective
  have hlog : 1 - a / b < Real.log (b / a) := by
    have h1 : a / b ≠ 1 := by
      intro h; rw [div_eq_one_iff_eq hb0.ne'] at h; linarith
    have := Real.log_lt_sub_one_of_pos (div_pos ha0 hb0) h1
    rw [Real.log_div ha0.ne' hb0.ne'] at this
    rw [Real.log_div hb0.ne' ha0.ne']
    linarith
  rw [Real.log_div hb0.ne' ha0.ne'] at hlog
  have e : 1 - a / b = (b - a) / b := by field_simp
  rw [e] at hlog
  have hq : κ / 2 * b ^ 2 - κ / 2 * a ^ 2 < (b - a) / b := by
    have hba : 0 < b - a := by linarith
    have h3 : κ / 2 * b ^ 2 - κ / 2 * a ^ 2 = κ / 2 * (b - a) * (b + a) := by ring
    have h4 : κ / 2 * (b - a) * (b + a) < κ * (b - a) * b := by
      have : 0 < κ * (b - a) := mul_pos hκ hba
      nlinarith
    have h5 : κ * (b - a) * b ≤ (b - a) / b := by
      rw [le_div_iff₀ hb0]
      nlinarith
    linarith
  linarith

/-- **The distortion vanishes as goods become perfect substitutes** (T8, O&R p. 668):
`ȳ₀ = [(θ−1)/(θκ)]^{1/2} → y^{PLAN}` as `θ → ∞`. -/
theorem ybar0_tendsto_planner {κ : ℝ} (hκ : 0 < κ) :
    Tendsto (fun θ : ℝ => Real.sqrt ((θ - 1) / (θ * κ))) atTop (𝓝 (plannerOutput κ)) := by
  have h : Tendsto (fun θ : ℝ => (1 - θ⁻¹) / κ) atTop (𝓝 ((1 - 0) / κ)) :=
    (tendsto_const_nhds.sub tendsto_inv_atTop_zero).div_const κ
  rw [sub_zero] at h
  have h' : Tendsto (fun θ : ℝ => (θ - 1) / (θ * κ)) atTop (𝓝 (1 / κ)) := by
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop 0] with θ hθ
    field_simp
  exact (Real.continuous_sqrt.tendsto _).comp h'

/-! ## No transitional dynamics under flexible prices (T9) -/

/-- A perfect-foresight path of the flexible-price economy, O&R §10.1.2–§10.1.4: the static
allocation at each date, the real rate `r_t` on bonds held from `t − 1` to `t` and Home's
per-capita bonds `B_t` carried into date `t` (Foreign holds `−(n/(1−n))B_t` by (17)). -/
structure FlexPath where
  alloc : ℕ → Allocation
  r : ℕ → ℝ
  B : ℕ → ℝ

/-- **A flexible-price perfect-foresight equilibrium**, O&R (8), (10), (11), (13), (15), (16),
(17): the static conditions at every date, both Euler equations (13) at the common real rate,
Home's real budget (54) (money and taxes cancel by (9), `real_budget_of_nominal`), positive
gross rates, and Home's no-Ponzi and transversality conditions on wealth
`W_t = (1 + r_t)B_t` at the market discount factor `R_T` (Foreign's budget is implied by
Walras's law, `IsFlexEqm.foreign_budget`). -/
structure IsFlexEqm (M : ReduxParams) (f : FlexPath) : Prop where
  static : ∀ t, IsStatic M (f.alloc t)
  euler : ∀ t, (f.alloc (t + 1)).C = M.β * (1 + f.r (t + 1)) * (f.alloc t).C
  euler_star : ∀ t, (f.alloc (t + 1)).Cs = M.β * (1 + f.r (t + 1)) * (f.alloc t).Cs
  budget : ∀ t, f.B (t + 1) = (1 + f.r t) * f.B t + (f.alloc t).q * (f.alloc t).y -
    (f.alloc t).C
  gross_rate_pos : ∀ t, 0 < 1 + f.r t
  no_ponzi : ∀ ε > 0, ∀ᶠ T in atTop, -ε < marketDiscount f.r T * ((1 + f.r T) * f.B T)
  transversality : ∀ ε > 0, ∃ᶠ T in atTop, marketDiscount f.r T * ((1 + f.r T) * f.B T) < ε

/-- **Foreign's budget is implied** (Walras's law, O&R fn 8): with `B*_t = −(n/(1−n))B_t`,
Foreign's real budget `B*_{t+1} = (1+r_t)B*_t + π*_t y*_t − C*_t` holds. -/
theorem IsFlexEqm.foreign_budget {M : ReduxParams} {f : FlexPath} (h : IsFlexEqm M f) (t : ℕ) :
    -(M.n / (1 - M.n)) * f.B (t + 1) = (1 + f.r t) * (-(M.n / (1 - M.n)) * f.B t) +
      (f.alloc t).qs * (f.alloc t).ys - (f.alloc t).Cs := by
  have hw := (h.static t).walras
  have hb := h.budget t
  have hn1 : 1 - M.n ≠ 0 := by linarith [M.hn1]
  rw [hb]
  field_simp
  linarith

/-- **Relative consumption is constant along any path** (exact form of (57), O&R p. 677): both
countries face the same real rate, so `C*_t/C_t = C*_0/C_0` for all `t`. -/
theorem IsFlexEqm.ratio_const {M : ReduxParams} {f : FlexPath} (h : IsFlexEqm M f) (t : ℕ) :
    (f.alloc t).Cs * (f.alloc 0).C = (f.alloc 0).Cs * (f.alloc t).C := by
  induction t with
  | zero => ring
  | succ t ih =>
    rw [h.euler t, h.euler_star t]
    linear_combination M.β * (1 + f.r (t + 1)) * ih

/-- A static allocation with outputs in ratio `λ = y*/y` has `y² (n + (1−n)λ^ρ) =
K(n + (1−n)λ^{−(θ+1)/θ})` (the gap relation with `y* = λy`; T9). -/
theorem IsStatic.sq_output {M : ReduxParams} {s : Allocation} (h : IsStatic M s) :
    s.y ^ 2 * (M.n + (1 - M.n) * (s.ys / s.y) ^ ((M.θ - 1) / M.θ)) =
      M.K * (M.n + (1 - M.n) * (s.ys / s.y) ^ (-(M.θ + 1) / M.θ)) := by
  have hθ0 : M.θ ≠ 0 := by linarith [M.hθ]
  have hrel := h.gap_relation
  set l := s.ys / s.y with hl
  have hlpos : 0 < l := div_pos h.ys_pos h.y_pos
  have hys : s.ys = l * s.y := by rw [hl]; have := h.y_pos.ne'; field_simp
  unfold gapFn at hrel
  rw [hys, mul_rpow hlpos.le h.y_pos.le, mul_rpow hlpos.le h.y_pos.le] at hrel
  have hsum : s.y ^ ((M.θ - 1) / M.θ) * s.y ^ ((M.θ + 1) / M.θ) = s.y ^ 2 := by
    rw [← rpow_add h.y_pos]
    have : (M.θ - 1) / M.θ + (M.θ + 1) / M.θ = 2 := by field_simp; ring
    rw [this, rpow_two]
  have hinv : s.y ^ (-(M.θ + 1) / M.θ) * s.y ^ ((M.θ + 1) / M.θ) = 1 := by
    rw [← rpow_add h.y_pos]
    have : -(M.θ + 1) / M.θ + (M.θ + 1) / M.θ = 0 := by ring
    rw [this, rpow_zero]
  have key : s.y ^ ((M.θ + 1) / M.θ) *
      (M.n * (M.K * s.y ^ (-(M.θ + 1) / M.θ) - s.y ^ ((M.θ - 1) / M.θ)) +
      (1 - M.n) * (M.K * (l ^ (-(M.θ + 1) / M.θ) * s.y ^ (-(M.θ + 1) / M.θ)) -
        l ^ ((M.θ - 1) / M.θ) * s.y ^ ((M.θ - 1) / M.θ))) = 0 := by
    rw [hrel, mul_zero]
  linear_combination -key + (M.n * M.K + (1 - M.n) * M.K * l ^ (-(M.θ + 1) / M.θ)) * hinv -
    (M.n + (1 - M.n) * l ^ ((M.θ - 1) / M.θ)) * hsum

/-- **No transitional dynamics under flexible prices** (T9; the exact nonlinear content of
O&R p. 660, p. 671 "the world economy jumps instantly to the steady state", and p. 677
"`b_t = b̄` for all `t ≥ 2`"). Along any flexible-price perfect-foresight equilibrium, let
`B̄ = (1 + r₀)B₀/(1 + δ)`. Then at EVERY date the allocation is the unique steady state
indexed by `B̄` (T7), the real rate is `r_t = δ` for all `t ≥ 1`, and bonds are `B_t = B̄` for
all `t ≥ 1`. Proof: equal real rates keep `C*/C` constant; the gap relation then pins `y` (and
so the whole static allocation) as a function of that ratio; constant consumption forces
`r = δ`; the budget with no-Ponzi and transversality forces income = expenditure (20). -/
theorem flexible_path_is_steady {M : ReduxParams} {f : FlexPath} (h : IsFlexEqm M f) :
    (∀ t, IsSteadyState M ((1 + f.r 0) * f.B 0 / (1 + M.δ)) (f.alloc t)) ∧
      (∀ t, f.r (t + 1) = M.δ) ∧ (∀ t, f.B (t + 1) = (1 + f.r 0) * f.B 0 / (1 + M.δ)) := by
  have hθ := M.hθ
  have hθ0 : M.θ ≠ 0 := by linarith
  have hK := M.K_pos
  have hn0 := M.hn0
  have hn1' : 0 < 1 - M.n := by linarith [M.hn1]
  have hδ := M.δ_pos
  -- step 1: the output ratio is constant
  have hst : ∀ t, IsStatic M (f.alloc t) := h.static
  have hratio : ∀ t, (f.alloc t).ys / (f.alloc t).y = (f.alloc 0).ys / (f.alloc 0).y := by
    intro t
    have hrt := h.ratio_const t
    -- `C/C* = (y*/y)^{(θ+1)/θ}` at each date
    have hCC : ∀ u, (f.alloc u).C / (f.alloc u).Cs =
        ((f.alloc u).ys / (f.alloc u).y) ^ ((M.θ + 1) / M.θ) := by
      intro u
      have hs := hst u
      have e1 := hs.C_mul_y
      have e2 := hs.Cs_mul_ys
      have e3 := hs.q_div_qs
      have hl : 0 < (f.alloc u).ys / (f.alloc u).y := div_pos hs.ys_pos hs.y_pos
      rw [rpow_succ_div hθ0 hl, ← e3]
      have := hs.y_pos.ne'
      have := hs.ys_pos.ne'
      have := hs.Cs_pos.ne'
      have := hs.qs_pos.ne'
      field_simp
      linear_combination (f.alloc u).qs * e1 - (f.alloc u).q * e2
    have hc : (f.alloc t).C / (f.alloc t).Cs = (f.alloc 0).C / (f.alloc 0).Cs := by
      have := (hst t).Cs_pos.ne'
      have := (hst 0).Cs_pos.ne'
      field_simp
      linarith
    rw [hCC t, hCC 0] at hc
    have hp : (0 : ℝ) < (M.θ + 1) / M.θ := div_pos (by linarith) (by linarith)
    exact (rpow_left_inj (div_pos (hst t).ys_pos (hst t).y_pos).le
      (div_pos (hst 0).ys_pos (hst 0).y_pos).le hp.ne').1 hc
  -- step 2: outputs, hence the whole allocation, are constant
  have hconst : ∀ t, f.alloc t = f.alloc 0 := by
    intro t
    have h1 := (hst t).sq_output
    have h2 := (hst 0).sq_output
    rw [hratio t] at h1
    have hlpos : 0 < (f.alloc 0).ys / (f.alloc 0).y := div_pos (hst 0).ys_pos (hst 0).y_pos
    have hfac : 0 < M.n + (1 - M.n) * ((f.alloc 0).ys / (f.alloc 0).y) ^ ((M.θ - 1) / M.θ) := by
      have := rpow_pos_of_pos hlpos ((M.θ - 1) / M.θ); positivity
    have hsq : (f.alloc t).y ^ 2 = (f.alloc 0).y ^ 2 := by
      have : ((f.alloc t).y ^ 2 - (f.alloc 0).y ^ 2) *
          (M.n + (1 - M.n) * ((f.alloc 0).ys / (f.alloc 0).y) ^ ((M.θ - 1) / M.θ)) = 0 := by
        linarith
      have := (mul_eq_zero.1 this).resolve_right hfac.ne'
      linarith
    have hy : (f.alloc t).y = (f.alloc 0).y := by
      have := (hst t).y_pos
      have := (hst 0).y_pos
      nlinarith [sq_nonneg ((f.alloc t).y - (f.alloc 0).y)]
    have hys : (f.alloc t).ys = (f.alloc 0).ys := by
      have h3 := hratio t
      rw [div_eq_div_iff (hst t).y_pos.ne' (hst 0).y_pos.ne', hy] at h3
      exact mul_right_cancel₀ (hst 0).y_pos.ne' h3
    exact (hst t).ext_of_outputs (hst 0) hy hys
  -- step 3: constant consumption forces `r = δ`
  have hr : ∀ t, f.r (t + 1) = M.δ := by
    intro t
    have he := h.euler t
    rw [hconst (t + 1), hconst t] at he
    exact steady_state_rate M.hβ0 (hst 0).C_pos he
  -- step 4: the budget with no-Ponzi and transversality gives (20)
  have hdisc : ∀ T, marketDiscount f.r T = (1 + M.δ)⁻¹ ^ T := by
    intro T
    unfold marketDiscount
    rw [Finset.prod_congr rfl (fun s _ => by rw [hr s]), Finset.prod_const, Finset.card_range]
  set W : ℕ → ℝ := fun t => (1 + f.r t) * f.B t with hW
  set a0 := f.alloc 0 with ha0
  have hWbud : ∀ t, W (t + 1) = (1 + M.δ) * W t + (1 + M.δ) * (a0.q * a0.y) -
      (1 + M.δ) * a0.C := by
    intro t
    simp only [hW]
    rw [hr t, h.budget t, hconst t]
    ring
  have hnp : ∀ ε > 0, ∀ᶠ T in atTop, -ε < (1 + M.δ)⁻¹ ^ T * W T := by
    intro ε hε
    filter_upwards [h.no_ponzi ε hε] with T hT
    rwa [hdisc T] at hT
  have htvc : ∀ ε > 0, ∃ᶠ T in atTop, (1 + M.δ)⁻¹ ^ T * W T < ε := by
    intro ε hε
    refine (h.transversality ε hε).mono fun T hT => ?_
    rwa [hdisc T] at hT
  obtain ⟨hC20, hWc⟩ := steady_state_budget hδ hWbud hnp htvc
  set Bbar := (1 + f.r 0) * f.B 0 / (1 + M.δ) with hBbar
  have hδ1 : (1 + M.δ) ≠ 0 := by linarith
  have hW0 : W 0 = (1 + M.δ) * Bbar := by simp only [hW, hBbar]; field_simp
  have hC : a0.C = M.δ * Bbar + a0.q * a0.y := by
    rw [hW0] at hC20
    have : (1 + M.δ) * (a0.C - (M.δ * Bbar + a0.q * a0.y)) = 0 := by linarith
    have := (mul_eq_zero.1 this).resolve_left hδ1
    linarith
  refine ⟨fun t => ?_, hr, fun t => ?_⟩
  · rw [hconst t]
    refine ⟨hst 0, hC, ?_⟩
    have hw := (hst 0).walras
    have hn1 : 1 - M.n ≠ 0 := by linarith
    rw [hC] at hw
    field_simp
    linarith
  · have h1 := hWc (t + 1)
    rw [hW0] at h1
    simp only [hW] at h1
    rw [hr t] at h1
    have : (1 + M.δ) * (f.B (t + 1) - Bbar) = 0 := by linarith
    have := (mul_eq_zero.1 this).resolve_left hδ1
    linarith

end ObstfeldRogoff.StickyPriceModels.ReduxSteadyState

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The redux model: the log-linear system

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §10.1.5–§10.1.6
(pp. 669–673) and the short-run current account of §10.1.7.2–§10.1.7.3 (pp. 675–677).

**Log-linearisation as differentiation (T10).** Each of the book's linear equations is the
derivative, at the symmetric steady state, of the corresponding exact equation written in
the logarithms of the variables. We state each one as a `HasDerivAt` along an arbitrary
direction of log-deviations (a directional derivative in every direction, i.e. the full
linearisation): the price indexes (27)–(28) (`hasDerivAt_log_bloc`), PPP (29), world demand
(30)–(31), world consumption (32), the labour–leisure conditions (33)–(34) (exactly linear in
logs), the Euler equations (35)–(36), money demand (37)–(38), (39), and the steady-state budgets
(40)–(41) (with `b̄ = dB̄/Cᵂ₀` a LEVEL change, since `B̄₀ = 0`).

**The steady-state linear system solved exactly (T11).** The long-run system (27)–(34), (40),
(41), (50), (51) has exactly one solution for every `b̄, m̄, m̄*`, namely (45)–(52) together with
the output levels `ȳ = −δb̄/2`, `ȳ* = nδb̄/(2(1−n))` (not given in the book) and the individual
prices (`steadyLinear_iff`). The wealth effect on relative consumption is dampened,
`(1+θ)/(2θ) < 1`, exactly when `θ > 1` (p. 672).

**The short-run current account (T12).** With preset prices, (27)–(28) give `p = (1−n)e` and
`p* = −ne`; (55) and (56) are derivatives of (54); `b̄ − b̄* = b̄/(1−n)`; and (57) holds EXACTLY
in the nonlinear model because both countries face the same real rate
(`consumption_ratio_exact`).
-/

namespace ObstfeldRogoff.StickyPriceModels.ReduxLogLinear

open Real Filter Topology ReduxPrimitives

/-! ## Log-linearisation of the price indexes (27)–(29) -/

/-- The derivative of `τ ↦ (A e^{τα})^{1−θ}` at `0` (used for (27)–(28)). -/
theorem hasDerivAt_rpow_exp {A α θ : ℝ} (hA : 0 < A) :
    HasDerivAt (fun τ => (A * Real.exp (τ * α)) ^ (1 - θ)) (A ^ (1 - θ) * ((1 - θ) * α)) 0 := by
  have e : (fun τ => (A * Real.exp (τ * α)) ^ (1 - θ)) =
      fun τ => A ^ (1 - θ) * Real.exp (τ * ((1 - θ) * α)) := by
    funext τ
    rw [mul_rpow hA.le (Real.exp_pos _).le, ← Real.exp_mul]
    ring_nf
  rw [e]
  have h := ((hasDerivAt_id (0 : ℝ)).mul_const ((1 - θ) * α)).exp.const_mul (A ^ (1 - θ))
  simpa using h

/-- **Log-linearising a two-bloc CES price index** (O&R (27)–(28), p. 669; T10): if the two bloc
prices are equal at the base point, `A e^{τα}` and `A e^{τβ}`, then
`d/dτ log [n a^{1−θ} + (1−n) b^{1−θ}]^{1/(1−θ)}` at `τ = 0` is `n α + (1−n) β`. -/
theorem hasDerivAt_log_bloc {θ n A α β : ℝ} (hθ : θ ≠ 1) (hn0 : 0 < n) (hn1 : n < 1)
    (hA : 0 < A) :
    HasDerivAt (fun τ => Real.log (blocPriceIndex θ n (A * Real.exp (τ * α))
      (A * Real.exp (τ * β)))) (n * α + (1 - n) * β) 0 := by
  have hθ' : 1 - θ ≠ 0 := sub_ne_zero.2 (Ne.symm hθ)
  set S : ℝ → ℝ := fun τ => n * (A * Real.exp (τ * α)) ^ (1 - θ) +
    (1 - n) * (A * Real.exp (τ * β)) ^ (1 - θ) with hS
  have hSpos : ∀ τ, 0 < S τ := fun τ => by
    have h1 := rpow_pos_of_pos (mul_pos hA (Real.exp_pos (τ * α))) (1 - θ)
    have h2 := rpow_pos_of_pos (mul_pos hA (Real.exp_pos (τ * β))) (1 - θ)
    have : 0 < 1 - n := by linarith
    simp only [hS]; positivity
  have e : (fun τ => Real.log (blocPriceIndex θ n (A * Real.exp (τ * α))
      (A * Real.exp (τ * β)))) = fun τ => 1 / (1 - θ) * Real.log (S τ) := by
    funext τ
    unfold blocPriceIndex
    rw [Real.log_rpow (hSpos τ)]
  rw [e]
  have hSd : HasDerivAt S (n * (A ^ (1 - θ) * ((1 - θ) * α)) +
      (1 - n) * (A ^ (1 - θ) * ((1 - θ) * β))) 0 :=
    ((hasDerivAt_rpow_exp (θ := θ) (α := α) hA).const_mul n).add
      ((hasDerivAt_rpow_exp (θ := θ) (α := β) hA).const_mul (1 - n))
  have hS0 : S 0 = A ^ (1 - θ) := by
    simp only [hS, zero_mul, Real.exp_zero, mul_one]; ring
  have hlog := (hSd.log (by rw [hS0]; exact (rpow_pos_of_pos hA _).ne')).const_mul (1 / (1 - θ))
  convert hlog using 1
  rw [hS0]
  have := (rpow_pos_of_pos hA (1 - θ)).ne'
  field_simp

/-- **(27)**, O&R p. 669 (T10): around `p̄₀(h) = 𝓔₀ p̄₀*(f)`, with log-deviations `a` of `p(h)`,
`e` of `𝓔` and `b` of `p*(f)`, the Home price index moves by `p = n a + (1−n)(e + b)`. -/
theorem linearise_27 {θ n ph0 E0 pfs0 a e b : ℝ} (hθ : θ ≠ 1) (hn0 : 0 < n) (hn1 : n < 1)
    (hph0 : 0 < ph0) (hbase : ph0 = E0 * pfs0) :
    HasDerivAt (fun τ => Real.log (blocPriceIndex θ n (ph0 * Real.exp (τ * a))
      ((E0 * Real.exp (τ * e)) * (pfs0 * Real.exp (τ * b)))))
      (n * a + (1 - n) * (e + b)) 0 := by
  have h := hasDerivAt_log_bloc (α := a) (β := e + b) hθ hn0 hn1 hph0
  convert h using 3 with τ
  rw [hbase, mul_add, Real.exp_add]
  ring_nf

/-- **(28)**, O&R p. 669 (T10): the Foreign price index moves by `p* = n(a − e) + (1−n) b`. -/
theorem linearise_28 {θ n ph0 E0 pfs0 a e b : ℝ} (hθ : θ ≠ 1) (hn0 : 0 < n) (hn1 : n < 1)
    (hpfs0 : 0 < pfs0) (hE0 : 0 < E0) (hbase : ph0 = E0 * pfs0) :
    HasDerivAt (fun τ => Real.log (blocPriceIndex θ n
      ((ph0 * Real.exp (τ * a)) / (E0 * Real.exp (τ * e))) (pfs0 * Real.exp (τ * b))))
      (n * (a - e) + (1 - n) * b) 0 := by
  have h := hasDerivAt_log_bloc (α := a - e) (β := b) hθ hn0 hn1 hpfs0
  convert h using 3 with τ
  rw [hbase, mul_sub, Real.exp_sub]
  have := (Real.exp_pos (τ * e)).ne'
  have := hE0.ne'
  field_simp

/-- **(29) requires no approximation**, O&R p. 670: PPP (7) holds exactly, so in logs
`log P − log P* = log 𝓔` at every point; hence `e = p − p*` for deviations. -/
theorem ppp_log_exact {θ n ph pfs E : ℝ} (hθ : θ ≠ 1) (hn0 : 0 < n) (hn1 : n < 1)
    (hph : 0 < ph) (hpfs : 0 < pfs) (hE : 0 < E) :
    Real.log (blocPriceIndex θ n ph (E * pfs)) - Real.log (blocPriceIndex θ n (ph / E) pfs) =
      Real.log E := by
  rw [bloc_ppp hθ hn0 hn1 hph hpfs hE, Real.log_mul hE.ne'
    (blocPriceIndex_pos hn0 hn1 (div_pos hph hE) hpfs).ne']
  ring

/-- The linear PPP identity (29) follows from the linear (27) and (28) (O&R p. 670). -/
theorem eq29_of_27_28 {n p ps ph pf e : ℝ} (h27 : p = n * ph + (1 - n) * (e + pf))
    (h28 : ps = n * (ph - e) + (1 - n) * pf) : e = p - ps := by
  rw [h27, h28]; ring

/-! ## Demand, world aggregates and labour supply (30)–(34) -/

/-- **(30)–(31) are exact in logs**, O&R p. 670 (T10): world demand (10) gives
`log y = −θ(log p(h) − log P) + log Cᵂ` at every point, so `y = θ(p − p(h)) + cᵂ` for
deviations. -/
theorem log_demand_exact {θ ph P X : ℝ} (hph : 0 < ph) (hP : 0 < P) (hX : 0 < X) :
    Real.log (cesDemand θ ph P X) = -θ * (Real.log ph - Real.log P) + Real.log X := by
  unfold cesDemand
  rw [Real.log_mul (rpow_pos_of_pos (div_pos hph hP) _).ne' hX.ne',
    Real.log_rpow (div_pos hph hP), Real.log_div hph.ne' hP.ne']

/-- **World consumption (32)** (the linearisation of (11)), O&R p. 670 (T10): around
`C̄ = C̄* = C₀`, `d log(nC + (1−n)C*) = n c + (1−n) c*`. -/
theorem linearise_world {n C0 c cs : ℝ} (hC0 : 0 < C0) :
    HasDerivAt (fun τ => Real.log (worldConsumption n (C0 * Real.exp (τ * c))
      (C0 * Real.exp (τ * cs)))) (n * c + (1 - n) * cs) 0 := by
  unfold worldConsumption
  have h1 : HasDerivAt (fun τ => C0 * Real.exp (τ * c)) (C0 * c) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const c).exp.const_mul C0
  have h2 : HasDerivAt (fun τ => C0 * Real.exp (τ * cs)) (C0 * cs) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const cs).exp.const_mul C0
  have hsum : n * (C0 * Real.exp (0 * c)) + (1 - n) * (C0 * Real.exp (0 * cs)) = C0 := by
    simp only [zero_mul, Real.exp_zero, mul_one]; ring
  have h := ((h1.const_mul n).add (h2.const_mul (1 - n))).log
    (by simp only [Pi.add_apply]; rw [hsum]; exact hC0.ne')
  convert h using 1
  simp
  field_simp
  ring

/-- **(32) from (27), (28), (30), (31)**, O&R p. 670: the population-weighted sum of the demand
equations gives `cᵂ = yᵂ` because `n p(h) + (1−n)p*(f) = n p + (1−n) p*`. -/
theorem eq32_of_demands {n θ p ps ph pf e y ys cW : ℝ} (h27 : p = n * ph + (1 - n) * (e + pf))
    (h28 : ps = n * (ph - e) + (1 - n) * pf) (h30 : y = θ * (p - ph) + cW)
    (h31 : ys = θ * (ps - pf) + cW) : n * y + (1 - n) * ys = cW := by
  rw [h30, h31, h27, h28]; ring

/-- **(33)–(34) are exact in logs**, O&R p. 670 (T10): if the labour–leisure condition (15)
`y^{(θ+1)/θ} = K (Cᵂ)^{1/θ}/C` holds at a base point and at a new point, then the log
changes satisfy `(θ+1) Δlog y = −θ Δlog C + Δlog Cᵂ` exactly. -/
theorem labour_log_exact {θ K y0 y1 C0 C1 X0 X1 : ℝ} (hθ : θ ≠ 0) (hK : 0 < K)
    (hy0 : 0 < y0) (hy1 : 0 < y1) (hC0 : 0 < C0) (hC1 : 0 < C1) (hX0 : 0 < X0) (hX1 : 0 < X1)
    (h0 : y0 ^ ((θ + 1) / θ) = K * X0 ^ (1 / θ) / C0)
    (h1 : y1 ^ ((θ + 1) / θ) = K * X1 ^ (1 / θ) / C1) :
    (θ + 1) * (Real.log y1 - Real.log y0) =
      -θ * (Real.log C1 - Real.log C0) + (Real.log X1 - Real.log X0) := by
  have l0 := congrArg Real.log h0
  have l1 := congrArg Real.log h1
  rw [Real.log_rpow hy0, Real.log_div (mul_pos hK (rpow_pos_of_pos hX0 _)).ne' hC0.ne',
    Real.log_mul hK.ne' (rpow_pos_of_pos hX0 _).ne', Real.log_rpow hX0] at l0
  rw [Real.log_rpow hy1, Real.log_div (mul_pos hK (rpow_pos_of_pos hX1 _)).ne' hC1.ne',
    Real.log_mul hK.ne' (rpow_pos_of_pos hX1 _).ne', Real.log_rpow hX1] at l1
  have e := congrArg (fun z => θ * z) (show (θ + 1) / θ * Real.log y1 - (θ + 1) / θ *
    Real.log y0 = 1 / θ * Real.log X1 - Real.log C1 - (1 / θ * Real.log X0 - Real.log C0) by
      linarith)
  field_simp at e
  linarith

/-! ## The Euler equation (35)–(36) and money demand (37)–(39) -/

/-- **(35)–(36)**, O&R p. 670 (T10): with `C_{t+1}/C_t = β(1 + r_{t+1})` and `β(1+δ) = 1`, the
log growth of consumption at `r = δ(1 + τ r̂)` has derivative `δ r̂/(1 + δ)` at `τ = 0`
(`r̂ = dr/r̄`, `r̄ = δ`), and is `0` at the steady state. -/
theorem linearise_35 {β δ rh : ℝ} (hδ : 0 < δ) (hβ : β * (1 + δ) = 1) :
    HasDerivAt (fun τ => Real.log (β * (1 + δ * (1 + τ * rh)))) (δ * rh / (1 + δ)) 0 ∧
      Real.log (β * (1 + δ * (1 + 0 * rh))) = 0 := by
  constructor
  · have h1 : HasDerivAt (fun τ => β * (1 + δ * (1 + τ * rh))) (β * (δ * rh)) 0 := by
      have := (((hasDerivAt_id (0 : ℝ)).mul_const rh).const_add 1).const_mul δ
      simpa using (this.const_add 1).const_mul β
    have h0 : β * (1 + δ * (1 + 0 * rh)) = 1 := by rw [zero_mul, add_zero, mul_one, hβ]
    have h2 := h1.log (by rw [h0]; norm_num)
    convert h2 using 1
    simp only [zero_mul, add_zero, mul_one]
    rw [hβ]
    have : (1 + δ) ≠ 0 := by linarith
    field_simp
    have hb : β = 1 / (1 + δ) := by field_simp; linarith
    rw [hb]
    field_simp
  · simp [hβ]

/-- **(37)–(38)**, O&R p. 670 (T10): write money demand (14) as
`log(M/P) = log χ + log C + log((1+i)/i)` with `1 + i_{t+1} = (P_{t+1}/P_t)(1 + r_{t+1})`.
Around `P_{t+1} = P_t`, `r = δ` (so `i = δ`), along `P_{t+1}/P_t = e^{τ Δp}`,
`r = δ(1 + τ r̂)`, the term `log((1+i)/i)` has derivative `−r̂/(1+δ) − Δp/δ`. -/
theorem linearise_37 {δ dp rh : ℝ} (hδ : 0 < δ) :
    HasDerivAt (fun τ => Real.log ((Real.exp (τ * dp) * (1 + δ * (1 + τ * rh))) /
      (Real.exp (τ * dp) * (1 + δ * (1 + τ * rh)) - 1)))
      (-(rh / (1 + δ)) - dp / δ) 0 := by
  set g : ℝ → ℝ := fun τ => Real.exp (τ * dp) * (1 + δ * (1 + τ * rh)) with hg
  have hgd : HasDerivAt g (dp * (1 + δ) + δ * rh) 0 := by
    have h1 := ((hasDerivAt_id (0 : ℝ)).mul_const dp).exp
    have h2 : HasDerivAt (fun τ => 1 + δ * (1 + τ * rh)) (δ * rh) 0 := by
      have := (((hasDerivAt_id (0 : ℝ)).mul_const rh).const_add 1).const_mul δ
      simpa using this.const_add 1
    have h3 := h1.mul h2
    have e : g = (fun x => Real.exp (id x * dp)) * (fun τ => 1 + δ * (1 + τ * rh)) := by
      funext τ; simp [hg]
    rw [e]
    convert h3 using 1
    simp
  have hg0 : g 0 = 1 + δ := by simp [hg]
  have hnum := hgd.log (by rw [hg0]; linarith)
  have hden := (hgd.sub_const 1).log (by rw [hg0]; simp; linarith)
  have hev : ∀ᶠ τ in 𝓝 (0 : ℝ), 1 < g τ :=
    hgd.continuousAt.eventually (lt_mem_nhds (by rw [hg0]; linarith))
  have hsum := hnum.sub hden
  have hcongr : (fun τ => Real.log (g τ / (g τ - 1))) =ᶠ[𝓝 0]
      fun τ => Real.log (g τ) - Real.log (g τ - 1) := by
    filter_upwards [hev] with τ hτ
    rw [Real.log_div (by linarith) (by linarith)]
  have hfin := hsum.congr_of_eventuallyEq hcongr
  convert hfin using 1
  rw [hg0]
  simp only [add_sub_cancel_left]
  have : (1 + δ) ≠ 0 := by linarith
  have := hδ.ne'
  field_simp
  ring

/-- **(39) = (37) − (38) with (29)**, O&R p. 671. -/
theorem eq39_of_37_38 {δ m ms p ps p1 ps1 c cs r e e1 : ℝ}
    (h37 : m - p = c - r / (1 + δ) - (p1 - p) / δ)
    (h38 : ms - ps = cs - r / (1 + δ) - (ps1 - ps) / δ)
    (h29 : e = p - ps) (h29' : e1 = p1 - ps1) :
    m - ms - e = c - cs - (e1 - e) / δ := by
  rw [h29, h29']
  have : (p1 - ps1 - (p - ps)) / δ = (p1 - p) / δ - (ps1 - ps) / δ := by ring
  rw [this]
  linarith

/-! ## The steady-state budgets (40)–(41) -/

/-- **(40)**, O&R p. 671 (T10): steady-state income = expenditure (20), `C = δB + π y`, around
`B̄₀ = 0`, `π̄₀ = 1`, `ȳ₀ = C̄₀`: along `B = τ b̄ C̄₀` (a LEVEL change, since `B̄₀ = 0`),
`π = e^{τ u}` (`u = p̄(h) − p̄`) and `y = C̄₀ e^{τ ŷ}`, `d log C = δ b̄ + u + ŷ`. -/
theorem linearise_40 {δ b u yh C0 : ℝ} (hC0 : 0 < C0) :
    HasDerivAt (fun τ => Real.log (δ * (τ * b * C0) + Real.exp (τ * u) * (C0 * Real.exp (τ * yh))))
      (δ * b + u + yh) 0 := by
  have h1 : HasDerivAt (fun τ => δ * (τ * b * C0)) (δ * (b * C0)) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).mul_const b).mul_const C0
    simpa using this.const_mul δ
  have h2 : HasDerivAt (fun τ => Real.exp (τ * u)) u 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const u).exp
  have h3 : HasDerivAt (fun τ => C0 * Real.exp (τ * yh)) (C0 * yh) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const yh).exp.const_mul C0
  have h4 := h1.add (h2.mul h3)
  have hval : δ * (0 * b * C0) + Real.exp (0 * u) * (C0 * Real.exp (0 * yh)) = C0 := by simp
  have h5 := h4.log (by simp only [Pi.add_apply, Pi.mul_apply]; rw [hval]; exact hC0.ne')
  have e : (fun τ => Real.log (δ * (τ * b * C0) + Real.exp (τ * u) * (C0 * Real.exp (τ * yh)))) =
      fun τ => Real.log ((fun τ => δ * (τ * b * C0)) τ +
        ((fun τ => Real.exp (τ * u)) * fun τ => C0 * Real.exp (τ * yh)) τ) := by
    funext τ; simp
  rw [e]
  convert h5 using 1
  simp only [Pi.add_apply, Pi.mul_apply]
  rw [hval]
  simp only [zero_mul, Real.exp_zero, one_mul]
  field_simp
  ring

/-- **(41)**, O&R p. 671 (T10): Foreign's steady-state budget (21), `C* = −(n/(1−n))δB + π* y*`,
linearises to `c̄* = −(n/(1−n))δ b̄ + p̄*(f) + ȳ* − p̄*`. -/
theorem linearise_41 {n δ b u yh C0 : ℝ} (hC0 : 0 < C0) :
    HasDerivAt (fun τ => Real.log (-(n / (1 - n)) * δ * (τ * b * C0) +
      Real.exp (τ * u) * (C0 * Real.exp (τ * yh))))
      (-(n / (1 - n)) * δ * b + u + yh) 0 := by
  have h := linearise_40 (δ := -(n / (1 - n)) * δ) (b := b) (u := u) (yh := yh) hC0
  convert h using 2 with τ

/-! ## The steady-state linear system (42)–(52) (T11) -/

/-- The unknowns of the long-run linear system, O&R §10.1.6 (pp. 671–673): log changes of
consumption `c̄, c̄*`, output `ȳ, ȳ*`, prices `p̄(h), p̄*(f), p̄, p̄*`, the exchange rate `ē`
and world consumption `c̄ᵂ`. -/
structure SteadyVars where
  c : ℝ
  cs : ℝ
  y : ℝ
  ys : ℝ
  ph : ℝ
  pf : ℝ
  p : ℝ
  ps : ℝ
  e : ℝ
  cW : ℝ

/-- **The long-run linear system**, O&R p. 671: barred (27), (28), (30), (31), (11)/(32), (33),
(34), the budgets (40), (41) and the long-run money demands (50), (51) (steady-state (37)–(38)
with constant prices, `m̄ − p̄ = c̄`), for given `b̄`, `m̄`, `m̄*`. -/
structure SteadyLinear (L : ReduxLinear) (b m ms : ℝ) (v : SteadyVars) : Prop where
  eq27 : v.p = L.n * v.ph + (1 - L.n) * (v.e + v.pf)
  eq28 : v.ps = L.n * (v.ph - v.e) + (1 - L.n) * v.pf
  eq30 : v.y = L.θ * (v.p - v.ph) + v.cW
  eq31 : v.ys = L.θ * (v.ps - v.pf) + v.cW
  eq32 : v.cW = L.n * v.c + (1 - L.n) * v.cs
  eq33 : (L.θ + 1) * v.y = -L.θ * v.c + v.cW
  eq34 : (L.θ + 1) * v.ys = -L.θ * v.cs + v.cW
  eq40 : v.c = L.δ * b + v.ph + v.y - v.p
  eq41 : v.cs = -(L.n / (1 - L.n)) * L.δ * b + v.pf + v.ys - v.ps
  eq50 : v.p = m - v.c
  eq51 : v.ps = ms - v.cs

/-- The closed-form long-run solution, O&R (45)–(52), p. 672–673, with the output levels
`ȳ = −δb̄/2`, `ȳ* = nδb̄/(2(1−n))` and the individual goods prices. -/
noncomputable def steadySolution (L : ReduxLinear) (b m ms : ℝ) : SteadyVars where
  c := (1 + L.θ) * L.δ * b / (2 * L.θ)
  cs := -(L.n / (1 - L.n)) * ((1 + L.θ) * L.δ * b / (2 * L.θ))
  y := -(L.δ * b) / 2
  ys := L.n * L.δ * b / (2 * (1 - L.n))
  p := m - (1 + L.θ) * L.δ * b / (2 * L.θ)
  ps := ms + (L.n / (1 - L.n)) * ((1 + L.θ) * L.δ * b / (2 * L.θ))
  e := m - ms - (1 + L.θ) * L.δ * b / (2 * L.θ * (1 - L.n))
  ph := m - (1 + L.θ) * L.δ * b / (2 * L.θ) + L.δ * b / (2 * L.θ)
  pf := ms + (L.n / (1 - L.n)) * ((1 + L.θ) * L.δ * b / (2 * L.θ)) -
    L.n * L.δ * b / (2 * L.θ * (1 - L.n))
  cW := 0

/-- **The long-run linear system has exactly one solution** (T11; O&R (42)–(52),
pp. 672–673): `SteadyLinear` holds IF AND ONLY IF the unknowns equal `steadySolution`. -/
theorem steadyLinear_iff (L : ReduxLinear) (b m ms : ℝ) (v : SteadyVars) :
    SteadyLinear L b m ms v ↔ v = steadySolution L b m ms := by
  have hθ : L.θ ≠ 0 := by linarith [L.hθ]
  have hθ1 : L.θ + 1 ≠ 0 := by linarith [L.hθ]
  have hn : 1 - L.n ≠ 0 := by linarith [L.hn1]
  constructor
  · intro h
    obtain ⟨h27, h28, h30, h31, h32, h33, h34, h40, h41, h50, h51⟩ := h
    rcases v with ⟨c, cs, y, ys, ph, pf, p, ps, e, cW⟩
    simp only at h27 h28 h30 h31 h32 h33 h34 h40 h41 h50 h51
    -- world aggregates (47)
    have s1 : p - ps = e := by linear_combination h27 - h28
    have s3 : L.n * y + (1 - L.n) * ys = cW := by
      have := eq32_of_demands h27 h28 h30 h31; linarith
    have s4 : cW = 0 := by
      have h2 : 2 * L.θ * cW = 0 := by
        linear_combination L.n * h33 + (1 - L.n) * h34 - (L.θ + 1) * s3 + L.θ * h32
      rcases mul_eq_zero.1 h2 with h | h
      · exact absurd h (mul_ne_zero two_ne_zero hθ)
      · exact h
    subst s4
    -- differences (42)–(45)
    have s6 : y - ys = -L.θ * (ph - e - pf) := by linear_combination h30 - h31 + L.θ * s1
    have h41' : (1 - L.n) * cs = -(L.n * L.δ * b) + (1 - L.n) * (pf + ys - ps) := by
      rw [h41]; field_simp; ring
    have s7 : (1 - L.n) * (c - cs) = L.δ * b + (1 - L.n) * ((ph - e - pf) + (y - ys)) := by
      linear_combination (1 - L.n) * h40 - h41' - (1 - L.n) * s1
    have s8 : (L.θ + 1) * (ph - e - pf) = c - cs := by
      have h2 : L.θ * ((L.θ + 1) * (ph - e - pf) - (c - cs)) = 0 := by
        linear_combination h34 - h33 + (L.θ + 1) * s6
      have := (mul_eq_zero.1 h2).resolve_left hθ
      linarith
    have s9 : c - cs = (1 + L.θ) * L.δ * b / (2 * L.θ * (1 - L.n)) := by
      have h2 : 2 * L.θ * (1 - L.n) * (c - cs) = (1 + L.θ) * L.δ * b := by
        linear_combination (L.θ + 1) * s7 + (1 - L.n) * (1 - L.θ) * s8 +
          (1 - L.n) * (L.θ + 1) * s6
      field_simp
      linarith
    -- levels (48)–(49)
    have hc : c = (1 + L.θ) * L.δ * b / (2 * L.θ) := by
      have : c = (1 - L.n) * (c - cs) := by linear_combination -h32
      rw [this, s9]; field_simp
    have hcs : cs = -(L.n / (1 - L.n)) * ((1 + L.θ) * L.δ * b / (2 * L.θ)) := by
      have : cs = c - (c - cs) := by ring
      rw [this, s9, hc]; field_simp; ring
    have hy : y = -(L.δ * b) / 2 := by
      have : y = -L.θ * c / (L.θ + 1) := by field_simp; linarith
      rw [this, hc]; field_simp; ring
    have hys : ys = L.n * L.δ * b / (2 * (1 - L.n)) := by
      have : ys = -L.θ * cs / (L.θ + 1) := by field_simp; linarith
      rw [this, hcs]; field_simp; ring
    have hT : ph - e - pf = L.δ * b / (2 * L.θ * (1 - L.n)) := by
      have : ph - e - pf = (c - cs) / (L.θ + 1) := by field_simp; linarith
      rw [this, s9]; field_simp; ring
    have hp : p = m - (1 + L.θ) * L.δ * b / (2 * L.θ) := by rw [h50, hc]
    have hps : ps = ms + (L.n / (1 - L.n)) * ((1 + L.θ) * L.δ * b / (2 * L.θ)) := by
      rw [h51, hcs]; ring
    have he : e = m - ms - (1 + L.θ) * L.δ * b / (2 * L.θ * (1 - L.n)) := by
      rw [← s1, hp, hps]; field_simp; ring
    have hph : ph = m - (1 + L.θ) * L.δ * b / (2 * L.θ) + L.δ * b / (2 * L.θ) := by
      have : ph = p + (1 - L.n) * (ph - e - pf) := by linear_combination -h27
      rw [this, hp, hT]; field_simp
    have hpf : pf = ms + (L.n / (1 - L.n)) * ((1 + L.θ) * L.δ * b / (2 * L.θ)) -
        L.n * L.δ * b / (2 * L.θ * (1 - L.n)) := by
      have : pf = ps - L.n * (ph - e - pf) := by linear_combination -h28
      rw [this, hps, hT]; ring
    simp only [steadySolution, SteadyVars.mk.injEq]
    exact ⟨hc, hcs, hy, hys, hph, hpf, hp, hps, he, trivial⟩
  · intro h
    subst h
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [steadySolution] <;> field_simp <;> ring

/-- **Existence and uniqueness of the long-run linear solution** (T11): for every `b̄, m̄, m̄*`
the system has exactly one solution. -/
theorem steadyLinear_existsUnique (L : ReduxLinear) (b m ms : ℝ) :
    ∃! v, SteadyLinear L b m ms v :=
  ⟨steadySolution L b m ms, (steadyLinear_iff L b m ms _).2 rfl,
    fun v hv => (steadyLinear_iff L b m ms v).1 hv⟩

/-- **(45)–(47), (52) and the output levels**, O&R pp. 672–673 (T11): any solution of the
long-run system has `c̄ − c̄* = (1+θ)δb̄/(2θ(1−n))` (45), `p̄(h) − ē − p̄*(f) = δb̄/(2θ(1−n))`
(46), `ȳᵂ = c̄ᵂ = 0` (47), `ȳ − ȳ* = −δb̄/(2(1−n))`, `ȳ = −δb̄/2`, `ȳ* = nδb̄/(2(1−n))`, and
`ē = m̄ − m̄* − (c̄ − c̄*)` (52). -/
theorem steadyLinear_consequences {L : ReduxLinear} {b m ms : ℝ} {v : SteadyVars}
    (h : SteadyLinear L b m ms v) :
    v.c - v.cs = (1 + L.θ) * L.δ * b / (2 * L.θ * (1 - L.n)) ∧
    v.ph - v.e - v.pf = L.δ * b / (2 * L.θ * (1 - L.n)) ∧
    L.n * v.y + (1 - L.n) * v.ys = 0 ∧ v.cW = 0 ∧
    v.y - v.ys = -(L.δ * b) / (2 * (1 - L.n)) ∧ v.y = -(L.δ * b) / 2 ∧
    v.ys = L.n * L.δ * b / (2 * (1 - L.n)) ∧ v.e = m - ms - (v.c - v.cs) := by
  have hv := (steadyLinear_iff L b m ms v).1 h
  have hθ : L.θ ≠ 0 := by linarith [L.hθ]
  have hn : 1 - L.n ≠ 0 := by linarith [L.hn1]
  subst hv
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [steadySolution] <;> (try field_simp) <;>
    (try ring)

/-- **The wealth effect on relative consumption is dampened exactly when `θ > 1`** (O&R p. 672,
"the impact of wealth transfers on consumption differentials is less (recall `θ > 1`)"): for
`θ > 0`, `(1+θ)/(2θ) < 1 ⟺ θ > 1`. -/
theorem dampening_iff {θ : ℝ} (hθ : 0 < θ) : (1 + θ) / (2 * θ) < 1 ↔ 1 < θ := by
  rw [div_lt_one (by positivity)]
  constructor <;> intro h <;> linarith

/-! ## The short-run current account (54)–(57) (T12) -/

/-- **Short-run price levels with preset prices**, O&R p. 677 (T12): with `p(h) = p*(f) = 0`
in (27)–(28), `p = (1−n)e` and `p* = −ne`. -/
theorem shortRun_prices {n p ps e : ℝ} (h27 : p = n * 0 + (1 - n) * (e + 0))
    (h28 : ps = n * (0 - e) + (1 - n) * 0) : p = (1 - n) * e ∧ ps = -(n * e) := by
  constructor <;> [rw [h27]; rw [h28]] <;> ring

/-- **(55)–(56) as derivatives of (54)**, O&R pp. 675–677 (T10/T12): with `B₁ = 0`, (54) gives
`B₂ = π₁ y₁ − C₁`. Along `π₁ = e^{τu}`, `y₁ = C̄₀e^{τŷ}`, `C₁ = C̄₀e^{τĉ}`, the normalised
level `B₂/C̄₀` has derivative `u + ŷ − ĉ`. With preset prices `u = p(h) − p = −(1−n)e` this is
(55), `b̄ = y − c − (1−n)e`; for Foreign `u = p*(f) − p* = ne` gives (56). -/
theorem linearise_55 {u yh ch C0 : ℝ} (hC0 : 0 < C0) :
    HasDerivAt (fun τ => (Real.exp (τ * u) * (C0 * Real.exp (τ * yh)) -
      C0 * Real.exp (τ * ch)) / C0) (u + yh - ch) 0 := by
  have h2 : HasDerivAt (fun τ => Real.exp (τ * u)) u 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const u).exp
  have h3 : HasDerivAt (fun τ => C0 * Real.exp (τ * yh)) (C0 * yh) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const yh).exp.const_mul C0
  have h4 : HasDerivAt (fun τ => C0 * Real.exp (τ * ch)) (C0 * ch) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const ch).exp.const_mul C0
  have h := ((h2.mul h3).sub h4).div_const C0
  convert h using 1
  simp only [zero_mul, Real.exp_zero, one_mul, mul_one]
  field_simp

/-- **(55)–(56) and the per-capita differential** (T12; O&R p. 677 and the p. 688 correction):
if `b̄ = y − c − (1−n)e`, `b̄* = y* − c* + ne` and net foreign assets sum to zero,
`n b̄ + (1−n) b̄* = 0` (17), then `b̄* = −(n/(1−n)) b̄`, `b̄ − b̄* = b̄/(1−n)` and
`b̄/(1−n) = (y − y*) − (c − c*) − e` (62). -/
theorem shortRun_ca {n y ys c cs e b bs : ℝ} (hn1 : n < 1) (h55 : b = y - c - (1 - n) * e)
    (h56 : bs = ys - cs + n * e) (h17 : n * b + (1 - n) * bs = 0) :
    bs = -(n / (1 - n)) * b ∧ b - bs = b / (1 - n) ∧
      b / (1 - n) = (y - ys) - (c - cs) - e := by
  have hn : 1 - n ≠ 0 := by linarith
  have hbs : bs = -(n / (1 - n)) * b := by field_simp; linarith
  refine ⟨hbs, ?_, ?_⟩
  · rw [hbs]; field_simp; ring
  · have : b - bs = (y - ys) - (c - cs) - e := by rw [h55, h56]; ring
    rw [← this, hbs]; field_simp; ring

/-- **(57) holds exactly in the nonlinear model** (T12; O&R p. 677): if both countries' Euler
equations (13) hold at the common real rate, `C₂ = β(1+r)C₁` and `C₂* = β(1+r)C₁*`, then
`C₂/C₂* = C₁/C₁*`; in logs, relative consumption changes are permanent,
`(log C₂ − log C₂*) = (log C₁ − log C₁*)`. -/
theorem consumption_ratio_exact {β r C1 C2 Cs1 Cs2 : ℝ} (hβ : 0 < β) (hr : 0 < 1 + r)
    (hC1 : 0 < C1) (hCs1 : 0 < Cs1) (he : C2 = β * (1 + r) * C1)
    (hes : Cs2 = β * (1 + r) * Cs1) :
    C2 * Cs1 = Cs2 * C1 ∧ Real.log C2 - Real.log Cs2 = Real.log C1 - Real.log Cs1 := by
  refine ⟨by rw [he, hes]; ring, ?_⟩
  have hk : 0 < β * (1 + r) := mul_pos hβ hr
  rw [he, hes, Real.log_mul hk.ne' hC1.ne', Real.log_mul hk.ne' hCs1.ne']
  ring

/-- **(57) in log-deviation form**, O&R p. 677: measured from a symmetric base `C̄₀ = C̄₀*`,
`c̄ − c̄* = c − c*` exactly. -/
theorem eq57_exact {β r C0 C1 C2 Cs1 Cs2 : ℝ} (hβ : 0 < β) (hr : 0 < 1 + r)
    (hC1 : 0 < C1) (hCs1 : 0 < Cs1) (he : C2 = β * (1 + r) * C1)
    (hes : Cs2 = β * (1 + r) * Cs1) :
    (Real.log C2 - Real.log C0) - (Real.log Cs2 - Real.log C0) =
      (Real.log C1 - Real.log C0) - (Real.log Cs1 - Real.log C0) := by
  have := (consumption_ratio_exact hβ hr hC1 hCs1 he hes).2
  linarith

end ObstfeldRogoff.StickyPriceModels.ReduxLogLinear

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The redux model: money shocks with preset prices

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §10.1.7
(pp. 674–683), §10.1.8.1 (pp. 683–684), p. 688 (country size) and Exercise 1 (p. 713).

* **No overshooting, EXACTLY (T13)**: for ANY permanent money shock after which the economy is
  in a flexible-price steady state from date 2, money demand (14), the Euler equation (13) and
  Fisher parity force `i₂ = δ` in each country exactly (`nominal_rate_exact`); with exact
  uncovered interest parity (real bonds + PPP, `uip_exact`) the exchange rate jumps at once to
  its long-run value, `𝓔₁ = 𝓔₂` (`no_overshooting_exact`). The linear version (58)–(60)
  (`mm_no_overshooting`) and the forward solution (61) under a no-bubble condition, with
  existence and uniqueness (`forward_solution_unique`, `forward_solution_exists`).
* **The GG schedule and the closed forms (62)–(68) (T14)** and **world aggregates (69)–(74)
  (T15)**: the full short-run/long-run linear system (`MoneyShockEqm`) has exactly one
  solution for every `m, m*` (`moneyShock_iff`), namely `e = [δ(1+θ)+2θ](m−m*)/D` (65),
  `c − c* = δ(θ²−1)(m−m*)/D` (66), `b̄ = 2(1−n)(θ−1)(m−m*)/(δ(1+θ)+2)` (67), (68),
  `cᵂ = mᵂ = yᵂ` (72), `r = −((1+δ)/δ)mᵂ` (73), and (74).
* **Comparative statics (T14)**: `e/(m−m*)` equals 1 at `θ = 1`, lies in `(0,1)` for `θ > 1`, is
  strictly decreasing in `θ` and tends to 0; the GG slope tends to 0 ("horizontal"); the
  short-run terms-of-trade effect exceeds the long-run one, their ratio being `O(δ)`; the CA
  effect falls with `n`. **(65) corrected**: `e < m − m*` iff `m − m* > 0` (for a contraction the
  inequality reverses); in general `|e| < |m − m*|`.
* **p. 688 corrected**: country size DOES enter the current account (67); the size-free object
  is the per-capita differential `b̄ − b̄* = b̄/(1−n)`.
* **The nominal interest rate is unchanged (T15)**: `î = 0` in each country after any permanent
  shock (`nominal_rate_unchanged`), the linear shadow of `nominal_rate_exact`.
* **Temporary shocks (fn 16, T16)**: effects are those of a permanent shock scaled by
  `δ/(1+δ)`, and the Home currency ends PERMANENTLY APPRECIATED, `e_t = −(c − c*) < 0` for
  `t ≥ 2` (not stated in the book).
* **Money growth (Exercise 1)**: `1 + ī = (1+δ)(1+μ)`, (26′), (37′), the MM′ schedule
  `e = ν(1+ī)/ī − (c−c*)` and the solution `e = [δ(1+θ)+2θ]ν(1+ī)/(ī D)`, and the variant with
  the growth change from date 2 (intercept `ν/ī`).
* **The equiproportionate shock, EXACTLY (10.1.8.1, T19)**: in the nonlinear model with preset
  prices, `M → μM`, `M* → μM*` has a unique equilibrium: `𝓔₁ = 𝓔₀`, `B₂ = 0`,
  `C₁ = C₁* = y₁ = y₁* = μȳ₀`, `i₂ = δ`, `1 + r₂ = (1+δ)/μ` (`equiproportionate_unique`,
  `equiproportionate_exists`). Output is demand-determined only while price ≥ marginal cost,
  `μ ≤ (θ/(θ−1))^{1/2}`; on that range the exact utility gain
  `log μ − ((θ−1)/(2θ))(μ² − 1)` is positive for `μ > 1` and has derivative `1/θ` at `μ = 1`.
-/

namespace ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks

open Real Filter Topology ReduxPrimitives ReduxLogLinear ReduxSteadyState

/-! ## No overshooting, exactly (T13) -/

/-- **The nominal interest rate after a permanent money shock is exactly `δ`** (T13; the exact
content of O&R (58)–(60), p. 678). Suppose money is permanently changed, `M₂ = M₁`, and from
date 2 the economy is in a steady state (constant prices, `i₃ = δ`). Money demand (14) at dates
1 and 2, the Euler equation (13) `C₂ = β(1+r₂)C₁`, Fisher parity
`1 + i₂ = (P₂/P₁)(1 + r₂)` and `β(1+δ) = 1` force `i₂ = δ`. -/
theorem nominal_rate_exact {β δ χ M P1 P2 C1 C2 r2 i2 : ℝ} (hβ : 0 < β) (hδ : 0 < δ)
    (hβδ : β * (1 + δ) = 1) (hχ : 0 < χ) (hM : 0 < M) (hP1 : 0 < P1) (hP2 : 0 < P2)
    (hC1 : 0 < C1) (hi2 : 0 < i2) (hr2 : 0 < 1 + r2)
    (hmd1 : M / P1 = χ * C1 * ((1 + i2) / i2)) (hmd2 : M / P2 = χ * C2 * ((1 + δ) / δ))
    (heuler : C2 = β * (1 + r2) * C1) (hfisher : 1 + i2 = P2 / P1 * (1 + r2)) : i2 = δ := by
  rw [heuler] at hmd2
  rw [div_eq_iff hP1.ne'] at hmd1
  rw [div_eq_iff hP2.ne'] at hmd2
  have a1 : M * i2 = χ * C1 * ((1 + i2) * P1) := by
    rw [hmd1]; field_simp
  have a2 : M * δ = χ * C1 * (1 + r2) * P2 * (β * (1 + δ)) := by
    rw [hmd2]; field_simp
  have hfis : (1 + i2) * P1 = P2 * (1 + r2) := by
    rw [hfisher]; field_simp
  rw [hfis] at a1
  rw [hβδ, mul_one] at a2
  have : M * (i2 - δ) = 0 := by linear_combination a1 - a2
  have := (mul_eq_zero.1 this).resolve_left hM.ne'
  linarith

/-- **Exact uncovered interest parity** (O&R p. 663 and p. 677): with a real bond in units of the
common consumption basket and PPP `𝓔 = P/P*` (7), the two Fisher relations
`1 + i = (P₂/P₁)(1 + r)` and `1 + i* = (P₂*/P₁*)(1 + r)` give `1 + i = (𝓔₂/𝓔₁)(1 + i*)`. -/
theorem uip_exact {P1 P2 Ps1 Ps2 r i is : ℝ} (hP1 : 0 < P1) (hPs1 : 0 < Ps1) (hPs2 : 0 < Ps2)
    (hf : 1 + i = P2 / P1 * (1 + r)) (hfs : 1 + is = Ps2 / Ps1 * (1 + r)) :
    1 + i = (P2 / Ps2) / (P1 / Ps1) * (1 + is) := by
  rw [hf, hfs]
  field_simp

/-- **No overshooting, EXACTLY** (T13; O&R p. 678 "the exchange rate jumps immediately to its new
long-run equilibrium"): if both nominal rates equal `δ` (`nominal_rate_exact`) then exact UIP
forces `𝓔₁ = 𝓔₂`, the long-run rate. The book's result is not an artefact of linearisation. -/
theorem no_overshooting_exact {δ P1 P2 Ps1 Ps2 r : ℝ} (hδ : 0 < δ) (hP1 : 0 < P1)
    (hPs1 : 0 < Ps1) (hPs2 : 0 < Ps2) (hf : 1 + δ = P2 / P1 * (1 + r))
    (hfs : 1 + δ = Ps2 / Ps1 * (1 + r)) : P1 / Ps1 = P2 / Ps2 := by
  have h := uip_exact hP1 hPs1 hPs2 hf hfs
  have h1 : (P2 / Ps2) / (P1 / Ps1) = 1 := by
    have : (1 + δ) * ((P2 / Ps2) / (P1 / Ps1) - 1) = 0 := by linarith
    have := (mul_eq_zero.1 this).resolve_left (by linarith)
    linarith
  have hne : P1 / Ps1 ≠ 0 := (div_pos hP1 hPs1).ne'
  field_simp at h1
  field_simp
  linarith

/-! ## The MM schedule (58)–(61) -/

/-- **The MM schedule and no overshooting in the linear model** (O&R (58)–(60), pp. 677–678):
with `m̄ − m̄* = m − m*` (53), `ē = (m − m*) − (c − c*)` ((52) with (57)) and the date-1 money
differential (58) `m − m* − e = c − c* − (ē − e)/δ`, the exchange rate jumps at once to its
long-run level: `e = ē = (m − m*) − (c − c*)` (60). -/
theorem mm_no_overshooting {δ x dc e eb : ℝ} (hδ : 0 < δ) (h58 : x - e = dc - (eb - e) / δ)
    (h59 : eb = x - dc) : e = eb ∧ e = x - dc := by
  have h : (eb - e) * (1 + 1 / δ) = 0 := by
    rw [h59] at h58 ⊢
    field_simp at h58 ⊢
    linarith
  have := (mul_eq_zero.1 h).resolve_right (by positivity)
  constructor <;> linarith

/-- The iterated MM recursion (O&R (39), (61)): with `q = 1/(1+a)`,
`e_t = q^N e_{t+N} + Σ_{j<N} a q^{j+1} (x_{t+j} − k)`. -/
theorem mm_iterate {a k : ℝ} (ha : 0 < a) {x ez : ℕ → ℝ}
    (hrec : ∀ t, x t - ez t = k - (ez (t + 1) - ez t) / a) (t N : ℕ) :
    ez t = (1 + a)⁻¹ ^ N * ez (t + N) +
      ∑ j ∈ Finset.range N, a * (1 + a)⁻¹ ^ (j + 1) * (x (t + j) - k) := by
  have hstep : ∀ s, ez s = (1 + a)⁻¹ * ez (s + 1) + a * (1 + a)⁻¹ * (x s - k) := by
    intro s
    have h := hrec s
    have : (1 + a) ≠ 0 := by linarith
    field_simp at h ⊢
    linarith
  induction N with
  | zero => simp
  | succ N ih =>
    rw [ih, Finset.sum_range_succ, hstep (t + N), show t + (N + 1) = t + N + 1 by ring]
    ring

/-- **The forward solution (61) is the ONLY no-bubble solution** (O&R p. 678; T13): if
`x_t − e_t = k − (e_{t+1} − e_t)/a` for all `t` (eq. (39) with `x = m − m*`, `k = c − c*`
constant by (57), `a = δ`), the no-bubble condition `(1+a)^{−T} e_T → 0` holds and
`Σ (1+a)^{−s} |x_s| < ∞`, then `e_t = −k + (a/(1+a)) Σ_{j≥0} (1+a)^{−j} x_{t+j}`. -/
theorem forward_solution_unique {a k : ℝ} (ha : 0 < a) {x ez : ℕ → ℝ}
    (hrec : ∀ t, x t - ez t = k - (ez (t + 1) - ez t) / a)
    (hnb : Tendsto (fun T => (1 + a)⁻¹ ^ T * ez T) atTop (𝓝 0))
    (hx : Summable (fun s => (1 + a)⁻¹ ^ s * x s)) (t : ℕ) :
    ez t = -k + a / (1 + a) * ∑' j, (1 + a)⁻¹ ^ j * x (t + j) := by
  set q := (1 + a)⁻¹ with hq
  have hq0 : 0 < q := inv_pos.2 (by linarith)
  have hq1 : q < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hqa : q * (1 + a) = 1 := inv_mul_cancel₀ (by linarith)
  -- the shifted discounted sequence is summable
  have hxs : Summable (fun j => q ^ j * x (t + j)) := by
    have h1 := (summable_nat_add_iff t).2 hx
    have h2 := h1.mul_left ((1 + a) ^ t)
    refine h2.congr fun j => ?_
    simp only [hq]
    rw [add_comm j t, pow_add]
    have : (1 + a) ^ t * (1 + a)⁻¹ ^ t = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ (by linarith), one_pow]
    linear_combination (1 + a)⁻¹ ^ j * x (t + j) * this
  have hgeo : Summable (fun j : ℕ => q ^ j) := summable_geometric_of_lt_one hq0.le hq1
  -- the bubble term vanishes
  have hb : Tendsto (fun N => q ^ N * ez (t + N)) atTop (𝓝 0) := by
    have h1 := (tendsto_add_atTop_iff_nat t).2 hnb
    have h2 := h1.const_mul ((1 + a) ^ t)
    rw [mul_zero] at h2
    refine h2.congr fun N => ?_
    simp only [hq]
    rw [add_comm N t, pow_add]
    have : (1 + a) ^ t * (1 + a)⁻¹ ^ t = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ (by linarith), one_pow]
    linear_combination (1 + a)⁻¹ ^ N * ez (t + N) * this
  -- the finite sums converge
  have hs : Tendsto (fun N => ∑ j ∈ Finset.range N, a * q ^ (j + 1) * (x (t + j) - k)) atTop
      (𝓝 (a * q * ∑' j, q ^ j * x (t + j) - a * q * k * ∑' j : ℕ, q ^ j)) := by
    have h1 := (hxs.hasSum.mul_left (a * q)).tendsto_sum_nat
    have h2 := (hgeo.hasSum.mul_left (a * q * k)).tendsto_sum_nat
    refine (h1.sub h2).congr fun N => ?_
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hlim := hb.add hs
  rw [zero_add] at hlim
  have hconst : Tendsto (fun N => (1 + a)⁻¹ ^ N * ez (t + N) +
      ∑ j ∈ Finset.range N, a * (1 + a)⁻¹ ^ (j + 1) * (x (t + j) - k)) atTop (𝓝 (ez t)) := by
    refine tendsto_const_nhds.congr fun N => ?_
    exact mm_iterate ha hrec t N
  have heq := tendsto_nhds_unique hconst hlim
  rw [heq, tsum_geometric_of_lt_one hq0.le hq1]
  have e1 : a * q * k * (1 - q)⁻¹ = k := by
    have : 1 - q = a * q := by linarith
    rw [this]
    field_simp
  have e2 : a * q = a / (1 + a) := by rw [hq, div_eq_mul_inv]
  rw [e1, e2]
  ring

/-- **The forward solution (61) solves the MM recursion and has no bubble** (O&R p. 678; T13,
existence): `e_t = −k + (a/(1+a)) Σ_{j≥0} (1+a)^{−j} x_{t+j}` satisfies (39) at every date and
`(1+a)^{−T} e_T → 0`. -/
theorem forward_solution_exists {a k : ℝ} (ha : 0 < a) {x : ℕ → ℝ}
    (hx : Summable (fun s => (1 + a)⁻¹ ^ s * x s)) :
    let ez : ℕ → ℝ := fun t => -k + a / (1 + a) * ∑' j, (1 + a)⁻¹ ^ j * x (t + j)
    (∀ t, x t - ez t = k - (ez (t + 1) - ez t) / a) ∧
      Tendsto (fun T => (1 + a)⁻¹ ^ T * ez T) atTop (𝓝 0) := by
  intro ez
  set q := (1 + a)⁻¹ with hq
  have hq0 : 0 < q := inv_pos.2 (by linarith)
  have hq1 : q < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hqa : q * (1 + a) = 1 := inv_mul_cancel₀ (by linarith)
  have hxs : ∀ t, Summable (fun j => q ^ j * x (t + j)) := by
    intro t
    have h1 := (summable_nat_add_iff t).2 hx
    have h2 := h1.mul_left ((1 + a) ^ t)
    refine h2.congr fun j => ?_
    simp only [hq]
    rw [add_comm j t, pow_add]
    have : (1 + a) ^ t * (1 + a)⁻¹ ^ t = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ (by linarith), one_pow]
    linear_combination (1 + a)⁻¹ ^ j * x (t + j) * this
  -- the one-step split of the tail sums
  have hsplit : ∀ t, ∑' j, q ^ j * x (t + j) = x t + q * ∑' j, q ^ j * x (t + 1 + j) := by
    intro t
    rw [(hxs t).tsum_eq_zero_add]
    simp only [pow_zero, one_mul, add_zero]
    congr 1
    rw [← tsum_mul_left]
    refine tsum_congr fun j => ?_
    rw [pow_succ, show t + (j + 1) = t + 1 + j by ring]
    ring
  refine ⟨fun t => ?_, ?_⟩
  · simp only [ez]
    rw [hsplit t]
    have : (1 + a) ≠ 0 := by linarith
    have hq' : q = 1 / (1 + a) := by rw [hq, one_div]
    rw [hq']
    field_simp
    ring
  · -- `q^T e_T = −k q^T + (a/(1+a)) Σ_j q^{T+j} x_{T+j}`, a tail of a convergent series
    have htail : Tendsto (fun T : ℕ => ∑' j : ℕ, q ^ (j + T) * x (j + T)) atTop (𝓝 0) :=
      tendsto_sum_nat_add (fun s => q ^ s * x s)
    have hgeo : Tendsto (fun T : ℕ => q ^ T) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hq0.le hq1
    have h := (hgeo.const_mul (-k)).add (htail.const_mul (a / (1 + a)))
    rw [mul_zero, mul_zero, add_zero] at h
    refine h.congr fun T => ?_
    simp only [ez]
    have e : ∑' j : ℕ, q ^ (j + T) * x (j + T) = q ^ T * ∑' j, q ^ j * x (T + j) := by
      rw [← tsum_mul_left]
      refine tsum_congr fun j => ?_
      rw [pow_add, add_comm j T]
      ring
    rw [e]
    ring

/-- **(60) as a special case of (61)**: for a permanent differential `x_t = m − m*` for all `t`,
the forward solution is `e_t = (m − m*) − (c − c*)` at every date (O&R p. 678). -/
theorem forward_solution_const {a k X : ℝ} (ha : 0 < a) :
    -k + a / (1 + a) * ∑' j : ℕ, (1 + a)⁻¹ ^ j * X = X - k := by
  have hq0 : 0 < (1 + a)⁻¹ := inv_pos.2 (by linarith)
  have hq1 : (1 + a)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  rw [tsum_mul_right, tsum_geometric_of_lt_one hq0.le hq1]
  have : (1 + a) ≠ 0 := by linarith
  have : 1 - (1 + a)⁻¹ = a / (1 + a) := by field_simp; ring
  rw [this]
  field_simp
  ring

/-! ## The GG schedule (62)–(64) -/

/-- **The GG schedule (64)**, O&R p. 679 (T14): from the short-run current accounts (62)
`b̄/(1−n) = (y − y*) − (c − c*) − e`, the output differential (63) `y − y* = θe`, the long-run
consumption differential (45) and (57), `e = [δ(1+θ) + 2θ](c − c*)/(δ(θ² − 1))`. -/
theorem gg_schedule {θ δ n y ys c cs e b cb cbs : ℝ} (hθ : 1 < θ) (hδ : 0 < δ) (hn1 : n < 1)
    (h63 : y - ys = θ * e) (h62 : b / (1 - n) = (y - ys) - (c - cs) - e)
    (h45 : cb - cbs = (1 + θ) * δ * b / (2 * θ * (1 - n))) (h57 : cb - cbs = c - cs) :
    e = (δ * (1 + θ) + 2 * θ) * (c - cs) / (δ * (θ ^ 2 - 1)) := by
  have hn : 1 - n ≠ 0 := by linarith
  have hθ0 : θ ≠ 0 := by linarith
  have hsq : θ ^ 2 - 1 ≠ 0 := by nlinarith
  have hb : b / (1 - n) = 2 * θ * (c - cs) / ((1 + θ) * δ) := by
    rw [← h57, h45]; field_simp
  rw [hb, h63] at h62
  have h1 : (1 + θ) * δ ≠ 0 := by positivity
  field_simp at h62 ⊢
  nlinarith [h62]

/-! ## The full money-shock system and its unique solution (65)–(74) (T14, T15) -/

/-- The short-run (date 1) unknowns of O&R §10.1.7 (pp. 675–683): `c, c*, y, y*, p, p*, e`,
world consumption `cᵂ`, the real interest rate `r` (between dates 1 and 2, in `dr/r̄` units) and
the current account `b̄` (which becomes the long-run net foreign asset position). -/
structure ShortVars where
  c : ℝ
  cs : ℝ
  y : ℝ
  ys : ℝ
  p : ℝ
  ps : ℝ
  e : ℝ
  cW : ℝ
  r : ℝ
  b : ℝ

/-- **The money-shock system**, O&R pp. 675–683: preset `p(h) = p*(f) = 0` in (27)–(28), world
demand (30)–(31), (32), the Euler equations (35)–(36) linking date 1 to the long run, the date-1
money demands (37)–(38) with date-2 prices at their long-run values, the current account (55),
and the long-run system (`SteadyLinear`) at `b̄` with a permanent shock `m̄ = m`, `m̄* = m*`
(53). The labour–leisure conditions (33)–(34) do not bind in the short run (p. 675). -/
structure MoneyShockEqm (L : ReduxLinear) (m ms : ℝ) (u : ShortVars) (v : SteadyVars) : Prop where
  eq27 : u.p = L.n * 0 + (1 - L.n) * (u.e + 0)
  eq28 : u.ps = L.n * (0 - u.e) + (1 - L.n) * 0
  eq30 : u.y = L.θ * (u.p - 0) + u.cW
  eq31 : u.ys = L.θ * (u.ps - 0) + u.cW
  eq32 : u.cW = L.n * u.c + (1 - L.n) * u.cs
  eq35 : v.c = u.c + L.δ / (1 + L.δ) * u.r
  eq36 : v.cs = u.cs + L.δ / (1 + L.δ) * u.r
  eq37 : m - u.p = u.c - u.r / (1 + L.δ) - (v.p - u.p) / L.δ
  eq38 : ms - u.ps = u.cs - u.r / (1 + L.δ) - (v.ps - u.ps) / L.δ
  eq55 : u.b = u.y - u.c - (1 - L.n) * u.e
  longrun : SteadyLinear L u.b m ms v

/-- The closed-form short-run solution, O&R (65)–(67), (70)–(74), pp. 681–683, with
`mᵂ = n m + (1−n) m*`. -/
noncomputable def shortRunSolution (L : ReduxLinear) (m ms : ℝ) : ShortVars where
  e := (L.δ * (1 + L.θ) + 2 * L.θ) * (m - ms) / L.D
  c := L.n * m + (1 - L.n) * ms + (1 - L.n) * (L.δ * (L.θ ^ 2 - 1) * (m - ms) / L.D)
  cs := L.n * m + (1 - L.n) * ms - L.n * (L.δ * (L.θ ^ 2 - 1) * (m - ms) / L.D)
  y := L.n * m + (1 - L.n) * ms +
    (1 - L.n) * L.θ * ((L.δ * (1 + L.θ) + 2 * L.θ) * (m - ms) / L.D)
  ys := L.n * m + (1 - L.n) * ms - L.n * L.θ * ((L.δ * (1 + L.θ) + 2 * L.θ) * (m - ms) / L.D)
  p := (1 - L.n) * ((L.δ * (1 + L.θ) + 2 * L.θ) * (m - ms) / L.D)
  ps := -(L.n * ((L.δ * (1 + L.θ) + 2 * L.θ) * (m - ms) / L.D))
  cW := L.n * m + (1 - L.n) * ms
  r := -((1 + L.δ) / L.δ) * (L.n * m + (1 - L.n) * ms)
  b := 2 * (1 - L.n) * (L.θ - 1) * (m - ms) / L.E

/-- The key short-run relations of any solution (used for `moneyShock_iff`): `m − p = c`,
`m* − p* = c*` (the MM relations with `î = 0`), `cᵂ = −δr/(1+δ)` (70) and the long-run
consumption differential (45) with (57). -/
theorem MoneyShockEqm.relations {L : ReduxLinear} {m ms : ℝ} {u : ShortVars}
    {v : SteadyVars} (h : MoneyShockEqm L m ms u v) :
    m - u.p = u.c ∧ ms - u.ps = u.cs ∧ u.cW = -(L.δ / (1 + L.δ) * u.r) ∧
      u.c - u.cs = (1 + L.θ) * L.δ * u.b / (2 * L.θ * (1 - L.n)) := by
  have hδ := L.hδ
  have hδ1 : (1 + L.δ) ≠ 0 := by linarith
  obtain ⟨hdiff, -, -, hcW, -⟩ := steadyLinear_consequences h.longrun
  have h50 := h.longrun.eq50
  have h51 := h.longrun.eq51
  have h35 := h.eq35
  have h36 := h.eq36
  have hmp : m - u.p = u.c := by
    have h37 := h.eq37
    rw [h50, h35] at h37
    have : (m - u.p - u.c) * (1 + 1 / L.δ) = 0 := by
      have e : (m - u.p - u.c) * (1 + 1 / L.δ) = (m - u.p) - (u.c - u.r / (1 + L.δ) -
          (m - (u.c + L.δ / (1 + L.δ) * u.r) - u.p) / L.δ) := by field_simp; ring
      rw [e]; linarith
    have := (mul_eq_zero.1 this).resolve_right (by positivity)
    linarith
  have hmps : ms - u.ps = u.cs := by
    have h38 := h.eq38
    rw [h51, h36] at h38
    have : (ms - u.ps - u.cs) * (1 + 1 / L.δ) = 0 := by
      have e : (ms - u.ps - u.cs) * (1 + 1 / L.δ) = (ms - u.ps) - (u.cs - u.r / (1 + L.δ) -
          (ms - (u.cs + L.δ / (1 + L.δ) * u.r) - u.ps) / L.δ) := by field_simp; ring
      rw [e]; linarith
    have := (mul_eq_zero.1 this).resolve_right (by positivity)
    linarith
  refine ⟨hmp, hmps, ?_, ?_⟩
  · have hw : L.n * v.c + (1 - L.n) * v.cs = 0 := by
      rw [← h.longrun.eq32]; exact hcW
    rw [h35, h36] at hw
    rw [h.eq32]
    linarith
  · rw [← hdiff, h35, h36]
    ring

/-- **The money-shock system has exactly one solution** (T14, T15; O&R (60)–(74), pp. 678–683):
`MoneyShockEqm` holds IF AND ONLY IF the short-run variables are `shortRunSolution` and the
long-run variables are `steadySolution` at the implied `b̄`. -/
theorem moneyShock_iff (L : ReduxLinear) (m ms : ℝ) (u : ShortVars) (v : SteadyVars) :
    MoneyShockEqm L m ms u v ↔
      u = shortRunSolution L m ms ∧ v = steadySolution L (shortRunSolution L m ms).b m ms := by
  have hθ := L.hθ
  have hθ0 : L.θ ≠ 0 := by linarith
  have hδ := L.hδ
  have hn1 : 1 - L.n ≠ 0 := by linarith [L.hn1]
  have hD := L.D_pos.ne'
  have hE := L.E_pos.ne'
  have hδ1 : (1 + L.δ) ≠ 0 := by linarith
  constructor
  · intro h
    obtain ⟨hmp, hmps, hcW, hdc⟩ := h.relations
    have h27 := h.eq27
    have h28 := h.eq28
    have h30 := h.eq30
    have h31 := h.eq31
    have h32 := h.eq32
    have h55 := h.eq55
    have hv := (steadyLinear_iff L u.b m ms v).1 h.longrun
    rcases u with ⟨c, cs, y, ys, p, ps, e, cW, r, b⟩
    simp only at hmp hmps hcW hdc h27 h28 h30 h31 h32 h55 hv ⊢
    have hp : p = (1 - L.n) * e := by linarith
    have hps : ps = -(L.n * e) := by linarith
    -- world aggregates (72)–(73)
    have hcW' : cW = L.n * m + (1 - L.n) * ms := by
      rw [h32]; rw [hp] at hmp; rw [hps] at hmps; linear_combination -L.n * hmp - (1 - L.n) * hmps
    have hr : r = -((1 + L.δ) / L.δ) * (L.n * m + (1 - L.n) * ms) := by
      rw [hcW'] at hcW
      field_simp at hcW ⊢
      linarith
    -- MM (60) and GG (64)
    have hMM : e = (m - ms) - (c - cs) := by rw [hp] at hmp; rw [hps] at hmps; linarith
    have hca : b = (1 - L.n) * ((L.θ - 1) * e - (c - cs)) := by
      linear_combination h55 + h30 + L.θ * hp + h32
    have hdc' : c - cs = L.δ * (L.θ ^ 2 - 1) * (m - ms) / L.D := by
      rw [hca, hMM] at hdc
      have key : (c - cs) * L.D = L.δ * (L.θ ^ 2 - 1) * (m - ms) := by
        unfold ReduxLinear.D
        field_simp at hdc
        linear_combination hdc
      field_simp
      linarith
    have he : e = (L.δ * (1 + L.θ) + 2 * L.θ) * (m - ms) / L.D := by
      rw [hMM, hdc']
      unfold ReduxLinear.D
      field_simp
      ring
    have hb : b = 2 * (1 - L.n) * (L.θ - 1) * (m - ms) / L.E := by
      rw [hca, he, hdc']
      unfold ReduxLinear.D ReduxLinear.E
      field_simp
      ring
    have hc : c = L.n * m + (1 - L.n) * ms +
        (1 - L.n) * (L.δ * (L.θ ^ 2 - 1) * (m - ms) / L.D) := by
      rw [← hcW', ← hdc', h32]; ring
    have hcs : cs = L.n * m + (1 - L.n) * ms - L.n * (L.δ * (L.θ ^ 2 - 1) * (m - ms) / L.D) := by
      rw [← hcW', ← hdc', h32]; ring
    refine ⟨?_, ?_⟩
    · simp only [shortRunSolution, ShortVars.mk.injEq]
      refine ⟨hc, hcs, ?_, ?_, ?_, ?_, he, hcW', hr, hb⟩
      · rw [h30, hp, hcW', he]; ring
      · rw [h31, hps, hcW', he]; ring
      · rw [hp, he]
      · rw [hps, he]
    · rw [hv, hb]; rfl
  · rintro ⟨rfl, rfl⟩
    have hE' : L.δ * (1 + L.θ) + 2 ≠ 0 := L.E_pos.ne'
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, (steadyLinear_iff L _ m ms _).2 rfl⟩ <;>
      simp only [steadySolution, shortRunSolution, ReduxLinear.D, ReduxLinear.E] <;>
      field_simp <;> ring

/-- **Existence and uniqueness of the money-shock equilibrium** (T14): for every `m, m*`. -/
theorem moneyShock_existsUnique (L : ReduxLinear) (m ms : ℝ) :
    ∃! w : ShortVars × SteadyVars, MoneyShockEqm L m ms w.1 w.2 := by
  refine ⟨(shortRunSolution L m ms, steadySolution L (shortRunSolution L m ms).b m ms),
    (moneyShock_iff L m ms _ _).2 ⟨rfl, rfl⟩, fun w hw => ?_⟩
  obtain ⟨h1, h2⟩ := (moneyShock_iff L m ms w.1 w.2).1 hw
  exact Prod.ext h1 h2

/-- **The closed forms (65)–(68)**, O&R p. 681 (T14): any solution has
`e = [δ(1+θ)+2θ](m−m*)/(θδ(1+θ)+2θ)` (65), `c − c* = δ(θ²−1)(m−m*)/(θδ(1+θ)+2θ)` (66),
`b̄ = 2(1−n)(θ−1)(m−m*)/(δ(1+θ)+2)` (67), `p̄(h) − ē − p̄*(f) = δ(θ−1)(m−m*)/(θδ(1+θ)+2θ)` (68),
and the exchange rate jumps to its long-run level, `e = ē` (60). -/
theorem moneyShock_closed_forms {L : ReduxLinear} {m ms : ℝ} {u : ShortVars} {v : SteadyVars}
    (h : MoneyShockEqm L m ms u v) :
    u.e = (L.δ * (1 + L.θ) + 2 * L.θ) * (m - ms) / L.D ∧
    u.c - u.cs = L.δ * (L.θ ^ 2 - 1) * (m - ms) / L.D ∧
    u.b = 2 * (1 - L.n) * (L.θ - 1) * (m - ms) / L.E ∧
    v.ph - v.e - v.pf = L.δ * (L.θ - 1) * (m - ms) / L.D ∧ u.e = v.e := by
  obtain ⟨rfl, rfl⟩ := (moneyShock_iff L m ms u v).1 h
  have hθ0 : L.θ ≠ 0 := by linarith [L.hθ]
  have hn1 : 1 - L.n ≠ 0 := by linarith [L.hn1]
  have hE' : L.δ * (1 + L.θ) + 2 ≠ 0 := L.E_pos.ne'
  simp only [steadySolution, shortRunSolution, ReduxLinear.D, ReduxLinear.E]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> (try trivial) <;> field_simp <;> ring

/-- **World aggregates (69)–(74)**, O&R pp. 682–683 (T15): `cᵂ = −δr/(1+δ)` (70),
`cᵂ = mᵂ = yᵂ` (72), `r = −((1+δ)/δ)mᵂ` (73), `y = mᵂ + (1−n)θe`, and (74)
`y = [δ(1+θ) + 2(n(1−θ)+θ)]m/(δ(1+θ)+2) + 2(1−n)(1−θ)m*/(δ(1+θ)+2)`. -/
theorem moneyShock_world {L : ReduxLinear} {m ms : ℝ} {u : ShortVars} {v : SteadyVars}
    (h : MoneyShockEqm L m ms u v) :
    u.cW = -(L.δ / (1 + L.δ) * u.r) ∧ u.cW = L.n * m + (1 - L.n) * ms ∧
    L.n * u.y + (1 - L.n) * u.ys = u.cW ∧
    u.r = -((1 + L.δ) / L.δ) * (L.n * m + (1 - L.n) * ms) ∧
    u.y = L.n * m + (1 - L.n) * ms + (1 - L.n) * L.θ * u.e ∧
    u.y = (L.δ * (1 + L.θ) + 2 * (L.n * (1 - L.θ) + L.θ)) / L.E * m +
      2 * (1 - L.n) * (1 - L.θ) / L.E * ms := by
  have hcW := h.relations.2.2.1
  obtain ⟨rfl, rfl⟩ := (moneyShock_iff L m ms u v).1 h
  have hθ0 : L.θ ≠ 0 := by linarith [L.hθ]
  have hE' : L.δ * (1 + L.θ) + 2 ≠ 0 := L.E_pos.ne'
  refine ⟨hcW, rfl, ?_, rfl, ?_, ?_⟩ <;>
    simp only [shortRunSolution, ReduxLinear.D, ReduxLinear.E] <;> field_simp <;> ring

/-- **(74): a Foreign monetary expansion lowers Home output**, O&R p. 683: the coefficient on
`m*` in (74) is `2(1−n)(1−θ)/(δ(1+θ)+2) < 0` for `θ > 1`. -/
theorem foreign_money_lowers_home_output (L : ReduxLinear) :
    2 * (1 - L.n) * (1 - L.θ) / L.E < 0 := by
  have := L.E_pos
  have h1 : 0 < 1 - L.n := by linarith [L.hn1]
  have h2 : 1 - L.θ < 0 := by linarith [L.hθ]
  apply div_neg_of_neg_of_pos _ this
  nlinarith

/-! ## Comparative statics (T14), the (65) sign condition and country size (p. 688) -/

/-- The exchange-rate response per unit of relative money, `e/(m − m*)` in (65), O&R p. 681. -/
noncomputable def exchangeRateCoef (θ δ : ℝ) : ℝ :=
  (δ * (1 + θ) + 2 * θ) / (θ * (δ * (1 + θ) + 2))

/-- **At `θ = 1` the exchange rate moves one-for-one** (O&R p. 681). -/
theorem exchangeRateCoef_one {δ : ℝ} (hδ : 0 < δ) : exchangeRateCoef 1 δ = 1 := by
  unfold exchangeRateCoef
  have : δ * (1 + 1) + 2 ≠ 0 := by positivity
  field_simp

/-- **(65): the currency depreciates less than proportionally**, O&R p. 681 (T14): for `θ > 1`,
`0 < e/(m − m*) < 1`. -/
theorem exchangeRateCoef_mem {θ δ : ℝ} (hθ : 1 < θ) (hδ : 0 < δ) :
    0 < exchangeRateCoef θ δ ∧ exchangeRateCoef θ δ < 1 := by
  unfold exchangeRateCoef
  have hden : 0 < θ * (δ * (1 + θ) + 2) := by
    have : 0 < θ := by linarith
    positivity
  constructor
  · exact div_pos (by nlinarith) hden
  · rw [div_lt_one hden]
    have : 0 < (θ - 1) * (δ * (1 + θ)) := mul_pos (by linarith) (by positivity)
    nlinarith

/-- **The exchange-rate response falls as goods become closer substitutes**, O&R p. 680 (T14):
`e/(m − m*)` is strictly decreasing in `θ > 0`. -/
theorem exchangeRateCoef_strictAntiOn {δ : ℝ} (hδ : 0 < δ) :
    StrictAntiOn (fun θ => exchangeRateCoef θ δ) (Set.Ioi 0) := by
  intro a ha b hb hab
  simp only [exchangeRateCoef]
  have ha0 : (0 : ℝ) < a := ha
  have hb0 : (0 : ℝ) < b := hb
  have hda : 0 < a * (δ * (1 + a) + 2) := by positivity
  have hdb : 0 < b * (δ * (1 + b) + 2) := by positivity
  rw [div_lt_div_iff₀ hdb hda]
  have key : (δ * (1 + a) + 2 * a) * (b * (δ * (1 + b) + 2)) -
      (δ * (1 + b) + 2 * b) * (a * (δ * (1 + a) + 2)) =
      (b - a) * (δ ^ 2 * (a + b) + δ * (δ + 2) + (δ + 2) * δ * a * b) := by ring
  have hpos : 0 < (b - a) * (δ ^ 2 * (a + b) + δ * (δ + 2) + (δ + 2) * δ * a * b) := by
    apply mul_pos (by linarith); positivity
  linarith

/-- **As `θ → ∞` the exchange-rate response vanishes**, O&R p. 680 (T14). -/
theorem exchangeRateCoef_tendsto {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun θ => exchangeRateCoef θ δ) atTop (𝓝 0) := by
  have h1 : Tendsto (fun θ : ℝ => δ * θ⁻¹ + (δ + 2)) atTop (𝓝 (δ * 0 + (δ + 2))) :=
    (tendsto_inv_atTop_zero.const_mul δ).add_const _
  have h2 : Tendsto (fun θ : ℝ => (δ * (1 + θ) + 2)⁻¹) atTop (𝓝 0) := by
    apply tendsto_inv_atTop_zero.comp
    exact tendsto_atTop_add_const_right _ _ ((tendsto_id.const_mul_atTop hδ).atTop_add
      tendsto_const_nhds |>.congr (fun θ => by simp; ring))
  have h := h1.mul h2
  rw [mul_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_gt_atTop 0] with θ hθ
  unfold exchangeRateCoef
  have : δ * (1 + θ) + 2 ≠ 0 := by positivity
  field_simp
  ring

/-- **The GG schedule becomes horizontal as `θ → ∞`**, O&R p. 680 (T14): its slope
`[δ(1+θ)+2θ]/(δ(θ²−1))` tends to `0`. -/
theorem gg_slope_tendsto {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun θ : ℝ => (δ * (1 + θ) + 2 * θ) / (δ * (θ ^ 2 - 1))) atTop (𝓝 0) := by
  have hinv : Tendsto (fun θ : ℝ => θ⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hup : Tendsto (fun θ : ℝ => 4 / (3 * δ) * (δ * θ⁻¹ * θ⁻¹ + (δ + 2) * θ⁻¹)) atTop
      (𝓝 (4 / (3 * δ) * (δ * 0 * 0 + (δ + 2) * 0))) :=
    (((hinv.const_mul δ).mul hinv).add (hinv.const_mul (δ + 2))).const_mul _
  simp only [mul_zero, add_zero] at hup
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [eventually_gt_atTop 2] with θ hθ
    have hθ0 : 0 < θ := by linarith
    have hsq : 0 < θ ^ 2 - 1 := by nlinarith
    exact div_nonneg (by positivity) (mul_pos hδ hsq).le
  · filter_upwards [eventually_gt_atTop 2] with θ hθ
    have hθ0 : 0 < θ := by linarith
    have hsq : 0 < θ ^ 2 - 1 := by nlinarith
    have hden : 0 < δ * (θ ^ 2 - 1) := mul_pos hδ hsq
    rw [div_le_iff₀ hden]
    have e : 4 / (3 * δ) * (δ * θ⁻¹ * θ⁻¹ + (δ + 2) * θ⁻¹) * (δ * (θ ^ 2 - 1)) =
        4 / 3 * (δ + (δ + 2) * θ) * (θ ^ 2 - 1) / θ ^ 2 := by field_simp
    rw [e, le_div_iff₀ (by positivity)]
    have hN : 0 < δ + (δ + 2) * θ := by positivity
    have h4 : 0 < θ ^ 2 - 4 := by nlinarith
    have e2 : δ * (1 + θ) + 2 * θ = δ + (δ + 2) * θ := by ring
    rw [e2]
    nlinarith [mul_pos hN h4]

/-- **(65) corrected: the sign condition** (O&R p. 681 writes `e < m − m*` "because `θ > 1`"; this
needs `m − m* > 0`): for `θ > 1`, with `e` given by (65), `e < m − m* ⟺ m − m* > 0`, and
`|e| < |m − m*|` whenever `m ≠ m*`. -/
theorem eq65_sign {θ δ X : ℝ} (hθ : 1 < θ) (hδ : 0 < δ) :
    (exchangeRateCoef θ δ * X < X ↔ 0 < X) ∧ (X ≠ 0 → |exchangeRateCoef θ δ * X| < |X|) := by
  obtain ⟨h0, h1⟩ := exchangeRateCoef_mem hθ hδ
  refine ⟨⟨fun h => by nlinarith, fun h => by nlinarith⟩, fun hX => ?_⟩
  rw [abs_mul, abs_of_pos h0]
  have := abs_pos.2 hX
  nlinarith

/-- **The short-run terms-of-trade effect dominates**, O&R p. 682 (T14): the long-run effect (68)
is `δ(θ−1)/(δ(1+θ)+2θ)` times the short-run effect `e` (65) in absolute value; this ratio lies in
`[0, 1)` and is below `δ/2`, i.e. of the order of the interest rate. -/
theorem tot_ratio_bounds {θ δ : ℝ} (hθ : 1 ≤ θ) (hδ : 0 < δ) :
    0 ≤ δ * (θ - 1) / (δ * (1 + θ) + 2 * θ) ∧ δ * (θ - 1) / (δ * (1 + θ) + 2 * θ) < 1 ∧
      δ * (θ - 1) / (δ * (1 + θ) + 2 * θ) < δ / 2 := by
  have hden : 0 < δ * (1 + θ) + 2 * θ := by nlinarith
  refine ⟨div_nonneg (by nlinarith) hden.le, by rw [div_lt_one hden]; nlinarith, ?_⟩
  rw [div_lt_iff₀ hden]
  nlinarith [mul_pos hδ (show 0 < δ * (1 + θ) + 2 by positivity)]

/-- **The larger the country, the smaller the current-account effect** (O&R p. 681): for
`m > m*` and `θ > 1`, `b̄ = 2(1−n)(θ−1)(m−m*)/(δ(1+θ)+2)` is strictly decreasing in `n`. -/
theorem ca_strictAnti_in_n {θ δ X : ℝ} (hθ : 1 < θ) (hδ : 0 < δ) (hX : 0 < X) :
    StrictAnti (fun n : ℝ => 2 * (1 - n) * (θ - 1) * X / (δ * (1 + θ) + 2)) := by
  intro a b hab
  have hE : 0 < δ * (1 + θ) + 2 := by positivity
  apply div_lt_div_of_pos_right _ hE
  have : 0 < (θ - 1) * X := mul_pos (by linarith) hX
  nlinarith

/-- **p. 688 corrected** (T14/T22): contrary to "country size `n` did not enter into the results
… for … the current account", the current account (67) depends on `n` (`ca_strictAnti_in_n`);
the size-free object is the per-capita differential `b̄ − b̄* = b̄/(1−n) = 2(θ−1)(m−m*)/E`. The
exchange rate (65), relative consumption (66) and the terms of trade (68) are indeed
independent of `n`: they coincide for any two size parameters. -/
theorem country_size_correction (L L' : ReduxLinear) (hθ : L.θ = L'.θ) (hδ : L.δ = L'.δ)
    (m ms : ℝ) :
    (shortRunSolution L m ms).e = (shortRunSolution L' m ms).e ∧
    (shortRunSolution L m ms).c - (shortRunSolution L m ms).cs =
      (shortRunSolution L' m ms).c - (shortRunSolution L' m ms).cs ∧
    (shortRunSolution L m ms).b / (1 - L.n) = (shortRunSolution L' m ms).b / (1 - L'.n) ∧
    (L.n ≠ L'.n → m ≠ ms → (shortRunSolution L m ms).b ≠ (shortRunSolution L' m ms).b) := by
  have hn1 : 1 - L.n ≠ 0 := by linarith [L.hn1]
  have hn1' : 1 - L'.n ≠ 0 := by linarith [L'.hn1]
  have hE : L.E = L'.E := by unfold ReduxLinear.E; rw [hθ, hδ]
  have hD : L.D = L'.D := by unfold ReduxLinear.D; rw [hθ, hδ]
  have hE0 := L.E_pos.ne'
  refine ⟨by simp only [shortRunSolution]; rw [hθ, hδ, hD], ?_, ?_, fun hn hm => ?_⟩
  · simp only [shortRunSolution]; rw [hθ, hδ, hD]; ring
  · simp only [shortRunSolution]; rw [hθ, hE]; field_simp
  · intro heq
    have hdiff : (shortRunSolution L m ms).b - (shortRunSolution L' m ms).b =
        2 * (L'.θ - 1) * (m - ms) * (L'.n - L.n) / L'.E := by
      simp only [shortRunSolution]; rw [hθ, hE]; ring
    rw [heq, sub_self] at hdiff
    have hE0' := L'.E_pos.ne'
    have hθ1 : L'.θ - 1 ≠ 0 := by linarith [L'.hθ]
    have hX : m - ms ≠ 0 := sub_ne_zero.2 hm
    have hnn : L'.n - L.n ≠ 0 := sub_ne_zero.2 (Ne.symm hn)
    have : 2 * (L'.θ - 1) * (m - ms) * (L'.n - L.n) / L'.E ≠ 0 := by positivity
    exact this hdiff.symm

/-! ## The nominal interest rate is unchanged (T15) -/

/-- The log-deviation of the gross nominal rate (O&R p. 665 Fisher relation, T15): along
`P_{t+1}/P_t = e^{τ Δp}` and `r = δ(1 + τ r̂)`, `d log(1 + i) = Δp + δ r̂/(1+δ)` at `τ = 0`. This
is the `î` of `nominal_rate_unchanged`. -/
theorem linearise_nominal_rate {δ dp rh : ℝ} (hδ : 0 < δ) :
    HasDerivAt (fun τ => Real.log (Real.exp (τ * dp) * (1 + δ * (1 + τ * rh))))
      (dp + δ * rh / (1 + δ)) 0 := by
  have h1 : HasDerivAt (fun τ => 1 + δ * (1 + τ * rh)) (δ * rh) 0 := by
    have := (((hasDerivAt_id (0 : ℝ)).mul_const rh).const_add 1).const_mul δ
    simpa using this.const_add 1
  have h2 := h1.log (by simp; linarith)
  have e : (fun τ => Real.log (Real.exp (τ * dp) * (1 + δ * (1 + τ * rh)))) =ᶠ[𝓝 0]
      fun τ => τ * dp + Real.log (1 + δ * (1 + τ * rh)) := by
    have hev : ∀ᶠ τ in 𝓝 (0 : ℝ), 0 < 1 + δ * (1 + τ * rh) :=
      h1.continuousAt.eventually (lt_mem_nhds (by simp; linarith))
    filter_upwards [hev] with τ hτ
    rw [Real.log_mul (Real.exp_pos _).ne' hτ.ne', Real.log_exp]
  have h3 := ((hasDerivAt_id (0 : ℝ)).mul_const dp).add h2
  have h4 := h3.congr_of_eventuallyEq e
  convert h4 using 1
  simp

/-- **The nominal interest rate does not change after a permanent shock** (T15; new): in each
country, the Euler equation (35) `c̄ = c + δr/(1+δ)`, date-1 money demand (37) and long-run money
demand `m − p̄ = c̄` ((50) with `m̄ = m`) imply `î = δr/(1+δ) + (p̄ − p) = 0`. The argument uses
nothing about the source of the shock, so it covers p. 699 ("the nominal interest rate doesn't
change") for productivity and government-spending shocks too. -/
theorem nominal_rate_unchanged {δ m p pb c cb r : ℝ} (hδ : 0 < δ)
    (h35 : cb = c + δ / (1 + δ) * r) (h37 : m - p = c - r / (1 + δ) - (pb - p) / δ)
    (h50 : pb = m - cb) : δ * r / (1 + δ) + (pb - p) = 0 := by
  have hδ1 : (1 + δ) ≠ 0 := by linarith
  have key : (δ * r / (1 + δ) + (pb - p)) * (1 + 1 / δ) = 0 := by
    have e : (δ * r / (1 + δ) + (pb - p)) * (1 + 1 / δ) =
        (m - p) - (c - r / (1 + δ) - (pb - p) / δ) + (δ / (1 + δ) * r + c - cb) +
        (pb - (m - cb)) := by field_simp; ring
    rw [e]
    linarith
  have := (mul_eq_zero.1 key).resolve_right (by positivity)
  exact this

/-! ## Temporary money shocks (fn 16, T16) -/

/-- Solving MM (forward form) and GG together: if `e = (x_eff) − (c − c*)` and
`e = G (c − c*)` with `G = [δ(1+θ)+2θ]/(δ(θ²−1))`, then `c − c* = δ(θ²−1) x_eff/D` and
`e = [δ(1+θ)+2θ] x_eff/D` (O&R (65)–(66), fn 16, Ex. 1). -/
theorem solve_mm_gg (L : ReduxLinear) {xe dc e : ℝ} (hmm : e = xe - dc)
    (hgg : e = (L.δ * (1 + L.θ) + 2 * L.θ) * dc / (L.δ * (L.θ ^ 2 - 1))) :
    dc = L.δ * (L.θ ^ 2 - 1) * xe / L.D ∧ e = (L.δ * (1 + L.θ) + 2 * L.θ) * xe / L.D := by
  have hθ := L.hθ
  have hδ := L.hδ
  have hsq : L.δ * (L.θ ^ 2 - 1) ≠ 0 := by
    have : 0 < L.θ ^ 2 - 1 := by nlinarith
    positivity
  have hD := L.D_pos.ne'
  have h2 : (xe - dc) * (L.δ * (L.θ ^ 2 - 1)) = (L.δ * (1 + L.θ) + 2 * L.θ) * dc := by
    rw [hmm] at hgg; rw [hgg]
    have : L.θ ^ 2 - 1 ≠ 0 := by nlinarith
    have := hδ.ne'
    field_simp
  have key : dc * L.D = L.δ * (L.θ ^ 2 - 1) * xe := by
    unfold ReduxLinear.D
    linear_combination -h2
  have hdc : dc = L.δ * (L.θ ^ 2 - 1) * xe / L.D := by field_simp; linarith
  refine ⟨hdc, ?_⟩
  rw [hmm, hdc]
  unfold ReduxLinear.D
  have : L.θ * (L.δ * (1 + L.θ) + 2) ≠ 0 := by
    have : 0 < L.θ := by linarith
    positivity
  field_simp
  ring

/-- **Temporary money shocks** (O&R fn 16, p. 681; T16): with a one-period Home expansion
`m₁ = m`, `m_s = 0` for `s ≥ 2`, `m* ≡ 0`, the forward MM equation (39) with no bubbles and the
unchanged GG schedule give `e₁ = (δ/(1+δ))[δ(1+θ)+2θ]m/D` and
`c − c* = (δ/(1+δ))δ(θ²−1)m/D`: the permanent-shock effects scaled by `δ/(1+δ) < 1`. From date 2
on the exchange rate is `e_t = −(c − c*)`. (Book date `t` is index `t − 1` here.) -/
theorem temporary_shock (L : ReduxLinear) {m dc : ℝ} {x ez : ℕ → ℝ} (hx0 : x 0 = m)
    (hxs : ∀ t, x (t + 1) = 0) (hrec : ∀ t, x t - ez t = dc - (ez (t + 1) - ez t) / L.δ)
    (hnb : Tendsto (fun T => (1 + L.δ)⁻¹ ^ T * ez T) atTop (𝓝 0))
    (hgg : ez 0 = (L.δ * (1 + L.θ) + 2 * L.θ) * dc / (L.δ * (L.θ ^ 2 - 1))) :
    ez 0 = L.δ / (1 + L.δ) * ((L.δ * (1 + L.θ) + 2 * L.θ) * m / L.D) ∧
    dc = L.δ / (1 + L.δ) * (L.δ * (L.θ ^ 2 - 1) * m / L.D) ∧ ∀ t, ez (t + 1) = -dc := by
  have hδ := L.hδ
  have hsum : Summable (fun s => (1 + L.δ)⁻¹ ^ s * x s) := by
    refine summable_of_ne_finset_zero (s := {0}) fun s hs => ?_
    simp only [Finset.mem_singleton] at hs
    obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hs
    rw [hxs t, mul_zero]
  have h0 := forward_solution_unique hδ hrec hnb hsum 0
  have hs0 : ∑' j, (1 + L.δ)⁻¹ ^ j * x (0 + j) = m := by
    rw [tsum_eq_single 0 (fun j hj => by
      obtain ⟨t, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hj
      rw [zero_add, hxs t, mul_zero])]
    simp [hx0]
  rw [hs0] at h0
  have hlater : ∀ t, ez (t + 1) = -dc := by
    intro t
    have h := forward_solution_unique hδ hrec hnb hsum (t + 1)
    have : ∑' j, (1 + L.δ)⁻¹ ^ j * x (t + 1 + j) = 0 := by
      have : ∀ j, (1 + L.δ)⁻¹ ^ j * x (t + 1 + j) = 0 := fun j => by
        rw [show t + 1 + j = (t + j) + 1 by ring, hxs, mul_zero]
      rw [tsum_congr this, tsum_zero]
    rw [this, mul_zero, add_zero] at h
    exact h
  obtain ⟨hdc, he⟩ := solve_mm_gg L (xe := L.δ / (1 + L.δ) * m) (by linarith) hgg
  refine ⟨?_, ?_, hlater⟩
  · rw [he]; ring
  · rw [hdc]; ring

/-- **After a temporary Home expansion the Home currency is PERMANENTLY APPRECIATED** (T16; not
stated in the book): in the setting of `temporary_shock`, for `m > 0` and `θ > 1`, the exchange
rate from date 2 on is `e_t = −(c − c*) < 0`, while on impact it depreciates, `e₁ > 0`. -/
theorem temporary_shock_appreciation (L : ReduxLinear) {m dc : ℝ} {x ez : ℕ → ℝ} (hm : 0 < m)
    (hx0 : x 0 = m) (hxs : ∀ t, x (t + 1) = 0)
    (hrec : ∀ t, x t - ez t = dc - (ez (t + 1) - ez t) / L.δ)
    (hnb : Tendsto (fun T => (1 + L.δ)⁻¹ ^ T * ez T) atTop (𝓝 0))
    (hgg : ez 0 = (L.δ * (1 + L.θ) + 2 * L.θ) * dc / (L.δ * (L.θ ^ 2 - 1))) :
    0 < ez 0 ∧ ∀ t, ez (t + 1) < 0 := by
  obtain ⟨he, hdc, hlater⟩ := temporary_shock L hx0 hxs hrec hnb hgg
  have hδ := L.hδ
  have hθ := L.hθ
  have hD := L.D_pos
  have hsq : 0 < L.θ ^ 2 - 1 := by nlinarith
  refine ⟨by rw [he]; positivity, fun t => ?_⟩
  rw [hlater t]
  have : 0 < dc := by rw [hdc]; positivity
  linarith

/-- The temporary-shock effects are strictly smaller than the permanent ones (O&R fn 16): the
scaling factor `δ/(1+δ)` lies in `(0, 1)`. -/
theorem temporary_scaling_lt_one {δ : ℝ} (hδ : 0 < δ) : 0 < δ / (1 + δ) ∧ δ / (1 + δ) < 1 :=
  ⟨by positivity, by rw [div_lt_one (by linarith)]; linarith⟩

/-! ## Exercise 1: money growth -/

/-- **Ex. 1(a): the steady-state nominal rate with money growth**, O&R p. 713: with steady
inflation `P_{t+1}/P_t = 1 + μ` and `r = δ`, Fisher parity gives `1 + ī = (1+δ)(1+μ)`. -/
theorem ex1_nominal_rate {δ μ i P P1 : ℝ} (hinfl : P1 / P = 1 + μ)
    (hfisher : 1 + i = P1 / P * (1 + δ)) : 1 + i = (1 + δ) * (1 + μ) := by
  rw [hfisher, hinfl]; ring

/-- **Ex. 1(a): (26′)**: steady-state real balances `χȳ₀(1+ī)/ī` FALL as money growth rises
(the real side is superneutral, so only the `(1+ī)/ī` factor moves): for `0 < ī < ī'`,
`χȳ₀(1+ī')/ī' < χȳ₀(1+ī)/ī`. -/
theorem ex1_real_balances_fall {χ y i i' : ℝ} (hχ : 0 < χ) (hy : 0 < y) (hi : 0 < i)
    (hii : i < i') : χ * y * ((1 + i') / i') < χ * y * ((1 + i) / i) := by
  apply mul_lt_mul_of_pos_left _ (by positivity)
  have hi' : 0 < i' := lt_trans hi hii
  rw [div_lt_div_iff₀ hi' hi]
  nlinarith

/-- **Ex. 1(a): (37′)** (T10 with money growth): around a trend with inflation `μ ≥ 0` and
`r = δ`, so `1 + ī = (1+μ)(1+δ)`, the term `log((1+i)/i)` of money demand has derivative
`−Δp/ī − δ r̂/((1+δ) ī)` along `P_{t+1}/P_t = (1+μ)e^{τΔp}`, `r = δ(1 + τ r̂)`. -/
theorem linearise_37_growth {δ μ dp rh : ℝ} (hδ : 0 < δ) (hμ : 0 ≤ μ) :
    HasDerivAt (fun τ => Real.log (((1 + μ) * Real.exp (τ * dp) * (1 + δ * (1 + τ * rh))) /
      ((1 + μ) * Real.exp (τ * dp) * (1 + δ * (1 + τ * rh)) - 1)))
      (-(dp / ((1 + μ) * (1 + δ) - 1)) -
        δ * rh / ((1 + δ) * ((1 + μ) * (1 + δ) - 1))) 0 := by
  set g : ℝ → ℝ := fun τ => (1 + μ) * Real.exp (τ * dp) * (1 + δ * (1 + τ * rh)) with hg
  have hgd : HasDerivAt g ((1 + μ) * (dp * (1 + δ) + δ * rh)) 0 := by
    have h1 := ((hasDerivAt_id (0 : ℝ)).mul_const dp).exp
    have h2 : HasDerivAt (fun τ => 1 + δ * (1 + τ * rh)) (δ * rh) 0 := by
      have := (((hasDerivAt_id (0 : ℝ)).mul_const rh).const_add 1).const_mul δ
      simpa using this.const_add 1
    have h3 := (h1.const_mul (1 + μ)).mul h2
    have e : g = (fun x => (1 + μ) * Real.exp (id x * dp)) * (fun τ => 1 + δ * (1 + τ * rh)) := by
      funext τ; simp [hg]
    rw [e]
    convert h3 using 1
    simp
    ring
  have hg0 : g 0 = (1 + μ) * (1 + δ) := by simp [hg]
  have hi : 0 < (1 + μ) * (1 + δ) - 1 := by nlinarith
  have hnum := hgd.log (by rw [hg0]; positivity)
  have hden := (hgd.sub_const 1).log (by rw [hg0]; linarith)
  have hev : ∀ᶠ τ in 𝓝 (0 : ℝ), 1 < g τ :=
    hgd.continuousAt.eventually (lt_mem_nhds (by rw [hg0]; linarith))
  have hcongr : (fun τ => Real.log (g τ / (g τ - 1))) =ᶠ[𝓝 0]
      fun τ => Real.log (g τ) - Real.log (g τ - 1) := by
    filter_upwards [hev] with τ hτ
    rw [Real.log_div (by linarith) (by linarith)]
  have hfin := (hnum.sub hden).congr_of_eventuallyEq hcongr
  convert hfin using 1
  rw [hg0]
  have : (1 + δ) ≠ 0 := by linarith
  have : (1 + μ) ≠ 0 := by linarith
  have := hi.ne'
  field_simp
  ring

/-- **Ex. 1(a): (39′)**, O&R p. 713: subtracting the growth versions of (37′) and (38′),
`m − p = c − δr/((1+δ)ī) − (p_{t+1} − p_t)/ī` and its Foreign twin, and using PPP (29), gives
`m − m* − e = c − c* − (e_{t+1} − e_t)/ī`: (39) with `δ` replaced by `ī`, so the forward
solution (61′) is `forward_solution_unique` at rate `ī`. -/
theorem eq39_growth {δ i m ms p ps p1 ps1 c cs r e e1 : ℝ}
    (h37 : m - p = c - δ * r / ((1 + δ) * i) - (p1 - p) / i)
    (h38 : ms - ps = cs - δ * r / ((1 + δ) * i) - (ps1 - ps) / i)
    (h29 : e = p - ps) (h29' : e1 = p1 - ps1) :
    m - ms - e = c - cs - (e1 - e) / i := by
  rw [h29, h29']
  have : (p1 - ps1 - (p - ps)) / i = (p1 - p) / i - (ps1 - ps) / i := by ring
  rw [this]
  linarith

/-- The discounted sums behind Ex. 1(b): for `a > 0`,
`(a/(1+a)) Σ_{j≥0} (1+a)^{−j}(1+j) = (1+a)/a` and `(a/(1+a)) Σ_{j≥0} (1+a)^{−j} j = 1/a`. -/
theorem ex1_sums {a : ℝ} (ha : 0 < a) :
    a / (1 + a) * ∑' j : ℕ, (1 + a)⁻¹ ^ j * ((j : ℝ) + 1) = (1 + a) / a ∧
      a / (1 + a) * ∑' j : ℕ, (1 + a)⁻¹ ^ j * (j : ℝ) = 1 / a := by
  set q := (1 + a)⁻¹ with hq
  have hq0 : 0 < q := inv_pos.2 (by linarith)
  have hq1 : q < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hnorm : ‖q‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos hq0]; exact hq1
  have hA : HasSum (fun j : ℕ => (j : ℝ) * q ^ j) (q / (1 - q) ^ 2) :=
    hasSum_coe_mul_geometric_of_norm_lt_one hnorm
  have hB : HasSum (fun j : ℕ => q ^ j) (1 - q)⁻¹ := hasSum_geometric_of_lt_one hq0.le hq1
  have h1q : 1 - q = a / (1 + a) := by rw [hq]; field_simp; ring
  have hA' : ∑' j : ℕ, q ^ j * (j : ℝ) = q / (1 - q) ^ 2 := by
    rw [← hA.tsum_eq]; exact tsum_congr fun j => by ring
  have hAB : ∑' j : ℕ, q ^ j * ((j : ℝ) + 1) = q / (1 - q) ^ 2 + (1 - q)⁻¹ := by
    rw [← hA.tsum_eq, ← hB.tsum_eq, ← hA.summable.tsum_add hB.summable]
    exact tsum_congr fun j => by ring
  have : (1 + a) ≠ 0 := by linarith
  have := ha.ne'
  refine ⟨?_, ?_⟩
  · rw [hAB, h1q, hq]; field_simp
  · rw [hA', h1q, hq]; field_simp

/-- **Ex. 1(b): a permanent rise in Home money growth from date 1**, O&R p. 713. With
`ν = log((1+μ')/(1+μ))` and the new growth applying from date 1 (`m_t = tν`, index `t − 1`
here: `x_t = (t+1)ν`), the forward MM′ equation at rate `ī` gives
`e₁ = ν(1+ī)/ī − (c − c*)`; with the unchanged GG schedule,
`e = [δ(1+θ)+2θ]ν(1+ī)/(ī D) > 0`, `c − c* = δ(θ²−1)ν(1+ī)/(ī D) > 0` for `ν > 0`. -/
theorem ex1_growth_shock (L : ReduxLinear) {i ν dc : ℝ} (hi : 0 < i) {x ez : ℕ → ℝ}
    (hx : ∀ t, x t = ((t : ℝ) + 1) * ν)
    (hrec : ∀ t, x t - ez t = dc - (ez (t + 1) - ez t) / i)
    (hnb : Tendsto (fun T => (1 + i)⁻¹ ^ T * ez T) atTop (𝓝 0))
    (hgg : ez 0 = (L.δ * (1 + L.θ) + 2 * L.θ) * dc / (L.δ * (L.θ ^ 2 - 1))) :
    ez 0 = ν * (1 + i) / i - dc ∧
    dc = L.δ * (L.θ ^ 2 - 1) * (ν * (1 + i) / i) / L.D ∧
    ez 0 = (L.δ * (1 + L.θ) + 2 * L.θ) * (ν * (1 + i) / i) / L.D := by
  have hq0 : 0 < (1 + i)⁻¹ := inv_pos.2 (by linarith)
  have hq1 : (1 + i)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hnorm : ‖(1 + i)⁻¹‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos hq0]; exact hq1
  have hsumA : Summable (fun j : ℕ => ((j : ℝ) + 1) * (1 + i)⁻¹ ^ j) := by
    have hA := (hasSum_coe_mul_geometric_of_norm_lt_one hnorm).summable
    have hB := summable_geometric_of_lt_one hq0.le hq1
    exact (hA.add hB).congr fun j => by ring
  have hsum : Summable (fun s => (1 + i)⁻¹ ^ s * x s) :=
    (hsumA.mul_right ν).congr fun s => by rw [hx s]; ring
  have h0 := forward_solution_unique hi hrec hnb hsum 0
  have hs : ∑' j, (1 + i)⁻¹ ^ j * x (0 + j) = ν * ∑' j : ℕ, (1 + i)⁻¹ ^ j * ((j : ℝ) + 1) := by
    rw [← tsum_mul_left]
    exact tsum_congr fun j => by rw [zero_add, hx j]; ring
  rw [hs] at h0
  have hmm : ez 0 = ν * (1 + i) / i - dc := by
    rw [h0]
    have := (ex1_sums hi).1
    have e : i / (1 + i) * (ν * ∑' j : ℕ, (1 + i)⁻¹ ^ j * ((j : ℝ) + 1)) =
      ν * (i / (1 + i) * ∑' j : ℕ, (1 + i)⁻¹ ^ j * ((j : ℝ) + 1)) := by ring
    rw [e, this]
    ring
  obtain ⟨hdc, he⟩ := solve_mm_gg L hmm hgg
  exact ⟨hmm, hdc, he⟩

/-- **Ex. 1(b), timing variant** (flag): if the new growth rate first applies to `M₂/M₁`
(`m₁ = 0`, `x_t = tν`), the MM′ intercept is `ν/ī` instead of `ν(1+ī)/ī`: `e₁ = ν/ī − (c − c*)`.
The signs of all effects are unchanged. -/
theorem ex1_growth_shock_late {i ν dc : ℝ} (hi : 0 < i) {x ez : ℕ → ℝ}
    (hx : ∀ t, x t = (t : ℝ) * ν)
    (hrec : ∀ t, x t - ez t = dc - (ez (t + 1) - ez t) / i)
    (hnb : Tendsto (fun T => (1 + i)⁻¹ ^ T * ez T) atTop (𝓝 0)) :
    ez 0 = ν / i - dc := by
  have hq0 : 0 < (1 + i)⁻¹ := inv_pos.2 (by linarith)
  have hq1 : (1 + i)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have hnorm : ‖(1 + i)⁻¹‖ < 1 := by rw [Real.norm_eq_abs, abs_of_pos hq0]; exact hq1
  have hsumA : Summable (fun j : ℕ => (j : ℝ) * (1 + i)⁻¹ ^ j) :=
    (hasSum_coe_mul_geometric_of_norm_lt_one hnorm).summable
  have hsum : Summable (fun s => (1 + i)⁻¹ ^ s * x s) :=
    (hsumA.mul_right ν).congr fun s => by rw [hx s]; ring
  have h0 := forward_solution_unique hi hrec hnb hsum 0
  have hs : ∑' j, (1 + i)⁻¹ ^ j * x (0 + j) = ν * ∑' j : ℕ, (1 + i)⁻¹ ^ j * (j : ℝ) := by
    rw [← tsum_mul_left]
    exact tsum_congr fun j => by rw [zero_add, hx j]; ring
  rw [hs] at h0
  rw [h0]
  have := (ex1_sums hi).2
  have e : i / (1 + i) * (ν * ∑' j : ℕ, (1 + i)⁻¹ ^ j * (j : ℝ)) =
    ν * (i / (1 + i) * ∑' j : ℕ, (1 + i)⁻¹ ^ j * (j : ℝ)) := by ring
  rw [e, this]
  ring

/-- **Ex. 1(b): the current account improves** (O&R p. 713): with `b̄/(1−n) = 2θ(c−c*)/((1+θ)δ)`
((45) with (57)), a rise in Home money growth (`c − c* > 0`) gives a Home surplus `b̄ > 0`. -/
theorem ex1_current_account (L : ReduxLinear) {b dc : ℝ}
    (h : b / (1 - L.n) = 2 * L.θ * dc / ((1 + L.θ) * L.δ)) (hdc : 0 < dc) : 0 < b := by
  have hn : 0 < 1 - L.n := by linarith [L.hn1]
  have hθ : 0 < L.θ := by linarith [L.hθ]
  have hpos : 0 < 2 * L.θ * dc / ((1 + L.θ) * L.δ) := by have := L.hδ; positivity
  rw [← h] at hpos
  exact (div_pos_iff_of_pos_right hn).1 hpos

/-! ## The equiproportionate money shock, exactly (10.1.8.1, T19) -/

/-- The bloc price index at equal bloc prices is that price (O&R (5), (22)). -/
theorem blocPriceIndex_self {θ n a : ℝ} (hθ : θ ≠ 1) (ha : 0 < a) :
    blocPriceIndex θ n a a = a := by
  unfold blocPriceIndex
  rw [show n * a ^ (1 - θ) + (1 - n) * a ^ (1 - θ) = a ^ (1 - θ) by ring, ← rpow_mul ha.le]
  have : (1 - θ) * (1 / (1 - θ)) = 1 := by
    have : 1 - θ ≠ 0 := sub_ne_zero.2 (Ne.symm hθ)
    field_simp
  rw [this, rpow_one]

/-- The date-1 unknowns of the nonlinear sticky-price economy after an unanticipated money shock,
O&R §10.1.7–§10.1.8 (pp. 674–684): the exchange rate `𝓔₁`, price levels `P₁, P₁*`, consumption,
output, the current account `B₂`, the real rate `r₂`, the nominal rates `i₂, i₂*`, date-2 price
levels `P₂, P₂*` and the long-run real allocation (a steady state from date 2 on, T9). -/
structure Date1Vars where
  E1 : ℝ
  P1 : ℝ
  Ps1 : ℝ
  C1 : ℝ
  Cs1 : ℝ
  y1 : ℝ
  ys1 : ℝ
  B2 : ℝ
  r2 : ℝ
  i2 : ℝ
  is2 : ℝ
  P2 : ℝ
  Ps2 : ℝ
  lr : Allocation

/-- **The nonlinear equilibrium after an unanticipated equiproportionate money shock**,
O&R §10.1.7–§10.1.8.1 (pp. 674–684). Starting from the symmetric steady state with price levels
`P₀, P₀*` (so the preset goods prices are `p(h) = P₀`, `p*(f) = P₀*`, eq. (22)), money becomes
`μM₀`, `μM₀*` permanently at date 1. Date 1: the price indexes (5)–(6), world demand (10) (output
demand-determined at preset prices), the current account (54) from `B₁ = 0`, the Euler equations
(13) into the long run, money demand (14), Fisher parity; from date 2: a flexible-price steady
state (T9, `flexible_path_is_steady`) with long-run money demand (26). EXACTLY, T9 indexes that
steady state by `B̄ = (1 + r₂)B₂/(1 + δ)` (the date-2 budget pays `r₂`, not `δ`, on `B₂`); the
book's "`b_t = b̄` for all `t ≥ 2`" (p. 677) is its first-order version (`longrun_assets`). -/
structure IsEquiEqm (M : ReduxParams) (P0 Ps0 M0 Ms0 μ : ℝ) (w : Date1Vars) : Prop where
  E1_pos : 0 < w.E1
  C1_pos : 0 < w.C1
  Cs1_pos : 0 < w.Cs1
  i2_pos : 0 < w.i2
  is2_pos : 0 < w.is2
  P2_pos : 0 < w.P2
  Ps2_pos : 0 < w.Ps2
  r2_pos : 0 < 1 + w.r2
  price : w.P1 = blocPriceIndex M.θ M.n P0 (w.E1 * Ps0)
  price_star : w.Ps1 = blocPriceIndex M.θ M.n (P0 / w.E1) Ps0
  demand : w.y1 = cesDemand M.θ P0 w.P1 (worldConsumption M.n w.C1 w.Cs1)
  demand_star : w.ys1 = cesDemand M.θ Ps0 w.Ps1 (worldConsumption M.n w.C1 w.Cs1)
  ca : w.B2 = P0 / w.P1 * w.y1 - w.C1
  euler : w.lr.C = M.β * (1 + w.r2) * w.C1
  euler_star : w.lr.Cs = M.β * (1 + w.r2) * w.Cs1
  money : μ * M0 / w.P1 = M.χ * w.C1 * ((1 + w.i2) / w.i2)
  money_star : μ * Ms0 / w.Ps1 = M.χ * w.Cs1 * ((1 + w.is2) / w.is2)
  fisher : 1 + w.i2 = w.P2 / w.P1 * (1 + w.r2)
  fisher_star : 1 + w.is2 = w.Ps2 / w.Ps1 * (1 + w.r2)
  longrun : IsSteadyState M ((1 + w.r2) * w.B2 / (1 + M.δ)) w.lr
  money2 : μ * M0 / w.P2 = M.χ * w.lr.C * ((1 + M.δ) / M.δ)
  money2_star : μ * Ms0 / w.Ps2 = M.χ * w.lr.Cs * ((1 + M.δ) / M.δ)

/-- **The equiproportionate shock: the equilibrium is unique and is what the book says, EXACTLY**
(O&R §10.1.8.1, pp. 683–684; T19). In any equilibrium: `i₂ = i₂* = δ` (the nominal rate is
unchanged), `𝓔₁ = 𝓔₀` (no exchange-rate or terms-of-trade effect), `B₂ = 0` (no current account),
`P₁ = P₀`, `C₁ = C₁* = y₁ = y₁* = μȳ₀`, `1 + r₂ = (1+δ)/μ`, `P₂ = μP₀`, and the long run is the
initial symmetric steady state. The proof is exact (no linearisation): `nominal_rate_exact` and
exact UIP give `𝓔₁ = 𝓔₂`; long-run money demand makes `𝓔₂/𝓔₀ = C̄*/C̄`; the current account has
the sign of `𝓔₁/𝓔₀ − 1`; and in a steady state `B̄ > 0 ⟺ C̄ > C̄*` (T7). -/
theorem equiproportionate_unique {M : ReduxParams} {P0 Ps0 M0 Ms0 μ : ℝ} {w : Date1Vars}
    (hP0 : 0 < P0) (hPs0 : 0 < Ps0) (hM0 : 0 < M0) (hMs0 : 0 < Ms0) (hμ : 0 < μ)
    (h26 : M0 / P0 = M.χ * (1 + M.δ) / M.δ * M.ybar0)
    (h26s : Ms0 / Ps0 = M.χ * (1 + M.δ) / M.δ * M.ybar0)
    (h : IsEquiEqm M P0 Ps0 M0 Ms0 μ w) :
    w.i2 = M.δ ∧ w.is2 = M.δ ∧ w.E1 = P0 / Ps0 ∧ w.B2 = 0 ∧ w.P1 = P0 ∧ w.Ps1 = Ps0 ∧
      w.C1 = μ * M.ybar0 ∧ w.Cs1 = μ * M.ybar0 ∧ w.y1 = μ * M.ybar0 ∧ w.ys1 = μ * M.ybar0 ∧
      1 + w.r2 = (1 + M.δ) / μ ∧ w.P2 = μ * P0 ∧ w.lr = symmetricSteady M := by
  have hθ := M.hθ
  have hθ1 : M.θ ≠ 1 := by linarith
  have hn0 := M.hn0
  have hn1 := M.hn1
  have hδ := M.δ_pos
  have hχ := M.hχ
  have hy0 := M.ybar0_pos
  have hβ := M.hβ0
  have hβδ := M.β_mul_one_add_δ
  have hP1 : 0 < w.P1 := by
    rw [h.price]; exact blocPriceIndex_pos hn0 hn1 hP0 (mul_pos h.E1_pos hPs0)
  have hPs1 : 0 < w.Ps1 := by
    rw [h.price_star]; exact blocPriceIndex_pos hn0 hn1 (div_pos hP0 h.E1_pos) hPs0
  have hlrC := h.longrun.static.C_pos
  have hlrCs := h.longrun.static.Cs_pos
  -- (a) nominal rates are exactly `δ`
  have hi2 : w.i2 = M.δ := nominal_rate_exact hβ hδ hβδ hχ (mul_pos hμ hM0) hP1 h.P2_pos
    h.C1_pos h.i2_pos h.r2_pos h.money h.money2 h.euler h.fisher
  have his2 : w.is2 = M.δ := nominal_rate_exact hβ hδ hβδ hχ (mul_pos hμ hMs0) hPs1 h.Ps2_pos
    h.Cs1_pos h.is2_pos h.r2_pos h.money_star h.money2_star h.euler_star h.fisher_star
  -- (b) exact UIP: `𝓔₁ = P₁/P₁* = P₂/P₂*`
  have hppp : w.P1 = w.E1 * w.Ps1 := by
    rw [h.price, h.price_star]; exact bloc_ppp hθ1 hn0 hn1 hP0 hPs0 h.E1_pos
  have hE12 : w.P1 / w.Ps1 = w.P2 / w.Ps2 := by
    have hf := h.fisher; have hfs := h.fisher_star
    rw [hi2] at hf; rw [his2] at hfs
    exact no_overshooting_exact hδ hP1 hPs1 h.Ps2_pos hf hfs
  -- (c) consumption from money demand
  have hM0' : M0 = M.χ * (1 + M.δ) / M.δ * M.ybar0 * P0 := by field_simp at h26 ⊢; linarith
  have hMs0' : Ms0 = M.χ * (1 + M.δ) / M.δ * M.ybar0 * Ps0 := by field_simp at h26s ⊢; linarith
  have hk : M.χ * ((1 + M.δ) / M.δ) ≠ 0 := by positivity
  have hC1 : w.C1 = μ * M.ybar0 * (P0 / w.P1) := by
    have e1 : w.C1 = μ * M0 / w.P1 / (M.χ * ((1 + M.δ) / M.δ)) := by
      rw [eq_div_iff hk, h.money, hi2]; ring
    rw [e1, hM0']; field_simp
  have hCs1 : w.Cs1 = μ * M.ybar0 * (Ps0 / w.Ps1) := by
    have e1 : w.Cs1 = μ * Ms0 / w.Ps1 / (M.χ * ((1 + M.δ) / M.δ)) := by
      rw [eq_div_iff hk, h.money_star, his2]; ring
    rw [e1, hMs0']; field_simp
  have hC2 : w.lr.C = μ * M.ybar0 * (P0 / w.P2) := by
    have e1 : w.lr.C = μ * M0 / w.P2 / (M.χ * ((1 + M.δ) / M.δ)) := by
      rw [eq_div_iff hk, h.money2]; ring
    rw [e1, hM0']; field_simp
  have hCs2 : w.lr.Cs = μ * M.ybar0 * (Ps0 / w.Ps2) := by
    have e1 : w.lr.Cs = μ * Ms0 / w.Ps2 / (M.χ * ((1 + M.δ) / M.δ)) := by
      rw [eq_div_iff hk, h.money2_star]; ring
    rw [e1, hMs0']; field_simp
  -- (d) the relative prices `α = P₀/P₁`, `α* = P₀*/P₁*`
  set a := P0 / w.P1 with ha
  set as := Ps0 / w.Ps1 with has
  have hapos : 0 < a := div_pos hP0 hP1
  have haspos : 0 < as := div_pos hPs0 hPs1
  have hidx : M.n * a ^ (1 - M.θ) + (1 - M.n) * as ^ (1 - M.θ) = 1 := by
    have := bloc_relative_price_sum hθ1 hn0 hn1 hP0 hPs0 h.E1_pos
    rw [← h.price, ← h.price_star] at this
    exact this
  have hsum : M.n * a * a ^ (-M.θ) + (1 - M.n) * as * as ^ (-M.θ) = 1 := by
    rw [mul_assoc, mul_assoc, ces_price_mul_demand hapos, ces_price_mul_demand haspos]
    exact hidx
  -- (e) the long-run exchange rate: `α* C̄ = α C̄*`
  have hcross : as * w.lr.C = a * w.lr.Cs := by
    rw [has, ha, hC2, hCs2]
    have h2 := hE12
    have := h.P2_pos.ne'
    have := h.Ps2_pos.ne'
    have := hP1.ne'
    have := hPs1.ne'
    field_simp at h2 ⊢
    linear_combination h2
  -- (f) the current account has the sign of `α* − α`
  have hy1e : w.y1 = a ^ (-M.θ) * (μ * M.ybar0 * (M.n * a + (1 - M.n) * as)) := by
    rw [h.demand]; unfold cesDemand worldConsumption; rw [← ha, hC1, hCs1]; ring
  have hB2 : w.B2 = μ * M.ybar0 * a * (1 - M.n) * as * (a ^ (-M.θ) - as ^ (-M.θ)) := by
    rw [h.ca, ← ha, hy1e, hC1]
    linear_combination (μ * M.ybar0 * a) * hsum
  have hneg : -M.θ < 0 := by linarith
  have hαeq : a = as := by
    rcases lt_trichotomy a as with hlt | heq | hgt
    · exfalso
      have hB : 0 < w.B2 := by
        rw [hB2]
        have := rpow_lt_rpow_of_neg hapos hlt hneg
        have h1 : 0 < 1 - M.n := by linarith
        have : 0 < a ^ (-M.θ) - as ^ (-M.θ) := by linarith
        positivity
      have hlt2 := (steady_C_gt_iff h.longrun).2 (by
        have := h.r2_pos; have : 0 < 1 + M.δ := by linarith
        positivity)
      have e1 := mul_lt_mul_of_pos_left hlt2 hapos
      have e2 := mul_lt_mul_of_pos_right hlt hlrC
      linarith
    · exact heq
    · exfalso
      have hB : w.B2 < 0 := by
        rw [hB2]
        have := rpow_lt_rpow_of_neg haspos hgt hneg
        have h1 : 0 < 1 - M.n := by linarith
        have : a ^ (-M.θ) - as ^ (-M.θ) < 0 := by linarith
        have hp : 0 < μ * M.ybar0 * a * (1 - M.n) * as := by positivity
        exact mul_neg_of_pos_of_neg hp this
      have hle : w.lr.C ≤ w.lr.Cs := by
        by_contra hc
        push Not at hc
        have h3 := (steady_C_gt_iff h.longrun).1 hc
        have h4 : (1 + w.r2) * w.B2 / (1 + M.δ) < 0 :=
          div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg h.r2_pos hB) (by linarith)
        linarith
      have e1 := mul_le_mul_of_nonneg_left hle hapos.le
      have e2 := mul_lt_mul_of_pos_right hgt hlrC
      linarith
  -- (g) hence `α = α* = 1`
  have ha1 : a = 1 := by
    rw [← hαeq] at hidx
    have h1 : a ^ (1 - M.θ) = 1 := by linarith
    have hne : (1 - M.θ) ≠ 0 := by linarith
    have := (rpow_left_inj hapos.le zero_le_one hne).1 (by rw [h1, one_rpow])
    exact this
  have has1 : as = 1 := by rw [← hαeq]; exact ha1
  have hP1eq : w.P1 = P0 := by
    rw [ha] at ha1; field_simp at ha1; linarith
  have hPs1eq : w.Ps1 = Ps0 := by
    rw [has] at has1; field_simp at has1; linarith
  have hE1 : w.E1 = P0 / Ps0 := by
    rw [hP1eq, hPs1eq] at hppp
    field_simp; linarith
  have hC1' : w.C1 = μ * M.ybar0 := by rw [hC1, ha1, mul_one]
  have hCs1' : w.Cs1 = μ * M.ybar0 := by rw [hCs1, has1, mul_one]
  have hX1 : worldConsumption M.n w.C1 w.Cs1 = μ * M.ybar0 := by
    unfold worldConsumption; rw [hC1', hCs1']; ring
  have hy1 : w.y1 = μ * M.ybar0 := by
    rw [h.demand, hX1, hP1eq, cesDemand_at_index M.θ hP0.ne']
  have hys1 : w.ys1 = μ * M.ybar0 := by
    rw [h.demand_star, hX1, hPs1eq, cesDemand_at_index M.θ hPs0.ne']
  have hB20 : w.B2 = 0 := by
    rw [h.ca, hy1, hC1', hP1eq, div_self hP0.ne']; ring
  have hlr : w.lr = symmetricSteady M := by
    have := h.longrun; rw [hB20, mul_zero, zero_div] at this
    exact (isSteadyState_zero_iff M w.lr).1 this
  have hr2 : 1 + w.r2 = (1 + M.δ) / μ := by
    have he := h.euler
    rw [hlr, hC1'] at he
    simp only [symmetricSteady] at he
    have hk2 : M.ybar0 * ((1 + w.r2) * μ - (1 + M.δ)) = 0 := by
      linear_combination (-(1 + M.δ)) * he - (1 + w.r2) * μ * M.ybar0 * hβδ
    have := (mul_eq_zero.1 hk2).resolve_left hy0.ne'
    rw [eq_div_iff hμ.ne']
    linarith
  have hP2 : w.P2 = μ * P0 := by
    have hc := hC2
    rw [hlr] at hc
    simp only [symmetricSteady] at hc
    have := h.P2_pos.ne'
    have e : M.ybar0 * w.P2 = μ * M.ybar0 * P0 := by
      calc M.ybar0 * w.P2 = μ * M.ybar0 * (P0 / w.P2) * w.P2 := by rw [← hc]
        _ = μ * M.ybar0 * P0 := by field_simp
    have hk3 : M.ybar0 * (w.P2 - μ * P0) = 0 := by linear_combination e
    have := (mul_eq_zero.1 hk3).resolve_left hy0.ne'
    linarith
  exact ⟨hi2, his2, hE1, hB20, hP1eq, hPs1eq, hC1', hCs1', hy1, hys1, hr2, hP2, hlr⟩

/-- **The long-run asset position: exact versus first order** (O&R p. 677, "`b_t = b̄` for all
`t ≥ 2`"): after the date-1 current account `B₂`, the flexible-price steady state from date 2 is
indexed EXACTLY by `B̄ = (1 + r₂)B₂/(1 + δ)` (`flexible_path_is_steady`, T9), not by `B₂`. Along
`B₂ = τ b̄ C̄₀`, `r₂ = δ(1 + τ r̂)`, the two agree to first order: `dB̄/dτ = b̄ C̄₀` at `τ = 0`. -/
theorem longrun_assets {δ b rh C0 : ℝ} (hδ : 0 < δ) :
    HasDerivAt (fun τ => (1 + δ * (1 + τ * rh)) * (τ * b * C0) / (1 + δ)) (b * C0) 0 := by
  have h1 : HasDerivAt (fun τ => 1 + δ * (1 + τ * rh)) (δ * rh) 0 := by
    have := (((hasDerivAt_id (0 : ℝ)).mul_const rh).const_add 1).const_mul δ
    simpa using this.const_add 1
  have h2 : HasDerivAt (fun τ : ℝ => τ * b * C0) (b * C0) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const b).mul_const C0
  have h := (h1.mul h2).div_const (1 + δ)
  convert h using 1
  have : (1 + δ) ≠ 0 := by linarith
  simp
  field_simp

/-- The equilibrium of the equiproportionate shock (T19), O&R pp. 683–684. -/
noncomputable def equiSolution (M : ReduxParams) (P0 Ps0 μ : ℝ) : Date1Vars where
  E1 := P0 / Ps0
  P1 := P0
  Ps1 := Ps0
  C1 := μ * M.ybar0
  Cs1 := μ * M.ybar0
  y1 := μ * M.ybar0
  ys1 := μ * M.ybar0
  B2 := 0
  r2 := (1 + M.δ) / μ - 1
  i2 := M.δ
  is2 := M.δ
  P2 := μ * P0
  Ps2 := μ * Ps0
  lr := symmetricSteady M

/-- **Existence for the equiproportionate shock** (T19): `equiSolution` satisfies every
equilibrium condition of `IsEquiEqm`. Together with `equiproportionate_unique` the nonlinear
sticky-price equilibrium exists and is unique for every `μ > 0`. -/
theorem equiproportionate_exists {M : ReduxParams} {P0 Ps0 M0 Ms0 μ : ℝ} (hP0 : 0 < P0)
    (hPs0 : 0 < Ps0) (hμ : 0 < μ) (h26 : M0 / P0 = M.χ * (1 + M.δ) / M.δ * M.ybar0)
    (h26s : Ms0 / Ps0 = M.χ * (1 + M.δ) / M.δ * M.ybar0) :
    IsEquiEqm M P0 Ps0 M0 Ms0 μ (equiSolution M P0 Ps0 μ) := by
  have hθ1 : M.θ ≠ 1 := by linarith [M.hθ]
  have hδ := M.δ_pos
  have hy0 := M.ybar0_pos
  have hβδ := M.β_mul_one_add_δ
  have hsym : IsSteadyState M ((1 + ((1 + M.δ) / μ - 1)) * 0 / (1 + M.δ)) (symmetricSteady M) := by
    rw [mul_zero, zero_div]; exact (isSteadyState_zero_iff M (symmetricSteady M)).2 rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hsym, ?_,
    ?_⟩ <;> simp only [equiSolution, symmetricSteady]
  · positivity
  · positivity
  · positivity
  · exact hδ
  · exact hδ
  · positivity
  · positivity
  · ring_nf; positivity
  · rw [div_mul_cancel₀ _ hPs0.ne', blocPriceIndex_self hθ1 hP0]
  · rw [div_div_eq_mul_div, mul_div_cancel_left₀ _ hP0.ne', blocPriceIndex_self hθ1 hPs0]
  · rw [cesDemand_at_index M.θ hP0.ne']; unfold worldConsumption; ring
  · rw [cesDemand_at_index M.θ hPs0.ne']; unfold worldConsumption; ring
  · rw [div_self hP0.ne']; ring
  · have : (1 + ((1 + M.δ) / μ - 1)) = (1 + M.δ) / μ := by ring
    rw [this]; field_simp; linarith
  · have : (1 + ((1 + M.δ) / μ - 1)) = (1 + M.δ) / μ := by ring
    rw [this]; field_simp; linarith
  · have hM0 : M0 = M.χ * (1 + M.δ) / M.δ * M.ybar0 * P0 := by field_simp at h26 ⊢; linarith
    rw [hM0]; field_simp
  · have hMs0 : Ms0 = M.χ * (1 + M.δ) / M.δ * M.ybar0 * Ps0 := by
      field_simp at h26s ⊢; linarith
    rw [hMs0]; field_simp
  · rw [mul_div_cancel_right₀ _ hP0.ne']; field_simp; ring
  · rw [mul_div_cancel_right₀ _ hPs0.ne']; field_simp; ring
  · have hM0 : M0 = M.χ * (1 + M.δ) / M.δ * M.ybar0 * P0 := by field_simp at h26 ⊢; linarith
    rw [hM0]; field_simp
  · have hMs0 : Ms0 = M.χ * (1 + M.δ) / M.δ * M.ybar0 * Ps0 := by
      field_simp at h26s ⊢; linarith
    rw [hMs0]; field_simp

/-- **Output is demand-determined only up to a bound** (O&R p. 674 and p. 688; T19–T20): at the
equiproportionate equilibrium a Home producer is willing to meet demand at the preset price iff
the real price per unit of marginal utility covers the marginal disutility of effort,
`(p(h)/P₁)/C₁ ≥ κ y₁`, which with `p(h) = P₁`, `C₁ = y₁ = μȳ₀` and `κȳ₀² = (θ−1)/θ` is exactly
`μ ≤ (θ/(θ−1))^{1/2}`. The book's "small shocks" hides this bound. -/
theorem equiproportionate_demand_bound (M : ReduxParams) {μ : ℝ} (hμ : 0 < μ) :
    M.κ * (μ * M.ybar0) ≤ 1 / (μ * M.ybar0) ↔ μ ≤ Real.sqrt (M.θ / (M.θ - 1)) := by
  have hy0 := M.ybar0_pos
  have hθ := M.hθ
  have hk := M.κ_mul_ybar0_sq
  have hθ1 : 0 < M.θ - 1 := by linarith
  rw [le_div_iff₀ (by positivity), Real.le_sqrt hμ.le (by positivity)]
  have e : M.κ * (μ * M.ybar0) * (μ * M.ybar0) = μ ^ 2 * ((M.θ - 1) / M.θ) := by
    rw [← hk]; ring
  rw [e, le_div_iff₀ hθ1]
  constructor
  · intro h
    have : μ ^ 2 * (M.θ - 1) ≤ M.θ := by
      have hθ0 : 0 < M.θ := by linarith
      rw [mul_div_assoc'] at h
      rwa [div_le_one hθ0] at h
    linarith
  · intro h
    have hθ0 : 0 < M.θ := by linarith
    rw [mul_div_assoc', div_le_one hθ0]
    linarith

/-- The exact period-1 utility gain of the equiproportionate shock, O&R §10.1.8.1 (T19):
`log μ − ((θ−1)/(2θ))(μ² − 1)`. -/
noncomputable def equiGain (θ μ : ℝ) : ℝ := Real.log μ - (θ - 1) / (2 * θ) * (μ ^ 2 - 1)

/-- **The real-utility change of the equiproportionate shock** (T19): with `C₁ = y₁ = μȳ₀` and the
initial `C = y = ȳ₀`, `[log C₁ − (κ/2)y₁²] − [log ȳ₀ − (κ/2)ȳ₀²] = log μ − ((θ−1)/(2θ))(μ²−1)`.
Later periods are unchanged (the long run is the initial steady state, `equiproportionate_unique`),
so this is the whole change in `Uᴿ` (p. 684). -/
theorem equiGain_eq (M : ReduxParams) {μ : ℝ} (hμ : 0 < μ) :
    (Real.log (μ * M.ybar0) - M.κ / 2 * (μ * M.ybar0) ^ 2) -
      (Real.log M.ybar0 - M.κ / 2 * M.ybar0 ^ 2) = equiGain M.θ μ := by
  have hy0 := M.ybar0_pos
  have hk := M.κ_mul_ybar0_sq
  have hθ0 : M.θ ≠ 0 := by linarith [M.hθ]
  unfold equiGain
  rw [Real.log_mul hμ.ne' hy0.ne']
  have e : M.κ / 2 * (μ * M.ybar0) ^ 2 - M.κ / 2 * M.ybar0 ^ 2 =
      (M.κ * M.ybar0 ^ 2) / 2 * (μ ^ 2 - 1) := by ring
  have : Real.log μ + Real.log M.ybar0 - M.κ / 2 * (μ * M.ybar0) ^ 2 -
      (Real.log M.ybar0 - M.κ / 2 * M.ybar0 ^ 2) =
      Real.log μ - (M.κ / 2 * (μ * M.ybar0) ^ 2 - M.κ / 2 * M.ybar0 ^ 2) := by ring
  rw [this, e, hk]
  field_simp

/-- **The equiproportionate expansion raises welfare, exactly** (O&R p. 683, "must raise welfare
in both countries"; T19): the gain is strictly increasing on `(0, (θ/(θ−1))^{1/2}]` and strictly
positive for `1 < μ ≤ (θ/(θ−1))^{1/2}`, i.e. on the whole range where output is
demand-determined (`equiproportionate_demand_bound`). -/
theorem equiGain_pos {θ μ : ℝ} (hθ : 1 < θ) (hμ1 : 1 < μ) (hμb : μ ≤ Real.sqrt (θ / (θ - 1))) :
    0 < equiGain θ μ ∧
      StrictMonoOn (equiGain θ) (Set.Ioc 0 (Real.sqrt (θ / (θ - 1)))) := by
  have hk : 0 < (θ - 1) / θ := div_pos (by linarith) (by linarith)
  have hplan : plannerOutput ((θ - 1) / θ) = Real.sqrt (θ / (θ - 1)) := by
    unfold plannerOutput; congr 1; field_simp
  have hmono := planner_strictMonoOn hk
  rw [hplan] at hmono
  have hrel : ∀ x, equiGain θ x = plannerObjective ((θ - 1) / θ) x + (θ - 1) / (2 * θ) := by
    intro x; unfold equiGain plannerObjective
    have : θ ≠ 0 := by linarith
    field_simp; ring
  have hstrict : StrictMonoOn (equiGain θ) (Set.Ioc 0 (Real.sqrt (θ / (θ - 1)))) := by
    intro a ha b hb hab
    rw [hrel a, hrel b]
    linarith [hmono ha hb hab]
  refine ⟨?_, hstrict⟩
  have h1mem : (1 : ℝ) ∈ Set.Ioc 0 (Real.sqrt (θ / (θ - 1))) :=
    ⟨one_pos, by linarith⟩
  have hμmem : μ ∈ Set.Ioc 0 (Real.sqrt (θ / (θ - 1))) := ⟨by linarith, hμb⟩
  have := hstrict h1mem hμmem hμ1
  have h0 : equiGain θ 1 = 0 := by simp [equiGain]
  linarith

/-- **First order: the welfare effect is `mᵂ/θ`** (T19 recovers (76), O&R p. 685): the
derivative of the exact gain at `μ = 1` is `1/θ`, so a proportional expansion `dμ = mᵂ` raises
`Uᴿ` by `mᵂ/θ`. -/
theorem equiGain_hasDerivAt_one {θ : ℝ} (hθ : θ ≠ 0) : HasDerivAt (equiGain θ) (1 / θ) 1 := by
  have h1 := Real.hasDerivAt_log (one_ne_zero (α := ℝ))
  have h2 : HasDerivAt (fun μ : ℝ => μ ^ 2 - 1) (2 * 1) 1 := by
    simpa using (hasDerivAt_pow 2 (1 : ℝ)).sub_const 1
  have h := h1.sub (h2.const_mul ((θ - 1) / (2 * θ)))
  convert h using 1
  · funext y; simp only [equiGain, Pi.sub_apply]
  · field_simp; ring

/-- **Real balances in the equiproportionate shock** (O&R p. 683 "real balances must rise in the
short run"; fn 19): at the equilibrium `M₁/P₁ = μ M₀/P₀` (up for `μ > 1`) and
`M₂/P₂ = M₀/P₀` (unchanged from date 2). -/
theorem equiproportionate_real_balances {P0 M0 μ : ℝ} (hP0 : 0 < P0) (hμ : 0 < μ) :
    μ * M0 / P0 = μ * (M0 / P0) ∧ μ * M0 / (μ * P0) = M0 / P0 := by
  refine ⟨by ring, ?_⟩
  field_simp

end ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The redux model: welfare

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §10.1.7.1 (p. 674),
§10.1.8.2 (pp. 684–686), §10.1.9 (pp. 686–688), §10.1.10 (pp. 688–689) and Exercise 3
(p. 713). The equiproportionate shock of §10.1.8.1 (T19) is in `ReduxMoneyShocks`.

* **(75) as a genuine derivative (T17).** Lifetime utility is an infinite discounted sum
  (`lifetimeWelfare`, a `tsum`); along the post-shock path, which is at its new steady state from
  date 2 on, it equals date-1 utility plus `β/(1−β) = 1/δ` times the long-run period utility
  (`lifetimeWelfare_twoRegime`). Its derivative in the direction of any log-deviations is
  `c + χ(m − p) − κȳ₀² y + (1/δ)[c̄ + χ(m̄ − p̄) − κȳ₀² ȳ]` (`welfare_hasDerivAt`), and with
  `κȳ₀² = (θ−1)/θ` the real part is exactly (75) (`welfare_eq75`).
* **(76) (T17).** The quasi-reduced forms of p. 685 hold for every money-shock equilibrium
  (`quasi_reduced_forms`); every term in `e` cancels IDENTICALLY (`welfare_e_cancels`), so
  `dUᴿ = cᵂ/θ = mᵂ/θ` for Home AND for Foreign (`welfare_eq76`), and this is the derivative of
  `Uᴿ` along the equilibrium response (`welfare_eq76_hasDerivAt`).
* **"As long as χ is not too large" made exact (T18, p. 684, fn 19).** For a Foreign expansion
  the total first-order change in Home utility, real balances included, is
  `(1−n)m*[(δ(1+θ)+2) + χ(δ(1+θ)+2θ+1−θ²)]/D` (`foreign_shock_total`). It is positive for EVERY
  `χ ≥ 0` iff `θ² − 2θ − 1 ≤ δ(1+θ)` (e.g. whenever `θ ≤ 1 + √2`); otherwise it is positive iff
  `χ < (δ(1+θ)+2)/(θ² − 2θ − 1 − δ(1+θ))`. Counterexample to the unconditional reading:
  `θ = 6`, `δ = 0.05`, `χ = 0.2` (threshold `≈ 0.104`): a Foreign expansion LOWERS Home welfare
  (`counterexample_theta6`). fn 19's real-balance claims are proved (`home_shock_real_balances`,
  `foreign_shock_real_balances`).
* **Menu costs and demand-determined output (T20, p. 674).** The producer's payoff is strictly
  concave in output; the gain from re-optimising at a preset price is at most
  `(marginal payoff)²/(2κ)`, hence SECOND order in the shock, so any menu cost `Z > 0` deters
  adjustment for all small enough shocks (`menu_cost_second_order`, `menu_cost_rationale`).
  Meeting demand at a preset price is optimal IFF price covers marginal cost
  (`meet_demand_iff`); at the initial steady state it does so strictly (markup `θ/(θ−1)`).
* **Income taxes (77)–(81) (T21).** Rebated taxes leave the budget (8) and the log-linear
  labour condition unchanged; (80); the welfare effect (81) of a Foreign expansion, with the exact
  sign condition `dUᴿ < 0 ⟺ τ(θ−1)² > δ(1+θ)+2` and "for large enough θ" made precise.
* **Small country (T22, p. 688).** As `n → 0` a Home expansion has no world effects and no welfare
  effect, while `y → θe`.
* **Exercise 3.** The small open economy directly: the nonlinear steady state exists and is unique
  for every `B̄`; the linear model has exactly one solution, which is (65)–(67) with `n = 0`,
  `m* = 0`, and its welfare effect is exactly zero.
-/

namespace ObstfeldRogoff.StickyPriceModels.ReduxWelfare

open Real Filter Topology ReduxPrimitives ReduxLogLinear ReduxSteadyState ReduxMoneyShocks

/-- The linear-model parameters `(θ, δ, n)` of a nonlinear parameter set (O&R §10.1.5, p. 669):
the log-linearisation is taken at the symmetric steady state of `M`. -/
noncomputable def linearOf (M : ReduxParams) : ReduxLinear :=
  ⟨M.θ, M.δ, M.n, M.hθ, M.δ_pos, M.hn0, M.hn1⟩

/-! ## Lifetime utility along a path that reaches its steady state at date 2 -/

/-- A two-regime path (O&R p. 675: "the economy reaches its long-run equilibrium in just one
period"): value `a` at the shock date (index 0 = the book's date 1), value `b` from then on. -/
def twoRegime (a b : ℝ) (s : ℕ) : ℝ := if s = 0 then a else b

/-- **Discounted sum of a two-regime path** (O&R p. 684, "the new steady state is reached after
just one period"): for `0 ≤ β < 1`, `Σ_{s≥0} β^s x_s = a + (β/(1−β)) b`. -/
theorem hasSum_twoRegime {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (a b : ℝ) :
    HasSum (fun s => β ^ s * twoRegime a b s) (a + β / (1 - β) * b) := by
  have h1 := (hasSum_geometric_of_lt_one hβ0 hβ1).mul_right b
  have h2 : HasSum (fun s : ℕ => if s = 0 then a - b else 0) (a - b) := hasSum_ite_eq 0 (a - b)
  have h := h1.add h2
  have hne : 1 - β ≠ 0 := by linarith
  convert h using 1
  · funext s
    unfold twoRegime
    split_ifs with hs
    · subst hs; ring
    · ring
  · field_simp; ring

/-- `β/(1−β) = 1/δ` with `δ = (1−β)/β` (O&R (19) and p. 684: `Σ_{s≥t+1} β^{s−t} = 1/δ`). -/
theorem beta_div_one_sub (M : ReduxParams) : M.β / (1 - M.β) = 1 / M.δ := by
  have h0 := M.hβ0
  have h1 : 1 - M.β ≠ 0 := by linarith [M.hβ1]
  unfold ReduxParams.δ timePreferenceRate
  field_simp

/-- The period utility (1), O&R p. 661, with a possibly shocked effort weight `κ`:
`log C + χ log(M/P) − (κ/2) y²`. -/
noncomputable def periodWelfare (χ κ C k y : ℝ) : ℝ := Real.log C + χ * Real.log k - κ / 2 * y ^ 2

/-- Lifetime utility (1), O&R p. 661, as a genuine infinite sum from the shock date:
`Σ_{s≥0} β^s [log C_s + χ log(M_s/P_s) − (κ/2) y_s²]`. -/
noncomputable def lifetimeWelfare (β χ κ : ℝ) (C k y : ℕ → ℝ) : ℝ :=
  ∑' s, β ^ s * periodWelfare χ κ (C s) (k s) (y s)

/-- The "real" component of utility, O&R p. 684: `Uᴿ = Σ_{s≥0} β^s [log C_s − (κ/2) y_s²]`. -/
noncomputable def realWelfare (β κ : ℝ) (C y : ℕ → ℝ) : ℝ :=
  ∑' s, β ^ s * (Real.log (C s) - κ / 2 * y s ^ 2)

/-- `Uᴿ` is lifetime utility with `χ = 0` (O&R p. 684). -/
theorem realWelfare_eq (β κ : ℝ) (C y : ℕ → ℝ) :
    realWelfare β κ C y = lifetimeWelfare β 0 κ C (fun _ => 1) y := by
  unfold realWelfare lifetimeWelfare periodWelfare
  simp

/-- **Lifetime utility along a two-regime path** (O&R p. 684): it is date-1 utility plus
`β/(1−β)` times long-run period utility (the sum is genuinely infinite and summable). -/
theorem lifetimeWelfare_twoRegime {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (χ κ C1 Cb k1 kb y1 yb : ℝ) :
    lifetimeWelfare β χ κ (twoRegime C1 Cb) (twoRegime k1 kb) (twoRegime y1 yb) =
      periodWelfare χ κ C1 k1 y1 + β / (1 - β) * periodWelfare χ κ Cb kb yb := by
  have h := hasSum_twoRegime hβ0 hβ1 (periodWelfare χ κ C1 k1 y1) (periodWelfare χ κ Cb kb yb)
  rw [← h.tsum_eq]
  unfold lifetimeWelfare
  congr 1
  funext s
  unfold twoRegime
  split_ifs <;> rfl

/-- The derivative of `τ ↦ log(A e^{τx})` is `x` (log-deviations, O&R §10.1.5). -/
theorem hasDerivAt_log_exp_path {A x : ℝ} (hA : 0 < A) :
    HasDerivAt (fun τ => Real.log (A * Real.exp (τ * x))) x 0 := by
  have e : (fun τ => Real.log (A * Real.exp (τ * x))) = fun τ => Real.log A + τ * x := by
    funext τ
    rw [Real.log_mul hA.ne' (Real.exp_pos _).ne', Real.log_exp]
  rw [e]
  simpa using ((hasDerivAt_id (0 : ℝ)).mul_const x).const_add (Real.log A)

/-- **Differentiating period utility** (O&R p. 684, and p. 696 for the productivity term): along
`C = C₀e^{τc}`, `M/P = k₀e^{τm}`, `y = Y₀e^{τŷ}` and effort weight `κ = κ₀(1 − τa)`
(`a = −dκ/κ₀`, O&R p. 696), the derivative of period utility at `τ = 0` is
`c + χm − κ₀Y₀²ŷ + κ₀Y₀²a/2`. -/
theorem hasDerivAt_periodWelfare (χ κ0 a : ℝ) {C0 k0 : ℝ} (Y0 c m y : ℝ) (hC0 : 0 < C0)
    (hk0 : 0 < k0) :
    HasDerivAt (fun τ => periodWelfare χ (κ0 * (1 - τ * a)) (C0 * Real.exp (τ * c))
      (k0 * Real.exp (τ * m)) (Y0 * Real.exp (τ * y)))
      (c + χ * m - κ0 * Y0 ^ 2 * y + κ0 * Y0 ^ 2 * a / 2) 0 := by
  have h1 := hasDerivAt_log_exp_path (x := c) hC0
  have h2 := (hasDerivAt_log_exp_path (x := m) hk0).const_mul χ
  have h3 : HasDerivAt (fun τ => κ0 * (1 - τ * a) / 2) (κ0 * (-a) / 2) 0 := by
    have := (((hasDerivAt_id (0 : ℝ)).mul_const a).const_sub 1).const_mul κ0
    simpa using this.div_const 2
  have h4 : HasDerivAt (fun τ => (Y0 * Real.exp (τ * y)) ^ 2) (2 * (Y0 * (Y0 * y))) 0 := by
    have hY : HasDerivAt (fun τ => Y0 * Real.exp (τ * y)) (Y0 * y) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const y).exp.const_mul Y0
    convert hY.mul hY using 1
    · funext τ; simp only [Pi.mul_apply]; ring
    · simp only [zero_mul, Real.exp_zero]; ring
  have h := (h1.add h2).sub (h3.mul h4)
  convert h using 1
  · funext τ
    simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, periodWelfare]
  · simp only [zero_mul, Real.exp_zero, mul_one, sub_zero]
    ring

/-- **The derivative of lifetime utility** (T17; O&R p. 684): for a path at its new steady state
from date 2 (a two-regime path) with log-deviations `c, c̄` (consumption), `m, m̄` (real
balances), `ŷ, ȳ` (output) and a permanent effort-weight shock `κ = κ₀(1 − τa)`, the derivative
of the infinite sum `Σ β^s u_s` at `τ = 0` is `[c + χm − κ₀Y₀²ŷ + κ₀Y₀²a/2] +
(β/(1−β))[c̄ + χm̄ − κ₀Y₀²ȳ + κ₀Y₀²a/2]`. -/
theorem welfare_hasDerivAt {β : ℝ} (hβ0 : 0 ≤ β) (hβ1 : β < 1) (χ κ0 a : ℝ) {C0 k0 kb0 : ℝ}
    (Y0 c cb m mb y yb : ℝ) (hC0 : 0 < C0) (hk0 : 0 < k0) (hkb0 : 0 < kb0) :
    HasDerivAt (fun τ => lifetimeWelfare β χ (κ0 * (1 - τ * a))
      (twoRegime (C0 * Real.exp (τ * c)) (C0 * Real.exp (τ * cb)))
      (twoRegime (k0 * Real.exp (τ * m)) (kb0 * Real.exp (τ * mb)))
      (twoRegime (Y0 * Real.exp (τ * y)) (Y0 * Real.exp (τ * yb))))
      ((c + χ * m - κ0 * Y0 ^ 2 * y + κ0 * Y0 ^ 2 * a / 2) +
        β / (1 - β) * (cb + χ * mb - κ0 * Y0 ^ 2 * yb + κ0 * Y0 ^ 2 * a / 2)) 0 := by
  have e : (fun τ => lifetimeWelfare β χ (κ0 * (1 - τ * a))
      (twoRegime (C0 * Real.exp (τ * c)) (C0 * Real.exp (τ * cb)))
      (twoRegime (k0 * Real.exp (τ * m)) (kb0 * Real.exp (τ * mb)))
      (twoRegime (Y0 * Real.exp (τ * y)) (Y0 * Real.exp (τ * yb)))) =
      fun τ => periodWelfare χ (κ0 * (1 - τ * a)) (C0 * Real.exp (τ * c))
        (k0 * Real.exp (τ * m)) (Y0 * Real.exp (τ * y)) + β / (1 - β) *
        periodWelfare χ (κ0 * (1 - τ * a)) (C0 * Real.exp (τ * cb))
          (kb0 * Real.exp (τ * mb)) (Y0 * Real.exp (τ * yb)) := by
    funext τ
    exact lifetimeWelfare_twoRegime hβ0 hβ1 _ _ _ _ _ _ _ _
  rw [e]
  exact (hasDerivAt_periodWelfare χ κ0 a Y0 c m y hC0 hk0).add
    ((hasDerivAt_periodWelfare χ κ0 a Y0 cb mb yb hC0 hkb0).const_mul _)

/-- The first-order change in real utility, the right side of (75), O&R p. 684:
`dUᴿ = c − ((θ−1)/θ) y + (1/δ)[c̄ − ((θ−1)/θ) ȳ]`. -/
noncomputable def dUR (L : ReduxLinear) (c y cb yb : ℝ) : ℝ :=
  c - (L.θ - 1) / L.θ * y + 1 / L.δ * (cb - (L.θ - 1) / L.θ * yb)

/-- **(75) is the derivative of `Uᴿ`** (T17; O&R p. 684): around the symmetric steady state
`C̄₀ = ȳ₀`, along log-deviations `c, ŷ` on impact and `c̄, ȳ` from date 2, the derivative of
`Uᴿ = Σ β^s [log C_s − (κ/2)y_s²]` is `c − ((θ−1)/θ)ŷ + (1/δ)[c̄ − ((θ−1)/θ)ȳ]`, using
`Σ_{s≥1} β^s = 1/δ` and `κȳ₀² = (θ−1)/θ` (24). -/
theorem welfare_eq75 (M : ReduxParams) (c y cb yb : ℝ) :
    HasDerivAt (fun τ => realWelfare M.β M.κ
      (twoRegime (M.ybar0 * Real.exp (τ * c)) (M.ybar0 * Real.exp (τ * cb)))
      (twoRegime (M.ybar0 * Real.exp (τ * y)) (M.ybar0 * Real.exp (τ * yb))))
      (dUR (linearOf M) c y cb yb) 0 := by
  have h := welfare_hasDerivAt M.hβ0.le M.hβ1 0 M.κ 0 M.ybar0 c cb 0 0 y yb M.ybar0_pos one_pos
    one_pos
  have e : (fun τ => realWelfare M.β M.κ
      (twoRegime (M.ybar0 * Real.exp (τ * c)) (M.ybar0 * Real.exp (τ * cb)))
      (twoRegime (M.ybar0 * Real.exp (τ * y)) (M.ybar0 * Real.exp (τ * yb)))) =
      fun τ => lifetimeWelfare M.β 0 (M.κ * (1 - τ * 0))
      (twoRegime (M.ybar0 * Real.exp (τ * c)) (M.ybar0 * Real.exp (τ * cb)))
      (twoRegime (1 * Real.exp (τ * 0)) (1 * Real.exp (τ * 0)))
      (twoRegime (M.ybar0 * Real.exp (τ * y)) (M.ybar0 * Real.exp (τ * yb))) := by
    funext τ
    rw [realWelfare_eq]
    unfold lifetimeWelfare periodWelfare
    simp
  rw [e]
  convert h using 1
  unfold dUR linearOf
  simp only
  rw [beta_div_one_sub M, M.κ_mul_ybar0_sq]
  ring

/-- The real-balance component of the first-order utility change (O&R p. 684 and fn 19):
`χ[x + x̄/δ]`, where `x = m − p` is the impact log-deviation of real balances and `x̄ = m̄ − p̄`
the long-run one. -/
noncomputable def realBalanceTerm (L : ReduxLinear) (χ x xb : ℝ) : ℝ := χ * (x + 1 / L.δ * xb)

/-- **The total first-order utility change** (T17–T18; O&R p. 684): around the symmetric steady
state, the derivative of TOTAL lifetime utility (1), real balances included, along impact
log-deviations `c, x, ŷ` and long-run `c̄, x̄, ȳ` is `dUᴿ + χ[x + x̄/δ]`. -/
theorem total_welfare_hasDerivAt (M : ReduxParams) {k0 kb0 : ℝ} (c cb x xb y yb : ℝ)
    (hk0 : 0 < k0) (hkb0 : 0 < kb0) :
    HasDerivAt (fun τ => lifetimeWelfare M.β M.χ M.κ
      (twoRegime (M.ybar0 * Real.exp (τ * c)) (M.ybar0 * Real.exp (τ * cb)))
      (twoRegime (k0 * Real.exp (τ * x)) (kb0 * Real.exp (τ * xb)))
      (twoRegime (M.ybar0 * Real.exp (τ * y)) (M.ybar0 * Real.exp (τ * yb))))
      (dUR (linearOf M) c y cb yb + realBalanceTerm (linearOf M) M.χ x xb) 0 := by
  have h := welfare_hasDerivAt M.hβ0.le M.hβ1 M.χ M.κ 0 M.ybar0 c cb x xb y yb M.ybar0_pos hk0
    hkb0
  have e : (fun τ => lifetimeWelfare M.β M.χ M.κ
      (twoRegime (M.ybar0 * Real.exp (τ * c)) (M.ybar0 * Real.exp (τ * cb)))
      (twoRegime (k0 * Real.exp (τ * x)) (kb0 * Real.exp (τ * xb)))
      (twoRegime (M.ybar0 * Real.exp (τ * y)) (M.ybar0 * Real.exp (τ * yb)))) =
      fun τ => lifetimeWelfare M.β M.χ (M.κ * (1 - τ * 0))
      (twoRegime (M.ybar0 * Real.exp (τ * c)) (M.ybar0 * Real.exp (τ * cb)))
      (twoRegime (k0 * Real.exp (τ * x)) (kb0 * Real.exp (τ * xb)))
      (twoRegime (M.ybar0 * Real.exp (τ * y)) (M.ybar0 * Real.exp (τ * yb))) := by
    funext τ; simp
  rw [e]
  convert h using 1
  unfold dUR realBalanceTerm linearOf
  simp only
  rw [beta_div_one_sub M, M.κ_mul_ybar0_sq]
  ring

/-! ## (76): the welfare effect of money shocks is `mᵂ/θ` (T17) -/

/-- **The quasi-reduced forms**, O&R p. 685: in every money-shock equilibrium
`y = mᵂ + (1−n)θe`, `c = δ(1−n)(θ²−1)e/(δ(1+θ)+2θ) + mᵂ`,
`c̄ = δ(1−n)(θ²−1)e/(δ(1+θ)+2θ)` and `ȳ = −δθ(1−n)(θ−1)e/(δ(1+θ)+2θ)`. -/
theorem quasi_reduced_forms {L : ReduxLinear} {m ms : ℝ} {u : ShortVars} {v : SteadyVars}
    (h : MoneyShockEqm L m ms u v) :
    u.y = L.n * m + (1 - L.n) * ms + (1 - L.n) * L.θ * u.e ∧
    u.c = L.δ * (1 - L.n) * (L.θ ^ 2 - 1) / (L.δ * (1 + L.θ) + 2 * L.θ) * u.e +
      (L.n * m + (1 - L.n) * ms) ∧
    v.c = L.δ * (1 - L.n) * (L.θ ^ 2 - 1) / (L.δ * (1 + L.θ) + 2 * L.θ) * u.e ∧
    v.y = -(L.δ * L.θ * (1 - L.n) * (L.θ - 1) / (L.δ * (1 + L.θ) + 2 * L.θ)) * u.e := by
  obtain ⟨rfl, rfl⟩ := (moneyShock_iff L m ms u v).1 h
  have hθ := L.hθ
  have hδ := L.hδ
  have hθ0 : L.θ ≠ 0 := by linarith
  have hG : L.δ * (1 + L.θ) + 2 * L.θ ≠ 0 := by nlinarith
  have hE : L.δ * (1 + L.θ) + 2 ≠ 0 := L.E_pos.ne'
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [shortRunSolution, steadySolution, ReduxLinear.D, ReduxLinear.E] <;>
    field_simp <;> ring

/-- **Every exchange-rate term cancels, identically** (O&R p. 685): substituting the quasi-reduced
forms into (75) gives `mᵂ/θ` for EVERY value of `e`. -/
theorem welfare_e_cancels (L : ReduxLinear) (e mW : ℝ) :
    dUR L (L.δ * (1 - L.n) * (L.θ ^ 2 - 1) / (L.δ * (1 + L.θ) + 2 * L.θ) * e + mW)
      (mW + (1 - L.n) * L.θ * e)
      (L.δ * (1 - L.n) * (L.θ ^ 2 - 1) / (L.δ * (1 + L.θ) + 2 * L.θ) * e)
      (-(L.δ * L.θ * (1 - L.n) * (L.θ - 1) / (L.δ * (1 + L.θ) + 2 * L.θ)) * e) = mW / L.θ := by
  have hθ := L.hθ
  have hδ := L.hδ
  have hθ0 : L.θ ≠ 0 := by linarith
  have hδ0 : L.δ ≠ 0 := hδ.ne'
  have hG : L.δ * (1 + L.θ) + 2 * L.θ ≠ 0 := by nlinarith
  unfold dUR
  field_simp
  ring

/-- **(76)**, O&R p. 685 (T17): in every money-shock equilibrium the first-order change in Home
real utility is `dUᴿ = cᵂ/θ = mᵂ/θ`, and so is Foreign's ("regardless of its origin"). -/
theorem welfare_eq76 {L : ReduxLinear} {m ms : ℝ} {u : ShortVars} {v : SteadyVars}
    (h : MoneyShockEqm L m ms u v) :
    dUR L u.c u.y v.c v.y = (L.n * m + (1 - L.n) * ms) / L.θ ∧
    dUR L u.cs u.ys v.cs v.ys = (L.n * m + (1 - L.n) * ms) / L.θ ∧
    dUR L u.c u.y v.c v.y = u.cW / L.θ := by
  have hcW := (moneyShock_world h).2.1
  obtain ⟨rfl, rfl⟩ := (moneyShock_iff L m ms u v).1 h
  have hθ := L.hθ
  have hδ := L.hδ
  have hθ0 : L.θ ≠ 0 := by linarith
  have hδ0 : L.δ ≠ 0 := hδ.ne'
  have hn : 1 - L.n ≠ 0 := by linarith [L.hn1]
  have hE : L.δ * (1 + L.θ) + 2 ≠ 0 := L.E_pos.ne'
  refine ⟨?_, ?_, ?_⟩
  · simp only [dUR, shortRunSolution, steadySolution, ReduxLinear.D, ReduxLinear.E]
    field_simp; ring
  · simp only [dUR, shortRunSolution, steadySolution, ReduxLinear.D, ReduxLinear.E]
    field_simp; ring
  · rw [hcW]
    simp only [dUR, shortRunSolution, steadySolution, ReduxLinear.D, ReduxLinear.E]
    field_simp; ring

/-- **(76) as a derivative** (T17): in the nonlinear model, real utility `Uᴿ` along the
equilibrium response to a money shock (impact `c, ŷ`, long run `c̄, ȳ` from the unique solution
of the linear system) has derivative `mᵂ/θ` at the initial steady state, for Home and Foreign. -/
theorem welfare_eq76_hasDerivAt (M : ReduxParams) {m ms : ℝ} {u : ShortVars} {v : SteadyVars}
    (h : MoneyShockEqm (linearOf M) m ms u v) :
    HasDerivAt (fun τ => realWelfare M.β M.κ
      (twoRegime (M.ybar0 * Real.exp (τ * u.c)) (M.ybar0 * Real.exp (τ * v.c)))
      (twoRegime (M.ybar0 * Real.exp (τ * u.y)) (M.ybar0 * Real.exp (τ * v.y))))
      ((M.n * m + (1 - M.n) * ms) / M.θ) 0 ∧
    HasDerivAt (fun τ => realWelfare M.β M.κ
      (twoRegime (M.ybar0 * Real.exp (τ * u.cs)) (M.ybar0 * Real.exp (τ * v.cs)))
      (twoRegime (M.ybar0 * Real.exp (τ * u.ys)) (M.ybar0 * Real.exp (τ * v.ys))))
      ((M.n * m + (1 - M.n) * ms) / M.θ) 0 := by
  obtain ⟨h1, h2, -⟩ := welfare_eq76 h
  refine ⟨?_, ?_⟩
  · have := welfare_eq75 M u.c u.y v.c v.y
    rwa [h1] at this
  · have := welfare_eq75 M u.cs u.ys v.cs v.ys
    rwa [h2] at this

/-! ## Real balances: the exact meaning of "χ not too large" (T18, p. 684, fn 19) -/

/-- **Total first-order welfare of a Foreign monetary expansion** (T18; O&R p. 684, fn 19): with
`m = 0`, Home's total utility change, real balances included (`x = m − p`, `x̄ = m̄ − p̄`), is
`(1−n)m*[(δ(1+θ)+2) + χ(δ(1+θ)+2θ+1−θ²)]/D`. -/
theorem foreign_shock_total {L : ReduxLinear} {ms : ℝ} {u : ShortVars} {v : SteadyVars}
    (h : MoneyShockEqm L 0 ms u v) (χ : ℝ) :
    dUR L u.c u.y v.c v.y + realBalanceTerm L χ (0 - u.p) (0 - v.p) =
      (1 - L.n) * ms * (L.E + χ * (L.δ * (1 + L.θ) + 2 * L.θ + 1 - L.θ ^ 2)) / L.D := by
  obtain ⟨rfl, rfl⟩ := (moneyShock_iff L 0 ms u v).1 h
  have hθ := L.hθ
  have hδ := L.hδ
  have hθ0 : L.θ ≠ 0 := by linarith
  have hδ0 : L.δ ≠ 0 := hδ.ne'
  have hE : L.δ * (1 + L.θ) + 2 ≠ 0 := L.E_pos.ne'
  simp only [dUR, realBalanceTerm, shortRunSolution, steadySolution, ReduxLinear.D,
    ReduxLinear.E]
  field_simp
  ring

/-- The exact threshold function of T18: `A = θ² − 2θ − 1 − δ(1+θ)`; the real-balance
coefficient in `foreign_shock_total` is `−A` (O&R fn 19). -/
theorem realBalance_coef (L : ReduxLinear) :
    L.δ * (1 + L.θ) + 2 * L.θ + 1 - L.θ ^ 2 = -(L.θ ^ 2 - 2 * L.θ - 1 - L.δ * (1 + L.θ)) := by
  ring

/-- **The sign of the Foreign-expansion welfare effect** (T18): for `m* > 0`, total Home welfare
rises IFF `χ(θ² − 2θ − 1 − δ(1+θ)) < δ(1+θ) + 2`. -/
theorem foreign_shock_welfare_pos_iff {L : ReduxLinear} {ms : ℝ} {u : ShortVars}
    {v : SteadyVars} (h : MoneyShockEqm L 0 ms u v) (hms : 0 < ms) (χ : ℝ) :
    0 < dUR L u.c u.y v.c v.y + realBalanceTerm L χ (0 - u.p) (0 - v.p) ↔
      χ * (L.θ ^ 2 - 2 * L.θ - 1 - L.δ * (1 + L.θ)) < L.E := by
  rw [foreign_shock_total h χ, realBalance_coef]
  have hD := L.D_pos
  have hn : 0 < 1 - L.n := by linarith [L.hn1]
  have hk : 0 < (1 - L.n) * ms := mul_pos hn hms
  rw [lt_div_iff₀ hD, zero_mul]
  constructor
  · intro h1
    by_contra h2
    push Not at h2
    have : L.E + χ * -(L.θ ^ 2 - 2 * L.θ - 1 - L.δ * (1 + L.θ)) ≤ 0 := by linarith
    nlinarith
  · intro h1
    have : 0 < L.E + χ * -(L.θ ^ 2 - 2 * L.θ - 1 - L.δ * (1 + L.θ)) := by linarith
    positivity

/-- **When is "χ not too large" vacuous?** (T18; O&R p. 684): for `m* > 0`, a Foreign expansion
raises total Home welfare for EVERY `χ ≥ 0` IFF `θ² − 2θ − 1 ≤ δ(1+θ)`. -/
theorem welfare_pos_forall_chi_iff {L : ReduxLinear} {ms : ℝ} {u : ShortVars} {v : SteadyVars}
    (h : MoneyShockEqm L 0 ms u v) (hms : 0 < ms) :
    (∀ χ, 0 ≤ χ → 0 < dUR L u.c u.y v.c v.y + realBalanceTerm L χ (0 - u.p) (0 - v.p)) ↔
      L.θ ^ 2 - 2 * L.θ - 1 ≤ L.δ * (1 + L.θ) := by
  have hE := L.E_pos
  constructor
  · intro hall
    by_contra hA
    push Not at hA
    have hA' : 0 < L.θ ^ 2 - 2 * L.θ - 1 - L.δ * (1 + L.θ) := by linarith
    have h1 := (foreign_shock_welfare_pos_iff h hms _).1
      (hall (L.E / (L.θ ^ 2 - 2 * L.θ - 1 - L.δ * (1 + L.θ))) (div_pos hE hA').le)
    rw [div_mul_cancel₀ _ hA'.ne'] at h1
    exact lt_irrefl _ h1
  · intro hA χ hχ
    rw [foreign_shock_welfare_pos_iff h hms]
    have : χ * (L.θ ^ 2 - 2 * L.θ - 1 - L.δ * (1 + L.θ)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hχ (by linarith)
    linarith

/-- **The exact threshold** (T18; O&R p. 684, "as long as χ is not too large"): if
`θ² − 2θ − 1 > δ(1+θ)`, a Foreign expansion (`m* > 0`) raises total Home welfare IFF
`χ < (δ(1+θ)+2)/(θ² − 2θ − 1 − δ(1+θ))`. -/
theorem welfare_threshold {L : ReduxLinear} {ms : ℝ} {u : ShortVars} {v : SteadyVars}
    (h : MoneyShockEqm L 0 ms u v) (hms : 0 < ms)
    (hA : L.δ * (1 + L.θ) < L.θ ^ 2 - 2 * L.θ - 1) (χ : ℝ) :
    0 < dUR L u.c u.y v.c v.y + realBalanceTerm L χ (0 - u.p) (0 - v.p) ↔
      χ < L.E / (L.θ ^ 2 - 2 * L.θ - 1 - L.δ * (1 + L.θ)) := by
  rw [foreign_shock_welfare_pos_iff h hms, lt_div_iff₀ (by linarith)]

/-- **No threshold for moderate substitutability** (T18): if `1 < θ ≤ 1 + √2` then
`θ² − 2θ − 1 ≤ 0 < δ(1+θ)`, so the Foreign-expansion welfare gain is positive for every `χ`. -/
theorem no_threshold_of_le {θ δ : ℝ} (hθ : 1 < θ) (hδ : 0 < δ) (hθ2 : θ ≤ 1 + Real.sqrt 2) :
    θ ^ 2 - 2 * θ - 1 < δ * (1 + θ) := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have h1 : θ - 1 ≤ Real.sqrt 2 := by linarith
  have h2 : (θ - 1) ^ 2 ≤ 2 := by
    have : 0 ≤ θ - 1 := by linarith
    nlinarith
  nlinarith

/-- The linear model at `θ = 6`, `δ = 0.05`, `n = 1/2` (O&R p. 684; the survey's counterexample to
an unconditional reading of "χ not too large"). -/
noncomputable def counterexampleModel : ReduxLinear :=
  ⟨6, 0.05, 1 / 2, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- **Counterexample: a Foreign expansion can LOWER Home welfare** (T18; O&R p. 684, fn 19): at
`θ = 6`, `δ = 0.05`, the threshold `(δ(1+θ)+2)/(θ²−2θ−1−δ(1+θ)) = 2.35/22.65` lies in
`(0.10, 0.11)`; with `χ = 0.2` every equilibrium of a Foreign expansion `m* > 0` has
`dUᴿ + χ[x + x̄/δ] = −(109/1410)m* < 0`, and such an equilibrium exists. -/
theorem counterexample_theta6 :
    (0.10 : ℝ) < (0.05 * (1 + 6) + 2) / (6 ^ 2 - 2 * 6 - 1 - 0.05 * (1 + 6)) ∧
    (0.05 * (1 + 6) + 2) / (6 ^ 2 - 2 * 6 - 1 - 0.05 * (1 + 6)) < (0.11 : ℝ) ∧
    (∀ ms : ℝ, 0 < ms → ∀ u v, MoneyShockEqm counterexampleModel 0 ms u v →
      dUR counterexampleModel u.c u.y v.c v.y +
        realBalanceTerm counterexampleModel 0.2 (0 - u.p) (0 - v.p) = -(109 / 1410) * ms ∧
      dUR counterexampleModel u.c u.y v.c v.y +
        realBalanceTerm counterexampleModel 0.2 (0 - u.p) (0 - v.p) < 0) ∧
    ∃ u v, MoneyShockEqm counterexampleModel 0 1 u v := by
  refine ⟨by norm_num, by norm_num, fun ms hms u v h => ?_, ?_⟩
  · have e := foreign_shock_total h 0.2
    have e2 : dUR counterexampleModel u.c u.y v.c v.y +
        realBalanceTerm counterexampleModel 0.2 (0 - u.p) (0 - v.p) = -(109 / 1410) * ms := by
      rw [e]
      simp only [counterexampleModel, ReduxLinear.D, ReduxLinear.E]
      norm_num
      ring
    exact ⟨e2, by rw [e2]; linarith⟩
  · obtain ⟨w, hw, -⟩ := moneyShock_existsUnique counterexampleModel 0 1
    exact ⟨w.1, w.2, hw⟩

/-- **fn 19: a Home expansion raises Home real balances in every period** (O&R p. 685, fn 19):
with `m > 0 = m*`, `m − p > 0` on impact and `m̄ − p̄ = c̄ > 0` in the long run; hence every
component of Home welfare rises, and total welfare rises for every `χ ≥ 0`. -/
theorem home_shock_real_balances {L : ReduxLinear} {m : ℝ} {u : ShortVars} {v : SteadyVars}
    (h : MoneyShockEqm L m 0 u v) (hm : 0 < m) (χ : ℝ) (hχ : 0 ≤ χ) :
    0 < m - u.p ∧ 0 < m - v.p ∧
      0 < dUR L u.c u.y v.c v.y + realBalanceTerm L χ (m - u.p) (m - v.p) := by
  have h76 := (welfare_eq76 h).1
  obtain ⟨rfl, rfl⟩ := (moneyShock_iff L m 0 u v).1 h
  have hθ := L.hθ
  have hδ := L.hδ
  have hn0 := L.hn0
  have hn : 0 < 1 - L.n := by linarith [L.hn1]
  have hD := L.D_pos
  have hE := L.E_pos
  have hsq : 0 < L.θ ^ 2 - 1 := by nlinarith
  have hθ1 : 0 < L.θ - 1 := by linarith
  have h1 : 0 < m - (shortRunSolution L m 0).p := by
    simp only [shortRunSolution]
    have e : m - (1 - L.n) * ((L.δ * (1 + L.θ) + 2 * L.θ) * (m - 0) / L.D) =
        L.n * m + (1 - L.n) * (L.δ * (L.θ ^ 2 - 1) * m / L.D) := by
      unfold ReduxLinear.D; field_simp; ring
    rw [e]; positivity
  have h2 : 0 < m - (steadySolution L (shortRunSolution L m 0).b m 0).p := by
    simp only [steadySolution, shortRunSolution]
    have : 0 < (1 + L.θ) * L.δ * (2 * (1 - L.n) * (L.θ - 1) * (m - 0) / L.E) / (2 * L.θ) := by
      have : 0 < m - 0 := by linarith
      positivity
    linarith
  refine ⟨h1, h2, ?_⟩
  rw [h76]
  unfold realBalanceTerm
  have : 0 ≤ χ * (m - (shortRunSolution L m 0).p +
      1 / L.δ * (m - (steadySolution L (shortRunSolution L m 0).b m 0).p)) := by positivity
  have : 0 < (L.n * m + (1 - L.n) * 0) / L.θ := by
    have : 0 < L.θ := by linarith
    simp only [mul_zero, add_zero]
    positivity
  linarith

/-- **fn 19: a Foreign expansion raises Home real balances in the short run and lowers them in
the long run** (O&R p. 685, fn 19): with `m = 0 < m*`, `0 − p > 0` (Home's currency appreciates)
but `0 − p̄ < 0` (the long-run Home price level rises). -/
theorem foreign_shock_real_balances {L : ReduxLinear} {ms : ℝ} {u : ShortVars} {v : SteadyVars}
    (h : MoneyShockEqm L 0 ms u v) (hms : 0 < ms) : 0 < 0 - u.p ∧ 0 - v.p < 0 := by
  obtain ⟨rfl, rfl⟩ := (moneyShock_iff L 0 ms u v).1 h
  have hθ := L.hθ
  have hδ := L.hδ
  have hn : 0 < 1 - L.n := by linarith [L.hn1]
  have hD := L.D_pos
  have hE := L.E_pos
  have hθ1 : 0 < L.θ - 1 := by linarith
  have hG : 0 < L.δ * (1 + L.θ) + 2 * L.θ := by positivity
  constructor
  · simp only [shortRunSolution]
    have : 0 < (1 - L.n) * ((L.δ * (1 + L.θ) + 2 * L.θ) * ms / L.D) := by positivity
    have e : (1 - L.n) * ((L.δ * (1 + L.θ) + 2 * L.θ) * (0 - ms) / L.D) =
        -((1 - L.n) * ((L.δ * (1 + L.θ) + 2 * L.θ) * ms / L.D)) := by ring
    rw [e]; linarith
  · simp only [steadySolution, shortRunSolution]
    have : 0 < (1 + L.θ) * L.δ * (2 * (1 - L.n) * (L.θ - 1) * ms / L.E) / (2 * L.θ) := by
      positivity
    have e : (1 + L.θ) * L.δ * (2 * (1 - L.n) * (L.θ - 1) * (0 - ms) / L.E) / (2 * L.θ) =
        -((1 + L.θ) * L.δ * (2 * (1 - L.n) * (L.θ - 1) * ms / L.E) / (2 * L.θ)) := by ring
    rw [e]; linarith

/-! ## Menu costs and demand-determined output (T20, p. 674) -/

/-- The producer's one-period payoff in utility units as a function of output, O&R p. 665 and
p. 674: real revenue `y^{(θ−1)/θ} (Cᵂ)^{1/θ}` (on the demand curve (10)) valued at the marginal
utility `1/C`, minus the disutility of effort `(κ/2) y²`. -/
noncomputable def producerPayoff (θ κ X C y : ℝ) : ℝ :=
  y ^ ((θ - 1) / θ) * X ^ (1 / θ) / C - κ / 2 * y ^ 2

/-- The marginal payoff `ρ y^{ρ−1} X^{1/θ}/C − κ y`, `ρ = (θ−1)/θ` (O&R (15)). -/
noncomputable def marginalPayoff (θ κ X C y : ℝ) : ℝ :=
  (θ - 1) / θ * y ^ ((θ - 1) / θ - 1) * X ^ (1 / θ) / C - κ * y

/-- **At a price `π`, the payoff is revenue minus effort** (O&R p. 665): if `y = π^{−θ} Cᵂ`
then `producerPayoff = π y/C − (κ/2) y²`. -/
theorem producerPayoff_at_price {θ κ X C q : ℝ} (hθ : θ ≠ 0) (hX : 0 < X) (hq : 0 < q) :
    producerPayoff θ κ X C (cesDemand θ q 1 X) =
      q * cesDemand θ q 1 X / C - κ / 2 * cesDemand θ q 1 X ^ 2 := by
  have hy : 0 < cesDemand θ q 1 X := cesDemand_pos θ hq one_pos hX
  have h := revenue_on_demand hθ hq hy hX rfl
  unfold producerPayoff
  rw [← h]

/-- **The payoff lies below its tangent parabola** (T20; strict concavity of `y ↦ y^ρ`): for
`y₁ > 0`, `y ≥ 0`, `W(y) ≤ W(y₁) + W′(y₁)(y − y₁) − (κ/2)(y − y₁)²`. -/
theorem producerPayoff_le {θ κ X C y1 y : ℝ} (hθ : 1 < θ) (hX : 0 < X) (hC : 0 < C)
    (hy1 : 0 < y1) (hy : 0 ≤ y) :
    producerPayoff θ κ X C y ≤ producerPayoff θ κ X C y1 + marginalPayoff θ κ X C y1 * (y - y1) -
      κ / 2 * (y - y1) ^ 2 := by
  have hρ0 : 0 < (θ - 1) / θ := div_pos (by linarith) (by linarith)
  have hρ1 : (θ - 1) / θ < 1 := by rw [div_lt_one (by linarith)]; linarith
  have ht := rpow_le_tangent hρ0 hρ1 hy1 hy
  have hA : 0 ≤ X ^ (1 / θ) / C := div_nonneg (rpow_nonneg hX.le _) hC.le
  have key := mul_le_mul_of_nonneg_right ht hA
  have e : producerPayoff θ κ X C y1 + marginalPayoff θ κ X C y1 * (y - y1) -
      κ / 2 * (y - y1) ^ 2 - producerPayoff θ κ X C y =
      ((y1 ^ ((θ - 1) / θ) + (θ - 1) / θ * y1 ^ ((θ - 1) / θ - 1) * (y - y1)) *
        (X ^ (1 / θ) / C) - y ^ ((θ - 1) / θ) * (X ^ (1 / θ) / C)) := by
    unfold producerPayoff marginalPayoff; ring
  linarith

/-- **The gain from re-optimising is at most `W′(y₁)²/(2κ)`** (T20(a)): for `κ > 0`, a producer
at output `y₁ > 0` gains at most `(marginal payoff)²/(2κ)` by moving to any other output. -/
theorem gain_le_sq {θ κ X C y1 y : ℝ} (hθ : 1 < θ) (hκ : 0 < κ) (hX : 0 < X) (hC : 0 < C)
    (hy1 : 0 < y1) (hy : 0 ≤ y) :
    producerPayoff θ κ X C y - producerPayoff θ κ X C y1 ≤
      marginalPayoff θ κ X C y1 ^ 2 / (2 * κ) := by
  have h := producerPayoff_le (κ := κ) hθ hX hC hy1 hy
  set g := marginalPayoff θ κ X C y1
  have e : g * (y - y1) - κ / 2 * (y - y1) ^ 2 =
      g ^ 2 / (2 * κ) - (g - κ * (y - y1)) ^ 2 / (2 * κ) := by field_simp; ring
  have : 0 ≤ (g - κ * (y - y1)) ^ 2 / (2 * κ) := by positivity
  linarith

/-- **The optimum is the labour–leisure condition (15)** (O&R p. 665; T20): output `y₁ > 0` is a
global maximiser of the producer's payoff IFF `W′(y₁) = 0`. -/
theorem producerPayoff_isMax_iff {θ κ X C y1 : ℝ} (hθ : 1 < θ) (hκ : 0 < κ) (hX : 0 < X)
    (hC : 0 < C) (hy1 : 0 < y1) :
    (∀ y, 0 ≤ y → producerPayoff θ κ X C y ≤ producerPayoff θ κ X C y1) ↔
      marginalPayoff θ κ X C y1 = 0 := by
  constructor
  · intro hmax
    have hd : HasDerivAt (producerPayoff θ κ X C) (marginalPayoff θ κ X C y1) y1 := by
      have h1 := ((Real.hasDerivAt_rpow_const (p := (θ - 1) / θ) (Or.inl hy1.ne')).mul_const
        (X ^ (1 / θ))).div_const C
      have h2 := (hasDerivAt_pow 2 y1).const_mul (κ / 2)
      have h := h1.sub h2
      convert h using 1
      · funext y; simp [producerPayoff]
      · unfold marginalPayoff; simp; ring
    have hloc : IsLocalMax (producerPayoff θ κ X C) y1 := by
      filter_upwards [lt_mem_nhds hy1] with y hy
      exact hmax y hy.le
    exact hloc.hasDerivAt_eq_zero hd
  · intro h0 y hy
    have := producerPayoff_le (κ := κ) hθ hX hC hy1 hy
    rw [h0, zero_mul, add_zero] at this
    have : 0 ≤ κ / 2 * (y - y1) ^ 2 := by positivity
    linarith

/-- **The marginal payoff at a preset price** (T20): at the demand `y = π₀^{−θ}X` for a preset
relative price `π₀`, the marginal payoff is `ρ π₀/C − κ π₀^{−θ} X` (marginal revenue in real
terms is the constant `ρ π₀`). -/
theorem marginalPayoff_at_demand {θ κ X C π0 : ℝ} (hθ : θ ≠ 0) (hX : 0 < X) (hπ0 : 0 < π0) :
    marginalPayoff θ κ X C (π0 ^ (-θ) * X) = (θ - 1) / θ * π0 / C - κ * (π0 ^ (-θ) * X) := by
  unfold marginalPayoff
  have e1 : (θ - 1) / θ - 1 = -(1 / θ) := by field_simp; ring
  have e2 : (π0 ^ (-θ) * X) ^ (-(1 / θ)) * X ^ (1 / θ) = π0 := by
    rw [mul_rpow (rpow_nonneg hπ0.le _) hX.le, ← rpow_mul hπ0.le, rpow_neg hX.le]
    have : -θ * -(1 / θ) = 1 := by field_simp
    rw [this, rpow_one]
    have := (rpow_pos_of_pos hX (1 / θ)).ne'
    field_simp
  rw [e1]
  have e3 : (θ - 1) / θ * (π0 ^ (-θ) * X) ^ (-(1 / θ)) * X ^ (1 / θ) / C =
      (θ - 1) / θ * ((π0 ^ (-θ) * X) ^ (-(1 / θ)) * X ^ (1 / θ)) / C := by ring
  rw [e3, e2]

/-- **The menu-cost rationale, precisely: the private gain from adjusting a preset price is
SECOND order** (T20(a); O&R p. 674, "small changes in an individual's price will have only a
second-order impact"). Let the relative price `π₀` be optimal at the base aggregates
`(X₀, C₀)` (`ρπ₀/C₀ = κπ₀^{−θ}X₀`, i.e. (15)), and let the aggregates move along
`X = X₀e^{τa}`, `C = C₀e^{τb}`. Keeping the price, the producer sells `π₀^{−θ}X`; there is a
constant `K` such that for all small `τ` NO output (equivalently no price) does better by more than
`Kτ²`. -/
theorem menu_cost_second_order {θ κ π0 X0 C0 : ℝ} (hθ : 1 < θ) (hκ : 0 < κ) (hπ0 : 0 < π0)
    (hX0 : 0 < X0) (hC0 : 0 < C0) (hopt : (θ - 1) / θ * π0 / C0 = κ * (π0 ^ (-θ) * X0))
    (a b : ℝ) :
    ∃ K, ∀ᶠ τ in 𝓝 (0 : ℝ), ∀ y, 0 ≤ y →
      producerPayoff θ κ (X0 * Real.exp (τ * a)) (C0 * Real.exp (τ * b)) y -
        producerPayoff θ κ (X0 * Real.exp (τ * a)) (C0 * Real.exp (τ * b))
          (π0 ^ (-θ) * (X0 * Real.exp (τ * a))) ≤ K * τ ^ 2 := by
  have hθ0 : θ ≠ 0 := by linarith
  set g : ℝ → ℝ := fun τ => (θ - 1) / θ * π0 / C0 * Real.exp (τ * (-b)) -
    κ * (π0 ^ (-θ) * X0) * Real.exp (τ * a) with hg
  have hgeq : ∀ τ, marginalPayoff θ κ (X0 * Real.exp (τ * a)) (C0 * Real.exp (τ * b))
      (π0 ^ (-θ) * (X0 * Real.exp (τ * a))) = g τ := by
    intro τ
    rw [marginalPayoff_at_demand hθ0 (mul_pos hX0 (Real.exp_pos _)) hπ0]
    simp only [hg]
    rw [show τ * -b = -(τ * b) by ring, Real.exp_neg]
    field_simp
  have hg0 : g 0 = 0 := by simp only [hg]; simp [hopt]
  have hgd : HasDerivAt g ((θ - 1) / θ * π0 / C0 * (-b) - κ * (π0 ^ (-θ) * X0) * a) 0 := by
    have h1 := ((hasDerivAt_id (0 : ℝ)).mul_const (-b)).exp.const_mul ((θ - 1) / θ * π0 / C0)
    have h2 := ((hasDerivAt_id (0 : ℝ)).mul_const a).exp.const_mul (κ * (π0 ^ (-θ) * X0))
    convert h1.sub h2 using 1
    · funext τ; simp only [hg, Pi.sub_apply, id_eq]
    · simp
  set g' := (θ - 1) / θ * π0 / C0 * (-b) - κ * (π0 ^ (-θ) * X0) * a
  have hlo := (hasDerivAt_iff_isLittleO.1 hgd).def (show (0 : ℝ) < 1 by norm_num)
  refine ⟨(|g'| + 1) ^ 2 / (2 * κ), ?_⟩
  filter_upwards [hlo] with τ hτ y hy
  have hb : |g τ| ≤ (|g'| + 1) * |τ| := by
    rw [hg0, sub_zero, sub_zero, smul_eq_mul, one_mul, Real.norm_eq_abs, Real.norm_eq_abs] at hτ
    have := abs_sub_abs_le_abs_sub (g τ) (τ * g')
    rw [abs_mul] at this
    nlinarith [abs_nonneg τ, abs_nonneg g']
  have hX : 0 < X0 * Real.exp (τ * a) := mul_pos hX0 (Real.exp_pos _)
  have hC : 0 < C0 * Real.exp (τ * b) := mul_pos hC0 (Real.exp_pos _)
  have hy1 : 0 < π0 ^ (-θ) * (X0 * Real.exp (τ * a)) := mul_pos (rpow_pos_of_pos hπ0 _) hX
  have hgain := gain_le_sq (κ := κ) hθ hκ hX hC hy1 hy
  rw [hgeq τ] at hgain
  have hsq : g τ ^ 2 ≤ ((|g'| + 1) * |τ|) ^ 2 := by
    rw [← sq_abs (g τ)]
    exact pow_le_pow_left₀ (abs_nonneg _) hb 2
  have : g τ ^ 2 / (2 * κ) ≤ (|g'| + 1) ^ 2 / (2 * κ) * τ ^ 2 := by
    rw [div_mul_eq_mul_div, div_le_div_iff_of_pos_right (by positivity)]
    calc g τ ^ 2 ≤ ((|g'| + 1) * |τ|) ^ 2 := hsq
      _ = (|g'| + 1) ^ 2 * τ ^ 2 := by rw [mul_pow, sq_abs]
  linarith

/-- **Any menu cost deters adjustment for small enough shocks** (T20(a); O&R p. 674, "producers
will not necessarily find it profitable to change prices in the face of sufficiently small demand
shocks"): for every menu cost `Z > 0`, for all small enough `τ` the gain from changing the preset
price is below `Z`. -/
theorem menu_cost_rationale {θ κ π0 X0 C0 : ℝ} (hθ : 1 < θ) (hκ : 0 < κ) (hπ0 : 0 < π0)
    (hX0 : 0 < X0) (hC0 : 0 < C0) (hopt : (θ - 1) / θ * π0 / C0 = κ * (π0 ^ (-θ) * X0))
    (a b Z : ℝ) (hZ : 0 < Z) :
    ∀ᶠ τ in 𝓝 (0 : ℝ), ∀ y, 0 ≤ y →
      producerPayoff θ κ (X0 * Real.exp (τ * a)) (C0 * Real.exp (τ * b)) y -
        producerPayoff θ κ (X0 * Real.exp (τ * a)) (C0 * Real.exp (τ * b))
          (π0 ^ (-θ) * (X0 * Real.exp (τ * a))) < Z := by
  obtain ⟨K, hK⟩ := menu_cost_second_order hθ hκ hπ0 hX0 hC0 hopt a b
  have hc : Tendsto (fun τ : ℝ => K * τ ^ 2) (𝓝 0) (𝓝 (K * 0 ^ 2)) :=
    ((continuous_const.mul (continuous_pow 2)).tendsto 0)
  rw [show K * (0 : ℝ) ^ 2 = 0 by ring] at hc
  filter_upwards [hK, hc.eventually (gt_mem_nhds hZ)] with τ h1 h2 y hy
  exact lt_of_le_of_lt (h1 y hy) h2

/-- **Meeting demand at a preset price is optimal IFF price covers marginal cost** (T20(b);
O&R p. 674): a producer with a fixed real price `q > 0` facing demand `y_d` can sell any
`y ∈ [0, y_d]`; producing `y_d` is optimal IFF `κ y_d ≤ q/C` (marginal disutility at `y_d` does
not exceed the marginal revenue `q` valued at `1/C`). -/
theorem meet_demand_iff {q C κ yd : ℝ} (hq : 0 < q) (hC : 0 < C) (hκ : 0 < κ) :
    (∀ y, 0 ≤ y → y ≤ yd → q * y / C - κ / 2 * y ^ 2 ≤ q * yd / C - κ / 2 * yd ^ 2) ↔
      κ * yd ≤ q / C := by
  constructor
  · intro h
    by_contra hlt
    push Not at hlt
    set y := q / C / κ with hy
    have hyle : y < yd := by rw [hy, div_lt_iff₀ hκ]; linarith
    have hy0 : 0 ≤ y := by positivity
    have := h y hy0 hyle.le
    have e : q * yd / C - κ / 2 * yd ^ 2 - (q * y / C - κ / 2 * y ^ 2) =
        -(κ / 2) * (yd - y) ^ 2 := by
      rw [hy]; field_simp; ring
    have : 0 < (κ / 2) * (yd - y) ^ 2 := by
      have : 0 < yd - y := by linarith
      positivity
    linarith
  · intro h y hy0 hyle
    have e : q * yd / C - κ / 2 * yd ^ 2 - (q * y / C - κ / 2 * y ^ 2) =
        (yd - y) * (q / C - κ / 2 * (yd + y)) := by field_simp; ring
    have h1 : 0 ≤ yd - y := by linarith
    have h2 : 0 ≤ q / C - κ / 2 * (yd + y) := by nlinarith
    nlinarith [mul_nonneg h1 h2]

/-- **At the initial steady state price strictly exceeds marginal cost** (O&R p. 674: "under
monopoly, prices are set above marginal cost"): with `q = 1`, `C = y = ȳ₀`, `κȳ₀ < 1/ȳ₀`, and
the markup of price over marginal cost is exactly `θ/(θ−1)`. -/
theorem steady_price_exceeds_mc (M : ReduxParams) :
    M.κ * M.ybar0 < 1 / M.ybar0 ∧ (1 / M.ybar0) / (M.κ * M.ybar0) = M.θ / (M.θ - 1) := by
  have hy := M.ybar0_pos
  have hk := M.κ_mul_ybar0_sq
  have hθ := M.hθ
  have hθ1 : M.θ - 1 ≠ 0 := by linarith
  have hθ0 : M.θ ≠ 0 := by linarith
  constructor
  · rw [lt_div_iff₀ hy]
    have : M.κ * M.ybar0 * M.ybar0 = (M.θ - 1) / M.θ := by rw [← hk]; ring
    rw [this, div_lt_one (by linarith)]
    linarith
  · have e : (1 / M.ybar0) / (M.κ * M.ybar0) = 1 / (M.κ * M.ybar0 ^ 2) := by
      have := M.hκ.ne'
      field_simp
    rw [e, hk]
    field_simp

/-! ## Distorting income taxes (77)–(81) (T21) -/

/-- **Rebated income taxes leave the budget unchanged** (O&R (77)–(78), p. 686–687): the
household budget (77) with income tax `τᴸ` and the government budget (78) with lump-sum rebate
`τ` combine to `P B′ = P(1+r)B + p y − P C`, the same as (8) with (9). -/
theorem tax_budget_rebate {P B B1 M Mprev r τL py C τ : ℝ} (hP : P ≠ 0)
    (h77 : P * B1 + M = P * (1 + r) * B + Mprev + (1 - τL) * py - P * C - P * τ)
    (h78 : 0 = τ + τL * py / P + (M - Mprev) / P) :
    P * B1 = P * (1 + r) * B + py - P * C := by
  have h : P * τ = -(τL * py) - (M - Mprev) := by
    have := congrArg (fun z => P * z) h78
    simp only [mul_zero] at this
    field_simp at this
    linarith
  linear_combination h77 - h

/-- **(80): steady-state output with an income tax**, O&R p. 687 (T21): in a symmetric steady
state (`y = C = Cᵂ`), the taxed labour condition (79)
`y^{(θ+1)/θ} = (1−τᴸ)((θ−1)/(θκ))(Cᵂ)^{1/θ}/C` holds IFF `y = [(θ−1)(1−τᴸ)/(θκ)]^{1/2}`. -/
theorem taxed_symmetric_output {θ κ τL y : ℝ} (hθ : 1 < θ) (hy : 0 < y) :
    y ^ ((θ + 1) / θ) = (1 - τL) * ((θ - 1) / (θ * κ)) * y ^ (1 / θ) / y ↔
      y = Real.sqrt ((θ - 1) * (1 - τL) / (θ * κ)) := by
  have hθ0 : θ ≠ 0 := by linarith
  rw [rpow_succ_div hθ0 hy]
  have hr := (rpow_pos_of_pos hy (1 / θ)).ne'
  have hK : (θ - 1) * (1 - τL) / (θ * κ) = (1 - τL) * ((θ - 1) / (θ * κ)) := by ring
  have e : (y * y ^ (1 / θ) = (1 - τL) * ((θ - 1) / (θ * κ)) * y ^ (1 / θ) / y) ↔
      y ^ 2 = (θ - 1) * (1 - τL) / (θ * κ) := by
    rw [hK, eq_div_iff hy.ne']
    constructor
    · intro h
      have h2 : (y ^ 2 - (1 - τL) * ((θ - 1) / (θ * κ))) * y ^ (1 / θ) = 0 := by
        linear_combination h
      have := (mul_eq_zero.1 h2).resolve_right hr
      linarith
    · intro h
      rw [← h]; ring
  rw [e]
  constructor
  · intro h; rw [← h, Real.sqrt_sq hy.le]
  · intro h
    have h0 : 0 ≤ (θ - 1) * (1 - τL) / (θ * κ) := by
      by_contra hneg
      push Not at hneg
      rw [Real.sqrt_eq_zero'.2 hneg.le] at h
      linarith
    rw [h, Real.sq_sqrt h0]

/-- **An income tax lowers steady-state output** (O&R p. 687): `τᴸ ↦ [(θ−1)(1−τᴸ)/(θκ)]^{1/2}` is
strictly decreasing on `τᴸ ≤ 1`. -/
theorem taxed_output_strictAntiOn {θ κ : ℝ} (hθ : 1 < θ) (hκ : 0 < κ) :
    StrictAntiOn (fun τL : ℝ => Real.sqrt ((θ - 1) * (1 - τL) / (θ * κ))) (Set.Iic 1) := by
  intro a ha b hb hab
  have ha' : a ≤ 1 := ha
  have hb' : b ≤ 1 := hb
  have hk : 0 < θ * κ := mul_pos (by linarith) hκ
  apply Real.sqrt_lt_sqrt
  · exact div_nonneg (mul_nonneg (by linarith) (by linarith)) hk.le
  · apply div_lt_div_of_pos_right _ hk
    have : 0 < θ - 1 := by linarith
    nlinarith

/-- **The log-linear labour condition is unchanged by the tax** (O&R p. 687, "the
log-linearization of the model goes through exactly as before"; T21): (79) is (15) with
`K` replaced by `(1−τᴸ)K`, and a constant factor drops out of log changes, so
`(θ+1)Δlog y = −θΔlog C + Δlog Cᵂ` exactly, which is (33). -/
theorem taxed_labour_log_exact {θ κ τL y0 y1 C0 C1 X0 X1 : ℝ} (hθ : 1 < θ) (hκ : 0 < κ)
    (hτ : τL < 1) (hy0 : 0 < y0) (hy1 : 0 < y1) (hC0 : 0 < C0) (hC1 : 0 < C1) (hX0 : 0 < X0)
    (hX1 : 0 < X1)
    (h0 : y0 ^ ((θ + 1) / θ) = (1 - τL) * ((θ - 1) / (θ * κ)) * X0 ^ (1 / θ) / C0)
    (h1 : y1 ^ ((θ + 1) / θ) = (1 - τL) * ((θ - 1) / (θ * κ)) * X1 ^ (1 / θ) / C1) :
    (θ + 1) * (Real.log y1 - Real.log y0) =
      -θ * (Real.log C1 - Real.log C0) + (Real.log X1 - Real.log X0) := by
  have hK : 0 < (1 - τL) * ((θ - 1) / (θ * κ)) :=
    mul_pos (by linarith) (div_pos (by linarith) (mul_pos (by linarith) hκ))
  exact labour_log_exact (by linarith) hK hy0 hy1 hC0 hC1 hX0 hX1 h0 h1

/-- The steady-state output with tax `τᴸ`, (80), O&R p. 687. -/
noncomputable def taxedOutput (M : ReduxParams) (τL : ℝ) : ℝ :=
  Real.sqrt ((M.θ - 1) * (1 - τL) / (M.θ * M.κ))

/-- `κ ȳ₀(τᴸ)² = (1−τᴸ)(θ−1)/θ` (O&R (80), used for (81)). -/
theorem κ_mul_taxedOutput_sq (M : ReduxParams) {τL : ℝ} (hτ : τL ≤ 1) :
    M.κ * taxedOutput M τL ^ 2 = (1 - τL) * ((M.θ - 1) / M.θ) := by
  have hθ := M.hθ
  have hκ := M.hκ
  unfold taxedOutput
  rw [Real.sq_sqrt (div_nonneg (mul_nonneg (by linarith) (by linarith))
    (mul_pos (by linarith) hκ).le)]
  have : M.θ ≠ 0 := by linarith
  field_simp

/-- The first-order change in real utility with an income tax, O&R p. 687–688:
`c − (1−τᴸ)((θ−1)/θ) y + (1/δ)[c̄ − (1−τᴸ)((θ−1)/θ) ȳ]`. -/
noncomputable def dURtax (L : ReduxLinear) (τL c y cb yb : ℝ) : ℝ :=
  c - (1 - τL) * ((L.θ - 1) / L.θ) * y + 1 / L.δ * (cb - (1 - τL) * ((L.θ - 1) / L.θ) * yb)

/-- **(75) with an income tax, as a derivative** (T21; O&R p. 687): around the taxed symmetric
steady state (80), the derivative of `Uᴿ` is `dURtax`. -/
theorem welfare_tax_hasDerivAt (M : ReduxParams) {τL : ℝ} (hτ : τL < 1) (c y cb yb : ℝ) :
    HasDerivAt (fun τ => realWelfare M.β M.κ
      (twoRegime (taxedOutput M τL * Real.exp (τ * c)) (taxedOutput M τL * Real.exp (τ * cb)))
      (twoRegime (taxedOutput M τL * Real.exp (τ * y)) (taxedOutput M τL * Real.exp (τ * yb))))
      (dURtax (linearOf M) τL c y cb yb) 0 := by
  have hθ := M.hθ
  have hY : 0 < taxedOutput M τL := by
    unfold taxedOutput
    exact Real.sqrt_pos.2 (div_pos (mul_pos (by linarith) (by linarith))
      (mul_pos (by linarith) M.hκ))
  have h := welfare_hasDerivAt M.hβ0.le M.hβ1 0 M.κ 0 (taxedOutput M τL) c cb 0 0 y yb hY
    one_pos one_pos
  have e : (fun τ => realWelfare M.β M.κ
      (twoRegime (taxedOutput M τL * Real.exp (τ * c)) (taxedOutput M τL * Real.exp (τ * cb)))
      (twoRegime (taxedOutput M τL * Real.exp (τ * y)) (taxedOutput M τL * Real.exp (τ * yb)))) =
      fun τ => lifetimeWelfare M.β 0 (M.κ * (1 - τ * 0))
      (twoRegime (taxedOutput M τL * Real.exp (τ * c)) (taxedOutput M τL * Real.exp (τ * cb)))
      (twoRegime (1 * Real.exp (τ * 0)) (1 * Real.exp (τ * 0)))
      (twoRegime (taxedOutput M τL * Real.exp (τ * y)) (taxedOutput M τL * Real.exp (τ * yb))) := by
    funext τ
    rw [realWelfare_eq]
    unfold lifetimeWelfare periodWelfare
    simp
  rw [e]
  convert h using 1
  unfold dURtax linearOf
  simp only
  rw [beta_div_one_sub M, κ_mul_taxedOutput_sq M hτ.le]
  ring

/-- **The tax wedge in welfare** (T21): `dURtax = dUᴿ + ((θ−1)/θ)τᴸ(y + ȳ/δ)` (O&R p. 687: the
marginal revenue from taxation is rebated to domestic residents only). -/
theorem dURtax_eq (L : ReduxLinear) (τL c y cb yb : ℝ) :
    dURtax L τL c y cb yb = dUR L c y cb yb + (L.θ - 1) / L.θ * τL * (y + yb / L.δ) := by
  unfold dURtax dUR; ring

/-- **(81)**, O&R p. 688 (T21): with an income tax, the welfare effect of a Foreign monetary
expansion (`m = 0`) on Home is `dUᴿ = ((1−n)m*/θ)[1 − τᴸ(θ−1)²/(δ(1+θ)+2)]`. The log-linear
equilibrium is the untaxed one (`taxed_labour_log_exact`, `tax_budget_rebate`). -/
theorem welfare_eq81 {L : ReduxLinear} {ms : ℝ} {u : ShortVars} {v : SteadyVars}
    (h : MoneyShockEqm L 0 ms u v) (τL : ℝ) :
    dURtax L τL u.c u.y v.c v.y =
      (1 - L.n) * ms / L.θ * (1 - τL * (L.θ - 1) ^ 2 / (L.δ * (1 + L.θ) + 2)) := by
  obtain ⟨rfl, rfl⟩ := (moneyShock_iff L 0 ms u v).1 h
  have hθ := L.hθ
  have hδ := L.hδ
  have hθ0 : L.θ ≠ 0 := by linarith
  have hδ0 : L.δ ≠ 0 := hδ.ne'
  have hE : L.δ * (1 + L.θ) + 2 ≠ 0 := L.E_pos.ne'
  simp only [dURtax, shortRunSolution, steadySolution, ReduxLinear.D, ReduxLinear.E]
  field_simp
  ring

/-- **The exact sign of (81)** (T21; O&R p. 688): for `m* > 0`, a Foreign expansion LOWERS Home
welfare IFF `τᴸ(θ−1)² > δ(1+θ) + 2`. -/
theorem welfare81_neg_iff {L : ReduxLinear} {ms : ℝ} {u : ShortVars} {v : SteadyVars}
    (h : MoneyShockEqm L 0 ms u v) (hms : 0 < ms) (τL : ℝ) :
    dURtax L τL u.c u.y v.c v.y < 0 ↔ L.δ * (1 + L.θ) + 2 < τL * (L.θ - 1) ^ 2 := by
  rw [welfare_eq81 h]
  have hθ := L.hθ
  have hE : 0 < L.δ * (1 + L.θ) + 2 := L.E_pos
  have hk : 0 < (1 - L.n) * ms / L.θ := by
    have : 0 < 1 - L.n := by linarith [L.hn1]
    have : 0 < L.θ := by linarith
    positivity
  rw [mul_neg_iff]
  constructor
  · rintro (⟨-, h2⟩ | ⟨h1, -⟩)
    · rw [sub_neg, one_lt_div hE] at h2; exact h2
    · linarith
  · intro h2
    left
    exact ⟨hk, by rw [sub_neg, one_lt_div hE]; exact h2⟩

/-- **"For large enough θ, Foreign monetary expansion lowers Home welfare"** (T21; O&R p. 688,
made precise): for every `δ > 0` and tax rate `τᴸ > 0` there is `θ̄` with
`τᴸ(θ−1)² > δ(1+θ) + 2` for all `θ > θ̄`. -/
theorem welfare81_large_theta {δ τL : ℝ} (hδ : 0 < δ) (hτ : 0 < τL) :
    ∃ θbar, ∀ θ, θbar < θ → δ * (1 + θ) + 2 < τL * (θ - 1) ^ 2 := by
  refine ⟨2 + (3 * δ + 2) / τL, fun θ hθ => ?_⟩
  set x := θ - 1 with hx
  have hq : 0 < (3 * δ + 2) / τL := by positivity
  have hx1 : 1 < x := by linarith
  have hx2 : (3 * δ + 2) / τL < x := by linarith
  have h3 : 3 * δ + 2 < τL * x := by rw [div_lt_iff₀ hτ] at hx2; linarith
  have e : δ * (1 + θ) + 2 = δ * x + 2 * δ + 2 := by rw [hx]; ring
  rw [e]
  nlinarith

/-- **For θ near one the monopoly distortion dominates** (T21; O&R p. 688): for `τᴸ ≤ 1` and
`1 < θ ≤ 2`, the bracket in (81) is positive, so a Foreign expansion raises Home welfare. -/
theorem welfare81_small_theta {δ τL θ : ℝ} (hδ : 0 < δ) (hτ1 : τL ≤ 1)
    (hθ1 : 1 < θ) (hθ2 : θ ≤ 2) : 0 < 1 - τL * (θ - 1) ^ 2 / (δ * (1 + θ) + 2) := by
  have hE : 0 < δ * (1 + θ) + 2 := by positivity
  rw [sub_pos, div_lt_one hE]
  have h1 : (θ - 1) ^ 2 ≤ 1 := by nlinarith
  have h2 : τL * (θ - 1) ^ 2 ≤ 1 := by
    calc τL * (θ - 1) ^ 2 ≤ 1 * 1 :=
          mul_le_mul hτ1 h1 (sq_nonneg _) zero_le_one
      _ = 1 := by ring
  nlinarith

/-! ## Country size and welfare (T22, §10.1.10, p. 688) -/

/-- **A Home monetary expansion in a country of size `n`** (T22; O&R p. 688): `dUᴿ = nm/θ`,
`cᵂ = nm`, `r = −((1+δ)/δ)nm`, and Home output `y = nm + (1−n)θe` with the size-free
`e = [δ(1+θ)+2θ]m/(θ(δ(1+θ)+2))` (`exchangeRateCoef`). -/
theorem home_shock_size {L : ReduxLinear} {m : ℝ} {u : ShortVars} {v : SteadyVars}
    (h : MoneyShockEqm L m 0 u v) :
    dUR L u.c u.y v.c v.y = L.n * m / L.θ ∧ u.cW = L.n * m ∧
    u.r = -((1 + L.δ) / L.δ) * (L.n * m) ∧ u.e = exchangeRateCoef L.θ L.δ * m ∧
    u.y = L.n * m + (1 - L.n) * L.θ * (exchangeRateCoef L.θ L.δ * m) := by
  obtain ⟨h1, -, -⟩ := welfare_eq76 h
  obtain ⟨-, hcW, -, hr, hy, -⟩ := moneyShock_world h
  have he := (moneyShock_closed_forms h).1
  have hE : exchangeRateCoef L.θ L.δ * m = (L.δ * (1 + L.θ) + 2 * L.θ) * (m - 0) / L.D := by
    unfold exchangeRateCoef ReduxLinear.D; ring
  refine ⟨by rw [h1]; ring, by rw [hcW]; ring, by rw [hr]; ring, by rw [he, hE], ?_⟩
  rw [hy, he, hE]; ring

/-- **The small-country limit** (T22; O&R p. 688): as `n → 0`, a Home monetary expansion has no
effect on world consumption, on the world real interest rate, or on Home welfare
(`nm/θ → 0`), while Home output tends to `θe`. -/
theorem small_country_limit (θ δ m : ℝ) :
    Tendsto (fun n : ℝ => n * m / θ) (𝓝 0) (𝓝 0) ∧
    Tendsto (fun n : ℝ => n * m) (𝓝 0) (𝓝 0) ∧
    Tendsto (fun n : ℝ => -((1 + δ) / δ) * (n * m)) (𝓝 0) (𝓝 0) ∧
    Tendsto (fun n : ℝ => n * m + (1 - n) * θ * (exchangeRateCoef θ δ * m)) (𝓝 0)
      (𝓝 (θ * (exchangeRateCoef θ δ * m))) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h : Continuous (fun n : ℝ => n * m / θ) := by fun_prop
    simpa using h.tendsto 0
  · have h : Continuous (fun n : ℝ => n * m) := by fun_prop
    simpa using h.tendsto 0
  · have h : Continuous (fun n : ℝ => -((1 + δ) / δ) * (n * m)) := by fun_prop
    simpa using h.tendsto 0
  · have h : Continuous (fun n : ℝ => n * m + (1 - n) * θ * (exchangeRateCoef θ δ * m)) := by
      fun_prop
    simpa using h.tendsto 0

/-! ## Exercise 3: the small country directly -/

/-- **Ex. 3, the nonlinear steady state of the small country exists and is unique for every
`B̄`** (O&R p. 713): with exogenous world demand `Cᵂ = X > 0` and interest rate `r = δ`, the
steady-state conditions — demand `y = p^{−θ}X`, the labour–leisure condition (15)
`y^{(θ+1)/θ} = K X^{1/θ}/C` and income = expenditure `C = δB̄ + p y` — have exactly one positive
solution `(y, p, C)`: `y = g⁻¹(δB̄/X^{1/θ})` with the gap function `g` of T7. -/
theorem ex3_steady_existsUnique {θ κ δ X : ℝ} (hθ : 1 < θ) (hκ : 0 < κ) (hX : 0 < X) (B : ℝ) :
    ∃! t : ℝ × ℝ × ℝ, 0 < t.1 ∧ 0 < t.2.1 ∧ 0 < t.2.2 ∧ t.1 = cesDemand θ t.2.1 1 X ∧
      t.1 ^ ((θ + 1) / θ) = (θ - 1) / (θ * κ) * X ^ (1 / θ) / t.2.2 ∧
      t.2.2 = δ * B + t.2.1 * t.1 := by
  have hθ0 : θ ≠ 0 := by linarith
  set K := (θ - 1) / (θ * κ) with hKdef
  have hK : 0 < K := div_pos (by linarith) (mul_pos (by linarith) hκ)
  have hXr := rpow_pos_of_pos hX (1 / θ)
  -- the reduction: any solution has `X^{1/θ} g(y) = δB̄`, `p = X^{1/θ}/y^{1/θ}`, `C = K p / y`
  have reduce : ∀ y p C : ℝ, 0 < y → 0 < p → 0 < C → y = cesDemand θ p 1 X →
      y ^ ((θ + 1) / θ) = K * X ^ (1 / θ) / C → C = δ * B + p * y →
      p = X ^ (1 / θ) / y ^ (1 / θ) ∧ C = K * p / y ∧
        X ^ (1 / θ) * gapFn θ K y = δ * B := by
    intro y p C hy hp hC hd hl hb
    have hyr := rpow_pos_of_pos hy (1 / θ)
    have hXeq : X ^ (1 / θ) = p * y ^ (1 / θ) := by
      have hX' : X = p ^ θ * y := by
        rw [hd]; unfold cesDemand
        rw [div_one, rpow_neg hp.le]
        have := (rpow_pos_of_pos hp θ).ne'
        field_simp
      rw [hX', mul_rpow (rpow_nonneg hp.le _) hy.le, ← rpow_mul hp.le, mul_one_div_cancel hθ0,
        rpow_one]
    have hp' : p = X ^ (1 / θ) / y ^ (1 / θ) := by rw [hXeq]; field_simp
    have hC' : C = K * p / y := by
      rw [rpow_succ_div hθ0 hy, hXeq] at hl
      field_simp at hl ⊢
      nlinarith [hl]
    refine ⟨hp', hC', ?_⟩
    rw [gapFn_eq hθ0 hy, hXeq]
    have : C - p * y = δ * B := by linarith
    rw [← this, hC']
    field_simp
  -- existence
  set y0 := gapInv θ K (δ * B / X ^ (1 / θ)) with hy0
  obtain ⟨hy0pos, hgy0⟩ := gapInv_spec hθ hK (δ * B / X ^ (1 / θ))
  rw [← hy0] at hy0pos hgy0
  have hy0r := rpow_pos_of_pos hy0pos (1 / θ)
  set p0 := X ^ (1 / θ) / y0 ^ (1 / θ) with hp0
  have hp0pos : 0 < p0 := div_pos hXr hy0r
  set C0 := K * p0 / y0 with hC0
  have hC0pos : 0 < C0 := div_pos (mul_pos hK hp0pos) hy0pos
  refine ⟨(y0, p0, C0), ⟨hy0pos, hp0pos, hC0pos, ?_, ?_, ?_⟩, ?_⟩
  · change y0 = cesDemand θ p0 1 X
    unfold cesDemand
    rw [div_one, hp0, div_rpow hXr.le hy0r.le, ← rpow_mul hX.le, ← rpow_mul hy0pos.le]
    have e : 1 / θ * -θ = -1 := by field_simp
    rw [e, rpow_neg_one, rpow_neg_one]
    field_simp
  · change y0 ^ ((θ + 1) / θ) = K * X ^ (1 / θ) / C0
    rw [rpow_succ_div hθ0 hy0pos, hC0, hp0]
    field_simp
  · change C0 = δ * B + p0 * y0
    have hg : X ^ (1 / θ) * gapFn θ K y0 = δ * B := by
      rw [hgy0]; field_simp
    rw [gapFn_eq hθ0 hy0pos] at hg
    rw [hC0, hp0, ← hg]
    field_simp
    ring
  · -- uniqueness
    rintro ⟨y, p, C⟩ ⟨hy, hp, hC, hd, hl, hb⟩
    simp only at hy hp hC hd hl hb
    obtain ⟨hp', hC', hg⟩ := reduce y p C hy hp hC hd hl hb
    have hyeq : y = y0 := by
      have : gapFn θ K y = δ * B / X ^ (1 / θ) := by
        rw [eq_div_iff hXr.ne']; linarith
      rw [hy0, ← this, gapInv_gapFn hθ hK hy]
    subst hyeq
    have hpeq : p = p0 := by rw [hp', hp0]
    subst hpeq
    rw [hC']

/-- **Ex. 3: consumption is flat, exactly** (O&R p. 713): with the exogenous world rate satisfying
`β(1+r) = 1`, the Euler equation (13) gives `C_{t+1} = C_t`; in logs `c̄ = c`. -/
theorem ex3_consumption_flat {β r C1 C2 : ℝ} (hβr : β * (1 + r) = 1)
    (heuler : C2 = β * (1 + r) * C1) : C2 = C1 := by
  rw [heuler, hβr, one_mul]

/-- The unknowns of the linearised small-country model of Ex. 3 (O&R p. 713): impact
consumption `c`, output `y`, the relative world price of the Home good `p`, the exchange rate `e`,
the current account `b̄`, and the long-run `c̄, ȳ, p̄, ē`. -/
structure Ex3Vars where
  c : ℝ
  y : ℝ
  p : ℝ
  e : ℝ
  b : ℝ
  cb : ℝ
  yb : ℝ
  pb : ℝ
  eb : ℝ

/-- **The linearised small-country model** (Ex. 3, O&R p. 713, following §10.1.5–§10.1.7 with
`Cᵂ`, `P*` and `r` exogenous): the Home-currency price of the Home good is preset, so its world
relative price moves by `p = −e`; demand `y = −θp`; the current account `b̄ = p + y − c` ((55));
the Euler equation with an exogenous rate `c̄ = c`; money demand at date 1 (the consumer price
level moves with `e`, `r̂ = 0`) and in the long run; and the long-run demand, labour–leisure
condition and budget (the analogues of (30), (33), (40)). -/
structure Ex3Eqm (L : ReduxLinear) (m : ℝ) (w : Ex3Vars) : Prop where
  price : w.p = -w.e
  demand : w.y = -L.θ * w.p
  ca : w.b = w.p + w.y - w.c
  euler : w.cb = w.c
  money : m - w.e = w.c - (w.eb - w.e) / L.δ
  money_lr : m - w.eb = w.cb
  demand_lr : w.yb = -L.θ * w.pb
  labour_lr : (L.θ + 1) * w.yb = -L.θ * w.cb
  budget_lr : w.cb = L.δ * w.b + w.pb + w.yb

/-- The closed-form solution of Ex. 3 (O&R p. 713): (65)–(67) with `n = 0`, `m* = 0`. -/
noncomputable def ex3Solution (L : ReduxLinear) (m : ℝ) : Ex3Vars where
  c := L.δ * (L.θ ^ 2 - 1) * m / L.D
  y := L.θ * ((L.δ * (1 + L.θ) + 2 * L.θ) * m / L.D)
  p := -((L.δ * (1 + L.θ) + 2 * L.θ) * m / L.D)
  e := (L.δ * (1 + L.θ) + 2 * L.θ) * m / L.D
  b := 2 * (L.θ - 1) * m / L.E
  cb := L.δ * (L.θ ^ 2 - 1) * m / L.D
  yb := -(L.θ * (L.δ * (L.θ ^ 2 - 1) * m / L.D)) / (L.θ + 1)
  pb := L.δ * (L.θ ^ 2 - 1) * m / L.D / (L.θ + 1)
  eb := (L.δ * (1 + L.θ) + 2 * L.θ) * m / L.D

/-- **Ex. 3 has exactly one solution** (O&R p. 713): `Ex3Eqm` holds IFF the unknowns are
`ex3Solution`, i.e. `c = c̄ = δ(θ²−1)m/D`, `e = ē = [δ(1+θ)+2θ]m/D`, `b̄ = 2(θ−1)m/(δ(1+θ)+2)`,
`y = θe`. -/
theorem ex3_iff (L : ReduxLinear) (m : ℝ) (w : Ex3Vars) : Ex3Eqm L m w ↔ w = ex3Solution L m := by
  have hθ := L.hθ
  have hδ := L.hδ
  have hθ0 : L.θ ≠ 0 := by linarith
  have hθ1 : L.θ + 1 ≠ 0 := by linarith
  have hD := L.D_pos.ne'
  have hE := L.E_pos.ne'
  constructor
  · rintro ⟨hp, hy, hb, heu, hm, hmlr, hylr, hllr, hblr⟩
    rcases w with ⟨c, y, p, e, b, cb, yb, pb, eb⟩
    simp only at hp hy hb heu hm hmlr hylr hllr hblr
    have hee : e = eb ∧ e = m - cb := mm_no_overshooting hδ (by rw [heu]; exact hm) (by linarith)
    have hpb : (L.θ + 1) * pb = cb := by
      have h2 : L.θ * ((L.θ + 1) * pb - cb) = 0 := by
        linear_combination (-1 : ℝ) * hllr + (L.θ + 1) * hylr
      have := (mul_eq_zero.1 h2).resolve_left hθ0
      linarith
    have h2c : 2 * L.θ * cb = (L.θ + 1) * L.δ * b := by
      linear_combination (L.θ + 1) * hblr + hpb + hllr
    have hb' : b = (L.θ - 1) * m - L.θ * cb := by
      rw [hb, hy, hp, hee.2, heu]; ring
    have key : cb * L.D = L.δ * (L.θ ^ 2 - 1) * m := by
      unfold ReduxLinear.D
      rw [hb'] at h2c
      linear_combination h2c
    have hcb : cb = L.δ * (L.θ ^ 2 - 1) * m / L.D := by field_simp; linarith
    have he : e = (L.δ * (1 + L.θ) + 2 * L.θ) * m / L.D := by
      rw [hee.2, hcb]; unfold ReduxLinear.D; field_simp; ring
    simp only [ex3Solution, Ex3Vars.mk.injEq]
    refine ⟨by rw [← heu, hcb], by rw [hy, hp, he]; ring, by rw [hp, he], he, ?_, hcb, ?_, ?_,
      by rw [← hee.1, he]⟩
    · rw [hb', hcb]; unfold ReduxLinear.D ReduxLinear.E; field_simp; ring
    · have : yb = -(L.θ * cb) / (L.θ + 1) := by field_simp; linarith
      rw [this, hcb]
    · have : pb = cb / (L.θ + 1) := by field_simp; linarith
      rw [this, hcb]
  · rintro rfl
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [ex3Solution, ReduxLinear.D, ReduxLinear.E] <;> field_simp <;> ring

/-- **Ex. 3 reproduces the two-country differentials** (O&R p. 713): the small-country
solution coincides with (65), (66) and the per-capita current-account differential of (67),
all of which are independent of `n` (`country_size_correction`), at `m* = 0`. -/
theorem ex3_matches_two_country (L : ReduxLinear) (m : ℝ) :
    (ex3Solution L m).e = (shortRunSolution L m 0).e ∧
    (ex3Solution L m).c = (shortRunSolution L m 0).c - (shortRunSolution L m 0).cs ∧
    (ex3Solution L m).b = (shortRunSolution L m 0).b / (1 - L.n) := by
  have hn : 1 - L.n ≠ 0 := by linarith [L.hn1]
  have hE := L.E_pos.ne'
  simp only [ex3Solution, shortRunSolution]
  refine ⟨by ring, by ring, ?_⟩
  field_simp
  ring

/-- **Ex. 3: no welfare effect for the small country** (O&R p. 688 and p. 713): the first-order
change in real utility (75) at the solution is exactly `0` (the GG cancellation). -/
theorem ex3_welfare_zero (L : ReduxLinear) (m : ℝ) :
    dUR L (ex3Solution L m).c (ex3Solution L m).y (ex3Solution L m).cb
      (ex3Solution L m).yb = 0 := by
  have hθ := L.hθ
  have hδ := L.hδ
  have hθ0 : L.θ ≠ 0 := by linarith
  have hθ1 : L.θ + 1 ≠ 0 := by linarith
  have hδ0 : L.δ ≠ 0 := hδ.ne'
  have hE : L.δ * (1 + L.θ) + 2 ≠ 0 := L.E_pos.ne'
  simp only [dUR, ex3Solution, ReduxLinear.D]
  field_simp
  ring

end ObstfeldRogoff.StickyPriceModels.ReduxWelfare

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The redux model: productivity and government-spending shocks

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §10.3,
pp. 696–706.

The book treats productivity shocks (§10.3.1, `a = −(κ − κ̄₀)/κ̄₀`) and government-spending
shocks (§10.3.2, a CES government basket with the same `θ`, dissipative, financed by lump-sum taxes)
separately and notes that the effects are additive in the linear model (p. 698). We therefore
solve ONE linear system that carries money, productivity and government spending at once
(`FiscalSteadyLinear`, `FiscalShockEqm`) and read off every result of the section as a special
case.

* **Exact foundations.** The labour–leisure condition with a shocked `κ` is exact in logs and
  linearises to (100)–(101) (`labour_log_exact_kappa`, `linearise_100`); fn 24 (general exponent
  `μ`: `c̄ᵂ = ȳᵂ = āᵂ/μ`); government demand (109) aggregates exactly with private demand
  (`world_demand_with_gov`); (108) with (8) gives the budget with `G` (`gov_budget_combined`),
  whose steady state is (111)–(112); the level linearisations of (109), (118) and (120)
  (`linearise_113`, `linearise_118`, `linearise_121`).
* **The long run (102)–(104), (123)–(126).** `fiscalSteadyLinear_iff`: for every
  `b̄, m̄, m̄*, ā, ā*, ḡ, ḡ*` exactly one solution, with `c̄ᵂ = (āᵂ − ḡᵂ)/2`,
  `ȳᵂ = (āᵂ + ḡᵂ)/2` and the terms of trade `(δb̄/(1−n) − (ā−ā*) − (ḡ−ḡ*))/(2θ)`.
* **The short run (105)–(107), (127)–(130).** `fiscalShock_iff`: for every shock exactly one
  solution, `e = {[δ(1+θ)+2θ](m−m*) + (1+θ)[δ(g−g*) + (ḡ−ḡ*)] − (θ−1)(ā−ā*)}/D`,
  `b̄ = (1−n)(θe − (m−m*) − (g−g*))`, `cᵂ = mᵂ`, `yᵂ = mᵂ + gᵂ`,
  `r = ((1+δ)/δ)((āᵂ − ḡᵂ)/2 − mᵂ)`; the nominal interest rate is unchanged in each country
  (`fiscal_nominal_rate_unchanged`, p. 699).
* **Corollaries.** A permanent Home productivity rise appreciates the Home currency, produces a
  current-account DEFICIT and a long-run consumption differential that is tempered but not
  reversed; a temporary productivity shock changes nothing but leisure; a temporary relative rise
  in Home government spending produces a deficit and a permanent one a SURPLUS; a temporary rise in
  world spending raises world output one for one and leaves `cᵂ` and `r` unchanged (p. 705).
* **Welfare (T24, T26), closed forms the book leaves to the reader.** Permanent Home productivity
  rise: `dUᴿ_Home = (ā/(2θ))[(θ−1) + (n+θ−1)/δ] > 0`, `dUᴿ_Foreign = nā/(2θδ) > 0` (p. 700 "one
  can show"). Government spending, Home spends: flexible prices, per period, Home `−ḡ(1 − n/(2θ))`,
  Foreign `nḡ/(2θ)`; sticky prices, temporary `g`: Home `−g(1 − n/θ)`, Foreign `ng/θ`; a
  future-only `ḡ`: Home `−(ḡ/δ)(1 − n/(2θ))`, Foreign `nḡ/(2θδ)`; permanent = the sum; world
  welfare falls. Each is a derivative of lifetime utility (`fiscal_welfare_hasDerivAt`).
-/

namespace ObstfeldRogoff.StickyPriceModels.ReduxFiscalProductivity

open Real Filter Topology ReduxPrimitives ReduxLogLinear ReduxSteadyState ReduxMoneyShocks
  ReduxWelfare

/-! ## Exact foundations of the productivity model (100)–(101), fn 24 -/

/-- **The labour–leisure condition with a productivity shock is exact in logs** (O&R p. 696,
(100)): if `y^{(θ+1)/θ} = ((θ−1)/(θκ)) X^{1/θ}/C` holds at `(κ₀, y₀, C₀, X₀)` and at
`(κ₁, y₁, C₁, X₁)`, then
`(θ+1)Δlog y = −θΔlog C + Δlog X − θΔlog κ`. -/
theorem labour_log_exact_kappa {θ κ0 κ1 y0 y1 C0 C1 X0 X1 : ℝ} (hθ : 1 < θ) (hκ0 : 0 < κ0)
    (hκ1 : 0 < κ1) (hy0 : 0 < y0) (hy1 : 0 < y1) (hC0 : 0 < C0) (hC1 : 0 < C1) (hX0 : 0 < X0)
    (hX1 : 0 < X1) (h0 : y0 ^ ((θ + 1) / θ) = (θ - 1) / (θ * κ0) * X0 ^ (1 / θ) / C0)
    (h1 : y1 ^ ((θ + 1) / θ) = (θ - 1) / (θ * κ1) * X1 ^ (1 / θ) / C1) :
    (θ + 1) * (Real.log y1 - Real.log y0) = -θ * (Real.log C1 - Real.log C0) +
      (Real.log X1 - Real.log X0) - θ * (Real.log κ1 - Real.log κ0) := by
  have hθ0 : θ ≠ 0 := by linarith
  have hθ1 : 0 < θ - 1 := by linarith
  have l0 := congrArg Real.log h0
  have l1 := congrArg Real.log h1
  have hA0 : 0 < (θ - 1) / (θ * κ0) := div_pos hθ1 (mul_pos (by linarith) hκ0)
  have hA1 : 0 < (θ - 1) / (θ * κ1) := div_pos hθ1 (mul_pos (by linarith) hκ1)
  rw [Real.log_rpow hy0, Real.log_div (mul_pos hA0 (rpow_pos_of_pos hX0 _)).ne' hC0.ne',
    Real.log_mul hA0.ne' (rpow_pos_of_pos hX0 _).ne', Real.log_rpow hX0,
    Real.log_div hθ1.ne' (mul_pos (by linarith) hκ0).ne',
    Real.log_mul (by linarith) hκ0.ne'] at l0
  rw [Real.log_rpow hy1, Real.log_div (mul_pos hA1 (rpow_pos_of_pos hX1 _)).ne' hC1.ne',
    Real.log_mul hA1.ne' (rpow_pos_of_pos hX1 _).ne', Real.log_rpow hX1,
    Real.log_div hθ1.ne' (mul_pos (by linarith) hκ1).ne',
    Real.log_mul (by linarith) hκ1.ne'] at l1
  have e := congrArg (fun z => θ * z) (show (θ + 1) / θ * Real.log y1 - (θ + 1) / θ *
    Real.log y0 = 1 / θ * Real.log X1 - Real.log C1 - Real.log κ1 -
      (1 / θ * Real.log X0 - Real.log C0 - Real.log κ0) by linarith)
  field_simp at e
  linarith

/-- **(100)–(101): the productivity term linearises to `θa`** (O&R p. 696): with
`κ = κ₀(1 − τa)` (so `a = −dκ/κ₀`), `d/dτ [−θ log κ] = θa` at `τ = 0`. -/
theorem linearise_100 {θ κ0 a : ℝ} (hκ0 : 0 < κ0) :
    HasDerivAt (fun τ => -θ * Real.log (κ0 * (1 - τ * a))) (θ * a) 0 := by
  have h1 : HasDerivAt (fun τ => κ0 * (1 - τ * a)) (κ0 * (-a)) 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).mul_const a).const_sub 1).const_mul κ0
  have h2 := (h1.log (by simpa using hκ0.ne')).const_mul (-θ)
  convert h2 using 1
  simp
  field_simp

/-- **fn 24: with disutility `(κ/μ)y^μ`, `c̄ᵂ = ȳᵂ = āᵂ/μ`** (O&R p. 697, fn 24): the
population-weighted labour–leisure condition `(θ(μ−1)+1)ȳᵂ = −θc̄ᵂ + c̄ᵂ + θāᵂ` together with
`ȳᵂ = c̄ᵂ` gives `c̄ᵂ = āᵂ/μ` (for `μ = 2` this is (104)). -/
theorem fn24_world {θ μ aW yW cW : ℝ} (hθ : 0 < θ) (hμ : 0 < μ)
    (hlab : (θ * (μ - 1) + 1) * yW = -θ * cW + cW + θ * aW) (hy : yW = cW) :
    cW = aW / μ ∧ yW = aW / μ := by
  have h : θ * μ * cW = θ * aW := by rw [hy] at hlab; linarith
  have hc : cW = aW / μ := by
    field_simp
    have := mul_left_cancel₀ hθ.ne' (show θ * (cW * μ) = θ * aW by linarith)
    linarith
  exact ⟨hc, by rw [hy, hc]⟩

/-! ## Exact foundations of the government-spending model (108)–(112) -/

/-- **(109): government demand aggregates with private demand** (O&R pp. 700–701): if both
governments buy the CES basket with the same `θ` (demands `(p(z)/P)^{−θ}G`), then with PPP
`p/P = p*/P*` the world demand for a Home good is `(p/P)^{−θ}(Cᵂ + Gᵂ)`. -/
theorem world_demand_with_gov {θ n p P ps Ps C Cs G Gs : ℝ} (hrel : p / P = ps / Ps) :
    n * (cesDemand θ p P C + cesDemand θ p P G) +
      (1 - n) * (cesDemand θ ps Ps Cs + cesDemand θ ps Ps Gs) =
      cesDemand θ p P (worldConsumption n C Cs + worldConsumption n G Gs) := by
  unfold cesDemand worldConsumption
  rw [← hrel]
  ring

/-- **(108) with (8): the budget with government spending** (O&R p. 701): the household budget
`P B′ + M = P(1+r)B + M₋₁ + p y − P C − P τ` and the government budget (108)
`G = τ + (M − M₋₁)/P` combine to `P B′ = P(1+r)B + p y − P C − P G` (the analogue of (120)). -/
theorem gov_budget_combined {P B B1 M Mprev r py C τ G : ℝ} (hP : P ≠ 0)
    (h8 : P * B1 + M = P * (1 + r) * B + Mprev + py - P * C - P * τ)
    (h108 : G = τ + (M - Mprev) / P) :
    P * B1 = P * (1 + r) * B + py - P * C - P * G := by
  have h : P * G = P * τ + (M - Mprev) := by rw [h108]; field_simp
  linear_combination h8 + h

/-- **(111)–(112): steady-state income = expenditure with government spending** (O&R p. 701): with
constant `B` the combined budget gives `C = rB + p y/P − G` (with `r = δ`, (111)). -/
theorem gov_steady_budget {P B r py C G : ℝ} (hP : P ≠ 0)
    (h : P * B = P * (1 + r) * B + py - P * C - P * G) : C = r * B + py / P - G := by
  field_simp
  linear_combination h

/-- **(113): the level linearisation of world demand with government spending** (O&R p. 701): with
`G₀ = 0`, along `Cᵂ = X₀e^{τcᵂ}` and `Gᵂ = τ gᵂ X₀` (a LEVEL change `gᵂ = dGᵂ/C̄ᵂ₀`),
`d log(Cᵂ + Gᵂ) = cᵂ + gᵂ`. -/
theorem linearise_113 {X0 cW gW : ℝ} (hX0 : 0 < X0) :
    HasDerivAt (fun τ => Real.log (X0 * Real.exp (τ * cW) + τ * gW * X0)) (cW + gW) 0 := by
  have h1 : HasDerivAt (fun τ => X0 * Real.exp (τ * cW)) (X0 * cW) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const cW).exp.const_mul X0
  have h2 : HasDerivAt (fun τ : ℝ => τ * gW * X0) (gW * X0) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const gW).mul_const X0
  have h := (h1.add h2).log (by simpa using hX0.ne')
  convert h using 1
  simp only [Pi.add_apply, zero_mul, Real.exp_zero, mul_one, add_zero]
  field_simp

/-- **(118): the level linearisation of the steady-state budget with government spending**
(O&R p. 702): around `B̄₀ = Ḡ₀ = 0`, along `B = τb̄C̄₀`, `π = e^{τu}`, `y = C̄₀e^{τŷ}`,
`G = τḡC̄₀`, `d log(δB + πy − G) = δb̄ + u + ŷ − ḡ`. -/
theorem linearise_118 {δ b u yh g C0 : ℝ} (hC0 : 0 < C0) :
    HasDerivAt (fun τ => Real.log (δ * (τ * b * C0) +
      Real.exp (τ * u) * (C0 * Real.exp (τ * yh)) - τ * g * C0)) (δ * b + u + yh - g) 0 := by
  have h1 : HasDerivAt (fun τ => δ * (τ * b * C0) + Real.exp (τ * u) * (C0 * Real.exp (τ * yh)))
      (C0 * (δ * b + u + yh)) 0 := by
    have hA : HasDerivAt (fun τ => δ * (τ * b * C0)) (δ * (b * C0)) 0 := by
      simpa using (((hasDerivAt_id (0 : ℝ)).mul_const b).mul_const C0).const_mul δ
    have hB : HasDerivAt (fun τ => Real.exp (τ * u)) u 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const u).exp
    have hC : HasDerivAt (fun τ => C0 * Real.exp (τ * yh)) (C0 * yh) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const yh).exp.const_mul C0
    convert hA.add (hB.mul hC) using 1
    simp only [zero_mul, Real.exp_zero, mul_one, one_mul]
    ring
  have h2 : HasDerivAt (fun τ : ℝ => τ * g * C0) (g * C0) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).mul_const g).mul_const C0
  have h := (h1.sub h2).log (by simpa using hC0.ne')
  convert h using 1
  simp only [Pi.sub_apply, zero_mul, Real.exp_zero, mul_one, mul_zero, sub_zero]
  field_simp
  ring

/-- **(121): the level linearisation of the short-run current account with government spending**
(O&R p. 702): with `B₁ = 0`, (120) gives `B₂ = πy − C − G`; along `π = e^{τu}`, `y = C̄₀e^{τŷ}`,
`C = C̄₀e^{τĉ}`, `G = τgC̄₀`, `d(B₂/C̄₀)/dτ = u + ŷ − ĉ − g`; with preset prices `u = −(1−n)e`. -/
theorem linearise_121 {u yh ch g C0 : ℝ} (hC0 : 0 < C0) :
    HasDerivAt (fun τ => (Real.exp (τ * u) * (C0 * Real.exp (τ * yh)) -
      C0 * Real.exp (τ * ch) - τ * g * C0) / C0) (u + yh - ch - g) 0 := by
  have h55 := linearise_55 (u := u) (yh := yh) (ch := ch) hC0
  have h2 : HasDerivAt (fun τ : ℝ => τ * g * C0 / C0) (g * C0 / C0) 0 := by
    simpa using (((hasDerivAt_id (0 : ℝ)).mul_const g).mul_const C0).div_const C0
  have h := h55.sub h2
  convert h using 1
  · funext τ; simp only [Pi.sub_apply]; ring
  · field_simp

/-! ## The long-run system with money, productivity and government spending -/

/-- The population-weighted world aggregate `xᵂ = n x + (1−n) x*` (O&R (11), (104), (115)). -/
def wavg (L : ReduxLinear) (x xs : ℝ) : ℝ := L.n * x + (1 - L.n) * xs

/-- **The long-run linear system with productivity and government spending**, O&R (102)–(104)
and (113)–(119), pp. 696–703: barred (27), (28); demand with government spending (113)–(114);
(32); the labour–leisure conditions with productivity and government spending
(100)–(101)/(116)–(117), `(θ+1)ȳ = −θc̄ + c̄ᵂ + ḡᵂ + θā`; the budgets with government spending
(118)–(119); and long-run money demand (50)–(51). For `ā = ā* = ḡ = ḡ* = 0` it is `SteadyLinear`. -/
structure FiscalSteadyLinear (L : ReduxLinear) (b m ms a as g gs : ℝ) (v : SteadyVars) : Prop where
  eq27 : v.p = L.n * v.ph + (1 - L.n) * (v.e + v.pf)
  eq28 : v.ps = L.n * (v.ph - v.e) + (1 - L.n) * v.pf
  eq113 : v.y = L.θ * (v.p - v.ph) + v.cW + wavg L g gs
  eq114 : v.ys = L.θ * (v.ps - v.pf) + v.cW + wavg L g gs
  eq32 : v.cW = L.n * v.c + (1 - L.n) * v.cs
  eq116 : (L.θ + 1) * v.y = -L.θ * v.c + v.cW + wavg L g gs + L.θ * a
  eq117 : (L.θ + 1) * v.ys = -L.θ * v.cs + v.cW + wavg L g gs + L.θ * as
  eq118 : v.c = L.δ * b + v.ph + v.y - v.p - g
  eq119 : v.cs = -(L.n / (1 - L.n)) * L.δ * b + v.pf + v.ys - v.ps - gs
  eq50 : v.p = m - v.c
  eq51 : v.ps = ms - v.cs

/-- The long-run terms of trade `p̄(h) − ē − p̄*(f) = (δb̄/(1−n) − (ā−ā*) − (ḡ−ḡ*))/(2θ)`, O&R
(46), (103), (126). -/
noncomputable def fiscalToT (L : ReduxLinear) (b a as g gs : ℝ) : ℝ :=
  (L.δ * b / (1 - L.n) - (a - as) - (g - gs)) / (2 * L.θ)

/-- The closed-form long-run solution with productivity and government spending, O&R
(102)–(104), (123)–(126): `c̄ᵂ = (āᵂ − ḡᵂ)/2`, `c̄ − c̄* = (θ+1)T + (ā − ā*)` with `T` the terms
of trade, and the levels. -/
noncomputable def fiscalSteadySolution (L : ReduxLinear) (b m ms a as g gs : ℝ) : SteadyVars where
  cW := (wavg L a as - wavg L g gs) / 2
  c := (wavg L a as - wavg L g gs) / 2 +
    (1 - L.n) * ((L.θ + 1) * fiscalToT L b a as g gs + (a - as))
  cs := (wavg L a as - wavg L g gs) / 2 - L.n * ((L.θ + 1) * fiscalToT L b a as g gs + (a - as))
  y := (wavg L a as + wavg L g gs) / 2 - L.θ * (1 - L.n) * fiscalToT L b a as g gs
  ys := (wavg L a as + wavg L g gs) / 2 + L.θ * L.n * fiscalToT L b a as g gs
  p := m - ((wavg L a as - wavg L g gs) / 2 +
    (1 - L.n) * ((L.θ + 1) * fiscalToT L b a as g gs + (a - as)))
  ps := ms - ((wavg L a as - wavg L g gs) / 2 -
    L.n * ((L.θ + 1) * fiscalToT L b a as g gs + (a - as)))
  e := m - ms - ((L.θ + 1) * fiscalToT L b a as g gs + (a - as))
  ph := m - ((wavg L a as - wavg L g gs) / 2 +
    (1 - L.n) * ((L.θ + 1) * fiscalToT L b a as g gs + (a - as))) +
    (1 - L.n) * fiscalToT L b a as g gs
  pf := ms - ((wavg L a as - wavg L g gs) / 2 -
    L.n * ((L.θ + 1) * fiscalToT L b a as g gs + (a - as))) - L.n * fiscalToT L b a as g gs

/-- **The long-run system has exactly one solution** (O&R (102)–(104), (123)–(126),
pp. 696–703): `FiscalSteadyLinear` holds IFF the unknowns equal `fiscalSteadySolution`. -/
theorem fiscalSteadyLinear_iff (L : ReduxLinear) (b m ms a as g gs : ℝ) (v : SteadyVars) :
    FiscalSteadyLinear L b m ms a as g gs v ↔ v = fiscalSteadySolution L b m ms a as g gs := by
  have hθ : L.θ ≠ 0 := by linarith [L.hθ]
  have hθ1 : L.θ + 1 ≠ 0 := by linarith [L.hθ]
  have hn : 1 - L.n ≠ 0 := by linarith [L.hn1]
  constructor
  · intro h
    obtain ⟨h27, h28, h113, h114, h32, h116, h117, h118, h119, h50, h51⟩ := h
    rcases v with ⟨c, cs, y, ys, ph, pf, p, ps, e, cW⟩
    simp only at h27 h28 h113 h114 h32 h116 h117 h118 h119 h50 h51
    unfold wavg at h113 h114 h116 h117
    have s1 : p - ps = e := by linear_combination h27 - h28
    have s3 : L.n * y + (1 - L.n) * ys = cW + (L.n * g + (1 - L.n) * gs) := by
      rw [h113, h114, h27, h28]; ring
    have s4 : cW = ((L.n * a + (1 - L.n) * as) - (L.n * g + (1 - L.n) * gs)) / 2 := by
      have h2 : 2 * L.θ * cW = L.θ * ((L.n * a + (1 - L.n) * as) - (L.n * g + (1 - L.n) * gs)) := by
        linear_combination L.n * h116 + (1 - L.n) * h117 - (L.θ + 1) * s3 + L.θ * h32
      field_simp
      have := mul_left_cancel₀ hθ (show L.θ * (cW * 2) =
        L.θ * ((L.n * a + (1 - L.n) * as) - (L.n * g + (1 - L.n) * gs)) by linarith)
      linarith
    have s6 : y - ys = -L.θ * (ph - e - pf) := by linear_combination h113 - h114 + L.θ * s1
    have h119' : (1 - L.n) * cs = -(L.n * L.δ * b) + (1 - L.n) * (pf + ys - ps - gs) := by
      rw [h119]; field_simp; ring
    have s7 : (1 - L.n) * (c - cs) =
        L.δ * b + (1 - L.n) * ((ph - e - pf) + (y - ys) - (g - gs)) := by
      linear_combination (1 - L.n) * h118 - h119' - (1 - L.n) * s1
    have s8 : c - cs = (L.θ + 1) * (ph - e - pf) + (a - as) := by
      have h2 : L.θ * ((c - cs) - (L.θ + 1) * (ph - e - pf) - (a - as)) = 0 := by
        linear_combination h116 - h117 - (L.θ + 1) * s6
      have := (mul_eq_zero.1 h2).resolve_left hθ
      linarith
    have hT : ph - e - pf = fiscalToT L b a as g gs := by
      have h2 : (1 - L.n) * (2 * L.θ * (ph - e - pf)) =
          L.δ * b - (1 - L.n) * ((a - as) + (g - gs)) := by
        linear_combination s7 - (1 - L.n) * s8 + (1 - L.n) * s6
      unfold fiscalToT
      rw [eq_div_iff (mul_ne_zero two_ne_zero hθ)]
      field_simp
      linear_combination h2
    have hdc : c - cs = (L.θ + 1) * fiscalToT L b a as g gs + (a - as) := by rw [s8, hT]
    have hc : c = cW + (1 - L.n) * (c - cs) := by linear_combination -h32
    have hcs : cs = cW - L.n * (c - cs) := by linear_combination -h32
    have hy : y = -L.θ * (1 - L.n) * (ph - e - pf) + cW + (L.n * g + (1 - L.n) * gs) := by
      rw [h113, h27]; ring
    have hys : ys = L.θ * L.n * (ph - e - pf) + cW + (L.n * g + (1 - L.n) * gs) := by
      rw [h114, h28]; ring
    have hph : ph = p + (1 - L.n) * (ph - e - pf) := by linear_combination -h27
    have hpf : pf = ps - L.n * (ph - e - pf) := by linear_combination -h28
    have he : e = m - ms - (c - cs) := by linear_combination -s1 + h50 - h51
    simp only [fiscalSteadySolution, SteadyVars.mk.injEq]
    unfold wavg
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, s4⟩
    · rw [hc, s4, hdc]
    · rw [hcs, s4, hdc]
    · rw [hy, hT, s4]; ring
    · rw [hys, hT, s4]; ring
    · rw [hph, hT, h50, hc, s4, hdc]
    · rw [hpf, hT, h51, hcs, s4, hdc]
    · rw [h50, hc, s4, hdc]
    · rw [h51, hcs, s4, hdc]
    · rw [he, hdc]
  · rintro rfl
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [fiscalSteadySolution, fiscalToT, wavg] <;> field_simp <;> ring

/-- **Consequences for the world and the terms of trade** (O&R (104), (123)–(124), (102), (103),
(125), (126)): any long-run solution has `c̄ᵂ = (āᵂ − ḡᵂ)/2`, `ȳᵂ = (āᵂ + ḡᵂ)/2`,
`p̄(h) − ē − p̄*(f) = (δb̄/(1−n) − (ā−ā*) − (ḡ−ḡ*))/(2θ)`,
`c̄ − c̄* = ((1+θ)/(2θ))(δb̄/(1−n) − (ḡ−ḡ*)) + ((θ−1)/(2θ))(ā−ā*)` and
`ȳ − ȳ* = −θ(p̄(h) − ē − p̄*(f))`. -/
theorem fiscalSteady_consequences {L : ReduxLinear} {b m ms a as g gs : ℝ} {v : SteadyVars}
    (h : FiscalSteadyLinear L b m ms a as g gs v) :
    v.cW = (wavg L a as - wavg L g gs) / 2 ∧
    L.n * v.y + (1 - L.n) * v.ys = (wavg L a as + wavg L g gs) / 2 ∧
    v.ph - v.e - v.pf = (L.δ * b / (1 - L.n) - (a - as) - (g - gs)) / (2 * L.θ) ∧
    v.c - v.cs = (1 + L.θ) / (2 * L.θ) * (L.δ * b / (1 - L.n) - (g - gs)) +
      (L.θ - 1) / (2 * L.θ) * (a - as) ∧
    v.y - v.ys = -L.θ * (v.ph - v.e - v.pf) := by
  have hv := (fiscalSteadyLinear_iff L b m ms a as g gs v).1 h
  have hθ : L.θ ≠ 0 := by linarith [L.hθ]
  have hn : 1 - L.n ≠ 0 := by linarith [L.hn1]
  subst hv
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩ <;> simp only [fiscalSteadySolution, fiscalToT, wavg] <;>
    field_simp <;> ring

/-! ## The short run with money, productivity and government spending -/

variable (L : ReduxLinear) in
/-- **The short-run system with money, productivity and government spending**, O&R §10.3
(pp. 698–705): preset `p(h) = p*(f) = 0` in (27)–(28); short-run demand with government spending
(113)–(114); (32); the Euler equations (35)–(36) and date-1 money demands (37)–(38) (unchanged:
"government spending does not affect the money demand or the consumption Euler equations",
p. 703); the current account with government spending (121); and the long-run system at `b̄` with
permanent money `m, m*`, long-run productivity `ā, ā*` and long-run spending `ḡ, ḡ*`. Short-run
productivity does not enter: the labour–leisure conditions do not bind (p. 697). -/
structure FiscalShockEqm (m ms g gs ab abs gb gbs : ℝ) (u : ShortVars) (v : SteadyVars) : Prop where
  eq27 : u.p = L.n * 0 + (1 - L.n) * (u.e + 0)
  eq28 : u.ps = L.n * (0 - u.e) + (1 - L.n) * 0
  eq113 : u.y = L.θ * (u.p - 0) + u.cW + wavg L g gs
  eq114 : u.ys = L.θ * (u.ps - 0) + u.cW + wavg L g gs
  eq32 : u.cW = L.n * u.c + (1 - L.n) * u.cs
  eq35 : v.c = u.c + L.δ / (1 + L.δ) * u.r
  eq36 : v.cs = u.cs + L.δ / (1 + L.δ) * u.r
  eq37 : m - u.p = u.c - u.r / (1 + L.δ) - (v.p - u.p) / L.δ
  eq38 : ms - u.ps = u.cs - u.r / (1 + L.δ) - (v.ps - u.ps) / L.δ
  eq121 : u.b = u.y - u.c - (1 - L.n) * u.e - g
  longrun : FiscalSteadyLinear L u.b m ms ab abs gb gbs v

/-- The short-run exchange rate, O&R (106) and (128) combined (p. 698, p. 705):
`e = {[δ(1+θ)+2θ](m−m*) + (1+θ)[δ(g−g*) + (ḡ−ḡ*)] − (θ−1)(ā−ā*)}/D`. -/
noncomputable def fiscalE (L : ReduxLinear) (m ms g gs ab abs gb gbs : ℝ) : ℝ :=
  ((L.δ * (1 + L.θ) + 2 * L.θ) * (m - ms) + (1 + L.θ) * (L.δ * (g - gs) + (gb - gbs)) -
    (L.θ - 1) * (ab - abs)) / L.D

/-- The closed-form short-run solution, O&R (105)–(107), (127)–(130). -/
noncomputable def fiscalShortRunSolution (L : ReduxLinear) (m ms g gs ab abs gb gbs : ℝ) :
    ShortVars where
  e := fiscalE L m ms g gs ab abs gb gbs
  c := wavg L m ms + (1 - L.n) * ((m - ms) - fiscalE L m ms g gs ab abs gb gbs)
  cs := wavg L m ms - L.n * ((m - ms) - fiscalE L m ms g gs ab abs gb gbs)
  y := L.θ * (1 - L.n) * fiscalE L m ms g gs ab abs gb gbs + wavg L m ms + wavg L g gs
  ys := -(L.θ * L.n * fiscalE L m ms g gs ab abs gb gbs) + wavg L m ms + wavg L g gs
  p := (1 - L.n) * fiscalE L m ms g gs ab abs gb gbs
  ps := -(L.n * fiscalE L m ms g gs ab abs gb gbs)
  cW := wavg L m ms
  r := (1 + L.δ) / L.δ * ((wavg L ab abs - wavg L gb gbs) / 2 - wavg L m ms)
  b := (1 - L.n) * (L.θ * fiscalE L m ms g gs ab abs gb gbs - (m - ms) - (g - gs))

/-- The MM relation `m − p = c` (O&R (60); T15): the Euler equation (35), date-1 money demand
(37) and long-run money demand (50) imply that real balances move with consumption. -/
theorem mm_relation {δ m p pb c cb r : ℝ} (hδ : 0 < δ) (h35 : cb = c + δ / (1 + δ) * r)
    (h37 : m - p = c - r / (1 + δ) - (pb - p) / δ) (h50 : pb = m - cb) : m - p = c := by
  have hi := nominal_rate_unchanged hδ h35 h37 h50
  have hδ1 : (1 + δ) ≠ 0 := by linarith
  have : (pb - p) / δ = -(r / (1 + δ)) := by
    have e : pb - p = -(δ * r / (1 + δ)) := by linarith
    rw [e]; field_simp
  rw [this] at h37
  linarith

/-- **The short-run system has exactly one solution** (O&R (105)–(107), (127)–(130),
pp. 698–705): `FiscalShockEqm` holds IFF the short-run variables are `fiscalShortRunSolution`
and the long-run variables are `fiscalSteadySolution` at the implied `b̄`. -/
theorem fiscalShock_iff (L : ReduxLinear) (m ms g gs ab abs gb gbs : ℝ) (u : ShortVars)
    (v : SteadyVars) :
    FiscalShockEqm L m ms g gs ab abs gb gbs u v ↔
      u = fiscalShortRunSolution L m ms g gs ab abs gb gbs ∧
      v = fiscalSteadySolution L (fiscalShortRunSolution L m ms g gs ab abs gb gbs).b m ms ab
        abs gb gbs := by
  have hθ := L.hθ
  have hθ0 : L.θ ≠ 0 := by linarith
  have hδ := L.hδ
  have hδ0 : L.δ ≠ 0 := hδ.ne'
  have hn1 : 1 - L.n ≠ 0 := by linarith [L.hn1]
  have hD := L.D_pos.ne'
  have hδ1 : (1 + L.δ) ≠ 0 := by linarith
  constructor
  · intro h
    have hv := (fiscalSteadyLinear_iff L u.b m ms ab abs gb gbs v).1 h.longrun
    obtain ⟨hcWlr, -, -, hdclr, -⟩ := fiscalSteady_consequences h.longrun
    have hmp := mm_relation hδ h.eq35 h.eq37 h.longrun.eq50
    have hmps := mm_relation hδ h.eq36 h.eq38 h.longrun.eq51
    have hwlr := h.longrun.eq32
    have h35 := h.eq35
    have h36 := h.eq36
    have h27 := h.eq27
    have h28 := h.eq28
    have h113 := h.eq113
    have h114 := h.eq114
    have h32 := h.eq32
    have h121 := h.eq121
    have hdiff : v.c - v.cs = u.c - u.cs := by rw [h35, h36]; ring
    rcases u with ⟨c, cs, y, ys, p, ps, e, cW, r, b⟩
    simp only at hmp hmps h35 h36 h27 h28 h113 h114 h32 h121 hdiff hdclr hv ⊢
    have hp : p = (1 - L.n) * e := by linarith
    have hps : ps = -(L.n * e) := by linarith
    have hcW : cW = wavg L m ms := by
      unfold wavg; rw [h32]; rw [hp] at hmp; rw [hps] at hmps
      linear_combination -L.n * hmp - (1 - L.n) * hmps
    have hr : r = (1 + L.δ) / L.δ * ((wavg L ab abs - wavg L gb gbs) / 2 - wavg L m ms) := by
      have hw : v.cW = cW + L.δ / (1 + L.δ) * r := by
        rw [hwlr, h35, h36, h32]; ring
      rw [hcWlr, hcW] at hw
      field_simp at hw ⊢
      linarith
    have hMM : e = (m - ms) - (c - cs) := by rw [hp] at hmp; rw [hps] at hmps; linarith
    have hb : b = (1 - L.n) * ((L.θ - 1) * e - (c - cs) - (g - gs)) := by
      rw [h121, h113, hp, h32]; unfold wavg; ring
    have hb' : b = (1 - L.n) * (L.θ * e - (m - ms) - (g - gs)) := by rw [hb, hMM]; ring
    have he : e = fiscalE L m ms g gs ab abs gb gbs := by
      rw [hdiff, hb'] at hdclr
      have h2 : (m - ms) - e = (1 + L.θ) / (2 * L.θ) *
          (L.δ * ((1 - L.n) * (L.θ * e - (m - ms) - (g - gs))) / (1 - L.n) - (gb - gbs)) +
          (L.θ - 1) / (2 * L.θ) * (ab - abs) := by rw [← hdclr]; linarith
      unfold fiscalE ReduxLinear.D
      rw [eq_div_iff (by have := L.D_pos; unfold ReduxLinear.D at this; linarith)]
      field_simp at h2
      linear_combination -h2
    refine ⟨?_, ?_⟩
    · simp only [fiscalShortRunSolution, ShortVars.mk.injEq]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, he, hcW, hr, ?_⟩
      · rw [← he, ← hcW]; linear_combination -h32 + (1 - L.n) * hMM
      · rw [← he, ← hcW]; linear_combination -h32 - L.n * hMM
      · rw [← he, h113, hp, hcW]; ring
      · rw [← he, h114, hps, hcW]; ring
      · rw [hp, he]
      · rw [hps, he]
      · rw [hb', he]
    · rw [hv, hb', he]
      rfl
  · rintro ⟨rfl, rfl⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
      (fiscalSteadyLinear_iff L _ m ms ab abs gb gbs _).2 rfl⟩ <;>
      simp only [fiscalSteadySolution, fiscalShortRunSolution, fiscalE, fiscalToT, wavg,
        ReduxLinear.D] <;> field_simp <;> ring

/-- **Existence and uniqueness of the short-run equilibrium** (O&R §10.3): for every combination
of money, productivity and government-spending shocks. -/
theorem fiscalShock_existsUnique (L : ReduxLinear) (m ms g gs ab abs gb gbs : ℝ) :
    ∃! w : ShortVars × SteadyVars, FiscalShockEqm L m ms g gs ab abs gb gbs w.1 w.2 := by
  refine ⟨(fiscalShortRunSolution L m ms g gs ab abs gb gbs, fiscalSteadySolution L
    (fiscalShortRunSolution L m ms g gs ab abs gb gbs).b m ms ab abs gb gbs),
    (fiscalShock_iff L m ms g gs ab abs gb gbs _ _).2 ⟨rfl, rfl⟩, fun w hw => ?_⟩
  obtain ⟨h1, h2⟩ := (fiscalShock_iff L m ms g gs ab abs gb gbs w.1 w.2).1 hw
  exact Prod.ext h1 h2

/-- **The money-only case is the model of §10.1** (O&R p. 696: the linearised equations of
§10.1.5 are unchanged): with no productivity or government-spending shocks the system is
exactly `MoneyShockEqm`. Hence a TEMPORARY productivity shock (`ā = ā* = 0`), which enters no
short-run equation, has no effect on any variable except leisure (O&R p. 697). -/
theorem fiscal_zero_iff_money (L : ReduxLinear) (m ms : ℝ) (u : ShortVars) (v : SteadyVars) :
    FiscalShockEqm L m ms 0 0 0 0 0 0 u v ↔ MoneyShockEqm L m ms u v := by
  have hw : wavg L 0 0 = 0 := by simp [wavg]
  constructor
  · intro h
    obtain ⟨h27, h28, h113, h114, h32, h35, h36, h37, h38, h121, hl⟩ := h
    obtain ⟨l27, l28, l113, l114, l32, l116, l117, l118, l119, l50, l51⟩ := hl
    rw [hw] at h113 h114 l113 l114 l116 l117
    refine ⟨h27, h28, by linarith, by linarith, h32, h35, h36, h37, h38, by linarith,
      ⟨l27, l28, by linarith, by linarith, l32, by linarith, by linarith, by linarith,
        by linarith, l50, l51⟩⟩
  · intro h
    obtain ⟨h27, h28, h30, h31, h32, h35, h36, h37, h38, h55, hl⟩ := h
    obtain ⟨l27, l28, l30, l31, l32, l33, l34, l40, l41, l50, l51⟩ := hl
    refine ⟨h27, h28, by rw [hw]; linarith, by rw [hw]; linarith, h32, h35, h36, h37, h38,
      by linarith, ⟨l27, l28, by rw [hw]; linarith, by rw [hw]; linarith, l32,
        by rw [hw]; linarith, by rw [hw]; linarith, by linarith, by linarith, l50, l51⟩⟩

/-- **The GG schedule with productivity and government spending** (O&R (105), p. 698, and (127),
p. 704): `e = [δ(1+θ)+2θ](c−c*)/(δ(θ²−1)) + (1/(θ−1))[g − g* + (ḡ−ḡ*)/δ] − (ā−ā*)/(δ(1+θ))`. -/
theorem fiscal_gg {L : ReduxLinear} {m ms g gs ab abs gb gbs : ℝ} {u : ShortVars}
    {v : SteadyVars} (h : FiscalShockEqm L m ms g gs ab abs gb gbs u v) :
    u.e = (L.δ * (1 + L.θ) + 2 * L.θ) * (u.c - u.cs) / (L.δ * (L.θ ^ 2 - 1)) +
      1 / (L.θ - 1) * ((g - gs) + (gb - gbs) / L.δ) - (ab - abs) / (L.δ * (1 + L.θ)) := by
  obtain ⟨rfl, -⟩ := (fiscalShock_iff L m ms g gs ab abs gb gbs u v).1 h
  have hθ := L.hθ
  have hδ := L.hδ.ne'
  have hθ1 : L.θ - 1 ≠ 0 := by linarith
  have hθ2 : 1 + L.θ ≠ 0 := by linarith
  have hsq : L.θ ^ 2 - 1 ≠ 0 := by nlinarith
  have hE : L.δ * (1 + L.θ) + 2 ≠ 0 := L.E_pos.ne'
  have hθ0 : L.θ ≠ 0 := by linarith
  simp only [fiscalShortRunSolution, fiscalE, wavg, ReduxLinear.D]
  field_simp
  ring

/-- **World aggregates and the real interest rate** (O&R (104), (107), (123)–(124), (130)): in
every short-run equilibrium `cᵂ = mᵂ`, `yᵂ = mᵂ + gᵂ`, and
`r = ((1+δ)/δ)((āᵂ − ḡᵂ)/2 − mᵂ)`; in the long run `c̄ᵂ = (āᵂ − ḡᵂ)/2`, `ȳᵂ = (āᵂ + ḡᵂ)/2`. -/
theorem fiscal_world {L : ReduxLinear} {m ms g gs ab abs gb gbs : ℝ} {u : ShortVars}
    {v : SteadyVars} (h : FiscalShockEqm L m ms g gs ab abs gb gbs u v) :
    u.cW = wavg L m ms ∧ L.n * u.y + (1 - L.n) * u.ys = wavg L m ms + wavg L g gs ∧
    u.r = (1 + L.δ) / L.δ * ((wavg L ab abs - wavg L gb gbs) / 2 - wavg L m ms) ∧
    v.cW = (wavg L ab abs - wavg L gb gbs) / 2 ∧
    L.n * v.y + (1 - L.n) * v.ys = (wavg L ab abs + wavg L gb gbs) / 2 := by
  obtain ⟨h1, h2, -⟩ := fiscalSteady_consequences h.longrun
  obtain ⟨rfl, -⟩ := (fiscalShock_iff L m ms g gs ab abs gb gbs u v).1 h
  refine ⟨rfl, ?_, rfl, h1, h2⟩
  simp only [fiscalShortRunSolution]
  ring

/-- **The nominal interest rate does not change** (O&R p. 699, "the nominal interest rate doesn't
change: expected deflation exactly offsets the rise in the real interest rate"; T15): in each
country `î = δr/(1+δ) + (p̄ − p) = 0` after any combination of permanent money, productivity and
government-spending shocks. -/
theorem fiscal_nominal_rate_unchanged {L : ReduxLinear} {m ms g gs ab abs gb gbs : ℝ}
    {u : ShortVars} {v : SteadyVars} (h : FiscalShockEqm L m ms g gs ab abs gb gbs u v) :
    L.δ * u.r / (1 + L.δ) + (v.p - u.p) = 0 ∧ L.δ * u.r / (1 + L.δ) + (v.ps - u.ps) = 0 :=
  ⟨nominal_rate_unchanged L.hδ h.eq35 h.eq37 h.longrun.eq50,
    nominal_rate_unchanged L.hδ h.eq36 h.eq38 h.longrun.eq51⟩

/-! ## Productivity shocks: corollaries (105)–(107) -/

/-- **(106) and (107)** (O&R p. 698): with money and productivity shocks only,
`e = {[δ(1+θ)+2θ](m−m*) − (θ−1)(ā−ā*)}/(θδ(1+θ)+2θ)` and `r = ((1+δ)/δ)(āᵂ/2 − mᵂ)`. -/
theorem productivity_eq106_107 {L : ReduxLinear} {m ms ab abs : ℝ} {u : ShortVars}
    {v : SteadyVars} (h : FiscalShockEqm L m ms 0 0 ab abs 0 0 u v) :
    u.e = ((L.δ * (1 + L.θ) + 2 * L.θ) * (m - ms) - (L.θ - 1) * (ab - abs)) /
      (L.θ * L.δ * (1 + L.θ) + 2 * L.θ) ∧
    u.r = (1 + L.δ) / L.δ * (wavg L ab abs / 2 - wavg L m ms) := by
  obtain ⟨rfl, -⟩ := (fiscalShock_iff L m ms 0 0 ab abs 0 0 u v).1 h
  simp only [fiscalShortRunSolution, fiscalE, wavg, ReduxLinear.D]
  constructor <;> ring

/-- **A permanent rise in Home productivity** (O&R pp. 698–699; T23), no money or fiscal shock:
the exchange rate is `e = −(θ−1)ā/D < 0` (the Home currency APPRECIATES, (106)); Home runs a
current-account DEFICIT `b̄ = −(1−n)(θ−1)ā/(δ(1+θ)+2)`; the long-run consumption differential
`(θ−1)ā/D` is positive but below its flexible-price value `(θ−1)ā/(2θ)` ("tempered but not
reversed"); world consumption does not move on impact while the real interest rate rises,
`r = ((1+δ)/δ)nā/2` (107). -/
theorem productivity_corollaries {L : ReduxLinear} {a : ℝ} {u : ShortVars} {v : SteadyVars}
    (h : FiscalShockEqm L 0 0 0 0 a 0 0 0 u v) (ha : 0 < a) :
    u.e = -((L.θ - 1) * a / L.D) ∧ u.e < 0 ∧
    u.b = -((1 - L.n) * (L.θ - 1) * a / L.E) ∧ u.b < 0 ∧
    v.c - v.cs = (L.θ - 1) * a / L.D ∧ 0 < v.c - v.cs ∧
    v.c - v.cs < (L.θ - 1) / (2 * L.θ) * a ∧ u.cW = 0 ∧
    u.r = (1 + L.δ) / L.δ * (L.n * a / 2) ∧ 0 < u.r := by
  have hdiff : v.c - v.cs = u.c - u.cs := by rw [h.eq35, h.eq36]; ring
  obtain ⟨rfl, -⟩ := (fiscalShock_iff L 0 0 0 0 a 0 0 0 u v).1 h
  have hθ := L.hθ
  have hδ := L.hδ
  have hn0 := L.hn0
  have hn : 0 < 1 - L.n := by linarith [L.hn1]
  have hD := L.D_pos
  have hE := L.E_pos
  have hθ1 : 0 < L.θ - 1 := by linarith
  have he : (fiscalShortRunSolution L 0 0 0 0 a 0 0 0).e = -((L.θ - 1) * a / L.D) := by
    simp only [fiscalShortRunSolution, fiscalE]; ring
  have hb : (fiscalShortRunSolution L 0 0 0 0 a 0 0 0).b = -((1 - L.n) * (L.θ - 1) * a / L.E) := by
    simp only [fiscalShortRunSolution, fiscalE]
    rw [ReduxLinear.D_eq]
    have := hE.ne'
    have : L.θ ≠ 0 := by linarith
    field_simp; ring
  have hdc : v.c - v.cs = (L.θ - 1) * a / L.D := by
    rw [hdiff]; simp only [fiscalShortRunSolution, fiscalE, wavg]; ring
  have h1 : 0 < (L.θ - 1) * a / L.D := by positivity
  have h2 : 0 < (1 - L.n) * (L.θ - 1) * a / L.E := by positivity
  refine ⟨he, by rw [he]; linarith, hb, by rw [hb]; linarith, hdc, by rw [hdc]; positivity, ?_, ?_,
    ?_, ?_⟩
  · rw [hdc]
    have hE2 : 2 < L.E := by
      unfold ReduxLinear.E; nlinarith [mul_pos hδ (show (0 : ℝ) < 1 + L.θ by linarith)]
    rw [ReduxLinear.D_eq, div_lt_iff₀ (mul_pos (by linarith) hE)]
    have hpos : 0 < (L.θ - 1) * a := mul_pos hθ1 ha
    have e : (L.θ - 1) / (2 * L.θ) * a * (L.θ * L.E) = (L.θ - 1) * a * L.E / 2 := by
      field_simp
    have : (L.θ - 1) * a * 2 < (L.θ - 1) * a * L.E := by nlinarith
    linarith [e]
  · simp only [fiscalShortRunSolution, wavg]; ring
  · simp only [fiscalShortRunSolution, wavg]; ring
  · simp only [fiscalShortRunSolution, wavg]
    have : 0 < (1 + L.δ) / L.δ := by positivity
    have : 0 < L.n * a / 2 := by positivity
    nlinarith

/-! ## Government spending: corollaries (123)–(130) -/

/-- **(128)–(129) in the book's form** (O&R p. 705): with no money or productivity shocks,
`e = δ(1+θ)[g − g* + (ḡ−ḡ*)/δ]/D` and
`b̄ = (1−n)δ(1+θ)[g − g* + (ḡ−ḡ*)/δ]/(δ(1+θ)+2) − (1−n)(g − g*)`. -/
theorem gov_eq128_129 {L : ReduxLinear} {g gs gb gbs : ℝ} {u : ShortVars} {v : SteadyVars}
    (h : FiscalShockEqm L 0 0 g gs 0 0 gb gbs u v) :
    u.e = L.δ * (1 + L.θ) * ((g - gs) + (gb - gbs) / L.δ) / L.D ∧
    u.b = (1 - L.n) * L.δ * (1 + L.θ) * ((g - gs) + (gb - gbs) / L.δ) / L.E -
      (1 - L.n) * (g - gs) := by
  obtain ⟨rfl, -⟩ := (fiscalShock_iff L 0 0 g gs 0 0 gb gbs u v).1 h
  have hδ := L.hδ.ne'
  have hE := L.E_pos.ne'
  have hθ0 : L.θ ≠ 0 := by linarith [L.hθ]
  simp only [fiscalShortRunSolution, fiscalE, ReduxLinear.D, ReduxLinear.E]
  refine ⟨?_, ?_⟩ <;> field_simp <;> ring

/-- **(122): the Foreign current account is implied** (O&R p. 702): in every short-run
equilibrium, `b̄* = −(n/(1−n)) b̄` (net foreign assets sum to zero, (17)) satisfies
`b̄* = y* − c* + ne − g*`. -/
theorem gov_eq122 {L : ReduxLinear} {m ms g gs ab abs gb gbs : ℝ} {u : ShortVars}
    {v : SteadyVars} (h : FiscalShockEqm L m ms g gs ab abs gb gbs u v) :
    -(L.n / (1 - L.n)) * u.b = u.ys - u.cs + L.n * u.e - gs := by
  have hn : 1 - L.n ≠ 0 := by linarith [L.hn1]
  have h121 := h.eq121
  have h113 := h.eq113
  have h114 := h.eq114
  have h27 := h.eq27
  have h28 := h.eq28
  have h32 := h.eq32
  unfold wavg at h113 h114
  have key : L.n * u.b + (1 - L.n) * (u.ys - u.cs + L.n * u.e - gs) = 0 := by
    rw [h121, h113, h114, h27, h28, h32]; ring
  field_simp
  linarith

/-- **Temporary versus permanent government spending and the current account** (O&R p. 705): a
TEMPORARY relative rise in Home spending (`ḡ = ḡ*`) gives a DEFICIT
`b̄ = −2(1−n)(g − g*)/(δ(1+θ)+2)`; a PERMANENT one (`ḡ − ḡ* = g − g*`) gives a SURPLUS
`b̄ = (1−n)(θ−1)(g − g*)/(δ(1+θ)+2)`. -/
theorem gov_current_account (L : ReduxLinear) {G : ℝ} (hG : 0 < G) :
    (fiscalShortRunSolution L 0 0 G 0 0 0 0 0).b = -(2 * (1 - L.n) * G / L.E) ∧
    (fiscalShortRunSolution L 0 0 G 0 0 0 0 0).b < 0 ∧
    (fiscalShortRunSolution L 0 0 G 0 0 0 G 0).b = (1 - L.n) * (L.θ - 1) * G / L.E ∧
    0 < (fiscalShortRunSolution L 0 0 G 0 0 0 G 0).b := by
  have hθ := L.hθ
  have hδ := L.hδ
  have hn : 0 < 1 - L.n := by linarith [L.hn1]
  have hE := L.E_pos
  have hθ0 : L.θ ≠ 0 := by linarith
  have h1 : (fiscalShortRunSolution L 0 0 G 0 0 0 0 0).b = -(2 * (1 - L.n) * G / L.E) := by
    simp only [fiscalShortRunSolution, fiscalE, ReduxLinear.D, ReduxLinear.E]
    have := hE.ne'; unfold ReduxLinear.E at this
    field_simp; ring
  have h2 : (fiscalShortRunSolution L 0 0 G 0 0 0 G 0).b = (1 - L.n) * (L.θ - 1) * G / L.E := by
    simp only [fiscalShortRunSolution, fiscalE, ReduxLinear.D, ReduxLinear.E]
    have := hE.ne'; unfold ReduxLinear.E at this
    field_simp; ring
  refine ⟨h1, ?_, h2, ?_⟩
  · rw [h1]; have : 0 < 2 * (1 - L.n) * G / L.E := by positivity
    linarith
  · rw [h2]; have : 0 < L.θ - 1 := by linarith
    positivity

/-- **A temporary rise in world government spending** (O&R p. 705): with no money, productivity
or future spending shocks, world consumption does not move, world output rises one for one,
`yᵂ = gᵂ`, and the real interest rate is unchanged, `r = 0`. -/
theorem temporary_world_spending {L : ReduxLinear} {g gs : ℝ} {u : ShortVars} {v : SteadyVars}
    (h : FiscalShockEqm L 0 0 g gs 0 0 0 0 u v) :
    u.cW = 0 ∧ L.n * u.y + (1 - L.n) * u.ys = wavg L g gs ∧ u.r = 0 := by
  obtain ⟨h1, h2, h3, -, -⟩ := fiscal_world h
  refine ⟨by rw [h1]; simp [wavg], by rw [h2]; simp [wavg], by rw [h3]; simp [wavg]⟩

/-- **Permanent government spending under flexible prices** (O&R p. 703): in the long-run system
with `b̄ = 0` and a relative rise `ḡ > ḡ*` in Home spending, the terms of trade deteriorate,
`p̄(h) − ē − p̄*(f) = −(ḡ − ḡ*)/(2θ) < 0`, and relative Home output rises. -/
theorem gov_flex_terms_of_trade {L : ReduxLinear} {m ms gb gbs : ℝ} {v : SteadyVars}
    (h : FiscalSteadyLinear L 0 m ms 0 0 gb gbs v) (hg : gbs < gb) :
    v.ph - v.e - v.pf = -((gb - gbs) / (2 * L.θ)) ∧ v.ph - v.e - v.pf < 0 ∧
      0 < v.y - v.ys := by
  obtain ⟨-, -, hT, -, hy⟩ := fiscalSteady_consequences h
  have hθ : 0 < L.θ := by linarith [L.hθ]
  have hT' : v.ph - v.e - v.pf = -((gb - gbs) / (2 * L.θ)) := by rw [hT]; ring
  have hneg : v.ph - v.e - v.pf < 0 := by
    rw [hT']; have : 0 < (gb - gbs) / (2 * L.θ) := div_pos (by linarith) (by positivity)
    linarith
  refine ⟨hT', hneg, ?_⟩
  rw [hy]; nlinarith

/-! ## Welfare (T24, T26) -/

/-- The first-order change in real utility with a permanent productivity shock, O&R p. 700: (75)
plus the direct effect of lower `κ` on the disutility of effort in every period,
`((θ−1)/θ)(ā/2)(1 + 1/δ)`. -/
noncomputable def dURprod (L : ReduxLinear) (a c y cb yb : ℝ) : ℝ :=
  dUR L c y cb yb + (L.θ - 1) / L.θ * (a / 2) * (1 + 1 / L.δ)

/-- **The welfare derivative with a permanent productivity shock** (T24; O&R p. 700): along
`κ = κ₀(1 − τā)` in every period and log-deviations `c, ŷ, c̄, ȳ`, the derivative of `Uᴿ`
is `dURprod`. -/
theorem fiscal_welfare_hasDerivAt (M : ReduxParams) (a c y cb yb : ℝ) :
    HasDerivAt (fun τ => lifetimeWelfare M.β 0 (M.κ * (1 - τ * a))
      (twoRegime (M.ybar0 * Real.exp (τ * c)) (M.ybar0 * Real.exp (τ * cb)))
      (twoRegime (1 * Real.exp (τ * 0)) (1 * Real.exp (τ * 0)))
      (twoRegime (M.ybar0 * Real.exp (τ * y)) (M.ybar0 * Real.exp (τ * yb))))
      (dURprod (linearOf M) a c y cb yb) 0 := by
  have h := welfare_hasDerivAt M.hβ0.le M.hβ1 0 M.κ a M.ybar0 c cb 0 0 y yb M.ybar0_pos one_pos
    one_pos
  convert h using 1
  unfold dURprod dUR linearOf
  simp only
  rw [beta_div_one_sub M, M.κ_mul_ybar0_sq]
  ring

/-- **A permanent rise in Home productivity raises welfare in BOTH countries** (T24; O&R p. 700,
"one can show", left to the reader): with no money or fiscal shocks,
`dUᴿ_Home = (ā/(2θ))[(θ−1) + (n+θ−1)/δ]` (including the direct effect of lower `κ`) and
`dUᴿ_Foreign = nā/(2θδ)`, both positive for `ā > 0`. -/
theorem productivity_welfare {L : ReduxLinear} {a : ℝ} {u : ShortVars} {v : SteadyVars}
    (h : FiscalShockEqm L 0 0 0 0 a 0 0 0 u v) :
    dURprod L a u.c u.y v.c v.y = a / (2 * L.θ) * ((L.θ - 1) + (L.n + L.θ - 1) / L.δ) ∧
    dUR L u.cs u.ys v.cs v.ys = L.n * a / (2 * L.θ * L.δ) ∧
    (0 < a → 0 < dURprod L a u.c u.y v.c v.y ∧ 0 < dUR L u.cs u.ys v.cs v.ys) := by
  obtain ⟨rfl, rfl⟩ := (fiscalShock_iff L 0 0 0 0 a 0 0 0 u v).1 h
  have hθ := L.hθ
  have hδ := L.hδ
  have hn0 := L.hn0
  have hθ0 : L.θ ≠ 0 := by linarith
  have hδ0 : L.δ ≠ 0 := hδ.ne'
  have hn : 1 - L.n ≠ 0 := by linarith [L.hn1]
  have hE : L.δ * (1 + L.θ) + 2 ≠ 0 := L.E_pos.ne'
  have hθ1 : L.θ + 1 ≠ 0 := by linarith
  have e1 : dURprod L a (fiscalShortRunSolution L 0 0 0 0 a 0 0 0).c
      (fiscalShortRunSolution L 0 0 0 0 a 0 0 0).y
      (fiscalSteadySolution L (fiscalShortRunSolution L 0 0 0 0 a 0 0 0).b 0 0 a 0 0 0).c
      (fiscalSteadySolution L (fiscalShortRunSolution L 0 0 0 0 a 0 0 0).b 0 0 a 0 0 0).y =
      a / (2 * L.θ) * ((L.θ - 1) + (L.n + L.θ - 1) / L.δ) := by
    simp only [dURprod, dUR, fiscalShortRunSolution, fiscalSteadySolution, fiscalE, fiscalToT,
      wavg, ReduxLinear.D]
    field_simp
    ring
  have e2 : dUR L (fiscalShortRunSolution L 0 0 0 0 a 0 0 0).cs
      (fiscalShortRunSolution L 0 0 0 0 a 0 0 0).ys
      (fiscalSteadySolution L (fiscalShortRunSolution L 0 0 0 0 a 0 0 0).b 0 0 a 0 0 0).cs
      (fiscalSteadySolution L (fiscalShortRunSolution L 0 0 0 0 a 0 0 0).b 0 0 a 0 0 0).ys =
      L.n * a / (2 * L.θ * L.δ) := by
    simp only [dUR, fiscalShortRunSolution, fiscalSteadySolution, fiscalE, fiscalToT,
      wavg, ReduxLinear.D]
    field_simp
    ring
  refine ⟨e1, e2, fun ha => ⟨?_, ?_⟩⟩
  · rw [e1]
    have : 0 < L.θ - 1 := by linarith
    have : 0 < L.n + L.θ - 1 := by linarith
    positivity
  · rw [e2]; positivity

/-- **fn 25: an anticipated permanent productivity rise** (O&R p. 699, fn 25): a change in `κ`
learned at date 1 but effective from date 2 leaves every short-run and long-run variable as in an
immediate permanent change (short-run productivity enters no equation of `FiscalShockEqm`); the
welfare derivative then lacks only the date-1 leisure term, which is `((θ−1)/θ)ā/2`. -/
theorem fn25_welfare_hasDerivAt (M : ReduxParams) (a c y cb yb : ℝ) :
    HasDerivAt (fun τ => ∑' s, M.β ^ s * twoRegime
      (periodWelfare 0 M.κ (M.ybar0 * Real.exp (τ * c)) 1 (M.ybar0 * Real.exp (τ * y)))
      (periodWelfare 0 (M.κ * (1 - τ * a)) (M.ybar0 * Real.exp (τ * cb)) 1
        (M.ybar0 * Real.exp (τ * yb))) s)
      (dURprod (linearOf M) a c y cb yb - (M.θ - 1) / M.θ * (a / 2)) 0 := by
  have e : (fun τ => ∑' s, M.β ^ s * twoRegime
      (periodWelfare 0 M.κ (M.ybar0 * Real.exp (τ * c)) 1 (M.ybar0 * Real.exp (τ * y)))
      (periodWelfare 0 (M.κ * (1 - τ * a)) (M.ybar0 * Real.exp (τ * cb)) 1
        (M.ybar0 * Real.exp (τ * yb))) s) = fun τ =>
      periodWelfare 0 (M.κ * (1 - τ * 0)) (M.ybar0 * Real.exp (τ * c)) (1 * Real.exp (τ * 0))
        (M.ybar0 * Real.exp (τ * y)) + M.β / (1 - M.β) *
      periodWelfare 0 (M.κ * (1 - τ * a)) (M.ybar0 * Real.exp (τ * cb)) (1 * Real.exp (τ * 0))
        (M.ybar0 * Real.exp (τ * yb)) := by
    funext τ
    rw [(hasSum_twoRegime M.hβ0.le M.hβ1 _ _).tsum_eq]
    simp
  rw [e]
  have h1 := hasDerivAt_periodWelfare 0 M.κ 0 M.ybar0 c 0 y M.ybar0_pos one_pos
  have h2 := (hasDerivAt_periodWelfare 0 M.κ a M.ybar0 cb 0 yb M.ybar0_pos one_pos).const_mul
    (M.β / (1 - M.β))
  convert h1.add h2 using 1
  unfold dURprod dUR linearOf
  simp only
  rw [beta_div_one_sub M, M.κ_mul_ybar0_sq]
  ring

/-- **Government spending under flexible prices** (T26; O&R p. 703, "a rise in Home government
spending would lower Home welfare … but raise welfare abroad"): in the long-run system with
`b̄ = 0` and a permanent rise `ḡ` in Home spending only, the per-period real-utility changes are
`c̄ − ((θ−1)/θ)ȳ = −ḡ(1 − n/(2θ)) < 0` for Home and `nḡ/(2θ) > 0` for Foreign; Home
consumption falls and output rises, Foreign consumption rises and output is unchanged. -/
theorem gov_flex_welfare {L : ReduxLinear} {m ms gb : ℝ} {v : SteadyVars}
    (h : FiscalSteadyLinear L 0 m ms 0 0 gb 0 v) :
    v.c - (L.θ - 1) / L.θ * v.y = -(gb * (1 - L.n / (2 * L.θ))) ∧
    v.cs - (L.θ - 1) / L.θ * v.ys = L.n * gb / (2 * L.θ) ∧
    (0 < gb → v.c < 0 ∧ 0 < v.y ∧ 0 < v.cs ∧ v.ys = 0) := by
  have hv := (fiscalSteadyLinear_iff L 0 m ms 0 0 gb 0 v).1 h
  subst hv
  have hθ := L.hθ
  have hn0 := L.hn0
  have hn1 := L.hn1
  have hθ0 : L.θ ≠ 0 := by linarith
  have hn : 1 - L.n ≠ 0 := by linarith
  have hc : (fiscalSteadySolution L 0 m ms 0 0 gb 0).c =
      -(gb * (L.n + (1 - L.n) * (L.θ + 1) / L.θ) / 2) := by
    simp only [fiscalSteadySolution, fiscalToT, wavg]; field_simp; ring
  have hy : (fiscalSteadySolution L 0 m ms 0 0 gb 0).y = gb / 2 := by
    simp only [fiscalSteadySolution, fiscalToT, wavg]; field_simp; ring
  have hcs : (fiscalSteadySolution L 0 m ms 0 0 gb 0).cs = L.n * gb / (2 * L.θ) := by
    simp only [fiscalSteadySolution, fiscalToT, wavg]; field_simp; ring
  have hys : (fiscalSteadySolution L 0 m ms 0 0 gb 0).ys = 0 := by
    simp only [fiscalSteadySolution, fiscalToT, wavg]; field_simp; ring
  have hθp : 0 < L.θ := by linarith
  refine ⟨?_, ?_, fun hg => ⟨?_, by rw [hy]; positivity, by rw [hcs]; positivity, hys⟩⟩
  · rw [hc, hy]; field_simp; ring
  · rw [hcs, hys]; ring
  · rw [hc]
    have : 0 < 1 - L.n := by linarith
    have : 0 < gb * (L.n + (1 - L.n) * (L.θ + 1) / L.θ) / 2 := by positivity
    linarith

/-- **Temporary government spending with sticky prices** (T26; O&R p. 706): a temporary rise `g`
in Home spending (no future spending, no money or productivity shock) changes real utility by
`dUᴿ_Home = −g(1 − n/θ) < 0` and `dUᴿ_Foreign = ng/θ > 0`; world welfare falls,
`n dUᴿ_Home + (1−n) dUᴿ_Foreign = ng(1/θ − 1) < 0`. -/
theorem gov_temporary_welfare {L : ReduxLinear} {g : ℝ} {u : ShortVars} {v : SteadyVars}
    (h : FiscalShockEqm L 0 0 g 0 0 0 0 0 u v) :
    dUR L u.c u.y v.c v.y = -(g * (1 - L.n / L.θ)) ∧ dUR L u.cs u.ys v.cs v.ys = L.n * g / L.θ ∧
    L.n * dUR L u.c u.y v.c v.y + (1 - L.n) * dUR L u.cs u.ys v.cs v.ys =
      L.n * g * (1 / L.θ - 1) := by
  obtain ⟨rfl, rfl⟩ := (fiscalShock_iff L 0 0 g 0 0 0 0 0 u v).1 h
  have hθ := L.hθ
  have hδ := L.hδ.ne'
  have hθ0 : L.θ ≠ 0 := by linarith
  have hn : 1 - L.n ≠ 0 := by linarith [L.hn1]
  have hE : L.δ * (1 + L.θ) + 2 ≠ 0 := L.E_pos.ne'
  refine ⟨?_, ?_, ?_⟩ <;>
    simp only [dUR, fiscalShortRunSolution, fiscalSteadySolution, fiscalE, fiscalToT, wavg,
      ReduxLinear.D] <;> field_simp <;> ring

/-- **Future government spending with sticky prices** (T26; O&R pp. 704–706): a rise `ḡ` in Home
spending from date 2 on (announced at date 1, no current spending) changes real utility by
`dUᴿ_Home = −(ḡ/δ)(1 − n/(2θ))` and `dUᴿ_Foreign = nḡ/(2θδ)`: exactly the flexible-price
per-period effects summed over dates `≥ 2`; every date-1 effect cancels. -/
theorem gov_future_welfare {L : ReduxLinear} {gb : ℝ} {u : ShortVars} {v : SteadyVars}
    (h : FiscalShockEqm L 0 0 0 0 0 0 gb 0 u v) :
    dUR L u.c u.y v.c v.y = -(gb / L.δ * (1 - L.n / (2 * L.θ))) ∧
    dUR L u.cs u.ys v.cs v.ys = L.n * gb / (2 * L.θ * L.δ) := by
  obtain ⟨rfl, rfl⟩ := (fiscalShock_iff L 0 0 0 0 0 0 gb 0 u v).1 h
  have hθ := L.hθ
  have hδ := L.hδ.ne'
  have hθ0 : L.θ ≠ 0 := by linarith
  have hθ1 : L.θ + 1 ≠ 0 := by linarith
  have hn : 1 - L.n ≠ 0 := by linarith [L.hn1]
  have hE : L.δ * (1 + L.θ) + 2 ≠ 0 := L.E_pos.ne'
  refine ⟨?_, ?_⟩ <;>
    simp only [dUR, fiscalShortRunSolution, fiscalSteadySolution, fiscalE, fiscalToT, wavg,
      ReduxLinear.D] <;> field_simp <;> ring

/-- **Permanent government spending with sticky prices** (T26; O&R p. 706, "overall Foreign
benefits and Home loses when Home's government spends more"): a permanent rise `g = ḡ` in Home
spending changes real utility by the sum of the temporary and future effects,
`dUᴿ_Home = −g(1 − n/θ) − (g/δ)(1 − n/(2θ)) < 0` and `dUᴿ_Foreign = ng/θ + ng/(2θδ) > 0`. -/
theorem gov_permanent_welfare {L : ReduxLinear} {g : ℝ} {u : ShortVars} {v : SteadyVars}
    (h : FiscalShockEqm L 0 0 g 0 0 0 g 0 u v) (hg : 0 < g) :
    dUR L u.c u.y v.c v.y = -(g * (1 - L.n / L.θ)) - g / L.δ * (1 - L.n / (2 * L.θ)) ∧
    dUR L u.cs u.ys v.cs v.ys = L.n * g / L.θ + L.n * g / (2 * L.θ * L.δ) ∧
    dUR L u.c u.y v.c v.y < 0 ∧ 0 < dUR L u.cs u.ys v.cs v.ys := by
  obtain ⟨rfl, rfl⟩ := (fiscalShock_iff L 0 0 g 0 0 0 g 0 u v).1 h
  have hθ := L.hθ
  have hδ := L.hδ
  have hn0 := L.hn0
  have hn1 := L.hn1
  have hθ0 : L.θ ≠ 0 := by linarith
  have hθ1 : L.θ + 1 ≠ 0 := by linarith
  have hn : 1 - L.n ≠ 0 := by linarith
  have hE : L.δ * (1 + L.θ) + 2 ≠ 0 := L.E_pos.ne'
  have e1 : dUR L (fiscalShortRunSolution L 0 0 g 0 0 0 g 0).c
      (fiscalShortRunSolution L 0 0 g 0 0 0 g 0).y
      (fiscalSteadySolution L (fiscalShortRunSolution L 0 0 g 0 0 0 g 0).b 0 0 0 0 g 0).c
      (fiscalSteadySolution L (fiscalShortRunSolution L 0 0 g 0 0 0 g 0).b 0 0 0 0 g 0).y =
      -(g * (1 - L.n / L.θ)) - g / L.δ * (1 - L.n / (2 * L.θ)) := by
    simp only [dUR, fiscalShortRunSolution, fiscalSteadySolution, fiscalE, fiscalToT, wavg,
      ReduxLinear.D]
    field_simp; ring
  have e2 : dUR L (fiscalShortRunSolution L 0 0 g 0 0 0 g 0).cs
      (fiscalShortRunSolution L 0 0 g 0 0 0 g 0).ys
      (fiscalSteadySolution L (fiscalShortRunSolution L 0 0 g 0 0 0 g 0).b 0 0 0 0 g 0).cs
      (fiscalSteadySolution L (fiscalShortRunSolution L 0 0 g 0 0 0 g 0).b 0 0 0 0 g 0).ys =
      L.n * g / L.θ + L.n * g / (2 * L.θ * L.δ) := by
    simp only [dUR, fiscalShortRunSolution, fiscalSteadySolution, fiscalE, fiscalToT, wavg,
      ReduxLinear.D]
    field_simp; ring
  have hθp : 0 < L.θ := by linarith
  refine ⟨e1, e2, ?_, ?_⟩
  · rw [e1]
    have h1 : 0 < 1 - L.n / L.θ := by rw [sub_pos, div_lt_one hθp]; linarith
    have h2 : 0 < 1 - L.n / (2 * L.θ) := by rw [sub_pos, div_lt_one (by positivity)]; linarith
    have : 0 < g * (1 - L.n / L.θ) := mul_pos hg h1
    have : 0 < g / L.δ * (1 - L.n / (2 * L.θ)) := by positivity
    linarith
  · rw [e2]; positivity

end ObstfeldRogoff.StickyPriceModels.ReduxFiscalProductivity

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The two-country model with preset wages (§10.4.2)

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §10.4.2,
pp. 709–711. Each country has a continuum of differentiated final goods and of differentiated
labour inputs; the representative Home firm produces with the CES technology (142),
`y(j) = ½[2∫₀^{1/2} ℓ(z)^{(φ−1)/φ}dz]^{φ/(φ−1)}`, `φ > 1`, and each worker is the monopoly supplier
of its labour type, with utility (141).

* **The firm (142).** On finitely many labour types with positive weights summing to one (the
  normalised measure `2dz` on `[0, ½]`), the minimum cost of output `y` is `W y`, with `W` the CES
  wage index, attained exactly by the CES labour demands (`firm_min_cost`, `firm_cost_eq_iff`); so
  marginal cost is the constant `W`, and under symmetric wages `W = w` and `y = ℓ/2`.
* **Markup pricing.** Facing constant-elasticity demand, the profit `(p − W)(p/P)^{−θ}Y` has the
  UNIQUE maximiser `p = θW/(θ−1)` (`markup_isGreatest`; Bernoulli's inequality).
* **The worker.** On its labour-demand curve, real labour income is
  `(W/P) h^{(φ−1)/φ} H^{1/φ}` (`labour_income_on_demand`): the worker's problem IS the household
  problem (12) of `ReduxPrimitives` with `θ` replaced by `φ` and the demand shifter
  `Z = (W/P) H^{1/φ}` (profits enter as lump-sum income), so `HouseholdEnv.isOptimal_iff` gives
  necessity and sufficiency of its first-order conditions over a genuine infinite horizon; under
  symmetry the labour condition is `w/P = (φ/(φ−1)) κ h C` (`wage_foc_symmetric`).
* **Equivalence with §10.1.** Markup + wage condition + demand give EXACTLY (15) with `κ`
  replaced by `κφ/(φ−1)` (`presetWage_labour_iff`), so the flexible-price model is the redux model
  with parameters `wageParams`: its steady state exists and is unique for every `B̄`, the
  symmetric steady state is (143) (`wageParams_ybar0`), below the §10.1 level, the log-linear
  labour condition is (33) exactly, and income = wages + profits gives (40) unchanged. With
  nominal wages preset, the markup rule presets goods prices EXACTLY even though they are
  flexible (`markup_log_exact`), so the short-run linear system is `MoneyShockEqm` and all the
  results of §10.1.7–§10.1.8 transfer (`presetWage_iff_money`). Workers meet labour demand at the
  preset wage iff the real wage covers the marginal disutility, which holds strictly at the steady
  state (markup `φ/(φ−1)`).
* **Pricing to market (144).** With linear technology the two markets separate; the unique optimum
  is `p(h) = θ_H w/(θ_H−1)` at home and `𝓔p*(h) = θ_F w/(θ_F−1)` abroad; with equal elasticities
  the law of one price holds endogenously, `p(h) = 𝓔p*(h)`, and pass-through is complete (the
  foreign-currency price has elasticity `−1` with respect to `𝓔`) even when the elasticities
  differ (`ptm_optimal`, `ptm_pass_through`).
* **The normalisation of (141)–(142)** (survey flag): (143) requires `ℓ` in (141) to be the
  worker's TOTAL hours (`= y`); with the per-firm reading the effective `κ` is `4κ` and output
  halves (`normalisation_flag`).
-/

namespace ObstfeldRogoff.StickyPriceModels.ReduxPresetWages

open Real Filter Topology ReduxPrimitives ReduxLogLinear ReduxSteadyState ReduxMoneyShocks
  ReduxWelfare

/-! ## The firm (142): cost minimisation -/

/-- The Home firm's output (142), O&R p. 710: `y = ½ · [Σ ωᵢ ℓᵢ^{(φ−1)/φ}]^{φ/(φ−1)}` on finitely
many labour types with weights `ω` (the normalised measure `2dz` on `[0, ½]`). -/
noncomputable def firmOutput {ι : Type*} [Fintype ι] (φ : ℝ) (ω ℓ : ι → ℝ) : ℝ :=
  cesQuantityIndex φ ω ℓ / 2

/-- The firm's wage bill `∫₀^{1/2} w(z) ℓ(z) dz = ½ Σ ωᵢ wᵢ ℓᵢ`, O&R p. 710. -/
noncomputable def wageBill {ι : Type*} [Fintype ι] (ω w ℓ : ι → ℝ) : ℝ :=
  cesExpenditure ω w ℓ / 2

/-- **The cost of output is at least `W y`** (O&R p. 710; CES duality, T1): for positive wages
and inputs, the wage bill is at least the wage index `W = [Σ ωᵢ wᵢ^{1−φ}]^{1/(1−φ)}` times
output. -/
theorem firm_cost_ge {ι : Type*} [Fintype ι] [Nonempty ι] {φ : ℝ} (hφ : 1 < φ) {ω w ℓ : ι → ℝ}
    (hω : ∀ i, 0 < ω i) (hw : ∀ i, 0 < w i) (hℓ : ∀ i, 0 < ℓ i) :
    cesPriceIndex φ ω w * firmOutput φ ω ℓ ≤ wageBill ω w ℓ := by
  have h := ces_expenditure_ge hφ hω hw hℓ
  unfold firmOutput wageBill
  linarith

/-- **The cost-minimising inputs are exactly the CES labour demands** (O&R (135) analogue,
p. 710): the wage bill equals `W y` IFF `ℓᵢ = (wᵢ/W)^{−φ} · 2y`. -/
theorem firm_cost_eq_iff {ι : Type*} [Fintype ι] [Nonempty ι] {φ : ℝ} (hφ : 1 < φ)
    {ω w ℓ : ι → ℝ} (hω : ∀ i, 0 < ω i) (hw : ∀ i, 0 < w i) (hℓ : ∀ i, 0 < ℓ i) :
    wageBill ω w ℓ = cesPriceIndex φ ω w * firmOutput φ ω ℓ ↔
      ℓ = cesDemandBundle φ ω w (2 * firmOutput φ ω ℓ) := by
  have h := ces_expenditure_eq_iff hφ hω hw hℓ
  unfold wageBill firmOutput at *
  have e : 2 * (cesQuantityIndex φ ω ℓ / 2) = cesQuantityIndex φ ω ℓ := by ring
  rw [e]
  constructor
  · intro h1; exact h.1 (by linarith)
  · intro h1; have := h.2 h1; linarith

/-- **Marginal cost is the wage index** (O&R p. 710): for every `y > 0` the minimum wage bill
over positive inputs producing `y` is exactly `W y`. -/
theorem firm_min_cost {ι : Type*} [Fintype ι] [Nonempty ι] {φ : ℝ} (hφ : 1 < φ) {ω w : ι → ℝ}
    (hω : ∀ i, 0 < ω i) (hw : ∀ i, 0 < w i) {y : ℝ} (hy : 0 < y) :
    IsLeast {Z | ∃ ℓ : ι → ℝ, (∀ i, 0 < ℓ i) ∧ firmOutput φ ω ℓ = y ∧ Z = wageBill ω w ℓ}
      (cesPriceIndex φ ω w * y) := by
  have hW := cesPriceIndex_pos (θ := φ) hω hw
  refine ⟨⟨cesDemandBundle φ ω w (2 * y), fun i => cesDemand_pos φ (hw i) hW (by linarith),
    ?_, ?_⟩, ?_⟩
  · unfold firmOutput
    rw [cesQuantityIndex_demandBundle hφ hω hw (by linarith)]
    ring
  · unfold wageBill
    rw [cesExpenditure_demandBundle hφ.ne' hω hw]
    ring
  · rintro Z ⟨ℓ, hℓ, hy', rfl⟩
    have := firm_cost_ge hφ hω hw hℓ
    rw [hy'] at this
    exact this

/-- **Symmetric wages and inputs** (O&R p. 710, "when all domestic labor inputs are used
symmetrically at level `ℓ`, `y = ℓ/2`"): with weights summing to one, the wage index of equal
wages `w` is `w`, and equal inputs `ℓ` produce `ℓ/2`. -/
theorem symmetric_firm {ι : Type*} [Fintype ι] [Nonempty ι] {φ : ℝ} (hφ : 1 < φ) {ω : ι → ℝ}
    (hsum : ∑ i, ω i = 1) {w ℓ : ℝ} (hw : 0 < w) (hℓ : 0 < ℓ) :
    cesPriceIndex φ ω (fun _ => w) = w ∧ firmOutput φ ω (fun _ => ℓ) = ℓ / 2 := by
  have hφ1 : 1 - φ ≠ 0 := by linarith
  have hφ2 : φ - 1 ≠ 0 := by linarith
  have hφ0 : φ ≠ 0 := by linarith
  constructor
  · unfold cesPriceIndex
    rw [← Finset.sum_mul, hsum, one_mul, ← rpow_mul hw.le]
    rw [show (1 - φ) * (1 / (1 - φ)) = 1 by field_simp, rpow_one]
  · unfold firmOutput cesQuantityIndex
    rw [← Finset.sum_mul, hsum, one_mul, ← rpow_mul hℓ.le]
    rw [show (φ - 1) / φ * (φ / (φ - 1)) = 1 by field_simp, rpow_one]

/-! ## Markup pricing -/

/-- **Markup pricing is the unique optimum** (O&R p. 710, `p = θw/(θ−1)`): for `θ > 1`, marginal
cost `W > 0`, price index `P > 0` and demand level `Y > 0`, the profit
`(p − W)(p/P)^{−θ}Y` is maximised over `p > 0` exactly at `p* = θW/(θ−1)`: it is at most the
profit at `p*`, strictly unless `p = p*`. -/
theorem markup_isGreatest {θ W P Y : ℝ} (hθ : 1 < θ) (hW : 0 < W) (hP : 0 < P) (hY : 0 < Y)
    {p : ℝ} (hp : 0 < p) :
    (p - W) * cesDemand θ p P Y ≤ (θ * W / (θ - 1) - W) * cesDemand θ (θ * W / (θ - 1)) P Y ∧
    (p ≠ θ * W / (θ - 1) →
      (p - W) * cesDemand θ p P Y < (θ * W / (θ - 1) - W) * cesDemand θ (θ * W / (θ - 1)) P Y) := by
  have hθ1 : 0 < θ - 1 := by linarith
  have hθ0 : 0 < θ := by linarith
  set ps := θ * W / (θ - 1) with hps
  have hpspos : 0 < ps := by positivity
  set x := p / ps with hx
  have hxpos : 0 < x := div_pos hp hpspos
  have hpx : p = ps * x := by rw [hx]; field_simp
  have hWps : W = ps * ((θ - 1) / θ) := by rw [hps]; field_simp
  set A := (ps / P) ^ (-θ) * Y with hA
  have hApos : 0 < A := mul_pos (rpow_pos_of_pos (div_pos hpspos hP) _) hY
  have hd : cesDemand θ p P Y = x ^ (-θ) * A := by
    unfold cesDemand
    rw [hA, hpx, show ps * x / P = x * (ps / P) by ring,
      mul_rpow hxpos.le (div_pos hpspos hP).le]
    ring
  have hds : cesDemand θ ps P Y = A := by unfold cesDemand; rw [hA]
  rw [hd, hds]
  have hxθ : 0 < x ^ θ := rpow_pos_of_pos hxpos θ
  have hinv : x ^ (-θ) = 1 / x ^ θ := by rw [rpow_neg hxpos.le, one_div]
  -- Bernoulli: `x^θ ≥ 1 + θ(x − 1)`
  have key : ∀ strict : Bool, (strict = true → x ≠ 1) →
      (if strict then θ * x - (θ - 1) < x ^ θ else θ * x - (θ - 1) ≤ x ^ θ) := by
    intro strict hs
    cases strict with
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      rcases eq_or_ne x 1 with h1 | h1
      · rw [h1, one_rpow]; linarith
      · have := one_add_mul_self_lt_rpow_one_add (s := x - 1) (by linarith) (sub_ne_zero.2 h1) hθ
        rw [show 1 + (x - 1) = x by ring] at this
        linarith
    | true =>
      simp only [↓reduceIte]
      have h1 := hs rfl
      have := one_add_mul_self_lt_rpow_one_add (s := x - 1) (by linarith) (sub_ne_zero.2 h1) hθ
      rw [show 1 + (x - 1) = x by ring] at this
      linarith
  have e1 : (p - W) * (x ^ (-θ) * A) = ps / θ * A * ((θ * x - (θ - 1)) / x ^ θ) := by
    rw [hinv, hpx, hWps]; field_simp
  have e2 : (ps - W) * A = ps / θ * A * 1 := by rw [hWps]; field_simp; ring
  have hc : 0 < ps / θ * A := by positivity
  constructor
  · rw [e1, e2]
    apply mul_le_mul_of_nonneg_left _ hc.le
    rw [div_le_one hxθ]
    simpa using key false (by simp)
  · intro hne
    have hx1 : x ≠ 1 := by
      intro h; apply hne; rw [hpx, h, mul_one]
    rw [e1, e2]
    apply mul_lt_mul_of_pos_left _ hc
    rw [div_lt_one hxθ]
    simpa using key true (fun _ => hx1)

/-! ## The worker -/

/-- **Labour income on the labour-demand curve** (O&R p. 710 and (135)–(136)): if the worker's
hours are `h = (w/W)^{−φ} H`, its real labour income is
`(w/P) h = (W/P) h^{(φ−1)/φ} H^{1/φ}`. Hence the worker's budget is the household budget (8) of
§10.1 with `θ` replaced by `φ` and demand shifter `Z = (W/P)H^{1/φ}`. -/
theorem labour_income_on_demand {φ w W P h H : ℝ} (hφ : φ ≠ 0) (hw : 0 < w) (hW : 0 < W)
    (hh : 0 < h) (hH : 0 < H) (hd : h = cesDemand φ w W H) :
    w / P * h = W / P * (h ^ ((φ - 1) / φ) * H ^ (1 / φ)) := by
  have hq : 0 < w / W := div_pos hw hW
  have hd' : h = cesDemand φ (w / W) 1 H := by
    rw [hd]; unfold cesDemand; rw [div_one]
  have h1 := revenue_on_demand hφ hq hh hH hd'
  have e : w / P * h = W / P * (w / W * h) := by field_simp
  rw [e, h1]

/-- **The worker's problem is the household problem of §10.1 with `θ → φ`** (O&R p. 710:
"the first-order condition governing the individual's labor-leisure decision is analogous to
eq. (136)"): for the environment with elasticity `φ`, demand shifter `Z_t = (W_t/P_t)H_t^{1/φ}`
and lump-sum income (profits) netted into `τ`, an admissible plan is optimal IFF it satisfies the
Euler equation, money demand, the labour condition and the transversality condition (genuine
infinite horizon; `HouseholdEnv.isOptimal_iff`). -/
theorem worker_isOptimal_iff {E : HouseholdEnv} {q : HouseholdPlan} (hreg : E.Regular) :
    E.IsOptimal q ↔ E.Admissible q ∧ E.EulerCond q ∧ E.MoneyCond q ∧ E.LabourCond q ∧
      E.Transversality (E.wealthPath q) :=
  HouseholdEnv.isOptimal_iff hreg

/-- **The symmetric wage condition** (O&R p. 710; survey T32): with `Z = (W/P)H^{1/φ}` and
symmetry `h = H`, the worker's labour condition `h^{(φ+1)/φ} = ((φ−1)/(φκ)) Z/C`
(`labourCond_iff_book`) holds IFF `W/P = (φ/(φ−1)) κ h C`. -/
theorem wage_foc_symmetric {φ κ h C WP : ℝ} (hφ : 1 < φ) (hκ : 0 < κ) (hh : 0 < h)
    (hC : 0 < C) :
    h ^ ((φ + 1) / φ) = (φ - 1) / (φ * κ) * (WP * h ^ (1 / φ)) / C ↔
      WP = φ / (φ - 1) * κ * h * C := by
  have hφ0 : φ ≠ 0 := by linarith
  have hφ1 : φ - 1 ≠ 0 := by linarith
  rw [rpow_succ_div hφ0 hh]
  have hr := (rpow_pos_of_pos hh (1 / φ)).ne'
  constructor
  · intro h1
    field_simp at h1
    field_simp
    linarith
  · intro h1
    rw [h1]
    field_simp

/-! ## Equivalence with the model of §10.1 -/

/-- **Markup + wage condition + demand give (15) with `κ → κφ/(φ−1)`** (O&R pp. 710–711; survey
T32): if the relative price is the markup over the real wage, `q = (θ/(θ−1)) ω`, the real wage
satisfies the symmetric wage condition `ω = (φ/(φ−1)) κ y C` (hours `= y`), and output is on the
demand curve `y = q^{−θ}Cᵂ`, then `y^{(θ+1)/θ} = ((θ−1)/(θκ′))(Cᵂ)^{1/θ}/C` with
`κ′ = κφ/(φ−1)` — exactly the labour–leisure condition (15) of §10.1 with `κ′` in place of `κ`. -/
theorem presetWage_labour_iff {θ φ κ q ω y C X : ℝ} (hθ : 1 < θ) (hφ : 1 < φ) (hκ : 0 < κ)
    (hq : 0 < q) (hy : 0 < y) (hC : 0 < C) (hX : 0 < X) (hmarkup : q = θ / (θ - 1) * ω)
    (hdem : y = cesDemand θ q 1 X) :
    ω = φ / (φ - 1) * κ * y * C ↔
      y ^ ((θ + 1) / θ) = (θ - 1) / (θ * (κ * φ / (φ - 1))) * X ^ (1 / θ) / C := by
  have hθ0 : θ ≠ 0 := by linarith
  have hθ1 : θ - 1 ≠ 0 := by linarith
  have hφ1 : φ - 1 ≠ 0 := by linarith
  have hφ0 : φ ≠ 0 := by linarith
  have hXr : X ^ (1 / θ) = q * y ^ (1 / θ) := by
    have hX' : X = q ^ θ * y := by
      rw [hdem]; unfold cesDemand
      rw [div_one, rpow_neg hq.le]
      have := (rpow_pos_of_pos hq θ).ne'
      field_simp
    rw [hX', mul_rpow (rpow_nonneg hq.le _) hy.le, ← rpow_mul hq.le, mul_one_div_cancel hθ0,
      rpow_one]
  rw [rpow_succ_div hθ0 hy, hXr]
  have hr := (rpow_pos_of_pos hy (1 / θ)).ne'
  rw [hmarkup]
  constructor
  · intro h; rw [h]; field_simp
  · intro h
    field_simp at h
    field_simp
    linarith

/-- The parameters of §10.1 that reproduce the preset-wage economy (O&R p. 710): the same
`β, χ, θ, n`, and effort weight `κ′ = κφ/(φ−1)`. -/
noncomputable def wageParams (M : ReduxParams) {φ : ℝ} (hφ : 1 < φ) : ReduxParams :=
  ⟨M.β, M.χ, M.κ * φ / (φ - 1), M.θ, M.n, M.hβ0, M.hβ1, M.hχ,
    div_pos (mul_pos M.hκ (by linarith)) (by linarith), M.hθ, M.hn0, M.hn1⟩

/-- **(143): the symmetric steady state with preset wages**, O&R p. 710: the steady state of the
flexible-price preset-wage economy (which is the §10.1 steady state for `wageParams`, existing
and unique for every `B̄` by `exists_unique_steady`) has
`ȳ₀ = ȳ₀* = [((φ−1)/φ)((θ−1)/θ)/κ]^{1/2}`, strictly below the §10.1 level `[(θ−1)/(θκ)]^{1/2}`
("output is lower due to monopoly distortions in both the labor market and the output
market"). -/
theorem wageParams_ybar0 (M : ReduxParams) {φ : ℝ} (hφ : 1 < φ) :
    (wageParams M hφ).ybar0 = Real.sqrt ((φ - 1) / φ * ((M.θ - 1) / M.θ) / M.κ) ∧
    (wageParams M hφ).ybar0 < M.ybar0 ∧
    IsSteadyState (wageParams M hφ) 0 (symmetricSteady (wageParams M hφ)) := by
  have hθ := M.hθ
  have hκ := M.hκ
  have hφ0 : φ ≠ 0 := by linarith
  have hφ1 : φ - 1 ≠ 0 := by linarith
  have hθ0 : M.θ ≠ 0 := by linarith
  have e : (wageParams M hφ).K = (φ - 1) / φ * ((M.θ - 1) / M.θ) / M.κ := by
    simp only [ReduxParams.K, wageParams]
    field_simp
  refine ⟨by rw [ReduxParams.ybar0, e], ?_, (isSteadyState_zero_iff _ _).2 rfl⟩
  unfold ReduxParams.ybar0
  apply Real.sqrt_lt_sqrt (wageParams M hφ).K_pos.le
  rw [e]
  unfold ReduxParams.K
  have h1 : (φ - 1) / φ < 1 := by rw [div_lt_one (by linarith)]; linarith
  have h2 : 0 < (M.θ - 1) / M.θ / M.κ := div_pos (div_pos (by linarith) (by linarith)) hκ
  have : (φ - 1) / φ * ((M.θ - 1) / M.θ) / M.κ = (φ - 1) / φ * ((M.θ - 1) / M.θ / M.κ) := by
    ring
  rw [this, show (M.θ - 1) / (M.θ * M.κ) = (M.θ - 1) / M.θ / M.κ by field_simp]
  nlinarith

/-- **The log-linear labour condition is (33), exactly** (O&R p. 710; survey T32): since the
preset-wage labour condition is (15) with `K′ = (θ−1)/(θκ′)`, log changes satisfy
`(θ+1)Δlog y = −θΔlog C + Δlog Cᵂ` exactly. -/
theorem presetWage_labour_log_exact {θ φ κ y0 y1 C0 C1 X0 X1 : ℝ} (hθ : 1 < θ) (hφ : 1 < φ)
    (hκ : 0 < κ) (hy0 : 0 < y0) (hy1 : 0 < y1) (hC0 : 0 < C0) (hC1 : 0 < C1) (hX0 : 0 < X0)
    (hX1 : 0 < X1)
    (h0 : y0 ^ ((θ + 1) / θ) = (θ - 1) / (θ * (κ * φ / (φ - 1))) * X0 ^ (1 / θ) / C0)
    (h1 : y1 ^ ((θ + 1) / θ) = (θ - 1) / (θ * (κ * φ / (φ - 1))) * X1 ^ (1 / θ) / C1) :
    (θ + 1) * (Real.log y1 - Real.log y0) =
      -θ * (Real.log C1 - Real.log C0) + (Real.log X1 - Real.log X0) := by
  have hK : 0 < (θ - 1) / (θ * (κ * φ / (φ - 1))) :=
    div_pos (by linarith) (mul_pos (by linarith) (div_pos (mul_pos hκ (by linarith))
      (by linarith)))
  exact labour_log_exact (by linarith) hK hy0 hy1 hC0 hC1 hX0 hX1 h0 h1

/-- **Income = wages + profits, so (40) is unchanged** (O&R p. 710: "Home agents each hold equal
shares of a portfolio of all Home firms"): with hours equal to output, `w y + (p − w) y = p y`,
so the steady-state budget is `C = δB + p(h)y/P` as in (20). -/
theorem wage_profit_income {w p y P : ℝ} : (w * y + (p - w) * y) / P = p * y / P := by ring

/-- **Preset wages preset goods prices, exactly** (O&R p. 710: "if final-goods prices are flexible,
wages are preset …"): with the markup rule `p = θw/(θ−1)` at both dates, the log change of the
goods price equals the log change of the wage; with the wage preset, `p₁ = p₀` exactly although
the goods price is flexible. -/
theorem markup_log_exact {θ w0 w1 : ℝ} (hθ : 1 < θ) (hw0 : 0 < w0) (hw1 : 0 < w1) :
    Real.log (θ * w1 / (θ - 1)) - Real.log (θ * w0 / (θ - 1)) = Real.log w1 - Real.log w0 ∧
      (w1 = w0 → θ * w1 / (θ - 1) = θ * w0 / (θ - 1)) := by
  have hθ0 : 0 < θ := by linarith
  have hθ1 : 0 < θ - 1 := by linarith
  refine ⟨?_, fun h => by rw [h]⟩
  rw [mul_div_assoc, mul_div_assoc, Real.log_mul hθ0.ne' (div_pos hw1 hθ1).ne',
    Real.log_mul hθ0.ne' (div_pos hw0 hθ1).ne', Real.log_div hw1.ne' hθ1.ne',
    Real.log_div hw0.ne' hθ1.ne']
  ring

variable (L : ReduxLinear) in
/-- **The short-run system with preset wages** (O&R p. 710): wages are preset (log deviations
`w = w* = 0`), goods prices follow the markup exactly (`p(h) = w`, `p*(f) = w*`,
`markup_log_exact`), and otherwise the date-1 equations and the long run are those of §10.1.7. -/
structure PresetWageEqm (m ms wh wf ph pf : ℝ) (u : ShortVars) (v : SteadyVars) : Prop where
  preset : wh = 0
  preset_star : wf = 0
  markup : ph = wh
  markup_star : pf = wf
  eq27 : u.p = L.n * ph + (1 - L.n) * (u.e + pf)
  eq28 : u.ps = L.n * (ph - u.e) + (1 - L.n) * pf
  eq30 : u.y = L.θ * (u.p - ph) + u.cW
  eq31 : u.ys = L.θ * (u.ps - pf) + u.cW
  eq32 : u.cW = L.n * u.c + (1 - L.n) * u.cs
  eq35 : v.c = u.c + L.δ / (1 + L.δ) * u.r
  eq36 : v.cs = u.cs + L.δ / (1 + L.δ) * u.r
  eq37 : m - u.p = u.c - u.r / (1 + L.δ) - (v.p - u.p) / L.δ
  eq38 : ms - u.ps = u.cs - u.r / (1 + L.δ) - (v.ps - u.ps) / L.δ
  eq55 : u.b = u.y - u.c + (ph - u.p)
  longrun : SteadyLinear L u.b m ms v

/-- **With preset wages the effects of money shocks are exactly those of §10.1** (O&R p. 710:
"the effects of a surprise permanent money increase on both consumption differentials and the
exchange rate are the same as in section 10.1"): `PresetWageEqm` holds IFF wages and goods prices
are unchanged and `MoneyShockEqm` holds; hence (by `moneyShock_iff`) the equilibrium exists, is
unique, and is given by (65)–(74). -/
theorem presetWage_iff_money (L : ReduxLinear) (m ms wh wf ph pf : ℝ) (u : ShortVars)
    (v : SteadyVars) :
    PresetWageEqm L m ms wh wf ph pf u v ↔
      wh = 0 ∧ wf = 0 ∧ ph = 0 ∧ pf = 0 ∧ MoneyShockEqm L m ms u v := by
  constructor
  · rintro ⟨h1, h2, h3, h4, h27, h28, h30, h31, h32, h35, h36, h37, h38, h55, hl⟩
    subst h1 h2
    subst h3 h4
    refine ⟨rfl, rfl, rfl, rfl, h27, h28, h30, h31, h32, h35, h36, h37, h38, ?_, hl⟩
    rw [h55, h27]; ring
  · rintro ⟨rfl, rfl, rfl, rfl, h⟩
    exact ⟨rfl, rfl, rfl, rfl, h.eq27, h.eq28, h.eq30, h.eq31, h.eq32, h.eq35, h.eq36, h.eq37,
      h.eq38, by rw [h.eq55, h.eq27]; ring, h.longrun⟩

/-- **Workers meet labour demand at the preset wage iff the real wage covers the marginal
disutility** (O&R p. 709 for §10.4.1, and p. 710): a worker with a fixed real wage `ω > 0`
facing demand `h_d` prefers supplying `h_d` to any `h ∈ [0, h_d]` IFF `κ h_d ≤ ω/C`
(`meet_demand_iff`). At the steady state the real wage exceeds the marginal disutility by the
markup `φ/(φ−1) > 1`: `ω/C = (φ/(φ−1))κh > κh`. -/
theorem worker_meets_demand {ω C κ hd : ℝ} (hω : 0 < ω) (hC : 0 < C) (hκ : 0 < κ) :
    (∀ h, 0 ≤ h → h ≤ hd → ω * h / C - κ / 2 * h ^ 2 ≤ ω * hd / C - κ / 2 * hd ^ 2) ↔
      κ * hd ≤ ω / C :=
  meet_demand_iff hω hC hκ

/-- **At the steady state the real wage strictly exceeds the marginal disutility of work**
(O&R p. 709, "the marginal utility of the initial real wage exceeds the marginal disutility from
labor"): if `ω = (φ/(φ−1))κhC` with `φ > 1`, `κ, h, C > 0`, then `κh < ω/C`. -/
theorem steady_wage_exceeds_mrs {φ κ h C ω : ℝ} (hφ : 1 < φ) (hκ : 0 < κ) (hh : 0 < h)
    (hC : 0 < C) (hω : ω = φ / (φ - 1) * κ * h * C) : κ * h < ω / C := by
  rw [hω]
  have hφ1 : 0 < φ - 1 := by linarith
  have e : φ / (φ - 1) * κ * h * C / C = φ / (φ - 1) * (κ * h) := by field_simp
  rw [e]
  have : 1 < φ / (φ - 1) := by rw [one_lt_div hφ1]; linarith
  have : 0 < κ * h := mul_pos hκ hh
  nlinarith

/-! ## Pricing to market (144) -/

/-- **(144): pricing to market with linear technology** (O&R p. 711): a Home firm with constant
marginal cost `w` sells at `p` in the Home market (demand `(p/P)^{−θ_H}X_H`) and at the
foreign-currency price `p*` abroad (demand `(p*/P*)^{−θ_F}X_F`, revenue `𝓔p*` per unit in Home
currency). Its profit separates across markets, and at every `(p, p*)` it is at most the profit
at `p = θ_H w/(θ_H−1)`, `𝓔p* = θ_F w/(θ_F−1)`, strictly unless both prices are these. -/
theorem ptm_optimal {θH θF w P Ps XH XF E : ℝ} (hθH : 1 < θH) (hθF : 1 < θF) (hw : 0 < w)
    (hP : 0 < P) (hPs : 0 < Ps) (hXH : 0 < XH) (hXF : 0 < XF) (hE : 0 < E) {p ps : ℝ}
    (hp : 0 < p) (hps : 0 < ps) :
    (p - w) * cesDemand θH p P XH + (E * ps - w) * cesDemand θF ps Ps XF ≤
      (θH * w / (θH - 1) - w) * cesDemand θH (θH * w / (θH - 1)) P XH +
      (θF * w / (θF - 1) - w) * cesDemand θF (θF * w / (θF - 1) / E) Ps XF ∧
    ((p ≠ θH * w / (θH - 1) ∨ E * ps ≠ θF * w / (θF - 1)) →
      (p - w) * cesDemand θH p P XH + (E * ps - w) * cesDemand θF ps Ps XF <
      (θH * w / (θH - 1) - w) * cesDemand θH (θH * w / (θH - 1)) P XH +
      (θF * w / (θF - 1) - w) * cesDemand θF (θF * w / (θF - 1) / E) Ps XF) := by
  -- the Foreign market in Home-currency prices `p′ = 𝓔p*`, with index `𝓔P*`
  have hconv : ∀ q, cesDemand θF q Ps XF = cesDemand θF (E * q) (E * Ps) XF := by
    intro q; unfold cesDemand; congr 2; field_simp
  have hH := markup_isGreatest hθH hw hP hXH hp
  have hF := markup_isGreatest hθF hw (mul_pos hE hPs) hXF (mul_pos hE hps)
  have hopt : cesDemand θF (θF * w / (θF - 1) / E) Ps XF =
      cesDemand θF (θF * w / (θF - 1)) (E * Ps) XF := by
    rw [hconv]; congr 1; field_simp
  rw [hconv ps, hopt]
  refine ⟨by linarith [hH.1, hF.1], fun hne => ?_⟩
  rcases hne with h1 | h1
  · linarith [hH.2 h1, hF.1]
  · linarith [hH.1, hF.2 h1]

/-- **The law of one price and complete pass-through under pricing to market** (O&R p. 711): with
equal elasticities `θ_H = θ_F = θ` the optimal prices satisfy `p(h) = 𝓔p*(h) = θw/(θ−1)` (LOOP
holds although arbitrage is precluded); for any elasticities the optimal foreign-currency price is
`p* = θ_F w/((θ_F−1)𝓔)`, whose elasticity with respect to `𝓔` is exactly `−1` (complete
pass-through): `d log p*/d log 𝓔 = −1`. -/
theorem ptm_pass_through {θ θF w E0 : ℝ} (hθF : 1 < θF) (hw : 0 < w) (hE0 : 0 < E0) :
    θ * w / (θ - 1) = E0 * (θ * w / (θ - 1) / E0) ∧
    HasDerivAt (fun τ => Real.log (θF * w / (θF - 1) / (E0 * Real.exp τ))) (-1) 0 := by
  refine ⟨by field_simp, ?_⟩
  have hk : 0 < θF * w / (θF - 1) := div_pos (mul_pos (by linarith) hw) (by linarith)
  have e : (fun τ => Real.log (θF * w / (θF - 1) / (E0 * Real.exp τ))) =
      fun τ => Real.log (θF * w / (θF - 1)) - Real.log E0 - τ := by
    funext τ
    rw [Real.log_div hk.ne' (mul_pos hE0 (Real.exp_pos τ)).ne',
      Real.log_mul hE0.ne' (Real.exp_pos τ).ne', Real.log_exp]
    ring
  rw [e]
  simpa using (hasDerivAt_id (0 : ℝ)).const_sub (Real.log (θF * w / (θF - 1)) - Real.log E0)

/-- **Different elasticities give different price levels, not incomplete pass-through** (O&R
p. 711: "if the constant elasticity of demand is different in the two markets, the levels of
prices will differ"): for `θ_H ≠ θ_F` (both `> 1`) the optimal `p(h) ≠ 𝓔p*(h)`, while `𝓔p*(h)`
does not depend on `𝓔`. -/
theorem ptm_different_elasticities {θH θF w : ℝ} (hθH : 1 < θH) (hθF : 1 < θF) (hw : 0 < w)
    (hne : θH ≠ θF) : θH * w / (θH - 1) ≠ θF * w / (θF - 1) := by
  intro h
  have h1 : θH - 1 ≠ 0 := by linarith
  have h2 : θF - 1 ≠ 0 := by linarith
  field_simp at h
  exact hne (by linarith)

/-! ## The normalisation of (141)–(142) -/

/-- **(143) requires `ℓ` in (141) to be TOTAL hours** (survey flag on O&R pp. 709–710): if instead
the disutility were `(κ/2)ℓ²` with `ℓ = 2y` (hours per firm-type with `y = ℓ/2`), then
`(κ/2)(2y)² = (4κ/2)y²`, the effective weight is `4κ`, and the symmetric steady-state output is
exactly half of (143). -/
theorem normalisation_flag {θ φ κ y : ℝ} (hθ : 1 < θ) (hφ : 1 < φ) (hκ : 0 < κ) :
    κ / 2 * (2 * y) ^ 2 = 4 * κ / 2 * y ^ 2 ∧
    Real.sqrt ((φ - 1) / φ * ((θ - 1) / θ) / (4 * κ)) =
      Real.sqrt ((φ - 1) / φ * ((θ - 1) / θ) / κ) / 2 := by
  refine ⟨by ring, ?_⟩
  have hA : 0 ≤ (φ - 1) / φ * ((θ - 1) / θ) / κ :=
    div_nonneg (mul_nonneg (div_nonneg (by linarith) (by linarith))
      (div_nonneg (by linarith) (by linarith))) hκ.le
  have e : (φ - 1) / φ * ((θ - 1) / θ) / (4 * κ) = (φ - 1) / φ * ((θ - 1) / θ) / κ / 2 ^ 2 := by
    field_simp; ring
  rw [e, Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 2 ^ 2), Real.sqrt_sq (by norm_num)]

end ObstfeldRogoff.StickyPriceModels.ReduxPresetWages

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The redux model: the steady-state linear system IS the derivative of the steady-state map

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §10.1.4–§10.1.6,
pp. 667–673.

`ReduxSteadyState` proves that for every level `B̄` of Home net foreign assets the flexible-price
steady state exists and is unique (T7, `steadyState M B̄`), although it has no closed form
(p. 668). `ReduxLogLinear` solves the book's long-run LINEAR system (42)–(52) exactly (T11,
`steadySolution`). The book obtains the second from the first by "log-linearising around the
symmetric steady state"; here we prove that this is literally true: the linear system is the
derivative at `B̄ = 0` of the nonlinear map `B̄ ↦ steadyState M B̄` (T10/T11 link).

**Method: a one-dimensional implicit-function argument through the gap function.** T7 reduced
the steady state to one equation: with the gap function `g` (`gapFn`) and its inverse `g⁻¹`
(`gapInv`), Home output is `y = g⁻¹(v)`, Foreign output `y* = g⁻¹(−(n/(1−n))v)`, where the gap
value `v(B̄) = g(y(B̄))` solves `A(v)·v = δB̄` with the positive continuous factor
`A(v) = Yᵂ(g⁻¹(v), g⁻¹(−(n/(1−n))v))^{1/θ}` (`phi_eq`).

1. `A` is bounded below by a positive constant (`A_lower`), so `|v(B̄)| ≤ δ|B̄|/a₀`: the gap
   value, hence the whole steady state, is CONTINUOUS at `B̄ = 0` (`gapValue_continuousAt`).
2. `v ↦ A(v)v` is differentiable at `0` with derivative `A(0) = ȳ₀^{1/θ} ≠ 0`
   (`hasDerivAt_mul_self`), so by the inverse-function theorem for derivatives
   (`HasDerivAt.of_local_left_inverse`) `v(B̄)` is differentiable at `0` with derivative
   `δ/ȳ₀^{1/θ}` (`gapValue_hasDerivAt`).
3. `g′(ȳ₀) = −2/ȳ₀^{1/θ}` (`gapFn_hasDerivAt_ybar0`), so `g⁻¹` has derivative `−ȳ₀^{1/θ}/2` at `0`
   (`gapInv_hasDerivAt_zero`), and by the chain rule `dy/dB̄ = −δ/2`,
   `dy*/dB̄ = nδ/(2(1−n))` (`output_hasDerivAt`, `output_star_hasDerivAt`).
4. Every other steady-state variable is an explicit function of outputs (T5, `ofOutputs`), so
   `d log Cᵂ = 0`, `d log π = δ/(2θȳ₀)`, `d log π* = −nδ/(2θ(1−n)ȳ₀)`,
   `d log C = (1+θ)δ/(2θȳ₀)`, `d log C* = −(n/(1−n))(1+θ)δ/(2θȳ₀)` per unit of `B̄`.

**The link (`linearisation_link`, `linearisation_link_system`).** Along `B̄ = τ b̄ C̄ᵂ₀`
(`b̄ = dB̄/C̄ᵂ₀`, a level change since `B̄₀ = 0`, O&R p. 671), the derivatives at `τ = 0` of the
logs of `y, y*, C, C*, Cᵂ, p(h)/P, p*(f)/P*` are EXACTLY the components `ȳ, ȳ*, c̄, c̄*, c̄ᵂ,
p̄(h) − p̄, p̄*(f) − p̄*` of the unique solution of the long-run linear system (42)–(52); completing
them with the nominal block (money demand (26) and PPP (7), both exact in logs) gives a vector that
satisfies `SteadyLinear` and therefore equals `steadySolution`.
-/

namespace ObstfeldRogoff.StickyPriceModels.ReduxLinearisationLink

open Real Filter Topology Set ReduxPrimitives ReduxLogLinear ReduxSteadyState

/-- The linear-model parameters `(θ, δ, n)` of a nonlinear parameter set (O&R §10.1.5, p. 669). -/
noncomputable def linkLinear (M : ReduxParams) : ReduxLinear :=
  ⟨M.θ, M.δ, M.n, M.hθ, M.δ_pos, M.hn0, M.hn1⟩

/-- The relative size `n/(1−n)` of the gap relation `g(y*) = −(n/(1−n)) g(y)` (O&R (20)–(21)). -/
noncomputable def relSize (M : ReduxParams) : ℝ := M.n / (1 - M.n)

/-- Home output in the steady state indexed by `B̄` (T7). -/
noncomputable def outputB (M : ReduxParams) (B : ℝ) : ℝ := (steadyState M B).y

/-- Foreign output in the steady state indexed by `B̄` (T7). -/
noncomputable def outputStarB (M : ReduxParams) (B : ℝ) : ℝ := (steadyState M B).ys

/-- The gap value `v(B̄) = g(y(B̄))` of the steady state indexed by `B̄` (T5, T7). -/
noncomputable def gapValue (M : ReduxParams) (B : ℝ) : ℝ := gapFn M.θ M.K (outputB M B)

/-- The factor `A(v) = Yᵂ(g⁻¹(v), g⁻¹(−(n/(1−n))v))^{1/θ}` of the one-dimensional reduction
(T7): the steady state solves `A(v)·v = δB̄`. -/
noncomputable def gapFactor (M : ReduxParams) (v : ℝ) : ℝ :=
  worldOutputIndex M.θ M.n (gapInv M.θ M.K v) (gapInv M.θ M.K (-(relSize M) * v)) ^ (1 / M.θ)

/-! ## The one-dimensional reduction -/

/-- The steady state at `B̄ = 0` is the symmetric one (O&R (22)–(24)). -/
theorem steadyState_zero (M : ReduxParams) : steadyState M 0 = symmetricSteady M :=
  (isSteadyState_zero_iff M _).1 (steadyState_spec M 0)

/-- Every steady state is built from its outputs (T5, `ofOutputs`). -/
theorem steadyState_eq_ofOutputs (M : ReduxParams) (B : ℝ) :
    steadyState M B = ofOutputs M (outputB M B) (outputStarB M B) :=
  (steadyState_spec M B).reduced.2

/-- Steady-state outputs are positive (O&R p. 667). -/
theorem outputB_pos (M : ReduxParams) (B : ℝ) : 0 < outputB M B ∧ 0 < outputStarB M B :=
  ⟨(steadyState_spec M B).static.y_pos, (steadyState_spec M B).static.ys_pos⟩

/-- `g⁻¹(0) = ȳ₀` (O&R (24)). -/
theorem gapInv_zero (M : ReduxParams) : gapInv M.θ M.K 0 = M.ybar0 := by
  have h := gapInv_gapFn M.hθ M.K_pos M.ybar0_pos
  rwa [ReduxParams.ybar0, gapFn_sqrt (by linarith [M.hθ]) M.K_pos] at h

/-- **Home output is `g⁻¹` of the gap value** (T7). -/
theorem outputB_eq (M : ReduxParams) (B : ℝ) : outputB M B = gapInv M.θ M.K (gapValue M B) :=
  (gapInv_gapFn M.hθ M.K_pos (outputB_pos M B).1).symm

/-- **Foreign output is `g⁻¹(−(n/(1−n))v)`** (T7): from the gap relation
`n g(y) + (1−n) g(y*) = 0`. -/
theorem outputStarB_eq (M : ReduxParams) (B : ℝ) :
    outputStarB M B = gapInv M.θ M.K (-(relSize M) * gapValue M B) := by
  have hrel := (steadyState_spec M B).static.gap_relation
  have hn : 1 - M.n ≠ 0 := by linarith [M.hn1]
  have hg : gapFn M.θ M.K (outputStarB M B) = -(relSize M) * gapValue M B := by
    unfold relSize gapValue outputB outputStarB
    field_simp
    linarith
  rw [← hg, gapInv_gapFn M.hθ M.K_pos (outputB_pos M B).2]

/-- **The one-dimensional steady-state equation** (T7): `A(v(B̄))·v(B̄) = δB̄`. -/
theorem phi_eq (M : ReduxParams) (B : ℝ) :
    gapFactor M (gapValue M B) * gapValue M B = M.δ * B := by
  have h := (steadyState_spec M B).reduced.1.2.2.2
  unfold gapFactor
  rw [← outputB_eq, ← outputStarB_eq]
  exact h

/-- The gap value at `B̄ = 0` is `0` (O&R (24)). -/
theorem gapValue_zero (M : ReduxParams) : gapValue M 0 = 0 := by
  unfold gapValue outputB
  rw [steadyState_zero]
  exact gapFn_sqrt (by linarith [M.hθ]) M.K_pos

/-! ## Step 1: continuity of the steady state at `B̄ = 0` -/

/-- The world output index of equal outputs is that output (O&R (18), (23)). -/
theorem worldOutputIndex_self {θ n a : ℝ} (hθ : 1 < θ) (ha : 0 < a) :
    worldOutputIndex θ n a a = a := by
  unfold worldOutputIndex
  rw [show n * a ^ ((θ - 1) / θ) + (1 - n) * a ^ ((θ - 1) / θ) = a ^ ((θ - 1) / θ) by ring,
    ← rpow_mul ha.le]
  have : (θ - 1) / θ * (θ / (θ - 1)) = 1 := by
    have : θ - 1 ≠ 0 := by linarith
    have : θ ≠ 0 := by linarith
    field_simp
  rw [this, rpow_one]

/-- The positive lower bound `a₀ = min(n^{1/(θ−1)}, (1−n)^{1/(θ−1)}) ȳ₀^{1/θ}` of the factor `A`
(T7). -/
noncomputable def gapFactorBound (M : ReduxParams) : ℝ :=
  min (M.n ^ (1 / (M.θ - 1))) ((1 - M.n) ^ (1 / (M.θ - 1))) * M.ybar0 ^ (1 / M.θ)

/-- `a₀ > 0` (T7). -/
theorem gapFactorBound_pos (M : ReduxParams) : 0 < gapFactorBound M := by
  have hn1 : 0 < 1 - M.n := by linarith [M.hn1]
  unfold gapFactorBound
  exact mul_pos (lt_min (rpow_pos_of_pos M.hn0 _) (rpow_pos_of_pos hn1 _))
    (rpow_pos_of_pos M.ybar0_pos _)

/-- **`A(v) ≥ a₀` for every `v`** (T7): at least one of the two outputs `g⁻¹(v)`,
`g⁻¹(−(n/(1−n))v)` is at least `ȳ₀` (because `g⁻¹` is decreasing and `g⁻¹(0) = ȳ₀`), and world
output dominates each country's weighted output (`worldOutputIndex_rpow_ge`). -/
theorem A_lower (M : ReduxParams) (v : ℝ) : gapFactorBound M ≤ gapFactor M v := by
  have hθ := M.hθ
  have hK := M.K_pos
  have hn0 := M.hn0
  have hn1 : 0 < 1 - M.n := by linarith [M.hn1]
  have hc : 0 ≤ relSize M := div_nonneg hn0.le hn1.le
  have hanti := (gapInv_strictAnti hθ hK).antitone
  have hy := (gapInv_spec hθ hK v).1
  have hys := (gapInv_spec hθ hK (-(relSize M) * v)).1
  have hθ0 : 0 < 1 / M.θ := by have : 0 < M.θ := by linarith
                               positivity
  unfold gapFactor gapFactorBound
  rcases le_total 0 v with hv | hv
  · -- Foreign output is at least `ȳ₀`
    have hge : M.ybar0 ≤ gapInv M.θ M.K (-(relSize M) * v) := by
      rw [← gapInv_zero M]; exact hanti (by nlinarith)
    have hlow := worldOutputIndex_rpow_ge hθ hn1 (by linarith [M.hn0]) hys hy
    rw [← worldOutputIndex_comm] at hlow
    calc min (M.n ^ (1 / (M.θ - 1))) ((1 - M.n) ^ (1 / (M.θ - 1))) * M.ybar0 ^ (1 / M.θ)
        ≤ (1 - M.n) ^ (1 / (M.θ - 1)) * gapInv M.θ M.K (-(relSize M) * v) ^ (1 / M.θ) :=
          mul_le_mul (min_le_right _ _) (rpow_le_rpow M.ybar0_pos.le hge hθ0.le)
            (rpow_nonneg M.ybar0_pos.le _) (rpow_nonneg hn1.le _)
      _ ≤ _ := hlow
  · -- Home output is at least `ȳ₀`
    have hge : M.ybar0 ≤ gapInv M.θ M.K v := by rw [← gapInv_zero M]; exact hanti hv
    have hlow := worldOutputIndex_rpow_ge hθ hn0 M.hn1 hy hys
    calc min (M.n ^ (1 / (M.θ - 1))) ((1 - M.n) ^ (1 / (M.θ - 1))) * M.ybar0 ^ (1 / M.θ)
        ≤ M.n ^ (1 / (M.θ - 1)) * gapInv M.θ M.K v ^ (1 / M.θ) :=
          mul_le_mul (min_le_left _ _) (rpow_le_rpow M.ybar0_pos.le hge hθ0.le)
            (rpow_nonneg M.ybar0_pos.le _) (rpow_nonneg hn0.le _)
      _ ≤ _ := hlow

/-- **The gap value is Lipschitz at `B̄ = 0`**: `|v(B̄)| ≤ δ|B̄|/a₀` (T7). -/
theorem gapValue_bound (M : ReduxParams) (B : ℝ) :
    |gapValue M B| ≤ M.δ * |B| / gapFactorBound M := by
  have ha := gapFactorBound_pos M
  have hA := A_lower M (gapValue M B)
  have h := phi_eq M B
  have hδ := M.δ_pos
  rw [le_div_iff₀ ha]
  have habs : |gapFactor M (gapValue M B)| * |gapValue M B| = M.δ * |B| := by
    rw [← abs_mul, h, abs_mul, abs_of_pos hδ]
  rw [abs_of_pos (lt_of_lt_of_le ha hA)] at habs
  nlinarith [abs_nonneg (gapValue M B)]

/-- **Continuity of the steady state at `B̄ = 0`, step 1**: the gap value is continuous at `0`
(T7). -/
theorem gapValue_continuousAt (M : ReduxParams) : ContinuousAt (gapValue M) 0 := by
  have ha := gapFactorBound_pos M
  rw [ContinuousAt, gapValue_zero]
  have hb : Tendsto (fun B : ℝ => M.δ * |B| / gapFactorBound M) (𝓝 0) (𝓝 0) := by
    have : Continuous (fun B : ℝ => M.δ * |B| / gapFactorBound M) := by fun_prop
    simpa using this.tendsto 0
  refine squeeze_zero_norm (fun B => ?_) hb
  rw [Real.norm_eq_abs]
  exact gapValue_bound M B

/-! ## Step 2: the gap value is differentiable at `B̄ = 0` -/

/-- The factor `A` is continuous at `0` (T7): `g⁻¹` is continuous and so is the CES aggregate. -/
theorem gapFactor_continuousAt (M : ReduxParams) : ContinuousAt (gapFactor M) 0 := by
  have hθ := M.hθ
  have hK := M.K_pos
  have hc := gapInv_continuous hθ hK
  have hρ : 0 ≤ (M.θ - 1) / M.θ := div_nonneg (by linarith) (by linarith)
  have h1 : ContinuousAt (fun v => gapInv M.θ M.K v ^ ((M.θ - 1) / M.θ)) 0 :=
    hc.continuousAt.rpow_const (Or.inr hρ)
  have h2 : ContinuousAt (fun v => gapInv M.θ M.K (-(relSize M) * v) ^ ((M.θ - 1) / M.θ)) 0 :=
    ((hc.comp (continuous_const.mul continuous_id)).continuousAt).rpow_const (Or.inr hρ)
  have h3 := ((h1.const_mul M.n).add (h2.const_mul (1 - M.n))).rpow_const
    (p := M.θ / (M.θ - 1)) (Or.inr (div_nonneg (by linarith) (by linarith)))
  have h4 := h3.rpow_const (p := 1 / M.θ) (Or.inr (div_nonneg zero_le_one (by linarith)))
  unfold gapFactor worldOutputIndex
  exact h4

/-- `A(0) = ȳ₀^{1/θ}` (O&R (23)–(24)). -/
theorem gapFactor_zero (M : ReduxParams) : gapFactor M 0 = M.ybar0 ^ (1 / M.θ) := by
  unfold gapFactor
  rw [mul_zero, gapInv_zero, worldOutputIndex_self M.hθ M.ybar0_pos]

/-- If `A` is continuous at `0`, then `v ↦ A(v)v` has derivative `A(0)` at `0`. -/
theorem hasDerivAt_mul_self {A : ℝ → ℝ} (hA : ContinuousAt A 0) :
    HasDerivAt (fun v => A v * v) (A 0) 0 := by
  rw [hasDerivAt_iff_tendsto_slope]
  have h : Tendsto A (𝓝[≠] (0 : ℝ)) (𝓝 (A 0)) := hA.tendsto.mono_left nhdsWithin_le_nhds
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with v hv
  rw [slope_def_field]
  have hv' : v ≠ 0 := hv
  field_simp
  ring

/-- **The gap value is differentiable at `B̄ = 0` with derivative `δ/ȳ₀^{1/θ}`** (the
one-dimensional implicit-function step): `A(v(B̄))v(B̄)/δ = B̄` for all `B̄`, the map
`v ↦ A(v)v/δ` has nonzero derivative `ȳ₀^{1/θ}/δ` at `v(0) = 0`, and `v` is continuous at `0`. -/
theorem gapValue_hasDerivAt (M : ReduxParams) :
    HasDerivAt (gapValue M) (M.δ / M.ybar0 ^ (1 / M.θ)) 0 := by
  have hδ := M.δ_pos
  have hy := rpow_pos_of_pos M.ybar0_pos (1 / M.θ)
  have hf : HasDerivAt (fun v => gapFactor M v * v / M.δ) (gapFactor M 0 / M.δ)
      (gapValue M 0) := by
    rw [gapValue_zero]
    exact (hasDerivAt_mul_self (gapFactor_continuousAt M)).div_const M.δ
  rw [gapFactor_zero] at hf
  have hinv := HasDerivAt.of_local_left_inverse (gapValue_continuousAt M) hf
    (div_pos hy hδ).ne' (Eventually.of_forall fun B => by
      rw [phi_eq M B]
      field_simp)
  convert hinv using 1
  field_simp

/-! ## Step 3: outputs -/

/-- **The derivative of the gap function at `ȳ₀`** (T7): `g′(ȳ₀) = −2/ȳ₀^{1/θ}`. -/
theorem gapFn_hasDerivAt_ybar0 (M : ReduxParams) :
    HasDerivAt (gapFn M.θ M.K) (-2 / M.ybar0 ^ (1 / M.θ)) M.ybar0 := by
  have hθ := M.hθ
  have hθ0 : M.θ ≠ 0 := by linarith
  set yb := M.ybar0 with hyb
  have hy : 0 < yb := M.ybar0_pos
  have h1 := (Real.hasDerivAt_rpow_const (p := -(M.θ + 1) / M.θ) (Or.inl hy.ne')).const_mul M.K
  have h2 := Real.hasDerivAt_rpow_const (x := yb) (p := (M.θ - 1) / M.θ) (Or.inl hy.ne')
  have h := h1.sub h2
  have hK : M.K = yb ^ (2 : ℝ) := by rw [hyb, rpow_two, M.ybar0_sq]
  have e1 : M.K * (-(M.θ + 1) / M.θ * yb ^ (-(M.θ + 1) / M.θ - 1)) =
      -(M.θ + 1) / M.θ * yb ^ (-(1 / M.θ)) := by
    rw [hK, show yb ^ (2 : ℝ) * (-(M.θ + 1) / M.θ * yb ^ (-(M.θ + 1) / M.θ - 1)) =
      -(M.θ + 1) / M.θ * (yb ^ (2 : ℝ) * yb ^ (-(M.θ + 1) / M.θ - 1)) by ring,
      ← rpow_add hy]
    congr 2
    field_simp
    ring
  have e2 : yb ^ ((M.θ - 1) / M.θ - 1) = yb ^ (-(1 / M.θ)) := by
    congr 1; field_simp; ring
  have e3 : yb ^ (-(1 / M.θ)) = 1 / yb ^ (1 / M.θ) := by rw [rpow_neg hy.le, inv_eq_one_div]
  convert h using 1
  · funext y; simp [gapFn]
  · rw [e1, e2, e3]
    field_simp
    ring

/-- **`g⁻¹` has derivative `−ȳ₀^{1/θ}/2` at `0`** (inverse-function theorem for derivatives;
`g⁻¹` is continuous and `g(g⁻¹(v)) = v`). -/
theorem gapInv_hasDerivAt_zero (M : ReduxParams) :
    HasDerivAt (gapInv M.θ M.K) (-(M.ybar0 ^ (1 / M.θ)) / 2) 0 := by
  have hy := rpow_pos_of_pos M.ybar0_pos (1 / M.θ)
  have hf : HasDerivAt (gapFn M.θ M.K) (-2 / M.ybar0 ^ (1 / M.θ)) (gapInv M.θ M.K 0) := by
    rw [gapInv_zero]; exact gapFn_hasDerivAt_ybar0 M
  have hinv := HasDerivAt.of_local_left_inverse (gapInv_continuous M.hθ M.K_pos).continuousAt hf
    (div_ne_zero (by norm_num) hy.ne') (Eventually.of_forall fun v =>
      (gapInv_spec M.hθ M.K_pos v).2)
  convert hinv using 1
  field_simp

/-- **`dy/dB̄ = −δ/2` at `B̄ = 0`** (O&R p. 673, `ȳ = −δb̄/2` in the linear model; T11). -/
theorem output_hasDerivAt (M : ReduxParams) : HasDerivAt (outputB M) (-(M.δ / 2)) 0 := by
  have hy := rpow_pos_of_pos M.ybar0_pos (1 / M.θ)
  have h2 := gapInv_hasDerivAt_zero M
  rw [← gapValue_zero M] at h2
  have h := h2.comp 0 (gapValue_hasDerivAt M)
  have e : outputB M = gapInv M.θ M.K ∘ gapValue M := by
    funext B; exact outputB_eq M B
  rw [e]
  convert h using 1
  field_simp

/-- **`dy*/dB̄ = nδ/(2(1−n))` at `B̄ = 0`** (O&R p. 673, `ȳ* = nδb̄/(2(1−n))`; T11). -/
theorem output_star_hasDerivAt (M : ReduxParams) :
    HasDerivAt (outputStarB M) (M.n * M.δ / (2 * (1 - M.n))) 0 := by
  have hy := rpow_pos_of_pos M.ybar0_pos (1 / M.θ)
  have hn : 1 - M.n ≠ 0 := by linarith [M.hn1]
  have h2 := gapInv_hasDerivAt_zero M
  have hv : HasDerivAt (fun B => -(relSize M) * gapValue M B)
      (-(relSize M) * (M.δ / M.ybar0 ^ (1 / M.θ))) 0 :=
    (gapValue_hasDerivAt M).const_mul _
  have hv0 : -(relSize M) * gapValue M 0 = 0 := by rw [gapValue_zero, mul_zero]
  rw [← hv0] at h2
  have h := h2.comp 0 hv
  have e : outputStarB M = gapInv M.θ M.K ∘ fun B => -(relSize M) * gapValue M B := by
    funext B; exact outputStarB_eq M B
  rw [e]
  convert h using 1
  unfold relSize
  field_simp

/-! ## Step 4: every steady-state variable -/

/-- At `B̄ = 0` both outputs are `ȳ₀` (O&R (23)–(24)). -/
theorem output_zero (M : ReduxParams) : outputB M 0 = M.ybar0 ∧ outputStarB M 0 = M.ybar0 := by
  unfold outputB outputStarB
  rw [steadyState_zero]
  exact ⟨rfl, rfl⟩

/-- The inner CES sum `S(B̄) = n y^ρ + (1−n) y*^ρ`, `ρ = (θ−1)/θ`, so that `Cᵂ = S^{1/ρ}`
(T5, O&R (18)). -/
noncomputable def worldSum (M : ReduxParams) (B : ℝ) : ℝ :=
  M.n * outputB M B ^ ((M.θ - 1) / M.θ) + (1 - M.n) * outputStarB M B ^ ((M.θ - 1) / M.θ)

/-- `S(B̄) > 0` (O&R (18)). -/
theorem worldSum_pos (M : ReduxParams) (B : ℝ) : 0 < worldSum M B := by
  have hn1 : 0 < 1 - M.n := by linarith [M.hn1]
  have h1 := rpow_pos_of_pos (outputB_pos M B).1 ((M.θ - 1) / M.θ)
  have h2 := rpow_pos_of_pos (outputB_pos M B).2 ((M.θ - 1) / M.θ)
  have := M.hn0
  unfold worldSum
  positivity

/-- **World consumption does not move to first order: `dS/dB̄ = 0`** (O&R (47), `c̄ᵂ = 0`): the
population-weighted output changes cancel, `n(−δ/2) + (1−n)·nδ/(2(1−n)) = 0`. -/
theorem worldSum_hasDerivAt (M : ReduxParams) : HasDerivAt (worldSum M) 0 0 := by
  obtain ⟨hy0, hys0⟩ := output_zero M
  have hyb := M.ybar0_pos
  have hn : 1 - M.n ≠ 0 := by linarith [M.hn1]
  have h1 := (output_hasDerivAt M).rpow_const (p := (M.θ - 1) / M.θ)
    (Or.inl (by rw [hy0]; exact hyb.ne'))
  have h2 := (output_star_hasDerivAt M).rpow_const (p := (M.θ - 1) / M.θ)
    (Or.inl (by rw [hys0]; exact hyb.ne'))
  have h := (h1.const_mul M.n).add (h2.const_mul (1 - M.n))
  convert h using 1
  · funext B; simp only [Pi.add_apply, worldSum]
  · rw [hy0, hys0]
    field_simp
    ring

/-- **`d log Cᵂ/dB̄ = 0` at `B̄ = 0`** (O&R (47)). -/
theorem logX_hasDerivAt (M : ReduxParams) :
    HasDerivAt (fun B => Real.log (steadyState M B).X) 0 0 := by
  have hθ := M.hθ
  have e : (fun B => Real.log (steadyState M B).X) =
      fun B => M.θ / (M.θ - 1) * Real.log (worldSum M B) := by
    funext B
    rw [steadyState_eq_ofOutputs]
    change Real.log (worldOutputIndex M.θ M.n (outputB M B) (outputStarB M B)) = _
    change Real.log (worldSum M B ^ (M.θ / (M.θ - 1))) = _
    rw [Real.log_rpow (worldSum_pos M B)]
  rw [e]
  have h := ((worldSum_hasDerivAt M).log (worldSum_pos M 0).ne').const_mul (M.θ / (M.θ - 1))
  simpa using h

/-- **`d log y/dB̄ = −δ/(2ȳ₀)` and `d log y*/dB̄ = nδ/(2(1−n)ȳ₀)` at `B̄ = 0`** (T11). -/
theorem logOutput_hasDerivAt (M : ReduxParams) :
    HasDerivAt (fun B => Real.log (steadyState M B).y) (-(M.δ / 2) / M.ybar0) 0 ∧
    HasDerivAt (fun B => Real.log (steadyState M B).ys)
      (M.n * M.δ / (2 * (1 - M.n)) / M.ybar0) 0 := by
  obtain ⟨hy0, hys0⟩ := output_zero M
  have hyb := M.ybar0_pos
  constructor
  · have h := (output_hasDerivAt M).log (by rw [hy0]; exact hyb.ne')
    rw [hy0] at h
    exact h
  · have h := (output_star_hasDerivAt M).log (by rw [hys0]; exact hyb.ne')
    rw [hys0] at h
    exact h

/-- **The terms of trade: `d log π/dB̄ = δ/(2θȳ₀)`, `d log π*/dB̄ = −nδ/(2θ(1−n)ȳ₀)`** (O&R
(46), with `π = p(h)/P = (Cᵂ/y)^{1/θ}`, T5). -/
theorem logPrice_hasDerivAt (M : ReduxParams) :
    HasDerivAt (fun B => Real.log (steadyState M B).q) (M.δ / (2 * M.θ * M.ybar0)) 0 ∧
    HasDerivAt (fun B => Real.log (steadyState M B).qs)
      (-(M.n * M.δ / (2 * M.θ * (1 - M.n) * M.ybar0))) 0 := by
  have hθ := M.hθ
  have hθ0 : M.θ ≠ 0 := by linarith
  have hyb := M.ybar0_pos
  have hn : 1 - M.n ≠ 0 := by linarith [M.hn1]
  have hX := logX_hasDerivAt M
  obtain ⟨hy, hys⟩ := logOutput_hasDerivAt M
  have eq : ∀ B, Real.log (steadyState M B).q =
      1 / M.θ * (Real.log (steadyState M B).X - Real.log (steadyState M B).y) := by
    intro B
    have hXp := (steadyState_spec M B).static.X_pos
    have hyp := (steadyState_spec M B).static.y_pos
    have hq : (steadyState M B).q = (steadyState M B).X ^ (1 / M.θ) /
        (steadyState M B).y ^ (1 / M.θ) := (steadyState_spec M B).static.eq_of_outputs.2.1.trans
          (by rw [(steadyState_spec M B).static.X_eq])
    rw [hq, Real.log_div (rpow_pos_of_pos hXp _).ne' (rpow_pos_of_pos hyp _).ne',
      Real.log_rpow hXp, Real.log_rpow hyp]
    ring
  have eqs : ∀ B, Real.log (steadyState M B).qs =
      1 / M.θ * (Real.log (steadyState M B).X - Real.log (steadyState M B).ys) := by
    intro B
    have hXp := (steadyState_spec M B).static.X_pos
    have hyp := (steadyState_spec M B).static.ys_pos
    have hq : (steadyState M B).qs = (steadyState M B).X ^ (1 / M.θ) /
        (steadyState M B).ys ^ (1 / M.θ) := (steadyState_spec M B).static.eq_of_outputs.2.2.1.trans
          (by rw [(steadyState_spec M B).static.X_eq])
    rw [hq, Real.log_div (rpow_pos_of_pos hXp _).ne' (rpow_pos_of_pos hyp _).ne',
      Real.log_rpow hXp, Real.log_rpow hyp]
    ring
  constructor
  · rw [show (fun B => Real.log (steadyState M B).q) = fun B =>
      1 / M.θ * (Real.log (steadyState M B).X - Real.log (steadyState M B).y) from funext eq]
    convert (hX.sub hy).const_mul (1 / M.θ) using 1
    field_simp
    ring
  · rw [show (fun B => Real.log (steadyState M B).qs) = fun B =>
      1 / M.θ * (Real.log (steadyState M B).X - Real.log (steadyState M B).ys) from funext eqs]
    convert (hX.sub hys).const_mul (1 / M.θ) using 1
    field_simp
    ring

/-- **Consumption: `d log C/dB̄ = (1+θ)δ/(2θȳ₀)`, `d log C*/dB̄ = −(n/(1−n))(1+θ)δ/(2θȳ₀)`**
(O&R (48)–(49), with `C = Kπ/y`, T5). -/
theorem logConsumption_hasDerivAt (M : ReduxParams) :
    HasDerivAt (fun B => Real.log (steadyState M B).C)
      ((1 + M.θ) * M.δ / (2 * M.θ * M.ybar0)) 0 ∧
    HasDerivAt (fun B => Real.log (steadyState M B).Cs)
      (-(M.n / (1 - M.n)) * ((1 + M.θ) * M.δ / (2 * M.θ * M.ybar0))) 0 := by
  have hθ := M.hθ
  have hθ0 : M.θ ≠ 0 := by linarith
  have hyb := M.ybar0_pos
  have hn : 1 - M.n ≠ 0 := by linarith [M.hn1]
  have hK := M.K_pos
  obtain ⟨hq, hqs⟩ := logPrice_hasDerivAt M
  obtain ⟨hy, hys⟩ := logOutput_hasDerivAt M
  have eq : ∀ B, Real.log (steadyState M B).C = Real.log M.K + Real.log (steadyState M B).q -
      Real.log (steadyState M B).y := by
    intro B
    have hs := (steadyState_spec M B).static
    rw [hs.eq_of_outputs.2.2.2.1, Real.log_div (mul_pos hK hs.q_pos).ne' hs.y_pos.ne',
      Real.log_mul hK.ne' hs.q_pos.ne']
  have eqs : ∀ B, Real.log (steadyState M B).Cs = Real.log M.K + Real.log (steadyState M B).qs -
      Real.log (steadyState M B).ys := by
    intro B
    have hs := (steadyState_spec M B).static
    rw [hs.eq_of_outputs.2.2.2.2, Real.log_div (mul_pos hK hs.qs_pos).ne' hs.ys_pos.ne',
      Real.log_mul hK.ne' hs.qs_pos.ne']
  constructor
  · rw [show (fun B => Real.log (steadyState M B).C) = fun B => Real.log M.K +
      Real.log (steadyState M B).q - Real.log (steadyState M B).y from funext eq]
    convert (hq.const_add (Real.log M.K)).sub hy using 1
    field_simp
    ring
  · rw [show (fun B => Real.log (steadyState M B).Cs) = fun B => Real.log M.K +
      Real.log (steadyState M B).qs - Real.log (steadyState M B).ys from funext eqs]
    convert (hqs.const_add (Real.log M.K)).sub hys using 1
    field_simp
    ring

/-! ## The link -/

/-- Differentiating along a direction: if `F` has derivative `d` at `0`, then `τ ↦ F(τc)` has
derivative `dc` at `0` (O&R p. 671: perturbations `B̄ = τ b̄ C̄ᵂ₀`). -/
theorem hasDerivAt_along {F : ℝ → ℝ} {d : ℝ} (c : ℝ) (h : HasDerivAt F d 0) :
    HasDerivAt (fun τ => F (τ * c)) (d * c) 0 := by
  have hl : HasDerivAt (fun τ : ℝ => τ * c) c 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).mul_const c
  exact h.comp_of_eq 0 hl (by ring)

/-- **The long-run linear system is the derivative of the nonlinear steady-state map**
(T10/T11 link; O&R §10.1.6, pp. 671–673). Along `B̄ = τ b̄ C̄ᵂ₀` (`C̄ᵂ₀ = ȳ₀`), the derivatives at
`τ = 0` of the logs of the steady-state outputs, consumptions, world consumption and relative
prices `p(h)/P`, `p*(f)/P*` are exactly the components `ȳ, ȳ*, c̄, c̄*, c̄ᵂ, p̄(h) − p̄,
p̄*(f) − p̄*` of the unique solution `steadySolution` of the linear system (42)–(52), for every
`b̄` and any monetary block `m̄, m̄*`. -/
theorem linearisation_link (M : ReduxParams) (b m ms : ℝ) :
    HasDerivAt (fun τ => Real.log (steadyState M (τ * (b * M.ybar0))).y)
      (steadySolution (linkLinear M) b m ms).y 0 ∧
    HasDerivAt (fun τ => Real.log (steadyState M (τ * (b * M.ybar0))).ys)
      (steadySolution (linkLinear M) b m ms).ys 0 ∧
    HasDerivAt (fun τ => Real.log (steadyState M (τ * (b * M.ybar0))).C)
      (steadySolution (linkLinear M) b m ms).c 0 ∧
    HasDerivAt (fun τ => Real.log (steadyState M (τ * (b * M.ybar0))).Cs)
      (steadySolution (linkLinear M) b m ms).cs 0 ∧
    HasDerivAt (fun τ => Real.log (steadyState M (τ * (b * M.ybar0))).X)
      (steadySolution (linkLinear M) b m ms).cW 0 ∧
    HasDerivAt (fun τ => Real.log (steadyState M (τ * (b * M.ybar0))).q)
      ((steadySolution (linkLinear M) b m ms).ph - (steadySolution (linkLinear M) b m ms).p) 0 ∧
    HasDerivAt (fun τ => Real.log (steadyState M (τ * (b * M.ybar0))).qs)
      ((steadySolution (linkLinear M) b m ms).pf -
        (steadySolution (linkLinear M) b m ms).ps) 0 := by
  have hθ := M.hθ
  have hθ0 : M.θ ≠ 0 := by linarith
  have hyb := M.ybar0_pos.ne'
  have hn : 1 - M.n ≠ 0 := by linarith [M.hn1]
  obtain ⟨hy, hys⟩ := logOutput_hasDerivAt M
  obtain ⟨hC, hCs⟩ := logConsumption_hasDerivAt M
  obtain ⟨hq, hqs⟩ := logPrice_hasDerivAt M
  have hX := logX_hasDerivAt M
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · convert hasDerivAt_along (b * M.ybar0) hy using 1
    simp only [steadySolution, linkLinear]; field_simp
  · convert hasDerivAt_along (b * M.ybar0) hys using 1
    simp only [steadySolution, linkLinear]; field_simp
  · convert hasDerivAt_along (b * M.ybar0) hC using 1
    simp only [steadySolution, linkLinear]; field_simp
  · convert hasDerivAt_along (b * M.ybar0) hCs using 1
    simp only [steadySolution, linkLinear]; field_simp
  · convert hasDerivAt_along (b * M.ybar0) hX using 1
    simp only [steadySolution, linkLinear]; ring
  · convert hasDerivAt_along (b * M.ybar0) hq using 1
    simp only [steadySolution, linkLinear]; field_simp; ring
  · convert hasDerivAt_along (b * M.ybar0) hqs using 1
    simp only [steadySolution, linkLinear]; field_simp; ring

/-- **The nominal block is exact in logs** (O&R (26), (50)–(52), (7)): long-run money demand
`M/P = (χ(1+δ)/δ) C` at two steady states gives `Δlog P = Δlog M − Δlog C` exactly (so
`p̄ = m̄ − c̄`), and `p(h) = P · (p(h)/P)` gives `Δlog p(h) = Δlog P + Δlog π`. -/
theorem nominal_block_exact {k M0 M1 P0 P1 C0 C1 : ℝ} (hk : 0 < k) (hM0 : 0 < M0) (hM1 : 0 < M1)
    (hP0 : 0 < P0) (hP1 : 0 < P1) (hC0 : 0 < C0) (hC1 : 0 < C1) (h0 : M0 / P0 = k * C0)
    (h1 : M1 / P1 = k * C1) :
    Real.log P1 - Real.log P0 = (Real.log M1 - Real.log M0) - (Real.log C1 - Real.log C0) := by
  have l0 := congrArg Real.log h0
  have l1 := congrArg Real.log h1
  rw [Real.log_div hM0.ne' hP0.ne', Real.log_mul hk.ne' hC0.ne'] at l0
  rw [Real.log_div hM1.ne' hP1.ne', Real.log_mul hk.ne' hC1.ne'] at l1
  linarith

/-- The vector of first-order responses of the nonlinear steady state along `B̄ = τ b̄ C̄ᵂ₀`,
completed by the exact nominal block (O&R (50)–(52), (7), (27)–(28)): real components are the
derivatives of the logs of `steadyState`; `p̄ = m̄ − c̄`, `p̄* = m̄* − c̄*`, `ē = p̄ − p̄*`,
`p̄(h) = p̄ + d log π`, `p̄*(f) = p̄* + d log π*`. -/
noncomputable def derivVars (M : ReduxParams) (b m ms : ℝ) : SteadyVars where
  c := deriv (fun τ => Real.log (steadyState M (τ * (b * M.ybar0))).C) 0
  cs := deriv (fun τ => Real.log (steadyState M (τ * (b * M.ybar0))).Cs) 0
  y := deriv (fun τ => Real.log (steadyState M (τ * (b * M.ybar0))).y) 0
  ys := deriv (fun τ => Real.log (steadyState M (τ * (b * M.ybar0))).ys) 0
  p := m - deriv (fun τ => Real.log (steadyState M (τ * (b * M.ybar0))).C) 0
  ps := ms - deriv (fun τ => Real.log (steadyState M (τ * (b * M.ybar0))).Cs) 0
  e := (m - deriv (fun τ => Real.log (steadyState M (τ * (b * M.ybar0))).C) 0) -
    (ms - deriv (fun τ => Real.log (steadyState M (τ * (b * M.ybar0))).Cs) 0)
  ph := (m - deriv (fun τ => Real.log (steadyState M (τ * (b * M.ybar0))).C) 0) +
    deriv (fun τ => Real.log (steadyState M (τ * (b * M.ybar0))).q) 0
  pf := (ms - deriv (fun τ => Real.log (steadyState M (τ * (b * M.ybar0))).Cs) 0) +
    deriv (fun τ => Real.log (steadyState M (τ * (b * M.ybar0))).qs) 0
  cW := deriv (fun τ => Real.log (steadyState M (τ * (b * M.ybar0))).X) 0

/-- **T11 is exactly the derivative of T7** (O&R pp. 671–673): the first-order responses of the
nonlinear steady state (`derivVars`) satisfy the book's long-run linear system `SteadyLinear`
(27)–(34), (40), (41), (50), (51), and hence equal its unique solution `steadySolution`
(45)–(52) (`steadyLinear_iff`). -/
theorem linearisation_link_system (M : ReduxParams) (b m ms : ℝ) :
    derivVars M b m ms = steadySolution (linkLinear M) b m ms ∧
      SteadyLinear (linkLinear M) b m ms (derivVars M b m ms) := by
  obtain ⟨hy, hys, hC, hCs, hX, hq, hqs⟩ := linearisation_link M b m ms
  have hθ := M.hθ
  have hθ0 : M.θ ≠ 0 := by linarith
  have hn : 1 - M.n ≠ 0 := by linarith [M.hn1]
  have heq : derivVars M b m ms = steadySolution (linkLinear M) b m ms := by
    simp only [derivVars, hy.deriv, hys.deriv, hC.deriv, hCs.deriv, hX.deriv, hq.deriv,
      hqs.deriv]
    simp only [steadySolution, linkLinear, SteadyVars.mk.injEq]
    refine ⟨trivial, trivial, trivial, trivial, ?_, ?_, trivial, ?_, ?_, trivial⟩ <;>
      field_simp <;> ring
  exact ⟨heq, (steadyLinear_iff _ b m ms _).2 heq⟩

end ObstfeldRogoff.StickyPriceModels.ReduxLinearisationLink

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# The small open economy with monopolistic nontradables: the model

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §10.2.1–10.2.3,
pp. 689–692. A small open economy has a constant endowment `ȳ_T` of a homogeneous traded good
priced in world markets (`P_T = 𝓔 P_T^*`, `P_T^*` constant) and a continuum of monopolistically
supplied nontraded goods. Period utility is (82):
`γ log C_T + (1−γ) log C_N + (χ/(1−ε)) (M/P)^{1−ε} − (κ/2) y_N²`, the consumer price index is
the Cobb–Douglas index (83), bonds are denominated in tradables with `β(1+r) = 1`, and seignorage
is rebated lump sum (85).

This file formalises the household problem as a genuine infinite-horizon problem.

* A generic infinite-horizon theory: the wealth recursion `A_{t+1} = (1+r)(A_t + h_t(x_t))`, the
  no-Ponzi condition, the transversality condition, sufficiency of a pointwise saddle condition
  (concave Lagrangian) together with the transversality condition, necessity of optimality under
  finite perturbations, and necessity of the transversality condition.
* The Cobb–Douglas price index (83) as a minimum cost, and the split (89).
* The household problem of (82), (84), (86): the book's budget (84) is equivalent to the wealth
  recursion; the first-order conditions (87)–(90) plus the no-Ponzi and transversality
  conditions are NECESSARY AND SUFFICIENT for optimality (`householdOptimal_iff`).
* Equilibrium: (91) holds exactly for ANY money path under the no-bubble condition; precisely,
  `C_T ≥ ȳ_T` always and `C_T = ȳ_T` iff the discounted real value of money has liminf zero;
  the money-demand equation (92); the unique steady-state output (93); the unique steady-state
  price level given the money supply; and existence (the steady state is an equilibrium).

Implicit hypotheses made explicit: `0 < β < 1`, `β(1+r) = 1`, `0 < γ < 1`, `χ > 0`, `ε > 0`,
`κ > 0`, `θ > 1`, positive prices, and a positive nominal interest rate (a positive user cost of
money, `1/P_{T,t} − 1/((1+r)P_{T,t+1}) > 0`). The book's real-balance term `(χ/(1−ε)) z^{1−ε}` is
read as `χ log z` at `ε = 1` (`moneyU`).
-/

namespace ObstfeldRogoff.StickyPriceModels.NontradablesModel

open Real Filter Topology Finset

/-! ## Tangent inequalities -/

/-- Tangent inequality behind the concavity of `(χ/(1−ε)) z^{1−ε}` and of revenue `y^{(θ−1)/θ}`
(O&R (82), (90), pp. 690–691): for `s ≤ 1`, `s ≠ 0`, `b^s/s ≤ a^s/s + a^{s−1}(b − a)`. -/
theorem rpow_div_le_tangent {s a b : ℝ} (hs0 : s ≠ 0) (hs1 : s ≤ 1) (ha : 0 < a) (hb : 0 < b) :
    b ^ s / s ≤ a ^ s / s + a ^ (s - 1) * (b - a) := by
  have hq : 0 < b / a := div_pos hb ha
  have key : b ^ s = a ^ s * (b / a) ^ s := by
    rw [div_rpow hb.le ha.le]; field_simp
  have hsplit : a ^ (s - 1) * (b - a) = a ^ s * (b / a - 1) := by
    rw [rpow_sub_one ha.ne']; field_simp
  have has : 0 < a ^ s := rpow_pos_of_pos ha s
  rcases lt_or_gt_of_ne hs0 with hneg | hpos
  · have h1 : 1 + s * (b / a - 1) ≤ (b / a) ^ s := by
      have e1 : (b / a) ^ s = exp (log (b / a) * s) := rpow_def_of_pos hq s
      have e2 := add_one_le_exp (log (b / a) * s)
      have e3 : log (b / a) ≤ b / a - 1 := log_le_sub_one_of_pos hq
      have e4 : s * (b / a - 1) ≤ log (b / a) * s := by nlinarith
      rw [e1]; linarith
    have h2 : s * (a ^ (s - 1) * (b - a)) ≤ b ^ s - a ^ s := by
      rw [hsplit, key]; nlinarith [mul_le_mul_of_nonneg_left h1 has.le]
    have h3 : (b ^ s - a ^ s) / s ≤ a ^ (s - 1) * (b - a) := by
      rw [div_le_iff_of_neg hneg]; linarith
    have h4 : (b ^ s - a ^ s) / s = b ^ s / s - a ^ s / s := sub_div _ _ _
    linarith
  · have h1 : (b / a) ^ s ≤ 1 + s * (b / a - 1) := by
      have := rpow_one_add_le_one_add_mul_self (s := b / a - 1) (by linarith) hpos.le hs1
      simpa using this
    have h2 : b ^ s - a ^ s ≤ s * (a ^ (s - 1) * (b - a)) := by
      rw [hsplit, key]; nlinarith [mul_le_mul_of_nonneg_left h1 has.le]
    have h3 : (b ^ s - a ^ s) / s ≤ a ^ (s - 1) * (b - a) := by
      rw [div_le_iff₀ hpos]; linarith
    have h4 : (b ^ s - a ^ s) / s = b ^ s / s - a ^ s / s := sub_div _ _ _
    linarith

/-- Tangent inequality for `y ↦ y^s`, `0 < s ≤ 1` (concavity of monopoly revenue, O&R (90),
p. 691): `b^s ≤ a^s + s a^{s−1}(b − a)`. -/
theorem rpow_le_tangent {s a b : ℝ} (hs0 : 0 < s) (hs1 : s ≤ 1) (ha : 0 < a) (hb : 0 < b) :
    b ^ s ≤ a ^ s + s * (a ^ (s - 1) * (b - a)) := by
  have h := rpow_div_le_tangent hs0.ne' hs1 ha hb
  have h' := mul_le_mul_of_nonneg_left h hs0.le
  have e1 : s * (b ^ s / s) = b ^ s := by field_simp
  have e2 : s * (a ^ s / s + a ^ (s - 1) * (b - a)) = a ^ s + s * (a ^ (s - 1) * (b - a)) := by
    field_simp
  linarith

/-- Tangent inequality for `k log` (O&R (82), p. 690): with `k ≥ 0`, `a, c > 0`,
`k log a − (k/c) a ≤ k log c − (k/c) c`. -/
theorem log_tangent {k a c : ℝ} (hk : 0 ≤ k) (ha : 0 < a) (hc : 0 < c) :
    k * log a - k / c * a ≤ k * log c - k / c * c := by
  have h1 : log (a / c) ≤ a / c - 1 := log_le_sub_one_of_pos (div_pos ha hc)
  rw [log_div ha.ne' hc.ne'] at h1
  have h2 := mul_le_mul_of_nonneg_left h1 hk
  have e : k * (a / c - 1) = k / c * a - k / c * c := by field_simp
  nlinarith

/-! ## Real balances in utility -/

/-- The real-balance term of (82), p. 690: `(χ/(1−ε)) z^{1−ε}`, read as `χ log z` at `ε = 1`
(the book's log limit). -/
noncomputable def moneyU (χ ε z : ℝ) : ℝ :=
  if ε = 1 then χ * log z else χ / (1 - ε) * z ^ (1 - ε)

/-- The marginal utility of real balances (O&R (88), p. 691) is `χ z^{−ε}`. -/
theorem hasDerivAt_moneyU (χ ε : ℝ) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (moneyU χ ε) (χ * z ^ (-ε)) z := by
  by_cases hε : ε = 1
  · subst hε
    have h := (hasDerivAt_log hz.ne').const_mul χ
    have e : moneyU χ 1 = fun w => χ * log w := by
      funext w; simp [moneyU]
    rw [e, rpow_neg_one]; exact h
  · have h1 : (1 : ℝ) - ε ≠ 0 := sub_ne_zero.mpr (Ne.symm hε)
    have h := (hasDerivAt_rpow_const (p := 1 - ε) (Or.inl hz.ne')).const_mul (χ / (1 - ε))
    have e : moneyU χ ε = fun w => χ / (1 - ε) * w ^ (1 - ε) := by
      funext w; simp [moneyU, hε]
    rw [e]
    convert h using 1
    rw [show (1 : ℝ) - ε - 1 = -ε by ring]; field_simp

/-- Concavity of the real-balance term (O&R (82), `ε > 0`), as a tangent inequality:
`v(b) ≤ v(a) + χ a^{−ε} (b − a)`. -/
theorem moneyU_le_tangent {χ ε a b : ℝ} (hχ : 0 ≤ χ) (hε : 0 < ε) (ha : 0 < a) (hb : 0 < b) :
    moneyU χ ε b ≤ moneyU χ ε a + χ * a ^ (-ε) * (b - a) := by
  by_cases h1 : ε = 1
  · subst h1
    simp only [moneyU, ite_true, rpow_neg_one]
    have := log_tangent hχ hb ha
    have e : χ / a * b - χ / a * a = χ * a⁻¹ * (b - a) := by field_simp
    nlinarith [log_tangent hχ hb ha]
  · have hs0 : (1 : ℝ) - ε ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
    simp only [moneyU, h1, ite_false]
    have ht := rpow_div_le_tangent hs0 (by linarith) ha hb
    have ht' := mul_le_mul_of_nonneg_left ht hχ
    have e1 : χ / (1 - ε) * b ^ (1 - ε) = χ * (b ^ (1 - ε) / (1 - ε)) := by ring
    have e2 : χ / (1 - ε) * a ^ (1 - ε) = χ * (a ^ (1 - ε) / (1 - ε)) := by ring
    rw [e1, e2, show (1 : ℝ) - ε - 1 = -ε by ring] at *
    nlinarith

/-- The real-balance term is strictly increasing for `χ > 0` (O&R (82)). -/
theorem moneyU_strictMonoOn {χ ε : ℝ} (hχ : 0 < χ) :
    StrictMonoOn (moneyU χ ε) (Set.Ioi 0) := by
  refine strictMonoOn_of_deriv_pos (convex_Ioi 0) ?_ ?_
  · intro z hz
    exact (hasDerivAt_moneyU χ ε hz).continuousAt.continuousWithinAt
  · intro z hz
    rw [interior_Ioi] at hz
    rw [(hasDerivAt_moneyU χ ε hz).deriv]
    exact mul_pos hχ (rpow_pos_of_pos hz _)


/-! ## Generic infinite-horizon theory -/

/-- The market discount factor `(1+r)^{−T}` in tradables (O&R §10.2.1, p. 690). -/
noncomputable def disc (r : ℝ) (T : ℕ) : ℝ := ((1 + r) ^ T)⁻¹

/-- Wealth recursion `A_{t+1} = (1+r)(A_t + h_t(x_t))`, where `h_t` is the net real resource
flow of the date-`t` choice (the budget (84) in wealth form, O&R p. 691). -/
noncomputable def wealth {X : Type*} (r A0 : ℝ) (h : ℕ → X → ℝ) (x : ℕ → X) : ℕ → ℝ
  | 0 => A0
  | t + 1 => (1 + r) * (wealth r A0 h x t + h t (x t))

/-- The discount factor is positive (O&R p. 690). -/
theorem disc_pos {r : ℝ} (hr : 0 < 1 + r) (T : ℕ) : 0 < disc r T :=
  inv_pos.mpr (pow_pos hr T)

/-- One-step discounting: `(1+r)^{−(t+1)}(1+r) = (1+r)^{−t}` (O&R p. 690). -/
theorem disc_succ_mul {r : ℝ} (hr : 0 < 1 + r) (t : ℕ) :
    disc r (t + 1) * (1 + r) = disc r t := by
  simp only [disc, pow_succ]
  field_simp

/-- Discounted wealth equals initial wealth plus the present value of net resources
(iterating (84), O&R fn 22 and p. 692). -/
theorem disc_mul_wealth {X : Type*} {r : ℝ} (hr : 0 < 1 + r) (A0 : ℝ) (h : ℕ → X → ℝ)
    (x : ℕ → X) (T : ℕ) :
    disc r T * wealth r A0 h x T = A0 + ∑ t ∈ range T, disc r t * h t (x t) := by
  induction T with
  | zero => simp [disc, wealth]
  | succ T ih =>
    rw [sum_range_succ, ← add_assoc, ← ih]
    have e : disc r (T + 1) * wealth r A0 h x (T + 1)
        = (disc r (T + 1) * (1 + r)) * (wealth r A0 h x T + h T (x T)) := by
      simp only [wealth]; ring
    rw [e, disc_succ_mul hr]; ring

/-- Two plans that agree outside a finite set `S` have discounted wealth differing, after `S`,
by the present value of the net-resource changes on `S` (O&R p. 691, perturbations). -/
theorem disc_mul_wealth_sub {X : Type*} {r : ℝ} (hr : 0 < 1 + r) (A0 : ℝ) (h : ℕ → X → ℝ)
    {x x' : ℕ → X} {S : Finset ℕ} (hS : ∀ t ∉ S, x' t = x t) {T : ℕ}
    (hT : ∀ t ∈ S, t < T) :
    disc r T * wealth r A0 h x' T
      = disc r T * wealth r A0 h x T + ∑ t ∈ S, disc r t * (h t (x' t) - h t (x t)) := by
  rw [disc_mul_wealth hr, disc_mul_wealth hr]
  have hsub : S ⊆ range T := fun t ht => mem_range.mpr (hT t ht)
  have e : ∑ t ∈ range T, disc r t * (h t (x' t) - h t (x t))
      = ∑ t ∈ S, disc r t * (h t (x' t) - h t (x t)) := by
    symm
    apply sum_subset hsub
    intro t _ htS
    rw [hS t htS]; ring
  have e2 : ∑ t ∈ range T, disc r t * h t (x' t)
      = ∑ t ∈ range T, disc r t * h t (x t)
        + ∑ t ∈ range T, disc r t * (h t (x' t) - h t (x t)) := by
    rw [← sum_add_distrib]; congr 1; funext t; ring
  rw [e2, e]; ring

/-- A series changed on a finite set stays summable, and its sum changes by the finite sum of
the changes (used for finite perturbations of lifetime utility (82)). -/
theorem tsum_eq_add_of_eq_off {f g : ℕ → ℝ} (hf : Summable f) (S : Finset ℕ)
    (hS : ∀ t ∉ S, g t = f t) :
    Summable g ∧ ∑' t, g t = ∑' t, f t + ∑ t ∈ S, (g t - f t) := by
  have hd : ∀ t ∉ S, g t - f t = 0 := fun t ht => by rw [hS t ht]; ring
  have hds : Summable fun t => g t - f t := summable_of_ne_finset_zero hd
  have hg : g = fun t => f t + (g t - f t) := by funext t; ring
  have hgs : Summable g := by rw [hg]; exact hf.add hds
  refine ⟨hgs, ?_⟩
  calc ∑' t, g t = ∑' t, (f t + (g t - f t)) := by rw [← hg]
    _ = ∑' t, f t + ∑' t, (g t - f t) := hf.tsum_add hds
    _ = ∑' t, f t + ∑ t ∈ S, (g t - f t) := by rw [tsum_eq_sum hd]

/-- The no-Ponzi condition `liminf (1+r)^{−T} A_T ≥ 0` (O&R (16), p. 666, not stated there;
supplied here), in the robust form `∀ δ > 0, eventually (1+r)^{−T} A_T ≥ −δ`. -/
def NoPonzi (r : ℝ) (A : ℕ → ℝ) : Prop :=
  ∀ δ > 0, ∀ᶠ T in atTop, -δ ≤ disc r T * A T

/-- The transversality condition in its necessary form `liminf (1+r)^{−T} A_T ≤ 0`
(O&R (16), p. 666): discounted wealth is frequently below every `δ > 0`. -/
def LiminfNonpos (r : ℝ) (A : ℕ → ℝ) : Prop :=
  ∀ δ > 0, ∃ᶠ T in atTop, disc r T * A T ≤ δ

/-- Optimality in the infinite-horizon problem (O&R (82) subject to (84)): the plan is admissible,
satisfies no-Ponzi, has summable discounted utility, and weakly beats every such plan. -/
def IsOptimal {X : Type*} (β r A0 : ℝ) (U h : ℕ → X → ℝ) (D : ℕ → Set X) (x : ℕ → X) :
    Prop :=
  (∀ t, x t ∈ D t) ∧ NoPonzi r (wealth r A0 h x) ∧ Summable (fun t => β ^ t * U t (x t)) ∧
    ∀ x' : ℕ → X, (∀ t, x' t ∈ D t) → NoPonzi r (wealth r A0 h x') →
      Summable (fun t => β ^ t * U t (x' t)) →
      ∑' t, β ^ t * U t (x' t) ≤ ∑' t, β ^ t * U t (x t)

/-- A convergent sequence that is frequently above `c` has limit at least `c`. -/
theorem le_of_tendsto_of_frequently {s : ℕ → ℝ} {L c : ℝ} (hs : Tendsto s atTop (𝓝 L))
    (hc : ∃ᶠ T in atTop, c ≤ s T) : c ≤ L := by
  by_contra hlt
  push Not at hlt
  have hev : ∀ᶠ T in atTop, s T < c := hs.eventually (gt_mem_nhds hlt)
  obtain ⟨T, h1, h2⟩ := (hc.and_eventually hev).exists
  linarith

/-- SUFFICIENCY (O&R §10.2.2, the concave-Lagrangian argument): if the plan maximises the
date-`t` Lagrangian `β^t U_t + μ₀(1+r)^{−t} h_t` pointwise over the admissible set, satisfies
no-Ponzi and the transversality condition (liminf form), and has summable utility, it is
optimal. -/
theorem isOptimal_of_saddle {X : Type*} {β r A0 μ0 : ℝ} {U h : ℕ → X → ℝ} {D : ℕ → Set X}
    {x : ℕ → X} (hr : 0 < 1 + r) (hμ : 0 ≤ μ0) (hx : ∀ t, x t ∈ D t)
    (hsum : Summable fun t => β ^ t * U t (x t)) (hnp : NoPonzi r (wealth r A0 h x))
    (htv : LiminfNonpos r (wealth r A0 h x))
    (hsad : ∀ t, ∀ y ∈ D t, β ^ t * U t y + μ0 * (disc r t * h t y)
      ≤ β ^ t * U t (x t) + μ0 * (disc r t * h t (x t))) :
    IsOptimal β r A0 U h D x := by
  refine ⟨hx, hnp, hsum, ?_⟩
  intro x' hx' hnp' hsum'
  set s : ℕ → ℝ := fun T => ∑ t ∈ range T, (β ^ t * U t (x t) - β ^ t * U t (x' t))
  have hlim : Tendsto s atTop
      (𝓝 (∑' t, β ^ t * U t (x t) - ∑' t, β ^ t * U t (x' t))) :=
    (hsum.hasSum.sub hsum'.hasSum).tendsto_sum_nat
  have hbound : ∀ T, μ0 * (disc r T * wealth r A0 h x' T - disc r T * wealth r A0 h x T)
      ≤ s T := by
    intro T
    rw [disc_mul_wealth hr, disc_mul_wealth hr]
    have e : μ0 * (A0 + ∑ t ∈ range T, disc r t * h t (x' t)
        - (A0 + ∑ t ∈ range T, disc r t * h t (x t)))
        = ∑ t ∈ range T, (μ0 * (disc r t * h t (x' t)) - μ0 * (disc r t * h t (x t))) := by
      rw [sum_sub_distrib, ← mul_sum, ← mul_sum]; ring
    rw [e]
    apply sum_le_sum
    intro t _
    have := hsad t (x' t) (hx' t)
    linarith
  have key : ∀ δ > 0, -(2 * μ0 * δ) ≤ ∑' t, β ^ t * U t (x t) - ∑' t, β ^ t * U t (x' t) := by
    intro δ hδ
    apply le_of_tendsto_of_frequently hlim
    refine ((htv δ hδ).and_eventually (hnp' δ hδ)).mono ?_
    intro T ⟨h1, h2⟩
    have := hbound T
    nlinarith
  have hfin : 0 ≤ ∑' t, β ^ t * U t (x t) - ∑' t, β ^ t * U t (x' t) := by
    apply le_of_forall_pos_le_add
    intro ε hε
    have := key (ε / (2 * μ0 + 1)) (by positivity)
    have h3 : 2 * μ0 * (ε / (2 * μ0 + 1)) ≤ ε := by
      rw [← mul_div_assoc, div_le_iff₀ (by positivity)]; nlinarith
    linarith
  linarith

/-- No-Ponzi is preserved by a finite perturbation that does not lower the present value of
net resources (O&R p. 691). -/
theorem noPonzi_of_perturb {X : Type*} {r A0 : ℝ} (hr : 0 < 1 + r) {h : ℕ → X → ℝ}
    {x x' : ℕ → X} {S : Finset ℕ} (hS : ∀ t ∉ S, x' t = x t)
    (hnp : NoPonzi r (wealth r A0 h x))
    (hpv : 0 ≤ ∑ t ∈ S, disc r t * (h t (x' t) - h t (x t))) :
    NoPonzi r (wealth r A0 h x') := by
  intro δ hδ
  filter_upwards [hnp δ hδ, eventually_gt_atTop (S.sup id)] with T h1 h2
  have hT : ∀ t ∈ S, t < T := fun t ht => lt_of_le_of_lt (le_sup (f := id) ht) h2
  rw [disc_mul_wealth_sub hr A0 h hS hT]
  linarith

/-- NECESSITY under finite perturbations (O&R §10.2.2): at an optimum, no admissible plan that
differs on a finite set `S` and satisfies no-Ponzi raises utility. -/
theorem perturb_utility_le {X : Type*} {β r A0 : ℝ} {U h : ℕ → X → ℝ} {D : ℕ → Set X}
    {x x' : ℕ → X} (hopt : IsOptimal β r A0 U h D x) (hx' : ∀ t, x' t ∈ D t) {S : Finset ℕ}
    (hS : ∀ t ∉ S, x' t = x t) (hnp' : NoPonzi r (wealth r A0 h x')) :
    ∑ t ∈ S, (β ^ t * U t (x' t) - β ^ t * U t (x t)) ≤ 0 := by
  obtain ⟨_, _, hsum, hbest⟩ := hopt
  have hS' : ∀ t ∉ S, β ^ t * U t (x' t) = β ^ t * U t (x t) := fun t ht => by rw [hS t ht]
  obtain ⟨hs', he⟩ := tsum_eq_add_of_eq_off hsum S hS'
  have := hbest x' hx' hnp' hs'
  linarith

/-- NECESSITY under finite perturbations, resource form: an admissible finite perturbation that
does not lower the present value of net resources cannot raise utility (O&R §10.2.2). -/
theorem perturb_utility_le_of_pv {X : Type*} {β r A0 : ℝ} (hr : 0 < 1 + r) {U h : ℕ → X → ℝ}
    {D : ℕ → Set X} {x x' : ℕ → X} (hopt : IsOptimal β r A0 U h D x)
    (hx' : ∀ t, x' t ∈ D t) {S : Finset ℕ} (hS : ∀ t ∉ S, x' t = x t)
    (hpv : 0 ≤ ∑ t ∈ S, disc r t * (h t (x' t) - h t (x t))) :
    ∑ t ∈ S, (β ^ t * U t (x' t) - β ^ t * U t (x t)) ≤ 0 :=
  perturb_utility_le hopt hx' hS (noPonzi_of_perturb hr hS hopt.2.1 hpv)

/-- NECESSITY OF THE TRANSVERSALITY CONDITION (O&R (16), p. 666, for the §10.2 problem): under
local non-satiation at date 0, an optimal plan has `liminf (1+r)^{−T} A_T ≤ 0`. -/
theorem liminfNonpos_of_isOptimal {X : Type*} {β r A0 : ℝ} (hr : 0 < 1 + r)
    {U h : ℕ → X → ℝ} {D : ℕ → Set X} {x : ℕ → X} (hopt : IsOptimal β r A0 U h D x)
    (hns : ∀ η > 0, ∃ y ∈ D 0, h 0 (x 0) - η ≤ h 0 y ∧ U 0 (x 0) < U 0 y) :
    LiminfNonpos r (wealth r A0 h x) := by
  intro δ hδ
  by_contra hcon
  rw [not_frequently] at hcon
  obtain ⟨y, hyD, hyh, hyU⟩ := hns δ hδ
  set x' : ℕ → X := Function.update x 0 y
  have hS : ∀ t ∉ ({0} : Finset ℕ), x' t = x t := by
    intro t ht
    simp only [Finset.mem_singleton] at ht
    simp [x', Function.update_of_ne ht]
  have hx' : ∀ t, x' t ∈ D t := by
    intro t
    by_cases ht : t = 0
    · subst ht; simp [x', hyD]
    · rw [hS t (by simpa using ht)]; exact hopt.1 t
  have hnp' : NoPonzi r (wealth r A0 h x') := by
    intro ε hε
    filter_upwards [hcon, eventually_gt_atTop 0] with T h1 h2
    have hT : ∀ t ∈ ({0} : Finset ℕ), t < T := by
      intro t ht; simp only [Finset.mem_singleton] at ht; omega
    rw [disc_mul_wealth_sub hr A0 h hS hT]
    simp only [Finset.sum_singleton, disc, pow_zero, inv_one, one_mul, x',
      Function.update_self]
    push Not at h1
    simp only [disc] at h1
    linarith
  have := perturb_utility_le hopt hx' hS hnp'
  simp [x'] at this
  linarith


/-! ## The Cobb–Douglas consumer price index (83) -/

/-- The consumption-based price index (83), p. 690:
`P = P_T^γ P_N^{1−γ} / (γ^γ (1−γ)^{1−γ})`. -/
noncomputable def cpi (γ PT PN : ℝ) : ℝ :=
  PT ^ γ * PN ^ (1 - γ) / (γ ^ γ * (1 - γ) ^ (1 - γ))

/-- Composite real consumption `C_T^γ C_N^{1−γ}` (O&R p. 690). -/
noncomputable def composite (γ CT CN : ℝ) : ℝ := CT ^ γ * CN ^ (1 - γ)

/-- The price index (83) is positive (O&R p. 690). -/
theorem cpi_pos {γ PT PN : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hT : 0 < PT) (hN : 0 < PN) :
    0 < cpi γ PT PN := by
  unfold cpi
  have : 0 < 1 - γ := by linarith
  positivity

/-- Key identity behind (83): `P · C_T^γ C_N^{1−γ} = (P_T C_T/γ)^γ (P_N C_N/(1−γ))^{1−γ}`. -/
theorem cpi_mul_composite {γ PT PN CT CN : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hT : 0 < PT)
    (hN : 0 < PN) (hCT : 0 < CT) (hCN : 0 < CN) :
    cpi γ PT PN * composite γ CT CN
      = (PT * CT / γ) ^ γ * (PN * CN / (1 - γ)) ^ (1 - γ) := by
  have h1 : 0 < 1 - γ := by linarith
  unfold cpi composite
  rw [div_rpow (by positivity) hγ0.le, div_rpow (by positivity) h1.le,
    mul_rpow hT.le hCT.le, mul_rpow hN.le hCN.le]
  have : 0 < γ ^ γ := rpow_pos_of_pos hγ0 γ
  have : 0 < (1 - γ) ^ (1 - γ) := rpow_pos_of_pos h1 _
  field_simp

/-- Weighted AM–GM in the form used for (83): `a^γ b^{1−γ} ≤ γ a + (1−γ) b`, strictly if
`a ≠ b`. -/
theorem wamgm_le {γ a b : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (ha : 0 < a) (hb : 0 < b) :
    a ^ γ * b ^ (1 - γ) ≤ γ * a + (1 - γ) * b ∧
      (a ≠ b → a ^ γ * b ^ (1 - γ) < γ * a + (1 - γ) * b) := by
  have e : a ^ γ * b ^ (1 - γ) = b * (1 + (a / b - 1)) ^ γ := by
    rw [show 1 + (a / b - 1) = a / b by ring, div_rpow ha.le hb.le, rpow_sub hb, rpow_one]
    have : 0 < b ^ γ := rpow_pos_of_pos hb γ
    field_simp
  have e2 : γ * a + (1 - γ) * b = b * (1 + γ * (a / b - 1)) := by field_simp; ring
  rw [e, e2]
  refine ⟨mul_le_mul_of_nonneg_left
    (rpow_one_add_le_one_add_mul_self (by have := div_pos ha hb; linarith) hγ0.le hγ1.le) hb.le,
    fun hne => mul_lt_mul_of_pos_left (rpow_one_add_lt_one_add_mul_self
      (by have := div_pos ha hb; linarith) ?_ hγ0 hγ1) hb⟩
  intro h0
  apply hne
  have : a / b = 1 := by linarith
  field_simp at this; linarith

/-- (83) is a lower bound on cost: `P · C_T^γ C_N^{1−γ} ≤ P_T C_T + P_N C_N`, with strict
inequality off the Cobb–Douglas split `P_T C_T/γ = P_N C_N/(1−γ)` (O&R p. 690). -/
theorem cpi_mul_composite_le {γ PT PN CT CN : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hT : 0 < PT)
    (hN : 0 < PN) (hCT : 0 < CT) (hCN : 0 < CN) :
    cpi γ PT PN * composite γ CT CN ≤ PT * CT + PN * CN ∧
      (PT * CT / γ ≠ PN * CN / (1 - γ) →
        cpi γ PT PN * composite γ CT CN < PT * CT + PN * CN) := by
  have h1 : 0 < 1 - γ := by linarith
  obtain ⟨hle, hlt⟩ := wamgm_le (a := PT * CT / γ) (b := PN * CN / (1 - γ)) hγ0 hγ1
    (by positivity) (by positivity)
  have e : γ * (PT * CT / γ) + (1 - γ) * (PN * CN / (1 - γ)) = PT * CT + PN * CN := by
    field_simp
  rw [cpi_mul_composite hγ0 hγ1 hT hN hCT hCN, ← e]
  exact ⟨hle, hlt⟩

/-- fn to (83), p. 690: `P` is the minimum money cost of one unit of `C_T^γ C_N^{1−γ}`,
attained EXACTLY at `C_T = γP/P_T`, `C_N = (1−γ)P/P_N` (existence and uniqueness). -/
theorem cpi_isMinCost {γ PT PN : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hT : 0 < PT) (hN : 0 < PN) :
    composite γ (γ * cpi γ PT PN / PT) ((1 - γ) * cpi γ PT PN / PN) = 1 ∧
      PT * (γ * cpi γ PT PN / PT) + PN * ((1 - γ) * cpi γ PT PN / PN) = cpi γ PT PN ∧
      ∀ CT CN, 0 < CT → 0 < CN → composite γ CT CN = 1 →
        cpi γ PT PN ≤ PT * CT + PN * CN ∧
        (PT * CT + PN * CN = cpi γ PT PN →
          CT = γ * cpi γ PT PN / PT ∧ CN = (1 - γ) * cpi γ PT PN / PN) := by
  have h1 : 0 < 1 - γ := by linarith
  have hP := cpi_pos hγ0 hγ1 hT hN
  set P := cpi γ PT PN with hPdef
  have hcomp : composite γ (γ * P / PT) ((1 - γ) * P / PN) = 1 := by
    have hm := cpi_mul_composite (CT := γ * P / PT) (CN := (1 - γ) * P / PN) hγ0 hγ1 hT hN
      (by positivity) (by positivity)
    rw [← hPdef] at hm
    have e1 : PT * (γ * P / PT) / γ = P := by field_simp
    have e2 : PN * ((1 - γ) * P / PN) / (1 - γ) = P := by field_simp
    rw [e1, e2, ← rpow_add hP, show γ + (1 - γ) = 1 by ring, rpow_one] at hm
    have := mul_left_cancel₀ hP.ne' (hm.trans (mul_one P).symm)
    exact this
  refine ⟨hcomp, by field_simp; ring, ?_⟩
  intro CT CN hCT hCN hc
  obtain ⟨hle, hlt⟩ := cpi_mul_composite_le hγ0 hγ1 hT hN hCT hCN
  rw [← hPdef, hc, mul_one] at hle hlt
  refine ⟨hle, fun heq => ?_⟩
  have hsplit : PT * CT / γ = PN * CN / (1 - γ) := by
    by_contra hne; have := hlt hne; linarith
  have hm := cpi_mul_composite hγ0 hγ1 hT hN hCT hCN
  rw [← hPdef, hc, mul_one, ← hsplit, ← rpow_add (by positivity),
    show γ + (1 - γ) = 1 by ring, rpow_one] at hm
  refine ⟨?_, ?_⟩
  · rw [hm]; field_simp
  · have : PN * CN / (1 - γ) = P := by rw [← hsplit, ← hm]
    field_simp at this ⊢; linarith

/-- (89), p. 691, as the Cobb–Douglas split: `P_T C_T/γ = P_N C_N/(1−γ)` iff
`C_N = ((1−γ)/γ)(P_T/P_N) C_T`. -/
theorem split_iff_89 {γ PT PN CT CN : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hN : 0 < PN) :
    PT * CT / γ = PN * CN / (1 - γ) ↔ CN = (1 - γ) / γ * (PT / PN) * CT := by
  have h1 : (1 : ℝ) - γ ≠ 0 := by linarith
  constructor <;> intro h
  · field_simp at h ⊢; linarith
  · rw [h]; field_simp


/-! ## The household problem (82), (84), (86) -/

/-- Parameters of the §10.2 economy (O&R (82)–(86), pp. 690–691). -/
structure Economy where
  β : ℝ
  r : ℝ
  γ : ℝ
  χ : ℝ
  ε : ℝ
  κ : ℝ
  θ : ℝ
  yT : ℝ

/-- The parameter restrictions of §10.2 made explicit (O&R pp. 690–691 and fn 2). -/
def Economy.Valid (E : Economy) : Prop :=
  0 < E.β ∧ E.β < 1 ∧ 0 < 1 + E.r ∧ 0 < E.γ ∧ E.γ < 1 ∧ 0 < E.χ ∧ 0 < E.ε ∧ 0 < E.κ ∧
    1 < E.θ ∧ 0 < E.yT

/-- Exogenous (to the household) paths: `P_{T,t}`, the nontradables index `P_{N,t}`, aggregate
nontradables consumption `C^A_{N,t}` and lump-sum taxes `τ_t` (O&R (84), (86), p. 691). -/
structure Prices where
  PT : ℕ → ℝ
  PN : ℕ → ℝ
  CA : ℕ → ℝ
  τ : ℕ → ℝ

/-- The real user cost of holding one unit of money from `t` to `t+1`, in tradables:
`1/P_{T,t} − 1/((1+r)P_{T,t+1}) = (i_{t+1}/(1+i_{t+1}))/P_{T,t}` (O&R (88), p. 691). -/
noncomputable def userCost (r : ℝ) (Q : Prices) (t : ℕ) : ℝ :=
  1 / Q.PT t - 1 / ((1 + r) * Q.PT (t + 1))

/-- Admissible price paths: positive prices and aggregate demand, and a positive nominal
interest rate (positive user cost of money) (implicit in O&R (92), p. 692). -/
def Prices.Valid (Q : Prices) (r : ℝ) : Prop :=
  ∀ t, 0 < Q.PT t ∧ 0 < Q.PN t ∧ 0 < Q.CA t ∧ 0 < userCost r Q t

/-- A date-`t` choice of the household: `C_T`, `C_N`, end-of-period money `M_t`, and output
`y_N` of its own nontraded good (O&R (82), (84), p. 690–691). -/
structure Choice where
  cT : ℝ
  cN : ℝ
  money : ℝ
  y : ℝ

/-- Admissible choices: all four components positive (O&R (82) needs `C_T, C_N, M > 0`). -/
def posChoice : Set Choice := {c | 0 < c.cT ∧ 0 < c.cN ∧ 0 < c.money ∧ 0 < c.y}

/-- The relative price `P_N/P_T` (O&R (89), p. 691). -/
noncomputable def relPrice (Q : Prices) (t : ℕ) : ℝ := Q.PN t / Q.PT t

/-- The consumer price index at date `t` (83). -/
noncomputable def cpiAt (E : Economy) (Q : Prices) (t : ℕ) : ℝ := cpi E.γ (Q.PT t) (Q.PN t)

/-- Period utility (82), p. 690. -/
noncomputable def periodU (E : Economy) (Q : Prices) (t : ℕ) (c : Choice) : ℝ :=
  E.γ * log c.cT + (1 - E.γ) * log c.cN + moneyU E.χ E.ε (c.money / cpiAt E Q t)
    - E.κ / 2 * c.y ^ 2

/-- The inverse of the demand curve (86): the money price at which `y` units are demanded,
`p_N = P_N (y/C^A_N)^{−1/θ}` (O&R p. 691). -/
noncomputable def invDemand (E : Economy) (Q : Prices) (t : ℕ) (y : ℝ) : ℝ :=
  Q.PN t * (y / Q.CA t) ^ (-1 / E.θ)

/-- Real revenue in tradables, `(P_N/P_T) y^{(θ−1)/θ} (C^A_N)^{1/θ}` (O&R fn 22, p. 691). -/
noncomputable def realRevenue (E : Economy) (Q : Prices) (t : ℕ) (y : ℝ) : ℝ :=
  relPrice Q t * (y ^ ((E.θ - 1) / E.θ) * Q.CA t ^ (1 / E.θ))

/-- Net real resource flow of a date-`t` choice (the budget (84) in tradables with the money
carried to `t+1` valued at its user cost) (O&R p. 691). -/
noncomputable def netRes (E : Economy) (Q : Prices) (t : ℕ) (c : Choice) : ℝ :=
  E.yT - Q.τ t + realRevenue E Q t c.y - relPrice Q t * c.cN - c.cT - c.money * userCost E.r Q t

/-- Initial real wealth `(1+r)B_0 + M_{−1}/P_{T,0}` (O&R (84), p. 691). -/
noncomputable def initWealth (E : Economy) (Q : Prices) (B0 Mm1 : ℝ) : ℝ :=
  (1 + E.r) * B0 + Mm1 / Q.PT 0

/-- Household optimality in the §10.2 problem: maximise (82) subject to (84), (86), no-Ponzi. -/
def HouseholdOptimal (E : Economy) (Q : Prices) (B0 Mm1 : ℝ) (c : ℕ → Choice) : Prop :=
  IsOptimal E.β E.r (initWealth E Q B0 Mm1) (periodU E Q) (netRes E Q) (fun _ => posChoice) c

/-- (86): at the inverse-demand price, CES demand `(p_N/P_N)^{−θ} C^A_N` is exactly `y`. -/
theorem cesDemand_invDemand (E : Economy) (Q : Prices) (t : ℕ) {y : ℝ} (hθ : 0 < E.θ)
    (hN : 0 < Q.PN t) (hA : 0 < Q.CA t) (hy : 0 < y) :
    cesDemand E.θ (invDemand E Q t y) (Q.PN t) (Q.CA t) = y := by
  unfold cesDemand invDemand
  rw [mul_div_cancel_left₀ _ hN.ne', ← rpow_mul (div_pos hy hA).le,
    show -1 / E.θ * -E.θ = 1 by field_simp, rpow_one]
  field_simp

/-- Revenue identity (O&R fn 22, p. 691): `p_N y / P_T = (P_N/P_T) y^{(θ−1)/θ} (C^A_N)^{1/θ}`. -/
theorem invDemand_mul (E : Economy) (Q : Prices) (t : ℕ) {y : ℝ} (hθ : 0 < E.θ)
    (hT : 0 < Q.PT t) (hA : 0 < Q.CA t) (hy : 0 < y) :
    invDemand E Q t y * y / Q.PT t = realRevenue E Q t y := by
  unfold invDemand realRevenue relPrice
  have hs : (E.θ - 1) / E.θ = -(1 / E.θ) + 1 := by field_simp; ring
  rw [hs, rpow_add hy, rpow_one, div_rpow hy.le hA.le, show (-1 / E.θ) = -(1 / E.θ) by ring,
    rpow_neg hA.le, rpow_neg hy.le]
  have : 0 < Q.CA t ^ (1 / E.θ) := rpow_pos_of_pos hA _
  have : 0 < y ^ (1 / E.θ) := rpow_pos_of_pos hy _
  field_simp

/-- Money carried into date `t`: `M_{−1}` at `t = 0`, `M_{t−1}` afterwards (O&R (84)). -/
def moneyPrev (Mm1 : ℝ) (c : ℕ → Choice) : ℕ → ℝ
  | 0 => Mm1
  | t + 1 => (c t).money

/-- The book's period budget constraint (84), p. 691, in money terms, with the monopolist's
price on its demand curve (86). -/
def Budget84 (E : Economy) (Q : Prices) (B : ℕ → ℝ) (Mm1 : ℝ) (c : ℕ → Choice) (t : ℕ) :
    Prop :=
  Q.PT t * B (t + 1) + (c t).money
    = Q.PT t * (1 + E.r) * B t + moneyPrev Mm1 c t + invDemand E Q t (c t).y * (c t).y
      + Q.PT t * E.yT - Q.PN t * (c t).cN - Q.PT t * (c t).cT - Q.PT t * Q.τ t

/-- (84) is EQUIVALENT to the wealth recursion with `A_t = (1+r)B_t + M_{t−1}/P_{T,t}`
(O&R p. 691): the Lean problem is exactly the book's. -/
theorem budget84_iff_wealth (E : Economy) (Q : Prices) (hE : E.Valid) (hQ : Q.Valid E.r)
    {B : ℕ → ℝ} {B0 Mm1 : ℝ} (hB0 : B 0 = B0) {c : ℕ → Choice} (hc : ∀ t, c t ∈ posChoice) :
    (∀ t, Budget84 E Q B Mm1 c t) ↔
      ∀ t, (1 + E.r) * B t + moneyPrev Mm1 c t / Q.PT t
        = wealth E.r (initWealth E Q B0 Mm1) (netRes E Q) c t := by
  obtain ⟨_, _, hr, _, _, _, _, _, hθ, _⟩ := hE
  have hθ0 : 0 < E.θ := by linarith
  set Ah : ℕ → ℝ := fun t => (1 + E.r) * B t + moneyPrev Mm1 c t / Q.PT t with hAh
  have step : ∀ t, Ah (t + 1) - (1 + E.r) * (Ah t + netRes E Q t (c t))
      = (1 + E.r) / Q.PT t * ((Q.PT t * B (t + 1) + (c t).money)
        - (Q.PT t * (1 + E.r) * B t + moneyPrev Mm1 c t + invDemand E Q t (c t).y * (c t).y
          + Q.PT t * E.yT - Q.PN t * (c t).cN - Q.PT t * (c t).cT - Q.PT t * Q.τ t)) := by
    intro t
    obtain ⟨hT, hN, hA, _⟩ := hQ t
    have hT1 := (hQ (t + 1)).1
    have hrev := invDemand_mul E Q t hθ0 hT hA (hc t).2.2.2
    have hrev' : invDemand E Q t (c t).y * (c t).y = Q.PT t * realRevenue E Q t (c t).y := by
      rw [← hrev]; field_simp
    simp only [hAh, netRes, userCost, relPrice, moneyPrev]
    rw [hrev']
    field_simp
    ring
  have hfac : ∀ t, (1 + E.r) / Q.PT t ≠ 0 := fun t => div_ne_zero hr.ne' (hQ t).1.ne'
  constructor
  · intro hb t
    induction t with
    | zero => simp [moneyPrev, wealth, initWealth, hB0]
    | succ t ih =>
      have h1 := step t
      rw [show Q.PT t * B (t + 1) + (c t).money - _ = 0 from sub_eq_zero.mpr (hb t),
        mul_zero, sub_eq_zero] at h1
      change Ah (t + 1) = _
      rw [h1, wealth]
      exact congrArg (fun z => (1 + E.r) * (z + netRes E Q t (c t))) ih
  · intro hw t
    have h1 := step t
    have e1 : Ah (t + 1) = wealth E.r (initWealth E Q B0 Mm1) (netRes E Q) c (t + 1) := hw (t + 1)
    have e0 : Ah t = wealth E.r (initWealth E Q B0 Mm1) (netRes E Q) c t := hw t
    rw [e1, e0, wealth, sub_self] at h1
    have := (mul_eq_zero.mp h1.symm).resolve_left (hfac t)
    exact sub_eq_zero.mp this


/-! ## First-order conditions (87)–(90) -/

/-- The consumption Euler equation for tradables, `γ/C_{T,t} = β(1+r) γ/C_{T,t+1}`; with
`β(1+r) = 1` this is (87), p. 691. -/
def EulerFOC (E : Economy) (c : ℕ → Choice) : Prop :=
  ∀ t, E.γ / (c t).cT = E.β * (1 + E.r) * (E.γ / (c (t + 1)).cT)

/-- The intratemporal condition (89), p. 691: `(1−γ)/C_N = (γ/C_T)(P_N/P_T)`. -/
def IntraFOC (E : Economy) (Q : Prices) (c : ℕ → Choice) : Prop :=
  ∀ t, (1 - E.γ) / (c t).cN = E.γ / (c t).cT * relPrice Q t

/-- The money condition behind (88), p. 691: the marginal utility of money equals the marginal
utility of tradables times the user cost,
`χ (M/P)^{−ε}/P = (γ/C_T)(1/P_{T,t} − 1/((1+r)P_{T,t+1}))`. -/
def MoneyFOC (E : Economy) (Q : Prices) (c : ℕ → Choice) : Prop :=
  ∀ t, E.χ * ((c t).money / cpiAt E Q t) ^ (-E.ε) / cpiAt E Q t
    = E.γ / (c t).cT * userCost E.r Q t

/-- The monopolist's output condition behind (90), p. 691: marginal disutility of effort equals
the marginal utility of marginal revenue, `κ y = (γ/C_T)(P_N/P_T)((θ−1)/θ) y^{−1/θ}(C^A_N)^{1/θ}`.
-/
def LabourFOC (E : Economy) (Q : Prices) (c : ℕ → Choice) : Prop :=
  ∀ t, E.κ * (c t).y = E.γ / (c t).cT * relPrice Q t *
    ((E.θ - 1) / E.θ * ((c t).y ^ ((E.θ - 1) / E.θ - 1) * Q.CA t ^ (1 / E.θ)))

/-- The pointwise Lagrangian inequality (O&R §10.2.2): at a choice satisfying (89), the money
condition and the output condition, with multiplier `λ = γ/C_T`, the date-`t` Lagrangian
`U_t + λ h_t` is maximised over all admissible choices (concavity). -/
theorem periodLagrangian_le (E : Economy) (Q : Prices) (hE : E.Valid) (hQ : Q.Valid E.r)
    (t : ℕ) {c y : Choice} (hc : c ∈ posChoice) (hy : y ∈ posChoice)
    (hN : (1 - E.γ) / c.cN = E.γ / c.cT * relPrice Q t)
    (hM : E.χ * (c.money / cpiAt E Q t) ^ (-E.ε) / cpiAt E Q t
      = E.γ / c.cT * userCost E.r Q t)
    (hL : E.κ * c.y = E.γ / c.cT * relPrice Q t *
      ((E.θ - 1) / E.θ * (c.y ^ ((E.θ - 1) / E.θ - 1) * Q.CA t ^ (1 / E.θ)))) :
    periodU E Q t y + E.γ / c.cT * netRes E Q t y
      ≤ periodU E Q t c + E.γ / c.cT * netRes E Q t c := by
  obtain ⟨_, _, _, hγ0, hγ1, hχ, hε, hκ, hθ, _⟩ := hE
  obtain ⟨hT, hPN, hA, _⟩ := hQ t
  obtain ⟨ha, hb, hn, hq⟩ := hc
  obtain ⟨ha', hb', hn', hq'⟩ := hy
  have hP : 0 < cpiAt E Q t := cpi_pos hγ0 hγ1 hT hPN
  have hρ : 0 < relPrice Q t := div_pos hPN hT
  set lam := E.γ / c.cT with hlam
  set ρ := relPrice Q t
  set P := cpiAt E Q t
  set K := Q.CA t ^ (1 / E.θ)
  set s := (E.θ - 1) / E.θ with hs
  have hK : 0 < K := rpow_pos_of_pos hA _
  have hs0 : 0 < s := div_pos (by linarith) (by linarith)
  have hs1 : s ≤ 1 := by rw [hs, div_le_one (by linarith)]; linarith
  have hlam0 : 0 < lam := div_pos hγ0 ha
  -- (A) tradables
  have hA' := log_tangent hγ0.le ha' ha
  -- (B) nontradables
  have hB' := log_tangent (k := 1 - E.γ) (by linarith) hb' hb
  have hBr : (1 - E.γ) / c.cN = lam * ρ := hN
  -- (C) money
  have hC' := moneyU_le_tangent hχ.le hε (div_pos hn hP) (div_pos hn' hP) (χ := E.χ)
  have hCr : E.χ * (c.money / P) ^ (-E.ε) * (y.money / P - c.money / P)
      = lam * userCost E.r Q t * (y.money - c.money) := by
    rw [← hM]; field_simp
  -- (D) output
  have hD1 := rpow_le_tangent hs0 hs1 hq hq'
  have hD2 : lam * ρ * K * y.y ^ s ≤ lam * ρ * K * c.y ^ s + E.κ * c.y * (y.y - c.y) := by
    have hL' : E.κ * c.y = lam * ρ * K * (s * c.y ^ (s - 1)) := by rw [hL]; ring
    have hpos : 0 ≤ lam * ρ * K := by positivity
    have := mul_le_mul_of_nonneg_left hD1 hpos
    rw [hL']; linarith
  have hD3 : -(E.κ / 2) * y.y ^ 2 ≤ -(E.κ / 2) * c.y ^ 2 - E.κ * c.y * (y.y - c.y) := by
    have hsq : -(E.κ / 2) * y.y ^ 2 - (-(E.κ / 2) * c.y ^ 2 - E.κ * c.y * (y.y - c.y))
        = -(E.κ / 2 * (y.y - c.y) ^ 2) := by ring
    have := mul_nonneg (by linarith : 0 ≤ E.κ / 2) (sq_nonneg (y.y - c.y))
    linarith
  simp only [periodU, netRes, realRevenue]
  rw [hBr] at hB'
  have e1 : (1 - E.γ) / c.cN * y.cN = lam * ρ * y.cN := by rw [hBr]
  have e2 : (1 - E.γ) / c.cN * c.cN = lam * ρ * c.cN := by rw [hBr]
  linarith [hA', hB', hC', hCr, hD2, hD3, e1, e2]

/-- Under the Euler equation, the discounted marginal utility of tradables is a market-discounted
constant: `β^t γ/C_{T,t} = (γ/C_{T,0}) (1+r)^{−t}` (O&R (87)). -/
theorem discounted_mu_of_euler {E : Economy} {c : ℕ → Choice} (hβ : 0 < E.β)
    (hr : 0 < 1 + E.r) (hc : ∀ t, c t ∈ posChoice) (heu : EulerFOC E c) (hγ : 0 < E.γ) (t : ℕ) :
    E.β ^ t * (E.γ / (c t).cT) = E.γ / (c 0).cT * disc E.r t := by
  induction t with
  | zero => simp [disc]
  | succ t ih =>
    have h := heu t
    have ha := (hc (t + 1)).1
    have hnext : E.γ / (c (t + 1)).cT = E.γ / (c t).cT / (E.β * (1 + E.r)) := by
      rw [h]; field_simp
    have e : E.γ / (c 0).cT * disc E.r (t + 1) = (E.γ / (c 0).cT * disc E.r t) / (1 + E.r) := by
      rw [← disc_succ_mul hr t]; field_simp
    rw [hnext, pow_succ, e, ← ih]
    field_simp

/-- SUFFICIENCY (O&R §10.2.2): an admissible plan with summable utility satisfying (87)–(90),
no-Ponzi and the transversality condition (liminf form) is a household optimum. -/
theorem householdOptimal_of_foc {E : Economy} {Q : Prices} (hE : E.Valid) (hQ : Q.Valid E.r)
    {B0 Mm1 : ℝ} {c : ℕ → Choice} (hc : ∀ t, c t ∈ posChoice)
    (hsum : Summable fun t => E.β ^ t * periodU E Q t (c t)) (heu : EulerFOC E c)
    (hN : IntraFOC E Q c) (hM : MoneyFOC E Q c) (hL : LabourFOC E Q c)
    (hnp : NoPonzi E.r (wealth E.r (initWealth E Q B0 Mm1) (netRes E Q) c))
    (htv : LiminfNonpos E.r (wealth E.r (initWealth E Q B0 Mm1) (netRes E Q) c)) :
    HouseholdOptimal E Q B0 Mm1 c := by
  have hE' := hE
  obtain ⟨hβ, _, hr, hγ0, _, _, _, _, _, _⟩ := hE'
  refine isOptimal_of_saddle (μ0 := E.γ / (c 0).cT) hr (div_pos hγ0 (hc 0).1).le hc hsum hnp
    htv ?_
  intro t y hy
  have hl := periodLagrangian_le E Q hE hQ t (hc t) hy (hN t) (hM t) (hL t)
  have hd := discounted_mu_of_euler hβ hr hc heu hγ0 t
  have hβt : 0 ≤ E.β ^ t := pow_nonneg hβ.le t
  have key := mul_le_mul_of_nonneg_left hl hβt
  have e : ∀ z : Choice, E.β ^ t * (periodU E Q t z + E.γ / (c t).cT * netRes E Q t z)
      = E.β ^ t * periodU E Q t z + E.γ / (c 0).cT * (disc E.r t * netRes E Q t z) := by
    intro z
    have h2 : E.γ / (c 0).cT * (disc E.r t * netRes E Q t z)
        = (E.β ^ t * (E.γ / (c t).cT)) * netRes E Q t z := by rw [hd]; ring
    rw [h2]; ring
  rw [e, e] at key
  exact key


/-- A single-date perturbation that keeps net resources weakly higher cannot raise date-`t`
utility at an optimum: `η ↦ U_t(g η)` has a local maximum at `0` (O&R §10.2.2). -/
theorem isLocalMax_of_perturb {E : Economy} {Q : Prices} {B0 Mm1 : ℝ} {c : ℕ → Choice}
    (hr : 0 < 1 + E.r) (hβ : 0 < E.β) (hopt : HouseholdOptimal E Q B0 Mm1 c) (t : ℕ)
    (g : ℝ → Choice) (hg0 : g 0 = c t) (hgpos : ∀ᶠ η in 𝓝 0, g η ∈ posChoice)
    (hgres : ∀ η, netRes E Q t (c t) ≤ netRes E Q t (g η)) :
    IsLocalMax (fun η => periodU E Q t (g η)) 0 := by
  filter_upwards [hgpos] with η hη
  set x' : ℕ → Choice := Function.update c t (g η)
  have hS : ∀ s ∉ ({t} : Finset ℕ), x' s = c s := by
    intro s hs
    simp only [Finset.mem_singleton] at hs
    simp [x', Function.update_of_ne hs]
  have hx' : ∀ s, x' s ∈ posChoice := by
    intro s
    by_cases hs : s = t
    · subst hs; simpa [x'] using hη
    · rw [hS s (by simpa using hs)]; exact hopt.1 s
  have hpv : 0 ≤ ∑ s ∈ ({t} : Finset ℕ),
      disc E.r s * (netRes E Q s (x' s) - netRes E Q s (c s)) := by
    simp only [Finset.sum_singleton, x', Function.update_self]
    exact mul_nonneg (disc_pos hr t).le (by linarith [hgres η])
  have h := perturb_utility_le_of_pv hr hopt hx' hS hpv
  simp only [Finset.sum_singleton, x', Function.update_self] at h
  have hβt : 0 < E.β ^ t := pow_pos hβ t
  simp only [hg0]
  nlinarith

/-- NECESSITY of (89), p. 691, at a household optimum. -/
theorem intraFOC_of_optimal {E : Economy} {Q : Prices} (hE : E.Valid)
    {B0 Mm1 : ℝ} {c : ℕ → Choice} (hopt : HouseholdOptimal E Q B0 Mm1 c) : IntraFOC E Q c := by
  obtain ⟨hβ, _, hr, hγ0, hγ1, _, _, _, _, _⟩ := hE
  intro t
  obtain ⟨ha, hb, hn, hq⟩ := hopt.1 t
  set ρ := relPrice Q t
  set g : ℝ → Choice := fun η =>
    ⟨(c t).cT - ρ * η, (c t).cN + η, (c t).money, (c t).y⟩ with hg
  have hg0 : g 0 = c t := by simp [g]
  have hgpos : ∀ᶠ η in 𝓝 0, g η ∈ posChoice := by
    have h1 : ∀ᶠ η in 𝓝 (0 : ℝ), 0 < (c t).cT - ρ * η :=
      (continuous_const.sub (continuous_const.mul continuous_id)).continuousAt.eventually
        (lt_mem_nhds (by simpa using ha))
    have h2 : ∀ᶠ η in 𝓝 (0 : ℝ), 0 < (c t).cN + η :=
      (continuous_const.add continuous_id).continuousAt.eventually
        (lt_mem_nhds (by simpa using hb))
    filter_upwards [h1, h2] with η e1 e2
    exact ⟨e1, e2, hn, hq⟩
  have hgres : ∀ η, netRes E Q t (c t) ≤ netRes E Q t (g η) := by
    intro η; simp only [netRes, g]; linarith
  have hmax := isLocalMax_of_perturb hr hβ hopt t g hg0 hgpos hgres
  have hfun : (fun η => periodU E Q t (g η)) = fun η =>
      E.γ * log ((c t).cT - ρ * η) + (1 - E.γ) * log ((c t).cN + η)
        + (moneyU E.χ E.ε ((c t).money / cpiAt E Q t) - E.κ / 2 * (c t).y ^ 2) := by
    funext η; simp only [periodU, g]; ring
  have hd1 : HasDerivAt (fun η => (c t).cT - ρ * η) (-ρ) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul ρ).const_sub (c t).cT
  have hd2 : HasDerivAt (fun η => (c t).cN + η) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_add (c t).cN
  have hd : HasDerivAt (fun η => periodU E Q t (g η))
      (E.γ * (-ρ / (c t).cT) + (1 - E.γ) * (1 / (c t).cN)) 0 := by
    rw [hfun]
    have e1 := (hd1.log (by simpa using ha.ne')).const_mul E.γ
    have e2 := (hd2.log (by simpa using hb.ne')).const_mul (1 - E.γ)
    simp only [mul_zero, sub_zero, add_zero] at e1 e2
    exact (e1.add e2).add_const _
  have h0 := hmax.hasDerivAt_eq_zero hd
  field_simp at h0 ⊢
  linarith

/-- NECESSITY of the money condition behind (88), p. 691, at a household optimum. -/
theorem moneyFOC_of_optimal {E : Economy} {Q : Prices} (hE : E.Valid) (hQ : Q.Valid E.r)
    {B0 Mm1 : ℝ} {c : ℕ → Choice} (hopt : HouseholdOptimal E Q B0 Mm1 c) : MoneyFOC E Q c := by
  obtain ⟨hβ, _, hr, hγ0, hγ1, _, _, _, _, _⟩ := hE
  intro t
  obtain ⟨ha, hb, hn, hq⟩ := hopt.1 t
  obtain ⟨hT, hPN, _, _⟩ := hQ t
  have hP : 0 < cpiAt E Q t := cpi_pos hγ0 hγ1 hT hPN
  set ι := userCost E.r Q t
  set P := cpiAt E Q t
  set g : ℝ → Choice := fun η =>
    ⟨(c t).cT - ι * η, (c t).cN, (c t).money + η, (c t).y⟩ with hg
  have hg0 : g 0 = c t := by simp [g]
  have hgpos : ∀ᶠ η in 𝓝 0, g η ∈ posChoice := by
    have h1 : ∀ᶠ η in 𝓝 (0 : ℝ), 0 < (c t).cT - ι * η :=
      (continuous_const.sub (continuous_const.mul continuous_id)).continuousAt.eventually
        (lt_mem_nhds (by simpa using ha))
    have h2 : ∀ᶠ η in 𝓝 (0 : ℝ), 0 < (c t).money + η :=
      (continuous_const.add continuous_id).continuousAt.eventually
        (lt_mem_nhds (by simpa using hn))
    filter_upwards [h1, h2] with η e1 e2
    exact ⟨e1, hb, e2, hq⟩
  have hgres : ∀ η, netRes E Q t (c t) ≤ netRes E Q t (g η) := by
    intro η; simp only [netRes, g]; linarith
  have hmax := isLocalMax_of_perturb hr hβ hopt t g hg0 hgpos hgres
  have hfun : (fun η => periodU E Q t (g η)) = fun η =>
      E.γ * log ((c t).cT - ι * η) + moneyU E.χ E.ε (((c t).money + η) / P)
        + ((1 - E.γ) * log (c t).cN - E.κ / 2 * (c t).y ^ 2) := by
    funext η; simp only [periodU, g]; ring
  have hd1 : HasDerivAt (fun η => (c t).cT - ι * η) (-ι) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul ι).const_sub (c t).cT
  have hd2 : HasDerivAt (fun η => ((c t).money + η) / P) (1 / P) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_add (c t).money).div_const P
  have hm : HasDerivAt (fun η => moneyU E.χ E.ε (((c t).money + η) / P))
      (E.χ * ((c t).money / P) ^ (-E.ε) * (1 / P)) 0 := by
    have := (hasDerivAt_moneyU E.χ E.ε (z := ((c t).money + 0) / P)
      (by simpa using div_pos hn hP)).comp (0 : ℝ) hd2
    convert this using 1 <;> first | rfl | simp
  have hd : HasDerivAt (fun η => periodU E Q t (g η))
      (E.γ * (-ι / (c t).cT) + E.χ * ((c t).money / P) ^ (-E.ε) * (1 / P)) 0 := by
    rw [hfun]
    have e1 := (hd1.log (by simpa using ha.ne')).const_mul E.γ
    simp only [mul_zero, sub_zero] at e1
    exact (e1.add hm).add_const _
  have h0 := hmax.hasDerivAt_eq_zero hd
  have : E.χ * ((c t).money / P) ^ (-E.ε) / P = E.γ / (c t).cT * ι := by
    field_simp at h0 ⊢; linarith
  exact this

/-- NECESSITY of the output condition behind (90), p. 691, at a household optimum. -/
theorem labourFOC_of_optimal {E : Economy} {Q : Prices} (hE : E.Valid)
    {B0 Mm1 : ℝ} {c : ℕ → Choice} (hopt : HouseholdOptimal E Q B0 Mm1 c) : LabourFOC E Q c := by
  obtain ⟨hβ, _, hr, hγ0, hγ1, _, _, _, hθ, _⟩ := hE
  intro t
  obtain ⟨ha, hb, hn, hq⟩ := hopt.1 t
  set R := realRevenue E Q t
  set s := (E.θ - 1) / E.θ
  set K := Q.CA t ^ (1 / E.θ)
  set ρ := relPrice Q t
  have hRd : HasDerivAt R (ρ * (s * (c t).y ^ (s - 1) * K)) (c t).y := by
    have := ((hasDerivAt_rpow_const (p := s) (Or.inl hq.ne')).mul_const K).const_mul ρ
    exact this
  set g : ℝ → Choice := fun η =>
    ⟨(c t).cT + (R ((c t).y + η) - R (c t).y), (c t).cN, (c t).money, (c t).y + η⟩ with hg
  have hg0 : g 0 = c t := by simp [g]
  have hRc : HasDerivAt (fun η => R ((c t).y + η)) (ρ * (s * (c t).y ^ (s - 1) * K)) 0 := by
    have hR0 : HasDerivAt R (ρ * (s * (c t).y ^ (s - 1) * K)) ((c t).y + 0) := by
      simpa using hRd
    have := hR0.comp (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).const_add (c t).y)
    convert this using 1 <;> first | rfl | simp
  have hd1 : HasDerivAt (fun η => (c t).cT + (R ((c t).y + η) - R (c t).y))
      (ρ * (s * (c t).y ^ (s - 1) * K)) 0 := by
    simpa using (hRc.sub_const (R (c t).y)).const_add (c t).cT
  have hgpos : ∀ᶠ η in 𝓝 0, g η ∈ posChoice := by
    have h1 : ∀ᶠ η in 𝓝 (0 : ℝ), 0 < (c t).cT + (R ((c t).y + η) - R (c t).y) :=
      hd1.continuousAt.eventually (lt_mem_nhds (by simpa using ha))
    have h2 : ∀ᶠ η in 𝓝 (0 : ℝ), 0 < (c t).y + η :=
      (continuous_const.add continuous_id).continuousAt.eventually
        (lt_mem_nhds (by simpa using hq))
    filter_upwards [h1, h2] with η e1 e2
    exact ⟨e1, hb, hn, e2⟩
  have hgres : ∀ η, netRes E Q t (c t) ≤ netRes E Q t (g η) := by
    intro η; simp only [netRes, g, R]; linarith
  have hmax := isLocalMax_of_perturb hr hβ hopt t g hg0 hgpos hgres
  have hfun : (fun η => periodU E Q t (g η)) = fun η =>
      E.γ * log ((c t).cT + (R ((c t).y + η) - R (c t).y)) - E.κ / 2 * ((c t).y + η) ^ 2
        + ((1 - E.γ) * log (c t).cN + moneyU E.χ E.ε ((c t).money / cpiAt E Q t)) := by
    funext η; simp only [periodU, g]; ring
  have hsq : HasDerivAt (fun η => ((c t).y + η) ^ 2) (2 * (c t).y) 0 := by
    have := (hasDerivAt_pow 2 ((c t).y + 0)).comp (0 : ℝ)
      ((hasDerivAt_id (0 : ℝ)).const_add (c t).y)
    convert this using 1 <;> first | rfl | simp
  have hd : HasDerivAt (fun η => periodU E Q t (g η))
      (E.γ * (ρ * (s * (c t).y ^ (s - 1) * K) / (c t).cT) - E.κ / 2 * (2 * (c t).y)) 0 := by
    rw [hfun]
    have e1 := (hd1.log (by simpa using ha.ne')).const_mul E.γ
    simp only [sub_self, add_zero] at e1
    exact ((e1.sub (hsq.const_mul (E.κ / 2)))).add_const _
  have h0 := hmax.hasDerivAt_eq_zero hd
  have : E.κ * (c t).y = E.γ / (c t).cT * ρ * (s * ((c t).y ^ (s - 1) * K)) := by
    field_simp at h0 ⊢; linarith
  exact this

/-- NECESSITY of the Euler equation (87), p. 691, at a household optimum (two-date
perturbation shifting tradables consumption from `t+1` to `t`). -/
theorem eulerFOC_of_optimal {E : Economy} {Q : Prices} (hE : E.Valid)
    {B0 Mm1 : ℝ} {c : ℕ → Choice} (hopt : HouseholdOptimal E Q B0 Mm1 c) : EulerFOC E c := by
  obtain ⟨hβ, _, hr, hγ0, _, _, _, _, _, _⟩ := hE
  intro t
  have ha := (hopt.1 t).1
  have ha' := (hopt.1 (t + 1)).1
  have htt : t + 1 ≠ t := Nat.succ_ne_self t
  set x' : ℝ → ℕ → Choice := fun η s =>
    if s = t then ⟨(c t).cT + η, (c t).cN, (c t).money, (c t).y⟩
    else if s = t + 1 then
      ⟨(c (t + 1)).cT - (1 + E.r) * η, (c (t + 1)).cN, (c (t + 1)).money, (c (t + 1)).y⟩
    else c s with hx'
  set f : ℝ → ℝ := fun η => E.β ^ t * (E.γ * log ((c t).cT + η))
    + E.β ^ (t + 1) * (E.γ * log ((c (t + 1)).cT - (1 + E.r) * η)) with hf
  have hloc : IsLocalMax f 0 := by
    have h1 : ∀ᶠ η in 𝓝 (0 : ℝ), 0 < (c t).cT + η :=
      (continuous_const.add continuous_id).continuousAt.eventually
        (lt_mem_nhds (by simpa using ha))
    have h2 : ∀ᶠ η in 𝓝 (0 : ℝ), 0 < (c (t + 1)).cT - (1 + E.r) * η :=
      (continuous_const.sub (continuous_const.mul continuous_id)).continuousAt.eventually
        (lt_mem_nhds (by simpa using ha'))
    filter_upwards [h1, h2] with η e1 e2
    have hS : ∀ s ∉ ({t, t + 1} : Finset ℕ), x' η s = c s := by
      intro s hs
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hs
      simp [x', hs.1, hs.2]
    have hadm : ∀ s, x' η s ∈ posChoice := by
      intro s
      by_cases hs1 : s = t
      · subst hs1; simp only [x', ↓reduceIte]
        exact ⟨e1, (hopt.1 s).2.1, (hopt.1 s).2.2.1, (hopt.1 s).2.2.2⟩
      by_cases hs2 : s = t + 1
      · subst hs2; simp only [x', htt, ↓reduceIte]
        exact ⟨e2, (hopt.1 (t + 1)).2.1, (hopt.1 (t + 1)).2.2.1, (hopt.1 (t + 1)).2.2.2⟩
      rw [hS s (by simp [hs1, hs2])]; exact hopt.1 s
    have hpv : 0 ≤ ∑ s ∈ ({t, t + 1} : Finset ℕ),
        disc E.r s * (netRes E Q s (x' η s) - netRes E Q s (c s)) := by
      rw [Finset.sum_pair htt.symm]
      simp only [x', htt, ↓reduceIte, netRes]
      have := disc_succ_mul hr t
      nlinarith
    have h := perturb_utility_le_of_pv hr hopt hadm hS hpv
    rw [Finset.sum_pair htt.symm] at h
    simp only [x', htt, ↓reduceIte, periodU] at h
    simp only [hf, add_zero, mul_zero, sub_zero]
    linarith
  have hd1 : HasDerivAt (fun η => (c t).cT + η) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_add (c t).cT
  have hd2 : HasDerivAt (fun η => (c (t + 1)).cT - (1 + E.r) * η) (-(1 + E.r)) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul (1 + E.r)).const_sub (c (t + 1)).cT
  have hd : HasDerivAt f (E.β ^ t * (E.γ * (1 / (c t).cT))
      + E.β ^ (t + 1) * (E.γ * (-(1 + E.r) / (c (t + 1)).cT))) 0 := by
    have e1 := ((hd1.log (by simpa using ha.ne')).const_mul E.γ).const_mul (E.β ^ t)
    have e2 := ((hd2.log (by simpa using ha'.ne')).const_mul E.γ).const_mul (E.β ^ (t + 1))
    simp only [add_zero, mul_zero, sub_zero] at e1 e2
    exact e1.add e2
  have h0 := hloc.hasDerivAt_eq_zero hd
  have hβt : 0 < E.β ^ t := pow_pos hβ t
  rw [pow_succ] at h0
  have : E.γ / (c t).cT = E.β * (1 + E.r) * (E.γ / (c (t + 1)).cT) := by
    have h3 : E.β ^ t * (E.γ / (c t).cT - E.β * (1 + E.r) * (E.γ / (c (t + 1)).cT)) = 0 := by
      rw [← h0]; field_simp; ring
    have := (mul_eq_zero.mp h3).resolve_left hβt.ne'
    linarith
  exact this

/-- NECESSITY of the transversality condition (liminf form) at a household optimum (O&R (16)
for the §10.2 problem): raising date-0 tradables consumption is always feasible. -/
theorem liminfNonpos_of_householdOptimal {E : Economy} {Q : Prices} (hE : E.Valid)
    {B0 Mm1 : ℝ} {c : ℕ → Choice} (hopt : HouseholdOptimal E Q B0 Mm1 c) :
    LiminfNonpos E.r (wealth E.r (initWealth E Q B0 Mm1) (netRes E Q) c) := by
  obtain ⟨_, _, hr, hγ0, _, _, _, _, _, _⟩ := hE
  refine liminfNonpos_of_isOptimal hr hopt ?_
  intro η hη
  obtain ⟨ha, hb, hn, hq⟩ := hopt.1 0
  refine ⟨⟨(c 0).cT + η, (c 0).cN, (c 0).money, (c 0).y⟩, ⟨by linarith, hb, hn, hq⟩, ?_, ?_⟩
  · simp only [netRes]; linarith
  · simp only [periodU]
    have := log_lt_log ha (by linarith : (c 0).cT < (c 0).cT + η)
    nlinarith

/-- MAIN THEOREM (O&R §10.2.2, (87)–(90)): an admissible plan is a household optimum IF AND ONLY
IF its utility is summable, it satisfies the first-order conditions (87)–(90), the no-Ponzi
condition and the transversality condition `liminf (1+r)^{−T} A_T ≤ 0`. -/
theorem householdOptimal_iff {E : Economy} {Q : Prices} (hE : E.Valid) (hQ : Q.Valid E.r)
    {B0 Mm1 : ℝ} {c : ℕ → Choice} :
    HouseholdOptimal E Q B0 Mm1 c ↔
      (∀ t, c t ∈ posChoice) ∧ Summable (fun t => E.β ^ t * periodU E Q t (c t)) ∧
      EulerFOC E c ∧ IntraFOC E Q c ∧ MoneyFOC E Q c ∧ LabourFOC E Q c ∧
      NoPonzi E.r (wealth E.r (initWealth E Q B0 Mm1) (netRes E Q) c) ∧
      LiminfNonpos E.r (wealth E.r (initWealth E Q B0 Mm1) (netRes E Q) c) := by
  constructor
  · intro h
    exact ⟨h.1, h.2.2.1, eulerFOC_of_optimal hE h, intraFOC_of_optimal hE h,
      moneyFOC_of_optimal hE hQ h, labourFOC_of_optimal hE h, h.2.1,
      liminfNonpos_of_householdOptimal hE h⟩
  · rintro ⟨hc, hs, he, hn, hm, hl, hnp, htv⟩
    exact householdOptimal_of_foc hE hQ hc hs he hn hm hl hnp htv


/-! ## The book's forms of (88), (90), (92) -/

/-- (88), p. 691, from the money condition and the Euler equation:
`γ/C_{T,t} = χ (P_{T,t}/P_t)(M_t/P_t)^{−ε} + β (P_{T,t}/P_{T,t+1}) γ/C_{T,t+1}`. -/
theorem money_88 {E : Economy} {Q : Prices} (hE : E.Valid) (hQ : Q.Valid E.r)
    {c : ℕ → Choice} (hc : ∀ t, c t ∈ posChoice) (heu : EulerFOC E c) (hM : MoneyFOC E Q c)
    (t : ℕ) :
    E.γ / (c t).cT = E.χ * (Q.PT t / cpiAt E Q t) * ((c t).money / cpiAt E Q t) ^ (-E.ε)
      + E.β * (Q.PT t / Q.PT (t + 1)) * (E.γ / (c (t + 1)).cT) := by
  obtain ⟨_, _, hr, hγ0, hγ1, _, _, _, _, _⟩ := hE
  obtain ⟨hT, hN, _, _⟩ := hQ t
  have hT1 := (hQ (t + 1)).1
  have hP : 0 < cpiAt E Q t := cpi_pos hγ0 hγ1 hT hN
  have h1 := hM t
  have h2 := heu t
  have ha := (hc t).1
  have ha1 := (hc (t + 1)).1
  unfold userCost at h1
  have e : E.χ * (Q.PT t / cpiAt E Q t) * ((c t).money / cpiAt E Q t) ^ (-E.ε)
      = Q.PT t * (E.χ * ((c t).money / cpiAt E Q t) ^ (-E.ε) / cpiAt E Q t) := by
    field_simp
  rw [e, h1]
  have e2 : E.β * (Q.PT t / Q.PT (t + 1)) * (E.γ / (c (t + 1)).cT)
      = E.γ / (c t).cT * (Q.PT t / ((1 + E.r) * Q.PT (t + 1))) := by
    rw [h2]; field_simp
  rw [e2]; field_simp; ring

/-- (90), p. 691, from the intratemporal and output conditions:
`y_N^{(θ+1)/θ} = ((θ−1)(1−γ)/(κθ)) (C^A_N)^{1/θ} / C_N`. -/
theorem labour_90 {E : Economy} {Q : Prices} (hE : E.Valid)
    {c : ℕ → Choice} (hc : ∀ t, c t ∈ posChoice) (hN : IntraFOC E Q c) (hL : LabourFOC E Q c)
    (t : ℕ) :
    (c t).y ^ ((E.θ + 1) / E.θ)
      = (E.θ - 1) * (1 - E.γ) / (E.κ * E.θ) * Q.CA t ^ (1 / E.θ) / (c t).cN := by
  obtain ⟨_, _, _, _, _, _, _, hκ, hθ, _⟩ := hE
  obtain ⟨_, hb, _, hq⟩ := hc t
  have hθ0 : 0 < E.θ := by linarith
  have h1 := hL t
  rw [← mul_assoc, ← hN t] at h1
  have e1 : (c t).y ^ ((E.θ + 1) / E.θ) = (c t).y * (c t).y ^ (1 / E.θ) := by
    rw [show (E.θ + 1) / E.θ = 1 + 1 / E.θ by field_simp, rpow_add hq, rpow_one]
  have e2 : (c t).y ^ ((E.θ - 1) / E.θ - 1) = ((c t).y ^ (1 / E.θ))⁻¹ := by
    rw [show (E.θ - 1) / E.θ - 1 = -(1 / E.θ) by field_simp; ring, rpow_neg hq.le]
  rw [e2] at h1
  have hy1 : 0 < (c t).y ^ (1 / E.θ) := rpow_pos_of_pos hq _
  rw [e1]
  field_simp at h1 ⊢
  linarith

/-- (92), p. 692: with `β(1+r) = 1`, money demand is
`M/P = [(χ/γ) (C_T P_T/P) / (1 − β P_{T,t}/P_{T,t+1})]^{1/ε}`. -/
theorem money_92 {E : Economy} {Q : Prices} (hE : E.Valid) (hβr : E.β * (1 + E.r) = 1)
    (hQ : Q.Valid E.r) {c : ℕ → Choice} (hc : ∀ t, c t ∈ posChoice) (hM : MoneyFOC E Q c)
    (t : ℕ) :
    (c t).money / cpiAt E Q t
      = (E.χ / E.γ * ((c t).cT * Q.PT t / cpiAt E Q t)
          / (1 - E.β * (Q.PT t / Q.PT (t + 1)))) ^ (1 / E.ε) := by
  obtain ⟨hβ, _, hr, hγ0, hγ1, hχ, hε, _, _, _⟩ := hE
  obtain ⟨hT, hN, _, hu⟩ := hQ t
  have hT1 := (hQ (t + 1)).1
  have hP : 0 < cpiAt E Q t := cpi_pos hγ0 hγ1 hT hN
  obtain ⟨ha, _, hn, _⟩ := hc t
  have hm : 0 < (c t).money / cpiAt E Q t := div_pos hn hP
  have hucost : userCost E.r Q t = (1 - E.β * (Q.PT t / Q.PT (t + 1))) / Q.PT t := by
    unfold userCost
    have : 1 / ((1 + E.r) * Q.PT (t + 1)) = E.β / Q.PT (t + 1) := by
      field_simp; linarith
    rw [this]; field_simp
  have hw : 0 < 1 - E.β * (Q.PT t / Q.PT (t + 1)) := by
    have := hu; rw [hucost] at this
    exact (div_pos_iff_of_pos_right hT).mp this
  have h1 := hM t
  rw [hucost] at h1
  set m := (c t).money / cpiAt E Q t
  set w := 1 - E.β * (Q.PT t / Q.PT (t + 1))
  have hA : m ^ (-E.ε) = E.γ / E.χ * (cpiAt E Q t / ((c t).cT * Q.PT t)) * w := by
    field_simp at h1 ⊢; linarith
  have key : m = (m ^ (-E.ε)) ^ (-(1 / E.ε)) := by
    rw [← rpow_mul hm.le, show -E.ε * -(1 / E.ε) = 1 by field_simp, rpow_one]
  rw [key, hA, rpow_neg (by positivity), ← inv_rpow (by positivity)]
  congr 1
  field_simp

/-! ## Equilibrium -/

/-- A symmetric flexible-price equilibrium given the money supply `M` (O&R §10.2.2–10.2.3):
households optimise, every producer sells `y_N = C_N = C^A_N` (symmetry, so `p_N = P_N`), the
money market clears, and seignorage is rebated (85). -/
def IsEquilibrium (E : Economy) (Q : Prices) (B0 Mm1 : ℝ) (M : ℕ → ℝ) (c : ℕ → Choice) :
    Prop :=
  HouseholdOptimal E Q B0 Mm1 c ∧ (∀ t, (c t).y = (c t).cN ∧ Q.CA t = (c t).cN) ∧
    (∀ t, (c t).money = M t) ∧ ∀ t, Q.τ t = -(M t - moneyPrev Mm1 c t) / Q.PT t

/-- Symmetry: when a producer sells `y = C^A_N`, its price equals the index, `p_N = P_N`
(O&R p. 692). -/
theorem invDemand_self (E : Economy) (Q : Prices) (t : ℕ) (hA : 0 < Q.CA t) :
    invDemand E Q t (Q.CA t) = Q.PN t := by
  simp [invDemand, div_self hA.ne']

/-- Net foreign bonds implied by wealth: `B_t = (A_t − M_{t−1}/P_{T,t})/(1+r)` (O&R (84)). -/
noncomputable def bonds (E : Economy) (Q : Prices) (B0 Mm1 : ℝ) (c : ℕ → Choice) (t : ℕ) :
    ℝ :=
  (wealth E.r (initWealth E Q B0 Mm1) (netRes E Q) c t - moneyPrev Mm1 c t / Q.PT t) / (1 + E.r)

/-- The discounted real value of money held into date `T`, `(1+r)^{−T} M_{T−1}/P_{T,T}`; the
book's no-speculative-bubble condition (p. 692) makes it vanish. -/
noncomputable def moneyBubble (E : Economy) (Q : Prices) (Mm1 : ℝ) (c : ℕ → Choice) (T : ℕ) :
    ℝ :=
  disc E.r T * (moneyPrev Mm1 c T / Q.PT T)

/-- In equilibrium, revenue equals the value of nontradables consumption:
`(P_N/P_T) C_N^{(θ−1)/θ} C_N^{1/θ} = (P_N/P_T) C_N` (O&R p. 692). -/
theorem realRevenue_symm (E : Economy) (Q : Prices) (t : ℕ) (hθ : 0 < E.θ) {x : ℝ}
    (hx : 0 < x) (hA : Q.CA t = x) : realRevenue E Q t x = relPrice Q t * x := by
  unfold realRevenue
  rw [hA, ← rpow_add hx, show (E.θ - 1) / E.θ + 1 / E.θ = 1 by field_simp; ring, rpow_one]

/-- The tradables current account in equilibrium (O&R (84)+(85), p. 691–692):
`B_0` as given and `B_{t+1} = (1+r)B_t + ȳ_T − C_{T,t}`: money and seignorage cancel. -/
theorem bonds_recursion {E : Economy} {Q : Prices} (hE : E.Valid) (hQ : Q.Valid E.r)
    {B0 Mm1 : ℝ} {M : ℕ → ℝ} {c : ℕ → Choice} (heq : IsEquilibrium E Q B0 Mm1 M c) :
    bonds E Q B0 Mm1 c 0 = B0 ∧
      ∀ t, bonds E Q B0 Mm1 c (t + 1) = (1 + E.r) * bonds E Q B0 Mm1 c t + E.yT - (c t).cT := by
  obtain ⟨hopt, hsym, hmon, htax⟩ := heq
  obtain ⟨_, _, hr, _, _, _, _, _, hθ, _⟩ := hE
  refine ⟨?_, ?_⟩
  · simp only [bonds, wealth, initWealth, moneyPrev]; field_simp; ring
  · intro t
    obtain ⟨hT, _, _, _⟩ := hQ t
    have hT1 := (hQ (t + 1)).1
    have hcN := (hopt.1 t).2.1
    have hrev := realRevenue_symm E Q t (by linarith) hcN (hsym t).2
    simp only [bonds, wealth, netRes, userCost]
    rw [show moneyPrev Mm1 c (t + 1) = (c t).money from rfl, (hsym t).1, hrev, htax t, hmon t]
    field_simp
    ring

/-- With `β(1+r) = 1`, the Euler equation makes tradables consumption constant, (87). -/
theorem cT_const {E : Economy} {c : ℕ → Choice} (hγ : 0 < E.γ) (hβr : E.β * (1 + E.r) = 1)
    (hc : ∀ t, c t ∈ posChoice) (heu : EulerFOC E c) (t : ℕ) : (c t).cT = (c 0).cT := by
  induction t with
  | zero => rfl
  | succ t ih =>
    have h := heu t
    rw [hβr, one_mul] at h
    have ha := (hc t).1
    have ha1 := (hc (t + 1)).1
    field_simp at h
    rw [← ih]; linarith

/-- Bonds in closed form when `B_0 = 0` and `C_T ≡ c`:
`(1+r)^{−T}(1+r)B_T = (1+r)(ȳ_T − c)(1 − (1+r)^{−T})/r` (O&R p. 692). -/
theorem disc_bonds_closed {E : Economy} {Q : Prices} {B0 Mm1 : ℝ} {c : ℕ → Choice}
    (hr0 : 0 < E.r) (hB : bonds E Q B0 Mm1 c 0 = 0)
    (hrec : ∀ t, bonds E Q B0 Mm1 c (t + 1) = (1 + E.r) * bonds E Q B0 Mm1 c t + E.yT - (c t).cT)
    (hconst : ∀ t, (c t).cT = (c 0).cT) (T : ℕ) :
    disc E.r T * ((1 + E.r) * bonds E Q B0 Mm1 c T)
      = (1 + E.r) * (E.yT - (c 0).cT) * (1 - disc E.r T) / E.r := by
  have hr : 0 < 1 + E.r := by linarith
  induction T with
  | zero => simp [disc, hB]
  | succ T ih =>
    rw [hrec T, hconst T]
    have hd := disc_succ_mul hr T
    have e : disc E.r (T + 1) = disc E.r T / (1 + E.r) := by
      rw [← hd]; field_simp
    rw [e]
    field_simp
    field_simp at ih
    linear_combination (1 + E.r) * ih

/-- The discount factor vanishes: `(1+r)^{−T} → 0` for `r > 0`. -/
theorem tendsto_disc {r : ℝ} (hr0 : 0 < r) : Tendsto (disc r) atTop (𝓝 0) := by
  have h1 : (1 + r)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by linarith)
  have h0 : 0 ≤ (1 + r)⁻¹ := by positivity
  have e : disc r = fun n => ((1 + r)⁻¹) ^ n := by funext n; simp [disc, inv_pow]
  rw [e]; exact tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1

/-- A convergent sequence that is frequently below `c` has limit at most `c`. -/
theorem ge_of_tendsto_of_frequently {s : ℕ → ℝ} {L c : ℝ} (hs : Tendsto s atTop (𝓝 L))
    (hc : ∃ᶠ T in atTop, s T ≤ c) : L ≤ c := by
  have := le_of_tendsto_of_frequently (s := fun T => -s T) (L := -L) (c := -c) hs.neg
    (hc.mono fun T h => by linarith)
  linarith

/-- The pieces of discounted wealth in equilibrium: bonds plus the money term (O&R (16)). -/
theorem disc_wealth_split {E : Economy} {Q : Prices} (hr : 0 < 1 + E.r) (B0 Mm1 : ℝ)
    (c : ℕ → Choice) (T : ℕ) :
    disc E.r T * wealth E.r (initWealth E Q B0 Mm1) (netRes E Q) c T
      = disc E.r T * ((1 + E.r) * bonds E Q B0 Mm1 c T) + moneyBubble E Q Mm1 c T := by
  simp only [bonds, moneyBubble]; field_simp; ring

/-- (91), p. 692, FIRST HALF: in any equilibrium with `β(1+r) = 1` and `B_0 = 0`, tradables
consumption is constant and AT LEAST the endowment (the transversality condition rules out
over-saving), for ANY money path. -/
theorem cT_ge_endowment {E : Economy} {Q : Prices} (hE : E.Valid) (hβr : E.β * (1 + E.r) = 1)
    (hQ : Q.Valid E.r) {Mm1 : ℝ} {M : ℕ → ℝ} {c : ℕ → Choice}
    (heq : IsEquilibrium E Q 0 Mm1 M c) (hMm1 : 0 < Mm1) :
    (∀ t, (c t).cT = (c 0).cT) ∧ E.yT ≤ (c 0).cT := by
  have hE' := hE
  obtain ⟨hβ, hβ1, hr, hγ0, _, _, _, _, _, _⟩ := hE'
  have hr0 : 0 < E.r := by nlinarith
  have hopt := heq.1
  have hconst := cT_const hγ0 hβr hopt.1 (eulerFOC_of_optimal hE hopt)
  refine ⟨hconst, ?_⟩
  obtain ⟨hB0, hrec⟩ := bonds_recursion hE hQ heq
  have hcl := disc_bonds_closed hr0 hB0 hrec hconst
  have hlim : Tendsto (fun T => disc E.r T * ((1 + E.r) * bonds E Q 0 Mm1 c T)) atTop
      (𝓝 ((1 + E.r) * (E.yT - (c 0).cT) * (1 - 0) / E.r)) := by
    simp_rw [hcl]
    exact ((tendsto_const_nhds.sub (tendsto_disc hr0)).const_mul _).div_const _
  have hMB : ∀ T, 0 ≤ moneyBubble E Q Mm1 c T := by
    intro T
    unfold moneyBubble
    refine mul_nonneg (disc_pos hr T).le (div_nonneg ?_ (hQ T).1.le)
    cases T with
    | zero => exact hMm1.le
    | succ T => exact (hopt.1 T).2.2.1.le
  have htv := liminfNonpos_of_householdOptimal hE hopt
  have hle : ∀ δ > 0, (1 + E.r) * (E.yT - (c 0).cT) * (1 - 0) / E.r ≤ δ := by
    intro δ hδ
    apply ge_of_tendsto_of_frequently hlim
    refine (htv δ hδ).mono fun T hT => ?_
    rw [disc_wealth_split hr] at hT
    linarith [hMB T]
  have h0 : (1 + E.r) * (E.yT - (c 0).cT) * (1 - 0) / E.r ≤ 0 :=
    le_of_forall_pos_le_add fun δ hδ => by linarith [hle δ hδ]
  rw [sub_zero, mul_one, div_nonpos_iff] at h0
  rcases h0 with ⟨_, h⟩ | ⟨h, _⟩
  · linarith
  · nlinarith

/-- (91), p. 692, EXACT FORM: in any equilibrium with `β(1+r) = 1` and `B_0 = 0`, for ANY money
path, `C_T = ȳ_T` IF AND ONLY IF the discounted real value of money has liminf zero (no
speculative bubble in money). -/
theorem cT_eq_endowment_iff {E : Economy} {Q : Prices} (hE : E.Valid) (hβr : E.β * (1 + E.r) = 1)
    (hQ : Q.Valid E.r) {Mm1 : ℝ} {M : ℕ → ℝ} {c : ℕ → Choice}
    (heq : IsEquilibrium E Q 0 Mm1 M c) (hMm1 : 0 < Mm1) :
    (c 0).cT = E.yT ↔ ∀ δ > 0, ∃ᶠ T in atTop, moneyBubble E Q Mm1 c T ≤ δ := by
  have hE' := hE
  obtain ⟨hβ, hβ1, hr, hγ0, _, _, _, _, _, _⟩ := hE'
  have hr0 : 0 < E.r := by nlinarith
  have hopt := heq.1
  obtain ⟨hconst, hge⟩ := cT_ge_endowment hE hβr hQ heq hMm1
  obtain ⟨hB0, hrec⟩ := bonds_recursion hE hQ heq
  have hcl := disc_bonds_closed hr0 hB0 hrec hconst
  constructor
  · intro hc δ hδ
    have htv := liminfNonpos_of_householdOptimal hE hopt
    refine (htv δ hδ).mono fun T hT => ?_
    rw [disc_wealth_split hr, hcl, hc, sub_self] at hT
    simpa using hT
  · intro hMB
    set L := (1 + E.r) * (E.yT - (c 0).cT) / E.r
    have hlim : Tendsto (fun T => disc E.r T * ((1 + E.r) * bonds E Q 0 Mm1 c T)) atTop
        (𝓝 (L * (1 - 0))) := by
      simp_rw [hcl]
      have := ((tendsto_const_nhds (x := (1 : ℝ))).sub (tendsto_disc hr0)).const_mul L
      refine this.congr fun T => ?_
      simp only [L]; ring
    rw [sub_zero, mul_one] at hlim
    have hge' : ∀ δ > 0, -(3 * δ) ≤ L := by
      intro δ hδ
      have hev : ∀ᶠ T in atTop, disc E.r T * ((1 + E.r) * bonds E Q 0 Mm1 c T) < L + δ :=
        hlim.eventually (gt_mem_nhds (by linarith))
      obtain ⟨T, ⟨h1, h2⟩, h3⟩ := (((hMB δ hδ).and_eventually (hopt.2.1 δ hδ)).and_eventually
        hev).exists
      rw [disc_wealth_split hr] at h2
      linarith
    have hL : 0 ≤ L := le_of_forall_pos_le_add fun δ hδ => by
      have := hge' (δ / 3) (by positivity); linarith
    have : (c 0).cT ≤ E.yT := by
      have := div_nonneg_iff.mp hL
      rcases this with ⟨h, _⟩ | ⟨_, h⟩
      · nlinarith
      · linarith
    linarith

/-- (91), p. 692, under the book's no-speculative-bubble condition `(1+r)^{−T} M_{T−1}/P_{T,T} → 0`:
`C_{T,t} = ȳ_T` and `B_t = 0` for all `t` — a balanced current account for ANY money path. -/
theorem balanced_current_account {E : Economy} {Q : Prices} (hE : E.Valid)
    (hβr : E.β * (1 + E.r) = 1) (hQ : Q.Valid E.r) {Mm1 : ℝ} {M : ℕ → ℝ} {c : ℕ → Choice}
    (heq : IsEquilibrium E Q 0 Mm1 M c) (hMm1 : 0 < Mm1)
    (hnb : Tendsto (moneyBubble E Q Mm1 c) atTop (𝓝 0)) :
    ∀ t, (c t).cT = E.yT ∧ bonds E Q 0 Mm1 c t = 0 := by
  obtain ⟨hconst, _⟩ := cT_ge_endowment hE hβr hQ heq hMm1
  have hc0 : (c 0).cT = E.yT := by
    rw [cT_eq_endowment_iff hE hβr hQ heq hMm1]
    intro δ hδ
    exact (hnb.eventually (gt_mem_nhds hδ)).frequently.mono fun _ h => h.le
  obtain ⟨hB0, hrec⟩ := bonds_recursion hE hQ heq
  intro t
  refine ⟨(hconst t).trans hc0, ?_⟩
  induction t with
  | zero => exact hB0
  | succ t ih => rw [hrec t, ih, hconst t, hc0]; ring


/-! ## Steady state (93) and the initial price level -/

/-- Steady-state nontradables output (93), p. 692: `ȳ_N = [(θ−1)(1−γ)/(κθ)]^{1/2}`. -/
noncomputable def ybarN (E : Economy) : ℝ := sqrt ((E.θ - 1) * (1 - E.γ) / (E.κ * E.θ))

/-- `ȳ_N > 0` (O&R (93)). -/
theorem ybarN_pos {E : Economy} (hE : E.Valid) : 0 < ybarN E := by
  obtain ⟨_, _, _, _, hγ1, _, _, hκ, hθ, _⟩ := hE
  unfold ybarN
  apply sqrt_pos.mpr
  apply div_pos (mul_pos (by linarith) (by linarith)) (mul_pos hκ (by linarith))

/-- `κ ȳ_N² = (θ−1)(1−γ)/θ` (O&R (93)). -/
theorem kappa_mul_ybarN_sq {E : Economy} (hE : E.Valid) :
    E.κ * ybarN E ^ 2 = (E.θ - 1) * (1 - E.γ) / E.θ := by
  obtain ⟨_, _, _, _, hγ1, _, _, hκ, hθ, _⟩ := hE
  unfold ybarN
  rw [sq_sqrt (div_nonneg (mul_nonneg (by linarith) (by linarith))
    (mul_nonneg hκ.le (by linarith)))]
  field_simp

/-- (93), p. 692: in ANY symmetric equilibrium, nontradables output and consumption equal `ȳ_N`
at every date (the unique positive solution of (90) with `y_N = C_N = C^A_N`). -/
theorem output_93 {E : Economy} {Q : Prices} (hE : E.Valid) {B0 Mm1 : ℝ} {M : ℕ → ℝ}
    {c : ℕ → Choice} (heq : IsEquilibrium E Q B0 Mm1 M c) (t : ℕ) :
    (c t).y = ybarN E ∧ (c t).cN = ybarN E := by
  have hE' := hE
  obtain ⟨_, _, _, _, hγ1, _, _, hκ, hθ, _⟩ := hE'
  obtain ⟨hopt, hsym, _, _⟩ := heq
  have hc := hopt.1
  have h90 := labour_90 hE hc (intraFOC_of_optimal hE hopt) (labourFOC_of_optimal hE hopt) t
  obtain ⟨hy, hA⟩ := hsym t
  rw [hA, ← hy] at h90
  have hq := (hc t).2.2.2
  set x := (c t).y
  have hθ0 : 0 < E.θ := by linarith
  have e1 : x ^ ((E.θ + 1) / E.θ) = x * x ^ (1 / E.θ) := by
    rw [show (E.θ + 1) / E.θ = 1 + 1 / E.θ by field_simp, rpow_add hq, rpow_one]
  rw [e1] at h90
  have hx1 : 0 < x ^ (1 / E.θ) := rpow_pos_of_pos hq _
  have hsq : x ^ 2 = (E.θ - 1) * (1 - E.γ) / (E.κ * E.θ) := by
    field_simp at h90 ⊢
    nlinarith
  have hxy : x = ybarN E := by
    unfold ybarN; rw [← hsq, sqrt_sq hq.le]
  exact ⟨hxy, hy ▸ hxy⟩

/-- Homogeneity of (83): `P = P_T · P(1, P_N/P_T)` (O&R p. 690). -/
theorem cpi_eq_mul {γ PT PN : ℝ} (hT : 0 < PT) (hN : 0 < PN) :
    cpi γ PT PN = PT * cpi γ 1 (PN / PT) := by
  unfold cpi
  rw [one_rpow, div_rpow hN.le hT.le, rpow_sub hT, rpow_one]
  have : 0 < PT ^ γ := rpow_pos_of_pos hT γ
  field_simp

/-- The steady-state relative price `P_N/P_T = ((1−γ)/γ)(ȳ_T/ȳ_N)` from (89) (O&R p. 692). -/
noncomputable def relPriceBar (E : Economy) : ℝ := (1 - E.γ) / E.γ * (E.yT / ybarN E)

/-- The steady-state ratio `P/P_T = P(1, P_N/P_T)` (O&R (83)). -/
noncomputable def cpiRatio (E : Economy) : ℝ := cpi E.γ 1 (relPriceBar E)

/-- Steady-state real balances from (92) with constant prices:
`M/P = [(χ/γ) ȳ_T (P_T/P)/(1−β)]^{1/ε}` (O&R p. 692). -/
noncomputable def realMoneyBar (E : Economy) : ℝ :=
  (E.χ / E.γ * (E.yT / cpiRatio E) / (1 - E.β)) ^ (1 / E.ε)

/-- The steady-state relative price is positive (O&R p. 692). -/
theorem relPriceBar_pos {E : Economy} (hE : E.Valid) : 0 < relPriceBar E := by
  have h := ybarN_pos hE
  obtain ⟨_, _, _, hγ0, hγ1, _, _, _, _, hy⟩ := hE
  unfold relPriceBar
  have : 0 < 1 - E.γ := by linarith
  positivity

/-- `P/P_T > 0` in the steady state (O&R (83)). -/
theorem cpiRatio_pos {E : Economy} (hE : E.Valid) : 0 < cpiRatio E := by
  have h := relPriceBar_pos hE
  obtain ⟨_, _, _, hγ0, hγ1, _, _, _, _, _⟩ := hE
  exact cpi_pos hγ0 hγ1 one_pos h

/-- Steady-state real balances are positive (O&R (92)). -/
theorem realMoneyBar_pos {E : Economy} (hE : E.Valid) : 0 < realMoneyBar E := by
  have h := cpiRatio_pos hE
  obtain ⟨_, hβ1, _, hγ0, _, hχ, _, _, _, hy⟩ := hE
  unfold realMoneyBar
  have : 0 < 1 - E.β := by linarith
  positivity

/-- UNIQUENESS of the steady state and of the initial price level `P̄_0` given `M̄_0`
(O&R §10.2.3, p. 692): in any equilibrium with constant prices `P_T, P_N`, constant money `M̄`,
`B_0 = 0` and `β(1+r) = 1`, the allocation is `(ȳ_T, ȳ_N, M̄, ȳ_N)` at every date,
`P_N = (P_N/P_T)‾ P_T`, and `P = M̄/(M/P)‾`, `P_T = M̄/((M/P)‾ (P/P_T)‾)` — all proportional to
`M̄` (long-run neutrality, (98)). -/
theorem steadyState_unique {E : Economy} {Q : Prices} (hE : E.Valid) (hβr : E.β * (1 + E.r) = 1)
    (hQ : Q.Valid E.r) {Mbar pT pN : ℝ} (hM0 : 0 < Mbar) {M : ℕ → ℝ} {c : ℕ → Choice}
    (hPT : ∀ t, Q.PT t = pT) (hPN : ∀ t, Q.PN t = pN) (hMt : ∀ t, M t = Mbar)
    (heq : IsEquilibrium E Q 0 Mbar M c) :
    (∀ t, (c t).cT = E.yT ∧ (c t).cN = ybarN E ∧ (c t).money = Mbar ∧ (c t).y = ybarN E) ∧
      pN = relPriceBar E * pT ∧ cpi E.γ pT pN = Mbar / realMoneyBar E ∧
      pT = Mbar / (realMoneyBar E * cpiRatio E) := by
  have hE' := hE
  obtain ⟨hβ, hβ1, hr, hγ0, hγ1, hχ, hε, _, _, hyT⟩ := hE'
  have hr0 : 0 < E.r := by nlinarith
  have hopt := heq.1
  have hc := hopt.1
  have hT : 0 < pT := hPT 0 ▸ (hQ 0).1
  have hN : 0 < pN := hPN 0 ▸ (hQ 0).2.1
  have hmp : ∀ T, moneyPrev Mbar c T = Mbar := by
    intro T; cases T with
    | zero => rfl
    | succ T => simp only [moneyPrev]; rw [heq.2.2.1 T, hMt T]
  have hnb : Tendsto (moneyBubble E Q Mbar c) atTop (𝓝 0) := by
    have e : moneyBubble E Q Mbar c = fun T => disc E.r T * (Mbar / pT) := by
      funext T; simp only [moneyBubble, hmp T, hPT T]
    rw [e]; simpa using (tendsto_disc hr0).mul_const (Mbar / pT)
  have hca := balanced_current_account hE hβr hQ heq hM0 hnb
  have h93 := output_93 hE heq
  have hall : ∀ t, (c t).cT = E.yT ∧ (c t).cN = ybarN E ∧ (c t).money = Mbar ∧
      (c t).y = ybarN E := fun t =>
    ⟨(hca t).1, (h93 t).2, (heq.2.2.1 t).trans (hMt t), (h93 t).1⟩
  have hyb := ybarN_pos hE
  -- (89)
  have hintra := intraFOC_of_optimal hE hopt 0
  rw [(hall 0).1, (hall 0).2.1] at hintra
  simp only [relPrice, hPT, hPN] at hintra
  have hrel : pN = relPriceBar E * pT := by
    unfold relPriceBar; field_simp at hintra ⊢; linarith
  -- (92)
  have h92 := money_92 hE hβr hQ hc (moneyFOC_of_optimal hE hQ hopt) 0
  simp only [cpiAt, hPT, hPN, (hall 0).1, (hall 0).2.2.1] at h92
  have hP : cpi E.γ pT pN = pT * cpiRatio E := by
    rw [cpi_eq_mul hT hN, hrel, mul_div_cancel_right₀ _ hT.ne']; rfl
  have hcr := cpiRatio_pos hE
  have hmb : Mbar / cpi E.γ pT pN = realMoneyBar E := by
    rw [h92, hP, div_self hT.ne', mul_one]
    unfold realMoneyBar
    congr 1
    field_simp
  have hPbar : cpi E.γ pT pN = Mbar / realMoneyBar E := by
    have hPpos : 0 < cpi E.γ pT pN := cpi_pos hγ0 hγ1 hT hN
    have := realMoneyBar_pos hE
    field_simp at hmb ⊢; linarith
  refine ⟨hall, hrel, hPbar, ?_⟩
  rw [hP] at hPbar
  field_simp at hPbar ⊢
  linarith

/-- The steady-state price paths given `M̄` (O&R §10.2.3): `P_T = M̄/((M/P)‾ (P/P_T)‾)`,
`P_N = (P_N/P_T)‾ P_T`, aggregate demand `ȳ_N`, zero taxes. -/
noncomputable def steadyPrices (E : Economy) (Mbar : ℝ) : Prices :=
  ⟨fun _ => Mbar / (realMoneyBar E * cpiRatio E),
    fun _ => relPriceBar E * (Mbar / (realMoneyBar E * cpiRatio E)), fun _ => ybarN E,
    fun _ => 0⟩

/-- The steady-state allocation `(ȳ_T, ȳ_N, M̄, ȳ_N)` (O&R (91), (93)). -/
noncomputable def steadyChoice (E : Economy) (Mbar : ℝ) : ℕ → Choice :=
  fun _ => ⟨E.yT, ybarN E, Mbar, ybarN E⟩

/-- EXISTENCE (O&R §10.2.3, p. 692): for every `M̄ > 0` the steady state IS an equilibrium —
the allocation `(ȳ_T, ȳ_N, M̄, ȳ_N)` is a genuine infinite-horizon household optimum at the
steady-state prices (verified through `householdOptimal_iff`), markets clear and (85) holds. -/
theorem steadyState_isEquilibrium {E : Economy} (hE : E.Valid) (hβr : E.β * (1 + E.r) = 1)
    {Mbar : ℝ} (hM0 : 0 < Mbar) :
    (steadyPrices E Mbar).Valid E.r ∧
      IsEquilibrium E (steadyPrices E Mbar) 0 Mbar (fun _ => Mbar) (steadyChoice E Mbar) := by
  have hE' := hE
  obtain ⟨hβ, hβ1, hr, hγ0, hγ1, hχ, hε, hκ, hθ, hyT⟩ := hE'
  have hr0 : 0 < E.r := by nlinarith
  have hyb := ybarN_pos hE
  have hrel := relPriceBar_pos hE
  have hcr := cpiRatio_pos hE
  have hmb := realMoneyBar_pos hE
  set pT := Mbar / (realMoneyBar E * cpiRatio E) with hpT
  have hT : 0 < pT := by positivity
  set Q := steadyPrices E Mbar
  set c := steadyChoice E Mbar
  have hu : ∀ t, userCost E.r Q t = (1 - E.β) / pT := by
    intro t
    simp only [userCost, Q, steadyPrices]
    rw [← hpT]
    have : 1 / ((1 + E.r) * pT) = E.β / pT := by field_simp; linarith
    rw [this]; field_simp
  have hQ : Q.Valid E.r := by
    intro t
    refine ⟨hT, by simp only [Q, steadyPrices]; positivity, hyb, ?_⟩
    rw [hu t]; exact div_pos (by linarith) hT
  have hPcpi : ∀ t, cpiAt E Q t = pT * cpiRatio E := by
    intro t
    simp only [cpiAt, Q, steadyPrices]
    rw [← hpT, cpi_eq_mul hT (by positivity), mul_div_cancel_right₀ _ hT.ne']
    rfl
  have hc : ∀ t, c t ∈ posChoice := fun _ => ⟨hyT, hyb, hM0, hyb⟩
  have hw : ∀ t, wealth E.r (initWealth E Q 0 Mbar) (netRes E Q) c t = Mbar / pT := by
    intro t
    induction t with
    | zero => simp only [wealth, initWealth, Q, steadyPrices]; rw [← hpT]; ring
    | succ t ih =>
      rw [wealth, ih]
      have hrev : realRevenue E Q t (c t).y = relPrice Q t * (c t).cN :=
        realRevenue_symm E Q t (by linarith) hyb rfl
      simp only [netRes, hrev, hu t]
      simp only [c, steadyChoice, Q, steadyPrices]
      field_simp
      linear_combination Mbar * hβr
  have hdw : Tendsto (fun T => disc E.r T * wealth E.r (initWealth E Q 0 Mbar) (netRes E Q) c T)
      atTop (𝓝 0) := by
    simp_rw [hw]; simpa using (tendsto_disc hr0).mul_const (Mbar / pT)
  have hnp : NoPonzi E.r (wealth E.r (initWealth E Q 0 Mbar) (netRes E Q) c) :=
    fun δ hδ => (hdw.eventually (lt_mem_nhds (by linarith : -δ < 0))).mono fun _ h => h.le
  have htv : LiminfNonpos E.r (wealth E.r (initWealth E Q 0 Mbar) (netRes E Q) c) :=
    fun δ hδ => (hdw.eventually (gt_mem_nhds hδ)).frequently.mono fun _ h => h.le
  have hsum : Summable fun t => E.β ^ t * periodU E Q t (c t) := by
    have e : (fun t => E.β ^ t * periodU E Q t (c t))
        = fun t => E.β ^ t * periodU E Q 0 (c 0) := by
      funext t; rfl
    rw [e]
    exact (summable_geometric_of_lt_one hβ.le hβ1).mul_right _
  have heu : EulerFOC E c := by
    intro t; simp only [c, steadyChoice]; rw [hβr, one_mul]
  have hN : IntraFOC E Q c := by
    intro t
    simp only [c, steadyChoice, relPrice, Q, steadyPrices]
    rw [mul_div_cancel_right₀ _ hT.ne']
    unfold relPriceBar; field_simp
  have hMF : MoneyFOC E Q c := by
    intro t
    simp only [c, steadyChoice]
    rw [hu t, hPcpi t]
    have hmbar : Mbar / (pT * cpiRatio E) = realMoneyBar E := by
      rw [hpT]; field_simp
    rw [hmbar]
    unfold realMoneyBar
    rw [← rpow_mul (by positivity), show 1 / E.ε * -E.ε = -1 by field_simp, rpow_neg_one]
    have : 0 < 1 - E.β := by linarith
    field_simp
  have hL : LabourFOC E Q c := by
    intro t
    simp only [c, steadyChoice, relPrice, Q, steadyPrices]
    rw [mul_div_cancel_right₀ _ hT.ne', ← rpow_add hyb,
      show (E.θ - 1) / E.θ - 1 + 1 / E.θ = 0 by field_simp; ring, rpow_zero, mul_one]
    have hk := kappa_mul_ybarN_sq hE
    unfold relPriceBar
    field_simp at hk ⊢
    linarith
  refine ⟨hQ, householdOptimal_of_foc hE hQ hc hsum heu hN hMF hL hnp htv, ?_, ?_, ?_⟩
  · intro t; exact ⟨rfl, rfl⟩
  · intro t; rfl
  · intro t
    have : moneyPrev Mbar c t = Mbar := by cases t <;> rfl
    simp [this, Q, steadyPrices]

end ObstfeldRogoff.StickyPriceModels.NontradablesModel

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Overshooting with preset nontradables prices: exact nonlinear results

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §10.2.4,
pp. 692–694, and end-of-chapter Exercise 2, p. 713. In the small open economy of
`NontradablesModel`, nontradables prices are preset one period in advance and an unanticipated
permanent money shock `M_1 = μ M_0` hits at date 1. The book log-linearises and obtains (99):
`p_T = e = [β + (1−β)ε] m / [β + (1−β)(1 − γ + γε)]`, so the exchange rate overshoots iff
`ε > 1`.

This file proves everything EXACTLY in the nonlinear model.

* With `x := P_{T,1}/P_{T,0}`, the date-1 money-demand equation (92), long-run neutrality
  (from `NontradablesModel.steadyState_unique`) and the preset `P_N` reduce to
  `μ^ε (1 − βx/μ) = (1−β) x^{1−γ+γε}`, which has a UNIQUE solution, and it lies in `(0, μ/β)`.
* Exact overshooting: for `μ > 1`, `x > μ ⟺ ε > 1`, `x = μ ⟺ ε = 1`, `x < μ ⟺ ε < 1`
  (reversed for `μ < 1`). Also `x > 1`, real balances rise strictly, and `C_N = y_N` rise by the
  factor `x`.
* (99) is the DERIVATIVE at `μ = 1` of the implicitly defined solution `x(μ)` (via the 1-D
  inverse function theorem), and (96)–(99) are verified as linear algebra and as derivatives.
* The whole sticky-price path is a genuine infinite-horizon equilibrium (household optimality
  with the preset price at date 1, via the concave-Lagrangian sufficiency theorem), IF AND ONLY
  IF `x` solves the impact equation and `x² ≤ θ/(θ−1)` (preset price at least ex post marginal
  cost: the exact meaning of "output is demand-determined").
* T29 (p. 694, "unambiguously improves welfare"): the exact gain in lifetime utility is
  `(1−γ)[log x − ((θ−1)/(2θ))(x² − 1)]` plus the strictly positive real-balance gain, positive on
  the whole demand-determined range; its derivative at `μ = 1` is `(1−γ)x'(1)/θ`.
* Exercise 2 (the real exchange rate `Q = 𝓔P^*/P` is never defined in the book; defined here):
  exact real interest parity `1 + r^C_{t+1} = (1+r) Q_{t+1}/Q_t`; on impact `Q_1/Q_0 = x^{1−γ} > 1`
  (real depreciation) and `r^C_2 < r`, for every `ε > 0`.
-/

namespace ObstfeldRogoff.StickyPriceModels.NontradablesOvershooting

open Real Filter Topology Finset
open ObstfeldRogoff.StickyPriceModels.NontradablesModel

/-! ## The exact impact equation -/

/-- The elasticity `1 − γ + γε` of the right side of the impact equation (O&R (99)). -/
noncomputable def expo (γ ε : ℝ) : ℝ := 1 - γ + γ * ε

/-- The impact equation `F(μ, x) = μ^ε (1 − βx/μ) − (1−β) x^{1−γ+γε}` whose zero is the impact
response `x = P_{T,1}/P_{T,0}` (O&R (92) at dates 0 and 1, pp. 692–693). -/
noncomputable def impactGap (β γ ε μ x : ℝ) : ℝ :=
  μ ^ ε * (1 - β * x / μ) - (1 - β) * x ^ expo γ ε

/-- `1 − γ + γε > 0` (O&R (99)). -/
theorem expo_pos {γ ε : ℝ} (hγ0 : 0 < γ) (hγ1 : γ < 1) (hε : 0 < ε) : 0 < expo γ ε := by
  unfold expo; nlinarith

/-- `ε > 1−γ+γε ⟺ ε > 1` for `γ < 1` (the overshooting comparison, O&R p. 693). -/
theorem expo_lt_iff {γ ε : ℝ} (hγ1 : γ < 1) : expo γ ε < ε ↔ 1 < ε := by
  unfold expo
  constructor <;> intro h <;> nlinarith

/-- The impact equation is strictly decreasing in `x ≥ 0` (O&R pp. 692–693). -/
theorem impactGap_strictAntiOn {β γ ε μ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hγ0 : 0 < γ)
    (hγ1 : γ < 1) (hε : 0 < ε) (hμ : 0 < μ) :
    StrictAntiOn (impactGap β γ ε μ) (Set.Ici 0) := by
  intro x1 hx1 x2 hx2 hlt
  simp only [Set.mem_Ici] at hx1 hx2
  unfold impactGap
  have ha := expo_pos hγ0 hγ1 hε
  have h1 : x1 ^ expo γ ε ≤ x2 ^ expo γ ε := rpow_le_rpow hx1 hlt.le ha.le
  have h2 : β * x1 / μ < β * x2 / μ := by
    apply div_lt_div_of_pos_right _ hμ; nlinarith
  have hme : 0 < μ ^ ε := rpow_pos_of_pos hμ ε
  nlinarith

/-- EXISTENCE AND UNIQUENESS of the impact response (O&R (99), exact version): for every `μ > 0`
there is exactly one `x > 0` with `F(μ, x) = 0`, and it satisfies `x < μ/β` (a positive nominal
interest rate at date 1). -/
theorem impact_exists_unique {β γ ε μ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hγ0 : 0 < γ)
    (hγ1 : γ < 1) (hε : 0 < ε) (hμ : 0 < μ) :
    ∃ x, 0 < x ∧ x < μ / β ∧ impactGap β γ ε μ x = 0 ∧
      ∀ y, 0 < y → impactGap β γ ε μ y = 0 → y = x := by
  have ha := expo_pos hγ0 hγ1 hε
  have hb : 0 < μ / β := div_pos hμ hβ
  have hcont : ContinuousOn (impactGap β γ ε μ) (Set.Icc 0 (μ / β)) := by
    unfold impactGap
    exact (continuous_const.mul (continuous_const.sub
      ((continuous_const.mul continuous_id).div_const μ))).sub
      (continuous_const.mul (continuous_rpow_const ha.le)) |>.continuousOn
  have h0 : impactGap β γ ε μ 0 = μ ^ ε := by
    simp [impactGap, zero_rpow ha.ne']
  have hend : impactGap β γ ε μ (μ / β) = -((1 - β) * (μ / β) ^ expo γ ε) := by
    unfold impactGap
    rw [show β * (μ / β) / μ = 1 by field_simp]; ring
  have hmem : (0 : ℝ) ∈ Set.Ioo (impactGap β γ ε μ (μ / β)) (impactGap β γ ε μ 0) := by
    rw [h0, hend]
    constructor
    · have : 0 < (1 - β) * (μ / β) ^ expo γ ε :=
        mul_pos (by linarith) (rpow_pos_of_pos hb _)
      linarith
    · exact rpow_pos_of_pos hμ ε
  obtain ⟨x, ⟨hx0, hxb⟩, hx⟩ := intermediate_value_Ioo' hb.le hcont hmem
  refine ⟨x, hx0, hxb, hx, fun y hy hy0 => ?_⟩
  by_contra hne
  have hanti := impactGap_strictAntiOn hβ hβ1 hγ0 hγ1 hε hμ
  rcases lt_or_gt_of_ne hne with h | h
  · have := hanti (Set.mem_Ici.mpr hy.le) (Set.mem_Ici.mpr hx0.le) h; linarith
  · have := hanti (Set.mem_Ici.mpr hx0.le) (Set.mem_Ici.mpr hy.le) h; linarith

/-- Any positive root of the impact equation is below `μ/β` (O&R (92) needs `1 − βx/μ > 0`). -/
theorem root_lt {β γ ε μ x : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hε : 0 < ε) (hμ : 0 < μ) (hx : 0 < x) (hF : impactGap β γ ε μ x = 0) : x < μ / β := by
  obtain ⟨z, hz0, hzb, _, huniq⟩ := impact_exists_unique hβ hβ1 hγ0 hγ1 hε hμ
  rw [huniq x hx hF]; exact hzb

/-- The value of the impact equation at `x = μ` (no overshooting):
`F(μ, μ) = (1−β)(μ^ε − μ^{1−γ+γε})` (O&R p. 693). -/
theorem impactGap_at_mu {β γ ε μ : ℝ} (hμ : 0 < μ) :
    impactGap β γ ε μ μ = (1 - β) * (μ ^ ε - μ ^ expo γ ε) := by
  unfold impactGap
  rw [show β * μ / μ = β by field_simp]; ring

/-- EXACT OVERSHOOTING (O&R (99) and p. 693, nonlinear version): for a monetary expansion
`μ > 1`, the tradables price (the exchange rate) overshoots its new long-run level `μ` IF AND
ONLY IF `ε > 1`; it moves one for one iff `ε = 1`; it undershoots iff `ε < 1`. -/
theorem overshoot_iff {β γ ε μ x : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hε : 0 < ε) (hμ : 1 < μ) (hx : 0 < x) (hF : impactGap β γ ε μ x = 0) :
    (μ < x ↔ 1 < ε) ∧ (x = μ ↔ ε = 1) ∧ (x < μ ↔ ε < 1) := by
  have hμ0 : 0 < μ := by linarith
  have hanti := impactGap_strictAntiOn hβ hβ1 hγ0 hγ1 hε hμ0
  have hFμ := impactGap_at_mu (β := β) (γ := γ) (ε := ε) hμ0
  have hb1 : 0 < 1 - β := by linarith
  have key1 : μ < x ↔ 0 < impactGap β γ ε μ μ := by
    constructor
    · intro h; have := hanti (Set.mem_Ici.mpr hμ0.le) (Set.mem_Ici.mpr hx.le) h; linarith
    · intro h; by_contra hle; push Not at hle
      rcases eq_or_lt_of_le hle with he | hlt
      · rw [he] at hF; linarith
      · have := hanti (Set.mem_Ici.mpr hx.le) (Set.mem_Ici.mpr hμ0.le) hlt; linarith
  have key2 : x < μ ↔ impactGap β γ ε μ μ < 0 := by
    constructor
    · intro h; have := hanti (Set.mem_Ici.mpr hx.le) (Set.mem_Ici.mpr hμ0.le) h; linarith
    · intro h; by_contra hle; push Not at hle
      rcases eq_or_lt_of_le hle with he | hlt
      · rw [← he] at hF; linarith
      · have := hanti (Set.mem_Ici.mpr hμ0.le) (Set.mem_Ici.mpr hx.le) hlt; linarith
  have hcmp1 : 0 < impactGap β γ ε μ μ ↔ 1 < ε := by
    rw [hFμ, ← expo_lt_iff hγ1, mul_pos_iff_of_pos_left hb1, sub_pos,
      rpow_lt_rpow_left_iff hμ]
  have hneg : ∀ d : ℝ, (1 - β) * d < 0 ↔ d < 0 := fun d =>
    ⟨fun h => by by_contra hc; push Not at hc; nlinarith [mul_nonneg hb1.le hc],
      fun h => mul_neg_of_pos_of_neg hb1 h⟩
  have hcmp2 : impactGap β γ ε μ μ < 0 ↔ ε < 1 := by
    rw [hFμ, hneg, sub_neg, rpow_lt_rpow_left_iff hμ]
    unfold expo
    constructor <;> intro h <;> nlinarith
  refine ⟨key1.trans hcmp1, ?_, key2.trans hcmp2⟩
  constructor
  · intro he
    rcases lt_trichotomy ε 1 with h | h | h
    · have := (key2.trans hcmp2).mpr h; linarith
    · exact h
    · have := (key1.trans hcmp1).mpr h; linarith
  · intro he
    rcases lt_trichotomy x μ with h | h | h
    · have := (key2.trans hcmp2).mp h; linarith
    · exact h
    · have := (key1.trans hcmp1).mp h; linarith

/-- EXACT OVERSHOOTING for a monetary CONTRACTION `0 < μ < 1` (the mirror image of (99)): the
tradables price falls below its new long-run level (`x < μ`) iff `ε > 1`. -/
theorem overshoot_iff_of_lt_one {β γ ε μ x : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hγ0 : 0 < γ)
    (hγ1 : γ < 1) (hε : 0 < ε) (hμ0 : 0 < μ) (hμ : μ < 1) (hx : 0 < x)
    (hF : impactGap β γ ε μ x = 0) : x < μ ↔ 1 < ε := by
  have hanti := impactGap_strictAntiOn hβ hβ1 hγ0 hγ1 hε hμ0
  have hFμ := impactGap_at_mu (β := β) (γ := γ) (ε := ε) hμ0
  have hb1 : 0 < 1 - β := by linarith
  have key : x < μ ↔ impactGap β γ ε μ μ < 0 := by
    constructor
    · intro h; have := hanti (Set.mem_Ici.mpr hx.le) (Set.mem_Ici.mpr hμ0.le) h; linarith
    · intro h; by_contra hle; push Not at hle
      rcases eq_or_lt_of_le hle with he | hlt
      · rw [← he] at hF; linarith
      · have := hanti (Set.mem_Ici.mpr hμ0.le) (Set.mem_Ici.mpr hx.le) hlt; linarith
  have hneg : ∀ d : ℝ, (1 - β) * d < 0 ↔ d < 0 := fun d =>
    ⟨fun h => by by_contra hc; push Not at hc; nlinarith [mul_nonneg hb1.le hc],
      fun h => mul_neg_of_pos_of_neg hb1 h⟩
  rw [key, hFμ, hneg, sub_neg, rpow_lt_rpow_left_iff_of_base_lt_one hμ0 hμ]
  unfold expo
  constructor <;> intro h <;> nlinarith


/-- For a monetary expansion `μ > 1` the tradables price rises: `x > 1` (O&R p. 693). -/
theorem one_lt_root {β γ ε μ x : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hε : 0 < ε) (hμ : 1 < μ) (hx : 0 < x) (hF : impactGap β γ ε μ x = 0) : 1 < x := by
  have hμ0 : 0 < μ := by linarith
  -- `φ(ν) = ν^ε − β ν^{ε−1}` is strictly increasing on `[1, ∞)`
  set φ : ℝ → ℝ := fun ν => ν ^ ε - β * ν ^ (ε - 1) with hφ
  have hφd : ∀ ν, 0 < ν → HasDerivAt φ (ε * ν ^ (ε - 1) - β * ((ε - 1) * ν ^ (ε - 1 - 1))) ν :=
    fun ν hν => (hasDerivAt_rpow_const (Or.inl hν.ne')).sub
      ((hasDerivAt_rpow_const (p := ε - 1) (Or.inl hν.ne')).const_mul β)
  have hmono : StrictMonoOn φ (Set.Ici 1) := by
    refine strictMonoOn_of_deriv_pos (convex_Ici 1) ?_ ?_
    · intro ν hν
      exact (hφd ν (by simp only [Set.mem_Ici] at hν; linarith)).continuousAt.continuousWithinAt
    · intro ν hν
      rw [interior_Ici] at hν
      simp only [Set.mem_Ioi] at hν
      have hν0 : 0 < ν := by linarith
      rw [(hφd ν hν0).deriv]
      have hp : 0 < ν ^ (ε - 1 - 1) := rpow_pos_of_pos hν0 _
      have e : ν ^ (ε - 1) = ν * ν ^ (ε - 1 - 1) := by
        rw [rpow_sub_one hν0.ne' (ε - 1)]; field_simp
      rw [e]
      rcases le_or_gt 1 ε with h | h
      · have : 0 < ε * ν - β * (ε - 1) := by nlinarith
        nlinarith
      · have : 0 < ε * ν - β * (ε - 1) := by nlinarith
        nlinarith
  have hφ1 : φ 1 < φ μ := hmono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr hμ.le) hμ
  simp only [hφ, one_rpow] at hφ1
  have hF1 : 0 < impactGap β γ ε μ 1 := by
    unfold impactGap
    rw [one_rpow]
    have e : μ ^ ε * (1 - β * 1 / μ) = μ ^ ε - β * μ ^ (ε - 1) := by
      rw [rpow_sub_one hμ0.ne']; field_simp
    rw [e]; linarith
  by_contra hle
  push Not at hle
  rcases eq_or_lt_of_le hle with he | hlt
  · rw [he] at hF; linarith
  · have := impactGap_strictAntiOn hβ hβ1 hγ0 hγ1 hε hμ0 (Set.mem_Ici.mpr hx.le)
      (Set.mem_Ici.mpr zero_le_one) hlt
    linarith

/-- Real balances rise strictly on impact (O&R p. 694, "real balances rise temporarily"):
`M_1/P_1 = μ M_0/(x^γ P_0) > M_0/P_0`, i.e. `μ/x^γ > 1`, for every `ε > 0` and `μ > 1`. -/
theorem realBalances_rise {β γ ε μ x : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hγ0 : 0 < γ)
    (hγ1 : γ < 1) (hε : 0 < ε) (hμ : 1 < μ) (hx : 0 < x) (hF : impactGap β γ ε μ x = 0) :
    1 < μ / x ^ γ := by
  have hμ0 : 0 < μ := by linarith
  have hxg : 0 < x ^ γ := rpow_pos_of_pos hx γ
  rw [one_lt_div hxg]
  rcases lt_or_ge x μ with h | h
  · calc x ^ γ < μ ^ γ := rpow_lt_rpow hx.le h hγ0
      _ < μ ^ (1 : ℝ) := rpow_lt_rpow_of_exponent_lt hμ hγ1
      _ = μ := rpow_one μ
  · have hx1 : 1 < x := lt_of_lt_of_le hμ h
    have hb : 0 < 1 - β * x / μ := by
      have := root_lt hβ hβ1 hγ0 hγ1 hε hμ0 hx hF
      rw [sub_pos, div_lt_one hμ0]
      calc β * x < β * (μ / β) := by nlinarith
        _ = μ := by field_simp
    unfold impactGap expo at hF
    have hsplit : x ^ (1 - γ + γ * ε) = x ^ (1 - γ) * (x ^ γ) ^ ε := by
      rw [← rpow_mul hx.le, ← rpow_add hx]
    rw [hsplit] at hF
    have hx1g : 1 < x ^ (1 - γ) := one_lt_rpow hx1 (by linarith)
    have hkey : (x ^ γ) ^ ε < μ ^ ε := by
      have h2 : 1 - β * x / μ ≤ 1 - β := by
        have : β ≤ β * x / μ := by rw [le_div_iff₀ hμ0]; nlinarith
        linarith
      have hxe : 0 < (x ^ γ) ^ ε := rpow_pos_of_pos hxg ε
      have h3 : (1 - β) * (x ^ γ) ^ ε < (1 - β) * x ^ (1 - γ) * (x ^ γ) ^ ε := by
        have : 0 < (1 - β) * (x ^ γ) ^ ε := mul_pos (by linarith) hxe
        nlinarith
      have h4 : (1 - β) * x ^ (1 - γ) * (x ^ γ) ^ ε = μ ^ ε * (1 - β * x / μ) := by linarith
      have h5 : (1 - β * x / μ) * (x ^ γ) ^ ε ≤ (1 - β) * (x ^ γ) ^ ε :=
        mul_le_mul_of_nonneg_right h2 hxe.le
      have h6 : (1 - β * x / μ) * (x ^ γ) ^ ε < (1 - β * x / μ) * μ ^ ε := by linarith
      exact lt_of_mul_lt_mul_left h6 hb.le
    exact (rpow_lt_rpow_iff hxg.le hμ0.le hε).mp hkey

/-! ## (99) as the derivative of the exact impact response -/

/-- The overshooting ratio map `H(t) = (1−β) t^a / (1−βt)`: `x = μt` solves the impact equation
iff `H(t) = μ^{(ε−1)(1−γ)}` (O&R (99), exact). -/
noncomputable def ratioMap (β a t : ℝ) : ℝ := (1 - β) * t ^ a / (1 - β * t)

/-- Rescaling the impact equation by `x = μt` (O&R p. 693):
`F(μ, μt) = μ^ε(1−βt)(1 − μ^{a−ε} H(t))`. -/
theorem impactGap_scaled {β γ ε μ t : ℝ} (hμ : 0 < μ) (ht : 0 < t) (hβt : β * t < 1) :
    impactGap β γ ε μ (μ * t)
      = μ ^ ε * (1 - β * t) * (1 - μ ^ (expo γ ε - ε) * ratioMap β (expo γ ε) t) := by
  unfold impactGap ratioMap
  have hb : (1 : ℝ) - β * t ≠ 0 := by linarith
  rw [mul_rpow hμ.le ht.le, rpow_sub hμ]
  have : 0 < μ ^ ε := rpow_pos_of_pos hμ ε
  field_simp

/-- `H(1) = 1` (O&R (99): no overshooting when `μ = 1`). -/
theorem ratioMap_one {β a : ℝ} (hβ1 : β < 1) : ratioMap β a 1 = 1 := by
  unfold ratioMap
  rw [one_rpow, mul_one, mul_one]
  exact div_self (by linarith)

/-- The strict derivative of `H` at `1` is `(β + (1−β)a)/(1−β)` (O&R (99)). -/
theorem hasStrictDerivAt_ratioMap {β a : ℝ} (hβ1 : β < 1) :
    HasStrictDerivAt (ratioMap β a) ((β + (1 - β) * a) / (1 - β)) 1 := by
  have hb : (1 : ℝ) - β * 1 ≠ 0 := by linarith
  have h1 := (hasStrictDerivAt_rpow_const_of_ne (one_ne_zero) a).const_mul (1 - β)
  have h2 := ((hasStrictDerivAt_id (1 : ℝ)).const_mul β).const_sub 1
  have h3 := h1.div h2 hb
  have e : ratioMap β a = (fun y => (1 - β) * y ^ a) / fun x => 1 - β * id x := by
    funext t; simp [ratioMap]
  rw [e]
  convert h3 using 1
  simp only [one_rpow, id]
  have : (1 : ℝ) - β ≠ 0 := by linarith
  field_simp
  ring

/-- (99) IS THE DERIVATIVE of the exact impact response (O&R (99), p. 693): if `X(μ)` is a
positive root of the impact equation for every `μ` near `1`, then
`X'(1) = [β + (1−β)ε]/[β + (1−β)(1−γ+γε)]`. Proved with the 1-D inverse function theorem
applied to `H`, and uniqueness of the root. -/
theorem hasDerivAt_impact {β γ ε : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hγ0 : 0 < γ)
    (hγ1 : γ < 1) (hε : 0 < ε) {X : ℝ → ℝ}
    (hX : ∀ᶠ μ in 𝓝 1, 0 < X μ ∧ impactGap β γ ε μ (X μ) = 0) :
    HasDerivAt X ((β + (1 - β) * ε) / (β + (1 - β) * expo γ ε)) 1 := by
  set a := expo γ ε with ha_def
  have ha := expo_pos hγ0 hγ1 hε
  set c := ε - a with hc
  set Hd := (β + (1 - β) * a) / (1 - β) with hHd_def
  have hb1 : 0 < 1 - β := by linarith
  have hHd : Hd ≠ 0 := by
    have : 0 < β + (1 - β) * a := by positivity
    exact (div_pos this hb1).ne'
  have hH := hasStrictDerivAt_ratioMap (a := a) hβ1
  set L := HasStrictDerivAt.localInverse (ratioMap β a) Hd 1 hH hHd
  have hH1 : ratioMap β a 1 = 1 := ratioMap_one hβ1
  have hL : HasStrictDerivAt L Hd⁻¹ (ratioMap β a 1) := hH.to_localInverse hHd
  have hleft := hH.eventually_left_inverse hHd
  have hright := hH.eventually_right_inverse hHd
  have hL1 : L 1 = 1 := by
    have := hleft.self_of_nhds; rw [hH1] at this; exact this
  rw [hH1] at hL hright
  -- the power map `μ ↦ μ^c`
  have hpw : HasDerivAt (fun μ : ℝ => μ ^ c) c 1 := by
    have := hasDerivAt_rpow_const (x := (1 : ℝ)) (p := c) (Or.inl one_ne_zero)
    simpa using this
  have hpt : Tendsto (fun μ : ℝ => μ ^ c) (𝓝 1) (𝓝 1) := by
    have := hpw.continuousAt.tendsto; simpa using this
  have hLt : Tendsto (fun μ : ℝ => L (μ ^ c)) (𝓝 1) (𝓝 1) := by
    have := hL.hasDerivAt.continuousAt.tendsto.comp hpt
    rw [hL1] at this; exact this
  have hIoo : Set.Ioo 0 (1 / β) ∈ 𝓝 (1 : ℝ) := by
    apply Ioo_mem_nhds one_pos
    rw [lt_div_iff₀ hβ]; linarith
  -- the explicit solution `Y μ = μ L(μ^c)`
  set Y : ℝ → ℝ := fun μ => μ * L (μ ^ c)
  have hXY : X =ᶠ[𝓝 1] Y := by
    filter_upwards [hX, hpt.eventually hright, hLt.eventually hIoo,
      Ioi_mem_nhds (zero_lt_one' ℝ)] with μ hXμ hR hI hμ
    obtain ⟨hI0, hI1⟩ := hI
    simp only [Set.mem_Ioi] at hμ
    have hβt : β * L (μ ^ c) < 1 := by
      rw [lt_div_iff₀ hβ] at hI1; linarith
    have hYroot : impactGap β γ ε μ (Y μ) = 0 := by
      simp only [Y]
      rw [impactGap_scaled hμ hI0 hβt, hR, ← rpow_add hμ,
        show a - ε + c = 0 by rw [hc]; ring, rpow_zero]
      ring
    have hY0 : 0 < Y μ := mul_pos hμ hI0
    by_contra hne
    have hanti := impactGap_strictAntiOn hβ hβ1 hγ0 hγ1 hε hμ
    rcases lt_or_gt_of_ne hne with h | h
    · have := hanti (Set.mem_Ici.mpr hXμ.1.le) (Set.mem_Ici.mpr hY0.le) h; linarith [hXμ.2]
    · have := hanti (Set.mem_Ici.mpr hY0.le) (Set.mem_Ici.mpr hXμ.1.le) h; linarith [hXμ.2]
  have hLat : HasDerivAt L Hd⁻¹ ((fun μ : ℝ => μ ^ c) 1) := by
    simp only [one_rpow]; exact hL.hasDerivAt
  have hcomp := hLat.comp (1 : ℝ) hpw
  have hY : HasDerivAt Y (1 * L ((1 : ℝ) ^ c) + 1 * (Hd⁻¹ * c)) 1 := by
    have := (hasDerivAt_id' (1 : ℝ)).mul hcomp
    convert this using 1 <;> rfl
  have hfin := hY.congr_of_eventuallyEq hXY
  convert hfin using 1
  rw [one_rpow, hL1, hHd_def, hc, ha_def]
  have : 0 < β + (1 - β) * expo γ ε := by positivity
  field_simp
  ring

/-- (99) in logarithms (O&R (99), `p_T = e`): `d log x / d log μ = [β+(1−β)ε]/[β+(1−β)(1−γ+γε)]`
at `μ = 1`. -/
theorem hasDerivAt_log_impact {β γ ε : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hγ0 : 0 < γ)
    (hγ1 : γ < 1) (hε : 0 < ε) {X : ℝ → ℝ}
    (hX : ∀ᶠ μ in 𝓝 1, 0 < X μ ∧ impactGap β γ ε μ (X μ) = 0) (hX1 : X 1 = 1) :
    HasDerivAt (fun m => log (X (exp m))) ((β + (1 - β) * ε) / (β + (1 - β) * expo γ ε)) 0 := by
  have hd := hasDerivAt_impact hβ hβ1 hγ0 hγ1 hε hX
  have hd' : HasDerivAt X ((β + (1 - β) * ε) / (β + (1 - β) * expo γ ε)) (exp 0) := by
    rw [exp_zero]; exact hd
  have h1 := (hd'.comp 0 (hasDerivAt_exp 0)).log (by simp [hX1])
  convert h1 using 1 <;> first | rfl | simp [hX1]

/-- The coefficient in (99) exceeds one iff `ε > 1` (overshooting, O&R p. 693). -/
theorem coef99_gt_one_iff {β γ ε : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hε : 0 < ε) :
    1 < (β + (1 - β) * ε) / (β + (1 - β) * expo γ ε) ↔ 1 < ε := by
  have ha := expo_pos hγ0 hγ1 hε
  have hden : 0 < β + (1 - β) * expo γ ε := by
    have : 0 < 1 - β := by linarith
    positivity
  rw [one_lt_div hden, ← expo_lt_iff hγ1]
  have : 0 < 1 - β := by linarith
  constructor <;> intro h <;> nlinarith

/-- The log-linear system (96)–(98) implies (99) (O&R pp. 693): with `p = γ p_T` (97) and
`p̄_T = m` (98), `ε(m − p) = p_T − p + (β/(1−β))(p_T − p̄_T)` (96) holds IFF
`p_T = [β + (1−β)ε] m / [β + (1−β)(1 − γ + γε)]` (99). -/
theorem loglinear_99 {β γ ε m pT : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hγ0 : 0 < γ) (hγ1 : γ < 1)
    (hε : 0 < ε) :
    ε * (m - γ * pT) = pT - γ * pT + β / (1 - β) * (pT - m) ↔
      pT = (β + (1 - β) * ε) * m / (β + (1 - β) * expo γ ε) := by
  have ha := expo_pos hγ0 hγ1 hε
  have hb : 0 < 1 - β := by linarith
  have hden : 0 < β + (1 - β) * expo γ ε := by positivity
  unfold expo at hden ⊢
  constructor
  · intro h
    field_simp at h
    rw [eq_div_iff hden.ne']
    linear_combination -h
  · intro h
    have h' := (eq_div_iff hden.ne').mp h
    have : (1 : ℝ) - β ≠ 0 := hb.ne'
    field_simp
    linear_combination -h'

/-- (96) is the derivative of the exact log money-demand equation (O&R (96), fn 23). On the
impact path the exact equation (92), relative to the initial steady state, reads
`Φ(m, u) = ε(m − γu) − (1−γ)u + log(1 − βe^{u−m}) − log(1−β) = 0` with `m = log μ`,
`u = log x`. Its derivative in `m` at `(0,0)` is `ε + β/(1−β)`. -/
theorem hasDerivAt_logMoneyDemand_m {β ε : ℝ} (hβ1 : β < 1) :
    HasDerivAt (fun m => ε * m + log (1 - β * exp (-m)) - log (1 - β)) (ε + β / (1 - β)) 0 := by
  have hb : (1 : ℝ) - β * exp (-0) ≠ 0 := by simp; linarith
  have h1 := ((hasDerivAt_neg (0 : ℝ)).exp.const_mul β).const_sub 1
  have h2 := h1.log hb
  have h3 := (((hasDerivAt_id (0 : ℝ)).const_mul ε).add h2).sub_const (log (1 - β))
  convert h3 using 1
  · rfl
  · simp only [neg_zero, exp_zero, mul_one]
    have : (1 : ℝ) - β ≠ 0 := by linarith
    field_simp

/-- (96), derivative in `u` (O&R (96)): `Φ(0, u)` has derivative
`−(εγ + 1 − γ + β/(1−β))` at `u = 0`; together with the derivative in `m`, the linearisation
`(ε + β/(1−β))m = (εγ + 1 − γ + β/(1−β))u` is exactly (96) with (97)–(98). -/
theorem hasDerivAt_logMoneyDemand_u {β γ ε : ℝ} (hβ1 : β < 1) :
    HasDerivAt (fun u => -(ε * γ + (1 - γ)) * u + log (1 - β * exp u) - log (1 - β))
      (-(ε * γ + (1 - γ) + β / (1 - β))) 0 := by
  have hb : (1 : ℝ) - β * exp 0 ≠ 0 := by simp; linarith
  have h1 := ((hasDerivAt_exp (0 : ℝ)).const_mul β).const_sub 1
  have h2 := h1.log hb
  have h3 := (((hasDerivAt_id (0 : ℝ)).const_mul (-(ε * γ + (1 - γ)))).add h2).sub_const
    (log (1 - β))
  convert h3 using 1
  · rfl
  · simp only [exp_zero, mul_one]
    have : (1 : ℝ) - β ≠ 0 := by linarith
    field_simp
    ring


/-! ## The sticky-price equilibrium path -/

/-- Homogeneity of the price index (83): `P(aP_T, bP_N) = a^γ b^{1−γ} P(P_T, P_N)`. -/
theorem cpi_scale {γ a b PT PN : ℝ} (ha : 0 < a) (hb : 0 < b) (hT : 0 < PT) (hN : 0 < PN) :
    cpi γ (a * PT) (b * PN) = a ^ γ * b ^ (1 - γ) * cpi γ PT PN := by
  unfold cpi
  rw [mul_rpow ha.le hT.le, mul_rpow hb.le hN.le]
  ring

/-- The pre-shock steady-state tradables price given `M_0` (O&R §10.2.3, from
`NontradablesModel.steadyState_unique`). -/
noncomputable def pT0 (E : Economy) (M0 : ℝ) : ℝ := M0 / (realMoneyBar E * cpiRatio E)

/-- The pre-shock (and preset) nontradables price `P_{N,0} = (P_N/P_T)‾ P_{T,0}` (O&R p. 692). -/
noncomputable def pN0 (E : Economy) (M0 : ℝ) : ℝ := relPriceBar E * pT0 E M0

/-- `P_{T,0} > 0` (O&R p. 692). -/
theorem pT0_pos {E : Economy} (hE : E.Valid) {M0 : ℝ} (hM0 : 0 < M0) : 0 < pT0 E M0 := by
  have := realMoneyBar_pos hE; have := cpiRatio_pos hE
  unfold pT0; positivity

/-- `P_{N,0} > 0` (O&R p. 692). -/
theorem pN0_pos {E : Economy} (hE : E.Valid) {M0 : ℝ} (hM0 : 0 < M0) : 0 < pN0 E M0 :=
  mul_pos (relPriceBar_pos hE) (pT0_pos hE hM0)

/-- LONG-RUN NEUTRALITY (98), p. 693: the steady-state price level is proportional to money,
`P̄_T(μM_0) = μ P̄_T(M_0)` and likewise `P̄_N` (uniqueness from
`NontradablesModel.steadyState_unique`). -/
theorem longRun_neutral (E : Economy) (M0 μ : ℝ) :
    pT0 E (μ * M0) = μ * pT0 E M0 ∧ pN0 E (μ * M0) = μ * pN0 E M0 := by
  unfold pN0 pT0; constructor <;> ring

/-- The pre-shock consumer price index `P̄_0 = P_{T,0} (P/P_T)‾ = M_0/(M/P)‾` (O&R p. 692). -/
theorem cpi_initial {E : Economy} (hE : E.Valid) {M0 : ℝ} (hM0 : 0 < M0) :
    cpi E.γ (pT0 E M0) (pN0 E M0) = pT0 E M0 * cpiRatio E := by
  have hT := pT0_pos hE hM0
  rw [cpi_eq_mul hT (pN0_pos hE hM0)]
  unfold pN0; rw [mul_div_cancel_right₀ _ hT.ne']; rfl

/-- `((M/P)‾)^{−ε} = γ (P/P_T)‾ (1−β)/(χ ȳ_T)` (O&R (92) in the steady state). -/
theorem realMoneyBar_rpow_neg {E : Economy} (hE : E.Valid) :
    realMoneyBar E ^ (-E.ε) = E.γ * cpiRatio E * (1 - E.β) / (E.χ * E.yT) := by
  have hcr := cpiRatio_pos hE
  obtain ⟨_, hβ1, _, hγ0, _, hχ, hε, _, _, hyT⟩ := hE
  unfold realMoneyBar
  have hb : 0 < 1 - E.β := by linarith
  have hpos : 0 ≤ E.χ / E.γ * (E.yT / cpiRatio E) / (1 - E.β) := by positivity
  rw [← rpow_mul hpos, show 1 / E.ε * -E.ε = -1 by field_simp, rpow_neg_one]
  field_simp

/-- The price paths after an unanticipated permanent money shock `M = μM_0` at book date 1
(Lean date 0): `P_T = xP_{T,0}` then `μP_{T,0}`; `P_N` preset at `P_{N,0}` then `μP_{N,0}`;
aggregate nontradables demand `xȳ_N` then `ȳ_N`; seignorage rebated (O&R §10.2.4, pp. 692–693).
-/
noncomputable def shockPrices (E : Economy) (M0 μ x : ℝ) : Prices :=
  ⟨fun t => if t = 0 then x * pT0 E M0 else μ * pT0 E M0,
    fun t => if t = 0 then pN0 E M0 else μ * pN0 E M0,
    fun t => if t = 0 then x * ybarN E else ybarN E,
    fun t => if t = 0 then -(μ * M0 - M0) / (x * pT0 E M0) else 0⟩

/-- The allocation on the shock path: `C_T = ȳ_T` always, `C_N = y_N = xȳ_N` on impact (95) and
`ȳ_N` afterwards, money `μM_0` (O&R (94)–(95), p. 693). -/
noncomputable def shockChoice (E : Economy) (M0 μ x : ℝ) : ℕ → Choice :=
  fun t => if t = 0 then ⟨E.yT, x * ybarN E, μ * M0, x * ybarN E⟩
    else ⟨E.yT, ybarN E, μ * M0, ybarN E⟩

/-- Net resources with the nontradables price PRESET at date 0: each producer sells `y` at the
common preset price `P_N`, so real revenue is `(P_N/P_T) y` (O&R p. 692). -/
noncomputable def stickyNetRes (E : Economy) (Q : Prices) (t : ℕ) (c : Choice) : ℝ :=
  if t = 0 then E.yT - Q.τ 0 + relPrice Q 0 * c.y - relPrice Q 0 * c.cN - c.cT
    - c.money * userCost E.r Q 0
  else netRes E Q t c

/-- Admissible choices with a preset price at date 0: at the common preset price demand is
`C^A_N` (CES demand at `p_N = P_N`), and a producer may sell any quantity up to demand
(O&R p. 692, "output is demand determined"). -/
def stickySet (Q : Prices) (t : ℕ) : Set Choice :=
  if t = 0 then {c | c ∈ posChoice ∧ c.y ≤ Q.CA 0} else posChoice

/-- Household optimality with the nontradables price preset at date 0 (O&R §10.2.4). -/
def StickyOptimal (E : Economy) (Q : Prices) (B0 Mm1 : ℝ) (c : ℕ → Choice) : Prop :=
  IsOptimal E.β E.r (initWealth E Q B0 Mm1) (periodU E Q) (stickyNetRes E Q) (stickySet Q) c

/-- A symmetric equilibrium with the preset price at date 0 (O&R §10.2.4): households optimise,
`y_N = C_N = C^A_N`, the money market clears and seignorage is rebated (85). -/
def IsStickyEquilibrium (E : Economy) (Q : Prices) (B0 Mm1 : ℝ) (M : ℕ → ℝ)
    (c : ℕ → Choice) : Prop :=
  StickyOptimal E Q B0 Mm1 c ∧ (∀ t, (c t).y = (c t).cN ∧ Q.CA t = (c t).cN) ∧
    (∀ t, (c t).money = M t) ∧ ∀ t, Q.τ t = -(M t - moneyPrev Mm1 c t) / Q.PT t

/-- The user cost of money on the shock path: `(1 − βx/μ)/(xP_{T,0})` on impact and
`(1−β)/(μP_{T,0})` afterwards (O&R (92)). -/
theorem shock_userCost {E : Economy} (hE : E.Valid) (hβr : E.β * (1 + E.r) = 1) {M0 μ x : ℝ}
    (hM0 : 0 < M0) (hμ : 0 < μ) (hx : 0 < x) :
    userCost E.r (shockPrices E M0 μ x) 0 = (1 - E.β * x / μ) / (x * pT0 E M0) ∧
      ∀ t, t ≠ 0 → userCost E.r (shockPrices E M0 μ x) t = (1 - E.β) / (μ * pT0 E M0) := by
  have hT := pT0_pos hE hM0
  obtain ⟨_, _, hr, _, _, _, _, _, _, _⟩ := hE
  have hinv : 1 / (1 + E.r) = E.β := by field_simp; linarith
  refine ⟨?_, fun t ht => ?_⟩
  · simp only [userCost, shockPrices, ↓reduceIte, Nat.add_one_ne_zero]
    have : 1 / ((1 + E.r) * (μ * pT0 E M0)) = E.β / (μ * pT0 E M0) := by
      rw [← hinv]; field_simp
    rw [this]; field_simp
  · simp only [userCost, shockPrices, ht, ↓reduceIte, Nat.add_one_ne_zero]
    have : 1 / ((1 + E.r) * (μ * pT0 E M0)) = E.β / (μ * pT0 E M0) := by
      rw [← hinv]; field_simp
    rw [this]; field_simp

/-- The impact CPI `P_1 = x^γ P̄_0` (O&R (97): `p = γ p_T`, exactly), and `P_t = μP̄_0` later. -/
theorem shock_cpi {E : Economy} (hE : E.Valid) {M0 μ x : ℝ} (hM0 : 0 < M0) (hμ : 0 < μ)
    (hx : 0 < x) :
    cpiAt E (shockPrices E M0 μ x) 0 = x ^ E.γ * (pT0 E M0 * cpiRatio E) ∧
      ∀ t, t ≠ 0 → cpiAt E (shockPrices E M0 μ x) t = μ * (pT0 E M0 * cpiRatio E) := by
  have hT := pT0_pos hE hM0
  have hN := pN0_pos hE hM0
  refine ⟨?_, fun t ht => ?_⟩
  · simp only [cpiAt, shockPrices, ↓reduceIte]
    rw [show pN0 E M0 = 1 * pN0 E M0 by ring, cpi_scale hx one_pos hT hN, one_rpow,
      mul_one, cpi_initial hE hM0]
  · simp only [cpiAt, shockPrices, ht, ↓reduceIte]
    rw [cpi_scale hμ hμ hT hN, ← rpow_add hμ, show E.γ + (1 - E.γ) = 1 by ring, rpow_one,
      cpi_initial hE hM0]

/-- The shock-path prices are admissible whenever `x < μ/β` (positive nominal interest on
impact; O&R (92)). -/
theorem shockPrices_valid {E : Economy} (hE : E.Valid) (hβr : E.β * (1 + E.r) = 1)
    {M0 μ x : ℝ} (hM0 : 0 < M0) (hμ : 0 < μ) (hx : 0 < x) (hxb : x < μ / E.β) :
    (shockPrices E M0 μ x).Valid E.r := by
  have hT := pT0_pos hE hM0
  have hN := pN0_pos hE hM0
  have hy := ybarN_pos hE
  obtain ⟨hu0, hu⟩ := shock_userCost hE hβr hM0 hμ hx
  have hβ := hE.1
  have hβ1 := hE.2.1
  intro t
  by_cases ht : t = 0
  · subst ht
    refine ⟨by simp only [shockPrices, ↓reduceIte]; positivity,
      by simp only [shockPrices, ↓reduceIte]; positivity,
      by simp only [shockPrices, ↓reduceIte]; positivity, ?_⟩
    rw [hu0]
    apply div_pos _ (by positivity)
    rw [sub_pos, div_lt_one hμ]
    rw [lt_div_iff₀ hβ] at hxb; linarith
  · refine ⟨by simp only [shockPrices, ht, ↓reduceIte]; positivity,
      by simp only [shockPrices, ht, ↓reduceIte]; positivity,
      by simp only [shockPrices, ht, ↓reduceIte]; positivity, ?_⟩
    rw [hu t ht]
    exact div_pos (by linarith) (by positivity)


/-- `M_0/P̄_0 = (M/P)‾`: the pre-shock real balances (O&R (92)). -/
theorem M0_div_cpi {E : Economy} (hE : E.Valid) {M0 : ℝ} (hM0 : 0 < M0) :
    M0 / (pT0 E M0 * cpiRatio E) = realMoneyBar E := by
  have := realMoneyBar_pos hE; have := cpiRatio_pos hE
  unfold pT0; field_simp

/-- THE IMPACT MONEY-DEMAND CONDITION IS THE IMPACT EQUATION (O&R (92) at date 1 with `P_N`
preset, `C_T = ȳ_T` and `P_{T,2} = μP_{T,0}`): the money first-order condition on impact holds IFF
`μ^ε(1 − βx/μ) = (1−β)x^{1−γ+γε}`. -/
theorem shock_moneyFOC0_iff {E : Economy} (hE : E.Valid) (hβr : E.β * (1 + E.r) = 1)
    {M0 μ x : ℝ} (hM0 : 0 < M0) (hμ : 0 < μ) (hx : 0 < x) :
    E.χ * (μ * M0 / cpiAt E (shockPrices E M0 μ x) 0) ^ (-E.ε)
        / cpiAt E (shockPrices E M0 μ x) 0
      = E.γ / E.yT * userCost E.r (shockPrices E M0 μ x) 0 ↔
      impactGap E.β E.γ E.ε μ x = 0 := by
  have hT := pT0_pos hE hM0
  have hcr := cpiRatio_pos hE
  have hmb := realMoneyBar_pos hE
  have hmneg := realMoneyBar_rpow_neg hE
  have hmd := M0_div_cpi hE hM0
  obtain ⟨hu0, _⟩ := shock_userCost hE hβr hM0 hμ hx
  obtain ⟨hP0, _⟩ := shock_cpi hE hM0 hμ hx
  obtain ⟨_, _, _, hγ0, _, hχ, hε, _, _, hyT⟩ := hE
  rw [hu0, hP0]
  set u := x ^ E.γ with hu
  have hu0' : 0 < u := rpow_pos_of_pos hx _
  have hμe : 0 < μ ^ E.ε := rpow_pos_of_pos hμ _
  have hrb : μ * M0 / (u * (pT0 E M0 * cpiRatio E)) = μ * realMoneyBar E / u := by
    rw [← hmd]; field_simp
  rw [hrb]
  have hpow : (μ * realMoneyBar E / u) ^ (-E.ε)
      = u ^ E.ε / μ ^ E.ε * realMoneyBar E ^ (-E.ε) := by
    rw [div_rpow (by positivity) hu0'.le, mul_rpow hμ.le hmb.le]
    simp only [rpow_neg hu0'.le, rpow_neg hμ.le]
    field_simp
  rw [hpow, hmneg]
  have hxa : x ^ expo E.γ E.ε = x / u * u ^ E.ε := by
    unfold expo
    rw [hu, ← rpow_mul hx.le, show 1 - E.γ + E.γ * E.ε = 1 - E.γ + E.γ * E.ε by rfl,
      rpow_add hx, rpow_sub hx, rpow_one]
  set K := E.γ / (E.yT * x * pT0 E M0 * μ ^ E.ε) with hK
  have hKpos : 0 < K := by positivity
  have hL : E.χ * (u ^ E.ε / μ ^ E.ε * (E.γ * cpiRatio E * (1 - E.β) / (E.χ * E.yT)))
      / (u * (pT0 E M0 * cpiRatio E)) = K * ((1 - E.β) * x ^ expo E.γ E.ε) := by
    rw [hxa, hK]; field_simp
  have hR : E.γ / E.yT * ((1 - E.β * x / μ) / (x * pT0 E M0))
      = K * (μ ^ E.ε * (1 - E.β * x / μ)) := by
    rw [hK]; field_simp
  rw [hL, hR]
  unfold impactGap
  constructor
  · intro h
    have := mul_left_cancel₀ hKpos.ne' h
    linarith
  · intro h
    congr 1; linarith

/-- The date-0 Lagrangian inequality with the price PRESET (O&R §10.2.4): if (89) and the money
condition hold and the preset price is at least ex post marginal cost,
`κ y_N ≤ (γ/C_T)(P_N/P_T)`, then selling the full demand maximises the date-0 Lagrangian over
all admissible choices (including rationing, `y ≤ C^A_N`). -/
theorem stickyLagrangian_le {E : Economy} (hE : E.Valid) (Q : Prices)
    (hQ0 : 0 < Q.PT 0 ∧ 0 < Q.PN 0 ∧ 0 < Q.CA 0 ∧ 0 < userCost E.r Q 0) {c y : Choice}
    (hc : c ∈ posChoice) (hy : y ∈ stickySet Q 0) (hcy : c.y = Q.CA 0)
    (hN : (1 - E.γ) / c.cN = E.γ / c.cT * relPrice Q 0)
    (hM : E.χ * (c.money / cpiAt E Q 0) ^ (-E.ε) / cpiAt E Q 0
      = E.γ / c.cT * userCost E.r Q 0)
    (hMC : E.κ * c.y ≤ E.γ / c.cT * relPrice Q 0) :
    periodU E Q 0 y + E.γ / c.cT * stickyNetRes E Q 0 y
      ≤ periodU E Q 0 c + E.γ / c.cT * stickyNetRes E Q 0 c := by
  obtain ⟨_, _, _, hγ0, hγ1, hχ, hε, hκ, _, _⟩ := hE
  obtain ⟨hT, hPN, hA, _⟩ := hQ0
  obtain ⟨ha, hb, hn, hq⟩ := hc
  simp only [stickySet, ↓reduceIte, Set.mem_ofPred_eq] at hy
  obtain ⟨⟨ha', hb', hn', hq'⟩, hyle⟩ := hy
  have hP : 0 < cpiAt E Q 0 := cpi_pos hγ0 hγ1 hT hPN
  set lam := E.γ / c.cT with hlam
  set ρ := relPrice Q 0
  set P := cpiAt E Q 0
  have hA' := log_tangent hγ0.le ha' ha
  have hB' := log_tangent (k := 1 - E.γ) (by linarith) hb' hb
  have hBr : (1 - E.γ) / c.cN = lam * ρ := hN
  have hC' := moneyU_le_tangent hχ.le hε (div_pos hn hP) (div_pos hn' hP) (χ := E.χ)
  have hCr : E.χ * (c.money / P) ^ (-E.ε) * (y.money / P - c.money / P)
      = lam * userCost E.r Q 0 * (y.money - c.money) := by
    rw [← hM]; field_simp
  have hD : -(E.κ / 2) * y.y ^ 2 + lam * ρ * y.y ≤ -(E.κ / 2) * c.y ^ 2 + lam * ρ * c.y := by
    have h1 : y.y ≤ c.y := hcy ▸ hyle
    have e : (-(E.κ / 2) * c.y ^ 2 + lam * ρ * c.y) - (-(E.κ / 2) * y.y ^ 2 + lam * ρ * y.y)
        = (c.y - y.y) * (lam * ρ - E.κ / 2 * (c.y + y.y)) := by ring
    have h2 : 0 ≤ lam * ρ - E.κ / 2 * (c.y + y.y) := by nlinarith
    nlinarith [mul_nonneg (sub_nonneg.mpr h1) h2]
  simp only [periodU, stickyNetRes, ↓reduceIte]
  rw [hBr] at hB'
  have e1 : (1 - E.γ) / c.cN * y.cN = lam * ρ * y.cN := by rw [hBr]
  have e2 : (1 - E.γ) / c.cN * c.cN = lam * ρ * c.cN := by rw [hBr]
  linarith [hA', hB', hC', hCr, hD, e1, e2]

/-- On the shock path the preset price is at least ex post marginal cost IFF
`x² ≤ θ/(θ−1)` (O&R p. 674, p. 692: the exact range in which output is demand-determined). -/
theorem shock_markup_iff {E : Economy} (hE : E.Valid) {M0 μ x : ℝ} (hM0 : 0 < M0) (hx : 0 < x) :
    E.κ * (x * ybarN E) ≤ E.γ / E.yT * relPrice (shockPrices E M0 μ x) 0 ↔
      x ^ 2 ≤ E.θ / (E.θ - 1) := by
  have hT := pT0_pos hE hM0
  have hy := ybarN_pos hE
  have hk := kappa_mul_ybarN_sq hE
  obtain ⟨_, _, _, hγ0, hγ1, _, _, hκ, hθ, hyT⟩ := hE
  have e : E.γ / E.yT * relPrice (shockPrices E M0 μ x) 0 = (1 - E.γ) / (x * ybarN E) := by
    simp only [relPrice, shockPrices, ↓reduceIte, pN0, relPriceBar]
    field_simp
  rw [e, le_div_iff₀ (by positivity : 0 < x * ybarN E),
    le_div_iff₀ (by linarith : 0 < E.θ - 1)]
  have e2 : E.κ * (x * ybarN E) * (x * ybarN E) = x ^ 2 * ((E.θ - 1) * (1 - E.γ) / E.θ) := by
    rw [← hk]; ring
  rw [e2]
  have h1 : 0 < 1 - E.γ := by linarith
  have h2 : 0 < E.θ := by linarith
  have e3 : x ^ 2 * ((E.θ - 1) * (1 - E.γ) / E.θ) = (x ^ 2 * (E.θ - 1)) * (1 - E.γ) / E.θ := by
    ring
  rw [e3, div_le_iff₀ h2]
  constructor
  · intro h; nlinarith
  · intro h; nlinarith


/-- With `β(1+r) = 1` the market discount factor is `β^t` (O&R p. 690). -/
theorem disc_eq_pow {E : Economy} (hβr : E.β * (1 + E.r) = 1) (t : ℕ) : disc E.r t = E.β ^ t := by
  have hb : E.β = (1 + E.r)⁻¹ := by
    have h : (1 + E.r) ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hβr; exact zero_ne_one hβr
    field_simp; linarith
  simp [disc, hb, inv_pow]

/-- The intratemporal condition (89) on the shock path, at every date (O&R (95)). -/
theorem shock_intra {E : Economy} (hE : E.Valid) {M0 μ x : ℝ} (hM0 : 0 < M0) (hμ : 0 < μ)
    (hx : 0 < x) (t : ℕ) :
    (1 - E.γ) / (shockChoice E M0 μ x t).cN
      = E.γ / (shockChoice E M0 μ x t).cT * relPrice (shockPrices E M0 μ x) t := by
  have hT := pT0_pos hE hM0
  have hy := ybarN_pos hE
  obtain ⟨_, _, _, hγ0, hγ1, _, _, _, _, hyT⟩ := hE
  by_cases ht : t = 0
  · subst ht
    simp only [shockChoice, shockPrices, relPrice, ↓reduceIte, pN0, relPriceBar]
    field_simp
  · simp only [shockChoice, shockPrices, relPrice, ht, ↓reduceIte, pN0, relPriceBar]
    field_simp

/-- The money condition on the shock path after impact (the new steady state), O&R (92). -/
theorem shock_money_later {E : Economy} (hE : E.Valid) (hβr : E.β * (1 + E.r) = 1)
    {M0 μ x : ℝ} (hM0 : 0 < M0) (hμ : 0 < μ) (hx : 0 < x) {t : ℕ} (ht : t ≠ 0) :
    E.χ * ((shockChoice E M0 μ x t).money / cpiAt E (shockPrices E M0 μ x) t) ^ (-E.ε)
        / cpiAt E (shockPrices E M0 μ x) t
      = E.γ / (shockChoice E M0 μ x t).cT * userCost E.r (shockPrices E M0 μ x) t := by
  have hT := pT0_pos hE hM0
  have hcr := cpiRatio_pos hE
  have hmneg := realMoneyBar_rpow_neg hE
  have hmd := M0_div_cpi hE hM0
  obtain ⟨_, hu⟩ := shock_userCost hE hβr hM0 hμ hx
  obtain ⟨_, hP⟩ := shock_cpi hE hM0 hμ hx
  obtain ⟨_, _, _, hγ0, _, hχ, _, _, _, hyT⟩ := hE
  rw [hu t ht, hP t ht]
  simp only [shockChoice, ht, ↓reduceIte]
  rw [show μ * M0 / (μ * (pT0 E M0 * cpiRatio E)) = M0 / (pT0 E M0 * cpiRatio E) by
    field_simp, hmd, hmneg]
  field_simp

/-- The output condition on the shock path after impact (the new steady state), O&R (90). -/
theorem shock_labour_later {E : Economy} (hE : E.Valid) {M0 μ x : ℝ} (hM0 : 0 < M0)
    (hμ : 0 < μ) {t : ℕ} (ht : t ≠ 0) :
    E.κ * (shockChoice E M0 μ x t).y = E.γ / (shockChoice E M0 μ x t).cT
      * relPrice (shockPrices E M0 μ x) t * ((E.θ - 1) / E.θ *
        ((shockChoice E M0 μ x t).y ^ ((E.θ - 1) / E.θ - 1)
          * (shockPrices E M0 μ x).CA t ^ (1 / E.θ))) := by
  have hT := pT0_pos hE hM0
  have hy := ybarN_pos hE
  have hk := kappa_mul_ybarN_sq hE
  obtain ⟨_, _, _, hγ0, hγ1, _, _, _, hθ, hyT⟩ := hE
  simp only [shockChoice, shockPrices, relPrice, ht, ↓reduceIte, pN0]
  rw [← rpow_add hy, show (E.θ - 1) / E.θ - 1 + 1 / E.θ = 0 by field_simp; ring, rpow_zero,
    mul_one, show μ * (relPriceBar E * pT0 E M0) / (μ * pT0 E M0) = relPriceBar E by
      field_simp]
  unfold relPriceBar
  field_simp at hk ⊢
  linarith

/-- Wealth on the shock path: `A_t = M_0/P_{T,0}` for every `t ≥ 1` (bonds stay zero; O&R (91)). -/
theorem shock_wealth {E : Economy} (hE : E.Valid) (hβr : E.β * (1 + E.r) = 1) {M0 μ x : ℝ}
    (hM0 : 0 < M0) (hμ : 0 < μ) (hx : 0 < x) {t : ℕ} (ht : 1 ≤ t) :
    wealth E.r (initWealth E (shockPrices E M0 μ x) 0 M0) (stickyNetRes E (shockPrices E M0 μ x))
      (shockChoice E M0 μ x) t = M0 / pT0 E M0 := by
  have hT := pT0_pos hE hM0
  have hy := ybarN_pos hE
  obtain ⟨hu0, hu⟩ := shock_userCost hE hβr hM0 hμ hx
  have hr := hE.2.2.1
  have hθ := hE.2.2.2.2.2.2.2.2.1
  induction t, ht using Nat.le_induction with
  | base =>
    have e : initWealth E (shockPrices E M0 μ x) 0 M0
        + stickyNetRes E (shockPrices E M0 μ x) 0 (shockChoice E M0 μ x 0)
        = E.β * (M0 / pT0 E M0) := by
      simp only [initWealth, stickyNetRes, ↓reduceIte]
      rw [hu0]
      simp only [shockChoice, shockPrices, relPrice, ↓reduceIte]
      field_simp
      ring
    change (1 + E.r) * (initWealth E (shockPrices E M0 μ x) 0 M0
      + stickyNetRes E (shockPrices E M0 μ x) 0 (shockChoice E M0 μ x 0)) = _
    rw [e, ← mul_assoc, mul_comm (1 + E.r), hβr, one_mul]
  | succ t ht ih =>
    have ht0 : t ≠ 0 := by omega
    rw [wealth, ih]
    have e : M0 / pT0 E M0 + stickyNetRes E (shockPrices E M0 μ x) t (shockChoice E M0 μ x t)
        = E.β * (M0 / pT0 E M0) := by
      simp only [stickyNetRes, ht0, ↓reduceIte, netRes]
      rw [hu t ht0]
      simp only [shockChoice, ht0, ↓reduceIte]
      rw [realRevenue_symm E (shockPrices E M0 μ x) t (by linarith) hy
        (by simp [shockPrices, ht0])]
      simp only [shockPrices, ht0, ↓reduceIte]
      field_simp
      ring
    rw [e, ← mul_assoc, mul_comm (1 + E.r), hβr, one_mul]

/-- EXISTENCE OF THE STICKY-PRICE EQUILIBRIUM (O&R §10.2.4, pp. 692–693, exact): if `x` solves
the impact equation and `x² ≤ θ/(θ−1)`, the shock path — `P_{T,1} = xP_{T,0}`, `P_N` preset,
`C_N = y_N = xȳ_N`, and the new steady state `μ×` the old one from date 2 — is a genuine
infinite-horizon equilibrium: households optimise over ALL plans (including rationing at the
preset price) subject to no-Ponzi, markets clear and seignorage is rebated. -/
theorem shock_isStickyEquilibrium {E : Economy} (hE : E.Valid) (hβr : E.β * (1 + E.r) = 1)
    {M0 μ x : ℝ} (hM0 : 0 < M0) (hμ : 0 < μ) (hx : 0 < x)
    (hF : impactGap E.β E.γ E.ε μ x = 0) (hdd : x ^ 2 ≤ E.θ / (E.θ - 1)) :
    (shockPrices E M0 μ x).Valid E.r ∧
      IsStickyEquilibrium E (shockPrices E M0 μ x) 0 M0 (fun _ => μ * M0)
        (shockChoice E M0 μ x) := by
  have hE' := hE
  obtain ⟨hβ, hβ1, hr, hγ0, hγ1, hχ, hε, hκ, hθ, hyT⟩ := hE'
  have hr0 : 0 < E.r := by nlinarith
  have hT := pT0_pos hE hM0
  have hy := ybarN_pos hE
  have hxb := root_lt hβ hβ1 hγ0 hγ1 hε hμ hx hF
  have hQ := shockPrices_valid hE hβr hM0 hμ hx hxb
  set Q := shockPrices E M0 μ x with hQdef
  set c := shockChoice E M0 μ x with hcdef
  have hc : ∀ t, c t ∈ posChoice := by
    intro t
    by_cases ht : t = 0
    · subst ht; simp only [c, shockChoice, ↓reduceIte]
      exact ⟨hyT, by positivity, by positivity, by positivity⟩
    · simp only [c, shockChoice, ht, ↓reduceIte]
      exact ⟨hyT, hy, by positivity, hy⟩
  have hadm : ∀ t, c t ∈ stickySet Q t := by
    intro t
    by_cases ht : t = 0
    · subst ht
      simp only [stickySet, ↓reduceIte, Set.mem_ofPred_eq]
      refine ⟨hc 0, ?_⟩
      simp [c, shockChoice, Q, shockPrices]
    · simp only [stickySet, ht, ↓reduceIte]; exact hc t
  -- summability
  have hsum : Summable fun t => E.β ^ t * periodU E Q t (c t) := by
    have hconst : ∀ t ∉ ({0} : Finset ℕ), E.β ^ t * periodU E Q t (c t)
        = E.β ^ t * periodU E Q 1 (c 1) := by
      intro t ht
      have ht0 : t ≠ 0 := by simpa using ht
      simp only [periodU, cpiAt, c, Q, shockChoice, shockPrices, ht0, ↓reduceIte,
        Nat.one_ne_zero]
    exact (tsum_eq_add_of_eq_off
      ((summable_geometric_of_lt_one hβ.le hβ1).mul_right (periodU E Q 1 (c 1))) {0}
      hconst).1
  -- wealth, no-Ponzi, transversality
  have hdw : Tendsto (fun T => disc E.r T
      * wealth E.r (initWealth E Q 0 M0) (stickyNetRes E Q) c T) atTop (𝓝 0) := by
    have h0 : Tendsto (fun T => disc E.r T * (M0 / pT0 E M0)) atTop (𝓝 0) := by
      simpa using (tendsto_disc hr0).mul_const (M0 / pT0 E M0)
    refine h0.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with T hT1
    rw [shock_wealth hE hβr hM0 hμ hx hT1]
  have hnp : NoPonzi E.r (wealth E.r (initWealth E Q 0 M0) (stickyNetRes E Q) c) :=
    fun δ hδ => (hdw.eventually (lt_mem_nhds (by linarith : -δ < 0))).mono fun _ h => h.le
  have htv : LiminfNonpos E.r (wealth E.r (initWealth E Q 0 M0) (stickyNetRes E Q) c) :=
    fun δ hδ => (hdw.eventually (gt_mem_nhds hδ)).frequently.mono fun _ h => h.le
  -- the saddle condition
  have hsad : ∀ t, ∀ y ∈ stickySet Q t, E.β ^ t * periodU E Q t y
      + E.γ / E.yT * (disc E.r t * stickyNetRes E Q t y)
      ≤ E.β ^ t * periodU E Q t (c t) + E.γ / E.yT * (disc E.r t * stickyNetRes E Q t (c t)) := by
    intro t y hyS
    rw [disc_eq_pow hβr]
    have hβt : 0 ≤ E.β ^ t := pow_nonneg hβ.le t
    have hcT : (c t).cT = E.yT := by
      by_cases ht : t = 0
      · subst ht; simp [c, shockChoice]
      · simp [c, shockChoice, ht]
    have key : periodU E Q t y + E.γ / E.yT * stickyNetRes E Q t y
        ≤ periodU E Q t (c t) + E.γ / E.yT * stickyNetRes E Q t (c t) := by
      by_cases ht : t = 0
      · subst ht
        have h1 := stickyLagrangian_le hE Q (hQ 0) (hc 0) hyS
          (by simp [c, shockChoice, Q, shockPrices]) (shock_intra hE hM0 hμ hx 0)
          (by
            have := (shock_moneyFOC0_iff hE hβr hM0 hμ hx).mpr hF
            simpa [c, shockChoice, Q] using this)
          (by
            have := (shock_markup_iff hE (μ := μ) hM0 hx).mpr hdd
            simpa [c, shockChoice, Q] using this)
        rw [hcT] at h1
        exact h1
      · have hyS' : y ∈ posChoice := by simpa [stickySet, ht] using hyS
        have h1 := periodLagrangian_le E Q hE hQ t (hc t) hyS' (shock_intra hE hM0 hμ hx t)
          (shock_money_later hE hβr hM0 hμ hx ht) (shock_labour_later hE hM0 hμ ht)
        rw [hcT] at h1
        simpa [stickyNetRes, ht] using h1
    have := mul_le_mul_of_nonneg_left key hβt
    nlinarith
  refine ⟨hQ, isOptimal_of_saddle (μ0 := E.γ / E.yT) hr (div_pos hγ0 hyT).le hadm hsum hnp htv
    hsad, ?_, ?_, ?_⟩
  · intro t
    by_cases ht : t = 0
    · subst ht; simp [c, shockChoice, Q, shockPrices]
    · simp [c, shockChoice, Q, shockPrices, ht]
  · intro t
    by_cases ht : t = 0
    · subst ht; simp [c, shockChoice]
    · simp [c, shockChoice, ht]
  · intro t
    by_cases ht : t = 0
    · subst ht; simp [Q, shockPrices, moneyPrev]
    · obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero ht
      by_cases hs : s = 0 <;> simp [Q, shockPrices, moneyPrev, c, shockChoice, hs]


/-- A single-date perturbation that keeps net resources weakly higher cannot raise date-`t`
utility at an optimum, for ANY infinite-horizon problem (O&R §10.2.2; generic form of
`NontradablesModel.isLocalMax_of_perturb`), stated on a set `s` of perturbation sizes. -/
theorem perturb_le_gen {X : Type*} {β r A0 : ℝ} (hr : 0 < 1 + r) (hβ : 0 < β)
    {U h : ℕ → X → ℝ} {D : ℕ → Set X} {c : ℕ → X} (hopt : IsOptimal β r A0 U h D c) (t : ℕ)
    (g : ℝ → X) {η : ℝ} (hη : g η ∈ D t) (hres : h t (c t) ≤ h t (g η)) :
    U t (g η) ≤ U t (c t) := by
  set x' : ℕ → X := Function.update c t (g η)
  have hS : ∀ s ∉ ({t} : Finset ℕ), x' s = c s := by
    intro s hs
    simp only [Finset.mem_singleton] at hs
    simp [x', Function.update_of_ne hs]
  have hx' : ∀ s, x' s ∈ D s := by
    intro s
    by_cases hs : s = t
    · subst hs; simpa [x'] using hη
    · rw [hS s (by simpa using hs)]; exact hopt.1 s
  have hpv : 0 ≤ ∑ s ∈ ({t} : Finset ℕ), disc r s * (h s (x' s) - h s (c s)) := by
    simp only [Finset.sum_singleton, x', Function.update_self]
    exact mul_nonneg (disc_pos hr t).le (by linarith)
  have hh := perturb_utility_le_of_pv hr hopt hx' hS hpv
  simp only [Finset.sum_singleton, x', Function.update_self] at hh
  have hβt : 0 < β ^ t := pow_pos hβ t
  nlinarith

/-- NECESSITY (O&R §10.2.4): if the shock path is a sticky-price equilibrium, then `x` solves the
impact equation `μ^ε(1 − βx/μ) = (1−β)x^{1−γ+γε}` (necessity of the money condition on
impact) AND `x² ≤ θ/(θ−1)` (a producer would ration at a preset price below marginal cost). -/
theorem shock_necessary {E : Economy} (hE : E.Valid) (hβr : E.β * (1 + E.r) = 1)
    {M0 μ x : ℝ} (hM0 : 0 < M0) (hμ : 0 < μ) (hx : 0 < x)
    (hQ : (shockPrices E M0 μ x).Valid E.r)
    (heq : IsStickyEquilibrium E (shockPrices E M0 μ x) 0 M0 (fun _ => μ * M0)
      (shockChoice E M0 μ x)) :
    impactGap E.β E.γ E.ε μ x = 0 ∧ x ^ 2 ≤ E.θ / (E.θ - 1) := by
  have hE' := hE
  obtain ⟨hβ, hβ1, hr, hγ0, hγ1, hχ, hε, hκ, hθ, hyT⟩ := hE'
  have hopt := heq.1
  have hy := ybarN_pos hE
  have hT := pT0_pos hE hM0
  set Q := shockPrices E M0 μ x with hQdef
  obtain ⟨hPT, hPN, hCA, hu⟩ := hQ 0
  have hP : 0 < cpiAt E Q 0 := cpi_pos hγ0 hγ1 hPT hPN
  set ι := userCost E.r Q 0
  set P := cpiAt E Q 0
  set ρ := relPrice Q 0
  have hρ : 0 < ρ := div_pos hPN hPT
  have hc0 : shockChoice E M0 μ x 0 = ⟨E.yT, x * ybarN E, μ * M0, x * ybarN E⟩ := by
    simp [shockChoice]
  have hCA0 : Q.CA 0 = x * ybarN E := by simp [Q, shockPrices]
  refine ⟨?_, ?_⟩
  · -- the money perturbation on impact
    set g : ℝ → Choice := fun η => ⟨E.yT - ι * η, x * ybarN E, μ * M0 + η, x * ybarN E⟩
    have hmax : IsLocalMax (fun η => periodU E Q 0 (g η)) 0 := by
      have h1 : ∀ᶠ η in 𝓝 (0 : ℝ), 0 < E.yT - ι * η :=
        (continuous_const.sub (continuous_const.mul continuous_id)).continuousAt.eventually
          (lt_mem_nhds (by simpa using hyT))
      have h2 : ∀ᶠ η in 𝓝 (0 : ℝ), 0 < μ * M0 + η :=
        (continuous_const.add continuous_id).continuousAt.eventually
          (lt_mem_nhds (by simpa using mul_pos hμ hM0))
      filter_upwards [h1, h2] with η e1 e2
      have hmem : g η ∈ stickySet Q 0 := by
        simp only [stickySet, ↓reduceIte, Set.mem_ofPred_eq, g, hCA0]
        exact ⟨⟨e1, by positivity, e2, by positivity⟩, le_rfl⟩
      have hres : stickyNetRes E Q 0 (shockChoice E M0 μ x 0) ≤ stickyNetRes E Q 0 (g η) := by
        rw [hc0]; simp only [stickyNetRes, ↓reduceIte, g]; linarith
      have := perturb_le_gen hr hβ hopt 0 g hmem hres
      rw [hc0] at this
      have hg0 : g 0 = ⟨E.yT, x * ybarN E, μ * M0, x * ybarN E⟩ := by simp [g]
      simp only [hg0]
      exact this
    have hfun : (fun η => periodU E Q 0 (g η)) = fun η =>
        E.γ * log (E.yT - ι * η) + moneyU E.χ E.ε ((μ * M0 + η) / P)
          + ((1 - E.γ) * log (x * ybarN E) - E.κ / 2 * (x * ybarN E) ^ 2) := by
      funext η; simp only [periodU, g]; ring
    have hd1 : HasDerivAt (fun η => E.yT - ι * η) (-ι) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).const_mul ι).const_sub E.yT
    have hd2 : HasDerivAt (fun η => (μ * M0 + η) / P) (1 / P) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).const_add (μ * M0)).div_const P
    have hm : HasDerivAt (fun η => moneyU E.χ E.ε ((μ * M0 + η) / P))
        (E.χ * ((μ * M0) / P) ^ (-E.ε) * (1 / P)) 0 := by
      have := (hasDerivAt_moneyU E.χ E.ε (z := (μ * M0 + 0) / P)
        (by simpa using div_pos (mul_pos hμ hM0) hP)).comp (0 : ℝ) hd2
      convert this using 1 <;> first | rfl | simp
    have hd : HasDerivAt (fun η => periodU E Q 0 (g η))
        (E.γ * (-ι / E.yT) + E.χ * ((μ * M0) / P) ^ (-E.ε) * (1 / P)) 0 := by
      rw [hfun]
      have e1 := (hd1.log (by simpa using hyT.ne')).const_mul E.γ
      simp only [mul_zero, sub_zero] at e1
      exact (e1.add hm).add_const _
    have h0 := hmax.hasDerivAt_eq_zero hd
    have hfoc : E.χ * (μ * M0 / P) ^ (-E.ε) / P = E.γ / E.yT * ι := by
      field_simp at h0 ⊢; linarith
    exact (shock_moneyFOC0_iff hE hβr hM0 hμ hx).mp hfoc
  · -- cutting output at the preset price is always feasible
    set g : ℝ → Choice := fun η => ⟨E.yT + ρ * η, x * ybarN E, μ * M0, x * ybarN E + η⟩
    have hmaxOn : IsLocalMaxOn (fun η => periodU E Q 0 (g η)) (Set.Iic 0) 0 := by
      have h1 : ∀ᶠ η in 𝓝 (0 : ℝ), 0 < E.yT + ρ * η :=
        (continuous_const.add (continuous_const.mul continuous_id)).continuousAt.eventually
          (lt_mem_nhds (by simpa using hyT))
      have h2 : ∀ᶠ η in 𝓝 (0 : ℝ), 0 < x * ybarN E + η :=
        (continuous_const.add continuous_id).continuousAt.eventually
          (lt_mem_nhds (by simpa using mul_pos hx hy))
      have h12 := (h1.and h2)
      filter_upwards [nhdsWithin_le_nhds h12, self_mem_nhdsWithin] with η ⟨e1, e2⟩ e3
      simp only [Set.mem_Iic] at e3
      have hmem : g η ∈ stickySet Q 0 := by
        simp only [stickySet, ↓reduceIte, Set.mem_ofPred_eq, g, hCA0]
        exact ⟨⟨e1, by positivity, by positivity, e2⟩, by linarith⟩
      have hres : stickyNetRes E Q 0 (shockChoice E M0 μ x 0) ≤ stickyNetRes E Q 0 (g η) := by
        rw [hc0]; simp only [stickyNetRes, ↓reduceIte, g]; linarith
      have := perturb_le_gen hr hβ hopt 0 g hmem hres
      rw [hc0] at this
      have hg0 : g 0 = ⟨E.yT, x * ybarN E, μ * M0, x * ybarN E⟩ := by simp [g]
      simp only [hg0]
      exact this
    have hfun : (fun η => periodU E Q 0 (g η)) = fun η =>
        E.γ * log (E.yT + ρ * η) - E.κ / 2 * (x * ybarN E + η) ^ 2
          + ((1 - E.γ) * log (x * ybarN E) + moneyU E.χ E.ε (μ * M0 / P)) := by
      funext η; simp only [periodU, g]; ring
    have hd1 : HasDerivAt (fun η => E.yT + ρ * η) ρ 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).const_mul ρ).const_add E.yT
    have hsq : HasDerivAt (fun η => (x * ybarN E + η) ^ 2) (2 * (x * ybarN E)) 0 := by
      have := (hasDerivAt_pow 2 (x * ybarN E + 0)).comp (0 : ℝ)
        ((hasDerivAt_id (0 : ℝ)).const_add (x * ybarN E))
      convert this using 1 <;> first | rfl | simp
    have hd : HasDerivAt (fun η => periodU E Q 0 (g η))
        (E.γ * (ρ / E.yT) - E.κ / 2 * (2 * (x * ybarN E))) 0 := by
      rw [hfun]
      have e1 := (hd1.log (by simpa using hyT.ne')).const_mul E.γ
      simp only [mul_zero, add_zero] at e1
      exact (e1.sub (hsq.const_mul (E.κ / 2))).add_const _
    have hcone : (-1 : ℝ) ∈ posTangentConeAt (Set.Iic (0 : ℝ)) 0 :=
      mem_posTangentConeAt_of_segment_subset
        ((convex_Iic (0 : ℝ)).segment_subset (by simp) (by norm_num))
    have hnp := hmaxOn.hasFDerivWithinAt_nonpos hd.hasFDerivAt.hasFDerivWithinAt hcone
    have hnp' : -(E.γ * (ρ / E.yT) - E.κ / 2 * (2 * (x * ybarN E))) ≤ 0 := by
      simpa using hnp
    have hMC : E.κ * (x * ybarN E) ≤ E.γ / E.yT * ρ := by
      have : E.γ * (ρ / E.yT) = E.γ / E.yT * ρ := by ring
      linarith
    exact (shock_markup_iff hE hM0 hx).mp hMC

/-- EXACT CHARACTERISATION (O&R §10.2.4): the shock path is a sticky-price equilibrium IF AND
ONLY IF `x` solves the impact equation and `x² ≤ θ/(θ−1)`. In particular the impact response is
UNIQUE, and it exists iff the unique root of the impact equation lies in the demand-determined
range. -/
theorem shock_equilibrium_iff {E : Economy} (hE : E.Valid) (hβr : E.β * (1 + E.r) = 1)
    {M0 μ x : ℝ} (hM0 : 0 < M0) (hμ : 0 < μ) (hx : 0 < x) :
    ((shockPrices E M0 μ x).Valid E.r ∧
      IsStickyEquilibrium E (shockPrices E M0 μ x) 0 M0 (fun _ => μ * M0)
        (shockChoice E M0 μ x)) ↔
      impactGap E.β E.γ E.ε μ x = 0 ∧ x ^ 2 ≤ E.θ / (E.θ - 1) :=
  ⟨fun ⟨hQ, heq⟩ => shock_necessary hE hβr hM0 hμ hx hQ heq,
    fun ⟨hF, hdd⟩ => shock_isStickyEquilibrium hE hβr hM0 hμ hx hF hdd⟩


/-- "SMALL SHOCKS" MADE PRECISE (O&R pp. 674, 692): for every permanent money shock `μ` close
enough to `1` the sticky-price equilibrium EXISTS (the unique impact response satisfies
`x² < θ/(θ−1)`), and it is unique by `shock_equilibrium_iff`. -/
theorem shock_equilibrium_exists_near_one {E : Economy} (hE : E.Valid)
    (hβr : E.β * (1 + E.r) = 1) {M0 : ℝ} (hM0 : 0 < M0) :
    ∀ᶠ μ in 𝓝 (1 : ℝ), ∃ x, 0 < x ∧ impactGap E.β E.γ E.ε μ x = 0 ∧
      (shockPrices E M0 μ x).Valid E.r ∧
      IsStickyEquilibrium E (shockPrices E M0 μ x) 0 M0 (fun _ => μ * M0)
        (shockChoice E M0 μ x) := by
  have hE' := hE
  obtain ⟨hβ, hβ1, _, hγ0, hγ1, _, hε, _, hθ, _⟩ := hE'
  set xm := sqrt (E.θ / (E.θ - 1)) with hxm
  have hq : 1 < E.θ / (E.θ - 1) := by rw [one_lt_div (by linarith)]; linarith
  have hxm1 : 1 < xm := by
    rw [hxm, lt_sqrt zero_le_one]; simpa using hq
  have hxm0 : 0 < xm := by linarith
  have hF1 : impactGap E.β E.γ E.ε 1 xm < 0 := by
    have h1 : impactGap E.β E.γ E.ε 1 1 = 0 := by rw [impactGap_at_mu one_pos]; simp
    have := impactGap_strictAntiOn hβ hβ1 hγ0 hγ1 hε one_pos (Set.mem_Ici.mpr zero_le_one)
      (Set.mem_Ici.mpr hxm0.le) hxm1
    linarith
  have hcont : ContinuousAt (fun μ => impactGap E.β E.γ E.ε μ xm) 1 := by
    unfold impactGap
    exact ((continuousAt_rpow_const 1 E.ε (Or.inl one_ne_zero)).mul (continuousAt_const.sub
      (continuousAt_const.div continuousAt_id one_ne_zero))).sub continuousAt_const
  filter_upwards [hcont.eventually (gt_mem_nhds hF1), Ioi_mem_nhds (zero_lt_one' ℝ)]
    with μ hFμ hμ
  simp only [Set.mem_Ioi] at hμ
  obtain ⟨x, hx0, _, hx, _⟩ := impact_exists_unique hβ hβ1 hγ0 hγ1 hε hμ
  have hxlt : x < xm := by
    by_contra hle; push Not at hle
    rcases eq_or_lt_of_le hle with he | hlt
    · rw [← he] at hx; linarith
    · have := impactGap_strictAntiOn hβ hβ1 hγ0 hγ1 hε hμ (Set.mem_Ici.mpr hxm0.le)
        (Set.mem_Ici.mpr hx0.le) hlt
      linarith
  have hdd : x ^ 2 ≤ E.θ / (E.θ - 1) := by
    have : x ^ 2 < xm ^ 2 := by nlinarith
    rw [hxm, sq_sqrt (by linarith)] at this
    exact this.le
  obtain ⟨hQ, heq⟩ := shock_isStickyEquilibrium hE hβr hM0 hμ hx0 hx hdd
  exact ⟨x, hx0, hx, hQ, heq⟩

/-! ## Positive consequences: exchange rate and nontradables output -/

/-- The nominal exchange rate `𝓔 = P_T/P_T^*` with `P_T^*` constant (law of one price,
O&R (83) and p. 693: `p_T = e`). -/
noncomputable def exchangeRate (PTstar PT : ℝ) : ℝ := PT / PTstar

/-- On the shock path `𝓔_1/𝓔_0 = x` and `𝓔_t/𝓔_0 = μ` from date 2 (O&R p. 693, `p_T = e`). -/
theorem shock_exchangeRate {E : Economy} (hE : E.Valid) {M0 μ x PTstar : ℝ} (hM0 : 0 < M0)
    (hs : 0 < PTstar) :
    exchangeRate PTstar ((shockPrices E M0 μ x).PT 0) / exchangeRate PTstar (pT0 E M0) = x ∧
      ∀ t, t ≠ 0 → exchangeRate PTstar ((shockPrices E M0 μ x).PT t)
        / exchangeRate PTstar (pT0 E M0) = μ := by
  have hT := pT0_pos hE hM0
  refine ⟨?_, fun t ht => ?_⟩
  · simp only [exchangeRate, shockPrices, ↓reduceIte]; field_simp
  · simp only [exchangeRate, shockPrices, ht, ↓reduceIte]; field_simp

/-- EXCHANGE-RATE OVERSHOOTING IN EQUILIBRIUM (O&R (99), p. 693, exact): on any sticky-price
equilibrium path after a permanent monetary expansion `μ > 1`, the exchange rate jumps above its
new long-run level (`𝓔_1 > 𝓔̄ = μ𝓔_0`) IF AND ONLY IF `ε > 1`. -/
theorem exchangeRate_overshoots_iff {E : Economy} (hE : E.Valid) (hβr : E.β * (1 + E.r) = 1)
    {M0 μ x PTstar : ℝ} (hM0 : 0 < M0) (hμ : 1 < μ) (hx : 0 < x) (hs : 0 < PTstar)
    (hQ : (shockPrices E M0 μ x).Valid E.r)
    (heq : IsStickyEquilibrium E (shockPrices E M0 μ x) 0 M0 (fun _ => μ * M0)
      (shockChoice E M0 μ x)) :
    exchangeRate PTstar ((shockPrices E M0 μ x).PT 1)
        < exchangeRate PTstar ((shockPrices E M0 μ x).PT 0) ↔ 1 < E.ε := by
  have hμ0 : 0 < μ := by linarith
  have hT := pT0_pos hE hM0
  obtain ⟨hF, _⟩ := shock_necessary hE hβr hM0 hμ0 hx hQ heq
  obtain ⟨hβ, hβ1, _, hγ0, hγ1, _, hε, _, _, _⟩ := hE
  have h := (overshoot_iff hβ hβ1 hγ0 hγ1 hε hμ hx hF).1
  simp only [exchangeRate, shockPrices, Nat.one_ne_zero, ↓reduceIte]
  rw [div_lt_div_iff_of_pos_right hs, mul_lt_mul_iff_left₀ hT]
  exact h

/-- (95), p. 693: on impact nontradables consumption and output rise by the factor `x > 1`
(`C_N = y_N = xȳ_N`), and tradables consumption is unchanged (O&R (91)). -/
theorem shock_output_rises {E : Economy} (hE : E.Valid) {M0 μ x : ℝ} (hβ : 0 < E.β)
    (hβ1 : E.β < 1) (hμ : 1 < μ) (hx : 0 < x) (hF : impactGap E.β E.γ E.ε μ x = 0) :
    (shockChoice E M0 μ x 0).cN = x * ybarN E ∧ (shockChoice E M0 μ x 0).y = x * ybarN E ∧
      ybarN E < (shockChoice E M0 μ x 0).y ∧ (shockChoice E M0 μ x 0).cT = E.yT := by
  have hy := ybarN_pos hE
  obtain ⟨_, _, _, hγ0, hγ1, _, hε, _, _, _⟩ := hE
  have hx1 := one_lt_root hβ hβ1 hγ0 hγ1 hε hμ hx hF
  exact ⟨by simp [shockChoice], by simp [shockChoice],
    by simp only [shockChoice, ↓reduceIte]; nlinarith, by simp [shockChoice]⟩

/-- (95), p. 693, exactly: on impact `y_N = C_N = ((1−γ)/γ)(P_{T,1}/P̄_{N,0}) ȳ_T`, with the
nontradables price preset at its pre-shock level. -/
theorem shock_95 {E : Economy} (hE : E.Valid) {M0 μ x : ℝ} (hM0 : 0 < M0) :
    (shockChoice E M0 μ x 0).cN
      = (1 - E.γ) / E.γ * ((shockPrices E M0 μ x).PT 0 / (shockPrices E M0 μ x).PN 0) * E.yT ∧
      (shockChoice E M0 μ x 0).y = (shockChoice E M0 μ x 0).cN := by
  have hT := pT0_pos hE hM0
  have hy := ybarN_pos hE
  obtain ⟨_, _, _, hγ0, hγ1, _, _, _, _, hyT⟩ := hE
  refine ⟨?_, by simp [shockChoice]⟩
  simp only [shockChoice, shockPrices, ↓reduceIte, pN0, relPriceBar]
  have : (1 : ℝ) - E.γ ≠ 0 := by linarith
  field_simp

/-! ## Welfare (p. 694) -/

/-- The real-utility gain on impact, `(1−γ)[log x − ((θ−1)/(2θ))(x² − 1)]` (O&R p. 694). -/
noncomputable def realGain (θ γ x : ℝ) : ℝ := (1 - γ) * (log x - (θ - 1) / (2 * θ) * (x ^ 2 - 1))

/-- The real-utility gain is strictly positive on the whole demand-determined range
`1 < x ≤ (θ/(θ−1))^{1/2}` (O&R p. 694, exact). -/
theorem realGain_pos {θ γ x : ℝ} (hθ : 1 < θ) (hγ1 : γ < 1) (hx : 1 < x)
    (hdd : x ^ 2 ≤ θ / (θ - 1)) : 0 < realGain θ γ x := by
  unfold realGain
  apply mul_pos (by linarith)
  have hx2 : 1 < x ^ 2 := by nlinarith
  have hx0 : 0 < x := by linarith
  -- `log x = log(x²)/2 > (1 − 1/x²)/2 ≥ ((θ−1)/θ)(x² − 1)/2`
  have hlog : log (x ^ 2) = 2 * log x := by
    rw [show x ^ 2 = x ^ (2 : ℕ) by rfl, log_pow]; norm_num
  have hstrict : 1 - 1 / x ^ 2 < log (x ^ 2) := by
    have h := log_lt_sub_one_of_pos (by positivity : 0 < 1 / x ^ 2) (by
      intro h; field_simp at h; linarith)
    rw [one_div, log_inv] at h
    rw [one_div]; linarith
  have hb : (θ - 1) / θ * (x ^ 2 - 1) ≤ 1 - 1 / x ^ 2 := by
    have h1 : (θ - 1) / θ ≤ 1 / x ^ 2 := by
      rw [div_le_div_iff₀ (by linarith) (by positivity)]
      rw [le_div_iff₀ (by linarith)] at hdd
      linarith
    have : 1 - 1 / x ^ 2 = 1 / x ^ 2 * (x ^ 2 - 1) := by field_simp
    rw [this]
    exact mul_le_mul_of_nonneg_right h1 (by linarith)
  have e : (θ - 1) / (2 * θ) * (x ^ 2 - 1) = ((θ - 1) / θ * (x ^ 2 - 1)) / 2 := by
    field_simp
  rw [e]
  linarith

/-- Period utility on the shock path after impact equals the pre-shock period utility
(O&R p. 694: "later periods are unchanged", money being neutral from date 2). -/
theorem shock_periodU_later {E : Economy} (hE : E.Valid) {M0 μ x : ℝ} (hM0 : 0 < M0)
    (hμ : 0 < μ) (hx : 0 < x) {t : ℕ} (ht : t ≠ 0) (s : ℕ) :
    periodU E (shockPrices E M0 μ x) t (shockChoice E M0 μ x t)
      = periodU E (steadyPrices E M0) s (steadyChoice E M0 s) := by
  obtain ⟨_, hP⟩ := shock_cpi hE hM0 hμ hx
  have hPs : cpiAt E (steadyPrices E M0) s = pT0 E M0 * cpiRatio E := by
    simp only [cpiAt, steadyPrices]
    exact cpi_initial hE hM0
  unfold periodU
  rw [hP t ht, hPs]
  simp only [shockChoice, steadyChoice, ht, ↓reduceIte]
  rw [show μ * M0 / (μ * (pT0 E M0 * cpiRatio E)) = M0 / (pT0 E M0 * cpiRatio E) by
    field_simp]

/-- THE EXACT WELFARE GAIN (O&R p. 694, T29): lifetime utility from the shock date on the
sticky-price path minus that on the no-shock path equals
`(1−γ)[log x − ((θ−1)/(2θ))(x² − 1)] + [v((μ/x^γ)(M/P)‾) − v((M/P)‾)]`: only the impact period
differs (genuine infinite-horizon sums). -/
theorem welfare_gain_eq {E : Economy} (hE : E.Valid) {M0 μ x : ℝ} (hM0 : 0 < M0) (hμ : 0 < μ)
    (hx : 0 < x) :
    Summable (fun t => E.β ^ t * periodU E (steadyPrices E M0) t (steadyChoice E M0 t)) ∧
    Summable (fun t => E.β ^ t * periodU E (shockPrices E M0 μ x) t (shockChoice E M0 μ x t)) ∧
    ∑' t, E.β ^ t * periodU E (shockPrices E M0 μ x) t (shockChoice E M0 μ x t)
      - ∑' t, E.β ^ t * periodU E (steadyPrices E M0) t (steadyChoice E M0 t)
      = realGain E.θ E.γ x + (moneyU E.χ E.ε (μ / x ^ E.γ * realMoneyBar E)
          - moneyU E.χ E.ε (realMoneyBar E)) := by
  have hy := ybarN_pos hE
  have hk := kappa_mul_ybarN_sq hE
  have hmd := M0_div_cpi hE hM0
  obtain ⟨hP0, _⟩ := shock_cpi hE hM0 hμ hx
  have hβ := hE.1
  have hβ1 := hE.2.1
  have hθ := hE.2.2.2.2.2.2.2.2.1
  set ub := periodU E (steadyPrices E M0) 0 (steadyChoice E M0 0)
  have hbase : (fun t => E.β ^ t * periodU E (steadyPrices E M0) t (steadyChoice E M0 t))
      = fun t => E.β ^ t * ub := by funext t; rfl
  have hsb : Summable fun t => E.β ^ t * ub :=
    (summable_geometric_of_lt_one hβ.le hβ1).mul_right ub
  have hoff : ∀ t ∉ ({0} : Finset ℕ),
      E.β ^ t * periodU E (shockPrices E M0 μ x) t (shockChoice E M0 μ x t) = E.β ^ t * ub := by
    intro t ht
    have ht0 : t ≠ 0 := by simpa using ht
    rw [shock_periodU_later hE hM0 hμ hx ht0 0]
  obtain ⟨hss, htsum⟩ := tsum_eq_add_of_eq_off hsb {0} hoff
  refine ⟨hbase ▸ hsb, hss, ?_⟩
  rw [hbase, htsum, Finset.sum_singleton, pow_zero, one_mul, one_mul, add_sub_cancel_left]
  have hPs : cpiAt E (steadyPrices E M0) 0 = pT0 E M0 * cpiRatio E := by
    simp only [cpiAt, steadyPrices]; exact cpi_initial hE hM0
  simp only [ub, periodU, hP0, hPs, shockChoice, steadyChoice, ↓reduceIte]
  rw [hmd, show μ * M0 / (x ^ E.γ * (pT0 E M0 * cpiRatio E))
      = μ / x ^ E.γ * (M0 / (pT0 E M0 * cpiRatio E)) by field_simp, hmd,
    log_mul hx.ne' hy.ne']
  unfold realGain
  have e : E.κ / 2 * (x * ybarN E) ^ 2 - E.κ / 2 * ybarN E ^ 2
      = (E.θ - 1) * (1 - E.γ) / E.θ / 2 * (x ^ 2 - 1) := by
    rw [← hk]; ring
  field_simp at e ⊢
  linear_combination (-1 : ℝ) * e

/-- A MONEY SHOCK UNAMBIGUOUSLY IMPROVES WELFARE (O&R p. 694, exact): for a permanent expansion
`μ > 1` whose impact response is demand-determined (`x² ≤ θ/(θ−1)`), lifetime utility on the
sticky-price path strictly exceeds that on the no-shock path — both the real-utility gain and
the real-balance gain are strictly positive. -/
theorem welfare_gain_pos {E : Economy} (hE : E.Valid) {M0 μ x : ℝ} (hM0 : 0 < M0) (hμ : 1 < μ)
    (hx : 0 < x) (hF : impactGap E.β E.γ E.ε μ x = 0) (hdd : x ^ 2 ≤ E.θ / (E.θ - 1)) :
    ∑' t, E.β ^ t * periodU E (steadyPrices E M0) t (steadyChoice E M0 t)
      < ∑' t, E.β ^ t * periodU E (shockPrices E M0 μ x) t (shockChoice E M0 μ x t) := by
  have hμ0 : 0 < μ := by linarith
  obtain ⟨_, _, heqn⟩ := welfare_gain_eq hE hM0 hμ0 hx
  have hmb := realMoneyBar_pos hE
  obtain ⟨hβ, hβ1, _, hγ0, hγ1, hχ, hε, _, hθ, _⟩ := hE
  have hx1 := one_lt_root hβ hβ1 hγ0 hγ1 hε hμ hx hF
  have hr := realGain_pos hθ hγ1 hx1 hdd
  have hrb := realBalances_rise hβ hβ1 hγ0 hγ1 hε hμ hx hF
  have hm : moneyU E.χ E.ε (realMoneyBar E) < moneyU E.χ E.ε (μ / x ^ E.γ * realMoneyBar E) :=
    moneyU_strictMonoOn hχ (Set.mem_Ioi.mpr hmb) (Set.mem_Ioi.mpr (by positivity))
      (by nlinarith)
  linarith

/-- First-order welfare (O&R p. 694): the derivative of the real-utility gain at `μ = 1` is
`(1−γ)/θ` times the (99) coefficient, i.e. `dU^R = (1−γ) p_T/θ > 0`. -/
theorem hasDerivAt_realGain {β γ ε θ : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hγ0 : 0 < γ)
    (hγ1 : γ < 1) (hε : 0 < ε) (hθ : 1 < θ) {X : ℝ → ℝ}
    (hX : ∀ᶠ μ in 𝓝 1, 0 < X μ ∧ impactGap β γ ε μ (X μ) = 0) :
    HasDerivAt (fun μ => realGain θ γ (X μ))
      ((1 - γ) / θ * ((β + (1 - β) * ε) / (β + (1 - β) * expo γ ε))) 1 := by
  have hd := hasDerivAt_impact hβ hβ1 hγ0 hγ1 hε hX
  have hX1 : X 1 = 1 := by
    obtain ⟨z, _, _, _, huniq⟩ := impact_exists_unique hβ hβ1 hγ0 hγ1 hε one_pos
    have h1 : impactGap β γ ε 1 1 = 0 := by
      rw [impactGap_at_mu one_pos]; simp
    rw [huniq (X 1) hX.self_of_nhds.1 hX.self_of_nhds.2, huniq 1 one_pos h1]
  set k := (β + (1 - β) * ε) / (β + (1 - β) * expo γ ε)
  have hlog := hd.log (by rw [hX1]; exact one_ne_zero)
  have hsq := hd.pow 2
  have h := ((hlog.sub ((hsq.sub_const 1).const_mul ((θ - 1) / (2 * θ))))).const_mul (1 - γ)
  have e : (fun μ => realGain θ γ (X μ))
      = fun μ => (1 - γ) * (log (X μ) - (θ - 1) / (2 * θ) * (X μ ^ 2 - 1)) := rfl
  rw [e]
  convert h using 1
  · rw [hX1]
    have : θ ≠ 0 := by linarith
    field_simp
    ring

/-! ## Exercise 2: the real exchange rate and the real interest rate (p. 713) -/

/-- The real exchange rate `Q = 𝓔P^*/P` with `𝓔 = P_T/P_T^*` and the foreign CPI `P^*`
constant (the book never defines it in §10.2; O&R Ex. 2, p. 713). -/
noncomputable def realExchangeRate (PTstar Pstar PT P : ℝ) : ℝ := PT / PTstar * Pstar / P

/-- The gross consumption-based real interest rate `1 + r^C_{t+1} = (1+i_{t+1})P_t/P_{t+1}`,
with interest parity `1 + i_{t+1} = (1+r)P_{T,t+1}/P_{T,t}` (O&R Ex. 2, p. 713). -/
noncomputable def grossRealRate (r PT PT' P P' : ℝ) : ℝ := (1 + r) * (PT' / PT) * (P / P')

/-- EXACT REAL INTEREST PARITY (O&R Ex. 2): `1 + r^C_{t+1} = (1+r) Q_{t+1}/Q_t`, for any positive
price paths. -/
theorem real_interest_parity {r PTstar Pstar PT PT' P P' : ℝ} (hs : 0 < PTstar)
    (hps : 0 < Pstar) (hT : 0 < PT) (hP : 0 < P) (hP' : 0 < P') :
    grossRealRate r PT PT' P P'
      = (1 + r) * (realExchangeRate PTstar Pstar PT' P' / realExchangeRate PTstar Pstar PT P) := by
  unfold grossRealRate realExchangeRate
  field_simp

/-- EXERCISE 2 ANSWERED EXACTLY (O&R p. 713): on the sticky-price path after a permanent
expansion `μ > 1`, for EVERY `ε > 0`, the real exchange rate depreciates on impact,
`Q_1/Q_0 = x^{1−γ} > 1`, returns to `Q_0` from date 2, and the consumption-based real interest
rate between dates 1 and 2 falls below `r`: `1 + r^C_2 = (1+r) x^{−(1−γ)} < 1 + r`. In logs,
`log(1 + r^C_2) − log(1+r) = −log(Q_1/Q_0)` (coefficient exactly one): the Dornbusch-type
co-movement holds without any need for overshooting. -/
theorem ex2_real_depreciation {E : Economy} (hE : E.Valid) {M0 μ x PTstar Pstar : ℝ}
    (hM0 : 0 < M0) (hμ : 1 < μ) (hx : 0 < x) (hF : impactGap E.β E.γ E.ε μ x = 0)
    (hs : 0 < PTstar) (hps : 0 < Pstar) :
    realExchangeRate PTstar Pstar ((shockPrices E M0 μ x).PT 0) (cpiAt E (shockPrices E M0 μ x) 0)
        / realExchangeRate PTstar Pstar (pT0 E M0) (pT0 E M0 * cpiRatio E) = x ^ (1 - E.γ) ∧
      1 < x ^ (1 - E.γ) ∧
      realExchangeRate PTstar Pstar ((shockPrices E M0 μ x).PT 1)
        (cpiAt E (shockPrices E M0 μ x) 1)
        = realExchangeRate PTstar Pstar (pT0 E M0) (pT0 E M0 * cpiRatio E) ∧
      grossRealRate E.r ((shockPrices E M0 μ x).PT 0) ((shockPrices E M0 μ x).PT 1)
          (cpiAt E (shockPrices E M0 μ x) 0) (cpiAt E (shockPrices E M0 μ x) 1)
        = (1 + E.r) * (x ^ (1 - E.γ))⁻¹ ∧
      grossRealRate E.r ((shockPrices E M0 μ x).PT 0) ((shockPrices E M0 μ x).PT 1)
          (cpiAt E (shockPrices E M0 μ x) 0) (cpiAt E (shockPrices E M0 μ x) 1) < 1 + E.r := by
  have hμ0 : 0 < μ := by linarith
  have hT := pT0_pos hE hM0
  have hcr := cpiRatio_pos hE
  obtain ⟨hP0, hP⟩ := shock_cpi hE hM0 hμ0 hx
  have hr := hE.2.2.1
  obtain ⟨hβ, hβ1, _, hγ0, hγ1, _, hε, _, _, _⟩ := hE
  have hx1 := one_lt_root hβ hβ1 hγ0 hγ1 hε hμ hx hF
  have hxg : 0 < x ^ E.γ := rpow_pos_of_pos hx _
  have hsplit : x ^ (1 - E.γ) = x / x ^ E.γ := by rw [rpow_sub hx, rpow_one]
  have hq1 : 1 < x ^ (1 - E.γ) := one_lt_rpow hx1 (by linarith)
  have hP1 := hP 1 Nat.one_ne_zero
  have hPT0 : (shockPrices E M0 μ x).PT 0 = x * pT0 E M0 := by simp [shockPrices]
  have hPT1 : (shockPrices E M0 μ x).PT 1 = μ * pT0 E M0 := by simp [shockPrices]
  have hgr : grossRealRate E.r ((shockPrices E M0 μ x).PT 0) ((shockPrices E M0 μ x).PT 1)
      (cpiAt E (shockPrices E M0 μ x) 0) (cpiAt E (shockPrices E M0 μ x) 1)
      = (1 + E.r) * (x ^ (1 - E.γ))⁻¹ := by
    rw [hP0, hP1, hPT0, hPT1, hsplit]
    unfold grossRealRate
    field_simp
  refine ⟨?_, hq1, ?_, hgr, ?_⟩
  · rw [hP0, hPT0, hsplit]
    unfold realExchangeRate
    field_simp
  · rw [hP1, hPT1]
    unfold realExchangeRate
    field_simp
  · rw [hgr]
    have : (x ^ (1 - E.γ))⁻¹ < 1 := inv_lt_one_of_one_lt₀ hq1
    nlinarith

/-- Exercise 2 in logs (O&R p. 713): `log(1 + r^C_2) − log(1 + r) = −(1−γ) log x
= −log(Q_1/Q_0)`, exactly. -/
theorem ex2_log_parity {r γ x : ℝ} (hr : 0 < 1 + r) (hx : 0 < x) :
    log ((1 + r) * (x ^ (1 - γ))⁻¹) - log (1 + r) = -((1 - γ) * log x) := by
  rw [log_mul hr.ne' (by positivity), log_inv, log_rpow hx]
  ring

/-- Exercise 2 to first order (O&R p. 713): `q = (1−γ) p_T`, i.e. the impact real-depreciation
factor `x(μ)^{1−γ}` has derivative `(1−γ)` times the (99) coefficient at `μ = 1`. -/
theorem hasDerivAt_realDepreciation {β γ ε : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hγ0 : 0 < γ)
    (hγ1 : γ < 1) (hε : 0 < ε) {X : ℝ → ℝ}
    (hX : ∀ᶠ μ in 𝓝 1, 0 < X μ ∧ impactGap β γ ε μ (X μ) = 0) :
    HasDerivAt (fun μ => X μ ^ (1 - γ))
      ((1 - γ) * ((β + (1 - β) * ε) / (β + (1 - β) * expo γ ε))) 1 := by
  have hd := hasDerivAt_impact hβ hβ1 hγ0 hγ1 hε hX
  have hX1 : X 1 = 1 := by
    obtain ⟨z, _, _, _, huniq⟩ := impact_exists_unique hβ hβ1 hγ0 hγ1 hε one_pos
    have h1 : impactGap β γ ε 1 1 = 0 := by
      rw [impactGap_at_mu one_pos]; simp
    rw [huniq (X 1) hX.self_of_nhds.1 hX.self_of_nhds.2, huniq 1 one_pos h1]
  have h := hd.rpow_const (p := 1 - γ) (Or.inl (by rw [hX1]; exact one_ne_zero))
  convert h using 1
  rw [hX1, one_rpow]; ring

/-- The internal real exchange rate `P_T/P_N` also rises by the factor `x` on impact and returns
to its initial value from date 2 (O&R Ex. 2: the sign conclusions coincide). -/
theorem ex2_internal_real_rate {E : Economy} (hE : E.Valid) {M0 μ x : ℝ} (hM0 : 0 < M0)
    (hμ : 0 < μ) :
    (shockPrices E M0 μ x).PT 0 / (shockPrices E M0 μ x).PN 0 = x * (pT0 E M0 / pN0 E M0) ∧
      (shockPrices E M0 μ x).PT 1 / (shockPrices E M0 μ x).PN 1 = pT0 E M0 / pN0 E M0 := by
  have hN := pN0_pos hE hM0
  refine ⟨?_, ?_⟩
  · simp only [shockPrices, ↓reduceIte]; ring
  · simp only [shockPrices, Nat.one_ne_zero, ↓reduceIte]; field_simp

end ObstfeldRogoff.StickyPriceModels.NontradablesOvershooting

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Preset nominal wages in the small country (§10.4.1)

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §10.4.1,
pp. 706–709. A single nontraded good is produced competitively from differentiated labour
types with the CES technology (131), `Y_N = [∫ ℓ(z)^{(φ−1)/φ} dz]^{φ/(φ−1)}`, `φ > 1`; each worker
is a monopoly supplier of its labour type, with utility (132) and budget (133); the firm's
problem (134) gives the labour demands (135).

This file proves:

* The competitive firm (131), (134)–(135), on finitely many labour types with positive weights
  (the continuum `[0,1]` of the book is the equal-weight limit; the argument is identical):
  the wage index `W` is the minimum cost of a unit of labour, the labour demands (135) are the
  UNIQUE cost-minimising inputs, profits are `(P_N − W)Y_N` at best, so an equilibrium with
  positive output requires the zero-profit condition `P_N = W`; under symmetric wages
  `W = w`, (138), and `Y_N = ℓ`, (137).
* The worker's problem (132)–(133) with labour demand (135) IS the household problem of
  `NontradablesModel` with `θ` replaced by `φ` and aggregate demand `C^A_N` replaced by `Y_N`:
  labour income `wℓ = P_N ℓ^{(φ−1)/φ} Y_N^{1/φ}`. Hence (136) and (87)–(89) are necessary and
  sufficient for the worker's optimum (genuine infinite horizon), and (140) is the unique
  steady-state labour supply.
* Preset wages (§10.4.1.3): with `w_1 = w_0` preset, zero profits force `P_{N,1} = w_1 = P_{N,0}`
  although `P_N` is flexible, so the short-run system is IDENTICAL to §10.2: the impact response,
  (99), exact overshooting iff `ε > 1`, the equilibrium characterisation (with `φ` in the
  demand-determination bound `x² ≤ φ/(φ−1)`) and the strict welfare gain all transfer (p. 709).
-/

namespace ObstfeldRogoff.StickyPriceModels.PresetWagesSmallCountry

open Real Filter Topology Finset
open ObstfeldRogoff.StickyPriceModels.NontradablesModel
open ObstfeldRogoff.StickyPriceModels.NontradablesOvershooting

/-! ## The competitive firm (131), (134)–(135) -/

/-- Strict tangent inequality for `y ↦ y^s`, `0 < s < 1`, `b ≠ a` (strict concavity of the CES
aggregator (131), O&R p. 706–707): `b^s < a^s + s a^{s−1}(b − a)`. -/
theorem rpow_lt_tangent {s a b : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (ha : 0 < a) (hb : 0 < b)
    (hne : b ≠ a) : b ^ s < a ^ s + s * (a ^ (s - 1) * (b - a)) := by
  have hq : 0 < b / a := div_pos hb ha
  have hq1 : b / a - 1 ≠ 0 := by
    intro h; apply hne; field_simp at h; linarith
  have h1 : (1 + (b / a - 1)) ^ s < 1 + s * (b / a - 1) :=
    rpow_one_add_lt_one_add_mul_self (by linarith) hq1 hs0 hs1
  rw [show 1 + (b / a - 1) = b / a by ring] at h1
  have has : 0 < a ^ s := rpow_pos_of_pos ha s
  have key : b ^ s = a ^ s * (b / a) ^ s := by rw [div_rpow hb.le ha.le]; field_simp
  have hsplit : a ^ (s - 1) * (b - a) = a ^ s * (b / a - 1) := by
    rw [rpow_sub_one ha.ne']; field_simp
  rw [key, hsplit]
  nlinarith [mul_lt_mul_of_pos_left h1 has]

variable {ι : Type*} [Fintype ι]

/-- The CES labour aggregate (131), p. 706, on finitely many labour types with weights `ω`:
`Y_N = [Σ ω_i ℓ_i^{(φ−1)/φ}]^{φ/(φ−1)}`. -/
noncomputable def laborAggregate (ω : ι → ℝ) (φ : ℝ) (ℓ : ι → ℝ) : ℝ :=
  (∑ i, ω i * ℓ i ^ ((φ - 1) / φ)) ^ (φ / (φ - 1))

/-- The wage index `W = [Σ ω_i w_i^{1−φ}]^{1/(1−φ)}` (dual of (131); O&R p. 707). -/
noncomputable def wageIndex (ω : ι → ℝ) (φ : ℝ) (w : ι → ℝ) : ℝ :=
  (∑ i, ω i * w i ^ (1 - φ)) ^ (1 / (1 - φ))

/-- The labour demands (135), p. 707: `ℓ_i = (w_i/W)^{−φ} Y_N`. -/
noncomputable def laborDemand (ω : ι → ℝ) (φ : ℝ) (w : ι → ℝ) (Y : ℝ) (i : ι) : ℝ :=
  (w i / wageIndex ω φ w) ^ (-φ) * Y

/-- The wage index is positive (O&R p. 707). -/
theorem wageIndex_pos [Nonempty ι] {ω w : ι → ℝ} {φ : ℝ} (hω : ∀ i, 0 < ω i)
    (hw : ∀ i, 0 < w i) : 0 < wageIndex ω φ w := by
  unfold wageIndex
  apply rpow_pos_of_pos
  exact Finset.sum_pos (fun i _ => mul_pos (hω i) (rpow_pos_of_pos (hw i) _)) univ_nonempty

/-- `W^{1−φ} = Σ ω_i w_i^{1−φ}` (O&R p. 707). -/
theorem wageIndex_rpow [Nonempty ι] {ω w : ι → ℝ} {φ : ℝ} (hφ : 1 < φ) (hω : ∀ i, 0 < ω i)
    (hw : ∀ i, 0 < w i) : wageIndex ω φ w ^ (1 - φ) = ∑ i, ω i * w i ^ (1 - φ) := by
  unfold wageIndex
  have hS : 0 < ∑ i, ω i * w i ^ (1 - φ) :=
    Finset.sum_pos (fun i _ => mul_pos (hω i) (rpow_pos_of_pos (hw i) _)) univ_nonempty
  rw [← rpow_mul hS.le, show 1 / (1 - φ) * (1 - φ) = 1 by
    have : (1 : ℝ) - φ ≠ 0 := by linarith
    field_simp, rpow_one]

/-- The labour demands (135) cost exactly `W Y_N` (O&R (134)–(135)). -/
theorem laborDemand_cost [Nonempty ι] {ω w : ι → ℝ} {φ Y : ℝ} (hφ : 1 < φ)
    (hω : ∀ i, 0 < ω i) (hw : ∀ i, 0 < w i) :
    ∑ i, ω i * (w i * laborDemand ω φ w Y i) = wageIndex ω φ w * Y := by
  have hW := wageIndex_pos (φ := φ) hω hw
  have hWr := wageIndex_rpow hφ hω hw
  have e : ∀ i, ω i * (w i * laborDemand ω φ w Y i)
      = (ω i * w i ^ (1 - φ)) * (wageIndex ω φ w ^ φ * Y) := by
    intro i
    unfold laborDemand
    rw [div_rpow (hw i).le hW.le, rpow_neg (hw i).le, rpow_neg hW.le, rpow_sub (hw i),
      rpow_one]
    have : 0 < w i ^ φ := rpow_pos_of_pos (hw i) φ
    field_simp
  simp_rw [e]
  rw [← Finset.sum_mul, ← hWr, ← mul_assoc, ← rpow_add hW, show 1 - φ + φ = 1 by ring,
    rpow_one]

/-- The labour demands (135) produce exactly `Y_N` (O&R (131), (135)). -/
theorem laborDemand_output [Nonempty ι] {ω w : ι → ℝ} {φ Y : ℝ} (hφ : 1 < φ)
    (hω : ∀ i, 0 < ω i) (hw : ∀ i, 0 < w i) (hY : 0 < Y) :
    laborAggregate ω φ (laborDemand ω φ w Y) = Y := by
  have hW := wageIndex_pos (φ := φ) hω hw
  have hWr := wageIndex_rpow hφ hω hw
  have hφ0 : 0 < φ := by linarith
  have e : ∀ i, ω i * laborDemand ω φ w Y i ^ ((φ - 1) / φ)
      = (ω i * w i ^ (1 - φ)) * (Y ^ ((φ - 1) / φ) / wageIndex ω φ w ^ (1 - φ)) := by
    intro i
    unfold laborDemand
    rw [mul_rpow (rpow_pos_of_pos (div_pos (hw i) hW) _).le hY.le, ← rpow_mul (div_pos (hw i)
      hW).le, show -φ * ((φ - 1) / φ) = 1 - φ by field_simp; ring, div_rpow (hw i).le hW.le]
    have : 0 < wageIndex ω φ w ^ (1 - φ) := rpow_pos_of_pos hW _
    field_simp
  unfold laborAggregate
  simp_rw [e]
  rw [← Finset.sum_mul, ← hWr]
  have : 0 < wageIndex ω φ w ^ (1 - φ) := rpow_pos_of_pos hW _
  rw [mul_div_cancel₀ _ this.ne', ← rpow_mul hY.le,
    show (φ - 1) / φ * (φ / (φ - 1)) = 1 by
      have : φ - 1 ≠ 0 := by linarith
      field_simp, rpow_one]

/-- COST MINIMISATION (O&R (134)–(135), p. 707): any positive input vector producing at least
`Y_N` costs at least `W Y_N`, with equality ONLY at the labour demands (135) (existence and
uniqueness of the cost-minimising inputs; strict concavity of (131)). -/
theorem labor_cost_ge [Nonempty ι] {ω w ℓ : ι → ℝ} {φ Y : ℝ} (hφ : 1 < φ)
    (hω : ∀ i, 0 < ω i) (hw : ∀ i, 0 < w i) (hℓ : ∀ i, 0 < ℓ i) (hY : 0 < Y)
    (hout : Y ≤ laborAggregate ω φ ℓ) :
    wageIndex ω φ w * Y ≤ ∑ i, ω i * (w i * ℓ i) ∧
      (∑ i, ω i * (w i * ℓ i) = wageIndex ω φ w * Y → ℓ = laborDemand ω φ w Y) := by
  have hW := wageIndex_pos (φ := φ) hω hw
  have hWr := wageIndex_rpow hφ hω hw
  have hφ0 : 0 < φ := by linarith
  set s := (φ - 1) / φ with hs
  have hs0 : 0 < s := div_pos (by linarith) hφ0
  have hs1 : s < 1 := by rw [hs, div_lt_one hφ0]; linarith
  set ℓ0 := laborDemand ω φ w Y
  have hℓ0 : ∀ i, 0 < ℓ0 i := fun i =>
    mul_pos (rpow_pos_of_pos (div_pos (hw i) hW) _) hY
  -- the two powers of the demands
  have hpow1 : ∀ i, ℓ0 i ^ s = (w i / wageIndex ω φ w) ^ (1 - φ) * Y ^ s := by
    intro i
    simp only [ℓ0, laborDemand]
    rw [mul_rpow (rpow_pos_of_pos (div_pos (hw i) hW) _).le hY.le,
      ← rpow_mul (div_pos (hw i) hW).le, show -φ * s = 1 - φ by rw [hs]; field_simp; ring]
  have hpow2 : ∀ i, ℓ0 i ^ (s - 1) = (w i / wageIndex ω φ w) * Y ^ (s - 1) := by
    intro i
    simp only [ℓ0, laborDemand]
    rw [mul_rpow (rpow_pos_of_pos (div_pos (hw i) hW) _).le hY.le,
      ← rpow_mul (div_pos (hw i) hW).le, show -φ * (s - 1) = 1 by rw [hs]; field_simp; ring,
      rpow_one]
  have hsum0 : ∑ i, ω i * ℓ0 i ^ s = Y ^ s := by
    simp_rw [hpow1]
    have e : ∀ i, ω i * ((w i / wageIndex ω φ w) ^ (1 - φ) * Y ^ s)
        = (ω i * w i ^ (1 - φ)) * (Y ^ s / wageIndex ω φ w ^ (1 - φ)) := by
      intro i; rw [div_rpow (hw i).le hW.le]; ring
    simp_rw [e]
    rw [← Finset.sum_mul, ← hWr, mul_div_cancel₀ _ (rpow_pos_of_pos hW _).ne']
  have hcost0 := laborDemand_cost (Y := Y) hφ hω hw
  -- output requirement in power form
  have hS : 0 < ∑ i, ω i * ℓ i ^ s :=
    Finset.sum_pos (fun i _ => mul_pos (hω i) (rpow_pos_of_pos (hℓ i) _)) univ_nonempty
  have hreq : Y ^ s ≤ ∑ i, ω i * ℓ i ^ s := by
    have h1 := rpow_le_rpow hY.le hout hs0.le
    unfold laborAggregate at h1
    rw [← rpow_mul hS.le, show φ / (φ - 1) * s = 1 by
      rw [hs]; have : φ - 1 ≠ 0 := by linarith
      field_simp, rpow_one] at h1
    exact h1
  -- the tangent bound
  have htan : ∀ i, ω i * ℓ i ^ s ≤ ω i * ℓ0 i ^ s
      + s * Y ^ (s - 1) / wageIndex ω φ w * (ω i * (w i * ℓ i) - ω i * (w i * ℓ0 i)) := by
    intro i
    have h := rpow_le_tangent hs0 hs1.le (hℓ0 i) (hℓ i)
    rw [hpow2 i] at h
    have := mul_le_mul_of_nonneg_left h (hω i).le
    have e : ω i * ((w i / wageIndex ω φ w * Y ^ (s - 1)) * (ℓ i - ℓ0 i)) * s
        = s * Y ^ (s - 1) / wageIndex ω φ w * (ω i * (w i * ℓ i) - ω i * (w i * ℓ0 i)) := by
      field_simp
    nlinarith
  have hsumtan : ∑ i, ω i * ℓ i ^ s ≤ Y ^ s + s * Y ^ (s - 1) / wageIndex ω φ w
      * (∑ i, ω i * (w i * ℓ i) - wageIndex ω φ w * Y) := by
    have := Finset.sum_le_sum (fun i (_ : i ∈ univ) => htan i)
    rw [Finset.sum_add_distrib, hsum0, ← Finset.mul_sum, Finset.sum_sub_distrib, hcost0]
      at this
    exact this
  have hk : 0 < s * Y ^ (s - 1) / wageIndex ω φ w := by
    have := rpow_pos_of_pos hY (s - 1); positivity
  refine ⟨?_, fun heq => ?_⟩
  · by_contra hlt
    push Not at hlt
    have : s * Y ^ (s - 1) / wageIndex ω φ w
        * (∑ i, ω i * (w i * ℓ i) - wageIndex ω φ w * Y) < 0 :=
      mul_neg_of_pos_of_neg hk (by linarith)
    linarith
  · funext i
    by_contra hne
    have hstrict : ∑ i, ω i * ℓ i ^ s < ∑ i, (ω i * ℓ0 i ^ s
        + s * Y ^ (s - 1) / wageIndex ω φ w * (ω i * (w i * ℓ i) - ω i * (w i * ℓ0 i))) := by
      apply Finset.sum_lt_sum (fun j _ => htan j)
      refine ⟨i, mem_univ i, ?_⟩
      have h := rpow_lt_tangent hs0 hs1 (hℓ0 i) (hℓ i) hne
      rw [hpow2 i] at h
      have := mul_lt_mul_of_pos_left h (hω i)
      have e : ω i * ((w i / wageIndex ω φ w * Y ^ (s - 1)) * (ℓ i - ℓ0 i)) * s
          = s * Y ^ (s - 1) / wageIndex ω φ w * (ω i * (w i * ℓ i) - ω i * (w i * ℓ0 i)) := by
        field_simp
      nlinarith
    rw [Finset.sum_add_distrib, hsum0, ← Finset.mul_sum, Finset.sum_sub_distrib, hcost0, heq,
      sub_self, mul_zero, add_zero] at hstrict
    linarith

/-- THE FIRM'S PROFIT (O&R (134), p. 707): for any positive inputs, profit is at most
`(P_N − W) Y_N`, so with constant returns the competitive firm can have a positive-output
optimum only if `P_N = W` (zero profit); then every output level is optimal, with profit zero,
exactly at the labour demands (135). -/
theorem firm_profit_le [Nonempty ι] {ω w ℓ : ι → ℝ} {φ PN : ℝ} (hφ : 1 < φ)
    (hω : ∀ i, 0 < ω i) (hw : ∀ i, 0 < w i) (hℓ : ∀ i, 0 < ℓ i) :
    PN * laborAggregate ω φ ℓ - ∑ i, ω i * (w i * ℓ i)
      ≤ (PN - wageIndex ω φ w) * laborAggregate ω φ ℓ := by
  have hφ0 : 0 < φ := by linarith
  have hS : 0 < ∑ i, ω i * ℓ i ^ ((φ - 1) / φ) :=
    Finset.sum_pos (fun i _ => mul_pos (hω i) (rpow_pos_of_pos (hℓ i) _)) univ_nonempty
  have hY : 0 < laborAggregate ω φ ℓ := rpow_pos_of_pos hS _
  have := (labor_cost_ge hφ hω hw hℓ hY le_rfl).1
  nlinarith

/-- Zero profit is attained by (135) when `P_N = W` (O&R (134)–(135)). -/
theorem firm_zero_profit [Nonempty ι] {ω w : ι → ℝ} {φ Y : ℝ} (hφ : 1 < φ)
    (hω : ∀ i, 0 < ω i) (hw : ∀ i, 0 < w i) (hY : 0 < Y) :
    wageIndex ω φ w * laborAggregate ω φ (laborDemand ω φ w Y)
      - ∑ i, ω i * (w i * laborDemand ω φ w Y i) = 0 := by
  rw [laborDemand_output hφ hω hw hY, laborDemand_cost hφ hω hw]; ring

/-- If `P_N > W` profits are unbounded (no competitive equilibrium), and if `P_N < W` every
positive plan loses money: an equilibrium with positive output forces `P_N = W`
(O&R p. 708). -/
theorem firm_price_eq_wageIndex [Nonempty ι] {ω w : ι → ℝ} {φ PN : ℝ} (hφ : 1 < φ)
    (hω : ∀ i, 0 < ω i) (hw : ∀ i, 0 < w i) :
    (wageIndex ω φ w < PN → ∀ B : ℝ, ∃ Y > 0,
      B < PN * laborAggregate ω φ (laborDemand ω φ w Y)
        - ∑ i, ω i * (w i * laborDemand ω φ w Y i)) ∧
    (PN < wageIndex ω φ w → ∀ ℓ : ι → ℝ, (∀ i, 0 < ℓ i) →
      PN * laborAggregate ω φ ℓ - ∑ i, ω i * (w i * ℓ i) < 0) := by
  refine ⟨fun hgt B => ?_, fun hlt ℓ hℓ => ?_⟩
  · set d := PN - wageIndex ω φ w
    have hd : 0 < d := by simp only [d]; linarith
    refine ⟨(|B| + 1) / d, by positivity, ?_⟩
    rw [laborDemand_output hφ hω hw (by positivity), laborDemand_cost hφ hω hw]
    have e : PN * ((|B| + 1) / d) - wageIndex ω φ w * ((|B| + 1) / d) = |B| + 1 := by
      rw [← sub_mul]; exact mul_div_cancel₀ _ hd.ne'
    rw [e]; linarith [le_abs_self B]
  · have hφ0 : 0 < φ := by linarith
    have hS : 0 < ∑ i, ω i * ℓ i ^ ((φ - 1) / φ) :=
      Finset.sum_pos (fun i _ => mul_pos (hω i) (rpow_pos_of_pos (hℓ i) _)) univ_nonempty
    have hY : 0 < laborAggregate ω φ ℓ := rpow_pos_of_pos hS _
    have := firm_profit_le (PN := PN) hφ hω hw hℓ
    nlinarith

/-- SYMMETRY (137)–(138), p. 708: with a common wage `w` and weights summing to one, the wage
index is `W = w` (so zero profit gives `w = P_N`, (138)), each type's demand is `Y_N`, and
the aggregate of equal inputs `ℓ` is `ℓ`, so `Y_N = ℓ`, (137). -/
theorem symmetric_wages [Nonempty ι] {ω : ι → ℝ} {φ w Y : ℝ} (hφ : 1 < φ)
    (hω1 : ∑ i, ω i = 1) (hw : 0 < w) (hY : 0 < Y) :
    wageIndex ω φ (fun _ => w) = w ∧ (∀ i, laborDemand ω φ (fun _ => w) Y i = Y) ∧
      laborAggregate ω φ (fun _ => Y) = Y := by
  have hW : wageIndex ω φ (fun _ => w) = w := by
    unfold wageIndex
    rw [← Finset.sum_mul, hω1, one_mul, ← rpow_mul hw.le, show (1 - φ) * (1 / (1 - φ)) = 1 by
      have : (1 : ℝ) - φ ≠ 0 := by linarith
      field_simp, rpow_one]
  refine ⟨hW, fun i => by simp [laborDemand, hW, div_self hw.ne'], ?_⟩
  unfold laborAggregate
  rw [← Finset.sum_mul, hω1, one_mul, ← rpow_mul hY.le, show (φ - 1) / φ * (φ / (φ - 1)) = 1 by
    have : φ - 1 ≠ 0 := by linarith
    have : φ ≠ 0 := by linarith
    field_simp, rpow_one]


/-! ## The worker's problem (132)–(136) and the steady state (140) -/

/-- The §10.4.1 economy: the §10.2 economy with the labour-demand elasticity `φ` in the place of
the goods-demand elasticity `θ` (O&R (132)–(135), pp. 707–708). -/
def wageEconomy (E : Economy) (φ : ℝ) : Economy := ⟨E.β, E.r, E.γ, E.χ, E.ε, E.κ, φ, E.yT⟩

/-- The §10.4.1 parameter restrictions: those of §10.2 and `φ > 1` (O&R p. 707). -/
theorem wageEconomy_valid {E : Economy} (hE : E.Valid) {φ : ℝ} (hφ : 1 < φ) :
    (wageEconomy E φ).Valid := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, _, h10⟩ := hE
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, hφ, h10⟩

/-- Labour demand (135) and labour income (133), p. 707: at the wage
`w = P_N (ℓ/Y_N)^{−1/φ}`, the demand `(w/P_N)^{−φ} Y_N` for type-`j` labour is exactly `ℓ`, and
real labour income is `wℓ/P_T = (P_N/P_T) ℓ^{(φ−1)/φ} Y_N^{1/φ}` — the §10.2 revenue with
`(θ, C^A_N)` replaced by `(φ, Y_N)`. (`Q.CA` is read as the path of `Y_N`.) -/
theorem laborIncome {E : Economy} {φ : ℝ} (hφ : 1 < φ) (Q : Prices) (t : ℕ) {ℓ : ℝ}
    (hT : 0 < Q.PT t) (hN : 0 < Q.PN t) (hY : 0 < Q.CA t) (hℓ : 0 < ℓ) :
    cesDemand φ (invDemand (wageEconomy E φ) Q t ℓ) (Q.PN t) (Q.CA t) = ℓ ∧
      invDemand (wageEconomy E φ) Q t ℓ * ℓ / Q.PT t = realRevenue (wageEconomy E φ) Q t ℓ :=
  ⟨cesDemand_invDemand (wageEconomy E φ) Q t (by simp [wageEconomy]; linarith) hN hY hℓ,
    invDemand_mul (wageEconomy E φ) Q t (by simp [wageEconomy]; linarith) hT hY hℓ⟩

/-- THE WORKER'S OPTIMUM (O&R (132)–(136)): a plan (tradables, nontradables, money, labour) is
optimal for the monopolistic worker IF AND ONLY IF (87), (89), the money condition (88), the
labour condition behind (136), no-Ponzi and the transversality condition hold (genuine infinite
horizon; specialisation of `NontradablesModel.householdOptimal_iff`). -/
theorem worker_optimal_iff {E : Economy} (hE : E.Valid) {φ : ℝ} (hφ : 1 < φ) {Q : Prices}
    (hQ : Q.Valid E.r) {B0 Mm1 : ℝ} {c : ℕ → Choice} :
    HouseholdOptimal (wageEconomy E φ) Q B0 Mm1 c ↔
      (∀ t, c t ∈ posChoice) ∧
      Summable (fun t => E.β ^ t * periodU (wageEconomy E φ) Q t (c t)) ∧
      EulerFOC (wageEconomy E φ) c ∧ IntraFOC (wageEconomy E φ) Q c ∧
      MoneyFOC (wageEconomy E φ) Q c ∧ LabourFOC (wageEconomy E φ) Q c ∧
      NoPonzi E.r (wealth E.r (initWealth (wageEconomy E φ) Q B0 Mm1)
        (netRes (wageEconomy E φ) Q) c) ∧
      LiminfNonpos E.r (wealth E.r (initWealth (wageEconomy E φ) Q B0 Mm1)
        (netRes (wageEconomy E φ) Q) c) :=
  householdOptimal_iff (wageEconomy_valid hE hφ) hQ

/-- (136), p. 708: at the worker's optimum,
`ℓ^{(φ+1)/φ} = [(φ−1)(1−γ)/(κφ)] Y_N^{1/φ} (1/C_N)` at every date. -/
theorem worker_136 {E : Economy} (hE : E.Valid) {φ : ℝ} (hφ : 1 < φ) {Q : Prices}
    {B0 Mm1 : ℝ} {c : ℕ → Choice}
    (hopt : HouseholdOptimal (wageEconomy E φ) Q B0 Mm1 c) (t : ℕ) :
    (c t).y ^ ((φ + 1) / φ) = (φ - 1) * (1 - E.γ) / (E.κ * φ) * Q.CA t ^ (1 / φ) / (c t).cN := by
  have hE' := wageEconomy_valid hE hφ
  exact labour_90 hE' hopt.1 (intraFOC_of_optimal hE' hopt) (labourFOC_of_optimal hE' hopt) t

/-- (140), p. 708: in any symmetric equilibrium (`ℓ = Y_N`, (137); `Y_N = C_N`, (139)) labour
supply equals `ℓ̄ = [(φ−1)(1−γ)/(κφ)]^{1/2} = ȳ_N` at every date (unique). -/
theorem laborSupply_140 {E : Economy} (hE : E.Valid) {φ : ℝ} (hφ : 1 < φ) {Q : Prices}
    {B0 Mm1 : ℝ} {M : ℕ → ℝ} {c : ℕ → Choice}
    (heq : IsEquilibrium (wageEconomy E φ) Q B0 Mm1 M c) (t : ℕ) :
    (c t).y = sqrt ((φ - 1) * (1 - E.γ) / (E.κ * φ)) ∧
      (c t).cN = sqrt ((φ - 1) * (1 - E.γ) / (E.κ * φ)) :=
  output_93 (wageEconomy_valid hE hφ) heq t

/-- EXISTENCE of the flexible-wage steady state (O&R p. 708, "steady-state prices ... are
determined as before"): for every `M̄ > 0` the §10.2 steady-state construction with `φ` in place
of `θ` is an equilibrium of the wage economy (specialisation of
`NontradablesModel.steadyState_isEquilibrium`). -/
theorem wage_steadyState_isEquilibrium {E : Economy} (hE : E.Valid)
    (hβr : E.β * (1 + E.r) = 1) {φ : ℝ} (hφ : 1 < φ) {Mbar : ℝ} (hM0 : 0 < Mbar) :
    (steadyPrices (wageEconomy E φ) Mbar).Valid E.r ∧
      IsEquilibrium (wageEconomy E φ) (steadyPrices (wageEconomy E φ) Mbar) 0 Mbar
        (fun _ => Mbar) (steadyChoice (wageEconomy E φ) Mbar) :=
  steadyState_isEquilibrium (wageEconomy_valid hE hφ) hβr hM0

/-! ## Preset wages (§10.4.1.3) -/

/-- Zero profits with PRESET wages (O&R p. 709): with symmetric wages the wage index equals the
wage, so the competitive firm's zero-profit condition `P_N = W` gives `P_{N,1} = w_1`; with
`w_1 = w_0` preset, `P_{N,1} = P_{N,0}` even though `P_N` is flexible. -/
theorem presetWage_price [Nonempty ι] {ω : ι → ℝ} {φ w0 w1 PN0 PN1 : ℝ} (hφ : 1 < φ)
    (hω1 : ∑ i, ω i = 1) (hw0 : 0 < w0) (hpre : w1 = w0)
    (hzp0 : PN0 = wageIndex ω φ (fun _ => w0)) (hzp1 : PN1 = wageIndex ω φ (fun _ => w1)) :
    PN1 = w1 ∧ PN1 = PN0 := by
  have h0 := (symmetric_wages (Y := 1) hφ hω1 hw0 one_pos).1
  have h1 := (symmetric_wages (Y := 1) hφ hω1 (hpre ▸ hw0) one_pos).1
  exact ⟨hzp1.trans h1, by rw [hzp1, h1, hzp0, h0, hpre]⟩

/-- THE PRESET-WAGE SHORT RUN IS IDENTICAL TO §10.2 (O&R p. 709): the preset-wage shock path
(`P_N` at its preset level `w_0`, labour demand-determined, rationing allowed) is an equilibrium
IF AND ONLY IF `x` solves the SAME impact equation as in §10.2 and `x² ≤ φ/(φ−1)` (the marginal
utility of the preset real wage is at least the marginal disutility of work). -/
theorem presetWage_equilibrium_iff {E : Economy} (hE : E.Valid) (hβr : E.β * (1 + E.r) = 1)
    {φ M0 μ x : ℝ} (hφ : 1 < φ) (hM0 : 0 < M0) (hμ : 0 < μ) (hx : 0 < x) :
    ((shockPrices (wageEconomy E φ) M0 μ x).Valid E.r ∧
      IsStickyEquilibrium (wageEconomy E φ) (shockPrices (wageEconomy E φ) M0 μ x) 0 M0
        (fun _ => μ * M0) (shockChoice (wageEconomy E φ) M0 μ x)) ↔
      impactGap E.β E.γ E.ε μ x = 0 ∧ x ^ 2 ≤ φ / (φ - 1) :=
  shock_equilibrium_iff (wageEconomy_valid hE hφ) hβr hM0 hμ hx

/-- THE IDENTICAL IMPACT RESPONSE (O&R p. 709, "one arrives at the IDENTICAL expression (99)"):
the impact response of the preset-wage economy coincides with that of the preset-price economy
with the same `β, γ, ε`, whatever `θ` and `φ`. -/
theorem presetWage_same_impact {E : Economy} (hE : E.Valid) (hβr : E.β * (1 + E.r) = 1)
    {φ M0 μ x x' : ℝ} (hφ : 1 < φ) (hM0 : 0 < M0) (hμ : 0 < μ) (hx : 0 < x) (hx' : 0 < x')
    (hprice : (shockPrices E M0 μ x).Valid E.r ∧
      IsStickyEquilibrium E (shockPrices E M0 μ x) 0 M0 (fun _ => μ * M0)
        (shockChoice E M0 μ x))
    (hwage : (shockPrices (wageEconomy E φ) M0 μ x').Valid E.r ∧
      IsStickyEquilibrium (wageEconomy E φ) (shockPrices (wageEconomy E φ) M0 μ x') 0 M0
        (fun _ => μ * M0) (shockChoice (wageEconomy E φ) M0 μ x')) :
    x' = x := by
  obtain ⟨hF, _⟩ := (shock_equilibrium_iff hE hβr hM0 hμ hx).mp hprice
  obtain ⟨hF', _⟩ := (presetWage_equilibrium_iff hE hβr hφ hM0 hμ hx').mp hwage
  obtain ⟨hβ, hβ1, _, hγ0, hγ1, _, hε, _, _, _⟩ := hE
  obtain ⟨z, _, _, _, huniq⟩ := impact_exists_unique hβ hβ1 hγ0 hγ1 hε hμ
  rw [huniq x' hx' hF', huniq x hx hF]

/-- (99) and exact overshooting with preset wages (O&R p. 709): on any preset-wage equilibrium
path after `μ > 1`, the exchange rate overshoots iff `ε > 1`. -/
theorem presetWage_overshoots_iff {E : Economy} (hE : E.Valid) (hβr : E.β * (1 + E.r) = 1)
    {φ M0 μ x PTstar : ℝ} (hφ : 1 < φ) (hM0 : 0 < M0) (hμ : 1 < μ) (hx : 0 < x)
    (hs : 0 < PTstar) (hQ : (shockPrices (wageEconomy E φ) M0 μ x).Valid E.r)
    (heq : IsStickyEquilibrium (wageEconomy E φ) (shockPrices (wageEconomy E φ) M0 μ x) 0 M0
      (fun _ => μ * M0) (shockChoice (wageEconomy E φ) M0 μ x)) :
    exchangeRate PTstar ((shockPrices (wageEconomy E φ) M0 μ x).PT 1)
        < exchangeRate PTstar ((shockPrices (wageEconomy E φ) M0 μ x).PT 0) ↔ 1 < E.ε :=
  exchangeRate_overshoots_iff (wageEconomy_valid hE hφ) hβr hM0 hμ hx hs hQ heq

/-- The essential welfare implication with preset wages (O&R p. 709, "the shock once again
coordinates an efficient increase in labor supply"): on the preset-wage path after `μ > 1` with
`x² ≤ φ/(φ−1)`, lifetime utility strictly rises; the real gain is
`(1−γ)[log x − ((φ−1)/(2φ))(x² − 1)] > 0`. -/
theorem presetWage_welfare_gain_pos {E : Economy} (hE : E.Valid) {φ M0 μ x : ℝ} (hφ : 1 < φ)
    (hM0 : 0 < M0) (hμ : 1 < μ) (hx : 0 < x) (hF : impactGap E.β E.γ E.ε μ x = 0)
    (hdd : x ^ 2 ≤ φ / (φ - 1)) :
    0 < realGain φ E.γ x ∧
      ∑' t, E.β ^ t * periodU (wageEconomy E φ) (steadyPrices (wageEconomy E φ) M0) t
          (steadyChoice (wageEconomy E φ) M0 t)
        < ∑' t, E.β ^ t * periodU (wageEconomy E φ) (shockPrices (wageEconomy E φ) M0 μ x) t
          (shockChoice (wageEconomy E φ) M0 μ x t) := by
  have hE' := wageEconomy_valid hE hφ
  obtain ⟨hβ, hβ1, _, hγ0, hγ1, _, hε, _, _, _⟩ := hE
  exact ⟨realGain_pos hφ hγ1 (one_lt_root hβ hβ1 hγ0 hγ1 hε hμ hx hF) hdd,
    welfare_gain_pos hE' hM0 hμ hx hF hdd⟩

end ObstfeldRogoff.StickyPriceModels.PresetWagesSmallCountry

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Cash in advance and the credibility of monetary policy (Exercise 4)

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, Chapter 10,
Exercise 4, pp. 713–714 (a cash-in-advance variant of the §10.2 model, pp. 689–694). Utility is
`γ log C_T + (1−γ) log C_N − (κ/2) y_N²` (no money in utility), with the contemporaneous
cash-in-advance constraint `M ≥ P_T C_T + P_N C_N`, holding with equality, and currency pays
the nominal interest rate (so the timing of the constraint introduces no wedge).

* (a) The CIA household problem is a genuine infinite-horizon problem; its first-order conditions
  (87), (89), (90) with no-Ponzi and the transversality condition are NECESSARY AND SUFFICIENT;
  in every symmetric flexible-price equilibrium `ȳ_N = C̄_N = [(θ−1)(1−γ)/(κθ)]^{1/2}` (unique),
  and the steady state exists.
* (b) The planner's output `ȳ_N^{PLAN} = ((1−γ)/κ)^{1/2}` is the unique maximiser, and
  `ȳ_N < ȳ_N^{PLAN}`.
* (c) EXACT (no linearisation): CIA with equality and (89) give `M = P_N C_N/(1−γ)`; with `P_N`
  preset at the level `(1−γ)M^e/ȳ_N` consistent with `M^e`, `y_N = C_N = (M/M^e) ȳ_N` and
  `P_T = γM/ȳ_T`. Finite-state version: with a random money supply on finitely many states and
  `M^e = E[M]`, the formula holds state by state and `E[y_N] = ȳ_N`.
* (d) The one-shot assumption spelled out: with expectations and the future real allocation
  held fixed, the authority's objective `U_t − (χ/2)(P_{T,t}/P_{T,t−1})²` differs across choices of
  `M_t` exactly by `(1−γ) log C_N − (κ/2) y_N² − (χ/2)(P_{T,t}/P_{T,t−1})²`; if next period's
  inflation penalty were counted with `M_{t+1}` fixed in levels, the extra term
  `−β(χ/2)(M_{t+1}/M_t)²` would appear — the one-shot game ignores it.
* (e) The best response is unique (strict concavity) and the one-shot equilibrium is UNIQUE:
  `μ = ((1−γ)/(χθ))^{1/2} = {κ[(ȳ_N^{PLAN})² − ȳ_N²]/χ}^{1/2}`. The penalty in the book is on the
  GROSS inflation factor (minimised at zero money): with the conventional `(π − 1)²` penalty the
  unique equilibrium is instead `μ = [1 + (1 + 4(1−γ)/(θχ))^{1/2}]/2 > 1`, an inflation bias
  relative to the commitment optimum `μ = 1`; under the literal gross penalty the commitment
  problem has no optimum at all.

The book's `χ` in (d) is the weight on the inflation penalty; here it is `E.χ` (the §10.2
real-balance parameter, which the CIA model does not otherwise use), and `E.ε` is unused.
-/

namespace ObstfeldRogoff.StickyPriceModels.CashInAdvanceCredibility

open Real Filter Topology Finset
open ObstfeldRogoff.StickyPriceModels.NontradablesModel
open ObstfeldRogoff.StickyPriceModels.NontradablesOvershooting

/-! ## (a) The cash-in-advance household problem -/

/-- Period utility of Exercise 4, p. 713: `γ log C_T + (1−γ) log C_N − (κ/2) y_N²`. -/
noncomputable def ciaU (E : Economy) (_t : ℕ) (c : Choice) : ℝ :=
  E.γ * log c.cT + (1 - E.γ) * log c.cN - E.κ / 2 * c.y ^ 2

/-- Net real resources in the CIA economy (O&R p. 714): currency pays the nominal interest
rate, so money and bonds earn the same return and money drops out of the wealth recursion;
`rev t y` is real revenue from selling `y` (the demand curve (86) under flexible prices, the
preset price times `y` otherwise). -/
noncomputable def ciaNetRes (E : Economy) (Q : Prices) (rev : ℕ → ℝ → ℝ) (t : ℕ) (c : Choice) :
    ℝ :=
  E.yT - Q.τ t + rev t c.y - relPrice Q t * c.cN - c.cT

/-- Admissible CIA choices: positive, the cash-in-advance constraint with equality
`M_t = P_{T,t} C_T + P_{N,t} C_N`, and output in the admissible set `Ys t` (O&R p. 713). -/
def ciaSet (Q : Prices) (Ys : ℕ → Set ℝ) (t : ℕ) : Set Choice :=
  {c | c ∈ posChoice ∧ c.money = Q.PT t * c.cT + Q.PN t * c.cN ∧ c.y ∈ Ys t}

/-- Optimality in the CIA economy from initial real wealth `A0` (O&R Ex. 4). -/
def CIAOptimal (E : Economy) (Q : Prices) (rev : ℕ → ℝ → ℝ) (Ys : ℕ → Set ℝ) (A0 : ℝ)
    (c : ℕ → Choice) : Prop :=
  IsOptimal E.β E.r A0 (ciaU E) (ciaNetRes E Q rev) (ciaSet Q Ys) c

/-- The flexible-price regime: revenue on the demand curve (86), any positive output. -/
noncomputable def flexRev (E : Economy) (Q : Prices) : ℕ → ℝ → ℝ := realRevenue E Q

/-- Any positive output is admissible under flexible prices (O&R Ex. 4(a)). -/
def flexYs : ℕ → Set ℝ := fun _ => Set.Ioi 0

/-- SUFFICIENCY in the CIA economy (O&R Ex. 4(a)): under flexible prices, an admissible plan with
summable utility satisfying (87), (89), (90), no-Ponzi and the transversality condition is
optimal. -/
theorem ciaOptimal_of_foc {E : Economy} {Q : Prices} (hE : E.Valid) (hQ : Q.Valid E.r)
    {A0 : ℝ} {c : ℕ → Choice} (hc : ∀ t, c t ∈ ciaSet Q flexYs t)
    (hsum : Summable fun t => E.β ^ t * ciaU E t (c t)) (heu : EulerFOC E c)
    (hN : IntraFOC E Q c) (hL : LabourFOC E Q c)
    (hnp : NoPonzi E.r (wealth E.r A0 (ciaNetRes E Q (flexRev E Q)) c))
    (htv : LiminfNonpos E.r (wealth E.r A0 (ciaNetRes E Q (flexRev E Q)) c)) :
    CIAOptimal E Q (flexRev E Q) flexYs A0 c := by
  have hE' := hE
  obtain ⟨hβ, _, hr, hγ0, hγ1, _, _, hκ, hθ, _⟩ := hE'
  have hpos : ∀ t, c t ∈ posChoice := fun t => (hc t).1
  refine isOptimal_of_saddle (μ0 := E.γ / (c 0).cT) hr (div_pos hγ0 (hpos 0).1).le hc hsum hnp
    htv ?_
  intro t y hy
  obtain ⟨ha, hb, _, hq⟩ := hpos t
  obtain ⟨⟨ha', hb', _, hq'⟩, _, _⟩ := hy
  obtain ⟨hT, hPN, hA, _⟩ := hQ t
  set lam := E.γ / (c t).cT with hlam
  set ρ := relPrice Q t
  set K := Q.CA t ^ (1 / E.θ)
  set s := (E.θ - 1) / E.θ with hs
  have hK : 0 < K := rpow_pos_of_pos hA _
  have hρ : 0 < ρ := div_pos hPN hT
  have hs0 : 0 < s := div_pos (by linarith) (by linarith)
  have hs1 : s ≤ 1 := by rw [hs, div_le_one (by linarith)]; linarith
  have hlam0 : 0 < lam := div_pos hγ0 ha
  have hA' := log_tangent hγ0.le ha' ha
  have hB' := log_tangent (k := 1 - E.γ) (by linarith) hb' hb
  have hBr : (1 - E.γ) / (c t).cN = lam * ρ := hN t
  have hD1 := rpow_le_tangent hs0 hs1 hq hq'
  have hD2 : lam * ρ * K * y.y ^ s ≤ lam * ρ * K * (c t).y ^ s
      + E.κ * (c t).y * (y.y - (c t).y) := by
    have hL' : E.κ * (c t).y = lam * ρ * K * (s * (c t).y ^ (s - 1)) := by rw [hL t]; ring
    have := mul_le_mul_of_nonneg_left hD1 (by positivity : 0 ≤ lam * ρ * K)
    rw [hL']; linarith
  have hD3 : -(E.κ / 2) * y.y ^ 2 ≤ -(E.κ / 2) * (c t).y ^ 2 - E.κ * (c t).y * (y.y - (c t).y) := by
    have := mul_nonneg (by linarith : 0 ≤ E.κ / 2) (sq_nonneg (y.y - (c t).y))
    nlinarith
  have hpt : ciaU E t y + lam * ciaNetRes E Q (flexRev E Q) t y
      ≤ ciaU E t (c t) + lam * ciaNetRes E Q (flexRev E Q) t (c t) := by
    simp only [ciaU, ciaNetRes, flexRev, realRevenue]
    rw [hBr] at hB'
    have e1 : (1 - E.γ) / (c t).cN * y.cN = lam * ρ * y.cN := by rw [hBr]
    have e2 : (1 - E.γ) / (c t).cN * (c t).cN = lam * ρ * (c t).cN := by rw [hBr]
    linarith [hA', hB', hD2, hD3, e1, e2]
  have hd := discounted_mu_of_euler hβ hr hpos heu hγ0 t
  have hβt : 0 ≤ E.β ^ t := pow_nonneg hβ.le t
  have key := mul_le_mul_of_nonneg_left hpt hβt
  have e : ∀ z : Choice, E.β ^ t * (ciaU E t z + lam * ciaNetRes E Q (flexRev E Q) t z)
      = E.β ^ t * ciaU E t z + E.γ / (c 0).cT * (disc E.r t * ciaNetRes E Q (flexRev E Q) t z) := by
    intro z
    have h2 : E.γ / (c 0).cT * (disc E.r t * ciaNetRes E Q (flexRev E Q) t z)
        = (E.β ^ t * (E.γ / (c t).cT)) * ciaNetRes E Q (flexRev E Q) t z := by rw [hd]; ring
    rw [h2]; ring
  rw [e, e] at key
  exact key

/-- NECESSITY of (89) in the CIA economy, in ANY pricing regime (O&R Ex. 4): reallocating
spending between tradables and nontradables (with money adjusting to keep the CIA constraint) is
always feasible. -/
theorem cia_intra_of_optimal {E : Economy} {Q : Prices} (hE : E.Valid) (hQ : Q.Valid E.r)
    {rev : ℕ → ℝ → ℝ} {Ys : ℕ → Set ℝ} {A0 : ℝ} {c : ℕ → Choice}
    (hopt : CIAOptimal E Q rev Ys A0 c) : IntraFOC E Q c := by
  obtain ⟨hβ, _, hr, hγ0, hγ1, _, _, _, _, _⟩ := hE
  intro t
  obtain ⟨⟨ha, hb, hn, hq⟩, _, hys⟩ := hopt.1 t
  obtain ⟨hT, hPN, _, _⟩ := hQ t
  set ρ := relPrice Q t
  set g : ℝ → Choice := fun η => ⟨(c t).cT - ρ * η, (c t).cN + η,
    Q.PT t * ((c t).cT - ρ * η) + Q.PN t * ((c t).cN + η), (c t).y⟩ with hg
  have hmax : IsLocalMax (fun η => ciaU E t (g η)) 0 := by
    have h1 : ∀ᶠ η in 𝓝 (0 : ℝ), 0 < (c t).cT - ρ * η :=
      (continuous_const.sub (continuous_const.mul continuous_id)).continuousAt.eventually
        (lt_mem_nhds (by simpa using ha))
    have h2 : ∀ᶠ η in 𝓝 (0 : ℝ), 0 < (c t).cN + η :=
      (continuous_const.add continuous_id).continuousAt.eventually
        (lt_mem_nhds (by simpa using hb))
    filter_upwards [h1, h2] with η e1 e2
    have hmem : g η ∈ ciaSet Q Ys t := ⟨⟨e1, e2, by positivity, hq⟩, rfl, hys⟩
    have hres : ciaNetRes E Q rev t (c t) ≤ ciaNetRes E Q rev t (g η) := by
      simp only [ciaNetRes, g]; linarith
    have h := perturb_le_gen hr hβ hopt t g hmem hres
    have hg0 : ciaU E t (g 0) = ciaU E t (c t) := by simp [g, ciaU]
    rw [hg0]; exact h
  have hfun : (fun η => ciaU E t (g η)) = fun η =>
      E.γ * log ((c t).cT - ρ * η) + (1 - E.γ) * log ((c t).cN + η)
        - E.κ / 2 * (c t).y ^ 2 := by
    funext η; simp only [ciaU, g]
  have hd1 : HasDerivAt (fun η => (c t).cT - ρ * η) (-ρ) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul ρ).const_sub (c t).cT
  have hd2 : HasDerivAt (fun η => (c t).cN + η) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_add (c t).cN
  have hd : HasDerivAt (fun η => ciaU E t (g η))
      (E.γ * (-ρ / (c t).cT) + (1 - E.γ) * (1 / (c t).cN)) 0 := by
    rw [hfun]
    have e1 := (hd1.log (by simpa using ha.ne')).const_mul E.γ
    have e2 := (hd2.log (by simpa using hb.ne')).const_mul (1 - E.γ)
    simp only [mul_zero, sub_zero, add_zero] at e1 e2
    exact (e1.add e2).sub_const _
  have h0 := hmax.hasDerivAt_eq_zero hd
  field_simp at h0 ⊢
  linarith

/-- NECESSITY of the Euler equation (87) in the CIA economy, in ANY pricing regime
(O&R Ex. 4): shifting tradables consumption between `t` and `t+1` (money adjusting to keep the
CIA constraint) is always feasible. -/
theorem cia_euler_of_optimal {E : Economy} {Q : Prices} (hE : E.Valid) (hQ : Q.Valid E.r)
    {rev : ℕ → ℝ → ℝ} {Ys : ℕ → Set ℝ} {A0 : ℝ} {c : ℕ → Choice}
    (hopt : CIAOptimal E Q rev Ys A0 c) : EulerFOC E c := by
  obtain ⟨hβ, _, hr, hγ0, _, _, _, _, _, _⟩ := hE
  intro t
  obtain ⟨⟨ha, hb, _, hq⟩, _, hys⟩ := hopt.1 t
  obtain ⟨⟨ha', hb', _, hq'⟩, _, hys'⟩ := hopt.1 (t + 1)
  obtain ⟨hT, hN, _, _⟩ := hQ t
  obtain ⟨hT', hN', _, _⟩ := hQ (t + 1)
  have htt : t + 1 ≠ t := Nat.succ_ne_self t
  set x' : ℝ → ℕ → Choice := fun η s =>
    if s = t then ⟨(c t).cT + η, (c t).cN, Q.PT t * ((c t).cT + η) + Q.PN t * (c t).cN,
      (c t).y⟩
    else if s = t + 1 then
      ⟨(c (t + 1)).cT - (1 + E.r) * η, (c (t + 1)).cN,
        Q.PT (t + 1) * ((c (t + 1)).cT - (1 + E.r) * η) + Q.PN (t + 1) * (c (t + 1)).cN,
        (c (t + 1)).y⟩
    else c s with hx'
  set f : ℝ → ℝ := fun η => E.β ^ t * (E.γ * log ((c t).cT + η))
    + E.β ^ (t + 1) * (E.γ * log ((c (t + 1)).cT - (1 + E.r) * η)) with hf
  have hloc : IsLocalMax f 0 := by
    have h1 : ∀ᶠ η in 𝓝 (0 : ℝ), 0 < (c t).cT + η :=
      (continuous_const.add continuous_id).continuousAt.eventually
        (lt_mem_nhds (by simpa using ha))
    have h2 : ∀ᶠ η in 𝓝 (0 : ℝ), 0 < (c (t + 1)).cT - (1 + E.r) * η :=
      (continuous_const.sub (continuous_const.mul continuous_id)).continuousAt.eventually
        (lt_mem_nhds (by simpa using ha'))
    filter_upwards [h1, h2] with η e1 e2
    have hS : ∀ s ∉ ({t, t + 1} : Finset ℕ), x' η s = c s := by
      intro s hs
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hs
      simp [x', hs.1, hs.2]
    have hadm : ∀ s, x' η s ∈ ciaSet Q Ys s := by
      intro s
      by_cases hs1 : s = t
      · subst hs1; simp only [x', ↓reduceIte]
        exact ⟨⟨e1, hb, by positivity, hq⟩, rfl, hys⟩
      by_cases hs2 : s = t + 1
      · subst hs2; simp only [x', htt, ↓reduceIte]
        exact ⟨⟨e2, hb', by positivity, hq'⟩, rfl, hys'⟩
      rw [hS s (by simp [hs1, hs2])]; exact hopt.1 s
    have hpv : 0 ≤ ∑ s ∈ ({t, t + 1} : Finset ℕ),
        disc E.r s * (ciaNetRes E Q rev s (x' η s) - ciaNetRes E Q rev s (c s)) := by
      rw [Finset.sum_pair htt.symm]
      simp only [x', htt, ↓reduceIte, ciaNetRes]
      have := disc_succ_mul hr t
      nlinarith
    have h := perturb_utility_le_of_pv hr hopt hadm hS hpv
    rw [Finset.sum_pair htt.symm] at h
    simp only [x', htt, ↓reduceIte, ciaU] at h
    simp only [hf, add_zero, mul_zero, sub_zero]
    linarith
  have hd1 : HasDerivAt (fun η => (c t).cT + η) 1 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).const_add (c t).cT
  have hd2 : HasDerivAt (fun η => (c (t + 1)).cT - (1 + E.r) * η) (-(1 + E.r)) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul (1 + E.r)).const_sub (c (t + 1)).cT
  have hd : HasDerivAt f (E.β ^ t * (E.γ * (1 / (c t).cT))
      + E.β ^ (t + 1) * (E.γ * (-(1 + E.r) / (c (t + 1)).cT))) 0 := by
    have e1 := ((hd1.log (by simpa using ha.ne')).const_mul E.γ).const_mul (E.β ^ t)
    have e2 := ((hd2.log (by simpa using ha'.ne')).const_mul E.γ).const_mul (E.β ^ (t + 1))
    simp only [add_zero, mul_zero, sub_zero] at e1 e2
    exact e1.add e2
  have h0 := hloc.hasDerivAt_eq_zero hd
  have hβt : 0 < E.β ^ t := pow_pos hβ t
  rw [pow_succ] at h0
  have h3 : E.β ^ t * (E.γ / (c t).cT - E.β * (1 + E.r) * (E.γ / (c (t + 1)).cT)) = 0 := by
    rw [← h0]; field_simp; ring
  have := (mul_eq_zero.mp h3).resolve_left hβt.ne'
  linarith

/-- NECESSITY of the output condition behind (90) in the flexible-price CIA economy
(O&R Ex. 4(a)). -/
theorem cia_labour_of_optimal {E : Economy} {Q : Prices} (hE : E.Valid) (hQ : Q.Valid E.r)
    {A0 : ℝ} {c : ℕ → Choice} (hopt : CIAOptimal E Q (flexRev E Q) flexYs A0 c) :
    LabourFOC E Q c := by
  obtain ⟨hβ, _, hr, hγ0, hγ1, _, _, _, hθ, _⟩ := hE
  intro t
  obtain ⟨⟨ha, hb, _, hq⟩, _, _⟩ := hopt.1 t
  obtain ⟨hT, hN, _, _⟩ := hQ t
  set R := realRevenue E Q t
  set s := (E.θ - 1) / E.θ
  set K := Q.CA t ^ (1 / E.θ)
  set ρ := relPrice Q t
  have hRd : HasDerivAt R (ρ * (s * (c t).y ^ (s - 1) * K)) (c t).y := by
    have := ((hasDerivAt_rpow_const (p := s) (Or.inl hq.ne')).mul_const K).const_mul ρ
    exact this
  have hRc : HasDerivAt (fun η => R ((c t).y + η)) (ρ * (s * (c t).y ^ (s - 1) * K)) 0 := by
    have hR0 : HasDerivAt R (ρ * (s * (c t).y ^ (s - 1) * K)) ((c t).y + 0) := by
      simpa using hRd
    have := hR0.comp (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).const_add (c t).y)
    convert this using 1 <;> first | rfl | simp
  have hd1 : HasDerivAt (fun η => (c t).cT + (R ((c t).y + η) - R (c t).y))
      (ρ * (s * (c t).y ^ (s - 1) * K)) 0 := by
    simpa using (hRc.sub_const (R (c t).y)).const_add (c t).cT
  set g : ℝ → Choice := fun η => ⟨(c t).cT + (R ((c t).y + η) - R (c t).y), (c t).cN,
    Q.PT t * ((c t).cT + (R ((c t).y + η) - R (c t).y)) + Q.PN t * (c t).cN,
    (c t).y + η⟩ with hg
  have hmax : IsLocalMax (fun η => ciaU E t (g η)) 0 := by
    have h1 : ∀ᶠ η in 𝓝 (0 : ℝ), 0 < (c t).cT + (R ((c t).y + η) - R (c t).y) :=
      hd1.continuousAt.eventually (lt_mem_nhds (by simpa using ha))
    have h2 : ∀ᶠ η in 𝓝 (0 : ℝ), 0 < (c t).y + η :=
      (continuous_const.add continuous_id).continuousAt.eventually
        (lt_mem_nhds (by simpa using hq))
    filter_upwards [h1, h2] with η e1 e2
    have hmem : g η ∈ ciaSet Q flexYs t :=
      ⟨⟨e1, hb, by positivity, e2⟩, rfl, Set.mem_Ioi.mpr e2⟩
    have hres : ciaNetRes E Q (flexRev E Q) t (c t) ≤ ciaNetRes E Q (flexRev E Q) t (g η) := by
      simp only [ciaNetRes, flexRev, g, R]; linarith
    have h := perturb_le_gen hr hβ hopt t g hmem hres
    have hg0 : ciaU E t (g 0) = ciaU E t (c t) := by simp [g, ciaU]
    rw [hg0]; exact h
  have hfun : (fun η => ciaU E t (g η)) = fun η =>
      E.γ * log ((c t).cT + (R ((c t).y + η) - R (c t).y)) - E.κ / 2 * ((c t).y + η) ^ 2
        + (1 - E.γ) * log (c t).cN := by
    funext η; simp only [ciaU, g]; ring
  have hsq : HasDerivAt (fun η => ((c t).y + η) ^ 2) (2 * (c t).y) 0 := by
    have := (hasDerivAt_pow 2 ((c t).y + 0)).comp (0 : ℝ)
      ((hasDerivAt_id (0 : ℝ)).const_add (c t).y)
    convert this using 1 <;> first | rfl | simp
  have hd : HasDerivAt (fun η => ciaU E t (g η))
      (E.γ * (ρ * (s * (c t).y ^ (s - 1) * K) / (c t).cT) - E.κ / 2 * (2 * (c t).y)) 0 := by
    rw [hfun]
    have e1 := (hd1.log (by simpa using ha.ne')).const_mul E.γ
    simp only [sub_self, add_zero] at e1
    exact ((e1.sub (hsq.const_mul (E.κ / 2)))).add_const _
  have h0 := hmax.hasDerivAt_eq_zero hd
  have : E.κ * (c t).y = E.γ / (c t).cT * ρ * (s * ((c t).y ^ (s - 1) * K)) := by
    field_simp at h0 ⊢; linarith
  exact this

/-- NECESSITY of the transversality condition (liminf form) in the CIA economy (O&R (16)). -/
theorem cia_liminfNonpos {E : Economy} {Q : Prices} (hE : E.Valid) (hQ : Q.Valid E.r)
    {rev : ℕ → ℝ → ℝ} {Ys : ℕ → Set ℝ} {A0 : ℝ} {c : ℕ → Choice}
    (hopt : CIAOptimal E Q rev Ys A0 c) :
    LiminfNonpos E.r (wealth E.r A0 (ciaNetRes E Q rev) c) := by
  obtain ⟨_, _, hr, hγ0, _, _, _, _, _, _⟩ := hE
  obtain ⟨hT, hN, _, _⟩ := hQ 0
  refine liminfNonpos_of_isOptimal hr hopt ?_
  intro η hη
  obtain ⟨⟨ha, hb, _, hq⟩, _, hys⟩ := hopt.1 0
  refine ⟨⟨(c 0).cT + η, (c 0).cN, Q.PT 0 * ((c 0).cT + η) + Q.PN 0 * (c 0).cN, (c 0).y⟩,
    ⟨⟨by linarith, hb, by positivity, hq⟩, rfl, hys⟩, ?_, ?_⟩
  · simp only [ciaNetRes]; linarith
  · simp only [ciaU]
    have := log_lt_log ha (by linarith : (c 0).cT < (c 0).cT + η)
    nlinarith

/-- EX. 4(a) MAIN THEOREM: under flexible prices a CIA plan is optimal IF AND ONLY IF it has
summable utility and satisfies (87), (89), (90), no-Ponzi and the transversality condition. -/
theorem ciaOptimal_iff {E : Economy} {Q : Prices} (hE : E.Valid) (hQ : Q.Valid E.r)
    {A0 : ℝ} {c : ℕ → Choice} :
    CIAOptimal E Q (flexRev E Q) flexYs A0 c ↔
      (∀ t, c t ∈ ciaSet Q flexYs t) ∧ Summable (fun t => E.β ^ t * ciaU E t (c t)) ∧
      EulerFOC E c ∧ IntraFOC E Q c ∧ LabourFOC E Q c ∧
      NoPonzi E.r (wealth E.r A0 (ciaNetRes E Q (flexRev E Q)) c) ∧
      LiminfNonpos E.r (wealth E.r A0 (ciaNetRes E Q (flexRev E Q)) c) := by
  constructor
  · intro h
    exact ⟨h.1, h.2.2.1, cia_euler_of_optimal hE hQ h, cia_intra_of_optimal hE hQ h,
      cia_labour_of_optimal hE hQ h, h.2.1, cia_liminfNonpos hE hQ h⟩
  · rintro ⟨hc, hs, he, hn, hl, hnp, htv⟩
    exact ciaOptimal_of_foc hE hQ hc hs he hn hl hnp htv

/-- EX. 4(a), p. 714: in every symmetric flexible-price CIA equilibrium (`y_N = C_N = C^A_N`),
nontradables output and consumption equal `ȳ_N = [(θ−1)(1−γ)/(κθ)]^{1/2}` at every date. -/
theorem cia_flexible_output {E : Economy} {Q : Prices} (hE : E.Valid) (hQ : Q.Valid E.r)
    {A0 : ℝ} {c : ℕ → Choice} (hopt : CIAOptimal E Q (flexRev E Q) flexYs A0 c)
    (hsym : ∀ t, (c t).y = (c t).cN ∧ Q.CA t = (c t).cN) (t : ℕ) :
    (c t).y = ybarN E ∧ (c t).cN = ybarN E := by
  have hpos : ∀ t, c t ∈ posChoice := fun t => (hopt.1 t).1
  have h90 := labour_90 hE hpos (cia_intra_of_optimal hE hQ hopt)
    (cia_labour_of_optimal hE hQ hopt) t
  obtain ⟨_, _, _, _, hγ1, _, _, hκ, hθ, _⟩ := hE
  obtain ⟨hy, hA⟩ := hsym t
  rw [hA, ← hy] at h90
  have hq := (hpos t).2.2.2
  set x := (c t).y
  have hθ0 : 0 < E.θ := by linarith
  have e1 : x ^ ((E.θ + 1) / E.θ) = x * x ^ (1 / E.θ) := by
    rw [show (E.θ + 1) / E.θ = 1 + 1 / E.θ by field_simp, rpow_add hq, rpow_one]
  rw [e1] at h90
  have hx1 : 0 < x ^ (1 / E.θ) := rpow_pos_of_pos hq _
  have hsq : x ^ 2 = (E.θ - 1) * (1 - E.γ) / (E.κ * E.θ) := by
    field_simp at h90 ⊢
    nlinarith
  have hxy : x = ybarN E := by
    unfold ybarN; rw [← hsq, sqrt_sq hq.le]
  exact ⟨hxy, hy ▸ hxy⟩

/-- The CIA steady-state prices (O&R Ex. 4(a)): any `P_T > 0`, `P_N = (P_N/P_T)‾ P_T`,
aggregate demand `ȳ_N`, zero taxes. -/
noncomputable def ciaSteadyPrices (E : Economy) (pT : ℝ) : Prices :=
  ⟨fun _ => pT, fun _ => relPriceBar E * pT, fun _ => ybarN E, fun _ => 0⟩

/-- The CIA steady-state allocation `(ȳ_T, ȳ_N, M = P_T ȳ_T + P_N ȳ_N, ȳ_N)` (O&R Ex. 4(a)). -/
noncomputable def ciaSteadyChoice (E : Economy) (pT : ℝ) : ℕ → Choice :=
  fun _ => ⟨E.yT, ybarN E, pT * E.yT + relPriceBar E * pT * ybarN E, ybarN E⟩

/-- EXISTENCE in Ex. 4(a): the CIA steady state is a genuine infinite-horizon household optimum
(zero initial wealth) with `y_N = C_N = C^A_N = ȳ_N`. -/
theorem cia_steadyState_optimal {E : Economy} (hE : E.Valid) (hβr : E.β * (1 + E.r) = 1)
    {pT : ℝ} (hT : 0 < pT) :
    (ciaSteadyPrices E pT).Valid E.r ∧
      CIAOptimal E (ciaSteadyPrices E pT) (flexRev E (ciaSteadyPrices E pT)) flexYs 0
        (ciaSteadyChoice E pT) ∧
      ∀ t, (ciaSteadyChoice E pT t).y = (ciaSteadyChoice E pT t).cN ∧
        (ciaSteadyPrices E pT).CA t = (ciaSteadyChoice E pT t).cN := by
  have hE' := hE
  obtain ⟨hβ, hβ1, hr, hγ0, hγ1, _, _, hκ, hθ, hyT⟩ := hE'
  have hr0 : 0 < E.r := by nlinarith
  have hy := ybarN_pos hE
  have hrel := relPriceBar_pos hE
  set Q := ciaSteadyPrices E pT
  set c := ciaSteadyChoice E pT
  have hQ : Q.Valid E.r := by
    intro t
    refine ⟨hT, by simp only [Q, ciaSteadyPrices]; positivity, hy, ?_⟩
    simp only [userCost, Q, ciaSteadyPrices]
    rw [div_sub_div _ _ hT.ne' (mul_pos hr hT).ne']
    apply div_pos _ (mul_pos hT (mul_pos hr hT))
    nlinarith
  have hc : ∀ t, c t ∈ ciaSet Q flexYs t := fun t =>
    ⟨⟨hyT, hy, by simp only [c, ciaSteadyChoice]; positivity, hy⟩,
      by simp [c, Q, ciaSteadyChoice, ciaSteadyPrices],
      Set.mem_Ioi.mpr hy⟩
  have hw : ∀ t, wealth E.r 0 (ciaNetRes E Q (flexRev E Q)) c t = 0 := by
    intro t
    induction t with
    | zero => rfl
    | succ t ih =>
      rw [wealth, ih]
      have hrev : flexRev E Q t (c t).y = relPrice Q t * (c t).cN :=
        realRevenue_symm E Q t (by linarith) hy rfl
      simp only [ciaNetRes, hrev]
      simp [c, Q, ciaSteadyChoice, ciaSteadyPrices]
  have hdw : Tendsto (fun T => disc E.r T * wealth E.r 0 (ciaNetRes E Q (flexRev E Q)) c T)
      atTop (𝓝 0) := by simp_rw [hw, mul_zero]; exact tendsto_const_nhds
  refine ⟨hQ, ciaOptimal_of_foc hE hQ hc ?_ ?_ ?_ ?_
    (fun δ hδ => (hdw.eventually (lt_mem_nhds (by linarith : -δ < 0))).mono fun _ h => h.le)
    (fun δ hδ => (hdw.eventually (gt_mem_nhds hδ)).frequently.mono fun _ h => h.le),
    fun t => ⟨rfl, rfl⟩⟩
  · exact (summable_geometric_of_lt_one hβ.le hβ1).mul_right (ciaU E 0 (c 0))
  · intro t; simp only [c, ciaSteadyChoice]; rw [hβr, one_mul]
  · intro t
    simp only [c, ciaSteadyChoice, relPrice, Q, ciaSteadyPrices]
    rw [mul_div_cancel_right₀ _ hT.ne']
    unfold relPriceBar; field_simp
  · intro t
    simp only [c, ciaSteadyChoice, relPrice, Q, ciaSteadyPrices]
    rw [mul_div_cancel_right₀ _ hT.ne', ← rpow_add hy,
      show (E.θ - 1) / E.θ - 1 + 1 / E.θ = 0 by field_simp; ring, rpow_zero, mul_one]
    have hk := kappa_mul_ybarN_sq hE
    unfold relPriceBar
    field_simp at hk ⊢
    linarith

/-! ## (b) The planner -/

/-- The planner's output (Ex. 4(b), p. 714): `ȳ_N^{PLAN} = ((1−γ)/κ)^{1/2}`. -/
noncomputable def yPlan (E : Economy) : ℝ := sqrt ((1 - E.γ) / E.κ)

/-- Ex. 4(b): the planner, choosing `y_N = C_N` to maximise `(1−γ) log C_N − (κ/2) y_N²`, has the
UNIQUE optimum `ȳ_N^{PLAN}` (strict concavity). -/
theorem planner_unique {E : Economy} (hE : E.Valid) {y : ℝ} (hy : 0 < y) :
    (1 - E.γ) * log y - E.κ / 2 * y ^ 2 ≤ (1 - E.γ) * log (yPlan E) - E.κ / 2 * yPlan E ^ 2 ∧
      (y ≠ yPlan E →
        (1 - E.γ) * log y - E.κ / 2 * y ^ 2 < (1 - E.γ) * log (yPlan E) - E.κ / 2 * yPlan E ^ 2) :=
  by
  obtain ⟨_, _, _, _, hγ1, _, _, hκ, _, _⟩ := hE
  have hq : 0 < (1 - E.γ) / E.κ := div_pos (by linarith) hκ
  have hp : 0 < yPlan E := sqrt_pos.mpr hq
  have hp2 : yPlan E ^ 2 = (1 - E.γ) / E.κ := sq_sqrt hq.le
  have hlog := log_tangent (k := 1 - E.γ) (by linarith) hy hp
  have hkey : (1 - E.γ) / yPlan E = E.κ * yPlan E := by
    field_simp; rw [hp2]; field_simp
  rw [hkey] at hlog
  have hsq : -(E.κ / 2) * y ^ 2 = -(E.κ / 2) * yPlan E ^ 2 - E.κ * yPlan E * (y - yPlan E)
      - E.κ / 2 * (y - yPlan E) ^ 2 := by ring
  refine ⟨?_, fun hne => ?_⟩
  · have := mul_nonneg (by linarith : 0 ≤ E.κ / 2) (sq_nonneg (y - yPlan E))
    nlinarith
  · have hpos : 0 < (y - yPlan E) ^ 2 := by
      have : y - yPlan E ≠ 0 := sub_ne_zero.mpr hne
      positivity
    have := mul_pos (by linarith : 0 < E.κ / 2) hpos
    nlinarith

/-- Monopoly depresses output below the planner's level: `ȳ_N < ȳ_N^{PLAN}` (O&R Ex. 4(b), cf.
(25)). -/
theorem ybarN_lt_yPlan {E : Economy} (hE : E.Valid) : ybarN E < yPlan E := by
  obtain ⟨_, _, _, _, hγ1, _, _, hκ, hθ, _⟩ := hE
  unfold ybarN yPlan
  apply sqrt_lt_sqrt (div_nonneg (mul_nonneg (by linarith) (by linarith))
    (mul_nonneg hκ.le (by linarith)))
  rw [div_lt_div_iff₀ (by positivity) hκ]
  have : 0 < 1 - E.γ := by linarith
  nlinarith

/-- The gap used in Ex. 4(e): `κ[(ȳ_N^{PLAN})² − ȳ_N²] = (1−γ)/θ`. -/
theorem kappa_gap {E : Economy} (hE : E.Valid) :
    E.κ * (yPlan E ^ 2 - ybarN E ^ 2) = (1 - E.γ) / E.θ := by
  have hk := kappa_mul_ybarN_sq hE
  obtain ⟨_, _, _, _, hγ1, _, _, hκ, hθ, _⟩ := hE
  have hq : 0 ≤ (1 - E.γ) / E.κ := div_nonneg (by linarith) hκ.le
  rw [mul_sub, hk]
  unfold yPlan
  rw [sq_sqrt hq]
  field_simp
  ring

/-! ## (c) Output with preset nontradables prices, exactly -/

/-- The preset nontradables price "consistent with `M^e`": `P_N = (1−γ)M^e/ȳ_N`
(O&R Ex. 4(c)). -/
noncomputable def presetPN (E : Economy) (Me : ℝ) : ℝ := (1 - E.γ) * Me / ybarN E

/-- The preset price is the flexible-price equilibrium price when `M = M^e` (O&R Ex. 4(c)):
with CIA equality, (89), `C_T = ȳ_T` and `C_N = ȳ_N`, `P_N = (1−γ)M^e/ȳ_N`. -/
theorem flexible_PN {E : Economy} (hE : E.Valid) {Me PT PN : ℝ} (hT : 0 < PT)
    (hcia : Me = PT * E.yT + PN * ybarN E)
    (h89 : (1 - E.γ) / ybarN E = E.γ / E.yT * (PN / PT)) : PN = presetPN E Me := by
  have hy := ybarN_pos hE
  obtain ⟨_, _, _, hγ0, hγ1, _, _, _, _, hyT⟩ := hE
  unfold presetPN
  rw [hcia]
  field_simp at h89 ⊢
  nlinarith

/-- EX. 4(c), EXACT: with CIA equality `M = P_T C_T + P_N C_N`, the Cobb–Douglas condition (89),
`C_T = ȳ_T`, and `P_N` preset at `(1−γ)M^e/ȳ_N`, nontradables consumption is
`C_N = (M/M^e) ȳ_N` (so `y_N = (M/M^e) ȳ_N` by demand determination) and `P_T = γM/ȳ_T`. -/
theorem preset_output {E : Economy} (hE : E.Valid) {M Me PT cN : ℝ} (hMe : 0 < Me)
    (hT : 0 < PT) (hcN : 0 < cN) (hcia : M = PT * E.yT + presetPN E Me * cN)
    (h89 : (1 - E.γ) / cN = E.γ / E.yT * (presetPN E Me / PT)) :
    cN = M / Me * ybarN E ∧ PT = E.γ * M / E.yT := by
  have hy := ybarN_pos hE
  obtain ⟨_, _, _, hγ0, hγ1, _, _, _, _, hyT⟩ := hE
  have h1g : 0 < 1 - E.γ := by linarith
  have hPN : 0 < presetPN E Me := by unfold presetPN; positivity
  -- (89): `P_T C_T = (γ/(1−γ)) P_N C_N`
  have hsplit : PT * E.yT * (1 - E.γ) = E.γ * (presetPN E Me * cN) := by
    field_simp at h89; linarith
  have hMsplit : M * (1 - E.γ) = presetPN E Me * cN := by
    rw [hcia]; nlinarith
  refine ⟨?_, ?_⟩
  · unfold presetPN at hMsplit
    field_simp at hMsplit ⊢
    have : 0 < 1 - E.γ := by linarith
    nlinarith
  · field_simp
    nlinarith

/-- Ex. 4(c) from OPTIMALITY: in any pricing regime (preset or not), at a CIA household optimum
with `C_T = ȳ_T` and `P_{N,t}` preset at `(1−γ)M^e_t/ȳ_N`, the household's nontradables demand is
`(M_t/M^e_t) ȳ_N` and `P_{T,t} = γM_t/ȳ_T` at every date. -/
theorem preset_output_of_optimal {E : Economy} {Q : Prices} (hE : E.Valid) (hQ : Q.Valid E.r)
    {rev : ℕ → ℝ → ℝ} {Ys : ℕ → Set ℝ} {A0 : ℝ} {c : ℕ → Choice}
    (hopt : CIAOptimal E Q rev Ys A0 c) {Me : ℕ → ℝ} (hMe : ∀ t, 0 < Me t)
    (hcT : ∀ t, (c t).cT = E.yT) (hPN : ∀ t, Q.PN t = presetPN E (Me t)) (t : ℕ) :
    (c t).cN = (c t).money / Me t * ybarN E ∧ Q.PT t = E.γ * (c t).money / E.yT := by
  have h89 := cia_intra_of_optimal hE hQ hopt t
  obtain ⟨⟨_, hb, hn, _⟩, hcia, _⟩ := hopt.1 t
  rw [hcT t, hPN t] at hcia
  simp only [relPrice] at h89
  rw [hcT t, hPN t] at h89
  exact preset_output hE (hMe t) (hQ t).1 hb hcia h89

/-- Ex. 4(c), FINITE-STATE VERSION: with a random money supply `M(s)` on finitely many states
`s` with probabilities `p_s`, and `P_N` preset at the level consistent with `M^e = E[M]`,
output is `(M(s)/M^e) ȳ_N` state by state, and expected output equals `ȳ_N`. -/
theorem preset_output_finite_state {S : Type*} [Fintype S] {E : Economy} (hE : E.Valid)
    {p M PT cN : S → ℝ}
    (hMe : 0 < ∑ s, p s * M s) (hT : ∀ s, 0 < PT s) (hcN : ∀ s, 0 < cN s)
    (hcia : ∀ s, M s = PT s * E.yT + presetPN E (∑ s', p s' * M s') * cN s)
    (h89 : ∀ s, (1 - E.γ) / cN s = E.γ / E.yT * (presetPN E (∑ s', p s' * M s') / PT s)) :
    (∀ s, cN s = M s / (∑ s', p s' * M s') * ybarN E) ∧ ∑ s, p s * cN s = ybarN E := by
  have hstate : ∀ s, cN s = M s / (∑ s', p s' * M s') * ybarN E := fun s =>
    (preset_output hE hMe (hT s) (hcN s) (hcia s) (h89 s)).1
  refine ⟨hstate, ?_⟩
  simp_rw [hstate]
  have e : ∀ s, p s * (M s / (∑ s', p s' * M s') * ybarN E)
      = (p s * M s) * (ybarN E / ∑ s', p s' * M s') := by intro s; ring
  simp_rw [e]
  rw [← Finset.sum_mul, mul_div_cancel₀ _ hMe.ne']

/-! ## (d) The authority's objective and the one-shot assumption -/

/-- Period utility along a money path under (c): `γ log ȳ_T + (1−γ) log C_N − (κ/2) y_N²` with
`C_N = y_N = (M/M^e) ȳ_N` (O&R Ex. 4(c)–(d)). -/
noncomputable def utilAt (E : Economy) (M Me : ℝ) : ℝ :=
  E.γ * log E.yT + (1 - E.γ) * log (M / Me * ybarN E) - E.κ / 2 * (M / Me * ybarN E) ^ 2

/-- Money carried into date `s`: `M_{−1}` at `s = 0` (O&R Ex. 4(d)). -/
def lagMoney (Mm1 : ℝ) (M : ℕ → ℝ) : ℕ → ℝ
  | 0 => Mm1
  | s + 1 => M s

/-- The authority's objective of Ex. 4(d), p. 714: `U_t − (χ/2)(P_{T,t}/P_{T,t−1})²`, with
`P_T ∝ M` by (c), from date `t` (Lean date 0). -/
noncomputable def authObj (E : Economy) (Mm1 : ℝ) (M Me : ℕ → ℝ) : ℝ :=
  ∑' s, E.β ^ s * utilAt E (M s) (Me s) - E.χ / 2 * (M 0 / Mm1) ^ 2

/-- The one-shot objective of Ex. 4(d): `(1−γ) log C_N − (κ/2) y_N² − (χ/2)(P_{T,t}/P_{T,t−1})²`. -/
noncomputable def oneShotObj (E : Economy) (Mm1 Me M : ℝ) : ℝ :=
  (1 - E.γ) * log (M / Me * ybarN E) - E.κ / 2 * (M / Me * ybarN E) ^ 2
    - E.χ / 2 * (M / Mm1) ^ 2

/-- Tradables inflation equals money growth: by (c), `P_{T,t}/P_{T,t−1} = M_t/M_{t−1}`
(O&R Ex. 4(d)). -/
theorem inflation_eq_money_growth {E : Economy} (hE : E.Valid) {M M' : ℝ} (hM' : 0 < M') :
    (E.γ * M / E.yT) / (E.γ * M' / E.yT) = M / M' := by
  obtain ⟨_, _, _, hγ0, _, _, _, _, _, hyT⟩ := hE
  field_simp

/-- EX. 4(d), THE ONE-SHOT REDUCTION: if the date-`t` money supply is changed while expectations
`M^e` and the future path `M_s`, `s > t`, are held fixed (one-shot play: future real allocations
do not respond), the authority's objective changes by exactly the change in the one-shot
objective `(1−γ) log C_N − (κ/2) y_N² − (χ/2)(P_{T,t}/P_{T,t−1})²`. -/
theorem authObj_sub {E : Economy} {Mm1 : ℝ} {M M' Me : ℕ → ℝ}
    (hsum : Summable fun s => E.β ^ s * utilAt E (M s) (Me s)) (hfut : ∀ s, s ≠ 0 → M' s = M s) :
    authObj E Mm1 M' Me - authObj E Mm1 M Me
      = oneShotObj E Mm1 (Me 0) (M' 0) - oneShotObj E Mm1 (Me 0) (M 0) := by
  have hoff : ∀ s ∉ ({0} : Finset ℕ),
      E.β ^ s * utilAt E (M' s) (Me s) = E.β ^ s * utilAt E (M s) (Me s) := by
    intro s hs; rw [hfut s (by simpa using hs)]
  obtain ⟨_, htsum⟩ := tsum_eq_add_of_eq_off hsum {0} hoff
  unfold authObj
  rw [htsum, Finset.sum_singleton, pow_zero, one_mul, one_mul]
  unfold oneShotObj utilAt
  ring

/-- The authority's objective INCLUDING every future inflation penalty
`Σ_s β^s (χ/2)(M_s/M_{s−1})²` (the dynamic objective that the one-shot game does not use). -/
noncomputable def fullObj (E : Economy) (Mm1 : ℝ) (M Me : ℕ → ℝ) : ℝ :=
  ∑' s, E.β ^ s * (utilAt E (M s) (Me s) - E.χ / 2 * (M s / lagMoney Mm1 M s) ^ 2)

/-- WHAT THE ONE-SHOT ASSUMPTION DROPS (O&R Ex. 4(d), made explicit): if the future money path is
held fixed IN LEVELS and the next-period inflation penalty is counted, a change in `M_t` changes
the objective by the one-shot change MINUS `β(χ/2)[(M_{t+1}/M_t')² − (M_{t+1}/M_t)²]`. The
one-shot game ignores exactly this channel (the effect of `M_t` on next period's inflation). -/
theorem fullObj_sub {E : Economy} {Mm1 : ℝ} {M M' Me : ℕ → ℝ}
    (hsum : Summable fun s => E.β ^ s *
      (utilAt E (M s) (Me s) - E.χ / 2 * (M s / lagMoney Mm1 M s) ^ 2))
    (hfut : ∀ s, s ≠ 0 → M' s = M s) :
    fullObj E Mm1 M' Me - fullObj E Mm1 M Me
      = (oneShotObj E Mm1 (Me 0) (M' 0) - oneShotObj E Mm1 (Me 0) (M 0))
        - E.β * (E.χ / 2) * ((M 1 / M' 0) ^ 2 - (M 1 / M 0) ^ 2) := by
  have hlag : ∀ s, 2 ≤ s → lagMoney Mm1 M' s = lagMoney Mm1 M s := by
    intro s hs
    obtain ⟨k, rfl⟩ : ∃ k, s = k + 1 := ⟨s - 1, by omega⟩
    simp only [lagMoney]; exact hfut k (by omega)
  have hoff : ∀ s ∉ ({0, 1} : Finset ℕ),
      E.β ^ s * (utilAt E (M' s) (Me s) - E.χ / 2 * (M' s / lagMoney Mm1 M' s) ^ 2)
        = E.β ^ s * (utilAt E (M s) (Me s) - E.χ / 2 * (M s / lagMoney Mm1 M s) ^ 2) := by
    intro s hs
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hs
    rw [hfut s hs.1, hlag s (by omega)]
  obtain ⟨_, htsum⟩ := tsum_eq_add_of_eq_off hsum {0, 1} hoff
  unfold fullObj
  rw [htsum, Finset.sum_pair (by norm_num : (0 : ℕ) ≠ 1)]
  simp only [lagMoney, pow_zero, pow_one, one_mul, hfut 1 one_ne_zero]
  unfold oneShotObj utilAt
  ring

/-! ## (e) The one-shot game -/

/-- The one-shot objective in money-growth form with penalty `(χ/2)(μ − a)²`: `a = 0` is the
book's gross-inflation penalty, `a = 1` the conventional `(π − 1)²` one (O&R Ex. 4(d)–(e)).
Here `μ = M_t/M_{t−1}` and `μ^e = M^e_t/M_{t−1}`. -/
noncomputable def gameObj (E : Economy) (a μe μ : ℝ) : ℝ :=
  (1 - E.γ) * log (μ / μe * ybarN E) - E.κ / 2 * (μ / μe * ybarN E) ^ 2 - E.χ / 2 * (μ - a) ^ 2

/-- The book's one-shot objective in money-growth form: `oneShotObj` at `M_t = μM_{t−1}`,
`M^e_t = μ^e M_{t−1}` is `gameObj` with `a = 0` (O&R Ex. 4(e)). -/
theorem oneShotObj_eq_gameObj {E : Economy} {Mm1 μe μ : ℝ} (hM : 0 < Mm1) (hμe : 0 < μe) :
    oneShotObj E Mm1 (μe * Mm1) (μ * Mm1) = gameObj E 0 μe μ := by
  unfold oneShotObj gameObj
  rw [show μ * Mm1 / (μe * Mm1) = μ / μe by field_simp, show μ * Mm1 / Mm1 = μ by field_simp,
    sub_zero]

/-- The best-response condition: `(1−γ)/μ = (κȳ_N²/μ^{e2}) μ + χ(μ − a)` (O&R Ex. 4(e)). -/
def BestResponseFOC (E : Economy) (a μe μ : ℝ) : Prop :=
  (1 - E.γ) / μ = E.κ * ybarN E ^ 2 / μe ^ 2 * μ + E.χ * (μ - a)

/-- BEST RESPONSE (O&R Ex. 4(e)): for given expectations `μ^e > 0`, `μ > 0` maximises the
one-shot objective over all positive money growth IF AND ONLY IF the first-order condition holds
(strict concavity); moreover the maximiser is then strict. -/
theorem gameObj_max_iff {E : Economy} (hE : E.Valid) {a μe μ : ℝ} (hμe : 0 < μe) (hμ : 0 < μ) :
    (∀ ν, 0 < ν → gameObj E a μe ν ≤ gameObj E a μe μ) ↔ BestResponseFOC E a μe μ := by
  have hy := ybarN_pos hE
  obtain ⟨_, _, _, _, hγ1, hχ, _, hκ, _, _⟩ := hE
  set k := E.κ * ybarN E ^ 2 / μe ^ 2 with hk
  have hk0 : 0 < k := by positivity
  have hform : ∀ ν, 0 < ν → gameObj E a μe ν
      = (1 - E.γ) * log ν - (k + E.χ) / 2 * ν ^ 2 + E.χ * a * ν
        + ((1 - E.γ) * log (ybarN E / μe) - E.χ / 2 * a ^ 2) := by
    intro ν hν
    unfold gameObj
    rw [show ν / μe * ybarN E = ν * (ybarN E / μe) by ring, log_mul hν.ne' (by positivity), hk]
    field_simp
    ring
  constructor
  · intro hmax
    have hloc : IsLocalMax (fun ν => (1 - E.γ) * log ν - (k + E.χ) / 2 * ν ^ 2 + E.χ * a * ν) μ
        := by
      filter_upwards [Ioi_mem_nhds hμ] with ν hν
      have h1 := hmax ν hν
      rw [hform ν hν, hform μ hμ] at h1
      linarith
    have h1 := (hasDerivAt_log hμ.ne').const_mul (1 - E.γ)
    have h2 := (hasDerivAt_pow 2 μ).const_mul ((k + E.χ) / 2)
    have h3 := (hasDerivAt_id' μ).const_mul (E.χ * a)
    have hd := (h1.sub h2).add h3
    have h0 := hloc.hasDerivAt_eq_zero hd
    unfold BestResponseFOC
    rw [← hk]
    norm_num at h0
    field_simp at h0 ⊢
    linarith
  · intro hfoc ν hν
    unfold BestResponseFOC at hfoc
    rw [← hk] at hfoc
    rw [hform ν hν, hform μ hμ]
    have hlog := log_tangent (k := 1 - E.γ) (by linarith) hν hμ
    have hsq := mul_nonneg (by linarith : 0 ≤ (k + E.χ) / 2) (sq_nonneg (ν - μ))
    have e : (1 - E.γ) / μ * ν - (1 - E.γ) / μ * μ = (k * μ + E.χ * (μ - a)) * (ν - μ) := by
      rw [hfoc]; ring
    nlinarith

/-- EXISTENCE AND UNIQUENESS OF THE BEST RESPONSE (O&R Ex. 4(e)): for every `μ^e > 0` there is
exactly one `μ > 0` satisfying the best-response condition (a quadratic with one positive root).
-/
theorem bestResponse_exists_unique {E : Economy} (hE : E.Valid) {a μe : ℝ} (hμe : 0 < μe) :
    ∃ μ, 0 < μ ∧ BestResponseFOC E a μe μ ∧ ∀ ν, 0 < ν → BestResponseFOC E a μe ν → ν = μ := by
  have hy := ybarN_pos hE
  obtain ⟨_, _, _, _, hγ1, hχ, _, hκ, _, _⟩ := hE
  set K := E.κ * ybarN E ^ 2 / μe ^ 2 + E.χ with hK
  have hK0 : 0 < K := by positivity
  set D := (E.χ * a) ^ 2 + 4 * K * (1 - E.γ) with hD
  have hD0 : 0 < D := by have : 0 < 1 - E.γ := by linarith
                         positivity
  set μ := (E.χ * a + sqrt D) / (2 * K) with hμdef
  have hsD : sqrt D ^ 2 = D := sq_sqrt hD0.le
  have hsDgt : |E.χ * a| < sqrt D := by
    rw [← sqrt_sq_eq_abs]
    apply sqrt_lt_sqrt (sq_nonneg _)
    have : 0 < 1 - E.γ := by linarith
    rw [hD]; nlinarith
  have hμ0 : 0 < μ := by
    apply div_pos _ (by positivity)
    have := neg_abs_le (E.χ * a); linarith
  have hfoc_iff : ∀ ν, 0 < ν → (BestResponseFOC E a μe ν ↔ K * ν ^ 2 - E.χ * a * ν
      - (1 - E.γ) = 0) := by
    intro ν hν
    unfold BestResponseFOC
    rw [hK]
    constructor
    · intro h; rw [div_eq_iff hν.ne'] at h; linear_combination -h
    · intro h; rw [div_eq_iff hν.ne']; linear_combination -h
  have hroot : K * μ ^ 2 - E.χ * a * μ - (1 - E.γ) = 0 := by
    have e1 : K * μ ^ 2 - E.χ * a * μ = (sqrt D ^ 2 - (E.χ * a) ^ 2) / (4 * K) := by
      rw [hμdef]; field_simp; ring
    rw [e1, hsD, hD]; field_simp; ring
  refine ⟨μ, hμ0, (hfoc_iff μ hμ0).mpr hroot, fun ν hν hfν => ?_⟩
  have hν' := (hfoc_iff ν hν).mp hfν
  -- two positive roots of the same quadratic coincide
  have hfac : K * (ν - μ) * (ν + μ - E.χ * a / K) = 0 := by
    field_simp; nlinarith
  rcases mul_eq_zero.mp hfac with h | h
  · rcases mul_eq_zero.mp h with h' | h'
    · exact absurd h' hK0.ne'
    · linarith
  · -- `ν + μ = χa/K` contradicts `μ > (χa + |χa|)/(2K) ≥ χa/K` and `ν > 0`
    have hμbig : E.χ * a / K < μ := by
      rw [hμdef, div_lt_div_iff₀ hK0 (by positivity)]
      have := le_abs_self (E.χ * a)
      nlinarith
    linarith

/-- A one-shot (rational-expectations) equilibrium (O&R Ex. 4(e)): money growth `μ > 0` that is
the best response to the expectation `μ^e = μ`. -/
def IsOneShotEquilibrium (E : Economy) (a μ : ℝ) : Prop :=
  0 < μ ∧ ∀ ν, 0 < ν → gameObj E a μ ν ≤ gameObj E a μ μ

/-- THE ONE-SHOT EQUILIBRIUM IS UNIQUE (O&R Ex. 4(e)): with penalty `(χ/2)(μ − a)²`,
`μ` is an equilibrium IFF `μ = [a + (a² + 4(1−γ)/(θχ))^{1/2}]/2`. -/
theorem oneShotEquilibrium_iff {E : Economy} (hE : E.Valid) {a μ : ℝ} :
    IsOneShotEquilibrium E a μ ↔
      μ = (a + sqrt (a ^ 2 + 4 * (1 - E.γ) / (E.θ * E.χ))) / 2 := by
  have hk := kappa_mul_ybarN_sq hE
  have hE' := hE
  obtain ⟨_, _, _, _, hγ1, hχ, _, hκ, hθ, _⟩ := hE'
  set D := a ^ 2 + 4 * (1 - E.γ) / (E.θ * E.χ) with hD
  have hD0 : 0 < D := by
    have : 0 < 1 - E.γ := by linarith
    have : 0 < E.θ := by linarith
    positivity
  have hsD : sqrt D ^ 2 = D := sq_sqrt hD0.le
  have hsDgt : |a| < sqrt D := by
    rw [← sqrt_sq_eq_abs]
    apply sqrt_lt_sqrt (sq_nonneg _)
    have : 0 < 1 - E.γ := by linarith
    have : 0 < E.θ := by linarith
    rw [hD]; have : 0 < 4 * (1 - E.γ) / (E.θ * E.χ) := by positivity
    linarith
  set μs := (a + sqrt D) / 2 with hμs
  have hμs0 : 0 < μs := by have := neg_abs_le a; rw [hμs]; linarith
  -- the equilibrium condition in quadratic form
  have hquad : ∀ ν, 0 < ν → (BestResponseFOC E a ν ν ↔ ν ^ 2 - a * ν - (1 - E.γ) / (E.θ * E.χ)
      = 0) := by
    intro ν hν
    unfold BestResponseFOC
    have hθ0 : 0 < E.θ := by linarith
    have e : E.κ * ybarN E ^ 2 = (E.θ - 1) * (1 - E.γ) / E.θ := hk
    constructor
    · intro h
      rw [e] at h
      field_simp at h ⊢
      nlinarith
    · intro h
      rw [e]
      field_simp at h ⊢
      nlinarith
  have hroot : μs ^ 2 - a * μs - (1 - E.γ) / (E.θ * E.χ) = 0 := by
    have e1 : μs ^ 2 - a * μs = (sqrt D ^ 2 - a ^ 2) / 4 := by rw [hμs]; ring
    rw [e1, hsD, hD]; ring
  constructor
  · rintro ⟨hμ, hmax⟩
    have hfoc := (gameObj_max_iff hE hμ hμ).mp hmax
    have hq := (hquad μ hμ).mp hfoc
    have hfac : (μ - μs) * (μ + μs - a) = 0 := by nlinarith
    rcases mul_eq_zero.mp hfac with h | h
    · linarith
    · have : a < μs := by have := le_abs_self a; rw [hμs]; linarith
      linarith
  · intro h
    rw [h]
    exact ⟨hμs0, (gameObj_max_iff hE hμs0 hμs0).mpr ((hquad μs hμs0).mpr hroot)⟩

/-- EX. 4(e), THE BOOK'S ANSWER (gross-inflation penalty, `a = 0`): the unique one-shot
equilibrium money growth is `M_t/M_{t−1} = P_{T,t}/P_{T,t−1} = ((1−γ)/(χθ))^{1/2}
= {κ[(ȳ_N^{PLAN})² − ȳ_N²]/χ}^{1/2}`. -/
theorem book_equilibrium {E : Economy} (hE : E.Valid) {μ : ℝ} :
    IsOneShotEquilibrium E 0 μ ↔ μ = sqrt ((1 - E.γ) / (E.χ * E.θ)) ∧
      sqrt ((1 - E.γ) / (E.χ * E.θ)) = sqrt (E.κ * (yPlan E ^ 2 - ybarN E ^ 2) / E.χ) := by
  have hgap := kappa_gap hE
  have hE' := hE
  obtain ⟨_, _, _, _, hγ1, hχ, _, _, hθ, _⟩ := hE'
  have hsame : sqrt ((1 - E.γ) / (E.χ * E.θ)) = sqrt (E.κ * (yPlan E ^ 2 - ybarN E ^ 2) / E.χ) := by
    rw [hgap]; congr 1; field_simp
  have hq : (0 + sqrt (0 ^ 2 + 4 * (1 - E.γ) / (E.θ * E.χ))) / 2
      = sqrt ((1 - E.γ) / (E.χ * E.θ)) := by
    have hpos : 0 ≤ (1 - E.γ) / (E.χ * E.θ) := by
      have : 0 < 1 - E.γ := by linarith
      have : 0 < E.θ := by linarith
      positivity
    rw [zero_add, show (0 : ℝ) ^ 2 + 4 * (1 - E.γ) / (E.θ * E.χ)
        = 2 ^ 2 * ((1 - E.γ) / (E.χ * E.θ)) by field_simp; ring,
      sqrt_mul (by norm_num), sqrt_sq (by norm_num)]
    ring
  rw [oneShotEquilibrium_iff hE, hq]
  exact ⟨fun h => ⟨h, hsame⟩, fun h => h.1⟩

/-- EX. 4(e) WITH THE CONVENTIONAL `(π − 1)²` PENALTY (`a = 1`, flagged): the unique one-shot
equilibrium is `μ = [1 + (1 + 4(1−γ)/(θχ))^{1/2}]/2`, which differs from the book's answer, and
exceeds one (an inflation bias). -/
theorem conventional_equilibrium {E : Economy} (hE : E.Valid) {μ : ℝ} :
    IsOneShotEquilibrium E 1 μ ↔ μ = (1 + sqrt (1 + 4 * (1 - E.γ) / (E.θ * E.χ))) / 2 := by
  rw [oneShotEquilibrium_iff hE, one_pow]

/-- The conventional-penalty equilibrium exhibits an inflation bias: `μ > 1` (O&R Ex. 4(e)). -/
theorem conventional_inflation_bias {E : Economy} (hE : E.Valid) {μ : ℝ}
    (h : IsOneShotEquilibrium E 1 μ) : 1 < μ := by
  rw [conventional_equilibrium hE] at h
  obtain ⟨_, _, _, _, hγ1, hχ, _, _, hθ, _⟩ := hE
  have hpos : 0 < 4 * (1 - E.γ) / (E.θ * E.χ) := by
    have : 0 < 1 - E.γ := by linarith
    have : 0 < E.θ := by linarith
    positivity
  have : 1 < sqrt (1 + 4 * (1 - E.γ) / (E.θ * E.χ)) := by
    rw [lt_sqrt zero_le_one]; linarith
  rw [h]; linarith

/-- Under commitment (expectations equal to the choice, so output is `ȳ_N` whatever `μ`), the
conventional penalty is minimised exactly at `μ = 1`: the discretionary equilibrium is
inflationary relative to commitment (O&R Ex. 4, cf. Chapter 9). -/
theorem commitment_conventional {E : Economy} (hE : E.Valid) {μ : ℝ} (hμ : 0 < μ) :
    gameObj E 1 μ μ ≤ gameObj E 1 1 1 ∧ (μ ≠ 1 → gameObj E 1 μ μ < gameObj E 1 1 1) := by
  have hχ := hE.2.2.2.2.2.1
  unfold gameObj
  rw [div_self hμ.ne', div_self one_ne_zero, sub_self]
  refine ⟨?_, fun hne => ?_⟩
  · have := mul_nonneg (by linarith : 0 ≤ E.χ / 2) (sq_nonneg (μ - 1)); linarith
  · have : 0 < (μ - 1) ^ 2 := by have : μ - 1 ≠ 0 := sub_ne_zero.mpr hne
                                 positivity
    have := mul_pos (by linarith : 0 < E.χ / 2) this; linarith

/-- The literal gross-inflation penalty has NO commitment optimum (flag on Ex. 4(d)): under
commitment every `μ > 0` is strictly beaten by `μ/2`, since the penalty `(χ/2)μ²` is minimised
only at zero money. -/
theorem commitment_gross_no_optimum {E : Economy} (hE : E.Valid) {μ : ℝ} (hμ : 0 < μ) :
    gameObj E 0 μ μ < gameObj E 0 (μ / 2) (μ / 2) := by
  have hχ := hE.2.2.2.2.2.1
  unfold gameObj
  rw [div_self hμ.ne', div_self (by positivity : μ / 2 ≠ 0), sub_zero, sub_zero]
  have h3 : E.χ / 2 * (μ / 2) ^ 2 < E.χ / 2 * μ ^ 2 := by
    have : (μ / 2) ^ 2 < μ ^ 2 := by nlinarith
    exact mul_lt_mul_of_pos_left this (by linarith)
  linarith

end ObstfeldRogoff.StickyPriceModels.CashInAdvanceCredibility

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

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

/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

/-!
# Evidence on sticky prices, wealth effects and the J-curve

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*: Box 10.1
("More Empirical Evidence on Sticky Prices"), p. 676; the Application "Wealth Effects and the
Real Exchange Rate", pp. 694–696, with its cross-section regression (p. 694) and Table 10.1
(p. 695).

The empirical material is formalised as precise algebraic and statistical claims:
* simple least squares on a finite sample: the normal equations are necessary and sufficient
  for minimising the residual sum of squares (unique minimiser), the minimum value, `0 ≤ R² ≤ 1`,
  and the exact identity `t² = (N − 2) R²/(1 − R²)` linking the slope `t`-statistic to `R²`;
* the regression `Δ log p = 0.039 + 1.042 ΔB/Y`, s.e. `(0.027)`, `(0.433)`, `R² = 0.31`:
  its `t`-ratios, significance for every critical value in `[1.45, 2.40]`, non-rejection of a
  unit slope, and internal consistency of the reported `R²` with the reported coefficient and
  standard error for the book's 15 OECD countries (the implied `R²` rounds to 0.31, robustly to
  the rounding of the reported numbers);
* Table 10.1: the J-curve pattern (negative in year 1, positive afterwards, strictly increasing,
  strictly diminishing increments, exactly one sign change) and the "modest impact" claim;
* Box 10.1: kurtosis is invariant to affine changes of units and to sign flips (so comparing
  the kurtosis of price increases with that of price cuts is unit-free), Pearson's inequality
  `kurtosis ≥ 1 + skewness²` (so excess kurtosis is at least `−2`), and the reported
  numbers (31.2 vs 4.6; Blinder's 55 percent; Kashyap's 12–18 month spells).
-/

namespace ObstfeldRogoff.StickyPriceModels.StickyPriceEvidence

open Finset

/-! ## Simple least squares on a finite sample -/

/-- O&R p. 694 (least squares): residual sum of squares `Σ (y_i − α − β x_i)²` of the line
`α + β x` on the sample `(x_i, y_i)`, `i < n`. -/
def rss {n : ℕ} (x y : Fin n → ℝ) (α β : ℝ) : ℝ := ∑ i, (y i - α - β * x i) ^ 2

/-- Sample mean `(1/N) Σ z_i` (O&R p. 694, least squares). -/
noncomputable def sampleMean {n : ℕ} (z : Fin n → ℝ) : ℝ := (∑ i, z i) / n

/-- Centred cross-product `Σ x_i y_i − (Σ x_i)(Σ y_i)/N` (O&R p. 694, least squares). -/
noncomputable def sxy {n : ℕ} (x y : Fin n → ℝ) : ℝ :=
  ∑ i, x i * y i - (∑ i, x i) * (∑ i, y i) / n

/-- OLS slope `sxy/sxx` (O&R p. 694, the coefficient 1.042). -/
noncomputable def olsSlope {n : ℕ} (x y : Fin n → ℝ) : ℝ := sxy x y / sxy x x

/-- OLS intercept `ȳ − β̂ x̄` (O&R p. 694, the coefficient 0.039). -/
noncomputable def olsIntercept {n : ℕ} (x y : Fin n → ℝ) : ℝ :=
  sampleMean y - olsSlope x y * sampleMean x

/-- Coefficient of determination `R² = sxy²/(sxx syy)` (O&R p. 694, `R² = 0.31`). -/
noncomputable def rSquared {n : ℕ} (x y : Fin n → ℝ) : ℝ :=
  sxy x y ^ 2 / (sxy x x * sxy y y)

/-- Classical OLS standard error of the slope, `√((RSS/(N − 2))/sxx)` (O&R p. 694, the 0.433). -/
noncomputable def slopeSE {n : ℕ} (x y : Fin n → ℝ) : ℝ :=
  Real.sqrt (rss x y (olsIntercept x y) (olsSlope x y) / (n - 2) / sxy x x)

/-- Slope `t`-statistic `β̂/se(β̂)` (O&R p. 694, `1.042/0.433`). -/
noncomputable def slopeT {n : ℕ} (x y : Fin n → ℝ) : ℝ := olsSlope x y / slopeSE x y

/-- Expansion of the residual sum of squares into raw sample sums (O&R p. 694). -/
theorem rss_expand {n : ℕ} (x y : Fin n → ℝ) (α β : ℝ) :
    rss x y α β = ∑ i, y i ^ 2 - 2 * α * ∑ i, y i - 2 * β * ∑ i, x i * y i + n * α ^ 2 +
      2 * α * β * ∑ i, x i + β ^ 2 * ∑ i, x i ^ 2 := by
  unfold rss
  have e : ∀ i, (y i - α - β * x i) ^ 2 = y i ^ 2 - 2 * α * y i - 2 * β * (x i * y i) +
      α ^ 2 + 2 * α * β * x i + β ^ 2 * x i ^ 2 := fun i => by ring
  simp only [e, sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_const, card_univ,
    Fintype.card_fin, nsmul_eq_mul]

/-- The centred sums are the textbook ones: `sxy = Σ (x_i − x̄)(y_i − ȳ)` (O&R p. 694). -/
theorem sxy_eq_centred {n : ℕ} (hn : n ≠ 0) (x y : Fin n → ℝ) :
    sxy x y = ∑ i, (x i - sampleMean x) * (y i - sampleMean y) := by
  have hN : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
  have e : ∀ i, (x i - sampleMean x) * (y i - sampleMean y) = x i * y i -
      sampleMean y * x i - sampleMean x * y i + sampleMean x * sampleMean y := fun i => by ring
  simp only [e, sum_add_distrib, sum_sub_distrib, ← mul_sum, sum_const, card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  unfold sxy sampleMean
  field_simp
  ring

/-- `sxx = Σ (x_i − x̄)² ≥ 0` (O&R p. 694). -/
theorem sxx_nonneg {n : ℕ} (hn : n ≠ 0) (x : Fin n → ℝ) : 0 ≤ sxy x x := by
  rw [sxy_eq_centred hn]
  exact sum_nonneg fun i _ => mul_self_nonneg _

/-- O&R p. 694 (least squares, exact decomposition): for every line `(α, β)`,
`RSS(α, β) = (syy − sxy²/sxx) + N (α − α̂ + (β − β̂) x̄)² + sxx (β − β̂)²`. -/
theorem rss_decomposition {n : ℕ} (hn : n ≠ 0) (x y : Fin n → ℝ) (hxx : sxy x x ≠ 0)
    (α β : ℝ) :
    rss x y α β = (sxy y y - sxy x y ^ 2 / sxy x x) +
      n * (α - olsIntercept x y + (β - olsSlope x y) * sampleMean x) ^ 2 +
        sxy x x * (β - olsSlope x y) ^ 2 := by
  have hN : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn
  rw [rss_expand]
  unfold olsIntercept olsSlope sampleMean
  set sx := ∑ i, x i
  set sy := ∑ i, y i
  have hxx' : ∑ i, x i ^ 2 = sxy x x + sx ^ 2 / n := by
    unfold sxy; simp only [sq]; ring
  have hyy' : ∑ i, y i ^ 2 = sxy y y + sy ^ 2 / n := by
    unfold sxy; simp only [sq]; ring
  have hxy' : ∑ i, x i * y i = sxy x y + sx * sy / n := by
    unfold sxy; ring
  rw [hxx', hyy', hxy']
  field_simp
  ring

/-- O&R p. 694 (least squares, necessity and sufficiency; existence and uniqueness): with
`N > 0` and a non-degenerate regressor (`sxx > 0`), `(α, β)` minimises the residual sum of
squares iff `β = sxy/sxx` and `α = ȳ − β x̄`. -/
theorem ols_minimises_iff {n : ℕ} (hn : n ≠ 0) (x y : Fin n → ℝ) (hxx : 0 < sxy x x)
    (α β : ℝ) :
    (∀ α' β', rss x y α β ≤ rss x y α' β') ↔ β = olsSlope x y ∧ α = olsIntercept x y := by
  have hN : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
  have hdec := rss_decomposition hn x y hxx.ne'
  constructor
  · intro h
    have h1 := h (olsIntercept x y) (olsSlope x y)
    rw [hdec, hdec] at h1
    simp only [sub_self, zero_mul, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, mul_zero] at h1
    have ha := mul_nonneg hN.le (sq_nonneg (α - olsIntercept x y +
      (β - olsSlope x y) * sampleMean x))
    have hb := mul_nonneg hxx.le (sq_nonneg (β - olsSlope x y))
    have hb0 : sxy x x * (β - olsSlope x y) ^ 2 = 0 := by linarith
    have hβ : (β - olsSlope x y) ^ 2 = 0 := by
      rcases mul_eq_zero.1 hb0 with h0 | h0
      · exact absurd h0 hxx.ne'
      · exact h0
    have hβ' : β = olsSlope x y := by
      have := pow_eq_zero_iff (n := 2) two_ne_zero |>.1 hβ
      linarith
    have ha0 : (n : ℝ) * (α - olsIntercept x y + (β - olsSlope x y) * sampleMean x) ^ 2 = 0 := by
      linarith
    have hα : (α - olsIntercept x y + (β - olsSlope x y) * sampleMean x) ^ 2 = 0 := by
      rcases mul_eq_zero.1 ha0 with h0 | h0
      · exact absurd h0 hN.ne'
      · exact h0
    have := pow_eq_zero_iff (n := 2) two_ne_zero |>.1 hα
    rw [hβ', sub_self, zero_mul, add_zero] at this
    exact ⟨hβ', by linarith⟩
  · rintro ⟨rfl, rfl⟩ α' β'
    rw [hdec, hdec]
    simp only [sub_self, zero_mul, add_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      zero_pow, mul_zero]
    have ha := mul_nonneg hN.le (sq_nonneg (α' - olsIntercept x y +
      (β' - olsSlope x y) * sampleMean x))
    have hb := mul_nonneg hxx.le (sq_nonneg (β' - olsSlope x y))
    linarith

/-- O&R p. 694: the minimised residual sum of squares is `syy − sxy²/sxx`. -/
theorem rss_at_ols {n : ℕ} (hn : n ≠ 0) (x y : Fin n → ℝ) (hxx : sxy x x ≠ 0) :
    rss x y (olsIntercept x y) (olsSlope x y) = sxy y y - sxy x y ^ 2 / sxy x x := by
  rw [rss_decomposition hn x y hxx]
  simp

/-- O&R p. 694: `R² = 1 − RSS/syy` at the least-squares line. -/
theorem rSquared_eq_one_sub {n : ℕ} (hn : n ≠ 0) (x y : Fin n → ℝ) (hxx : sxy x x ≠ 0)
    (hyy : sxy y y ≠ 0) :
    rSquared x y = 1 - rss x y (olsIntercept x y) (olsSlope x y) / sxy y y := by
  rw [rss_at_ols hn x y hxx]
  unfold rSquared
  field_simp
  ring

/-- O&R p. 694: `0 ≤ R² ≤ 1` (the upper bound is the Cauchy–Schwarz inequality
`sxy² ≤ sxx syy`, obtained here from `RSS ≥ 0`). -/
theorem rSquared_mem_Icc {n : ℕ} (hn : n ≠ 0) (x y : Fin n → ℝ) (hxx : 0 < sxy x x)
    (hyy : 0 < sxy y y) : 0 ≤ rSquared x y ∧ rSquared x y ≤ 1 := by
  have hrss : 0 ≤ rss x y (olsIntercept x y) (olsSlope x y) :=
    sum_nonneg fun i _ => sq_nonneg _
  constructor
  · unfold rSquared
    positivity
  · rw [rSquared_eq_one_sub hn x y hxx.ne' hyy.ne']
    have := div_nonneg hrss hyy.le
    linarith

/-- O&R p. 694 (exact identity linking the reported statistics): with `N > 2`, `sxx > 0`,
`syy > 0` and an imperfect fit (`RSS > 0`), the slope `t`-statistic satisfies
`t² = (N − 2) R²/(1 − R²)`. -/
theorem slopeT_sq {n : ℕ} (hn : 2 < n) (x y : Fin n → ℝ) (hxx : 0 < sxy x x)
    (hyy : 0 < sxy y y) (hrss : 0 < rss x y (olsIntercept x y) (olsSlope x y)) :
    slopeT x y ^ 2 = (n - 2) * rSquared x y / (1 - rSquared x y) := by
  have hn0 : n ≠ 0 := by omega
  have hN : (2 : ℝ) < n := by exact_mod_cast hn
  have hN2 : (0 : ℝ) < n - 2 := by linarith
  have hR := rSquared_eq_one_sub hn0 x y hxx.ne' hyy.ne'
  set R := rss x y (olsIntercept x y) (olsSlope x y) with hRdef
  have hvar : 0 ≤ R / (n - 2) / sxy x x := by positivity
  have h1R : 1 - rSquared x y = R / sxy y y := by rw [hR]; ring
  unfold slopeT slopeSE
  rw [← hRdef, div_pow, Real.sq_sqrt hvar, h1R]
  unfold rSquared olsSlope
  have hR0 : R ≠ 0 := hrss.ne'
  field_simp

/-- O&R p. 694: inverting the identity, the `R²` implied by a slope `t`-statistic is
`t²/(N − 2 + t²)`. -/
theorem rSquared_of_slopeT {n : ℕ} (hn : 2 < n) (x y : Fin n → ℝ) (hxx : 0 < sxy x x)
    (hyy : 0 < sxy y y) (hrss : 0 < rss x y (olsIntercept x y) (olsSlope x y)) :
    rSquared x y = slopeT x y ^ 2 / (n - 2 + slopeT x y ^ 2) := by
  have hn0 : n ≠ 0 := by omega
  have hN : (2 : ℝ) < n := by exact_mod_cast hn
  have ht := slopeT_sq hn x y hxx hyy hrss
  have h1 : 1 - rSquared x y ≠ 0 := by
    rw [rSquared_eq_one_sub hn0 x y hxx.ne' hyy.ne']
    have := div_pos hrss hyy
    linarith
  have hpos : 0 < (n : ℝ) - 2 + slopeT x y ^ 2 := by
    have := sq_nonneg (slopeT x y); linarith
  rw [eq_div_iff hpos.ne', ht]
  field_simp
  ring

/-! ## The wealth-effects regression (p. 694) -/

/-- O&R p. 694: the slope `t`-ratio `1.042/0.433` lies in `(2.40, 2.41)`. -/
theorem wealth_slope_tratio :
    (2.40 : ℝ) < 1.042 / 0.433 ∧ (1.042 : ℝ) / 0.433 < 2.41 := by
  constructor <;> norm_num

/-- O&R p. 694: the intercept `t`-ratio `0.039/0.027` lies in `(1.44, 1.45)`. -/
theorem wealth_intercept_tratio :
    (1.44 : ℝ) < 0.039 / 0.027 ∧ (0.039 : ℝ) / 0.027 < 1.45 := by
  constructor <;> norm_num

/-- O&R p. 694: for every two-sided critical value `cv ∈ [1.45, 2.40]` (this range contains
both the normal 1.96 and the Student-`t` with 13 degrees of freedom, 2.160), the slope is
significant and the intercept is not. -/
theorem wealth_significance {cv : ℝ} (h1 : 1.45 ≤ cv) (h2 : cv ≤ 2.40) :
    cv < (1.042 : ℝ) / 0.433 ∧ (0.039 : ℝ) / 0.027 < cv := by
  constructor
  · have := wealth_slope_tratio.1; linarith
  · have := wealth_intercept_tratio.2; linarith

/-- O&R p. 694: 1.96 and 2.160 lie in the critical-value range of `wealth_significance`. -/
theorem standard_critical_values_in_range :
    ((1.45 : ℝ) ≤ 1.96 ∧ (1.96 : ℝ) ≤ 2.40) ∧ ((1.45 : ℝ) ≤ 2.160 ∧ (2.160 : ℝ) ≤ 2.40) := by
  norm_num

/-- O&R p. 694 ("an increase of 1 percent ... is associated with a 1 percent appreciation"):
the hypothesis of a unit slope is not rejected for any critical value `cv ≥ 0.1`, because
`|1.042 − 1|/0.433 < 0.1`. -/
theorem wealth_unit_slope_not_rejected {cv : ℝ} (hcv : 0.1 ≤ cv) :
    |(1.042 : ℝ) - 1| / 0.433 < cv := by
  have : |(1.042 : ℝ) - 1| / 0.433 < 0.1 := by
    rw [abs_of_pos (by norm_num)]; norm_num
  linarith

/-- O&R p. 694 with `slopeT_sq` (internal consistency, point version): for the book's 15 OECD
countries (`N − 2 = 13`) the `R²` implied by the reported `t = 1.042/0.433` lies in
`[0.305, 0.315)`, i.e. rounds to the reported 0.31. -/
theorem wealth_implied_rSquared :
    (0.305 : ℝ) ≤ (1.042 / 0.433) ^ 2 / (13 + (1.042 / 0.433) ^ 2) ∧
      (1.042 / 0.433 : ℝ) ^ 2 / (13 + (1.042 / 0.433) ^ 2) < 0.315 := by
  constructor <;> norm_num

/-- O&R p. 694 (internal consistency, robust to rounding): for every coefficient `b` and
standard error `s` that round to the reported 1.042 and 0.433, the implied `R²`
`(b/s)²/(13 + (b/s)²)` rounds to the reported 0.31. -/
theorem wealth_implied_rSquared_robust {b s : ℝ} (hb1 : 1.0415 ≤ b) (hb2 : b ≤ 1.0425)
    (hs1 : 0.4325 ≤ s) (hs2 : s ≤ 0.4335) :
    (0.305 : ℝ) ≤ (b / s) ^ 2 / (13 + (b / s) ^ 2) ∧ (b / s) ^ 2 / (13 + (b / s) ^ 2) < 0.315 := by
  have hs : 0 < s := by linarith
  have ht1 : 2.40 ≤ b / s := by rw [le_div_iff₀ hs]; linarith
  have ht2 : b / s ≤ 2.42 := by rw [div_le_iff₀ hs]; linarith
  set t := b / s
  have hsq1 : 5.76 ≤ t ^ 2 := by nlinarith
  have hsq2 : t ^ 2 ≤ 5.8564 := by nlinarith
  have hpos : 0 < 13 + t ^ 2 := by linarith
  constructor
  · rw [le_div_iff₀ hpos]; linarith
  · rw [div_lt_iff₀ hpos]; linarith

/-! ## Table 10.1: the J-curve (p. 695) -/

/-- O&R Table 10.1, p. 695: change in the U.S. current account (percent of GDP) in years 1–6
after a 20 percent real dollar depreciation (average of six econometric models). -/
noncomputable def caResponse : Fin 6 → ℝ := ![-0.24, 0.61, 1.22, 1.36, 1.46, 1.54]

/-- O&R Table 10.1: year-on-year increments of the current-account response. -/
noncomputable def caIncrement (i : Fin 5) : ℝ := caResponse i.succ - caResponse i.castSucc

/-- O&R p. 695 (the "J-curve" effect): the current account deteriorates in year 1. -/
theorem caResponse_year_one_neg : caResponse 0 < 0 := by
  norm_num [caResponse]

/-- O&R p. 695: the current account improves in every year from year 2 on. -/
theorem caResponse_later_pos : ∀ i : Fin 6, i ≠ 0 → 0 < caResponse i := by
  intro i hi
  fin_cases i <;> first | exact absurd rfl hi | norm_num [caResponse]

/-- O&R p. 695 ("only over time do the quantity responses outweigh the price effects"): the
response is strictly increasing over the six years. -/
theorem caResponse_strictMono : StrictMono caResponse := by
  rw [Fin.strictMono_iff_lt_succ]
  intro i
  fin_cases i <;> norm_num [caResponse]

/-- O&R p. 695: the increments strictly diminish (the response is concave in time). -/
theorem caIncrement_strictAnti : StrictAnti caIncrement := by
  rw [Fin.strictAnti_iff_succ_lt]
  intro i
  fin_cases i <;> norm_num [caIncrement, caResponse]

/-- O&R p. 695 (J-curve, precise): there is exactly one year-to-year sign change, from year 1
to year 2. -/
theorem caResponse_unique_sign_change :
    ∃! i : Fin 5, caResponse i.castSucc < 0 ∧ 0 < caResponse i.succ := by
  refine ⟨0, ?_, ?_⟩
  · norm_num [caResponse]
  · intro i hi
    fin_cases i
    · rfl
    all_goals norm_num [caResponse] at hi

/-- O&R p. 695 ("a very substantial permanent depreciation has only a relatively modest impact
on the current account"): per percentage point of depreciation, the response never exceeds
0.08 percent of GDP. -/
theorem caResponse_modest : ∀ i : Fin 6, caResponse i / 20 < 0.08 := by
  intro i
  fin_cases i <;> norm_num [caResponse]

/-- O&R Table 10.1: the cumulative six-year improvement is 5.95 percent of one year's GDP. -/
theorem caResponse_cumulative : ∑ i, caResponse i = 5.95 := by
  simp [caResponse, Fin.sum_univ_succ]
  norm_num

/-! ## Box 10.1: kurtosis of price changes (p. 676) -/

/-- Box 10.1, p. 676: weighted mean `Σ p_i z_i` of a finite distribution of price changes. -/
def wMean {ι : Type*} [Fintype ι] (p z : ι → ℝ) : ℝ := ∑ i, p i * z i

/-- Box 10.1: `k`-th central moment `Σ p_i (z_i − μ)^k`. -/
def cMoment {ι : Type*} [Fintype ι] (p z : ι → ℝ) (k : ℕ) : ℝ :=
  ∑ i, p i * (z i - wMean p z) ^ k

/-- Box 10.1: kurtosis `m₄/m₂²` (excess kurtosis is this minus 3). -/
noncomputable def kurtosis {ι : Type*} [Fintype ι] (p z : ι → ℝ) : ℝ :=
  cMoment p z 4 / cMoment p z 2 ^ 2

/-- Box 10.1: affine change of units `a + b z` shifts the mean affinely (weights sum to one). -/
theorem wMean_affine {ι : Type*} [Fintype ι] {p : ι → ℝ} (hp : ∑ i, p i = 1) (z : ι → ℝ)
    (a b : ℝ) : wMean p (fun i => a + b * z i) = a + b * wMean p z := by
  unfold wMean
  have e : ∀ i, p i * (a + b * z i) = a * p i + b * (p i * z i) := fun i => by ring
  simp only [e, sum_add_distrib, ← mul_sum, hp, mul_one]

/-- Box 10.1: central moments scale as `b^k` under `a + b z`. -/
theorem cMoment_affine {ι : Type*} [Fintype ι] {p : ι → ℝ} (hp : ∑ i, p i = 1) (z : ι → ℝ)
    (a b : ℝ) (k : ℕ) : cMoment p (fun i => a + b * z i) k = b ^ k * cMoment p z k := by
  unfold cMoment
  rw [wMean_affine hp, mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [show a + b * z i - (a + b * wMean p z) = b * (z i - wMean p z) by ring, mul_pow]
  ring

/-- Box 10.1 (the kurtosis comparison is unit-free): kurtosis is invariant to every affine
change of units `a + b z` with `b ≠ 0`. -/
theorem kurtosis_affine {ι : Type*} [Fintype ι] {p : ι → ℝ} (hp : ∑ i, p i = 1) (z : ι → ℝ)
    (a : ℝ) {b : ℝ} (hb : b ≠ 0) : kurtosis p (fun i => a + b * z i) = kurtosis p z := by
  unfold kurtosis
  rw [cMoment_affine hp, cMoment_affine hp, mul_pow, ← pow_mul]
  exact mul_div_mul_left _ _ (pow_ne_zero _ hb)

/-- Box 10.1: kurtosis is unchanged by a sign flip, so price cuts may be measured as negative
changes or as positive magnitudes. -/
theorem kurtosis_neg {ι : Type*} [Fintype ι] {p : ι → ℝ} (hp : ∑ i, p i = 1) (z : ι → ℝ) :
    kurtosis p (fun i => -z i) = kurtosis p z := by
  have := kurtosis_affine hp z 0 (b := -1) (by norm_num)
  simpa using this

/-- Box 10.1: the first central moment vanishes. -/
theorem cMoment_one {ι : Type*} [Fintype ι] {p : ι → ℝ} (hp : ∑ i, p i = 1) (z : ι → ℝ) :
    cMoment p z 1 = 0 := by
  unfold cMoment
  simp only [pow_one, mul_sub, sum_sub_distrib, ← sum_mul, hp, one_mul]
  unfold wMean
  ring

/-- Box 10.1 (Pearson's inequality): for a nonnegative weighting summing to one with positive
variance, `m₄/m₂² ≥ 1 + m₃²/m₂³`, i.e. kurtosis is at least one plus the squared skewness. -/
theorem pearson_inequality {ι : Type*} [Fintype ι] {p : ι → ℝ} (hp0 : ∀ i, 0 ≤ p i)
    (hp : ∑ i, p i = 1) (z : ι → ℝ) (hvar : 0 < cMoment p z 2) :
    1 + cMoment p z 3 ^ 2 / cMoment p z 2 ^ 3 ≤ kurtosis p z := by
  set m2 := cMoment p z 2
  set c := cMoment p z 3 / m2
  have hnn : 0 ≤ ∑ i, p i * ((z i - wMean p z) ^ 2 - c * (z i - wMean p z) - m2) ^ 2 :=
    sum_nonneg fun i _ => mul_nonneg (hp0 i) (sq_nonneg _)
  have e : ∀ i, p i * ((z i - wMean p z) ^ 2 - c * (z i - wMean p z) - m2) ^ 2 =
      p i * (z i - wMean p z) ^ 4 - 2 * c * (p i * (z i - wMean p z) ^ 3) +
        (c ^ 2 - 2 * m2) * (p i * (z i - wMean p z) ^ 2) +
          2 * c * m2 * (p i * (z i - wMean p z) ^ 1) + m2 ^ 2 * p i := fun i => by ring
  simp only [e, sum_add_distrib, sum_sub_distrib, ← mul_sum] at hnn
  have h1 := cMoment_one hp z
  unfold cMoment at h1
  rw [h1, hp] at hnn
  change 0 ≤ cMoment p z 4 - 2 * c * cMoment p z 3 + (c ^ 2 - 2 * m2) * m2 + 2 * c * m2 * 0 +
    m2 ^ 2 * 1 at hnn
  unfold kurtosis
  rw [← sub_nonneg]
  have e2 : cMoment p z 4 / m2 ^ 2 - (1 + cMoment p z 3 ^ 2 / m2 ^ 3) =
      (cMoment p z 4 - 2 * c * cMoment p z 3 + (c ^ 2 - 2 * m2) * m2 + 2 * c * m2 * 0 +
        m2 ^ 2 * 1) / m2 ^ 2 := by
    simp only [c]
    field_simp
    ring
  rw [e2]
  positivity

/-- Box 10.1: excess kurtosis (kurtosis − 3) is never below `−2`, so the reported excess
kurtoses are far inside the admissible range. -/
theorem excess_kurtosis_ge {ι : Type*} [Fintype ι] {p : ι → ℝ} (hp0 : ∀ i, 0 ≤ p i)
    (hp : ∑ i, p i = 1) (z : ι → ℝ) (hvar : 0 < cMoment p z 2) : -2 ≤ kurtosis p z - 3 := by
  have := pearson_inequality hp0 hp z hvar
  have : 0 ≤ cMoment p z 3 ^ 2 / cMoment p z 2 ^ 3 := by positivity
  linarith

/-- Box 10.1, p. 676 (Kashyap 1995): the excess kurtosis of price increases (31.2) is more than
six times that of price cuts (4.6), and both exceed the normal benchmark 0. -/
theorem kashyap_kurtosis_comparison :
    (6 : ℝ) * 4.6 < 31.2 ∧ (0 : ℝ) < 4.6 := by norm_num

/-- Box 10.1, p. 676 (Blinder 1991): 55 percent of GNP repriced no more than once a year is a
majority. -/
theorem blinder_majority : (1 / 2 : ℝ) < 0.55 := by norm_num

/-- Box 10.1, p. 676 (Kashyap 1995): an average spell of `D ∈ [12, 18]` months between price
changes means between two thirds of a change and one change per year. -/
theorem kashyap_annual_frequency {D : ℝ} (h1 : 12 ≤ D) (h2 : D ≤ 18) :
    (2 / 3 : ℝ) ≤ 12 / D ∧ 12 / D ≤ 1 := by
  have hD : 0 < D := by linarith
  constructor
  · rw [le_div_iff₀ hD]; linarith
  · rw [div_le_one hD]; exact h1

end ObstfeldRogoff.StickyPriceModels.StickyPriceEvidence

set_option linter.style.longLine false
#print axioms ObstfeldRogoff.StickyPriceModels.cesDemand
#print axioms ObstfeldRogoff.StickyPriceModels.cesDemand_at_index
#print axioms ObstfeldRogoff.StickyPriceModels.cesDemand_pos
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.rpow_lt_tangent
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.rpow_le_tangent
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.cesQuantityIndex
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.cesPriceIndex
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.cesExpenditure
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.cesPrice_sum_pos
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.cesPriceIndex_pos
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.cesPriceIndex_rpow
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.cesQuantityIndex_rpow
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.cesQuantityIndex_pos
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.ces_relative_price_sum
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.ces_demand_rpow_rho
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.ces_demand_rpow_rho_sub_one
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.ces_price_mul_demand
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.cesDemandBundle
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.cesExpenditure_demandBundle
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.cesQuantityIndex_demandBundle
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.ces_expenditure_ge
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.ces_expenditure_eq_iff
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.ces_minimum_cost
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.ces_utility_max
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.cesDemandBundle_ratio
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.cesPriceIndex_smul
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.cesPriceIndex_mono
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.ppp_of_loop
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.blocPriceIndex
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.blocPriceIndex_eq_ces
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.blocPriceIndex_pos
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.blocPriceIndex_rpow
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.bloc_ppp
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.bloc_relative_price_sum
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.worldConsumption
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.worldConsumption_pos
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.world_demand
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.demand_iff_price
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.revenue_on_demand
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.marketDiscount
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.marketDiscount_zero
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.marketDiscount_succ
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.marketDiscount_pos
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.marketDiscount_const
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.marketDiscount_succ_mul
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.wealth
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.wealth_succ
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.userCost
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.userCost_eq_fisher
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.wealth_of_budget
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.wealth_pv_identity
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.wealth_congr_after
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.wealth_congr_before
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.wealth_shift_date0
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.HouseholdEnv
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.HouseholdEnv.mk
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.HouseholdEnv.β
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.HouseholdEnv.χ
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.HouseholdEnv.κ
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.HouseholdEnv.θ
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.HouseholdEnv.r
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.HouseholdEnv.uc
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.HouseholdEnv.τ
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.HouseholdEnv.Z
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.HouseholdEnv.W0
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.HouseholdPlan
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.HouseholdPlan.mk
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.HouseholdPlan.C
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.HouseholdPlan.m
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.HouseholdPlan.y
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.HouseholdEnv.Regular
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.HouseholdEnv.periodUtility
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.HouseholdEnv.utility
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.HouseholdEnv.outlay
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.HouseholdEnv.wealthPath
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.HouseholdEnv.NoPonzi
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.HouseholdEnv.Transversality
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.HouseholdEnv.Admissible
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.HouseholdEnv.IsOptimal
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.HouseholdEnv.EulerCond
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.HouseholdEnv.MoneyCond
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.HouseholdEnv.LabourCond
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.moneyCond_iff_book
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.labourCond_iff_book
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.HouseholdEnv.discounted_marginal_utility
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.HouseholdEnv.tsum_eq_add_of_eqOn_compl
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.HouseholdEnv.period_gain_le
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.HouseholdEnv.isOptimal_of_foc
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.HouseholdEnv.hasDerivAt_log_affine
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.HouseholdEnv.eventually_pos_affine
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.HouseholdEnv.noPonzi_congr
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.HouseholdEnv.euler_of_optimal
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.HouseholdEnv.money_foc_of_optimal
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.HouseholdEnv.labour_foc_of_optimal
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.HouseholdEnv.transversality_of_optimal
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.HouseholdEnv.isOptimal_iff
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.book_tvc_identity
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.book_tvc_iff
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.real_budget_of_nominal
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.world_goods_market
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.walras_identity
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.timePreferenceRate
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.beta_mul_one_add_timePreferenceRate
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.timePreferenceRate_pos
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.steady_state_rate
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.steady_state_budget
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.foreign_steady_state_income
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.steady_state_real_balances
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.ReduxParams
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.ReduxParams.mk
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.ReduxParams.β
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.ReduxParams.χ
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.ReduxParams.κ
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.ReduxParams.θ
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.ReduxParams.n
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.ReduxParams.hβ0
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.ReduxParams.hβ1
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.ReduxParams.hχ
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.ReduxParams.hκ
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.ReduxParams.hθ
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.ReduxParams.hn0
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.ReduxParams.hn1
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.ReduxParams.δ
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.ReduxParams.K
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.ReduxParams.ybar0
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.ReduxParams.δ_pos
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.ReduxParams.β_mul_one_add_δ
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.ReduxParams.K_pos
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.ReduxParams.ybar0_pos
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.ReduxParams.ybar0_sq
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.ReduxParams.κ_mul_ybar0_sq
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.ReduxLinear
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.ReduxLinear.mk
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.ReduxLinear.θ
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.ReduxLinear.δ
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.ReduxLinear.n
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.ReduxLinear.hθ
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.ReduxLinear.hδ
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.ReduxLinear.hn0
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.ReduxLinear.hn1
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.ReduxLinear.D
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.ReduxLinear.E
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.ReduxLinear.E_pos
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.ReduxLinear.D_pos
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.ReduxLinear.D_eq
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPrimitives.ReduxLinear.D_eq_sum
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.rpow_succ_div
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.rpow_pred_div
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.rpow_neg_succ_div
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.rpow_inv_rpow_self'
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.gapFn
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.gapFn_eq
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.gapFn_strictAntiOn
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.gapFn_continuousOn
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.gapFn_sqrt
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.gapFn_pos_iff
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.gapFn_neg_iff
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.gapFn_eq_zero_iff
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.gapFn_injOn
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.gapFn_surj
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.gapInv
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.gapInv_spec
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.gapInv_gapFn
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.gapInv_strictAnti
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.gapInv_continuous
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.worldOutputIndex
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.worldOutputIndex_pos
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.worldOutputIndex_rpow
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.worldOutputIndex_comm
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.Allocation
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.Allocation.mk
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.Allocation.y
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.Allocation.ys
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.Allocation.C
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.Allocation.Cs
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.Allocation.q
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.Allocation.qs
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.Allocation.X
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.IsStatic
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.IsStatic.mk
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.IsStatic.y_pos
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.IsStatic.ys_pos
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.IsStatic.C_pos
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.IsStatic.Cs_pos
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.IsStatic.q_pos
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.IsStatic.qs_pos
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.IsStatic.X_pos
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.IsStatic.demand
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.IsStatic.demand_star
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.IsStatic.labour
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.IsStatic.labour_star
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.IsStatic.price_index
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.IsStatic.world
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.IsSteadyState
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.IsSteadyState.mk
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.IsSteadyState.static
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.IsSteadyState.budget
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.IsSteadyState.budget_star
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.IsStatic.X_rpow
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.IsStatic.X_rpow_star
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.IsStatic.C_mul_y
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.IsStatic.Cs_mul_ys
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.IsStatic.excess_eq
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.IsStatic.excess_eq_star
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.IsStatic.walras
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.IsStatic.gap_relation
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.IsStatic.X_eq
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.IsStatic.q_div_qs
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.IsStatic.eq_of_outputs
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.IsStatic.ext_of_outputs
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.ofOutputs
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.ReducedSystem
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.isSteadyState_ofOutputs
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.IsSteadyState.reduced
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.isSteadyState_iff_reduced
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.IsSteadyState.q_mul_gap
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.IsSteadyState.qs_mul_gap
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.kgap_strictAnti
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.not_lt_of_steady
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.steady_unique
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.worldOutputIndex_rpow_ge
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.exists_reduced_pos
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.exists_reduced
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.exists_unique_steady
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.steadyState
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.steadyState_spec
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.eq_steadyState
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.symmetricSteady
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.isSteadyState_zero_iff
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.symmetric_real_balances
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.steady_creditor
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.steady_debtor
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.steady_C_gt_iff
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.plannerObjective
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.plannerOutput
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.planner_max
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.ybar0_lt_plannerOutput
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.planner_strictMonoOn
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.ybar0_tendsto_planner
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.FlexPath
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.FlexPath.mk
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.FlexPath.alloc
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.FlexPath.r
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.FlexPath.B
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.IsFlexEqm
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.IsFlexEqm.mk
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.IsFlexEqm.static
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.IsFlexEqm.euler
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.IsFlexEqm.euler_star
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.IsFlexEqm.budget
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.IsFlexEqm.gross_rate_pos
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.IsFlexEqm.no_ponzi
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.IsFlexEqm.transversality
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.IsFlexEqm.foreign_budget
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.IsFlexEqm.ratio_const
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.IsStatic.sq_output
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxSteadyState.flexible_path_is_steady
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxLogLinear.hasDerivAt_rpow_exp
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxLogLinear.hasDerivAt_log_bloc
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxLogLinear.linearise_27
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxLogLinear.linearise_28
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxLogLinear.ppp_log_exact
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxLogLinear.eq29_of_27_28
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxLogLinear.log_demand_exact
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxLogLinear.linearise_world
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxLogLinear.eq32_of_demands
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxLogLinear.labour_log_exact
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxLogLinear.linearise_35
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxLogLinear.linearise_37
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxLogLinear.eq39_of_37_38
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxLogLinear.linearise_40
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxLogLinear.linearise_41
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxLogLinear.SteadyVars
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxLogLinear.SteadyVars.mk
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxLogLinear.SteadyVars.c
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxLogLinear.SteadyVars.cs
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxLogLinear.SteadyVars.y
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxLogLinear.SteadyVars.ys
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxLogLinear.SteadyVars.ph
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxLogLinear.SteadyVars.pf
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxLogLinear.SteadyVars.p
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxLogLinear.SteadyVars.ps
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxLogLinear.SteadyVars.e
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxLogLinear.SteadyVars.cW
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxLogLinear.SteadyLinear
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxLogLinear.SteadyLinear.mk
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxLogLinear.SteadyLinear.eq27
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxLogLinear.SteadyLinear.eq28
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxLogLinear.SteadyLinear.eq30
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxLogLinear.SteadyLinear.eq31
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxLogLinear.SteadyLinear.eq32
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxLogLinear.SteadyLinear.eq33
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxLogLinear.SteadyLinear.eq34
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxLogLinear.SteadyLinear.eq40
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxLogLinear.SteadyLinear.eq41
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxLogLinear.SteadyLinear.eq50
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxLogLinear.SteadyLinear.eq51
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxLogLinear.steadySolution
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxLogLinear.steadyLinear_iff
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxLogLinear.steadyLinear_existsUnique
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxLogLinear.steadyLinear_consequences
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxLogLinear.dampening_iff
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxLogLinear.shortRun_prices
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxLogLinear.linearise_55
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxLogLinear.shortRun_ca
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxLogLinear.consumption_ratio_exact
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxLogLinear.eq57_exact
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.nominal_rate_exact
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.uip_exact
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.no_overshooting_exact
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.mm_no_overshooting
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.mm_iterate
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.forward_solution_unique
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.forward_solution_exists
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.forward_solution_const
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.gg_schedule
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.ShortVars
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.ShortVars.mk
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.ShortVars.c
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.ShortVars.cs
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.ShortVars.y
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.ShortVars.ys
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.ShortVars.p
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.ShortVars.ps
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.ShortVars.e
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.ShortVars.cW
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.ShortVars.r
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.ShortVars.b
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.MoneyShockEqm
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.MoneyShockEqm.mk
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.MoneyShockEqm.eq27
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.MoneyShockEqm.eq28
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.MoneyShockEqm.eq30
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.MoneyShockEqm.eq31
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.MoneyShockEqm.eq32
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.MoneyShockEqm.eq35
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.MoneyShockEqm.eq36
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.MoneyShockEqm.eq37
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.MoneyShockEqm.eq38
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.MoneyShockEqm.eq55
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.MoneyShockEqm.longrun
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.shortRunSolution
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.MoneyShockEqm.relations
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.moneyShock_iff
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.moneyShock_existsUnique
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.moneyShock_closed_forms
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.moneyShock_world
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.foreign_money_lowers_home_output
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.exchangeRateCoef
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.exchangeRateCoef_one
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.exchangeRateCoef_mem
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.exchangeRateCoef_strictAntiOn
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.exchangeRateCoef_tendsto
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.gg_slope_tendsto
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.eq65_sign
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.tot_ratio_bounds
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.ca_strictAnti_in_n
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.country_size_correction
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.linearise_nominal_rate
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.nominal_rate_unchanged
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.solve_mm_gg
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.temporary_shock
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.temporary_shock_appreciation
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.temporary_scaling_lt_one
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.ex1_nominal_rate
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.ex1_real_balances_fall
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.linearise_37_growth
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.eq39_growth
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.ex1_sums
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.ex1_growth_shock
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.ex1_growth_shock_late
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.ex1_current_account
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.blocPriceIndex_self
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.Date1Vars
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.Date1Vars.mk
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.Date1Vars.E1
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.Date1Vars.P1
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.Date1Vars.Ps1
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.Date1Vars.C1
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.Date1Vars.Cs1
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.Date1Vars.y1
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.Date1Vars.ys1
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.Date1Vars.B2
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.Date1Vars.r2
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.Date1Vars.i2
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.Date1Vars.is2
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.Date1Vars.P2
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.Date1Vars.Ps2
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.Date1Vars.lr
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.IsEquiEqm
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.IsEquiEqm.mk
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.IsEquiEqm.E1_pos
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.IsEquiEqm.C1_pos
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.IsEquiEqm.Cs1_pos
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.IsEquiEqm.i2_pos
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.IsEquiEqm.is2_pos
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.IsEquiEqm.P2_pos
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.IsEquiEqm.Ps2_pos
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.IsEquiEqm.r2_pos
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.IsEquiEqm.price
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.IsEquiEqm.price_star
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.IsEquiEqm.demand
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.IsEquiEqm.demand_star
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.IsEquiEqm.ca
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.IsEquiEqm.euler
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.IsEquiEqm.euler_star
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.IsEquiEqm.money
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.IsEquiEqm.money_star
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.IsEquiEqm.fisher
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.IsEquiEqm.fisher_star
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.IsEquiEqm.longrun
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.IsEquiEqm.money2
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.IsEquiEqm.money2_star
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.equiproportionate_unique
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.longrun_assets
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.equiSolution
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.equiproportionate_exists
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.equiproportionate_demand_bound
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.equiGain
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.equiGain_eq
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.equiGain_pos
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.equiGain_hasDerivAt_one
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxMoneyShocks.equiproportionate_real_balances
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxWelfare.linearOf
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxWelfare.twoRegime
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxWelfare.hasSum_twoRegime
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxWelfare.beta_div_one_sub
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxWelfare.periodWelfare
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxWelfare.lifetimeWelfare
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxWelfare.realWelfare
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxWelfare.realWelfare_eq
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxWelfare.lifetimeWelfare_twoRegime
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxWelfare.hasDerivAt_log_exp_path
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxWelfare.hasDerivAt_periodWelfare
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxWelfare.welfare_hasDerivAt
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxWelfare.dUR
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxWelfare.welfare_eq75
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxWelfare.realBalanceTerm
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxWelfare.total_welfare_hasDerivAt
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxWelfare.quasi_reduced_forms
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxWelfare.welfare_e_cancels
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxWelfare.welfare_eq76
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxWelfare.welfare_eq76_hasDerivAt
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxWelfare.foreign_shock_total
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxWelfare.realBalance_coef
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxWelfare.foreign_shock_welfare_pos_iff
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxWelfare.welfare_pos_forall_chi_iff
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxWelfare.welfare_threshold
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxWelfare.no_threshold_of_le
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxWelfare.counterexampleModel
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxWelfare.counterexample_theta6
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxWelfare.home_shock_real_balances
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxWelfare.foreign_shock_real_balances
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxWelfare.producerPayoff
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxWelfare.marginalPayoff
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxWelfare.producerPayoff_at_price
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxWelfare.producerPayoff_le
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxWelfare.gain_le_sq
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxWelfare.producerPayoff_isMax_iff
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxWelfare.marginalPayoff_at_demand
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxWelfare.menu_cost_second_order
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxWelfare.menu_cost_rationale
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxWelfare.meet_demand_iff
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxWelfare.steady_price_exceeds_mc
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxWelfare.tax_budget_rebate
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxWelfare.taxed_symmetric_output
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxWelfare.taxed_output_strictAntiOn
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxWelfare.taxed_labour_log_exact
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxWelfare.taxedOutput
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxWelfare.κ_mul_taxedOutput_sq
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxWelfare.dURtax
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxWelfare.welfare_tax_hasDerivAt
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxWelfare.dURtax_eq
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxWelfare.welfare_eq81
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxWelfare.welfare81_neg_iff
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxWelfare.welfare81_large_theta
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxWelfare.welfare81_small_theta
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxWelfare.home_shock_size
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxWelfare.small_country_limit
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxWelfare.ex3_steady_existsUnique
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxWelfare.ex3_consumption_flat
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxWelfare.Ex3Vars
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxWelfare.Ex3Vars.mk
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxWelfare.Ex3Vars.c
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxWelfare.Ex3Vars.y
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxWelfare.Ex3Vars.p
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxWelfare.Ex3Vars.e
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxWelfare.Ex3Vars.b
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxWelfare.Ex3Vars.cb
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxWelfare.Ex3Vars.yb
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxWelfare.Ex3Vars.pb
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxWelfare.Ex3Vars.eb
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxWelfare.Ex3Eqm
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxWelfare.Ex3Eqm.mk
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxWelfare.Ex3Eqm.price
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxWelfare.Ex3Eqm.demand
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxWelfare.Ex3Eqm.ca
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxWelfare.Ex3Eqm.euler
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxWelfare.Ex3Eqm.money
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxWelfare.Ex3Eqm.money_lr
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxWelfare.Ex3Eqm.demand_lr
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxWelfare.Ex3Eqm.labour_lr
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxWelfare.Ex3Eqm.budget_lr
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxWelfare.ex3Solution
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxWelfare.ex3_iff
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxWelfare.ex3_matches_two_country
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxWelfare.ex3_welfare_zero
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxFiscalProductivity.labour_log_exact_kappa
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxFiscalProductivity.linearise_100
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxFiscalProductivity.fn24_world
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxFiscalProductivity.world_demand_with_gov
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxFiscalProductivity.gov_budget_combined
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxFiscalProductivity.gov_steady_budget
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxFiscalProductivity.linearise_113
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxFiscalProductivity.linearise_118
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxFiscalProductivity.linearise_121
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxFiscalProductivity.wavg
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxFiscalProductivity.FiscalSteadyLinear
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxFiscalProductivity.FiscalSteadyLinear.mk
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxFiscalProductivity.FiscalSteadyLinear.eq27
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxFiscalProductivity.FiscalSteadyLinear.eq28
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxFiscalProductivity.FiscalSteadyLinear.eq113
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxFiscalProductivity.FiscalSteadyLinear.eq114
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxFiscalProductivity.FiscalSteadyLinear.eq32
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxFiscalProductivity.FiscalSteadyLinear.eq116
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxFiscalProductivity.FiscalSteadyLinear.eq117
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxFiscalProductivity.FiscalSteadyLinear.eq118
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxFiscalProductivity.FiscalSteadyLinear.eq119
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxFiscalProductivity.FiscalSteadyLinear.eq50
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxFiscalProductivity.FiscalSteadyLinear.eq51
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxFiscalProductivity.fiscalToT
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxFiscalProductivity.fiscalSteadySolution
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxFiscalProductivity.fiscalSteadyLinear_iff
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxFiscalProductivity.fiscalSteady_consequences
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxFiscalProductivity.FiscalShockEqm
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxFiscalProductivity.FiscalShockEqm.mk
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxFiscalProductivity.FiscalShockEqm.eq27
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxFiscalProductivity.FiscalShockEqm.eq28
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxFiscalProductivity.FiscalShockEqm.eq113
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxFiscalProductivity.FiscalShockEqm.eq114
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxFiscalProductivity.FiscalShockEqm.eq32
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxFiscalProductivity.FiscalShockEqm.eq35
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxFiscalProductivity.FiscalShockEqm.eq36
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxFiscalProductivity.FiscalShockEqm.eq37
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxFiscalProductivity.FiscalShockEqm.eq38
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxFiscalProductivity.FiscalShockEqm.eq121
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxFiscalProductivity.FiscalShockEqm.longrun
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxFiscalProductivity.fiscalE
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxFiscalProductivity.fiscalShortRunSolution
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxFiscalProductivity.mm_relation
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxFiscalProductivity.fiscalShock_iff
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxFiscalProductivity.fiscalShock_existsUnique
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxFiscalProductivity.fiscal_zero_iff_money
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxFiscalProductivity.fiscal_gg
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxFiscalProductivity.fiscal_world
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxFiscalProductivity.fiscal_nominal_rate_unchanged
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxFiscalProductivity.productivity_eq106_107
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxFiscalProductivity.productivity_corollaries
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxFiscalProductivity.gov_eq128_129
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxFiscalProductivity.gov_eq122
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxFiscalProductivity.gov_current_account
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxFiscalProductivity.temporary_world_spending
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxFiscalProductivity.gov_flex_terms_of_trade
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxFiscalProductivity.dURprod
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxFiscalProductivity.fiscal_welfare_hasDerivAt
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxFiscalProductivity.productivity_welfare
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxFiscalProductivity.fn25_welfare_hasDerivAt
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxFiscalProductivity.gov_flex_welfare
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxFiscalProductivity.gov_temporary_welfare
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxFiscalProductivity.gov_future_welfare
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxFiscalProductivity.gov_permanent_welfare
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPresetWages.firmOutput
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPresetWages.wageBill
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPresetWages.firm_cost_ge
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPresetWages.firm_cost_eq_iff
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPresetWages.firm_min_cost
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPresetWages.symmetric_firm
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPresetWages.markup_isGreatest
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPresetWages.labour_income_on_demand
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPresetWages.worker_isOptimal_iff
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPresetWages.wage_foc_symmetric
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPresetWages.presetWage_labour_iff
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPresetWages.wageParams
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPresetWages.wageParams_ybar0
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPresetWages.presetWage_labour_log_exact
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPresetWages.wage_profit_income
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPresetWages.markup_log_exact
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPresetWages.PresetWageEqm
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPresetWages.PresetWageEqm.mk
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPresetWages.PresetWageEqm.preset
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPresetWages.PresetWageEqm.preset_star
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPresetWages.PresetWageEqm.markup
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPresetWages.PresetWageEqm.markup_star
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPresetWages.PresetWageEqm.eq27
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPresetWages.PresetWageEqm.eq28
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPresetWages.PresetWageEqm.eq30
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPresetWages.PresetWageEqm.eq31
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPresetWages.PresetWageEqm.eq32
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPresetWages.PresetWageEqm.eq35
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPresetWages.PresetWageEqm.eq36
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPresetWages.PresetWageEqm.eq37
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPresetWages.PresetWageEqm.eq38
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPresetWages.PresetWageEqm.eq55
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPresetWages.PresetWageEqm.longrun
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPresetWages.presetWage_iff_money
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPresetWages.worker_meets_demand
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPresetWages.steady_wage_exceeds_mrs
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPresetWages.ptm_optimal
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPresetWages.ptm_pass_through
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPresetWages.ptm_different_elasticities
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxPresetWages.normalisation_flag
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxLinearisationLink.linkLinear
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxLinearisationLink.relSize
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxLinearisationLink.outputB
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxLinearisationLink.outputStarB
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxLinearisationLink.gapValue
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxLinearisationLink.gapFactor
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxLinearisationLink.steadyState_zero
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxLinearisationLink.steadyState_eq_ofOutputs
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxLinearisationLink.outputB_pos
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxLinearisationLink.gapInv_zero
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxLinearisationLink.outputB_eq
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxLinearisationLink.outputStarB_eq
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxLinearisationLink.phi_eq
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxLinearisationLink.gapValue_zero
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxLinearisationLink.worldOutputIndex_self
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxLinearisationLink.gapFactorBound
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxLinearisationLink.gapFactorBound_pos
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxLinearisationLink.A_lower
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxLinearisationLink.gapValue_bound
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxLinearisationLink.gapValue_continuousAt
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxLinearisationLink.gapFactor_continuousAt
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxLinearisationLink.gapFactor_zero
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxLinearisationLink.hasDerivAt_mul_self
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxLinearisationLink.gapValue_hasDerivAt
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxLinearisationLink.gapFn_hasDerivAt_ybar0
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxLinearisationLink.gapInv_hasDerivAt_zero
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxLinearisationLink.output_hasDerivAt
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxLinearisationLink.output_star_hasDerivAt
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxLinearisationLink.output_zero
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxLinearisationLink.worldSum
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxLinearisationLink.worldSum_pos
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxLinearisationLink.worldSum_hasDerivAt
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxLinearisationLink.logX_hasDerivAt
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxLinearisationLink.logOutput_hasDerivAt
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxLinearisationLink.logPrice_hasDerivAt
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxLinearisationLink.logConsumption_hasDerivAt
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxLinearisationLink.hasDerivAt_along
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxLinearisationLink.linearisation_link
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxLinearisationLink.nominal_block_exact
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxLinearisationLink.derivVars
#print axioms ObstfeldRogoff.StickyPriceModels.ReduxLinearisationLink.linearisation_link_system
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.rpow_div_le_tangent
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.rpow_le_tangent
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.log_tangent
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.moneyU
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.hasDerivAt_moneyU
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.moneyU_le_tangent
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.moneyU_strictMonoOn
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.disc
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.wealth
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.disc_pos
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.disc_succ_mul
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.disc_mul_wealth
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.disc_mul_wealth_sub
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.tsum_eq_add_of_eq_off
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.NoPonzi
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.LiminfNonpos
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.IsOptimal
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.le_of_tendsto_of_frequently
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.isOptimal_of_saddle
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.noPonzi_of_perturb
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.perturb_utility_le
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.perturb_utility_le_of_pv
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.liminfNonpos_of_isOptimal
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.cpi
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.composite
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.cpi_pos
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.cpi_mul_composite
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.wamgm_le
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.cpi_mul_composite_le
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.cpi_isMinCost
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.split_iff_89
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.Economy
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.Economy.mk
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.Economy.β
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.Economy.r
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.Economy.γ
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.Economy.χ
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.Economy.ε
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.Economy.κ
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.Economy.θ
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.Economy.yT
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.Economy.Valid
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.Prices
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.Prices.mk
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.Prices.PT
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.Prices.PN
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.Prices.CA
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.Prices.τ
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.userCost
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.Prices.Valid
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.Choice
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.Choice.mk
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.Choice.cT
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.Choice.cN
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.Choice.money
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.Choice.y
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.posChoice
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.relPrice
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.cpiAt
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.periodU
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.invDemand
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.realRevenue
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.netRes
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.initWealth
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.HouseholdOptimal
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.cesDemand_invDemand
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.invDemand_mul
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.moneyPrev
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.Budget84
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.budget84_iff_wealth
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.EulerFOC
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.IntraFOC
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.MoneyFOC
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.LabourFOC
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.periodLagrangian_le
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.discounted_mu_of_euler
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.householdOptimal_of_foc
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.isLocalMax_of_perturb
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.intraFOC_of_optimal
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.moneyFOC_of_optimal
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.labourFOC_of_optimal
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.eulerFOC_of_optimal
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.liminfNonpos_of_householdOptimal
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.householdOptimal_iff
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.money_88
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.labour_90
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.money_92
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.IsEquilibrium
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.invDemand_self
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.bonds
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.moneyBubble
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.realRevenue_symm
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.bonds_recursion
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.cT_const
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.disc_bonds_closed
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.tendsto_disc
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.ge_of_tendsto_of_frequently
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.disc_wealth_split
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.cT_ge_endowment
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.cT_eq_endowment_iff
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.balanced_current_account
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.ybarN
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.ybarN_pos
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.kappa_mul_ybarN_sq
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.output_93
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.cpi_eq_mul
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.relPriceBar
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.cpiRatio
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.realMoneyBar
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.relPriceBar_pos
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.cpiRatio_pos
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.realMoneyBar_pos
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.steadyState_unique
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.steadyPrices
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.steadyChoice
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesModel.steadyState_isEquilibrium
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesOvershooting.expo
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesOvershooting.impactGap
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesOvershooting.expo_pos
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesOvershooting.expo_lt_iff
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesOvershooting.impactGap_strictAntiOn
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesOvershooting.impact_exists_unique
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesOvershooting.root_lt
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesOvershooting.impactGap_at_mu
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesOvershooting.overshoot_iff
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesOvershooting.overshoot_iff_of_lt_one
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesOvershooting.one_lt_root
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesOvershooting.realBalances_rise
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesOvershooting.ratioMap
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesOvershooting.impactGap_scaled
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesOvershooting.ratioMap_one
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesOvershooting.hasStrictDerivAt_ratioMap
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesOvershooting.hasDerivAt_impact
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesOvershooting.hasDerivAt_log_impact
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesOvershooting.coef99_gt_one_iff
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesOvershooting.loglinear_99
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesOvershooting.hasDerivAt_logMoneyDemand_m
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesOvershooting.hasDerivAt_logMoneyDemand_u
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesOvershooting.cpi_scale
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesOvershooting.pT0
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesOvershooting.pN0
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesOvershooting.pT0_pos
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesOvershooting.pN0_pos
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesOvershooting.longRun_neutral
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesOvershooting.cpi_initial
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesOvershooting.realMoneyBar_rpow_neg
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesOvershooting.shockPrices
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesOvershooting.shockChoice
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesOvershooting.stickyNetRes
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesOvershooting.stickySet
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesOvershooting.StickyOptimal
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesOvershooting.IsStickyEquilibrium
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesOvershooting.shock_userCost
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesOvershooting.shock_cpi
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesOvershooting.shockPrices_valid
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesOvershooting.M0_div_cpi
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesOvershooting.shock_moneyFOC0_iff
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesOvershooting.stickyLagrangian_le
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesOvershooting.shock_markup_iff
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesOvershooting.disc_eq_pow
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesOvershooting.shock_intra
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesOvershooting.shock_money_later
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesOvershooting.shock_labour_later
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesOvershooting.shock_wealth
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesOvershooting.shock_isStickyEquilibrium
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesOvershooting.perturb_le_gen
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesOvershooting.shock_necessary
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesOvershooting.shock_equilibrium_iff
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesOvershooting.shock_equilibrium_exists_near_one
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesOvershooting.exchangeRate
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesOvershooting.shock_exchangeRate
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesOvershooting.exchangeRate_overshoots_iff
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesOvershooting.shock_output_rises
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesOvershooting.shock_95
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesOvershooting.realGain
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesOvershooting.realGain_pos
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesOvershooting.shock_periodU_later
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesOvershooting.welfare_gain_eq
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesOvershooting.welfare_gain_pos
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesOvershooting.hasDerivAt_realGain
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesOvershooting.realExchangeRate
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesOvershooting.grossRealRate
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesOvershooting.real_interest_parity
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesOvershooting.ex2_real_depreciation
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesOvershooting.ex2_log_parity
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesOvershooting.hasDerivAt_realDepreciation
#print axioms ObstfeldRogoff.StickyPriceModels.NontradablesOvershooting.ex2_internal_real_rate
#print axioms ObstfeldRogoff.StickyPriceModels.PresetWagesSmallCountry.rpow_lt_tangent
#print axioms ObstfeldRogoff.StickyPriceModels.PresetWagesSmallCountry.laborAggregate
#print axioms ObstfeldRogoff.StickyPriceModels.PresetWagesSmallCountry.wageIndex
#print axioms ObstfeldRogoff.StickyPriceModels.PresetWagesSmallCountry.laborDemand
#print axioms ObstfeldRogoff.StickyPriceModels.PresetWagesSmallCountry.wageIndex_pos
#print axioms ObstfeldRogoff.StickyPriceModels.PresetWagesSmallCountry.wageIndex_rpow
#print axioms ObstfeldRogoff.StickyPriceModels.PresetWagesSmallCountry.laborDemand_cost
#print axioms ObstfeldRogoff.StickyPriceModels.PresetWagesSmallCountry.laborDemand_output
#print axioms ObstfeldRogoff.StickyPriceModels.PresetWagesSmallCountry.labor_cost_ge
#print axioms ObstfeldRogoff.StickyPriceModels.PresetWagesSmallCountry.firm_profit_le
#print axioms ObstfeldRogoff.StickyPriceModels.PresetWagesSmallCountry.firm_zero_profit
#print axioms ObstfeldRogoff.StickyPriceModels.PresetWagesSmallCountry.firm_price_eq_wageIndex
#print axioms ObstfeldRogoff.StickyPriceModels.PresetWagesSmallCountry.symmetric_wages
#print axioms ObstfeldRogoff.StickyPriceModels.PresetWagesSmallCountry.wageEconomy
#print axioms ObstfeldRogoff.StickyPriceModels.PresetWagesSmallCountry.wageEconomy_valid
#print axioms ObstfeldRogoff.StickyPriceModels.PresetWagesSmallCountry.laborIncome
#print axioms ObstfeldRogoff.StickyPriceModels.PresetWagesSmallCountry.worker_optimal_iff
#print axioms ObstfeldRogoff.StickyPriceModels.PresetWagesSmallCountry.worker_136
#print axioms ObstfeldRogoff.StickyPriceModels.PresetWagesSmallCountry.laborSupply_140
#print axioms ObstfeldRogoff.StickyPriceModels.PresetWagesSmallCountry.wage_steadyState_isEquilibrium
#print axioms ObstfeldRogoff.StickyPriceModels.PresetWagesSmallCountry.presetWage_price
#print axioms ObstfeldRogoff.StickyPriceModels.PresetWagesSmallCountry.presetWage_equilibrium_iff
#print axioms ObstfeldRogoff.StickyPriceModels.PresetWagesSmallCountry.presetWage_same_impact
#print axioms ObstfeldRogoff.StickyPriceModels.PresetWagesSmallCountry.presetWage_overshoots_iff
#print axioms ObstfeldRogoff.StickyPriceModels.PresetWagesSmallCountry.presetWage_welfare_gain_pos
#print axioms ObstfeldRogoff.StickyPriceModels.CashInAdvanceCredibility.ciaU
#print axioms ObstfeldRogoff.StickyPriceModels.CashInAdvanceCredibility.ciaNetRes
#print axioms ObstfeldRogoff.StickyPriceModels.CashInAdvanceCredibility.ciaSet
#print axioms ObstfeldRogoff.StickyPriceModels.CashInAdvanceCredibility.CIAOptimal
#print axioms ObstfeldRogoff.StickyPriceModels.CashInAdvanceCredibility.flexRev
#print axioms ObstfeldRogoff.StickyPriceModels.CashInAdvanceCredibility.flexYs
#print axioms ObstfeldRogoff.StickyPriceModels.CashInAdvanceCredibility.ciaOptimal_of_foc
#print axioms ObstfeldRogoff.StickyPriceModels.CashInAdvanceCredibility.cia_intra_of_optimal
#print axioms ObstfeldRogoff.StickyPriceModels.CashInAdvanceCredibility.cia_euler_of_optimal
#print axioms ObstfeldRogoff.StickyPriceModels.CashInAdvanceCredibility.cia_labour_of_optimal
#print axioms ObstfeldRogoff.StickyPriceModels.CashInAdvanceCredibility.cia_liminfNonpos
#print axioms ObstfeldRogoff.StickyPriceModels.CashInAdvanceCredibility.ciaOptimal_iff
#print axioms ObstfeldRogoff.StickyPriceModels.CashInAdvanceCredibility.cia_flexible_output
#print axioms ObstfeldRogoff.StickyPriceModels.CashInAdvanceCredibility.ciaSteadyPrices
#print axioms ObstfeldRogoff.StickyPriceModels.CashInAdvanceCredibility.ciaSteadyChoice
#print axioms ObstfeldRogoff.StickyPriceModels.CashInAdvanceCredibility.cia_steadyState_optimal
#print axioms ObstfeldRogoff.StickyPriceModels.CashInAdvanceCredibility.yPlan
#print axioms ObstfeldRogoff.StickyPriceModels.CashInAdvanceCredibility.planner_unique
#print axioms ObstfeldRogoff.StickyPriceModels.CashInAdvanceCredibility.ybarN_lt_yPlan
#print axioms ObstfeldRogoff.StickyPriceModels.CashInAdvanceCredibility.kappa_gap
#print axioms ObstfeldRogoff.StickyPriceModels.CashInAdvanceCredibility.presetPN
#print axioms ObstfeldRogoff.StickyPriceModels.CashInAdvanceCredibility.flexible_PN
#print axioms ObstfeldRogoff.StickyPriceModels.CashInAdvanceCredibility.preset_output
#print axioms ObstfeldRogoff.StickyPriceModels.CashInAdvanceCredibility.preset_output_of_optimal
#print axioms ObstfeldRogoff.StickyPriceModels.CashInAdvanceCredibility.preset_output_finite_state
#print axioms ObstfeldRogoff.StickyPriceModels.CashInAdvanceCredibility.utilAt
#print axioms ObstfeldRogoff.StickyPriceModels.CashInAdvanceCredibility.lagMoney
#print axioms ObstfeldRogoff.StickyPriceModels.CashInAdvanceCredibility.authObj
#print axioms ObstfeldRogoff.StickyPriceModels.CashInAdvanceCredibility.oneShotObj
#print axioms ObstfeldRogoff.StickyPriceModels.CashInAdvanceCredibility.inflation_eq_money_growth
#print axioms ObstfeldRogoff.StickyPriceModels.CashInAdvanceCredibility.authObj_sub
#print axioms ObstfeldRogoff.StickyPriceModels.CashInAdvanceCredibility.fullObj
#print axioms ObstfeldRogoff.StickyPriceModels.CashInAdvanceCredibility.fullObj_sub
#print axioms ObstfeldRogoff.StickyPriceModels.CashInAdvanceCredibility.gameObj
#print axioms ObstfeldRogoff.StickyPriceModels.CashInAdvanceCredibility.oneShotObj_eq_gameObj
#print axioms ObstfeldRogoff.StickyPriceModels.CashInAdvanceCredibility.BestResponseFOC
#print axioms ObstfeldRogoff.StickyPriceModels.CashInAdvanceCredibility.gameObj_max_iff
#print axioms ObstfeldRogoff.StickyPriceModels.CashInAdvanceCredibility.bestResponse_exists_unique
#print axioms ObstfeldRogoff.StickyPriceModels.CashInAdvanceCredibility.IsOneShotEquilibrium
#print axioms ObstfeldRogoff.StickyPriceModels.CashInAdvanceCredibility.oneShotEquilibrium_iff
#print axioms ObstfeldRogoff.StickyPriceModels.CashInAdvanceCredibility.book_equilibrium
#print axioms ObstfeldRogoff.StickyPriceModels.CashInAdvanceCredibility.conventional_equilibrium
#print axioms ObstfeldRogoff.StickyPriceModels.CashInAdvanceCredibility.conventional_inflation_bias
#print axioms ObstfeldRogoff.StickyPriceModels.CashInAdvanceCredibility.commitment_conventional
#print axioms ObstfeldRogoff.StickyPriceModels.CashInAdvanceCredibility.commitment_gross_no_optimum
#print axioms ObstfeldRogoff.StickyPriceModels.PassThrough.elasticity
#print axioms ObstfeldRogoff.StickyPriceModels.PassThrough.segmentedProfit
#print axioms ObstfeldRogoff.StickyPriceModels.PassThrough.ceProfit
#print axioms ObstfeldRogoff.StickyPriceModels.PassThrough.ceMarkupPrice
#print axioms ObstfeldRogoff.StickyPriceModels.PassThrough.linProfit
#print axioms ObstfeldRogoff.StickyPriceModels.PassThrough.linPrice
#print axioms ObstfeldRogoff.StickyPriceModels.PassThrough.convexCostProfit
#print axioms ObstfeldRogoff.StickyPriceModels.PassThrough.exportProfit
#print axioms ObstfeldRogoff.StickyPriceModels.PassThrough.lcpLoss
#print axioms ObstfeldRogoff.StickyPriceModels.PassThrough.segmented_optimum_iff
#print axioms ObstfeldRogoff.StickyPriceModels.PassThrough.convexCostProfit_gap
#print axioms ObstfeldRogoff.StickyPriceModels.PassThrough.convexCost_optimum_iff
#print axioms ObstfeldRogoff.StickyPriceModels.PassThrough.convexCost_foreign_price_depends_on_home_demand
#print axioms ObstfeldRogoff.StickyPriceModels.PassThrough.markup_bernoulli
#print axioms ObstfeldRogoff.StickyPriceModels.PassThrough.markup_bernoulli_strict
#print axioms ObstfeldRogoff.StickyPriceModels.PassThrough.ceMarkupPrice_pos
#print axioms ObstfeldRogoff.StickyPriceModels.PassThrough.ceMarkupPrice_gt_cost
#print axioms ObstfeldRogoff.StickyPriceModels.PassThrough.ceProfit_ratio
#print axioms ObstfeldRogoff.StickyPriceModels.PassThrough.ceProfit_le_markup
#print axioms ObstfeldRogoff.StickyPriceModels.PassThrough.ceProfit_lt_markup
#print axioms ObstfeldRogoff.StickyPriceModels.PassThrough.ce_optimal_price_iff
#print axioms ObstfeldRogoff.StickyPriceModels.PassThrough.foc_of_isLocalMax
#print axioms ObstfeldRogoff.StickyPriceModels.PassThrough.lerner_rule
#print axioms ObstfeldRogoff.StickyPriceModels.PassThrough.ce_demand_elasticity
#print axioms ObstfeldRogoff.StickyPriceModels.PassThrough.ce_lerner_index
#print axioms ObstfeldRogoff.StickyPriceModels.PassThrough.markup_factor_gt_one
#print axioms ObstfeldRogoff.StickyPriceModels.PassThrough.markup_factor_strictAntiOn
#print axioms ObstfeldRogoff.StickyPriceModels.PassThrough.markup_factor_tendsto_one
#print axioms ObstfeldRogoff.StickyPriceModels.PassThrough.cesDemand_eq_const_elast
#print axioms ObstfeldRogoff.StickyPriceModels.PassThrough.cesDemand_optimal_price_iff
#print axioms ObstfeldRogoff.StickyPriceModels.PassThrough.exportProfit_eq
#print axioms ObstfeldRogoff.StickyPriceModels.PassThrough.ceMarkupPrice_div
#print axioms ObstfeldRogoff.StickyPriceModels.PassThrough.ptm_optimal_prices_iff
#print axioms ObstfeldRogoff.StickyPriceModels.PassThrough.ptm_loop_of_equal_elasticity
#print axioms ObstfeldRogoff.StickyPriceModels.PassThrough.ptm_loop_iff
#print axioms ObstfeldRogoff.StickyPriceModels.PassThrough.elasticity_const_add_div
#print axioms ObstfeldRogoff.StickyPriceModels.PassThrough.ce_passThrough_elasticity
#print axioms ObstfeldRogoff.StickyPriceModels.PassThrough.ce_passThrough_exact
#print axioms ObstfeldRogoff.StickyPriceModels.PassThrough.ce_home_currency_export_price
#print axioms ObstfeldRogoff.StickyPriceModels.PassThrough.linProfit_gap
#print axioms ObstfeldRogoff.StickyPriceModels.PassThrough.lin_optimal_price_iff
#print axioms ObstfeldRogoff.StickyPriceModels.PassThrough.linPrice_bounds
#print axioms ObstfeldRogoff.StickyPriceModels.PassThrough.lin_passThrough_elasticity
#print axioms ObstfeldRogoff.StickyPriceModels.PassThrough.lin_passThrough_bounds
#print axioms ObstfeldRogoff.StickyPriceModels.PassThrough.lin_passThrough_strictMonoOn_cost
#print axioms ObstfeldRogoff.StickyPriceModels.PassThrough.lin_passThrough_strictAntiOn_exchange_rate
#print axioms ObstfeldRogoff.StickyPriceModels.PassThrough.lin_demand_elasticity_at_optimum
#print axioms ObstfeldRogoff.StickyPriceModels.PassThrough.lin_optimal_demand_elasticity_props
#print axioms ObstfeldRogoff.StickyPriceModels.PassThrough.lin_price_falls_less_than_proportionally
#print axioms ObstfeldRogoff.StickyPriceModels.PassThrough.foreign_optimum_invariant_to_nominal_scaling
#print axioms ObstfeldRogoff.StickyPriceModels.PassThrough.markup_invariant_to_nominal_scaling
#print axioms ObstfeldRogoff.StickyPriceModels.PassThrough.home_optimum_homogeneous
#print axioms ObstfeldRogoff.StickyPriceModels.PassThrough.ce_markup_invariant_rigid_wage
#print axioms ObstfeldRogoff.StickyPriceModels.PassThrough.lin_markup_strictMonoOn_rigid_wage
#print axioms ObstfeldRogoff.StickyPriceModels.PassThrough.pcp_passThrough_elasticity
#print axioms ObstfeldRogoff.StickyPriceModels.PassThrough.lcp_passThrough_elasticity
#print axioms ObstfeldRogoff.StickyPriceModels.PassThrough.pcp_markup
#print axioms ObstfeldRogoff.StickyPriceModels.PassThrough.lcp_markup
#print axioms ObstfeldRogoff.StickyPriceModels.PassThrough.pcp_sales_strictMonoOn
#print axioms ObstfeldRogoff.StickyPriceModels.PassThrough.lcp_meets_demand_iff
#print axioms ObstfeldRogoff.StickyPriceModels.PassThrough.lcpLoss_nonneg
#print axioms ObstfeldRogoff.StickyPriceModels.PassThrough.lcpLoss_pos
#print axioms ObstfeldRogoff.StickyPriceModels.PassThrough.lcpLoss_self
#print axioms ObstfeldRogoff.StickyPriceModels.PassThrough.lcpLoss_hasDerivAt_zero
#print axioms ObstfeldRogoff.StickyPriceModels.PassThrough.lcp_menu_cost_neighbourhood
#print axioms ObstfeldRogoff.StickyPriceModels.PassThrough.retail_passThrough_elasticity
#print axioms ObstfeldRogoff.StickyPriceModels.PassThrough.retail_passThrough_bounds
#print axioms ObstfeldRogoff.StickyPriceModels.StickyPriceEvidence.rss
#print axioms ObstfeldRogoff.StickyPriceModels.StickyPriceEvidence.sampleMean
#print axioms ObstfeldRogoff.StickyPriceModels.StickyPriceEvidence.sxy
#print axioms ObstfeldRogoff.StickyPriceModels.StickyPriceEvidence.olsSlope
#print axioms ObstfeldRogoff.StickyPriceModels.StickyPriceEvidence.olsIntercept
#print axioms ObstfeldRogoff.StickyPriceModels.StickyPriceEvidence.rSquared
#print axioms ObstfeldRogoff.StickyPriceModels.StickyPriceEvidence.slopeSE
#print axioms ObstfeldRogoff.StickyPriceModels.StickyPriceEvidence.slopeT
#print axioms ObstfeldRogoff.StickyPriceModels.StickyPriceEvidence.rss_expand
#print axioms ObstfeldRogoff.StickyPriceModels.StickyPriceEvidence.sxy_eq_centred
#print axioms ObstfeldRogoff.StickyPriceModels.StickyPriceEvidence.sxx_nonneg
#print axioms ObstfeldRogoff.StickyPriceModels.StickyPriceEvidence.rss_decomposition
#print axioms ObstfeldRogoff.StickyPriceModels.StickyPriceEvidence.ols_minimises_iff
#print axioms ObstfeldRogoff.StickyPriceModels.StickyPriceEvidence.rss_at_ols
#print axioms ObstfeldRogoff.StickyPriceModels.StickyPriceEvidence.rSquared_eq_one_sub
#print axioms ObstfeldRogoff.StickyPriceModels.StickyPriceEvidence.rSquared_mem_Icc
#print axioms ObstfeldRogoff.StickyPriceModels.StickyPriceEvidence.slopeT_sq
#print axioms ObstfeldRogoff.StickyPriceModels.StickyPriceEvidence.rSquared_of_slopeT
#print axioms ObstfeldRogoff.StickyPriceModels.StickyPriceEvidence.wealth_slope_tratio
#print axioms ObstfeldRogoff.StickyPriceModels.StickyPriceEvidence.wealth_intercept_tratio
#print axioms ObstfeldRogoff.StickyPriceModels.StickyPriceEvidence.wealth_significance
#print axioms ObstfeldRogoff.StickyPriceModels.StickyPriceEvidence.standard_critical_values_in_range
#print axioms ObstfeldRogoff.StickyPriceModels.StickyPriceEvidence.wealth_unit_slope_not_rejected
#print axioms ObstfeldRogoff.StickyPriceModels.StickyPriceEvidence.wealth_implied_rSquared
#print axioms ObstfeldRogoff.StickyPriceModels.StickyPriceEvidence.wealth_implied_rSquared_robust
#print axioms ObstfeldRogoff.StickyPriceModels.StickyPriceEvidence.caResponse
#print axioms ObstfeldRogoff.StickyPriceModels.StickyPriceEvidence.caIncrement
#print axioms ObstfeldRogoff.StickyPriceModels.StickyPriceEvidence.caResponse_year_one_neg
#print axioms ObstfeldRogoff.StickyPriceModels.StickyPriceEvidence.caResponse_later_pos
#print axioms ObstfeldRogoff.StickyPriceModels.StickyPriceEvidence.caResponse_strictMono
#print axioms ObstfeldRogoff.StickyPriceModels.StickyPriceEvidence.caIncrement_strictAnti
#print axioms ObstfeldRogoff.StickyPriceModels.StickyPriceEvidence.caResponse_unique_sign_change
#print axioms ObstfeldRogoff.StickyPriceModels.StickyPriceEvidence.caResponse_modest
#print axioms ObstfeldRogoff.StickyPriceModels.StickyPriceEvidence.caResponse_cumulative
#print axioms ObstfeldRogoff.StickyPriceModels.StickyPriceEvidence.wMean
#print axioms ObstfeldRogoff.StickyPriceModels.StickyPriceEvidence.cMoment
#print axioms ObstfeldRogoff.StickyPriceModels.StickyPriceEvidence.kurtosis
#print axioms ObstfeldRogoff.StickyPriceModels.StickyPriceEvidence.wMean_affine
#print axioms ObstfeldRogoff.StickyPriceModels.StickyPriceEvidence.cMoment_affine
#print axioms ObstfeldRogoff.StickyPriceModels.StickyPriceEvidence.kurtosis_affine
#print axioms ObstfeldRogoff.StickyPriceModels.StickyPriceEvidence.kurtosis_neg
#print axioms ObstfeldRogoff.StickyPriceModels.StickyPriceEvidence.cMoment_one
#print axioms ObstfeldRogoff.StickyPriceModels.StickyPriceEvidence.pearson_inequality
#print axioms ObstfeldRogoff.StickyPriceModels.StickyPriceEvidence.excess_kurtosis_ge
#print axioms ObstfeldRogoff.StickyPriceModels.StickyPriceEvidence.kashyap_kurtosis_comparison
#print axioms ObstfeldRogoff.StickyPriceModels.StickyPriceEvidence.blinder_majority
#print axioms ObstfeldRogoff.StickyPriceModels.StickyPriceEvidence.kashyap_annual_frequency
