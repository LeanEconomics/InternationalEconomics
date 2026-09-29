/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StickyPriceModels.Model
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Algebra.BigOperators.Field

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
