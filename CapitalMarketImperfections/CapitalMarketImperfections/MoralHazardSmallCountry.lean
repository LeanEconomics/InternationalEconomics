/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Darboux
import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Convex.Basic
import Mathlib.Analysis.Convex.Function
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.LinearCombination

/-!
# Moral hazard in international lending: the small-country model

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §6.4.1
(pp. 407–413), §6.4.3 (p. 416) and end-of-chapter Exercises 4 and 5 (p. 427).

Entrepreneurs with linear utility `U = C₂` and date-1 endowment `Y₁` invest `I` in a family
firm that yields `Z` with probability `π(I)` and `0` otherwise, and may covertly lend `L ≥ 0`
abroad at the gross world rate `R = 1 + r`; the finance constraint is (45) `I + L = Y₁ + D`.
Lenders observe `Y₁`, `D` and `Y₂` but not `I` or `L`; contracts are `(P(Z), P(0), D)`.

We assume (O&R p. 408) `π(0) = 0`, `π' > 0`, `π` strictly concave (as a strictly decreasing
continuous derivative), `π'(0)Z > R`, and — never stated in the book but forced since `π` is a
probability — `π ≤ 1`. From these we *derive* the existence and uniqueness of the efficient
investment `Ī` of (44).

* **The borrower's problem (46)–(47).** Given a contract the borrower's choice is unique and
  equals `min(Y₁ + D, I*)` where `π'(I*)[Z − (P(Z) − P(0))] = R` (or `0`). The book's (47) is an
  equality only for an interior choice; we prove the correct statement, including the corner.
  The first-best contract induces `I < Ī` and gives lenders less than `R`.
* **The optimal incentive-compatible contract (Fig. 6.11, (49), fns 65–66).** With limited
  liability `P(0) ≤ E` (`E = 0` in the text, `E = E₂` in Exercise 4) we prove, with no
  interiority assumption: the IC curve is strictly decreasing and vanishes at `Ī`; the ZP curve is
  strictly increasing (fn 66); they cross exactly once, at `I ∈ (Y₁, Ī)`; no contract of any kind
  (any `P(Z)`, any `P(0) ≤ E`, any `D`) satisfying lenders' participation induces more
  investment or gives the borrower more; the optimum is *unique*, has `P(0) = E`, and `L = 0`
  (the conclusion of fn 65, here derived). The Kuhn–Tucker route of fn 65 is also formalised:
  every Kuhn–Tucker point has `λ > 0` and hence `L = 0`, the linear-independence constraint
  qualification holds at the optimum, and the multipliers there exist, are unique and positive.
* **Comparative statics (p. 412).** Investment rises with `Y₁` and `Z` and falls with `r`;
  borrowing rises with `Z`; `π'(I)Z > R`; output is below full information. The claim that a
  rise in `Y₁` raises investment by *less* than `Y₁` (so capital inflows fall) is **false in
  general**: we give the exact condition and an explicit counterexample.
* **§6.4.3.** The first-best insurance contract equalises consumption and is the full-information
  optimum; under any full-insurance contract the entrepreneur invests nothing.
* **Exercise 4.** Collateral `E₂` acts exactly like extra wealth `E₂/R` and raises investment
  (and restores the first best if large enough); a government debt `D^G` serviced by taxing
  successful firms acts like a wealth loss `D^G/R` and lowers investment (debt overhang).
* **Exercise 5.** No tax–transfer scheme between savers and entrepreneurs is a Pareto
  improvement: the equilibrium is constrained efficient.
-/

namespace ObstfeldRogoff.CapitalMarketImperfections.MoralHazardSmallCountry

open Set

/-- The success-probability technology of §6.4.1, O&R p. 408: `prob = π` with derivative
`dprob = π'` on `[0, ∞)`; `π(0) = 0`, `π' > 0` and strictly decreasing (strict concavity), and
`π ≤ 1` (implicit in the book: `π` is a probability). Continuity of `π'` is not assumed: it is
derived from Darboux's theorem (`SuccessProb.dprob_continuousOn`). -/
structure SuccessProb where
  prob : ℝ → ℝ
  dprob : ℝ → ℝ
  hasDerivAt : ∀ I, 0 ≤ I → HasDerivAt prob (dprob I) I
  dprob_pos : ∀ I, 0 ≤ I → 0 < dprob I
  dprob_strictAnti : StrictAntiOn dprob (Ici 0)
  prob_zero : prob 0 = 0
  prob_le_one : ∀ I, 0 ≤ I → prob I ≤ 1

namespace SuccessProb

variable (T : SuccessProb)

/-- `π` is continuous on `[0, ∞)`. -/
theorem continuousOn_prob : ContinuousOn T.prob (Ici 0) := fun I hI =>
  (T.hasDerivAt I hI).continuousAt.continuousWithinAt

/-- `π'` is antitone on `[0, ∞)` (weak form of strict concavity). -/
theorem dprob_le_of_le {I J : ℝ} (hI : 0 ≤ I) (hIJ : I ≤ J) : T.dprob J ≤ T.dprob I :=
  T.dprob_strictAnti.antitoneOn hI (le_trans hI hIJ : (0 : ℝ) ≤ J) hIJ

/-- **`π'` is continuous on `[0, ∞)`**, derived rather than assumed: a derivative has the
intermediate value property (Darboux's theorem), and a monotone function with that property has
no jumps. -/
theorem dprob_continuousOn : ContinuousOn T.dprob (Ici 0) := by
  intro x hx
  have hx0 : (0 : ℝ) ≤ x := hx
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  have darb : ∀ a b m : ℝ, 0 ≤ a → a ≤ b → T.dprob b < m → m < T.dprob a →
      ∃ c ∈ Ioo a b, T.dprob c = m := by
    intro a b m ha hab h1 h2
    obtain ⟨c, hc, hcm⟩ := exists_hasDerivWithinAt_eq_of_lt_of_gt hab
      (fun y hy => (T.hasDerivAt y (le_trans ha hy.1)).hasDerivWithinAt) h2 h1
    exact ⟨c, hc, hcm⟩
  obtain ⟨δ1, hδ1, h1⟩ : ∃ δ > 0, ∀ y, x ≤ y → y < x + δ → T.dprob x - ε < T.dprob y := by
    by_cases hc : T.dprob x - ε < T.dprob (x + 1)
    · refine ⟨1, one_pos, fun y hxy hy => ?_⟩
      have := T.dprob_le_of_le (le_trans hx0 hxy) hy.le
      linarith
    · push Not at hc
      obtain ⟨c, hc1, hcv⟩ := darb x (x + 1) (T.dprob x - ε / 2) hx0 (by linarith)
        (by linarith) (by linarith)
      refine ⟨c - x, by linarith [hc1.1], fun y hxy hy => ?_⟩
      have := T.dprob_le_of_le (le_trans hx0 hxy) (by linarith : y ≤ c)
      linarith
  obtain ⟨δ2, hδ2, h2⟩ : ∃ δ > 0, ∀ y, 0 ≤ y → y ≤ x → x - δ < y →
      T.dprob y < T.dprob x + ε := by
    rcases hx0.lt_or_eq with hxp | hxe
    · by_cases hc : T.dprob (x / 2) < T.dprob x + ε
      · refine ⟨x / 2, by linarith, fun y hy hyx hy2 => ?_⟩
        have := T.dprob_le_of_le (by linarith : (0 : ℝ) ≤ x / 2) (by linarith : x / 2 ≤ y)
        linarith
      · push Not at hc
        obtain ⟨c, hc1, hcv⟩ := darb (x / 2) x (T.dprob x + ε / 2) (by linarith) (by linarith)
          (by linarith) (by linarith)
        refine ⟨x - c, by linarith [hc1.2], fun y hy hyx hy2 => ?_⟩
        have := T.dprob_le_of_le (by linarith [hc1.1] : (0 : ℝ) ≤ c) (by linarith : c ≤ y)
        linarith
    · refine ⟨1, one_pos, fun y hy hyx _ => ?_⟩
      have : y = x := le_antisymm hyx (hxe ▸ hy)
      rw [this]; linarith
  refine ⟨min δ1 δ2, lt_min hδ1 hδ2, fun y hy hdist => ?_⟩
  have hy0 : (0 : ℝ) ≤ y := hy
  rw [Real.dist_eq, abs_lt] at hdist ⊢
  rcases le_total x y with hxy | hyx
  · have a := h1 y hxy (by linarith [min_le_left δ1 δ2])
    have b := T.dprob_le_of_le hx0 hxy
    constructor <;> linarith
  · have a := h2 y hy0 hyx (by linarith [min_le_right δ1 δ2])
    have b := T.dprob_le_of_le hy0 hyx
    constructor <;> linarith

/-- Strict supporting-line inequality `π(J) < π(I) + π'(I)(J − I)` for `J ≠ I` in `[0, ∞)`:
the strict concavity of `π`, O&R p. 408 (proved from the mean value theorem). -/
theorem tangent_lt {I J : ℝ} (hI : 0 ≤ I) (hJ : 0 ≤ J) (hne : J ≠ I) :
    T.prob J < T.prob I + T.dprob I * (J - I) := by
  rcases lt_or_gt_of_ne hne with h | h
  · obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope T.prob T.dprob h
      (fun x hx => (T.hasDerivAt x (le_trans hJ hx.1)).continuousAt.continuousWithinAt)
      (fun x hx => T.hasDerivAt x (le_trans hJ hx.1.le))
    have hlt : T.dprob I < T.dprob c :=
      T.dprob_strictAnti (le_trans hJ hc.1.le : (0 : ℝ) ≤ c) hI hc.2
    have hIJ : 0 < I - J := by linarith
    rw [eq_div_iff hIJ.ne'] at hcd
    nlinarith
  · obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope T.prob T.dprob h
      (fun x hx => (T.hasDerivAt x (le_trans hI hx.1)).continuousAt.continuousWithinAt)
      (fun x hx => T.hasDerivAt x (le_trans hI hx.1.le))
    have hlt : T.dprob c < T.dprob I :=
      T.dprob_strictAnti hI (le_trans hI hc.1.le : (0 : ℝ) ≤ c) hc.1
    have hJI : 0 < J - I := by linarith
    rw [eq_div_iff hJI.ne'] at hcd
    nlinarith

/-- Weak supporting-line inequality `π(J) ≤ π(I) + π'(I)(J − I)` on `[0, ∞)`. -/
theorem tangent_le {I J : ℝ} (hI : 0 ≤ I) (hJ : 0 ≤ J) :
    T.prob J ≤ T.prob I + T.dprob I * (J - I) := by
  rcases eq_or_ne J I with h | h
  · rw [h]; simp
  · exact (T.tangent_lt hI hJ h).le

/-- `π` is strictly increasing on `[0, ∞)`, O&R p. 408. -/
theorem prob_strictMonoOn : StrictMonoOn T.prob (Ici 0) := by
  intro I hI J hJ hIJ
  have := T.tangent_lt (mem_Ici.1 hJ) (mem_Ici.1 hI) hIJ.ne
  have := T.dprob_pos J hJ
  nlinarith

/-- `π(I) > 0` for `I > 0`. -/
theorem prob_pos {I : ℝ} (hI : 0 < I) : 0 < T.prob I := by
  have := T.prob_strictMonoOn (mem_Ici.2 le_rfl) (mem_Ici.2 hI.le) hI
  rwa [T.prob_zero] at this

/-- `π ≥ 0` on `[0, ∞)`. -/
theorem prob_nonneg {I : ℝ} (hI : 0 ≤ I) : 0 ≤ T.prob I := by
  rcases hI.lt_or_eq with h | h
  · exact (T.prob_pos h).le
  · rw [← h, T.prob_zero]

/-- `π(I) < 1` on `[0, ∞)`: success is never certain. -/
theorem prob_lt_one {I : ℝ} (hI : 0 ≤ I) : T.prob I < 1 :=
  lt_of_lt_of_le (T.prob_strictMonoOn (mem_Ici.2 hI) (mem_Ici.2 (by linarith)) (lt_add_one I))
    (T.prob_le_one (I + 1) (by linarith))

/-- The average product exceeds the marginal product: `I π'(I) < π(I)` for `I > 0`
(O&R fn 66, "since `π` is strictly concave with `π(0) = 0`"). -/
theorem mul_dprob_lt_prob {I : ℝ} (hI : 0 < I) : I * T.dprob I < T.prob I := by
  have := T.tangent_lt hI.le le_rfl (ne_of_lt hI)
  rw [T.prob_zero] at this
  linarith

/-- The average product is strictly decreasing: `J π(I) > I π(J)` for `0 < I < J`. -/
theorem avg_prob_strictAnti {I J : ℝ} (hI : 0 < I) (hIJ : I < J) :
    I * T.prob J < J * T.prob I := by
  have h1 := T.tangent_lt hI.le (by linarith : (0 : ℝ) ≤ J) (ne_of_gt hIJ)
  have h2 := T.mul_dprob_lt_prob hI
  nlinarith

/-- `π'(I) ≤ 1/I`: the marginal product vanishes at infinity (from `π ≤ 1`). -/
theorem dprob_lt_inv {I : ℝ} (hI : 0 < I) : T.dprob I < 1 / I := by
  rw [lt_div_iff₀ hI]
  have := T.mul_dprob_lt_prob hI
  have := T.prob_le_one I hI.le
  linarith

/-- Every level `c ∈ (0, π'(0))` is attained by `π'` at exactly one point, which is positive
(intermediate value theorem plus strict monotonicity). -/
theorem exists_unique_dprob_eq {c : ℝ} (hc : 0 < c) (hc0 : c < T.dprob 0) :
    ∃! I, 0 < I ∧ T.dprob I = c := by
  have hb : 0 < 1 / c := by positivity
  have hlow : T.dprob (1 / c) < c := by
    have := T.dprob_lt_inv hb
    rwa [one_div_one_div] at this
  obtain ⟨I, hI, hIc⟩ := intermediate_value_Icc' hb.le
    (T.dprob_continuousOn.mono (fun x hx => mem_Ici.2 hx.1)) ⟨hlow.le, hc0.le⟩
  have hI0 : 0 < I := by
    rcases hI.1.lt_or_eq with h | h
    · exact h
    · rw [← h] at hIc; linarith
  refine ⟨I, ⟨hI0, hIc⟩, ?_⟩
  rintro J ⟨hJ, hJc⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have := T.dprob_strictAnti (mem_Ici.2 hJ.le) (mem_Ici.2 hI0.le) h
    linarith
  · have := T.dprob_strictAnti (mem_Ici.2 hI0.le) (mem_Ici.2 hJ.le) h
    linarith

/-- Strict midpoint concavity: `π(a) + π(b) < 2π((a+b)/2)` for `a ≠ b` in `[0, ∞)`. -/
theorem prob_midpoint_lt {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a ≠ b) :
    T.prob a + T.prob b < 2 * T.prob ((a + b) / 2) := by
  have hm : 0 ≤ (a + b) / 2 := by positivity
  have h1 := T.tangent_lt hm ha (by intro h; apply hab; linarith)
  have h2 := T.tangent_lt hm hb (by intro h; apply hab; linarith)
  nlinarith

end SuccessProb

/-! ## Efficient investment (44) -/

/-- Expected net output `π(I)Z − R(I − Y₁)`: date-2 value of expected profit
`−I + π(I)Z/(1+r)` plus the endowment, O&R p. 408. -/
noncomputable def netOutput (T : SuccessProb) (Z R Y₁ I : ℝ) : ℝ := T.prob I * Z - R * (I - Y₁)

/-- `Z > 0` follows from `π'(0)Z > R > 0`, O&R p. 408. -/
theorem Z_pos {T : SuccessProb} {Z R : ℝ} (hR : 0 < R) (hZ : R < T.dprob 0 * Z) : 0 < Z := by
  have := T.dprob_pos 0 le_rfl
  by_contra h
  push Not at h
  nlinarith

/-- **Existence and uniqueness of the efficient investment level `Ī`**, (44), O&R p. 408:
`π'(Ī)Z = R` has exactly one solution, which is positive. -/
theorem efficient_investment_exists_unique {T : SuccessProb} {Z R : ℝ} (hR : 0 < R)
    (hZ : R < T.dprob 0 * Z) : ∃! Ibar, 0 < Ibar ∧ T.dprob Ibar * Z = R := by
  have hZ0 := Z_pos hR hZ
  obtain ⟨I, ⟨hI, hIc⟩, huniq⟩ := T.exists_unique_dprob_eq (c := R / Z) (by positivity)
    (by rw [div_lt_iff₀ hZ0]; linarith)
  refine ⟨I, ⟨hI, by rw [hIc]; field_simp⟩, ?_⟩
  rintro J ⟨hJ, hJc⟩
  exact huniq J ⟨hJ, by rw [eq_div_iff hZ0.ne']; exact hJc⟩

/-- Net output is strictly increasing on `[0, Ī]`, O&R p. 408. -/
theorem netOutput_strictMonoOn {T : SuccessProb} {Z R Y₁ Ibar : ℝ} (hZ : 0 < Z)
    (hIbar : T.dprob Ibar * Z = R) {I J : ℝ} (hI : 0 ≤ I) (hIJ : I < J) (hJ : J ≤ Ibar) :
    netOutput T Z R Y₁ I < netOutput T Z R Y₁ J := by
  have ht := T.tangent_lt (by linarith : (0 : ℝ) ≤ J) hI (ne_of_lt hIJ)
  have hd : T.dprob Ibar ≤ T.dprob J := T.dprob_le_of_le (by linarith) hJ
  have h1 : Z * (T.dprob J * (J - I)) < Z * (T.prob J - T.prob I) :=
    mul_lt_mul_of_pos_left (by linarith) hZ
  have h2 : T.dprob Ibar * (J - I) ≤ T.dprob J * (J - I) :=
    mul_le_mul_of_nonneg_right hd (by linarith)
  unfold netOutput
  nlinarith

/-- `Ī` uniquely maximises expected net output over `I ≥ 0`, O&R (44), p. 408. -/
theorem efficient_investment_maximises {T : SuccessProb} {Z R Y₁ Ibar : ℝ} (hZ : 0 < Z)
    (hIbar0 : 0 ≤ Ibar) (hIbar : T.dprob Ibar * Z = R) {I : ℝ} (hI : 0 ≤ I) (hne : I ≠ Ibar) :
    netOutput T Z R Y₁ I < netOutput T Z R Y₁ Ibar := by
  have ht := T.tangent_lt hIbar0 hI hne
  unfold netOutput
  nlinarith

/-! ## The borrower's problem (46)–(47) -/

/-- A loan contract `(P(Z), P(0), D)`: repayment on success, repayment on failure, gross
borrowing, O&R p. 409–410. -/
structure Contract where
  PZ : ℝ
  P0 : ℝ
  D : ℝ

/-- The borrower's stake in success, `Z − (P(Z) − P(0))`, O&R (47). -/
def stake (Z : ℝ) (c : Contract) : ℝ := Z - (c.PZ - c.P0)

/-- The borrower's expected date-2 consumption (46), O&R p. 410, when he invests `I` and lends
`L = Y₁ + D − I` abroad; `E ≥ 0` is observable (collateralisable) date-2 income (Exercise 4;
`E = 0` in the text). -/
noncomputable def borrowerPayoff (T : SuccessProb) (Z R Y₁ E : ℝ) (c : Contract) (I : ℝ) : ℝ :=
  T.prob I * (Z + E - c.PZ) + (1 - T.prob I) * (E - c.P0) + R * (Y₁ + c.D - I)

/-- (46) rewritten: `EC₂ = π(I)·stake + (E − P(0)) + R(Y₁ + D − I)`. -/
theorem borrowerPayoff_eq (T : SuccessProb) (Z R Y₁ E : ℝ) (c : Contract) (I : ℝ) :
    borrowerPayoff T Z R Y₁ E c I =
      T.prob I * stake Z c + (E - c.P0) + R * (Y₁ + c.D - I) := by
  unfold borrowerPayoff stake; ring

/-- The borrower's optimal choice: `I ∈ [0, Y₁ + D]` (so `L ≥ 0`, (45)) maximising (46). -/
def IsBestResponse (T : SuccessProb) (Z R Y₁ E : ℝ) (c : Contract) (I : ℝ) : Prop :=
  0 ≤ I ∧ I ≤ Y₁ + c.D ∧
    ∀ J, 0 ≤ J → J ≤ Y₁ + c.D → borrowerPayoff T Z R Y₁ E c J ≤ borrowerPayoff T Z R Y₁ E c I

/-- The payoff difference between two investment levels. -/
theorem borrowerPayoff_sub (T : SuccessProb) (Z R Y₁ E : ℝ) (c : Contract) (I J : ℝ) :
    borrowerPayoff T Z R Y₁ E c J - borrowerPayoff T Z R Y₁ E c I =
      stake Z c * (T.prob J - T.prob I) - R * (J - I) := by
  rw [borrowerPayoff_eq, borrowerPayoff_eq]; ring

/-- **The borrower's choice, interior or corner** (correcting (47), O&R p. 410): if the stake
is positive and `π'(I*)·stake = R`, the unique optimal investment is `min(Y₁ + D, I*)`. -/
theorem bestResponse_of_foc {T : SuccessProb} {Z R Y₁ E : ℝ} {c : Contract} (hs : 0 < stake Z c)
    (hW : 0 ≤ Y₁ + c.D) {Istar : ℝ} (hI0 : 0 ≤ Istar) (hfoc : T.dprob Istar * stake Z c = R) :
    IsBestResponse T Z R Y₁ E c (min (Y₁ + c.D) Istar) ∧
      ∀ J, IsBestResponse T Z R Y₁ E c J → J = min (Y₁ + c.D) Istar := by
  set W := Y₁ + c.D
  set I₀ := min W Istar
  have hI₀ : 0 ≤ I₀ := le_min hW hI0
  have hI₀W : I₀ ≤ W := min_le_left _ _
  have hcoef : 0 ≤ T.dprob I₀ * stake Z c - R := by
    have := T.dprob_le_of_le hI₀ (min_le_right W Istar)
    nlinarith
  have strict : ∀ J, 0 ≤ J → J ≤ W → J ≠ I₀ →
      borrowerPayoff T Z R Y₁ E c J < borrowerPayoff T Z R Y₁ E c I₀ := by
    intro J hJ hJW hne
    have hd := borrowerPayoff_sub T Z R Y₁ E c I₀ J
    have ht := T.tangent_lt hI₀ hJ hne
    have key : (T.dprob I₀ * stake Z c - R) * (J - I₀) ≤ 0 := by
      rcases le_or_gt J I₀ with h | h
      · exact mul_nonpos_of_nonneg_of_nonpos hcoef (by linarith)
      · have hIs : I₀ = Istar := by
          have : I₀ < W := lt_of_lt_of_le h hJW
          rcases min_choice W Istar with h' | h'
          · exact absurd h' (ne_of_lt this)
          · exact h'
        have : T.dprob I₀ * stake Z c - R = 0 := by rw [hIs, hfoc]; ring
        rw [this]; simp
    nlinarith
  refine ⟨⟨hI₀, hI₀W, ?_⟩, ?_⟩
  · intro J hJ hJW
    rcases eq_or_ne J I₀ with h | h
    · rw [h]
    · exact (strict J hJ hJW h).le
  · rintro J ⟨hJ, hJW, hbest⟩
    by_contra hne
    have := strict J hJ hJW hne
    have := hbest I₀ hI₀ hI₀W
    linarith

/-- **The borrower's choice when investment is unattractive**: if `π'(0)·stake ≤ R` (in
particular if the stake is nonpositive) the unique optimal investment is `0`. -/
theorem bestResponse_zero {T : SuccessProb} {Z R Y₁ E : ℝ} {c : Contract} (hR : 0 < R)
    (hW : 0 ≤ Y₁ + c.D) (hs : T.dprob 0 * stake Z c ≤ R) :
    IsBestResponse T Z R Y₁ E c 0 ∧ ∀ J, IsBestResponse T Z R Y₁ E c J → J = 0 := by
  have strict : ∀ J, 0 < J →
      borrowerPayoff T Z R Y₁ E c J < borrowerPayoff T Z R Y₁ E c 0 := by
    intro J hJ
    have hd := borrowerPayoff_sub T Z R Y₁ E c 0 J
    rw [T.prob_zero] at hd
    have ht := T.tangent_lt le_rfl hJ.le (ne_of_gt hJ)
    rw [T.prob_zero] at ht
    have hp := T.prob_pos hJ
    rcases le_or_gt (stake Z c) 0 with h | h
    · nlinarith
    · nlinarith
  refine ⟨⟨le_rfl, hW, ?_⟩, ?_⟩
  · intro J hJ _
    rcases hJ.lt_or_eq with h | h
    · exact (strict J h).le
    · rw [← h]
  · rintro J ⟨hJ, _, hbest⟩
    by_contra hne
    have := strict J (lt_of_le_of_ne hJ (Ne.symm hne))
    have := hbest 0 le_rfl hW
    linarith

/-- If investing is attractive at the margin, `π'(0)·stake > R`, the unconstrained optimum `I*`
with `π'(I*)·stake = R` exists and is unique and positive. -/
theorem exists_unique_Istar {T : SuccessProb} {Z R : ℝ} {c : Contract} (hR : 0 < R)
    (hs : R < T.dprob 0 * stake Z c) : ∃! Istar, 0 < Istar ∧ T.dprob Istar * stake Z c = R := by
  have hs0 : 0 < stake Z c := by
    have := T.dprob_pos 0 le_rfl
    by_contra h; push Not at h; nlinarith
  obtain ⟨I, ⟨hI, hIc⟩, huniq⟩ := T.exists_unique_dprob_eq (c := R / stake Z c)
    (by positivity) (by rw [div_lt_iff₀ hs0]; linarith)
  refine ⟨I, ⟨hI, by rw [hIc]; field_simp⟩, ?_⟩
  rintro J ⟨hJ, hJc⟩
  exact huniq J ⟨hJ, by rw [eq_div_iff hs0.ne']; exact hJc⟩

/-- The borrower's problem always has exactly one solution (for `R > 0`, `Y₁ + D ≥ 0`),
O&R p. 410. -/
theorem bestResponse_exists_unique (T : SuccessProb) {Z R Y₁ E : ℝ} (c : Contract) (hR : 0 < R)
    (hW : 0 ≤ Y₁ + c.D) : ∃! I, IsBestResponse T Z R Y₁ E c I := by
  rcases le_or_gt (T.dprob 0 * stake Z c) R with h | h
  · obtain ⟨hb, hu⟩ := bestResponse_zero (E := E) hR hW h
    exact ⟨0, hb, hu⟩
  · obtain ⟨Istar, ⟨hI, hfoc⟩, _⟩ := exists_unique_Istar hR h
    have hs0 : 0 < stake Z c := by
      have := T.dprob_pos 0 le_rfl
      by_contra h'; push Not at h'; nlinarith
    obtain ⟨hb, hu⟩ := bestResponse_of_foc (E := E) hs0 hW hI.le hfoc
    exact ⟨_, hb, hu⟩

/-- Necessary condition for a positive optimal investment: `π'(I)·stake ≥ R`. -/
theorem bestResponse_foc_ge {T : SuccessProb} {Z R Y₁ E : ℝ} {c : Contract} (hR : 0 < R)
    {I : ℝ} (hbest : IsBestResponse T Z R Y₁ E c I) (hI : 0 < I) :
    R ≤ T.dprob I * stake Z c := by
  have hW : 0 ≤ Y₁ + c.D := le_trans hbest.1 hbest.2.1
  rcases le_or_gt (T.dprob 0 * stake Z c) R with h | h
  · have := (bestResponse_zero (E := E) hR hW h).2 I hbest
    linarith
  · obtain ⟨Istar, ⟨hIs, hfoc⟩, _⟩ := exists_unique_Istar hR h
    have hs0 : 0 < stake Z c := by
      have := T.dprob_pos 0 le_rfl
      by_contra h'; push Not at h'; nlinarith
    have heq := (bestResponse_of_foc (E := E) hs0 hW hIs.le hfoc).2 I hbest
    have hle : I ≤ Istar := by rw [heq]; exact min_le_right _ _
    have := T.dprob_le_of_le hbest.1 hle
    nlinarith

/-- **(47) with its correct domain**, O&R p. 410: an interior optimal investment
(`0 < I < Y₁ + D`, i.e. `L > 0`) satisfies `π'(I)[Z − (P(Z) − P(0))] = R`. -/
theorem bestResponse_foc_interior {T : SuccessProb} {Z R Y₁ E : ℝ} {c : Contract} (hR : 0 < R)
    {I : ℝ} (hbest : IsBestResponse T Z R Y₁ E c I) (hI : 0 < I) (hIW : I < Y₁ + c.D) :
    T.dprob I * stake Z c = R := by
  have hW : 0 ≤ Y₁ + c.D := le_trans hbest.1 hbest.2.1
  rcases le_or_gt (T.dprob 0 * stake Z c) R with h | h
  · have := (bestResponse_zero (E := E) hR hW h).2 I hbest
    linarith
  · obtain ⟨Istar, ⟨hIs, hfoc⟩, _⟩ := exists_unique_Istar hR h
    have hs0 : 0 < stake Z c := by
      have := T.dprob_pos 0 le_rfl
      by_contra h'; push Not at h'; nlinarith
    have heq := (bestResponse_of_foc (E := E) hs0 hW hIs.le hfoc).2 I hbest
    have : I = Istar := by
      rcases min_choice (Y₁ + c.D) Istar with h' | h'
      · rw [h'] at heq; linarith
      · rw [h'] at heq; exact heq
    rw [this, hfoc]

/-- The first-best contract `P(Z) = R(Ī − Y₁)/π(Ī)`, `P(0) = 0`, `D = Ī − Y₁`, O&R p. 409. -/
noncomputable def firstBestContract (T : SuccessProb) (R Y₁ Ibar : ℝ) : Contract :=
  ⟨R * (Ibar - Y₁) / T.prob Ibar, 0, Ibar - Y₁⟩

/-- **The first-best contract is not incentive compatible** (O&R p. 410): offered it, the
borrower invests strictly less than `Ī`, and lenders earn an expected return strictly below
`R` on their loan. -/
theorem firstBest_contract_underinvests {T : SuccessProb} {Z R Y₁ Ibar : ℝ} (hR : 0 < R)
    (hY : 0 ≤ Y₁) (hYI : Y₁ < Ibar) (hIbar : T.dprob Ibar * Z = R) {I : ℝ}
    (hbest : IsBestResponse T Z R Y₁ 0 (firstBestContract T R Y₁ Ibar) I) :
    I < Ibar ∧
      T.prob I * (firstBestContract T R Y₁ Ibar).PZ < R * (firstBestContract T R Y₁ Ibar).D := by
  have hIb : 0 < Ibar := by linarith
  have hpI := T.prob_pos hIb
  have hPZ : 0 < (firstBestContract T R Y₁ Ibar).PZ := by
    unfold firstBestContract; simp only
    have : 0 < Ibar - Y₁ := by linarith
    positivity
  have hlt : I < Ibar := by
    rcases hbest.1.lt_or_eq with h | h
    · have hfoc := bestResponse_foc_ge hR hbest h
      have hstake : stake Z (firstBestContract T R Y₁ Ibar) < Z := by
        unfold stake firstBestContract at *; simp only at *; linarith
      have hd := T.dprob_pos I hbest.1
      have hZ : 0 < Z := by
        have := T.dprob_pos Ibar hIb.le
        by_contra h'; push Not at h'; nlinarith
      by_contra hge
      push Not at hge
      have := T.dprob_le_of_le hIb.le hge
      have h1 := mul_lt_mul_of_pos_left hstake hd
      have h2 := mul_le_mul_of_nonneg_right this hZ.le
      linarith
    · rw [← h]; exact hIb
  refine ⟨hlt, ?_⟩
  have hmono := T.prob_strictMonoOn (mem_Ici.2 hbest.1) (mem_Ici.2 hIb.le) hlt
  have hval : T.prob Ibar * (firstBestContract T R Y₁ Ibar).PZ =
      R * (firstBestContract T R Y₁ Ibar).D := by
    unfold firstBestContract; simp only; field_simp
  nlinarith


/-! ## The IC and ZP curves of Fig. 6.11 -/

/-- The incentive-compatibility curve `IC`: `P(Z) = Z − R/π'(I)`, O&R p. 410 (with `P(0) = 0`).
-/
noncomputable def icCurve (T : SuccessProb) (Z R I : ℝ) : ℝ := Z - R / T.dprob I

/-- The zero-profit curve `ZP` (49): `P(Z) = R(I − w)/π(I)`, O&R p. 412, where `w` is the
entrepreneur's effective wealth (`w = Y₁` in the text; `w = Y₁ + E₂/R` in Exercise 4). -/
noncomputable def zpCurve (T : SuccessProb) (R w I : ℝ) : ℝ := R * (I - w) / T.prob I

/-- `IC − ZP`; the small-country equilibrium is its zero, O&R Fig. 6.11. -/
noncomputable def eqmGap (T : SuccessProb) (Z R w I : ℝ) : ℝ := icCurve T Z R I - zpCurve T R w I

/-- `IC` is strictly decreasing, O&R p. 410. -/
theorem icCurve_strictAntiOn (T : SuccessProb) (Z : ℝ) {R : ℝ} (hR : 0 < R) :
    StrictAntiOn (icCurve T Z R) (Ici 0) := by
  intro I hI J hJ hIJ
  have h := T.dprob_strictAnti hI hJ hIJ
  have hJp := T.dprob_pos J hJ
  unfold icCurve
  have : R / T.dprob I < R / T.dprob J := div_lt_div_of_pos_left hR hJp h
  linarith

/-- `IC` meets the horizontal axis exactly at `Ī`: `P(Z) = 0 ↔ π'(I)Z = R`, O&R p. 410. -/
theorem icCurve_eq_zero_iff (T : SuccessProb) {Z R I : ℝ} (hI : 0 ≤ I) :
    icCurve T Z R I = 0 ↔ T.dprob I * Z = R := by
  have hd := (T.dprob_pos I hI).ne'
  unfold icCurve
  rw [sub_eq_zero, eq_div_iff hd]
  constructor <;> intro h <;> linarith

/-- `IC` is positive iff `I < Ī`, i.e. `π'(I)Z > R`. -/
theorem icCurve_pos_iff (T : SuccessProb) {Z R I : ℝ} (hI : 0 ≤ I) :
    0 < icCurve T Z R I ↔ R < T.dprob I * Z := by
  have hd := T.dprob_pos I hI
  unfold icCurve
  rw [sub_pos, div_lt_iff₀ hd]
  constructor <;> intro h <;> linarith

/-- `ZP` passes through `(w, 0)`, O&R p. 412. -/
theorem zpCurve_self (T : SuccessProb) (R w : ℝ) : zpCurve T R w w = 0 := by
  simp [zpCurve]

/-- **`ZP` is strictly increasing** for `w ≥ 0` (O&R fn 66), proved without derivatives from the
strictly decreasing average product. -/
theorem zpCurve_strictMonoOn (T : SuccessProb) {R w : ℝ} (hR : 0 < R) (hw : 0 ≤ w) :
    StrictMonoOn (zpCurve T R w) (Ioi 0) := by
  intro I hI J hJ hIJ
  have hI0 : 0 < I := hI
  have hpI := T.prob_pos hI0
  have hpJ := T.prob_pos (hI0.trans hIJ)
  have havg := T.avg_prob_strictAnti hI0 hIJ
  have hmono := T.prob_strictMonoOn (mem_Ici.2 hI0.le) (mem_Ici.2 (hI0.trans hIJ).le) hIJ
  have key : 0 < (J - w) * T.prob I - (I - w) * T.prob J := by
    nlinarith [mul_nonneg hw (le_of_lt (sub_pos.2 hmono))]
  unfold zpCurve
  rw [div_lt_div_iff₀ hpI hpJ]
  nlinarith [mul_pos hR key]

/-- The slope of `ZP` (O&R fn 66): `d/dI [R(I − w)/π(I)] = R[π(I) − (I − w)π'(I)]/π(I)²`. -/
theorem zpCurve_hasDerivAt (T : SuccessProb) (R w : ℝ) {I : ℝ} (hI : 0 < I) :
    HasDerivAt (zpCurve T R w)
      (R * (T.prob I - (I - w) * T.dprob I) / T.prob I ^ 2) I := by
  have hp := (T.prob_pos hI).ne'
  have h1 : HasDerivAt (fun x : ℝ => R * (x - w)) (R * 1) I :=
    ((hasDerivAt_id I).sub_const w).const_mul R
  have h2 := h1.div (T.hasDerivAt I hI.le) hp
  unfold zpCurve
  convert h2 using 1
  ring

/-- The slope of `ZP` is positive for `w ≥ 0`: `π(I) > I π'(I) ≥ (I − w)π'(I)`, O&R fn 66. -/
theorem zpCurve_slope_pos (T : SuccessProb) {R w I : ℝ} (hR : 0 < R) (hw : 0 ≤ w) (hI : 0 < I) :
    0 < R * (T.prob I - (I - w) * T.dprob I) / T.prob I ^ 2 := by
  have h1 := T.mul_dprob_lt_prob hI
  have h2 := T.dprob_pos I hI.le
  have hp := T.prob_pos hI
  have : 0 < T.prob I - (I - w) * T.dprob I := by nlinarith
  positivity

/-- The slope of `IC` (O&R p. 410): `d/dI [Z − R/π'(I)] = Rπ''(I)/π'(I)²`, nonpositive, when `π'`
has derivative `π''(I)` at `I`. -/
theorem icCurve_hasDerivAt (T : SuccessProb) (Z R : ℝ) {I d2 : ℝ} (hI : 0 ≤ I)
    (hd2 : HasDerivAt T.dprob d2 I) :
    HasDerivAt (icCurve T Z R) (R * d2 / T.dprob I ^ 2) I := by
  have hd := (T.dprob_pos I hI).ne'
  have h := ((hd2.inv hd).const_mul R).const_sub Z
  unfold icCurve
  convert h using 1
  · ext x; simp [div_eq_mul_inv]
  · field_simp

/-- `IC − ZP` is strictly decreasing on `(0, ∞)` for `w ≥ 0`. -/
theorem eqmGap_strictAntiOn (T : SuccessProb) (Z : ℝ) {R w : ℝ} (hR : 0 < R) (hw : 0 ≤ w) :
    StrictAntiOn (eqmGap T Z R w) (Ioi 0) := by
  intro I hI J hJ hIJ
  have h1 := icCurve_strictAntiOn T Z hR (mem_Ici.2 (le_of_lt hI)) (mem_Ici.2 (le_of_lt hJ)) hIJ
  have h2 := zpCurve_strictMonoOn T hR hw hI hJ hIJ
  unfold eqmGap
  linarith

/-- `IC − ZP` is continuous on `(0, ∞)`. -/
theorem eqmGap_continuousOn (T : SuccessProb) (Z R w : ℝ) :
    ContinuousOn (eqmGap T Z R w) (Ioi 0) := by
  have hd : ContinuousOn T.dprob (Ioi 0) := T.dprob_continuousOn.mono Ioi_subset_Ici_self
  have hp : ContinuousOn T.prob (Ioi 0) := T.continuousOn_prob.mono Ioi_subset_Ici_self
  unfold eqmGap icCurve zpCurve
  apply ContinuousOn.sub
  · exact continuousOn_const.sub (continuousOn_const.div hd
      (fun x hx => (T.dprob_pos x (le_of_lt hx)).ne'))
  · exact ((continuousOn_const.mul (continuousOn_id.sub continuousOn_const))).div hp
      (fun x hx => (T.prob_pos hx).ne')

/-- `IC − ZP` is strictly increasing in wealth `w` (ZP shifts right, O&R p. 412). -/
theorem eqmGap_lt_of_wealth_lt (T : SuccessProb) (Z : ℝ) {R w w' I : ℝ} (hR : 0 < R)
    (hww : w < w') (hI : 0 < I) : eqmGap T Z R w I < eqmGap T Z R w' I := by
  have hp := T.prob_pos hI
  unfold eqmGap zpCurve
  have : R * (I - w') / T.prob I < R * (I - w) / T.prob I :=
    div_lt_div_of_pos_right (by nlinarith) hp
  linarith

/-- **Existence and uniqueness of the small-country equilibrium** (Fig. 6.11): for wealth
`0 < w < Ī` (i.e. `π'(w)Z > R`) the curves `IC` and `ZP` cross at exactly one `I > 0`. -/
theorem equilibrium_exists_unique (T : SuccessProb) {Z R w : ℝ} (hR : 0 < R) (hw : 0 < w)
    (hwI : R < T.dprob w * Z) : ∃! I, 0 < I ∧ eqmGap T Z R w I = 0 := by
  have hd0 : T.dprob w ≤ T.dprob 0 := T.dprob_le_of_le le_rfl hw.le
  have hZ : 0 < Z := by
    have := T.dprob_pos w hw.le
    by_contra h; push Not at h; nlinarith
  obtain ⟨Ibar, ⟨hIb, hIbZ⟩, _⟩ := efficient_investment_exists_unique (T := T) hR
    (by nlinarith : R < T.dprob 0 * Z)
  have hwIb : w < Ibar := by
    by_contra h; push Not at h
    have := T.dprob_le_of_le hIb.le h
    nlinarith
  have hgw : 0 < eqmGap T Z R w w := by
    unfold eqmGap; rw [zpCurve_self, sub_zero]
    exact (icCurve_pos_iff T hw.le).2 hwI
  have hgI : eqmGap T Z R w Ibar < 0 := by
    unfold eqmGap
    rw [(icCurve_eq_zero_iff T hIb.le).2 hIbZ]
    have hp := T.prob_pos hIb
    unfold zpCurve
    have : 0 < R * (Ibar - w) / T.prob Ibar := by
      have : 0 < Ibar - w := by linarith
      positivity
    linarith
  obtain ⟨I, hI, hIg⟩ := intermediate_value_Icc' hwIb.le
    ((eqmGap_continuousOn T Z R w).mono (fun x hx => lt_of_lt_of_le hw hx.1))
    ⟨hgI.le, hgw.le⟩
  have hI0 : 0 < I := lt_of_lt_of_le hw hI.1
  refine ⟨I, ⟨hI0, hIg⟩, ?_⟩
  rintro J ⟨hJ, hJg⟩
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have := eqmGap_strictAntiOn T Z hR hw.le hJ hI0 h
    linarith
  · have := eqmGap_strictAntiOn T Z hR hw.le hI0 hJ h
    linarith

/-- **Location of the equilibrium** (O&R p. 412): for `0 ≤ w` with `π'(w)Z > R`, any crossing
`I > 0` satisfies `w < I` and `π'(I)Z > R` (so `I < Ī`: equilibrium investment is strictly
below the efficient level and the expected marginal product exceeds the safe rate). -/
theorem equilibrium_bounds (T : SuccessProb) {Z R w I : ℝ} (hR : 0 < R) (hw : 0 ≤ w)
    (hwI : R < T.dprob w * Z) (hI : 0 < I) (hg : eqmGap T Z R w I = 0) :
    w < I ∧ R < T.dprob I * Z := by
  have hp := T.prob_pos hI
  have heq : icCurve T Z R I = zpCurve T R w I := by unfold eqmGap at hg; linarith
  have hwI' : w < I := by
    by_contra h; push Not at h
    have hzp : zpCurve T R w I ≤ 0 := by
      unfold zpCurve
      exact div_nonpos_of_nonpos_of_nonneg (by nlinarith) hp.le
    have hic : 0 < icCurve T Z R I := by
      rw [icCurve_pos_iff T hI.le]
      have hd := T.dprob_le_of_le hI.le h
      have hZ : 0 < Z := by
        have := T.dprob_pos w hw
        by_contra h'; push Not at h'; nlinarith
      nlinarith
    linarith
  refine ⟨hwI', ?_⟩
  rw [← icCurve_pos_iff T hI.le, heq]
  unfold zpCurve
  have : 0 < I - w := by linarith
  positivity

/-! ## The optimal incentive-compatible contract -/

/-- A small-country lending setting, O&R §6.4.1 (plus observable date-2 income `E ≥ 0` of
Exercise 4; `E = 0` in the text), in the borrowing regime `0 < Y₁ + E/R < Ī` assumed on
O&R p. 408 (`Ī > Y₁`). -/
structure Setting where
  T : SuccessProb
  Z : ℝ
  R : ℝ
  Y₁ : ℝ
  E : ℝ
  R_pos : 0 < R
  Y₁_nonneg : 0 ≤ Y₁
  E_nonneg : 0 ≤ E
  wealth_pos : 0 < Y₁ + E / R
  borrowing : R < T.dprob (Y₁ + E / R) * Z

namespace Setting

variable (S : Setting)

/-- Effective wealth `w = Y₁ + E/R`, O&R p. 412 and Exercise 4. -/
noncomputable def w : ℝ := S.Y₁ + S.E / S.R

/-- `R w = R Y₁ + E`. -/
theorem R_mul_w : S.R * S.w = S.R * S.Y₁ + S.E := by
  unfold w; field_simp [S.R_pos.ne']

/-- Lenders' participation (48), as a weak inequality: the expected repayment covers `R D`,
O&R p. 410. -/
def Participates (c : Contract) (I : ℝ) : Prop :=
  S.R * c.D ≤ S.T.prob I * c.PZ + (1 - S.T.prob I) * c.P0

/-- A contract `c` inducing investment `I` is admissible if it respects limited liability
`P(0) ≤ E` (O&R p. 410: a borrower could always feign bankruptcy rather than pay out of hidden
assets), `I` is the borrower's optimal response, and lenders participate. -/
def Admissible (c : Contract) (I : ℝ) : Prop :=
  c.P0 ≤ S.E ∧ IsBestResponse S.T S.Z S.R S.Y₁ S.E c I ∧ S.Participates c I

/-- The equilibrium contract at investment `Iₑ`: `P(Z) = Z + E − R/π'(Iₑ)` (the IC curve),
`P(0) = E`, `D = Iₑ − Y₁`, O&R p. 410–412. -/
noncomputable def eqmContract (Ie : ℝ) : Contract :=
  ⟨S.Z + S.E - S.R / S.T.dprob Ie, S.E, Ie - S.Y₁⟩

/-- `Z > 0`. -/
theorem Z_pos : 0 < S.Z := by
  have := S.T.dprob_pos _ S.wealth_pos.le
  have := S.borrowing
  have := S.R_pos
  by_contra h; push Not at h; nlinarith

/-- The equilibrium investment exists and is unique (Fig. 6.11). -/
theorem eqm_exists_unique : ∃! Ie, 0 < Ie ∧ eqmGap S.T S.Z S.R S.w Ie = 0 :=
  equilibrium_exists_unique S.T S.R_pos S.wealth_pos S.borrowing

/-- The efficient investment `Ī` exists (44). -/
theorem exists_Ibar : ∃ Ibar, 0 < Ibar ∧ S.T.dprob Ibar * S.Z = S.R := by
  have hd0 : S.T.dprob (S.Y₁ + S.E / S.R) ≤ S.T.dprob 0 := S.T.dprob_le_of_le le_rfl
    S.wealth_pos.le
  have := S.Z_pos
  have := S.borrowing
  obtain ⟨Ibar, h, _⟩ := efficient_investment_exists_unique (T := S.T) S.R_pos
    (by nlinarith : S.R < S.T.dprob 0 * S.Z)
  exact ⟨Ibar, h⟩

/-- The equilibrium investment lies in `(Y₁ + E/R, Ī)`, and `Y₁ < Iₑ`, O&R p. 412. -/
theorem eqm_bounds {Ie : ℝ} (hIe : 0 < Ie) (hg : eqmGap S.T S.Z S.R S.w Ie = 0) :
    S.w < Ie ∧ S.Y₁ < Ie ∧ S.R < S.T.dprob Ie * S.Z := by
  obtain ⟨h1, h2⟩ := equilibrium_bounds S.T S.R_pos S.wealth_pos.le S.borrowing hIe hg
  have h1' : S.w < Ie := h1
  refine ⟨h1', ?_, h2⟩
  have : S.Y₁ ≤ S.w := by
    unfold w; have := S.E_nonneg; have := S.R_pos
    have : 0 ≤ S.E / S.R := by positivity
    linarith
  linarith

/-- The equilibrium identity `π(Iₑ)(Z − R/π'(Iₑ)) = R(Iₑ − Y₁) − E`. -/
theorem eqm_identity {Ie : ℝ} (hIe : 0 < Ie) (hg : eqmGap S.T S.Z S.R S.w Ie = 0) :
    S.T.prob Ie * (S.Z - S.R / S.T.dprob Ie) = S.R * (Ie - S.Y₁) - S.E := by
  have hp := (S.T.prob_pos hIe).ne'
  have hw := S.R_mul_w
  unfold eqmGap icCurve zpCurve at hg
  have : S.Z - S.R / S.T.dprob Ie = S.R * (Ie - S.w) / S.T.prob Ie := by linarith
  rw [this]
  field_simp
  linarith

/-- **The equilibrium contract implements `Iₑ` with no covert lending** (O&R p. 411–412): the
borrower's unique optimal response is `Iₑ`, `L = 0`, and lenders exactly break even (48). -/
theorem eqmContract_admissible {Ie : ℝ} (hIe : 0 < Ie) (hg : eqmGap S.T S.Z S.R S.w Ie = 0) :
    S.Admissible (S.eqmContract Ie) Ie ∧
      (∀ J, IsBestResponse S.T S.Z S.R S.Y₁ S.E (S.eqmContract Ie) J → J = Ie) ∧
      S.Y₁ + (S.eqmContract Ie).D - Ie = 0 ∧
      S.R * (S.eqmContract Ie).D =
        S.T.prob Ie * (S.eqmContract Ie).PZ + (1 - S.T.prob Ie) * (S.eqmContract Ie).P0 := by
  have hd := S.T.dprob_pos Ie hIe.le
  obtain ⟨_, hY, _⟩ := S.eqm_bounds hIe hg
  have hstake : stake S.Z (S.eqmContract Ie) = S.R / S.T.dprob Ie := by
    unfold stake eqmContract; ring
  have hs : 0 < stake S.Z (S.eqmContract Ie) := by rw [hstake]; exact div_pos S.R_pos hd
  have hfoc : S.T.dprob Ie * stake S.Z (S.eqmContract Ie) = S.R := by
    rw [hstake]; field_simp
  have hW : S.Y₁ + (S.eqmContract Ie).D = Ie := by unfold eqmContract; ring
  obtain ⟨hb, hu⟩ := bestResponse_of_foc (T := S.T) (R := S.R) (Y₁ := S.Y₁) (E := S.E) hs
    (by rw [hW]; exact hIe.le) hIe.le hfoc
  rw [hW, min_self] at hb hu
  have hid := S.eqm_identity hIe hg
  have hpart : S.R * (S.eqmContract Ie).D =
      S.T.prob Ie * (S.eqmContract Ie).PZ + (1 - S.T.prob Ie) * (S.eqmContract Ie).P0 := by
    unfold eqmContract; simp only
    linear_combination (-1 : ℝ) * hid
  exact ⟨⟨le_refl _, hb, hpart.le⟩, hu, by rw [hW]; ring, hpart⟩

/-- **No admissible contract induces more investment than `Iₑ`** (O&R p. 411–412), whatever
`P(Z)`, `P(0) ≤ E` and `D`, and whether or not the borrower's choice is interior. -/
theorem admissible_investment_le {Ie : ℝ} (hIe : 0 < Ie) (hg : eqmGap S.T S.Z S.R S.w Ie = 0)
    {c : Contract} {I : ℝ} (hc : S.Admissible c I) : I ≤ Ie := by
  obtain ⟨hP0, hbest, hpart⟩ := hc
  by_contra hlt
  push Not at hlt
  have hI : 0 < I := hIe.trans hlt
  have hd := S.T.dprob_pos I hI.le
  have hp := S.T.prob_pos hI
  have hp1 := S.T.prob_lt_one hI.le
  have hfoc := bestResponse_foc_ge S.R_pos hbest hI
  unfold stake at hfoc
  have hPZ : c.PZ ≤ S.Z + c.P0 - S.R / S.T.dprob I := by
    have : S.R / S.T.dprob I ≤ S.Z - (c.PZ - c.P0) := by
      rw [div_le_iff₀ hd]; linarith
    linarith
  have hD : I - S.Y₁ ≤ c.D := by linarith [hbest.2.1]
  unfold Participates at hpart
  have chain : S.R * (I - S.Y₁) - S.E ≤ S.T.prob I * (S.Z - S.R / S.T.dprob I) := by
    have h1 : S.R * (I - S.Y₁) ≤ S.R * c.D := mul_le_mul_of_nonneg_left hD S.R_pos.le
    have h2 : S.T.prob I * c.PZ ≤ S.T.prob I * (S.Z + c.P0 - S.R / S.T.dprob I) :=
      mul_le_mul_of_nonneg_left hPZ hp.le
    nlinarith
  have hgap : 0 ≤ eqmGap S.T S.Z S.R S.w I := by
    unfold eqmGap icCurve zpCurve
    have hw := S.R_mul_w
    rw [sub_nonneg, div_le_iff₀ hp]
    nlinarith
  have := eqmGap_strictAntiOn S.T S.Z S.R_pos (show 0 ≤ S.w from le_of_lt S.wealth_pos)
    (show Ie ∈ Ioi (0 : ℝ) from hIe) (show I ∈ Ioi (0 : ℝ) from hI) hlt
  linarith

/-- The borrower's payoff under an admissible contract is at most expected net output plus `E`
(lenders' participation), O&R p. 411. -/
theorem admissible_payoff_le_netOutput {c : Contract} {I : ℝ} (hc : S.Admissible c I) :
    borrowerPayoff S.T S.Z S.R S.Y₁ S.E c I ≤ netOutput S.T S.Z S.R S.Y₁ I + S.E := by
  obtain ⟨_, _, hpart⟩ := hc
  unfold Participates at hpart
  unfold borrowerPayoff netOutput
  nlinarith

/-- **The equilibrium contract is optimal** (O&R p. 410–412): the borrower's payoff under any
admissible contract is at most his payoff under the equilibrium contract, which equals expected
net output at `Iₑ` plus `E`. -/
theorem admissible_payoff_le {Ie : ℝ} (hIe : 0 < Ie) (hg : eqmGap S.T S.Z S.R S.w Ie = 0)
    {c : Contract} {I : ℝ} (hc : S.Admissible c I) :
    borrowerPayoff S.T S.Z S.R S.Y₁ S.E c I ≤
      borrowerPayoff S.T S.Z S.R S.Y₁ S.E (S.eqmContract Ie) Ie ∧
    borrowerPayoff S.T S.Z S.R S.Y₁ S.E (S.eqmContract Ie) Ie =
      netOutput S.T S.Z S.R S.Y₁ Ie + S.E := by
  obtain ⟨_, _, _, hpart⟩ := S.eqmContract_admissible hIe hg
  have hval : borrowerPayoff S.T S.Z S.R S.Y₁ S.E (S.eqmContract Ie) Ie =
      netOutput S.T S.Z S.R S.Y₁ Ie + S.E := by
    unfold borrowerPayoff netOutput
    unfold eqmContract at hpart ⊢; simp only at hpart ⊢
    linear_combination hpart
  refine ⟨?_, hval⟩
  rw [hval]
  have h1 := S.admissible_payoff_le_netOutput hc
  have hle := S.admissible_investment_le hIe hg hc
  obtain ⟨Ibar, hIb, hIbZ⟩ := S.exists_Ibar
  have hIeb : Ie ≤ Ibar := by
    obtain ⟨_, _, h⟩ := S.eqm_bounds hIe hg
    by_contra hh; push Not at hh
    have := S.T.dprob_le_of_le hIb.le hh.le
    have := S.Z_pos
    nlinarith
  rcases hle.lt_or_eq with h | h
  · have := netOutput_strictMonoOn (Y₁ := S.Y₁) S.Z_pos hIbZ hc.2.1.1 h hIeb
    linarith
  · subst h; exact h1

/-- **Uniqueness of the optimal contract** (O&R p. 410–412): an admissible contract inducing
`Iₑ` must be the equilibrium contract — in particular `P(0) = E` (so `P(0) = 0` in the text is a
result, not an assumption) and `D = Iₑ − Y₁`, i.e. no covert lending, `L = 0` (fn 65). -/
theorem admissible_at_Ie_unique {Ie : ℝ} (hIe : 0 < Ie) (hg : eqmGap S.T S.Z S.R S.w Ie = 0)
    {c : Contract} (hc : S.Admissible c Ie) : c = S.eqmContract Ie := by
  obtain ⟨hP0, hbest, hpart⟩ := hc
  have hd := S.T.dprob_pos Ie hIe.le
  have hp := S.T.prob_pos hIe
  have hfoc := bestResponse_foc_ge S.R_pos hbest hIe
  unfold stake at hfoc
  have hPZ : c.PZ ≤ S.Z + c.P0 - S.R / S.T.dprob Ie := by
    have : S.R / S.T.dprob Ie ≤ S.Z - (c.PZ - c.P0) := by
      rw [div_le_iff₀ hd]; linarith
    linarith
  have hD : Ie - S.Y₁ ≤ c.D := by linarith [hbest.2.1]
  unfold Participates at hpart
  have hid := S.eqm_identity hIe hg
  have h1 : S.R * (Ie - S.Y₁) ≤ S.R * c.D := mul_le_mul_of_nonneg_left hD S.R_pos.le
  have h2 : S.T.prob Ie * c.PZ ≤ S.T.prob Ie * (S.Z + c.P0 - S.R / S.T.dprob Ie) :=
    mul_le_mul_of_nonneg_left hPZ hp.le
  -- every link of the chain is an equality
  have eP0 : c.P0 = S.E := by nlinarith
  have eD : c.D = Ie - S.Y₁ := by
    have : S.R * c.D ≤ S.R * (Ie - S.Y₁) := by nlinarith
    have := le_of_mul_le_mul_left this S.R_pos
    linarith
  have ePZ : c.PZ = S.Z + S.E - S.R / S.T.dprob Ie := by
    have : S.T.prob Ie * (S.Z + c.P0 - S.R / S.T.dprob Ie) ≤ S.T.prob Ie * c.PZ := by
      nlinarith
    have := le_of_mul_le_mul_left this hp
    rw [eP0] at this hPZ
    linarith
  cases c
  simp only at eP0 eD ePZ
  unfold eqmContract
  rw [eP0, eD, ePZ]

/-- **Characterisation of the optimal incentive-compatible contract** (O&R p. 410–412, Fig. 6.11,
fn 65): there is exactly one contract that is admissible (for some induced investment) and gives
the borrower at least as much as every admissible contract; it is the equilibrium contract, it
induces `Iₑ` (the unique crossing of IC and ZP) with `L = 0`. -/
theorem optimal_contract_exists_unique :
    ∃! c : Contract, ∃ I, S.Admissible c I ∧
      ∀ c' I', S.Admissible c' I' →
        borrowerPayoff S.T S.Z S.R S.Y₁ S.E c' I' ≤ borrowerPayoff S.T S.Z S.R S.Y₁ S.E c I := by
  obtain ⟨Ie, ⟨hIe, hg⟩, _⟩ := S.eqm_exists_unique
  obtain ⟨hadm, _, _, _⟩ := S.eqmContract_admissible hIe hg
  refine ⟨S.eqmContract Ie, ⟨Ie, hadm, fun c' I' h => (S.admissible_payoff_le hIe hg h).1⟩, ?_⟩
  rintro c ⟨I, hc, hmax⟩
  have hge := hmax _ _ hadm
  obtain ⟨hle, hval⟩ := S.admissible_payoff_le hIe hg hc
  -- the payoff is maximal, so `I = Iₑ`
  have hI : I = Ie := by
    have h1 := S.admissible_payoff_le_netOutput hc
    have hIle := S.admissible_investment_le hIe hg hc
    rcases hIle.lt_or_eq with h | h
    · obtain ⟨Ibar, hIb, hIbZ⟩ := S.exists_Ibar
      have hIeb : Ie ≤ Ibar := by
        obtain ⟨_, _, h'⟩ := S.eqm_bounds hIe hg
        by_contra hh; push Not at hh
        have := S.T.dprob_le_of_le hIb.le hh.le
        have := S.Z_pos
        nlinarith
      have := netOutput_strictMonoOn (Y₁ := S.Y₁) S.Z_pos hIbZ hc.2.1.1 h hIeb
      linarith
    · exact h
  rw [hI] at hc
  exact S.admissible_at_Ie_unique hIe hg hc

end Setting


/-! ## Footnote 65: the Kuhn–Tucker route

The book's lender problem in fn 65 (with `P(0) = 0`): choose `(I, D, P(Z))` to maximise
`π(I)[Z − P(Z)] + R(Y₁ + D − I)` subject to zero profit `π(I)P(Z) = RD`, the incentive
constraint `π'(I)[Z − P(Z)] = R` and `L = Y₁ + D − I ≥ 0`, with multipliers `ψ, μ, λ`. The
problem is not concave, so the Kuhn–Tucker conditions are not sufficient; optimality was proved
directly above. Here we show (a) every Kuhn–Tucker point has `λ > 0`, hence `L = 0` (the claim
of fn 65), and is the optimum; (b) the linear-independence constraint qualification holds at the
optimum (the hypothesis the book's use of Kuhn–Tucker necessity needs but never checks); (c)
the multipliers at the optimum exist, are unique and positive. -/

/-- A second derivative of a strictly concave `π` is nonpositive. -/
theorem SuccessProb.d2_nonpos (T : SuccessProb) {I d2 : ℝ} (hI : 0 ≤ I)
    (h : HasDerivAt T.dprob d2 I) : d2 ≤ 0 := by
  have ht := h.tendsto_slope_zero_right
  apply le_of_tendsto ht
  filter_upwards [self_mem_nhdsWithin] with t (htp : 0 < t)
  have : T.dprob (I + t) < T.dprob I :=
    T.dprob_strictAnti (mem_Ici.2 hI) (mem_Ici.2 (by linarith)) (by linarith)
  simp only [smul_eq_mul]
  exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 htp.le) (by linarith)

/-- The Kuhn–Tucker conditions of fn 65 (O&R p. 411) at `(I, D, P(Z))` with multipliers `ψ` (zero
profit), `μ` (incentive compatibility), `lam` (`L ≥ 0`), where `d2 = π''(I)`: stationarity of the
Lagrangian in `I`, `D`, `P(Z)`, and complementary slackness. -/
def KTConditions (T : SuccessProb) (Z R Y₁ d2 I D PZ ψ μ lam : ℝ) : Prop :=
  T.dprob I * (Z - PZ) - R + ψ * (T.dprob I * PZ) + μ * (d2 * (Z - PZ)) - lam = 0 ∧
    R - ψ * R + lam = 0 ∧
    -T.prob I + ψ * T.prob I - μ * T.dprob I = 0 ∧
    0 ≤ lam ∧ lam * (Y₁ + D - I) = 0

/-- The constraints of fn 65: zero profit (48), incentive compatibility (47), `L ≥ 0`, `I ≥ 0`. -/
def KTConstraints (T : SuccessProb) (Z R Y₁ I D PZ : ℝ) : Prop :=
  T.prob I * PZ = R * D ∧ T.dprob I * (Z - PZ) = R ∧ 0 ≤ Y₁ + D - I ∧ 0 ≤ I

/-- The book's form (i) of the `I`-condition, obtained by using (47) to eliminate `Z − P(Z)`:
`ψπ'(I)P(Z) + μ Rπ''(I)/π'(I) − λ = 0`, O&R fn 65. -/
theorem kt_book_form {T : SuccessProb} {Z R Y₁ d2 I D PZ ψ μ lam : ℝ}
    (hkt : KTConditions T Z R Y₁ d2 I D PZ ψ μ lam) (hc : KTConstraints T Z R Y₁ I D PZ) :
    ψ * T.dprob I * PZ + μ * (R * d2 / T.dprob I) - lam = 0 := by
  obtain ⟨h1, _⟩ := hkt
  obtain ⟨_, hic, _, hI⟩ := hc
  have hd := (T.dprob_pos I hI).ne'
  have : Z - PZ = R / T.dprob I := by rw [eq_div_iff hd]; linarith
  rw [this] at h1
  have e : T.dprob I * (R / T.dprob I) = R := by field_simp
  rw [e] at h1
  have e2 : μ * (d2 * (R / T.dprob I)) = μ * (R * d2 / T.dprob I) := by ring
  rw [e2] at h1
  linarith

/-- **Footnote 65: at every Kuhn–Tucker point `λ > 0`, hence `L = 0`** (O&R p. 411). If `λ = 0`
then `ψ = 1`, `μ = 0`, so `π'(I)Z = R`, `P(Z) = 0`, `D = 0` and `I ≤ Y₁ < Ī`, a contradiction. -/
theorem kt_point_no_lending {T : SuccessProb} {Z R Y₁ d2 I D PZ ψ μ lam : ℝ} (hR : 0 < R)
    (hY : 0 ≤ Y₁) (hYI : R < T.dprob Y₁ * Z)
    (hkt : KTConditions T Z R Y₁ d2 I D PZ ψ μ lam) (hc : KTConstraints T Z R Y₁ I D PZ) :
    0 < lam ∧ Y₁ + D - I = 0 := by
  obtain ⟨h1, h2, h3, hlam, hcs⟩ := hkt
  obtain ⟨hzp, hic, hL, hI⟩ := hc
  have hd := T.dprob_pos I hI
  have hlpos : 0 < lam := by
    rcases hlam.lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h] at h1 h2
      have hψ : ψ = 1 := by
        have : R * (1 - ψ) = 0 := by linarith
        rcases mul_eq_zero.1 this with h' | h'
        · linarith
        · linarith
      rw [hψ] at h1 h3
      have hμ : μ = 0 := by
        have : μ * T.dprob I = 0 := by linarith
        rcases mul_eq_zero.1 this with h' | h'
        · exact h'
        · linarith
      rw [hμ] at h1
      have hZ : T.dprob I * Z = R := by linarith
      have hPZ : PZ = 0 := by
        have : T.dprob I * PZ = 0 := by linarith
        rcases mul_eq_zero.1 this with h' | h'
        · linarith
        · exact h'
      rw [hPZ] at hzp
      have hD : D = 0 := by
        have : R * D = 0 := by linarith
        rcases mul_eq_zero.1 this with h' | h'
        · linarith
        · exact h'
      rw [hD] at hL
      have hle : T.dprob Y₁ ≤ T.dprob I := T.dprob_le_of_le hI (by linarith)
      have hZp : 0 < Z := by
        have := T.dprob_pos Y₁ hY
        by_contra h'; push Not at h'; nlinarith
      nlinarith
  refine ⟨hlpos, ?_⟩
  rcases mul_eq_zero.1 hcs with h | h
  · linarith
  · exact h

/-- **Every Kuhn–Tucker point is the optimal contract** (with `0 < Y₁ < Ī`): it has `L = 0`,
`D = I − Y₁`, `P(Z) = Z − R/π'(I)`, and `I` is the unique crossing of IC and ZP. -/
theorem kt_point_is_optimum {T : SuccessProb} {Z R Y₁ d2 I D PZ ψ μ lam : ℝ} (hR : 0 < R)
    (hY : 0 < Y₁) (hYI : R < T.dprob Y₁ * Z)
    (hkt : KTConditions T Z R Y₁ d2 I D PZ ψ μ lam) (hc : KTConstraints T Z R Y₁ I D PZ) :
    0 < I ∧ D = I - Y₁ ∧ PZ = Z - R / T.dprob I ∧ eqmGap T Z R Y₁ I = 0 := by
  obtain ⟨_, hL⟩ := kt_point_no_lending hR hY.le hYI hkt hc
  obtain ⟨hzp, hic, _, hI⟩ := hc
  have hD : D = I - Y₁ := by linarith
  have hI0 : 0 < I := by
    rcases hI.lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h, T.prob_zero] at hzp
      have : D = 0 := by
        have : R * D = 0 := by linarith
        rcases mul_eq_zero.1 this with h' | h'
        · linarith
        · exact h'
      rw [← h] at hD
      linarith
  have hd := (T.dprob_pos I hI).ne'
  have hPZ : PZ = Z - R / T.dprob I := by
    have : R / T.dprob I = Z - PZ := by rw [div_eq_iff hd]; linarith
    linarith
  refine ⟨hI0, hD, hPZ, ?_⟩
  have hp := (T.prob_pos hI0).ne'
  have hz : R * (I - Y₁) / T.prob I = PZ := by rw [← hD, ← hzp]; field_simp
  unfold eqmGap icCurve zpCurve
  rw [hz, hPZ]
  ring

/-- **The linear-independence constraint qualification at the optimum** (the hypothesis needed
for Kuhn–Tucker necessity in fn 65): at `D = I − Y₁`, `P(Z) = Z − R/π'(I)` with `I` the
equilibrium investment, the gradients in `(I, D, P(Z))` of zero profit `(π'P, −R, π)`, of
incentive compatibility `(π''(Z − P), 0, −π')` and of `L ≥ 0` `(−1, 1, 0)` are linearly
independent. -/
theorem licq_at_optimum {T : SuccessProb} {Z R Y₁ I d2 : ℝ} (hR : 0 < R) (hY : 0 ≤ Y₁)
    (hI : 0 < I) (hg : eqmGap T Z R Y₁ I = 0) (hd2 : HasDerivAt T.dprob d2 I) (a b c : ℝ)
    (e1 : a * (T.dprob I * (Z - R / T.dprob I)) + b * (d2 * (Z - (Z - R / T.dprob I))) +
      c * (-1) = 0)
    (e2 : a * (-R) + b * 0 + c * 1 = 0)
    (e3 : a * T.prob I + b * (-T.dprob I) + c * 0 = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  have hd := T.dprob_pos I hI.le
  have hp := T.prob_pos hI
  have hd2n := T.d2_nonpos hI.le hd2
  have h66 := T.mul_dprob_lt_prob hI
  -- the equilibrium: `π(I)(Z − R/π'(I)) = R(I − Y₁)`
  have heq : T.prob I * (Z - R / T.dprob I) = R * (I - Y₁) := by
    unfold eqmGap icCurve zpCurve at hg
    have : Z - R / T.dprob I = R * (I - Y₁) / T.prob I := by linarith
    rw [this]; field_simp
  have hc : c = a * R := by linarith
  have hb : b * T.dprob I = a * T.prob I := by linarith
  have e1' : a * (T.dprob I * Z - R) + b * (d2 * (R / T.dprob I)) - c = 0 := by
    have : T.dprob I * (Z - R / T.dprob I) = T.dprob I * Z - R := by field_simp
    rw [this] at e1
    have : Z - (Z - R / T.dprob I) = R / T.dprob I := by ring
    rw [this] at e1
    linarith
  -- multiply through by `π'(I)²` and substitute
  have key : a * (T.dprob I ^ 2 * (T.dprob I * Z - R) + T.prob I * d2 * R -
      R * T.dprob I ^ 2) = 0 := by
    have : (a * (T.dprob I * Z - R) + b * (d2 * (R / T.dprob I)) - c) * T.dprob I ^ 2 = 0 := by
      rw [e1']; ring
    have e4 : b * (d2 * (R / T.dprob I)) * T.dprob I ^ 2 = (b * T.dprob I) * d2 * R := by
      field_simp
    rw [sub_mul, add_mul, e4, hb, hc] at this
    linarith
  have hK : T.dprob I ^ 2 * (T.dprob I * Z - R) + T.prob I * d2 * R - R * T.dprob I ^ 2 < 0 := by
    -- `π'(I)Z − R = π'(I) R (I − Y₁)/π(I)` and `π'(I)(I − Y₁) < π(I)`
    have hZ : T.prob I * (T.dprob I * Z - R) = T.dprob I * (R * (I - Y₁)) := by
      rw [← heq]; field_simp
    have h1 : T.dprob I * (I - Y₁) < T.prob I := by nlinarith [mul_nonneg hd.le hY]
    have hlt : T.prob I * (T.dprob I * Z - R) < T.prob I * R := by
      rw [hZ]; nlinarith [mul_lt_mul_of_pos_right h1 hR]
    have h2 : T.dprob I * Z - R < R := lt_of_mul_lt_mul_left hlt hp.le
    have h3 : T.prob I * d2 * R ≤ 0 := by
      have := mul_nonpos_of_nonneg_of_nonpos hp.le hd2n
      nlinarith
    have h4 := mul_lt_mul_of_pos_left h2 (pow_pos hd 2)
    nlinarith
  have ha : a = 0 := by
    rcases mul_eq_zero.1 key with h | h
    · exact h
    · linarith
  refine ⟨ha, ?_, by rw [hc, ha]; ring⟩
  rw [ha] at hb
  have : b * T.dprob I = 0 := by linarith
  rcases mul_eq_zero.1 this with h | h
  · exact h
  · linarith

/-- **The Kuhn–Tucker multipliers at the optimum exist, are unique, and are positive**
(O&R fn 65): with `A = R(1 − π π''/π'²)` and `B = π'(I)P(Z)`, `ψ = A/(A − B) > 1`,
`λ = R(ψ − 1) > 0`, `μ = π(ψ − 1)/π' > 0`. -/
theorem kt_multipliers_at_optimum {T : SuccessProb} {Z R Y₁ I d2 : ℝ} (hR : 0 < R)
    (hY : 0 ≤ Y₁) (hI : 0 < I) (hYI : Y₁ < I) (hg : eqmGap T Z R Y₁ I = 0)
    (hd2 : HasDerivAt T.dprob d2 I) :
    ∃! m : ℝ × ℝ × ℝ,
      KTConditions T Z R Y₁ d2 I (I - Y₁) (Z - R / T.dprob I) m.1 m.2.1 m.2.2 ∧
        1 < m.1 ∧ 0 < m.2.1 ∧ 0 < m.2.2 := by
  have hd := T.dprob_pos I hI.le
  have hp := T.prob_pos hI
  have hd2n := T.d2_nonpos hI.le hd2
  have h66 := T.mul_dprob_lt_prob hI
  obtain ⟨P, hP⟩ : ∃ P, P = Z - R / T.dprob I := ⟨_, rfl⟩
  have heq : T.prob I * P = R * (I - Y₁) := by
    unfold eqmGap icCurve zpCurve at hg
    have : Z - R / T.dprob I = R * (I - Y₁) / T.prob I := by linarith
    rw [hP, this]; field_simp
  rw [← hP]
  obtain ⟨A, hA⟩ : ∃ A, A = R - R * T.prob I * d2 / T.dprob I ^ 2 := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B, B = T.dprob I * P := ⟨_, rfl⟩
  have hBpos : 0 < B := by
    have : 0 < P := by
      have hYI : 0 < R * (I - Y₁) := mul_pos hR (by linarith)
      have : 0 < T.prob I * P := by rw [heq]; exact hYI
      exact pos_of_mul_pos_right this hp.le
    rw [hB]; positivity
  have hAB : B < A := by
    have hBv : T.prob I * B = T.dprob I * (R * (I - Y₁)) := by rw [hB, ← heq]; ring
    have h1 : T.dprob I * (I - Y₁) < T.prob I := by nlinarith [mul_nonneg hd.le hY]
    have hlt : T.prob I * B < T.prob I * R := by
      rw [hBv]; nlinarith [mul_lt_mul_of_pos_right h1 hR]
    have hBR : B < R := lt_of_mul_lt_mul_left hlt hp.le
    have : R * T.prob I * d2 / T.dprob I ^ 2 ≤ 0 := by
      apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
      have := mul_nonpos_of_nonneg_of_nonpos (mul_pos hR hp).le hd2n
      linarith
    rw [hA]; linarith
  have hApos : 0 < A := lt_trans hBpos hAB
  obtain ⟨ψ, hψ⟩ : ∃ ψ, ψ = A / (A - B) := ⟨_, rfl⟩
  have hψv : ψ * (A - B) = A := by rw [hψ]; field_simp [(by linarith : A - B ≠ 0)]
  have hψ1 : 1 < ψ := by rw [hψ, lt_div_iff₀ (by linarith)]; linarith
  have hexpr : ∀ x : ℝ, T.dprob I * (Z - P) - R + x * (T.dprob I * P) +
      T.prob I * (x - 1) / T.dprob I * (d2 * (Z - P)) - R * (x - 1) = A - x * (A - B) := by
    intro x
    rw [hA, hB, show Z - P = R / T.dprob I by rw [hP]; ring]
    field_simp
    ring
  refine ⟨(ψ, T.prob I * (ψ - 1) / T.dprob I, R * (ψ - 1)), ⟨⟨?_, ?_, ?_, ?_, ?_⟩, hψ1, ?_, ?_⟩,
    ?_⟩
  · simp only
    rw [hexpr, hψv]; ring
  · simp only; ring
  · simp only; field_simp; ring
  · simp only; nlinarith
  · simp only; ring
  · simp only; have : 0 < ψ - 1 := by linarith
    positivity
  · simp only; nlinarith
  · rintro ⟨ψ', μ', lam'⟩ ⟨⟨k1, k2, k3, _, _⟩, _, _, _⟩
    have hμ' : μ' = T.prob I * (ψ' - 1) / T.dprob I := by
      rw [eq_div_iff hd.ne']; linarith
    have hl' : lam' = R * (ψ' - 1) := by linarith
    simp only at k1
    rw [hμ', hl', hexpr] at k1
    have hψeq : ψ' = ψ := by
      rw [hψ, eq_div_iff (by linarith)]; linarith
    rw [hψeq] at hμ' hl'
    rw [hψeq, hμ', hl']

/-! ## Comparative statics (p. 412) -/

/-- **Investment rises with initial wealth** (O&R p. 412: a rise in `Y₁` shifts ZP right and
raises `I`): if `w < w'` with `w' ≥ 0` and `I`, `I'` are the respective crossings, `I < I'`. -/
theorem eqm_strictMono_wealth (T : SuccessProb) {Z R w w' I I' : ℝ} (hR : 0 < R) (hw' : 0 ≤ w')
    (hww : w < w') (hI : 0 < I) (hI' : 0 < I') (hg : eqmGap T Z R w I = 0)
    (hg' : eqmGap T Z R w' I' = 0) : I < I' := by
  have h1 := eqmGap_lt_of_wealth_lt T Z hR hww hI
  by_contra hle
  push Not at hle
  rcases hle.lt_or_eq with h | h
  · have := eqmGap_strictAntiOn T Z hR hw' (show I' ∈ Ioi (0 : ℝ) from hI')
      (show I ∈ Ioi (0 : ℝ) from hI) h
    linarith
  · rw [h] at hg'; linarith

/-- **Investment rises with the success payoff `Z`** (O&R p. 412: IC shifts up). -/
theorem eqm_strictMono_Z (T : SuccessProb) {Z Z' R w I I' : ℝ} (hR : 0 < R) (hw : 0 ≤ w)
    (hZZ : Z < Z') (hI : 0 < I) (hI' : 0 < I') (hg : eqmGap T Z R w I = 0)
    (hg' : eqmGap T Z' R w I' = 0) : I < I' := by
  have h1 : eqmGap T Z R w I < eqmGap T Z' R w I := by unfold eqmGap icCurve; linarith
  by_contra hle
  push Not at hle
  rcases hle.lt_or_eq with h | h
  · have := eqmGap_strictAntiOn T Z' hR hw (show I' ∈ Ioi (0 : ℝ) from hI')
      (show I ∈ Ioi (0 : ℝ) from hI) h
    linarith
  · rw [h] at hg'; linarith

/-- **Investment falls with the world interest rate** (O&R p. 412: both curves shift left). -/
theorem eqm_strictAnti_R (T : SuccessProb) {Z R R' w I I' : ℝ} (hR : 0 < R) (hZ : 0 < Z)
    (hw : 0 ≤ w) (hRR : R < R') (hI : 0 < I) (hI' : 0 < I') (hg : eqmGap T Z R w I = 0)
    (hg' : eqmGap T Z R' w I' = 0) : I' < I := by
  have hR' : 0 < R' := hR.trans hRR
  -- `Z = R·β(I)` with `β(I) = 1/π'(I) + (I − w)/π(I) > 0`
  have hβ : 0 < 1 / T.dprob I + (I - w) / T.prob I := by
    have : Z = R * (1 / T.dprob I + (I - w) / T.prob I) := by
      unfold eqmGap icCurve zpCurve at hg
      have e : R * (1 / T.dprob I + (I - w) / T.prob I) =
          R / T.dprob I + R * (I - w) / T.prob I := by ring
      rw [e]; linarith
    rw [this] at hZ
    exact pos_of_mul_pos_right hZ hR.le
  have h1 : eqmGap T Z R' w I < 0 := by
    have e : eqmGap T Z R' w I = eqmGap T Z R w I -
        (R' - R) * (1 / T.dprob I + (I - w) / T.prob I) := by
      unfold eqmGap icCurve zpCurve; ring
    rw [e, hg]
    have : 0 < (R' - R) * (1 / T.dprob I + (I - w) / T.prob I) :=
      mul_pos (by linarith) hβ
    linarith
  by_contra hle
  push Not at hle
  rcases hle.lt_or_eq with h | h
  · have := eqmGap_strictAntiOn T Z hR' hw (show I ∈ Ioi (0 : ℝ) from hI)
      (show I' ∈ Ioi (0 : ℝ) from hI') h
    linarith
  · rw [← h] at hg'; linarith

/-- **Richer countries have smaller gaps between the expected marginal product and the safe
rate** (O&R p. 412): `π'(I)Z − R` falls as equilibrium investment rises. -/
theorem mpk_gap_falls (T : SuccessProb) {Z R I I' : ℝ} (hZ : 0 < Z) (hI : 0 ≤ I) (hII : I < I') :
    T.dprob I' * Z - R < T.dprob I * Z - R := by
  have := T.dprob_strictAnti (mem_Ici.2 hI) (mem_Ici.2 (by linarith)) hII
  nlinarith

/-- **Expected output is below the full-information level** (O&R p. 412): `π(Iₑ)Z < π(Ī)Z`. -/
theorem output_below_full_information (T : SuccessProb) {Z Ie Ibar : ℝ} (hZ : 0 < Z)
    (hIe : 0 ≤ Ie) (hlt : Ie < Ibar) : T.prob Ie * Z < T.prob Ibar * Z := by
  have := T.prob_strictMonoOn (mem_Ici.2 hIe) (mem_Ici.2 (by linarith)) hlt
  nlinarith

/-! ### Does a rise in `Y₁` raise investment by less than `Y₁`? (p. 412)

The book asserts that investment rises by less than `Y₁`, so capital inflows `D = I − Y₁` fall.
At an equilibrium `D = Φ(I)` with `Φ(I) = π(I)(Z/R − 1/π'(I))`, so inflows fall iff `Φ`
decreases between the two equilibrium investment levels; locally, iff
`(I − Y₁)π'(I)/π(I)² < −π''(I)/π'(I)²`. This is not implied by the book's assumptions: an
explicit counterexample follows. -/

/-- Capital inflows as a function of equilibrium investment, `Φ(I) = π(I)(Z/R − 1/π'(I))`. -/
noncomputable def inflowFn (T : SuccessProb) (Z R I : ℝ) : ℝ := T.prob I * (Z / R - 1 / T.dprob I)

/-- At an equilibrium, capital inflows `I − w` equal `Φ(I)`. -/
theorem eqm_inflow (T : SuccessProb) {Z R w I : ℝ} (hR : 0 < R) (hI : 0 < I)
    (hg : eqmGap T Z R w I = 0) : I - w = inflowFn T Z R I := by
  have hp := (T.prob_pos hI).ne'
  have hd := (T.dprob_pos I hI.le).ne'
  unfold eqmGap icCurve zpCurve at hg
  unfold inflowFn
  have : Z - R / T.dprob I = R * (I - w) / T.prob I := by linarith
  have e : Z / R - 1 / T.dprob I = (Z - R / T.dprob I) / R := by field_simp
  rw [e, this]
  field_simp

/-- Between two equilibria, inflows fall iff investment rises by less than wealth iff `Φ` falls:
the exact content of the p. 412 claim. -/
theorem inflow_falls_iff (T : SuccessProb) {Z R w w' I I' : ℝ} (hR : 0 < R) (hI : 0 < I)
    (hI' : 0 < I') (hg : eqmGap T Z R w I = 0) (hg' : eqmGap T Z R w' I' = 0) :
    (I' - w' < I - w ↔ I' - I < w' - w) ∧
      (I' - w' < I - w ↔ inflowFn T Z R I' < inflowFn T Z R I) := by
  rw [← eqm_inflow T hR hI hg, ← eqm_inflow T hR hI' hg']
  constructor <;> constructor <;> intro h <;> linarith

/-- The derivative of `Φ` when `π'` has derivative `π''(I) = d2`:
`Φ'(I) = π'(I)(Z/R − 1/π'(I)) + π(I)π''(I)/π'(I)²`. -/
theorem inflowFn_hasDerivAt (T : SuccessProb) (Z R : ℝ) {I d2 : ℝ} (hI : 0 ≤ I)
    (hd2 : HasDerivAt T.dprob d2 I) :
    HasDerivAt (inflowFn T Z R)
      (T.dprob I * (Z / R - 1 / T.dprob I) + T.prob I * (d2 / T.dprob I ^ 2)) I := by
  have hd := (T.dprob_pos I hI).ne'
  have hinv : HasDerivAt (fun x => Z / R - 1 / T.dprob x) (d2 / T.dprob I ^ 2) I := by
    have := ((hd2.inv hd).const_sub (Z / R))
    convert this using 1
    · ext x; simp [one_div]
    · field_simp
  exact (T.hasDerivAt I hI).mul hinv

/-- **The exact condition** (correcting O&R p. 412): at an equilibrium, `Φ'(I) < 0` (inflows
locally fall as `Y₁` rises) iff `(I − w)π'(I)/π(I)² < −π''(I)/π'(I)²`. -/
theorem inflowFn_deriv_neg_iff (T : SuccessProb) {Z R w I d2 : ℝ} (hR : 0 < R) (hI : 0 < I)
    (hg : eqmGap T Z R w I = 0) :
    T.dprob I * (Z / R - 1 / T.dprob I) + T.prob I * (d2 / T.dprob I ^ 2) < 0 ↔
      (I - w) * T.dprob I / T.prob I ^ 2 < -d2 / T.dprob I ^ 2 := by
  have hp := T.prob_pos hI
  have hd := T.dprob_pos I hI.le
  have hΦ := eqm_inflow T hR hI hg
  unfold inflowFn at hΦ
  have e : Z / R - 1 / T.dprob I = (I - w) / T.prob I := by
    rw [eq_div_iff hp.ne']; linarith
  rw [e]
  have e1 : T.dprob I * ((I - w) / T.prob I) + T.prob I * (d2 / T.dprob I ^ 2) =
      T.prob I * ((I - w) * T.dprob I / T.prob I ^ 2 - -d2 / T.dprob I ^ 2) := by
    field_simp
    ring
  rw [e1]
  constructor
  · intro h
    have := (mul_neg_iff.1 h)
    rcases this with ⟨_, h2⟩ | ⟨h1, _⟩
    · linarith
    · linarith
  · intro h
    exact mul_neg_of_pos_of_neg hp (by linarith)

/-- The rational technology `π(I) = I/(1 + I)`, `π'(I) = 1/(1 + I)²`, satisfying all the
assumptions of O&R p. 408 (used for the counterexample to the p. 412 claim). -/
noncomputable def ratProb : SuccessProb where
  prob I := I / (1 + I)
  dprob I := 1 / (1 + I) ^ 2
  hasDerivAt I hI := by
    have h1 : (1 + I) ≠ 0 := by positivity
    have := (hasDerivAt_id' I).div ((hasDerivAt_id' I).const_add 1) h1
    exact this.congr_deriv (by field_simp; ring)
  dprob_pos I hI := by positivity
  dprob_strictAnti := by
    intro a ha b hb hab
    have ha' : (0 : ℝ) ≤ a := ha
    apply one_div_lt_one_div_of_lt (by positivity)
    exact pow_lt_pow_left₀ (by linarith) (by linarith) two_ne_zero
  prob_zero := by simp
  prob_le_one I hI := by
    rw [div_le_one (by positivity)]
    linarith

/-- **Counterexample to O&R p. 412** ("investment rises by less than `Y₁` … capital inflows `D`
decline"): with `π(I) = I/(1+I)`, `Z = 5/2`, `r = 0`, raising `Y₁` from `7/300` to `1/16` raises
the (unique) equilibrium investment from `1/5` to `1/4` — by `1/20 > 47/1200`, the rise in `Y₁` —
and capital inflows rise from `53/300` to `3/16`. Both endowments are in the borrowing regime. -/
theorem p412_counterexample :
    ∃ (T : SuccessProb) (Z R Y₁ Y₁' I I' : ℝ),
      0 < R ∧ 0 < Y₁ ∧ Y₁ < Y₁' ∧ R < T.dprob Y₁ * Z ∧ R < T.dprob Y₁' * Z ∧
      0 < I ∧ eqmGap T Z R Y₁ I = 0 ∧ 0 < I' ∧ eqmGap T Z R Y₁' I' = 0 ∧
      (∀ J, 0 < J → eqmGap T Z R Y₁ J = 0 → J = I) ∧
      (∀ J, 0 < J → eqmGap T Z R Y₁' J = 0 → J = I') ∧
      Y₁' - Y₁ < I' - I ∧ I - Y₁ < I' - Y₁' := by
  have g1 : eqmGap ratProb (5 / 2) 1 (7 / 300) (1 / 5) = 0 := by
    unfold eqmGap icCurve zpCurve; simp only [ratProb]; norm_num
  have g2 : eqmGap ratProb (5 / 2) 1 (1 / 16) (1 / 4) = 0 := by
    unfold eqmGap icCurve zpCurve; simp only [ratProb]; norm_num
  have uniq : ∀ w I J : ℝ, 0 ≤ w → 0 < I → 0 < J → eqmGap ratProb (5 / 2) 1 w I = 0 →
      eqmGap ratProb (5 / 2) 1 w J = 0 → J = I := by
    intro w I J hw hI hJ hgI hgJ
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have := eqmGap_strictAntiOn ratProb (5 / 2) one_pos hw
        (show J ∈ Ioi (0 : ℝ) from hJ) (show I ∈ Ioi (0 : ℝ) from hI) h
      linarith
    · have := eqmGap_strictAntiOn ratProb (5 / 2) one_pos hw
        (show I ∈ Ioi (0 : ℝ) from hI) (show J ∈ Ioi (0 : ℝ) from hJ) h
      linarith
  refine ⟨ratProb, 5 / 2, 1, 7 / 300, 1 / 16, 1 / 5, 1 / 4, one_pos, by norm_num, by norm_num,
    ?_, ?_, by norm_num, g1, by norm_num, g2, ?_, ?_, by norm_num, by norm_num⟩
  · simp only [ratProb]; norm_num
  · simp only [ratProb]; norm_num
  · intro J hJ hgJ; exact uniq _ _ _ (by norm_num) (by norm_num) hJ g1 hgJ
  · intro J hJ hgJ; exact uniq _ _ _ (by norm_num) (by norm_num) hJ g2 hgJ


/-! ### Is investment a concave function of wealth? (p. 413)

The book says that "under plausible conditions" `I` is a strictly concave function of `Y₁`, so
that greater wealth inequality lowers average investment. The equilibrium investment `I(w)` is
the inverse of the wealth map `g(I) = I − Φ(I)`, so we obtain an exact, derivative-free
criterion: `I(·)` is strictly concave on a wealth interval **iff** capital inflows `Φ` are
strictly concave on the corresponding investment interval. Under it, inequality lowers average
investment (Jensen; and any widening of a two-point spread lowers it further). The criterion
can fail: for the technology `π(I) = 0.3·I/(0.01 + I) + 0.7·I/(1 + I)` an equal wealth
distribution yields *less* average investment than an unequal one. -/

/-- The wealth at which `I` is the equilibrium investment, `g(I) = I − Φ(I)`. -/
noncomputable def eqmWealth (T : SuccessProb) (Z R I : ℝ) : ℝ := I - inflowFn T Z R I

/-- `I` is the crossing for wealth `w` iff `w = g(I)`. -/
theorem eqmGap_eq_zero_iff_wealth (T : SuccessProb) {Z R w I : ℝ} (hR : 0 < R) (hI : 0 < I) :
    eqmGap T Z R w I = 0 ↔ w = eqmWealth T Z R I := by
  constructor
  · intro hg; have := eqm_inflow T hR hI hg; unfold eqmWealth; linarith
  · intro hw
    have hp := (T.prob_pos hI).ne'
    have hd := (T.dprob_pos I hI.le).ne'
    unfold eqmGap icCurve zpCurve
    rw [hw]; unfold eqmWealth inflowFn
    field_simp
    ring

/-- The equilibrium investment as a function of wealth (the unique crossing when it exists). -/
noncomputable def eqmI (T : SuccessProb) (Z R w : ℝ) : ℝ := by
  classical
  exact if h : ∃ I, 0 < I ∧ eqmGap T Z R w I = 0 then h.choose else 0

/-- `eqmI` picks out the crossing whenever there is one (`w ≥ 0`). -/
theorem eqmI_eq (T : SuccessProb) {Z R w I : ℝ} (hR : 0 < R) (hw : 0 ≤ w) (hI : 0 < I)
    (hg : eqmGap T Z R w I = 0) : eqmI T Z R w = I := by
  have hex : ∃ I, 0 < I ∧ eqmGap T Z R w I = 0 := ⟨I, hI, hg⟩
  unfold eqmI
  rw [dite_eq_left_of_eq_true (eq_true hex)]
  obtain ⟨h1, h2⟩ := hex.choose_spec
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  · have := eqmGap_strictAntiOn T Z hR hw (show hex.choose ∈ Ioi (0 : ℝ) from h1)
      (show I ∈ Ioi (0 : ℝ) from hI) h
    linarith
  · have := eqmGap_strictAntiOn T Z hR hw (show I ∈ Ioi (0 : ℝ) from hI)
      (show hex.choose ∈ Ioi (0 : ℝ) from h1) h
    linarith

/-- In the borrowing regime `0 < w`, `π'(w)Z > R`, `eqmI w` is the positive crossing. -/
theorem eqmI_spec (T : SuccessProb) {Z R w : ℝ} (hR : 0 < R) (hw : 0 < w)
    (hwI : R < T.dprob w * Z) : 0 < eqmI T Z R w ∧ eqmGap T Z R w (eqmI T Z R w) = 0 := by
  obtain ⟨I, ⟨hI, hg⟩, _⟩ := equilibrium_exists_unique T hR hw hwI
  rw [eqmI_eq T hR hw.le hI hg]
  exact ⟨hI, hg⟩

/-- On a wealth interval `[wa, wb]` in the borrowing regime (`0 < wa`, `π'(wb)Z > R`),
equilibrium investment is strictly increasing, and `g` inverts it: `g(I(w)) = w`,
and every `I ∈ [I(wa), I(wb)]` is `I(g(I))` with `g(I) ∈ [wa, wb]`. -/
theorem eqmI_interval_facts (T : SuccessProb) {Z R wa wb : ℝ} (hR : 0 < R) (hwa : 0 < wa)
    (hwab : wa ≤ wb) (hwb : R < T.dprob wb * Z) :
    (∀ w ∈ Icc wa wb, 0 < eqmI T Z R w ∧ eqmGap T Z R w (eqmI T Z R w) = 0) ∧
    StrictMonoOn (eqmI T Z R) (Icc wa wb) ∧
    (∀ w ∈ Icc wa wb, eqmWealth T Z R (eqmI T Z R w) = w) ∧
    (∀ I ∈ Icc (eqmI T Z R wa) (eqmI T Z R wb),
      eqmWealth T Z R I ∈ Icc wa wb ∧ eqmI T Z R (eqmWealth T Z R I) = I) := by
  have spec : ∀ w ∈ Icc wa wb, 0 < eqmI T Z R w ∧ eqmGap T Z R w (eqmI T Z R w) = 0 := by
    intro w hw
    have hw0 : 0 < w := lt_of_lt_of_le hwa hw.1
    apply eqmI_spec T hR hw0
    have := T.dprob_le_of_le hw0.le hw.2
    have hZ : 0 < Z := by
      have := T.dprob_pos wb (hwa.le.trans (hw.1.trans hw.2))
      by_contra h; push Not at h; nlinarith
    nlinarith
  have mono : StrictMonoOn (eqmI T Z R) (Icc wa wb) := by
    intro w hw w' hw' hlt
    exact eqm_strictMono_wealth T hR (lt_of_lt_of_le hwa hw'.1).le hlt (spec w hw).1
      (spec w' hw').1 (spec w hw).2 (spec w' hw').2
  have inv : ∀ w ∈ Icc wa wb, eqmWealth T Z R (eqmI T Z R w) = w := by
    intro w hw
    exact ((eqmGap_eq_zero_iff_wealth T hR (spec w hw).1).1 (spec w hw).2).symm
  refine ⟨spec, mono, inv, ?_⟩
  intro I hI
  have ha := spec wa ⟨le_rfl, hwab⟩
  have hb := spec wb ⟨hwab, le_rfl⟩
  have hIpos : 0 < I := lt_of_lt_of_le ha.1 hI.1
  have hg : eqmGap T Z R (eqmWealth T Z R I) I = 0 :=
    (eqmGap_eq_zero_iff_wealth T hR hIpos).2 rfl
  have hlow : wa ≤ eqmWealth T Z R I := by
    by_contra h; push Not at h
    have := eqm_strictMono_wealth T hR hwa.le h hIpos ha.1 hg ha.2
    linarith [hI.1]
  have hhigh : eqmWealth T Z R I ≤ wb := by
    by_contra h; push Not at h
    have := eqm_strictMono_wealth T hR (hwa.le.trans hlow) h hb.1 hIpos hb.2 hg
    linarith [hI.2]
  exact ⟨⟨hlow, hhigh⟩, eqmI_eq T hR (hwa.le.trans hlow) hIpos hg⟩

/-- **The exact condition for p. 413** (derivative-free): on a wealth interval `[wa, wb]` in
the borrowing regime, equilibrium investment `I(w)` is strictly concave **iff** capital inflows
`Φ(I) = π(I)(Z/R − 1/π'(I))` are strictly concave on `[I(wa), I(wb)]`. -/
theorem eqmI_strictConcave_iff (T : SuccessProb) {Z R wa wb : ℝ} (hR : 0 < R) (hwa : 0 < wa)
    (hwab : wa ≤ wb) (hwb : R < T.dprob wb * Z) :
    StrictConcaveOn ℝ (Icc wa wb) (eqmI T Z R) ↔
      StrictConcaveOn ℝ (Icc (eqmI T Z R wa) (eqmI T Z R wb)) (inflowFn T Z R) := by
  obtain ⟨_, mono, inv, back⟩ := eqmI_interval_facts T hR hwa hwab hwb
  constructor
  · intro hc
    refine ⟨convex_Icc _ _, ?_⟩
    intro I₁ hI₁ I₂ hI₂ hne a b ha hb hab
    obtain ⟨hw₁, e₁⟩ := back I₁ hI₁
    obtain ⟨hw₂, e₂⟩ := back I₂ hI₂
    have hwne : eqmWealth T Z R I₁ ≠ eqmWealth T Z R I₂ := by
      intro h; apply hne; rw [← e₁, ← e₂, h]
    have key := hc.2 hw₁ hw₂ hwne ha hb hab
    rw [e₁, e₂] at key
    simp only [smul_eq_mul] at key ⊢
    have hJ : a * I₁ + b * I₂ ∈ Icc (eqmI T Z R wa) (eqmI T Z R wb) := by
      have := (convex_Icc (eqmI T Z R wa) (eqmI T Z R wb)) hI₁ hI₂ ha.le hb.le hab
      simpa [smul_eq_mul] using this
    obtain ⟨hwJ, eJ⟩ := back _ hJ
    have hwbar : a * eqmWealth T Z R I₁ + b * eqmWealth T Z R I₂ ∈ Icc wa wb := by
      have := (convex_Icc wa wb) hw₁ hw₂ ha.le hb.le hab
      simpa [smul_eq_mul] using this
    have hlt : eqmWealth T Z R (a * I₁ + b * I₂) <
        a * eqmWealth T Z R I₁ + b * eqmWealth T Z R I₂ := by
      by_contra h; push Not at h
      have := mono.monotoneOn hwbar hwJ h
      rw [eJ] at this; linarith
    unfold eqmWealth at hlt
    have : a * I₁ + b * I₂ = a * I₁ + b * I₂ := rfl
    nlinarith
  · intro hc
    refine ⟨convex_Icc _ _, ?_⟩
    intro w₁ hw₁ w₂ hw₂ hne a b ha hb hab
    have hmem : ∀ w ∈ Icc wa wb, eqmI T Z R w ∈ Icc (eqmI T Z R wa) (eqmI T Z R wb) :=
      fun w hw => ⟨mono.monotoneOn ⟨le_rfl, hwab⟩ hw hw.1,
        mono.monotoneOn hw ⟨hwab, le_rfl⟩ hw.2⟩
    have hIne : eqmI T Z R w₁ ≠ eqmI T Z R w₂ := fun h => hne (mono.injOn hw₁ hw₂ h)
    have key := hc.2 (hmem w₁ hw₁) (hmem w₂ hw₂) hIne ha hb hab
    simp only [smul_eq_mul] at key ⊢
    have hJ : a * eqmI T Z R w₁ + b * eqmI T Z R w₂ ∈
        Icc (eqmI T Z R wa) (eqmI T Z R wb) := by
      have := (convex_Icc (eqmI T Z R wa) (eqmI T Z R wb)) (hmem w₁ hw₁) (hmem w₂ hw₂)
        ha.le hb.le hab
      simpa [smul_eq_mul] using this
    obtain ⟨hwJ, eJ⟩ := back _ hJ
    have hwbar : a * w₁ + b * w₂ ∈ Icc wa wb := by
      have := (convex_Icc wa wb) hw₁ hw₂ ha.le hb.le hab
      simpa [smul_eq_mul] using this
    have i₁ := inv w₁ hw₁
    have i₂ := inv w₂ hw₂
    unfold eqmWealth at i₁ i₂
    have hlt : eqmWealth T Z R (a * eqmI T Z R w₁ + b * eqmI T Z R w₂) < a * w₁ + b * w₂ := by
      unfold eqmWealth; nlinarith
    have := mono hwJ hwbar hlt
    rw [eJ] at this
    exact this

/-- **Inequality lowers average investment** (O&R p. 413) when `I(·)` is strictly concave: for
any finite population of entrepreneur groups with weights `αᵢ > 0` summing to one and wealths
`wᵢ` in the interval, not all equal, average investment `Σ αᵢ I(wᵢ)` is strictly below the
investment `I(Σ αᵢ wᵢ)` under an equal distribution of the same total wealth. -/
theorem inequality_lowers_average_investment (T : SuccessProb) {Z R : ℝ} {W : Set ℝ}
    (hconc : StrictConcaveOn ℝ W (eqmI T Z R)) {ι : Type} (t : Finset ι) (α w : ι → ℝ)
    (hα : ∀ i ∈ t, 0 < α i) (hsum : ∑ i ∈ t, α i = 1) (hw : ∀ i ∈ t, w i ∈ W)
    (hne : ∃ j ∈ t, ∃ k ∈ t, w j ≠ w k) :
    ∑ i ∈ t, α i * eqmI T Z R (w i) < eqmI T Z R (∑ i ∈ t, α i * w i) := by
  have := hconc.lt_map_sum hα hsum hw hne
  simpa [smul_eq_mul] using this

/-- **A wider spread lowers average investment further** (a mean-preserving spread of a
two-group distribution, O&R p. 413): for a strictly concave `f` and `0 ≤ h < h'`,
`f(w̄ + h') + f(w̄ − h') < f(w̄ + h) + f(w̄ − h)`. -/
theorem spread_lowers_average {f : ℝ → ℝ} {W : Set ℝ} (hconc : StrictConcaveOn ℝ W f)
    {wbar h h' : ℝ} (hh : 0 ≤ h) (hhh : h < h') (hp : wbar + h' ∈ W) (hm : wbar - h' ∈ W) :
    f (wbar + h') + f (wbar - h') < f (wbar + h) + f (wbar - h) := by
  have hh' : 0 < h' := lt_of_le_of_lt hh hhh
  have hne : wbar + h' ≠ wbar - h' := by intro e; linarith
  set t := (h' + h) / (2 * h') with ht
  have ht0 : 0 < t := by rw [ht]; positivity
  have ht1 : 0 < 1 - t := by
    rw [ht, sub_pos, div_lt_one (by positivity)]; linarith
  have e1 : t * (wbar + h') + (1 - t) * (wbar - h') = wbar + h := by
    rw [ht]; field_simp; ring
  have e2 : (1 - t) * (wbar + h') + t * (wbar - h') = wbar - h := by
    rw [ht]; field_simp; ring
  have a1 := hconc.2 hp hm hne ht0 ht1 (by ring)
  have a2 := hconc.2 hp hm hne ht1 ht0 (by ring)
  simp only [smul_eq_mul] at a1 a2
  rw [e1] at a1
  rw [e2] at a2
  linarith

/-- For `π(I) = I/(1+I)` the p. 413 condition holds everywhere: `Φ(I) = (Z/R)I/(1+I) − I(1+I)` is
strictly concave on `[0, ∞)` (`Z ≥ 0`, `R > 0`). -/
theorem ratProb_inflow_strictConcave {Z R : ℝ} (hZ : 0 ≤ Z) (hR : 0 < R) :
    StrictConcaveOn ℝ (Ici 0) (inflowFn ratProb Z R) := by
  have hform : ∀ I : ℝ, 0 ≤ I →
      inflowFn ratProb Z R I = Z / R * (1 - 1 / (1 + I)) - I * (1 + I) := by
    intro I hI
    have : (1 + I) ≠ 0 := by positivity
    unfold inflowFn; simp only [ratProb]
    field_simp
    ring
  refine ⟨convex_Ici 0, ?_⟩
  intro x hx y hy hne a b ha hb hab
  have hx0 : (0 : ℝ) ≤ x := hx
  have hy0 : (0 : ℝ) ≤ y := hy
  have hxy : 0 ≤ a • x + b • y := by simp only [smul_eq_mul]; positivity
  rw [hform x hx0, hform y hy0, hform _ hxy]
  simp only [smul_eq_mul]
  have hb' : b = 1 - a := by linarith
  subst hb'
  -- `1/(1+·)` is convex and `I(1+I)` strictly convex
  have hconv : 1 / (1 + (a * x + (1 - a) * y)) ≤ a * (1 / (1 + x)) + (1 - a) * (1 / (1 + y)) := by
    rw [div_le_iff₀ (by positivity)]
    have hu : 0 < 1 + x := by linarith
    have hv : 0 < 1 + y := by linarith
    rw [show a * (1 / (1 + x)) + (1 - a) * (1 / (1 + y)) =
      (a * (1 + y) + (1 - a) * (1 + x)) / ((1 + x) * (1 + y)) by field_simp]
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith [mul_nonneg (mul_nonneg ha.le hb.le) (sq_nonneg (x - y))]
  have hsq : a * (x * (1 + x)) + (1 - a) * (y * (1 + y)) >
      (a * x + (1 - a) * y) * (1 + (a * x + (1 - a) * y)) := by
    have : 0 < (x - y) ^ 2 := by
      have : x - y ≠ 0 := sub_ne_zero.2 hne
      positivity
    nlinarith [mul_pos ha hb]
  have hZR : 0 ≤ Z / R := div_nonneg hZ hR.le
  nlinarith [mul_le_mul_of_nonneg_left hconv hZR]

/-- The hyperbolic technology `π(I) = I/(c + I)`, `π'(I) = c/(c + I)²`, `c > 0`. -/
noncomputable def hypProb (c : ℝ) (hc : 0 < c) : SuccessProb where
  prob I := I / (c + I)
  dprob I := c / (c + I) ^ 2
  hasDerivAt I hI := by
    have h1 : c + I ≠ 0 := by positivity
    have := (hasDerivAt_id' I).div ((hasDerivAt_id' I).const_add c) h1
    exact this.congr_deriv (by field_simp; ring)
  dprob_pos I hI := by positivity
  dprob_strictAnti := by
    intro a ha b hb hab
    have ha' : (0 : ℝ) ≤ a := ha
    apply div_lt_div_of_pos_left hc (by positivity)
    exact pow_lt_pow_left₀ (by linarith) (by linarith) two_ne_zero
  prob_zero := by simp
  prob_le_one I hI := by
    rw [div_le_one (by positivity)]
    linarith

/-- A mixture `aπ₁ + (1 − a)π₂` of two technologies is a technology. -/
noncomputable def SuccessProb.mix (T₁ T₂ : SuccessProb) (a : ℝ) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    SuccessProb where
  prob I := a * T₁.prob I + (1 - a) * T₂.prob I
  dprob I := a * T₁.dprob I + (1 - a) * T₂.dprob I
  hasDerivAt I hI := ((T₁.hasDerivAt I hI).const_mul a).add ((T₂.hasDerivAt I hI).const_mul (1 - a))
  dprob_pos I hI := by
    have h1 := T₁.dprob_pos I hI
    have h2 := T₂.dprob_pos I hI
    rcases ha0.lt_or_eq with ha | ha
    · nlinarith [mul_pos ha h1, mul_nonneg (sub_nonneg.2 ha1) h2.le]
    · rw [← ha]; linarith
  dprob_strictAnti := by
    intro x hx y hy hxy
    have h1 := T₁.dprob_strictAnti hx hy hxy
    have h2 := T₂.dprob_strictAnti hx hy hxy
    change a * T₁.dprob y + (1 - a) * T₂.dprob y < a * T₁.dprob x + (1 - a) * T₂.dprob x
    rcases ha1.lt_or_eq with ha | ha
    · nlinarith [mul_lt_mul_of_pos_left h2 (sub_pos.2 ha),
        mul_le_mul_of_nonneg_left h1.le ha0]
    · rw [ha]; linarith
  prob_zero := by simp [T₁.prob_zero, T₂.prob_zero]
  prob_le_one I hI := by
    have := T₁.prob_le_one I hI
    have := T₂.prob_le_one I hI
    nlinarith

/-- The technology `π(I) = 0.3·I/(0.01 + I) + 0.7·I/(1 + I)` used against p. 413. -/
noncomputable def mixTech : SuccessProb :=
  SuccessProb.mix (hypProb (1 / 100) (by norm_num)) (hypProb 1 one_pos) (3 / 10) (by norm_num)
    (by norm_num)

/-- **Counterexample to the p. 413 presumption.** With `π(I) = 0.3·I/(0.01+I) + 0.7·I/(1+I)`,
`Z = 3/2`, `r = 0`: wealths `w₁ = 27/11000` and `w₃ = 2043447/28958800` (both in the borrowing
regime) have equilibrium investments `1/10` and `3/25`, but the mean wealth has equilibrium
investment strictly below `(1/10 + 3/25)/2`. So `I(·)` is not concave on `[w₁, w₃]`, and splitting
entrepreneurs evenly between `w₁` and `w₃` gives *higher* average investment than giving all of
them the mean wealth. -/
theorem p413_counterexample :
    0 < (27 / 11000 : ℝ) ∧ (27 / 11000 : ℝ) < 2043447 / 28958800 ∧
      1 < mixTech.dprob (2043447 / 28958800) * (3 / 2) ∧
      eqmI mixTech (3 / 2) 1 (27 / 11000) = 1 / 10 ∧
      eqmI mixTech (3 / 2) 1 (2043447 / 28958800) = 3 / 25 ∧
      eqmI mixTech (3 / 2) 1 ((27 / 11000 + 2043447 / 28958800) / 2) <
        (eqmI mixTech (3 / 2) 1 (27 / 11000) + eqmI mixTech (3 / 2) 1 (2043447 / 28958800)) / 2 ∧
      ¬ ConcaveOn ℝ (Icc (27 / 11000 : ℝ) (2043447 / 28958800)) (eqmI mixTech (3 / 2) 1) := by
  have g1 : eqmWealth mixTech (3 / 2) 1 (1 / 10) = 27 / 11000 := by
    unfold eqmWealth inflowFn; simp only [mixTech, SuccessProb.mix, hypProb]; norm_num
  have g3 : eqmWealth mixTech (3 / 2) 1 (3 / 25) = 2043447 / 28958800 := by
    unfold eqmWealth inflowFn; simp only [mixTech, SuccessProb.mix, hypProb]; norm_num
  have gJ : eqmWealth mixTech (3 / 2) 1 (11 / 100) = 8371429 / 226543600 := by
    unfold eqmWealth inflowFn; simp only [mixTech, SuccessProb.mix, hypProb]; norm_num
  have hd3 : 1 < mixTech.dprob (2043447 / 28958800) * (3 / 2) := by
    simp only [mixTech, SuccessProb.mix, hypProb]; norm_num
  have e1 : eqmI mixTech (3 / 2) 1 (27 / 11000) = 1 / 10 :=
    eqmI_eq mixTech one_pos (by norm_num) (by norm_num)
      ((eqmGap_eq_zero_iff_wealth mixTech one_pos (by norm_num)).2 g1.symm)
  have e3 : eqmI mixTech (3 / 2) 1 (2043447 / 28958800) = 3 / 25 :=
    eqmI_eq mixTech one_pos (by norm_num) (by norm_num)
      ((eqmGap_eq_zero_iff_wealth mixTech one_pos (by norm_num)).2 g3.symm)
  set m : ℝ := (27 / 11000 + 2043447 / 28958800) / 2 with hm
  have hm0 : 0 < m := by rw [hm]; norm_num
  have hmI : 1 < mixTech.dprob m * (3 / 2) := by
    have := mixTech.dprob_le_of_le hm0.le (show m ≤ 2043447 / 28958800 by rw [hm]; norm_num)
    linarith
  obtain ⟨hIm, hgm⟩ := eqmI_spec mixTech one_pos hm0 hmI
  have hgJ : eqmGap mixTech (3 / 2) 1 (8371429 / 226543600) (11 / 100) = 0 :=
    (eqmGap_eq_zero_iff_wealth mixTech one_pos (by norm_num)).2 gJ.symm
  have hlt : eqmI mixTech (3 / 2) 1 m < 11 / 100 :=
    eqm_strictMono_wealth mixTech one_pos (by norm_num) (by rw [hm]; norm_num) hIm
      (by norm_num) hgm hgJ
  have hmain : eqmI mixTech (3 / 2) 1 m <
      (eqmI mixTech (3 / 2) 1 (27 / 11000) + eqmI mixTech (3 / 2) 1 (2043447 / 28958800)) / 2 := by
    rw [e1, e3]; linarith
  refine ⟨by norm_num, by norm_num, hd3, e1, e3, hmain, ?_⟩
  intro hc
  have := hc.2 (show (27 / 11000 : ℝ) ∈ Icc (27 / 11000 : ℝ) (2043447 / 28958800) by
      constructor <;> norm_num)
    (show (2043447 / 28958800 : ℝ) ∈ Icc (27 / 11000 : ℝ) (2043447 / 28958800) by
      constructor <;> norm_num)
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num)
  simp only [smul_eq_mul] at this
  have e : (1 / 2 : ℝ) * (27 / 11000) + 1 / 2 * (2043447 / 28958800) = m := by rw [hm]; ring
  rw [e] at this
  linarith

/-! ## §6.4.3: implications for consumption insurance (p. 416) -/

/-- Date-2 consumption after success, `Z − P(Z) + R(Y₁ − I)`, O&R p. 416. -/
def c2Success (Z R Y₁ PZ I : ℝ) : ℝ := Z - PZ + R * (Y₁ - I)

/-- Date-2 consumption after failure, `−P(0) + R(Y₁ − I)`, O&R p. 416. -/
def c2Failure (R Y₁ P0 I : ℝ) : ℝ := -P0 + R * (Y₁ - I)

/-- Expected utility `π(I)u(C₂ˢ) + (1 − π(I))u(C₂ᶠ)` of a risk-averse entrepreneur,
O&R p. 416. -/
noncomputable def insuredEU (T : SuccessProb) (u : ℝ → ℝ) (Z R Y₁ PZ P0 I : ℝ) : ℝ :=
  T.prob I * u (c2Success Z R Y₁ PZ I) + (1 - T.prob I) * u (c2Failure R Y₁ P0 I)

/-- The first-best insurance contract `P(Z) = (1 − π(Ī))Z`, `P(0) = −π(Ī)Z` makes insurers
break even at `Ī` and equalises consumption at `π(Ī)Z + R(Y₁ − Ī)`, O&R p. 416. -/
theorem firstBest_insurance (T : SuccessProb) (Z R Y₁ Ibar : ℝ) :
    T.prob Ibar * ((1 - T.prob Ibar) * Z) + (1 - T.prob Ibar) * (-(T.prob Ibar * Z)) = 0 ∧
      c2Success Z R Y₁ ((1 - T.prob Ibar) * Z) Ibar = T.prob Ibar * Z + R * (Y₁ - Ibar) ∧
      c2Failure R Y₁ (-(T.prob Ibar * Z)) Ibar = T.prob Ibar * Z + R * (Y₁ - Ibar) := by
  unfold c2Success c2Failure
  refine ⟨by ring, by ring, by ring⟩

/-- **The first-best insurance contract is the full-information optimum** (O&R p. 416): if
investment were contractible, then for any `I ≥ 0` and any contract on which insurers do not
lose, expected utility is at most `u(π(Ī)Z + R(Y₁ − Ī))`, with equality only at `I = Ī` with
full insurance. Here `u` is strictly increasing and strictly concave. -/
theorem firstBest_insurance_optimal {T : SuccessProb} {u : ℝ → ℝ} (hu : StrictMono u)
    (hc : StrictConcaveOn ℝ univ u) {Z R Y₁ Ibar : ℝ} (hZ : 0 < Z) (hIb : 0 < Ibar)
    (hIbar : T.dprob Ibar * Z = R) {I PZ P0 : ℝ} (hI : 0 ≤ I)
    (hprofit : 0 ≤ T.prob I * PZ + (1 - T.prob I) * P0) :
    insuredEU T u Z R Y₁ PZ P0 I ≤ u (T.prob Ibar * Z + R * (Y₁ - Ibar)) ∧
      (insuredEU T u Z R Y₁ PZ P0 I = u (T.prob Ibar * Z + R * (Y₁ - Ibar)) →
        I = Ibar ∧ c2Success Z R Y₁ PZ I = c2Failure R Y₁ P0 I) := by
  set p := T.prob I with hp
  have hp0 : 0 ≤ p := T.prob_nonneg hI
  have hp1 : p < 1 := T.prob_lt_one hI
  set a := c2Success Z R Y₁ PZ I
  set b := c2Failure R Y₁ P0 I
  have hmean : p * a + (1 - p) * b ≤ T.prob I * Z - R * (I - Y₁) := by
    simp only [a, b, c2Success, c2Failure]; rw [← hp]; nlinarith
  have hno : netOutput T Z R Y₁ I ≤ netOutput T Z R Y₁ Ibar := by
    rcases eq_or_ne I Ibar with h | h
    · rw [h]
    · exact (efficient_investment_maximises hZ hIb.le hIbar hI h).le
  have hnoI : T.prob Ibar * Z + R * (Y₁ - Ibar) = netOutput T Z R Y₁ Ibar := by
    unfold netOutput; ring
  have hjensen : p * u a + (1 - p) * u b ≤ u (p * a + (1 - p) * b) := by
    have := hc.concaveOn.2 (mem_univ a) (mem_univ b) hp0 (by linarith : 0 ≤ 1 - p)
      (by ring)
    simpa [smul_eq_mul] using this
  have hmono : u (p * a + (1 - p) * b) ≤ u (T.prob Ibar * Z + R * (Y₁ - Ibar)) := by
    apply hu.monotone
    rw [hnoI]; unfold netOutput at hno ⊢; linarith
  refine ⟨by unfold insuredEU; exact hjensen.trans hmono, ?_⟩
  intro heq
  unfold insuredEU at heq
  have hIeq : I = Ibar := by
    by_contra hne
    have hlt := efficient_investment_maximises (Y₁ := Y₁) hZ hIb.le hIbar hI hne
    have : u (p * a + (1 - p) * b) < u (T.prob Ibar * Z + R * (Y₁ - Ibar)) := by
      apply hu
      rw [hnoI]; unfold netOutput at hlt ⊢; linarith
    linarith
  refine ⟨hIeq, ?_⟩
  by_contra hab
  have hpp : 0 < p := by rw [hp, hIeq]; exact T.prob_pos hIb
  have := hc.2 (mem_univ a) (mem_univ b) hab hpp (by linarith : 0 < 1 - p) (by ring)
  simp only [smul_eq_mul] at this
  linarith

/-- **Under full insurance the entrepreneur does not invest** (O&R p. 416): if a contract makes
consumption state-independent (`Z − P(Z) = −P(0)`), expected utility is strictly decreasing in
`I`, so `I = 0` is the unique optimal investment. -/
theorem fullInsurance_zero_investment {T : SuccessProb} {u : ℝ → ℝ} (hu : StrictMono u)
    {Z R Y₁ PZ P0 : ℝ} (hR : 0 < R) (hfull : Z - PZ = -P0) {I : ℝ} (hI : 0 < I) :
    insuredEU T u Z R Y₁ PZ P0 I < insuredEU T u Z R Y₁ PZ P0 0 := by
  have hs : ∀ J, c2Success Z R Y₁ PZ J = c2Failure R Y₁ P0 J := by
    intro J; unfold c2Success c2Failure; linarith
  have hval : ∀ J, insuredEU T u Z R Y₁ PZ P0 J = u (c2Failure R Y₁ P0 J) := by
    intro J; unfold insuredEU; rw [hs J]; ring
  rw [hval, hval]
  apply hu
  unfold c2Failure
  nlinarith

/-- **The first-best insurance contract is not sustainable under asymmetric information**
(O&R p. 416): it gives full insurance, so the entrepreneur invests nothing, and then insurers'
expected profit is `−π(Ī)Z < 0`. -/
theorem firstBest_insurance_unsustainable {T : SuccessProb} {u : ℝ → ℝ} (hu : StrictMono u)
    {Z R Y₁ Ibar : ℝ} (hR : 0 < R) (hZ : 0 < Z) (hIb : 0 < Ibar) :
    (∀ I, 0 < I → insuredEU T u Z R Y₁ ((1 - T.prob Ibar) * Z) (-(T.prob Ibar * Z)) I <
        insuredEU T u Z R Y₁ ((1 - T.prob Ibar) * Z) (-(T.prob Ibar * Z)) 0) ∧
      T.prob 0 * ((1 - T.prob Ibar) * Z) + (1 - T.prob 0) * (-(T.prob Ibar * Z)) < 0 := by
  refine ⟨fun I hI => fullInsurance_zero_investment hu hR (by ring) hI, ?_⟩
  rw [T.prob_zero]
  have := T.prob_pos hIb
  nlinarith

/-- **Positive investment requires bearing consumption risk** (O&R p. 416): if investing some
`I > 0` is weakly better than not investing, the contract cannot equalise consumption. -/
theorem positive_investment_leaves_risk {T : SuccessProb} {u : ℝ → ℝ} (hu : StrictMono u)
    {Z R Y₁ PZ P0 I : ℝ} (hR : 0 < R) (hI : 0 < I)
    (hopt : insuredEU T u Z R Y₁ PZ P0 0 ≤ insuredEU T u Z R Y₁ PZ P0 I) :
    c2Success Z R Y₁ PZ I ≠ c2Failure R Y₁ P0 I := by
  intro h
  have hfull : Z - PZ = -P0 := by unfold c2Success c2Failure at h; linarith
  have := fullInsurance_zero_investment (T := T) (Y₁ := Y₁) hu hR hfull hI
  linarith

/-! ### The optimal incentive-compatible insurance contract (p. 416)

The book calls the optimal contract under risk aversion "messy" and asserts that it leaves
consumption subject to production uncertainty and investment below the first best. We set the
problem up precisely: a contract `(P(Z), P(0))` with payments bounded by some `M` (the book is
silent on bounds; the results hold for every `M ≥ |Z|`), the entrepreneur's choice `I ∈ [0, Y₁]`
maximising his expected utility (incentive compatibility, as a global optimum, not a first-order
condition), and zero expected profit for insurers at the induced `I`. We prove: an optimal
contract **exists**; its value is **strictly below** the first best (so the trade-off is real);
under any implementable contract consumption is risky **iff** investment is positive; at an
interior optimum the entrepreneur's first-order condition holds. The book's claim that the
optimum leaves consumption risky is **false in general**: for CARA utility `−e^{−kc}` and
`π(I) = 1 − e^{−I}` with `kR ≥ 1`, no contract whatever induces positive investment, so every
optimal contract has `I = 0` and riskless consumption. -/

/-- An implementable insurance contract with payments bounded by `M` (O&R p. 416): `I ∈ [0, Y₁]`
maximises the entrepreneur's expected utility over `[0, Y₁]` (incentive compatibility) and
insurers break even at `I`. -/
def RaImplementable (T : SuccessProb) (u : ℝ → ℝ) (Z R Y₁ M PZ P0 I : ℝ) : Prop :=
  |PZ| ≤ M ∧ |P0| ≤ M ∧ 0 ≤ I ∧ I ≤ Y₁ ∧
    (∀ J, 0 ≤ J → J ≤ Y₁ → insuredEU T u Z R Y₁ PZ P0 J ≤ insuredEU T u Z R Y₁ PZ P0 I) ∧
    T.prob I * PZ + (1 - T.prob I) * P0 = 0

/-- **Existence of an optimal incentive-compatible insurance contract** (O&R p. 416), for any
payment bound `M ≥ |Z|`, when `u` is monotone and concave (hence continuous). The feasible set is
compact: the incentive constraint is a closed condition (the graph of the entrepreneur's
argmax is closed). -/
theorem ra_optimal_contract_exists (T : SuccessProb) {u : ℝ → ℝ} (hmono : Monotone u)
    (hconc : ConcaveOn ℝ univ u) {Z R Y₁ M : ℝ} (hR : 0 < R) (hY : 0 ≤ Y₁) (hM : |Z| ≤ M) :
    ∃ PZ P0 I, RaImplementable T u Z R Y₁ M PZ P0 I ∧
      ∀ PZ' P0' I', RaImplementable T u Z R Y₁ M PZ' P0' I' →
        insuredEU T u Z R Y₁ PZ' P0' I' ≤ insuredEU T u Z R Y₁ PZ P0 I := by
  have hu : Continuous u := continuousOn_univ.1 (hconc.continuousOn isOpen_univ)
  have hM0 : 0 ≤ M := (abs_nonneg Z).trans hM
  set pc : ℝ → ℝ := fun I => T.prob (max I 0) with hpc
  have hpcc : Continuous pc :=
    T.continuousOn_prob.comp_continuous (continuous_id.max continuous_const)
      (fun x => mem_Ici.2 (le_max_right x 0))
  have hpc_eq : ∀ I, 0 ≤ I → pc I = T.prob I := fun I hI => by simp [hpc, max_eq_left hI]
  set E : ℝ × ℝ × ℝ → ℝ → ℝ := fun x J =>
    pc J * u (Z - x.1 + R * (Y₁ - J)) + (1 - pc J) * u (-x.2.1 + R * (Y₁ - J)) with hE
  have hE_eq : ∀ x J, 0 ≤ J → E x J = insuredEU T u Z R Y₁ x.1 x.2.1 J := by
    intro x J hJ
    simp only [hE, insuredEU, c2Success, c2Failure, hpc_eq J hJ]
  have hEc : ∀ J, Continuous fun x : ℝ × ℝ × ℝ => E x J := by
    intro J
    simp only [hE]
    fun_prop
  have hEd : Continuous fun x : ℝ × ℝ × ℝ => E x x.2.2 := by
    simp only [hE]
    have := hpcc
    fun_prop
  set S : Set (ℝ × ℝ × ℝ) :=
    {x | |x.1| ≤ M} ∩ {x | |x.2.1| ≤ M} ∩ {x | 0 ≤ x.2.2} ∩ {x | x.2.2 ≤ Y₁} ∩
      (⋂ J ∈ Icc (0 : ℝ) Y₁, {x | E x J ≤ E x x.2.2}) ∩
      {x | pc x.2.2 * x.1 + (1 - pc x.2.2) * x.2.1 = 0} with hS
  have hSclosed : IsClosed S := by
    refine (((((isClosed_le (by fun_prop) continuous_const).inter
      (isClosed_le (by fun_prop) continuous_const)).inter
      (isClosed_le continuous_const (by fun_prop))).inter
      (isClosed_le (by fun_prop) continuous_const)).inter ?_).inter ?_
    · exact isClosed_biInter fun J _ => isClosed_le (hEc J) hEd
    · exact isClosed_eq (by have := hpcc; fun_prop) continuous_const
  have hSsub : S ⊆ Icc (-M) M ×ˢ Icc (-M) M ×ˢ Icc 0 Y₁ := by
    intro x hx
    obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, _⟩, _⟩ := hx
    exact ⟨abs_le.1 h1, abs_le.1 h2, h3, h4⟩
  have hScpt : IsCompact S :=
    (isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)).of_isClosed_subset hSclosed hSsub
  have hmemS : ∀ x : ℝ × ℝ × ℝ, x ∈ S ↔ RaImplementable T u Z R Y₁ M x.1 x.2.1 x.2.2 := by
    intro x
    constructor
    · rintro ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩
      refine ⟨h1, h2, h3, h4, ?_, ?_⟩
      · intro J hJ hJY
        have := mem_iInter₂.1 h5 J ⟨hJ, hJY⟩
        simp only [Set.mem_ofPred_eq] at this
        rwa [hE_eq x J hJ, hE_eq x x.2.2 h3] at this
      · simp only [Set.mem_ofPred_eq] at h6; rwa [hpc_eq _ h3] at h6
    · rintro ⟨h1, h2, h3, h4, h5, h6⟩
      refine ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, ?_⟩, ?_⟩
      · refine mem_iInter₂.2 fun J hJ => ?_
        simp only [Set.mem_ofPred_eq]
        rw [hE_eq x J hJ.1, hE_eq x x.2.2 h3]
        exact h5 J hJ.1 hJ.2
      · simp only [Set.mem_ofPred_eq]; rw [hpc_eq _ h3]; exact h6
  -- the full-insurance, no-investment contract `(Z, 0)` is implementable
  have h0 : RaImplementable T u Z R Y₁ M Z 0 0 := by
    refine ⟨hM, by simpa using hM0, le_rfl, hY, ?_, by simp [T.prob_zero]⟩
    intro J hJ _
    unfold insuredEU c2Success c2Failure
    rw [T.prob_zero]
    have : u (-0 + R * (Y₁ - J)) ≤ u (-0 + R * (Y₁ - 0)) := hmono (by nlinarith)
    simp only [sub_self, zero_add, neg_zero, sub_zero, zero_mul, one_mul] at this ⊢
    nlinarith [this]
  obtain ⟨x, hx, hmax⟩ := hScpt.exists_isMaxOn ⟨(Z, 0, 0), (hmemS _).2 h0⟩ hEd.continuousOn
  have hximp := (hmemS x).1 hx
  refine ⟨x.1, x.2.1, x.2.2, hximp, ?_⟩
  intro PZ' P0' I' himp
  have hmem : (PZ', P0', I') ∈ S := (hmemS _).2 himp
  have := hmax hmem
  simp only [Set.mem_ofPred_eq] at this
  rw [hE_eq _ _ himp.2.2.1, hE_eq _ _ hximp.2.2.1] at this
  exact this

/-- **The optimum is strictly worse than the first best** (O&R p. 416: the contract trades off
efficient production against efficient risk sharing): every implementable contract gives
expected utility strictly below `u(π(Ī)Z + R(Y₁ − Ī))`. -/
theorem ra_below_first_best {T : SuccessProb} {u : ℝ → ℝ} (hu : StrictMono u)
    (hc : StrictConcaveOn ℝ univ u) {Z R Y₁ M Ibar PZ P0 I : ℝ} (hR : 0 < R) (hZ : 0 < Z)
    (hIb : 0 < Ibar) (hIbar : T.dprob Ibar * Z = R)
    (himp : RaImplementable T u Z R Y₁ M PZ P0 I) :
    insuredEU T u Z R Y₁ PZ P0 I < u (T.prob Ibar * Z + R * (Y₁ - Ibar)) := by
  obtain ⟨_, _, hI0, hIY, hic, hzp⟩ := himp
  obtain ⟨hle, heq⟩ := firstBest_insurance_optimal (T := T) hu hc hZ hIb hIbar (Y₁ := Y₁)
    (PZ := PZ) (P0 := P0) hI0 (by rw [hzp])
  refine lt_of_le_of_ne hle fun h => ?_
  obtain ⟨hI, hfull⟩ := heq h
  have hfull' : Z - PZ = -P0 := by unfold c2Success c2Failure at hfull; linarith
  have hIpos : 0 < I := hI ▸ hIb
  have := fullInsurance_zero_investment (T := T) (Y₁ := Y₁) hu hR hfull' hIpos
  have := hic 0 le_rfl (hI0.trans hIY)
  linarith

/-- **Consumption is risky iff investment is positive** under any implementable contract
(the correct form of O&R p. 416's "leaves domestic consumption subject to production
uncertainty"): the bad-state probability is positive and the two consumptions differ exactly
when `I > 0`. -/
theorem ra_risky_iff_invest {T : SuccessProb} {u : ℝ → ℝ} (hu : StrictMono u)
    {Z R Y₁ M PZ P0 I : ℝ} (hR : 0 < R) (himp : RaImplementable T u Z R Y₁ M PZ P0 I) :
    (0 < T.prob I ∧ c2Success Z R Y₁ PZ I ≠ c2Failure R Y₁ P0 I) ↔ 0 < I := by
  obtain ⟨_, _, hI0, hIY, hic, _⟩ := himp
  constructor
  · rintro ⟨hp, _⟩
    rcases hI0.lt_or_eq with h | h
    · exact h
    · rw [← h, T.prob_zero] at hp; exact absurd hp (lt_irrefl 0)
  · intro hI
    exact ⟨T.prob_pos hI, positive_investment_leaves_risk hu hR hI (hic 0 le_rfl (hI0.trans hIY))⟩

/-- **The entrepreneur's first-order condition** at an implementable contract with interior
investment `0 < I < Y₁` (O&R p. 410, 416): if `u` has derivatives `u'(C₂ˢ)`, `u'(C₂ᶠ)`, then
`π'(I)[u(C₂ˢ) − u(C₂ᶠ)] = R[π(I)u'(C₂ˢ) + (1 − π(I))u'(C₂ᶠ)]`. -/
theorem ra_ic_foc {T : SuccessProb} {u : ℝ → ℝ} {Z R Y₁ M PZ P0 I du₁ du₂ : ℝ}
    (himp : RaImplementable T u Z R Y₁ M PZ P0 I) (hI : 0 < I) (hIY : I < Y₁)
    (h₁ : HasDerivAt u du₁ (c2Success Z R Y₁ PZ I))
    (h₂ : HasDerivAt u du₂ (c2Failure R Y₁ P0 I)) :
    T.dprob I * (u (c2Success Z R Y₁ PZ I) - u (c2Failure R Y₁ P0 I)) =
      R * (T.prob I * du₁ + (1 - T.prob I) * du₂) := by
  obtain ⟨_, _, _, _, hic, _⟩ := himp
  have hs : HasDerivAt (fun J => c2Success Z R Y₁ PZ J) (-R) I := by
    unfold c2Success
    have := (((hasDerivAt_id' I).const_sub Y₁).const_mul R).const_add (Z - PZ)
    exact this.congr_deriv (by ring)
  have hf : HasDerivAt (fun J => c2Failure R Y₁ P0 J) (-R) I := by
    unfold c2Failure
    have := (((hasDerivAt_id' I).const_sub Y₁).const_mul R).const_add (-P0)
    exact this.congr_deriv (by ring)
  have hEU : HasDerivAt (fun J => insuredEU T u Z R Y₁ PZ P0 J)
      (T.dprob I * u (c2Success Z R Y₁ PZ I) + T.prob I * (du₁ * -R) +
        (-T.dprob I * u (c2Failure R Y₁ P0 I) + (1 - T.prob I) * (du₂ * -R))) I := by
    have hp := T.hasDerivAt I hI.le
    have a := hp.mul (h₁.comp I hs)
    have b := (hp.const_sub 1).mul (h₂.comp I hf)
    exact a.add b
  have hmax : IsLocalMax (fun J => insuredEU T u Z R Y₁ PZ P0 J) I := by
    apply IsMaxOn.isLocalMax (s := Icc 0 Y₁)
    · intro J hJ; exact hic J hJ.1 hJ.2
    · exact Icc_mem_nhds hI hIY
  have := hmax.hasDerivAt_eq_zero hEU
  linarith

/-- The exponential technology `π(I) = 1 − e^{−I}`, `π'(I) = e^{−I}`. -/
noncomputable def expProb : SuccessProb where
  prob I := 1 - Real.exp (-I)
  dprob I := Real.exp (-I)
  hasDerivAt I _ := by
    have := ((Real.hasDerivAt_exp (-I)).comp I (hasDerivAt_neg I)).const_sub 1
    exact this.congr_deriv (by ring)
  dprob_pos I _ := Real.exp_pos _
  dprob_strictAnti := by
    intro a _ b _ hab
    exact Real.exp_lt_exp.2 (by linarith)
  prob_zero := by simp
  prob_le_one I _ := by have := Real.exp_pos (-I); linarith

/-- CARA utility `u(c) = −e^{−kc}` (`k > 0`) is strictly increasing and strictly concave. -/
theorem cara_props {k : ℝ} (hk : 0 < k) :
    StrictMono (fun c : ℝ => -Real.exp (-k * c)) ∧
      StrictConcaveOn ℝ univ (fun c : ℝ => -Real.exp (-k * c)) := by
  constructor
  · intro x y hxy
    simp only [neg_lt_neg_iff]
    exact Real.exp_lt_exp.2 (by nlinarith)
  · refine ⟨convex_univ, ?_⟩
    intro x _ y _ hne a b ha hb hab
    have hne' : -k * x ≠ -k * y := by
      intro h; apply hne
      have := mul_left_cancel₀ (neg_ne_zero.2 hk.ne') h
      exact this
    have := strictConvexOn_exp.2 (mem_univ (-k * x)) (mem_univ (-k * y)) hne' ha hb hab
    simp only [smul_eq_mul] at this ⊢
    have e : a * (-k * x) + b * (-k * y) = -k * (a * x + b * y) := by ring
    rw [e] at this
    linarith

/-- **Counterexample to O&R p. 416** ("leaves domestic consumption subject to production
uncertainty"): with CARA utility `−e^{−kc}`, `π(I) = 1 − e^{−I}` and `kR ≥ 1`, *every* contract
`(P(Z), P(0))` makes `I = 0` the entrepreneur's unique best choice. Hence every implementable
(in particular every optimal) contract has `I = 0`, and consumption is riskless. -/
theorem cara_no_investment {k Z R Y₁ PZ P0 J : ℝ} (hkR : 1 ≤ k * R) (hJ : 0 < J) :
    insuredEU expProb (fun c => -Real.exp (-k * c)) Z R Y₁ PZ P0 J <
      insuredEU expProb (fun c => -Real.exp (-k * c)) Z R Y₁ PZ P0 0 := by
  unfold insuredEU c2Success c2Failure
  simp only [expProb, neg_zero, Real.exp_zero, sub_self, zero_mul, one_mul, sub_zero, zero_add]
  have h1 : 0 < 1 - Real.exp (-J) := by
    have := Real.exp_lt_exp.2 (show -J < 0 by linarith); rw [Real.exp_zero] at this; linarith
  have h2 : Real.exp (-J) * Real.exp (-k * (-P0 + R * (Y₁ - J))) =
      Real.exp (-k * (-P0 + R * Y₁)) * Real.exp ((k * R - 1) * J) := by
    rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  have h3 : 1 ≤ Real.exp ((k * R - 1) * J) :=
    Real.one_le_exp (mul_nonneg (by linarith) hJ.le)
  have h4 : 0 < Real.exp (-k * (Z - PZ + R * (Y₁ - J))) := Real.exp_pos _
  have h5 : 0 < Real.exp (-k * (-P0 + R * Y₁)) := Real.exp_pos _
  nlinarith [mul_pos h1 h4, mul_le_mul_of_nonneg_left h3 h5.le]

/-- Consequently, in the CARA–exponential example every implementable contract induces `I = 0`
(no production risk), although the first-best investment `Ī = log(Z/R)` is positive for `Z > R`.
-/
theorem cara_implementable_zero {k Z R Y₁ M PZ P0 I : ℝ} (hkR : 1 ≤ k * R)
    (himp : RaImplementable expProb (fun c => -Real.exp (-k * c)) Z R Y₁ M PZ P0 I) :
    I = 0 := by
  obtain ⟨_, _, hI0, hIY, hic, _⟩ := himp
  by_contra hne
  have hI : 0 < I := lt_of_le_of_ne hI0 (Ne.symm hne)
  have := cara_no_investment (Z := Z) (Y₁ := Y₁) (PZ := PZ) (P0 := P0) hkR hI
  have := hic 0 le_rfl (hI0.trans hIY)
  linarith

/-- In the CARA–exponential example the first-best investment is `Ī = log(Z/R) > 0` (`Z > R`). -/
theorem expProb_Ibar {Z R : ℝ} (hR : 0 < R) (hZR : R < Z) :
    0 < Real.log (Z / R) ∧ expProb.dprob (Real.log (Z / R)) * Z = R := by
  have hZ : 0 < Z := hR.trans hZR
  refine ⟨Real.log_pos ((one_lt_div hR).2 hZR), ?_⟩
  simp only [expProb]
  rw [Real.exp_neg, Real.exp_log (div_pos hZ hR)]
  field_simp

/-- For `π(I) = I/(1+I)` the p. 413 claim holds: on every borrowing-regime wealth interval
equilibrium investment is strictly concave in wealth (so inequality lowers average
investment there). -/
theorem ratProb_eqmI_strictConcave {Z R wa wb : ℝ} (hZ : 0 ≤ Z) (hR : 0 < R) (hwa : 0 < wa)
    (hwab : wa ≤ wb) (hwb : R < ratProb.dprob wb * Z) :
    StrictConcaveOn ℝ (Icc wa wb) (eqmI ratProb Z R) := by
  obtain ⟨spec, _, _, _⟩ := eqmI_interval_facts ratProb hR hwa hwab hwb
  refine (eqmI_strictConcave_iff ratProb hR hwa hwab hwb).2 ?_
  exact (ratProb_inflow_strictConcave hZ hR).subset
    (fun x hx => mem_Ici.2 ((spec wa ⟨le_rfl, hwab⟩).1.le.trans hx.1)) (convex_Icc _ _)

/-! ## Exercise 4: collateral and government-debt overhang (p. 427) -/

/-- **Exercise 4(a): the curves with collateral `E₂`.** With `P(0) = E₂` the IC curve is
`P(Z) = Z + E₂ − R/π'(I)` and the ZP curve is `P(Z) = [R(I − Y₁) − (1 − π(I))E₂]/π(I)`; they cross
exactly where the text's curves cross with `Y₁` replaced by `Y₁ + E₂/R`. -/
theorem ex4a_curves (T : SuccessProb) {Z R Y₁ E₂ I : ℝ} (hR : 0 < R) (hI : 0 < I) :
    Z + E₂ - R / T.dprob I = (R * (I - Y₁) - (1 - T.prob I) * E₂) / T.prob I ↔
      eqmGap T Z R (Y₁ + E₂ / R) I = 0 := by
  have hp := (T.prob_pos hI).ne'
  unfold eqmGap icCurve zpCurve
  rw [sub_eq_zero]
  have e1 : (R * (I - Y₁) - (1 - T.prob I) * E₂) / T.prob I =
      R * (I - (Y₁ + E₂ / R)) / T.prob I + E₂ := by
    field_simp; ring
  rw [e1]
  constructor <;> intro h <;> linarith

/-- **Exercise 4(a): collateral raises investment** (and borrowing): the equilibrium with
collateral `E₂ > 0` has strictly higher investment than without. -/
theorem ex4a_collateral_raises_investment (T : SuccessProb) {Z R Y₁ E₂ I I' : ℝ} (hR : 0 < R)
    (hY : 0 ≤ Y₁) (hE : 0 < E₂) (hI : 0 < I) (hI' : 0 < I') (hg : eqmGap T Z R Y₁ I = 0)
    (hg' : eqmGap T Z R (Y₁ + E₂ / R) I' = 0) : I < I' := by
  have : 0 < E₂ / R := div_pos hE hR
  exact eqm_strictMono_wealth T hR (by linarith) (by linarith) hI hI' hg hg'

/-- **Exercise 4(a): enough collateral restores the first best.** If `Y₁ < Ī ≤ Y₁ + E₂/R`, the
riskless collateralised loan `P(Z) = P(0) = R(Ī − Y₁)`, `D = Ī − Y₁` respects limited liability,
lenders break even, the borrower's unique optimal response is `Ī`, and his payoff equals the
maximal net output plus `E₂`; no contract meeting lenders' participation does better. -/
theorem ex4a_large_collateral_first_best {T : SuccessProb} {Z R Y₁ E₂ Ibar : ℝ} (hR : 0 < R)
    (hY : Y₁ < Ibar) (hIb : 0 < Ibar) (hbig : Ibar ≤ Y₁ + E₂ / R) (hIbar : T.dprob Ibar * Z = R) :
    let c : Contract := ⟨R * (Ibar - Y₁), R * (Ibar - Y₁), Ibar - Y₁⟩
    c.P0 ≤ E₂ ∧ R * c.D = T.prob Ibar * c.PZ + (1 - T.prob Ibar) * c.P0 ∧
      IsBestResponse T Z R Y₁ E₂ c Ibar ∧ (∀ J, IsBestResponse T Z R Y₁ E₂ c J → J = Ibar) ∧
      borrowerPayoff T Z R Y₁ E₂ c Ibar = netOutput T Z R Y₁ Ibar + E₂ ∧
      ∀ (c' : Contract) (J : ℝ), 0 ≤ J → R * c'.D ≤ T.prob J * c'.PZ + (1 - T.prob J) * c'.P0 →
        borrowerPayoff T Z R Y₁ E₂ c' J ≤ netOutput T Z R Y₁ Ibar + E₂ := by
  intro c
  have hZ : 0 < Z := by
    have := T.dprob_pos Ibar hIb.le
    by_contra h; push Not at h; nlinarith
  have hstake : stake Z c = Z := by simp only [stake, c]; ring
  have hs : 0 < stake Z c := by rw [hstake]; exact hZ
  have hfoc : T.dprob Ibar * stake Z c = R := by rw [hstake]; exact hIbar
  have hW : Y₁ + c.D = Ibar := by simp only [c]; ring
  obtain ⟨hb, hu⟩ := bestResponse_of_foc (T := T) (R := R) (Y₁ := Y₁) (E := E₂) hs
    (by rw [hW]; exact hIb.le) hIb.le hfoc
  rw [hW, min_self] at hb hu
  refine ⟨?_, ?_, hb, hu, ?_, ?_⟩
  · simp only [c]
    have := (le_div_iff₀ hR).1 (by linarith : Ibar - Y₁ ≤ E₂ / R)
    linarith
  · simp only [c]; ring
  · unfold borrowerPayoff netOutput; simp only [c]; ring
  · intro c' J hJ hpart
    have h1 : borrowerPayoff T Z R Y₁ E₂ c' J ≤ netOutput T Z R Y₁ J + E₂ := by
      unfold borrowerPayoff netOutput; nlinarith
    rcases eq_or_ne J Ibar with h | h
    · subst h; exact h1
    · have := efficient_investment_maximises (Y₁ := Y₁) hZ hIb.le hIbar hJ h
      linarith

/-- **Exercise 4(b): the overhang equilibrium is the text's equilibrium with `Y₁` replaced by
`Y₁ − D^G/R`.** If each entrepreneur, taking the tax `τ` on success as given, is at the crossing
for payoff `Z − τ`, and the government budget `π(I)τ = D^G` balances, then `I` is the crossing
for payoff `Z` and wealth `Y₁ − D^G/R`; and conversely, with `τ = D^G/π(I)`. -/
theorem ex4b_overhang_equivalence (T : SuccessProb) {Z R Y₁ DG I : ℝ} (hR : 0 < R) (hI : 0 < I) :
    eqmGap T (Z - DG / T.prob I) R Y₁ I = 0 ↔ eqmGap T Z R (Y₁ - DG / R) I = 0 := by
  have hp := (T.prob_pos hI).ne'
  have e : eqmGap T (Z - DG / T.prob I) R Y₁ I = eqmGap T Z R (Y₁ - DG / R) I := by
    unfold eqmGap icCurve zpCurve
    field_simp
    ring
  rw [e]

/-- **Exercise 4(b): the overhang of government debt reduces investment** (O&R p. 415, 427): the
equilibrium with debt `D^G > 0` serviced by a success tax has strictly lower investment than the
equilibrium without debt. -/
theorem ex4b_overhang_lowers_investment (T : SuccessProb) {Z R Y₁ DG I I₀ : ℝ} (hR : 0 < R)
    (hY : 0 ≤ Y₁) (hDG : 0 < DG) (hI : 0 < I) (hI₀ : 0 < I₀)
    (hg : eqmGap T (Z - DG / T.prob I) R Y₁ I = 0) (hg₀ : eqmGap T Z R Y₁ I₀ = 0) : I < I₀ := by
  rw [ex4b_overhang_equivalence T hR hI] at hg
  have : 0 < DG / R := div_pos hDG hR
  exact eqm_strictMono_wealth T hR hY (by linarith) hI hI₀ hg hg₀

/-- Exercise 4(b), consistency: at an overhang equilibrium with `I > Y₁` the individual's
contract problem (payoff `Z − τ`) is in the borrowing regime `π'(Y₁)(Z − τ) > R`, so the
characterisation of the optimal contract applies to it. -/
theorem ex4b_individual_borrowing_regime (T : SuccessProb) {Z R Y₁ τ I : ℝ} (hR : 0 < R)
    (hY : 0 ≤ Y₁) (hYI : Y₁ < I) (hg : eqmGap T (Z - τ) R Y₁ I = 0) :
    R < T.dprob Y₁ * (Z - τ) := by
  have hI : 0 < I := lt_of_le_of_lt hY hYI
  have hp := T.prob_pos hI
  have hic : 0 < icCurve T (Z - τ) R I := by
    have : icCurve T (Z - τ) R I = zpCurve T R Y₁ I := by unfold eqmGap at hg; linarith
    rw [this]; unfold zpCurve
    have : 0 < I - Y₁ := by linarith
    positivity
  rw [icCurve_pos_iff T hI.le] at hic
  have hle := T.dprob_le_of_le hY hYI.le
  have hZt : 0 < Z - τ := by
    have := T.dprob_pos I hI.le
    by_contra h; push Not at h; nlinarith
  nlinarith

/-! ## Exercise 5: constrained efficiency (p. 427) -/

/-- An entrepreneur's expected consumption under the planner's scheme — a date-1 transfer `τ₁`
from his saver and a tax `τ₂` on success paid to savers — and a market loan contract `c`,
O&R Exercise 5. -/
noncomputable def schemePayoff (S : Setting) (τ₁ τ₂ : ℝ) (c : Contract) (I : ℝ) : ℝ :=
  S.T.prob I * (S.Z + S.E - τ₂ - c.PZ) + (1 - S.T.prob I) * (S.E - c.P0) +
    S.R * (S.Y₁ + τ₁ + c.D - I)

/-- The combined position: the scheme plus the market loan contract is itself a contract
`(P(Z) + τ₂, P(0), D + τ₁)`. -/
def combinedContract (τ₁ τ₂ : ℝ) (c : Contract) : Contract := ⟨c.PZ + τ₂, c.P0, c.D + τ₁⟩

/-- The entrepreneur's payoff under the scheme is his payoff under the combined contract. -/
theorem schemePayoff_eq (S : Setting) (τ₁ τ₂ : ℝ) (c : Contract) (I : ℝ) :
    schemePayoff S τ₁ τ₂ c I =
      borrowerPayoff S.T S.Z S.R S.Y₁ S.E (combinedContract τ₁ τ₂ c) I := by
  unfold schemePayoff borrowerPayoff combinedContract; simp only; ring

/-- **Exercise 5: no scheme makes savers no worse off without hurting entrepreneurs.** Savers
consume `R(Y₁ − τ₁) + π(I)τ₂`, a gain `G = π(I)τ₂ − Rτ₁` over laissez-faire. If `G ≥ 0`, the
entrepreneur's payoff plus `G` is at most his laissez-faire payoff (the equilibrium contract's):
whatever savers gain, entrepreneurs lose at least as much. The planner, who like lenders cannot
observe `I`, faces the entrepreneur's best response to the combined position, and market
lenders participate. -/
theorem ex5_no_pareto_improvement (S : Setting) {Ie : ℝ} (hIe : 0 < Ie)
    (hg : eqmGap S.T S.Z S.R S.w Ie = 0) {τ₁ τ₂ : ℝ} {c : Contract} {I : ℝ}
    (hP0 : c.P0 ≤ S.E)
    (hbest : IsBestResponse S.T S.Z S.R S.Y₁ S.E (combinedContract τ₁ τ₂ c) I)
    (hpart : S.Participates c I) (hsavers : S.R * τ₁ ≤ S.T.prob I * τ₂) :
    schemePayoff S τ₁ τ₂ c I + (S.T.prob I * τ₂ - S.R * τ₁) ≤
      borrowerPayoff S.T S.Z S.R S.Y₁ S.E (S.eqmContract Ie) Ie := by
  have hadm : S.Admissible (combinedContract τ₁ τ₂ c) I := by
    refine ⟨hP0, hbest, ?_⟩
    unfold Setting.Participates combinedContract at *; simp only
    nlinarith
  have hle := S.admissible_investment_le hIe hg hadm
  obtain ⟨_, hval⟩ := S.admissible_payoff_le hIe hg hadm
  rw [hval]
  have h1 : schemePayoff S τ₁ τ₂ c I + (S.T.prob I * τ₂ - S.R * τ₁) ≤
      netOutput S.T S.Z S.R S.Y₁ I + S.E := by
    unfold Setting.Participates at hpart
    unfold schemePayoff netOutput; nlinarith
  obtain ⟨Ibar, hIb, hIbZ⟩ := S.exists_Ibar
  have hIeb : Ie ≤ Ibar := by
    obtain ⟨_, _, h⟩ := S.eqm_bounds hIe hg
    by_contra hh; push Not at hh
    have := S.T.dprob_le_of_le hIb.le hh.le
    have := S.Z_pos
    nlinarith
  rcases hle.lt_or_eq with h | h
  · have := netOutput_strictMonoOn (Y₁ := S.Y₁) S.Z_pos hIbZ hbest.1 h hIeb
    linarith
  · subst h; exact h1

/-- **Exercise 5 / O&R p. 415: the equilibrium is constrained Pareto optimal.** No scheme leaves
savers no worse off and entrepreneurs no worse off with one group strictly better off. -/
theorem ex5_constrained_efficient (S : Setting) {Ie : ℝ} (hIe : 0 < Ie)
    (hg : eqmGap S.T S.Z S.R S.w Ie = 0) {τ₁ τ₂ : ℝ} {c : Contract} {I : ℝ}
    (hP0 : c.P0 ≤ S.E)
    (hbest : IsBestResponse S.T S.Z S.R S.Y₁ S.E (combinedContract τ₁ τ₂ c) I)
    (hpart : S.Participates c I) (hsavers : S.R * τ₁ ≤ S.T.prob I * τ₂) :
    ¬ (borrowerPayoff S.T S.Z S.R S.Y₁ S.E (S.eqmContract Ie) Ie ≤ schemePayoff S τ₁ τ₂ c I ∧
        (S.R * τ₁ < S.T.prob I * τ₂ ∨
          borrowerPayoff S.T S.Z S.R S.Y₁ S.E (S.eqmContract Ie) Ie <
            schemePayoff S τ₁ τ₂ c I)) := by
  have h := ex5_no_pareto_improvement S hIe hg hP0 hbest hpart hsavers
  rintro ⟨h1, h2 | h2⟩ <;> linarith

end ObstfeldRogoff.CapitalMarketImperfections.MoralHazardSmallCountry
