/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import CapitalMarketImperfections.DebtCeiling
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Algebra.Order.Field

/-!
# Borrowing under a debt limit, precommitment, and dynamic inconsistency

Obstfeld and Rogoff (1996), *Foundations of International Macroeconomics*, §6.2.1.2–6.2.1.4,
pp. 387–391 (eqs. (31)–(35), footnotes 38–40, Figure 6.6).

With `U(D, K) = u(Y₁ + D − K) + βu(F(K) + K − (1+r)D)` (eq. (31), the repay objective of
`DebtCeiling`) we prove:
* §6.2.1.2: for the problem `max U` s.t. `D ≤ D̄` (32) the Kuhn–Tucker conditions are
  *sufficient* (for concave `u`, `F`) and *necessary* (at an interior local optimum), and when
  the multiplier is positive, `F′(K) > r` and, if `β(1+r) = 1`, `C₁ < C₂`;
* §6.2.1.3: for the precommitment problem `max U` s.t. `(1+r)D ≤ η[F(K)+K]` (33) the conditions
  (34)–(35) with complementary slackness are sufficient (concave `u`, `F`, `η ≥ 0`) and
  necessary at a local optimum (the constraint gradient never vanishes, so no further
  constraint qualification is needed); with a positive multiplier `F′(K) > r ⇔ η < 1`,
  `1 + F′(K) < u′(C₁)/(βu′(C₂))`, and consumption tilts up when `β(1+r) = 1`; and the
  precommitment value is at least the discretionary value (p. 389);
* the log-linear example (p. 390): the precommitment optimum in closed form, the ratio
  `C₂/(βC₁) = (1+r)(1+α)(1−η)/(1+r−η(1+α))`, which exceeds `1 + α` iff `α > r` (not "using
  (25)": (25) only makes the denominator positive), footnote 38's slope, footnote 39's
  `D^P/K^P = η(1+α)/(1+r) < 1`;
* §6.2.1.4 (Figure 6.6): at `(D^P, K^P)` the country, once the loan is made, strictly prefers
  to default, investing `K^D < K^P` and reaching strictly higher utility — the precommitment
  plan is dynamically inconsistent — and consequently `D^P > D̄`.
-/

namespace ObstfeldRogoff.CapitalMarketImperfections.PrecommitmentInvestment

open Real Set Filter Topology

/-! ## Calculus tools -/

/-- The tangent-line (supporting-line) inequality for a concave function with a derivative, used
for sufficiency of the Kuhn–Tucker conditions (O&R pp. 387–389): if `f` is concave on a convex
`S ∋ x₀, y` and `f′(x₀) = d`, then `f(y) ≤ f(x₀) + d(y − x₀)`. -/
theorem concave_tangent_le {f : ℝ → ℝ} {S : Set ℝ} (hf : ConcaveOn ℝ S f) {x₀ y d : ℝ}
    (hx : x₀ ∈ S) (hy : y ∈ S) (hd : HasDerivAt f d x₀) : f y ≤ f x₀ + d * (y - x₀) := by
  rcases lt_trichotomy x₀ y with h | h | h
  · have := hf.slope_le_of_hasDerivAt hx hy h hd
    rw [slope_def_field, div_le_iff₀ (by linarith)] at this
    linarith
  · subst h
    simp
  · have := hf.le_slope_of_hasDerivAt hy hx h hd
    rw [slope_def_field, le_div_iff₀ (by linarith)] at this
    linarith

/-- Derivatives of a concave function are antitone (O&R p. 388, "consumption is tilted
upward"): if `f` is concave on `S ∋ x < y` with `f′(x) = a`, `f′(y) = b`, then `b ≤ a`. -/
theorem concave_deriv_antitone {f : ℝ → ℝ} {S : Set ℝ} (hf : ConcaveOn ℝ S f) {x y a b : ℝ}
    (hx : x ∈ S) (hy : y ∈ S) (hxy : x < y) (ha : HasDerivAt f a x) (hb : HasDerivAt f b y) :
    b ≤ a :=
  (hf.le_slope_of_hasDerivAt hx hy hxy hb).trans (hf.slope_le_of_hasDerivAt hx hy hxy ha)

/-- A one-sided first-order condition (for the multiplier signs, O&R pp. 388–389): if
`f(y) ≤ f(a)` for all `y < a` near `a` and `f′(a) = d`, then `d ≥ 0`. -/
theorem deriv_nonneg_of_left_max {f : ℝ → ℝ} {a d : ℝ} (hf : HasDerivAt f d a)
    (h : ∀ᶠ y in 𝓝[<] a, f y ≤ f a) : 0 ≤ d := by
  have ht : Tendsto (slope f a) (𝓝[<] a) (𝓝 d) :=
    (hasDerivAt_iff_tendsto_slope.mp hf).mono_left
      (nhdsWithin_mono _ fun y (hy : y < a) => hy.ne)
  apply ge_of_tendsto ht
  filter_upwards [h, self_mem_nhdsWithin] with y hy hy'
  rw [slope_def_field]
  exact div_nonneg_of_nonpos (sub_nonpos.mpr hy) (by rw [mem_Iio] at hy'; linarith)

/-- Partial derivative of (31) in debt, O&R p. 388: at `D`,
`∂U/∂D = u′(C₁) − (1+r)βu′(C₂)`. -/
theorem hasDerivAt_objective_debt {u F : ℝ → ℝ} {Y₁ r β D K u₁ u₂ : ℝ}
    (hu₁ : HasDerivAt u u₁ (Y₁ + D - K)) (hu₂ : HasDerivAt u u₂ (F K + K - (1 + r) * D)) :
    HasDerivAt (fun D => DebtCeiling.repayObjective u F Y₁ r β D K)
      (u₁ - (1 + r) * β * u₂) D := by
  have h1 : HasDerivAt (fun D => Y₁ + D - K) 1 D := by
    simpa using ((hasDerivAt_id D).const_add Y₁).sub_const K
  have h2 : HasDerivAt (fun D => F K + K - (1 + r) * D) (-(1 + r)) D := by
    simpa using ((hasDerivAt_id D).const_mul (1 + r)).const_sub (F K + K)
  unfold DebtCeiling.repayObjective
  exact HasDerivAt.congr_deriv (HasDerivAt.add (hu₁.comp D h1) ((hu₂.comp D h2).const_mul β))
    (by ring)

/-! ## §6.2.1.2: optimal borrowing given the ceiling, (31)–(32) -/

/-- Sufficiency of the Kuhn–Tucker conditions for (31)–(32), O&R p. 388: let `u` be concave on
`(0, ∞)` and increasing at `C₂` (`u′(C₂) ≥ 0`), `F` concave on a convex set `S`, `β ≥ 0`. If a
plan `(D*, K*)` with `D* ≤ D̄`, positive consumption and `K* ∈ S` satisfies, for some `λ ≥ 0`,
`u′(C₁) = (1+r)βu′(C₂) + λ`, `u′(C₁) = [1 + F′(K*)]βu′(C₂)` and `λ(D̄ − D*) = 0`, then it
maximises (31) over all plans with `D ≤ D̄`, positive consumption and `K ∈ S`. -/
theorem ceiling_kt_sufficient {u F : ℝ → ℝ} {S : Set ℝ} (hu : ConcaveOn ℝ (Ioi 0) u)
    (hF : ConcaveOn ℝ S F) {Y₁ r β Dbar Ds Ks u₁ u₂ f₁ lam : ℝ} (hβ : 0 ≤ β)
    (hKs : Ks ∈ S) (hc₁ : 0 < Y₁ + Ds - Ks) (hc₂ : 0 < F Ks + Ks - (1 + r) * Ds)
    (hu₁ : HasDerivAt u u₁ (Y₁ + Ds - Ks)) (hu₂ : HasDerivAt u u₂ (F Ks + Ks - (1 + r) * Ds))
    (hF' : HasDerivAt F f₁ Ks) (hu₂0 : 0 ≤ u₂) (hlam : 0 ≤ lam)
    (hfoc1 : u₁ = (1 + r) * β * u₂ + lam) (hfoc2 : u₁ = (1 + f₁) * β * u₂)
    (hcs : lam * (Dbar - Ds) = 0) {D K : ℝ} (hD : D ≤ Dbar) (hK : K ∈ S)
    (h₁ : 0 < Y₁ + D - K) (h₂ : 0 < F K + K - (1 + r) * D) :
    DebtCeiling.repayObjective u F Y₁ r β D K ≤ DebtCeiling.repayObjective u F Y₁ r β Ds Ks := by
  unfold DebtCeiling.repayObjective
  have t1 := concave_tangent_le hu (mem_Ioi.mpr hc₁) (mem_Ioi.mpr h₁) hu₁
  have t2 := concave_tangent_le hu (mem_Ioi.mpr hc₂) (mem_Ioi.mpr h₂) hu₂
  have t3 := concave_tangent_le hF hKs hK hF'
  have t3' := mul_le_mul_of_nonneg_left t3 (mul_nonneg hβ hu₂0)
  have t2' := mul_le_mul_of_nonneg_left t2 hβ
  have hl : lam * (D - Dbar) ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hlam (by linarith)
  have key : u₁ * ((D - Ds) - (K - Ks)) + β * u₂ * ((f₁ + 1) * (K - Ks) - (1 + r) * (D - Ds)) =
      lam * (D - Ds) := by
    linear_combination (D - Ds) * hfoc1 - (K - Ks) * hfoc2
  nlinarith

/-- Necessity of the Kuhn–Tucker conditions for (31)–(32), O&R p. 388: if `(D*, K*)` with
`D* ≤ D̄` maximises (31) over all plans with `D ≤ D̄` in a neighbourhood of `(D*, K*)`, and
`u`, `F` are differentiable at the relevant points, then there is `λ ≥ 0` with
`u′(C₁) = (1+r)βu′(C₂) + λ`, `u′(C₁) = [1 + F′(K*)]βu′(C₂)` and `λ(D̄ − D*) = 0`. -/
theorem ceiling_kt_necessary {u F : ℝ → ℝ} {Y₁ r β Dbar Ds Ks u₁ u₂ f₁ : ℝ}
    {N : Set (ℝ × ℝ)} (hN : N ∈ 𝓝 (Ds, Ks)) (hDs : Ds ≤ Dbar)
    (hopt : ∀ p ∈ N, p.1 ≤ Dbar → DebtCeiling.repayObjective u F Y₁ r β p.1 p.2 ≤
      DebtCeiling.repayObjective u F Y₁ r β Ds Ks)
    (hu₁ : HasDerivAt u u₁ (Y₁ + Ds - Ks)) (hu₂ : HasDerivAt u u₂ (F Ks + Ks - (1 + r) * Ds))
    (hF' : HasDerivAt F f₁ Ks) :
    ∃ lam, 0 ≤ lam ∧ u₁ = (1 + r) * β * u₂ + lam ∧ u₁ = (1 + f₁) * β * u₂ ∧
      lam * (Dbar - Ds) = 0 := by
  refine ⟨u₁ - (1 + r) * β * u₂, ?_, by ring, ?_, ?_⟩
  · -- the debt direction: lowering `D` is always feasible
    have hD := hasDerivAt_objective_debt (β := β) hu₁ hu₂
    apply deriv_nonneg_of_left_max hD
    have hc : ContinuousAt (fun D : ℝ => (D, Ks)) Ds :=
      (continuous_id.prodMk continuous_const).continuousAt
    have hmem : ∀ᶠ D in 𝓝 Ds, (D, Ks) ∈ N := hc.preimage_mem_nhds hN
    filter_upwards [nhdsWithin_le_nhds hmem, self_mem_nhdsWithin] with D hD1 hD2
    exact hopt _ hD1 (by rw [mem_Iio] at hD2; exact hD2.le.trans hDs)
  · -- the investment direction: an interior maximum
    have hK := DebtCeiling.hasDerivAt_repayObjective (β := β) hu₁ hu₂ hF'
    have hc : ContinuousAt (fun K : ℝ => (Ds, K)) Ks :=
      (continuous_const.prodMk continuous_id).continuousAt
    have hmax : IsLocalMax (DebtCeiling.repayObjective u F Y₁ r β Ds) Ks := by
      filter_upwards [hc.preimage_mem_nhds hN] with K hK
      exact hopt _ hK hDs
    have := hmax.hasDerivAt_eq_zero hK
    linarith
  · rcases hDs.lt_or_eq with hlt | heq
    · have hD := hasDerivAt_objective_debt (β := β) hu₁ hu₂
      have hc : ContinuousAt (fun D : ℝ => (D, Ks)) Ds :=
        (continuous_id.prodMk continuous_const).continuousAt
      have hmax : IsLocalMax (fun D => DebtCeiling.repayObjective u F Y₁ r β D Ks) Ds := by
        filter_upwards [hc.preimage_mem_nhds hN, Iio_mem_nhds hlt] with D hD1 hD2
        exact hopt _ hD1 (le_of_lt hD2)
      rw [hmax.hasDerivAt_eq_zero hD, zero_mul]
    · rw [heq, sub_self, mul_zero]

/-- A binding debt ceiling raises the domestic return above the world rate, O&R p. 388: in the
Kuhn–Tucker conditions of (31)–(32), if `λ > 0`, `β > 0` and `u′(C₂) > 0`, then
`F′(K₂) > r`. -/
theorem ceiling_binding_return_gt {r β u₁ u₂ f₁ lam : ℝ} (hβ : 0 < β) (hu₂ : 0 < u₂)
    (hlam : 0 < lam) (hfoc1 : u₁ = (1 + r) * β * u₂ + lam) (hfoc2 : u₁ = (1 + f₁) * β * u₂) :
    r < f₁ := by
  by_contra h
  push Not at h
  have : 0 ≤ (r - f₁) * (β * u₂) := mul_nonneg (by linarith) (by positivity)
  nlinarith

/-- A binding debt ceiling tilts consumption upward, O&R p. 388: if `β(1+r) = 1`, `λ > 0`, and
`u` is concave on `(0, ∞)` with `u′(C₁) = (1+r)βu′(C₂) + λ`, then `C₁ < C₂`
("`u′(C₁) > u′(C₂)`"). -/
theorem ceiling_binding_tilt {u : ℝ → ℝ} (hu : ConcaveOn ℝ (Ioi 0) u) {r β C₁ C₂ u₁ u₂ lam : ℝ}
    (hC₁ : 0 < C₁) (hC₂ : 0 < C₂) (hu₁ : HasDerivAt u u₁ C₁) (hu₂ : HasDerivAt u u₂ C₂)
    (hβr : β * (1 + r) = 1) (hlam : 0 < lam) (hfoc1 : u₁ = (1 + r) * β * u₂ + lam) :
    C₁ < C₂ := by
  have e : (1 + r) * β * u₂ = u₂ := by
    rw [show (1 + r) * β = β * (1 + r) by ring, hβr, one_mul]
  have hgt : u₂ < u₁ := by rw [hfoc1, e]; linarith
  by_contra h
  push Not at h
  rcases h.lt_or_eq with h' | h'
  · have := concave_deriv_antitone hu (mem_Ioi.mpr hC₂) (mem_Ioi.mpr hC₁) h' hu₂ hu₁
    linarith
  · subst h'
    have := hu₁.unique hu₂
    linarith

/-! ## §6.2.1.3: precommitment in investment, (33)–(35) -/

/-- Sufficiency of (34)–(35) with complementary slackness for the precommitment problem
`max (31)` s.t. (33) `(1+r)D ≤ η[F(K)+K]`, O&R p. 389: let `u` be concave on `(0, ∞)` with
`u′(C₂) ≥ 0`, `F` concave on a convex set `S`, `β ≥ 0`, `η ≥ 0`, `λ ≥ 0`. If
`u′(C₁) = (1+r)[βu′(C₂) + λ]` (34), `u′(C₁) = [βu′(C₂) + λη][1 + F′(K*)]` (35) and
`λ{η[F(K*)+K*] − (1+r)D*} = 0`, then `(D*, K*)` maximises (31) over all plans satisfying (33)
with positive consumption and `K ∈ S`. (The Lagrangian is concave because (33) is a concave
constraint.) -/
theorem precommit_kt_sufficient {u F : ℝ → ℝ} {S : Set ℝ} (hu : ConcaveOn ℝ (Ioi 0) u)
    (hF : ConcaveOn ℝ S F) {Y₁ r β η Ds Ks u₁ u₂ f₁ lam : ℝ} (hβ : 0 ≤ β) (hη : 0 ≤ η)
    (hKs : Ks ∈ S) (hc₁ : 0 < Y₁ + Ds - Ks) (hc₂ : 0 < F Ks + Ks - (1 + r) * Ds)
    (hu₁ : HasDerivAt u u₁ (Y₁ + Ds - Ks)) (hu₂ : HasDerivAt u u₂ (F Ks + Ks - (1 + r) * Ds))
    (hF' : HasDerivAt F f₁ Ks) (hu₂0 : 0 ≤ u₂) (hlam : 0 ≤ lam)
    (h34 : u₁ = (1 + r) * (β * u₂ + lam)) (h35 : u₁ = (β * u₂ + lam * η) * (1 + f₁))
    (hcs : lam * (η * (F Ks + Ks) - (1 + r) * Ds) = 0) {D K : ℝ}
    (hD : (1 + r) * D ≤ η * (F K + K)) (hK : K ∈ S)
    (h₁ : 0 < Y₁ + D - K) (h₂ : 0 < F K + K - (1 + r) * D) :
    DebtCeiling.repayObjective u F Y₁ r β D K ≤ DebtCeiling.repayObjective u F Y₁ r β Ds Ks := by
  unfold DebtCeiling.repayObjective
  have t1 := concave_tangent_le hu (mem_Ioi.mpr hc₁) (mem_Ioi.mpr h₁) hu₁
  have t2 := concave_tangent_le hu (mem_Ioi.mpr hc₂) (mem_Ioi.mpr h₂) hu₂
  have t3 := concave_tangent_le hF hKs hK hF'
  have t3' := mul_le_mul_of_nonneg_left t3 (mul_nonneg hβ hu₂0)
  have t3'' := mul_le_mul_of_nonneg_left t3 (mul_nonneg hlam hη)
  have t2' := mul_le_mul_of_nonneg_left t2 hβ
  have hg : 0 ≤ lam * (η * (F K + K) - (1 + r) * D) := mul_nonneg hlam (by linarith)
  have key : u₁ * ((D - Ds) - (K - Ks)) + β * u₂ * ((f₁ + 1) * (K - Ks) - (1 + r) * (D - Ds)) +
      lam * (η * (f₁ + 1) * (K - Ks) - (1 + r) * (D - Ds)) = 0 := by
    linear_combination (D - Ds) * h34 - (K - Ks) * h35
  nlinarith

/-- Necessity of (34)–(35) with complementary slackness, O&R p. 389: if `(D*, K*)` satisfies
(33) and maximises (31) over the plans satisfying (33) in a neighbourhood of `(D*, K*)`, with
`r > −1` and `u`, `F` differentiable at the relevant points, then there is `λ ≥ 0` with (34),
(35) and `λ{η[F(K*)+K*] − (1+r)D*} = 0`. No constraint qualification is needed: along the
binding constraint `D = η[F(K)+K]/(1+r)` the problem is an unconstrained problem in `K`, and
lowering `D` is always feasible. -/
theorem precommit_kt_necessary {u F : ℝ → ℝ} {Y₁ r β η Ds Ks u₁ u₂ f₁ : ℝ} (hr : -1 < r)
    {N : Set (ℝ × ℝ)} (hN : N ∈ 𝓝 (Ds, Ks)) (hfeas : (1 + r) * Ds ≤ η * (F Ks + Ks))
    (hopt : ∀ p ∈ N, (1 + r) * p.1 ≤ η * (F p.2 + p.2) →
      DebtCeiling.repayObjective u F Y₁ r β p.1 p.2 ≤
        DebtCeiling.repayObjective u F Y₁ r β Ds Ks)
    (hu₁ : HasDerivAt u u₁ (Y₁ + Ds - Ks)) (hu₂ : HasDerivAt u u₂ (F Ks + Ks - (1 + r) * Ds))
    (hF' : HasDerivAt F f₁ Ks) :
    ∃ lam, 0 ≤ lam ∧ u₁ = (1 + r) * (β * u₂ + lam) ∧ u₁ = (β * u₂ + lam * η) * (1 + f₁) ∧
      lam * (η * (F Ks + Ks) - (1 + r) * Ds) = 0 := by
  have h1r : 0 < 1 + r := by linarith
  have hD := hasDerivAt_objective_debt (β := β) hu₁ hu₂
  have hK := DebtCeiling.hasDerivAt_repayObjective (β := β) hu₁ hu₂ hF'
  have hcD : ContinuousAt (fun D : ℝ => (D, Ks)) Ds :=
    (continuous_id.prodMk continuous_const).continuousAt
  have hcK : ContinuousAt (fun K : ℝ => (Ds, K)) Ks :=
    (continuous_const.prodMk continuous_id).continuousAt
  have hFc : ContinuousAt (fun K => η * (F K + K)) Ks :=
    (hF'.continuousAt.add continuousAt_id).const_mul η
  rcases hfeas.lt_or_eq with hlt | heq
  · -- slack constraint: an interior maximum, `λ = 0`
    have hmaxD : IsLocalMax (fun D => DebtCeiling.repayObjective u F Y₁ r β D Ks) Ds := by
      have hc : ContinuousAt (fun D : ℝ => (1 + r) * D) Ds := (continuous_const_mul _).continuousAt
      filter_upwards [hcD.preimage_mem_nhds hN, hc.eventually_lt continuousAt_const hlt]
        with D hD1 hD2
      exact hopt _ hD1 hD2.le
    have hmaxK : IsLocalMax (DebtCeiling.repayObjective u F Y₁ r β Ds) Ks := by
      filter_upwards [hcK.preimage_mem_nhds hN, continuousAt_const.eventually_lt hFc hlt]
        with K hK1 hK2
      exact hopt _ hK1 hK2.le
    have e1 := hmaxD.hasDerivAt_eq_zero hD
    have e2 := hmaxK.hasDerivAt_eq_zero hK
    refine ⟨0, le_rfl, by linarith, by linarith, by ring⟩
  · -- binding constraint: move along `D = η[F(K)+K]/(1+r)`
    set lam := (u₁ - (1 + r) * β * u₂) / (1 + r) with hlam
    have hlam0 : 0 ≤ lam := by
      apply div_nonneg _ h1r.le
      apply deriv_nonneg_of_left_max hD
      filter_upwards [nhdsWithin_le_nhds (hcD.preimage_mem_nhds hN), self_mem_nhdsWithin]
        with D hD1 hD2
      rw [mem_Iio] at hD2
      exact hopt _ hD1 (by simp only; nlinarith)
    set curve : ℝ → ℝ := fun K => η * (F K + K) / (1 + r) with hcv
    have hcK' : curve Ks = Ds := by
      rw [hcv]
      simp only
      rw [← heq]
      field_simp
    have hcurve : ContinuousAt (fun K => (curve K, K)) Ks :=
      (hFc.div_const _).prodMk continuousAt_id
    have hN' : N ∈ 𝓝 (curve Ks, Ks) := by rw [hcK']; exact hN
    have hmax : IsLocalMax (fun K => DebtCeiling.repayObjective u F Y₁ r β (curve K) K) Ks := by
      filter_upwards [hcurve.preimage_mem_nhds hN'] with K hK1
      have := hopt _ hK1 (by simp only [hcv]; field_simp; exact le_rfl)
      rw [hcK']
      exact this
    have e1 : Y₁ + curve Ks - Ks = Y₁ + Ds - Ks := by rw [hcK']
    have e2 : F Ks + Ks - (1 + r) * curve Ks = F Ks + Ks - (1 + r) * Ds := by rw [hcK']
    have hin1 : HasDerivAt (fun K => Y₁ + curve K - K) (η * (f₁ + 1) / (1 + r) - 1) Ks := by
      have := (((hF'.add (hasDerivAt_id Ks)).const_mul η).div_const (1 + r)).const_add Y₁
      exact (this.sub (hasDerivAt_id Ks)).congr_deriv (by simp)
    have hin2 : HasDerivAt (fun K => F K + K - (1 + r) * curve K)
        ((f₁ + 1) - (1 + r) * (η * (f₁ + 1) / (1 + r))) Ks :=
      (hF'.add (hasDerivAt_id Ks)).sub
        ((((hF'.add (hasDerivAt_id Ks)).const_mul η).div_const (1 + r)).const_mul (1 + r))
    rw [← e1] at hu₁
    rw [← e2] at hu₂
    have hphi : HasDerivAt (fun K => DebtCeiling.repayObjective u F Y₁ r β (curve K) K)
        (u₁ * (η * (f₁ + 1) / (1 + r) - 1) +
          β * (u₂ * ((f₁ + 1) - (1 + r) * (η * (f₁ + 1) / (1 + r))))) Ks := by
      unfold DebtCeiling.repayObjective
      exact HasDerivAt.add (HasDerivAt.comp (h := fun K => Y₁ + curve K - K) Ks hu₁ hin1)
        ((HasDerivAt.comp (h := fun K => F K + K - (1 + r) * curve K) Ks hu₂ hin2).const_mul β)
    have e3 := hmax.hasDerivAt_eq_zero hphi
    refine ⟨lam, hlam0, ?_, ?_, ?_⟩
    · rw [hlam]; field_simp; ring
    · rw [hlam]
      field_simp at e3 ⊢
      linear_combination -e3
    · rw [heq, sub_self, mul_zero]

/-- Under precommitment a binding constraint raises the domestic return above `r` exactly when
sanctions are incomplete, O&R p. 389 ("`F′(K₂)` must exceed `r` for `λ` to be strictly
positive"): if (34)–(35) hold with `λ > 0`, `βu′(C₂) > 0`, `η ≥ 0` and `r > −1`, then
`F′(K*) > r ⇔ η < 1`. -/
theorem precommit_return_gt_iff {r β η u₁ u₂ f₁ lam : ℝ} (hr : -1 < r) (hβu : 0 < β * u₂)
    (hη : 0 ≤ η) (hlam : 0 < lam) (h34 : u₁ = (1 + r) * (β * u₂ + lam))
    (h35 : u₁ = (β * u₂ + lam * η) * (1 + f₁)) : r < f₁ ↔ η < 1 := by
  have hA : 0 < β * u₂ + lam * η := by nlinarith
  have heq : (1 + r) * (β * u₂ + lam) = (β * u₂ + lam * η) * (1 + f₁) := h34.symm.trans h35
  constructor
  · intro hf
    by_contra hη1
    push Not at hη1
    have : lam ≤ lam * η := by nlinarith
    nlinarith
  · intro hη1
    by_contra hf
    push Not at hf
    have : lam * η < lam := by nlinarith
    nlinarith

/-- Investment falls short of the consumption MRS under precommitment, O&R p. 389 (condition
(35): "the marginal gross return to investment is below the marginal rate of substitution"):
if (34)–(35) hold with `λ > 0`, `η > 0`, `βu′(C₂) > 0`, `r > −1`, then
`[1 + F′(K*)]βu′(C₂) < u′(C₁)`. -/
theorem precommit_return_lt_mrs {r β η u₁ u₂ f₁ lam : ℝ} (hr : -1 < r) (hβu : 0 < β * u₂)
    (hη : 0 < η) (hlam : 0 < lam) (h34 : u₁ = (1 + r) * (β * u₂ + lam))
    (h35 : u₁ = (β * u₂ + lam * η) * (1 + f₁)) : (1 + f₁) * (β * u₂) < u₁ := by
  have hu₁ : 0 < u₁ := by
    rw [h34]
    exact mul_pos (by linarith) (by linarith)
  have hA : 0 < β * u₂ + lam * η := by nlinarith
  have hf : 0 < 1 + f₁ := by
    by_contra h
    push Not at h
    nlinarith
  have : 0 < lam * η * (1 + f₁) := mul_pos (mul_pos hlam hη) hf
  nlinarith

/-- Upward consumption tilt under binding precommitment, O&R p. 389 ("consumption will have an
upward tilt when `β(1+r) = 1`"): with (34), `λ > 0`, `r > −1` and `u` concave on `(0, ∞)`,
`C₁ < C₂`. -/
theorem precommit_tilt {u : ℝ → ℝ} (hu : ConcaveOn ℝ (Ioi 0) u) {r β C₁ C₂ u₁ u₂ lam : ℝ}
    (hr : -1 < r) (hC₁ : 0 < C₁) (hC₂ : 0 < C₂) (hu₁ : HasDerivAt u u₁ C₁)
    (hu₂ : HasDerivAt u u₂ C₂) (hβr : β * (1 + r) = 1) (hlam : 0 < lam)
    (h34 : u₁ = (1 + r) * (β * u₂ + lam)) : C₁ < C₂ :=
  ceiling_binding_tilt hu hC₁ hC₂ hu₁ hu₂ hβr (lam := (1 + r) * lam)
    (mul_pos (by linarith) hlam) (by rw [h34]; ring)

/-- The precommitment value is at least the discretionary value, O&R p. 389 ("the country must
benefit, since it can always commit to the investment level that would arise under complete
discretion"): let `(D*, K*)` maximise (31) subject to (33) over plans with positive
consumption, and let `D` be a debt level at which, with discretion, repayment is (weakly)
preferred, with repay optimum `K^N` (the hypotheses of `DebtCeiling.repay_optimal_of_value_ge`
on a set `S` of plans). Then the discretionary outcome `(D, K^N)` satisfies (33), so its utility
is at most the precommitment value. -/
theorem precommitment_value_ge_discretion {u F : ℝ → ℝ} (hu : StrictMonoOn u (Ioi 0))
    {Y₁ r η β D Ds Ks : ℝ} (hβ : 0 < β) {S : Set ℝ}
    (hpos : ∀ K ∈ S, 0 < F K + K - (1 + r) * D ∧ 0 < (1 - η) * (F K + K)) {KN KD : ℝ}
    (hKN : KN ∈ S) (hN : IsMaxOn (DebtCeiling.repayObjective u F Y₁ r β D) S KN)
    (hD : IsMaxOn (DebtCeiling.defaultObjective u F Y₁ η β D) S KD)
    (hge : DebtCeiling.defaultObjective u F Y₁ η β D KD ≤
      DebtCeiling.repayObjective u F Y₁ r β D KN)
    (hc₁ : 0 < Y₁ + D - KN)
    (hopt : ∀ D' K', (1 + r) * D' ≤ η * (F K' + K') → 0 < Y₁ + D' - K' →
      0 < F K' + K' - (1 + r) * D' →
      DebtCeiling.repayObjective u F Y₁ r β D' K' ≤ DebtCeiling.repayObjective u F Y₁ r β Ds Ks) :
    DebtCeiling.repayObjective u F Y₁ r β D KN ≤ DebtCeiling.repayObjective u F Y₁ r β Ds Ks := by
  obtain ⟨-, -, hIC⟩ := DebtCeiling.repay_optimal_of_value_ge hu hβ hpos hKN hN hD hge
  exact hopt D KN hIC hc₁ (hpos KN hKN).1

/-- On a binding sanction constraint repaying and defaulting give the same consumption, O&R
Figure 6.6 (point `P` lies on both GNPᴺ and GNPᴰ): if `(1+r)D = η[F(K)+K]` then the repay and
default objectives coincide at `(D, K)`. -/
theorem objectives_eq_of_binding {u F : ℝ → ℝ} {Y₁ r η β D K : ℝ}
    (hbind : (1 + r) * D = η * (F K + K)) :
    DebtCeiling.defaultObjective u F Y₁ η β D K = DebtCeiling.repayObjective u F Y₁ r β D K := by
  unfold DebtCeiling.defaultObjective DebtCeiling.repayObjective
  rw [hbind]
  ring_nf

/-! ## The log-linear example, p. 390, footnotes 38–39 -/

/-- Strict version of the log-utility budget bound: if `c₁ + c₂/R = W` and `c₁ ≠ W/(1+β)`, then
`log c₁ + β log c₂ < (1+β) log(W/(1+β)) + β log(Rβ)` (uniqueness of the optimum (27)/(29)).
(O&R §6.2.1.2–6.2.1.4, pp. 387–390.) -/
theorem log_two_period_lt {W R β c₁ c₂ : ℝ} (hW : 0 < W) (hR : 0 < R) (hβ : 0 < β)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hbud : c₁ + c₂ / R = W) (hne : c₁ ≠ W / (1 + β)) :
    log c₁ + β * log c₂ < (1 + β) * log (W / (1 + β)) + β * log (R * β) := by
  set s₁ := W / (1 + β) with hs₁
  set s₂ := R * β * (W / (1 + β)) with hs₂
  have hs₁p : 0 < s₁ := by positivity
  have hs₂p : 0 < s₂ := by positivity
  have h1 : log c₁ - log s₁ < c₁ / s₁ - 1 := by
    rw [← log_div hc₁.ne' hs₁p.ne']
    refine log_lt_sub_one_of_pos (div_pos hc₁ hs₁p) ?_
    intro h
    exact hne ((div_eq_one_iff_eq hs₁p.ne').mp h)
  have h2 : log c₂ - log s₂ ≤ c₂ / s₂ - 1 := by
    rw [← log_div hc₂.ne' hs₂p.ne']
    exact log_le_sub_one_of_pos (div_pos hc₂ hs₂p)
  have h2' := mul_le_mul_of_nonneg_left h2 hβ.le
  have key : c₁ / s₁ - 1 + β * (c₂ / s₂ - 1) = 0 := by
    subst hbud
    rw [hs₁, hs₂]
    field_simp
    ring
  have hlog2 : log s₂ = log (R * β) + log s₁ := by
    rw [hs₂, log_mul (by positivity) hs₁p.ne']
  nlinarith

/-- The precommitment debt–investment ratio, footnote 39, O&R p. 390: `c = η(1+α)/(1+r)`. -/
noncomputable def precommitRatio (α r η : ℝ) : ℝ := η * (1 + α) / (1 + r)

/-- The precommitment investment `K^P`, O&R p. 390 (with `u = log`, `F = αK`, (33) binding):
`K^P = βY₁/[(1+β)(1 − c)]`, `c = η(1+α)/(1+r)`. -/
noncomputable def precommitInvestment (Y₁ α r β η : ℝ) : ℝ :=
  β * Y₁ / ((1 + β) * (1 - precommitRatio α r η))

/-- The precommitment loan `D^P = cK^P`, O&R p. 390: `η(1+α)K^P = (1+r)D^P`. -/
noncomputable def precommitDebt (Y₁ α r β η : ℝ) : ℝ :=
  precommitRatio α r η * precommitInvestment Y₁ α r β η

/-- Basic facts on the log-linear precommitment plan, O&R p. 390: under (25), `0 < c < 1`,
`K^P > 0`, `D^P > 0`, (33) binds, `C₁ = Y₁/(1+β)` and `C₂ = (1−η)(1+α)K^P`. -/
theorem precommit_basic {Y₁ α r β η : ℝ} (hY : 0 < Y₁) (hβ : 0 < β) (hη0 : 0 < η)
    (hr : -1 < r) (hα : 0 < 1 + α) (h25 : η * (1 + α) < 1 + r) :
    0 < precommitRatio α r η ∧ precommitRatio α r η < 1 ∧
      0 < precommitInvestment Y₁ α r β η ∧ 0 < precommitDebt Y₁ α r β η ∧
      (1 + r) * precommitDebt Y₁ α r β η =
        η * (α * precommitInvestment Y₁ α r β η + precommitInvestment Y₁ α r β η) ∧
      Y₁ + precommitDebt Y₁ α r β η - precommitInvestment Y₁ α r β η = Y₁ / (1 + β) ∧
      α * precommitInvestment Y₁ α r β η + precommitInvestment Y₁ α r β η -
          (1 + r) * precommitDebt Y₁ α r β η =
        (1 - η) * (1 + α) * precommitInvestment Y₁ α r β η := by
  have h1r : 0 < 1 + r := by linarith
  have hc0 : 0 < precommitRatio α r η := by unfold precommitRatio; positivity
  have hc1 : precommitRatio α r η < 1 := by
    unfold precommitRatio; rw [div_lt_one h1r]; exact h25
  have hK : 0 < precommitInvestment Y₁ α r β η := by
    unfold precommitInvestment
    have : 0 < 1 - precommitRatio α r η := by linarith
    positivity
  have hbind : (1 + r) * precommitDebt Y₁ α r β η =
      η * (α * precommitInvestment Y₁ α r β η + precommitInvestment Y₁ α r β η) := by
    unfold precommitDebt precommitRatio
    field_simp
    ring
  refine ⟨hc0, hc1, hK, mul_pos hc0 hK, hbind, ?_, ?_⟩
  · unfold precommitDebt precommitInvestment
    have : 1 - precommitRatio α r η ≠ 0 := by linarith
    field_simp
    ring
  · rw [hbind]; ring

/-- The Kuhn–Tucker multiplier of the log-linear precommitment problem, O&R p. 390:
`λ = u′(C₁)/(1+r) − βu′(C₂)` with `u′ = 1/C`. -/
noncomputable def precommitMultiplier (Y₁ α r β η : ℝ) : ℝ :=
  (Y₁ / (1 + β))⁻¹ / (1 + r) - β * ((1 - η) * (1 + α) * precommitInvestment Y₁ α r β η)⁻¹

/-- The log-linear precommitment plan satisfies (34)–(35) and complementary slackness, and its
multiplier is positive exactly when `α > r`, O&R pp. 389–390 (under (25), `0 < η < 1`,
`β, Y₁ > 0`, `1 + α > 0`). -/
theorem precommit_kt_logLinear {Y₁ α r β η : ℝ} (hY : 0 < Y₁) (hβ : 0 < β) (hη0 : 0 < η)
    (hη1 : η < 1) (hr : -1 < r) (hα : 0 < 1 + α) (h25 : η * (1 + α) < 1 + r) :
    (Y₁ / (1 + β))⁻¹ = (1 + r) * (β * ((1 - η) * (1 + α) * precommitInvestment Y₁ α r β η)⁻¹ +
        precommitMultiplier Y₁ α r β η) ∧
      (Y₁ / (1 + β))⁻¹ = (β * ((1 - η) * (1 + α) * precommitInvestment Y₁ α r β η)⁻¹ +
        precommitMultiplier Y₁ α r β η * η) * (1 + α) ∧
      (0 < precommitMultiplier Y₁ α r β η ↔ r < α) := by
  have h1r : 0 < 1 + r := by linarith
  have h1η : 0 < 1 - η := by linarith
  obtain ⟨-, hc1, -, -, -, -, -⟩ := precommit_basic hY hβ hη0 hr hα h25
  have hd : 0 < 1 + r - η * (1 + α) := by linarith
  have hKP : precommitInvestment Y₁ α r β η =
      β * Y₁ * (1 + r) / ((1 + β) * (1 + r - η * (1 + α))) := by
    unfold precommitInvestment precommitRatio
    field_simp
  refine ⟨?_, ?_, ?_⟩
  · unfold precommitMultiplier; field_simp; ring
  · unfold precommitMultiplier
    rw [hKP]
    field_simp
    ring
  · have hm : precommitMultiplier Y₁ α r β η =
        (1 + β) * (α - r) / (Y₁ * (1 + r) * (1 - η) * (1 + α)) := by
      unfold precommitMultiplier
      rw [hKP]
      field_simp
      ring
    rw [hm]
    constructor
    · intro h
      by_contra h'
      push Not at h'
      have : (1 + β) * (α - r) / (Y₁ * (1 + r) * (1 - η) * (1 + α)) ≤ 0 :=
        div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos (by linarith)
          (by linarith)) (by positivity)
      linarith
    · intro h
      have : 0 < α - r := by linarith
      positivity

/-- `F = αK` is concave (it is linear). (O&R §6.2.1.2–6.2.1.4, pp. 387–390.) -/
theorem linear_concaveOn (α : ℝ) : ConcaveOn ℝ univ fun K : ℝ => α * K :=
  ⟨convex_univ, fun x _ y _ a b _ _ _ => by simp only [smul_eq_mul]; exact le_of_eq (by ring)⟩

/-- The log-linear precommitment optimum, O&R p. 390: with `u = log`, `F = αK`, `α > r > −1`,
`0 < η < 1`, `β, Y₁ > 0` and (25), the plan `(D^P, K^P)` maximises (31) over all plans
satisfying (33) with positive consumption. (Global optimality via the sufficiency theorem
`precommit_kt_sufficient`.) -/
theorem logLinear_precommit_optimal {Y₁ α r β η : ℝ} (hY : 0 < Y₁) (hβ : 0 < β)
    (hη0 : 0 < η) (hη1 : η < 1) (hr : -1 < r) (hrα : r < α) (h25 : η * (1 + α) < 1 + r)
    {D K : ℝ} (hD : (1 + r) * D ≤ η * (α * K + K)) (h₁ : 0 < Y₁ + D - K)
    (h₂ : 0 < α * K + K - (1 + r) * D) :
    DebtCeiling.repayObjective log (fun K => α * K) Y₁ r β D K ≤
      DebtCeiling.repayObjective log (fun K => α * K) Y₁ r β (precommitDebt Y₁ α r β η)
        (precommitInvestment Y₁ α r β η) := by
  have hα : 0 < 1 + α := by linarith
  obtain ⟨-, -, hK, -, hbind, hC1, hC2⟩ := precommit_basic hY hβ hη0 hr hα h25
  obtain ⟨h34, h35, hlamiff⟩ := precommit_kt_logLinear hY hβ hη0 hη1 hr hα h25
  have hc₂ : 0 < (1 - η) * (1 + α) * precommitInvestment Y₁ α r β η := by
    have : 0 < 1 - η := by linarith
    positivity
  have hu₁ : HasDerivAt log (Y₁ / (1 + β))⁻¹
      (Y₁ + precommitDebt Y₁ α r β η - precommitInvestment Y₁ α r β η) := by
    rw [hC1]; exact hasDerivAt_log (by positivity)
  have hu₂ : HasDerivAt log ((1 - η) * (1 + α) * precommitInvestment Y₁ α r β η)⁻¹
      (α * precommitInvestment Y₁ α r β η + precommitInvestment Y₁ α r β η -
        (1 + r) * precommitDebt Y₁ α r β η) := by
    rw [hC2]; exact hasDerivAt_log hc₂.ne'
  have hF : HasDerivAt (fun K : ℝ => α * K) α (precommitInvestment Y₁ α r β η) := by
    simpa using (hasDerivAt_id (precommitInvestment Y₁ α r β η)).const_mul α
  exact precommit_kt_sufficient strictConcaveOn_log_Ioi.concaveOn (linear_concaveOn α) hβ.le
    hη0.le (mem_univ _) (by rw [hC1]; positivity) (by rw [hC2]; exact hc₂)
    hu₁ hu₂ hF (inv_pos.mpr hc₂).le (hlamiff.mpr hrα).le h34 h35
    (by rw [hbind, sub_self, mul_zero]) hD (mem_univ K) h₁ h₂

/-- The precommitment consumption ratio, O&R p. 390:
`u′(C₁)/(βu′(C₂)) = C₂/(βC₁) = (1+r)(1+α)(1−η)/(1+r−η(1+α))`. -/
theorem precommit_consumption_ratio {Y₁ α r β η : ℝ} (hY : 0 < Y₁) (hβ : 0 < β)
    (hr : -1 < r) (hα : 0 < 1 + α) (h25 : η * (1 + α) < 1 + r) :
    ((1 - η) * (1 + α) * precommitInvestment Y₁ α r β η) / (β * (Y₁ / (1 + β))) =
      (1 + r) * (1 + α) * (1 - η) / (1 + r - η * (1 + α)) := by
  have h1r : 0 < 1 + r := by linarith
  have hd : 0 < 1 + r - η * (1 + α) := by linarith
  unfold precommitInvestment precommitRatio
  have : 1 - η * (1 + α) / (1 + r) ≠ 0 := by
    rw [sub_ne_zero, ne_comm, ne_eq, div_eq_one_iff_eq h1r.ne']; linarith
  field_simp

/-- The inequality asserted on p. 390, corrected: `(1+r)(1+α)(1−η)/(1+r−η(1+α)) > 1 + α` holds
if and only if `α > r` (given `η > 0`, `1 + α > 0` and (25)). The book says to verify it
"using (25)"; (25) only makes the denominator positive — the inequality itself is `α > r`. -/
theorem precommit_ratio_gt_iff {α r η : ℝ} (hη0 : 0 < η) (hα : 0 < 1 + α)
    (h25 : η * (1 + α) < 1 + r) :
    1 + α < (1 + r) * (1 + α) * (1 - η) / (1 + r - η * (1 + α)) ↔ r < α := by
  have hd : 0 < 1 + r - η * (1 + α) := by linarith
  rw [lt_div_iff₀ hd]
  have e : (1 + r) * (1 + α) * (1 - η) - (1 + α) * (1 + r - η * (1 + α)) =
      η * (1 + α) * (α - r) := by ring
  have hp : 0 < η * (1 + α) := mul_pos hη0 hα
  constructor
  · intro h
    have : 0 < η * (1 + α) * (α - r) := by linarith
    have := (pos_iff_pos_of_mul_pos this).mp hp
    linarith
  · intro h
    have : 0 < η * (1 + α) * (α - r) := mul_pos hp (by linarith)
    linarith

/-- Footnote 38, O&R p. 390: the slope of the ray `OC` through the precommitment point is
`C₂/C₁ = β(1+r)(1+α)(1−η)/(1+r−η(1+α))`. -/
theorem footnote38_slope {Y₁ α r β η : ℝ} (hY : 0 < Y₁) (hβ : 0 < β)
    (hr : -1 < r) (hα : 0 < 1 + α) (h25 : η * (1 + α) < 1 + r) :
    ((1 - η) * (1 + α) * precommitInvestment Y₁ α r β η) / (Y₁ / (1 + β)) =
      β * (1 + r) * (1 + α) * (1 - η) / (1 + r - η * (1 + α)) := by
  have h := precommit_consumption_ratio hY hβ hr hα h25
  have hb : (0 : ℝ) < Y₁ / (1 + β) := by positivity
  rw [div_eq_iff (by positivity)] at h
  rw [div_eq_iff hb.ne', h]
  ring

/-- Footnote 39, O&R p. 390: along the binding repayment constraint
`η(1+α)K^P = (1+r)D^P`, and under (25) `D^P/K^P = η(1+α)/(1+r) < 1`, so the country must cut
current consumption every time it raises investment, which bounds precommitment borrowing. -/
theorem footnote39_debt_investment_ratio {Y₁ α r β η : ℝ} (hY : 0 < Y₁) (hβ : 0 < β)
    (hη0 : 0 < η) (hr : -1 < r) (hα : 0 < 1 + α) (h25 : η * (1 + α) < 1 + r) :
    η * (1 + α) * precommitInvestment Y₁ α r β η = (1 + r) * precommitDebt Y₁ α r β η ∧
      precommitDebt Y₁ α r β η / precommitInvestment Y₁ α r β η = η * (1 + α) / (1 + r) ∧
      precommitDebt Y₁ α r β η / precommitInvestment Y₁ α r β η < 1 := by
  obtain ⟨-, hc1, hK, -, hbind, -, -⟩ := precommit_basic hY hβ hη0 hr hα h25
  have hratio : precommitDebt Y₁ α r β η / precommitInvestment Y₁ α r β η =
      η * (1 + α) / (1 + r) := by
    unfold precommitDebt
    rw [mul_div_assoc, div_self hK.ne', mul_one]
    rfl
  refine ⟨by rw [hbind]; ring, hratio, ?_⟩
  rw [hratio]
  exact hc1

/-! ## §6.2.1.4: dynamic inconsistency (Figure 6.6) -/

/-- Dynamic inconsistency, O&R p. 390 and Figure 6.6: in the log-linear example (with
`α > r > −1`, `0 < η < 1`, `β, Y₁ > 0` and (25)), once the precommitment loan `D^P` has been
made the country does strictly better by defaulting and investing `K^D = β(Y₁ + D^P)/(1+β)`:
(i) `U^D(D^P) > U(D^P, K^P)` (point `D` lies on a higher indifference curve than `P`);
(ii) `K^D < K^P`; (iii) ex post default is strictly preferred to repayment,
`U^N(D^P) < U^D(D^P)`; hence (iv) `D^P > D̄`: rational lenders will not lend `D^P`. -/
theorem dynamic_inconsistency {Y₁ α r β η : ℝ} (hY : 0 < Y₁) (hβ : 0 < β)
    (hη0 : 0 < η) (hη1 : η < 1) (hr : -1 < r) (hrα : r < α) (h25 : η * (1 + α) < 1 + r) :
    DebtCeiling.repayObjective log (fun K => α * K) Y₁ r β (precommitDebt Y₁ α r β η)
        (precommitInvestment Y₁ α r β η) < DebtCeiling.defaultValue Y₁ α η β
          (precommitDebt Y₁ α r β η) ∧
      DebtCeiling.defaultInvestment Y₁ β (precommitDebt Y₁ α r β η) <
        precommitInvestment Y₁ α r β η ∧
      DebtCeiling.repayValue Y₁ α r β (precommitDebt Y₁ α r β η) <
        DebtCeiling.defaultValue Y₁ α η β (precommitDebt Y₁ α r β η) ∧
      DebtCeiling.debtCeiling Y₁ α r β η < precommitDebt Y₁ α r β η := by
  have hα : 0 < 1 + α := by linarith
  have h1η : 0 < 1 - η := by linarith
  obtain ⟨hc0, hc1, hK, hDP, hbind, hC1, hC2⟩ := precommit_basic hY hβ hη0 hr hα h25
  set KP := precommitInvestment Y₁ α r β η with hKPdef
  set DP := precommitDebt Y₁ α r β η with hDPdef
  set c := precommitRatio α r η with hcdef
  have hWD : 0 < Y₁ + DP := by linarith
  obtain ⟨-, -, hdmax, hdval⟩ := DebtCeiling.logLinear_default_optimum (η := η) (α := α) hα hβ
    hη1 hWD
  -- (i): at `K^P` the default objective equals the precommitment utility, and `K^P ≠ K^D`
  have hi : DebtCeiling.repayObjective log (fun K => α * K) Y₁ r β DP KP <
      DebtCeiling.defaultValue Y₁ α η β DP := by
    rw [← objectives_eq_of_binding hbind]
    unfold DebtCeiling.defaultObjective DebtCeiling.defaultValue
    have hR : 0 < (1 - η) * (1 + α) := mul_pos h1η hα
    have hbud : (Y₁ + DP - KP) + (1 - η) * (α * KP + KP) / ((1 - η) * (1 + α)) = Y₁ + DP :=
      DebtCeiling.default_budget Y₁ α η DP KP hα hη1
    have hne : Y₁ + DP - KP ≠ (Y₁ + DP) / (1 + β) := by
      rw [hC1]
      intro h
      have : Y₁ = Y₁ + DP := by
        have hb : (1 + β) ≠ 0 := by linarith
        field_simp at h
        linarith
      linarith
    have := log_two_period_lt hWD hR hβ (by rw [hC1]; positivity)
      (mul_pos h1η (by nlinarith)) hbud hne
    rw [show (1 - η) * (1 + α) * β = (1 - η) * (1 + α) * β by ring]
    linarith
  -- (ii)
  have hii : DebtCeiling.defaultInvestment Y₁ β DP < KP := by
    unfold DebtCeiling.defaultInvestment
    have e : KP * (1 - c) * (1 + β) = β * Y₁ := by
      rw [hKPdef]; unfold precommitInvestment
      rw [← hcdef]
      have : 1 - c ≠ 0 := by linarith
      field_simp
    have hDPc : DP = c * KP := rfl
    rw [div_lt_iff₀ (by linarith), hDPc]
    nlinarith [mul_pos hc0 hK]
  -- (iii)
  have hiii : DebtCeiling.repayValue Y₁ α r β DP < DebtCeiling.defaultValue Y₁ α η β DP := by
    by_contra hle
    push Not at hle
    have hW : 0 < DebtCeiling.repayWealth Y₁ α r DP := by
      unfold DebtCeiling.repayWealth
      have : 0 ≤ (α - r) / (1 + α) := div_nonneg (by linarith) hα.le
      positivity
    obtain ⟨hN1, hN2, -, hNval⟩ := DebtCeiling.logLinear_repay_optimum (r := r) hα hβ hW
    set KN := DebtCeiling.repayInvestment Y₁ α r β DP
    have hn1 : 0 < Y₁ + DP - KN := by rw [hN1]; positivity
    have hn2 : 0 < α * KN + KN - (1 + r) * DP := by rw [hN2]; positivity
    have hKNpos : 0 < α * KN + KN := by nlinarith
    -- full repayment is incentive compatible at `K^N`
    have hIC : (1 + r) * DP ≤ η * (α * KN + KN) := by
      by_contra hlt
      push Not at hlt
      have hlt' : α * KN + KN - (1 + r) * DP < (1 - η) * (α * KN + KN) := by linarith
      have h1 := log_lt_log hn2 hlt'
      have h2 := hdmax KN hn1 (mul_pos h1η hKNpos)
      rw [hdval] at h2
      unfold DebtCeiling.defaultObjective at h2
      have h3 : DebtCeiling.repayObjective log (fun K => α * K) Y₁ r β DP KN =
          DebtCeiling.repayValue Y₁ α r β DP := hNval
      unfold DebtCeiling.repayObjective at h3
      simp only at h2 h3
      nlinarith
    have hopt := logLinear_precommit_optimal hY hβ hη0 hη1 hr hrα h25 hIC hn1 hn2
    rw [hNval] at hopt
    linarith
  refine ⟨hi, hii, hiii, ?_⟩
  -- (iv)
  have hak := DebtCeiling.ceiling_denominator_pos_of_ineq25 hα hβ hη0 hη1 h25
  exact (DebtCeiling.default_iff_gt_debtCeiling hY hr hrα.le hβ hη0 hη1 hak hDP.le).mp hiii

end ObstfeldRogoff.CapitalMarketImperfections.PrecommitmentInvestment
