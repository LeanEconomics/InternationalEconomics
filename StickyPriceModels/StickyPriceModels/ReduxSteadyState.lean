/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StickyPriceModels.ReduxPrimitives
import Mathlib.Topology.Order.MonotoneContinuity
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.SpecialFunctions.Sqrt

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
