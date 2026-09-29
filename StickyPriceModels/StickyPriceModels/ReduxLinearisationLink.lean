/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/
import StickyPriceModels.ReduxLogLinear
import StickyPriceModels.ReduxSteadyState
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

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
